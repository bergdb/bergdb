package bergdb.storage;

import java.io.IOException;
import java.io.InterruptedIOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.common.Bug;
import bergdb.common.NullProgressListener;
import bergdb.common.ProgressListener;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.pub.util.BadReplicaException;
import bergdb.pub.util.StorageInfo;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * <p>An object of this class is used to handle multiple storage locations.
 * There is exactly one main storage and zero or more replicas.
 * Data appended to this object is written to the main storage and all replicas.
 * A replica can be added while the database is running. Also replicas can be removed while
 * the database is running.<p>
 * 
 * <p>When the database is started this object is used to synch the initial storages. The storage
 * with the longest stream "wins" and the others are appended to from this longest stream.</p>
 * 
 * <p>This class is not thread-safe by itself. By default methods and constructors require
 * Write Access. get() requires Read Access. sync() and syncStrong() that can be called 
 * from any thread.</p>
 * 
 * @author Frans Lundberg
 */
public class StorageManager implements AppendOnlyStream {
    //
    // Note for developers. There is no point implementing finalize() with "stop()" in hope that 
    // BufferedStream thread would stop. This does not work since those threads have 
    // a reference to MyStorage (BufferedStream.setListener()) which have an implicit reference
    // to StorageManager (non-static inner class).
    //
    // Note the use of CAS - compare and swap on the reference to 'internal'.
    // Data stored in 'internal' changes seldom compared to number of times it is read.
    //
    
    public static final int DEFAULT_REPLICA_BUFFER_SIZE = 20 * 1000000;
    public static final int DEFAULT_REPLICA_BUFFER_TIME = 2 * 1000;
    public static final int DEFAULT_BUFFER_SIZE = 10 * 1000000;
    /**
     * The main stream's buffer time in ms. 20 since 2026-10-20 (bergdb item 005-13): 100 was
     * chosen for rotating drives; on an SSD a sync after a commit then waited about 120 ms, and
     * a shorter time costs no throughput of writers that do not sync.
     */
    public static final int DEFAULT_BUFFER_TIME = 20;
    
    private final AtomicReference<Internal> internal;
    private final Object writeLock;
    private final AppendOnlyStream mainStream;
    private long streamLength;
        // The length of this AppendOnlyStream based on all bytes appended with append().
    
    // Durability rule D1, access d1Size protected by d1Lock.
    // d1Lock is used to publish changes of d1Size (d1Lock.notifyAll()).
    private long d1Size;
    private final Object d1Lock = new Object();
    
    // Durability rule D2, access to d2Size protected by d2Lock.
    // d2Lock is used to publish changes of d2Size (d2Lock.notifyAll()).
    private long d2Size;
    private final Object d2Lock = new Object();
    private volatile boolean isSynched = false;

    /**
     * Creates a new object based on the supplied builder object.
     * Streams that are not already a BufferedStream are wrapped with a BufferedStream.
     */
    @SuppressWarnings("resource")
    private StorageManager(Builder builder) {
        if (builder.streams.size() == 0) {
            throw new IllegalArgumentException("No streams set.");
        }
        
        if (builder.writeLock == null) {
            throw new Bug("writeLock == null");
        }
        
        Internal in = new Internal();
        
        this.writeLock = builder.writeLock;
        in.streams = new BufferedStream[builder.streams.size()];
        in.storages = new StorageInfo[in.streams.length];
        
        for (int i = 0; i < in.streams.length; i++) {
            Builder.StreamInfo info = builder.streams.get(i);
            AppendOnlyStream stream = info.stream;
            BufferedStream buffered;
            
            buffered = new BufferedStream(stream, info.bufferSize, info.bufferTime);
            buffered.start();
            
            in.streams[i] = buffered;
            
            StorageInfo storage = new MyStorage(in.streams[i], info.name);
            if (storage.getConfirmedLength() != in.streams[i].getLength()) {
                throw new IllegalArgumentException("Bad state of storages[" + i + "]");
            }
            
            in.storages[i] = storage;     
        }
        
        this.mainStream = in.streams[0];
        
        in.d1 = new MainConfirmedRule();
        in.d2 = new OneActiveReplicaRule();
        in.errorRule = new MainErrorRule();
        in.hasError = false;
        
        this.internal = new AtomicReference<Internal>();
        this.internal.set(in);
            // Publishes constructor writes to readers calling internal.get().
    }
    
    public void stop() {
        closeInner(false);
    }
    
    public void close() {
        closeInner(true);
    }
    
    private void closeInner(boolean close) {
        Internal in;
        Internal newIn;
        
        in = internal.get();
            
        if (!in.hasError) {
            newIn = in.copy();
            newIn.hasError = true;
            newIn.errorString = "Storage is closing.";
            
            internal.set(newIn);
            in = newIn;
        }
        
        for (int i = 0; i < in.streams.length; i++) {
            BufferedStream b = in.streams[i];
            if (b != null && close) {
                try {
                    b.close();
                } catch (IOException e) {
                    // Empty. NOTE We could issue warning.
                }
            }
            
            if (b != null && !close) {
                b.stop();
            }
            
            StorageInfo storage = in.storages[i];
            if (storage instanceof SynchingStorage) {
                SynchingStorage ss = (SynchingStorage) storage;
                ss.signalStopSync();
            }
        }
    }

    private void setError(String message) {
        // If error already set, this error is discarded.
        // Optimistic concurrency control used.
        
        assert message != null;
        
        while (true) {
            Internal in0 = internal.get();
            if (in0.hasError) {
                assert in0.errorString != null;
                break;
            }
            Internal in1 = in0.copy();
            in1.errorString = message;
            in1.hasError = true;
            if (internal.compareAndSet(in0, in1)) {
                break;
            }
        }
    }
    
    /**
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws BadReplicaException  If a replica has an ID that does not equal the database ID.
     */
    public void checkStreamIds() {
        Internal in = internal.get();

        if (in.streams.length == 1) {
            // If no replicas, there is nothing to check.
            return;
        }
        
        if (in.streams[0].getLength() == 0) {
            // If empty main stream, we have an empty database, nothing to check.
            return;
        }
        
        byte[] mainId = readId(in.streams[0]);
        if (mainId == null) {
            throw new StreamFormatException("No valid meta block could be read from main stream '" 
                    + in.storages[0].getName() + ".");
        }
        
        for (int i = 1; i < in.streams.length; i++) {
            AppendOnlyStream stream = in.streams[i];
            
            if (stream.getLength() > 0) {
                byte[] replicaId = readId(stream);
                if (replicaId == null) {
                    throw new BadReplicaException("Could not read valid meta block from replica '" 
                            + in.storages[i].getName() + "'.");
                }
                                        
                if (!Util.areEqual(mainId, replicaId)) {
                    throw new BadReplicaException("ID of replica stream (" + StringUtil.toHex(replicaId)
                            + ") does not match database ID (" + StringUtil.toHex(mainId) + ").");
                }
            }
        }
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    private byte[] readId(AppendOnlyStream aos) {
        RecoverableStream rStream = new RecoverableStream(aos, new MetaBlock());
        MetaBlock meta = rStream.readLastValidMetaBlock();
        return meta == null ? null : meta.getId();
    }
    
    /**
     * Syncs main stream from longest replica.
     * If main stream is the longest stream already (or as long as the longest replica) this
     * method does nothing.
     * 
     * @param progressListener
     * @throws IOException
     */
    private void syncMainStream() throws IOException {
        //
        // Only called from DB.reallyStart(). Both DB.writeLock and DB.readSynch should be held 
        // by caller.
        // Method has no progressListener since this operation is expected to be fast.
        // A replica should seldom be longer than main stream. If could happen, but should only
        // be for a second of data or so.
        //
        // Outline
        // * Finds longest replica stream with available data to append to main stream.
        // * Copies data from longest to main stream.
        //

        Internal in = internal.get();

        AppendOnlyStream mainStream = in.streams[0];
        int indexOfLongest = 0;
        long lengthOfLongest = mainStream.getLength();
        
        for (int i = 1; i < in.storages.length; i++) {
            AppendOnlyStream stream = in.streams[i];
            
            long length = stream.getLength();
            if (length > lengthOfLongest) {
                if (stream.getFirstPos() <= mainStream.getLength()) {
                    // If 'stream' has the required data to append to main stream:
                    lengthOfLongest = length;
                    indexOfLongest = i;
                }
            }
        }
        
        if (indexOfLongest == 0) {
            // If no replica with available data is longer than main stream:
            return;
        }
        
        AppendOnlyStream longestStream = in.streams[indexOfLongest];
        long totalBytesToWrite = longestStream.getLength() - mainStream.getLength();
        
        copyStreamData(longestStream, mainStream, new NullProgressListener(), totalBytesToWrite, 0);
    }
    
    /**
     * Synchronizes replica streams. Assumes main stream has been synced from longest replica
     * already.
     * 
     * @throws IOException 
     * @throws BadReplicaException
     */
    private void syncReplicaStreams(ProgressListener progressListener) throws IOException {
        //
        // Only called from DB.reallyStart(). Both DB.writeLock and DB.readSynch should be held by caller.
        //

        Internal in = internal.get();
        
        // seekTo() of certain non-main streams is needed. 
        // Will possibly remove left-over data from very old replicas.
        // For an empty replica, the seekTo() call will "seek" stream pointer to 'firstPos'.
        // Appending will start from there.
        
        long firstPos = mainStream.getFirstPos();

        for (int i = 1; i < in.storages.length; i++) {
            AppendOnlyStream stream = in.streams[i];
            if (stream.getLength() < firstPos) {
                stream.seekFirstPos(firstPos);
            }
        }
        
        // Computes totalBytesToWrite and checks replica state.
        
        long mainStreamLength = mainStream.getLength();
        long bytesWritten = 0;
        long totalBytesToWrite = 0;
        
        for (int i = 1; i < in.storages.length; i++) {
            AppendOnlyStream stream = in.streams[i];
            long diff = mainStreamLength - stream.getLength();
            if (diff < 0) {
                StorageInfo s = in.storages[i];
                throw new BadReplicaException("Replica '" + s.getName() + " is illegal. It's length is " 
                        + stream.getLength() + " while main stream length is " + mainStreamLength + ".");
            }
            
            totalBytesToWrite += diff;
        }
        
        // Appends to replicas
        
        for (int i = 1; i < in.storages.length; i++) {
            AppendOnlyStream destStream = in.streams[i];
            bytesWritten = copyStreamData(mainStream, destStream, progressListener,
                    totalBytesToWrite, bytesWritten);
        }
    }
    
    /**
     * Synchronizes storages based on the "longest" storage available.
     * 
     * @throws IOException
     * @throws BadReplicaException
     */
    public void syncStreams(ProgressListener progressListener) throws IOException {
        syncMainStream();
        syncReplicaStreams(progressListener);
        
        computeRules();
        this.streamLength = mainStream.getLength();
        this.isSynched = true;
        progressListener.progress(100, "Done.");
    }
    
    private long copyStreamData(AppendOnlyStream sourceStream, AppendOnlyStream destStream,
            ProgressListener progressListener, long totalBytesToWrite, long bytesWritten)
            throws IOException {
        
        long destLength = destStream.getLength();
        long sourceLength = sourceStream.getLength();
        
        assert destLength >= 0 : "destLength: " + destLength;
        assert sourceLength >= 0 : "sourceLength: " + sourceLength;
        
        long diff = sourceLength - destLength;
        
        if (diff > 0) {
            byte[] buffer = new byte[50*1000];
            
            while (diff > 0) {
                int chunkSize = diff <= buffer.length ? (int) diff : buffer.length;
                sourceStream.read(destLength, buffer, 0, chunkSize);
                destStream.append(buffer, 0, chunkSize);
                destLength += chunkSize;
                diff -= chunkSize;
                bytesWritten += chunkSize;
            }
            
            int progressValue = (int) (100.0 * bytesWritten / (double) totalBytesToWrite);
            assert progressValue >= 0;
            assert progressValue <= 100;
            progressListener.progress(progressValue, "Synched " + bytesWritten  
                    + " bytes out of " + totalBytesToWrite + " bytes.");
        }
        return bytesWritten;
    }
    
    /**
     * Evaluates the error rule, the d1 rule, and the d2 rule. hasError is set to true if there
     * is an error. d1size and d2size fields are updated as computed from the d1/d2 rules.
     */
    private void computeRules() {
        // This method is called from unsynchronized threads in BufferedStream.
       
        Internal in = internal.get();
        String error = in.errorRule.computeError(in.storages);
        if (error != null) {
            setError(error);
            return;
        }
        
        synchronized (d1Lock) {
            long size = in.d1.computeSize(in.storages);

            if (size > d1Size) {
                d1Size = size;
                d1Lock.notifyAll();
            }
            
            if (size == -1) {
                setError("d1 rule returned -1");
                return;
            }
        }
        
        synchronized (d2Lock) {
            long size = in.d2.computeSize(in.storages);
            
            // The following if statement forces d2Size <= d1Size which must always be true.
            // The body of the if statement will never run if d1/d2 rules are configured properly.
            if (size > d1Size) {
                size = d1Size;
            }
            
            if (size > d2Size) {
                d2Size = size;
                d2Lock.notifyAll();
            }
            
            if (size == -1) {
                setError("d2 rule returned -1");
                return;
            }
        }
    }
    
    public void sync(long pos) throws IOException {
        synchronized (d1Lock) {
            while (d1Size < pos) {
                Internal in = internal.get();
                if (in.hasError) {
                    assert in.errorString != null;
                    throw new IOException("StorageManager has error: " + in.errorString);
                }
                
                try {
                    d1Lock.wait(500);
                } catch (InterruptedException e) {
                    // Not an IOException of the storage, which fails the database (bergdb
                    // 005-30, Db.sync).
                    throw new InterruptedIOException("Thread was interrupted while waiting " +
                    		"for D1 size " + pos + ".");
                }
            }
        }
    }
    
    public void syncStrong(long pos) throws IOException {
        synchronized (d2Lock) {
            while (d2Size < pos) {
                Internal in = internal.get();
                if (in.hasError) {
                    assert in.errorString != null;
                    throw new IOException("StorageManager has error: " + in.errorString);
                }
                
                try {
                    d2Lock.wait(500);
                } catch (InterruptedException e) {
                    // Not an IOException of the storage (bergdb 005-30).
                    throw new InterruptedIOException("Thread was interrupted while waiting " +
                            "for D1 size " + pos + ".");
                }
            }
        }
    }
    
    private boolean hasNameAlready(Internal in, String name) {        
        for (int i = 0; i < in.storages.length; i++) {
            if (in.storages[i].getName().equals(name)) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Adds a replica while the storage manager is active; caller must call 
     * syncReplica() after calling this method. Possibly from another thread.
     * 
     * @param name  Name of the storage.
     * @param replica  Replica stream.
     * @param bufferSize  Buffer size in bytes.
     * @param bufferTime  Buffer time in ms.
     * @throws IllegalArgumentException  If a parameter is null or otherwise not allowed.
     * @throws BadReplicaException  If the replica stream is longer than the main stream; 
     * if the replica stream has a different database ID than the main stream.
     */
    public SynchingStorage addReplica(String name, AppendOnlyStream replica, 
            int bufferSize, int bufferTime) throws IOException {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("name = empty string not allowed");
        }
        
        if (replica == null) {
            throw new IllegalArgumentException("replica == null not allowed");
        }
        
        if (bufferSize < 0) {
            throw new IllegalArgumentException("bufferSize = " + bufferSize + " not allowed");
        }
        
        if (bufferSize < 100) {
            bufferSize = 100;
        }
        
        if (bufferTime < 0) {
            throw new IllegalArgumentException("Bad bufferTime, " + bufferTime + ".");
        }
        
        if (bufferTime < 10) {
            bufferTime = 10;
        }
        
        long mainLength = mainStream.getLength();
        long replicaLength = replica.getLength();
        
        if (replicaLength > mainLength) {
            throw new BadReplicaException("Replica '" + name + "' has stream length " + replicaLength 
                    + ", larger than main stream length (" + mainLength + "). Not allowed.");
        }
        
        long firstPosOfMain = mainStream.getFirstPos();
        if (replicaLength < firstPosOfMain) {
            replica.seekFirstPos(firstPosOfMain);
            replicaLength = replica.getLength();
            assert replicaLength == firstPosOfMain;
            assert replica.getFirstPos() == replicaLength;
        }

        // Optimistic concurrency control (CAS on this.internal).
        
        SynchingStorage synchingStorage;
        
        while (true) {
            Internal in = internal.get();
            if (hasNameAlready(in, name)) {
                throw new IllegalArgumentException("A storage with the name '" + name 
                        + "' already exists.");
            }
            
            StorageInfo[] newStorages = new StorageInfo[in.storages.length + 1];
            BufferedStream[] newStorageStreams = new BufferedStream[newStorages.length];
            
            System.arraycopy(in.storages, 0, newStorages, 0, in.storages.length);
            System.arraycopy(in.streams, 0, newStorageStreams, 0, in.streams.length);
            
            BufferedStream buffered = new BufferedStream(replica, bufferSize, bufferTime);
            buffered.start();
            
            MyStorage myStorage = new MyStorage(buffered, name);
            synchingStorage = new SynchingStorage(buffered, myStorage);
            newStorages[newStorages.length - 1] = synchingStorage;
            
            Internal newIn = in.copy();
            newIn.storages = newStorages;
            newIn.streams = newStorageStreams;
            
            if (internal.compareAndSet(in, newIn)) {
                break;
            } else {
                try {
                    buffered.close();
                } catch (IOException e) {
                    // Empty. NOTE We could issue warning.
                }
            }
        }
        
        return synchingStorage;
    }
    
    public void syncReplica(SynchingStorage synchingStorage, ProgressListener progressListener) {
        synchingStorage.sync(progressListener);
    }
    
    /**
     * Removes the replica with the given name if it exists, otherwise
     * this method does nothing.
     * 
     * @param name  Name of replica stream.
     */
    public void removeReplica(String name) {        
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        Internal in;
        int removeIndex = -1;
        
        // Optimistic concurrency control based on internal.compareAndSet().
        
        A: while (true) {
            in = internal.get();
            
            for (int i = 1; i < in.storages.length; i++) {
                StorageInfo storage = in.storages[i];
                
                if (storage.getName().equals(name)) {
                    removeIndex = i;
                    Internal newIn = in.copy();
                    newIn.storages = new StorageInfo[in.storages.length - 1];
                    newIn.streams = new BufferedStream[in.storages.length - 1];
                    
                    int index = 0;
                    for (int j = 0; j < in.storages.length; j++) {
                        if (j != i) {
                            newIn.storages[index] = in.storages[j];
                            newIn.streams[index] = in.streams[j];
                            index++;
                        }
                    }
                    
                    if (internal.compareAndSet(in, newIn)) {
                        break A;
                    } else {
                        continue A;
                    }
                }
            }
            
            // name not found.
            break;
        }
        
        if (removeIndex != -1) {
            BufferedStream b = in.streams[removeIndex];
            b.stop();       // Note, we call stop(), no flushing in calling thread.
        }
    }

    /**
     * Returns the stream length based on all bytes received (append()) by this object.
     * Caller must have Write Access.
     */
    public long getLength() {
        return streamLength;
    }
    
    /**
     * Caller must have WriteAccess.
     */
    /** The stream length that has ordinary durability (D1), as sync() waits for. */
    public long getDurableLength() {
        synchronized (d1Lock) {
            return d1Size;
        }
    }
    
    public long getFirstPos() {
        return mainStream.getFirstPos();
    }

    /**
     * Reads from the storage.
     * Caller must have Read Access.
     */
    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        //
        // Note: We could have multiple mains and scale out the reads between them.
        // Note: We could implement fail-over from one main storage to another in case one 
        //   becomes faulty. This can be accomplished by underlying file system however.
        //
        // Synch note: Read can be called from concurrent threads.
        // Synch note: If an error occurs, the caller acquires Write Access
        // by acquiring the writeLock. The performance penalty is neglectable
        // since it should happen rarely.
        //
        // The only synch of readers is the volatile read of hasError. 
        // Should not limit performance. However, since this field is set
        // from threads that have either Read Access or Write Access, we could
        // avoid using volatile. hasError is set by a thread with Write Access
        // and the change of the field is published with: [synchronized(readSynch) {}].
        // Since caller must have Read Access it should have done readSynch recently.
        
        Internal in = internal.get();
        if (in.hasError) {
            throw new IOException(in.errorString);
        }
        
        try {
            mainStream.read(position, dest, destOffset, length);
        } catch (ReadBelowFirstPosException e) {
            // 2026-10-13 (docs/levels.md, W1): a read admitted before a cut
            // that reached bytes the cut removed. That read fails; the stream is not faulty,
            // so it is not closed and the storage does not get an error state.
            throw e;
        } catch (IOException e) {
            handleStreamException(mainStream, e);
            throw e;
        }
    }
    
    private void handleStreamException(AppendOnlyStream stream, IOException e) {
        // computeRules() is called since the data available to the rules
        // have been changed.
        // Optimistic concurrency control with CAS on this.internal.
        
        A: while (true) {
            Internal in = internal.get();
            boolean found = false;
            
            for (int i = 0; i < in.streams.length; i++) {
                if (in.streams[i] == stream) {
                    found = true;
                    Internal newIn = in.copy();
                    
                    try {
                        stream.close();
                    } catch (IOException e1) {
                        // Empty. NOTE We could issue a warning.
                    }
                    
                    newIn.streams[i] = null;
                    newIn.storages[i] = new ErrorStorage(in.storages[i].getName(), e.toString());
                    
                    if (internal.compareAndSet(in, newIn)) {
                        break A;
                    }
                }
            }
            
            if (!found) {
                break;      // Already handled, or not one of in.streams.
            }
        }
    
        computeRules();
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final void append(byte[] source, int sourceOffset, int length) throws IOException {
        Internal in = internal.get();
        
        if (in.hasError) {
            assert in.errorString != null;
            throw new IOException(in.errorString);
        } else if (!isSynched) {
            throw new IllegalStateException("Storage manager not synched, call synch().");
        }
        
        try {
            mainStream.append(source, sourceOffset, length);
        } catch (IOException e) {
            // An exception when appending to main is always an error.
            
            handleStreamException(mainStream, e);
            throw e;
        }
        
        for (int i = 1; i < in.storages.length; i++) {
            StorageInfo s = in.storages[i];
            if (s.getStatus() == StorageInfo.STATUS_ACTIVE) {
                try {
                    AppendOnlyStream stream = in.streams[i];
                    assert stream != null : "in.streams[i] is null, i = " + i + ", s = " + s.toString();
                    stream.append(source, sourceOffset, length);
                } catch (IOException e) {
                    // Exception not automatically rethrown here. 
                    // Possibly, we want to continue running.
                    
                    handleStreamException(in.streams[i], e);
                    
                    Internal in2 = internal.get();
                    if (in2.hasError) {
                        throw new IOException(in2.errorString);
                    }
                }
            }
        }
        
        this.streamLength += length;
    }

    public void pretruncate(long position) throws IOException {
        Internal in = internal.get();
        
        if (in.hasError) {
            throw new IOException(in.errorString);
        }
        
        final AppendOnlyStream[] myStreams = in.streams;
        
        for (AppendOnlyStream s: myStreams) {
            s.pretruncate(position);
        }
    }
    
    public void seekFirstPos(long position) {
        throw new UnsupportedOperationException();
    }
    
    public StorageInfo[] getStorageInfos() {
        Internal in = internal.get();
        return in.storages.clone();
    }
    
    public StorageInfo getStorageInfo(String name) {
        StorageInfo result = null;
        
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        Internal in = internal.get();
        
        for (int i = 0; i < in.storages.length; i++) {
            StorageInfo s = in.storages[i];
            assert s != null : "s is null, i = " + i;
            assert s.getName() != null : "s.getName() is null";
            if (s.getName().equals(name)) {
                result = s;
                break;
            }
        }
        
        return result;
    }
    
    /**
     * Sets durability rule D2.
     */
    public void setD2(DurabilityRule d2) {
        if (d2 == null) {
            throw new IllegalArgumentException("d2 == null not allowed");
        }
        
        // Optimistic locking based on internal.compareAndSet().
        while (true) {
            Internal in = internal.get();
            Internal newIn = in.copy();
            newIn.d2 = d2;
            if (internal.compareAndSet(in, newIn)) {
                break;
            }
        }
    }
    
    public AppendOnlyStream getMainStream() {
        return mainStream;
    }
    
    /**
     * Builds a DBStorageManager.
     */
    public static class Builder {
        private Object writeLock;
        private ArrayList<StreamInfo> streams;
        private HashSet<String> nameSet;
        
        public Builder(Object writeLock) {
            if (writeLock == null) {
                throw new IllegalArgumentException("writeLock == null not allowed");
            }
            
            streams = new ArrayList<StreamInfo>();
            nameSet = new HashSet<String>();
            this.writeLock = writeLock;
        }
        
        public Builder stream(String name, AppendOnlyStream stream) {
            if (name == null) {
                throw new IllegalArgumentException("name == null not allowed");
            }
            
            if (name.length() == 0) {
                throw new IllegalArgumentException("name = empty string not allowed");
            }
            
            if (stream == null) {
                throw new IllegalArgumentException("stream == null not allowed");
            }
            
            if (nameSet.contains(name)) {
                throw new IllegalArgumentException("Stream name '" + name + "' already exists.");
            }
            
            if (stream instanceof BufferedStream) {
                throw new IllegalArgumentException("'stream' is BufferedStream; not allowed.");
            }
            
            nameSet.add(name);
            StreamInfo info = new StreamInfo();
            info.name = name;
            info.stream = stream;
            info.bufferSize = DEFAULT_BUFFER_SIZE;
            info.bufferTime = DEFAULT_BUFFER_TIME;
            streams.add(info);
            
            return this;
        }
        
        public Builder stream(String name, AppendOnlyStream stream, int bufferSize, int bufferTime) {
            if (name == null) {
                throw new IllegalArgumentException("name == null not allowed");
            }
            
            if (name.length() == 0) {
                throw new IllegalArgumentException("name = empty string not allowed");
            }
            
            if (stream == null) {
                throw new IllegalArgumentException("stream == null not allowed");
            }
            
            if (nameSet.contains(name)) {
                throw new IllegalArgumentException("Stream name '" + name + "' already exists.");
            }
            
            if (stream instanceof BufferedStream) {
                throw new IllegalArgumentException("'stream' is BufferedStream; not allowed.");
            }
            
            nameSet.add(name);
            StreamInfo info = new StreamInfo();
            info.name = name;
            info.stream = stream;
            info.bufferSize = bufferSize;
            info.bufferTime = bufferTime;
            streams.add(info);
            
            return this;
        }
        
        public StorageManager build() {
            if (streams.size() == 0) {
                throw new IllegalArgumentException("no streams");
            }
            
            return new StorageManager(this);
        }
        
        private static class StreamInfo {
            String name;
            AppendOnlyStream stream;
            int bufferSize;
            int bufferTime;
        }
    }
    
    /**
     * Internal data. Object used to be able to atomically change state
     * without expensive locking.
     */
    private static class Internal {
        BufferedStream[] streams;
        StorageInfo[] storages;
        DurabilityRule d1;
        DurabilityRule d2;
        ErrorRule errorRule;
        boolean hasError;
        public String errorString;
        
        Internal copy() {
            Internal copy = new Internal();
            copy.streams = streams.clone();
            copy.storages = storages.clone();
            copy.d1 = d1;
            copy.d2 = d2;
            copy.errorRule = errorRule;
            copy.hasError = hasError;
            return copy;
        }
    }
    
    private class MyStorage implements StorageInfo {
        private final String name;
        private final AtomicLong confirmedLength = new AtomicLong();
        
        public MyStorage(final BufferedStream stream, String name) {
            this.name = name;
            this.confirmedLength.set(stream.getLength());
            stream.setAppendListener(new AppendListener() {
                public void dataAppended(long postStreamSize) {
                    confirmedLength.set(postStreamSize);
                    computeRules();
                }
                
                public void appendFailed(IOException e) {
                    handleStreamException(stream, e);
                }
            });
        }

        public String getName() {
            return name;
        }

        public int getStatus() {
            return StorageInfo.STATUS_ACTIVE;
        }

        public String getStatusString() {
            return "ok";
        }

        public long getConfirmedLength() {
            return confirmedLength.get();
        }
        
        public String toString() {
            return name + " STATUS_ACTIVE";
        }
    }
    
    public class SynchingStorage implements StorageInfo {
        private final MyStorage myStorage;
        private volatile String statusString;
        private final BufferedStream replicaStream;
        private volatile boolean stopSync = false;
        
        public SynchingStorage(BufferedStream replicaStream, MyStorage myStorage) {
            this.myStorage = myStorage;
            this.replicaStream = replicaStream;
            this.statusString = "Synchronizing replica stream.";
        }

        public String getName() {
            return myStorage.getName();
        }

        public synchronized int getStatus() {
            return StorageInfo.STATUS_INITIALIZING;
        }

        public synchronized String getStatusString() {
            return statusString;
        }

        public long getConfirmedLength() {
            // Should it be supported?
            throw new UnsupportedOperationException();
        }
        
        public String toString() {
            return "SynchingStorage " + getName() + ", " + getStatusString();
        }
        
        /**
         * Signals to the synch method (sync()) that it should stop. 
         * This method does not wait until the thread calling sync() has actually stopped; 
         * it returns immediately.
         */
        public synchronized void signalStopSync() {
            this.stopSync = true;
        }
        
        public void sync(ProgressListener progressListener) {
            final byte[] buffer = new byte[50 * 1000];
            long mainLength;
            long replicaLength;
            long diff;
            long totalDiff = 0;
            boolean firstTime = true;
            IOException ioException = null;
            
            progressListener.progress(0, "Starting to sync replica '" + myStorage.getName() + "'.");
            
            try {
                A: while (true) {
                    if (stopSync) {
                        throw new IOException("Synch thread stopped.");
                    }
                    
                    synchronized (writeLock) {
                        mainLength = mainStream.getLength();
                        replicaLength = replicaStream.getLength();
                        diff = mainLength - replicaLength;
                        
                        if (firstTime) {
                            totalDiff = diff;
                            firstTime = false;
                        }
                        
                        totalDiff = totalDiff == 0 ? 1 : totalDiff;
                        int progressValue = 100 - (int)(diff * 100 / totalDiff);
                        progressValue = progressValue < 0 ? 0 : progressValue;
                        progressListener.progress(progressValue, "Synching storage '" 
                                + myStorage.getName() + "', " + diff + " bytes left.");
                        
                        statusString = "Synching, " + diff + " bytes left.";
                        
                        if (diff < buffer.length) {
                            // If diff is small enough, write the last bytes
                            // to replica, then replace SynchingStorage with MyStorage.
                            // Do this while synched on DB.writeLock.
                            
                            copy(replicaLength, (int) diff, buffer);
                            makeActive();
                            break A;
                        }
                    }
                    
                    int bytesToCopy = diff <= buffer.length ? (int) diff : buffer.length;
                    copy(replicaLength, bytesToCopy, buffer);
                }
            } catch (IOException e) {
                ioException = e;
                StorageManager.this.handleStreamException(replicaStream, e);
            }
            
            String note = ioException == null ? "Success." : "Error: " + ioException.getMessage();
            progressListener.progress(100, note);
        }
        
        private void copy(long startPos, int bytesToCopy, byte[] buffer) throws IOException {
            if (bytesToCopy > buffer.length || bytesToCopy < 0) {
                throw new Bug("Unexpected, " + bytesToCopy + ", " + buffer.length);
            }
            
            mainStream.read(startPos, buffer, 0, bytesToCopy);
            replicaStream.append(buffer, 0, bytesToCopy);
            
        }
        
        /**
         * Makes the synching stream active; actually replacing the
         * SynchingStorage with a MyStorage based on the same underlying
         * stream.
         */
        private void makeActive() {
            
            // Optimistic concurrency control using internal.compareAndSet().
            while (true) {
                Internal in = internal.get();
                Internal newIn = in.copy();
                
                for (int i = 0; i < in.storages.length; i++) {
                    StorageInfo s = in.storages[i];
                    if (s == this) {
                        newIn.storages[i] = this.myStorage;
                        newIn.streams[i] = this.replicaStream;
                    }
                }
                
                if (internal.compareAndSet(in, newIn)) {
                    break;
                }
            }
        }
    }
    
    private class ErrorStorage implements StorageInfo {
        private final String name;
        private final String errorMessage;
        
        public ErrorStorage(String name, String errorMessage) {
            this.errorMessage = errorMessage;
            this.name = name;
        }

        public String getName() {
            return name;
        }

        public int getStatus() {
            return StorageInfo.STATUS_ERROR;
        }

        public String getStatusString() {
            return errorMessage;
        }

        public long getConfirmedLength() {
            throw new IllegalStateException("Cannot get size of error stream.");
        }
        
        public String toString() {
            return name + " STATUS_ERROR";
        }
    }
}

/*

Dependencies
============

130411 Frans. This class depends on lower-level classes: BufferedStream, AppendOnlyStream.
Also on: pub.BadReplicaException, pub.StorageInfo. No dependencies on Db or RecoverableStream.
This class forms a layer: "Storage Layer". The Core Layer uses StorageManager and only that
(except for when building Db).


Sync notes
==========

1302 Frans: An object of this class is accessed by a number of different
types of concurrent threads.

* Readers. 
    Read threads calling read(). These threads run in parallel and has
    DB.get()/getMany() in the call stack.
    Readers always read from mainStream which is final.
    Writes: error.
* Writer.
    Write threads execute one at a time. They share the common DB.writeLock.
    The writer calls the constructor, getSize, append, and more.
    Writes: error, append.
* WaitForSync.
    Threads waiting until a particular spos has been confirmed to be durable.
    These are user threads with no particular synchronization.
    They synchronize on d1Lock/d2Lock while they wait for a change in 
    d1Size/d2Size. These threads call sync()/syncStrong().
    Writes: none.
* Buffer threads.
    These threads are started by BufferedStream. They will asynchronously
    call computeRules to recompute the rules (determine possible error
    condition, d1Size, d2Size) once a stream has a new confirmed size.
    WaitForSync threads may be waiting for dXSize to increase and they will
    be notified of changes.
    We could synch on DB.writeLock. At max load, we typically have 
    hundreds of transactions per append (because of BufferedStream),
    so this could be OK performance-wise.
    We could synch on a special ruleLock object too. Having multiple
    concurrent rule computations seems problematic. 
    Writes: error flag, d1Size, d2Size.
* Thread that changes rules. No synch requirements on thread.
    Writes: d1, d2, errorRule.
* Thread that adds or removes a replica. No synch requirements.
    Writes: streams, storages.

*/