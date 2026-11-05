package bergdb.storage;

import java.io.IOException;
import java.io.InterruptedIOException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * <p>The storage of a database: its one stream, the main storage, behind a BufferedStream,
 * and the durable length that the syncs wait for (rule D1, the main stream's confirmed
 * length: written and, with a file storage, forced).</p>
 * 
 * <p>Until 2026-11-04 it also held replicas: other streams, each behind a BufferedStream of
 * its own, that every append was written to; a second rule, D2, for SyncLevel.ORDINARY (the
 * main and one replica); the copying between the streams at startup ("the longest stream
 * wins"); and replicas added and removed while the database ran. Replication was removed
 * at Frans's decision (bergdb 005-11, options A and C2: copies are left to the OS and the
 * file system); the design as it was is described in bergdb 017-03.</p>
 * 
 * <p>This class is not thread-safe by itself. By default methods and constructors require
 * Write Access. get() requires Read Access. sync() can be called from any thread.</p>
 * 
 * @author Frans Lundberg
 */
public class StorageManager implements AppendOnlyStream {
    //
    // Note for developers. There is no point implementing finalize() with "stop()" in hope that 
    // BufferedStream thread would stop. This does not work since those threads have 
    // a reference to the append listener (BufferedStream.setAppendListener()), which has an
    // implicit reference to StorageManager (an anonymous inner class).
    //
    
    public static final int DEFAULT_BUFFER_SIZE = 10 * 1000000;
    /**
     * The main stream's buffer time in ms. 100 until 2026-10-20, chosen for rotating drives;
     * 20 until 2026-10-29 (bergdb item 005-13): on an SSD a sync after a commit waited about
     * 120 ms at 100. Since 2026-10-27 (bergdb item 005-48) a sync does not wait for it: a
     * waiting sync has the buffer written at once (BufferedStream.flushSoon). The buffer time
     * is the longest time that bytes nobody syncs on stay in the buffer. 50 since 2026-10-29
     * (bergdb item 005-64): writers that do not sync get 11 to 35 percent fewer forces than at
     * 20, so fewer rewrites of the stream's last page, with the same throughput and latency;
     * syncs are unchanged. For bytes nobody synced, a power loss can take the writes of about
     * 1.1 to 2 buffer times (four waits of bufferTime / 4 and two forces; about 82 ms of writes
     * on macOS), fewer at high rates, where a quarter of the buffer starts a flush, and never
     * more than the buffer.
     */
    public static final int DEFAULT_BUFFER_TIME = 50;
    
    private final BufferedStream mainStream;
    private long streamLength;
        // The length of this AppendOnlyStream based on all bytes appended with append().
    
    // Durability rule D1, access d1Size protected by d1Lock.
    // d1Lock is used to publish changes of d1Size (d1Lock.notifyAll()).
    private long d1Size;
    private final Object d1Lock = new Object();
    
    /** The main stream's confirmed length, as its BufferedStream reports it. */
    private final AtomicLong confirmedLength = new AtomicLong();
    
    /**
     * Null while the storage works; else the error, set once: the main stream failed
     * (handleStreamException), or the storage is closing. Then every later append, read and
     * sync that has to wait throws.
     */
    private final AtomicReference<String> error = new AtomicReference<String>();
    
    /** Set once, by the first handleStreamException, which closes the main stream. */
    private final AtomicBoolean mainFailing = new AtomicBoolean();
    
    /** The main stream's failure, once the error is set, else null; see hasFailed(). */
    private volatile IOException mainFailure = null;
    
    private volatile boolean isStarted = false;

    /**
     * Creates a new object based on the supplied builder object.
     * The stream is wrapped with a BufferedStream.
     */
    @SuppressWarnings("resource")
    private StorageManager(Builder builder) {
        if (builder.stream == null) {
            throw new IllegalArgumentException("No stream set.");
        }
        
        final BufferedStream buffered = new BufferedStream(builder.stream, builder.bufferSize,
                builder.bufferTime);
        buffered.start();
        this.mainStream = buffered;
        
        this.confirmedLength.set(buffered.getLength());
        buffered.setAppendListener(new AppendListener() {
            public void dataAppended(long postStreamSize) {
                confirmedLength.set(postStreamSize);
                computeRules();
            }
            
            public void appendFailed(IOException e) {
                handleStreamException(e);
            }
        });
    }
    
    public void stop() {
        closeInner(false);
    }
    
    public void close() {
        closeInner(true);
    }
    
    /**
     * As close(), and throws the first failure of a stream's close, such as a flush that
     * failed (2026-10-24, bergdb 005-32): for a start that throws, which adds it to its own.
     */
    public void closeAndThrow() throws IOException {
        IOException e = closeInner(true);
        if (e != null) {
            throw e;
        }
    }
    
    /** Returns the first failure of the stream's close, or null. */
    private IOException closeInner(boolean close) {
        IOException first = null;
        
        error.compareAndSet(null, "Storage is closing.");
        
        if (!mainFailing.get()) {
            // A failed main stream was closed by handleStreamException.
            if (close) {
                try {
                    mainStream.close();
                } catch (IOException e) {
                    // NOTE We could issue warning.
                    first = e;
                }
            } else {
                mainStream.stop();
            }
        }
        return first;
    }

    private void setError(String message) {
        // If error already set, this error is discarded.
        assert message != null;
        error.compareAndSet(null, message);
    }
    
    /**
     * Makes the storage ready for appends, at startup, before recovery (Db.start): its
     * length is the main stream's, and so is its durable length. Until 2026-11-04 (bergdb
     * 005-11) the startup here first checked the database ID of each replica and copied the
     * longest stream's bytes onto the others.
     */
    public void start() {
        computeRules();
        this.streamLength = mainStream.getLength();
        this.isStarted = true;
    }
    
    /**
     * Evaluates rule D1: d1Size becomes the main stream's confirmed length, unless the
     * storage has an error.
     */
    private void computeRules() {
        // This method is called from unsynchronized threads in BufferedStream.
        
        if (error.get() != null) {
            return;
        }
        
        synchronized (d1Lock) {
            long size = confirmedLength.get();
            if (size > d1Size) {
                d1Size = size;
                d1Lock.notifyAll();
            }
        }
    }
    
    /**
     * Waits until the durable length of rule D1 is at least 'length': every byte before that
     * position is durable. A transaction is durable when its last byte is, so a sync of it
     * waits for its lastPos + 1 (bergdb 005-44).
     * 
     * <p>If it must wait, it has the main stream write what is buffered at once
     * (BufferedStream.flushSoon), and waits for that write and its force, not for the
     * buffer time; syncs that wait at the same time share one write and one force (group
     * commit, 2026-10-27, bergdb 005-48).</p>
     */
    public void sync(long length) throws IOException {
        synchronized (d1Lock) {
            while (d1Size < length) {
                String e0 = error.get();
                if (e0 != null) {
                    throw new IOException("StorageManager has error: " + e0);
                }
                
                mainStream.flushSoon(length);   // Group commit (bergdb 005-48).
                try {
                    d1Lock.wait(500);
                } catch (InterruptedException e) {
                    // Not an IOException of the storage, which fails the database (bergdb
                    // 005-30, Db.sync). The interrupt flag is set again (bergdb 005-46).
                    Thread.currentThread().interrupt();
                    throw new InterruptedIOException("Thread was interrupted while waiting " +
                    		"for D1 size " + length + ".");
                }
            }
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
     * The stream length that has ordinary durability (D1), as sync() waits for. Caller must
     * have WriteAccess.
     */
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
     * <p>A read past the end (EOFException) fails the storage, and so the database, as any
     * IOException of the main stream does: the database reads only at positions it got from
     * the stream, so such a read means corrupt data or a bug, and the database then stops
     * (bergdb 018-02). A read below the first position, which a cut overtook, does not: its
     * ReadBelowFirstPosException leaves the storage as it was.</p>
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
        // The only synch of readers is the volatile read of the error. 
        // Should not limit performance. However, since this field is set
        // from threads that have either Read Access or Write Access, we could
        // avoid using volatile. The error is set by a thread with Write Access
        // and the change of the field is published with: [synchronized(readSynch) {}].
        // Since caller must have Read Access it should have done readSynch recently.
        
        String e0 = error.get();
        if (e0 != null) {
            throw new IOException(e0);
        }
        
        try {
            mainStream.read(position, dest, destOffset, length);
        } catch (ReadBelowFirstPosException e) {
            // 2026-10-13 (bergdb 011-04, W1): a read admitted before a cut
            // that reached bytes the cut removed. That read fails; the stream is not faulty,
            // so it is not closed and the storage does not get an error state.
            throw e;
        } catch (IOException e) {
            handleStreamException(e);
            throw e;
        }
    }
    
    /**
     * The main stream failed: the storage gets its error, and the stream is closed, once.
     * The error comes first (2026-11-05, bergdb 015-81): an unchecked exception of the close
     * left here before it, and ended the storage thread, so a sync waited for ever and the
     * database ran on. What the close throws is kept with 'e', as suppressed.
     */
    private void handleStreamException(IOException e) {
        if (!mainFailing.compareAndSet(false, true)) {
            return;     // Already handled.
        }
        
        setError("Main storage not active. " + e.toString());
        mainFailure = e;
        
        try {
            mainStream.close();
        } catch (IOException | RuntimeException | Error e1) {
            if (e1 != e) {      // BufferedStream.close() throws a failed flush's 'e' again.
                e.addSuppressed(e1);
            }
        }
    }
    
    /**
     * True when the main stream has failed: an append, a read or a flush of it threw an
     * IOException, the stream is closed (or being closed, by handleStreamException), and
     * every later append, read and waiting sync throws. Not after a close alone.
     */
    public boolean hasFailed() {
        return mainFailure != null;
    }
    
    /**
     * What failed the main stream, as hasFailed() says, else null: the IOException of its
     * append, read or flush. The database fails with it at its next call (Db, bergdb 015-35).
     */
    public IOException getFailure() {
        return mainFailure;
    }

    /**
     * Caller must hold DB.writeLock.
     */
    public final void append(byte[] source, int sourceOffset, int length) throws IOException {
        String e0 = error.get();
        
        if (e0 != null) {
            throw new IOException(e0);
        } else if (!isStarted) {
            throw new IllegalStateException("Storage manager not started, call start().");
        } else if (length < 0) {
            // Refused before anything changes (2026-11-05, bergdb 015-79): the length was
            // lowered by it. Not an IOException, so the storage does not fail.
            throw new IllegalArgumentException("negative length, " + length);
        }
        
        try {
            mainStream.append(source, sourceOffset, length);
        } catch (IOException e) {
            // An exception when appending to main is always an error.
            
            handleStreamException(e);
            throw e;
        }
        
        this.streamLength += length;
    }

    public void pretruncate(long position) throws IOException {
        String e0 = error.get();
        
        if (e0 != null) {
            throw new IOException(e0);
        }
        
        mainStream.pretruncate(position);
    }
    
    public AppendOnlyStream getMainStream() {
        return mainStream;
    }
    
    /**
     * Builds a StorageManager.
     */
    public static class Builder {
        private AppendOnlyStream stream;
        private int bufferSize;
        private int bufferTime;
        
        public Builder() {
        }
        
        /** Sets the stream, with the default buffer size and time. */
        public Builder stream(AppendOnlyStream stream) {
            return stream(stream, DEFAULT_BUFFER_SIZE, DEFAULT_BUFFER_TIME);
        }
        
        /**
         * Sets the stream, with the given buffer size in bytes and buffer time in ms. One
         * stream: since 2026-11-04 (bergdb 005-11) a second one, then a replica, is refused.
         */
        public Builder stream(AppendOnlyStream stream, int bufferSize, int bufferTime) {
            if (stream == null) {
                throw new IllegalArgumentException("stream == null not allowed");
            }
            
            if (this.stream != null) {
                throw new IllegalStateException("A stream is set already; a database has one "
                        + "stream (bergdb 005-11).");
            }
            
            if (stream instanceof BufferedStream) {
                throw new IllegalArgumentException("'stream' is BufferedStream; not allowed.");
            }
            
            this.stream = stream;
            this.bufferSize = bufferSize;
            this.bufferTime = bufferTime;
            
            return this;
        }
        
        public StorageManager build() {
            if (stream == null) {
                throw new IllegalArgumentException("no stream");
            }
            
            return new StorageManager(this);
        }
    }
}

/*

Dependencies
============

130411 Frans. This class depends on lower-level classes: BufferedStream, AppendOnlyStream.
No dependencies on Db or RecoverableStream. (Until 2026-11-04, bergdb 005-11, also on
pub.BadReplicaException and pub.StorageInfo, for the replicas.)
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
    They synchronize on d1Lock while they wait for a change in 
    d1Size. These threads call sync().
    Writes: none.
* Buffer threads.
    These threads are started by BufferedStream. They will asynchronously
    call computeRules to recompute the rule (d1Size) once the stream has a new
    confirmed size, or handleStreamException when a flush failed.
    WaitForSync threads may be waiting for d1Size to increase and they will
    be notified of changes.
    We could synch on DB.writeLock. At max load, we typically have 
    hundreds of transactions per append (because of BufferedStream),
    so this could be OK performance-wise.
    We could synch on a special ruleLock object too. Having multiple
    concurrent rule computations seems problematic. 
    Writes: error, d1Size.

*/