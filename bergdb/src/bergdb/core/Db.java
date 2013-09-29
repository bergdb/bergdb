package bergdb.core;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.Bug;
import bergdb.common.IWarner;
import bergdb.common.NullProgressListener;
import bergdb.common.ProgressListener;
import bergdb.common.Util;
import bergdb.core.GetMany.StopCondition;
import bergdb.coreds.Choices;
import bergdb.coreds.EvictData;
import bergdb.coreds.GetData;
import bergdb.coreds.INode;
import bergdb.coreds.KeyAccessPath;
import bergdb.coreds.KeyNode;
import bergdb.coreds.Keys;
import bergdb.coreds.Klong;
import bergdb.coreds.KlongWithPointer;
import bergdb.coreds.Pointer;
import bergdb.coreds.Spos;
import bergdb.coreds.TopAccessPath;
import bergdb.coreds.TopDs;
import bergdb.coreds.TopNode;
import bergdb.coreds.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.pub.BadReplicaException;
import bergdb.pub.Clock;
import bergdb.pub.IllegalDbStateException;
import bergdb.pub.Job;
import bergdb.pub.JobStatus;
import bergdb.pub.LookupTimeNotAvailableException;
import bergdb.pub.StorageInfo;
import bergdb.storage.BufferedStream;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * <p>
 * An object of this class provides access to the data in the database. This
 * class is the internal DB implementation; it should not be used directly by
 * end users unless they really need the absolutely highest performance. This
 * class implements the <i>Core Layer</i>, see below. Also this class works as a
 * central delegator object for the database application (and as a class-for-me
 * class).
 * <p>
 * <p>
 * The API of the <i>Core Layer</i> consists of the methods:
 * </p>
 * <ul>
 * <li>get()</li>
 * <li>getMany()</li>
 * <li>execute(Transaction)</li>
 * </ul>
 * 
 * <p>
 * Only these methods should be used by a consumer of the Core Layer once the
 * DB has been started and before it has been stopped. This API
 * form a narrow "waist" with a large code base under it and potentially a large code
 * base "above" it. These methods are believed to be "feature complete" in the
 * sense that all features we want from the database can be implemented on top
 * of them. Functionality that can be provided by using only the Core Layer API,
 * should not offered by this class. The method start(), is needed by a user,
 * but for initialization like the constructor or DB.Builder class.
 * </p>
 * 
 * <p>DB Shutdown. The DB typically has allocated resources besides memory: 
 * open sockets, open files, running threads. These resources are guaranteed
 * to be *eventually released* without any action from the DB user after the
 * finalize() method has been called from the garbage collector.
 * The DB user can call DB.stop() to request the eventual release of resources.
 * Resources are not guaranteed to be released when stop() returns, but sometime
 * in the near future (typically within a second).</p>
 * 
 * @author Frans Lundberg
 */
public class Db implements TopDs.DbForMe, IWarner, GetMany.DbForMe {
    //
    // 1210 Frans: Making many fields final increased GET performance somewhat.
    //
    // Note: There must be no reference to a Db object from a thread started
    // by the database (directly or indirectly). 
    // Otherwise, the Db object will never be available for garbage collection,
    // finalize() will not be called, and the thread will not stop.
    //
    
    /** 
     * IKP - internal key prefix - prefix of keys used to store internal database data.
     * Is set to /#ikp/ for 2013.2.130818. Could be changed to "/#i/", but that destroys binary 
     * compatibility.
     */
    public static final String INTERNAL_KEY_PREFIX = Util.identity("/#ikp/");
    
    private static final long[] DUMMY_KEY = Keys.toSegments(INTERNAL_KEY_PREFIX + "-dummy");
    
    private static final int STATE_ZERO = 1;
    private static final int STATE_STARTING = 2;
    private static final int STATE_ACTIVE = 3;
    private static final int STATE_STOPPING = 4;

    private final Object writeLock;
        // Global write lock. Held when STM stuff is done and while transaction serialized to bytes.
    private final Object readSynch;
        // Lock used to make sure writes from DB(), start(), execute(), are published
        // by the writer and 
        // made visible to readers calling get(), getMany().
        // It is typically used with an empty block: "synchronized (readSynch) {}".
        
    private final Object[] pointerLocks;
    private final int pointerLocksLength;
        // Locks to synchronized node pointers. See followPointer().
    private final IKeyModSet keyModSet;
    private final NodeStream nodeStream; // IO for DB to read/append nodes.
    private final StorageManager storageManager;
    private final DirtyNodes dirtyNodes;
    private TopDs topDS;
    private int state = STATE_ZERO;
        // Synch note: writes published by readSynch.
    
    private final Random evictRandom;
    private DatabaseId databaseIdFromBuilder;
        // DatabaseId from Database.Builder, may be null.
    private final Reclaim reclaim;
        // Object used for stream space reclaim.
    private final MetaBlock metaBlock;
        // MetaBlock of RecoverableStream.

    // ---- Settings ----
    // Fields affected by settings.

    private final int maxNodeSize; // max node size in klongs, should no exceed 62.
    private final DbClock dbClock;
    private final IEvictBoss evictBoss;
    private final PrintStream out;
    
    private int startupDistance; 
        // Current startupDistance that affects getDirtyLimit().
        // Sync note: protected by writeLock.
    private int newIncreasedStartupDistance;
        // Normally -1, if not it is the new requested increased startup distance.
        // The 'startupDistance' field is not set immediately, after next meta block has
        // written this new value of startupDistance to the stream.
        // The last metablock stream value of startDistance must be >= this.startDistance.

    // ---- Listeners ----
    
    private final TransactionListener reclaimTransactionListener;

    // ---- Working data for write access ----
    // Must only be accessed from threads holding writeLock.

    /** The access path of top nodes used to access a KV in a set operation. */
    private final TopAccessPath topAccessPath;
    /** The access path of key nodes used to access a KV in a set operation. */
    private final KeyAccessPath keyAccessPath;
    /** Temporary working data. */
    private final KlongWithPointer kwi;
    /** Temporary working data, length = 0. */
    private final KlongWithPointer[] zeroKwis;
    /** Temporary working data, length = 1. */
    private final KlongWithPointer[] oneKwi;
    /** Temporary working data, length = 2. */
    private final KlongWithPointer[] twoKwis;
    /**  Temporary working data. */
    private final Pointer tempPointer;
    /** The nodes updated for the current transaction. To be written to the stream. */
    private final TransactionNodes transactionNodes;
    /** Current transaction while writeLock is held. */
    private Trans trans;
    /** Access data for the current transaction. */
    private long transAccessData;
    /** End stream position of last transaction; used by Db.sync(). */
    private long lastSposOfLastTrans;

    // ---- Counters, statistics, aux state ----
    //
    // The cacheMemoryValue can be used as a time scale instead of ordinary
    // calendar time.
    // It is suitable for cache-related timing, cache eviction.
    // Note that cachedMemoryValue and cachedNodeCount are read and written from
    // concurrent
    // threads, so there is a small probability of "missing an update" when
    // multiple writers
    // add to these values. We allow this to happen, we only need approximate
    // values.
    // "volatile" is needed to assure the values themselves are read/written
    // atomically.
    //

    public final static long MIN_CACHE_MEMORY_VALUE = 10;
    
    private final AtomicLong cachedMemoryValue = new AtomicLong(MIN_CACHE_MEMORY_VALUE);
        // The cachedMemoryValue is an estimate of the total amount of memory cached
        // since the database process was started. It works as a time-scale for the cache.
        // Yes, starting from minCacheMemoryValue instead of 0 has importance.
    private final AtomicLong getOpCount = new AtomicLong(0);
        // Number of get operations processed since startup of DB.
    
    private long transactionCount = 0;
        // Number of transactions executed since this.start().
        // Protected by writeLock.
    
    private long kvCount = 0;
        // Number of KVs set since this.start().
        // Protected by writeLock.
    
    // Below two, protected by writeLock.
    private double dirtyFraction100 = 0.10;
    private double dirtyFraction1000 = 0.10;
    
    /**
     * Private constructor, only DB.Builder calls it. Wires dependencies based
     * on Builder settings.
     */
    private Db(Builder b) {
        writeLock = new Object();
        readSynch = new Object();
        pointerLocksLength = 128;
        pointerLocks = new Object[pointerLocksLength];
        for (int i = 0; i < pointerLocksLength; i++) {
            pointerLocks[i] = new Object();
        }

        evictRandom = new Random(0);
        kwi = new KlongWithPointer();
        zeroKwis = new KlongWithPointer[] {};
        oneKwi = new KlongWithPointer[] { new KlongWithPointer() };
        twoKwis = new KlongWithPointer[] { new KlongWithPointer(), new KlongWithPointer() };
        tempPointer = new Pointer();
        topAccessPath = new TopAccessPath();
        keyAccessPath = new KeyAccessPath();
        transactionNodes = new TransactionNodes();
        keyModSet = new KeyModSet2();
        dirtyNodes = new DirtyNodes();
 
        this.startupDistance = b.startupDistance;
       
        this.newIncreasedStartupDistance = -1;
        
        this.metaBlock = new MetaBlock();
        
        StorageManager.Builder smBuilder = new StorageManager.Builder(writeLock);
        for (int i = 0; i < b.streamInfos.size(); i++) {
            Builder.StreamInfo info = b.streamInfos.get(i);
            smBuilder.stream(info.name, info.stream, info.bufferSize, info.bufferTime);
        }
        this.storageManager = smBuilder.build();
        
        AppendOnlyStream aos = storageManager;
        this.lastSposOfLastTrans = aos.getLength();
        
        RecoverableStream rstream = new RecoverableStream(aos, metaBlock);
        this.nodeStream = new NodeStream(rstream, !b.disableStreamWrite, writeLock);
        this.nodeStream.getMetaBlock().setStartupDistance(b.startupDistance);
        
        this.maxNodeSize = b.maxNodeSize;
        this.dbClock = new DbClock(b.clock);
        this.evictBoss = b.evictBoss;
        
        this.reclaim = new Reclaim(this, aos);
        
        this.reclaimTransactionListener = reclaim;
        reclaim.setRetainDuration(b.retainDuration);

        this.out = System.out;
        this.databaseIdFromBuilder = b.id;

        //
        // Synch note:
        // Synchronized blocks make sure the writes in the constructor are
        // visible to writers and readers. 
        // Readers synchronize with readSynch (get(), getMany()) and writers
        // synchronize with writeLock.
        //
        synchronized (readSynch) {}
        synchronized (writeLock) {}
    }

    /**
     * Returns the current length of the database stream. The method acquires
     * DB.writeLock; may affect performance.
     */
    public final long getStreamLength() {
        synchronized (writeLock) {
            return nodeStream.getLength();
        }
    }

    public int getStartupDistance() {
        synchronized (writeLock) {
            return this.startupDistance;
        }
    }
    
    public String getStartupDistanceH() {
        int sd;
        int newSd;
        int metaSd;
        
        synchronized (writeLock) {
            sd = this.startupDistance;
            newSd = this.newIncreasedStartupDistance;
            metaSd = this.nodeStream.getMetaBlock().getStartupDistance();
        }
        
        return "DB.startupDistance = " + sd 
                + ", db.new..=" + newSd 
                + ", metablock sd = " 
                + metaSd;
    }
    
    public double getDirtyFraction100() {
        synchronized (writeLock) {
            return this.dirtyFraction100;
        }
    }
    
    public double getDirtyFraction1000() {
        synchronized (writeLock) {
            return this.dirtyFraction1000;
        }
    }
    
    /**
     * Suggests a new startup distance.
     */
    public void setStartupDistance(int newDistance) {
        if (newDistance < 0) {
            throw new IllegalArgumentException("Bad newDistance: " + newDistance + ".");
        }
        
        synchronized (writeLock) {
            if (this.newIncreasedStartupDistance != -1) {
                throw new IllegalStateException("An increase of startupDistance from " 
                        + this.startupDistance + " to " + this.newIncreasedStartupDistance 
                        + " has been requested but not finalized. Cannot make change request "
                        + "to startupDistance: " + newDistance + ".");
            }
            
            if (newDistance < startupDistance) {
                decreaseStartupDistance(newDistance);
            }
            
            if (newDistance > startupDistance) {
                increaseStartupDistance(newDistance);
            }
        }
    }
    
    private void decreaseStartupDistance(int newDistance) {
        // Checks should have been done by caller.
        // Note. Possibly, we could split decrease into many parts for large decreases
        // to avoid large transactions.
        //
        // 1. Set this.startupDistance.
        // 2. Run dummy transaction. May cause many dirty nodes to be written since
        //    result of getDirtyLimit() changes.
        // 3. Modify startupDistance of metaBlock. Next time metaBlock is written, the 
        //    new startupDistance will be available to an "upstarter" (a process calling DB.start()).
        //
        
        assert Thread.holdsLock(writeLock);
        assert newDistance >= 0;
        assert newDistance < startupDistance;
        
        this.startupDistance = newDistance;
        execute(Trans.builder().set(Db.DUMMY_KEY, new byte[0]).build());
        nodeStream.getMetaBlock().setStartupDistance(newDistance);
    }
    
    private void increaseStartupDistance(int newDistance) {
        // Checks should have been done by caller.
        //
        // 1. Increases startupDistance in meta block.
        // 2. Sets this.newIncreasedStartupDistance. This is a request to change this.startupDistance
        //    later, after meta block has been written to stream.
        //
        
        assert Thread.holdsLock(writeLock);
        assert newDistance > 0;
        assert newDistance > startupDistance;
        
        nodeStream.getMetaBlock().setStartupDistance(newDistance);
        this.newIncreasedStartupDistance = newDistance;
    }
    
    public long getCachedMemoryValue() {
        return cachedMemoryValue.get();
    }

    public long getRetainDuration() {
        return reclaim.getRetainDuration();
    }

    /**
     * Sets retain duration.
     * 
     * @param duration
     *            Number of time units (see Clock.UNITS_PER_SEC).
     */
    public void setRetainDuration(long duration) {
        reclaim.setRetainDuration(duration);
    }
    
    public void setReclaimInternalFraction(double internalFraction) {
        reclaim.setInternalFraction(internalFraction);
    }
    
    public double getInternalFraction() {
        return reclaim.getInternalFraction();
    }
    
    public long getReclaimIterationCount() {
        return reclaim.getIterationCount();
    }

    /**
     * First (smallest) time available for a lookup.
     */
    public long getFirstAvailableLookupTime() {
        synchronized (readSynch) {}
        return reclaim.getFirstAvailableLookupTime();
    }

    public long getFirstAvailablePos() {
        synchronized (readSynch) {}
        return reclaim.getFirstAvailablePos();
    }
    
    public long getTransactionCount() {
        synchronized (writeLock) {
            return transactionCount;
        }
    }
    
    public long getKvCount() {
        synchronized (writeLock) {
            return kvCount;
        }
    }
    
    /**
     * Returns the number of get operations that has completed since DB.start() was called.
     */
    public long getGetOpCount() {
        return getOpCount.get();
    }

    public final long getPosOfLastValidMetaBlock() {
        return nodeStream.getPosOfLastValidMetaBlock();
    }
    
    /**
     * Adds a replica stream while the database is running. The replica will be
     * synched with the main stream in a background Job that is returned to the
     * caller.
     * 
     * @param name
     *            Name of the storage.
     * @param replicaStream
     *            The replica stream.
     * @param bufferSize
     *            Buffer size in of BufferedStream that will wrap 'stream'. In
     *            bytes.
     * @param bufferTime
     *            Buffer time in milliseconds.
     * @throws BadReplicaException
     *            If the replica stream is longer than the main stream; if the
     *            replica stream has a different database ID than the main
     *            stream.
     * @throws IOException
     *            If there was an IO error with the replica.
     */
    public Job addReplica(final String name, final AppendOnlyStream replicaStream,
            final int bufferSize, final int bufferTime) throws IOException {
        // Note, the dummy write followed by waitForD2 call are needed to make
        // sure replica is really synched once the Job finishes.
        
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed.");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("Empty string for 'name' not allowed.");
        }
        
        if (replicaStream == null) {
            throw new IllegalArgumentException("replicaStream == null not allowed.");
        }
        
        if (replicaStream instanceof BufferedStream) {
            throw new IllegalArgumentException("'replica' is instance of BufferedStream; not allowed.");
        }
        
        // Shared final refs. Array values protected by: progressLock.
        final Object progressLock = new Object();
        final int[] progressValue = new int[] { 0 };
        final String[] progressNote = new String[] { "About to start to synch." };

        final ProgressListener progressListener = new ProgressListener() {
            public void progress(int myProgressValue, String myProgressNote) {
                synchronized (progressLock) {
                    if (myProgressValue == 100) {
                        progressValue[0] = 99;
                        progressNote[0] = "Almost done, waitForD2...";
                    } else {
                        progressValue[0] = myProgressValue;
                        progressNote[0] = myProgressNote;
                    }
                }
            }
        };

        // Checks database id of main and replica; must match.
        
        checkReplicaId(metaBlock.getId(), replicaStream);

        final StorageManager.SynchingStorage ss = storageManager.addReplica(name, replicaStream,
                bufferSize, bufferTime);

        final Thread syncThread = new Thread(new Runnable() {
            public void run() {
                storageManager.syncReplica(ss, progressListener);
                Trans trans = Trans.builder().set(DUMMY_KEY, new byte[0]).build();
                Db.this.execute(trans);
                Db.this.waitForD2(trans.lastSpos);

                synchronized (progressLock) {
                    progressValue[0] = 100;
                    progressNote[0] = "Done!";
                }
            }
        });
        syncThread.setName("db-addReplica-sync-" + name + "-" + syncThread.getId());
        syncThread.setPriority(Thread.NORM_PRIORITY - 1);
        syncThread.start();

        // Adaptor, adapts Thread + ProgressListener to a Job.
        
        Job job = new Job() {
            public JobStatus getStatus() {
                final int pValue;
                final String pNote;

                synchronized (progressLock) {
                    pValue = progressValue[0];
                    pNote = progressNote[0];
                }

                return new JobStatus() {
                    public int progress() {
                        return pValue;
                    }

                    public String note() {
                        return pNote;
                    }
                };
            }

            public JobStatus join() {
                return join(0);
            }

            public JobStatus join(int millis) {
                try {
                    syncThread.join(millis);
                } catch (InterruptedException e) {
                    throw new Error("Internal thread unexpectedly interrupted.");
                }
                return getStatus();
            }
        };

        return job;
    }

    /**
     * @throws BadReplicaException
     */
    private void checkReplicaId(byte[] mainId, final AppendOnlyStream replicaStream) {
        if (replicaStream.getLength() > 0) {
            RecoverableStream rStream = new RecoverableStream(replicaStream, new MetaBlock());
            MetaBlock meta = rStream.readLastValidMetaBlock();
            if (meta == null) {
                throw new BadReplicaException("Found no valid meta block in replica stream; " +
                		"replica length: " + replicaStream.getLength() + ".");
            }
            
            byte[] replicaId = meta.getId();
            
            if (replicaId == null) {
                throw new Bug("replicaId == null");
            }
            
            if (mainId == null) {
                throw new Bug("mainId == null");
            }
            
            if (replicaId.length == 0) {
                throw new Bug("replicaId.length == 0");
            }
            
            if (mainId.length == 0) {
                throw new Bug("mainId.length == 0");
            }

            if (!Util.areEqual(mainId, replicaId)) {
                throw new BadReplicaException("ID of replica stream (" + Util.toHexString(replicaId)
                        + ") does not match database ID (" + Util.toHexString(mainId) + ").");
            }
        }
    }
    
    public void removeReplica(String name) {
        storageManager.removeReplica(name);
    }
    
    public StorageInfo[] getStorageInfos() {
        return storageManager.getStorageInfos();
    }

    /**
     * For internal use.
     */
    public final NodeStream getStream() {
        return nodeStream;
    }
    
    public long getTime() {
        return dbClock.getTime();
    }
    
    public long getTimeForGet(long wantedTime) {
        return dbClock.timeForGet(wantedTime);
    }

    /**
     * Returns the collection of dirty nodes. Needed by DB monitor. Same
     * reference is always returned since it comes from a final field.
     */
    public final DirtyNodes getDirtyNodes() {
        return dirtyNodes;
    }

    public final Object getWriteLock() {
        return writeLock;
    }
    
    /**
     * Returns the readSynch lock Object.
     */
    public final Object getReadSynch() {
        return readSynch;
    }
    
    
    private static String getStateName(int state) {
        String result;
        
        switch (state) {
        case STATE_ZERO:
            result = "STATE_ZERO";
            break;
        case STATE_STARTING:
            result = "STATE_STARTING";
            break;
        case STATE_ACTIVE:
            result = "STATE_ACTIVE";
            break;
        case STATE_STOPPING:
            result = "STATE_STOPPING";
            break;
        default:
            result = "Unknown DB state (" + state + ")";
        }
        return result;
    }

    /**
     * Starts the database by reading from the stream. Call once per object
     * after constructor and before the get/set methods.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalStateException
     *             If start() has been called already.
     * @throws BadReplicaException
     */
    public void start() {
        synchronized (writeLock) {
            synchronized (readSynch) {
                startInner();
            }
        }
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws BadReplicaException
     * @throws IllegalDbStateException
     */
    private void startInner() {
        if (state != STATE_ZERO) {
            throw new IllegalDbStateException("DB has been started already, "
                    + "start() should be called once only; DB state is: " 
                    + getStateName(state) + ".");
        }

        boolean dbCreated;      // True if db was created in this method (there was no existing data).
        
        storageManager.checkStreamIds();
        
        // Synchronizes storages based on the "longest" storage available.
        
        try {
            storageManager.syncStreams(new NullProgressListener());
        } catch (IOException e) {
            throw new StreamIoException(e);
        }

        // Init DB graph state if stream is empty, otherwise recover existing one.

        if (nodeStream.getLength() == 0) {
            createInitialState();
            dbCreated = true;
        } else {
            dbCreated = false;
        }

        // Recovers stream, reads meta block in stream.

        nodeStream.recover();

        // An assertion

        if (Util.hasOnlyZeros(nodeStream.getMetaBlock().getId())) {
            throw new IllegalStateException("Invalid database ID, only zero bytes.");
        }

        // Startup phase
        
        if (!dbCreated) {
            this.startupDistance = nodeStream.getMetaBlock().getStartupDistance();
            if (startupDistance < 0) {
                throw new StreamFormatException("Bad value of startupDistance in meta " +
                		"block of stream: " + startupDistance + ".");
            }
            
            // TODO A. Part of bug fix... Db.startInner()
//System.out.println("Db.startInner(), startupDistance: " + this.startupDistance);
//this.startupDistance += 2*1000000;   // not enough with 2M
//this.startupDistance += 3*1000000;    // Works!
//System.out.println("Db.startInner(), startupDistance: " + this.startupDistance);
        }
        
        long pos1 = nodeStream.getPosOfLastCompletedTrans();
        long startPos = pos1 - (startupDistance + 1);
        startPos = startPos < 0 ? 0 : startPos;
  
//System.out.println("Db, node stream length: " + nodeStream.getLength());
//System.out.println("Db, pos1 = " + pos1 + ", startPos = " + startPos);

        // posMap is a map from spos of a node to the node itself.
        // nextMap is a map from previous spos of a node to the node itself.

        HashMap<Long, INode> posMap = new HashMap<Long, INode>();
        HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // sposPrevious
                                                                   // -> Node

        long lastTransactionTime = 0;

        NodeStream.TransIterator ti = nodeStream.new TransIterator(startPos);
        while (ti.next()) {
            if (ti.nextTransPos < startPos) {
                continue; // We can allow to skip forward here
            }

            lastTransactionTime = ti.getTransactionTime();

            NodeStream.NodeIterator ni = ti.getNodeIterator();
            while (ni.next()) {
                INode node = ni.node;
                posMap.put(node.getSpos(), node);
                long prev = ni.sposPrevious;
                if (prev != Spos.NULL) {
                    nextMap.put(prev, node);
                }

                this.cachedMemoryValue.addAndGet(node.getMemSize());
            }
        }

        dbClock.setLastTransactionTime(lastTransactionTime);

        reconciliatePointers(posMap, nextMap);

        this.state = STATE_ACTIVE;

        reclaim.initFromDb();
            // state = STATE_ACTIVE needed before this method.
    }

    private void reconciliatePointers(HashMap<Long, INode> posMap, HashMap<Long, INode> nextMap) {
        //
        // Pointer reconciliation phase
        // * Refreshes stream pointers
        // * Creates memory pointers
        // * Finds the superRoot TopNode among the startup nodes.
        //

        TopNode superRoot = null;
        Pointer pointer = new Pointer();

        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();

            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, pointer);
                if (pointer.isNull()) {
                    continue;
                }

                long pos = pointer.getPos();

                while (true) {
                    INode next = nextMap.get(pos);
                    if (next == null) {
                        break;
                    }
                    pos = next.getSpos();
                }

                if (pointer.getPos() != pos) {
                    node.setPointer(i, null, pos);
                }
            }

            // Check for super root node.

            if (node instanceof TopNode) {
                TopNode potentialSuperRoot = (TopNode) node;
                if (superRoot == null) {
                    superRoot = potentialSuperRoot;
                }

                if (potentialSuperRoot.topNodeId > superRoot.topNodeId) {
                    superRoot = potentialSuperRoot;
                }
            }
        }

        if (superRoot == null) {
            throw new StreamFormatException("Could not find root node within startup node set.");
        }

        this.topDS = new TopDs(superRoot);

        // Creates memory pointers from stream pointers.

        long accessData = getAccessData();
        Pointer p2 = new Pointer();

        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();

            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p2);
                if (p2.isNull()) {
                    continue;
                }

                INode pointee = posMap.get(p2.pos);
                if (pointee != null) {
                    node.setPointer(i, pointee, accessData);
                }
            }
        }
    }
    
    /**
     * <p>Calling this method is a request for stopping the database to not allow
     * any more get/execute operations on it and to eventually release resources
     * held by this object.
     * This method returns quickly, it does not wait for threads to finish, 
     * storage streams to flush and files to be closed. It only request a release
     * of such resources in the near future. Typically, resources will be released
     * within a second after this method has been called.
     * It is safe to call this method multiple times and from different threads.
     * If database has been stopped already, a call to this method does nothing.</p>
     * 
     * <p>When this method returns, it is guaranteed that no write operation is running or
     * will be started, and no read operation will be started (but could be running).</p>
     */
    public void stop() {
        synchronized (readSynch) {};
        
        if (state == STATE_STOPPING) {
            return;
        }
        
        state = STATE_STOPPING;
        synchronized (readSynch) {};
        storageManager.stop();
    }
    
    /**
     * Stops the database, flushes the storage streams and releases resources; 
     * for example closes open files and network sockets.
     * This method does what stop() does and more.
     */
    public void close() {
        synchronized (readSynch) {};
        
        if (state == STATE_STOPPING) {
            return;
        }
        
        synchronized (this.writeLock) {
            if (state == STATE_STOPPING) {
                return;
            }
            
            state = STATE_STOPPING;
            
            synchronized (readSynch) {};
        }
            
        // Here, no write op is running or will be started.
        // No read op (get) will be started, but may be running.
        
        storageManager.close();
    }
    
    public void finalize() {
        stop();
    }

    /**
     * Creates the initial state of an empty database. Only two nodes will
     * exist: the super root top node and the space root node (a key node).
     * Called if the transaction stream is empty when the database is started.
     * 
     * @throws StreamIoException
     */
    private void createInitialState() {

        // Creates a new static ID for the database or uses builderDatabaseId
        // if non-null.

        DatabaseId id = (databaseIdFromBuilder == null) ? new DatabaseId() : databaseIdFromBuilder;
        nodeStream.getMetaBlock().setId(id.getBytes());
        GetData gdForFindRoot = new GetData();

        synchronized (writeLock) {
            long time = dbClock.getTime();

            KeyNode root = new KeyNode();
            topDS = TopDs.createFromFirstRoot(time, root, Spos.DEFAULT_ACCESS_DATA);
            KeyNode spaceRoot = topDS.findRoot(this, time, true, null, Spos.DEFAULT_ACCESS_DATA,
                    gdForFindRoot);
            TopNode superRoot = topDS.getSuperRoot();

            assert spaceRoot == root;
            assert spaceRoot.getSpos() == Spos.NULL;
            assert superRoot.getSpos() == Spos.NULL : "Expected " + Spos.NULL + ", was "
                    + superRoot.getSpos();
            assert topDS.getSuperRoot().rootPointerPos == Spos.DEFAULT_ACCESS_DATA;

            Trans t = Trans.builder().build();
            this.transactionNodes.add(spaceRoot);
            this.transactionNodes.add(superRoot);
            t.isInternal = true;
            executeInner(t, true);

            assert spaceRoot.getSpos() != Spos.NULL;
            assert superRoot.getSpos() != Spos.NULL;
        }
    }
    
    /**
     * Makes a TopNode dirty if not already dirty. This method returns immediately
     * if the node is dirty already. Caller must hold this.writeLock.
     */
    private final void makeDirty(TopNode n) {
        assert Thread.holdsLock(this.writeLock);
        
        if (!n.isDirty) {
            n.isDirty = true;
            dirtyNodes.add(n);
        }
    }
    
    /**
     * Makes a KeyNode dirty if not already dirty. This method returns immediately
     * if the node is dirty already. Caller must hold this.writeLock.
     */
    private final void makeDirty(KeyNode n) {
        assert Thread.holdsLock(this.writeLock);
        
        if (!n.isDirty) {
            //n.isDirty = false;   // Bug fixed 130522. Existed for 20 days or so.
            n.isDirty = true;
            dirtyNodes.add(n);
        }
    }

    /**
     * Follows a pointer. This method must always be used when a pointer is
     * followed. This is an essential method of the database.
     * 
     * @param predecessor
     *            Needed to update a pointer in predecessor to cache a node read
     *            from stream. Also needed to update access data in predecessor.
     *            Cannot be null.
     * @param pointerIndex
     *            Index to the node pointer in predecessor. The parameter is
     *            ignored if 'cache' is false.
     * @param cache
     *            Whether to cache the result node or not.
     * @param accessData
     *            The access data to set for the pointer followed. If accessData == 0, no changes
     *            is made to the access data of the pointer.
     * @return The pointee node.
     */
    public final INode followPointer(final INode predecessor, final int pointerIndex,
            final boolean cache, final long accessData, final GetData gd) {
        //
        // Method must be public since it implements an interface.
        //

        INode result;
        assert predecessor != null;
        assert gd != null : "gd == null, not allowed";

        final Object lock = getPointerLock(predecessor, pointerIndex);

        synchronized (lock) {
            INode pointerNode = predecessor.getPointerNode(pointerIndex);
            long pointerPos = predecessor.getPointerPos(pointerIndex);

            assert !Pointer.isNull(pointerNode, pointerPos) : "Pointer is null: " + pointerNode
                    + ", " + pointerPos;

            if (Pointer.isMem(pointerNode)) {
                result = pointerNode;
                if (accessData != 0) {
                    predecessor.setPointerAccessData(pointerIndex, accessData);
                }
                gd.followMemoryPointerCount++;
            } else {
                result = nodeStream.readNode(pointerPos, null);
                if (cache) {
                    predecessor.setPointer(pointerIndex, result, accessData);
                    cachedMemoryValue.addAndGet(result.getMemSize());
                }
                
                gd.followStreamPointerCount++;
            }
        }

        return result;
    }

    /**
     * Returns a lock for the pointerIndex'th pointer of node 'node'.
     */
    private final Object getPointerLock(final INode node, final int pointerIndex) {
        int value = (node.hashCode() + 13 * pointerIndex);
        value = (value < 0) ? -value : value;
        return pointerLocks[value % pointerLocksLength];
    }

    /**
     * Prints the in memory part of the DB graph. Useful for test and
     * development.
     */
    public void printGraph(PrintStream out) {
        TopNode top = topDS.getSuperRoot();
        top.printGraph(out, "", 0);
    }

    /**
     * Gets a value given a key. This is the primary and fastest GET method with
     * no memory allocation.
     * 
     * @param lookupTime
     *            The DB time for which to make the GET operation. Use
     *            Long.MAX_VALUE to lookup the state at the latest possible
     *            time.
     * @throws IllegalDbStateException
     *             If start() has not been called or stop()/stopFast() has been called. 
     *             The database is not in the active state.
     * @throws StreamFormatException
     *             If the database stream is corrupt.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream.
     */
    public byte[] get(long lookupTime, long[] keySegments, GetData gd) {
        //
        // Few assumptions of previous state of gd are assumed. db.kwi must be non-null, however.
        //

        assert gd != null;
        assert gd.kwi != null;

        // Makes sure writes from startup and execute() are visible.
        synchronized (readSynch) {}

        int myState = state;
        if (myState != STATE_ACTIVE) {
            if (myState == STATE_STOPPING) {
                throw new DbStoppingException("Cannot call get() when DB is stopping.");
            } else {
                throw new IllegalDbStateException("Cannot call get() when DB state is " 
                        + getStateName(myState) + ".");
            }
        }
        
        long firstAvailable = reclaim.getFirstAvailableLookupTime();
        if (lookupTime < firstAvailable) {
            String lookupTimeString = DbUtil.dbTimeToUtc(lookupTime);
            String firstTimeString = DbUtil.dbTimeToUtc(firstAvailable);
            throw new LookupTimeNotAvailableException("Cannot lookup at time " + lookupTime 
                    + " (" + lookupTimeString 
                    + ", the first time available for lookup is " 
                    + firstAvailable + " (" + firstTimeString + ").");
        }

        gd.accessData = getAccessData();

        if (gd.evictData.enableEvict) {
            possiblyEvict(gd.evictData);
        }

        KeyNode segmentRoot;
        int segmentCount = keySegments.length;
        int lastIndex = segmentCount - 1;
        byte[] result = null;
        INode item;
        KeyNode node;

        long time = dbClock.timeForGet(lookupTime);
        // Limits lookup time so it strictly less than the transaction time of
        // any running
        // or future transaction.
        gd.actualLookupTime = time;
        gd.nodeDepth = 0;

        // This method call adds all nodes including super root and the returned
        // segmentRoot to accessPath if accessPath is non-null.

        segmentRoot = topDS.findRoot(this, time, gd.cache, null, gd.accessData, gd);

        if (segmentRoot == null) {
            return null;
        }

        // For each segment in key segment array
        for (int i = 0; i < segmentCount; i++) {
            item = getEqNodeInSegment(time, segmentRoot, keySegments[i], gd, null);

            if (i == lastIndex) {
                result = null;
                if (item != null && item instanceof ValueNode) {
                    result = ((ValueNode) item).getValue();
                }
                break;
            } else {
                if (item instanceof KeyNode) {
                    node = (KeyNode) item;
                } else {
                    node = null;
                }

                if (node == null) {
                    result = null;
                    break;
                }
                gd.nodeDepth++;
                segmentRoot = node;
            }
        }

        getOpCount.incrementAndGet();
        return result;
    }
    
    /**
     * Simulates a get() lookup to gather the node index choices that are made 
     * to access the value corresponding to a certain key.
     * Caller holds Db.writeLock. The transactionTime must have been "released" 
     * for use by get operations.
     * 
     * @param choices Output parameter that collects the result.
     */
    private void getChoices(long[] key, Choices choices, boolean isDelete) {
        KeyNode segmentRoot;
        int segmentCount = key.length;
        int lastIndex = segmentCount - 1;
        INode node;
        KeyNode keyNode;
        GetData gd = trans.getData;

        long time = trans.transactionTime;
        if (isDelete) {
            time = time - 1;
            if (time < 0) {
                throw new Bug("Negative lookup time: " + time + ".");
            }
        }
        gd.nodeDepth = 0;

        segmentRoot = topDS.findRootAndRecordChoices(this, time, false, 0, gd, choices);
        
        // For each segment in key segment array
        for (int i = 0; i < segmentCount; i++) {
            node = getEqNodeInSegment(time, segmentRoot, key[i], gd, choices);

            if (i == lastIndex) {
                break;
            } else {
                if (node instanceof KeyNode) {
                    keyNode = (KeyNode) node;
                } else {
                    keyNode = null;
                }

                if (keyNode == null) {
                    break;
                }
                gd.nodeDepth++;
                segmentRoot = keyNode;
            }
        }
    }
    
    /**
     * Follows node pointer choices to create and return a key.
     * Currently (2013-05) used for testing only.
     */
    private long[] followChoices(Choices choices) {
        ArrayList<Long> key = new ArrayList<Long>();
        GetData gd = new GetData();
        gd.accessData = getAccessData();
        
        INode node = topDS.getSuperRoot();
        int choiceIndex = 0;
        
        while (true) {
            int choice = choices.getChoice(choiceIndex);
            
            if (node instanceof KeyNode) {
                KeyNode k = (KeyNode) node;
                if (k.isSegmentLeaf()) {
                    key.add(Klong.getCompareValue(k.getKlong(choice)));
                }
            }
            
            if (choiceIndex < choices.getSize() - 1) {
                INode newNode = followPointer(node, choice, false, gd.accessData, gd);
                choiceIndex++;
                node = newNode;
            } else {
                break;
            }
        }
        
        return Util.toArray(key);
    }
    
    /**
     * Follows the pointers in the DB graph from the super top node using the given 
     * node index choices.
     * Useful for testing.
     */
    public INode findNode(int[] choices) {
        if (choices == null) {
            throw new IllegalArgumentException("choices == null not allowed");
        }
        
        GetData gd = new GetData();
        INode node = this.getSuperRoot();
        
        for (int i = 0; i < choices.length; i++) {
            int choice = choices[i];
            node = this.followPointer(node, choice, false, 0, gd);
            if (node == null) {
                break;
            }
        }
        
        return node;
    }

    /**
     * Get multiple KVs in increasing key order.
     * 
     * @param g
     *            Input and output parameters.
     * @see GetMany
     * @throws IllegalDbStateException
     *             If start() has not been called.
     * @throws StreamFormatException
     *             If the database stream is corrupt.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream.
     */
    public void getMany(GetMany g) {
        //
        // Note, multiple get operations may be running in parallel.
        // All data used must be thread safe. Temporary, operation-local data is stored in 
        // the 'g' object.
        //

        assert g.result != null;
        assert g.result.size() == 0 : "g.result.size() not 0, but " + g.result.size();
        assert g.stopCondition != null;

        synchronized (readSynch) {}
            // Makes sure writes from startup and execute() are visible.

        int myState = state;
        if (myState != STATE_ACTIVE) {
            if (myState == STATE_STOPPING) {
                throw new DbStoppingException("Cannot call getMany() when DB is stopping.");
            } else {
                throw new IllegalDbStateException("Cannot call getMany() when DB state is " 
                        + getStateName(myState) + ".");
            }
        }
        
        long first = reclaim.getFirstAvailableLookupTime();
        if (g.lookupTime < first) {
            String lookupTimeString = DbUtil.dbTimeToUtc(g.lookupTime);
            String firstString = DbUtil.dbTimeToUtc(first);
            throw new LookupTimeNotAvailableException("Cannot lookup at time " + g.lookupTime 
                    + " (" + lookupTimeString 
                    + ", the first time available for lookup is " 
                    + first + " (" + firstString + ").");
        }

        EvictData ed = new EvictData();

        long accessData = getAccessData();

        possiblyEvict(ed);

        g.actualLookupTime = dbClock.timeForGet(g.lookupTime);
            // Limits lookup time so it strictly less than the transaction time of
            // any running or future transaction.

        KeyNode root = topDS.findRoot(this, g.actualLookupTime, g.cache, null, accessData, g.gd);

        if (root == null) {
            return;
        }

        GetMany.Chain chain = g.new Chain((GetMany.DbForMe) this);
        chain.setup(root);

        outer: while (true) {
            Kvt kvt = chain.next();

            if (kvt == null) {
                g.stopCondition.eod();
                break outer;
            }
            
            getOpCount.incrementAndGet();

            int shouldStop = g.stopCondition.handleKvt(kvt);

            switch (shouldStop) {
            case StopCondition.STOP:
                break outer;
            case StopCondition.ADD:
                g.result.add(kvt);
                break;
            case StopCondition.ADD_AND_STOP:
                g.result.add(kvt);
                break outer;
            case StopCondition.CONTINUE:
                // empty
                break;
            default:
                assert false : "Bad int value: " + shouldStop;
            }
        }
    }


    /**
     * Gets a ValueNode or KeyNode from a segment in the DB graph. Returns null
     * if none was found.
     * 
     * @param time
     *            The lookup time.
     * @param segmentRoot
     *            The segment root key node.
     * @param compareValue
     *            The compareValue to search for.
     * @param gd
     *            GetData to the lookup operation.
     * @param choices
     *            The choice path records pointer indexes chosen, may be null to
     *            disable the choice recording.
     */
    private final INode getEqNodeInSegment(long time, KeyNode segmentRoot, long compareValue,
            GetData gd, Choices choices) {
        final KlongWithPointer kwi = gd.kwi;
        KeyNode current = segmentRoot;
        INode result;

        while (true) {
            if (current.isSegmentLeaf()) {
                current.searchEq(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                } else {
                    if (choices != null) choices.add(kwi.pointerIndex);
                    result = followPointer(current, kwi.pointerIndex, gd.cache, gd.accessData, gd);
                }
                break;

            } else {
                current.searchLte(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                    break;
                } else {
                    assert kwi.node == null || kwi.node instanceof KeyNode : "Expected a KeyNode, got "
                            + kwi.node;

                    if (choices != null) choices.add(kwi.pointerIndex);
                    KeyNode nextCurrent = (KeyNode) followPointer(current, kwi.pointerIndex,
                            gd.cache, gd.accessData, gd);
                    current = nextCurrent;
                    gd.nodeDepth++;
                }
            }
        }

        return result;
    }

    /**
     * Same as "execute(b.build());", AVOID using this method in new code, 
     * use execute(Trans).
     * Db is selfish, should provide minimal interface, not convinience methods.
     */
    public final void execute(Trans.Builder b) {
        //
        // This little method does not comply with the minimum Core Layer API rule.
        // Should be be avoided, but currently (2012-12) called from over 100 places.
        //
        execute(b.build());
    }

    /**
     * Executes a transaction using the STM approach. Assumes: t.kvs is sorted.
     * 
     * @throws IllegalDbStateException
     *             If start() has not been called or database is stopping.
     * @throws RerunException
     *             Thrown if the transaction was cancelled and should be rerun
     *             because one or more KVs with a key in the read key hash set,
     *             were changed after the read time of the transaction. STM
     *             approach.
     * @throws StreamFormatException
     *             If the database stream is corrupt.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream.
     * @throws InternalDataException
     *             If BergDB internal data in the database is corrupt.
     */
    public final void execute(final Trans t) {
        //
        // Executes a KV set request as an ACID transaction.
        //
        // We make sure all readers have a read time that is strictly less than
        // t.transactionTime
        // while the synchronized(writeLock) clause is executing. This is
        // handled by dbClock.
        //

        // Makes sure writes from startup and execute() are visible.
        // We do not hold DB.writeLock yet.
        synchronized (readSynch) {}

        int myState = state;
        if (myState != STATE_ACTIVE) {
            if (myState == STATE_STOPPING) {
                throw new DbStoppingException("Cannot call getMany() when DB is stopping.");
            } else {
                throw new IllegalDbStateException("Cannot call getMany() when DB state is " 
                        + getStateName(myState) + ".");
            }
        }

        executeInner(t, false);
    }
    
    /**
     * Waits until D1 durability has been achieved for stream position 'spos'.
     * 
     * @throws StreamIoException
     */
    public void waitForD1(long spos) {
        try {
            storageManager.waitForD1(spos);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /**
     * Waits until D2 durability has been achieved for stream position 'spos'.
     * 
     * @throws StreamIoException
     */
    public void waitForD2(long spos) {
        try {
            storageManager.waitForD2(spos);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /**
     * Waits for last stream position to be considered durable according to durability rule D2.
     * 
     * @throws StreamIoException
     */
    public void sync() {
        long spos;
        
        synchronized (writeLock) {
            spos = this.lastSposOfLastTrans;
        }
        
        waitForD2(spos);
    }

    /**
     * @throws RerunException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException
     */
    private void executeInner(Trans t, final boolean isPrimordial) {
        //
        // Executes a KV set request as an ACID transaction.
        //
        // We make sure all readers have a read time that is strictly less than
        // t.transactionTime while the synchronized(writeLock) clause is executing.
        // This is handled by dbClock.
        //
        // Reads the KVs as warm-up; aims to avoid lengthy disk reads and cache
        // misses while synchronizing on this.writeLock. We want to minimize the time holding
        // this.writeLock. However, if we do write transactions from a single thread anyway, it
        // would be better to void these get operations (would save 10-20% CPU for execute()).
        // NOTE Room for a small optimization. A special warmup() method could be more performant
        // than the general-purpose, public get() method.
        //
        
        long time = dbClock.getTime();

        boolean enableEvict = t.getData.evictData.enableEvict;
        t.getData.evictData.enableEvict = false;

        // Warm-up code, avoids read from stream while holding writeLock.
        for (Kv kv : t.kvs) {
            this.get(time, kv.keySegments, t.getData);
        }

        t.getData.evictData.enableEvict = enableEvict;

        synchronized (writeLock) {
            assert topAccessPath.getSize() == 0 : "topAccessPath.size = " + topAccessPath.getSize() 
                    + ", keyAccessPath.size = " + keyAccessPath.size;
            assert keyAccessPath.size == 0 : "topAccessPath.size = " + topAccessPath.getSize() 
                    + ", keyAccessPath.size = " + keyAccessPath.size;
            if (!isPrimordial) assert transactionNodes.size() == 0;
            
            this.trans = t;
            this.transAccessData = getAccessData();

            // Returns to caller with a RerunException if any key was modified after 
            // the read time of the transaction.
            // This is the essence of the STM (software transactional memory) approach.

            for (long hash : t.readKeyHashes) {
                if (keyModSet.modifiedAfter(t.readTime, hash)) {
                    throw new RerunException(hash);
                }
            }

            try {
                t.transactionTime = dbClock.transactionBegin();
                setKvs();
                kvCount += t.kvs.length;
                transactionCount++;

                synchronized (readSynch) {}
                    // Publishes the changes by the writer thread to the readers. This is done
                    // before the t.transactionTime can be used as lookup time, so all readers
                    // (that do: "synchronized (readSynch) {}") are guaranteed to see all changes
                    // made by the writer (the thread executing this code).
            } finally {
                dbClock.transactionEnd();
                // After above line, get requests can use the time
                // t.transactionTime.
            }

            for (int i = 0; i < t.writeKeyHashes.length; i++) {
                keyModSet.add(t.transactionTime, t.writeKeyHashes[i]);
            }

            // IDEA 1210, we could possibly finish holding the writeLock here
            // already. If so, the serialization of the nodes would have to be done using the
            // transaction time as a parameter to the serialization.
            // Since all nodes are persistent data structures, this could work.
            // There would be a need to queue the transaction in a stream output
            // queue to enforce the ordering of the transactions. The serialization could
            // possibly be done in a separate thread, or not.
            
            // 1305 Frans: Adds choices for ValueNodes to transactionNodes (+20% CPU).
            // This is needed to have an active replica.
            
            for (int i = 0; i < transactionNodes.valueSize; i++) {
                long[] key = transactionNodes.keys[i];
                getChoices(key, transactionNodes.choices[i], transactionNodes.valueNodes[i].isDelete());
                assert Keys.compareKeys(key, followChoices(transactionNodes.choices[i])) == 0 :
                    "key:" + Keys.toString(key) + ", choices: " + transactionNodes.choices[i];
            }
            
            addNodesToStream();
            this.lastSposOfLastTrans = this.trans.lastSpos;

            clearTransMemory();

            // 1301 Frans. The following line moved to inside the synchronized
            // (writeLock) block to KISS the reclaim stuff. However, it does not have to
            // belong to the writeLock code block.
            reclaimTransactionListener.transactionCompleted(t);
        }
    }

    /**
     * Writes the nodes in this.transactionNodes to stream. Uses this.trans, 
     * this.transactionNodes, this.metaBlock, this.cacheMemoryValue, and more.
     * The caller must hold DB.writeLock.
     * 
     * @throws StreamIoException
     */
    private void addNodesToStream() {
        //
        // Note the call to getTooDirtyNodes. This is done without including the size
        // of the current transaction. This means that the startup algorithm must
        // take this into account. It must start reading before or at:
        // spos = (last-spos-of-stream - (startupDistance + size-of-last-Transaction)).
        // So, the spos that is at last startupDistance bytes before the beginning of the 
        // last completed transaction.
        //
        
        assert Thread.holdsLock(writeLock);
        
        // Below is a simple implementation of the cachedMemoryValue.
        // Everything written to the stream is considered new data to the cache. This is not true.
        // KeyNode can be appended to without adding them to cache again. Also, the dirty
        // nodes are already cached. To handle this better, we could report to DB when
        // KeyNodes grow (their arrays enlarged) and when new nodes are created.
        // An DbForMe interface sent to KeyNode methods that may enlarge its memory use,
        // and to constructors of ValueNode, KeyNode, TopNode. Maybe overkill?

        this.cachedMemoryValue.addAndGet(transactionNodes.sumMemSize());

        long dirtyLimit = getDirtyLimit();

        // NOTE The current implementation works (120522)
        // However, a small transaction that comes after a large one, will often get unfairly
        // many dirty KeyNodes/TopNodes to write.
        // Would be better if the number of extra (too dirty nodes) nodes in a transaction was
        // proportional to the Kvs of the transaction.
        // This can be solved. The total size of the transaction nodes can be computed first, 
        // then..

        int ordinaryNodeCount = transactionNodes.size();
        
        dirtyNodes.getTooDirtyNodes(dirtyLimit, true, transactionNodes);
        
        {   // Computes dirtyFraction100, dirtyFraction1000. For statistics, monitoring.
            int totalNodeCount = transactionNodes.size();
            int dirtyNodeCount = totalNodeCount - ordinaryNodeCount;
            double dirtyFraction = ((double) dirtyNodeCount) / totalNodeCount;
            this.dirtyFraction100   = 0.99  * this.dirtyFraction100  +  0.01  * dirtyFraction;
            this.dirtyFraction1000  = 0.999 * this.dirtyFraction1000 +  0.001 * dirtyFraction;
        }

        trans.nodeCount = transactionNodes.size();
        
        boolean wroteMetaBlock = nodeStream.addNodes(trans.transactionTime, transactionNodes, trans);
        
        // TODO B. Check below code. Still needed? Did I simply this by writing a whole block?
        
        if (wroteMetaBlock && this.newIncreasedStartupDistance != -1) {
            assert newIncreasedStartupDistance > startupDistance 
                    : newIncreasedStartupDistance + ", " + startupDistance;
            startupDistance = newIncreasedStartupDistance;
            newIncreasedStartupDistance = -1;
        }
    }

    /**
     * Clears temporary references at end of transaction. Important to avoid memory leakage
     * and prepare for next transaction. Caller must hold writeLock.
     */
    private void clearTransMemory() {
        assert Thread.holdsLock(writeLock);
        this.trans = null;
        topAccessPath.clear();
        keyAccessPath.clear();
        transactionNodes.clear();
        kwi.node = null;
        oneKwi[0].node = null;
        tempPointer.node = null;
    }

    /**
     * Returns the stream position that is currently the "dirty limit". 
     * In general: nodeStream.getLength() - this.startupDistance is returned.
     * The caller must hold DB.writeLock.
     */
    private long getDirtyLimit() {
        assert Thread.holdsLock(writeLock);
        long dirtyLimit = nodeStream.getLength() - this.startupDistance;
        dirtyLimit = dirtyLimit < 0 ? 0 : dirtyLimit;
        return dirtyLimit;
    }

    /**
     * Sets the KVs directly to the in-memory data structure. This method runs with exclusive 
     * write access to the data structure (synchronized (writeLock)). However, there may be
     * concurrent readers that read with a lookup time strictly less than the transaction time
     * (trans.transactionTime). Caller must hold writeLock.
     */
    private final void setKvs() {
        //
        // 1210 Frans: Added [if (kv.keyTransformation != ...], [if (kv.valueTransformation != ...]
        // These changes do not add any measurable overhead when null; measured with test.Set.
        //

        assert Thread.holdsLock(writeLock);
        final int length = trans.kvs.length;

        for (int i = 0; i < length; i++) {
            int segmentCount;
            int lastSegmentIndex;
            KeyNode segmentRoot;
            final long[] keySegments;
            Kv kv = trans.kvs[i];

            if (kv.keyTransformation != null) {
                kv.keyTransformation.transform(trans, i);
            }

            if (kv.valueTransformation != null) {
                final byte[] previous = this.get(trans.transactionTime, kv.keySegments, 
                        trans.getData);
                kv.value = kv.valueTransformation.transform(trans.transactionTime, kv.value,
                        previous);
            }

            keySegments = kv.keySegments;

            segmentCount = keySegments.length;
            lastSegmentIndex = segmentCount - 1;
            keyAccessPath.clearFast();
            topAccessPath.clearFast();

            segmentRoot = topDS.findRoot(this, trans.transactionTime, true, topAccessPath,
                    this.transAccessData, trans.getData);
            keyAccessPath.add(Klong.NULL, segmentRoot);

            for (int i3 = 0; i3 < segmentCount; i3++) {
                assert segmentRoot.assertOk(maxNodeSize);
                
                if (i3 == lastSegmentIndex) {
                    setValue(segmentRoot, keySegments[i3], kv);
                } else {
                    segmentRoot = setNode(segmentRoot, keySegments[i3]);
                }
            }

            // Makes nodes on access path dirty if not already dirty.

            for (int i2 = 0, size = keyAccessPath.getSize(); i2 < size; i2++) {
                makeDirty(keyAccessPath.get(i2));
            }

            for (int i1 = 0, size = topAccessPath.getSize(); i1 < size; i1++) {
                makeDirty(topAccessPath.get(i1));
            }
        }
    }

    /**
     * Sets a value in the segment that has 'node' as its root node. If a Kv
     * with the key already exists, its value is overwritten.
     * 
     * @param node
     *            The segment root node.
     */
    private void setValue(KeyNode node, long compareValue, Kv kv) {
        while (!node.isSegmentLeaf()) {
            node = findNextNode(compareValue, kwi, node);
        }
        
        assert node.size <= this.maxNodeSize : "Overfull node, node.size=" + node.size 
                + ", maxNodeSize=" + maxNodeSize + ", node: " + node.toString();

        if (kv.value == null) {
            // If a delete operation.
            
            // 130514 Frans: Added delete ValueNode to transaction nodes. Needed to store choices for
            // the delete operation. But only non-noop deletes added.
            
            // Inserts a delete klong if needed.
            boolean isNoop = insertDeleteKlong(node, keyAccessPath.size - 1, compareValue);
            if (!isNoop) {
                transactionNodes.add(node);
                ValueNode valueNode = new ValueNode(null);
                transactionNodes.add(valueNode, kv.keySegments);
            }
        } else {
            transactionNodes.add(node);
            
            ValueNode valueNode = new ValueNode(kv.value);
            transactionNodes.add(valueNode, kv.keySegments);
            
            // We need to be able to fit two more klongs. A TIME klong might be needed.
            // This is sub-optimal. Sometimes a node can be added without adding a TIME klong.
            // Little to gain from optimizing this, however.
            
            // "+1" needed, there may be a need to insert a TIME klong too.
            if (node.size + 1 < this.maxNodeSize) {
                node.addKlong(trans.transactionTime, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, this.transAccessData);
            } else {
                oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                oneKwi[0].node = valueNode;
                oneKwi[0].pos = this.transAccessData;
                insertKlongs(node, keyAccessPath.size - 1, oneKwi);
            }
        }
    }

    /**
     * Ensures a klong-and-node with compareValue exists in the segment of the
     * data structure with 'segmentRoot' as the root node. If it does not exist,
     * a new klong is inserted pointing to a new node. The new node is the
     * segment root of a newly created segment. Returns the next segment root.
     */
    private KeyNode setNode(KeyNode segmentRoot, long compareValue) {
        KeyNode current = segmentRoot;
        KeyNode result;
        final Trans t = trans;

        if (t.trace) {
            out.println("setNode, depth " + keyAccessPath.size + ", compareValue "
                    + Klong.toString(Klong.compareValueToKeyKlong(compareValue)));
        }
        
        while (!current.isSegmentLeaf()) {
            current = findNextNode(compareValue, kwi, current);
            
            if (t.trace) {
                out.println("setNode, current = " + current);
            }
        }

        current.searchEq(t.transactionTime, compareValue, kwi);

        if (kwi.klong == Klong.NULL) {
            // If not found, create the node

            KeyNode child = new KeyNode(true); // New segment leaf node.

            // "+1" needed since there might be a need to insert a TIME klong too.
            if (current.size + 1 < this.maxNodeSize) {
                current.addKlong(trans.transactionTime, Klong.compareValueToKeyKlong(compareValue),
                        child, this.transAccessData);
            } else {
                oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                oneKwi[0].node = child;
                oneKwi[0].pos = this.transAccessData;
                insertKlongs(current, keyAccessPath.size - 1, oneKwi);
            }
            result = child;

            transactionNodes.add(current);
            transactionNodes.add(child);

        } else {
            // If found
            result = (KeyNode) followPointer(current, kwi.pointerIndex, true, transAccessData, t.getData);
        }

        keyAccessPath.add(kwi.klong, result);
        return result;
    }

    /**
     * Finds the next node to follow given a non-leaf node 'current' and the key
     * 'compareValue'. Note, only for SET operations (transactions). 
     * Calling thread must hold DB.writeLock.
     * 
     * @param kwi
     *            For temporary storage.
     */
    private KeyNode findNextNode(long compareValue, KlongWithPointer kwi, KeyNode current) {
        assert Thread.holdsLock(writeLock);
        current.searchLte(trans.transactionTime, compareValue, kwi);
        assert kwi.klong != Klong.NULL;
        KeyNode node = (KeyNode) followPointer(current, kwi.pointerIndex, true,
                this.transAccessData, trans.getData);
        assert node != null;
        keyAccessPath.add(kwi.klong, node);
        return node;
    }

    /**
     * Inserts one or two non-delete klongs to 'node' for the current
     * transaction. This method splits 'node' and its ancestors if needed. Write
     * access to 'node' and possibly its parents (for recursive split) is
     * required.
     * 
     * @param node
     *            Node into which to insert.
     * @param depth
     *            Depth of 'node' in the access path.
     * @param toInsert
     *            The klongs and pointers to insert. 1 or 2 long array.
     */
    private void insertKlongs(final KeyNode node, final int depth, final KlongWithPointer[] toInsert) {
        //
        // This should be the only way the DB adds klongs to KeyNodes. It is the
        // central point of code for node splitting.
        //
        // Implementation note: we allow memory allocation for a split, avoid it
        // otherwise.
        //
        // For performance, we use special code for the most common case of
        // inserting exactly one klong to a non-full node.
        //

        assert toInsert.length < 3 : "toInsert.length = " + toInsert.length;
        assert node.assertOk(maxNodeSize);

        // "+1" is needed since a TIME klong could be added along with the toInsert klongs.
        final boolean isFull = node.size + toInsert.length + 1 > this.maxNodeSize;

        if (!isFull) {
            for (int i = 0; i < toInsert.length; i++) {
                KlongWithPointer kwi = toInsert[i];
                node.addKlong(trans.transactionTime, kwi.klong, kwi.node, this.transAccessData);
                assert node.assertOk(maxNodeSize);
            }
        } else {
            // 'node' is full. We cannot append 'toInsert' to it.
            final long tTime = this.trans.transactionTime;
            KeyNode last = node.lastVersion(tTime);
            transactionNodes.add(last);
            
            assert last.assertOk(maxNodeSize);
            handleLastVersionOfFullNode(node, depth, toInsert, tTime, last);
        }
    }

    private void handleLastVersionOfFullNode(final KeyNode node, final int depth,
            final KlongWithPointer[] toInsert, final long tTime, KeyNode last) {
        final int lastSize = last.size;

        if (lastSize > this.maxNodeSize / 2) {
            // Last version is large enough to split. Split and insert.
            splitNode(node, last, depth, toInsert);
        } else {
            // Last version is small enough not to split into two nodes.
            replaceNodeWithLastVersion(tTime, last, depth, toInsert);
        }
    }

    /**
     * Appends a delete klong to 'node' if needed to delete the klong with the
     * given compare value.
     * 
     * @return True if the operation is a noop (no operation).
     */
    private boolean insertDeleteKlong(final KeyNode node, final int depth,
            final long compareValueToDelete) {
        //
        // If needed, a delete bitmap klong is added to the node for the current
        // transaction time to delete a key klong with the specified compareValue.
        // If no such key klong exists, or if it is already deleted, no action
        // is taken (it is a NOOP).
        // If 'node' ends with a delete klong of the current transaction (same transaction time), 
        // the delete klong is updated to set a delete bit for the specified compareValue.
        //
        // -- Implementation notes --
        // Loop through. Is it a noop? If not, can it be added to existing
        // delete klong of transaction or not? At end if noop, do nothing. If not, either modify
        // existing delete klong or add one to 'node'.
        //

        final short sz = node.size;
        assert sz <= this.maxNodeSize : "Bad node size: " + sz;
        long arrayTime = -1;
        long tTime = trans.transactionTime;
        long arrayDel = Klong.createDeleteBitmap();
        long del = Klong.createDeleteBitmap();
        boolean hasTransDel = false;
            // Set to true if last klong is a delete for the same time as this transaction.

        for (int i = 0; i < sz; i++) {
            long klong = node.klongs[i];
            int type = Klong.getIntType(klong);

            switch (type) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                if (arrayTime > tTime) {
                    throw new Bug("Bad state of node, arrayTime > transaction time."
                            + " arrayTime=" + arrayTime + ", tTime=" + tTime + ", node="
                            + node.toString() + ".");
                }
                break;
            case Klong.INT_TYPE_KEY:
                long arrayCompareValue = Klong.getCompareValue(klong);
                if (compareValueToDelete == arrayCompareValue) {
                    del = Klong.delete(del, i);
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                arrayDel = klong;
                if (arrayTime == tTime && i == sz - 1) {
                    hasTransDel = true;
                }
                break;
            default:
                assert false : "Bad klong type at " + i + ": " + type + ".";
            }
        }

        long union = (del | arrayDel);
        boolean isNoop = (union == arrayDel);
        
        if (!isNoop) {
            if (hasTransDel) {
                node.klongs[sz - 1] = union;
                // Direct modification, but still OK. A reader will always have a lookup
                // time < trans.transactionTime. So, a reader is guaranteed not to see
                // the delete at trans.transactionTime before the transaction completes.
                // No need to add 'node' to transaction nodes. It is there
                // already since it has a delete klong for transationTime.
            } else {                
                if (node.size + 1 < this.maxNodeSize) {
                    node.addKlong(tTime, union, null, transAccessData);
                } else {
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                    transactionNodes.add(last);
                    
                    handleLastVersionOfFullNode(node, depth, zeroKwis, tTime, last);
                }
            }
        }
        
        return isNoop;
    }

    private void replaceNodeWithLastVersion(final long tTime, KeyNode last, final int depth,
            KlongWithPointer[] toInsert) {
        // Last version is small enough not to split into two nodes, but not
        // empty.

        final KeyNode parent = getParent(depth);
        
        assert transactionNodes.contains(last) : "Expected transactionNodes to contain 'last'.";

        for (int i = 0; i < toInsert.length; i++) {
            KlongWithPointer kwi = toInsert[i];
            last.addKlong(tTime, kwi.klong, kwi.node, this.transAccessData);
        }

        if (parent == null) {
            // 'node' is the current space root. Replace it with 'last'.
            topDS.newSuperRoot(tTime, last, this.transAccessData);
            assert last.checkWithMessage() == null;
            transactionNodes.add(topDS.getSuperRoot());

        } else {
            long klong1 = keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL;

            // "+1" needed since a TIME klong might be needed too.
            if (parent.size + 1 < this.maxNodeSize) {
                parent.addKlong(trans.transactionTime, klong1, last, this.transAccessData);
            } else {
                oneKwi[0].klong = klong1;
                oneKwi[0].node = last;
                oneKwi[0].pos = this.transAccessData;
                insertKlongs(parent, depth - 1, oneKwi);
            }

            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();

            transactionNodes.add(parent);
        }
    }

    /**
     * Called to split 'node'.
     * There are three different kinds of node splits:
     * 1. 'node' is the space root node (parent == null).
     * 2. The parent is a segment leaf (the full node is a segment root).
     * 3. The parent is not a segment leaf.
     * 
     * @param node  The node that is full and needs to be split.
     * @param last
     * @param depth
     * @param toInsert
     */
    private void splitNode(final KeyNode node, KeyNode last, final int depth,
            final KlongWithPointer[] toInsert) {
        final long tTime = this.trans.transactionTime;
        final boolean isSegmentLeaf = node.isSegmentLeaf();
        final KeyNode first = new KeyNode(isSegmentLeaf);
        final KeyNode second = new KeyNode(isSegmentLeaf);
        final KeyNode parent = getParent(depth);
        trans.splitCount++;
        
        assert transactionNodes.contains(last) : "Expected 'last' to already be in transactionNodes.";

        if (parent == null) {
            if (trans.trace) {
                out.println("SPLIT, parent==null");
            }

            KeyNode newRoot = new KeyNode(false);
            long secondKlong = node.firstAndSecond(tTime, last, toInsert, first, second);
            newRoot.addKlong(tTime, Klong.EMPTY_KEY, first, this.transAccessData);
            newRoot.addKlong(tTime, secondKlong, second, this.transAccessData);

            topDS.newSuperRoot(tTime, newRoot, getAccessData());

            assert newRoot.checkWithMessage() == null;

            transactionNodes.add(newRoot);
            transactionNodes.add(topDS.getSuperRoot());
            transactionNodes.add(first);
            transactionNodes.add(second);

        } else if (parent.isSegmentLeaf()) {
            // Parent is segment leaf, so 'node' is a segment root. We need a
            // new segment root.

            if (trans.trace) {
                out.println("SPLIT, parent.isSegmentLeaf()");
            }

            KeyNode newSegmentRoot = new KeyNode(false);
            long secondKlong = node.firstAndSecond(tTime, last, toInsert, first, second);

            newSegmentRoot.addKlong(tTime, Klong.EMPTY_KEY, first, this.transAccessData);
            newSegmentRoot.addKlong(tTime, secondKlong, second, this.transAccessData);

            long klong1 = keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL;

            if (parent.size < this.maxNodeSize) {
                parent.addKlong(trans.transactionTime, klong1, newSegmentRoot, this.transAccessData);
            } else {
                oneKwi[0].klong = klong1;
                oneKwi[0].node = newSegmentRoot;
                oneKwi[0].pos = this.transAccessData;
                insertKlongs(parent, depth - 1, oneKwi);
            }

            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();
            assert newSegmentRoot.checkWithMessage() == null;

            transactionNodes.add(newSegmentRoot);
            transactionNodes.add(parent);
            transactionNodes.add(first);
            transactionNodes.add(second);

        } else {
            // Parent is not a segment leaf, so 'node' is not a segment root.

            if (trans.trace) {
                out.println("SPLIT, NOT parent.isSegmentLeaf()");
            }

            long secondKlong = node.firstAndSecond(tTime, last, toInsert, first, second);
            long firstKlong = keyAccessPath.getKlong(depth);

            twoKwis[0].klong = firstKlong;
            twoKwis[0].node = first;
            twoKwis[0].pos = this.transAccessData;
            twoKwis[1].klong = secondKlong;
            twoKwis[1].node = second;
            twoKwis[1].pos = this.transAccessData;

            insertKlongs(parent, depth - 1, twoKwis);

            assert parent.checkWithMessage() == null : parent.checkWithMessage();

            transactionNodes.add(parent);
            transactionNodes.add(first);
            transactionNodes.add(second);
        }
    }

    /**
     * Returns the parent node of a node with the given 'depth' or null if the
     * there is no parent. The "parent" is taken from this.keyAccessPath.
     * Caller must hold writeLock.
     */
    private KeyNode getParent(int depth) {
        assert Thread.holdsLock(writeLock);
        return (--depth) < 0 ? null : this.keyAccessPath.get(depth);
    }

    public long getAccessData() {
        return -cachedMemoryValue.get();
    }

    private void possiblyEvict(EvictData ed) {
        // Synch note: concurrent access must be supported.
        // We have a benign race condition here. Updates could be missed.

        if (evictBoss.evictOrNot()) {
            evict(ed);
        }
    }
    
    public void flushCache() {
        
    }

    /**
     * Runs the evict algorithm and returns the number of nodes evicted.
     */
    public final void evict(EvictData ed) {
        // Synch note: concurrent access must be supported.

        ed.pointerCount = 0;
        ed.evictCount = 0;
        evictInner(ed);
        evictBoss.reportEvictCount(ed);
    }

    private void evictInner(EvictData ed) {
        //
        // node ----> nextNode ---> next2
        //
        // Synch note: concurrent access must be supported by this method.
        //
        // Consider: should we call evict on nodes further up in three?
        //

        final Pointer pointer = ed.tempPointer;

        INode node = topDS.getSuperRoot();
        INode nextNode;
        INode next2;
        long limit = this.cachedMemoryValue.get() - evictBoss.getCacheDuration();
        limit = limit < 0 ? 0 : limit;
        // limit is the limit for accessData. Nodes accessed after limit are not evictable.

        int rand = Math.abs(evictRandom.nextInt());
        // random int used as randomness for this evict operation.

        getEvictPointer(node, rand, pointer);
        nextNode = pointer.node;

        if (nextNode == null) {
            // Only superRoot is cached, nothing to evict.
            assert node.getMemoryPointerCount() == 0 : "Count is " + node.getMemoryPointerCount()
                    + " for node " + node + ".";
            return;
        }

        while (true) {
            getEvictPointer(nextNode, rand, pointer);
            next2 = pointer.node;

            if (next2 == null) {
                break;
            }

            // Here we go to the next deeper level.

            node = nextNode;
            nextNode = next2;
            next2 = null;
        }

        // Here, we have selected a node, 'node' to process.

        evict(node, limit, ed);
    }

    /**
     * Evicts all pointers in the node that are evictable.
     */
    private void evict(INode node, long limit, EvictData ed) {
        // NOTE This is awkward.
        switch (node.getType()) {
        case INode.TYPE_KEY_NODE:
            evictKeyNode((KeyNode) node, limit, ed);
            break;
        case INode.TYPE_TOP_NODE:
            evictTopNode((TopNode) node, limit, ed);
            break;
        default:
            throw new Bug("Unexpected node type: " + node.getClass().getName());
        }
    }

    private void evictTopNode(TopNode node, long limit, EvictData ed) {
        INode pointee;
        ed.pointerCount += 1; // +1 for root pointer.

        pointee = node.rootPointer;
        if (pointee != null && !pointee.isDirty()
                && AccessData.getAccessTimeNoChecks(node.rootPointerPos) <= limit) {

            // Probably an evictable pointer, but we must synch to make an
            // atomic read plus
            // subsequent write.

            synchronized (this.getPointerLock(node, 0)) {
                pointee = node.rootPointer;
                if (pointee != null && !pointee.isDirty()
                        && AccessData.getAccessTime(node.rootPointerPos) <= limit) {
                    node.rootPointerPos = pointee.getSpos();
                    node.rootPointer = null;
                    ed.evictCount++;
                }
            }
        }

        for (int i = 0; i < node.pointersLength; i++) {
            if (node.pointersPos[i] == Spos.NULL) {
                // If "null" pointer. Not all pointer index values have actual
                // pointers.
                continue;
            }

            ed.pointerCount++;
            pointee = node.pointers[i];

            if (pointee != null && !pointee.isDirty() && node.pointersPos[i] != Spos.NULL
                    && AccessData.getAccessTimeNoChecks(node.pointersPos[i]) <= limit) {

                // Probably evictable pointer

                synchronized (this.getPointerLock(node, i + 1)) {
                    pointee = node.pointers[i];
                    if (node.pointers[i] != null
                            && AccessData.getAccessTime(node.pointersPos[i]) <= limit) {
                        node.pointersPos[i] = pointee.getSpos();
                        node.pointers[i] = null;
                        ed.evictCount++;
                    }
                }
            }
        }
    }

    private void evictKeyNode(KeyNode node, long limit, EvictData ed) {
        //
        // getAccessTimeNoChecks() used when not in synch. Possibly concurrently
        // modified.
        //
        // NOTE Could be moved to KeyNode class if DB.getPointerLock() is made
        // available to the method (ClassForMe approach).
        //

        int sz = node.size;
        int pointerCount = 0;
            // Number of TYPE_KEY klongs. Points to ValueNode or KeyNode.
            // Delete and time klongs do not have corresponding pointers.

        for (int i = 0; i < sz; i++) {
            if (Klong.getType(node.klongs[i]) != Klong.TYPE_KEY) {
                continue;
            }

            pointerCount++;
            INode pointee = node.pointers[i];

            if (pointee != null && !pointee.isDirty()
                    && AccessData.getAccessTimeNoChecks(node.pos[i]) <= limit) {
                synchronized (getPointerLock(node, i)) {
                    pointee = node.pointers[i];

                    if (pointee != null && !pointee.isDirty()
                            && AccessData.getAccessTime(node.pos[i]) <= limit) {
                        node.pos[i] = pointee.getSpos();
                        node.pointers[i] = null;
                        ed.evictCount++;
                    }
                }
            }
        }

        ed.pointerCount += pointerCount;
    }

    /**
     * Sets p.node and p.index. p.node will be null if none found. Set p with a
     * node and its index. Only memory pointers are considered.
     */
    private void getEvictPointer(INode node, int rand, Pointer p) {
        // Returns a random in-memory pointer and its pointer index written to
        // p.

        switch (node.getType()) {
        case INode.TYPE_KEY_NODE:
            getEvictPointer((KeyNode) node, rand, p);
            break;
        case INode.TYPE_TOP_NODE:
            getEvictPointer((TopNode) node, rand, p);
            break;
        default:
            p.node = null;
            p.pos = Spos.NULL;
            p.index = -1;
        }
    }

    private void getEvictPointer(TopNode topNode, int rand, Pointer p) {
        int length = topNode.pointersLength + 1;
        int index;
        p.node = null;
        p.index = -1;

        for (int i = 0; i < length; i++) {
            index = rand % length;
            assert index >= 0 : "index = " + index;

            if (index == 0) {
                p.node = topNode.rootPointer;
                if (p.node != null) {
                    p.index = index;
                    break;
                }
            } else {
                p.node = topNode.pointers[index - 1];
                if (p.node != null) {
                    p.index = index;
                    break;
                }
            }

            rand++;
        }
    }

    private void getEvictPointer(KeyNode keyNode, int rand, Pointer p) {
        int size = keyNode.size;
        p.node = null;
        p.index = -1;

        for (int i = 0; i < size; i++) {
            int index = rand % size;

            synchronized (getPointerLock(keyNode, index)) {
                p.node = keyNode.pointers[index];
            }

            if (p.node != null) {
                p.index = index;
                break;
            }

            rand++;
        }
    }

    /**
     * Reports a warning. Current implementation prints to DB.out - standard
     * database output.
     */
    public void warn(String message, Throwable t) {
        out.println("WARNING. " + message);
        t.printStackTrace(out);
    }

    /**
     * Returns current super root.
     */
    public final TopNode getSuperRoot() {
        return topDS.getSuperRoot();
    }

    /**
     * Creates and returns a DB.Builder that can create a DB object. The
     * "official" and only public way of creating a DB.
     */
    public static Builder builder() {
        return new Builder();
    }

    /**
     * An object of this class is used to properly build a DB object.
     */
    public static class Builder {
        private Clock clock;
        private boolean disableStreamWrite;
        private int maxNodeSize;
        private int startupDistance;
        private IEvictBoss evictBoss;
        private long retainDuration;
            // Number of time units to retain data available for lookups.
        private DatabaseId id;
            // Database ID if new database, or null.
        private List<StreamInfo> streamInfos;
        
        static class StreamInfo {
            String name;
            AppendOnlyStream stream;
            int bufferSize;
            int bufferTime;
        }

        private Builder() {
            streamInfos = new ArrayList<StreamInfo>();
            
            // Default settings for DB.
            
            //startupDistance = 10 * 1000000;
            startupDistance = 20 * 1000000;    // 130707 Frans: new default startup distance.
            clock = new SystemClock();
            evictBoss = new FixedDurationEvictBoss();
            maxNodeSize30();
            
            //retainDuration = Clock.UNITS_PER_SEC * 3600L * 24 * 7;
            retainDuration = Long.MAX_VALUE;   
                // 130707 Frans: default retain duration = forever. Was one week.
        }

        /**
         * Returns index to stream with given name, or -1 if no stream with the given 
         * name exists in streamInfos.
         */
        private int indexOfStream(String name) {
            if (name == null) throw new IllegalArgumentException("name == null");
            final int size = streamInfos.size();
            int result = -1;
            
            for (int i = 0; i < size; i++) {
                StreamInfo info = streamInfos.get(i);
                if (info.name.equals(name)) {
                    result = i;
                    break;
                }
            }
            
            return result;
        }
        
        /**
         * Chooses a non-default clock to use for the database.
         */
        public Builder clock(Clock clock) {
            this.clock = clock;
            return this;
        }

        /**
         * Sets the database ID. This method is suitable for deterministic
         * testing. This setting only applies for non-existent databases.
         */
        public Builder id(DatabaseId id) {
            if (id == null) {
                throw new IllegalArgumentException("id == null not allowed");
            }

            this.id = id;
            return this;
        }

        public Builder maxNodeSize8() {
            this.maxNodeSize = 8;
            return this;
        }

        public Builder maxNodeSize14() {
            this.maxNodeSize = 16 - 2;
            return this;
        }

        public Builder maxNodeSize30() {
            this.maxNodeSize = 32 - 2;
            return this;
        }

        public Builder maxNodeSize62() {
            this.maxNodeSize = 64 - 2;
            return this;
        }

        public Builder startupDistance(int startupDistance) {
            if (startupDistance < 10) {
                throw new IllegalArgumentException("Too small, " + startupDistance);
            }

            this.startupDistance = startupDistance;
            return this;
        }

        /**
         * Use an internal test clock together with DB.setTime to handle the
         * time. Suitable for testing.
         */
        public Builder testClock() {
            this.clock = new KTestClock();
            return this;
        }

        /**
         * Use the system clock (System.currentTimeMillis()) as the database
         * time.
         */
        public Builder systemClock() {
            this.clock = new SystemClock();
            return this;
        }
        
        public Builder retainDuration(long retainDuration) {
            final long MIN = 1 * Clock.UNITS_PER_SEC;
            
            if (retainDuration < 0) {
                throw new IllegalArgumentException("Negative retainDuration not allowed.");
            }
            
            if (retainDuration < MIN) {
                throw new IllegalArgumentException("retainDuration is too small, must be at " +
                		"least one second (" + MIN + "), was " + retainDuration + ".");
            }
            
            this.retainDuration = retainDuration;
            return this;
        }
        
        public Builder retainForever() {
            return retainDuration(Long.MAX_VALUE);
        }

        /**
         * Sets a non-default evict boss. The evict boss decides when to evict
         * nodes from memory.
         */
        public Builder evictBoss(IEvictBoss evictBoss) {
            this.evictBoss = evictBoss;
            return this;
        }

        public Builder noEvict() {
            this.evictBoss = new NoEvictBoss();
            return this;
        }
        
        /**
         * Sets main stream.
         */
        public Builder mainStream(AppendOnlyStream appendOnlyStream) {
            if (this.streamInfos.size() == 0) {
                stream("main", appendOnlyStream);
            } else {
                StreamInfo info = new StreamInfo();
                info.name = "main";
                info.stream = appendOnlyStream;
                info.bufferSize = StorageManager.DEFAULT_BUFFER_SIZE;
                info.bufferTime = StorageManager.DEFAULT_BUFFER_TIME;
                
                streamInfos.set(0, info);
            }
            
            return this;
        }
        
        /** 
         * Adds a storage stream, default buffer parameters are used.
         * If 'name' is the same as an existing stream, the existing one is replaced.
         */
        public Builder stream(String name, AppendOnlyStream aos) {
            if (streamInfos.size() == 0) {
                return stream(name, aos, 
                        StorageManager.DEFAULT_BUFFER_SIZE, 
                        StorageManager.DEFAULT_BUFFER_TIME);
            } else {
                return stream(name, aos,
                        StorageManager.DEFAULT_REPLICA_BUFFER_SIZE,
                        StorageManager.DEFAULT_REPLICA_BUFFER_TIME);
            }
        }
        
        /** 
         * Adds a storage stream with the given buffer parameters.
         * If 'name' is the same as an existing stream, the existing one is replaced.
         * 
         * @param name
         *      Name of the stream. The "main" stream is special.
         * @param stream
         *      The output database stream.
         * @param bufferSize
         *      Buffer size in bytes.
         * @param bufferTime  
         *      Maximum time in milliseconds to buffer the data 
         *      before the buffer is flushed.
         */
        public Builder stream(String name, AppendOnlyStream stream, int bufferSize, int bufferTime) {
            if (name == null) {
                throw new IllegalArgumentException("name == null not allowed");
            }
            
            if (stream == null) {
                throw new IllegalArgumentException("stream == null not allowed");
            }
            
            if (bufferSize < 0) {
                throw new IllegalArgumentException("Illegal bufferSize, " + bufferSize + ".");
            }
            
            if (bufferTime < 0) {
                throw new IllegalArgumentException("Bad bufferTime, " + bufferTime + ".");
            }
            
            if (bufferSize < 100) {
                bufferSize = 100;
            }
            
            if (bufferTime < 10) {
                bufferTime = 10;
            }
            
            StreamInfo info = new StreamInfo();
            info.name = name;
            info.stream = stream;
            info.bufferSize = bufferSize;
            info.bufferTime = bufferTime;
            
            int index = this.indexOfStream(name);
            if (index == -1) {
                streamInfos.add(info);
            } else {
                streamInfos.set(index, info);     // replaces previous value
            }
            
            return this;
        }
        
        /**
         * For testing, it disables all writes to 'appendOnlyStream' and the serialization of
         * stream nodes.
         */
        public Builder disableStreamWrite() {
            this.disableStreamWrite = true;
            return this;
        }

        /**
         * Use the default unit test setup. No write to disk, a deterministic
         * clock is used. The node stream is an in-memory stream.
         * Short buffer time (10 ms) for fast tests.
         */
        public Builder testSetup() {
            testClock();
            evictBoss = new NoEvictBoss();
            stream("main", new MemoryStream(), 100*1000, 10);
            retainForever();
            id = DatabaseId.getTestId();
            return this;
        }
        
        /**
         * Use the default unit test setup and a specified stream.
         * Short buffer time (10 ms) for fast tests.
         */
        public Builder testSetup(AppendOnlyStream stream) {
            testSetup();
            stream("main", stream, 100*1000, 10);
            
            //testClock();
            //evictBoss = new NoEvictBoss();
            //stream("main", stream, 100*1000, 10);
            //retainForever();
            //id = DatabaseId.getTestId();
            return this;
        }

        public Db build() {
            //
            // At this time, we know all DB settings. Time to create the DB object.
            //

            if (streamInfos.size() == 0) {
                throw new IllegalStateException("No streams. At least one is required.");
            }

            return new Db(this);
        }

        /**
         * Same as calling done() and then start() on the returned DB object.
         * 
         * @throws StreamIoException
         * @throws StreamFormatException
         */
        public Db start() {
            Db db = build();
            db.start();
            return db;
        }
    }

    /**
     * A listener ("handler") for the transactionCompleted event.
     */
    public static interface TransactionListener {

        /**
         * Exceptions specified below are allowed since SpaceReclaim needs to
         * run database transactions to fulfill its need. Those transactions may
         * throw DBStreamFormatException, DBStreamIOException. In addition,
         * DBDataException may be throws by SpaceReclaim.
         * 
         * @throws StreamFormatException
         * @throws StreamIoException
         * @throws InternalDataException
         */
        public void transactionCompleted(Trans t);
    }
    
    /**
     * Unit tests that need access to private fields. Use sparingly, put tests in DBTester
     * or elsewhere if possible.
     */
    public static class Tester {
        public static void testStartupDistanceIncrease() {
            // Checks increase of startup distance. Increase not affective immediately, but
            // after the stream meta block has been written to stream.
            
            byte[] value = new byte[100*1000];
            MemoryStream stream = new MemoryStream();
            Db db = Db.builder().mainStream(stream).startupDistance(1*1000000).start();
            Trans trans = Trans.builder().set("1", value).build();
            db.execute(trans);
            
            Assert.assertTrue(trans.lastSpos < RecoverableStream.META_BLOCK_DISTANCE);
            Assert.assertEquals(-1, db.newIncreasedStartupDistance);
            
            db.setStartupDistance(2*1000000);
            Assert.assertEquals(1*1000000, db.getStartupDistance());
            Assert.assertEquals(2*1000000, db.newIncreasedStartupDistance);
            
            int index = 10;
            
            while (trans.lastSpos <= RecoverableStream.META_BLOCK_DISTANCE) {
                trans = Trans.builder().set("" + index, value).build();
                db.execute(trans);
                index++;
            }
            
            Assert.assertEquals(2*1000000, db.getStartupDistance());
            Assert.assertEquals(-1, db.newIncreasedStartupDistance);
            
            db.stop();
        }
    }
}

/*

======== Log ========

Different IKP values.

//public static final String INTERNAL_KEY_PREFIX = Util.identity("/#ikp/");  // ok, used now!

//public static final String INTERNAL_KEY_PREFIX = Util.identity("/dikp/"); // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".db/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".dc/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".dbx/");   // fails!
       // bergdb.pubimp.PubTesterComposite.testEqAndStart2
       // bergdb.pubimp.PubTesterComposite.testStart2
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".xx/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity("fml/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity("fmlx");   // OK
//public static final String INTERNAL_KEY_PREFIX = Util.identity("./");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".db2/");   // fails like .dbx/
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".db/a-longer-dir/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity(".db333444/");   // ok
//public static final String INTERNAL_KEY_PREFIX = Util.identity("55555");   // fails like .dbx/
//public static final String INTERNAL_KEY_PREFIX = Util.identity("\u0000i/");   // Works!
//public static final String INTERNAL_KEY_PREFIX = Util.identity("\u0000i/");   // Works!


======== Concurrency ========
 
130122 Frans. The concurrency implementation of DB is fast and
non-conventional. The advantage is that readers (threads calling
DB.get()/getMany()) will never block on anything but stream reads. Yes,
really never! This is independent on what a writer does.
 
---- The essence ----
 
An initialized DB instance is essentially only used through the three methods
get(), getMany() and execute(Trans). A thread that calls get()/getMany() is
called a *reader* while a thread that calls execute() is called a *writer*.
The core part of execute() runs holding a lock called DB.writeLock. So,
execute() is called in serial, one thread at a time. I have measured
throughput of small transactions at 100,000 transactions/s, so the
exclusive-write-access does not result in bad performance. Likely, the
underlying storage device will limit the performance.

All transactions of BergDB are ACID transactions. Using an SQL term, the
isolation level is serializable (the highest isolation level) with maintained
performance.
 
A writer published its writes (modifications to data) for readers by an empty
synchronized block. See code fragment below.
     
    t.transactionTime = dbClock.transactionBegin(); 
    setKVs(); 
    synchronized (readSynch) {} 
    dbClock.transactionEnd();
 
Readers are guaranteed to see the changes since the read methods
(get/getMany) also synchronize on readSynch in the beginning of the methods.
See code fragment below.

synchronized (readSynch) {} actualLookupTime =
dbClock.timeForGet(requestedLookupTime);
 
The memory writes made by the writer can in general become visible to readers
before the synch operation. The execute() method is however designed in a
particular way. The writes by the writer preserves the previous states - a
lookup with a given actualLookupTime will always give the same result. So,
readers can access the database while the writer is executing transactions.
The result of a transaction will never become visible to a read until the
reader will use an actualLookupTime that is equal or greater the the
transaction time of the transaction.
 
Note that this approach requires a lot from the writer. Any memory write may
or may not become visible to concurrent readers and possibly these writes can
become visible in another order than the order observed by the writer. This
is how the Java Memory Model works
(http://jeremymanson.blogspot.se/2008/11/what-volatile-means-in-java.html).
 
The dbClock object in the code above ensures that actualLookupTime of any
lookup (read operation) is less than the transaction time of any running or
future transaction.
 
---- Initialization ----
 
The construction of the DB instance and DB.start() (database startup) are
protected by the code holding both the locks DB.writeLock and DB.readSynch.
All changes of the init stage should thus be available to any writer thread
and any reader thread since that synchronize on writeLock/readSynch before
any memory reads.
 
---- KeyNode ----
 
The long[] klongs field of KeyNode is important. It has valid klongs in the
range[0..size-1] where "size" is the volatile short field KeyNode.size. This
volatile size if key to the concurrency implementation. Once KeyNode.size is
increased (it never decreases) by the writer all other changes to the KeyNode
needed to read the new range of klongs [0..newSize-1] has been made by the
writer.
 
Readers that want to access the state of a KeyNode must *first* read
KeyNode.size before any other fields of the object. This ensures that all
memory writes required to read klongs in the range [0..size-1] are visible to
the reader.
 
Readers must not read klongs that are not in the currently valid klongs array
range [0..size-1].
 
======== maxNodeSize ========
 
//maxNodeSize = 16 - 2; 
maxNodeSize = 32 - 2; 
//maxNodeSize = 64 - 2;
  
32-2 works best on Rose for Get. Possibly more on computers with // larger cache
lines. Rose has 64 byte cache line. Linda has 64 byte cache line.
(Linux command: sudo cat /sys/devices/system/cpu/cpu0/cache/index0/coherency_line_size) 
-2 is used to have margin. -1 did not work on Rose. 
For Set ops, its is less sensitive. Everything from 8-2 to 128-2 is reasonable. 
(does not degrade performance more than 20% from optimum).

*/