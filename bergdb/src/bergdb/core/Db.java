package bergdb.core;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.Bug;
import bergdb.common.IWarner;
import bergdb.common.NullProgressListener;
import bergdb.common.ProgressListener;
import bergdb.common.Util;
import bergdb.dag.AccessData;
import bergdb.dag.Choices;
import bergdb.dag.Constants;
import bergdb.dag.Dag;
import bergdb.dag.EvictData;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.NodeVisitor;
import bergdb.dag.Pointer;
import bergdb.dag.PutData;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.TransNodes;
import bergdb.dag.TransSeq;
import bergdb.dag.ValueNode;
import bergdb.dag.Dag.PointerListener;
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
 * <li>getOne()</li>
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
public class Db implements IWarner {
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
     * 131023: changed from /#ikp/ to "/#i/", destroyed binary compatibility.
     */
    public static final String INTERNAL_KEY_PREFIX = Util.identity("/#i/");
    
    private static final long[] DUMMY_KEY = Keys.toSegments(INTERNAL_KEY_PREFIX + "-dummy");
    
    private static final int STATE_ZERO = 1;
    private static final int STATE_STARTING = 2;
    private static final int STATE_ACTIVE = 3;
    private static final int STATE_STOPPING = 4;

    private final WriteLock writeLock;
        // Global write lock. Held when STM stuff is done and while transaction serialized to bytes.
    private final ReadSync readSync;
        // Lock used to make sure writes from DB(), start(), execute(), are published
        // by the writer and made visible to readers calling get(), getMany().
        // It is typically used with an empty block: "synchronized (readSynch) {}".
        
    private final Object[] pointerLocks;
    private final int pointerLocksLength;
        // Locks to synchronized node pointers. See followPointer().
    private final IKeyModSet keyModSet;
    private final NodeStream nodeStream; // IO for DB to read/append nodes.
    private final StorageManager storageManager;
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

    private final DbClock dbClock;
    private final IEvictBoss evictBoss;
    private final PrintStream out;
    private final Builder builder;   // stored for use by Graph.Builder. See startinner().
    
    private long startupDistance; 
        // Current startupDistance that affects getDirtyLimit().
        // Sync note: protected by writeLock.

    // ---- Listeners ----
    
    private final TransactionListener reclaimTransactionListener;

    // ---- Working data for write access ----
    // Must only be accessed from threads holding writeLock.
    
    private final StartupPos startupPos;
    
    /** PutData, set to non-null together with graph. */
    private PutData pd;
    
    /** The nodes updated for the current transaction. To be written to the stream. */
    private final TransNodes transNodes;
    
    /** Current transaction while writeLock is held. */
    private Trans trans;
    
    /** End stream position of last transaction; used by Db.sync(). */
    private long lastSposOfLastTrans;
    
    /** First spos of last transaction to have executed. */
    @SuppressWarnings("unused")
    private long sposOfLastTrans;
    

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

    public final static long MIN_CACHE_MEMORY_VALUE = Constants.MIN_CACHE_MEMORY_VALUE;
    
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
    
    private long nodesWritten = 0;
        // Number of nodes written since database started.
    private long ordinaryNodesWritten = 0;
    
    // Below two, protected by writeLock.
    private double dirtyFraction100 = 0.10;
    private double dirtyFraction1000 = 0.10;
    
    // ---- Graph ----
    
    private Dag graph;
    
    
    /**
     * Private constructor, only DB.Builder calls it. Wires dependencies based
     * on Builder settings.
     */
    private Db(Builder b) {
        writeLock = new WriteLock();
        readSync = new ReadSync();
        
        pointerLocksLength = 128;
        pointerLocks = new Object[pointerLocksLength];
        for (int i = 0; i < pointerLocksLength; i++) {
            pointerLocks[i] = new Object();
        }
        
        builder = b;

        evictRandom = new Random(0);      // pseudo-random, but deterministic.
        transNodes = new TransNodes();
        keyModSet = new KeyModSet2();
 
        this.startupDistance = b.startupDistance;
        this.startupPos = new StartupPos(0);
        
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
        synchronized (readSync) {}
        synchronized (writeLock) {}
    }
    
    /**
     * Useful for testing; violates Law of Demeter.
     */
    public Dag getGraph() {
        return graph;
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

    public long getStartupDistance() {
        synchronized (writeLock) {
            return this.startupDistance;
        }
    }
    
    public String getStartupDistanceH() {
        long sd;
        int metaSd;
        
        synchronized (writeLock) {
            sd = this.startupDistance;
            metaSd = this.nodeStream.getMetaBlock().getStartupDistance();
        }
        
        return "DB.startupDistance = " + sd + ", metablock sd = " + metaSd;
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
    
    public long getNodesWritten() {
        synchronized (writeLock) {
            return this.nodesWritten;
        }
    }
    
    public long getOrdinaryNodesWritten() {
        synchronized (writeLock) {
            return this.ordinaryNodesWritten;
        }
    }
    
    /**
     * Suggests a new startup distance.
     * If the startup distance is reduced drastically, this method
     * can cause a large transaction to run. It is recommended that the 
     * startup distance is reduced no more than 10M for every call to this 
     * method. Call this method repeatedly to reduce the startup distance
     * more than 10M.
     */
    public void setStartupDistance(long newDistance) {
        //
        // A dummy transaction of size >= META_BLOCK_DISTANCE is written
        // to the stream to ensure that the new value of startupDistance is 
        // stored in a meta block in the stream.
        //
        
        if (newDistance < 0) {
            throw new IllegalArgumentException("Bad newDistance: " + newDistance + ".");
        }
        
        long min = RecoverableStream.META_BLOCK_DISTANCE * 2;
        long max = 1000*1000000;
        
        newDistance = newDistance < min ? min : newDistance;
        newDistance = newDistance > max ? max : newDistance;
        
        int dist = (int) newDistance;
        byte[] dummyValue = new byte[RecoverableStream.META_BLOCK_DISTANCE];
        
        synchronized (writeLock) {
            this.startupDistance = newDistance;
            this.nodeStream.getMetaBlock().setStartupDistance(dist);
            this.execute(Trans.builder().put(DUMMY_KEY, dummyValue).build());
        }
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
        synchronized (readSync) {}
        return reclaim.getFirstAvailableLookupTime();
    }

    public long getFirstAvailablePos() {
        synchronized (readSync) {}
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
        // Note, the dummy write followed by syncStrong call are needed to make
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
                        progressNote[0] = "Almost done, waiting for syncString...";
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
                Trans trans = Trans.builder().put(DUMMY_KEY, new byte[0]).build();
                Db.this.execute(trans);
                Db.this.syncStrong(trans.lastSpos);

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

    public final Object getWriteLock() {
        return writeLock;
    }
    
    /**
     * Returns the readSynch lock Object.
     */
    public final Object getReadSynch() {
        return readSync;
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
        start(Db.DO_NOTHING_START_LISTENER);
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
    public void start(StartListener listener) {
        synchronized (writeLock) {
            synchronized (readSync) {
                startInner(listener);
            }
        }
    }
    
    /**
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws BadReplicaException
     * @throws IllegalDbStateException
     */
    private void startInner(StartListener listener) {
        if (state != STATE_ZERO) {
            throw new IllegalDbStateException("Db has been started already, "
                    + "start() should be called once only; Db state is: " 
                    + getStateName(state) + ".");
        }

        storageManager.checkStreamIds();
        
        try {
            storageManager.syncStreams(new NullProgressListener());
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        // Inits stream with primordial state (two nodes) if needed.
        
        if (nodeStream.getLength() == 0) {
            createInitialStreamState();
        }

        // Recovers stream, reads meta block in stream.

        nodeStream.recover();

        // An assertion

        if (Util.hasOnlyZeros(nodeStream.getMetaBlock().getId())) {
            throw new IllegalStateException("Invalid database ID, only zero bytes.");
        }

        // Startup phase
        
        this.startupDistance = nodeStream.getMetaBlock().getStartupDistance();
        if (startupDistance <= 0) {
            throw new StreamFormatException("Bad value of startupDistance in meta " +
            		"block of stream: " + startupDistance + ".");
        }
        this.startupPos.set(nodeStream.getMetaBlock().getStartupPos());
        
        listener.startupDistance(this.startupDistance);
        
        //long pos1 = nodeStream.getPosOfLastCompletedTrans();
        //
        //long startPos = pos1 - (startupDistance + 1);
        //startPos = startPos < 0 ? 0 : startPos;
        //
        
        long startPos = startupPos.get();
        listener.startPos(startPos);
        
        // posMap is a map from spos of a node to the node itself.
        // nextMap is a map from previous spos of a node to the node itself.

        HashMap<Long, INode> posMap = new HashMap<Long, INode>();
        HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // sposPrevious
                                                                   // -> Node

        TransSeq seq = new TransSeq();
        
        long lastTransactionTime = 0;

        NodeStream.TransIterator ti = nodeStream.new TransIterator(startPos);
        while (ti.next()) {
            if (ti.nextTransPos < startPos) {
                continue; // We can skip forward here
            }
            
            listener.tpos(ti.tpos);

            lastTransactionTime = ti.getTransactionTime();
            ArrayList<INode> tnodes = new ArrayList<INode>();

            NodeStream.NodeIterator ni = ti.getNodeIterator();
            while (ni.next()) {
                INode node = ni.node;
                if (node.isTopOrKeyNode()) {
                    tnodes.add(node);
                }
                posMap.put(node.getSpos(), node);
                long prev = ni.sposPrevious;
                if (prev != Spos.NULL) {
                    nextMap.put(prev, node);
                }

                this.cachedMemoryValue.addAndGet(node.getMemSize());
            }
            
            INode[] nodeArray = new INode[tnodes.size()];
            tnodes.toArray(nodeArray);
            seq.add(new TransSeq.Tset(nodeArray, ti.getTpos(), ti.getLastPos()));
        }

        dbClock.setLastTransactionTime(lastTransactionTime);

        Dag.Builder b = Dag.builder();
        b.nodeReader(nodeStream);
        setMaxNodeSize(b);
        
        this.graph = b.createFromStreamNodes(getAccessData(), posMap, nextMap, seq);
        
        this.pd = graph.newPutData();
        this.pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeChanged(TopNode node) {
                transNodes.addTopNode(node);
            }
            
            public void newValueNode(ValueNode node, long[] key) {
                transNodes.addValueNode(node, key);
            }
            
            public void keyNodeChanged(KeyNode node) {
                transNodes.addKeyNode(node);
            }
        };

        this.state = STATE_ACTIVE;

        reclaim.initFromDb();
            // state = STATE_ACTIVE needed before this method.
    }

    private void setMaxNodeSize(Dag.Builder b) {
        switch (builder.maxNodeSize) {
        case 62:
            b.maxNodeSize62();
            break;
        case 30:
            b.maxNodeSize30();
            break;
        case 14:
            b.maxNodeSize14();
            break;
        case 8:
            b.maxNodeSize8();
            break;
        case 6:
            b.maxNodeSize6();
            break;
        default:
            throw new IllegalStateException("maxNodeSize = " + builder.maxNodeSize);
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
        synchronized (readSync) {};
        
        if (state == STATE_STOPPING) {
            return;
        }
        
        state = STATE_STOPPING;
        synchronized (readSync) {};
        storageManager.stop();
    }
    
    /**
     * Stops the database, flushes the storage streams and releases resources; 
     * for example closes open files and network sockets.
     * This method does what stop() does and more.
     */
    public void close() {
        synchronized (readSync) {};
        
        if (state == STATE_STOPPING) {
            return;
        }
        
        synchronized (this.writeLock) {
            if (state == STATE_STOPPING) {
                return;
            }
            
            state = STATE_STOPPING;
            
            synchronized (readSync) {};
        }
            
        // Here, no write op is running or will be started.
        // No read op (get) will be started, but may be running.
        
        storageManager.close();
    }
    
    public void finalize() {
        stop();
    }
    
    private void createInitialStreamState() {
        KeyNode root = new KeyNode();
        TopDs top;
        
        long tt = dbClock.transactionBegin();
        try {
            top = TopDs.createFromFirstRoot(tt, root, AccessData.DEFAULT_ACCESS_DATA);
        } finally {
            dbClock.transactionEnd();
        }
        
        this.transNodes.addKeyNode(root);
        this.transNodes.addTopNode(top.getSuperRoot());
        
        this.trans = Trans.builder().build();
        
        DatabaseId id = (databaseIdFromBuilder == null) ? new DatabaseId() : databaseIdFromBuilder;
        nodeStream.getMetaBlock().setId(id.getBytes());
        nodeStream.getMetaBlock().setStartupPos(0);
        
        this.appendNodesToStream();
        this.clearTransMemory();
    }
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and
     * development.
     */
    public void printGraph(PrintStream out) {
        graph.printGraph(out);
    }
    
    /**
     * Creates and returns a new GetData object for use with the getOne() method.
     */
    public GetData newGetData() {
        return graph.newGetData();
    }
    
    /**
     * Creates and returns a new GetMany object for use with the getMany() method.
     */
    public GetMany newGetMany() {
        return graph.newGetMany();
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
    public byte[] getOne(long lookupTime, long[] keySegments, GetData gd) {
        //
        // Few assumptions of previous state of gd are assumed. db.kwi must be non-null, however.
        //

        assert gd != null;
        assert gd.kwi != null;

        // Makes sure writes from startup and execute() are visible.
        synchronized (readSync) {}

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

        byte[] result = null;

        long time = dbClock.timeForGet(lookupTime);
        // Limits lookup time so it strictly less than the transaction time of
        // any running
        // or future transaction.
        gd.actualLookupTime = time;
        gd.nodeDepth = 0;

        result = graph.getOne(gd.actualLookupTime, keySegments, gd);

        getOpCount.incrementAndGet();
        return result;
    }
    
    /**
     * Follows the pointers in the DB graph from the super top node using the given 
     * node index choices.
     * Useful for testing.
     */
    public INode findNode(int[] choices, GetData gd) {
        return graph.findNode(choices, gd);
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
        // Note, multiple get operations may be running in parallel.
        // All data used must be thread safe. Temporary, operation-local data is stored in 
        // the 'g' object.
        //

        assert g.result != null;
        assert g.result.size() == 0 : "g.result.size() not 0, but " + g.result.size();
        assert g.stopCondition != null;

        synchronized (readSync) {}
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
        
        g.gd.accessData = getAccessData();

        possiblyEvict(ed);

        g.actualLookupTime = dbClock.timeForGet(g.lookupTime);
            // Limits lookup time so it strictly less than the transaction time of
            // any running or future transaction.

        
        graph.getMany(g);
    }

    
    /**
     * Waits until ordinary durability has been achieved for stream position 'spos'.
     * 
     * @throws StreamIoException
     */
    public void sync(long spos) {
        try {
            storageManager.sync(spos);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /**
     * Waits until strong durability has been achieved for stream position 'spos'.
     * 
     * @throws StreamIoException
     */
    public void syncStrong(long spos) {
        try {
            storageManager.syncStrong(spos);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /**
     * Waits for last stream position to be considered durable according to ordinary sync.
     * 
     * @throws StreamIoException
     */
    public void sync() {
        long spos;
        
        synchronized (writeLock) {
            spos = this.lastSposOfLastTrans;
        }
        
        sync(spos);
    }
    
    /**
     * Waits for last stream position to be considered durable according to strong sync.
     * 
     * @throws StreamIoException
     */
    public void syncStrong() {
        long spos;
        
        synchronized (writeLock) {
            spos = this.lastSposOfLastTrans;
        }
        
        syncStrong(spos);
    }
    
    /**
     * This method visits all nodes in memory to check that there state is consistent
     * and that they are not too dirty.
     * This method locks on both writeLock and readSynch. Use for testing only.
     */
    public void checkNodes() throws AssertionError {
        synchronized (writeLock) {
            synchronized (readSync) {
                checkNodeInner();
            }
        }
    }
    
    private void checkNodeInner() throws AssertionError {
        final long[] counters = new long[4];
            // top, key, value, dirty, total
        //final long dirtyLimit = this.getDirtyLimit();
        //long lastTransSize = this.lastSposOfLastTrans - this.sposOfLastTrans;
        //final long dLimit = dirtyLimit - lastTransSize;
        
        NodeVisitor visitor = new NodeVisitor() {
            public void visit(TopNode node) {
                counters[0]++;
                //checkTooDirty(node);
            }

            public void visit(KeyNode node) {
                counters[1]++;
                node.check();    // throws AssertionError if bad.
                //checkTooDirty(node);
            }

            public void visit(ValueNode node) {
                counters[2]++;
                //checkTooDirty(node);
            }
            
            /*private void checkTooDirty(INode node) {
                long spos = node.getSpos();
                boolean isDirty = node.isDirty();
                
                if (spos == Spos.NULL) {
                    throw new AssertionError("spos of node is Spos.NULL. node: " + node);
                }
                
                if (isDirty) counters[3]++;
                
                if (isDirty && spos <= dLimit) {
                    long length = Db.this.getStreamLength();
                    String message = "Node too dirty. Stream length: " + length 
                            + ", Dirty limit: " + dirtyLimit + ", node: " + node;
                    
                    throw new AssertionError(message);
                }
            }*/
        };
        
        graph.visitMemoryNodes(visitor);
        
        //long total = counters[0] + counters[1] + counters[2];
        //
        //System.out.println("Db.checkNodes(): " + total + " nodes (" 
        //        + counters[0] + ", " + counters[1] + ", " + counters[2] + ", " + counters[3] + ")");
        //System.out.println("Db.checkNodes(): last trans size: " + lastTransSize);
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

        // Makes sure writes from startup and previous execute() are visible.
        // We do not hold DB.writeLock yet.
        synchronized (readSync) {}

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
     * @throws RerunException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException
     */
    private void executeInner(Trans t, final boolean isPrimordial) {
        //
        // Executes a KV set request as an atomic transaction.
        //
        // We make sure all readers have a read time that is strictly less than
        // t.transactionTime while the synchronized(writeLock) clause is executing.
        // This is handled by dbClock.
        //
        // Reads the KVs as warm-up; aims to avoid lengthy disk reads and cache
        // misses while synchronizing on this.writeLock. We want to minimize the time holding
        // this.writeLock. However, if we do write transactions from a single thread anyway, it
        // would be better to void these get operations (would save 10-20% CPU for execute()).
        // NOTE Room for a minor optimization. A special warmup() method could be more performant
        // than the general-purpose, public get() method.
        //
        
        long time = dbClock.getTime();

        boolean enableEvict = t.getData.evictData.enableEvict;
        t.getData.evictData.enableEvict = false;

        // Warm-up code, avoids read from stream while holding writeLock.
        for (Kv kv : t.kvs) {
            this.getOne(time, kv.keySegments, t.getData);
        }

        t.getData.evictData.enableEvict = enableEvict;
        
        synchronized (writeLock) {
            if (!isPrimordial) assert transNodes.size() == 0;
            this.pd.spaceSplitCount = 0;
            
            this.trans = t;

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
                putKvs();
                kvCount += t.kvs.length;
                transactionCount++;

                synchronized (readSync) {}
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
            
            appendNodesToStream();
            
            this.lastSposOfLastTrans = this.trans.lastSpos;
            this.sposOfLastTrans = this.trans.tpos;
            this.startupPos.releaseForEvict();
            
            clearTransMemory();

            // The synch statement below guarantees that the writes are visible to
            // all readers assuming they also use the same statement as below
            // before that start reading.
            
            synchronized (readSync) {}
            
            // 1301 Frans. The following line moved to inside the synchronized
            // (writeLock) block to KISS the reclaim stuff. However, it does not really 
            // have to belong to the writeLock code block.
            
            reclaimTransactionListener.transactionCompleted(t);
            
        }
    }
    
    /**
     * Records choices and ensures that index nodes last written to stream before limit
     * is added to transNodes.
     */
    private void recordChoicesAndEnsureIncluded(final long limit) {        
        GetData gd = graph.newGetData();
        gd.actualLookupTime = trans.transactionTime;
        gd.accessData = pd.accessData;
        
        final Choices[] finalChoice = new Choices[1];
        
        gd.pointerListener = new PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                if (superRoot.getSpos() < limit) {
                    transNodes.addTopNode(superRoot);
                }
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result,
                    int pointerType) {
                if (result.getSpos() < limit && result.isTopOrKeyNode()) {
                    if (result.getType() == INode.TYPE_TOP_NODE) {
                        transNodes.addTopNode((TopNode) result);
                    } else {
                        transNodes.addKeyNode((KeyNode) result);
                    }
                }
                finalChoice[0].add(pointerIndex);
            }
        };
        
        for (int i = 0; i < transNodes.valueSize; i++) {
            finalChoice[0] = transNodes.choices[i];
            long[] key = transNodes.keys[i];
            byte[] value = getOne(gd.actualLookupTime, key, gd);
            
            assert transNodes.valueNodes[i].isDelete() || Assert.arrayEquals(transNodes.valueNodes[i].getValue(), value);
        }
    }

    /**
     * Writes the nodes in this.transNodes to stream. Uses this.trans, 
     * this.transNodes, this.metaBlock, this.cacheMemoryValue, and more.
     * The caller must hold DB.writeLock.
     * 
     * @throws StreamIoException
     */
    private void appendNodesToStream() {
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

        this.cachedMemoryValue.addAndGet(transNodes.sumMemSize());

        // NOTE The current implementation works (120522)
        // However, a small transaction that comes after a large one, will often get unfairly
        // many dirty KeyNodes/TopNodes to write.
        // Would be better if the number of extra (too dirty nodes) nodes in a transaction was
        // proportional to the Kvs of the transaction.
        // This can be solved. The total size of the transaction nodes can be computed first, 
        // then..

        int ordinaryNodeCount = transNodes.size();
        
        long startupPos2 = startupPos.next(this.startupDistance, nodeStream.getLength());
        
        if (graph != null) {
            graph.getTransSeq().addToTransNodes(startupPos2, transNodes);
            recordChoicesAndEnsureIncluded(startupPos2);
        }
        
        computeStats(ordinaryNodeCount);

        assert trans != null : "trans is null";
        assert transNodes != null : "transNodes is null";
        
        trans.nodeCount = transNodes.size();
        
        nodeStream.appendNodes(trans.transactionTime, transNodes, trans);

        MetaBlock meta = nodeStream.getMetaBlock();
        meta.setStartupPos(startupPos.get());
        
        if (graph != null) {
            graph.getTransSeq().add(transNodes.createTset(trans.tpos, trans.lastSpos));            
            graph.getTransSeq().removeBeforeSpos(startupPos2);
        }
        
        this.nodesWritten += transNodes.size();
        this.ordinaryNodesWritten += ordinaryNodeCount;
        trans.listener.nodesWritten(transNodes);
    }

    /**
     * Computes this.dirtyFraction100, this.dirtyFraction1000.
     * 
     * @param ordinaryNodeCount   The number of ordinary (non-dirty) nodes of the transaction.
     */
    private void computeStats(int ordinaryNodeCount) {
        // Computes dirtyFraction100, dirtyFraction1000.
        
        int totalNodeCount = transNodes.size();
        int dirtyNodeCount = totalNodeCount - ordinaryNodeCount;
        double dirtyFraction = ((double) dirtyNodeCount) / totalNodeCount;
        this.dirtyFraction100   = 0.99  * this.dirtyFraction100  +  0.01  * dirtyFraction;
        this.dirtyFraction1000  = 0.999 * this.dirtyFraction1000 +  0.001 * dirtyFraction;
    }

    /**
     * Clears temporary references at end of transaction. Important to avoid memory leakage
     * and prepare for next transaction. Caller must hold writeLock.
     */
    private void clearTransMemory() {
        assert Thread.holdsLock(writeLock);
        this.trans = null;
        transNodes.clear();
    }

    /**
     * Sets the KVs directly to the in-memory data structure. This method runs with exclusive 
     * write access to the data structure (synchronized (writeLock)). However, there may be
     * concurrent readers that read with a lookup time strictly less than the transaction time
     * (trans.transactionTime). Caller must hold writeLock.
     */
    private final void putKvs() {
        //
        // 1210 Frans: Added [if (kv.keyTransformation != ...], [if (kv.valueTransformation != ...]
        // These changes do not add any measurable overhead when null; measured with test.Set.
        //

        assert Thread.holdsLock(writeLock);
        final int length = trans.kvs.length;        
        pd.tt = trans.transactionTime;

        for (int i = 0; i < length; i++) {
            Kv kv = trans.kvs[i];

            if (kv.keyTransformation != null) {
                kv.keyTransformation.transform(trans, i);
            }

            if (kv.valueTransformation != null) {
                final byte[] previous = this.getOne(trans.transactionTime, kv.keySegments, 
                        trans.getData);
                kv.value = kv.valueTransformation.transform(trans.transactionTime, kv.value,
                        previous);
            }

            graph.putKv(kv.keySegments, kv.value, pd);
            
            pd.clearFast();
        }
        
        pd.clear();
    }

    public long getAccessData() {
        return -cachedMemoryValue.get();
    }

    private final void possiblyEvict(EvictData ed) {
        // Synch note: concurrent access must be supported.
        // We have a benign race condition here. Updates could be missed.

        if (evictBoss.evictOrNot()) {
            evict(ed);
        }
    }

    /**
     * Runs the evict algorithm.
     */
    public final void evict(EvictData ed) {
        // Synch note: concurrent access must be supported.

        ed.pointerCount = 0;
        ed.evictCount = 0;
        ed.startupPos = this.startupPos.get();
        evictInner(ed);
        evictBoss.reportEvictCount(ed);
    }

    private void evictInner(EvictData ed) {
        //
        // node ----> nextNode ---> next2
        //
        // Synch note: concurrent access must be supported by this method.
        // Multiple concurrent readers, one writer.
        // rand is used to somewhat randomly choose a nodes to evict process.
        // For performance a single call to evictRandom.nextInt() is used.
        // To increase randomness, the rand value is increase between each time it is used.
        
        final Pointer pointer = ed.tempPointer;

        INode node = graph.getSuperRoot();
        INode nextNode;
        INode next2;
        long limit = this.cachedMemoryValue.get() - evictBoss.getCacheDuration();
        ed.accessTimeLimit = limit < 0 ? 0 : limit;
            // Nodes accessed after accessTimeLimit are not evictable.

        int rand = Math.abs(evictRandom.nextInt());
            // random int used as randomness for this evict operation.
        
        getEvictPointer2(node, rand, pointer);
        rand += 31;
        nextNode = pointer.node;

        if (nextNode == null) {
            // Only superRoot is cached, nothing to evict.
            assert node.getMemoryPointerCount() == 0 : "Count is " + node.getMemoryPointerCount()
                    + " for node " + node + ".";
            return;
        }

        while (true) {
            getEvictPointer2(nextNode, rand, pointer);
            rand += 17;
            next2 = pointer.node;

            if (next2 == null) {
                break;
            }

            // Here we go to the next deeper level.

            node = nextNode;
            nextNode = next2;
            next2 = null;
        }

        // We have selected a node to process.
        evictPointers(node, ed);
    }
    
    /**
     * Evicts all evictable pointers of 'node'.
     */
    private void evictPointers(INode node, EvictData ed) {
        int count = node.getPointerCount();
        for (int i = 0; i < count; i++) {
            INode pointee = node.getPointerNode(i);
            if (pointee != null) {
                synchronized (graph.getPointerLock(node, i)) {
                    pointee = node.getPointerNode(i); // re-read needed in case
                                                      // change happened.
                    long pointeePos;

                    if (pointee != null
                            && (pointeePos = pointee.getSpos()) != Spos.NULL
                            && !(pointeePos >= ed.startupPos)
                            && AccessData.getAccessTime(node.getPointerAccessData(i)) <= ed.accessTimeLimit) {

                        node.setPointer(i, null, pointeePos);
                        ed.evictCount += 1;
                    }
                }
            }
        }
    }

    
    private void getEvictPointer2(INode node, int rand, Pointer p) {
        int length = node.getPointerCount();
        int index;
        p.node = null;
        p.index = -1;
        
        for (int i = 0; i < length; i++) {
            index = rand % length;
            assert index >= 0 && index < length;
            
            synchronized (graph.getPointerLock(node, index)) {
                node.getPointer(index, p);
            }
            
            if (p.node != null) {
                p.index = index;
                break;
            }
            
            rand += 1;
        }
    }

    /**
     * Reports a warning. Current implementation prints to Db.out - standard
     * database output.
     */
    public void warn(String message, Throwable t) {
        // TODO Z LATER. This is not really used, we need other way to handle warnings.
        
        out.println("WARNING. " + message);
        t.printStackTrace(out);
    }

    /**
     * Returns current super root.
     * Use for testing only.
     */
    public final TopNode getSuperRoot() {
        return graph.getSuperRoot();
    }

    /**
     * Creates and returns a DB.Builder that can create a DB object. The
     * "official" and only public way of creating a DB.
     */
    public static Builder builder() {
        return new Builder();
    }
    
    
    // ======== Types ========
    
    /** Special class for Db.readSync is useful for debug. */
    public static class ReadSync {}
    
    /** Special class for Db.writeLock is useful for debug. */
    public static class WriteLock {}
    
    /**
     * For listening to what happens at startup. Useful for testing / debugging.
     */
    public static interface StartListener {
        void startupDistance(long startupDistance);
        void tpos(long startPos);
        void startPos(long startPos);
    }
    
    public static final DoNothingStartListener DO_NOTHING_START_LISTENER = new DoNothingStartListener();
    
    public static class DoNothingStartListener implements StartListener {
        public void startupDistance(long startupDistance) {}
        public void tpos(long startPos) {}
        public void startPos(long startPos) {}
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
     * A listener ("handler") for the transactionCompleted event, 
     * method transactionCompleted().
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
     * Unit tests that need access to private fields. Use sparingly, elsewhere when possible.
     */
    public static class Tester {
        public static void test0() {}
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