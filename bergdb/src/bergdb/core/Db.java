package bergdb.core;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.common.Bug;
import bergdb.common.NullProgressListener;
import bergdb.common.Util;
import bergdb.core.DbHelper.AddReplicaClass;
import bergdb.dag.AccessData;
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
import bergdb.dag.ValueNode;
import bergdb.pub.BadReplicaException;
import bergdb.pub.IllegalDbStateException;
import bergdb.pub.Job;
import bergdb.pub.LookupTimeNotAvailableException;
import bergdb.pub.StorageInfo;
import bergdb.storage.BufferedStream;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;

/**
 * <p>An object of this class provides access to the data in the database. This
 * class is the internal DB implementation; it should not be used directly by
 * end users unless they really need the absolutely highest performance or some feature
 * not exposed by the higher level API. 
 * This class implements the <i>Core Layer</i>, see below.</p>
 * 
 * <p>The API of the <i>Core Layer</i> consists of the methods:
 * </p>
 * <ul>
 * <li>getOne()</li>
 * <li>getMany()</li>
 * <li>execute(Transaction)</li>
 * </ul>
 * 
 * <p>These methods are the only ones that need to be used by a consumer of the 
 * Core Layer once the Db has been started and before it has been stopped. This API
 * form a narrow "waist" with a large code base under it and potentially a large code
 * base "above" it. These methods are believed to be "feature complete" in the
 * sense that all features we want from the database can be implemented on top
 * of them. Functionality that can be provided by using only the Core Layer API,
 * should not offered by this class. The method start(), is needed by a user,
 * but for initialization like the constructor or DB.Builder class.</p>
 * 
 * <p>Db Shutdown. The DB typically has allocated resources besides memory: 
 * open sockets, open files, running threads. These resources are guaranteed
 * to be *eventually released* without any action from the DB user after the
 * finalize() method has been called from the garbage collector.
 * The DB user can call DB.stop() to request the eventual release of resources.
 * Resources are not guaranteed to be released when stop() returns, but they will
 * be release in the the near future (typically within a second).</p>
 * 
 * @author Frans Lundberg
 */
public class Db {
    //
    // Note: There must be no reference to a Db object from a thread started
    // by the database (directly or indirectly). 
    // Otherwise, the Db object will never be available for garbage collection.
    //
    
    /** 
     * IKP - internal key prefix - prefix of keys used to store internal database data.
     * 131023: changed from /#ikp/ to "/#i/", destroyes binary compatibility.
     */
    public static final String INTERNAL_KEY_PREFIX = Util.identity("/#i/");
    
    /**
     * Minimum possible cacheMemoryValue.
     */
    public static final long MIN_CACHE_MEMORY_VALUE = Constants.MIN_CACHE_MEMORY_VALUE;
    
    /**
     * Used for internal dummy writes. 
     * No real data is stored for this key and it is not accessible externally
     * (from Pub API).
     */
    static final long[] DUMMY_KEY = Keys.toSegments(INTERNAL_KEY_PREFIX + "-dummy");

    /** 
     * State of the database. Synch note: writes published by readSync.
     */
    private DbState state = DbState.ZERO;
    
    /**
     * Global transaction write lock. Held when STM stuff is done.
     */
    private final WriteLock writeLock;
    
    /**
     * Sync object used to make sure writes from Db(), start(), execute(), are published
     * and made visible to threads calling getOne(), getMany().
     * It is typically used with an empty block: "synchronized (readSynch) {}".
     */
    private final ReadSync readSync;
    
    private final IKeyModSet keyModSet;
    private final NodeStream nodeStream;
    private final StorageManager storageManager;
    private final Random evictRandom;
    private Dag dag;
    private KvTransSeq kvTransSeq;
    private final ExecuteData x;
    private final Aux aux = new Aux();
    
    /** DatabaseId from Database.Builder, may be null. */
    private DatabaseId databaseIdFromBuilder;
    
    /** The reclaim algorithm. */
    private final Reclaim reclaim;
    
    /** The current meta block data of the node stream. */
    private final MetaBlock metaBlock;
    
    // ---- Settings ----

    private final DbClock dbClock;
    private final IEvictBoss evictBoss;
    private final int maxNodeSize;
    
    /** Current startupDistance. Sync note: protected by writeLock. */
    private int startupDistance;
    
    // ---- Misc ----
    
    private DatabaseId databaseId;
    private final TransactionListener reclaimTransactionListener;
    private final Internal internal;
    
    private StartupPosUpdater startupPosUpdater = new StartupPosUpdater() {
        public long newStartupPos(long current, long streamLength, int startupDistance, 
                PosOfTransBeforeFunction posFunction) { 
            long candidate = streamLength - startupDistance;
            candidate = candidate < 0 ? 0 : candidate;
            long pos = posFunction.posOfTransBefore(candidate);
            long updated = pos == -1 ? current : pos;
            return updated;
        }
    };

    /**
     * Constructor takes a DbBuilder; it wires dependencies based on builder settings.
     */
    Db(DbBuilder b) {
        internal = new Internal();
        writeLock = new WriteLock();
        readSync = new ReadSync();
        x = new ExecuteData();
        
        evictRandom = new Random(0);      // pseudo-random, but deterministic.
        keyModSet = new KeyModSet();
 
        this.maxNodeSize = b.maxNodeSize;
        this.startupDistance = b.startupDistance;
        this.metaBlock = new MetaBlock();
        
        StorageManager.Builder smBuilder = new StorageManager.Builder(writeLock);
        for (int i = 0; i < b.streamInfos.size(); i++) {
            DbBuilder.StreamInfo info = b.streamInfos.get(i);
            smBuilder.stream(info.name, info.stream, info.bufferSize, info.bufferTime);
        }
        this.storageManager = smBuilder.build();
        
        AppendOnlyStream aos = storageManager;
        x.lastSposOfLastTrans = aos.getLength();
        
        RecoverableStream rstream = new RecoverableStream(aos, metaBlock);
        this.nodeStream = new NodeStream(rstream, writeLock);
        this.nodeStream.getMetaBlock().setStartupDistance(b.startupDistance);
        
        this.dbClock = new DbClock(b.clock);
        this.evictBoss = b.evictBoss;
        
        this.reclaim = new Reclaim(this, aos);
        
        this.reclaimTransactionListener = reclaim;
        reclaim.setRetainDuration(b.retainDurationInTimeUnits);
        
        this.databaseIdFromBuilder = b.id;
        
        //
        // Synch note: Synchronized blocks make sure the writes in constructor are
        // published to threads synchronizing on readSync or writeLock.
        //
        synchronized (readSync) {}
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
    
    public double getDirtyFraction100() {
        synchronized (writeLock) {
            return aux.dirtyFraction100;
        }
    }
    
    public double getDirtyFraction1000() {
        synchronized (writeLock) {
            return aux.dirtyFraction1000;
        }
    }
    
    public long getNodesWritten() {
        synchronized (writeLock) {
            return aux.nodesWritten;
        }
    }
    
    public long getOrdinaryNodesWritten() {
        synchronized (writeLock) {
            return aux.ordinaryNodesWritten;
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
    public void setStartupDistance(int newDistance) {
        //
        // A dummy transaction of size >= META_BLOCK_DISTANCE is written
        // to the stream to ensure that the new value of startupDistance is 
        // stored in a meta block in the stream.
        //
        
        if (newDistance < 0) {
            throw new IllegalArgumentException("Bad newDistance: " + newDistance + ".");
        }
        
        int min = RecoverableStream.META_BLOCK_DISTANCE * 2;
        int max = 1000*1000000;
        
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
        return aux.cachedMemoryValue.get();
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
            return aux.transactionCount;
        }
    }
    
    public long getKvCount() {
        synchronized (writeLock) {
            return aux.kvCount;
        }
    }
    
    /**
     * Returns the number of get operations that has completed since Db.start() was called.
     */
    public long getGetOpCount() {
        return aux.getOpCount.get();
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
        
        // Checks database id of main and replica; must match. 
        DbHelper.checkReplicaId(metaBlock.getId(), replicaStream);
        
        return AddReplicaClass.addReplica(storageManager, this, name, replicaStream, bufferSize, bufferTime);
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
    
    /**
     * @see bergdb.core.DbClock
     */
    public long currentTime() {
        return dbClock.currentTime();
    }
    
    /**
     * Internal, not part of public API.
     * Returns internal (actual) lookup time given a wanted lookup time.
     */
    public long lookupTime(long wantedLookupTime) {
        return dbClock.lookupTime(wantedLookupTime);
    }

    /**
     * Starts the database by reading from the stream. Call once per Db object
     * after constructor and before the get/set methods.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalStateException
     *             If start() has been called already.
     * @throws BadReplicaException
     */
    public void start() {
        start(StartParams.NULL, Db.StartListener.DO_NOTHING);
    }
    
    public static class StartParams {
        public static final StartParams NULL = new StartParams();
        public long startupPos;
        public int startupDistance;
        
        public StartParams() {
            startupPos = Spos.NULL;
            startupDistance = -1;
        }
        
        public boolean isNull() {
            return this == NULL;
        }
    }
    
    /**
     * Starts the database by reading from the stream. Call once per Db object
     * after constructor and before the get/set methods.
     * 
     * @param param params  
     *          Used for testing, normally set to StartParams.NULL as default.
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalStateException
     *          If start() has been called already.
     * @throws BadReplicaException
     */
    public void start(StartParams params, StartListener listener) {
        synchronized (writeLock) {
            synchronized (readSync) {
                startInner(params, listener);
            }
        }
    }
    
    /**
     * The startup implementation.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws BadReplicaException
     * @throws IllegalDbStateException
     */
    private void startInner(StartParams params, StartListener listener) {        
        assertStateIsZero();

        syncStreams();
        handleEmptyStream();
        nodeStream.recover();
        handleStartParams(params, listener);
        
        ArrayList<StoredTrans> transactions = readTransactions(x.startupPos.get());
        listener.reportStartupTransactions(transactions);
        setLastTransTimeOfDbClock(transactions);
        
        startDag(transactions);
        
        createPutAndGetData();
        
        this.state = DbState.ACTIVE;
        reclaim.initFromDb();
    }

    private void createPutAndGetData() {
        x.putData = createPutData();
        x.getData = newGetData();
    }

    private void startDag(ArrayList<StoredTrans> transactions) {
        DagStarter.Result result = DagStarter.start(transactions, getAccessData(), nodeStream, maxNodeSize);
        dag = result.getDag();
        
        //DbStarter.Result result = DbStarter.start(this, transactions, getAccessData(), nodeStream, maxNodeSize);
        
        aux.cachedMemoryValue.set(result.getCachedMemoryValue());
        kvTransSeq = result.getKvTransSeq();
    }

    /**
     * @throws StreamFormatException
     * @param listener
     */
    private void handleStartParams(StartParams params, StartListener listener) {
        if (params.isNull()) {
            params = new StartParams();
            MetaBlock meta = nodeStream.getMetaBlock();
            params.startupPos = getStartupPosFromMetaBlock(meta);
            params.startupDistance = getStartupDistanceFromMetaBlock(meta);
        }
        
        startupDistance = params.startupDistance;
        x.startupPos.set(params.startupPos);
        listener.reportStartupDistance(startupDistance);
        listener.reportStartPos(x.startupPos.get());
    }

    private long getStartupPosFromMetaBlock(MetaBlock meta) {
        long pos = meta.getStartupPos();
        if (pos < 0) {
            throw new StreamFormatException("Bad value of startupPos in meta " +
                    "block of stream: " + pos + ".");
        }
        return pos;
    }

    private int getStartupDistanceFromMetaBlock(MetaBlock meta) {
        int distance = meta.getStartupDistance();
        if (distance <= 0) {
            throw new StreamFormatException("Bad value of startupDistance in meta " +
                    "block of stream: " + distance + ".");
        }
        return distance;
    }
    
    /** Reads transactions from DB stream starting at startPos. */
    private ArrayList<StoredTrans> readTransactions(long startupPos) {
        if (startupPos == 0) {
            startupPos = RecoverableStream.META_BLOCK_SIZE;
        }
        
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        NodeStream.TransIterator ti = nodeStream.createTransIteratorFromExactStartupPos(startupPos);
        while (ti.next()) {
            StoredTrans stored = ti.getStoredTrans();
            transactions.add(stored);
        }
        
        return transactions;
    }
    
    private void setLastTransTimeOfDbClock(ArrayList<StoredTrans> transactions) {
        long lastTransTime;
        int size = transactions.size();
        
        if (size == 0) {
            throw new StreamFormatException("No transactions in startup transaction set.");
        } else {
            lastTransTime = transactions.get(size - 1).tt;
        }
        
        dbClock.setLastTransTime(lastTransTime);
    }
    
    private PutData createPutData() {
        assert dag != null : "dag is null";
        
        PutData putData = dag.newPutData();
        putData.nodeChangeListener = new Dag.NodeChangeListener() {
            public void newTopNode(TopNode node) {
                // The gotDirty code in the PointerListener is not enough for
                // the case when new top nodes are created.
                // This method call assumes new nodes are not dirty.
                
                assert node.isDirty == false : "node is dirty, " + node;
                makeDirtyIfNeeded(node);
            }
            
            public void newValueNode(ValueNode node, long[] key) {
                x.kvTransNodes.addValueNode(node, key);
            }
            
            public void keyNodeChanged(KeyNode node) {
                // The gotDirty code in the PointerListener is not enough for
                // the case when new key nodes are created.
                // This method call assumes new nodes are not dirty.
                makeDirtyIfNeeded(node);
            }
        };
        
        // Extends existing pointerListener used by Dag.
        
        final Dag.PointerListener pListener = putData.pointerListener;
        
        putData.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                pListener.superRootAccessed(superRoot);
                makeDirtyIfNeeded(superRoot);
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                pListener.pointerFollowed(predecessor, pointerIndex, result, pointerType);
                makeDirtyIfNeeded(result);
            }
        };
        
        return putData;
    }

    /**
     * @throws IllegalDbStateException
     */
    private void assertStateIsZero() {
        if (state != DbState.ZERO) {
            throw new IllegalDbStateException("Db has been started already, "
                    + "start() should be called once only; Db state is: " 
                    + state + ".");
        }
    }

    /**
     * If the stream is empty, this method creates the database id 
     * (if not given in the database builder)
     * and writes the first metablock and the primordial transaction to the stream.
     */
    private void handleEmptyStream() {
        if (nodeStream.getLength() == 0) {
            determineDatabaseId();
            writePrimordialTransaction();
        }
    }
    
    private void determineDatabaseId() {
        if (databaseIdFromBuilder.isCreateLaterMarker()) {
            databaseId = DatabaseId.createRandom();
        } else {
            databaseId = databaseIdFromBuilder;
        }
    }

    private void writePrimordialTransaction() {
        long tt;
        try {
            tt = dbClock.transactionBegin();
        } finally {
            dbClock.transactionEnd();
        }
        
        KeyNode root = new KeyNode();
        TopNode superRoot = TopDs.createSuperRootFromFirstKeyNode(tt, root, AccessData.DEFAULT_ACCESS_DATA);
        
        MetaBlock meta = nodeStream.getMetaBlock();
        meta.setId(databaseId.getBytes());
        meta.setStartupDistance(startupDistance);
        meta.setStartupPos(0);
        meta.setTime(tt);
        
        this.kvTransSeq = new KvTransSeq();
        
        Trans trans = Trans.builder().build();
        trans.time = tt;
        trans.isInternal = true;
        
        x.begin(trans);
        
        assert !root.isDirty;
        assert !superRoot.isDirty;
        makeDirtyIfNeeded(root);
        makeDirtyIfNeeded(superRoot);
        
        x.kvTransNodes.addKeyNode(root);
        x.kvTransNodes.addTopNode(superRoot);
        
        storeKvTrans();
        storeIndexTrans(computeNewStartupPos(), true, false);
        
        x.lastSposOfLastTrans = trans.lastPos;
        
        x.end();
    }

    private void makeDirtyIfNeeded(INode node) {
        if (!node.isDirty() && node.isIndexNode()) {
            node.setDirty(true);
            x.transInfo.gotDirtyNodes.add(node);
        }
    }

    /**
     * Syncs raw storage streams.
     */
    private void syncStreams() {
        storageManager.checkStreamIds();
        
        try {
            storageManager.syncStreams(new NullProgressListener());
        } catch (IOException e) {
            throw new StreamIoException(e);
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
        
        if (state == DbState.STOPPING) {
            return;
        }
        
        state = DbState.STOPPING;
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
        
        if (state == DbState.STOPPING) {
            return;
        }
        
        synchronized (this.writeLock) {
            if (state == DbState.STOPPING) {
                return;
            }
            
            state = DbState.STOPPING;
            
            synchronized (readSync) {};
        }
            
        // Here, no write op is running or will be started.
        // No read op (get) will be started, but may be running.
        
        storageManager.close();
    }
    
    protected void finalize() throws Throwable {
        stop();
        super.finalize();
    }
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and
     * development.
     */
    public void printGraph(PrintStream out) {
        dag.printGraph(out);
    }
    
    /**
     * Creates and returns a new GetData object for use with the getOne() method.
     */
    public GetData newGetData() {
        return dag.newGetData();
    }
    
    /**
     * Creates and returns a new GetMany object for use with the getMany() method.
     */
    public GetMany newGetMany() {
        return dag.newGetMany();
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
        assert gd != null;
        assert gd.kwi != null;
        
        assertDbStateIsActive("getOne");

        // Makes sure writes from startup and execute() are visible.
        synchronized (readSync) {}
        
        return getOneInternal(lookupTime, keySegments, gd);
    }
    
    public byte[] getOneInternal(long lookupTime, long[] keySegments, GetData gd) {
        //
        // Few assumptions of previous state of gd are assumed. db.kwi must be non-null, however.
        //
        
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

        // Limits lookup time so it is strictly less than the transaction time of
        // any running or future transaction.
        long time = dbClock.lookupTime(lookupTime);
        
        gd.actualLookupTime = time;
        gd.nodeDepth = 0;

        result = dag.getOne(gd.actualLookupTime, keySegments, gd);

        aux.getOpCount.incrementAndGet();
        return result;
    }
    
    /**
     * Follows the pointers in the Db graph from the super top node using the given 
     * node index choices. Useful for testing.
     */
    public INode findNode(int[] choices, GetData gd) {
        return dag.findNode(choices, gd);
    }

    /**
     * Get multiple KVs in increasing or decreasing key order.
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

        assertDbStateIsActive("getMany");
        
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

        g.actualLookupTime = dbClock.lookupTime(g.lookupTime);
            // Limits lookup time so it strictly less than the transaction time of
            // any currently running or any future transaction.

        dag.getMany(g);
        
        aux.getOpCount.addAndGet(g.getOpCount);
    }
    
    /**
     * Sync method with parametarized sync level.
     * 
     * @param syncLevel
     *      The sync level.
     */
    public void sync(SyncLevel syncLevel) {
        sync(0, syncLevel);
    }
    
    /**
     * Sync method with parametarized sync level.
     * 
     * @param pos
     *      Stream position to sync to or 0 to sync to last transaction written.
     * @param syncLevel
     *      The sync level.
     */
    public void sync(long pos, SyncLevel syncLevel) {
        if (syncLevel == null) {
            throw new IllegalArgumentException("syncLevel == null not allowed");
        }
        
        if (syncLevel == SyncLevel.NONE) {
            return;
        }
        
        if (pos == 0) {
            synchronized (writeLock) {
                pos = x.lastSposOfLastTrans;
            }
        }
        
        switch (syncLevel) {
        case ORDINARY:
        case STRONG:
            try {
                if (syncLevel == SyncLevel.ORDINARY) {
                    storageManager.sync(pos);
                } else {
                    storageManager.syncStrong(pos);
                }
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            break;
        
        default:
            throw new Bug("never happens, " + syncLevel);
        }
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
        
        NodeVisitor visitor = new NodeVisitor() {
            public void visit(TopNode node) {
                counters[0]++;
            }

            public void visit(KeyNode node) {
                counters[1]++;
                node.check();    // throws AssertionError if bad.
            }

            public void visit(ValueNode node) {
                counters[2]++;
            }
        };
        
        dag.visitMemoryNodes(visitor);
    }
    
    /**
     * Same as "execute(b.build());", AVOID using this method in new code, 
     * use execute(Trans).
     * Db is selfish, should provide minimal interface, not convinience methods.
     */
    public final void execute(Trans.Builder b) {
        //
        // This little method does not comply with the minimal Core Layer API rule.
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
        // t.transTime while the synchronized(writeLock) clause is executing. 
        // This is handled by dbClock.
        //

        // Makes sure writes from startup and previous execute() calls are visible.
        // We do not hold DB.writeLock yet.
        synchronized (readSync) {}

        assertDbStateIsActive("execute");
        executeInner(t);
    }

    private void assertDbStateIsActive(String methodName) {
        DbState myState = state;
        if (myState != DbState.ACTIVE) {
            if (myState == DbState.STOPPING) {
                throw new DbStoppingException("Cannot call " + methodName + "() while DB is stopping.");
            } else {
                throw new IllegalDbStateException("Cannot call " + methodName + "() when DB state is " 
                        + myState + ".");
            }
        }
    }
    
    /**
     * Executes a transaction; this is the heart of the transaction handling.
     * 
     * @throws RerunException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException
     */
    private void executeInner(Trans t) {
        //
        // We make sure all readers have a read time that is strictly less than
        // t.time while the synchronized(writeLock) clause is executing.
        // This is handled by dbClock.
        //
        
        warmup(t);
        
        synchronized (writeLock) {
            x.begin(t);
            
            stmCheckConflicts(t);

            try {
                t.time = dbClock.transactionBegin();
                putKvs();

                synchronized (readSync) {}
                    // Publishes the changes by the writer thread to the readers. This is done
                    // before the t.transTime can be used as lookup time, so all readers
                    // (that do: "synchronized (readSynch) {}") are guaranteed to see all 
                    // in-memory changes made by the writer (the thread executing this code).
                
            } finally {
                dbClock.transactionEnd();
                    // After this, read operations can use the lookuptime t.time.
            }
            
            stmRecordKeys(t);

            storeKvTrans();
            
            long sp0 = x.startupPos.get();
            long sp1;
            if (x.trans.isRerun) {
                long storedSp = x.trans.storedStartupPos;
                if (storedSp == -1) {
                    sp1 = sp0;
                } else {
                    sp1 = storedSp;
                }
            } else {
                sp1 = computeNewStartupPos();
            }
            
            storeIndexTrans(sp1, sp1 == sp0, x.trans.isRerun); 
            
            aux.updateStats();
            
            x.startupPos.releaseForEvict();
            
            x.end();

            // The synch statement guarantees that the writes are visible to all readers 
            // assuming they also do [synchronized(readSync) {}] before they start reading.
            synchronized (readSync) {}
            
            // 1301 Frans. The below line moved to inside the synchronized (writeLock) block 
            // to KISS the reclaim stuff. However, fundamentally, it does not have to 
            // belong to the block.
            reclaimTransactionListener.transactionCompleted(t);    
        }
    }

    /**
     * Returns to caller with a RerunException if any key was modified after 
     * the read time of the transaction. This is the essence of the 
     * STM (software transactional memory) approach.
     * 
     * @throws RerunException
     */
    private final void stmCheckConflicts(Trans t) {
        for (long hash : t.readKeyHashes) {
            if (keyModSet.modifiedAfter(t.readTime, hash)) {
                throw new RerunException(hash);
            }
        }
    }

    /**
     * Records hash values of the keys for the KVs updated by the transaction, t.
     */
    private void stmRecordKeys(Trans t) {
        // Note, possible refactoring: Extract stm methods to Stm class, or merge with KeyModSet.
        
        for (int i = 0; i < t.writeKeyHashes.length; i++) {
            keyModSet.add(t.time, t.writeKeyHashes[i]);
        }
    }
    
    /**
     * Reads the KVs as warm-up; aims to avoid lengthy disk reads and cache
     * misses while synchronizing on this.writeLock. We want to minimize the time holding
     * this.writeLock. However, if we do write transactions from a single thread anyway, it
     * would be better to void these get operations (would save 10-20% CPU for execute()).
     * This is a trade-off. Of course, we could have optimization setting for this:
     * [enum ThreadOptimization { SINGLE_WRITE_THREAD, MULTIPLE_WRITE_THREADS }].
     * But, until proven important enough, we keep variability as low as possible and focus
     * on best "worst-case" performance (worst-case performance vs best-case performance).
     */
    private final void warmup(Trans t) {
        assert x != null : "x == null";
        assert x.getData != null : "x.getData == null";
        
        final long readTime = dbClock.lookupTime(Long.MAX_VALUE);
        final GetData gd = x.getData;

        boolean enableEvict = gd.evictData.enableEvict;
        gd.evictData.enableEvict = false;

        for (Kv kv : t.kvs) {
            this.getOneInternal(readTime, kv.getKey(), gd);
        }

        gd.evictData.enableEvict = enableEvict;
    }

    /** Appends the KV transaction to the db stream and updates KvTransSeq. */
    private void storeKvTrans() {
        assert x.trans != null : "trans is null";
        assert x.kvTransNodes != null : "transNodes is null";
        
        x.trans.nodeCount = x.kvTransNodes.size();
        
        nodeStream.appendNodes(x.kvTransNodes, x.trans);
        x.transInfo.tpos = x.trans.pos;
        x.transInfo.lastPos = x.trans.lastPos;
        x.transInfo.tt = x.trans.time;
        kvTransSeq.add(x.transInfo);
        
        x.kvTransNodes.clean();
    }

    /** 
     * Appends the index transaction to the db stream and updates startupPos
     * so it is effective for next transaction. 
     */
    private void storeIndexTrans(long newStartupPos, boolean wasSpIncreased, boolean isRerun) {
        // Note, we could re-use nodeTrans object for performance like we do for
        // storeKvTrans (x.kvTransNodes).
        // NOTE Do we need double storage of startupPos? In MetaBlock and x.startupPos?
        
        kvTransSeq.addToTransNodes(newStartupPos, x.indexTransNodes);
        kvTransSeq.removeBefore(newStartupPos);
        
        if (x.indexTransNodes.size() > 0) {
            Trans trans = Trans.builder().build();
            trans.isInternal = true;
            trans.time = x.trans.time;
            trans.isRerun = isRerun;
            trans.storedStartupPos = wasSpIncreased ? newStartupPos : -1;
            
            nodeStream.appendNodes(x.indexTransNodes, trans);
            x.indexTransNodes.clean();
        }

        x.startupPos.set(newStartupPos);
    }

    /** 
     * Computes a new startupPos based on the current current startupPos,
     * the stream length and the startupPosUpdater.
     */
    private long computeNewStartupPos() {
        long current = x.startupPos.get();
        long length = nodeStream.getLength();
        return startupPosUpdater.newStartupPos(
                current, length, startupDistance, (PosOfTransBeforeFunction) kvTransSeq);
    }

    /**
     * Sets the KVs directly to the in-memory data structure. This method runs with exclusive 
     * write access to the data structure (synchronized (writeLock)). However, there may be
     * concurrent readers that read with a lookup time strictly less than the transaction time
     * (trans.time).
     *
     * @throws IllegalDbStateException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws DbException
     */
    private final void putKvs() {
        assert Thread.holdsLock(writeLock);
        final int length = x.trans.kvs.length;        
        x.putData.tt = x.trans.time;

        for (int i = 0; i < length; i++) {
            Kv kv = x.trans.kvs[i];

            if (kv.keyTransformation != null) {
                kv.getKeyTransformation().transform(x.trans, i);
            }

            if (kv.valueTransformation != null) {
                final byte[] previousValue = this.getOne(x.trans.time, kv.getKey(), x.getData);
                kv.transformValue(x.trans.time, previousValue);
            }

            dag.putKv(kv.getKey(), kv.getValue(), x.putData);
            
            x.putData.clearFast();
        }
        
        x.putData.clear();
    }

    public long getAccessData() {
        return -aux.cachedMemoryValue.get();
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
        ed.startupPos = x.startupPos.getForEvict();
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

        INode node = dag.getSuperRoot();
        INode nextNode;
        INode next2;
        long limit = aux.cachedMemoryValue.get() - evictBoss.getCacheDuration();
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
                synchronized (dag.getPointerLock(node, i)) {
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
            
            synchronized (dag.getPointerLock(node, index)) {
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
     * Returns access to the internals of Db.
     * Warning, this method is for internal use only.
     */
    public Internal internal() {
        return internal;
    }

    /**
     * Creates and returns a Db.Builder that can create a Db object. 
     * The "official" and only public way of creating a Db.
     */
    public static DbBuilder builder() {
        return new DbBuilder();
    }
    
    
    // ======== Types ========
    
    /** 
     * Using a special class for Db.readSync is useful for debug / monitoring.
     * The class has no other purpose.
     */
    public static class ReadSync {}
    
    /** 
     * Using a special class for Db.writeLock is useful for debug / monitoring.
     * The class has no other purpose.
     */
    public static class WriteLock {}
    
    /**
     * Access to the internal structure of the Db object.
     * Do NOT use these methods for normal operation, they are available
     * for developement, testing, and internal use.
     */
    public class Internal {
        public TopNode superRoot() { return dag.getSuperRoot(); }
        
        public Dag dag() { return dag; }
        
        public void setDag(Dag d) { 
            dag = d;
        }

        public long getStartupPos() { return x.startupPos.get(); }

        public Object getWriteLock() { return writeLock; }
        
        public Object getReadSynch() { return readSync; }
        
        public ExecuteData x() { return x; }
        
        public void setStartupPosUpdater(StartupPosUpdater u) {
            synchronized (writeLock) {
                startupPosUpdater = u;
            }
        }
        
        public void executeInner(Trans t) { Db.this.executeInner(t); }
        
        public void createPutAndGetData() { Db.this.createPutAndGetData(); }
    }
    
    /**
     * Collection of variables for method Db.execute(Transaction).
     * All field access must be from thread holding Db.writeLock.
     */
    public class ExecuteData {
        /** Current transaction while writeLock is held. */
        public Trans trans;
        
        /** Current startupPos; stream pos to use by startup procedure. */
        public final StartupPos startupPos;
        
        /** PutData used when executing a transaction. */
        public PutData putData;
        
        /** GetData used when executing a transaction. */
        public GetData getData;
        
        /** The nodes updated for the current transaction. To be written to the stream. */
        public final TransNodes kvTransNodes;
        public final TransNodes indexTransNodes;
        
        public KvTransSeq.TransInfo transInfo;
        
        /** End stream position of last transaction; used by Db.sync(). */
        public long lastSposOfLastTrans;
        
        private ExecuteData() {
            startupPos = new StartupPos(0);
            kvTransNodes = new TransNodes();
            indexTransNodes = new TransNodes();
        }
        
        /** 
         * Called before transaction executes, just after Db.writeLock held. 
         * Allows ExecuteData to prepare for new transaction.
         */
        private void begin(Trans trans) {
            this.trans = trans;
            transInfo = new KvTransSeq.TransInfo();
            if (x.putData != null) {
                x.putData.spaceSplitCount = 0;
            }
        }
        
        /**
         * Called after transaction has done putKvs(), but still holds Db.writeLock.
         * Clears temporary references at end of transaction. Important to avoid memory leakage
         * and prepare for next transaction. Caller must hold writeLock.
         */
        private void end() {
            // Good to clear here, kvTransNodes/indexTransNodes. 
            // Large transaction otherwise consumes memory until next transaction written.
            
            x.lastSposOfLastTrans = x.trans.lastPos;
            trans = null;
            kvTransNodes.clear();
            indexTransNodes.clear();
        }
    }
    
    /**
     * Private auxilliary database state; counters, statistics, ...
     */
    private class Aux {
        
        /**
         * The cachedMemoryValue is an estimate of the total amount of memory cached
         * since the database process was started. It works as a time-scale for the cache.
         * Yes, starting from minCacheMemoryValue instead of 0 has importance.
         */
        private final AtomicLong cachedMemoryValue = new AtomicLong(MIN_CACHE_MEMORY_VALUE);
        
        /** Number of get operations processed since startup of Db. */
        private final AtomicLong getOpCount = new AtomicLong(0);
        
        /** 
         * Number of transactions executed since this.start(). 
         * Protected by writeLock.
         */
        private long transactionCount = 0;
        
        /**
         * Number of KVs set since this.start().
         * Protected by writeLock.
         */
        private long kvCount = 0;
        
        private long nodesWritten = 0;
            // Number of nodes written since database started.
        private long ordinaryNodesWritten = 0;
        
        // Below two, protected by writeLock.
        private double dirtyFraction100 = 0.10;
        private double dirtyFraction1000 = 0.10;
        
        private void updateStats() {
            kvCount += x.trans.kvs.length;
            transactionCount++;
            
            int ordinaryNodeCount = x.kvTransNodes.size();
            nodesWritten += x.kvTransNodes.size();
            ordinaryNodesWritten += ordinaryNodeCount;
            
            int totalNodeCount = x.kvTransNodes.size();
            int dirtyNodeCount = totalNodeCount - ordinaryNodeCount;
            double dirtyFraction = ((double) dirtyNodeCount) / totalNodeCount;
            dirtyFraction100   = 0.99  * aux.dirtyFraction100  +  0.01  * dirtyFraction;
            dirtyFraction1000  = 0.999 * aux.dirtyFraction1000 +  0.001 * dirtyFraction;
            
            cachedMemoryValue.addAndGet(x.kvTransNodes.sumMemSize());
        }
    }
    
    /**
     * For listening to what happens at startup. Useful for testing / debugging.
     */
    public static interface StartListener {
        public void reportStartupDistance(long startupDistance);
        public void reportStartPos(long startPos);
        public void reportStartupTransactions(ArrayList<StoredTrans> transactions);
        
        public static final StartListener DO_NOTHING = new StartListener() {
            public void reportStartupDistance(long startupDistance) {}
            public void reportStartPos(long startPos) {}
            public void reportStartupTransactions(ArrayList<StoredTrans> transactions) {}
        };
    }
    
    public static final PrintStartListener SYSTEM_OUT_START_LISTENER = new PrintStartListener(System.out);
    
    public static class PrintStartListener implements StartListener {
        private PrintStream p;
        
        public PrintStartListener(PrintStream out) {
            this.p = out;
        }
        
        public void reportStartupDistance(long startupDistance) {
            p.println("startupDistance: " + startupDistance);
        }
        
        public void reportStartPos(long startPos) {
            p.println("startPos: " + startPos);
        }
        
        public void reportStartupTransactions(ArrayList<StoredTrans> transactions) {
            p.println("---- startupTransactions ----");
            for (StoredTrans s : transactions) {
                p.println("StoredTrans: " + s);
                for (StoredNode n : s.nodes) {
                    p.println("  " + n);
                }
            }
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
}


/*


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
     
    t.transTime = dbClock.transactionBegin(); 
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