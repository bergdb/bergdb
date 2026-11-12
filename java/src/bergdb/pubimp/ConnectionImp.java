package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.core.Db;
import bergdb.core.DbConstants;
import bergdb.core.InternalDataException;
import bergdb.core.Reclaim;
import bergdb.core.StoredNode;
import bergdb.core.StoredTrans;
import bergdb.core.StoredValueNode;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.Spos;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.DbObject;
import bergdb.pub.Kv;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.UseIndexBuilder;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.WBuilder;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;

/**
 * Implementation of Connection.
 * 
 * @author Frans Lundberg
 */
class ConnectionImp implements Connection {
    private final Db db;
    private final DatabaseImp database;
    private final GetData getData;
    private long lookupTime;
    private boolean enableKeyReplace;
    private boolean freezeLookupTime;
    long lastSposOfLastTrans;
    
    /**
     * The key of the last read that retrieved a value, the value whose transaction
     * getData.tpos names: transactionInfo() follows reclaim's copies of the value back by it
     * (bergdb 021-17). Set with getData.tpos, by each read that finds a value.
     */
    private long[] infoKey;
    
    /**
     * The thread in a call of this connection, or null (bergdb 021-22, 020-24-11, U11-2).
     * A connection is used by one thread at a time (Connection): each call that reads or
     * changes its state (getData, infoKey, the lookup time, lastSposOfLastTrans) or runs a
     * transaction enters (enter(), a compare-and-set, uncontended in the normal case) and
     * leaves (leave()); a call of another thread meanwhile throws IllegalStateException
     * before it reads or changes anything. A call inside a call of the same thread, as a Data
     * Object constructor's get in a get or a put in an rw() action, is not refused. Until
     * 2026-11-09 threads that shared a connection shared its GetData: reads returned
     * another key's value, threw ArrayIndexOutOfBoundsException, and failed the database
     * with a message of corrupt data ("Bad value pointer -1").
     */
    private final AtomicReference<Thread> user = new AtomicReference<Thread>();

    public ConnectionImp(DatabaseImp database) {
        assert database != null;
        this.database = database;
        this.db = database.getDb();
        this.getData = db.newGetData();
        this.getData.actualLookupTime = -1;
        this.lookupTime = Time.MAX.units();
            // Time.MAX, as Connection.setLookupTime() says (bergdb 015-59). It was
            // Long.MAX_VALUE, above Time's range: getLookupTime() threw. The reads are the
            // same, as DbClock.lookupTime() takes the last transaction's time for both.
        this.enableKeyReplace = false;
        this.lastSposOfLastTrans = 0;
    }
    
    /**
     * Enters a call of this connection (user): true if it is the thread's outer call, which
     * leave() ends; false for a call inside a call of the same thread.
     * 
     * @throws IllegalStateException  If another thread is in a call of this connection.
     */
    final boolean enter() {
        return enter(user, "A Connection");
    }
    
    /** Leaves a call that enter() entered; 'outer' is what enter() returned. */
    final void leave(boolean outer) {
        leave(user, outer);
    }
    
    /**
     * Enters a call of an object that one thread uses at a time, whose 'user' is the thread
     * in a call of it, or null (bergdb 021-22): true if the call is the thread's outer one,
     * which leave(user, true) ends; false for a call inside a call of the same thread.
     * 
     * @throws IllegalStateException  If another thread is in a call of it; 'what' names it.
     */
    static boolean enter(AtomicReference<Thread> user, String what) {
        // A lock's orders: acquire here, release in leave(). The plain read finds the
        // thread's own outer call: only this thread sets 'user' to itself.
        final Thread t = Thread.currentThread();
        if (user.getPlain() == t) {
            return false;
        }
        if (user.compareAndExchangeAcquire(null, t) == null) {
            return true;
        }
        throw new IllegalStateException(what + " is used by one thread at a time: another "
                + "thread is in a call of it. Nothing was read or changed (bergdb 021-22).");
    }
    
    /** Leaves a call that enter(user, what) entered; 'outer' is what it returned. */
    static void leave(AtomicReference<Thread> user, boolean outer) {
        if (outer) {
            user.setRelease(null);
        }
    }
    
    public final void setLookupTime(Time lookupTime) {
        if (lookupTime == null) {
            throw new IllegalArgumentException("lookupTime == null not allowed");
        }
        final boolean outer = enter();
        try {
            setLookupTime(lookupTime.units());
        } finally {
            leave(outer);
        }
    }

    /**
     * Sets database lookup time.
     * 
     * @param lookupTime  Time on clock units.
     */
    public final void setLookupTime(long lookupTime) {
        this.freezeLookupTime = false;
        this.lookupTime = lookupTime;
    }

    public final Time getLookupTime() {
        return Time.units(lookupTime);
    }
    
    public final void freezeLookupTime() {
        final boolean outer = enter();
        try {
            this.freezeLookupTime = true;
            this.lookupTime = Time.MAX.units();
                // Each call freezes anew, at the latest state as of the next read (bergdb
                // 018-04, Q2). Before, a second call kept the first frozen time.
        } finally {
            leave(outer);
        }
    }
    
    public Time currentTime() {
        return database.currentTime();
    }

    public final void setEnableKeyReplace(boolean enable) {
        final boolean outer = enter();
        enableKeyReplace = enable;
        leave(outer);
    }

    public final boolean getEnableKeyReplace() {
        return enableKeyReplace;
    }

    /**
     * Returns the actual lookup time that was used for the last read operation.
     * 
     * @throws IllegalStateException
     *             if no operation has been made with the connection and thus
     *             not actual lookup time is available.
     */
    final long getActualLookupTime() {
        long result = getData.actualLookupTime;
        if (result == -1) {
            throw new IllegalStateException("No available actual lookup time, "
                    + "a call to a read operation must be made before calling getActualLookupTime().");
        }
        return result;
    }
    
    public TransactionInfo transactionInfo() {
        final boolean outer = enter();
        try {
            return transactionInfoInner();
        } finally {
            leave(outer);
        }
    }
    
    private TransactionInfo transactionInfoInner() {
        if (getData.actualLookupTime == -1) {
            throw new IllegalStateException("No available transaction info, "
                    + "a call to get() must be made before calling transactionInfo().");
        }
        
        if (getData.tpos == Spos.NULL) {
            // The get read the value while its transaction was stored (bergdb 005-34).
            throw new IllegalStateException("No available transaction info: the transaction "
                    + "that wrote the value was still being stored when get() read it; call "
                    + "get() again.");
        }
        
        if (getData.tpos == 0) {
            // No read has found a value (bergdb 015-62): the gets found no entry. 0 is no
            // transaction's position (a meta block is there), and Db.getTrans(0) threw
            // IllegalArgumentException.
            throw new IllegalStateException("No available transaction info: the get() found "
                    + "no entry, and no get() before it retrieved a value.");
        }
        
        // A record that the writer has not appended in whole yet: getTrans waits for it
        // (bergdb 021-13). It threw IllegalArgumentException, or failed the database.
        // Internal.getTrans(): the position is the database's, a get's, so a record there that
        // is not a committed transaction is damage (bergdb 021-27).
        StoredTrans stored = db.internal().getTrans(getData.tpos);
        
        // A record of reclaim's is not the transaction that wrote the value: reclaim has
        // rewritten the value, in a step of its own, so that the transaction that wrote it
        // can be cut (Reclaim.step). Until 2026-10-25 this method gave the step's time and its
        // row; then, until bergdb 021-17 (020-24-06, U6-1), it threw
        // LookupTimeNotAvailableException for every copy, from reclaim's first iteration on,
        // long before anything was cut. The copy is the value at the key just before the
        // step: the step reads the latest state and puts the value with the key as read (its
        // keyRead and readTime), so a write of the key between them makes it run again. So
        // the value at the step's time less one unit is the one copied, the original or an
        // older copy, followed back in the same way; each time is smaller than the last.
        // A time before the first available lookup time is refused: the transaction that
        // wrote the value is before it then, and reclaim has cut it or is about to.
        // A record that is no copy of reclaim's, though it holds a KV under reclaim's prefix,
        // is malformed internal data, which only a write through the Core's Db makes (keys
        // under /# are BergDB's, bergdb 020-22): refused with InternalDataException, and the
        // database goes on (bergdb 021-17, R17-1). It was taken for a copy and followed back:
        // with no value of the key before it, a Bug that failed the database; with one, a
        // wrong transaction. So the value before must be the record's own, byte for byte,
        // and stored before it. A Core write of the same bytes again with such a KV is still
        // taken for a copy.
        GetData before = null;
        while (isReclaims(stored)) {
            if (before == null) {
                before = db.newGetData();
            }
            final byte[] copy = valueOf(stored, infoKey);
            if (copy == null) {
                throw notACopy(stored, "it has no value of the key");
            }
            final long copyTime = stored.tt;
            final byte[] copied;
            try {
                copied = db.getOne(copyTime - 1, infoKey, before);
            } catch (LookupTimeNotAvailableException e) {
                final long first = db.getFirstAvailableLookupTime();
                LookupTimeNotAvailableException ex = new LookupTimeNotAvailableException(
                        "No available transaction info: reclaim has rewritten the value, at time "
                        + copyTime + " (" + Time.units(copyTime) + "), and the transaction that "
                        + "wrote it is before the first available lookup time, " + first + " ("
                        + Time.units(first) + "), and no longer available.");
                ex.initCause(e);
                throw ex;
            }
            if (copied == null) {
                throw notACopy(stored, "the key has no value before it");
            }
            if (!Arrays.equals(copied, copy)) {
                throw notACopy(stored, "the key's value before it is another");
            }
            if (before.tpos < 0 || before.tpos >= stored.tpos) {
                throw notACopy(stored, "the key's value before it is not stored before it, "
                        + "but at " + before.tpos);
            }
            stored = db.internal().getTrans(before.tpos);
        }
        final StoredTrans storedTrans = stored;
        
        // The user's KVs only (2026-10-25, bergdb 005-42): those under the internal prefix,
        // an index's entries, were given too, and their key() threw, as they have no ukey.
        // A key that is no ukey's, which only a write through the Core API makes, is left out
        // too (bergdb 020-22, R22-1): its key() threw, or gave the ukey of another key.
        final ArrayList<Kv<byte[]>> kvs = new ArrayList<Kv<byte[]>>();
        for (int i = 0; i < storedTrans.nodes.length; i++) {
            StoredNode storedNode = storedTrans.nodes[i];
            
            if (storedNode instanceof StoredValueNode) {
                final StoredValueNode storedValueNode = (StoredValueNode) storedNode;
                if (Keys.isPrefix(DbConstants.INTERNAL_PREFIX_SKEY, storedValueNode.getKey())) {
                    continue;
                }
                String ikey = Keys.bkey2ikeyOrNull(Keys.toBytes(storedValueNode.getKey()));
                final String ukey = ikey == null ? null : PubKeys.i2uOrNull(ikey);
                if (ukey == null) {
                    continue;
                }
                
                kvs.add(new Kv<byte[]>() {
                    public String key() {
                        return ukey;
                    }

                    public byte[] value() {
                        return storedValueNode.getValueNode().getValue();
                    }
                });
            }
        }
        
        return new TransactionInfo() {
            public Time time() {
                return Time.units(storedTrans.tt);
            }

            public List<Kv<byte[]>> kvs() {
                return kvs;
            }
        };
    }
    
    /**
     * True if 'stored' is one of reclaim's records, one with a KV under its prefix (bergdb
     * 005-42): a record of a step, the only one of reclaim's with a value of the user.
     */
    private static boolean isReclaims(StoredTrans stored) {
        for (StoredNode node : stored.nodes) {
            if (node instanceof StoredValueNode 
                    && Keys.isPrefix(Reclaim.KEY_PREFIX_SKEY, ((StoredValueNode) node).getKey())) {
                return true;
            }
        }
        return false;
    }
    
    /** The value that 'stored' puts at 'key', or null if it has none (or deletes it). */
    private static byte[] valueOf(StoredTrans stored, long[] key) {
        for (StoredNode node : stored.nodes) {
            if (node instanceof StoredValueNode 
                    && Arrays.equals(key, ((StoredValueNode) node).getKey())) {
                return ((StoredValueNode) node).getValueNode().getValue();
            }
        }
        return null;
    }
    
    /**
     * The refusal of a record with a KV under reclaim's prefix that is no copy of reclaim's
     * of the value of infoKey (bergdb 021-17, R17-1): malformed internal data.
     */
    private InternalDataException notACopy(StoredTrans stored, String why) {
        String ikey = Keys.bkey2ikeyOrNull(Keys.toBytes(infoKey));
        String ukey = ikey == null ? null : PubKeys.i2uOrNull(ikey);
        return new InternalDataException("No available transaction info: the record at stream "
                + "pos " + stored.tpos + " holds a KV under reclaim's prefix, but is no copy of "
                + "reclaim's of the value at " + (ukey == null ? "the key" : ukey) + ": " + why
                + ". Malformed internal data, which only a write through the Core's Db makes.");
    }

    /**
     * Internal method to get the value (byte[]) given a key (long[]) at a
     * specified lookup time. No argument checking.
     */
    final byte[] getBytesAtLookupTime(long lookupTime, long[] key) {
        byte[] value = db.getOne(lookupTime, key, getData);
        if (value != null) {
            infoKey = key;
        }
        
        // After the read, as in getInternal() (bergdb 015-48). Before it, a frozen time was
        // set to the time of the read before, or to -1 if there was none, and an exists()
        // as the first read after freezeLookupTime() froze that time, not its own.
        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }

        return value;
    }

    /**
     * The actual lookup time of a scan that starts now at the wanted time (usePrimary()):
     * resolved as a get resolves it, and, after freezeLookupTime(), it fixes the frozen time
     * as the first read after it does (bergdb 020-10, section 3.6). The connection's
     * GetData is not touched: transactionInfo() still describes the last get() (N3).
     */
    final long scanLookupTime(long wantedLookupTime) {
        long time = db.lookupTime(wantedLookupTime);
        if (this.freezeLookupTime && this.lookupTime != time) {
            this.lookupTime = time;
        }
        return time;
    }

    /**
     * @throws IllegalArgumentException
     *             If ukey is null or not of a valid format: PubKeys.u2i() throws it, as
     *             for get() and an rw-transaction's exists() (bergdb 019-05).
     */
    public final boolean exists(String ukey) {
        // NOTE Maybe we should have separate method for this. Or a boolean
        // field in GetData whether to get the actual value or not. 
        // Sometimes key and time is enough. Like here.

        if (ukey == null) {
            throw new IllegalArgumentException("ukey == null not allowed");
        }

        String ikey = PubKeys.u2i(ukey);
        final boolean outer = enter();
        try {
            byte[] bytes = getBytesAtLookupTime(lookupTime, Keys.toSegments(ikey));
            return bytes != null;
        } finally {
            leave(outer);
        }
    }

    public final Db getDb() {
        return db;
    }
    
    /**
     * Fails the database with an Error that a transaction of the Pub API met, also in the
     * application's Action, which runs before the Core's execute(), and returns it for the
     * call to throw as it is (2026-11-06, bergdb 019-10), as the Core's calls do (Db,
     * "Errors"): the database cannot tell whose Error it is.
     */
    final Error failed(Error e) {
        db.internal().fail(e);
        return e;
    }

    public Transaction rw(Action action) {
        if (action == null) {
            throw new IllegalArgumentException("action == null not allowed");
        }
        final boolean outer = enter();
        try {
            return new RwTransaction(this, action).execute();
        } finally {
            leave(outer);
        }
    }

    public WBuilder w() {
        return new WBuilderImp(this);
    }

    /**
     * @throws ObjectCreationException
     * @throws DbException
     * @throws IllegalArgumentException
     *             If an argument is null or if 'ukey' has an invalid format.
     */
    public <TYPE> TYPE get(String ukey, Class<TYPE> clazz) {
        if (clazz == null) {
            throw new IllegalArgumentException("clazz == null not allowed");
        }

        if (ukey == null) {
            throw new IllegalArgumentException("ukey == null not allowed");
        }

        String ikey = PubKeys.u2i(ukey);

        final boolean outer = enter();
        try {
            return getInternal(lookupTime, ikey, clazz);
        } finally {
            leave(outer);
        }
    }

    /**
     * Puts a key-object entry to the database. If an entry with the given key
     * already exists, it is overwritten.
     * 
     * @param key
     *            The key of the key-value entry. Must begin with "/".
     * @param object
     *            The object to store. Cannot be null.
     * @throws DbException
     *            If the transaction could not be processed because the
     *            database is faulty.
     * @throws IllegalArgumentException
     *            If 'key' is null or otherwise invalid, or if object is null.
     */
    public Transaction put(String key, Object object) {
        final boolean outer = enter();
        try {
            return w().put(key, object).execute();
        } finally {
            leave(outer);
        }
    }

    public Transaction delete(String key) {
        final boolean outer = enter();
        try {
            return w().delete(key).execute();
        } finally {
            leave(outer);
        }
    }

    /**
     * Get method for internal use. All gets (calls to Db.get() from Pub Layer)
     * should go through this method, getBytesAtLookupTime() or getInTransaction().
     * Sources of gets: Connection, IndexManager, IndexIterBuilderImp.IndexIterator; and
     * RwEnvironment, with getInTransaction().
     */
    public final <TYPE> TYPE getInternal(long lookupTime, String ikey, Class<TYPE> clazz) {
        final long[] key = Keys.toSegments(ikey);
        byte[] value = db.getOne(lookupTime, key, getData);
        if (value != null) {
            infoKey = key;
        }

        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }

        // What transactionInfo() describes is this get's, also when the conversion runs a
        // Data Object constructor that reads through this connection, which sets them
        // anew (020-24-11, U11-5: transactionInfo() then gave the constructor's read).
        final long tpos = getData.tpos;
        final long actualLookupTime = getData.actualLookupTime;
        final long[] readKey = infoKey;
        try {
            return database.getKvToObjectConverter().createObject(clazz, ikey, value);
        } finally {
            getData.tpos = tpos;
            getData.actualLookupTime = actualLookupTime;
            infoKey = readKey;
        }
    }
    
    /**
     * A read of an rw- or w-transaction on this connection (RwEnvironmentImp), with the
     * transaction's own GetData, gd, which gives the read's actual lookup time. It leaves
     * the connection's read state as it was: its frozen lookup time, and the last get() that
     * transactionInfo() describes (bergdb 015-42). Before, a transaction's reads went
     * through getInternal() and the connection's GetData: the first set a frozen lookup time
     * to the latest, and transactionInfo() then described the transaction's last read.
     */
    final <TYPE> TYPE getInTransaction(GetData gd, long lookupTime, String ikey, 
            Class<TYPE> clazz) {
        byte[] value = db.getOne(lookupTime, Keys.toSegments(ikey), gd);
        return database.getKvToObjectConverter().createObject(clazz, ikey, value);
    }

    public final DatabaseImp getDatabaseImp() {
        return this.database;
    }

    /**
     * @throws IllegalArgumentException
     *             if indexName == null, or type == null.
     * @throws NoSuchIndexException
     */
    public <TYPE> UseIndexBuilder<TYPE> useIndex(String indexName, Class<TYPE> type) {
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }

        if (type == null) {
            throw new IllegalArgumentException("type == null not allowed");
        }

        final boolean outer = enter();
        try {
            return new UseIndexBuilderImp<TYPE>(this, indexName, type, lookupTime);
                // throws NoSuchIndexException if index does not exists
        } finally {
            leave(outer);
        }
    }

    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) {
        // The class first, whatever the data (bergdb 020-09, section 3.3).
        if (type != null && !type.equals(String.class) && !type.equals(byte[].class)
                && !type.equals(DbObject.class) && !type.equals(Object.class)) {
            DataObjects.checkGet(type);
        }
        final boolean outer = enter();
        try {
            return new UsePrimaryBuilderImp<TYPE>(this, type, lookupTime);
        } finally {
            leave(outer);
        }
    }

    /**
     * Waits until ordinary durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws StreamIoException
     */
    public void sync() {
        sync(SyncLevel.ORDINARY);
    }
    
    /**
     * Waits until the specified durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws StreamIoException
     */
    public void sync(SyncLevel syncLevel) {
        final boolean outer = enter();
        try {
            this.db.sync(lastSposOfLastTrans, syncLevel);
        } finally {
            leave(outer);
        }
    }
}
