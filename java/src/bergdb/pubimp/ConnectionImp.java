package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import bergdb.core.Db;
import bergdb.core.DbConstants;
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
    
    public final void setLookupTime(Time lookupTime) {
        if (lookupTime == null) {
            throw new IllegalArgumentException("lookupTime == null not allowed");
        }
        setLookupTime(lookupTime.units());
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
        this.freezeLookupTime = true;
        this.lookupTime = Time.MAX.units();
            // Each call freezes anew, at the latest state as of the next read (bergdb 018-04,
            // Q2). Before, a second call kept the first frozen time.
    }
    
    public Time currentTime() {
        return database.currentTime();
    }

    public final void setEnableKeyReplace(boolean enable) {
        enableKeyReplace = enable;
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
        
        final StoredTrans storedTrans = db.getTrans(getData.tpos);
        
        // The user's KVs only (2026-10-25, bergdb 005-42): those under the internal prefix,
        // an index's entries, were given too, and their key() threw, as they have no ukey.
        // And a record of reclaim's is not the transaction that wrote the value: reclaim has
        // rewritten the value, so that the transaction that wrote it can be cut. It gave the
        // step's time and its row.
        final ArrayList<Kv<byte[]>> kvs = new ArrayList<Kv<byte[]>>();
        for (int i = 0; i < storedTrans.nodes.length; i++) {
            StoredNode storedNode = storedTrans.nodes[i];
            
            if (storedNode instanceof StoredValueNode) {
                final StoredValueNode storedValueNode = (StoredValueNode) storedNode;
                if (Keys.isPrefix(Reclaim.KEY_PREFIX_SKEY, storedValueNode.getKey())) {
                    throw new LookupTimeNotAvailableException("No available transaction info: "
                            + "reclaim has rewritten the value, and the transaction that wrote "
                            + "it is no longer available.");
                }
                if (Keys.isPrefix(DbConstants.INTERNAL_PREFIX_SKEY, storedValueNode.getKey())) {
                    continue;
                }
                
                kvs.add(new Kv<byte[]>() {
                    public String key() {
                        byte[] bkey = Keys.toBytes(storedValueNode.getKey());
                        String ukey = PubKeys.i2u(Keys.bkey2ikey(bkey));
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
     * Internal method to get the value (byte[]) given a key (long[]) at a
     * specified lookup time. No argument checking.
     */
    final byte[] getBytesAtLookupTime(long lookupTime, long[] key) {
        byte[] value = db.getOne(lookupTime, key, getData);
        
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
        byte[] bytes = getBytesAtLookupTime(lookupTime, Keys.toSegments(ikey));
        return bytes != null;
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
        return new RwTransaction(this, action).execute();
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

        TYPE result = getInternal(lookupTime, ikey, clazz);
        return result;
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
        return w().put(key, object).execute();
    }

    public Transaction delete(String key) {
        return w().delete(key).execute();
    }

    /**
     * Get method for internal use. All gets (calls to Db.get() from Pub Layer)
     * should go through this method, getBytesAtLookupTime() or getInTransaction().
     * Sources of gets: Connection, IndexManager, IndexIterBuilderImp.IndexIterator; and
     * RwEnvironment, with getInTransaction().
     */
    public final <TYPE> TYPE getInternal(long lookupTime, String ikey, Class<TYPE> clazz) {
        byte[] value = db.getOne(lookupTime, Keys.toSegments(ikey), getData);

        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }

        TYPE result = database.getKvToObjectConverter().createObject(clazz, ikey, value);
        return result;
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


        UseIndexBuilderImp<TYPE> b = new UseIndexBuilderImp<TYPE>(this, indexName, type, lookupTime);
            // throws NoSuchIndexException if index does not exists
        return b;
    }

    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) {
        // The class first, whatever the data (bergdb 020-09, section 3.3).
        if (type != null && !type.equals(String.class) && !type.equals(byte[].class)
                && !type.equals(DbObject.class) && !type.equals(Object.class)) {
            DataObjects.checkGet(type);
        }
        return new UsePrimaryBuilderImp<TYPE>(this, type, lookupTime);
    }

    /**
     * Waits until ordinary durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws StreamIoException
     */
    public void sync() {
        this.db.sync(lastSposOfLastTrans, SyncLevel.ORDINARY);
    }
    
    /**
     * Waits until the specified durability has been achieved for the last
     * transaction started with this connection.
     * 
     * @throws StreamIoException
     */
    public void sync(SyncLevel syncLevel) {
        this.db.sync(lastSposOfLastTrans, syncLevel);
    }
}
