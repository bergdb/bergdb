package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import bergdb.core.Db;
import bergdb.core.StoredNode;
import bergdb.core.StoredTrans;
import bergdb.core.StoredValueNode;
import bergdb.core.SyncLevel;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Kv;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.UseIndexBuilder;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.WBuilder;

/**
 * Implementation of Connection.
 * 
 * @author Frans Lundberg
 */
public class ConnectionImp implements Connection {
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
        this.lookupTime = Long.MAX_VALUE;
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
    
    public final Time time() {
        if (getData.actualLookupTime == -1) {
            throw new IllegalStateException("No available value time, "
                    + "a call to get() must be made before calling time().");
        }
        
        return Time.units(getData.kvTime);
    }
    
    public TransactionInfo transactionInfo() {
        if (getData.actualLookupTime == -1) {
            throw new IllegalStateException("No available transaction info, "
                    + "a call to get() must be made before calling transactionInfo().");
        }
        
        final StoredTrans storedTrans = db.getTrans(getData.tpos);
        
        final ArrayList<Kv<byte[]>> kvs = new ArrayList<Kv<byte[]>>();
        for (int i = 0; i < storedTrans.nodes.length; i++) {
            StoredNode storedNode = storedTrans.nodes[i];
            
            if (storedNode instanceof StoredValueNode) {
                final StoredValueNode storedValueNode = (StoredValueNode) storedNode;
                kvs.add(new Kv<byte[]>() {
                    public String key() {
                        // TODO D. we cannot in general convert keys to ukey (strings). How to handle in Pub Layer?
                        byte[] bkey = Keys.toBytes(storedValueNode.getKey());
                        String ukey = PubKeys.i2u(Keys.bkey2ikey(bkey));
                        return ukey;
                    }

                    public String ikey() {
                        throw new UnsupportedOperationException("not implemented");
                    }

                    public byte[] value() {
                        return storedValueNode.getValueNode().getValue();
                    }

                    public Time time() {
                        return Time.units(storedTrans.tt);
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
        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }

        return db.getOne(lookupTime, key, getData);
    }

    public Database getDatabase() {
        return database;
    }

    /**
     * @throws IllegalArgumentException
     *             Ff ukey is null or not of a valid format.
     */
    public final boolean exists(String ukey) {
        // NOTE Maybe we should have separate method for this. Or a boolean
        // field in GetData whether to get the actual value or not. 
        // Sometimes key and time is enough. Like here.

        if (ukey == null) {
            throw new IllegalArgumentException("ukey == null not allowed");
        }

        String ikey;

        try {
            ikey = PubKeys.u2i(ukey);
        } catch (IllegalArgumentException e) {
            return false;
        }

        byte[] bytes = getBytesAtLookupTime(lookupTime, Keys.toSegments(ikey));
        return bytes != null;
    }

    public final Db getDb() {
        return db;
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
     * @throws NoFieldsSetException
     * @throws DbException
     * @throws NoSuchObjectException
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

    /**
     * Puts a key-object entry to the database; the key is taken from the field
     * 'key' of the object. The object must have a field of type String and name
     * 'key', otherwise an exception is thrown. If an entry with the given key
     * already exists, it is overwritten.
     * 
     * @param object
     *            The object to store. Cannot be null and must have a String
     *            field named 'key'.
     * @throws DbException
     *             If the transaction could not be processed because the
     *             database is faulty.
     * @throws MissingKeyFieldException
     *             If 'object' does not have a String field named 'key'.
     * @throws IllegalArgumentException
     *             If the key field string is null or otherwise invalid, or if
     *             object is null.
     */
    public Transaction put(Object object) {
        return w().put(object).execute();
    }
    
    public Transaction delete(String key) {
        return w().delete(key).execute();
    }

    /**
     * Get method for internal use. All gets (calls to Db.get() from Pub Layer)
     * should go through this method or getBytesAtLookupTime(). Sources of gets:
     * Connection, RwEnvironment, IndexManager,
     * IndexIterBuilderImp.IndexIterator.
     */
    public final <TYPE> TYPE getInternal(long lookupTime, String ikey, Class<TYPE> clazz) {
        byte[] value = db.getOne(lookupTime, Keys.toSegments(ikey), getData);

        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }

        TYPE result = database.getKvToObjectConverter().createObject(clazz, ikey, value);
        return result;
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

        
        if (indexName.equals(Database.PRIMARY)) {
            throw new IllegalArgumentException("This method cannot be used for primary index (\""
                    + Database.PRIMARY + "\"), try Connection.usePrimary().");
        }

        UseIndexBuilderImp<TYPE> b = new UseIndexBuilderImp<TYPE>(this, indexName, type, lookupTime);
            // throws NoSuchIndexException if index does not exists
        return b;
    }

    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) {
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
