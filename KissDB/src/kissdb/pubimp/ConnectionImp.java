package kissdb.pubimp;

import kissdb.core.Db;
import kissdb.core.GetData;
import kissdb.core.Keys;
import kissdb.pub.Action;
import kissdb.pub.Connection;
import kissdb.pub.Database;
import kissdb.pub.UseIndexBuilder;
import kissdb.pub.NoSuchObjectException;
import kissdb.pub.UsePrimaryBuilder;
import kissdb.pub.Transaction;
import kissdb.pub.WBuilder;

public class ConnectionImp implements Connection {
    private final Db db;
    private final DatabaseImp database;
    private final GetData getData;
    private long lookupTime;
    private boolean enableKeyReplace;
    private boolean freezeLookupTime;
    
    public ConnectionImp(DatabaseImp database) {
        assert database != null;
        this.database = database;
        this.db = database.getDb();
        this.getData = new GetData();
        this.getData.actualLookupTime = -1;
        this.lookupTime = Long.MAX_VALUE;
        this.enableKeyReplace = false;
    }
    
    public final void setLookupTime(long lookupTime) {
        if (lookupTime < 0) {
            throw new IllegalArgumentException("Bad lookupTime, " + lookupTime + ".");
        }
        this.freezeLookupTime = false;
        this.lookupTime = lookupTime;
    }
    
    public final void freezeLookupTime() {
        this.freezeLookupTime = true;
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
     * @throws IllegalStateException if no operation has been made with the connection and thus
     * not actual lookup time is available.
     */
    public final long getActualLookupTime() {
        long result = getData.actualLookupTime;
        if (result == -1) {
            throw new IllegalStateException("No available actual lookup time, " +
            		"a call to a read operation must be made before calling this method.");
        }
        return result;
    }
    
    /**
     * Internal method to get the value (byte[]) given a key (long[])
     * at a specified lookup time. No argument checking.
     */
    final byte[] getBytesAtLookupTime(long lookupTime, long[] key) {
        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }
        
        return db.get(lookupTime, key, getData);
    }
    
    public Database getDatabase() {
        return database;
    }

    public final boolean exists(String ukey) {
        // NOTE Maybe we should have separate method for this. Or a boolean field in GetData
        // whether to get the actual value or not. Sometimes key and time can be enough. 
        // Like here.
        
        String ikey = PubKeys.u2i(ukey);
        
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
        return new RwTransaction(this, action);
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
     * Get method for internal use.
     * All gets (calls to Db.get() from Pub Layer) should go through this method
     * or getBytesAtLookupTime(). Sources of gets: Connection, RwEnvironment, 
     * IndexManager, IndexIterBuilderImp.IndexIterator.
     */
    public final <TYPE> TYPE getInternal(long lookupTime, String ikey, Class<TYPE> clazz) {
        byte[] value = db.get(lookupTime, Keys.toSegments(ikey), getData);
        
        if (this.freezeLookupTime && this.lookupTime != getData.actualLookupTime) {
            this.lookupTime = getData.actualLookupTime;
        }
        
//        String ukey;
//        try {
//            ukey = PubKeys.i2u(ikey);
//        } catch (IllegalArgumentException e) {
//            ukey = null;
//        }
        
        TYPE result = database.getKvToObject().createObject(clazz, ikey, value);
        return result;
    }
    
    public final DatabaseImp getDatabaseImp() {
        return this.database;
    }
    
    /**
     * @throws IllegalArgumentException if indexName == null, or type == null.
     * @throws NoSuchIndexException
     * @see kissdb.pub.Connection
     */
    public <TYPE> UseIndexBuilder<TYPE> useIndex(String indexName, Class<TYPE> type) {
        if (indexName == null) {
            throw new IllegalArgumentException("indexName == null not allowed");
        }
        
        if (type == null) {
            throw new IllegalArgumentException("type == null not allowed");
        }
        
        if (indexName.equals(Database.PRIMARY)) {
            throw new IllegalArgumentException("This method cannot be used for primary index (\"" + Database.PRIMARY 
                    + "\"), try Connection.usePrimary().");
        }
        
        UseIndexBuilderImp<TYPE> b = new UseIndexBuilderImp<TYPE>(this, indexName, type, lookupTime);
            // throws NoSuchIndexException if index does not exists
        return b;
    }
    
    public <TYPE> UsePrimaryBuilder<TYPE> usePrimary(Class<TYPE> type) {
        return new UsePrimaryBuilderImp<TYPE>(this, type, lookupTime);
    }
}

// NOTE Consider storing a RwEnvironmentImp object in this class. For performance. Heavy to initialize.
