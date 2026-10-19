package bergdb.core;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import bergdb.pub.util.Clock;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * An object of this class is used to properly build a Db object.
 */
public class DbBuilder {
    Clock clock;
    int maxNodeSize;
    int startupDistance;
    long cacheSizeIndicator;
    long retainDurationInTimeUnits;
    DatabaseId id;
    List<DbBuilder.StreamInfo> streamInfos = new ArrayList<DbBuilder.StreamInfo>();
    File createdTxtDir;
    String createdTxtCryptoKeyInfo;
    Eviction.Schedule evictionSchedule = Eviction.defaultSchedule();
    long evictionSeed = Eviction.defaultSeed();
    int auditEvery = Audit.EVERY;
    long reclaimStepReserve = Long.getLong("stepreserve", Reclaim.DEFAULT_STEP_RESERVE);
    long evictionBudget = Long.getLong("evictbudget", -1);
    long secondTopOrdinal = 1;
    
    static class StreamInfo {
        String name;
        AppendOnlyStream stream;
        int bufferSize;
        int bufferTime;
    }

    private DbBuilder() {
        
        // DatabaseId.createRandom() is not used because it can be slow. 
        // A NULL id is replaced by Db when Db is started.
        id = DatabaseId.CREATE_LATER_MARKER;
        defaultSettings();
    }
    
    /**
     * Default database settings are specified in this method.
     */
    private void defaultSettings() {
        //
        // DatabaseBuilderImp (Pub API) is used, its defaults apply.
        //
        // 150103 Frans: keeping maxNodeSize30() after renewed investigation. 
        //      See end comments of Db class.
        // 130707 Frans: default retain duration = forever. Was one week before.
        //
        
        // 2026-10-13 (docs/levels.md, "Level 2 under load"): was 20 MB. With
        // 50 MB, startup takes about 0.6 s with 1000-byte values (1.4 s with 100-byte 
        // values, single-put transactions), and the bytes appended per user byte fall
        // by 9% (1000 bytes) to 26% (100 bytes). The cache size indicator is kept.
        startupDistance = 50 * 1000000;
        cacheSizeIndicator = 200 * 1000000;
        clock = new SystemClock();
        
        maxNodeSize30();
        retainDurationInTimeUnits = Long.MAX_VALUE;
    }
    
    /**
     * Creates a new DbBuilder instance.
     * Only Db should call this method.
     */
    static DbBuilder createForDb() {
        return new DbBuilder();
    }
    
    public int getStreamCount() {
        return streamInfos.size();
    }
    
    public AppendOnlyStream getMainStream() {
        if (streamInfos.size() == 0) {
            return null;
        } else {
            return streamInfos.get(0).stream;
        }
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
            DbBuilder.StreamInfo info = streamInfos.get(i);
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
    public DbBuilder clock(Clock clock) {
        this.clock = clock;
        return this;
    }

    /**
     * Sets the database ID. This method is suitable for deterministic
     * testing. This setting only applies for non-existent databases.
     */
    public DbBuilder id(DatabaseId id) {
        if (id == null) {
            throw new IllegalArgumentException("id == null not allowed");
        }

        this.id = id;
        return this;
    }
    
    /**
     * Use a test ID (DatabaseId.TEST_ID) for database ID.
     * This is faster than generating an id with SecureRandom which is the default
     * when no id has been set in this builder.
     */
    public DbBuilder testId() {
        this.id = DatabaseId.TEST_ID;
        return this;
    }

    public DbBuilder maxNodeSize8() {
        this.maxNodeSize = 8;
        return this;
    }

    public DbBuilder maxNodeSize14() {
        this.maxNodeSize = 16 - 2;
        return this;
    }

    public DbBuilder maxNodeSize30() {
        this.maxNodeSize = 32 - 2;
        return this;
    }

    public DbBuilder maxNodeSize62() {
        this.maxNodeSize = 64 - 2;
        return this;
    }

    public DbBuilder startupDistance(int startupDistance) {
        if (startupDistance < 10) {
            throw new IllegalArgumentException("Too small, " + startupDistance);
        }

        this.startupDistance = startupDistance;
        return this;
    }
    
    public DbBuilder cacheSizeIndicator(long cacheSizeIndicator) {
        this.cacheSizeIndicator = cacheSizeIndicator;
        return this;
    }
    
    /**
     * Use the system clock (System.currentTimeMillis()) as the database
     * time.
     */
    public DbBuilder systemClock() {
        this.clock = new SystemClock();
        return this;
    }
    
    public DbBuilder retainDuration(long retainDurationInTimeUnits) {
        final long MIN = 1 * Clock.UNITS_PER_SEC;
        
        if (retainDurationInTimeUnits < 0) {
            throw new IllegalArgumentException("Negative retainDuration not allowed.");
        }
        
        if (retainDurationInTimeUnits < MIN) {
            throw new IllegalArgumentException("retainDuration is too small, must be at " +
            		"least one second (" + MIN + "), was " + retainDurationInTimeUnits + ".");
        }
        
        this.retainDurationInTimeUnits = retainDurationInTimeUnits;
        return this;
    }
    
    public DbBuilder retainForever() {
        return retainDuration(Long.MAX_VALUE);
    }

    /**
     * The eviction schedule (Eviction; bergdb item 001, WPs J2, J3 and J7): the capacity
     * controller (budget, the default: the budget is the cache size indicator); or, for
     * tests, none, every detachable value after every transaction, every detachable object
     * after every transaction, or each slot to one with probability 0.3 (seeded). The
     * system property evict sets the default.
     */
    public DbBuilder evictionSchedule(Eviction.Schedule schedule, long seed) {
        this.evictionSchedule = schedule;
        this.evictionSeed = seed;
        return this;
    }

    /**
     * The reserve for a reclaim step's pinned bytes (Reclaim.setStepReserve; bergdb item 001,
     * WP J6). The default is Reclaim.DEFAULT_STEP_RESERVE, or the system property
     * stepreserve, so that the stress programs can split the steps.
     */
    public DbBuilder reclaimStepReserve(long bytes) {
        this.reclaimStepReserve = bytes;
        return this;
    }

    /**
     * The audit (Audit; bergdb item 001, WP J1), for tests: after every 'every'-th
     * transaction and at every startup, with its oracle; 0 is off. The default is the
     * system property audit.
     */
    public DbBuilder audit(int every) {
        this.auditEvery = every;
        return this;
    }

    /**
     * For tests (bergdb item 005-02): the database's second top node gets this ordinal, not
     * 1 (TopDs.setSecondOrdinal), so that a test crosses 2^30, 2^31 or 2^32, or reaches the
     * end of the ordinals near 2^48, without making as many top nodes. Give it at every
     * start of the database, as the node size: the startup's rerun makes the top nodes of
     * the startup section again.
     */
    public DbBuilder secondTopOrdinal(long ordinal) {
        this.secondTopOrdinal = ordinal;
        return this;
    }

    /**
     * No eviction: the capacity controller's budget, the cache size indicator, becomes
     * Long.MAX_VALUE (Eviction, bergdb item 001, WP J7). The test setups use it.
     */
    public DbBuilder noEvict() {
        this.cacheSizeIndicator = Long.MAX_VALUE;
        return this;
    }
    
    /**
     * Sets main db stream.
     */
    public DbBuilder mainStream(AppendOnlyStream appendOnlyStream) {
        if (this.streamInfos.size() == 0) {
            stream("main", appendOnlyStream);
        } else {
            DbBuilder.StreamInfo info = new StreamInfo();
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
    public DbBuilder stream(String name, AppendOnlyStream aos) {
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
    public DbBuilder stream(String name, AppendOnlyStream stream, int bufferSize, int bufferTime) {
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
        
        DbBuilder.StreamInfo info = new StreamInfo();
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
     * If called, the database will (of possible) create a created.txt file in the
     * database directory.
     * 
     * @param dir  The directory to create the file in.
     * @param cryptoKeyInfo  Information about the crypto key used or null if encryption is not used.
     */
    public DbBuilder createdTxt(File dir, String cryptoKeyInfo) {
        this.createdTxtDir = dir;
        this.createdTxtCryptoKeyInfo = cryptoKeyInfo;
        return this;
    }

    /**
     * Used for the default unit test setup. No write to disk, a deterministic
     * clock is used. The node stream is an in-memory stream.
     * Short buffer time (10 ms) for fast tests.
     */
    public DbBuilder testSetup() {
        testSetupExceptStream();
        stream("main", new MemoryStream(), 100*1000, 10);
        return this;
    }
    
    /**
     * Use the default unit test setup and a specified stream.
     * Short buffer time (10 ms) for fast tests.
     */
    public DbBuilder testSetup(AppendOnlyStream stream) {
        testSetupExceptStream();
        stream("main", stream, 100*1000, 10);
        return this;
    }
    
    /**
     * Tests setup except stream; test clock, no evict, retain forever and testId().
     */
    public void testSetupExceptStream() {
        // Test setup except for stream.
        clock(new CoreTestClock());
        noEvict();
        retainForever();
        testId();
    }

    public Db build() {
        //
        // At this time, we know all Db settings. Time to create the Db object.
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
