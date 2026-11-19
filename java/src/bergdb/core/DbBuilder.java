package bergdb.core;

import java.io.File;

import bergdb.pub.util.Clock;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * An object of this class is used to properly build a Db object: Db.builder() gives one, and
 * start() builds and starts the Db. A Db's user sets the stream (mainStream()), and may set
 * the clock and the cache size indicator; the defaults are the system clock and 200 MB. The
 * startup distance is not the builder's since bergdb 028-13: a new database has 50 MB, and
 * Db.setStartupDistance() changes it, also right after the start that creates the database.
 * The maximum node size is 30 for every database a user makes, and
 * no public method sets it (bergdb 026-08): the stream keeps it, and a start refuses a
 * database of another size. The sizes 8, 14 and 62 are for BergDB's own tests
 * (maxNodeSize8(), TestNodeSize). Of the other methods, id() and createdTxt() are for the Pub
 * API, and the rest for tests. Db's Javadoc, "Opening a database", has an example (bergdb
 * 020-24-09, U9-6).
 * 
 * <p>Part of the Core API, which Db's Javadoc names ("The Core API"; bergdb 020-27, Q1): for
 * low-level control and the most performance, less stable and less safe than the Pub API,
 * whose DatabaseBuilder (bergdb.pub) is the stable, default and preferred way to start a
 * database. The members that their Javadoc gives for tests are internal.</p>
 */
public class DbBuilder {
    Clock clock;
    int maxNodeSize;
    long cacheSizeIndicator;
    DatabaseId id;
    /** The database's one stream, or null (bergdb 005-11: no replicas since 2026-11-04). */
    DbBuilder.StreamInfo streamInfo = null;
    File createdTxtDir;
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
        // 2026-11-05 (bergdb 015-87): the retain duration is no longer a builder setting;
        // it is kept in the stream and set by Db.setRetainDuration. Forever until then.
        //
        // 2026-11-19 (bergdb 028-13): the startup distance is no longer the builder's; its
        // default, 50 MB, is Db.DEFAULT_STARTUP_DISTANCE.
        //
        
        cacheSizeIndicator = 200 * 1000000;
        clock = new SystemClock();
        
        maxNodeSize30();
    }
    
    /**
     * Creates a new DbBuilder instance.
     * Only Db should call this method.
     */
    static DbBuilder createForDb() {
        return new DbBuilder();
    }
    
    /** True if the stream is set. */
    public boolean hasStream() {
        return streamInfo != null;
    }
    
    public AppendOnlyStream getMainStream() {
        if (streamInfo == null) {
            return null;
        } else {
            return streamInfo.stream;
        }
    }
    
    /**
     * Chooses a non-default clock to use for the database; by default the system clock,
     * System.currentTimeMillis() in clock units (systemClock()).
     * 
     * @throws IllegalArgumentException  If clock is null: at the call since bergdb 020-27,
     *      Q2; before, build() refused it.
     */
    public DbBuilder clock(Clock clock) {
        if (clock == null) {
            throw new IllegalArgumentException("clock == null not allowed");
        }
        this.clock = clock;
        return this;
    }

    /**
     * Sets the database ID. This method is suitable for deterministic
     * testing. This setting only applies for non-existent databases.
     * 
     * @throws IllegalArgumentException  If id is null.
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

    /**
     * Maximum node size 8, for BergDB's own tests (bergdb 026-08): a small size gives deep
     * trees with few keys. Every database a user makes has 30; these setters are
     * package-private, and the tests outside bergdb.core reach them through TestNodeSize. A
     * database made at a size other than 30 carries no promise that a later release reads it.
     * The size must stay the same for a database: it is in the stream from the creation, and
     * a start with another size is refused (bergdb 005-50).
     */
    DbBuilder maxNodeSize8() {
        this.maxNodeSize = 8;
        return this;
    }

    /**
     * Maximum node size 14, for BergDB's own tests, as maxNodeSize8() (bergdb 026-08).
     */
    DbBuilder maxNodeSize14() {
        this.maxNodeSize = 16 - 2;
        return this;
    }

    /**
     * Maximum node size 30, the default and the size of every database a user makes, by
     * either API (bergdb 026-08; 024-19, Q1): for the tests that choose a size, as
     * maxNodeSize8().
     */
    DbBuilder maxNodeSize30() {
        this.maxNodeSize = 32 - 2;
        return this;
    }

    /**
     * Maximum node size 62, for BergDB's own tests, as maxNodeSize8() (bergdb 026-08). The
     * largest: a delete bitmap names 62 klongs of its node, and no larger size can be chosen
     * (bergdb 024-19, Q6).
     */
    DbBuilder maxNodeSize62() {
        this.maxNodeSize = 64 - 2;
        return this;
    }
    
    /**
     * The cache size indicator in bytes, the budget of the cache (Db.getCacheSizeIndicator());
     * 200 MB by default. A value below 1 is refused with IllegalArgumentException, as
     * Db.setCacheSizeIndicator() refuses it (bergdb 020-27: it was taken, a budget of 0 or
     * less, and an AssertionError of Cache3 with -ea).
     */
    public DbBuilder cacheSizeIndicator(long cacheSizeIndicator) {
        if (cacheSizeIndicator < 1) {
            throw new IllegalArgumentException("Bad cacheSizeIndicator: " + cacheSizeIndicator
                    + ".");
        }
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
    
    /**
     * The eviction schedule (Eviction; bergdb item 001, WPs J2, J3 and J7): the capacity
     * controller (budget, the default: the budget is the cache size indicator); or, for
     * tests, none, every detachable value after every transaction, every detachable object
     * after every transaction, or each slot to one with probability 0.3 (seeded). The
     * system property evict sets the default.
     * 
     * @throws IllegalArgumentException  If schedule is null (bergdb 020-27, Q2: it was taken,
     *      and the start threw NullPointerException).
     */
    public DbBuilder evictionSchedule(Eviction.Schedule schedule, long seed) {
        if (schedule == null) {
            throw new IllegalArgumentException("schedule == null not allowed");
        }
        this.evictionSchedule = schedule;
        this.evictionSeed = seed;
        return this;
    }

    /**
     * The reserve for a reclaim step's pinned bytes (Reclaim.setStepReserve; bergdb item 001,
     * WP J6). The default is Reclaim.DEFAULT_STEP_RESERVE, or the system property
     * stepreserve, so that the stress programs can split the steps. A setting for tests
     * (bergdb 015-87, F7): below the default it changes the stream's bytes, and it is not
     * kept in the stream.
     */
    public DbBuilder reclaimStepReserve(long bytes) {
        // Here, not in the Db's constructor after the storage has started (bergdb 005-32).
        if (bytes < 1) {
            throw new IllegalArgumentException("Illegal step reserve, " + bytes);
        }
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
     * Long.MAX_VALUE (Eviction, bergdb item 001, WP J7). The test setups use it. Without
     * eviction the dead hand does not run either (Eviction.deadStep; bergdb 023-07, section
     * 5.6): the memory of ended versions, the objects stored before a cut, is released only
     * at a restart (023-06, Z15).
     */
    public DbBuilder noEvict() {
        this.cacheSizeIndicator = Long.MAX_VALUE;
        return this;
    }
    
    /**
     * Sets main db stream, named "main", with the default buffer parameters; it replaces a
     * stream set before, whatever its name. For a database in a directory, a
     * bergdb.stream.FileStream on it; for one in memory, a bergdb.stream.MemoryStream (Db,
     * "Opening a database"). The Db closes the stream at its stop() or close().
     * 
     * @throws IllegalArgumentException  If stream is null; the stream set before is kept
     *      (bergdb 020-27, Q2: it was removed).
     */
    public DbBuilder mainStream(AppendOnlyStream stream) {
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }
        this.streamInfo = null;
        return stream("main", stream);
    }
    
    /** 
     * Sets the database's stream, default buffer parameters are used.
     * If 'name' is the same as the stream set before, that one is replaced.
     * 
     * @throws IllegalArgumentException  If name or stream is null.
     */
    public DbBuilder stream(String name, AppendOnlyStream stream) {
        return stream(name, stream, 
                StorageManager.DEFAULT_BUFFER_SIZE, 
                StorageManager.DEFAULT_BUFFER_TIME);
    }
    
    /** 
     * Sets the database's stream with the given buffer parameters.
     * If 'name' is the same as the stream set before, that one is replaced. A database has
     * one stream: since 2026-11-04 (bergdb 005-11) a stream of another name, until then a
     * replica, is refused with an IllegalStateException.
     * 
     * @param name
     *      Name of the stream.
     * @param stream
     *      The output database stream.
     * @param bufferSize
     *      Buffer size in bytes, the largest; a value below 100 is taken as 100. The buffer
     *      starts smaller, at most 64 KiB, and grows with use (BufferedStream, bergdb 026-07).
     * @param bufferTime  
     *      Maximum time in milliseconds to buffer the data 
     *      before the buffer is flushed; a value below 10 is taken as 10.
     * @throws IllegalArgumentException
     *      If name or stream is null, or bufferSize or bufferTime is negative.
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
        
        if (streamInfo != null && !streamInfo.name.equals(name)) {
            throw new IllegalStateException("A stream, '" + streamInfo.name + "', is set "
                    + "already; a database has one stream, and '" + name + "' would be a "
                    + "replica, removed in bergdb 005-11.");
        }
        streamInfo = info;     // replaces a previous value
        
        return this;
    }
    
    /**
     * If called, the database will (of possible) create a created.txt file in the
     * database directory. Its line "crypto key:" says "none (not encrypted)", or, for a main
     * stream that is a SalsaStream, internal since 2026.4, its key's name (bergdb 020-28:
     * until then this method took the key's line as a second argument; release 2026.4 has no
     * encryption in its API).
     * 
     * @param dir  The directory to create the file in.
     * @throws IllegalArgumentException  If dir is null (bergdb 020-27, Q2: it was taken, as no
     *      created.txt).
     */
    public DbBuilder createdTxt(File dir) {
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        this.createdTxtDir = dir;
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
     * 
     * @throws IllegalArgumentException  If stream is null; nothing is set then.
     */
    public DbBuilder testSetup(AppendOnlyStream stream) {
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }
        testSetupExceptStream();
        stream("main", stream, 100*1000, 10);
        return this;
    }
    
    /**
     * Tests setup except stream; test clock, no evict and testId(). The retain duration is
     * forever until Db.setRetainDuration is called (bergdb 015-87).
     */
    public void testSetupExceptStream() {
        // Test setup except for stream.
        clock(new CoreTestClock());
        noEvict();
        testId();
    }

    /**
     * Builds the Db; start() starts it.
     * 
     * @throws IllegalStateException  If no stream is set.
     */
    public Db build() {
        //
        // At this time, we know all Db settings. Time to create the Db object.
        //

        if (streamInfo == null) {
            throw new IllegalStateException("No stream. One is required.");
        }

        return new Db(this);
    }

    /**
     * Same as calling build() and then start() on the returned DB object.
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
