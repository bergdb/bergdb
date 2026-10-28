package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.util.Clock;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;

/**
 * This class is used to build a Database instance.
 * Use like this: <code>Database d = Builder.database().settingX().start();</code>
 * to create a Database.
 * 
 * @author Frans Lundberg
 */
public class DatabaseBuilderImp implements DatabaseBuilder {
    private final DbBuilder dbBuilder;
    private CryptoKey cryptoKey = null;
    private int cacheSizeInMb;         // cache size indicator from user
    private int startupDistanceInMb;
    
    /** The directory of dir(), opened by start() (bergdb 005-66), or null. */
    private File dir = null;
    
    /** The directories of replica(), by name, in the order given; opened by start(). */
    private final Map<String, File> replicaDirs = new LinkedHashMap<String, File>();
    
    
    public DatabaseBuilderImp() {
        // Sets some default values.
        
        dbBuilder = Db.builder();
        
        long max = Runtime.getRuntime().maxMemory();
        if (max == Long.MAX_VALUE) {
            cacheSizeInMb = 100;
        } else {
            int maxMb = (int) (max / 1000000);
            cacheSizeInMb = maxMb / 5;
            if (cacheSizeInMb < 2) {
                cacheSizeInMb = 2;
            }
        }
        
        startupDistanceInMb = 50;      // Was 20 (2026-10-13).
    }
    
    /**
     * Returns the internal Db.Builder object.
     * Not part of Pub API.
     */
    public DbBuilder getDbBuilder() {
        return dbBuilder;
    }
    
    public DatabaseBuilder memory() {
        dbBuilder.mainStream(new MemoryStream());
        this.dir = null;
        return this;
    }
    
    public DatabaseBuilder cryptoKey(CryptoKey cryptoKey) {
        if (!cryptoKey.isNull()) {
            this.cryptoKey = cryptoKey;
        }
        
        return this;
    }
    
    public DatabaseBuilder replica(String name, String dir) throws IOException {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        replicaDirs.put(name, new File(dir));
        return this;
    }
    
    public DatabaseBuilder dir(String dirname) {
        File d = new File(dirname);
        return dir(d);
    }
    
    /**
     * Records the directory; start() opens it (bergdb 005-66). Until 005-66 this method
     * opened it, and a builder that was never started held it, since 005-63 its lock too,
     * until the JVM ended.
     */
    public DatabaseBuilder dir(File dir) {
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        this.dir = dir;
        return this;
    }
    
    public DatabaseBuilder clock(final Clock clock) {
        dbBuilder.clock(clock);
        return this;
    }
    
    public DatabaseBuilder retainDuration(Duration retainDuration) {
        dbBuilder.retainDuration(retainDuration.units());
        return this;
    }
    
    /**
     * Not part of Pub API.
     */
    public DatabaseBuilder mainStream(final AppendOnlyStream stream) {
        dbBuilder.mainStream(stream);
        this.dir = null;
        return this;
    }
    
    /**
     * Not part of Pub API.
     */
    public DatabaseBuilder stream(String name, AppendOnlyStream stream) {
        dbBuilder.stream(name, stream);
        return this;
    }
    
    public DatabaseBuilder startupDistanceInMb(int startupDistanceInMb) {
        if (startupDistanceInMb < 5) {
            startupDistanceInMb = 5;
        }
        
        if (startupDistanceInMb > 1000) {
            startupDistanceInMb = 1000;
        }
        
        this.startupDistanceInMb = startupDistanceInMb;
        return this;
    }
    
    public DatabaseBuilder cacheSizeInMb(int cacheSizeInMb) {
        // Note: we might want to clamp depending on startupDistance? 2 x startupDistance perhaps.
        
        if (cacheSizeInMb < 4) {
            cacheSizeInMb = 4;
        }
        
        if (cacheSizeInMb > 100*1000) {
            // Limit to max 100 GB memory for cache
            cacheSizeInMb = 100*1000;
        }
        
        this.cacheSizeInMb = cacheSizeInMb;
        return this;
    }
    
    public Database start() {
        // In long (bergdb item 001, WP J7: M45 of bergdb 001-08; before 2026-10-18
        // int times int, which overflowed for more than 2,147 MB, so with heaps above about
        // 10.7 GB by default). It is the capacity controller's budget (core/Eviction.java).
        long cacheSizeIndicator = this.cacheSizeInMb * 1000000L;
        int startupDistance = this.startupDistanceInMb * 1000000;
        
        dbBuilder.startupDistance(startupDistance);
        dbBuilder.cacheSizeIndicator(cacheSizeIndicator);
        
        if (dir == null && dbBuilder.getStreamCount() == 0) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        Db db;
        try {
            openDirs();
            handleCryptoKeyAndCreatedTxt();
            db = dbBuilder.build();
        } catch (RuntimeException | Error e) {
            // The streams that openDirs() opened are closed (2026-10-24, bergdb 005-32): a
            // crypto key of an unknown algorithm left the directory's file open.
            dbBuilder.closeStreams(e);
            throw e;
        }
        return DatabaseImp.createAndStart(db);
    }
    
    /**
     * Opens the directories of dir() and replica() (bergdb 005-66): the database's first,
     * then the replicas in the order given. Each stream goes to the DbBuilder as it is
     * opened, so that a failure closes those before it (start(), closeStreams).
     */
    private void openDirs() {
        if (dir != null) {
            dbBuilder.mainStream(openDir(dir));
        }
        for (Map.Entry<String, File> replica : replicaDirs.entrySet()) {
            int bufferSize = StorageManager.DEFAULT_REPLICA_BUFFER_SIZE;
            int bufferTime = StorageManager.DEFAULT_BUFFER_TIME;
            dbBuilder.stream(replica.getKey(), openDir(replica.getValue()), bufferSize, bufferTime);
        }
    }
    
    private static FileStream openDir(File dir) {
        try {
            return new FileStream(dir);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }

    private void handleCryptoKeyAndCreatedTxt() {
        // Note, that we do not handle buffer size, buffer time. Using defaults.
        // This is fine now (July 2015) since those parameters are not yet exposed to Pub API.
        
        if (dbBuilder.getStreamCount() == 0) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        AppendOnlyStream aos = dbBuilder.getMainStream();
        
        if (this.cryptoKey == null) {
            if (aos instanceof FileStream) {
                FileStream fileStream = (FileStream) aos;
                dbBuilder.createdTxt(fileStream.getDir(), null);
            }
        } else {
            String algo = cryptoKey.getAlgo();
            
            if (!algo.equals("salsa")) {
                throw new IllegalStateException("Cannot encrypt with algorithm '" + algo + "'. Not supported.");
            }
            
            byte[] keyData = cryptoKey.getKeyData();
            if (keyData.length != 40) {
                throw new IllegalStateException("Unexpected keyData length, " + keyData.length + ".");
            }
            
            SalsaStream salsa;
            
            try {
                byte[] nonce = Util.subarray(keyData, 0, 8);
                byte[] key = Util.subarray(keyData, 8, 32);
                salsa = new SalsaStream(aos, nonce, key);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            
            if (aos instanceof FileStream) {
                FileStream fileStream = (FileStream) aos;
                dbBuilder.createdTxt(fileStream.getDir(), cryptoKey.toStringWithMaskedKey());
            }
            
            dbBuilder.mainStream(salsa);
        }
    }
    
    
    // ======== Testing ========
    
    @Nano private static void testStartupDistance1() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.startupDistanceInMb(7).memory();
        Database database = b.start();
        long startupDistance = ((DatabaseImp) database).getDb().getStartupDistance();
        database.stop();
        
        Assert.assertEquals(7*1000000, startupDistance);
    }
    
    /** The cache size in bytes, the eviction budget, is computed in long (M45): 3,000 MB. */
    @Nano private static void testCacheSizeAbove2GB() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.cacheSizeInMb(3000).memory();
        Database database = b.start();
        long budget = ((DatabaseImp) database).getDb().internal().eviction().budget();
        database.stop();
        
        Assert.assertEquals(3000L * 1000000, budget);
    }
    
    @Nano private static void testStartupDistance2() {
        //
        // Tests clamping to minimum startup distance.
        //
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.startupDistanceInMb(1).memory();
        Database database = b.start();
        long startupDistance = ((DatabaseImp) database).getDb().getStartupDistance();
        database.stop();
        
        Assert.assertEquals(5*1000000, startupDistance);
    }
}
