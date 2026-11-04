package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

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
import bergdb.pub.util.DatabaseMissingException;
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
        this.startupDistanceInMb = clampStartupDistanceInMb(startupDistanceInMb);
        return this;
    }
    
    /** The startup distance in MB, clamped to 5 to 1000; also Database's setter's. */
    static int clampStartupDistanceInMb(int startupDistanceInMb) {
        if (startupDistanceInMb < 5) {
            startupDistanceInMb = 5;
        }
        
        if (startupDistanceInMb > 1000) {
            startupDistanceInMb = 1000;
        }
        
        return startupDistanceInMb;
    }
    
    public DatabaseBuilder cacheSizeInMb(int cacheSizeInMb) {
        this.cacheSizeInMb = clampCacheSizeInMb(cacheSizeInMb);
        return this;
    }
    
    /** The cache size in MB, clamped to 4 to 100,000; also Database's setter's. */
    static int clampCacheSizeInMb(int cacheSizeInMb) {
        // Note: we might want to clamp depending on startupDistance? 2 x startupDistance perhaps.
        
        if (cacheSizeInMb < 4) {
            cacheSizeInMb = 4;
        }
        
        if (cacheSizeInMb > 100*1000) {
            // Limit to max 100 GB memory for cache
            cacheSizeInMb = 100*1000;
        }
        
        return cacheSizeInMb;
    }
    
    public Database start() {
        // In long (bergdb item 001, WP J7: M45 of bergdb 001-08; before 2026-10-18
        // int times int, which overflowed for more than 2,147 MB, so with heaps above about
        // 10.7 GB by default). It is the capacity controller's budget (core/Eviction.java).
        long cacheSizeIndicator = this.cacheSizeInMb * 1000000L;
        int startupDistance = this.startupDistanceInMb * 1000000;
        
        dbBuilder.startupDistance(startupDistance);
        dbBuilder.cacheSizeIndicator(cacheSizeIndicator);
        
        if (dir == null && !dbBuilder.hasStream()) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        // What can refuse the start is checked before openDirs() opens a directory, which
        // creates it, its lock file and an empty first stream file (2026-11-03, bergdb 015-01,
        // 015-06): a refused start opens, creates and writes nothing.
        checkCryptoKey();
        if (dir != null) {
            refuseMissingStream(dir);
        }
        
        Db db;
        List<FileStream> opened = new ArrayList<FileStream>();
        try {
            openDirs(opened);
            handleCryptoKeyAndCreatedTxt();
            db = dbBuilder.build();
        } catch (RuntimeException | Error e) {
            // A start that throws closes the streams that it opened (2026-10-24, bergdb
            // 005-32), and no other (2026-11-04, bergdb 015-56): the DbBuilder also holds the
            // streams of an earlier start of this builder, which its database uses. Until
            // 015-56 this closed every stream of the DbBuilder, so a second start(), refused
            // as the first's database has the directory, closed that database's stream: it
            // failed at its next sync, and its lock was released (bergdb 016-06, R8-F10).
            closeStreams(opened, e);
            throw e;
        }
        return DatabaseImp.createAndStart(db);
    }
    
    /**
     * Opens the directory of dir() (bergdb 005-66). The stream goes to 'opened' as it is
     * opened, so that a later failure of the start closes it (start(); bergdb 015-56), and
     * then to the DbBuilder. Until 2026-11-04 (bergdb 005-11) it opened the directories of
     * replica() too, after the database's own.
     */
    private void openDirs(List<FileStream> opened) {
        if (dir != null) {
            FileStream main = openDir(dir);
            opened.add(main);
            dbBuilder.mainStream(main);
        }
    }
    
    /**
     * Closes the streams that a start opened, for a start that throws (bergdb 005-32,
     * 015-56). A failure of a close is added to 'failure' as suppressed.
     */
    private static void closeStreams(List<FileStream> streams, Throwable failure) {
        for (FileStream stream : streams) {
            try {
                stream.close();
            } catch (IOException | RuntimeException e) {
                failure.addSuppressed(e);
            }
        }
    }
    
    /**
     * Refuses a crypto key of another algorithm than salsa, or with key data of another
     * length than 40 bytes; before the directories are opened (2026-11-03, bergdb 015-06).
     * Before, the start opened the directory first, and a refused start left it, its lock
     * file and an empty first stream file, which breaks the restore in place of a database
     * whose first file has another name (FileStream's check of the files' positions).
     */
    private void checkCryptoKey() {
        if (cryptoKey == null) {
            return;
        }
        String algo = cryptoKey.getAlgo();
        if (!algo.equals("salsa")) {
            throw new IllegalStateException("Cannot encrypt with algorithm '" + algo + "'. Not supported.");
        }
        byte[] keyData = cryptoKey.getKeyData();
        if (keyData.length != 40) {
            throw new IllegalStateException("Unexpected keyData length, " + keyData.length + ".");
        }
    }
    
    /**
     * Refuses a directory that held a database and has no stream byte (2026-11-03, bergdb
     * 015-01): it has created.txt, which a creation writes once its first bytes are durable
     * (Db.handleEmptyStream), and no *.bergdb file with a byte (FileStream.hasStreamBytes).
     * Before the directory is opened, so that the start opens, creates and writes nothing;
     * safe without the directory's lock, as a running database always has a stream file
     * with bytes. A directory without created.txt, also an empty or a missing one, is a new
     * database, as before.
     *
     * @throws DatabaseMissingException
     */
    private static void refuseMissingStream(File dir) {
        File createdTxt = new File(dir, "created.txt");
        if (createdTxt.isFile() && !FileStream.hasStreamBytes(dir)) {
            throw new DatabaseMissingException("The directory " + dir + " held a database "
                    + "(its created.txt), and its stream is missing: no stream file (*.bergdb) "
                    + "with a byte. The start has opened, created and written nothing. Restore "
                    + "the *.bergdb files from a backup and start again; or, to create a new, "
                    + "empty database there, remove created.txt and the *.bergdb files and "
                    + "start again (bergdb 015-01).");
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
        
        if (!dbBuilder.hasStream()) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        AppendOnlyStream aos = dbBuilder.getMainStream();
        
        if (this.cryptoKey == null) {
            if (aos instanceof FileStream) {
                FileStream fileStream = (FileStream) aos;
                dbBuilder.createdTxt(fileStream.getDir(), null);
            }
        } else {
            byte[] keyData = cryptoKey.getKeyData();     // checked by checkCryptoKey()
            
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
