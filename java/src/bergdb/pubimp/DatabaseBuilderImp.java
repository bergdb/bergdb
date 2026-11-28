package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.storage.StreamIoException;
import bergdb.storage.VersioningStreamException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * This class is used to build a Database instance.
 * Use like this: <code>Database d = Builder.database().settingX().start();</code>
 * to create a Database.
 * 
 * @author Frans Lundberg
 */
public class DatabaseBuilderImp implements DatabaseBuilder {
    private final DbBuilder dbBuilder;
    private int cacheSizeInMb;         // cache size indicator from user
    
    /** The directory of create() or open(), opened by start() (bergdb 005-66), or null. */
    private File dir = null;
    
    /** True for open(): start() refuses a directory without a database (bergdb 015-05). */
    private boolean mustExist = false;
    
    /**
     * The database of this builder's last start on a stream of memory() or mainStream(), and
     * that stream, or null; for refuseStreamInUse() (bergdb 015-65).
     */
    private Db streamDb = null;
    private AppendOnlyStream streamDbStream = null;
    
    
    public DatabaseBuilderImp() {
        // Sets some default values.
        
        dbBuilder = Db.builder();
        
        cacheSizeInMb = defaultCacheSizeInMb(Runtime.getRuntime().maxMemory());
    }
    
    /**
     * The default cache size in MB for a JVM whose maximum heap is maxMemory bytes
     * (Runtime.maxMemory(), Long.MAX_VALUE for no maximum): a fifth of it, clamped as a
     * value of cacheSizeInMb() is, to 4 to 100,000 (2026-11-09, bergdb 020-25, C3: it was
     * at least 2 and not clamped above, so a heap under 20 MB gave 2 or 3, and one over 500
     * GB more than 100,000), or 100 for no maximum.
     */
    static int defaultCacheSizeInMb(long maxMemory) {
        if (maxMemory == Long.MAX_VALUE) {
            return 100;
        }
        return clampCacheSizeInMb((int) Math.min(Integer.MAX_VALUE, maxMemory / 5000000));
    }
    
    /**
     * Returns the internal Db.Builder object. Internal, not API (bergdb 020-10, section 7): for BergDB's tests and tools.
     */
    public DbBuilder getDbBuilder() {
        return dbBuilder;
    }
    
    public DatabaseBuilder memory() {
        dbBuilder.mainStream(new MemoryStream());
        this.dir = null;
        this.mustExist = false;
        return this;
    }
    
    /** Records the directory, in which start() may create a database (bergdb 015-05). */
    public DatabaseBuilder create(String dirname) {
        return directory(dirname, false);
    }
    
    /** Records the directory, in which start() must find a database (bergdb 015-05). */
    public DatabaseBuilder open(String dirname) {
        return directory(dirname, true);
    }
    
    /**
     * Records the directory; start() opens it (bergdb 005-66). Until 005-66 the builder's
     * dir() opened it, and a builder that was never started held it, since 005-63 its lock
     * too, until the JVM ended. Until 015-05 dir() was create(), and open() did not exist.
     */
    private DatabaseBuilder directory(String dirname, boolean mustExist) {
        if (dirname == null) {
            throw new IllegalArgumentException("dirname == null not allowed");
        }
        this.dir = new File(dirname);
        this.mustExist = mustExist;
        return this;
    }
    
    /**
     * Refuses null here (bergdb 019-44); until 019-44 it was taken, and start() threw
     * IllegalArgumentException after it had made the directory and bergdb.lock.
     */
    public DatabaseBuilder clock(final Clock clock) {
        if (clock == null) {
            throw new IllegalArgumentException("clock == null not allowed");
        }
        dbBuilder.clock(clock);
        return this;
    }
    
    /**
     * The database's main stream. Internal, not API (bergdb 020-10, section 7): for BergDB's tests and tools.
     */
    public DatabaseBuilder mainStream(final AppendOnlyStream stream) {
        dbBuilder.mainStream(stream);
        this.dir = null;
        this.mustExist = false;
        return this;
    }
    
    /**
     * A stream of the database by its name. Internal, not API (bergdb 020-10, section 7): for BergDB's tests and tools.
     */
    public DatabaseBuilder stream(String name, AppendOnlyStream stream) {
        dbBuilder.stream(name, stream);
        return this;
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
        
        dbBuilder.cacheSizeIndicator(cacheSizeIndicator);
        
        if (dir == null && !dbBuilder.hasStream()) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        if (dir == null) {
            refuseStreamInUse();
        }
        
        // What can refuse the start is checked before openDirs() opens a directory, which
        // creates it and its lock file (2026-11-03, bergdb 015-01, 015-06; open()'s refusal
        // 2026-11-05, 015-05): a refused start opens, creates and writes nothing. A start
        // refused after the open, in Db.start before the creation's first write (a clock out
        // of range, bergdb 005-18), leaves the lock file, never deleted (bergdb 005-63), and
        // no stream file: the first append creates the first (2026-11-06, bergdb 015-06).
        if (dir != null) {
            refuseMissingStream(dir);
            refuseEncrypted(dir);
            if (mustExist) {
                refuseNoDatabase(dir);
            }
        }
        
        Db db;
        List<FileStream> opened = new ArrayList<FileStream>();
        try {
            openDirs(opened);
            handleCreatedTxt();
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
        DatabaseImp database = DatabaseImp.createAndStart(db);
        if (dir == null) {
            streamDb = db;
            streamDbStream = dbBuilder.getMainStream();
        }
        return database;
    }
    
    /**
     * Refuses a start on the stream of memory() or mainStream() that this builder gave to a
     * database that has not closed: it runs, or is closing after stop() (2026-11-05, bergdb
     * 015-65), as start() refuses a directory that a database has (bergdb 005-63). Until
     * 015-65 a second start gave the running database's stream to a second database: both
     * appended to it, each missed the other's puts, and the close of one closed the stream
     * of the other.
     * memory() and mainStream() give the builder another stream, which is not refused.
     */
    private void refuseStreamInUse() {
        if (streamDb == null) {
            return;
        }
        if (dbBuilder.getMainStream() != streamDbStream || streamDb.internal().isClosed()) {
            streamDb = null;
            streamDbStream = null;
            return;
        }
        throw new IllegalStateException("The database that this builder started on its "
                + "stream of memory() has not closed: it runs, or is closing after stop(). "
                + "A second database on the stream would append to it too. Close that "
                + "database first, or call memory() for a new database (bergdb 015-65).");
    }
    
    /**
     * Opens the directory of create() or open() (bergdb 005-66). The stream goes to
     * 'opened' as it is opened, so that a later failure of the start closes it (start();
     * bergdb 015-56), and then to the DbBuilder. Until 2026-11-04 (bergdb 005-11) it opened the directories of
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
     * Refuses a directory that held a database and has no stream byte (2026-11-03, bergdb
     * 015-01): it has created.txt, which a creation writes once its records are durable
     * (Db.startInner; bergdb 028-18), and no *.bergdb file with a byte
     * (FileStream.hasStreamBytes).
     * Before the directory is opened, so that the start opens, creates and writes nothing;
     * safe without the directory's lock, as a running database always has a stream file
     * with bytes. A directory without created.txt, also an empty or a missing one, is a new
     * database, as before.
     *
     * @throws DatabaseMissingException
     */
    private static void refuseMissingStream(File dir) {
        File createdTxt = new File(dir, "created.txt");
        if (createdTxt.isFile() && !hasStreamBytes(dir)) {
            throw new DatabaseMissingException("The directory " + dir + " held a database "
                    + "(its created.txt), and its stream is missing: no stream file (*.bergdb) "
                    + "with a byte. The start has opened, created and written nothing. Restore "
                    + "the *.bergdb files from a backup and start again; or, to create a new, "
                    + "empty database there, remove created.txt and the *.bergdb files and "
                    + "start again (bergdb 015-01).");
        }
    }
    
    /**
     * Refuses a directory whose database an earlier release encrypted (2026-11-09, bergdb
     * 020-28): BergDB has no encryption in its API since release 2026.4, and such a stream
     * does not read without its key. Its created.txt names the key, its data masked, on the
     * line "crypto key:", as every release with encryption wrote it, at the creation and at
     * a start that found the file missing; a database without encryption has "none (not
     * encrypted)" there, and one created since 2026-11-27 has no such line (bergdb 028-69).
     * Before the directory is opened, so that the start opens, creates and writes nothing;
     * it only reads created.txt, so the lock is not needed. A directory without created.txt,
     * or without that line, is not refused here: a stream that an earlier release encrypted
     * is then refused by its magic bytes (Db.startInner), with a StreamFormatException whose
     * message names this case among others.
     *
     * @throws VersioningStreamException
     * @throws StreamIoException  if created.txt cannot be read
     */
    private static void refuseEncrypted(File dir) {
        String keyInfo = createdTxtKeyInfo(dir);
        if (keyInfo == null || keyInfo.isEmpty() || keyInfo.startsWith("none")) {
            return;
        }
        throw new VersioningStreamException("The database in " + dir + " is encrypted: its "
                + "created.txt names the crypto key " + keyInfo + ". An earlier release of "
                + "BergDB, 2026.3 or before, encrypted it, and this release cannot start it: "
                + "BergDB has no encryption since release 2026.4. The start has opened, created "
                + "and written nothing. To keep the data, read it with the release that wrote "
                + "the database and its key, and put it into a new database with this release, "
                + "for example with two programs, one on each release's jar; the history is "
                + "not copied (bergdb 020-28; the release notes of 2026.4).");
    }
    
    /**
     * The value of created.txt's line "crypto key:" in 'dir', trimmed, such as "none (not
     * encrypted)" or "3fa2c901-salsa-****"; null if the directory has no created.txt, or the
     * file has no such line (bergdb 020-28). The file is read as ISO-8859-1, so that any bytes
     * read: the line is ASCII.
     *
     * @throws StreamIoException  if created.txt cannot be read
     */
    static String createdTxtKeyInfo(File dir) {
        File createdTxt = new File(dir, "created.txt");
        if (!createdTxt.isFile()) {
            return null;
        }
        byte[] bytes;
        try {
            bytes = java.nio.file.Files.readAllBytes(createdTxt.toPath());
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        String text = new String(bytes, java.nio.charset.StandardCharsets.ISO_8859_1);
        final String label = "crypto key:";
        for (String line : text.split("\\r?\\n")) {
            if (line.startsWith(label)) {
                return line.substring(label.length()).trim();
            }
        }
        return null;
    }
    
    /**
     * For open(), which never creates a database (2026-11-05, bergdb 015-05): refuses a
     * directory that is missing, is not a directory, or holds no *.bergdb file with a byte
     * (FileStream.hasStreamBytes); after refuseMissingStream, whose message tells more of a
     * directory with created.txt. Before the directory is opened, so that the start creates
     * and writes nothing; safe without the lock, as for refuseMissingStream.
     *
     * @throws DatabaseMissingException
     */
    private static void refuseNoDatabase(File dir) {
        String what;
        if (!dir.exists()) {
            what = "the directory does not exist";
        } else if (!dir.isDirectory()) {
            what = "it is not a directory";
        } else if (!hasStreamBytes(dir)) {
            what = "it has no stream file (*.bergdb) with a byte";
        } else {
            return;
        }
        throw new DatabaseMissingException("No database in " + dir + ": " + what + ". "
                + "DatabaseBuilder.open() never creates one; the start has created and written "
                + "nothing. Check the path, and that its volume is mounted; to create a new "
                + "database there, use DatabaseBuilder.create() (bergdb 015-05).");
    }
    
    /**
     * FileStream.hasStreamBytes(dir); a StreamIoException, as for a directory that cannot be
     * opened, if it cannot be listed: an I/O error, or no permission to read it (bergdb
     * 020-20). Until 020-20 such a directory with created.txt was refused as one whose stream
     * is missing, with a message that said to remove its files.
     */
    private static boolean hasStreamBytes(File dir) {
        try {
            return FileStream.hasStreamBytes(dir);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    private static FileStream openDir(File dir) {
        try {
            return new FileStream(dir);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }

    /** A directory's database, whose main stream is a FileStream, has created.txt. */
    private void handleCreatedTxt() {
        // Note, that we do not handle buffer size, buffer time. Using defaults.
        // This is fine now (July 2015) since those parameters are not yet exposed to Pub API.
        
        if (!dbBuilder.hasStream()) {
            throw new IllegalStateException("no streams, please provide a database stream");
        }
        
        AppendOnlyStream aos = dbBuilder.getMainStream();
        if (aos instanceof FileStream) {
            FileStream fileStream = (FileStream) aos;
            dbBuilder.createdTxt(fileStream.getDir());
        }
    }
    
    
    // ======== Testing ========
    
    /**
     * A new database has 50 MB; Database.setStartupDistanceInMb() sets another right after
     * the start (bergdb 028-13: the builder's startupDistanceInMb() was removed).
     */
    @Nano private static void testStartupDistance1() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.memory();
        Database database = b.start();
        long before = ((DatabaseImp) database).getDb().getStartupDistance();
        database.setStartupDistanceInMb(7);
        long startupDistance = ((DatabaseImp) database).getDb().getStartupDistance();
        database.stop();
        
        Assert.assertEquals("the default", 50*1000000, before);
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
    
    /**
     * bergdb 019-44: clock(null) is refused, as create(null) and open(null) are; before, it
     * was taken and start() threw after it had made the directory and bergdb.lock.
     */
    @Nano private static void testClockNullRefused() {
        IllegalArgumentException e = null;
        try {
            new DatabaseBuilderImp().clock(null);
        } catch (IllegalArgumentException e1) {
            e = e1;
        }
        Assert.assertTrue("IllegalArgumentException for clock(null)", e != null);
    }
    
    /** The setter clamps to 5 to 1000 MB (bergdb 028-13: as the builder's method did). */
    @Nano private static void testStartupDistance2() {
        DatabaseBuilderImp b = new DatabaseBuilderImp();
        b.memory();
        Database database = b.start();
        database.setStartupDistanceInMb(1);
        long low = ((DatabaseImp) database).getDb().getStartupDistance();
        database.setStartupDistanceInMb(5000);
        long high = ((DatabaseImp) database).getDb().getStartupDistance();
        database.setStartupDistanceInMb(Integer.MIN_VALUE);
        int mb = database.getStartupDistanceInMb();
        database.stop();
        
        Assert.assertEquals(5*1000000, low);
        Assert.assertEquals(1000*1000000, high);
        Assert.assertEquals(5, mb);
    }
}
