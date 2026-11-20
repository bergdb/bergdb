package bergdb.pub;

import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;

/**
 * A DatabaseBuilder is used to create a Database.
 * Use the settings methods (create or open, memory, clock, ...) and then 
 * call start() to create and start the database. The startup distance is not the
 * builder's: a new database has 50 MB, and Database.setStartupDistanceInMb() changes it,
 * also right after the start that creates the database (bergdb 028-13).
 * 
 * @see Database
 * @author Frans Lundberg
 */
public interface DatabaseBuilder {
    
    /**
     * Opens the database in the given directory, or creates one there if the directory holds
     * none, as NIO's {@code StandardOpenOption.CREATE} opens a file or creates it (bergdb
     * 015-05). The database's stream is stored in files in the directory. start() opens the
     * directory, and creates it, with its missing parents, if it does not exist; a directory
     * that holds neither created.txt nor a stream file (*.bergdb) with a byte, a missing or
     * an empty one, or one with other files only, gets a new, empty database. This method
     * only records the directory (bergdb 005-66), so a builder that is not started holds
     * nothing, and start() throws what opening the directory throws.
     * 
     * <p>A directory that holds a database has created.txt, written once the database's
     * creation is durable; start() refuses one that has created.txt and no stream file
     * (*.bergdb) with a byte, with a DatabaseMissingException (bergdb 015-01). A directory
     * without created.txt and without a stream file with a byte, also an empty or a missing
     * one, gets a new, empty database, as a wrong path or a volume that is not mounted does
     * too. A directory with stream files and without created.txt is opened, and the start
     * writes created.txt again (bergdb 020-24-08, U8-8). An application that must never
     * create a database there uses {@link #open(String)}.</p>
     * 
     * @param dirname  The database's directory.
     * @throws IllegalArgumentException If dirname is null.
     */
    public DatabaseBuilder create(String dirname);
    
    /**
     * Opens the existing database in the given directory, and never creates one: start()
     * throws a DatabaseMissingException if the directory is missing, is not a directory, or
     * holds no stream file (*.bergdb) with a byte (bergdb 015-05). Such a start creates and
     * writes nothing: no directory, no lock file, no created.txt and no stream file. So a
     * wrong path, or a volume that is not mounted, is refused, where {@link #create(String)}
     * would give a new, empty database; an application whose database must be there, and a
     * tool that reads a database, use this method. This method only records the directory
     * (bergdb 005-66), as create(String) does; start() opens it.
     * 
     * <p>A directory with created.txt and no stream byte is refused as by create(String),
     * with that DatabaseMissingException's message (bergdb 015-01).</p>
     * 
     * @param dirname  The database's directory.
     * @throws IllegalArgumentException If dirname is null.
     */
    public DatabaseBuilder open(String dirname);
    
    /**
     * An in-memory database stream will be used.
     * This option may be suitable for testing.
     */
    public DatabaseBuilder memory();
    
    /**
     * Sets a non-default database clock. Use this method together with a TestClock to do
     * deterministic testing. The database's threads call the clock, so it must be
     * thread-safe (bergdb 019-44).
     * 
     * @throws IllegalArgumentException If clock is null (bergdb 019-44).
     */
    public DatabaseBuilder clock(Clock clock);
    
    /**
     * Sets a cache size indicator in MB.
     * A small value will leave more available memory for the rest of the JVM application,
     * while a larger value likely improves database performance.
     * The actual resulting cache size depends on application code, 
     * the operating system and the JVM. 
     * The cache size indicator is the budget of the database's cache: when
     * the index nodes and values it holds in memory pass it, it evicts those used least
     * recently, down to three quarters of it. What the database must keep in memory (the
     * nodes changed since its startup position, of the order of the startup distance) is
     * never evicted and may exceed it. The default is a fifth of the JVM's maximum heap,
     * clamped as a value given is (bergdb 020-25, C3), or 100 if the JVM has no maximum.
     * Database.setCacheSizeInMb() changes it while the database runs, for that run (bergdb
     * 005-52). The value is clamped to 4 to 100,000.
     * 
     * <p>A budget below what the database must keep slows it down, by design: the database
     * is then over its budget all the time, each commit ends with a batch of eviction, and a
     * read that loads an index node or a value from the stream waits for the eviction
     * thread, at most 2 ms a load, whenever the loads outrun it; so while anything is
     * written, reads go at the pace of eviction. What must be kept follows the startup
     * distance, not the budget: about 2 to 3 times the startup distance of heap
     * (Database.setStartupDistanceInMb()). In a new user's catalogue of 2 million objects at
     * the default startup distance, 50, the heap held 110 to 160 MB after a start with a
     * budget of 4 MB, and gets were several times fewer than with a budget of 200 MB while a
     * writer wrote (bergdb 020-24-04, U4-1 and U4-2). So give a budget well above what must
     * be kept; for a small heap, make the startup distance small, not the budget.</p>
     * 
     * @param cacheSizeInMb  The cache size indicator in megabytes (mega = 1000000).
     */
    public DatabaseBuilder cacheSizeInMb(int cacheSizeInMb);

    /**
     * Starts the database. When this method returns, connections to the
     * database can be made.
     * 
     * <p>A start that throws has closed what it opened, its files and its threads, when the
     * exception leaves (bergdb 005-32): the start can be tried again, or the directory
     * removed, at once.</p>
     * 
     * <p>One database at a time has the directory of create() or open() (bergdb 005-63):
     * while another database has it open, in this process or in another, also one that this
     * builder started or one that is closing after stop(), start() throws a
     * StreamIoException whose cause is a bergdb.stream.DirectoryInUseException. Nothing in
     * the directory has been read or changed then, and the database that has it runs on as
     * before (bergdb 015-56). The lock is the operating system's lock on the file bergdb.lock
     * in the directory, which the operating system releases when the process ends, also at
     * a crash: it is never stale, and the file need never be removed. Do not delete
     * bergdb.lock while a database has the directory: a start in another process then makes
     * the file again, locks it and starts, and two databases write the same stream files,
     * which can lose what either writes and damage the stream (bergdb 020-24-08, U8-9).
     * In this process, a start is refused in the same way at the path of a database that
     * has not closed, also when its directory was deleted, moved or replaced since, so that
     * a new database at the path of a deleted one waits until that one has closed
     * (Database.stop(); bergdb 021-20); the start has then made the directory, if it was
     * missing, and nothing else.</p>
     * 
     * <p>A start may write to the stream: it completes a cut tail, as a crash leaves it, and
     * writes created.txt if it is missing. On a full disk a start may therefore be refused,
     * with a StreamIoException, or may work, and the database then fails at the first write
     * that needs room (Database, "Errors"; bergdb 020-24-08, U8-2).</p>
     * 
     * <p>One database at a time has the stream of memory() too (bergdb 015-65): while the
     * database that this builder started on it has not closed, it runs or is closing after
     * stop(), start() throws an IllegalStateException, and that database runs on as before.
     * Call memory() again for a new, empty database. Once that database has closed, start()
     * starts a database on its closed stream: it reads the data, but its first write to the
     * stream, a sync or the background write of a transaction, fails it
     * (DbFailedException).</p>
     * 
     * <p>Release 2026.4 has no encryption (bergdb 020-28; the package's
     * {@linkplain bergdb.pub##encryption Encryption}). A database that an earlier release
     * encrypted, with a crypto key, is refused, and the start has opened, created and written
     * nothing: its created.txt names the key, and start() throws a VersioningStreamException,
     * a StreamFormatException, that says so; without its created.txt, start() reads the stream,
     * whose first bytes read are not those of a BergDB stream, and throws a
     * StreamFormatException that names this case among the likely causes. Its data can be
     * moved with the earlier release, as the release notes of 2026.4 say.</p>
     * 
     * @throws IllegalStateException
     *             If no database was given: neither create(), open() nor memory() was
     *             called; or if the database that this builder started on its stream of
     *             memory() has not closed (bergdb 015-65).
     * @throws DbException
     *             If a functioning database could not be started; among them a
     *             StreamIoException if the directory of create() or open() cannot be
     *             opened or listed (an I/O error, no permission to read it, a path of
     *             create() that is not a directory; bergdb 020-20, 020-24-08), or another
     *             database has it
     *             (the cause a DirectoryInUseException, bergdb 005-63). A read or a write
     *             that fails on the storage during the start, as on a full disk or with a
     *             stream file missing, throws the storage's exception, a StreamIoException,
     *             or a StreamFormatException for a damaged stream (Database, "Errors";
     *             bergdb 020-24-08, U8-2). A StreamFormatException also if the stream is not
     *             a BergDB stream, or is damaged where the start reads it first: the magic
     *             bytes of its last meta block, one of the blocks written at every 200,000
     *             bytes of the stream, so in a database of less than 200 kB its first bytes;
     *             or if an earlier release encrypted it (above). The message names the likely
     *             causes, and the start has written nothing (bergdb 005-33, 005-40, 020-28).
     *             A VersioningStreamException, a StreamFormatException, also if the database
     *             holds an index of BergDB 2026.3 and before: such a database does not start,
     *             and is made again from its data (the package's
     *             {@linkplain bergdb.pub##objects Objects}; bergdb 020-08). And a
     *             VersioningStreamException if a release before 2026.6 wrote the database
     *             (its meta blocks of version 154; bergdb 028-15): this release does not
     *             open it, the message names release 2026.5, and the start, as create() on
     *             its directory, changes no file; its data is read with the release that
     *             wrote the database and put into a new one with this release, as the release
     *             notes say (bergdb 024-26, U26-8; 028-15, 028-30).
     * @throws DatabaseNotCreatedException
     *             If the database's creation did not complete: a crash, as a power loss,
     *             while it was created left a part of it, and no data (bergdb 005-33). The
     *             start has written nothing. To create the database, remove its files, in
     *             its directory the stream's files (*.bergdb) and created.txt, and start
     *             again. A database that holds data never gives this exception.
     * @throws DatabaseMissingException
     *             If the directory of create() or open() held a database and its stream is
     *             missing: it has created.txt, and no stream file (*.bergdb) with a byte;
     *             the files were removed, not restored, or emptied (bergdb 015-01). The
     *             start has opened, created and written nothing. Restore the *.bergdb files
     *             and start again; or, for a new, empty database there, remove created.txt
     *             and the *.bergdb files. Also, for open(), if the directory is missing,
     *             is not a directory, or holds no stream file with a byte (bergdb 015-05);
     *             the start has then created and written nothing.
     */
    public abstract Database start();
}
