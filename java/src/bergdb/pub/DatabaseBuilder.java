package bergdb.pub;

import java.io.IOException;

import bergdb.pub.util.BadCryptoKey;
import bergdb.pub.util.BadReplicaException;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;

/**
 * A DatabaseBuilder is used to create a Database.
 * Use the settings methods (dir, memory, replica, clock, ...) and then 
 * call start() to create and start the database.
 * 
 * @see Database
 * @author Frans Lundberg
 */
public interface DatabaseBuilder {
    
    /**
     * Use the given directory to store the database stream in files. start() opens the
     * directory, and creates it if it does not exist; this method only records it (bergdb
     * 005-66), so a builder that is not started holds nothing. Until 005-66 this method
     * opened it and threw the errors that start() now throws.
     * 
     * <p>One database at a time has the directory (bergdb 005-63): while another database
     * has it open, in this process or in another, also one that this builder started or one
     * that is closing after stop(), start() throws a StreamIoException whose cause is a
     * bergdb.stream.DirectoryInUseException. Nothing in the directory has been read or
     * changed then, and the database that has it runs on as before (bergdb 015-56).</p>
     * 
     * <p>A directory that holds a database has created.txt, written once the database's
     * creation is durable; start() refuses one that has created.txt and no stream file
     * (*.bergdb) with a byte, with a DatabaseMissingException (bergdb 015-01). A directory
     * without created.txt, also an empty or a missing one, gets a new, empty database, as a
     * wrong path or a volume that is not mounted does too. An application that must never
     * create a database there checks, before start(), that created.txt exists in it.</p>
     */
    public DatabaseBuilder dir(String dirname);
    
    /**
     * An in-memory database stream will be used.
     * This option may be suitable for testing.
     */
    public DatabaseBuilder memory();
    
    /**
     * Provide a CryptoKey to use an existing encrypted database, or start a
     * new one using the provided encryption key.
     * 
     * @param cryptoKey  
     *      The crypto key to use or CryptoKey.NULL to not use any encryption.
     */
    public DatabaseBuilder cryptoKey(CryptoKey cryptoKey);
    
    /**
     * Adds a replica to the sets of database replicas.
     * 
     * <p>Experimental, with known faults, and not to be used in production; its API will
     * change in a later release (2026-11-03; bergdb 005-11, and bergdb 016-01, section 3).</p>
     * 
     * <p>Its known faults: a replica is written in plain text, also when the database is
     * encrypted. With reclaim (a finite retain duration), a crash can leave a replica that
     * does not start, or that gives wrong answers at times it claims to have. A replica
     * whose storage fails is dropped without a word, and reclaim's next cut then fails the
     * database. A start without a replica that a crash left ahead of the main, and then one
     * with it, can leave two histories, or a database that does not start. A slow replica
     * slows every write, and a hung one stops them.</p>
     * 
     * <p>start() opens the replica's directory, after the database's own; this method only
     * records it (bergdb 005-66). Until 005-66 it opened it, and a replica added before
     * dir() was dropped.</p>
     * 
     * @param name  Name of the storage replica.
     * @param dir   Directory of the replica database data.
     * @throws IOException  Not thrown since bergdb 005-66: start() throws a
     *      StreamIoException if the directory cannot be opened. Kept so that callers compile.
     */
    public DatabaseBuilder replica(String name, String dir) throws IOException;
    
    /**
     * Sets a non-default database clock. Use this method together with a TestClock to do
     * deterministic testing.
     */
    public DatabaseBuilder clock(Clock clock);
    
    /**
     * Sets the wanted retain duration.
     */
    public DatabaseBuilder retainDuration(Duration duration);
    
    /**
     * Sets the startup distance to a non-default value.
     * A small startup distance can decrease database startup time; while a larger
     * startup distance can improve the overall database performance.
     * For a low-end PC with 0.5 GB of RAM, a value of 5 is reasonable, while a 
     * high-end server may use 50. The default is 50: startup then takes about 0.6 s
     * with 1000-byte values and 1.4 s with 100-byte values, on a fast SSD (measured
     * 2026-10-13). Existing databases keep the startup distance stored in their
     * stream; Database.setStartupDistanceInMb() changes it while the database runs, and
     * the stream keeps the new value (bergdb 005-53). The value should be seen as a proposal, 
     * to the database. If the database considers the value
     * too small or to high, it may clamp it to an internally permitted range.
     * 
     * @param startupDistanceInMb    The startup distance in megabytes (mega = 1000000). 
     *                               Value should be between 5 and 1000.
     */
    public DatabaseBuilder startupDistanceInMb(int startupDistanceInMb);
    
    /**
     * Sets a cache size indicator in MB.
     * A small value will leave more available memory for the rest of the JVM application,
     * while a larger value likely improves database performance.
     * The actual resulting cache size depends on application code, 
     * the operating system and the JVM. 
     * Typical actual cache memory use is in the range [0.5 * cacheSizeInMb, 2.0 * cacheSizeInMb].
     * Since 2026-10-18 the cache size indicator is the budget of the database's cache: when
     * the index nodes and values it holds in memory pass it, it evicts those used least
     * recently, down to three quarters of it. What the database must keep in memory (the
     * nodes changed since its startup position, of the order of the startup distance) is
     * never evicted and may exceed it. The default is a fifth of the JVM's maximum heap.
     * Database.setCacheSizeInMb() changes it while the database runs, for that run (bergdb
     * 005-52).
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
     * @throws DbException
     *             If a functioning database could not be started; among them a
     *             StreamIoException if a directory of dir() or replica() cannot be opened,
     *             or another database has it (the cause a DirectoryInUseException, bergdb
     *             005-63).
     * @throws BadReplicaException
     *             If the replica provided when creating the Database object
     *             is not a valid replica of the database. The database ID in
     *             the stream may be wrong, for example.
     * @throws BadCryptoKey
     *             If the wrong crypto key is used, or none is used with an encrypted
     *             database or a crypto key is used with an unencrypted database. The
     *             start has then written nothing to the database, so it can be started
     *             with the right key (bergdb 005-40; until 2026-10-25, such a start after
     *             a crash could make the database unreadable with the right key too).
     * @throws DatabaseNotCreatedException
     *             If the database's creation did not complete: a crash, as a power loss,
     *             while it was created left a part of it, and no data (bergdb 005-33). The
     *             start has written nothing. To create the database, remove its files, in
     *             its directory the stream's files (*.bergdb) and created.txt, and start
     *             again. A database that holds data never gives this exception.
     * @throws DatabaseMissingException
     *             If the directory of dir() held a database and its stream is missing: it
     *             has created.txt, and no stream file (*.bergdb) with a byte; the files
     *             were removed, not restored, or emptied (bergdb 015-01). The start has
     *             opened, created and written nothing. Restore the *.bergdb files and start
     *             again; or, for a new, empty database there, remove created.txt and the
     *             *.bergdb files. Before, such a start created a new, empty database.
     */
    public abstract Database start();
}
