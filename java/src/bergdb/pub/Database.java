package bergdb.pub;

import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.SyncLevel;

/**
 * <p>A representation of a started BergDB database.</p>
 * 
 * <p>One database at a time has a directory: DatabaseBuilder.start() refuses a second while
 * the first is open (bergdb 005-63).</p>
 * 
 * <p><b>Errors</b> (bergdb 019-10). BergDB assumes a sound environment: correct
 * storage, which returns the bytes written to it, and enough memory and stack for its work.
 * Its checksums and checks find some damage of the stored bytes, not all: they are a best
 * effort, and damage that passes them gives wrong values with no error. Only a cut tail, as
 * after a crash or a power loss, is recovered. BergDB does not try to recover when the
 * environment fails; the database fails instead. That happens on:</p>
 * <ul>
 * <li>an I/O error or corrupt data in the storage;</li>
 * <li>an Error, such as OutOfMemoryError or StackOverflowError, thrown while the database
 * reads, runs a transaction (its Action too) or syncs, or on one of its own threads, such
 * as an index job's;</li>
 * <li>any exception after a transaction's checks, once it changes the database (its
 * Action and the checks come before), as nothing is rolled back.</li>
 * </ul>
 * <p>A failed database does no more work. The call that met the failure throws it: an Error
 * as it is, anything else as a DbFailedException. Every later read and transaction throws a
 * DbFailedException with the first failure as its cause, and nothing more is written.
 * Transactions that a sync() has returned for are safe; stop() and close() still work, and
 * so does sync() while the storage does. The application should then end its process; the
 * next start recovers the database as after a crash: a failed transaction is there if it was
 * written before the failure, and otherwise not. An in-memory database is lost. For
 * OutOfMemoryError, the JVM option -XX:+ExitOnOutOfMemoryError ends the process at once,
 * and that is the advice: while the heap stays full, BergDB cannot promise even to fail
 * cleanly, so a sync() or close() may then wait (bergdb 019-39).</p>
 *
 * <p>Everything else the database throws fails only that call, and the database goes on: a
 * transaction refused by its checks, such as one that is too large, a read whose lookup
 * time has expired (LookupTimeNotAvailableException; see getFirstAvailableLookupTime()), a
 * bad argument. The conversion of a read value to your object is not the database's
 * read: what it throws, an Error too, fails only that call (bergdb 019-40).</p>
 * 
 * <p><b>The files</b> (bergdb 020-24-08). A start recovers a cut tail of the stream, the
 * end that a crash or a power loss did not write, which holds only transactions that no
 * sync() had returned for. It cannot tell such a cut from one that took more: nothing
 * outside the stream records how long the stream was (U8-1). So if the last stream file
 * (*.bergdb, the one with the largest number) is deleted, emptied or cut while the database
 * is stopped, by a backup or sync tool, a script or a hand, the next start works without an
 * error, and the transactions in the lost part are gone, also those that a sync() returned
 * for; the next write goes where the cut is, so the lost file can no longer be put back. A
 * stream file deleted or cut anywhere else is refused by the start, and other damage to the
 * files is refused by the start or fails a read (DbFailedException), or passes the checks
 * (above). The files before a gap in the stream's files, as a power loss can leave among
 * the old files that reclaim's cut deletes, are not the stream: the start deletes them if
 * each one is the database's, by its first meta block, and else refuses, with a
 * StreamIoException that names the file, having deleted and written nothing (bergdb
 * 028-66). So leave the files alone while the database is stopped, as while it runs, and
 * copy, move or restore a stopped database's files all together: the stream's files and
 * created.txt.</p>
 * 
 * <p><b>What a crash keeps</b> (bergdb 020-24-13, U13-3). The transactions are written to
 * the stream one after another, in the order of their commits, each in a record of its own
 * with the index entries that it makes: a put(), a delete(), a WBuilder's execute() and an
 * rw() alike. A crash or a power loss cuts the stream's tail, and the start drops a record
 * that the cut reached: the database then holds a prefix of the transactions, each whole
 * or not at all, and none after one that is missing. A sync() returns when the stream is
 * durable up to its transaction, and so every transaction committed before it, from any
 * connection; Connection.sync() waits for the last transaction of its connection. So an
 * import that syncs after each batch finds after a crash every batch up to the last that a
 * sync() returned for, and goes on after the last batch that it finds.</p>
 * 
 * <p>A power loss must leave a cut tail and no other bytes: the file storage forces each
 * append to the device before the append returns, and relies on a file system that keeps a
 * file's appends in order, as common ones do (bergdb 014-01, section 7; 005-83). A kill of
 * the process or a crash can also leave zeros within the last stream file's length, where
 * the bytes of the last write should be, as APFS (macOS) does (bergdb 033, RB-012): a start
 * leaves a run of zero bytes of at most 8 MB at the end of the last stream file out of the
 * stream, and recovers the stream as a cut tail; the file storage cuts the zeros from the
 * file at its first write, so a start refused before it writes leaves the files as they
 * were. No committed transaction is among such zeros: each committed transaction's record
 * and each valid meta block of the stream ends in the byte 10. A kill during an append on
 * APFS can also leave there the bytes of a file deleted before, such as an older stream
 * file of the database or another database's file (bergdb 035-02, 028-67): each meta block
 * holds its own position and the database's ID, and each transaction's record a check of
 * the ID, its position and its header, so a start takes no meta block or record of another
 * file or place. A tail that is not the stream's own records, such as those bytes, a longer
 * run of zeros that reaches past a transaction's end, or other bytes after the last
 * transaction, as a file system that writes a file's length before its data can leave, is
 * refused before the start writes anything: start() throws a StreamFormatException whose
 * message names the cause and P, the position where the stream's own records end ("The
 * stream's records end at stream position P"), for example "Bad transaction size in db
 * stream, S, spos P. Stream length: L. ..." for zeros (U8-3). To start the
 * database, keep a copy of its files, then cut the stream at P: cut the stream file that
 * holds P to P less the file's first position, which is the number in its name times
 * 100,000 (00000000000300.bergdb begins at 30,000,000), and remove the later stream files,
 * if any. What the stream held from P on is lost.</p>
 * 
 * <p>A full disk fails the database as any I/O error does (U8-4). Nothing inside the
 * database frees space: a delete writes, and reclaim writes the values it keeps before it
 * cuts. Free space outside the database, or copy the stopped database's files to a larger
 * disk, and start it again. A start may write too (DatabaseBuilder.start()), so on a full
 * disk it may be refused. Leave room: with a finite retain duration the stream holds
 * several times the live data (setRetainDuration()).</p>
 * 
 * <p>Interrupts (bergdb 005-46). An interrupt of the calling thread never fails the
 * database. Three calls only wait, and an interrupt ends the wait: sync() throws a
 * DbException, and the transaction stays committed; a Job's join() returns the job's
 * status; and a transaction that waits to run again after a conflict throws a DbException,
 * not run. Every other call ignores an interrupt until it is done. Either way, the
 * thread's interrupt flag is set when the call returns or throws, if it was set before or
 * during the call.</p>
 * 
 * <p>Stop or close each Database that is started, as a file: nothing else stops it (bergdb
 * 005-55). Until it closes, a started database holds its write buffer, 64 KiB to 10 MB of
 * heap as its writes need (about 0.7 MB of heap in all for a small file database), one
 * thread and three open files (a file database; bergdb 026-07; 020-24-10, U10-2;
 * setStartupDistanceInMb()). stop() returns at once; close()
 * waits until the database is closed. Database is
 * AutoCloseable (bergdb 005-59), so a try-with-resources block closes it when the block ends,
 * also when the block throws:</p>
 * <pre>
 * try (Database db = Factory.database().memory().start()) {
 *     db.connection().put("/a.txt", "Hello world!");
 * }
 * </pre>
 * 
 * @author Frans Lundberg
 */
public interface Database extends AutoCloseable {

    /**
     * Returns information about the startup of this database.
     */
    public StartupInfo getStartupInfo();

    /**
     * <p>Stops the database and closes it properly, without waiting (bergdb 005-35): no
     * transaction or read starts after this method, and a transaction whose commit has begun
     * completes. Every transaction that has returned is then written and the files are
     * closed, in the background, typically within a second, also when the program returns
     * from main right after this method. This method returns at once; close() also waits
     * until the database is closed.
     * The background close runs in a thread that a return from main waits for, and
     * System.exit() does not: after stop(), System.exit() can lose transactions that have
     * returned, as a crash does, and so can stop() in a shutdown hook (bergdb 020-24-10,
     * U10-4). Before System.exit(), and in a shutdown hook, call close().
     * Call close() to wait for completion and report a failed flush or storage close
     * (bergdb 005-73, F5).
     * </p>
     *
     * <p>A call that runs in another thread at the stop, and has not begun its commit, is
     * refused: it throws IllegalDbStateException, nothing of it is written, and the database
     * has not failed (bergdb 020-24-03, U3-1). That holds for an rw() whose action runs: the
     * action's next read throws it, or the commit does, and rw() throws it. It holds for a
     * put(), a delete() or a WBuilder's execute() that has not reached its commit, and for
     * a read: get(), exists(), useIndex(), and a scan's iterator at its next read from the
     * database, which hasNext() or next() makes after the values it read before (U3-5). A
     * read that loads from the storage as the storage closes may throw another DbException
     * instead, a StreamIoException; the database has not failed then either. A sync() at a
     * stop: see sync().
     * </p>
     * 
     * <p>Call sync() before stop() when the transactions must be durable when stop()
     * returns: with a file storage, sync() waits until they are forced to the device.
     * This method is OK to call multiple times from multiple unsynchronized threads; only
     * the first call to this method has any effect (idempotent method).
     * </p>
     * 
     * <p>After this method, also once the database has closed, every read and every
     * transaction, through any connection, setRetainDuration(), setStartupDistanceInMb(),
     * deleteIndex() and an IndexBuilder's start() throw IllegalDbStateException and change
     * nothing. The other calls are taken: close(), stop() again, sync() (see sync()),
     * setCacheSizeInMb(), which only sets the value, the getters, which give the last
     * values, connection(), newConnection() and indexJob() (bergdb 020-24-15, U15-3).
     * </p>
     * 
     * <p>stop() or close() must be called once the Database is no longer used, as close() for
     * a file or a socket: nothing else stops it, not even the garbage collector (bergdb
     * 005-55). A Database that is not stopped keeps its storage threads, its open files, its
     * write buffer and its memory until the JVM exits. What it has committed is still
     * written within the buffer time, as after any commit; at the exit of the JVM, what is
     * buffered and not yet written is lost, as in a crash, which the database tolerates.
     * </p>
     * 
     * <p>The write buffer and the buffer time (bergdb 020-24-10, U10-9). A transaction that
     * returns is in the write buffer, 64 KiB to 10 MB of heap as the writes need (bergdb
     * 026-07), and the database's thread writes it to the storage soon after: when 2.5 MB,
     * a quarter of the largest buffer, are buffered, when a sync() waits, or
     * else once the buffer time, 50 ms, has passed, and with a file storage it is durable
     * once written; a busy disk can make that longer. Neither is a setting in this release.
     * A program that ends without stop() or close() loses what is still in the buffer.
     * </p>
     * 
     * <p>Start another database on the same directory only after this one is closed, when
     * close() has returned (bergdb 005-63). Until then, a start there is refused:
     * DatabaseBuilder.start() throws.
     * </p>
     * 
     * <p>Delete, move or replace the directory only after close() has returned, too (bergdb
     * 021-20, from 020-24-10, U10-1). In this process, a start at the directory's path is
     * refused until this database has closed, also when the directory was deleted and made
     * again since. A database whose directory is deleted, moved or replaced while it runs, or
     * after stop() while it closes, fails (DbFailedException, or a StreamIoException of
     * close()), at the latest when it needs its next stream file; what it wrote after the
     * delete is lost with the directory. It checks the directory right before it makes or
     * deletes a stream file, with nothing that waits in between, and again after (bergdb
     * 021-24). A replacement in the short window between the check and the step, usually
     * microseconds, longer if the thread is paused, as by a garbage collection, is not
     * prevented: the step then leaves an empty stream file in the new directory, or, at a
     * cut, deletes the new directory's file of the same name; a start there is refused
     * until the empty file is removed, with an exception that depends on what else is in
     * the directory; the check after the step fails the database if the directory is still
     * replaced. Otherwise it writes nothing into the directory that is then at the path.
     * </p>
     */
    public void stop();
    
    /**
     * <p>Stops the database as stop() does, and waits until it is closed (bergdb 005-59):
     * every transaction that has returned is written, with a file storage forced to the
     * device, the files are closed, and the storage threads have ended; also when stop() or
     * another close() began the close. It waits for a transaction whose commit has begun,
     * not for another call that runs, such as an rw() whose action runs: that call is
     * refused, as stop() says (bergdb 020-24-03, U3-1). After this method, the calls that
     * stop() refuses are refused, and the others are taken, as after stop(); sync() returns,
     * unless the close failed (bergdb 020-24-15, U15-3). It is safe to call it several times,
     * also after stop(), and from different threads. A closed database has released its
     * write buffer, also one closed in the background after stop(): a closed Database that
     * the application still references holds little heap (bergdb 020-24-10, U10-3).
     * </p>
     * 
     * <p>This is AutoCloseable's close(), without its checked exception: a try-with-resources
     * block calls it when the block ends, also when the block throws.
     * A failed final flush or storage close throws StreamIoException, also after stop()
     * or an earlier close() (bergdb 005-73, F5). So does an earlier failure of the storage
     * that no call has reported, such as a failed write of the storage thread while the
     * application made no call (bergdb 019-09): the transactions that were buffered are
     * lost. A close of a database that has failed (a call threw DbFailedException) returns
     * normally, as that failure was reported.
     * </p>
     */
    public void close();

    /**
     * Gets a connection to the database. The returned object is always the same object for one
     * specific thread that calls this method. Two different threads calling this method are
     * guaranteed to get different Connection instances. Each call sets the requested lookup
     * time of the returned Connection to Time.MAX, the latest state (Connection.setLookupTime()).
     * The database holds the calling threads weakly: the connection of a thread that has ended
     * goes once the thread is no longer referenced and the collector has taken it, at a later
     * call of connection() (bergdb 015-60).
     *
     * @throws IllegalStateException
     *             If another thread is in a call of the thread's connection, as for its
     *             setLookupTime(): a connection is used by one thread at a time (Connection,
     *             "Threads"; bergdb 021-22).
     */
    public Connection connection();

    /**
     * Creates and returns a new connection to the database. The returned object is always newly
     * created in this method and is guaranteed not to be returned from subsequent calls to
     * newConnection() or connection(). Its requested lookup time is Time.MAX, the latest state
     * (Connection.setLookupTime()). For a second connection in a thread, such as a reader at
     * another lookup time; a thread's own connection is connection()'s (Connection).
     */
    public Connection newConnection();

    /**
     * Waits until the last committed transaction has been stored durably according to the ordinary
     * durability rules.
     * Durably means that a crash or a power loss keeps it; damage to the files may not: a
     * last stream file that is deleted or cut while the database is stopped loses it without
     * an error ("The files" above; bergdb 020-24-08, U8-1).
     * 
     * @throws DbException
     *             if the database is faulty, or if the thread is interrupted while it waits
     *             (a StreamIoException whose cause is an InterruptedIOException): the
     *             transaction stays committed, the database goes on, and the thread's interrupt
     *             flag is set (bergdb 005-46). Or if the database is stopping or stopped
     *             (stop()) and the transaction is not yet durable: a StreamIoException
     *             ("Storage is closing."), the database has not failed, and close() still
     *             writes the transaction (bergdb 020-24-03, U3-3). If it is durable, this
     *             method returns, also then: after close(), or after stop() once the
     *             database has closed, every transaction is durable, unless the close
     *             failed (bergdb 020-24-10, U10-6).
     * @throws DbFailedException
     *             If the storage has failed: the database fails (see above).
     */
    public void sync();
    
    /**
     * Waits until the last committed transaction has been stored durably according to the
     * specified sync level.
     * 
     * @throws DbException
     *             if the database is faulty, or if the thread is interrupted while it waits,
     *             as for sync().
     * @throws DbFailedException
     *             If the storage has failed: the database fails (see above).
     * @throws IllegalArgumentException
     *             If syncLevel is null (bergdb 020-25).
     */
    public void sync(SyncLevel syncLevel);

    /**
     * <p>Returns the current time of the database clock.
     * The returned time is guaranteed to be less than
     * the transaction time of any currently executing transaction (if any transaction is executing)
     * and less than the transaction time of any future transaction.
     * The returned time is also guaranteed to be greater than or equal to the transaction 
     * time of the last completed transaction.</p>
     *
     * <p>These promises are for this started database: a time that currentTime() returned
     * holds for the session that returned it. After a restart, with a clock that stands
     * still (a test clock) or was set back, a transaction can get a time at or before a time
     * that currentTime() returned before the restart, and a read at that time then sees that
     * transaction (bergdb 018-04, Q5; 028-74). A time that holds across restarts is the time
     * of a transaction that was committed and is durable (Transaction.getTime(), after
     * Transaction.sync()): every later transaction, also after a restart, gets a later
     * time.</p>
     */
    public Time currentTime();

    /**
     * Returns the minimum duration for which data should be available for historic lookups:
     * the retain duration kept in the stream, as the last setRetainDuration() set it, or
     * Duration.MAX (forever) if it was never called.
     */
    public Duration getRetainDuration();

    /**
     * <p>
     * Sets the retain duration of the database. The retain duration is the amount of time that
     * historic data states should stay available for lookup operations. A new database keeps
     * old states forever (Duration.MAX) until this method is called.
     * </p>
     * 
     * <p>
     * The value is kept in the stream (bergdb 015-87): the call commits a small transaction
     * of the database's own with it, and a start reads it, so a restart keeps the value; it
     * need not, and cannot, be given to the DatabaseBuilder. The new value is in force when
     * the method returns. A call with the value in force writes nothing. A setting that
     * changes the stream's bytes, as this one does, is kept in the stream. Like any
     * transaction, it is written to storage soon after the method returns, and a crash
     * before it is durable (sync()) can undo it: the restart then has the value before the
     * call, and reclaim cuts by that value (bergdb 020-24-06, U6-3).
     * </p>
     * 
     * <p>
     * If the retain duration is increased, the actual duration available for lookups will increase
     * until it equals or exceeds the retain duration set in this method. Use
     * getFirstAvailableLookupTime() to see the currently available time span for lookups.
     * </p>
     * 
     * <p>
     * A finite duration makes the database reclaim stream space: it rewrites live values that
     * are stored in the front of the stream, and then cuts the front. This costs writes and
     * space. Measured with the default settings (2026-10-13, see bergdb 011-04, "Level 3
     * cost"): when the duration is short, the write efficiency (user bytes divided by stream
     * bytes written) is 23 to 38 percent lower than without reclaim, and the stream kept is
     * several times the data accessible within the duration (store efficiency 0.09 to 0.75,
     * depending on value size and update pattern). The cost is lower for a long duration.
     * </p>
     *
     * <p>
     * Reclaim works in iterations, not as the duration passes (bergdb 011-04): one begins at
     * a commit when the stream has grown by more than twice the startup distance
     * (getStartupDistanceInMb()) since the last one began, and a quarter of the duration has
     * passed since then. At the commits that follow, it rewrites the live values stored
     * before its cut point, a part at each, at most a quarter of what the stream has grown
     * by since it began. When it has rewritten them all, its end is older than the retain
     * duration and the startup section has moved past it, the stream is cut at its cut point
     * and getFirstAvailableLookupTime() moves; until then every earlier state stays
     * readable. So however short the duration, nothing is cut before the stream has grown by
     * about four times the startup distance in a small database, after about 200 MB of puts
     * with the default 50 MB and 20 to 30 MB with 5 MB (measured, bergdb 020-24-03, U3-9),
     * and by more in a database with much live data, which the first iteration rewrites. A
     * smaller startup distance cuts sooner. A database that is not written to does none of
     * this by itself; maintain() lets the application ask for it (bergdb 024-32).
     * </p>
     *
     * <p>
     * What stays on disk follows from that (bergdb 020-24-06, U6-2): the stream from the
     * last cut point on, which is where the iteration before the cut one began. That is
     * about the stream written within the retain duration plus that of one or two
     * iterations, and an iteration spans at least twice the startup distance, the stream of a
     * quarter of the duration, and four times the live data, which it rewrites at a quarter
     * of the stream's growth. Measured with small values and 3 s retained: 22 to 31 MB at a
     * startup distance of 5 MB and 3.5 MB of stream a second; about 100 MB at 50 MB and that
     * rate; 200 to 340 MB at 50 MB and 35 MB a second; 750 to 1,100 MB with a million live
     * keys (92 MB of puts). So the retain duration bounds what stays readable, not the size
     * on disk, and a smaller startup distance keeps less.
     * </p>
     *
     * <p>
     * Use Duration.MAX to keep old states available forever. Note, that this will increase the
     * database storage space indefinitely even when data is deleted from the database. This could
     * be a valid setting however. The retain duration can be decreased later, also while the
     * database is running.
     * </p>
     * 
     * @param duration
     *            The duration to retain historic data states available for lookup operations.
     * @throws IllegalArgumentException  If duration is null or shorter than one second.
     * @throws IllegalDbStateException  If the database is stopping or stopped, as a
     *     transaction does; the retain duration is then unchanged.
     * @throws DbFailedException  If the database has failed, as a transaction does; the
     *     retain duration is then unchanged.
     */
    public void setRetainDuration(Duration duration);

    /**
     * <p>Returns the startup distance setting in MB (mega = 1000000, rounded): the target
     * size of the startup section, not the section's present length.</p>
     */
    public int getStartupDistanceInMb();

    /**
     * <p>Sets the startup distance, the target size of the startup section: the part of the
     * stream that a start reads (bergdb 005-49), while the database runs (bergdb 005-53).
     * A new database has 50 MB. This method is the only way to set another: call it right
     * after start(), also the start that creates the database; DatabaseBuilder has no method
     * for it since release 2026.6 (bergdb 028-13). The value is clamped to 5 to 1000 MB, and
     * getStartupDistanceInMb() then gives the value set. The new setting is in force when
     * the method returns. It is written to the stream
     * with a small transaction of the database's own (a KV of 4 bytes), so a restart keeps
     * it, as it keeps the setting the database was created with; a call with the setting in
     * force writes nothing. A setting that changes the stream's bytes, as this one does, is
     * kept in the stream; one that does not, as the cache size, lasts for the run. Like any
     * transaction, it is written to storage soon after the method returns, and a crash
     * before it is durable (sync()) can undo it: the restart then has the setting before
     * the call (bergdb 020-24-06, U6-3).</p>
     *
     * <p>The startup section follows the setting as transactions are committed: after a
     * decrease, each commit writes more of the index, in proportion to its size, and no
     * commit writes the whole of it; the section is near the new setting after stream of
     * about 1.4 times the index changed since the startup position (bergdb 007-06, 007-07).
     * Without commits it does not move. After an increase, commits write less of the index
     * until the section has grown to the setting. A larger distance writes fewer bytes a put
     * and starts more slowly. With a finite retain duration it also paces reclaim: a larger
     * distance cuts later and keeps more on disk (setRetainDuration(); bergdb 020-24-06,
     * U6-2).</p>
     *
     * <p>A small startup distance can decrease database startup time, while a larger
     * startup distance can improve the overall database performance. For a low-end PC with
     * 0.5 GB of RAM, a value of 5 is reasonable, while a database of 10 million keys or more
     * may use 200 to 1000 (bergdb 005-38). At the default, 50, startup took about 0.6 s with
     * 100,000 keys of 1000-byte values and 1.4 s with 1 million keys of 100-byte values,
     * written by single puts, with the stream in the operating system's file cache, on a
     * fast SSD (measured 2026-10-13, before eviction; bergdb 011-04). A start's time grows
     * with the transactions it reruns and the index nodes it reads, so with more keys: with
     * 10 to 50 million keys of small values, a warm start takes about 62 to 104 ms a
     * megabyte of its startup section, 3 to 5 s at 50 (bergdb 006-19, 007-05); measure a
     * start with your own data. A start reruns each transaction of its startup section
     * whole, so a transaction larger than the startup distance makes every start read all
     * of it, also after small transactions after it, until about twice the startup distance
     * has been written after it: at a startup distance of 5, after one transaction of 200 MB
     * a start took 2.7 to 3.1 s, and 0.07 s once 10 MB more had been written (bergdb
     * 020-24-13, U13-7).</p>
     *
     * <p>The startup distance, not the cache budget (DatabaseBuilder.cacheSizeInMb()), sets
     * the heap that a database needs. What the database must keep in memory, the index
     * nodes changed since its startup position, which eviction never takes, is about 2 to 3
     * times the startup distance of heap (bergdb 006-19), and a start needs about twice the
     * startup distance of heap above what the running database needs, whatever the budget
     * (bergdb 019-45). A new user's catalogue of 2 million objects, 4.9 GB of stream, with a
     * budget of 4 MB (bergdb 020-24-04, U4-2): at the default 50, the heap held 110 to 160 MB
     * after a start; the start failed with an OutOfMemoryError in a heap of 256 MB and ran in
     * 384 MB. At 5, it held 21 to 42 MB and ran in 96 MB. So for a small heap set a small
     * startup distance; the budget comes on top of what must be kept. A start reads the
     * stream's setting, so a database that is to run in a small heap gets its small setting
     * right after the start that creates it, and keeps it.</p>
     *
     * <p>Every started database also holds its write buffer, from its start until it closes
     * (stop()): 64 KiB at the start, whatever its data, startup distance and budget. The
     * buffer grows with the write rate, up to 10 MB, when writes come faster than the
     * storage takes them, and shrinks back to 64 KiB after 2 seconds with nothing to write
     * (bergdb 026-07). So a small started database holds about 0.7 MB of heap (a file
     * database; a memory database about 1.7 MB, its stream included), one thread and three
     * open files, and up to 10 MB more while it writes fast. Until release 2026.6 the buffer
     * was 10 MB from the start: a small file database held about 11 MB of heap, and 48 small
     * ones filled a heap of 512 MB (bergdb 020-24-10, U10-2). A closed database releases its
     * buffer (close()).</p>
     *
     * @param startupDistanceInMb  The startup distance in megabytes (mega = 1000000),
     *     clamped to 5 to 1000.
     * @throws IllegalDbStateException  If the database is stopping or stopped, as a
     *     transaction does; the setting is then unchanged.
     * @throws DbFailedException  If the database has failed, as a transaction does.
     */
    public void setStartupDistanceInMb(int startupDistanceInMb);

    /**
     * <p>Returns the cache size setting in MB (mega = 1000000, rounded): the budget of the
     * database's cache, not the memory the cache holds now.</p>
     */
    public int getCacheSizeInMb();

    /**
     * <p>Sets the cache size indicator in MB, the budget of the database's cache, while the
     * database runs (bergdb 005-52), as DatabaseBuilder.cacheSizeInMb() does at start,
     * clamped the same way, to 4 to 100,000 MB. The new budget is in force when the method
     * returns. After a decrease the database evicts what it holds above the budget in
     * batches of at most 2 ms, which this call and the database's commits and reads start,
     * until the memory it holds is at most the budget, also if no call follows; reads may
     * wait for a batch meanwhile, at most 2 ms each. A commit's own reads of the keys it
     * writes do not wait, and the commit runs one batch at its end (bergdb 005-52); the
     * memory held may rise by what those reads load until then. What the database must keep
     * in memory (the nodes changed since its startup position) is never evicted and may
     * exceed the budget; a budget below it makes reads go at the pace of eviction while
     * anything is written (DatabaseBuilder.cacheSizeInMb(); bergdb 020-24-04, U4-1). After an
     * increase, the cache grows as data is read.</p>
     *
     * <p>The setting is for this run only: it changes no byte of the stream, so it is not
     * kept there, and a restart takes the builder's value, or its default, a fifth of the
     * JVM's maximum heap. A setting that changes the stream's bytes, as the startup distance,
     * is kept in the stream; one that does not lasts for the run. After stop() the method
     * only sets the value, which getCacheSizeInMb() then gives; it evicts nothing.</p>
     *
     * @param cacheSizeInMb  The cache size indicator in megabytes (mega = 1000000).
     */
    public void setCacheSizeInMb(int cacheSizeInMb);

    /**
     * <p>
     * Returns the first (earliest) lookup time that is currently available for making a lookup (get
     * operation).
     * </p>
     *
     * <p>
     * Before reclaim's first cut, so always in a database whose retain duration was never
     * finite, it is Time.units(0), 1970-01-01 00:00:00 UTC: every state is readable (bergdb
     * 020-24-06, U6-7). It moves only when reclaim decides a cut, which it does at a commit
     * when the retain duration is finite (setRetainDuration() says when): without commits it
     * stays, also over a restart, and states older than the retain duration stay readable
     * meanwhile.
     * </p>
     *
     * <p>
     * Within a run, the time only moves forward. A restart after a crash can give an earlier
     * time (bergdb 020-24-06, U6-4): reclaim moves the time when it decides a cut, and cuts
     * the stream only when the record of that decision is durable; a crash before then can
     * lose that record, and the stream is then as it was: the restart gives the time before
     * the decision, and every state from it is readable and right. A restart after stop() or
     * close() keeps the time.
     * </p>
     *
     * <p>
     * A read at an earlier lookup time throws LookupTimeNotAvailableException. The time can
     * move while a read is running: a read that was accepted may then fail with the same
     * exception, if it needs data that was removed; the database and other reads are not
     * affected. The database guarantees that lookups work for
     * every time in [now - retain duration, now] when the time is moved; a read that runs longer
     * than that may expire. Retry such a read with a later lookup time.
     * </p>
     */
    public Time getFirstAvailableLookupTime();
    
    /**
     * <p>Gives the database time for its maintenance now, within a budget (bergdb 031-04): the
     * application's call for the database's maintenance while it is idle. Calling it is
     * optional: the maintenance goes on while the application uses the database, at its
     * commits, whether this method is called or not. In Frans Lundberg's words (2026-11-10):
     * "maintenance should be performed while doing other operations on the database, so the
     * user explicitly calling maintain() should be optional, not a requirement on the user
     * that she must call maintain."</p>
     * 
     * <p>What it is for: a database that is not used does no work by itself, so with a
     * finite retain duration (setRetainDuration()) the stream space of deleted and
     * overwritten data comes back only as the application commits more. An application that
     * has deleted much and then writes little or nothing can call this method when it is
     * idle, to have the space back without writes of its own. The calls rewrite the live
     * data once, in parts, and the space comes back once the retain duration has passed
     * since that pass ended: a pass takes about getStreamSize() divided by the budget's bytes
     * in calls. Calls after that do little or nothing until the application writes again.
     * With the retain duration forever (the default) there is nothing to do.</p>
     * 
     * <p>The budget is an indication of the work allowed in the call, in cost units: a unit
     * is about the work of writing 1 kB to the stream. It is clamped to 100 to 100,000. The
     * database may use less than the budget, or none, depending on its state, and may go
     * past it by a small part's work. How the cost is counted may change between releases.
     * The work runs in parts, each a transaction of the database's own, with its own time and
     * one record, as a commit has (bergdb 031-06): a commit waits for the part that runs, and
     * reads go on.</p>
     * 
     * @param budget  The work allowed in this call, in cost units of about 1 kB written.
     * @throws IllegalDbStateException  If the database is stopping or stopped, as a
     *     transaction does.
     * @throws DbFailedException  If the database has failed, as a transaction does.
     * @throws bergdb.pub.util.DbException  If the database takes no more transactions (its
     *     top node ordinals or its times are used up), as a transaction is refused; nothing
     *     more is written then. Or if the thread is interrupted during a sync.
     */
    public void maintain(int budget);
    
    /**
     * The size of the stream kept, in bytes: from the first position that reclaim has not
     * cut to the stream's end (bergdb 031-04). Exact, and free to call. The storage may hold
     * a little more (a file storage drops whole files). With a finite retain duration it
     * holds the live data, the states that the duration keeps readable, and what reclaim
     * has not yet given back; in a database not written to for longer than the retain
     * duration, what it holds beyond the live data is what maintain() can give back.
     */
    public long getStreamSize();

    /**
     * A builder of a user index of the name (bergdb 020-10, section 3.1; see IndexBuilder).
     * Whether an index of the name exists is checked at the builder's start(), not here.
     * 
     * @param indexName  The index's name: 1 to 255 UTF-8 bytes, without '/', whitespace
     *     (Character.isWhitespace) or a lone surrogate. "primary" is a name like any other.
     * @throws IllegalArgumentException  If 'indexName' is not such a name.
     */
    public IndexBuilder indexBuilder(String indexName);

    /**
     * Deletes the index in one transaction: when this returns, the index is gone at every
     * later lookup time and its name is free; its entries are removed in the background. A
     * build of the index ends, FAILED with the reason "deleted": its job's join() throws
     * IndexBuildException. A scan at a lookup time when the index was active still works,
     * until reclaim's cut passes that time. Like any transaction, the deletion is written to
     * storage soon after this returns, and a crash before it is durable (sync()) can undo it:
     * the index is then there again, as before the call.
     * 
     * @throws NoSuchIndexException  If there is no index of the name.
     * @throws bergdb.pub.util.DbException  If the deletion's transaction is refused; then
     *     nothing changed.
     */
    public void deleteIndex(String indexName);
    
    /**
     * The job of the index's build in this process: the one IndexBuilder.start() returned,
     * or the one a start resumed; for an index that was active at the start, a job whose
     * status is ACTIVE with count 0, which join() returns at once. If the build failed in
     * this process, the job's join() throws an IndexBuildException each time it is called,
     * as on the job that start() returned, and its getStatus() gives FAILED (Job.join()).
     * 
     * @throws NoSuchIndexException  If there is no index of the name now.
     */
    public Job indexJob(String indexName);
}
