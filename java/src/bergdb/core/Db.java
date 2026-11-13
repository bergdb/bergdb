package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.InterruptedIOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Set;
import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.NodeVisitor;
import bergdb.dag.PutData;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.BadMagicBytes;
import bergdb.storage.BufferedStream;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamException;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.storage.VersioningStreamException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.ReadBelowFirstPosException;
import bergdb.stream.SalsaStream;

/**
 * <p><b>The Core API</b> (bergdb 020-27, Q1; Frans, 2026-11-09). The Pub API (bergdb.pub and
 * bergdb.pub.util) is BergDB's stable, default and preferred API. The Core API is for when
 * low-level control or the most performance is really needed. It is less stable: it may
 * change faster between releases. It is less safe, and its writes can break the Pub API's
 * data (see "Keys and the layers above" below; bergdb 020-22). It is mostly the layer that
 * the Pub API is built on. The Core API is: this class, Db; DbBuilder, but for its members
 * for tests; Trans.Builder, and Trans as a transaction to execute with its outputs tt, tpos,
 * lastPos and nextPos; GetData; GetMany and its stop conditions; Kvt;
 * StoredTrans as getTrans() gives it; StartInfo; the key conversions Keys.toSegments() and
 * Keys.toBytes(); FileStream and MemoryStream as a stream for DbBuilder; and the exceptions
 * that their Javadoc names. Everything else that is reachable from them is internal, whatever
 * is public, and may change without notice: among others Db.internal() and Db.Internal,
 * Db.ExecuteData, Db.TestHooks, TestNodeSize, Db.StartParams and the listeners, lookupTime(),
 * checkNodes(), the members that their Javadoc calls internal or for tests, Trans's other
 * fields, GetMany.Chain, and the stream classes beyond making a stream.</p>
 * 
 * <p>An object of this class provides access to the data in the database. This
 * class is the main class of the internal low-level database implementation.
 * It should not be used directly by users unless they really 
 * need the highest possible performance or some feature not exposed by 
 * the higher level API.
 * This class implements the <i>Core Data API</i>, see below.</p>
 * 
 * <p>The <i>Core Data API</i> consists of the following methods of Db:
 * </p>
 * <ul>
 * <li>getOne()</li>
 * <li>getMany()</li>
 * <li>getTrans()</li>
 * <li>execute()</li>
 * </ul>
 * 
 * <p>These methods are the only ones that are called by the consumer of the 
 * core layer to read and write data.
 * This API form a narrow waist with a large code base under it and a large code
 * base above it. These methods are believed to be feature complete in the
 * sense that all features we want from the database can be implemented on top
 * of them. Functionality that can be provided by using the Core API,
 * should not be offered by this class.</p>
 * 
 * <p><b>Opening a database</b> (bergdb 020-24-09, U9-6). A Db runs on one stream, the
 * AppendOnlyStream that DbBuilder.mainStream() takes: for a database in a directory, a
 * bergdb.stream.FileStream on the directory, the stream of the Pub API's databases; for one in
 * memory, a bergdb.stream.MemoryStream. Their constructors are all that a Db's user calls of
 * them: the Db reads and appends through AppendOnlyStream, and its stop() and close(), and a
 * start that throws, close the stream, so that the application does not close it (only if
 * DbBuilder.build() throws, before a Db is made, does the application close the stream with
 * its close()). FileStream's constructor throws IOException, a DirectoryInUseException for a
 * directory that another stream has open. The builder's defaults: the system clock
 * (currentTime()), a cache budget of 200 MB and a startup distance of 50 MB; of its other
 * methods, id() and createdTxt() are the Pub API's, the rest for tests. The maximum node size,
 * the most klongs of a node of the index, is 30 for every database, by this API and the Pub
 * API, with no method to set it (bergdb 026-08): the stream keeps it, and a start refuses a
 * database of another size, as BergDB's own tests make at 8, 14 and 62. An example with keys
 * and values of bytes, which writes, reads and closes:</p>
 * <pre>{@code
 * try (Db db = Db.builder().mainStream(new FileStream(new File("mydb"))).start()) {
 *     byte[] key = {0x10, 0x20};
 *     Trans t = db.trans().put(key, new byte[] {1, 2, 3}).build();
 *     db.execute(t);                       // committed, at the time t.tt
 *     db.sync(SyncLevel.ORDINARY);         // durable
 *     byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData());
 *     GetMany g = db.newGetMany();         // every KV of the latest state, in key order
 *     db.getMany(g);
 *     for (Kvt kvt : g.result) {
 *         byte[] k = Keys.toBytes(kvt.key);
 *         byte[] v = kvt.value;
 *     }
 * }
 * }</pre>
 * 
 * <p><b>Keys and values</b> (bergdb 020-24-09, U9-5). A key is an array of bytes, its bkey
 * (doc-files/key-encoding.md), which the calls take and give as segments:
 * Keys.toSegments(byte[]) makes them, and Keys.toBytes(long[]) gives the bytes back, as of a
 * Kvt's key. Any bytes make a key, the empty array too, which is a key as any other (only a
 * String key, Keys.toBytes(String), is never empty). getMany() gives the keys in the unsigned
 * order of their bytes, as java.util.Arrays.compareUnsigned(byte[], byte[]) orders them: a key
 * comes before its extensions, so that 61 &lt; 61 00 &lt; 61 00 00 &lt; 61 01 &lt; 61 61 &lt;
 * 62; the empty key is first, and FF FF comes after FF. A key has at most 111 bytes ("Limits"
 * below; bergdb 024-17, L2): a key is stored as a path of key nodes, a level for each 7 bytes,
 * so that a key costs memory, stream bytes and time in proportion to its length, many times
 * what a value of that length costs (until release 2026.5 a key had no maximum length, and a
 * commit of a key of 1 MB after one of 100 kB with the same start took 2.6 to 5.8 s; bergdb
 * 021-16, Q1). The keys that share their first j
 * segments, their first 7j bytes, share a segment tree, a tree of key nodes, and a key of
 * exactly 7, 14 or 21 bytes ends with an empty segment (Keys.toSegments). So a prefix of 7,
 * 14 or 21 bytes that only one key has, the whole key included when its length is exactly
 * that, is a key node for that key alone: about 226 bytes of heap when in memory, where a KV
 * with an empty value whose key shares its prefixes costs about 130 in all. A random key of
 * L bytes, such as a UUID, pays it L / 7 times, rounded down (5 for 36 bytes), and one byte
 * more or less of a fixed-width key can add or save a node a key. With noEvict() and keys
 * put in key order, the heap above the empty database's is at most about 131 K + 230 T
 * bytes and the values' byte arrays, K the KVs and T the segment trees beyond the first
 * segment's; in random key order K's constant is about 181 (bergdb 024-08, sections 5 and
 * 7). With eviction the heap stays near the budget whatever the keys,
 * and those nodes cost stream bytes and node reads instead (024-08, section 8). Keep keys
 * short, put large data in values, and let keys that are written together share their
 * start. A value is an array of bytes, the empty array too, which is a value, not a delete;
 * Trans.Builder.delete() removes a key's value. A put of a null value is refused with
 * IllegalArgumentException. A value has at most 8 MiB, and the keys and values of one
 * transaction at most 32 MiB ("Limits" below).</p>
 * 
 * <p><b>Threads</b> (bergdb 020-24-09, U9-7). A Db is for any number of threads at once:
 * execute(), getOne(), getMany(), getTrans(), sync() and the settings may be called from
 * several threads, with no lock of the application's. Transactions run one at a time, each
 * whole; reads run in parallel with each other and with a transaction. A read gives the state
 * at its actual lookup time (GetData.actualLookupTime, GetMany.actualLookupTime): the lookup
 * time asked for, or the time of the last committed transaction if that is earlier, so that
 * Long.MAX_VALUE gives the latest state. That state holds every transaction with a time at or
 * before it and nothing of a later one, never a part of a transaction, and no transaction that
 * runs or comes later has a time at or before it: a read at a time that currentTime() or a
 * read's actual lookup time gave reads the same state whenever it runs, until reclaim cuts it
 * (getFirstAvailableLookupTime()). A GetData, a GetMany and a Trans.Builder are for one thread
 * at a time, so that each thread makes its own (newGetData(), newGetMany(), trans()); a GetData
 * may be used again for the thread's next get, a GetMany is for one call (GetMany).</p>
 * 
 * <p><b>Optimistic transactions</b> (the STM; bergdb 020-24-09, U9-7). A transaction that
 * writes what it computed from its reads, such as a counter's increment, and must not lose
 * another thread's write, gives its read time and the keys it read. execute() then refuses it
 * with RerunException, and changes nothing, if a transaction with a later time than the read
 * time wrote one of those keys; the application reads again and retries:</p>
 * <pre>{@code
 * while (true) {
 *     long t = db.currentTime();              // the read time
 *     byte[] old = db.getOne(t, Keys.toSegments(key), db.newGetData());
 *     Trans.Builder b = db.trans().lookupTime(t).keyRead(Keys.toSegments(key));
 *     b.put(key, increment(old));
 *     try {
 *         db.execute(b.build());
 *         break;
 *     } catch (RerunException e) {
 *         // Another transaction wrote the key after t: read again.
 *     }
 * }
 * }</pre>
 * <p>The read time is Trans.Builder.lookupTime(), Long.MAX_VALUE by default, which checks
 * nothing; give a time that currentTime() or a read's actual lookup time gave. keyRead() adds a
 * key read, with a value or without, and addReadHash() and addReadHashes() a key's hash
 * (Keys.hash()): a put or a delete of the key by a transaction with a later time is a
 * conflict. addVirtualWriteHash() adds a hash that the transaction counts as written, with no
 * key, so that transactions that share no key can still conflict on it, as the Pub API's index
 * builds do with a hash of their directory. Keys are compared by their hashes: a write of
 * another key with the same hash gives a rerun that was not needed, never a missed one. A
 * scan's range is not covered: a key written into the range after the read time is a
 * conflict only if the transaction read that key or a hash that the writer wrote. The
 * database keeps the hashes of the last 96,000 to 128,000 key writes, in memory, since its
 * start: a read time older than they cover, or before the start's last recovered transaction,
 * gives RerunException too, whatever was written; read again at a new time.</p>
 * 
 * <p><b>Keys and the layers above</b> (bergdb 020-22; 010-01, P12). The Core takes any key
 * and knows nothing of the layers above it. A database of the Pub API (bergdb.pub) keeps its
 * data in the Core under keys of its own, and the Core does not stop another writer there: a
 * write through Db can break the Pub API's data, as an edit of the database's files can. In a
 * database that the Pub API uses, a key is of one of three kinds, by its first bytes (its
 * bkey, doc-files/key-encoding.md):</p>
 * <ul>
 * <li><b>Your keys</b>: every key that does not start with the bytes 01 66, 01 2f or 01 25,
 * the bkeys of "/d", "/-" and "/#": a key whose first byte is not 01, or a String key such
 * as "/k1". BergDB never reads them for their meaning or changes them, in this release or a
 * later one: the Core keeps them as any key (reclaim copies a live value forward, as it copies
 * every value).</li>
 * <li><b>The Pub API's keys</b>: the bkey of the ikey of a Pub key, such as "/da/-b" for
 * "/a/b". A put or a delete there is allowed: the Pub API's reads check what they read. But
 * only the Pub API's own writes keep its indexes. A put at an object key (no suffix, or
 * ".obj") of a directory that has an index, building or active, can leave the value out of
 * the index's scans until the key is written again through the Pub API (a put of its own
 * bytes will do), or the index is deleted and created again: write such keys before the index
 * is created, or make it again after. (A put that keeps what the index takes from the value,
 * the fields of its levels, changes nothing in the index.) A delete there leaves an entry
 * that scans skip. Any other key that starts with "/d" or "/-" is reserved.</li>
 * <li><b>BergDB's keys</b>: every key that starts with "/#", among them the internal prefix
 * "/#i/" (DbConstants.INTERNAL_PREFIX): reclaim's state and the Pub API's index definitions,
 * entries and markers. Do not write them. Data there that does not parse is refused with
 * InternalDataException, at a start or at the read that meets it. Data that parses but that
 * BergDB did not write makes values missing from an index's scans, or an index disappear.
 * Of them, the keys that the Core writes itself are refused (below).</li>
 * </ul>
 * <p><b>The Core's own keys are refused</b> (bergdb 024-37; 010-04, R5: the Core API never
 * destroys the key-value store). The key "/#i/-dummy" (the bkey 01 25 6b 01 2f 66 77 6f 6f
 * 7b), and reclaim's directory "/#i/dreclaim/" with every key under it, are written by the
 * Core alone. A start reads them, and a value there that the Core did not write could make
 * a database that never starts again (until release 2026.5 seven bytes put at
 * "/#i/dreclaim/-settings.txt" did). So a caller's put or delete at one of them is refused
 * before anything is written, and the database goes on: by the Trans.Builder call that
 * takes the key, with IllegalArgumentException, which spoils the builder; and by execute(),
 * with a DbException, for a key that a key transformation gives and for the KVs of the
 * internal calls Trans.Builder.putLongKey() and deleteLongKey(). The Pub API's keys under
 * "/#i/" (those that start with "/#i/di") are not refused: the Pub API writes them through
 * Db. A read of the Core's keys is allowed.</p>
 * <p>The Core writes BergDB's keys itself, also in a database that the Pub API never opens
 * (bergdb 020-24-09, U9-4). A new database has none. setStartupDistance() puts a value of 200
 * kB at "/#i/-dummy" (the bytes 01 25 6b 01 2f 66 77 6f 6f 7b), which stays live, so that
 * reclaim copies it forward as any live value; setRetainDuration() and
 * setReclaimInternalFraction() put reclaim's settings at "/#i/dreclaim/-settings.txt"; and
 * reclaim, when it runs, keeps its state under "/#i/dreclaim/", as maintain() its filler
 * "/#i/dreclaim/-fill.txt", deleted at once. getMany() returns these keys
 * as any other, getTrans() lists them, getTransactionCount() counts their transactions and
 * getKvCount() their KVs. So in every database, used by the Pub API or not, a key whose bytes
 * start with 01 25, the bkey of "/#", is BergDB's: do not write it, and to read only the other
 * keys, skip those, with a StopCondition that returns CONTINUE for a key that starts with 01
 * 25 (Keys.toBytes() of the Kvt's key), or with two scans, one that stops before 01 25 and one
 * from 01 26.</p>
 * <p>A scan of an index never returns a value that does not match its query, whatever was
 * written through Db: it checks each value against the index (bergdb 020-10, section 3.4).
 * Write through Db while no Database runs on the stream: the Db under a running Database is
 * not API, and BergDB reads some of its keys only at a start (the index manager its index
 * definitions), so that such a Db's writes of BergDB's keys are seen only in part until the
 * next start.</p>
 * 
 * <p><b>Limits</b> (bergdb 024-17, section 6; decided by Frans on 2026-11-11). A transaction,
 * its keys and its values have fixed limits, the same for every database and node size, and
 * checked before the transaction's go point: a transaction over one is refused, nothing of it
 * is written, and the database goes on. They are constants of the release, not settings: a
 * later release may raise them, never lower them.</p>
 * <ul>
 * <li><b>A key</b> has at most MAX_KEY_BYTES = 111 bytes as stored, its bkey: 16 segments of 7
 * bytes. About 100 characters as a rule of thumb: ASCII letters and digits are one byte each,
 * letters such as å, ä and ö two (UTF-8), and each "/" of a Pub key two (its ikey has a byte
 * for each part). A longer key is refused by the Trans.Builder call that takes it, with an
 * IllegalArgumentException, which spoils the builder (Trans.Builder); a key that a key
 * transformation makes longer, by execute(), with a DbException (L2). A key fits if its
 * bytes, key.length of a byte[] key or the UTF-8 of a String key, are at most
 * MAX_KEY_BYTES: check that before the call, no method is needed (bergdb 026-02, option E;
 * bergdb.pub.Limits counts a Pub key, which has a byte more for each part).</li>
 * <li><b>A value</b> has at most MAX_VALUE_BYTES = 8 MiB, 8,388,608 bytes, refused by the
 * Trans.Builder call that takes it with an IllegalArgumentException (L4). A value
 * transformation's result over it is refused by execute(), with a DbException, as an
 * exception of the transformation is (ValueTransformation; bergdb 026-06).</li>
 * <li><b>A transaction</b> has at most MAX_OPERATIONS = 500 operations, the KVs it puts or
 * deletes, one a key (Trans.Builder.build()) (L1): a delete counts whether its key has a value
 * or not, though one of a key without a value stores nothing (getTrans()); at most MAX_TRANS_KEY_BYTES = 56 KiB,
 * 57,344 bytes, of keys (L3); and at most MAX_TRANS_BYTES = 32 MiB of keys and values (L5).
 * execute() refuses one over them with a DbException. L3 binds only on BergDB's own keys,
 * which may be longer than a user's (the Pub API's index entries): 500 keys of 111 bytes are
 * 55,500 bytes.</li>
 * </ul>
 * <p>Larger work is split: transactions of at most 500 operations, with a marker key written
 * in the last one, which readers look at first; a larger value in chunks under keys of their
 * own and a manifest written last (bergdb 024-17, 6.7). The limits bound what a transaction
 * can make dirty in the index, so that its record fits the record limit, 2^31 - 9 bytes, at
 * every node size (024-17, section 5; the Lean model's Limits.release). The checks of the
 * record's size and of the index nodes a transaction can make dirty (bergdb 005-17, 005-31)
 * stay, as refusals before the go point. A transaction with key or value transformations
 * can still meet 005-31's: the check counts a transformed KV coarsely, from the stream's
 * length (at node size 62, 500 such KVs of 111-byte keys on a stream of 258 kB; review
 * rev24, R3). A value transformation's result counts for L5, and for 005-17's size,
 * as a value given directly: execute() checks them after the transformations, before the go
 * point (bergdb 026-06; ValueTransformation).</p>
 * 
 * <p><b>Errors</b> (2026-11-06, bergdb 019-10; 010-01, P7). BergDB assumes a sound
 * environment: correct storage, a stream that returns the bytes appended to it, and enough
 * memory and stack for its work. Its checksums and checks find some damage of the stored
 * bytes, not all: they are a best effort, and damage that passes them gives wrong values
 * with no error. Only a cut tail, as after a crash or a power loss, is recovered. BergDB
 * does not try to recover when the environment fails; the database fails instead. That
 * happens on:</p>
 * <ul>
 * <li>an I/O error or corrupt data in the storage;</li>
 * <li>an unexpected exception from the storage's stream;</li>
 * <li>an Error, such as OutOfMemoryError or StackOverflowError, thrown during a read, a
 * transaction or a sync, also in the application's code that it runs (a getMany's
 * StopCondition), or on one of the database's own threads;</li>
 * <li>any exception after a transaction's go point, as nothing there is undone.</li>
 * </ul>
 * <p>A failed database does no more work. The call that met the failure throws it: an Error
 * as it is, anything else as a DbFailedException. Every later read and transaction throws a
 * DbFailedException with the first failure as its cause, and nothing more is appended.
 * Transactions that a sync() has returned for are safe; stop() and close() still work, and
 * so does sync() while the storage does. The application should then end its process; the
 * next start recovers the database as after a crash. For OutOfMemoryError, the JVM option
 * -XX:+ExitOnOutOfMemoryError ends the process at once, and that is the advice: while the
 * heap stays full, BergDB cannot promise even to fail cleanly, so a sync() or close() may
 * then wait (bergdb 019-39). (A start that fails throws what it met, and the database is
 * stopped; see start().)</p>
 * 
 * <p>Everything else the database throws fails only that call, and the database goes on: a
 * transaction refused before its go point, a lookup time no longer available, a bad
 * argument. A null argument is refused with an IllegalArgumentException that names it,
 * before anything else, as in the Pub API: by Db, DbBuilder, Trans.Builder and GetMany's stop
 * conditions, and a GetMany whose stop condition is null (bergdb 020-27, Q2).</p>
 * 
 * <p>Db shutdown. The Db typically has allocated resources besides memory: 
 * open files, running threads, open sockets for example. The Db user must call stop() or
 * close() once the Db is no longer used, as for a file or a socket: stop() requests the
 * release of the resources and returns at once, close() also waits until they are released.
 * Nothing else releases them (2026-10-27, bergdb 005-55: finalize() is gone, with no
 * safety net in its place). A Db that is not stopped keeps its threads, its open files,
 * its write buffer and its memory until the JVM exits. What it has
 * committed is still written within the buffer time (50 ms by default), as after any
 * commit; its threads are daemon threads, so they do not
 * keep the JVM alive, and at its exit what is buffered and not yet written is lost, as in
 * a crash, which the database tolerates.</p>
 * 
 * <p>Db is AutoCloseable (bergdb 005-59): a try-with-resources block closes it with close()
 * when the block ends, also when the block throws, and so waits until it is closed.</p>
 * 
 * @author Frans Lundberg
 */
public class Db implements AutoCloseable {
    
    // ======== Limits (bergdb 024-17, section 6; 024-24) ========
    // Fixed constants, the same for every database: raise later, never lower (024-17, 6.3).
    // Db's Javadoc, "Limits", and the pub package's say them for users.
    
    /**
     * L1: the most operations of a transaction, the KVs it puts or deletes after
     * Trans.Builder.build()'s rule of one operation a key (bergdb 024-17, L1). Checked by
     * execute(), before the write lock.
     */
    public static final int MAX_OPERATIONS = 500;
    
    /**
     * L2: the most bytes of a key as stored, its bkey: 16 segments of 7 bytes (a key of b
     * bytes has b / 7 + 1 segments, so 112 bytes would be 17; bergdb 024-17, L2, F10). Checked
     * by the Trans.Builder call that takes the key, and by execute() for a key that a key
     * transformation gives. BergDB's own longer keys (the Pub API's index entries) are put
     * through Trans.Builder's internal calls, which do not check it; L3 bounds them.
     */
    public static final int MAX_KEY_BYTES = 111;
    
    /**
     * L3: the most bytes of the keys of a transaction, 56 KiB: 500 keys of 111 bytes are
     * 55,500 bytes, so only BergDB's own longer keys meet it (bergdb 024-17, L3). With L1 it
     * bounds the key segments of a transaction, and so the index nodes it can make dirty
     * (024-17, 5.2a). Checked by execute(), before the write lock.
     */
    public static final int MAX_TRANS_KEY_BYTES = 56 * 1024;
    
    /**
     * L4: the most bytes of a value, 8 MiB (bergdb 024-17, L4). Checked by the Trans.Builder
     * call that takes the value; a value transformation's result over it refuses the
     * transaction, by execute(), with a DbException (bergdb 026-06; ValueTransformation).
     */
    public static final int MAX_VALUE_BYTES = 8 * 1024 * 1024;
    
    /**
     * L5: the most bytes of the keys and values of a transaction, 32 MiB (bergdb 024-17, L5).
     * Checked by execute(), before the write lock.
     */
    public static final long MAX_TRANS_BYTES = 32L * 1024 * 1024;
    
    private Dag dag;
    
    private final NodeCollection nodeCollection;
    
    private final NodeStream nodeStream;
    
    private TransSeq transSeq;
    
    /**
     * The newest written top node: the top node with the largest id among those written to
     * the stream. Every transaction stores the position of its latest version (topPos), from
     * which startup finds the super root (bergdb 011-11, M18). Set at startup;
     * accessed by the writer (writeLock) only.
     */
    private TopNode newestWrittenTop;
    
    /**
     * Global transaction write lock. Held when STM stuff is happening.
     */
    private final WriteLock writeLock;
    
    /**
     * Writers waiting for writeLock in executeInner (bergdb item 009, step 3d): the eviction
     * thread gives way to them (Eviction.EvictorRun), as a monitor is not fair and a busy
     * eviction thread would keep the writer out.
     */
    private final java.util.concurrent.atomic.AtomicInteger writersWaiting =
            new java.util.concurrent.atomic.AtomicInteger();
    
    /**
     * Sync object used to make sure writes from Db(), start(), execute(), are published
     * and made visible to threads calling getOne(), getMany().
     * It is typically used with an empty block: "synchronized (readSynch) {}".
     */
    private final ReadSync readSync;
    
    private final KeyModSet keyModSet;
    
    private final StorageManager storageManager;
    
    /** The reclaim algorithm. */
    private final Reclaim reclaim;
    
    /** 
     * State of the database. Synch note: volatile since bergdb item 009, step 1c, so that a
     * read, which no longer synchronizes on readSync, sees it; written under readSync, as
     * before (setFailed(), stop()).
     */
    private volatile DbState state = DbState.ZERO;
    
    /**
     * What failed the database, the first time, or null; the state is then FAILED: what a
     * transaction threw after its go point (bergdb 005-01, fail()), what a read or a sync
     * met on the storage (bergdb 005-30, failOnStorage()), a failure of the storage that
     * the next call finds (bergdb 015-35, assertDbStateIsActive()), or an Error that a call
     * met, or anything that one of the database's own threads met (bergdb 019-10, failed(),
     * Internal.fail()). Written under readSync, with the state (setFailed()).
     */
    private volatile Throwable failure = null;
    
    /**
     * The close of the storage, which stop() starts in a thread of its own and close() waits
     * for (2026-10-24, bergdb 005-35): begun and done, under closeLock. See closeStorage().
     */
    private final Object closeLock = new Object();
    private boolean closeBegun = false;
    private boolean closeDone = false;
    private IOException closeFailure;    // Under closeLock, also when stop() began the close.
    
    private final ExecuteData x;
    private final Aux aux = new Aux();
    
    /** DatabaseId from Database.Builder, may be null. */
    private DatabaseId databaseIdFromBuilder;
    
    /** The current meta block data of the node stream. */
    private final MetaBlock metaBlock;
    
    private final DbClock dbClock;
    private final int maxNodeSize;
    
    /** Current startupDistance. Sync note: protected by writeLock. */
    private int startupDistance;
    
    // ---- Misc ----
    
    private DatabaseId databaseId;
    private final TransactionListener reclaimTransactionListener;
    private final Internal internal;
    private File createdTxtDir;
    private String createdTxtCryptoKeyInfo;
    private Cache3 cache;

    /**
     * Whether the main stream is encrypted: a SalsaStream, as DatabaseBuilderImp makes for its
     * internal crypto key; for the message of a start refused for the magic bytes (bergdb
     * 005-33). Release 2026.4 has no encryption in its API (bergdb 020-28).
     */
    private final boolean encrypted;
    
    /**
     * The length of a new database's stream, what a creation writes (2026-10-25, bergdb
     * 005-33): the first meta block, 128 bytes, and the primordial transaction, 144 bytes
     * (its header, the super root with its one pointer, the first key node, empty, and the
     * record's end, aligned to 8; 136 until the top node's header grew by 8 bytes, bergdb
     * 024-25). writePrimordialTransaction() asserts it.
     */
    static final long CREATION_LENGTH = RecoverableStream.META_BLOCK_SIZE + 144;
    
    /**
     * The audit (bergdb item 001, WP J1; test-only): after every auditEvery-th transaction
     * and at every startup; 0 is off. DbBuilder.audit(), by default the system property
     * audit (Audit.EVERY).
     */
    private final int auditEvery;

    /**
     * The audit's oracle of latest positions (test-only), kept only when the audit is on;
     * see Audit.
     */
    private final Audit.Oracle oracle;

    /** Transactions since the last audit; see audit(). */
    private int auditCountdown;

    /** Eviction at transaction boundaries (bergdb item 001, WP J2 on); see Eviction. */
    private final Eviction eviction;
    
    /** The ordinal of the second top node: 1, or for tests another (DbBuilder.secondTopOrdinal). */
    private final long secondTopOrdinal;
    

    /**
     * Constructor takes a DbBuilder; it wires dependencies based on builder settings.
     */
    Db(DbBuilder b) {
        internal = new Internal();
        writeLock = new WriteLock();
        readSync = new ReadSync();
        x = new ExecuteData();
        keyModSet = new KeyModSet();
        
        Cache.DbInfo dbInfo = new Cache.DbInfo() {};
        
        cache = new Cache3(dbInfo);
        cache.setSizeIndicator(b.cacheSizeIndicator);
        // The capacity controller's budget: the cache size indicator, or for tests the system
        // property evictbudget (DbBuilder; bergdb item 001, WP J7).
        eviction = new Eviction(b.evictionSchedule, b.evictionSeed,
                b.evictionBudget > 0 ? b.evictionBudget : b.cacheSizeIndicator);
        auditEvery = b.auditEvery;
        oracle = auditEvery > 0 ? new Audit.Oracle() : null;
        auditCountdown = auditEvery;
        secondTopOrdinal = b.secondTopOrdinal;
 
        this.maxNodeSize = b.maxNodeSize;
        this.startupDistance = b.startupDistance;
        this.metaBlock = new MetaBlock();        
        // Before the storage, whose threads and open files nothing would close if this threw
        // (bergdb 005-32): a null clock.
        this.dbClock = new DbClock(b.clock);
        this.storageManager = createStorageManager(b);
        
        AppendOnlyStream aos = storageManager;
        x.endOfLastTrans = aos.getLength();
        
        RecoverableStream rstream = new RecoverableStream(aos, metaBlock);
        this.nodeStream = new NodeStream(rstream, writeLock);
        this.nodeStream.getMetaBlock().setStartupDistance(b.startupDistance);
        
        this.nodeCollection = new NodeCollection(dbInfo, nodeStream, cache);
        nodeCollection.setLoadListener(new NodeCollection.LoadListener() {
            public void loaded(bergdb.dag.OpData op) {
                // The capacity controller (WP J7). A load of a transaction's warmup wakes the
                // eviction thread and does not wait for its batch, as a reader's load does
                // under pressure (bergdb 005-52, option B; Eviction.afterLoad). The warmup's
                // GetData has a class of its own, Trans.WarmupGetData: the test is a type
                // check, made only here, after a read from the stream; a follow that finds
                // its object in memory makes no call.
                eviction.afterLoad(Db.this, !(op instanceof Trans.WarmupGetData));
            }
        });
        
        this.reclaim = new Reclaim(this, aos);
        reclaim.setStepReserve(b.reclaimStepReserve);
        this.reclaimTransactionListener = reclaim;
        // The retain duration and the internal fraction: the stream's, read by
        // Reclaim.initFromDb at the start (bergdb 015-87); not the builder's.
        
        this.databaseIdFromBuilder = b.id;
        
        this.createdTxtDir = b.createdTxtDir;
        // The key's line of created.txt comes from the SalsaStream, not from the builder
        // (2026-11-09, bergdb 020-28): DbBuilder.createdTxt took it until the encryption
        // left the API.
        this.encrypted = b.getMainStream() instanceof SalsaStream;
        this.createdTxtCryptoKeyInfo = encrypted
                ? ((SalsaStream) b.getMainStream()).getKeyInfo() : null;
        
        //
        // Synch note: Synchronized blocks make sure the writes in constructor are
        // published to threads synchronizing on readSync or writeLock.
        //
        synchronized (readSync) {}
        synchronized (writeLock) {}
    }

    private StorageManager createStorageManager(DbBuilder b) {
        DbBuilder.StreamInfo info = b.streamInfo;
        StorageManager.Builder smBuilder = new StorageManager.Builder();
        smBuilder.stream(info.stream, info.bufferSize, info.bufferTime);
        
        StorageManager sm = smBuilder.build();
        return sm;
    }

    /**
     * Returns the current length of the database stream. The method acquires
     * Db.writeLock; may affect performance.
     */
    public final long getStreamLength() {
        synchronized (writeLock) {
            return nodeStream.getLength();
        }
    }

    /**
     * The startup distance in force, in bytes: after start(), the stream's, as the creation
     * (DbBuilder.startupDistance()) or the last setStartupDistance() set it.
     */
    public int getStartupDistance() {
        synchronized (writeLock) {
            return this.startupDistance;
        }
    }
    
    /**
     * Sets the startup distance, the target size of the startup section. The take
     * (TransSeq.take) holds the actual startup distance, such that the stream's length minus
     * it is the position a start reads from, near the setting, and in any case it takes the
     * transactions that begin twice the setting or more before the end of the stream (the
     * deadline). The new setting applies at once: after a decrease, the commits that follow
     * write more index nodes, each in proportion to its size, until the startup section is
     * near the new setting; after an increase, fewer. A decrease does not make one commit
     * write the index nodes of every transaction past twice the new setting: while the
     * actual startup distance is longer than that, the deadline is at about the actual
     * startup distance and comes down with it, a commit at a time (bergdb 007-03, D4;
     * 007-07). So one call is enough, with no need to lower the distance in steps. The
     * section comes down only as transactions are committed: in 007-06's runs, over stream
     * of about 1.4 times the bytes of the dirty index nodes at the decrease. This method
     * commits a transaction with a value of 200 kB, at the key "/#i/-dummy", where it stays
     * live (Keys and the layers above), so that a meta block in the stream
     * records the new setting: a start reads it from there, as the setting decides the
     * stream's bytes (010-P2). The value is clamped to 400,000 to 1,000,000,000 bytes
     * (twice RecoverableStream.META_BLOCK_DISTANCE to 10^9), and the clamped value is set; a
     * call whose clamped value is the setting in force writes nothing (bergdb 005-53). So on
     * a database whose setting is outside that range, which DbBuilder.startupDistance allows
     * (10 bytes and up), any call writes and sets a value inside it (bergdb 015-76). A
     * negative value is refused with IllegalArgumentException and changes nothing. On a
     * database that is not active the call throws as a transaction does
     * (IllegalDbStateException, DbStoppingException, DbFailedException), and a call that
     * is refused leaves the setting as it was.
     */
    public void setStartupDistance(int newDistance) {
        //
        // A dummy transaction of size >= META_BLOCK_DISTANCE is written
        // to the stream to ensure that the new value of startupDistance is 
        // stored in a meta block in the stream.
        //
        
        if (newDistance < 0) {
            throw new IllegalArgumentException("Bad newDistance: " + newDistance + ".");
        }
        
        int min = RecoverableStream.META_BLOCK_DISTANCE * 2;
        int max = 1000*1000000;
        
        newDistance = newDistance < min ? min : newDistance;
        newDistance = newDistance > max ? max : newDistance;
        
        int dist = (int) newDistance;
        byte[] dummyValue = new byte[RecoverableStream.META_BLOCK_DISTANCE];
        
        synchronized (writeLock) {
            // The state first, so that a refused call changes nothing (bergdb 005-53).
            assertDbStateIsActive("setStartupDistance");
            int old = this.startupDistance;
            if (newDistance == old) return;
            this.startupDistance = newDistance;
            this.nodeStream.getMetaBlock().setStartupDistance(dist);
            try {
                this.execute(trans().putCore(DbConstants.DUMMY_KEY, dummyValue).build());
            } catch (RuntimeException | Error e) {
                // Refused, or the database failed and must be restarted, which reads the
                // stream's setting.
                this.startupDistance = old;
                this.nodeStream.getMetaBlock().setStartupDistance(old);
                throw e;
            }
        }
    }
    
    /**
     * Returns the cache size indicator in bytes, the budget of the cache: the capacity
     * controller's high watermark (Eviction), DbBuilder.cacheSizeIndicator or the value of
     * setCacheSizeIndicator() since the start.
     */
    public long getCacheSizeIndicator() {
        return eviction.budget();
    }

    /**
     * Sets the cache size indicator in bytes, the budget of the cache, while the database
     * runs (bergdb 005-52): the capacity controller's budget and low watermark (Eviction)
     * and Cache3's indicator, in force when the method returns. After a decrease the method
     * wakes the eviction thread if the resident bytes are over the new budget; it evicts in
     * batches of at most 2 ms, between transactions, until they are at most the budget, so
     * that a database that is not used gives the memory back too: work that the call starts
     * (010-P3). Commits and loads run batches too, as always. What must stay in memory (the
     * nodes changed since the startup position) is never evicted and may exceed the budget.
     * After an increase there is nothing to do. The setting is for this run only: it
     * changes no byte of the stream (level4.sh's EvictionInvariance), so it is not kept
     * there, and a start takes the builder's value. A setting that changes the stream's
     * bytes is kept in the stream (setStartupDistance, 010-P2); one that does not lasts for
     * the run. On a database that is not active the method only sets the value. A value
     * below 1 is refused with IllegalArgumentException, and the setting stays as it was.
     */
    public void setCacheSizeIndicator(long sizeIndicator) {
        if (sizeIndicator < 1) {
            throw new IllegalArgumentException("Bad sizeIndicator: " + sizeIndicator + ".");
        }
        try {
            cache.setSizeIndicator(sizeIndicator);
            eviction.setBudget(this, sizeIndicator);    // It may start the eviction thread.
        } catch (Error e) {
            throw failed(e);
        }
    }

    /**
     * The retain duration in force, in time units: the stream's, as the last
     * setRetainDuration() wrote it; Long.MAX_VALUE, forever, if it was never called.
     */
    public long getRetainDuration() {
        return reclaim.getRetainDuration();
    }

    /**
     * Sets the retain duration, and keeps it in the stream (bergdb 015-87): the time for
     * which old states stay available for lookups; Long.MAX_VALUE is forever, in force
     * until a call sets another. A finite duration makes reclaim rewrite live values and
     * cut the front of the stream. The value decides the stream's bytes, so it is kept in
     * the stream, as the startup distance is (010-P2): the call commits a small internal
     * transaction with reclaim's settings, at the key "/#i/dreclaim/-settings.txt"
     * (Reclaim.SETTINGS_KEY_NAME; Keys and the layers above), and a start reads
     * them; a restart keeps the value, and there is no builder setting. The new value is in
     * force when the method returns, from the next transaction on. A call with the value in
     * force writes nothing. On a database that is not active the call throws as a
     * transaction does (IllegalDbStateException, DbStoppingException, DbFailedException),
     * and so it does, with a DbException, on one that has used its top node ordinals
     * (bergdb 005-02); a call that is refused, or whose commit fails, leaves the value as
     * it was.
     * 
     * @param duration
     *            Number of time units (see Clock.UNITS_PER_SEC), at least one second.
     * @throws IllegalArgumentException  If duration is less than one second.
     */
    public void setRetainDuration(long duration) {
        Reclaim.checkRetainDuration(duration);
        synchronized (writeLock) {
            // The state first, so that a refused call changes nothing (bergdb 015-87, F6).
            assertDbStateIsActive("setRetainDuration");
            reclaim.setSettings(duration, reclaim.getInternalFractionUnits());
        }
    }
    
    /**
     * Does a bounded part of the database's maintenance now, and returns whether more is due
     * (bergdb 024-32). Optional: the maintenance goes on in the ordinary operations, at the
     * application's commits, whether this method is called or not. Frans (2026-11-10, bergdb
     * 023-04, Y10): "maintainance should be performed while doing other operations on the
     * database, so the user explicitely calling maintain() should be optional, not a
     * requirement on the user that she must call maintain." What it adds: a database that
     * the application no longer writes to does no work by itself (010-01, P3), so with a
     * finite retain duration its space comes back only with later commits; calls of this
     * method bring it back without them. Called again and again, with time passing, it
     * brings a database that has been emptied to about the stream of a fresh one (bergdb
     * 023-02, F7; java/stress/CountGates.java, G5).
     * 
     * <p>One call does, in the database's own internal transactions, at most: the start of
     * a reclaim iteration, if a quarter of the retain duration has passed since the last
     * one began, the last one is cut and the new one's cut would release at least 400 kB;
     * one reclaim step (about 16 kB of KVs scanned); one write of index nodes of the startup
     * section that an iteration waits for (at most 256 kB beyond one transaction's); one
     * filler of at most 200 kB, put and deleted, so that a meta block follows the cut point;
     * the cut, when it is due, after a sync if its table is not yet durable; and a batch of
     * the eviction's dead hand, which drops the objects of versions that a cut has ended
     * (Eviction; as after a transaction, with a cache budget). Each part is
     * no larger than what reclaim does after a commit. With a retain duration of forever
     * there is nothing to do (Reclaim.maintain; bergdb 024-32, section 2).</p>
     * 
     * <p>It runs under the write lock, as a commit does: it waits for a running commit, and
     * a commit waits for it; reads go on as during commits. The sync, if any, is outside the
     * lock. What it writes depends on the state and the call's time, as a transaction's
     * does, so the stream is the same after the same calls (010-01, P2). A call when
     * nothing is due writes nothing.</p>
     * 
     * @return True if more is due now: another call would do more. False if nothing is due
     *      until time passes (a quarter of the retain duration for the next iteration, the
     *      retain duration for a cut) or the application writes. A caller that wants the
     *      space back now calls it until it returns false, and again later.
     * @throws IllegalDbStateException, DbStoppingException, DbFailedException  On a
     *      database that is not active, as a transaction (and setRetainDuration()).
     * @throws DbException  If the database has used its top node ordinals, or has no time
     *      left for a user transaction (bergdb 005-02, 015-55): as a transaction is refused.
     *      Nothing is written then.
     * @throws StreamIoException  If the sync is interrupted, or the database is stopping.
     */
    public boolean maintain() {
        final long durableAt;
        synchronized (writeLock) {
            assertDbStateIsActive("maintain");
            refuseIfTopOrdinalsUsed();
            if (!dbClock.userTimeLeft()) {
                throw new DbException("No database time is left for maintain(): the times "
                        + "after " + DbClock.LAST_USER_TIME + " are kept for reclaim's "
                        + "internal transactions after a user transaction. Nothing is written.");
            }
            final long now = dbClock.currentTime();
            final boolean more;
            try {
                more = reclaim.maintain(now, dbClock.lookupTime(Long.MAX_VALUE));
            } catch (DbStoppingException | DbFailedException e) {
                // stop() or close() came during the call (bergdb 015-53): what is committed
                // stays, and the rest goes on after the next start. Or one of its internal
                // transactions failed the database.
                throw e;
            } catch (Throwable e) {
                // As reclaim's work within a commit's go point (executeInner): whatever else
                // throws fails the database, since reclaim's state in memory may be ahead of
                // the stream. The checks above refuse a call before it changes anything.
                if (setFailed(e) == DbState.STOPPING || e instanceof Error) {
                    if (e instanceof Error) throw (Error) e;
                    throw (RuntimeException) e;
                }
                throw new DbFailedException("maintain() failed after it began (the cause); "
                        + "the database takes no more transactions or reads and must be "
                        + "restarted: the restart rebuilds it from the stream.", e);
            }
            durableAt = reclaim.pendingCutDurableAt();
            if (durableAt == -1 || getDurableLength() >= durableAt) {
                reclaim.cutIfDurableNow();
                // The dead hand (Eviction), as after a transaction: the objects of the
                // versions that the cut ended leave memory, a batch a call.
                final boolean dead = maintainEviction();
                return reclaim.maintainDue(now) || dead;
            }
        }
        
        // A cut is decided and its table is not yet durable (Reclaim.cutIfDurable): a sync
        // outside the lock, then the cut.
        sync(durableAt - 1, SyncLevel.ORDINARY);
        synchronized (writeLock) {
            assertDbStateIsActive("maintain");
            reclaim.cutIfDurableNow();
            final boolean dead = maintainEviction();
            return reclaim.maintainDue(dbClock.currentTime()) || dead;
        }
    }
    
    /** maintain()'s step of the eviction's dead hand; under the write lock. */
    private boolean maintainEviction() {
        try {
            return eviction.maintainStep(this);
        } catch (Throwable e) {
            if (setFailed(e) == DbState.STOPPING || e instanceof Error) {
                if (e instanceof Error) throw (Error) e;
                throw (RuntimeException) e;
            }
            throw new DbFailedException("maintain() failed after it began (the cause); "
                    + "the database takes no more transactions or reads and must be "
                    + "restarted: the restart rebuilds it from the stream.", e);
        }
    }
    
    /**
     * Sets reclaim's internal fraction: the bytes an iteration rewrites, compared to the
     * stream's growth while it runs; 0.25 by default. Used from the next step.
     * 
     * <p>It must be between 0.001 and 0.90 inclusive. NaN and other values are refused with
     * an IllegalArgumentException, and the setting stays as it was (bergdb 005-73).</p>
     * 
     * <p>Kept in the stream with the retain duration, as setRetainDuration() keeps that
     * (bergdb 015-87, F7): a commit of reclaim's settings, nothing written when the value
     * is in force, refused as a transaction is on a database that is not active, the value
     * unchanged when refused; a restart keeps it.</p>
     * 
     * <p>Reclaim keeps the fraction as an integer in units of 2^-16 (bergdb 005-79): the
     * nearest one, (int) Math.round(internalFraction * 65536), so 0.25 is kept exactly and
     * 0.1 as 6,554 units (0.100006). The product with a power of two is exact, so only
     * Math.round rounds, half up. No double decides the stream's bytes.</p>
     */
    public void setReclaimInternalFraction(double internalFraction) {
        if (Double.isNaN(internalFraction) || internalFraction < 0.001 || internalFraction > 0.90) {
            throw new IllegalArgumentException("Illegal internalFraction value, " + internalFraction);
        }
        int units = (int) Math.round(internalFraction * Reclaim.FRACTION_ONE);
        synchronized (writeLock) {
            assertDbStateIsActive("setReclaimInternalFraction");
            reclaim.setSettings(reclaim.getRetainDuration(), units);
        }
    }
    
    /**
     * Reclaim's internal fraction as it is used: its units of 2^-16 over 65,536, which is
     * exact (bergdb 005-79). After setReclaimInternalFraction(0.25) it is 0.25; after 0.1 it
     * is 6554 / 65536.0.
     */
    public double getInternalFraction() {
        return reclaim.getInternalFractionUnits() / (double) Reclaim.FRACTION_ONE;
    }
    
    /** The number of reclaim's iterations that this Db has completed since its start(). */
    public long getReclaimIterationCount() {
        return reclaim.getIterationCount();
    }

    /**
     * First (smallest) time available for a lookup.
     */
    public long getFirstAvailableLookupTime() {
        synchronized (readSync) {}
        return reclaim.getFirstAvailableLookupTime();
    }

    /**
     * The first position of the stream that reclaim has not cut: 0 before the first cut, then
     * the position of the last cut. The stream before it is removed, or may be at any time,
     * and a transaction there is no longer available (getTrans()).
     */
    public long getFirstAvailablePos() {
        synchronized (readSync) {}
        return reclaim.getFirstAvailablePos();
    }
    
    /**
     * The number of transactions that this Db has executed since its start(), BergDB's own
     * included (the settings' commits, reclaim's steps; Keys and the layers above): 0 after a
     * start, not the number of transactions in the database (bergdb 020-24-09, U9-10).
     */
    public long getTransactionCount() {
        synchronized (writeLock) {
            return aux.transactionCount;
        }
    }
    
    /**
     * The number of KVs of the transactions that getTransactionCount() counts: each
     * transaction's puts and deletes, one a key (Trans.Builder.build()), a delete of a key
     * without a value included. 0 after a start; not the number of keys with a value
     * (bergdb 020-24-09, U9-10).
     */
    public long getKvCount() {
        synchronized (writeLock) {
            return aux.kvCount;
        }
    }
    
    /**
     * Returns the number of get operations that has completed since Db.start() was called.
     */
    public long getGetOpCount() {
        return aux.getOpCount.sum();
    }

    /** The stream length that has ordinary durability; see SyncLevel.ORDINARY. */
    public long getDurableLength() {
        return storageManager.getDurableLength();
    }
    
    /**
     * The position of the transaction named by the last valid meta block; recovery starts
     * there. See RecoverableStream.getLastTransSposOfLastValidMetaBlock().
     */
    public final long getLastTransPosOfLastValidMetaBlock() {
        return nodeStream.getLastTransPosOfLastValidMetaBlock();
    }
    
    /**
     * The current database time, in clock units (100 ns since 1970; Clock): the clock's time
     * (DbBuilder.clock(), the system clock by default), but never earlier than the last
     * transaction's time or a time that this method gave before, and earlier than the time of
     * every transaction that runs or comes later. So a read at it reads the same state
     * whenever it runs, and it may be a transaction's read time ("Threads" and "Optimistic
     * transactions" above).
     * 
     * @see bergdb.core.DbClock
     */
    public long currentTime() {
        return dbClock.currentTime();
    }
    
    /**
     * Internal, not part of public API.
     * Returns internal (actual) lookup time given a wanted lookup time.
     */
    public long lookupTime(long wantedLookupTime) {
        return dbClock.lookupTime(wantedLookupTime);
    }

    /**
     * Starts the database by reading from the stream. Call once per Db object
     * after constructor and before the get/set methods.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     *             Among others, if the database has another maximum node size than this
     *             start, 30 but in BergDB's own tests (bergdb 026-08), or none, as one
     *             written before 2026-10-27 (bergdb 005-50); the start then writes nothing.
     * @throws DatabaseNotCreatedException
     *             If the stream holds a creation that did not complete, and no committed
     *             transaction (bergdb 005-33). The start writes nothing.
     * @throws IllegalDbStateException
     *             If start() has been called already, or stop(): nothing is closed then.
     * @throws DbFailedException
     *             If a read of reclaim's settings or table, the last step of the startup,
     *             fails on the storage (bergdb 005-30).
     */
    public StartInfo start() {        
        return start(StartParams.NULL);
    }
    
    /**
     * Starts the database by reading from the stream. Call once per Db object
     * after constructor and before the get/set methods.
     * 
     * <p>A start that throws closes the storage before the exception leaves (2026-10-24,
     * bergdb 005-32): what it appended is written (recovery's zero fill, as any start writes
     * it; until 2026-11-04, bergdb 005-11, also the copies between the main stream and its
     * replicas), the stream is closed and its thread has ended, and the database is
     * stopped: later calls are refused as after stop(). A failure of that close is added to
     * the exception as suppressed. Before, the storage ran on until the garbage collector
     * finalized the Db, and its threads wrote into a database started after it on the same
     * files.</p>
     * 
     * @param params  
     *          Used for testing, normally set to StartParams.NULL as default.
     * @throws IllegalArgumentException
     *          If params is null: nothing is closed then (bergdb 020-27, Q2).
     * @throws StreamIoException
     * @throws StreamFormatException
     *          Among others, if the database has another maximum node size than this
     *          start, 30 but in BergDB's own tests (bergdb 026-08), or none, as one written
     *          before 2026-10-27 (bergdb 005-50); the start then writes nothing.
     * @throws DatabaseNotCreatedException
     *          If the stream holds a creation that did not complete, and no committed
     *          transaction (bergdb 005-33). The start writes nothing.
     * @throws IllegalDbStateException
     *          If start() has been called already, or stop(): nothing is closed then.
     * @throws DbFailedException
     *          If a read of reclaim's settings or table, the last step of the startup,
     *          fails on the storage (bergdb 005-30).
     */
    public StartInfo start(StartParams params) {
        if (params == null) {
            // Before the locks and the state: a null closed the storage (bergdb 020-27, Q2).
            throw new IllegalArgumentException("params == null not allowed");
        }
        Throwable failure;
        synchronized (writeLock) {
            synchronized (readSync) {
                assertStateIsZero();
                try {
                    return startInner(params);
                } catch (Throwable e) {
                    // Under both locks, so that no call sees what the start left.
                    state = DbState.STOPPING;
                    failure = e;
                }
            }
        }
        closeAfterFailedStart(failure);
        if (failure instanceof RuntimeException) {
            throw (RuntimeException) failure;
        }
        if (failure instanceof Error) {
            throw (Error) failure;
        }
        throw new Bug("start() threw a checked exception, " + failure);
    }
    
    /**
     * Closes the storage of a start that threw, outside the locks (bergdb 005-32); see
     * start(). StorageManager's close needs neither writeLock nor readSync.
     */
    private void closeAfterFailedStart(Throwable failure) {
        synchronized (closeLock) {
            closeBegun = true;      // A later stop() or close() has nothing to do.
        }
        try {
            IOException e = closeStorage(true);
            if (e != null && e != failure) {
                failure.addSuppressed(e);
            }
        } catch (RuntimeException | Error e) {
            if (e != failure) {
                failure.addSuppressed(e);
            }
        }
    }
    
    /**
     * The startup implementation.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     * @throws IllegalDbStateException
     * @throws DatabaseNotCreatedException
     */
    private StartInfo startInner(StartParams params) {
        assertStateIsZero();

        storageManager.start();
        handleEmptyStream();
        refuseIncompleteCreation();
        
        try {
            refuseOtherNodeSize();
            nodeStream.recover();
        } catch (BadMagicBytes e) {
            // 2026-10-25 (bergdb 005-33): without a crypto key, the message said that the
            // wrong key was used too, also for a stream of zero bytes, as a power loss can
            // leave one.
            // 2026-11-09 (bergdb 020-24-07, U7-7): with a key, the message named only a
            // wrong key, and a damaged stream gives it with the right key too.
            // 2026-11-09 (bergdb 020-28): a StreamFormatException, with the BadMagicBytes as
            // its cause; it was the Pub API's BadCryptoKey, removed with the encryption from
            // 2026.4's API. Without a key, the message names a stream that an earlier release
            // encrypted, which this one does not read; the Pub API refuses such a database by
            // its created.txt before (DatabaseBuilderImp.refuseEncrypted).
            throw new StreamFormatException(encrypted
                    ? "Invalid magic bytes in stream, read with the crypto key given: likely, "
                    + "the wrong crypto key was used, or the database is not encrypted; else "
                    + "the stream is damaged, or it is not a BergDB stream. The start has "
                    + "written nothing."
                    : "Invalid magic bytes in stream: the stream is not a BergDB stream, or it "
                    + "is damaged; or an earlier release of BergDB, 2026.3 or before, encrypted "
                    + "it, and this release cannot read it: it has no encryption (bergdb "
                    + "020-28). The start has written nothing.", e);
        }
        
        handleStartParams(params);
        
        long startupPos = x.startupPos.get();
        ArrayList<StoredTrans> transactions = readTransactions(startupPos);
        
        setLastTransTimeOfDbClock(transactions);
        
        startDb(transactions);
        // Seed STM coverage only after DbStarter has validated the recovered times.
        keyModSet.setFirstTime(transactions.get(transactions.size() - 1).tt);
        
        createPutAndGetData();
        writeCreatedTxtIfMissing();
        
        this.state = DbState.ACTIVE;
        reclaim.initFromDb();
        synchronized (writeLock) {
            // The admission of the large values that the start made resident, as after a
            // record that this database writes (Eviction.recordWritten): their records are in
            // the stream, and their pointers become stream pointers; the list is empty after
            // it (bergdb 015-68). Until 015-68 the rerun's pointer listener (newPutData) put
            // them on the list, and only the next transaction's record took them off: a
            // database opened for reads kept them in memory, outside the resident bytes. The
            // resident key nodes too, as a record's written nodes (bergdb 019-47): the start
            // links the values of the section's first transaction, which is not rerun, into
            // the section's node versions (DbStarter.createMemoryPointers), and the list did
            // not have those; a large one stayed in its leaf.
            eviction.recordWritten(this, cache.nodes().iterator());
            eviction.afterTransaction(this);    // the controller, after startup's loads (J7)
        }
        if (auditEvery > 0) {
            synchronized (writeLock) {
                audit(true);
            }
        }
        
        StartInfo result = new StartInfo();
        result.startPos = startupPos;
        result.startupDistance = startupDistance;
        result.startTime = transactions.get(0).tt;
        result.transCount = transactions.size();
        result.lastPos = transactions.get(transactions.size() - 1).lastPos;
        
        return result;
    }

    private void startDb(ArrayList<StoredTrans> transactions) {
        DbStarter.start(this, transactions, getAccessData(), maxNodeSize);
    }

    private void createPutAndGetData() {
        x.putData = newPutData();
        x.getData = newGetData();
    }
    
    /**
     * @throws StreamFormatException
     * @param listener
     */
    private void handleStartParams(StartParams params) {
        // params.isNull() is normally true, can be overridden for test purposes.
        
        if (params.isNull()) {
            params = new StartParams();
            MetaBlock meta = nodeStream.getMetaBlock();
            meta.checkFormat();
            
            // From meta saves 8 bytes per trans (4% stream space trans with one kv of size 10-90).
            params.startupPos = getStartupPosFromLastTransaction(meta.getLastTransSpos());
            params.startupDistance = meta.getStartupDistance();
        }
        
        startupDistance = params.startupDistance;
        x.startupPos.set(params.startupPos);
    }

    /**
     * Returns the startupPos stored in the last successful transaction
     * by iterating from transPos to the end of the stream.
     */
    private long getStartupPosFromLastTransaction(long transPos) {
        // This approach was used from 150422 instead of the previous approach to use
        // the startPos from the last valid meta block.
        
        // 2026-10-13 (Reclaim.Tester.testRestartAfterCut): transPos is the position
        // of a transaction (from the last meta block), so the iteration starts there. It
        // used to search back for a meta block before transPos, which may have been cut
        // away by reclaim (pretruncate).
        if (transPos == Spos.NULL) {
            transPos = RecoverableStream.META_BLOCK_SIZE;   // The first transaction.
        }
        
        assert transPos >= 0 : "bad transPos: " + transPos;
        
        NodeStream.TransIterator iter = nodeStream.createTransIteratorFromExactStartupPos(transPos);
        long result = transPos;
        long lastTpos = Spos.NULL;
        
        while (iter.next()) {
            if (!iter.transOk) continue;
            
            StoredTrans storedTrans = iter.getStoredTrans();
            result = storedTrans.startupPos;            
            checkStartupPos(storedTrans);
            lastTpos = storedTrans.tpos;
        }
        
        // The meta block read at recovery holds the position of the last transaction
        // before it was written. Set it to the last transaction, as it is without a 
        // restart, so that the next meta block written is the same.
        if (lastTpos != Spos.NULL) {
            nodeStream.getMetaBlock().setLastTransSpos(lastTpos);
        }
        
        return result;
    }
    
    /**
     * Refuses a record whose startupPos cannot be one that the take wrote: negative, not a
     * multiple of the record alignment, in the first meta block (only 0 is), or after the
     * record's own position. Checks, not asserts, as no checksum covers a record's header
     * (bergdb 015-75; before, an assert only). They do not show that the position is a
     * record that the take reached (015-73).
     * 
     * @throws StreamFormatException
     */
    private static void checkStartupPos(StoredTrans storedTrans) {
        final long sp = storedTrans.startupPos;
        final String problem;
        if (sp < 0) {
            problem = "negative";
        } else if (sp % RecoverableStream.TRANS_ALIGNMENT != 0) {
            problem = "not a multiple of " + RecoverableStream.TRANS_ALIGNMENT;
        } else if (sp != 0 && sp < RecoverableStream.META_BLOCK_SIZE) {
            problem = "in the first meta block";
        } else if (sp > storedTrans.tpos) {
            problem = "after the record";
        } else {
            return;
        }
        throw new StreamFormatException("The record at " + storedTrans.tpos + " has startupPos "
                + sp + ", " + problem + ".");
    }
    
    /** 
     * Reads transactions from DB stream starting at startPos. 
     */
    private ArrayList<StoredTrans> readTransactions(long startupPos) {
        if (startupPos == 0) {
            startupPos = RecoverableStream.META_BLOCK_SIZE;
        }
        
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        NodeStream.TransIterator ti = nodeStream.createTransIteratorFromExactStartupPos(startupPos);
        while (ti.next()) {
            StoredTrans stored = ti.getStoredTrans();
            transactions.add(stored);
        }
        
        return transactions;
    }
    
    private void setLastTransTimeOfDbClock(ArrayList<StoredTrans> transactions) {
        long lastTransTime;
        int size = transactions.size();
        
        if (size == 0) {
            throw new StreamFormatException("No transactions in startup transaction set.");
        } else {
            lastTransTime = transactions.get(size - 1).tt;
        }
        
        dbClock.setLastTransTime(lastTransTime);
    }
    
    private PutData newPutData() {
        assert dag != null : "dag is null";
        assert this.nodeCollection != null : "Db.nodeCollection is null";
        
        PutData pd = dag.newPutData();
        pd.pointerFollower = this.nodeCollection.writer();
        
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) {
                // The gotDirty code in the PointerListener is not enough for
                // the case when new top nodes are created.
                // This method call assumes new nodes are not dirty.
                
                assert node.isDirty == false : "node is dirty, " + node;
                setIdOfNode(node);
                registerNewNode(node);
                markAtEndOfOp(node);
                opChanged = true;
            }
            
            public void keyNodeCreated(KeyNode node) {
                setIdOfNode(node);
                registerNewNode(node);
                markAtEndOfOp(node);
                opChanged = true;
            }
            
            public void keyNodeChanged(KeyNode node) {
                markAtEndOfOp(node);
                opChanged = true;
            }
            
            public void valueNodeCreated(ValueNode node, long[] key) {
                setIdOfNode(node);
                cache.tickAccessClock();
                cache.residents().added(node);
                x.transNodes.addValueNode(node, key);
                x.trans.listener.valueNodeCreated(node, key);
                final TestHooks hooks = testHooks;
                if (hooks != null) {
                    hooks.valueNodeCreated(node, key);
                }
                opChanged = true;
            }
            
            public void keyNodeReplaced(KeyNode node) {
                if (x.transInfo != null) replacedInTrans.add(node);
                final TestHooks hooks = testHooks;
                if (hooks != null) {
                    hooks.nodeReplaced(node);
                }
            }
            
            public void keyNodeTakenBack(KeyNode node) {
                keyNodeReplaced(node);
                takenBackInTrans.add(node);
            }
            
            public void topNodeReplaced(TopNode node) {
                if (x.transInfo != null) replacedInTrans.add(node);
                final TestHooks hooks = testHooks;
                if (hooks != null) {
                    hooks.nodeReplaced(node);
                }
            }
        };
        
        // Extends existing pointerListener used by Dag.
        
        final Dag.PointerListener pListener = pd.pointerListener;
        
        pd.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                pListener.superRootAccessed(superRoot);
                markAtEndOfOp(superRoot);
            }
            
            public void pointerFollowed(Node predecessor, int pointerIndex, Node result, int pointerType) {
                pListener.pointerFollowed(predecessor, pointerIndex, result, pointerType);
                markAtEndOfOp(result);
            }
        };
        
        pd.pointerCreatedListener = new Dag.PointerCreatedListener() {
            public void pointerCreated(Node from, int index, Node to) {
                assert !Spos.isNull(from.getId()) : 
                    "from-node has NULL id, from: " + from + ", to: " + to;
                assert !Spos.isNull(to.getId()) : 
                    "to-node has NULL id, from " + from + ", to: " + to;
                
                cache.pointerCreated(from, index, to);
                if (to instanceof ValueNode) {
                    eviction.largeValueCreated(from, index, (ValueNode) to);
                }
            }
        };
        
        return pd;
    }

    /**
     * @throws IllegalDbStateException
     */
    private void assertStateIsZero() {
        if (state != DbState.ZERO) {
            throw new IllegalDbStateException("Db has been started already, "
                    + "start() should be called once only; Db state is: " 
                    + state + ".");
        }
    }

    /**
     * If the stream is empty, this method creates the database id 
     * (if not given in the database builder)
     * and writes the first metablock and the primordial transaction to the stream.
     * 
     * <p>With created.txt (DbBuilder.createdTxt, the Pub API's directories), the creation is
     * made durable first, by a sync as Db.sync(ORDINARY) makes (rule D1: the main stream's
     * write and force), and created.txt written after it (2026-11-03, bergdb 015-01): so
     * created.txt marks a directory whose creation reached the disk, and the Pub API's start
     * refuses one that has it and no stream byte. Before, created.txt was written at once,
     * and the creation reached the file with the buffer's first write, after start()
     * returned. A sync that fails fails the start, and no created.txt is written.</p>
     * 
     * @throws StreamIoException
     */
    private void handleEmptyStream() {
        if (nodeStream.getLength() == 0) {
            determineDatabaseId();            
            writePrimordialTransaction();
            if (createdTxtDir != null) {
                syncCreation();
                writeCreatedTxt(Util.today(), databaseId);
            }
        }
    }
    
    /**
     * Waits until the creation is durable, by rule D1 (bergdb 015-01), without being
     * interrupted: a start ignores an interrupt until it is done, and keeps the thread's
     * flag (bergdb 005-46; PubInterruptTester). StorageManager.sync ends on an interrupt and
     * sets the flag again; here the flag is cleared and the wait goes on, and the flag is set
     * again at the end.
     * 
     * @throws StreamIoException  If the storage has failed: the start fails.
     */
    private void syncCreation() {
        boolean interrupted = false;
        try {
            while (true) {
                try {
                    storageManager.sync(CREATION_LENGTH);
                    return;
                } catch (InterruptedIOException e) {
                    Thread.interrupted();
                    interrupted = true;
                }
            }
        } catch (IOException e) {
            throw new StreamIoException(e);
        } finally {
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }
    
    /**
     * Writes created.txt for a database that holds data and has none (2026-11-03, bergdb
     * 015-01, A+): its created.txt was lost, or its creation stopped between the sync and
     * created.txt (handleEmptyStream). The creation date is unknown. Called at the end of a
     * start that read the stream, so that the Pub API refuses the directory if its stream
     * goes missing later. A failure to write it fails the start, as handleEmptyStream's does.
     */
    private void writeCreatedTxtIfMissing() {
        if (createdTxtDir == null || new File(createdTxtDir, "created.txt").exists()) {
            return;
        }
        writeCreatedTxt("unknown (created.txt written at a start on " + Util.today() + ")",
                DatabaseId.createFromBytes(nodeStream.getMetaBlock().getId()));
    }
    
    /**
     * Refuses a stream that holds a creation which did not complete (2026-10-25, bergdb
     * 005-33), before recovery: a crash, as a power loss, while the database was created left
     * a part of what the creation writes (RecoverableStream.isIncompleteCreation). Such a
     * stream holds no committed transaction, so no data, and it is not a database: a stream
     * is valid only after its primordial transaction has run (Frans, 2012-08-20). Before, the
     * start threw one of three StreamFormatExceptions that did not say so, and recovery
     * zero-filled a cut transaction first. Now nothing is written, and the application, or a
     * person, removes the files.
     *
     * @throws DatabaseNotCreatedException
     */
    private void refuseIncompleteCreation() {
        if (nodeStream.isIncompleteCreation(CREATION_LENGTH)) {
            throw new DatabaseNotCreatedException("The database was not completely created "
                    + "(a crash or a power loss while it was created?): its stream, of length "
                    + nodeStream.getLength() + ", holds an incomplete creation, and no data. "
                    + "Remove its files and start it again; the start then creates it (bergdb "
                    + "005-33).");
        }
    }
    
    /**
     * Refuses a start with another maximum node size than the database's, and a database
     * whose meta block has none, before recovery writes anything (2026-10-27, bergdb 005-50).
     * The size is in every meta block from the creation on; this reads the last valid one,
     * as recovery does first. Before, a start with another size reran the startup section
     * with it, which splits nodes otherwise, and failed with what looked like a corrupt
     * stream ("node ... not found"); or it started, and the stream it then wrote could not
     * be started again, with either size (bergdb 005-50, question 3). A size above
     * Dag.MAX_NODE_SIZE, 62, is refused as a damaged block (bergdb 024-19, Q6). A user's
     * start has the size 30, the only one of a user's database since bergdb 026-08; the sizes
     * 8, 14 and 62 are for BergDB's own tests (DbBuilder.maxNodeSize8()), and the meta block's
     * field is kept, written and checked, as a hook for a later release that allows others.
     *
     * @throws StreamFormatException
     * @throws VersioningStreamException  no size: a database written before 2026-10-27
     */
    private void refuseOtherNodeSize() {
        MetaBlock last = nodeStream.readLastValidMetaBlock();
        if (last == null) {
            return;     // recover() refuses it.
        }
        final int size = last.getMaxNodeSize();
        if (size == 0) {
            throw new VersioningStreamException("The database's meta block has no maximum node "
                    + "size: it was written by a version of BergDB before 2026-10-27, which "
                    + "this one does not start (bergdb 005-50). The start has written nothing.");
        }
        if (size > Dag.MAX_NODE_SIZE) {
            // No release makes one: 62 is the largest (bergdb 024-19, Q6). A damaged block.
            throw new StreamFormatException("The database's meta block gives the maximum node "
                    + "size " + size + ", above " + Dag.MAX_NODE_SIZE + ", the largest node "
                    + "size of BergDB (bergdb 024-19, Q6): the block is damaged, or the stream "
                    + "is not BergDB's. The start has written nothing.");
        }
        if (size != maxNodeSize) {
            throw new StreamFormatException("The database's maximum node size is " + size
                    + ", and this start uses " + maxNodeSize + ". BergDB makes and starts "
                    + "databases of the node size 30 (bergdb 026-08); the other sizes are for "
                    + "BergDB's own tests, and a database made at one starts only with it. The "
                    + "start has written nothing (bergdb 005-50).");
        }
    }
    
    private void determineDatabaseId() {
        if (databaseIdFromBuilder.isCreateLaterMarker()) {
            databaseId = DatabaseId.createRandom();
        } else {
            databaseId = databaseIdFromBuilder;
        }
    }

    /**
     * Creates the two nodes for the primordial transaction and writes them to
     * the db stream. This is a special case treated as such.
     */
    private void writePrimordialTransaction() {
        //
        // Created node instances should not "leak" from this method.
        // The startup process will create the node instances from the stream.
        // We do not want duplicates. Just append the nodes to stream, 
        // this method should not change the in-memory state.
        //
        
        // transactionBegin() before the try (bergdb 005-18): when it throws, no transaction
        // has begun, and there is none to end.
        long tt = dbClock.transactionBegin(true);
        dbClock.transactionEnd();
        
        // The root's id first, and canonical: the super root's pointer holds the root's
        // handle, and a record names a canonical object's position (bergdb item 009, step
        // 3a; the record rule, Handle.serializedRef).
        KeyNode root = KeyNode.nodeWithTime(tt);
        setIdOfNode(root);
        root.setCanonical(true);
        TopNode superRoot = TopDs.createSuperRootFromFirstKeyNode(tt, root, 
                AccessData.DEFAULT_ACCESS_DATA, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        
        setIdOfNode(superRoot);
        
        MetaBlock meta = nodeStream.getMetaBlock();
        meta.setId(databaseId.getBytes());
        meta.setStartupDistance(startupDistance);
        meta.setMaxNodeSize(maxNodeSize);       // bergdb 005-50
        meta.setTime(tt);
        
        Trans trans = this.trans().build();
        trans.tt = tt;
        trans.isInternal = true;
        trans.startupPos = 0;
        
        TransNodes transNodes = new TransNodes();
        transNodes.addKeyNode(root);
        transNodes.addTopNode(superRoot);
        
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>(), superRoot);
        assert trans.lastPos + 1 == CREATION_LENGTH : "creation length " + (trans.lastPos + 1);
        
        // This is needed to be able to use sync() method.
        x.endOfLastTrans = trans.lastPos + 1;
    }
    
    /** 
     * Writes created.txt if createdTxt parameters has been set in DbBuilder.
     * 
     * @param creationDate  The creation date's text: today's, or "unknown ..." (A+).
     * @param id  The database's ID.
     * @throws StreamIoException 
     */
    private void writeCreatedTxt(String creationDate, DatabaseId id) {
        if (createdTxtDir == null) {
            return;
        }
        
        String keyInfo = createdTxtCryptoKeyInfo == null ? 
                "none (not encrypted)" : createdTxtCryptoKeyInfo;
        
        StringBuilder b = new StringBuilder();
        b.append("This directory contains a BergDB database.\n");
        b.append("\n");
        b.append("creation date: " + creationDate + "\n");
        b.append("created with:  BergDB " + BuildInfo.RELEASE + "\n");
        b.append("database ID:   " + id.idToString() + "\n");
        b.append("crypto key:    " + keyInfo + "\n");
        b.append("\n");
        
        try {
            byte[] stringBytes = b.toString().getBytes("UTF-8");
            Util.bytesToFile(stringBytes, new File(createdTxtDir, "created.txt"));
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
    }
    
    /**
     * Sets node id to next available vpos, also sets node spos to the same vpos.
     * New nodes use the node id (vpos) for the spos value until the first
     * time they are written to stream.
     */
    private void setIdOfNode(Node node) {
        long vpos = x.nextVpos;
        node.setId(vpos);
        node.setSpos(vpos);
        x.increaseNextVpos();
    }
    
    /**
     * The audit (bergdb item 001, WP J1; test-only, auditEvery > 0): at startup, and after
     * every auditEvery-th transaction. The caller holds writeLock, between transactions.
     */
    private void audit(boolean always) {
        if (!always && --auditCountdown > 0) return;
        auditCountdown = auditEvery;
        Audit.record(Audit.check(this), always ? "startup" : "transaction");
    }

    /**
     * Makes a node that a put created the canonical object of its node, in the node
     * table (bergdb 011-04, level 2).
     */
    private void registerNewNode(Node node) {
        node.setCanonical(true);
        cache.register(node);
        cache.tickAccessClock();
    }

    // ======== Marking: step 3 of a transaction ========
    //
    // The index nodes that an operation (one put or delete of the transaction) follows,
    // creates or changes get dirty when the operation ends, and only if it changed something:
    // a delete of a key that does not exist marks nothing. At the end of the transaction, a
    // node that the transaction replaced (Dag.handleFullNode, TopDs.newSuperRoot) is no longer
    // current; if it got dirty in the transaction, it is clean again and leaves D, since its
    // latest version is still good for every earlier time. So step 3 marks exactly the nodes
    // that the Lean model marks: the index nodes current at the transaction time with a node
    // created or changed by the transaction below them (T13 in lean/; bergdb 011-11,
    // M2). Before 2026-10-16, every such node got dirty at once, also on the path of a delete
    // of a missing key and when the transaction replaced the node later. A reclaim step's
    // touch (Level 3, Trans.touch) marks the nodes it visits first, and those marks stay, also
    // for a node that the step's puts then replace; the puts' marks of replaced nodes go, as
    // in any transaction (the Lean model's step 3, touchOf; bergdb item 001, WP R8: M17 in
    // bergdb 001-07). Before 2026-10-17, a touch transaction kept every mark.
    
    /** The index nodes that the current operation followed, created or changed. */
    private final ArrayList<Node> opMarks = new ArrayList<Node>();
    
    /** Whether the current operation changed the Dag. */
    private boolean opChanged = false;
    
    /** The nodes that the current transaction made and took back (bergdb 023-05, P4). */
    private final ArrayList<Node> takenBackInTrans = new ArrayList<Node>();
    
    /** The nodes that the current transaction replaced. */
    private final Set<Node> replacedInTrans = 
            Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
    
    /**
     * The number of nodes that the current transaction's touch made dirty: the first ones of
     * x.transInfo.gotDirtyNodes (0 without a touch).
     */
    private int touchMarks = 0;
    
    private void markAtEndOfOp(Node node) {
        if (x.transInfo == null) return;
        if (node != null && node.isIndexNode()) opMarks.add(node);
    }
    
    /**
     * Makes the nodes of the operation dirty if it changed something, or always.
     */
    private void endOfOp(boolean always) {
        if (always || opChanged) {
            for (Node n : opMarks) makeDirtyIfNeeded(n);
        }
        opMarks.clear();
        opChanged = false;
    }
    
    /**
     * Takes the nodes that the transaction replaced out of the nodes that got dirty in it,
     * but those that its touch made dirty.
     */
    private void endOfTrans() {
        if (!replacedInTrans.isEmpty() && x.transInfo != null) {
            final ArrayList<Node> gotDirty = x.transInfo.gotDirtyNodes;
            final int keep = x.trans.touch ? touchMarks : 0;
            ArrayList<Node> kept = new ArrayList<Node>(gotDirty.size());
            for (int i = 0; i < gotDirty.size(); i++) {
                Node n = gotDirty.get(i);
                if (i >= keep && replacedInTrans.contains(n)) {
                    n.setDirty(false);
                    // Counted with its bytes now: the transaction may have grown its arrays
                    // before it replaced it, and it is not written (bergdb 019-20).
                    cache.residents().grown(n);
                } else {
                    kept.add(n);
                }
            }
            x.transInfo.gotDirtyNodes = kept;
        }
        replacedInTrans.clear();
        touchMarks = 0;
        // Nodes the transaction made and took back (bergdb 023-05, P4, as P2), out of D above,
        // leave the node table: never written, and no node names them.
        for (Node n : takenBackInTrans) {
            cache.dropNode(n);
        }
        takenBackInTrans.clear();
    }

    /**
     * If 'node' is not dirty, it is added to the gotDirty nodes and
     * it dirty flag is set.
     * 
     * @return True if 'node' got dirty.
     */
    private void makeDirtyIfNeeded(final Node node) {
        assert x != null : "x is null";
        
        if (x.transInfo == null) return;
        
        if (!node.isIndexNode()) {
            return;
        }
        
        if (!node.isDirty()) {
            node.setDirty(true);
            x.transInfo.addGotDirtyNode(node);
            if (x.trans.touch) {
                x.trans.dirtiedNodes++;
                x.trans.dirtiedBytes += node.isTopNode() 
                        ? StoredTopNode.getByteSize((TopNode) node)
                        : StoredKeyNode.getByteSize((KeyNode) node);
            }
        }
    }

    /**
     * <p>Stops the database and closes it properly, without waiting (2026-10-24, bergdb
     * 005-35). No transaction or read starts after this method; a transaction that runs
     * completes, and is written. A read that runs can complete, or throw StreamIoException
     * ("Storage is closing.") where a later one throws DbStoppingException (getOne(),
     * getMany()). A thread of its own then writes what is buffered, closes
     * the storage streams and their files, and ends their threads, typically within a
     * second. That thread is not a daemon, so a program that returns from main after stop()
     * still writes all it had. close() waits for it.</p>
     * 
     * <p>Every transaction that has returned is written, as with close(), and with a file
     * storage forced to the device (FileStream forces every append, or with per-append
     * forcing off its last file at its close, bergdb 005-47); only close() waits
     * for that. This method returns at once; if its thread cannot be made or started, as at
     * an OutOfMemoryError, it closes on the calling thread and throws what it met (bergdb
     * 019-39).
     * Call close() to wait for completion and report a failed flush or storage close
     * (bergdb 005-73, F5).
     * It is safe to call it several times and from different threads; only the first call
     * of stop() or close() has an effect.</p>
     * 
     * <p>Start another database on the same directory only after this one is closed, when
     * close() has returned (bergdb 005-63). Until then, a new FileStream on the directory
     * is refused with DirectoryInUseException.</p>
     * 
     * <p>Until 005-35, stop() dropped what was still buffered (all of a quick run's
     * transactions, unless a sync came first), did not wait for a running transaction,
     * and a writer that waited for room in the buffer waited for ever.</p>
     */
    public void stop() {
        // Under readSync, as a failure (setFailed(), bergdb 005-30): no failure comes after it.
        synchronized (readSync) {
            state = DbState.STOPPING;
        }
        synchronized (closeLock) {
            if (closeBegun) {
                return;
            }
            closeBegun = true;
        }
        try {
            Thread closer = new Thread(new Runnable() {
                public void run() {
                    closeStorage(false);
                }
            });
            closer.setName("Db-close-" + closer.getId());
            closer.setDaemon(false);
            Util.start(closer);
        } catch (Throwable e) {
            // No closer, as at an OutOfMemoryError: this thread closes (2026-11-06, bergdb
            // 019-39). closeBegun stayed set with no closer, and close() waited for ever.
            closeStorage(false);
            throw e;
        }
    }
    
    /**
     * Stops the database as stop() does, and waits until it is closed: every transaction
     * that has returned is written, the storage streams and their files are closed, and
     * their threads have ended. Also when stop() or another close() began the close; then
     * it returned at once (2026-10-24, bergdb 005-35, Frans's note "26102424-BUG1-close").
     * Called within a transaction (from an action or a listener, which hold the write
     * lock), it closes the storage at once, as before: a close that another call began
     * waits for that lock. It is safe to call it several times, also after stop(), and from
     * different threads. It is AutoCloseable's close() (bergdb 005-59): a try-with-resources
     * block calls it when the block ends, also when the block throws.
     * A failed final flush or storage close throws StreamIoException, also after stop()
     * or an earlier close() (bergdb 005-73, F5). So does an earlier failure of the storage
     * that no call has reported, such as a failed write of the storage thread while the
     * application made no call (2026-11-05, bergdb 019-09): the transactions that were
     * buffered are lost. A close of a database that has failed (DbFailedException) returns
     * normally, as that failure was reported.
     */
    public void close() {
        // Under readSync, as a failure (setFailed(), bergdb 005-30).
        synchronized (readSync) {
            state = DbState.STOPPING;
        }
        boolean mine;
        synchronized (closeLock) {
            mine = !closeBegun;
            closeBegun = true;
        }
        if (mine) {
            closeStorage(false);
        } else if (Thread.holdsLock(writeLock)) {
            // Waiting for the other closer would deadlock on this transaction's lock.
            final boolean storageFailedBefore = storageManager.hasFailed();
            try {
                storageManager.closeAndThrow();
            } catch (IOException e) {
                if (!reportedBefore(storageFailedBefore, false)) {
                    synchronized (closeLock) {
                        if (closeFailure == null) closeFailure = e;
                    }
                    throw new StreamIoException(e);
                }
            }
        } else {
            waitUntilClosed();
        }
        synchronized (closeLock) {
            if (closeFailure != null) {
                throw new StreamIoException(closeFailure);
            }
        }
    }
        
    /**
     * The one close of the database (2026-10-24, bergdb 005-35), for stop(), close() and a
     * start that throws: takes the write lock, so that a transaction that runs completes and
     * is written (no transaction starts after it, as the state is STOPPING), ends the eviction
     * thread (bergdb 005-51), then closes the storage, which writes what is buffered, closes
     * the streams and ends their threads.
     * 
     * <p>The storage's close fails also when the storage had failed before it, with that
     * failure (StorageManager.closeInner, 2026-11-05, bergdb 019-09), and close() throws it,
     * unless reportedBefore().</p>
     * 
     * @param startThrew  True for the close of a start that threw (closeAfterFailedStart()).
     * @return The first failure of a stream's close, such as a failed flush, or null; null
     *      also when reportedBefore().
     */
    private IOException closeStorage(boolean startThrew) {
        boolean storageFailedBefore = false;
        try {
            synchronized (writeLock) {
                // A transaction that runs has ended.
            }
            // The eviction thread waits with no timeout; it ends now (bergdb 005-51).
            eviction.endThread(!Thread.holdsLock(writeLock));
            storageFailedBefore = storageManager.hasFailed();
            storageManager.closeAndThrow();
            return null;
        } catch (IOException e) {
            if (reportedBefore(storageFailedBefore, startThrew)) {
                return null;
            }
            synchronized (closeLock) {
                if (closeFailure == null) closeFailure = e;
            }
            return e;
        } finally {
            synchronized (closeLock) {
                closeDone = true;
                closeLock.notifyAll();
            }
        }
    }
            
    /**
     * True when close() does not throw the close's failure, as a call has reported it
     * (2026-11-05, bergdb 019-09, Frans's option (a)): the storage had failed before its
     * close, and the database had failed before it stopped (the state FAILED, which stop()
     * and close() then set to STOPPING; 'failure' is set only while the state is ACTIVE, by
     * setFailed()), so a call threw DbFailedException; or the start threw. Otherwise,
     * close() is the one call left to report the failure, such as a failed write of the
     * storage thread with no call of the application on the storage (010-01, P7). A failure
     * of the close itself, such as a failed final flush, is thrown as before (bergdb 005-73,
     * F5).
     */
    private boolean reportedBefore(boolean storageFailedBefore, boolean startThrew) {
        return storageFailedBefore && (startThrew || failure != null);
    }
    
    /** Waits, without being interrupted, until closeStorage() is done (bergdb 005-35). */
    private void waitUntilClosed() {
        boolean interrupted = false;
        synchronized (closeLock) {
            while (!closeDone) {
                try {
                    closeLock.wait();
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }
    }
    
    /**
     * Prints the in memory part of the dag. Useful for test and
     * development.
     * 
     * @throws IllegalArgumentException  If out is null (bergdb 020-27, Q2).
     */
    public void printDag(PrintStream out) {
        if (out == null) {
            throw new IllegalArgumentException("out == null not allowed");
        }
        assertDbStateIsActive("printDag");
        dag.printGraph(out);
    }
    
    /**
     * Before the startup has made the Dag (not started, or a start that threw and stopped the
     * database, bergdb 005-32), refuses the call as a read is refused, instead of a
     * NullPointerException.
     */
    private void assertHasDag(String methodName) {
        if (dag == null) {
            synchronized (readSync) {}
            assertDbStateIsActive(methodName);
        }
    }
    
    /**
     * Creates and returns a new GetData object for use with the getOne() method.
     */
    public GetData newGetData() {
        assert this.nodeCollection != null : "Db.nodeCollection is null";
        assertHasDag("newGetData");
        GetData gd = dag.newGetData();
        gd.pointerFollower = this.nodeCollection;
        return gd;
    }
    
    /**
     * Creates and returns a new GetMany object for use with the getMany() method.
     */
    public GetMany newGetMany() {
        assertHasDag("newGetMany");
        GetMany g = dag.newGetMany();
        g.gd.pointerFollower = this.nodeCollection;
        final TestHooks hooks = testHooks;
        if (hooks != null) {
            hooks.getManyCreated(g);
        }
        return g;
    }

    /**
     * Gets a value given an exact match with a key. This is the primary and fastest 
     * GET method with no memory allocation.
     * The array returned is the database's own when the value is in memory: the caller
     * must not change it. The Pub API returns it too, for a byte[] (bergdb 015-47).
     * 
     * @param lookupTime
     *            The requested lookup time. The time for which to make the lookup. 
     *            Use Long.MAX_VALUE to lookup the state at the latest possible time.
     * @param keySegments
     *            The key, as segments: Keys.toSegments() of its bytes ("Keys and values"
     *            above).
     * @param gd
     *            A GetData from newGetData(), for one thread at a time; it may be used
     *            again. After the call, its actualLookupTime is the time of the state read
     *            ("Threads" above), and for a value found, its tpos is the position of the
     *            transaction that wrote the value, which getTrans() reads; for a value that
     *            reclaim has copied forward, reclaim's (see getTrans()).
     * @return The value, or null if the key has no value at the lookup time.
     * @throws IllegalArgumentException
     *             If keySegments or gd is null, or keySegments has no segment (bergdb
     *             020-27, Q2).
     * @throws IllegalDbStateException
     *             If start() has not been called, or stop() or close() has (a
     *             DbStoppingException then).
     *             The database is not in the active state.
     * @throws DbFailedException
     *             If the database has failed, or fails now: the read failed on the storage
     *             (an I/O error, corrupt data; the cause; bergdb 005-30).
     * @throws Error
     *             As it is, such as an OutOfMemoryError: the database fails (bergdb 019-10;
     *             "Errors" above).
     * @throws LookupTimeNotAvailableException
     *             If the lookup time is before the first available lookup time, also when
     *             a cut has overtaken the read.
     * @throws StreamFormatException
     *             If the database stream is corrupt, while the database is stopping.
     * @throws StreamIoException
     *             If the database is stopping: a read that runs when stop() or close() is
     *             called can meet the storage as it closes and throw this, such as "Storage
     *             is closing.", where a read that begins after the call throws
     *             DbStoppingException; the database has not failed (bergdb 020-24-09,
     *             U9-14), and an I/O error of a read while it stops is thrown so too. While
     *             the database is active, an I/O error is a DbFailedException, with the
     *             StreamIoException as its cause.
     */
    public byte[] getOne(long lookupTime, long[] keySegments, GetData gd) {
        // A null argument refused (bergdb 020-27, Q2): it threw NullPointerException, a null gd
        // an AssertionError with -ea.
        if (keySegments == null) {
            throw new IllegalArgumentException("keySegments == null not allowed");
        }
        if (gd == null) {
            throw new IllegalArgumentException("gd == null not allowed");
        }
        if (keySegments.length == 0) {
            // As a put of it (Trans.Builder); it gave null.
            throw new IllegalArgumentException("keySegments.length == 0 not allowed: a key has "
                    + "one segment at least (Keys.toSegments()).");
        }
        assert gd.kwi != null;
        
        // Publication (bergdb item 009, step 1c): the read of the volatile state above, then
        // in getOneInternal the volatile first available lookup time and the clock's volatile
        // last transaction time, read before the Dag, give this read the writes of startup and
        // of the transactions before its lookup time. Until 2026-10-25 an empty
        // synchronized (readSync) block here did, a write of the monitor's word by every get.
        try {
            assertDbStateIsActive("getOne");
            return getOneInternal(lookupTime, keySegments, gd);
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    /**
     * Reads the transaction at stream position 'tpos', a caller's position: the transaction
     * of a value that a get read (GetData.tpos), or Trans.tpos after execute(). 'tpos' must
     * be the position of a transaction; any other is the caller's mistake, refused with
     * IllegalArgumentException, and the database goes on (bergdb 021-27; 010-04, R5). The
     * Pub API's Connection.transactionInfo() reads with Internal.getTrans(), which takes the
     * position as the database's own, so that a record there that is not a committed
     * transaction is damage.
     * A get can give the position of a record that the writer has not yet appended in
     * whole, as the writer sets the positions of a record's nodes before it appends it; the
     * call then waits for the writer, until the record is in the stream (bergdb 021-13).
     * 
     * <p>The StoredTrans gives the transaction's time (tt), its positions (tpos, lastPos)
     * and, by getValueNodes(), its puts and deletes, a StoredValueNode each, with its key
     * (bergdb 020-24-09, U9-9). A delete of a key that had no value at the transaction's
     * time stores nothing and is not listed, as the Pub API's TransactionInfo leaves it out.
     * A value that reclaim has copied forward (setRetainDuration()) is read from reclaim's
     * step, so that a get's tpos is the step's: a transaction of reclaim's, whose value nodes
     * are the values that it copied, each with its key, and reclaim's own keys under
     * "/#i/dreclaim/" (Keys and the layers above). The transaction that wrote the value is
     * found by a get of the key at the step's time less one unit, which gives the value as
     * the step read it and that value's tpos, again a step's if reclaim had copied it before,
     * as the Pub API's Connection.transactionInfo() does (bergdb 021-17); while that time is
     * not before getFirstAvailableLookupTime().</p>
     *
     * @throws IllegalArgumentException
     *             If 'tpos' cannot start a transaction: negative (Spos.NULL from a get: the
     *             value's transaction was still being stored), not a multiple of 8, in a
     *             meta block (bergdb 005-34), or at or past the end of the stream (bergdb
     *             005-43). Nothing is read. Since 2026-11-12 (bergdb 021-27) also if the
     *             bytes at 'tpos' are not a committed transaction's record: a bad size,
     *             version byte or last byte, a record not committed, a node whose checksum
     *             fails, a malformed node; the read's StreamFormatException is the cause, and
     *             the database goes on. Such a position is in general one inside a record,
     *             not at its start. The position is the caller's, so it is not taken for
     *             damage, as it was (the database failed); damage at a transaction's position
     *             is refused so too. Nothing tells a position inside a record from a record's
     *             start: one inside a record whose bytes there happen to form a well-formed
     *             committed record (a value can hold such bytes) gives a StoredTrans of
     *             them, of no real transaction. The position is the caller's responsibility.
     *             A size over 1 MiB in the header at 'tpos' is believed only after the
     *             records' sizes, walked from the meta block at or before 'tpos', reach
     *             'tpos', before the record is read (bergdb 021-27, Q27-1): inside a record
     *             it is refused so, with no array made of that size.
     * @throws DbFailedException
     *             If the database has failed, or fails now: the read failed on the storage
     *             (an I/O error, the environment's; bergdb 010-01, P7); the cause is the
     *             read's exception.
     * @throws Error
     *             As it is, such as an OutOfMemoryError: the database fails (bergdb 019-10;
     *             "Errors" above).
     * @throws LookupTimeNotAvailableException
     *             If reclaim has removed the transaction: the time of the get has expired.
     */
    public StoredTrans getTrans(long tpos) {
        try {
            return getTransInner(tpos, false);
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    /**
     * getTrans() and Internal.getTrans(): 'own' if the position is the database's own, from
     * a get (GetData.tpos), so that a record there that is not a committed transaction is
     * damage and fails the database (bergdb 005-30, 005-34, 005-82); a caller's position is
     * refused instead (bergdb 021-27).
     */
    private StoredTrans getTransInner(long tpos, boolean own) {
        // Refused before it reads (2026-10-24, bergdb 005-34): it would read the middle of a
        // record as a transaction.
        final long inBlock = tpos % RecoverableStream.META_BLOCK_DISTANCE;
        if (tpos < 0 || tpos % NodeStream.TRANS_ALIGNMENT != 0 
                || inBlock < RecoverableStream.META_BLOCK_SIZE) {
            throw new IllegalArgumentException("Not a position of a transaction, " + tpos + ".");
        }
        
        // A record that the writer has not appended in whole waits for the writer (2026-11-09,
        // bergdb 021-13). A get gives a value's position as soon as the writer has set the
        // positions of the record's nodes, before it appends the record, which can take
        // several appends (a meta block in the record) and wait for room in the storage's
        // buffer. The read found none of the record, at or past the end of the stream, and
        // threw IllegalArgumentException; or a part of it, whose size went beyond the
        // stream's length: a StreamFormatException, which failed the database. The writer
        // appends the record under writeLock, so after the lock it is in the stream in whole,
        // or the database has failed, which the state check below finds. Only a position at or
        // after the end of the records appended in whole waits, a bad one too (refused after
        // it as before); the wait is for the rest of the writer's transaction.
        if (tpos >= nodeStream.getAppendedEnd()) {
            synchronized (writeLock) {}
        }
        
        // The state checked since bergdb 005-30 (it read on after a failure). Publication: the
        // volatile state, as in getOne (bergdb item 009, step 1c; an empty synchronized
        // (readSync) block until 2026-10-25).
        assertDbStateIsActive("getTrans");

        // A caller's position: a large size there is believed only at a record's start
        // (bergdb 021-27, Q27-1).
        NodeStream.TransIterator ti = own
                ? nodeStream.createTransIteratorFromExactStartupPos(tpos)
                : nodeStream.createTransIteratorAtCallersPos(tpos);
        StoredTrans stored = null;
        try {
            // The parse within the try since 2026-11-03 (bergdb 005-82): it came after it, and
            // its exception, a node's checksum or a malformed record, escaped as it was, with
            // the database still active. Only next() reads the stream.
            if (ti.next()) {
                stored = parseTrans(ti, tpos);
            }
        } catch (StreamIoException e) {
            if (isReadBelowCut(e)) {
                LookupTimeNotAvailableException ex = new LookupTimeNotAvailableException(
                        "The transaction at stream pos " + tpos + " is no longer available: "
                        + "reclaim has removed it.");
                ex.initCause(e);
                throw ex;
            }
            throw failOnStorage(e, "A read");
        } catch (StreamFormatException e) {
            // Corrupt data, as for the other reads (2026-10-24, bergdb 005-34): it was thrown
            // as it was, as the Pub API's position was wrong for a value after a meta block in
            // its record, and for a value that startup had rerun. And the parse's, since
            // bergdb 005-82. For a position the database has given only (bergdb 021-27): a
            // caller's position, such as one inside a record, failed the database (the C
            // port's black-box user, 022, U2-4). Frans, 2026-11-12: a read "should fail or
            // succeed, but never block the database"; the position "comes from the user and
            // cannot be fully trusted" (010-04, R5).
            if (own) {
                throw failOnStorage(e, "A read");
            }
            throw new IllegalArgumentException("Not a position of a transaction, " + tpos
                    + ": the bytes there are not a committed transaction's record (the cause).",
                    e);
        }
        if (stored == null) {
            // At or past the end of the stream, refused as the positions above are (2026-10-25,
            // bergdb 005-43). It was a DbException.
            throw new IllegalArgumentException("Not a position of a transaction, " + tpos
                    + ": at or past the end of the stream.");
        }
        
        return stored;
    }
    
    /**
     * Parses the record that 'ti' has read, for getTrans() (2026-11-03, bergdb 005-82). A
     * StreamFormatException is thrown as it is. Any other RuntimeException means a malformed
     * record too, or a bug: it becomes a StreamFormatException with it as the cause, so that
     * getTrans() fails the database (bergdb 010-01, P7). Since bergdb 015-07 the node parsers
     * check their fields against the node's size, so that no malformed node is known to come
     * here; before, a node whose checksum was right but whose value size was -1 did
     * (DbTesterFailure.testParseTransWraps). The parse reads only the record's bytes, not the
     * stream. Package-private for that test.
     */
    static StoredTrans parseTrans(NodeStream.TransIterator ti, long tpos) {
        try {
            return ti.getStoredTrans();
        } catch (StreamFormatException e) {
            throw e;
        } catch (RuntimeException e) {
            throw new StreamFormatException("A malformed record at stream pos " + tpos
                    + ": its parse threw " + e + ".", e);
        }
    }
    
    
    /**
     * The warm-up's read: no edge and no state check, so not public (bergdb 019-40); the
     * package's, as item 004's ScaleBench and IndexCensus call it.
     */
    byte[] getOneInternal(long lookupTime, long[] keySegments, GetData gd) {
        //
        // Few assumptions of previous state of gd are assumed. db.kwi must be non-null, however.
        //
        
        long firstAvailable = reclaim.getFirstAvailableLookupTime();
        if (lookupTime < firstAvailable) {
            String lookupTimeString = DbUtil.dbTimeToUtc(lookupTime);
            String firstTimeString = DbUtil.dbTimeToUtc(firstAvailable);
            throw new LookupTimeNotAvailableException("Cannot lookup at time " + lookupTime 
                    + " (" + lookupTimeString 
                    + "): the first time available for lookup is " 
                    + firstAvailable + " (" + firstTimeString + ").");
        }

        gd.accessData = getAccessData();

        byte[] result = null;

        // Limits lookup time so it is strictly less than the transaction time of
        // any running or future transaction.
        long time = dbClock.lookupTime(lookupTime);
        
        gd.actualLookupTime = time;
        gd.nodeDepth = 0;

        try {
            result = dag.getOne(gd.actualLookupTime, keySegments, gd);
        } catch (StreamException e) {
            throw readFailed(e, time);
        }

        aux.getOpCount.increment();
        return result;
    }

    /**
     * Get multiple KVs in increasing or decreasing key order: the unsigned order of the keys'
     * bytes ("Keys and values" above), at the state of g's lookup time ("Threads" above).
     * 
     * @param g     Input and output parameters: a new GetMany, from newGetMany(), for each
     *              call (GetMany).
     * @throws IllegalArgumentException
     *              If g or its stopCondition is null, its startKey has no segment, its
     *              result is not empty, its endKey is set for a backward scan (bergdb
     *              021-28), or its stop condition answers a value other than the four of
     *              StopCondition, which ends the scan (bergdb 020-27, Q2).
     * @throws IllegalDbStateException
     *              If start() has not been called, or stop() or close() has (a
     *              DbStoppingException then).
     * @throws DbFailedException
     *              If the database has failed, or fails now: the read failed on the
     *              storage (an I/O error, corrupt data; the cause; bergdb 005-30).
     * @throws Error
     *              As it is, such as an OutOfMemoryError, also one of g's StopCondition:
     *              the database fails (bergdb 019-10; "Errors" above).
     * @throws LookupTimeNotAvailableException
     *              If the lookup time is before the first available lookup time, also
     *              when a cut has overtaken the read.
     * @throws StreamFormatException
     *              If the database stream is corrupt, while the database is stopping.
     * @throws StreamIoException
     *              If the database is stopping: a read that runs when stop() or close() is
     *              called can meet the storage as it closes and throw this, such as
     *              "Storage is closing.", where a read that begins after the call throws
     *              DbStoppingException; the database has not failed (bergdb 020-24-09,
     *              U9-14), and an I/O error of a read while it stops is thrown so too.
     *              While the database is active, an I/O error is a DbFailedException, with
     *              the StreamIoException as its cause.
     * @see GetMany
     */
    public void getMany(GetMany g) {
        // Note, multiple get operations may be running in parallel.
        // All data used must be thread safe. 
        // Operation-local data is stored in the 'g' object.
        //

        // A null refused (bergdb 020-27, Q2): it threw NullPointerException, a null stop
        // condition an AssertionError with -ea.
        if (g == null) {
            throw new IllegalArgumentException("g == null not allowed");
        }
        if (g.stopCondition == null) {
            throw new IllegalArgumentException("g.stopCondition == null not allowed");
        }
        // Asserts until bergdb 020-27, Q2, range checks. A startKey of no segments: with -ea an
        // AssertionError of GetMany.Chain failed the database, without -ea no KV. A result not
        // empty: without -ea the KVs were added to it.
        if (g.startKey != null && g.startKey.length == 0) {
            throw new IllegalArgumentException("g.startKey.length == 0 not allowed: a key has "
                    + "one segment at least; null starts at the first key.");
        }
        if (g.result.size() != 0) {
            throw new IllegalArgumentException("g.result not empty, " + g.result.size()
                    + " KVs: clear it, or use a new GetMany (newGetMany()).");
        }
        if (g.endKey != null && !g.forward) {
            throw new IllegalArgumentException("g.endKey with a backward scan: the end is for "
                    + "forward scans only (bergdb 021-28).");
        }

        try {
            getManyInner(g);
        } catch (Error e) {
            throw failed(e);        // Also one of the caller's StopCondition (bergdb 019-10).
        }
    }
    
    private void getManyInner(GetMany g) {
        // Publication: as in getOne (bergdb item 009, step 1c; an empty synchronized (readSync)
        // block until 2026-10-25).
        assertDbStateIsActive("getMany");
        
        long first = reclaim.getFirstAvailableLookupTime();
        if (g.lookupTime < first) {
            String lookupTimeString = DbUtil.dbTimeToUtc(g.lookupTime);
            String firstString = DbUtil.dbTimeToUtc(first);
            throw new LookupTimeNotAvailableException("Cannot lookup at time " + g.lookupTime 
                    + " (" + lookupTimeString 
                    + "): the first time available for lookup is " 
                    + first + " (" + firstString + ").");
        }
        
        g.gd.accessData = getAccessData();
        
        g.actualLookupTime = dbClock.lookupTime(g.lookupTime);
            // Limits lookup time so it strictly less than the transaction time of
            // any currently running or any future transaction.

        try {
            dag.getMany(g);
        } catch (StreamException e) {
            throw readFailed(e, g.actualLookupTime);
        }
        
        aux.getOpCount.add(g.getOpCount);
    }
    
    /**
     * Decides whether a failed read has expired. A read that was admitted before reclaim
     * moved the first available lookup time can still reach bytes that the cut then removed
     * (bergdb 011-04, W1, decision D1 = A: such a read may expire). If the stream
     * says the bytes are before its first position and the lookup time is now before the
     * first available lookup time, the read has expired: the caller gets a
     * LookupTimeNotAvailableException, as if it had asked a moment later. Anything else is
     * a real failure and is returned unchanged; it fails the database (readFailed()).
     *
     * <p>'lookupTime' is the actual lookup time, the snapshot the read uses (see
     * DbClock.lookupTime()), not the requested one: a read of the latest state, Long.MAX_VALUE,
     * reads the state at the time of the last transaction, and that snapshot expires when a
     * cut overtakes it (ReclaimReaderTester.testLatestReaderExpiresWhenCutOvertakesIt).</p>
     */
    private RuntimeException expiredIfReadBelowCut(StreamException e, long lookupTime) {
        if (isReadBelowCut(e)) {
            synchronized (readSync) {}      // Publishes the first available lookup time.
            long first = reclaim.getFirstAvailableLookupTime();
            if (lookupTime < first) {
                LookupTimeNotAvailableException ex = new LookupTimeNotAvailableException(
                        "The lookup at time " + lookupTime + " (" + DbUtil.dbTimeToUtc(lookupTime)
                        + ") expired while it ran: the first time available for lookup is now "
                        + first + " (" + DbUtil.dbTimeToUtc(first) + "). Retry with a later time.");
                ex.initCause(e);
                return ex;
            }
        }
        return e;
    }

    /** True if 'e' comes from a read of bytes before the first position of the stream. */
    private static boolean isReadBelowCut(Throwable e) {
        for (Throwable t = e; t != null; t = t.getCause()) {
            if (t instanceof ReadBelowFirstPosException) {
                return true;
            }
            if (t.getCause() == t) {
                break;
            }
        }
        return false;
    }

    /**
     * Decides what a read that failed on the stream throws (bergdb 005-30). A read that a
     * cut has overtaken expires (expiredIfReadBelowCut()), and the database goes on. Any
     * other failure fails the database (failOnStorage()).
     */
    private RuntimeException readFailed(StreamException e, long lookupTime) {
        final RuntimeException expired = expiredIfReadBelowCut(e, lookupTime);
        return expired != e ? expired : failOnStorage(e, "A read");
    }

    /**
     * As sync(0, syncLevel): waits until the last transaction written is durable.
     *
     * @param syncLevel
     *      The sync level; SyncLevel.NONE returns at once.
     * @throws IllegalArgumentException
     *      If syncLevel is null.
     */
    public void sync(SyncLevel syncLevel) {
        sync(0, syncLevel);
    }
    
    /**
     * Waits until the stream is durable up to 'pos', at the given sync level.
     *
     * @param pos
     *      The stream position of the last byte to make durable, a transaction's lastPos, or
     *      0 for the last transaction written. The sync returns when every byte up to and
     *      including it is durable (2026-10-25, bergdb 005-44: it returned when the bytes
     *      before it were, so the transaction's last byte, its commit byte, could still be in
     *      the write buffer, and a crash then lost the transaction).
     * @param syncLevel
     *      The sync level; SyncLevel.NONE returns at once.
     * @throws IllegalArgumentException
     *      If syncLevel is null.
     * @throws DbFailedException
     *      If the storage has failed (the cause): the database fails, as on a read that
     *      fails on the storage (bergdb 005-30). After another failure, a sync of the
     *      transactions before it still works while the storage does.
     * @throws Error
     *      As it is, such as an OutOfMemoryError: the database fails (bergdb 019-10; "Errors"
     *      above).
     * @throws StreamIoException
     *      If the thread was interrupted while it waited, or the database is stopping.
     */
    public void sync(long pos, SyncLevel syncLevel) {
        if (syncLevel == null) {
            throw new IllegalArgumentException("syncLevel == null not allowed");
        }
        
        if (syncLevel == SyncLevel.NONE) {
            return;
        }
        
        // The durable length to wait for: the bytes before it are durable (bergdb 005-44).
        final long length;
        if (pos == 0) {
            synchronized (writeLock) {
                length = x.endOfLastTrans;
            }
        } else {
            length = pos + 1;
        }
        
        switch (syncLevel) {
        case ORDINARY:
            try {
                storageManager.sync(length);
            } catch (InterruptedIOException e) {
                // Not a failure of the storage (bergdb 005-30).
                throw new StreamIoException(e);
            } catch (IOException e) {
                throw failOnStorage(new StreamIoException(e), "A sync");
            } catch (Error e) {
                throw failed(e);
            }
            break;
        
        default:
            throw new Bug("never happens, " + syncLevel);
        }
    }
    
    /**
     * This method visits all nodes in memory to check that the state is consistent.
     * This method locks on both writeLock and readSynch. Use for testing only.
     */
    public void checkNodes() throws AssertionError {
        synchronized (writeLock) {
            synchronized (readSync) {
                checkNodeInner();
            }
        }
    }
    
    private void checkNodeInner() throws AssertionError {
        final long[] counters = new long[4];
            // top, key, value, dirty, total
        
        NodeVisitor visitor = new NodeVisitor() {
            public void visit(TopNode node) {
                counters[0]++;
            }

            public void visit(KeyNode node) {
                counters[1]++;
                node.check();    // throws AssertionError if bad.
            }

            public void visit(ValueNode node) {
                counters[2]++;
            }
        };
        
        dag.visitMemoryNodes(visitor);
    }
    
    /**
     * Same as "execute(b.build())"; AVOID using this method.
     * 
     * @throws IllegalArgumentException  If b is null (bergdb 020-27, Q2).
     * @throws IllegalStateException  If b is spoiled: a call of it was refused, and nothing
     *      is written (Trans.Builder; bergdb 024-26, U26-5).
     */
    public final void execute(Trans.Builder b) {
        if (b == null) {
            throw new IllegalArgumentException("b == null not allowed");
        }
        //
        // This little method does not comply with the Minimal Core Layer rule.
        // Should be be avoided, but is currently (2015-08) called from 90 places.
        //
        execute(b.build());
    }

    /**
     * Executes a transaction using the STM approach. 
     * Assumption: t.kvs is sorted.
     * 
     * <p>Everything that may refuse the transaction is checked before its go point, and
     * nothing changes before it: a refused transaction leaves the database as it was, and
     * the database goes on. After the go point nothing refuses the transaction and nothing
     * is undone. An exception there means that the storage, the JVM or memory failed, or a
     * bug, and the database fails (bergdb 005-01): it refuses every later transaction and
     * read with a DbFailedException until it is restarted. The restart rebuilds it from the
     * stream, which holds whole records only, as after a crash. stop(), close() and sync()
     * still work. A read that fails on the storage, such as one of the warm-up before the
     * go point, fails the database too (bergdb 005-30), and so does an Error anywhere in the
     * call (bergdb 019-10; "Errors" above).</p>
     * 
     * @throws IllegalArgumentException
     *             If t is null (bergdb 020-27, Q2).
     * @throws IllegalDbStateException
     *             If start() has not been called or database is stopping.
     * @throws DbFailedException
     *             If the database has failed: this transaction threw after its go point, or
     *             a read of its warm-up failed on the storage (the cause), or the database
     *             failed before (the cause is the first failure). Whether this transaction
     *             is in the stream is known after the restart.
     * @throws Error
     *             As it is, such as an OutOfMemoryError, before the go point too: the
     *             database fails (bergdb 019-10; "Errors" above).
     * @throws RerunException
     *             Thrown if the transaction was cancelled and should be rerun
     *             because one or more KVs with a key in the read key hash set,
     *             were changed after the read time of the transaction; 
     *             the STM approach.
     *             Also if the read time is outside the STM's retained coverage, including
     *             before the last recovered commit at startup (bergdb 005-70, option A).
     * @throws StreamFormatException
     *             If the database stream is corrupt, while the database is stopping; else
     *             the cause of a DbFailedException.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream, while the database is
     *             stopping; else the cause of a DbFailedException.
     * @throws InternalDataException
     *             If BergDB internal data in the database is corrupt.
     * @throws DbException
     *             If the transaction is refused before its go point, and the database goes
     *             on: it passes a limit of "Limits" above, its operations (L1), its keys'
     *             bytes (L3) or its keys' and values' bytes (L5), or a key transformation
     *             gives a key over L2 or the keys over L3 (bergdb 024-17, 024-24), or throws
     *             a RuntimeException (the cause; bergdb 026-06); a value
     *             transformation throws a RuntimeException (the cause), or gives a value over
     *             L4, or values that take the transaction over L5 or 005-17's size, and its
     *             KVs are left as they were (bergdb 026-06; ValueTransformation); a KV is at
     *             a key that the Core writes itself, as written (putLongKey(), deleteLongKey())
     *             or as a key transformation gave it ("The Core's own keys are refused";
     *             bergdb 024-37); it is too
     *             large for a record (bergdb 005-17), or its dirty index nodes would not fit
     *             in one record (005-31); its key transformations make two of its keys one
     *             key, and its KVs are left as they were (bergdb 024-16; Trans.Builder); the
     *             clock's time is out of range (005-18), or in the last 1,024 database
     *             times, kept for reclaim (015-55); or the database has used its top node
     *             ordinals, after about 2^48 changes of the space root, and then every later
     *             transaction is refused too; reads go on (bergdb item 005-02).
     */
    public final void execute(final Trans t) {
        //
        // Executes a KV set request as an ACID transaction.
        //
        // We make sure all readers have a read time that is strictly less than
        // t.transTime while the synchronized(writeLock) clause is executing. 
        // This is handled by dbClock.
        //

        if (t == null) {
            // Before the state (bergdb 020-27, Q2): it threw NullPointerException.
            throw new IllegalArgumentException("t == null not allowed");
        }

        // Makes sure writes from startup and previous execute() calls are visible.
        // We do not hold DB.writeLock yet.
        synchronized (readSync) {}

        try {
            assertDbStateIsActive("execute");
            executeInner(t);
        } catch (Error e) {
            throw failed(e);        // Also before the go point (bergdb 019-10).
        }
    }

    private void assertDbStateIsActive(String methodName) {
        DbState myState = state;
        if (myState == DbState.ACTIVE && storageManager.hasFailed()) {
            // 2026-11-05 (bergdb 015-35): the storage failed with no call of ours on it, as a
            // write of its thread (BufferedStream), and the database fails now (010-01, P7).
            // It stayed active, and gets served from memory went on, until a transaction, a
            // sync or a load met the failure.
            setFailed(new StreamIoException(storageManager.getFailure()));
            myState = state;
        }
        if (myState != DbState.ACTIVE) {
            if (myState == DbState.STOPPING) {
                throw new DbStoppingException("Cannot call " + methodName + "() while DB is stopping.");
            } else if (myState == DbState.FAILED) {
                throw new DbFailedException("Cannot call " + methodName + "(): the database "
                        + "failed (the cause) and must be restarted.", failure);
            } else {
                throw new IllegalDbStateException("Cannot call " + methodName + "() when DB state is " 
                        + myState + ".");
            }
        }
    }
    
    /**
     * The top node ordinals below the bound, TopNode.MAX_TOP_NODE_ID_VALUE, that are left
     * when user transactions are refused (bergdb item 005-02): room for the internal
     * transactions that run after a user transaction, reclaim's, at most five today.
     */
    private static final long TOP_ORDINAL_MARGIN = 1024;
    
    /** The super root's ordinal from which user transactions are refused. */
    static final long LAST_TOP_ORDINAL = TopNode.MAX_TOP_NODE_ID_VALUE - TOP_ORDINAL_MARGIN;
    
    /**
     * Refuses a user transaction, or a call of a setter that commits reclaim's settings
     * (bergdb 015-87), once the top node ordinals are used up to LAST_TOP_ORDINAL. The
     * caller holds the write lock.
     * 
     * @throws DbException
     */
    void refuseIfTopOrdinalsUsed() {
        if (dag.getTopDs().getSuperRoot().topNodeId >= LAST_TOP_ORDINAL) {
            throw new DbException("The database has used its top node ordinals (up to "
                    + LAST_TOP_ORDINAL + "); it takes no more transactions.");
        }
    }
    
    /**
     * Executes a transaction; this is the heart of the transaction handling.
     * 
     * <p>The go point (bergdb 005-01, register M49; Frans's design, from 2008: no rollback,
     * check first). Everything that may refuse the transaction is checked before it, and
     * nothing is changed before it. After it, the transaction runs to its end without an
     * exception as long as the storage, the JVM and memory work. If one of them fails, or a
     * bug throws, nothing is undone: the database fails (fail()) and must be restarted.</p>
     * 
     * @throws RerunException
     * @throws DbFailedException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException
     */
    private void executeInner(Trans t) {
        //
        // We make sure all readers have a read time that is strictly less than
        // t.time while the synchronized(writeLock) clause is executing.
        // This is handled by dbClock.
        //
        
        if (!t.isInternal()) {
            checkSize(t);
        }
        t.warmupGetData.pointerFollower = x.getData.pointerFollower;
        warmup(t);
        final Before before = new Before(t.tt);     // a refusal gives it back (giveBack)
        
        writersWaiting.incrementAndGet();
        synchronized (writeLock) {
            writersWaiting.decrementAndGet();
            try {
                // Again under the lock (bergdb 005-01): a writer that waited for the lock while
                // another one failed must not run on what the failed one left in memory.
                assertDbStateIsActive("execute");
            
                // The end of the top node ordinals (bergdb item 005-02, register M46): checked
                // before the transaction changes anything. A transaction makes at most one top
                // node, and reclaim's internal transactions run only after a user transaction,
                // within the margin, or at a call of a setter of reclaim's settings, which
                // Reclaim.setSettings refuses before it as this refuses a user transaction
                // (refuseIfTopOrdinalsUsed; bergdb 015-87); so no transaction reaches the bound,
                // where TopNode throws.
                // A database that ends here can still be read and restarted.
                if (!t.isInternal()) {
                    refuseIfTopOrdinalsUsed();
                }
                if (!t.isInternal()) {
                    checkDirtyNodes(t);
                }
                x.begin(t);
            
                stmCheckConflicts(t);

                // transactionBegin() refuses a clock out of range (bergdb 005-18), and a user
                // transaction in the times kept for reclaim's internal transactions after it
                // (bergdb 015-55); before the try, so that nothing has begun or changed when it
                // throws.
                t.tt = dbClock.transactionBegin(!t.isInternal());
            } catch (Error e) {
                // Recorded before the lock is released, as fail() does after the go point
                // (bergdb 019-40): a writer that waits for the lock then finds the database
                // failed.
                throw failed(e);
            }
            
            // The key transformations, at t.tt, and the refusal of a transaction that they
            // leave with two KVs at one key (bergdb 024-16): before the go point, so that the
            // refusal leaves everything as it was. Until 024-16 they ran in putKvs().
            final Kv[] kvs = transformKeys(t, before);
            
            // The value transformations of a user transaction, at t.tt, and the refusal of one
            // that throws or whose values pass the limits (bergdb 026-06; 010-04, R5): before
            // the go point too. Until 026-06 they ran in putKvs(), where that failed the
            // database. Reclaim's row stays there (transformValues()).
            if (!t.isInternal()) {
                transformValues(t, kvs, before);
            }
            
            // The go point. From here nothing refuses the transaction and nothing is undone:
            // whatever throws fails the database (bergdb 005-01).
            try {
                putKvs(kvs);

                // The synch statement below publishes the changes by the writer thread 
                // (the thread executing this code) to the readers. This is done
                // before the t.tt can be used as lookup time, so all readers
                // (that do: "synchronized (readSynch) {}") are guaranteed to see all 
                // in-memory changes made by the writer.
                synchronized (readSync) {}
                
                // After the call to dbClock.transactionEnd(), read operations may use
                // t.tt as a lookup time. Not in a finally since bergdb 005-01: when putKvs()
                // throws, t.tt never becomes a lookup time, and a read that comes in before
                // the database is seen as failed reads the state before the transaction.
                dbClock.transactionEnd();
                
                stmRecordKeys(t);

                store(); 
                
                aux.updateStats();
                
                x.startupPos.releaseForEvict();
                
                x.trans.listener.transExecuted(x);
                final TestHooks hooks = testHooks;
                if (hooks != null) {
                    hooks.transExecuted(x);
                }
                
                x.end();
                
                eviction.afterTransaction(this);
                if (auditEvery > 0) audit(false);

                // The synch statement guarantees that the writes are visible to all readers 
                // assuming they also do [synchronized(readSync) {}] before they start reading.
                synchronized (readSync) {}
                
                // 1301 Frans. The below line moved to inside the synchronized (writeLock) block 
                // to KISS the reclaim stuff. However, fundamentally, it does not have to 
                // belong to the block.
                try {
                    reclaimTransactionListener.transactionCompleted(t);    
                } catch (DbStoppingException e) {
                    // stop() or close() came during reclaim's work for this transaction
                    // (bergdb 015-53). Reclaim's reads and internal transactions are refused
                    // at their entry, an internal transaction before its go point, so none is
                    // half written. This transaction is committed (its record is appended, and
                    // the close writes it), so the call returns, as stop()'s Javadoc says;
                    // reclaim's work goes on at the next start, as after a crash here. Any
                    // other exception fails the database, as before.
                }
            } catch (Throwable e) {
                throw fail(t, e);
            }
        }
    }
    
    /**
     * Fails the database (bergdb 005-01, register M49) with what a transaction threw after
     * its go point; called under writeLock. Nothing is undone, as the database is never used
     * again: it refuses every later transaction and read with a DbFailedException whose cause
     * is the first failure, until it is restarted. The stream holds whole records only (a
     * transaction is appended in one piece, NodeStream.appendNodes), and nothing is appended
     * after a failure, so the restart rebuilds the database as after a crash at this point:
     * without the failed transaction, or with it if its record was appended before the
     * failure. stop(), close() and sync() still work.
     * 
     * <p>Reclaim's internal transactions run within a user transaction's go point
     * (transactionCompleted()); one that fails first fails the database, and its
     * DbFailedException comes here and is returned as it is, as is that of a read in the
     * transaction that fails on the storage (failOnStorage()). While the database is stopping,
     * a failure is the stop's and is thrown as it is, as before: close() called within a
     * transaction closes the storage under it, so its append can fail (since bergdb 005-35,
     * the close of stop() and close() waits for a running transaction).</p>
     * 
     * <p>An Error before the go point fails the database too (failed(); 2026-11-06, bergdb
     * 019-10): under the write lock, before it is released (bergdb 019-40), and in the
     * warm-up at the edge of execute(), as does one of a read or a sync: the class
     * Javadoc's "Errors".</p>
     * 
     * @return The exception for the caller to throw: a DbFailedException, or the exception
     *      itself while the database is stopping.
     * @throws Error The Error itself, after the database has failed.
     */
    private RuntimeException fail(Trans t, Throwable e) {
        if (setFailed(e) == DbState.STOPPING) {
            if (e instanceof Error) throw (Error) e;
            return e instanceof RuntimeException ? (RuntimeException) e : new DbException(
                    "The transaction failed while the database was stopping.", e);
        }
        
        if (e instanceof Error) throw (Error) e;
        if (e instanceof DbFailedException) return (DbFailedException) e;
        return new DbFailedException("The transaction at time " + t.tt + " failed after it "
                + "began (the cause); nothing is undone. The database takes no more "
                + "transactions or reads and must be restarted: the restart rebuilds it from "
                + "the stream.", e);
    }

    /**
     * Fails the database with 'e' if it is active: keeps 'e' as the first failure and sets
     * FAILED, in one step under readSync (bergdb 005-30). The writer (fail()), the readers
     * (failOnStorage()) and a call that finds the storage failed (assertDbStateIsActive(),
     * bergdb 015-35) come here, and stop() and close() set STOPPING under readSync
     * too, so the first failure is the one kept, and no failure comes after a stop.
     *
     * @return The state before.
     */
    private DbState setFailed(Throwable e) {
        synchronized (readSync) {
            final DbState before = state;
            if (before == DbState.ACTIVE) {
                failure = e;
                state = DbState.FAILED;
            }
            return before;
        }
    }
    
    /**
     * Fails the database with an Error that a call met, and returns it for the call to throw
     * as it is (2026-11-06, bergdb 019-10): the edge of each call that reads, writes or syncs
     * (getOne, getMany, getTrans, execute, sync, setCacheSizeIndicator; start() stops the
     * database instead). An Error means a failed environment (memory, stack) or a bug, and
     * the database cannot tell whose it is: its own, or one of the application's code that it
     * runs, a getMany's StopCondition (010-01, P7). setFailed() first, which allocates
     * nothing, so that a second OutOfMemoryError cannot lose the failure.
     */
    private Error failed(Error e) {
        setFailed(e);
        return e;
    }

    /**
     * Fails the database with what a read or a sync met on the storage (bergdb 005-30): an
     * I/O error or corrupt data, as after a transaction that fails after its go point
     * (fail()). The storage below has stopped already after an I/O error (FileStream,
     * StorageManager), and corrupt data means lost data or a bug: a database that serves
     * around it is worse than one that stops. Nothing has changed in memory (a load that
     * fails registers nothing). A transaction that runs meanwhile ends as it would anyway:
     * committed, or failed after its go point.
     *
     * @param what  "A read" or "A sync", for the message.
     * @return The exception for the caller to throw: a DbFailedException with 'e' as the
     *      cause; or 'e' itself while the database is stopping (stop() closes the storage
     *      under running reads) or before it has started.
     */
    private RuntimeException failOnStorage(StreamException e, String what) {
        final DbState before = setFailed(e);
        if (before != DbState.ACTIVE && before != DbState.FAILED) {
            return e;
        }
        return new DbFailedException(what + " failed on the storage (the cause). The database "
                + "takes no more transactions or reads and must be restarted.", e);
    }
    
    /**
     * Refuses a transaction whose value nodes would take more than StoredTrans.valueLimit()
     * bytes of its record, before it changes anything (2026-10-21, bergdb 005-17). Before,
     * the record's size wrapped in an int, or its buffer could not be made, in store(): after
     * the transaction had changed the Dag (M49), and every later transaction failed too.
     * A transaction whose index nodes could not be written in one record is refused too,
     * under the write lock (checkDirtyNodes(), bergdb 005-31).
     * 
     * <p>Not for reclaim's internal transactions (bergdb 015-50), which run inside a user
     * transaction's go point, where a refusal fails the database: a step keeps its value
     * nodes within valueLimit() itself (Reclaim.step), each value as its user transaction
     * did, and adds its row; the table and the settings are small.</p>
     *
     * @throws DbException
     */
    private static void checkSize(Trans t) {
        checkLimits(t.kvs);
        checkCoreKeys(t.kvs);
        long bytes = 0;
        for (Kv kv : t.kvs) {
            bytes += StoredValueNode.getByteSizeLong(kv.getValue(), kv.getKey());
        }
        final long limit = StoredTrans.valueLimit();
        if (bytes > limit) {
            throw new DbException("The transaction is too large: its values and keys take " 
                    + bytes + " bytes in the stream, more than " + limit + ".");
        }
    }
    
    /**
     * Refuses a user transaction with a KV at a key that the Core writes itself
     * (Trans.coreKey(): "/#i/-dummy", "/#i/dreclaim/" and the keys under it), keys as written,
     * unless the KV came from Trans.Builder's Core calls (Kv.coreWrite; bergdb 024-37; 010-04,
     * R5). The Builder's public calls refuse such a key already; this check is for the KVs
     * that they do not check, those of putLongKey() and deleteLongKey() and those set in
     * t.kvs (its kvs are public). Called by checkSize(), before the write lock and the go
     * point; a key that a key transformation gives is checked by transformKeys(). Not for
     * reclaim's internal transactions, which copy the Core's keys as any live KV.
     *
     * @throws DbException
     */
    static void checkCoreKeys(Kv[] kvs) {
        for (Kv kv : kvs) {
            if (!kv.coreWrite && Trans.coreKey(kv.getKey())) {
                throw new DbException(Trans.coreKeyMessage(kv.getKey()));
            }
        }
    }
    
    /**
     * Refuses a user transaction over the limits L1, L3 and L5 (bergdb 024-17, section 6;
     * "Limits" in the class Javadoc): its operations, its keys' bytes, its keys' and values'
     * bytes, as Trans.Builder.build() gave them, keys as written. Called by checkSize(),
     * before the write lock and the go point, so that a refused transaction leaves nothing,
     * and the refusal does not depend on what the database holds. L2 and L4 are checked by
     * the Trans.Builder calls that take a key or a value; a key transformation's keys by
     * transformKeys(). Not for reclaim's internal transactions, which are within the limits
     * by construction (024-17, 5.5): a step puts at most 16 kB of scanned KVs or one KV.
     *
     * @throws DbException
     */
    static void checkLimits(Kv[] kvs) {
        // Each KV, whatever built the Trans (its kvs are public): a key over L2 but one of
        // BergDB's own from the internal calls, a value over L4 (review rev24, R1, R2). Until
        // then only the Trans.Builder calls checked them, and a value over L4 put through
        // t.kvs failed the database when reclaim copied it.
        for (Kv kv : kvs) {
            final long k = Trans.keyBytes(kv.getKey());
            if (k > MAX_KEY_BYTES && !(kv.longKey && Trans.ownKey(kv.getKey()))) {
                throw new DbException("A key of the transaction has " + k + " bytes, more "
                        + "than " + MAX_KEY_BYTES + " (bergdb 024-17, L2).");
            }
            if (kv.getValue() != null && kv.getValue().length > MAX_VALUE_BYTES) {
                throw new DbException("A value of the transaction has " 
                        + kv.getValue().length + " bytes, more than " + MAX_VALUE_BYTES 
                        + " (bergdb 024-17, L4).");
            }
        }
        if (kvs.length > MAX_OPERATIONS) {
            throw new DbException("The transaction has " + kvs.length + " operations, more "
                    + "than " + MAX_OPERATIONS + " (bergdb 024-17, L1). Split it into "
                    + "transactions.");
        }
        long keyBytes = 0;
        long bytes = 0;
        for (Kv kv : kvs) {
            final long k = Trans.keyBytes(kv.getKey());
            keyBytes += k;
            bytes += k + (kv.getValue() == null ? 0 : kv.getValue().length);
        }
        if (keyBytes > MAX_TRANS_KEY_BYTES) {
            throw new DbException("The keys of the transaction have " + keyBytes + " bytes, "
                    + "more than " + MAX_TRANS_KEY_BYTES + " (bergdb 024-17, L3). Split it "
                    + "into transactions.");
        }
        if (bytes > MAX_TRANS_BYTES) {
            throw new DbException("The keys and values of the transaction have " + bytes 
                    + " bytes, more than " + MAX_TRANS_BYTES + " (bergdb 024-17, L5). Split it "
                    + "into transactions.");
        }
    }
    
    /**
     * Refuses a transaction whose index nodes, those it makes dirty or creates, could take
     * more than StoredTrans.dirtyLimit() bytes, before it changes anything (2026-10-24,
     * bergdb 005-31). TransSeq.take takes transactions whole, so it would never take such a
     * transaction, and the startup pos would stay before it for good: the startup section,
     * startup, D and the stream would grow without end. Called under writeLock, before the
     * go point; not for reclaim's internal transactions: a step makes dirty the index nodes
     * on the paths of its own puts only (touchPaths), and it puts at most the KVs of its
     * scan, 16 kB of them or one KV, and its row. Until bergdb 024-07 a step's touch walked
     * a key range and had no bound: the last step of an iteration over keys in time order
     * made dirty every index node, which at about 100M keys no record could take (024-07,
     * section 3).
     * 
     * <p>A cheap test first: every key at most three nodes a level of a path of at most
     * 'height' levels a segment, and three more; 'height' from the stream's length, as a
     * tree of n nodes with at least two children each is at most log2(n) + 1 high. Only a
     * transaction that fails it walks the paths of its keys (Dag.dirtyNodeBound()). A key
     * with a key transformation, known only at the put, counts as the cheap test counts it.
     * Each node at the largest size, and 16 bytes for its entry in the got-dirty list.</p>
     *
     * @throws DbException
     */
    private void checkDirtyNodes(Trans t) {
        final long limit = StoredTrans.dirtyLimit();
        final long nodeBytes = 32 + 16L * (maxNodeSize + 1) + 16;
        // Its two top nodes: 48 + 16 h bytes each (StoredTopNode, bergdb 024-25), h at most 48
        // (TopNode.MAX_HEIGHT), and a got-dirty entry of 16 (until 024-24's merge of
        // 024-25, 40 + 16 x 64 + 16, the size before CRC32C, a bound of it too).
        final long topBytes = 2 * (48 + 16L * 48 + 16);
        final long height = 2 + 63 - Long.numberOfLeadingZeros(
                Math.max(1, nodeStream.getLength() / 48));
        
        long cheap = 0;
        for (Kv kv : t.kvs) {
            // A delete: with the upward unlink and the merges four klongs in every node of its
            // path, the klongs of root collapse in the segment leaves above, and four nodes a
            // level and two levels more for the merges (Dag.dirtyNodeBound; bergdb 023-07,
            // section 5.4; 024-21): 20 nodes a level, over the walk's count of a delete with
            // its path's overflows at node size 8 (2026.4: 7); a put 3. A value
            // transformation may give null, a delete (bergdb 023-11, review B, B2).
            final boolean delete = kv.getValue() == null || kv.valueTransformation != null;
            cheap += (delete ? 20 : 3) * height * kv.getKey().length + 3;
        }
        if (cheap <= (limit - topBytes) / nodeBytes) {
            return;
        }
        
        int n = 0;
        long nodes = 0;
        final long[][] keys = new long[2 * t.kvs.length][];
        final boolean[] deletes = new boolean[2 * t.kvs.length];
        for (Kv kv : t.kvs) {
            if (kv.keyTransformation != null) {
                // As the cheap test counts it: a delete too (bergdb 024-21: until then a delete
                // with a key transformation counted as a put, 3 nodes a level).
                final boolean delete = kv.getValue() == null || kv.valueTransformation != null;
                nodes += (delete ? 20 : 3) * height * kv.getKey().length + 3;
            } else {
                keys[n] = kv.getKey();
                deletes[n] = kv.getValue() == null && kv.valueTransformation == null;
                n++;
                if (kv.valueTransformation != null) {
                    // It may give null, a delete: walked as a put and as a delete, an
                    // over-count (bergdb 023-11, review B, B2).
                    keys[n] = kv.getKey();
                    deletes[n] = true;
                    n++;
                }
            }
        }
        final long time = dbClock.lookupTime(Long.MAX_VALUE);
        try {
            nodes += dag.dirtyNodeBound(time, java.util.Arrays.copyOf(keys, n), 
                    java.util.Arrays.copyOf(deletes, n), newGetData());
        } catch (StreamException e) {
            throw readFailed(e, time);
        }
        if (nodes > (limit - topBytes) / nodeBytes) {
            throw new DbException("The transaction is too large: the index nodes it can make "
                    + "dirty or create, up to " + nodes + ", could take " 
                    + (nodes * nodeBytes + topBytes) + " bytes in a record, more than " + limit
                    + " (bergdb 005-31). A larger update must be split into transactions.");
        }
    }
    
    private void store() {
        long currentSp = x.startupPos.get();
        long newSp;
        
        // The record's own bytes, which pace take() (bergdb 005-49), and the bytes of the
        // record besides the index nodes that take() adds, so that the record stays within
        // the record limit (bergdb 005-17).
        final TransNodes tn = x.transNodes;
        final long ownBytes = TransSeq.ownBytes(tn.valueRecordBytes);
        long fixedBytes = ownBytes + 16L * x.transInfo.gotDirtyNodes.size();
        for (int i = 0; i < tn.topCount; i++) {
            fixedBytes += StoredTopNode.getByteSize(tn.topNodes[i]) + 16;
        }
        for (int i = 0; i < tn.keyCount; i++) {
            fixedBytes += StoredKeyNode.getByteSize(tn.keyNodes[i]) + 16;
        }
        
        newSp = transSeq.take(currentSp, nodeStream.getLength(), startupDistance, ownBytes,
                x.transNodes, StoredTrans.recordLimit - fixedBytes);
        if (x.trans.maintainTakeTo > newSp) {
            // The empty record of a maintain() call (bergdb 024-32, section 2.2, M4): more of
            // D after the share, oldest first, up to the position that reclaim waits for.
            long bytes = ownBytes + 16L * x.transInfo.gotDirtyNodes.size();
            for (int i = 0; i < tn.topCount; i++) {
                bytes += StoredTopNode.getByteSize(tn.topNodes[i]) + 16;
            }
            for (int i = 0; i < tn.keyCount; i++) {
                bytes += StoredKeyNode.getByteSize(tn.keyNodes[i]) + 16;
            }
            newSp = transSeq.takeTo(newSp, x.trans.maintainTakeTo, 
                    Reclaim.MAINTAIN_TAKE_BYTES, x.transNodes, StoredTrans.recordLimit - bytes);
        }
        x.trans.startupPos = newSp;
        
        // Note: nodeStream.appendNodes() does things beyond writing to stream, it sets spos of nodes.
        // This is not needed for rerun transactions, however. They have value nodes only
        // and their spos:es are set elsewhere.
        
        // Before the record's nodes are cleaned: resolvePointers resolves the pinned set
        // (D's nodes and the record's, dirty) by node id (bergdb item 001, WP R8, change 1).
        resolvePointersOfTakenNodes();
        x.transNodes.clean();
        handleStillDirtyNodes();
        
        TopNode top = newestWrittenTop;
        for (int i = 0; i < x.transNodes.topCount; i++) {
            TopNode t = x.transNodes.topNodes[i];
            if (top == null || t.topNodeId > top.topNodeId) {
                top = t;
            }
        }
        
        nodeStream.appendNodes(x.transNodes, x.trans, x.transInfo.gotDirtyNodes, top);
        newestWrittenTop = top;
        
        // The resident registry (bergdb item 001, WP J1): a written index object is counted
        // with its size now; the audit's oracle learns the record's positions.
        Iterator<Node> written = x.transNodes.indexNodeIterator();
        while (written.hasNext()) {
            cache.residents().grown(written.next());
        }
        eviction.recordWritten(this, x.transNodes.indexNodeIterator());   // admission (009, 3b)
        if (oracle != null) oracle.appended(x.transNodes);

        reclaim.recordWritten(x.trans, x.transNodes);       // Statistics, if on.
        
        x.trans.nodeCount = x.transNodes.size();
        x.transInfo.tpos = x.trans.tpos;
        x.transInfo.lastPos = x.trans.lastPos;
        x.transInfo.tt = x.trans.tt;
        x.transInfo.startupPos = newSp;
        x.transInfo.ownBytes = ownBytes;
        
        transSeq.add(x.transInfo);      // adds to end of transSeq queue
        
        x.startupPos.set(newSp);
    }

    /**
     * Resolves the pointers of the index nodes about to be written, so that they name the
     * latest versions, and the still-dirty test sees every node in D they point to
     * (bergdb 011-04, level 2; NodeCollection.resolvePointers).
     */
    private void resolvePointersOfTakenNodes() {
        long accessData = getAccessData();
        Iterator<Node> iter = x.transNodes.indexNodeIterator();
        while (iter.hasNext()) {
            nodeCollection.resolvePointers(iter.next(), accessData);
        }
    }

    private void handleStillDirtyNodes() {
        int stillDirtyCount;
        do {
            stillDirtyCount = DbHelper.handleStillDirtyNodes(x.transNodes.indexNodeIterator(), x.transInfo);
        } while (stillDirtyCount > 0);
    }
    
    /**
     * Returns to caller with a RerunException if any key was modified after 
     * the read time of the transaction. This is the essence of the 
     * STM (software transactional memory) approach.
     * 
     * @throws RerunException
     */
    private final void stmCheckConflicts(Trans t) {
        for (long hash : t.readKeyHashes) {
            if (keyModSet.modifiedAfter(t.readTime, hash)) {
                throw new RerunException(hash);
            }
        }
    }

    /**
     * Records hash values of the keys for the KVs updated by the transaction, t.
     */
    private void stmRecordKeys(Trans t) {
        for (int i = 0; i < t.writeKeyHashes.length; i++) {
            keyModSet.add(t.tt, t.writeKeyHashes[i]);
        }
    }
    
    /**
     * Reads the KVs as warm-up; aims to avoid lengthy disk reads and cache
     * misses while synchronizing on this.writeLock. We want to minimize the time holding
     * this.writeLock. However, if we do write transactions from a single thread anyway, it
     * would be better to avoid these get operations (would save 10-20% CPU for execute()).
     * This is a trade-off. Of course, we could easily have an optimization setting for this:
     * [enum ThreadOptimization { SINGLE_WRITE_THREAD, MULTIPLE_WRITE_THREADS }].
     * But, until proven important enough, we keep variability as low as possible and focus
     * on good worst-case performance.
     * 
     * <p>A read that a cut overtakes ends the warmup (bergdb 015-52, 016-06's R7-F3): it
     * reads at the latest time when it starts, and other writers commit while it waits on
     * the storage, so a cut can overtake that time. It threw LookupTimeNotAvailableException
     * out of execute(), which refused the transaction with an exception that its Javadoc
     * does not list. The warmup only loads nodes; the transaction reads again under the
     * lock, at the latest time.</p>
     */
    private final void warmup(Trans t) {
        final long readTime = dbClock.lookupTime(Long.MAX_VALUE);
        final GetData gd = t.warmupGetData;

        try {
            for (Kv kv : t.kvs) {
                this.getOneInternal(readTime, kv.getKey(), gd);
            }
        } catch (LookupTimeNotAvailableException e) {
            // A cut overtook readTime; see above.
        }
    }

    /**
     * Sets the KVs directly to the in-memory data structure. This method runs with exclusive 
     * write access to the data structure (synchronized (writeLock)). However, there may be
     * concurrent readers that read with a lookup time strictly less than the transaction time
     * (x.trans.tt).
     *
     * @throws IllegalDbStateException
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws DbException
     */
    private final void putKvs(final Kv[] kvs) {
        assert Thread.holdsLock(writeLock);
        x.putData.tt = x.trans.tt;
        x.putData.accessData = getAccessData();
        // Cleared for the puts of startup (DbStarter), which use the same listeners; no
        // transaction runs after one that threw, which fails the database (bergdb 005-01).
        opMarks.clear();
        opChanged = false;
        replacedInTrans.clear();
        takenBackInTrans.clear();
        touchMarks = 0;

        if (x.trans.touch) {
            // 2026-10-13: was after the puts. Before them, the touch makes dirty 
            // every index node on the paths of the transaction's keys, so that the value
            // transformation of the row of a reclaim step, wherever its key sorts, can store
            // what the step made dirty (Trans.dirtiedBytes). The puts then make dirty only
            // the nodes they create. Until bergdb 024-07 the touch visited a key range
            // (touchRange), to the end of the key space in an iteration's last step.
            touchPaths();
            endOfOp(true);
            touchMarks = x.transInfo == null ? 0 : x.transInfo.gotDirtyNodes.size();
            x.putData.clearFast();
        }

        // The KVs in key order, one a key, after the key transformations (transformKeys; bergdb
        // 023-08, section 7, Q4; 024-16): the index gets a transaction's operations in the order
        // of their keys, whatever the order a transformation left them in, so two transactions
        // with the same operations run the same and write the same stream. A user
        // transaction's value transformations ran before the go point, in this order
        // (transformValues(), bergdb 026-06); an internal transaction's, the row of a reclaim
        // step, run in the put loop: each reads the previous value at tt, as before.
        // The record holds the KVs put, and the startup's rerun applies them in their stored
        // order, this order, and does not sort.
        for (int i = 0; i < kvs.length; i++) {
            Kv kv = kvs[i];

            if (kv.valueTransformation != null && x.trans.isInternal()) {
                final byte[] previousValue = this.getOne(x.trans.tt, kv.getKey(), x.getData);
                kv.transformValue(x.trans.tt, previousValue);
            }

            final TestHooks kvHooks = testHooks;
            if (kvHooks != null) {
                kvHooks.kvApplied(kv.getKey(), kv.getValue());
            }
            dag.putKv(kv.getKey(), kv.getValue(), x.putData);
            endOfOp(false);
            
            x.putData.clearFast();
        }
        
        endOfTrans();
        x.putData.clear();
    }

    /**
     * Runs every key transformation of the transaction, at its time t.tt, and returns the KVs
     * to put, in key order (bergdb 024-16, section 3, S2): t.kvs itself if none has a key
     * transformation (Trans.Builder.build sorted them, one KV a key as written), else a sorted
     * copy (sortByKey). Called under writeLock after DbClock.transactionBegin(), before the go
     * point. A transaction whose KVs have, after the transformations, two at one key is
     * refused: one operation a key reaches the index, always (Frans, 2026-11-11,
     * 09:43: "One transaction must not set (put or delete) a value more than once! This is a
     * strict rule."). Two KVs are two keys as written, as build() keeps one KV a key as
     * written, so a KV is never taken for two. Until 024-16 one of them was kept: the one
     * called last (024-10, R2), and until release 2026.4 the last put in the order of the
     * keys as written, or a delete if there was no put (023-09, section 7.1).
     *
     * <p>A refusal leaves everything as it was before the call: each transformed KV gets its
     * key as written back, and its write hash, so that the Trans can be run again, and t.tt
     * gets its value before the call, before.tt; the time is given back
     * (DbClock.transactionCancel()); nothing has been put, written or recorded (giveBack()).
     * The transformed keys and their write hashes as written are kept in 'before', for a
     * refusal by transformValues() too.
     * A transaction that commits keeps its transformed keys, as before. A transformation that
     * throws a RuntimeException refuses the transaction in the same way (bergdb 026-06; 010-04,
     * R5; until 026-06 it failed the database, as when it ran after the go point); an Error
     * fails the database (KeyTransformation).</p>
     *
     * @throws DbException  If two KVs have one key after the transformations; if a key that a
     *      transformation gave has more than MAX_KEY_BYTES (L2), or the keys more than
     *      MAX_TRANS_KEY_BYTES (L3) (bergdb 024-24); if a transformation threw a
     *      RuntimeException (the cause; bergdb 026-06).
     * @throws DbFailedException  If the sort threw: a bug.
     */
    private Kv[] transformKeys(final Trans t, final Before before) {
        final Kv[] kvs = t.kvs;
        long[][] written = null;                // the keys as written of the KVs transformed
        long[] hashes = null;                   // and their write hashes, by index
        final Kv[] sorted;
        DbException refused = null;             // a transformation threw (bergdb 026-06)
        try {
            for (int i = 0; i < kvs.length && refused == null; i++) {
                final Kv kv = kvs[i];
                if (kv.keyTransformation != null) {
                    if (written == null) {
                        written = new long[kvs.length][];
                        hashes = new long[kvs.length];
                        before.keys = written;
                        before.hashes = hashes;
                    }
                    written[i] = kv.getKey();
                    hashes[i] = t.writeKeyHashes[i];
                    try {
                        kv.keyTransformation.transform(t, i);
                    } catch (RuntimeException e) {
                        // The caller's mistake: refused, and the database goes on (bergdb
                        // 026-06; 010-04, R5). Until 026-06 it failed the database.
                        refused = new DbException("The key transformation of " 
                                + shown(written[i]) + " threw (the cause). The transaction is "
                                + "refused; nothing of it is written, and the database goes "
                                + "on (bergdb 026-06).", e);
                        giveBack(t, before);
                    }
                }
            }
            if (written == null) {
                return kvs;
            }
            sorted = refused == null ? sortByKey(kvs) : null;
        } catch (Throwable e) {
            throw fail(t, e);
        }
        if (refused != null) {
            throw refused;
        }
        try {           // an Error is recorded under the lock (bergdb 019-40)
            for (int i = 1; i < sorted.length; i++) {
                if (Keys.compareArrays(sorted[i - 1].getKey(), sorted[i].getKey()) != 0) {
                    continue;
                }
                final String message = "Two keys of the transaction are one key after its "
                        + "key transformations: " + shown(written, kvs, sorted[i - 1])
                        + " and " + shown(written, kvs, sorted[i]) + " as written are both "
                        + shown(sorted[i].getKey()) + ". The transaction is refused; "
                        + "nothing of it is written, and the database goes on: a "
                        + "transaction has one operation a key (bergdb 024-16).";
                giveBack(t, before);
                throw new DbException(message);
            }
            // The limits on the keys as transformed (bergdb 024-17, 5.1; 024-24): L2 for each
            // key a transformation gave, but for BergDB's own longer keys (Kv.longKey), and
            // L3 for the keys of the transaction. The Pub API's key replace keeps a key's
            // length, so it never meets them.
            long keyBytes = 0;
            for (int i = 0; i < kvs.length; i++) {
                final long k = Trans.keyBytes(kvs[i].getKey());
                keyBytes += k;
                if (written[i] != null && k > MAX_KEY_BYTES 
                        && !(kvs[i].longKey && Trans.ownKey(kvs[i].getKey()))) {
                    final String message = "The key transformation of " + shown(written[i]) 
                            + " gave a key of " + k + " bytes, more than " + MAX_KEY_BYTES
                            + " (bergdb 024-17, L2). The transaction is refused; nothing of "
                            + "it is written, and the database goes on.";
                    giveBack(t, before);
                    throw new DbException(message);
                }
            }
            // A key of the Core's own that a transformation gave (bergdb 024-37; 010-04, R5;
            // checkCoreKeys() for the keys as written).
            for (int i = 0; i < kvs.length; i++) {
                if (written[i] != null && !t.isInternal() && !kvs[i].coreWrite
                        && Trans.coreKey(kvs[i].getKey())) {
                    final String message = "The key transformation of " + shown(written[i])
                            + " gave a key of the Core's own. " 
                            + Trans.coreKeyMessage(kvs[i].getKey());
                    giveBack(t, before);
                    throw new DbException(message);
                }
            }
            if (keyBytes > MAX_TRANS_KEY_BYTES && !t.isInternal()) {
                final String message = "The keys of the transaction have " + keyBytes 
                        + " bytes after its key transformations, more than "
                        + MAX_TRANS_KEY_BYTES + " (bergdb 024-17, L3). The transaction is "
                        + "refused; nothing of it is written, and the database goes on.";
                giveBack(t, before);
                throw new DbException(message);
            }
        } catch (Error e) {
            throw failed(e);
        }
        return sorted;
    }
    
    /**
     * Leaves a transaction that transformKeys() or transformValues() refuses as it was before
     * the call: each KV that a key transformation changed gets its key as written back, and
     * its write hash; each KV with a value transformation that has run gets its value as
     * given back (bergdb 026-06); t.tt gets before.tt, and the time is given back
     * (DbClock.transactionCancel()).
     */
    private void giveBack(Trans t, Before before) {
        final Kv[] kvs = t.kvs;
        for (int j = 0; j < kvs.length; j++) {
            if (before.keys != null && before.keys[j] != null) {
                kvs[j].setKey(before.keys[j]);
                t.writeKeyHashes[j] = before.hashes[j];
            }
            if (before.values != null && kvs[j].valueTransformation != null) {
                kvs[j].setValue(before.values[j]);
            }
        }
        t.tt = before.tt;
        dbClock.transactionCancel();
    }
    
    /**
     * What a refusal under the write lock gives back to its transaction (giveBack(); bergdb
     * 024-16, S5; 026-06): t.tt before the call; the keys as written and the write hashes of
     * the KVs that a key transformation changed, by their index in t.kvs (null where none,
     * all null if no KV has a key transformation); the values as given of the KVs with a value
     * transformation, by index (null if none has one). Made by executeInner() for each
     * transaction; the arrays only for a transaction with transformations.
     */
    private static final class Before {
        final long tt;
        long[][] keys;
        long[] hashes;
        byte[][] values;
        
        Before(long tt) {
            this.tt = tt;
        }
    }
    
    /**
     * Runs every value transformation of a user transaction, at its time t.tt, in the order of
     * 'kvs', the KVs to put in key order as transformKeys() gave them, and checks the values
     * they give (bergdb 026-06; 010-04, R5). Called under writeLock after transformKeys(),
     * before the go point, so that a refusal leaves everything as it was. Until 026-06 the
     * transformations ran in putKvs(), after the go point, where an exception of one, or a
     * value over L4, failed the database (bergdb 024-24, QL6; 015-51). Each transformation
     * gets the KV's value as given and the value of its key before the transaction, read at
     * t.tt as putKvs() read it: the transaction has one operation a key (bergdb 024-16, S3),
     * so none of its puts comes before. The order and the values are those of putKvs(), so
     * the stream is the same.
     * 
     * <p>Not for reclaim's internal transactions, whose transformations run in putKvs(): the
     * row of a reclaim step stores the bytes of the index nodes that the step's touch and puts
     * made dirty (Reclaim.step, Trans.dirtiedBytes), known only there; a step keeps its
     * values within the limits itself.</p>
     * 
     * <p>A transformation that throws a RuntimeException, a value over MAX_VALUE_BYTES (L4),
     * keys and values of more than MAX_TRANS_BYTES (L5), or value nodes of more than
     * StoredTrans.valueLimit() (bergdb 005-17), counted with the values that the
     * transformations gave, refuse the transaction with a DbException: giveBack() gives each
     * KV with a value transformation its value as given, the key transformations' keys and
     * write hashes, and the time back; nothing has been put, written or recorded. A
     * transaction that commits keeps the transformed values in its KVs, as before. An Error
     * fails the database (bergdb 019-10), and so does a read that fails on the storage
     * (005-30).</p>
     * 
     * @throws DbException  If the transaction is refused.
     * @throws DbFailedException  If a read of a previous value failed on the storage.
     */
    private void transformValues(final Trans t, final Kv[] kvs, final Before before) {
        final Kv[] own = t.kvs;
        for (int i = 0; i < own.length; i++) {
            if (own[i].valueTransformation != null) {
                if (before.values == null) {
                    before.values = new byte[own.length][];
                }
                before.values[i] = own[i].getValue();
            }
        }
        if (before.values == null) {
            return;
        }
        
        try {           // an Error is recorded under the lock (bergdb 019-40)
            long bytes = 0;             // L5's count: keys and values
            long nodeBytes = 0;         // 005-17's count: the value nodes
            for (Kv kv : kvs) {
                if (kv.valueTransformation != null) {
                    final byte[] previous;
                    try {
                        previous = getOne(t.tt, kv.getKey(), x.getData);
                    } catch (RuntimeException e) {
                        // As in putKvs(): a read that fails on the storage has failed the
                        // database (failOnStorage()), and anything else is a bug.
                        throw fail(t, e);
                    }
                    try {
                        kv.transformValue(t.tt, previous);
                    } catch (RuntimeException e) {
                        final String message = "The value transformation of " 
                                + shown(kv.getKey()) + " threw (the cause). The transaction "
                                + "is refused; nothing of it is written, and the database "
                                + "goes on (bergdb 026-06).";
                        giveBack(t, before);
                        throw new DbException(message, e);
                    }
                    final byte[] v = kv.getValue();
                    if (v != null && v.length > MAX_VALUE_BYTES) {
                        final String message = "The value transformation of " 
                                + shown(kv.getKey()) + " gave a value of " + v.length 
                                + " bytes, more than " + MAX_VALUE_BYTES + " (bergdb 024-17, "
                                + "L4). The transaction is refused; nothing of it is written, "
                                + "and the database goes on (bergdb 026-06).";
                        giveBack(t, before);
                        throw new DbException(message);
                    }
                }
                final byte[] v = kv.getValue();
                bytes += Trans.keyBytes(kv.getKey()) + (v == null ? 0 : v.length);
                nodeBytes += StoredValueNode.getByteSizeLong(v, kv.getKey());
            }
            if (bytes > MAX_TRANS_BYTES) {
                final String message = "The keys and values of the transaction have " + bytes 
                        + " bytes after its value transformations, more than " 
                        + MAX_TRANS_BYTES + " (bergdb 024-17, L5). The transaction is "
                        + "refused; nothing of it is written, and the database goes on "
                        + "(bergdb 026-06).";
                giveBack(t, before);
                throw new DbException(message);
            }
            final long limit = StoredTrans.valueLimit();
            if (nodeBytes > limit) {
                final String message = "The transaction is too large after its value "
                        + "transformations: its values and keys take " + nodeBytes 
                        + " bytes in the stream, more than " + limit + " (bergdb 005-17). "
                        + "The transaction is refused; nothing of it is written, and the "
                        + "database goes on (bergdb 026-06).";
                giveBack(t, before);
                throw new DbException(message);
            }
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    /** A KV's key as written, for transformKeys()'s message. */
    private static String shown(long[][] written, Kv[] kvs, Kv kv) {
        for (int j = 0; j < kvs.length; j++) {
            if (kvs[j] == kv) {
                return shown(written[j] != null ? written[j] : kv.getKey());
            }
        }
        return shown(kv.getKey());
    }
    
    /** A key for a message: its text, at most 100 characters of it (bergdb 024-16). */
    private static String shown(long[] key) {
        final String s = Keys.toDisplayString(Keys.toBytes(key));
        return s.length() <= 100 ? "\"" + s + "\""
                : "\"" + s.substring(0, 100) + "...\" (" + s.length() + " characters)";
    }

    /**
     * The KVs sorted by key, in a new array (transformKeys; bergdb 023-08, section 7, Q4):
     * 'kvs' is left as it is, so that a Trans can be run again (its Javadoc allows reuse),
     * each key transformation seeing its own KV (bergdb 023-11, review A, F1). Two KVs with
     * one key are next to each other, and transformKeys() refuses the transaction (bergdb
     * 024-16).
     */
    static Kv[] sortByKey(Kv[] kvs) {
        final Kv[] sorted = kvs.clone();
        java.util.Arrays.sort(sorted, new java.util.Comparator<Kv>() {
            public int compare(Kv a, Kv b) {
                return Keys.compareArrays(a.getKey(), b.getKey());
            }
        });
        return sorted;
    }
    
    /**
     * The touch of a reclaim step (Trans.touch; bergdb 024-07): visits, as the writer, the
     * index nodes on the path of each key of the transaction at the transaction time, from
     * the super root to the segment leaf of the key (Dag.followPath), so that each gets dirty
     * before the puts; the values are not read. These are the nodes that the transaction's
     * puts follow, so the touch visits no node off the paths of its own puts: a step's index
     * nodes are those of the paths of its own puts, however many keys the database holds.
     * 
     * <p>Until 024-07 it visited every node reachable at the transaction time for the keys of
     * a range (touchRange, 2026-10-13), the range of the step's scan, and in an iteration's
     * last step the range from the scan's last key to the end of the key space: every key
     * put after the scan's keys since the iteration started, at 10M keys in time order
     * 772,454 nodes in one transaction, pinned at once and then written in one record of 206
     * MB (bergdb 024-07, section 2). The range was walked for
     * the nodes that held deleted keys only, which no put reaches; since format 6 a delete
     * unlinks the nodes it empties (Dag.deleteUpward), so every index node that a lookup
     * reaches, but an empty space root, has a live key below it, and the put of that key, the
     * user's or a step's rewrite, makes the node dirty (024-07, section 4; the Lean model's
     * T_cover).</p>
     */
    private void touchPaths() {
        final GetData gd = dag.newGetData();
        gd.pointerFollower = x.putData.pointerFollower;
        gd.pointerListener = x.putData.pointerListener;      // makes nodes dirty
        Reclaim.TouchCounter counter = null;
        if (x.trans.touchCount != null) {
            counter = new Reclaim.TouchCounter(x.trans.touchCount, x.trans.touchOldBefore,
                    x.putData.pointerListener);
            gd.pointerListener = counter;
        }
        final TestHooks hooks = testHooks;
        if (hooks != null) {
            final Dag.PointerListener inner = gd.pointerListener;
            gd.pointerListener = new Dag.PointerListener() {
                public void superRootAccessed(TopNode superRoot) {
                    hooks.nodeTouched(superRoot);
                    inner.superRootAccessed(superRoot);
                }

                public void pointerFollowed(Node predecessor, int pointerIndex, Node result,
                        int pointerType) {
                    if (result != null && result.isIndexNode()) {
                        hooks.nodeTouched(result);
                    }
                    inner.pointerFollowed(predecessor, pointerIndex, result, pointerType);
                }
            };
        }
        gd.accessData = x.putData.accessData;
        for (Kv kv : x.trans.kvs) {
            dag.followPath(x.trans.tt, kv.getKey(), gd);
        }
        if (counter != null) {
            counter.finish();
        }
    }

    /**
     * Returns the current 'access data' that should be written to accessed pointers.
     * The 'access data' is a negative value: minus the access clock (Cache3.accessClock;
     * bergdb item 001, WP R8, change 4; before 2026-10-17, minus the node table's putSize).
     */
    public long getAccessData() {
        return -cache.accessClock();
    }

    /**
     * Returns access to the internals of Db.
     * Warning, this method is for internal use only.
     */
    public Internal internal() {
        return internal;
    }
    
    /**
     * Creates and returns a Db.Builder that can create a Db object. 
     * The "official" and only public way of creating a Db.
     */
    public static DbBuilder builder() {
        return DbBuilder.createForDb();
    }   
    
    /**
     * Creates a transaction builder object for creating transactions that are
     * suitable to run on this database.
     */
    public Trans.Builder trans() {
        // Currently, the Db settings do not affect how Trans objects are 
        // created, but this may well be changed in the future. 
        // This method gives Db an opportunity to affect how Trans objects are created.
        
        return Trans.Builder.ForDb.create();
    }
    

    // ======== Types ========
    
    /** 
     * Using a special class for Db.readSync is useful for debug / monitoring.
     * The class has no other purpose.
     */
    public static class ReadSync {}
    
    /** 
     * Using a special class for Db.writeLock is useful for debug / monitoring.
     * The class has no other purpose.
     */
    public static class WriteLock {}
    
    /**
     * Access to the internal structure of the Db object.
     * Do NOT use these methods for normal operation, they are available
     * for development, testing, and internal use.
     */
    public class Internal {
        public TopNode superRoot() { return dag.getTopDs().getSuperRoot(); }
        
        public Dag dag() { return dag; }
        
        public void setDag(Dag d) {
            dag = d;
            d.getTopDs().setSecondOrdinal(secondTopOrdinal);
        }

        public long getStartupPosForEvict() { return x.startupPos.get(); }

        public Object getWriteLock() { return writeLock; }
        
        /**
         * Db.getTrans() for a position the database has given, a get's GetData.tpos, as the
         * Pub API's Connection.transactionInfo() reads it (bergdb 021-27): a record there that
         * is not a committed transaction is damage, and fails the database
         * (DbFailedException, the read's StreamFormatException the cause), as for the other
         * reads (bergdb 005-30, 005-34, 005-82). Otherwise as Db.getTrans().
         */
        public StoredTrans getTrans(long tpos) {
            try {
                return getTransInner(tpos, true);
            } catch (Error e) {
                throw failed(e);
            }
        }
        
        /** Writers waiting for the write lock (bergdb item 009, step 3d; Eviction). */
        public int writersWaiting() { return writersWaiting.get(); }
        
        public Object getReadSynch() { return readSync; }
        
        public ExecuteData x() { return x; }
        
        public void createPutAndGetData() { Db.this.createPutAndGetData(); }

        public void setTransSeq(TransSeq seq) { Db.this.transSeq = seq; }
        
        /** Sets the newest written top node; for startup (DbStarter). */
        public void setNewestWrittenTop(TopNode top) { Db.this.newestWrittenTop = top; }
        
        public TopNode newestWrittenTop() { return newestWrittenTop; }
        
        public TransSeq transSeq() { return transSeq; }
        
        public NodeStream nodeStream() { return nodeStream; }
        
        public Cache3 cache() { return cache; }
        
        /** The audit's oracle, or null if the audit is off; see Audit. */
        public Audit.Oracle oracle() { return oracle; }
        
        /** Eviction at transaction boundaries; see Eviction. */
        public Eviction eviction() { return eviction; }

        /**
         * The writer's waits for room in the main stream's write buffer since the last call,
         * as a line, for test reports; see BufferedStream.takeRoomWaits() (bergdb 005-46).
         */
        public String takeWriteBufferWaits() {
            AppendOnlyStream main = storageManager.getMainStream();
            return main instanceof BufferedStream ? ((BufferedStream) main).takeRoomWaits()
                    : "(no write buffer)";
        }
        
        /** The cache's figures now, for tools; see CacheStats (bergdb item 009, step 1a). */
        public CacheStats cacheStats() {
            long[] e = eviction.figures();
            return new CacheStats(cache.residents().bytes(), nodeCollection.loads(), e[0], e[1],
                    e[2], e[3]);
        }

        /**
         * One eviction sweep now, with the given schedule, under the write lock, between
         * transactions; for tests (bergdb item 001, WP J5: EvictionReaderTester).
         */
        /** The maximum node size. */
        public int maxNodeSize() { return maxNodeSize; }

        /** True when the database is active: started, not stopping. */
        public boolean isActive() { return state == DbState.ACTIVE; }

        /**
         * True when the database's close has ended: its storage streams are closed, also
         * after a failed close (closeStorage()). False while it runs or is closing after
         * stop(). For DatabaseBuilderImp's refusal of a second start on the stream of a
         * database that it started (bergdb 015-65).
         */
        public boolean isClosed() {
            synchronized (closeLock) {
                return closeDone;
            }
        }

        /**
         * Fails the database with what one of its own threads, or the Pub API, met: a batch
         * of the eviction thread (bergdb 015-25; Eviction.EvictorRun), an index job, an Error
         * in a Pub API call (2026-11-06, bergdb 019-10). As a transaction that throws after
         * its go point fails it (fail(); 010-01, P7): nothing is undone, and every later
         * transaction and read is refused with a DbFailedException whose cause is the first
         * failure, until the database is restarted; stop(), close() and sync() still work.
         * Nothing while it is stopping. It allocates nothing (setFailed()). Until 019-10
         * failByEviction().
         */
        public void fail(Throwable e) { setFailed(e); }

        public void evictNow(Eviction.Schedule schedule, long seed) {
            synchronized (writeLock) {
                new Eviction(schedule, seed).afterTransaction(Db.this);
            }
        }
        
        public Reclaim reclaim() { return reclaim; }

        public NodeCollection nodeCollection() { return nodeCollection; }

        public AppendOnlyStream getMainStream() {
            return storageManager.getMainStream();
        }
        
        /**
         * True when the main stream has failed, as after a failed flush; see
         * StorageManager.hasFailed(). For tests; until 2026-11-04 (bergdb 005-11) they asked
         * getStorageInfos().
         */
        public boolean storageFailed() {
            return storageManager.hasFailed();
        }
        
        /**
         * Follows the pointers in the Db graph from the super top node using the given 
         * node index choices. Useful for testing.
         */
        public Node findNode(int[] choices, GetData gd) {
            return dag.findNode(choices, gd);
        }
        
        public PutData newPutData() {
            return Db.this.newPutData();
        }
    }
    
    /**
     * Collection of operation-scope data for method Db.execute().
     * All access must be from thread holding Db.writeLock.
     */
    public final class ExecuteData {
        /** Current transaction while writeLock is held. */
        public Trans trans;
        
        /** Current startupPos; stream pos to use by startup procedure. */
        public final StartupPos startupPos;
        
        /** PutData used when executing a transaction. */
        public PutData putData;
        
        /** GetData used when executing a transaction. */
        public GetData getData;
        
        /** The nodes updated for the current transaction. To be written to the stream. */
        public final TransNodes transNodes;
        
        public TransSeq.TransInfo transInfo;
        
        /**
         * The stream length just past the last byte of the last transaction (at the start, the
         * stream's length): what sync() of the last transaction waits for. It was the position
         * of that last byte, one byte short (bergdb 005-44).
         */
        public long endOfLastTrans;

        /** The vpos to assign to next index node that is created. */
        private long nextVpos;
        
        private ExecuteData() {
            startupPos = new StartupPos(0);
            transNodes = new TransNodes();
        }
        
        public final void increaseNextVpos() {
            x.nextVpos = Spos.nextVpos(x.nextVpos);
        }

        /** 
         * Called before transaction executes, just after Db.writeLock held. 
         * Allows ExecuteData to prepare for new transaction.
         */
        private void begin(Trans trans) {
            assert x.putData != null;
            // Empty between transactions (bergdb 005-01, M49): a transaction that throws after
            // its go point fails the database, so no later one writes its nodes as its own.
            assert transNodes.size() == 0 : "the nodes of another transaction, "
                    + transNodes.size();
            this.trans = trans;
            transInfo = new TransSeq.TransInfo();
            x.nextVpos = nodeStream.getNextPos() + 1;
            x.putData.spaceSplitCount = 0;
        }
        
        /**
         * Called after transaction has done putKvs(), but still holds Db.writeLock.
         * Clears temporary references at end of transaction. Important to avoid memory leakage
         * and prepare for next transaction. Caller must hold writeLock.
         */
        private void end() {
            // Good to clear here, kvTransNodes/indexTransNodes. 
            // Large transaction otherwise consumes memory until next transaction executed.
            
            x.endOfLastTrans = x.trans.lastPos + 1;
            trans = null;
            transNodes.clear();
        }
    }
    
    /**
     * Private auxilliary database state; counters, statistics, ...
     */
    public final class Aux {
        
        /** Number of get operations processed since startup of Db. */
        /** Striped (bergdb item 009, step 1c): readers do not share one counter's word. */
        private final java.util.concurrent.atomic.LongAdder getOpCount
                = new java.util.concurrent.atomic.LongAdder();
        
        /** 
         * Number of transactions executed since this.start(). 
         * Protected by writeLock.
         */
        private long transactionCount = 0;
        
        /**
         * Number of KVs set since this.start().
         * Protected by writeLock.
         */
        private long kvCount = 0;
        
        private void updateStats() {
            kvCount += x.trans.kvs.length;
            transactionCount++;
        }
    }
    
    public static class StartParams {
        public static final StartParams NULL = new StartParams();
        public long startupPos;
        public int startupDistance;
        
        public StartParams() {
            startupPos = Spos.NULL;
            startupDistance = -1;
        }
        
        public boolean isNull() {
            return this == NULL;
        }
    }
    
    /**
     * For listening to what happens at startup. Useful for testing / debugging.
     */
    public static interface StartListener {
    }
    
    public static final PrintStartListener SYSTEM_OUT_START_LISTENER = new PrintStartListener(System.out);
    
    public static class PrintStartListener implements StartListener {
        private PrintStream p;
        
        public PrintStartListener() {
            this(System.out);
        }
        
        public PrintStartListener(PrintStream out) {
            this.p = out;
        }
    }
    
    /**
     * A listener ("handler") for the transactionCompleted event, 
     * method transactionCompleted().
     */
    public static interface TransactionListener {

        /**
         * Exceptions specified below are allowed since SpaceReclaim needs to
         * run database transactions to fulfill its need. Those transactions may
         * throw DBStreamFormatException, DBStreamIOException. In addition,
         * DBDataException may be throws by SpaceReclaim.
         * 
         * @throws StreamFormatException
         * @throws StreamIoException
         * @throws InternalDataException
         */
        public void transactionCompleted(Trans t);
    }

    /**
     * Test-only hooks (bergdb item 001, WP R2), for java/stress/TraceExport.java: called for
     * every executed transaction, the internal ones (reclaim's steps and table stores)
     * included, so that a trace can have a record for each. null, the default, does nothing.
     * All calls come from the thread that holds the write lock.
     */
    public static interface TestHooks {
        /** The record of x.trans has been appended and D updated (after store()). */
        public void transExecuted(ExecuteData x);

        /** The transaction being executed created a value node. */
        public void valueNodeCreated(ValueNode node, long[] key);

        /**
         * The transaction being executed is about to give the Dag this operation (Db.putKvs,
         * before Dag.putKv): the key, and the value after its transformation, null for a
         * delete; in the order the Dag gets them. A delete that changes nothing is told here
         * too, and makes no value node (bergdb 024-12, section 2.6: the trace's OP lines).
         */
        public default void kvApplied(long[] key, byte[] value) {}

        /**
         * The touch of the transaction being executed (Trans.touch) visited an index node; the
         * super root included. A node on the paths of several keys is reported for each.
         */
        public void nodeTouched(Node node);

        /**
         * newGetMany() made g, for a reader of the Core API or the Pub API's scans; a test may
         * set g.gd.pointerListener to count the nodes that the scan follows (bergdb 021-28).
         */
        public default void getManyCreated(GetMany g) {}

        /**
         * The transaction being executed replaced an index node (a split, a new super root):
         * the node is no longer current (bergdb item 001, WP P3).
         */
        public void nodeReplaced(Node node);
    }

    /** The test-only hooks, or null. See TestHooks. */
    public static volatile TestHooks testHooks = null;
}


/*

======== Concurrency ========
 
2015-01 Frans: The concurrency implementation of Db is fast and
non-conventional. The advantage is that readers (threads calling
DB.get()/getMany()) will *never* block on anything but stream reads. 
Yes, really never! This is independent on what a writer does and 
other concurrent read threads.
 
---- The essence ----
 
An initialized Db instance is essentially only used through the three methods
getOne(), getMany() and execute(Trans). A thread that calls getOne()/getMany()
is called a *reader* while a thread that calls execute() is called a *writer*.
A core part of execute() holds a lock called Db.writeLock. So, a part of 
execute() is called in serial, one thread at a time. I have measured the 
throughput of small transactions at over 100,000 transactions/s, so the
exclusive-write-access does not result in bad performance. Likely, IO will 
limit performance. An STM (software transactional memory) approach is used 
to achieve fast optimistic concurrency control.

All transactions of BergDB are ACID transactions. Using an SQL term, the
isolation level is serializable (the highest isolation level) with maintained
performance.
 
A writer published its writes (modifications to data) for readers by an empty
synchronized block. See code fragment below.
     
    t.transTime = dbClock.transactionBegin(); 
    setKVs(); 
    synchronized (readSynch) {} 
    dbClock.transactionEnd();
 
Readers are guaranteed to see the changes since the read methods
(getOne/getMany) also synchronize on readSynch in the beginning of the methods.
See code fragment below.

    synchronized (readSynch) {}
    actualLookupTime = dbClock.timeForGet(requestedLookupTime);

2026-10-25 (bergdb item 009, step 1c; items/009-handles/02-implementation-plan.md,
section 3): readers no longer synchronize on readSynch. Every get then wrote the
monitor's word, which all readers share, and readers did not scale. Instead, a read
reads volatile fields before the Dag: the database's state (assertDbStateIsActive), the
first available lookup time (Reclaim), and the clock's last transaction time
(DbClock.lookupTime). The writer's writes before dbClock.transactionEnd() happen before
the clock's volatile write, so a reader that reads the clock sees them, as the empty
synchronized block of the writer and the reader's did. The writer's blocks stay.

The memory writes made by the writer can in general become visible to readers
before the synch operation. The execute() method is however designed in a
particular way. The writes by the writer preserves the previous states - a
lookup with a given actualLookupTime will always give the same result. So,
readers can access the database while the writer is executing transactions.
The result of a transaction is not visible to a reader unless
the reader uses an actualLookupTime that is equal or greater than the
transaction time of the transaction.

Note that this approach requires a lot from the writer. Any memory write may
or may not become visible to concurrent readers and possibly these writes can
become visible in another order than the order observed by the writer. This
is how the Java Memory Model works
(http://jeremymanson.blogspot.se/2008/11/what-volatile-means-in-java.html).
 
The dbClock object in the code above ensures that actualLookupTime of any
lookup (read operation) is less than the transaction time of any running or
future transaction.
 
---- Initialization ----
 
The construction of the Db instance and Db.start() (database startup) are
protected by the code holding both the locks Db.writeLock and Db.readSynch.
All changes of the init stage should thus be available to any writer thread
and any reader thread since that synchronize on writeLock/readSynch before
any memory reads.
 
---- KeyNode ----
 
The long[] klongs field of KeyNode is important. It has valid klongs in the
range[0..size-1] where "size" is the volatile short field KeyNode.size. This
volatile size is key to the concurrency implementation. Once KeyNode.size is
increased (it never decreases) by the writer all other changes to the KeyNode
needed to read the new range of klongs [0..newSize-1] has been made by the
writer.
 
Readers that want to access the state of a KeyNode must *first* read
KeyNode.size before any other fields of the object. This ensures that all
memory writes required to read klongs in the range [0..size-1] are visible to
the reader.
 
Readers must not read klongs that are not in the currently valid klongs array
range [0..size-1].

 
======== CorePerf vs maximum node size ========

Frans 2015-01. The maximum number of klongs per KeyNode.
Checking if 30 is still a good choice. Measured on my Cissi laptop.

Max node size   CorePerf geo mean (get, get4t, getmany, set)
 8              1.00 (1.25, 1.65, 0.73, 0.66)
14              0.73 (0.82, 1.06, 0.61, 0.55)
30              0.77 (0.79, 0.98, 0.86, 0.54)
62              0.89 (0.86, 1.06, 1.22, 0.60)

The default maxNodeSize = 30 is still a reasonable choice.
14 is even faster for the CorePerf geo mean, but 30 is best for getOne() 
performance (one or 4 threads).

There are other criteria besides CorePerf; stream size, memory usage. Not
investigated now.

*/