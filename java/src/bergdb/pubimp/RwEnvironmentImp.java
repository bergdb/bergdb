package bergdb.pubimp;

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import bergdb.common.MyLongSet;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.KeyTransformation;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DataFormatException;
import bergdb.pub.DbObject;
import bergdb.pub.RwEnvironment;
import bergdb.pub.util.BadFormatException;

/**
 * Environment for a transaction.
 * 
 * <p>Threads (bergdb 021-21, 020-24-11, U11-1 and U11-3). The action may use the
 * environment from several threads while it runs: each call of the user's that reads or
 * changes the state below (the read time, the read set, readData, the write maps, the
 * outputs) does so under the environment's lock, and checks under it that the environment is
 * open; uncontended in the normal case of one thread. A conversion, from a value read or to
 * a value put, runs outside the lock: it may run user code. The run's thread closes the
 * environment when the action returns, under the lock, before the commit (RwTransaction):
 * from then on every call of the user's throws IllegalStateException, and the commit reads
 * the state without the lock, as no call changes it any more. Until 2026-11-09 nothing was
 * locked, and the environment was closed only after the commit: threads in the action lost
 * puts, read another key's value and failed the database, and a thread left by the action
 * put while the commit read the maps, which committed an object without its index entry.
 * The internal calls (indexEntries, createTrans, getMany, set, addReadHash) take no lock:
 * they run in the run's thread, after close() or, for an index build's step, in an
 * environment that no user has.</p>
 * 
 * @author Frans Lundberg
 */
class RwEnvironmentImp implements RwEnvironment {
    // One object of this class per run of an rw-transaction's action (bergdb 021-21), and
    // one per WBuilder. If needed for performance, this could change. Initialization is 
    // relatively heavy.
    
    private static final byte[] emptyByteArray = new byte[0];
    private HashMap<String, Object> output;
    private boolean firstRead;
    private long readTime;
    private MyLongSet readHashes;
    private GetData readData;       // The reads' own (bergdb 015-42); made at the first read.
    
    // The writes, one operation a key in each map (bergdb 015-40): a value, or null for a
    // delete. Every put and delete at an object key (no suffix, or ".obj"), of any value, is
    // in objectOps, and keeps the directory's indexes (bergdb 020-10, section 5.1; 015-46: a
    // String or byte[] put was in kvOps, and left the previous object's index entries);
    // every other key's is in kvOps. So the last call on a key wins in its one map (bergdb
    // 015-41). In indexOps a put of an index entry stays over a delete of it
    // (deleteIndexEntry). Two keys that key replace makes one, such as
    // "/t/${transactionTime}.txt" and the key with the time's digits, are two keys here: the
    // Core refuses the transaction at the commit (bergdb 024-16). So the order of the calls
    // on different keys does not matter, and the maps need not keep it (024-10's
    // LinkedHashMaps, for its rule R2, are gone with that rule).
    private HashMap<MapKey, byte[]> kvOps;
    private HashMap<String, ObjectInfo> objectOps;
    private HashMap<MapKey, byte[]> indexOps;
    private final ConnectionImp connection;
    private final boolean enableKeyReplace;
    private volatile boolean closed;                    // Set by close(), under the lock.
    
    public RwEnvironmentImp(ConnectionImp connection) {
        this(connection, connection.getEnableKeyReplace());
    }
    
    /**
     * An environment with key replace as given: a later run of an rw-transaction's action
     * gets an environment of its own (nextRun()), with the setting the connection had at
     * rw() (bergdb 020-24-02, I-6).
     */
    private RwEnvironmentImp(ConnectionImp connection, boolean enableKeyReplace) {
        readHashes = new MyLongSet();
        kvOps = new HashMap<MapKey, byte[]>();
        objectOps = new HashMap<String, ObjectInfo>();
        indexOps = new HashMap<MapKey, byte[]>();
        firstRead = true;
        readTime = -1;
        this.connection = connection;
        output = null;
        this.enableKeyReplace = enableKeyReplace;
    }
    
    /**
     * A new, open environment for the next run of an rw-transaction's action, with this one's
     * connection and key replace (bergdb 021-21, U11-3): each run has its own, which close()
     * ends when the run's action returns, so that a thread that a run left behind cannot
     * write into a later run.
     */
    RwEnvironmentImp nextRun() {
        return new RwEnvironmentImp(connection, enableKeyReplace);
    }
    
    public boolean exists(String ukey) {
        return get(ukey, byte[].class) != null;
    }
    
    /**
     * @throws IllegalArgumentException
     */
    public <TYPE> TYPE get(String ukey, Class<TYPE> clazz) {
        checkOpen();
        String ikey = PubKeys.u2i(ukey);
        
        long[] keySegments = Keys.toSegments(ikey);
        
        // The read fixes the read time, then the value is converted: a conversion that
        // throws, which the action may catch, leaves the time fixed, so the action's reads
        // read one state (RwEnvironment.get; bergdb 020-13, bug 1). Until 2026-11-09 the time
        // was fixed after the conversion: after a first get that threw, the next read was
        // at the latest time and the STM check against it, and a run that read two states
        // of one key committed.
        // The read set, the read time and readData under the lock, the conversion, which
        // may run user code, outside it (bergdb 021-21).
        byte[] value;
        synchronized (this) {
            checkOpen();
            addReadHash(Keys.hash(keySegments));
            long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
            value = connection.getDb().getOne(lookupTime, keySegments, readData());
            if (firstRead) {
                readTime = readData.actualLookupTime;
                firstRead = false;
            }
        }
        
        return connection.getDatabaseImp().getKvToObjectConverter().createObject(clazz, ikey,
                value);
    }
    
    private <TYPE> TYPE getInternal(String ikey, Class<TYPE> clazz) {
        long[] keySegments = Keys.toSegments(ikey);
        addReadHash(Keys.hash(keySegments));
        long lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        TYPE result = connection.getInTransaction(readData(), lookupTime, ikey, clazz);
        
        if (firstRead) {
            readTime = readData.actualLookupTime;
            firstRead = false;
        }
        
        return result;
    }
    
    /**
     * The GetData of this transaction's reads, its own, not the connection's: a read here
     * leaves the connection's frozen lookup time and its transactionInfo() as they were
     * (bergdb 015-42).
     */
    private GetData readData() {
        if (readData == null) {
            readData = connection.getDb().newGetData();
        }
        return readData;
    }
    
    /**
     * Ends the environment of an rw-transaction's run when its action returns, before the
     * commit: a call of a method of RwEnvironment then throws IllegalStateException (bergdb
     * 005-12), from any thread. Under the lock, so that a call that another thread is making
     * has ended, and none that changes the state begins: the commit reads it as the action
     * left it (bergdb 021-21, U11-3; until 2026-11-09 the environment was closed after the
     * commit). Before 005-12, a put() or delete() made then was lost silently, and a
     * setOutput() changed the outputs of the committed transaction.
     */
    public synchronized void close() {
        closed = true;
    }
    
    private void checkOpen() {
        if (closed) {
            throw new IllegalStateException("The RwEnvironment is used after the action has "
                    + "run; it is valid only while Action.run() runs.");
        }
    }
    
    /**
     * Checks the name of an output, for setOutput() and Transaction.getOutput().
     * 
     * @throws IllegalArgumentException if name is null or empty.
     */
    static void checkOutputName(String name) {
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        
        if (name.length() == 0) {
            throw new IllegalArgumentException("The empty string is not allowed for 'name'.");
        }
    }
    
    public void setOutput(String name, Object value) {
        checkOpen();
        checkOutputName(name);
        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed");
        }
        
        synchronized (this) {
            checkOpen();
            if (output == null) {
                output = new HashMap<String, Object>();
            }
            output.put(name, value);
        }
    }
    
    /** The outputs, read after close() (RwTransaction). */
    public HashMap<String, Object> getOutputMap() {
        // NOTE If we would start to reuse RwEnvironmentImp objects, we must copy 'output' before
        // returning it. Alternatively, it can be copied when this object is reset for reuse.
        return output;
    }
    
    void addReadHash(long hash) {
        this.readHashes.add(hash);
    }
    
    public final int getObjectOpsSize() {
        return objectOps.size();
    }
    
    /**
     * Prepares internal data structures for rerunning a W-transaction.
     */
    public void prepareForWRerun() {
        // No user reads for a w-transaction.
        // Set operations not done again (kvOps, objectOps).
        // Index lookup is done again.
        
        firstRead = true;
        readTime = -1;
        readHashes.clear();
        
        if (objectOps.size() > 0) {
            for (ObjectInfo info : objectOps.values()) {
                info.indexes = null;
            }
            
            indexOps.clear();
        }
    }
    
    private static KeyTransformation getKeyTransformation(String key) {
        return key.contains("${transactionTime}") ? replaceTransformation : null;
    }
    
    /**
     * The UTF-8 of a String value, checked before it is made. A lone surrogate is refused, as
     * in a key (bergdb 015-49): its UTF-8 bytes would have '?' in its place, and a get would
     * return another string (bergdb 019-44). So is a String whose UTF-8 takes more than
     * 'limit' bytes, ObjectFormat.MAX_ARRAY for a put, counted first (2026-11-09, bergdb
     * 020-08, section 3: the encoding of a String of more than about 2^31 bytes in UTF-8 threw
     * OutOfMemoryError, an Error that fails the database in rw(), bergdb 019-10).
     *
     * @throws IllegalArgumentException  If 's' has a lone surrogate or too many bytes.
     */
    static byte[] stringValue(String s, long limit) {
        if (PubKeys.hasLoneSurrogate(s)) {
            throw new IllegalArgumentException("String value has a lone surrogate, a "
                    + "char of U+D800 to U+DFFF that is not part of a surrogate pair "
                    + "(bergdb 019-44).");
        }
        if (3L * s.length() > limit) {       // a char takes at most 3 bytes in UTF-8
            long size = StringUtil.utf8Size(s);
            if (size > limit) {
                throw new IllegalArgumentException("String value of " + size + " bytes in "
                        + "UTF-8; a value has at most " + limit + ", the most bytes a Java "
                        + "array holds (bergdb 020-08, section 3).");
            }
            // Into an array of its size: getBytes() may need more than Java's largest
            // array on the way (the review of e92a95a).
            return StringUtil.toBytes(s, (int) size);
        }
        return StringUtil.toBytes(s);
    }

    private static final byte[] TRANSACTION_TIME_BYTES = Keys.toBytes("${transactionTime}");
    
    /**
     * A put of a String's or a byte[]'s bytes: at an object key in objectOps, which keeps the
     * indexes (bergdb 020-10, section 5.1; 015-46), else in kvOps. A String's is never an
     * object (bergdb 020-08, section 3).
     */
    private void setBytes(String ikey, byte[] value, boolean string) {        
        if (value == null) {
            throw new IllegalArgumentException("value == null not allowed.");
        }
        
        KeyTransformation kt = enableKeyReplace ? getKeyTransformation(ikey) : null;
        if (Entries.isObjectKey(ikey)) {
            writeObject(ikey, ObjectInfo.ofBytes(ikey, value, string, kt));
        } else {
            writeKv(new MapKey(Keys.toSegments(ikey), kt), value);
        }
    }
    
    /**
     * A put or delete of the user's at an object key into objectOps: under the lock, refused
     * once the environment is closed (bergdb 021-21).
     */
    private synchronized void writeObject(String ikey, ObjectInfo info) {
        checkOpen();
        objectOps.put(ikey, info);
    }
    
    /** A put or delete of the user's at another key, as writeObject (bergdb 021-21). */
    private synchronized void writeKv(MapKey key, byte[] value) {
        checkOpen();
        setKv(key, value);
    }
    
    // Used internally, no checking
    void set(byte[] key, byte[] value, KeyTransformation kt) {
        setKv(new MapKey(Keys.toSegments(key), kt), value);
    }
    
    /**
     * Sets the operation of a key in kvOps, a put, or a delete if value is null: it replaces
     * the key's earlier one, so the last call on a key wins (bergdb 015-40). The key is
     * removed first, as a HashMap keeps its first key object when a put replaces an entry,
     * and the key transformation of the MapKey must be the last call's (a delete has none).
     */
    private void setKv(MapKey key, byte[] value) {
        kvOps.remove(key);
        kvOps.put(key, value);
    }

    /**
     * @throws IllegalArgumentException if 'ukey' is null or invalid.
     */
    public void delete(String ukey) {
        // Null values allowed in a HashMap.
        
        checkOpen();
        String ikey = PubKeys.u2i(ukey);

        if (Entries.isObjectKey(ikey)) {
            writeObject(ikey, new ObjectInfo(ikey, null, null));
        } else {
            writeKv(new MapKey(Keys.toSegments(ikey), null), null);   
        }
    }
    
    /**
     * @throws IllegalArgumentException
     */
    public void put(String ukey, Object object) {
        // Implementation here must match the Java object creation. Currently (June 2013) this
        // is made in pubimp.KvToObjectImp.createObject().
        
        checkOpen();
        if (object == null) {
            throw new IllegalArgumentException("object == null not allowed");
        }
        
        String ikey = PubKeys.u2i(ukey);
        checkReplaceInDirectory(ukey, ikey);
        Class<?> clazz = object.getClass();
        
        if (clazz.equals(byte[].class)) {
            // NOTE, No check here, but we could force suffix != EMPTY.
            // A copy: the value in memory must not be the caller's array, which the caller
            // may change after the put (bergdb 015-47).
            setBytes(ikey, ((byte[]) object).clone(), false);
        } else if (clazz.equals(String.class)) {
            setBytes(ikey, stringValue((String) object, ObjectFormat.MAX_ARRAY), true);
        } else {
            if (!Entries.isObjectKey(ikey)) {
                // The user's key; it gave the ikey, "/dk/-x.OBJ" (bergdb 020-24-05, U5-9).
                throw new IllegalArgumentException("Bad key for an object, '" + ukey + "': an "
                        + "object is put only at a key without a suffix or with the suffix "
                        + "\".obj\", in lower case.");
            }
            writeObject(ikey, new ObjectInfo(ikey, object, 
                    enableKeyReplace ? getKeyTransformation(ikey) : null));
        }
    }
    
    /**
     * Refuses a put at an object key whose directory holds "${transactionTime}" when key
     * replace is on (the Codex review's X1, bergdb 020-14): the directory that such a put
     * lands in is known only at the commit, when the transaction's time is, but its index set
     * and the previous value are read before (020-10, section 5.1). Until 2026-11-09 they were
     * read for the key as written: an index of that directory lost the entry of an object the
     * put did not change, and one of the directory the put landed in missed the new object.
     * A key with a suffix is never indexed, and is replaced anywhere (015-64).
     *
     * @throws IllegalArgumentException  If so, before anything is written.
     */
    private void checkReplaceInDirectory(String ukey, String ikey) {
        if (enableKeyReplace && Entries.isObjectKey(ikey)
                && ikey.substring(0, ikey.lastIndexOf('/')).contains(REPLACE_ME)) {
            throw new IllegalArgumentException("Key replace in the directory of an object "
                    + "key is not allowed: the indexes of the directory that the put lands in "
                    + "would not be known before the commit; \"${transactionTime}\" may be in "
                    + "the key's name, the part after its last '/'. Key: " + ukey
                    + " (bergdb 020-14, X1).");
        }
    }
    
    /**
     * Deletes an index entry of an object's previous value, unless this transaction puts it
     * (bergdb 015-40): when the indexed fields of an object are unchanged, the entry deleted
     * for its previous value and the one put for its new value are one key, and the entry
     * must stay, whatever the order of the two calls. indexEntries() deletes first, so the
     * put replaces the delete; before 015-40, when MapKey.equals was never true and indexOps
     * held both, Trans.Builder.build's rule (a put over a delete) kept the entry. The put is
     * also the last operation on the entry, in the order of an object's change: its previous
     * value's entries deleted, then its new value's put (bergdb 024-10, section 3, R6).
     */
    private void deleteIndexEntry(byte[] indexKey) {
        indexOps.putIfAbsent(new MapKey(Keys.toSegments(indexKey), null), null);
            // null marks "delete op"; putIfAbsent replaces a delete, not a put
    }
    
    /**
     * Sets and deletes the index entries of this transaction's writes at object keys, after
     * the user's action has run (or at once for a w()), by bergdb 020-10, section 5.1, for
     * every put and delete at an object key, of any value:
     * <ol>
     * <li>The read time R is fixed first: if nothing was read yet, R is the latest
     *     transaction's time, as a read at Long.MAX_VALUE resolves it (fixReadTime), before
     *     anything below. Until 2026-11-08 the index set was read before R existed (015-28,
     *     015-43, S2-F12): an index created or deleted meanwhile was missed.</li>
     * <li>The hash of each directory's virtual key goes into the read set, whether the
     *     directory has an index or not: a creation or deletion of an index of the directory
     *     writes it, so this transaction runs again if one commits after R.</li>
     * <li>The index set of each directory is read from the manager, under its lock, after
     *     R (IndexManager.getActiveIndexesForDir): a change of the set at or before R is in
     *     it (020-10, section 5.2).</li>
     * <li>If the set is not empty, the previous value is read at R (its key's hash in the
     *     read set), the entries of the previous value are deleted and those of the new one
     *     put. A value that is not a stored object of format 2 (a String's bytes, a byte[]
     *     that fails 020-07's full check) has no entries, so a String or a byte[] put over an
     *     object deletes its entries (015-46); a byte[] that passes the check is an object
     *     (020-10, section 3.3). A String put's new value is not looked at: a String is never
     *     an object, of format 2 or 1 (020-08, section 3).</li>
     * <li>The index definitions' keys are not in the read set: an activation does not change
     *     the set.</li>
     * </ol>
     * 
     * @throws DataFormatException  If, in a directory with an index, the new value of a
     *      byte[] put is an object of format 1 (BergDB 2026.3's, by its structure,
     *      ObjectFormat.isFormat1): such a put is refused; in a directory without an index it
     *      is stored as it is (bergdb 020-08, step 3 and section 3; 020-10, section 5.1). A
     *      String put's new value never is one. A previous value of format 1 has no entries,
     *      so a put over it and a delete of it work (2026-11-09).
     */
    public void indexEntries(IndexManager m) throws DataFormatException {
        assert m != null : "m is null";
        assert objectOps != null;
        
        if (objectOps.size() == 0) {
            return;
        }
        
        fixReadTime();
        for (ObjectInfo info : objectOps.values()) {
            addReadHash(IndexManager.vhashOfDir(info.dir));
        }
        m.hook(IndexManager.WRITE_BEFORE_SET);
        for (ObjectInfo info : objectOps.values()) {
            info.indexes = m.getActiveIndexesForDir(info.dir);
        }
        m.hook(IndexManager.WRITE_AFTER_SET);
        
        for (Map.Entry<String, ObjectInfo> entry : objectOps.entrySet()) {
            final ObjectInfo info = entry.getValue();
            final String ikey = entry.getKey();
            
            if (info.indexes == null || info.indexes.length == 0) {
                continue;
            }
            
            // The previous value, read at R, to delete its entries. One of format 1 has none:
            // no index of 2026.4 indexed one (a build fails over it, a byte[] put of it is
            // refused), so a put over it and a delete of it work (2026-11-09, the review of
            // e92a95a: they were refused, so such a key stayed while the index existed).
            // A put whose key is replaced ("${transactionTime}" in its name: put() refuses
            // it in the directory) lands at a key whose name holds its commit's time, after R,
            // which no key replace wrote before: it has no previous value. The key as written
            // is another key; its value and entries stay (the Codex review's X1, bergdb
            // 020-14, and 020-13, bug 3: until 2026-11-09 its value was taken as the
            // previous one, and its entries deleted).
            byte[] previous = info.kt != null ? null : getInternal(ikey, byte[].class);
            boolean previousFormat1 = previous != null && ObjectFormat.isFormat1(previous);
            for (IndexDefinition def : info.indexes) {
                byte[] old = previousFormat1 ? null : def.entry(ikey, previous);
                byte[] put = info.string ? null : def.entry(ikey, info.value);
                if (old != null) {
                    deleteIndexEntry(old);
                }
                if (put != null) {
                    // Removed first, so that the MapKey kept is the put's, with its kt.
                    KeyTransformation kt = enableKeyReplace && getKeyTransformation(ikey) != null
                            ? entryTransformation(put.length - IndexKeys.fileKey(ikey).length)
                            : null;
                    MapKey key = new MapKey(Keys.toSegments(put), kt);
                    indexOps.remove(key);
                    indexOps.put(key, emptyByteArray);
                }
            }
        }
    }
    
    /**
     * Fixes the read time R if nothing was read yet: the latest transaction's time, as a read
     * at Long.MAX_VALUE resolves it (bergdb 020-10, section 5.1, step 1). Every later read of
     * the transaction is at R, and its Core transaction's read set is checked against R.
     */
    private void fixReadTime() {
        if (firstRead) {
            readTime = connection.getDb().lookupTime(Long.MAX_VALUE);
            firstRead = false;
        }
    }
    
    /**
     * Internal method for using GetMany in an RW transaction.
     * g.lookupTime is set by this method and should not be set by the caller.
     * The KVs read are not put in the read set: the caller adds the hashes of those its
     * writes depend on (addReadHash). Its one caller, a build step, adds the hash of each
     * value whose entry it puts (bergdb 020-18, F1: every KV read was added, so a write of a
     * key with a suffix, which has no entry and takes no index manager's lock, made the
     * step run again, also under that lock).
     */
    void getMany(GetMany g) {
        g.lookupTime = firstRead ? Long.MAX_VALUE : this.readTime;
        
        connection.getDb().getMany(g);
        if (firstRead) {
            this.readTime = g.actualLookupTime;
            firstRead = false;
            
            //System.out.println("RwEnvironmentImp, firstRead, readTime: " + readTime + ", " + g.result.size());
        }
    }
    
    /**
     * This method creates the transaction (core.Trans) based on the values set to readHashes, 
     * kvOps, objectOps, indexOps. If this transaction is an RW transaction
     * (Connection.rw()), the Action.run() method has been run already.
     */
    public Trans createTrans(Db db) {
        Trans.Builder b = db.trans();
        
        b.lookupTime(readTime == -1 ? Long.MAX_VALUE : this.readTime);
        
        if (readHashes.isArray()) {
            b.addReadHashes(readHashes.getArray(), readHashes.size());
        } else {
            for (long hash : readHashes) {
                b.addReadHash(hash);
            }
        }
        
        for (Map.Entry<MapKey, byte[]> entry : kvOps.entrySet()) {
            final long[] key = entry.getKey().getArray();
            final byte[] value = entry.getValue();
            final KeyTransformation kt = entry.getKey().getKeyTransformation();
            
            if (value == null) {
                b.delete(key);
            } else {
                b.put(key, kt, value, null);
            }
        }
        
        for (Map.Entry<String, ObjectInfo> entry : objectOps.entrySet()) {
            final String key = entry.getKey();
            final ObjectInfo info = entry.getValue();
            
            if (info.value == null) {
                b.delete(key);
            } else {
                b.put(Keys.toSegments(key), info.kt, info.value, null);
            }
        }
        
        for (Map.Entry<MapKey, byte[]> entry : indexOps.entrySet()) {
            final MapKey mkey = entry.getKey();
            final long[] key = mkey.getArray();
            final byte[] value = entry.getValue();
            final KeyTransformation kt = mkey.getKeyTransformation();
            
            if (value == null) {
                b.delete(key);
            } else {
                b.put(key, kt, value, null);
            }
        }
        
        Trans trans = b.build();
        return trans;
    }
    
    private static final String REPLACE_ME = Util.identity("${transactionTime}");
    private static final byte[] REPLACE_ME_BYTES = Keys.toBytes(REPLACE_ME);
    private static final int REPLACE_ME_LENGTH = REPLACE_ME_BYTES.length;
    
    private static final KeyTransformation replaceTransformation = entryTransformation(0);
    
    /**
     * A key transformation that replaces every "${transactionTime}" in the key's bytes from
     * 'from' to its end, from the end of the key (bergdb 015-64; until 015-64 only the last),
     * with the transaction's time. The time's digits cannot form a new occurrence. For an
     * index entry 'from' is where its K starts, so that only the value's name is replaced, not
     * an indexed value that holds the text (bergdb 020-10, section 5.3, N11: until 2026-11-09
     * every occurrence in the entry's key was).
     */
    static KeyTransformation entryTransformation(final int from) {
        return new KeyTransformation() {
            public void transform(Trans trans, int index) {
                byte[] bytes = Keys.toBytes(trans.kvs[index].getKey());
                byte[] timeBytes = Keys.toBytes(transTimeToString(trans.tt));
                assert timeBytes.length == REPLACE_ME_LENGTH;
                boolean found = false;
                
                int startIndex = bytes.length - REPLACE_ME_LENGTH;
                while (startIndex >= from) {
                    boolean match = true;
                    for (int i = 0; i < REPLACE_ME_LENGTH; i++) {
                        if (bytes[startIndex + i] != REPLACE_ME_BYTES[i]) {
                            match = false;
                            break;
                        }
                    }
                    
                    if (match) {
                        System.arraycopy(timeBytes, 0, bytes, startIndex, REPLACE_ME_LENGTH);
                        found = true;
                        startIndex -= REPLACE_ME_LENGTH;
                    } else {
                        startIndex--;
                    }
                }
                
                if (!found) {
                    return;
                }
                
                long[] newKey = Keys.toSegments(bytes);
                trans.kvs[index].setKey(newKey);
                trans.writeKeyHashes[index] = Keys.hash(newKey);
            }
        };
    }
    
    private static final String transTimeToString(long transTime) {
        assert transTime >= Klong.MIN_TIME && transTime <= Klong.MAX_TIME;
        return String.format(Locale.US, "%018d", transTime);
    }
    
    /**
     * A put or a delete at an object key: the stored value, or null for a delete; for an
     * object put, its DbObject too (bergdb 020-10, section 5.1).
     */
    private static class ObjectInfo {
        String dir;              // The directory where object is stored.
        String name;             // short object name
        DbObject dbo;            // The object of an object put, else null
        byte[] value;            // The value to store, null for a delete
        boolean string;          // A String put: never an object (bergdb 020-08, section 3)
        IndexDefinition[] indexes;
        KeyTransformation kt;    // If non-null, the key transformation to use.
        
        /**
         * Creates the object.
         * 
         * @param key
         * @param object 'null' used to mark a deletion.
         */
        ObjectInfo(String ikey, Object object, KeyTransformation kt) {
            assert ikey != null;
            int charIndex = ikey.lastIndexOf('/');
            assert charIndex != -1 : "An object must be stored in a directory, missing '/' in key.";
            assert Entries.isObjectKey(ikey);
            
            dir = ikey.substring(0, charIndex + 1);
            name = ikey.substring(charIndex + 1);
            
            if (object == null) {
                dbo = null;
                value = null;
            } else if (object instanceof DbObject) {
                // A user's DbObject: a copy of its bytes, checked by the full check (the
                // review of bergdb 020-10, B3: its own array was stored, and changed by a
                // change of getBytes()' array; and a class that joined bergdb.pub could
                // make one that breaks a rule). An object that DataObjects builds is not
                // checked again.
                dbo = (DbObject) object;
                value = dbo.getBytes();
                try {
                    ObjectFormat.checkStored(value);
                } catch (BadFormatException e) {
                    throw new IllegalArgumentException("The DbObject put at " 
                            + PubKeys.i2u(ikey) + " is not a stored object of format 2: " 
                            + e.getMessage(), e);
                }
            } else {
                dbo = DbObject.toDbObject(object);
                value = dbo.getBytes();
            }
            
            this.kt = kt;
        }
        
        /** A put of a String's or a byte[]'s bytes at an object key. */
        static ObjectInfo ofBytes(String ikey, byte[] value, boolean string, 
                KeyTransformation kt) {
            ObjectInfo info = new ObjectInfo(ikey, null, kt);
            info.value = value;
            info.string = string;
            return info;
        }
    }

    
    /**
     * Internal class that bounds a key transformation with a database key.
     * Two MapKeys are equal when their keys are, whatever their transformations.
     * Until 2026-11-03 (bergdb 015-40) equals() tested for a long[] and so was never true:
     * a map held each call on a key, and the order of the calls was lost.
     */
    private static final class MapKey {
        private long[] array;
        private KeyTransformation kt;
        
        public MapKey(long[] array, KeyTransformation kt) {
            assert array != null;
            this.array = array;
            this.kt = kt;
        }
        
        public KeyTransformation getKeyTransformation() {
            return kt;
        }

        public boolean equals(Object key) {
            if (key == null) {
                return false;
            }
            
            if (!(key instanceof MapKey)) {
                return false;
            }
            
            MapKey key2 = (MapKey) key;
            long[] array2 = key2.array;
            
            if (array.length != array2.length) {
                return false;
            }
            
            for (int i = 0; i < array.length; i++) {
                if (array[i] != array2[i]) {
                    return false;
                }
            }
            
            return true;
        }
        
        /**
         * See http://stackoverflow.com/questions/2827612/effective-java-hashcode-implementation.
         */
        public int hashCode() {
            long prime = 37;
            long value = prime;
            for (int i = 0; i < array.length; i++) {
                value = value * prime + array[i];
            }
            
            int result = (int) value;
            result = (int) (result * prime + value >>> 32);
            return result;
        }
        
        public final long[] getArray() {
            return array;
        }
    }
    
    private static boolean assertionsEnabled() {
        boolean enabled = false;
        try {
            assert false;                                                                                                                                                                                                                                           
        } catch (AssertionError e) {
            enabled = true;
        }
        return enabled;
    }
    
    @Nano
    public static void testTransactionTimeString1() {
        long[] times = {0, 200, 17000000000000000L};
        String[] expected = {
                "000000000000000000", 
                "000000000000000200", 
                "017000000000000000"
        };  
        
        for (int i = 0; i < times.length; i++) {
            Assert.assertEquals(expected[i], transTimeToString(times[i]));
        }
    }
    
    @Nano
    public static void testTransactionTimeString2() {
        // Assertions must be enabled to test this. (-ea). Otherwise, nothing is tested.
        Throwable ex = null;
        try {
            transTimeToString(210000000000000000L);
        } catch (AssertionError e) {
            ex = e;
        }
        
        if (assertionsEnabled()) {
            Assert.assertTrue(ex != null);
        }
    }
    
    public static void main(String[] args) {
        System.out.println("transTimeToString, 1, 111222333444L");
        System.out.println(transTimeToString(1));
        System.out.println(transTimeToString(111222333444L));
        System.out.println(transTimeToString(Klong.MAX_TIME));
        
        // -->
        // 000000000000000001
        // 000000111222333444
        // 072057594037927935
        // 18 chars.
    }
}
