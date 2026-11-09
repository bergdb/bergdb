package bergdb.pubimp;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.DbObject;
import bergdb.pub.Kv;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.util.BadFormatException;

/**
 * The listing of a directory, the primary scan (bergdb 020-10, section 3.5): its own
 * iterator over the Core's Db.getMany, which reads the directory's own keys in pages, at
 * the lookup time that the constructor resolves. It was a wrapper of UseIndexBuilderImp
 * with the pseudo-index "primary" until 2026-11-08.
 *
 * @author Frans Lundberg
 */
class UsePrimaryBuilderImp<TYPE> implements UsePrimaryBuilder<TYPE> {
    /** A page of Db.getMany visits at most this many keys, values of this many bytes... */
    static final int PAGE_KEYS = 100;
    private static final long PAGE_BYTES = 50 * 1000 * 1000;
    /** ...and takes at most this time. */
    private static final long PAGE_NANOS = 1000 * 1000 * 1000;

    /** The kinds of values a type lists (bergdb 020-10, section 3.5). */
    private static final int ALL = 0;
    private static final int NOT_OBJECTS = 1;
    private static final int OBJECTS = 2;

    private final ConnectionImp connection;
    private final Class<TYPE> type;
    private final int kind;
    /** The actual lookup time of every iterator. */
    private final long lookupTime;
    /** The bkey of the directory's idir and '-': the prefix of its own keys; null until dir(). */
    private byte[] prefix;
    /** The length of the prefix's ikey, idir and '-'. */
    private int prefixIkeyLength;
    /** The bkey bytes of startAt()'s name, or null. */
    private byte[] startName;
    private boolean inclusive = true;
    private boolean inclusiveCalled = false;
    private boolean forward = true;
    /** True after objects() or kvs(): the other calls throw. */
    private boolean listing = false;

    /**
     * Takes the lookup time: wantedLookupTime resolved now, as a get resolves it, and the
     * connection's frozen time fixed by it if not fixed yet (bergdb 020-10, section 3.6).
     *
     * @throws IllegalArgumentException  If type is null.
     */
    public UsePrimaryBuilderImp(ConnectionImp connection, Class<TYPE> type,
            long wantedLookupTime) {
        if (type == null) {
            throw new IllegalArgumentException("type == null not allowed");
        }

        this.connection = connection;
        this.type = type;
        if (type.equals(byte[].class) || type.equals(Object.class)) {
            this.kind = ALL;
        } else if (type.equals(String.class)) {
            this.kind = NOT_OBJECTS;
        } else {
            this.kind = OBJECTS;
            if (!type.equals(DbObject.class)) {
                // The class first, also for a directory without an object (bergdb 020-09,
                // section 3.3): ObjectCreationException.
                DataObjects.checkGet(type);
            }
        }
        this.lookupTime = connection.scanLookupTime(wantedLookupTime);
    }

    public UsePrimaryBuilder<TYPE> dir(String udir) {
        checkNotListing("dir");
        if (prefix != null) {
            throw new IllegalStateException("dir() was called before: a listing has one "
                    + "directory.");
        }
        if (udir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        String idir = PubKeys.udir2idir(udir);      // its rules (bergdb 021-09)
        prefix = Keys.toBytes(idir + PubKeys.FILE_PREFIX);
        prefixIkeyLength = idir.length() + 1;
        return this;
    }

    public UsePrimaryBuilder<TYPE> inclusive(boolean inclusive) {
        checkNotListing("inclusive");
        checkDir("inclusive");
        if (inclusiveCalled) {
            throw new IllegalStateException("inclusive() was called before.");
        }
        this.inclusiveCalled = true;
        this.inclusive = inclusive;
        return this;
    }

    public UsePrimaryBuilder<TYPE> backward() {
        checkNotListing("backward");
        checkDir("backward");
        if (!forward) {
            throw new IllegalStateException("backward() was called before.");
        }
        this.forward = false;
        return this;
    }

    public UsePrimaryBuilder<TYPE> startAt(String name) {
        checkNotListing("startAt");
        checkDir("startAt");
        if (startName != null) {
            throw new IllegalStateException("startAt() was called before.");
        }
        if (name == null) {
            throw new IllegalArgumentException("name == null not allowed");
        }
        if (name.isEmpty()) {
            throw new IllegalArgumentException("A name in a directory is not empty.");
        }
        if (name.indexOf('/') != -1) {
            throw new IllegalArgumentException("A name in a directory has no '/', was: "
                    + name);
        }
        if (PubKeys.hasLoneSurrogate(name)) {
            throw new IllegalArgumentException("The name has a lone surrogate, a char of "
                    + "U+D800 to U+DFFF that is not part of a surrogate pair, as a key may "
                    + "not (bergdb 015-49, S2-F24).");
        }
        startName = Keys.toBytes(name);
        return this;
    }

    public Iterable<TYPE> objects() {
        startListing();
        return new Iterable<TYPE>() {
            public Iterator<TYPE> iterator() {
                final Scan scan = new Scan();
                return new Iterator<TYPE>() {
                    public boolean hasNext() {
                        return scan.hasNext();
                    }

                    public TYPE next() {
                        return scan.next().value();
                    }

                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }

    public Iterable<Kv<TYPE>> kvs() {
        startListing();
        return new Iterable<Kv<TYPE>>() {
            public Iterator<Kv<TYPE>> iterator() {
                return new Scan();
            }
        };
    }

    private void checkNotListing(String call) {
        if (listing) {
            throw new IllegalStateException(call + "() after objects() or kvs(): the builder "
                    + "is spent.");
        }
    }

    private void checkDir(String call) {
        if (prefix == null) {
            throw new IllegalStateException(call + "() before dir(): dir() is the first call.");
        }
    }

    private void startListing() {
        if (prefix == null) {
            throw new IllegalStateException("No dir(): a listing needs its directory, which "
                    + "dir() gives as the first call (bergdb 020-10, S2-F17).");
        }
        listing = true;
    }

    /**
     * True if the value at ikey is an object (bergdb 020-10, section 3.5; 020-08, section
     * 3): an object key and the object format's header (Entries.isProbablyDbObject), and the
     * format's full check passed (the DbObject constructor's). So a byte[] at an object key
     * that starts as an object but fails the check is a byte[]: a class leaves it out, and
     * String.class lists it. The check makes the scan of a class parse each object twice,
     * once here and once in its conversion.
     *
     * <p>An object of format 1, BergDB 2026.3's and before, is an object here, so that its
     * conversion refuses it, naming the format (bergdb 020-08, step 3).</p>
     */
    static boolean isObject(String ikey, byte[] value) {
        if (Entries.isFormat1Object(ikey, value)) {
            return true;
        }
        if (!Entries.isProbablyDbObject(ikey, value)) {
            return false;
        }
        try {
            new DbObject(value);
            return true;
        } catch (BadFormatException e) {
            return false;
        }
    }

    /** The least key above every key that starts with 'bytes'. */
    private static byte[] after(byte[] bytes) {
        byte[] result = bytes.clone();
        int last = result.length - 1;
        assert (result[last] & 0xff) < 0xff : "a prefix ends with '-'";
        result[last]++;
        return result;
    }

    /** An iterator of the listing: the pages of Db.getMany, the values of the type's kind. */
    private final class Scan implements Iterator<Kv<TYPE>> {
        private final long[] prefixSegments = Keys.toSegments(prefix);
        /** Where the next page starts. */
        private long[] from;
        private boolean fromInclusive;
        private List<Kvt> page = Collections.emptyList();
        private int pos = 0;
        /** True if the page is the last one. */
        private boolean lastPage = false;
        /** The next value of the type's kind, looked ahead by hasNext(), or null. */
        private Kvt next = null;
        private String nextIkey = null;

        Scan() {
            if (startName != null) {
                from = Keys.toSegments(Util.concat(prefix, startName));
                fromInclusive = inclusive;
            } else if (forward) {
                from = prefixSegments;
                fromInclusive = false;
            } else {
                from = Keys.toSegments(after(prefix));
                fromInclusive = false;
            }
        }

        /**
         * Reads the next page, the keys after the last one visited.
         *
         * @throws bergdb.pub.util.LookupTimeNotAvailableException  If the lookup time is
         *     before the first available one.
         */
        private void readPage() {
            Db db = connection.getDb();
            GetMany g = db.newGetMany();
            Page p = new Page(prefixSegments);
            g.startKey = from;
            g.inclusive = fromInclusive;
            g.forward = forward;
            g.lookupTime = lookupTime;
            g.stopCondition = p;
            db.getMany(g);
            page = g.result;
            pos = 0;
            lastPage = !p.endedAtLimit;
            if (p.lastKey != null) {
                from = p.lastKey;
                fromInclusive = false;
            }
        }

        public boolean hasNext() {
            while (next == null) {
                if (pos < page.size()) {
                    Kvt kvt = page.get(pos++);
                    if (kvt.value == null) {
                        continue;
                    }
                    // A bkey without an ikey (written through the Core or by another
                    // writer; bergdb 021-06), or a key whose name has a '/', which is no
                    // user's key of the directory, is not listed.
                    String ikey = Keys.bkey2ikeyOrNull(Keys.toBytes(kvt.key));
                    if (ikey == null || ikey.indexOf('/', prefixIkeyLength) != -1) {
                        continue;
                    }
                    boolean listed = kind == ALL
                            || (kind == OBJECTS) == isObject(ikey, kvt.value);
                    if (listed) {
                        next = kvt;
                        nextIkey = ikey;
                    }
                } else if (lastPage) {
                    return false;
                } else {
                    readPage();
                }
            }
            return true;
        }

        /**
         * @throws bergdb.pub.ObjectCreationException  If the value cannot be made into the
         *     type, as for get(); the next call goes on with the next value.
         */
        public Kv<TYPE> next() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            final byte[] value = next.value;
            final String ikey = nextIkey;
            next = null;
            nextIkey = null;

            String ukey = PubKeys.i2u(ikey);    // a key of the directory, with no '/' in its name
            TYPE object = connection.getDatabaseImp().getKvToObjectConverter()
                    .createObject(type, ikey, value);
            return new PrimaryKv<TYPE>(ukey, object);
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * The stop condition of a page: the keys under the prefix, at most PAGE_KEYS of them,
     * PAGE_BYTES and PAGE_NANOS; it remembers the last key it visited.
     */
    private static final class Page implements GetMany.StopCondition {
        private final long[] prefix;
        private final long t0 = System.nanoTime();
        private int count = 0;
        private long bytes = 0;
        /** True if a limit ended the page, not the end of the prefix or of the database. */
        boolean endedAtLimit = false;
        /** The key of the last entry visited under the prefix, or null. */
        long[] lastKey = null;

        Page(long[] prefix) {
            this.prefix = prefix;
        }

        public int handleKvt(Kvt kvt) {
            if (!Keys.isPrefix(prefix, kvt.key)) {
                return STOP;
            }
            lastKey = kvt.key;
            count++;
            bytes += kvt.key.length * 8 + (kvt.value == null ? 0 : kvt.value.length);
            if (count >= PAGE_KEYS || bytes > PAGE_BYTES || System.nanoTime() - t0 > PAGE_NANOS) {
                endedAtLimit = true;
                return ADD_AND_STOP;
            }
            return ADD;
        }

        public void eod() {
        }
    }

    private static final class PrimaryKv<T> implements Kv<T> {
        private final String key;
        private final T value;

        PrimaryKv(String key, T value) {
            this.key = key;
            this.value = value;
        }

        public String key() {
            return key;
        }

        public T value() {
            return value;
        }
    }
}
