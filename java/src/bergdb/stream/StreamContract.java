package bergdb.stream;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * The shared contract tester of AppendOnlyStream (2026-11-05, bergdb 018-02): the checks
 * that every implementation passes, at the edges of the interface's Javadoc, and the list of
 * known faults that the harness skips. StreamContractTester runs it on the streams of this
 * package, bergdb.storage.StorageContractTester on BufferedStream and StorageManager.
 *
 * <p>Each check gets a new stream from the implementation's Factory and closes it. The
 * checks: an empty stream; length 0; appends and reads; a negative append, and one longer
 * than its array; a negative read, and one longer than its array; a read past the end, at
 * it, across it and beyond it; a read below the first position after a cut; cuts within the
 * length; a cut at the length, on an empty stream and on one with bytes; a cut beyond the
 * length, refused (or held, or ignored, as the Javadoc says of BufferedStream and
 * OneFileStream); close(). And FileStream's file-size limit, fileSizeLimit().</p>
 *
 * <p>A failed check is a fault. If FAULTS names its entry and SKIP has the entry, it is a
 * known fault and is skipped; else the test fails, and names the entry, or says that the
 * fault has none. A line of SKIP whose checks all pass also fails the test: a fix removes
 * its own line (bergdb 018-02, section 5). With the system property bergdb.contract.skip set
 * to "none", nothing is skipped, and the test shows every known fault.</p>
 */
public final class StreamContract {

    /**
     * The known faults that the harness skips (bergdb 018-02, section 5), one line per
     * entry. A fix removes its entry's line.
     */
    static final String[] SKIP = {
        "015-80",
        "019-02",
    };

    /**
     * The entry of a failed check: the implementation (* for any), the start of the check's
     * name, the entry. The first row that matches counts.
     */
    static final String[][] FAULTS = {
        {"FileStream",      "a negative append",                "015-26"},
        {"FileStream",      "a cut at the length",              "015-31"},
        {"FileStream",      "the file-size limit",              "015-33"},
        {"BufferedStream",  "a negative append",                "015-79"},
        {"StorageManager",  "a negative append",                "015-79"},
        {"BufferedStream",  "one writer",                       "015-80"},
        {"StorageManager",  "one writer",                       "015-80"},
        {"BufferedStream",  "a read past the end",              "015-83"},
        {"StorageManager",  "a read past the end",              "015-83"},
        {"BufferedStream",  "an empty stream",                  "015-83"},
        {"StorageManager",  "an empty stream",                  "015-83"},
        {"OneFileStream",   "a negative append",                "019-02"},
        {"SalsaStream",     "a negative append",                "019-02"},
        {"*",               "an append longer than its array",  "019-02"},
        {"*",               "a negative read",                  "019-02"},
        {"*",               "a read longer than its array",     "019-02"},
    };

    private StreamContract() {}

    /** Makes a new, empty stream for one check. */
    public interface Factory {
        AppendOnlyStream create() throws IOException;
    }

    /** What a stream does with a cut beyond its length; the Javadoc of pretruncate(). */
    public enum CutBeyond { REFUSED, HELD, IGNORED }

    /** An implementation to check. */
    public static final class Impl {
        final String name;
        final Factory factory;
        CutBeyond cutBeyond = CutBeyond.REFUSED;

        public Impl(String name, Factory factory) {
            this.name = name;
            this.factory = factory;
        }

        public Impl cutBeyond(CutBeyond c) {
            this.cutBeyond = c;
            return this;
        }
    }

    /** A check on a new stream. */
    interface Check {
        void run(AppendOnlyStream s, Impl impl) throws Exception;
    }

    /** Runs every check on 'impl'; adds what they find to 'results'. */
    public static void check(Impl impl, Results results) {
        check(results, impl, "an empty stream", StreamContract::emptyStream);
        check(results, impl, "length 0", StreamContract::lengthZero);
        check(results, impl, "appends and reads", StreamContract::appendsAndReads);
        check(results, impl, "a negative append", StreamContract::negativeAppend);
        check(results, impl, "an append longer than its array", StreamContract::longAppend);
        check(results, impl, "a negative read", StreamContract::negativeRead);
        check(results, impl, "a read longer than its array", StreamContract::longRead);
        for (final long[] r : new long[][] {{10, 1}, {8, 4}, {1000, 1}}) {
            check(results, impl, "a read past the end, " + r[1] + " bytes at " + r[0]
                    + " of 10", (s, i) -> readPastEnd(s, r[0], (int) r[1]));
        }
        check(results, impl, "a read below the first position", StreamContract::readBelowFirst);
        check(results, impl, "cuts within the length", StreamContract::cutsWithin);
        check(results, impl, "a cut at the length, 0", StreamContract::cutAtLengthEmpty);
        check(results, impl, "a cut at the length, 3", StreamContract::cutAtLength);
        check(results, impl, "a cut beyond the length", StreamContract::cutBeyond);
        check(results, impl, "close()", (s, i) -> {
            append(s, 5);
            s.close();
        });
    }

    private static void check(Results results, Impl impl, String name, Check check) {
        Throwable failure = null;
        AppendOnlyStream s = null;
        try {
            s = impl.factory.create();
            check.run(s, impl);
        } catch (Throwable e) {
            failure = e;
        } finally {
            if (s != null) {
                try {
                    s.close();
                } catch (Throwable e) {
                    // Not this check's subject; close() has its own.
                }
            }
        }
        results.record(impl.name, name, failure, true);
    }

    // ======== The checks ========

    /** The byte at stream position 'pos', in every check. */
    public static byte at(long pos) {
        return (byte) (pos * 31 + 7);
    }

    /** Appends n bytes of at(), from the stream's length. */
    static void append(AppendOnlyStream s, int n) throws IOException {
        long from = s.getLength();
        byte[] b = new byte[n];
        for (int i = 0; i < n; i++) {
            b[i] = at(from + i);
        }
        s.append(b, 0, n);
        expect("the length after an append of " + n + " at " + from, from + n, s.getLength());
    }

    /** Reads n bytes at 'pos' and compares them with at(). */
    static void readAndCompare(AppendOnlyStream s, long pos, int n) throws IOException {
        byte[] b = new byte[n + 2];
        s.read(pos, b, 1, n);
        for (int i = 0; i < n; i++) {
            if (b[1 + i] != at(pos + i)) {
                throw new AssertionError("read(" + pos + ", " + n + "): byte " + b[1 + i]
                        + " at " + (pos + i) + ", where " + at(pos + i) + " was appended");
            }
        }
    }

    public static void expect(String what, long expected, long actual) {
        if (expected != actual) {
            throw new AssertionError(what + " is " + actual + ", expected " + expected);
        }
    }

    /** Runs 'call', which must throw an exception of class 'expected'. */
    static void expectThrows(String what, Class<? extends Throwable> expected, Call call) {
        try {
            call.run();
        } catch (Throwable e) {
            if (expected.isInstance(e)) {
                return;
            }
            AssertionError a = new AssertionError(what + " threw " + e + ", expected "
                    + expected.getSimpleName());
            a.initCause(e);
            throw a;
        }
        throw new AssertionError(what + " returned, expected " + expected.getSimpleName());
    }

    interface Call {
        void run() throws Exception;
    }

    private static void emptyStream(AppendOnlyStream s, Impl impl) throws IOException {
        expect("the length of a new stream", 0, s.getLength());
        expect("the first position of a new stream", 0, s.getFirstPos());
        s.read(0, new byte[1], 0, 0);
        // Last: a StorageManager fails at a read past the end, by design (bergdb 018-02,
        // section 2.2, item 8). The first append of a new stream is checked by lengthZero.
        expectThrows("read(0, 1) of an empty stream", EOFException.class,
                () -> s.read(0, new byte[1], 0, 1));
    }

    private static void lengthZero(AppendOnlyStream s, Impl impl) throws IOException {
        s.append(new byte[0], 0, 0);
        expect("the length after an append of 0 bytes", 0, s.getLength());
        append(s, 10);
        s.append(new byte[5], 3, 0);
        expect("the length after an append of 0 bytes", 10, s.getLength());
        s.read(10, new byte[1], 0, 0);
        s.read(4, new byte[1], 1, 0);
        readAndCompare(s, 0, 10);
    }

    private static void appendsAndReads(AppendOnlyStream s, Impl impl) throws IOException {
        int[] sizes = {1, 7, 1000, 70000, 3};
        for (int n : sizes) {
            append(s, n);
        }
        long length = s.getLength();
        readAndCompare(s, 0, (int) length);
        readAndCompare(s, 5, 10);
        readAndCompare(s, length - 1, 1);
        readAndCompare(s, 1000, 50000);
    }

    private static void negativeAppend(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 3);
        expectThrows("append(byte[1], 0, -1)", IllegalArgumentException.class,
                () -> s.append(new byte[1], 0, -1));
        expect("the length after a refused append", 3, s.getLength());
        readAndCompare(s, 2, 1);
        append(s, 1);
        readAndCompare(s, 0, 4);
    }

    private static void longAppend(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 3);
        expectThrows("append(byte[5], 0, 6)", IllegalArgumentException.class,
                () -> s.append(new byte[5], 0, 6));
        expect("the length after a refused append", 3, s.getLength());
        append(s, 1);
        readAndCompare(s, 0, 4);
    }

    private static void negativeRead(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 10);
        expectThrows("read(0, byte[4], 0, -1)", IllegalArgumentException.class,
                () -> s.read(0, new byte[4], 0, -1));
        readAndCompare(s, 0, 10);
        append(s, 1);
        readAndCompare(s, 0, 11);
    }

    private static void longRead(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 10);
        expectThrows("read(0, byte[4], 0, 5)", IllegalArgumentException.class,
                () -> s.read(0, new byte[4], 0, 5));
        readAndCompare(s, 0, 10);
        append(s, 1);
        readAndCompare(s, 0, 11);
    }

    private static void readPastEnd(AppendOnlyStream s, long pos, int n) throws IOException {
        append(s, 10);
        expectThrows("read(" + pos + ", " + n + ") of 10 bytes", EOFException.class,
                () -> s.read(pos, new byte[n], 0, n));
    }

    private static void readBelowFirst(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 1300 * 1000);
        append(s, 1200 * 1000);
        long cut = 2100 * 1000;
        s.pretruncate(cut);
        expect("the length after a cut", 2500 * 1000, s.getLength());
        long first = s.getFirstPos();
        if (first > cut) {
            throw new AssertionError("the first position after a cut at " + cut + " is " + first);
        }
        readAndCompare(s, cut, 1000);
        if (first > 0) {
            expectThrows("read(" + (first - 1) + ", 1), below the first position, " + first,
                    ReadBelowFirstPosException.class, () -> s.read(first - 1, new byte[1], 0, 1));
        }
        append(s, 10);
        readAndCompare(s, cut, 400 * 1000 + 10);
    }

    private static void cutsWithin(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 1000);
        for (long cut : new long[] {0, 300, 300, 999}) {
            s.pretruncate(cut);
            expect("the length after a cut at " + cut, 1000, s.getLength());
            long first = s.getFirstPos();
            if (first > cut) {
                throw new AssertionError("the first position after a cut at " + cut + " is "
                        + first);
            }
            readAndCompare(s, cut, (int) (1000 - cut));
        }
        append(s, 5);
        readAndCompare(s, 999, 6);
    }

    private static void cutAtLengthEmpty(AppendOnlyStream s, Impl impl) throws IOException {
        s.pretruncate(0);
        expect("the length after a cut at 0 of an empty stream", 0, s.getLength());
        append(s, 1);
        readAndCompare(s, 0, 1);
    }

    private static void cutAtLength(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 3);
        s.pretruncate(3);
        expect("the length after a cut at the length", 3, s.getLength());
        append(s, 1);
        readAndCompare(s, 3, 1);
    }

    private static void cutBeyond(AppendOnlyStream s, Impl impl) throws IOException {
        append(s, 10);
        long first = s.getFirstPos();
        if (impl.cutBeyond == CutBeyond.REFUSED) {
            try {
                s.pretruncate(11);
                throw new AssertionError("pretruncate(11) of 10 bytes returned; refused, "
                        + "expected");
            } catch (IllegalArgumentException | IOException expected) {
                // As the Javadoc says.
            }
            expect("the length after a refused cut", 10, s.getLength());
            expect("the first position after a refused cut", first, s.getFirstPos());
            readAndCompare(s, 0, 10);
        } else {
            s.pretruncate(11);
            expect("the length after a cut beyond the length", 10, s.getLength());
        }
        append(s, 5);
        readAndCompare(s, 11, 4);
        if (s.getFirstPos() > 11) {
            throw new AssertionError("the first position after a cut at 11 is "
                    + s.getFirstPos());
        }
    }

    // ======== FileStream's file-size limit ========

    private static final long M100 = 100 * 1000 * 1000L;
    private static final long G2 = 2000 * 1000 * 1000L;

    /**
     * FileStream's file-size limit: with setMax2G(true), no file over 2 GB (bergdb 015-33,
     * review R2-F4). The directory is the one R2-F4's probe makes, with 400 restarts that
     * write 100 MB each, made directly: 400 files of 100 MB, sparse, 40 GB in all, so that a
     * start chooses 100 MB files from the last two, and the next file the size rule's 10 GB
     * (a quarter of what the stream holds). Then 2.1 GB of appends. Writes are sparse and
     * nothing is forced (SparseIo): the size of the files is the subject. Under a second, and
     * no disk space, on a file system with sparse files; on one without, it says so and
     * passes, as it would write 42 GB.
     *
     * @return  Null, or why the check did not run.
     */
    static String fileSizeLimit(File dir) throws IOException {
        File probe = new File(dir, "sparse-probe");
        long free = dir.getUsableSpace();
        try (RandomAccessFile r = new RandomAccessFile(probe, "rw")) {
            r.setLength(10 * M100);
        }
        long used = free - dir.getUsableSpace();
        if (!probe.delete()) {
            throw new IOException("could not delete " + probe);
        }
        if (used > 5 * M100) {
            return "no sparse files here: a 1 GB file took " + used + " bytes";
        }

        for (int i = 0; i < 400; i++) {
            String index = "" + i * (M100 / 100000);
            String name = "00000000000000".substring(index.length()) + index + ".bergdb";
            try (RandomAccessFile r = new RandomAccessFile(new File(dir, name), "rw")) {
                r.setLength(M100);
            }
        }
        FileStream s = new FileStream(dir, new SparseIo());
        try {
            s.setMax2G(true);
            expect("the length of 400 files of 100 MB", 400 * M100, s.getLength());
            byte[] mb = new byte[1000 * 1000];
            for (int i = 0; i < 2100; i++) {
                s.append(mb, 0, mb.length);
            }
        } finally {
            s.close();
        }
        for (File f : dir.listFiles()) {
            if (f.length() > G2) {
                throw new AssertionError("with setMax2G(true), the file " + f.getName()
                        + " has " + f.length() + " bytes, more than 2 GB");
            }
        }
        return null;
    }

    /** Sparse writes and no forces: for the size of the files, not their bytes. */
    static final class SparseIo extends FileStreamIo {
        protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset,
                int length) throws IOException {
            long end = handle.getFilePointer() + length;
            handle.setLength(end);
            handle.seek(end);
        }

        protected void forceFile(File file, RandomAccessFile handle) {}

        protected void forceDirectory(File dir) {}
    }

    /** Writes, and no forces: durability is not the contract's subject, and forces are slow. */
    public static final class NoForceIo extends FileStreamIo {
        protected void forceFile(File file, RandomAccessFile handle) {}

        protected void forceDirectory(File dir) {}
    }

    // ======== Results ========

    /** What the checks found, and what the skip list makes of it. */
    public static final class Results {
        private final List<String[]> failures = new ArrayList<String[]>();
        private final Map<String, Boolean> entryFailed = new TreeMap<String, Boolean>();
        private int count = 0;

        /**
         * Records a check: passed if 'failure' is null. 'stale' says that the check is
         * deterministic: if it is an entry's and passes, the entry is fixed.
         */
        public synchronized void record(String impl, String check, Throwable failure,
                boolean stale) {
            count++;
            String entry = entryOf(impl, check);
            if (entry != null && stale) {
                Boolean before = entryFailed.get(entry);
                entryFailed.put(entry, (before != null && before) || failure != null);
            }
            if (failure != null) {
                failures.add(new String[] {entry, impl + ", " + check + ": "
                        + describe(failure)});
            }
        }

        /** Throws an AssertionError if a fault is not skipped, or a skip line is stale. */
        public synchronized void assertOk(PrintStream out) {
            Set<String> skip = skipList();
            List<String> problems = new ArrayList<String>();
            int known = 0;
            for (String[] f : failures) {
                if (f[0] != null && skip.contains(f[0])) {
                    out.println("Known fault " + f[0] + ", skipped: " + f[1]);
                    known++;
                } else if (f[0] != null) {
                    problems.add(f[0] + ": " + f[1]);
                } else {
                    problems.add("No entry, a new fault: " + f[1]);
                }
            }
            for (Map.Entry<String, Boolean> e : entryFailed.entrySet()) {
                if (!e.getValue() && skip.contains(e.getKey())) {
                    problems.add(e.getKey() + ": in the skip list, StreamContract.SKIP, but its "
                            + "checks pass; its fix removes the line");
                }
            }
            out.println(count + " checks, " + known + " known faults skipped, " + problems.size()
                    + " failed");
            if (!problems.isEmpty()) {
                StringBuilder b = new StringBuilder("The stream contract (bergdb 018-02), "
                        + problems.size() + " failed:");
                for (String p : problems) {
                    b.append("\n  ").append(p);
                }
                throw new AssertionError(b.toString());
            }
        }
    }

    /** The entry of a failed check, or null. */
    static String entryOf(String impl, String check) {
        for (String[] row : FAULTS) {
            if ((row[0].equals(impl) || row[0].equals("*")) && check.startsWith(row[1])) {
                return row[2];
            }
        }
        return null;
    }

    /** Whether the skip list has 'entry'. */
    public static boolean skipped(String entry) {
        return skipList().contains(entry);
    }
    
    /** SKIP; empty with -Dbergdb.contract.skip=none. */
    static Set<String> skipList() {
        if ("none".equals(System.getProperty("bergdb.contract.skip"))) {
            return new HashSet<String>();
        }
        return new HashSet<String>(Arrays.asList(SKIP));
    }

    /** The failure, with the place in BergDB's code that threw it. */
    static String describe(Throwable failure) {
        StringBuilder b = new StringBuilder(failure.toString());
        Throwable t = failure.getCause() != null ? failure.getCause() : failure;
        if (t != failure) {
            b.append("; cause ").append(t);
        }
        StackTraceElement[] trace = t.getStackTrace();
        if (trace.length > 0 && trace[0].getClassName().equals(StreamContract.class.getName())) {
            return b.toString();    // A check's own failure: its message says it.
        }
        for (StackTraceElement e : trace) {
            if (e.getClassName().startsWith("bergdb.")
                    && !e.getClassName().startsWith(StreamContract.class.getName())) {
                b.append(" (at ").append(e.getClassName().substring(7)).append('.')
                        .append(e.getMethodName()).append(':').append(e.getLineNumber())
                        .append(')');
                break;
            }
        }
        return b.toString();
    }
}
