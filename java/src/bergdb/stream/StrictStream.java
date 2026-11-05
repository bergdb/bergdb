package bergdb.stream;

import java.io.EOFException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

/**
 * A strict AppendOnlyStream for tests (2026-11-05, bergdb 018-02): it wraps a stream and
 * checks each call against AppendOnlyStream's Javadoc, on both sides, and throws Breach at
 * once on a breach. The harness of the stream contract (bergdb 018-01, section 6.3) puts it
 * under BufferedStream and StorageManager.
 *
 * <p>The caller's side, the layer above: one writer at a time, every call but read() made
 * by one thread at a time, as CONCURRENCY says (OVERLAP; getLength() and getFirstPos()
 * included, which need the write lock too); no negative length, no length past the array,
 * no negative position (ARGUMENT); no cut past the length (CUT_BEYOND_LENGTH). The Javadoc
 * says what a stream does with such a call; a layer of BergDB must not make one.</p>
 *
 * <p>The wrapped stream's side: after an append, the length grows by the bytes appended;
 * getLength() returns that length, which never decreases (LENGTH); getFirstPos() never
 * decreases and stays at or below the length and the last cut (FIRST_POS); a read past the
 * end throws EOFException (NOT_EOF), one of bytes that are there returns them, not
 * EOFException or ReadBelowFirstPosException (LOST), and returns the bytes that were
 * appended (BYTES; the first 16 MB appended through this stream are kept to compare); a
 * call that the caller made by the rules throws no unchecked exception (UNCHECKED).</p>
 *
 * <p>Every breach is kept: breaches(). A test asserts that there is none after a run, also
 * when the Breach was thrown in a thread of the code under test and caught there
 * (BufferedStream's thread turns what a flush throws into a failure of the stream).
 * tolerate() makes a kind kept but not thrown: a test that runs a workload while a known
 * fault is open (bergdb 018-02, section 5) can go on past it.</p>
 *
 * <p>A Hook sees each call before the wrapped stream does, inside the call's writer section:
 * a test can hold a call there, as BufferedStream's test of one writer does, and harness 6.2
 * of bergdb 018-01 can count the calls (the number given to the hook) and make one fail.</p>
 */
public class StrictStream implements AppendOnlyStream {

    /** The calls of AppendOnlyStream. */
    public enum Op { GET_LENGTH, GET_FIRST_POS, READ, APPEND, PRETRUNCATE, CLOSE }

    /** The kinds of breach; see the class's Javadoc. */
    public enum Kind {
        OVERLAP, ARGUMENT, CUT_BEYOND_LENGTH,
        LENGTH, FIRST_POS, NOT_EOF, LOST, BYTES, UNCHECKED
    }

    /** A breach of AppendOnlyStream's contract. An Error, as a failed assertion. */
    public static final class Breach extends AssertionError {
        private static final long serialVersionUID = 1L;
        public final Kind kind;

        Breach(Kind kind, String message, Throwable cause) {
            super(kind + ": " + message, cause);
            this.kind = kind;
        }
    }

    /**
     * Sees each call before the wrapped stream does; for a non-read call, while the call
     * holds the writer's place. It can wait, count, or throw (an IOException, an unchecked
     * exception or an Error), and what it throws goes to the caller unchecked.
     */
    public interface Hook {
        /** @param n  The number of the call, from 1, over all calls of this stream. */
        void before(Op op, long n) throws IOException;
    }

    private static final int MAX_KEPT = 16 * 1000 * 1000;

    private final AppendOnlyStream inner;
    private final AtomicReference<String> writer = new AtomicReference<String>();
    private final AtomicLong calls = new AtomicLong();
    private final List<Breach> breaches = new ArrayList<Breach>();
    private final Set<Kind> tolerated = EnumSet.noneOf(Kind.class);
    private volatile Hook hook = null;

    /** The length: the bytes appended through this stream so far. Set by the writer. */
    private volatile long length;
    /** The length and the bytes of an append in progress: a read may see them already. */
    private volatile long lengthUpper;
    /** The highest cut so far: bytes from it are kept. */
    private volatile long keptFrom;
    /** The highest first position returned so far. Writer only. */
    private long firstPos;
    /** After a failed call or close(), a read may fail as the stream likes. */
    private volatile boolean failedOrClosed = false;

    /** The bytes appended, from position 'keptStart', while they fit MAX_KEPT. Under keptLock. */
    private final Object keptLock = new Object();
    private long keptStart;
    private byte[] kept = new byte[1024];
    private int keptLength = 0;
    private boolean keptFull = false;

    /** Wraps 'inner', which may hold bytes already: their length and first position count. */
    public StrictStream(AppendOnlyStream inner) {
        if (inner == null) {
            throw new IllegalArgumentException("inner == null not allowed");
        }
        this.inner = inner;
        this.length = inner.getLength();
        this.lengthUpper = length;
        this.firstPos = inner.getFirstPos();
        this.keptFrom = firstPos;
        this.keptStart = length;
    }

    public AppendOnlyStream getInner() {
        return inner;
    }

    public void setHook(Hook hook) {
        this.hook = hook;
    }

    /** Makes breaches of these kinds kept, not thrown. */
    public synchronized void tolerate(Kind... kinds) {
        tolerated.addAll(Arrays.asList(kinds));
    }

    /** The breaches so far, first first. */
    public synchronized List<Breach> breaches() {
        return new ArrayList<Breach>(breaches);
    }

    /** The number of calls so far. */
    public long calls() {
        return calls.get();
    }

    // ======== AppendOnlyStream ========

    public long getLength() {
        boolean w = enter(Op.GET_LENGTH);
        try {
            callHookUnchecked(Op.GET_LENGTH);
            long result = inner.getLength();
            if (result != length) {
                breach(Kind.LENGTH, "getLength() returned " + result + ", but " + length
                        + " bytes have been appended", null);
            }
            return result;
        } finally {
            exit(w);
        }
    }

    public long getFirstPos() {
        boolean w = enter(Op.GET_FIRST_POS);
        try {
            callHookUnchecked(Op.GET_FIRST_POS);
            long result = inner.getFirstPos();
            checkFirstPos(result, "getFirstPos()");
            return result;
        } finally {
            exit(w);
        }
    }

    public void read(long position, byte[] dest, int destOffset, int len) throws IOException {
        if (dest == null || position < 0 || len < 0 || destOffset < 0
                || len > dest.length - destOffset) {
            breach(Kind.ARGUMENT, "read(" + position + ", byte[" + (dest == null ? "null"
                    : dest.length) + "], " + destOffset + ", " + len + ")", null);
        }
        long end = position + len;
        long lengthBefore = length;
        callHook(Op.READ);
        try {
            inner.read(position, dest, destOffset, len);
        } catch (EOFException e) {
            if (end <= lengthBefore && position >= keptFrom && !failedOrClosed) {
                breach(Kind.LOST, "read(" + position + ", " + len + ") threw EOFException, "
                        + "but the length was " + lengthBefore + " when it began", e);
            }
            throw e;
        } catch (ReadBelowFirstPosException e) {
            if (len > 0 && position >= keptFrom) {
                breach(Kind.LOST, "read(" + position + ", " + len + ") threw "
                        + "ReadBelowFirstPosException, but no cut is above " + keptFrom, e);
            }
            throw e;
        } catch (IOException e) {
            if (end > lengthUpper && !failedOrClosed) {
                breach(Kind.NOT_EOF, "read(" + position + ", " + len + ") past the end, at "
                        + length + ", threw " + e + ", not EOFException", e);
            }
            throw e;
        } catch (RuntimeException | Error e) {
            if (e instanceof Breach) throw e;
            breach(Kind.UNCHECKED, "read(" + position + ", " + len + ") threw " + e, e);
            throw e;
        }
        if (end > lengthUpper) {
            breach(Kind.NOT_EOF, "read(" + position + ", " + len + ") past the end, at "
                    + length + ", returned", null);
        }
        compareKept(position, dest, destOffset, len);
    }

    public void append(byte[] source, int sourceOffset, int len) throws IOException {
        boolean w = enter(Op.APPEND);
        try {
            if (source == null || len < 0 || sourceOffset < 0
                    || len > source.length - sourceOffset) {
                breach(Kind.ARGUMENT, "append(byte[" + (source == null ? "null" : source.length)
                        + "], " + sourceOffset + ", " + len + ")", null);
            }
            callHook(Op.APPEND);
            long before = length;
            lengthUpper = before + len;
            try {
                inner.append(source, sourceOffset, len);
            } catch (IOException e) {
                afterFailedAppend(before);
                throw e;
            } catch (RuntimeException | Error e) {
                afterFailedAppend(before);
                if (e instanceof Breach) throw e;
                breach(Kind.UNCHECKED, "append of " + len + " bytes at " + before + " threw "
                        + e, e);
                throw e;
            }
            keep(source, sourceOffset, len);
            length = before + len;
            long result = inner.getLength();
            if (result != length) {
                breach(Kind.LENGTH, "the length after an append of " + len + " bytes at "
                        + before + " is " + result + ", not " + length, null);
            }
        } finally {
            exit(w);
        }
    }

    public void pretruncate(long position) throws IOException {
        boolean w = enter(Op.PRETRUNCATE);
        try {
            if (position < 0) {
                breach(Kind.ARGUMENT, "pretruncate(" + position + ")", null);
            }
            if (position > length) {
                breach(Kind.CUT_BEYOND_LENGTH, "pretruncate(" + position + "), beyond the "
                        + "length, " + length, null);
            }
            callHook(Op.PRETRUNCATE);
            try {
                inner.pretruncate(position);
            } catch (IOException e) {
                failedOrClosed = true;
                throw e;
            } catch (RuntimeException | Error e) {
                if (e instanceof Breach) throw e;
                breach(Kind.UNCHECKED, "pretruncate(" + position + "), at or below the length, "
                        + length + ", threw " + e, e);
                throw e;
            }
            if (position > keptFrom) {
                keptFrom = position;
            }
            checkFirstPos(inner.getFirstPos(), "getFirstPos() after pretruncate(" + position
                    + ")");
        } finally {
            exit(w);
        }
    }

    public void close() throws IOException {
        boolean w = enter(Op.CLOSE);
        try {
            failedOrClosed = true;
            callHook(Op.CLOSE);
            inner.close();
        } finally {
            exit(w);
        }
    }

    // ======== The checks ========

    /**
     * Takes the writer's place and returns true, or throws OVERLAP; returns false if OVERLAP
     * is tolerated, and the call goes on beside the other.
     */
    private boolean enter(Op op) {
        String me = op + " in thread " + Thread.currentThread().getName();
        if (writer.compareAndSet(null, me)) {
            return true;
        }
        breach(Kind.OVERLAP, me + " overlaps " + writer.get() + ": one writer at a time", null);
        return false;
    }

    private void exit(boolean entered) {
        if (entered) {
            writer.set(null);
        }
    }

    /** For getLength() and getFirstPos(), which throw no IOException: one is wrapped. */
    private void callHookUnchecked(Op op) {
        try {
            callHook(op);
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }

    private void callHook(Op op) throws IOException {
        long n = calls.incrementAndGet();
        Hook h = hook;
        if (h != null) {
            h.before(op, n);
        }
    }

    private void breach(Kind kind, String message, Throwable cause) {
        Breach b = new Breach(kind, message, cause);
        synchronized (this) {
            breaches.add(b);
            if (tolerated.contains(kind)) {
                return;
            }
        }
        throw b;
    }

    /** Writer only. */
    private void checkFirstPos(long f, String what) {
        if (f < firstPos || f > length || f > keptFrom) {
            breach(Kind.FIRST_POS, what + " is " + f + "; it was " + firstPos + ", the length is "
                    + length + ", and the bytes from " + keptFrom + " are kept", null);
        }
        if (f > firstPos) {
            firstPos = f;
        }
    }

    /** After a failed append: the length may have grown, not decreased; the bytes are lost. */
    private void afterFailedAppend(long before) {
        failedOrClosed = true;
        long l = inner.getLength();
        if (l < before) {
            breach(Kind.LENGTH, "the length decreased from " + before + " to " + l
                    + " in a failed append", null);
        }
        length = Math.max(before, l);
        lengthUpper = length;
        synchronized (keptLock) {
            keptFull = true;
        }
    }

    private void keep(byte[] source, int offset, int len) {
        synchronized (keptLock) {
            if (keptFull || keptLength + (long) len > MAX_KEPT) {
                keptFull = true;
                return;
            }
            if (keptLength + len > kept.length) {
                kept = Arrays.copyOf(kept, Math.max(keptLength + len, 2 * kept.length));
            }
            System.arraycopy(source, offset, kept, keptLength, len);
            keptLength += len;
        }
    }

    private void compareKept(long position, byte[] dest, int destOffset, int len) {
        synchronized (keptLock) {
            for (int i = 0; i < len; i++) {
                long k = position + i - keptStart;
                if (k < 0) {
                    continue;
                }
                if (k >= keptLength) {
                    break;
                }
                if (dest[destOffset + i] != kept[(int) k]) {
                    breach(Kind.BYTES, "read(" + position + ", " + len + ") returned "
                            + dest[destOffset + i] + " at " + (position + i) + ", where "
                            + kept[(int) k] + " was appended", null);
                    return;
                }
            }
        }
    }
}
