package bergdb.stream;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.Platform;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.StrictStream.Kind;

/**
 * The stream contract (2026-11-05, bergdb 018-02) on the streams of this package:
 * StreamContract's checks on FileStream, MemoryStream, OneFileStream, CutStream and
 * SalsaStream; FileStream's file-size limit; and StrictStream's own checks. DummyStream and
 * ReadOnlyStream are left out: they do not keep the contract by design (DummyStream keeps
 * only its first 10,000 bytes; ReadOnlyStream refuses appends and cuts).
 */
public class StreamContractTester {

    private static void check(TestEnvironment c, StreamContract.Impl impl) {
        StreamContract.Results results = new StreamContract.Results();
        StreamContract.check(impl, results);
        results.assertOk(c.out());
    }

    @Nano
    public static void testFileStream(final TestEnvironment c) {
        check(c, new StreamContract.Impl("FileStream",
                () -> new FileStream(c.createTempDir(), new StreamContract.NoForceIo())));
    }

    /** bergdb 015-33: with setMax2G(true), no file over 2 GB. */
    @Nano
    public static void testFileStreamSizeLimit(TestEnvironment c) {
        StreamContract.Results results = new StreamContract.Results();
        Throwable failure = null;
        try {
            String note = StreamContract.fileSizeLimit(c.createTempDir());
            if (note != null) {
                c.out().println("The file-size limit not checked: " + note);
                return;
            }
        } catch (Throwable e) {
            failure = e;
        }
        results.record("FileStream", "the file-size limit", failure, true);
        results.assertOk(c.out());
    }

    @Nano
    public static void testMemoryStream(TestEnvironment c) {
        check(c, new StreamContract.Impl("MemoryStream", () -> new MemoryStream()));
    }

    @Nano
    public static void testOneFileStream(final TestEnvironment c) {
        Platform.skipOnAndroid("OneFileStream, a stream for tests, seeks to a read's position, "
                + "and Android's lseek refuses one near Long.MAX_VALUE (EINVAL)");
        check(c, new StreamContract.Impl("OneFileStream",
                () -> new OneFileStream(new File(c.createTempDir(), "stream")))
                .cutBeyond(StreamContract.CutBeyond.IGNORED));
    }

    @Nano
    public static void testCutStream(TestEnvironment c) {
        check(c, new StreamContract.Impl("CutStream", () -> new CutStream()));
    }

    @Nano
    public static void testSalsaStream(TestEnvironment c) {
        check(c, new StreamContract.Impl("SalsaStream",
                () -> new SalsaStream(new MemoryStream(), new byte[8], new byte[32])));
    }

    // ======== StrictStream ========

    private static Kind kindOf(StrictStream s, StreamContract.Call call) {
        try {
            call.run();
        } catch (StrictStream.Breach e) {
            List<StrictStream.Breach> all = s.breaches();
            Assert.assertTrue("the breach is kept", all.get(all.size() - 1) == e);
            return e.kind;
        } catch (Exception e) {
            throw new AssertionError("threw " + e + ", not a Breach", e);
        }
        return null;
    }

    /** StrictStream refuses the caller's breaches. */
    @Nano
    public static void testStrictCaller() throws Exception {
        final StrictStream s = new StrictStream(new MemoryStream());
        Assert.assertEquals(Kind.ARGUMENT, kindOf(s, () -> s.append(new byte[1], 0, -1)));
        Assert.assertEquals(Kind.ARGUMENT, kindOf(s, () -> s.append(new byte[1], 0, 2)));
        Assert.assertEquals(Kind.ARGUMENT, kindOf(s, () -> s.read(0, new byte[1], 0, -1)));
        Assert.assertEquals(Kind.ARGUMENT, kindOf(s, () -> s.read(-1, new byte[1], 0, 0)));
        s.append(new byte[10], 0, 10);
        Assert.assertEquals(Kind.CUT_BEYOND_LENGTH, kindOf(s, () -> s.pretruncate(11)));
        Assert.assertEquals(Kind.ARGUMENT, kindOf(s, () -> s.pretruncate(-1)));
        Assert.assertEquals(null, kindOf(s, () -> s.pretruncate(10)));
        Assert.assertEquals(10, s.getLength());
        Assert.assertEquals(6, s.breaches().size());

        // One writer: an append held by the hook, and a cut from another thread.
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        s.setHook((op, n) -> {
            if (op == StrictStream.Op.APPEND) {
                entered.countDown();
                try {
                    release.await(5, TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
            }
        });
        Thread t = new Thread(() -> {
            try {
                s.append(new byte[1], 0, 1);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });
        t.start();
        entered.await();
        Assert.assertEquals(Kind.OVERLAP, kindOf(s, () -> s.pretruncate(5)));
        Assert.assertEquals(Kind.OVERLAP, kindOf(s, () -> s.getFirstPos()));
        s.tolerate(Kind.OVERLAP);
        Assert.assertEquals(null, kindOf(s, () -> s.getLength()));
        release.countDown();
        t.join();
        s.setHook(null);
        Assert.assertEquals(11, s.getLength());
        Assert.assertEquals(9, s.breaches().size());
        s.close();
    }

    /** A stream that breaks the contract in a way chosen by the test. */
    private static final class BadStream extends MemoryStream {
        String bad = "";

        @Override public synchronized void read(long position, byte[] dest, int off, int len)
                throws IOException {
            if (bad.equals("read") && position + len > getLength()) {
                throw new IOException("past the end");
            }
            if (bad.equals("silent")) {
                return;     // 'dest' as it was, as MemoryStream gave near Long.MAX_VALUE
            }
            super.read(position, dest, off, len);
            if (bad.equals("bytes") && len > 0) {
                dest[off] ^= 1;
            }
            if (bad.equals("eof")) {
                throw new EOFException("lost");
            }
        }

        @Override public synchronized void append(byte[] source, int off, int len)
                throws IOException {
            super.append(source, off, len);
            if (bad.equals("append")) {
                super.append(source, off, 1);
            }
        }

        @Override public synchronized void pretruncate(long spos) {
            if (bad.equals("cut")) {
                throw new IllegalStateException("bad cut");
            }
            super.pretruncate(spos);
        }
    }

    /** StrictStream finds the wrapped stream's breaches. */
    @Nano
    public static void testStrictWrapped() throws Exception {
        final BadStream bad = new BadStream();
        final StrictStream s = new StrictStream(bad);
        s.append(new byte[10], 0, 10);
        Assert.assertEquals(null, kindOf(s, () -> s.read(0, new byte[10], 0, 10)));
        Assert.assertEquals(null, kindOf(s, () -> {
            try {
                s.read(5, new byte[10], 0, 10);
            } catch (EOFException expected) {
                // Not a breach.
            }
        }));
        // A read whose end, position + len, overflows a long (bergdb 021-14): its
        // EOFException is not a breach (it was LOST), and a return is (it was none).
        Assert.assertEquals(null, kindOf(s, () -> {
            try {
                s.read(Long.MAX_VALUE - 2, new byte[4], 0, 4);
            } catch (EOFException expected) {
                // Not a breach.
            }
        }));
        bad.bad = "silent";
        Assert.assertEquals(Kind.NOT_EOF,
                kindOf(s, () -> s.read(Long.MAX_VALUE - 2, new byte[4], 0, 4)));
        bad.bad = "read";
        Assert.assertEquals(Kind.NOT_EOF, kindOf(s, () -> s.read(5, new byte[10], 0, 10)));
        bad.bad = "bytes";
        Assert.assertEquals(Kind.BYTES, kindOf(s, () -> s.read(0, new byte[10], 0, 10)));
        bad.bad = "eof";
        Assert.assertEquals(Kind.LOST, kindOf(s, () -> s.read(0, new byte[10], 0, 10)));
        bad.bad = "cut";
        Assert.assertEquals(Kind.UNCHECKED, kindOf(s, () -> s.pretruncate(10)));
        bad.bad = "append";
        Assert.assertEquals(Kind.LENGTH, kindOf(s, () -> s.append(new byte[2], 0, 2)));
        Assert.assertEquals(6, s.breaches().size());
        s.close();
    }
}
