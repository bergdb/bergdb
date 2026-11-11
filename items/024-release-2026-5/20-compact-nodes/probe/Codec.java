package bergdb.core;

import java.io.*;
import java.util.*;

/**
 * bergdb 024-20: encoding C of a key node's body (section 4.9 of the item), a round trip over
 * real nodes, and a micro-benchmark of writing and reading against today's format 2. Written
 * 2026-11-11. Not product code.
 *
 * Encoding C, after today's 8-byte node header (size, type 20, format, checksum):
 *   byte      leaf << 7 | n                  (n at most 127)
 *   varint    off, the node's offset in its record's bytes (so a node read alone finds its
 *             record's start tpos, as a value node does with its stored offset)
 *   varint    zigzag(id - tpos)
 *   ref       prevPos
 * A ref is relative to tpos: varint 0 for -1; 2d + 1 for the position d bytes before tpos;
 * 2 and then a u32 x for the position tpos + x (a node of the same record, whose position is
 * not known when this node's size is computed, so of a fixed width).
 *   n entries, each a tag byte and its fields:
 *     time    tag 0x00; varint: the time for the node's first time klong, else zigzag(t - t')
 *             with t' the time klong before it
 *     key     tag 0x40 | len << 3 | s, s the leading data bytes shared with the key klong
 *             before it in the node (0 for the first); then len - s data bytes; then the ref
 *     bitmap  tag 0xc0 | c, c the bits set that the bitmap before it in the node did not set;
 *             then c bytes, each a bit index from 0 to 61
 * A node that cannot be so encoded (a bitmap that clears a bit, n over 127, a key klong with
 * bits 0 to 2 set, a time klong with bits 56 to 61 set, a time klong's or bitmap's ref other
 * than -1), or whose encoding C is longer than 32 + 16 n bytes, is written in format 2.
 *
 * java -cp ... bergdb.core.Codec DUMPFILE [rounds]
 */
public class Codec {

    // ---- encoding C ----

    static int putV(byte[] b, int o, long x) {
        while ((x & ~0x7fL) != 0) {
            b[o++] = (byte) ((x & 0x7f) | 0x80);
            x >>>= 7;
        }
        b[o++] = (byte) x;
        return o;
    }

    static long zz(long x) { return (x << 1) ^ (x >> 63); }

    static long unzz(long x) { return (x >>> 1) ^ -(x & 1); }

    static int ref(byte[] b, int o, long tpos, long r) {
        if (r == -1) return putV(b, o, 0);
        if (r < tpos) return putV(b, o, 2 * (tpos - r) + 1);
        b[o++] = 2;
        long x = r - tpos;
        for (int j = 0; j < 4; j++) b[o++] = (byte) (x >>> (8 * j));
        return o;
    }

    /** Encodes the body; returns the end offset, or -1 if the node needs format 2. */
    static int encode(long tpos, int off, long id, long prev, boolean leaf, long[] kl, long[] rf,
            int n, byte[] b, int o) {
        if (n > 127) return -1;
        b[o++] = (byte) ((leaf ? 0x80 : 0) | n);
        o = putV(b, o, off);
        o = putV(b, o, zz(id - tpos));
        o = ref(b, o, tpos, prev);
        long prevKey = -1, prevTime = -1, prevBmp = 0;
        for (int i = 0; i < n; i++) {
            long k = kl[i];
            int t = (int) (k >>> 62);
            if (t == 0) {
                if ((k >>> 56) != 0 || rf[i] != -1) return -1;
                b[o++] = 0;
                o = putV(b, o, prevTime < 0 ? k : zz(k - prevTime));
                prevTime = k;
            } else if (t == 1) {
                if ((k & 7) != 0) return -1;
                int len = (int) ((k >>> 3) & 7);
                int s = 0;
                if (prevKey >= 0) {
                    int pl = (int) ((prevKey >>> 3) & 7);
                    while (s < len && s < pl
                            && ((k >>> (54 - 8 * s)) & 0xff) == ((prevKey >>> (54 - 8 * s)) & 0xff)) {
                        s++;
                    }
                }
                b[o++] = (byte) (0x40 | len << 3 | s);
                for (int j = s; j < len; j++) b[o++] = (byte) (k >>> (54 - 8 * j));
                o = ref(b, o, tpos, rf[i]);
                prevKey = k;
            } else if (t == 3) {
                if (rf[i] != -1 || (prevBmp & ~k) != 0) return -1;
                long nb = k & ~prevBmp & 0x3fffffffffffffffL;
                b[o++] = (byte) (0xc0 | Long.bitCount(nb));
                while (nb != 0) {
                    int bit = Long.numberOfTrailingZeros(nb);
                    b[o++] = (byte) bit;
                    nb &= nb - 1;
                }
                prevBmp = k;
            } else {
                return -1;
            }
        }
        return o;
    }

    // decoding state: returned through fields to keep the loop allocation free
    long dId, dPrev;
    boolean dLeaf;
    int dN;

    int vo;

    long getV(byte[] b) {
        long x = 0;
        int sh = 0;
        while (true) {
            int c = b[vo++];
            x |= (long) (c & 0x7f) << sh;
            if (c >= 0) return x;
            sh += 7;
        }
    }

    long getRef(byte[] b, long tpos) {
        long v = getV(b);
        if (v == 0) return -1;
        if ((v & 1) == 1) return tpos - (v >>> 1);
        long x = (b[vo] & 0xffL) | (b[vo + 1] & 0xffL) << 8 | (b[vo + 2] & 0xffL) << 16
                | (b[vo + 3] & 0xffL) << 24;
        vo += 4;
        return tpos + x;
    }

    int dOff;

    /**
     * Decodes a body at o into kl and rf; returns the end offset. tpos is the record's start,
     * which a reader computes from the node's position and its stored offset.
     */
    int decode(byte[] b, int o, long tpos, long[] kl, long[] rf) {
        vo = o;
        int h = b[vo++] & 0xff;
        dLeaf = (h & 0x80) != 0;
        int n = h & 0x7f;
        dN = n;
        dOff = (int) getV(b);
        dId = tpos + unzz(getV(b));
        dPrev = getRef(b, tpos);
        long prevKey = 0, prevTime = -1, prevBmp = 0;
        for (int i = 0; i < n; i++) {
            int tag = b[vo++] & 0xff;
            int t = tag >>> 6;
            if (t == 0) {
                long v = getV(b);
                long tm = prevTime < 0 ? v : prevTime + unzz(v);
                kl[i] = tm;
                rf[i] = -1;
                prevTime = tm;
            } else if (t == 1) {
                int len = (tag >>> 3) & 7, s = tag & 7;
                long k = (1L << 62) | ((long) len << 3);
                for (int j = 0; j < s; j++) k |= prevKey & (0xffL << (54 - 8 * j));
                for (int j = s; j < len; j++) k |= (long) (b[vo++] & 0xff) << (54 - 8 * j);
                kl[i] = k;
                rf[i] = getRef(b, tpos);
                prevKey = k;
            } else {
                int c = tag & 0x3f;
                long bm = prevBmp;
                for (int j = 0; j < c; j++) bm |= 1L << b[vo++];
                bm |= 3L << 62;
                kl[i] = bm;
                rf[i] = -1;
                prevBmp = bm;
            }
        }
        return vo;
    }

    // ---- today's format 2, the body as StoredKeyNode writes and parses it ----

    static void putLong(byte[] b, int o, long x) {
        for (int j = 0; j < 8; j++) b[o + j] = (byte) (x >>> (8 * j));
    }

    static long getLong(byte[] b, int o) {
        return (b[o] & 0xffL) | (b[o + 1] & 0xffL) << 8 | (b[o + 2] & 0xffL) << 16
                | (b[o + 3] & 0xffL) << 24 | (b[o + 4] & 0xffL) << 32 | (b[o + 5] & 0xffL) << 40
                | (b[o + 6] & 0xffL) << 48 | (b[o + 7] & 0xffL) << 56;
    }

    static int encode2(long pos, long id, long prev, boolean leaf, long[] kl, long[] rf, int n,
            byte[] b, int o) {
        putLong(b, o + 8, prev);
        putLong(b, o + 16, (leaf ? 1 : 0) | (long) n << 8);
        putLong(b, o + 24, id);
        for (int i = 0; i < n; i++) putLong(b, o + 32 + 8 * i, kl[i]);
        for (int i = 0; i < n; i++) putLong(b, o + 32 + 8 * n + 8 * i, rf[i]);
        return o + 32 + 16 * n;
    }

    int decode2(byte[] b, int o, long[] kl, long[] rf) {
        dPrev = getLong(b, o + 8);
        dLeaf = b[o + 16] == 1;
        int n = (b[o + 17] & 0xff) | (b[o + 18] & 0xff) << 8;
        dN = n;
        dId = getLong(b, o + 24);
        for (int i = 0; i < n; i++) kl[i] = getLong(b, o + 32 + 8 * i);
        for (int i = 0; i < n; i++) {
            rf[i] = getLong(b, o + 32 + 8 * n + 8 * i);
            int t = (int) (kl[i] >>> 62);
            if (t == 2) throw new IllegalStateException();
        }
        return o + 32 + 16 * n;
    }

    // ---- the round trip and the benchmark ----

    public static void main(String[] args) throws Exception {
        DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(args[0])));
        int rounds = args.length > 1 ? Integer.parseInt(args[1]) : 20;
        ArrayList<long[]> kls = new ArrayList<long[]>(), rfs = new ArrayList<long[]>();
        ArrayList<long[]> meta = new ArrayList<long[]>();
        long bytes2 = 0;
        while (true) {
            long pos;
            try {
                pos = in.readLong();
            } catch (EOFException e) {
                break;
            }
            long tpos = in.readLong();
            int noff = in.readInt();
            int ns = in.readInt();
            byte[] b = new byte[ns];
            in.readFully(b);
            int n = (b[17] & 0xff) | (b[18] & 0xff) << 8;
            long[] kl = new long[n], rf = new long[n];
            for (int i = 0; i < n; i++) {
                kl[i] = getLong(b, 32 + 8 * i);
                rf[i] = getLong(b, 32 + 8 * n + 8 * i);
            }
            kls.add(kl);
            rfs.add(rf);
            meta.add(new long[] {pos, getLong(b, 24), getLong(b, 8), b[16], tpos, noff});
            bytes2 += ns;
        }
        int N = kls.size();
        // the round trip
        Codec c = new Codec();
        byte[] buf = new byte[1 << 16];
        long bytesC = 0;
        int fallback = 0;
        long[] k2 = new long[128], r2 = new long[128];
        for (int x = 0; x < N; x++) {
            long[] m = meta.get(x);
            long[] kl = kls.get(x), rf = rfs.get(x);
            int e = encode(m[4], (int) m[5], m[1], m[2], m[3] == 1, kl, rf, kl.length, buf, 8);
            if (e < 0 || e > 32 + 16 * kl.length) {
                fallback++;
                bytesC += 32 + 16 * kl.length;
                continue;
            }
            bytesC += e;
            int d = c.decode(buf, 8, m[4], k2, r2);
            if (d != e || c.dId != m[1] || c.dPrev != m[2] || c.dLeaf != (m[3] == 1) || c.dN != kl.length) {
                throw new AssertionError("header " + x);
            }
            for (int i = 0; i < kl.length; i++) {
                if (k2[i] != kl[i] || r2[i] != rf[i]) {
                    throw new AssertionError("node " + x + " klong " + i + ": " + Long.toHexString(kl[i])
                            + " " + Long.toHexString(k2[i]) + " ref " + rf[i] + " " + r2[i]);
                }
            }
        }
        System.out.printf("ROUNDTRIP nodes=%d ok, format2=%d bytes, C=%d bytes (%.3f), fallback=%d%n",
                N, bytes2, bytesC, (double) bytesC / bytes2, fallback);
        // the benchmark: write = encode + checksum; read = checksum + decode
        byte[][] enc2 = new byte[N][], encC = new byte[N][];
        for (int x = 0; x < N; x++) {
            long[] m = meta.get(x);
            long[] kl = kls.get(x), rf = rfs.get(x);
            byte[] a = new byte[32 + 16 * kl.length];
            encode2(m[0], m[1], m[2], m[3] == 1, kl, rf, kl.length, a, 0);
            enc2[x] = a;
            int e = encode(m[4], (int) m[5], m[1], m[2], m[3] == 1, kl, rf, kl.length, buf, 8);
            encC[x] = Arrays.copyOf(buf, e);
        }
        long sink = 0;
        for (int round = 0; round < rounds; round++) {
            long t0 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                long[] m = meta.get(x);
                long[] kl = kls.get(x);
                int e = encode2(m[0], m[1], m[2], m[3] == 1, kl, rfs.get(x), kl.length, buf, 0);
                sink += NodeChecksum.sumWithZeroReplace(buf, 0, e, 6);
            }
            long t1 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                long[] m = meta.get(x);
                long[] kl = kls.get(x);
                int e = encode(m[4], (int) m[5], m[1], m[2], m[3] == 1, kl, rfs.get(x), kl.length, buf, 8);
                sink += NodeChecksum.sumWithZeroReplace(buf, 0, e, 6);
            }
            long t2 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                byte[] a = enc2[x];
                sink += NodeChecksum.sumWithZeroReplace(a, 0, a.length, 6);
                sink += c.decode2(a, 0, k2, r2) + k2[0];
            }
            long t3 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                byte[] a = encC[x];
                sink += NodeChecksum.sumWithZeroReplace(a, 0, a.length, 6);
                sink += c.decode(a, 8, meta.get(x)[4], k2, r2) + k2[0];
            }
            long t4 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                byte[] a = enc2[x];
                sink += c.decode2(a, 0, k2, r2) + k2[0];
            }
            long t5 = System.nanoTime();
            for (int x = 0; x < N; x++) {
                sink += c.decode(encC[x], 8, meta.get(x)[4], k2, r2) + k2[0];
            }
            long t6 = System.nanoTime();
            if (round >= rounds / 2) {
                System.out.printf("BENCH round=%d ns/node: write2=%.1f writeC=%.1f read2=%.1f readC=%.1f"
                        + " (without the checksum: decode2=%.1f decodeC=%.1f)%n", round,
                        (t1 - t0) / (double) N, (t2 - t1) / (double) N, (t3 - t2) / (double) N,
                        (t4 - t3) / (double) N, (t5 - t4) / (double) N, (t6 - t5) / (double) N);
            }
        }
        // today's whole parse, for scale: StoredKeyNode.parse (checksum not included)
        long t0 = System.nanoTime();
        for (int x = 0; x < N; x++) {
            byte[] a = enc2[x];
            StoredKeyNode s = StoredKeyNode.parse(withHeader(a), 0, meta.get(x)[0]);
            sink += s.getNode().getSize();
        }
        long t1 = System.nanoTime();
        System.out.printf("PARSE StoredKeyNode.parse ns/node=%.1f (one pass, cold)%n", (t1 - t0) / (double) N);
        System.out.println("sink " + sink);
    }

    static byte[] withHeader(byte[] a) {
        int n = (a[17] & 0xff) | (a[18] & 0xff) << 8;
        a[0] = (byte) a.length; a[1] = (byte) (a.length >>> 8); a[2] = 0; a[3] = 0;
        a[4] = 20; a[5] = 2;
        return a;
    }
}
