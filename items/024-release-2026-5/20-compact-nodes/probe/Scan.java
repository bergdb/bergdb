package bergdb.core;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.util.*;
import java.util.zip.Deflater;

/**
 * The stream reader of bergdb 024-20, written 2026-11-11: where a stream's bytes go, and what
 * candidate encodings of the nodes would have written. It reads the files of a stream
 * directory (*.bergdb) directly, read only, with no BergDB class: the layout of 024-02,
 * sections 5 to 13. One core. Since 2026-11-12: record format 7 with the 12-byte node header of
 * 024-25 (node formats 3, 3, 5: the CRC32C sum in bytes 8 to 11; the fields after it moved).
 *
 * java -cp DIR bergdb.core.Scan dir=STREAMDIR [from=POS] [ops=N] [deflate=K] [label=TEXT]
 *   from     count only the records at or after this position (a phase's start)
 *   ops      the user operations of the window, for "a put" figures
 *   deflate  deflate every K-th record (1: all; 0: none), java.util.zip, levels 1 and 6
 */
public class Scan {
    static final long D = 200000, M = 128;

    // ---- the stream's files ----
    final ArrayList<FileChannel> chans = new ArrayList<FileChannel>();
    final ArrayList<Long> starts = new ArrayList<Long>();
    long firstPos, length;

    void open(File dir) throws IOException {
        File[] fs = dir.listFiles();
        ArrayList<File> l = new ArrayList<File>();
        for (File f : fs) if (f.getName().matches("[0-9]{14}\\.bergdb")) l.add(f);
        Collections.sort(l);
        if (l.isEmpty()) throw new IOException("no stream in " + dir);
        for (File f : l) {
            long s = Long.parseLong(f.getName().substring(0, 14)) * 100000L;
            chans.add(new RandomAccessFile(f, "r").getChannel());
            starts.add(s);
        }
        firstPos = starts.get(0);
        FileChannel last = chans.get(chans.size() - 1);
        length = starts.get(starts.size() - 1) + last.size();
    }

    void read(long pos, byte[] b, int off, int len) throws IOException {
        while (len > 0) {
            int i = Collections.binarySearch(starts, pos);
            if (i < 0) i = -i - 2;
            FileChannel c = chans.get(i);
            long fo = pos - starts.get(i);
            int n = (int) Math.min(len, c.size() - fo);
            if (n <= 0) throw new EOFException("pos " + pos);
            ByteBuffer bb = ByteBuffer.wrap(b, off, n);
            while (bb.hasRemaining()) {
                if (c.read(bb, fo + (n - bb.remaining())) < 0) throw new EOFException();
            }
            pos += n; off += n; len -= n;
        }
    }

    /** The position of record byte n of a record at p (024-02, section 5). */
    static long getSpos(long p, long n) {
        long pos = p;
        if (pos % D == 0) pos += M;
        while (true) {
            long next = (pos / D + 1) * D;
            long avail = next - pos;
            if (n < avail) return pos + n;
            n -= avail;
            pos = next + M;
        }
    }

    /** A record's bytes, without the meta blocks inside it. */
    byte[] readRecord(long tpos, int size) throws IOException {
        byte[] b = new byte[size];
        long pos = tpos;
        int off = 0;
        while (off < size) {
            if (pos % D == 0) pos += M;
            long next = (pos / D + 1) * D;
            int n = (int) Math.min(size - off, next - pos);
            read(pos, b, off, n);
            off += n;
            pos += n;
        }
        return b;
    }

    long firstRecord() throws IOException {
        if (firstPos == 0) return M;
        byte[] mb = new byte[(int) M];
        for (long k = (firstPos + D - 1) / D; k * D < length; k++) {
            read(k * D, mb, 0, (int) M);
            if (mb[127] != 10) continue;
            long lt = le64(mb, 16);
            if (lt >= firstPos) return lt;
        }
        throw new IOException("no record start found after the cut");
    }

    static int le32(byte[] b, int o) {
        return (b[o] & 0xff) | (b[o + 1] & 0xff) << 8 | (b[o + 2] & 0xff) << 16 | (b[o + 3] & 0xff) << 24;
    }

    static long le64(byte[] b, int o) {
        return (le32(b, o) & 0xffffffffL) | ((long) le32(b, o + 4)) << 32;
    }

    // ---- encodings ----

    static int v(long x) {          // unsigned LEB128 varint, x >= 0
        int n = 1;
        while ((x >>>= 7) != 0) n++;
        return n;
    }

    static long zz(long x) { return (x << 1) ^ (x >> 63); }

    static int z(long x) { return v(zz(x)); }

    /** A reference relative to the node's own position: 0 for -1, else 1 + zigzag(pos - ref). */
    static int ref(long pos, long r) {
        if (r == -1) return 1;
        long d = zz(pos - r);
        return v(d + 1);
    }

    static int refAbs(long r) { return v(r + 1); }

    /**
     * A reference relative to its record's start tpos (encoding C, section 4 of the item):
     * varint 0 for -1; 2d + 1 for a position d bytes before tpos; 2, then a u32 offset, for a
     * position at or after tpos (in the record itself: written before the target's position is
     * known, so of a fixed width). 1, 1 to 10, or 5 bytes.
     */
    /** As refT, absolute: varint 0 for -1; 2r + 1 for a position r before tpos; 2 and a u32. */
    static int refA(long tpos, long r) {
        if (r == -1) return 1;
        if (r < tpos) return v(2 * r + 1);
        return 5;
    }

    static int refT(long tpos, long r) {
        if (r == -1) return 1;
        if (r < tpos) return v(2 * (tpos - r) + 1);
        return 5;
    }

    // ---- the tallies ----

    final LinkedHashMap<String, long[]> cats = new LinkedHashMap<String, long[]>();

    void add(String name, long bytes) {
        long[] a = cats.get(name);
        if (a == null) { a = new long[2]; cats.put(name, a); }
        a[0] += bytes;
        a[1]++;
    }

    final LinkedHashMap<String, long[]> cands = new LinkedHashMap<String, long[]>();

    void cand(String name, long bytes) {
        long[] a = cands.get(name);
        if (a == null) { a = new long[1]; cands.put(name, a); }
        a[0] += bytes;
    }

    long records, failed, valueNodes, deleteNodes, keyNodes, leafNodes, innerNodes, topNodes,
            recordBytes, windowStart = -1, windowEnd, metaBlocks, gdPairs;
    long keyKlongsInLeaves, liveInLeaves;
    long[] recSizes = new long[1 << 16];
    int recN;
    long maxRec;
    long dSampled, dIn, dOut1, dOut6, dNodeIn, dNodeOut, dIdxIn, dIdxOut;
    byte[] idx = new byte[1 << 16];
    int idxN;
    int deflateEvery;
    final Deflater def1 = new Deflater(1, true), def6 = new Deflater(6, true);
    final Deflater defN = new Deflater(6, true);
    final byte[] dbuf = new byte[1 << 20];
    // knode size histogram of n
    long[] nHist = new long[70];

    int deflate(Deflater d, byte[] b, int off, int len) {
        d.reset();
        d.setInput(b, off, len);
        d.finish();
        int out = 0;
        byte[] buf = len + 64 > dbuf.length ? new byte[len + 64] : dbuf;
        while (!d.finished()) out += d.deflate(buf, 0, buf.length);
        return out;
    }

    void scan(long from) throws IOException {
        long tpos = firstRecord();
        byte[] h = new byte[4];
        long lastTpos = -1;
        while (tpos < length) {
            long p = tpos % D == 0 ? tpos + M : tpos;
            if (p + 4 > length) break;
            read(p, h, 0, 4);
            int size = le32(h, 0);
            if (size < 17 || getSpos(tpos, size - 1) >= length) break;
            long next = getSpos(tpos, size);
            if (tpos >= from) {
                if (windowStart < 0) windowStart = tpos;
                windowEnd = next;
                byte[] r = readRecord(tpos, size);
                if (r[size - 1] == 0) {
                    failed++;
                    add("failed record", size);
                } else {
                    record(tpos, r);
                }
            }
            lastTpos = tpos;
            tpos = next;
        }
        if (windowStart >= 0) {
            // meta blocks in [windowStart, windowEnd)
            metaBlocks = (windowEnd - 1) / D - (windowStart - 1) / D;
            add("meta blocks", metaBlocks * M);
        }
    }

    void record(long tpos, byte[] r) {
        records++;
        final int size = r.length;
        recordBytes += size;
        if (recN == recSizes.length) recSizes = Arrays.copyOf(recSizes, recN * 2);
        recSizes[recN++] = size;
        maxRec = Math.max(maxRec, size);
        long time = le64(r, 8), sp = le64(r, 16), top = le64(r, 24);
        add("record header", 32);
        // compact record header: size 4, format 1, time 8, startupPos and topPos relative
        long recC = 32;     // the header stays: its fields name positions in the record
        int off = 32;
        long[] ccur = new long[1];
        // compact sizes of the nodes, by encoding
        idxN = 0;
        while (true) {
            int ns = le32(r, off);
            if (ns == 0) break;
            int type = r[off + 4];
            long npos = getSpos(tpos, off);
            if (type == 20 || type == 10) {
                if (idx.length < idxN + ns) idx = Arrays.copyOf(idx, 2 * (idxN + ns));
                System.arraycopy(r, off, idx, idxN, ns);
                idxN += ns;
            }
            if (type == 20) keyNode(r, off, ns, npos, time, tpos);
            else if (type == 10) topNode(r, off, ns, npos, tpos);
            else if (type == 30 || type == 40) valueNode(r, off, ns, npos, type == 40, tpos);
            else throw new IllegalStateException("type " + type + " at " + npos);
            off += ns;
        }
        add("end marker and count", 8);
        int n = le32(r, off + 4);
        gdPairs += n;
        int gdOff = off + 8;
        long gdC = 0;
        for (int i = 0; i < n; i++) {
            long id = le64(r, gdOff + 16 * i), pos = le64(r, gdOff + 16 * i + 8);
            gdC += z(id - tpos) + z(pos - tpos);
        }
        add("got-dirty ids", 8L * n);
        add("got-dirty positions", 8L * n);
        int content = gdOff + 16 * n + 1;
        add("padding", size - content);
        add("last byte", 1);
        recC += 1 + v(n) + gdC + 1;     // end marker, count, pairs, last byte
        cand("R1 record frame compact", recC);
        cand("R0 record frame today", 32 + 8 + 16L * n + 1);
        cand("R0 padding today", size - content);
        if (deflateEvery > 0 && records % deflateEvery == 0) {
            dSampled++;
            dIn += size;
            dOut1 += deflate(def1, r, 0, size);
            dOut6 += deflate(def6, r, 0, size);
            if (idxN > 0) {
                dIdxIn += idxN;
                dIdxOut += deflate(def6, idx, 0, idxN);
            }
        }
    }

    void topNode(byte[] r, int off, int ns, long npos, long tpos) {
        topNodes++;
        // format 3 (024-25): h at 16, the ordinal at 18 to 23, id 24, root time 32, root 40,
        // then h pairs (position, time) from 48
        int hh = r[off + 16];
        add("top node", ns - 16L * hh);
        add("top node skip pointers", 16L * hh);
        long c = 12 + v(off) + 1 + v(le64(r, off + 16) >>> 16) + z(le64(r, off + 24) - tpos) + 8
                + refT(tpos, le64(r, off + 40));
        for (int i = 0; i < hh; i++) {
            c += refT(tpos, le64(r, off + 48 + 16 * i)) + 8;
        }
        cand("T1 top compact", c);
        cand("T0 top today", ns);
    }

    void valueNode(byte[] r, int off, int ns, long npos, boolean del, long tpos) {
        // format 5 (024-25): id at 12, offset 20, L 24, the value 28; a delete node's key at 24
        long id = le64(r, off + 12);
        int ro = le32(r, off + 20);
        int L = 0, ko;
        if (del) {
            deleteNodes++;
            ko = off + 24;
        } else {
            valueNodes++;
            L = le32(r, off + 24);
            ko = off + 28 + L;
        }
        int ksize = le32(r, ko);
        int k = ksize / 8;
        long lastSeg = le64(r, ko + 4 + 8 * (k - 1));
        int lastLen = (int) ((lastSeg >>> 3) & 7);
        int klen = 7 * (k - 1) + lastLen;
        String p = del ? "delete node " : "value node ";
        int hdr = del ? 28 : 32;
        add(p + "header", hdr);
        if (!del) add("value node value", L);
        add(p + "key bytes", klen);
        add(p + "key segment overhead", 8L * k - klen);
        int used = hdr + L + 8 * k;
        add(p + "padding", ns - used);
        // V1: the 12-byte node header, id relative to tpos, offset v, L v, key length v + bytes
        long c = 12 + z(id - tpos) + v(ro) + (del ? 0 : v(L) + L) + v(klen) + klen;
        cand(del ? "V1 delete compact" : "V1 value compact", c);
        cand(del ? "V0 delete today" : "V0 value today", ns);
        // V2: as V1 without the stored offset (the reader knows its record)
        cand(del ? "V2 delete compact no offset" : "V2 value compact no offset", c - v(ro));
    }

    DataOutputStream dump;
    int dumpLeft;
    /** Each key node's last version seen in the window: id -> {position, n}. */
    final HashMap<Long, long[]> lastVersion = new HashMap<Long, long[]>();
    long versionsSeen, versionsAfterOwnPrev;

    void keyNode(byte[] r, int off, int ns, long npos, long recTime, long tpos) {
        keyNodes++;
        if (dump != null && dumpLeft > 0) {
            dumpLeft--;
            try {
                dump.writeLong(npos);
                dump.writeLong(tpos);
                dump.writeInt(off);
                dump.writeInt(ns);
                dump.write(r, off, ns);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        // format 3 (024-25): leaf at 12, n at 13 and 14, prevPos 16, id 24, klongs from 32
        boolean leaf = r[off + 12] == 1;
        if (leaf) leafNodes++; else innerNodes++;
        String p = leaf ? "leaf " : "inner ";
        int n = (r[off + 13] & 0xff) | (r[off + 14] & 0xff) << 8;
        nHist[Math.min(n, 69)]++;
        long prev = le64(r, off + 16), id = le64(r, off + 24);
        long[] kl = new long[n], rf = new long[n];
        for (int i = 0; i < n; i++) {
            kl[i] = le64(r, off + 32 + 8 * i);
            rf[i] = le64(r, off + 32 + 8 * n + 8 * i);
        }
        // the last delete bitmap
        long bmp = 0;
        for (int i = 0; i < n; i++) if ((kl[i] >>> 62) == 3) bmp = kl[i];
        boolean[] dead = new boolean[n];
        int nt = 0, nb = 0, nl = 0, nd = 0;
        for (int i = 0; i < n; i++) {
            int t = (int) (kl[i] >>> 62);
            if (t == 0) { nt++; continue; }
            if (t == 3) { nb++; continue; }
            boolean d = i < 62 && ((bmp >>> i) & 1) != 0;
            if (!d) {
                long cv = kl[i];
                for (int j = i + 1; j < n && !d; j++) d = kl[j] == cv;
            }
            dead[i] = d;
            if (d) nd++; else nl++;
        }
        if (leaf) { keyKlongsInLeaves += nl + nd; liveInLeaves += nl; }
        add(p + "node header", 12);
        add(p + "prevPos", 8);
        add(p + "leaf, n, reserved", 4);
        add(p + "id", 8);
        add(p + "time klongs", 8L * nt);
        add(p + "time klong refs (-1)", 8L * nt);
        add(p + "bitmap klongs", 8L * nb);
        add(p + "bitmap refs (-1)", 8L * nb);
        add(p + "live key klongs", 8L * nl);
        add(p + "live key refs", 8L * nl);
        add(p + "dead key klongs", 8L * nd);
        add(p + "dead key refs", 8L * nd);

        long k0 = ns;
        // K1: no refs for time and bitmap klongs
        long k1 = 32 + 16L * (nl + nd) + 8L * (nt + nb);
        // the compact header: the 12-byte node header with leaf + n in its byte 6 (zero today),
        // the node's offset in its record v, id zigzag relative to tpos, prevPos refT
        long hdrRel = 12 + v(off) + z(id - tpos) + refT(tpos, prev);
        // K2: K1 with the compact header
        long k2 = hdrRel + 16L * (nl + nd) + 8L * (nt + nb);
        // K2f: K2 with the refs of key klongs as fixed 6-byte positions
        long k2f = hdrRel + 14L * (nl + nd) + 8L * (nt + nb);
        // K3: K2 with the refs of key klongs as refT
        long k3 = hdrRel;
        // K4 (= K3 + compact klongs), K4b (klongs as zigzag deltas), K5 (K4, dead dropped)
        long klongC = 0, klongD = 0, klongCLive = 0, refsRel = 0, refsRelLive = 0, refsAbs = 0;
        // the delta: the klongs after those of the node's previous version, when that version
        // is in the window, the node was not replaced (prevPos is that version) and n grew
        long[] lv = lastVersion.get(id);
        int nPrev = 0;
        if (lv != null && lv[0] == prev && lv[1] <= n) nPrev = (int) lv[1];
        if (lv == null) lastVersion.put(id, lv = new long[2]);
        lv[0] = npos;
        lv[1] = n;
        versionsSeen++;
        if (nPrev > 0) versionsAfterOwnPrev++;
        long deltaC = 0;
        long prevKey = -1, prevTime = -1, prevBmp = 0, prevKeyD = 0;
        long prevKeyLive = -1;
        long sharedBytes = 0;
        long cTime = 0, cBmp = 0, cLive = 0, cDead = 0;    // encoding C's bytes by kind of klong
        for (int i = 0; i < n; i++) {
            if (i == nPrev) deltaC -= klongC + refsRel;
            int t = (int) (kl[i] >>> 62);
            if (t == 0) {
                long tm = kl[i] & 0x00ffffffffffffffL;
                // the first time klong whole (a node read alone does not know its record's time)
                int c = 1 + (prevTime < 0 ? v(tm) : z(tm - prevTime));
                klongC += c;
                klongD += c;
                klongCLive += c;
                cTime += c;
                prevTime = tm;
                k3 += 8;
            } else if (t == 3) {
                long nb2 = kl[i] & ~prevBmp & 0x3fffffffffffffffL;
                int c = 1 + Long.bitCount(nb2);
                klongC += c;
                klongD += c;
                klongCLive += c;
                cBmp += c;
                prevBmp = kl[i];
                k3 += 8;
            } else {
                long cv = kl[i];
                int len = (int) ((cv >>> 3) & 7);
                int sh = prevKey < 0 ? 0 : shared(prevKey, cv, len);
                int c = 1 + len - sh;
                sharedBytes += sh;
                klongC += c;
                klongD += 1 + (prevKey < 0 ? v(cv & 0x3fffffffffffffffL) : z(cv - prevKey));
                prevKey = cv;
                int rr = refT(tpos, rf[i]);
                refsAbs += refA(tpos, rf[i]);
                refsRel += rr;
                if (dead[i]) cDead += c + rr; else cLive += c + rr;
                if (!dead[i]) {
                    int shl = prevKeyLive < 0 ? 0 : shared(prevKeyLive, cv, len);
                    klongCLive += 1 + len - shl;
                    prevKeyLive = cv;
                    refsRelLive += rr;
                }
                k3 += 8 + rr;
            }
        }
        long k4 = hdrRel + klongC + refsRel;
        deltaC += klongC + refsRel;
        if (nPrev == n) deltaC = 0;
        cand(p + "D0 delta in format 2: 32 + 16 a new klong", nPrev > 0 ? 32 + 16L * (n - nPrev) : ns);
        cand(p + "D1 delta in encoding C", nPrev > 0 ? hdrRel + deltaC : k4);
        cand(p + "count versions after their own previous", nPrev > 0 ? 1 : 0);
        cand(p + "count klongs repeated from the previous version", nPrev);
        // encoding C (K4) by part, for 024-19's model of a node's bytes
        cand(p + "C part header", hdrRel);
        cand(p + "C part klongs (tags and bytes)", klongC);
        cand(p + "C part refs", refsRel);
        cand(p + "C kind time klongs", cTime);
        cand(p + "C kind bitmaps", cBmp);
        cand(p + "C kind live key klongs with refs", cLive);
        cand(p + "C kind dead key klongs with refs", cDead);
        cand(p + "count nodes", 1);
        cand(p + "count time klongs", nt);
        cand(p + "count bitmap klongs", nb);
        cand(p + "count live key klongs", nl);
        cand(p + "count dead key klongs", nd);
        long k4b = hdrRel + klongD + refsRel;
        long k5 = hdrRel + klongCLive + refsRelLive;
        long k0live = 32 + 16L * (n - nd);
        cand(p + "K0 today", k0);
        cand(p + "K0d today without dead klongs", k0live);
        cand(p + "K1 no refs of time and bitmap klongs", k1);
        cand(p + "K2 K1 + compact header", k2);
        cand(p + "K2f K2 + 6-byte refs", k2f);
        cand(p + "K3 K2 + refs relative to the record", k3);
        cand(p + "K3a K2 + refs absolute varint", k3 - refsRel + refsAbs);
        cand(p + "K4 K3 + compact klongs, shared prefix", k4);
        cand(p + "K4b K3 + klongs as zigzag deltas", k4b);
        cand(p + "K5 K4 without dead klongs", k5);
        cand(p + "key bytes shared with the previous klong", sharedBytes);
        if (deflateEvery > 0 && keyNodes % deflateEvery == 0) {
            dNodeIn += ns;
            dNodeOut += deflate(defN, r, off, ns);
        }
    }

    /** Leading data bytes of b that equal a's (both key klongs), at most len. */
    static int shared(long a, long b, int len) {
        int s = 0;
        for (int j = 0; j < len; j++) {
            long ba = (a >>> (54 - 8 * j)) & 0xff, bb = (b >>> (54 - 8 * j)) & 0xff;
            int la = (int) ((a >>> 3) & 7);
            if (j >= la || ba != bb) break;
            s++;
        }
        return s;
    }

    void report(PrintStream out, String label, long ops) {
        long total = windowEnd - windowStart;
        double o = Math.max(1, ops);
        out.printf("SCAN %s window=%d..%d bytes=%d records=%d failed=%d ops=%d value=%d delete=%d"
                + " keynodes=%d (leaf %d, inner %d) top=%d gdpairs=%d meta=%d%n", label, windowStart,
                windowEnd, total, records, failed, ops, valueNodes, deleteNodes, keyNodes, leafNodes,
                innerNodes, topNodes, gdPairs, metaBlocks);
        long[] rs = Arrays.copyOf(recSizes, recN);
        Arrays.sort(rs);
        if (recN > 0) {
            out.printf("RECSIZE %s mean=%.0f p50=%d p90=%d p99=%d max=%d%n", label,
                    (double) recordBytes / recN, rs[recN / 2], rs[(int) (recN * 0.9)],
                    rs[(int) (recN * 0.99)], rs[recN - 1]);
        }
        long sum = 0;
        for (Map.Entry<String, long[]> e : cats.entrySet()) sum += e.getValue()[0];
        out.printf("CHECK %s categories=%d window=%d diff=%d%n", label, sum, total, total - sum);
        for (Map.Entry<String, long[]> e : cats.entrySet()) {
            long b = e.getValue()[0];
            out.printf("CAT %s | %-40s %14d %6.2f%% %9.1f/op%n", label, e.getKey(), b,
                    100.0 * b / Math.max(1, total), b / o);
        }
        for (Map.Entry<String, long[]> e : cands.entrySet()) {
            long b = e.getValue()[0];
            out.printf("CAND %s | %-48s %14d %9.1f/op%n", label, e.getKey(), b, b / o);
        }
        out.printf("KLONGS %s leaf key klongs/leaf=%.2f live/leaf=%.2f%n", label,
                (double) keyKlongsInLeaves / Math.max(1, leafNodes),
                (double) liveInLeaves / Math.max(1, leafNodes));
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < nHist.length; i++) if (nHist[i] > 0) sb.append(i).append(':').append(nHist[i]).append(' ');
        out.printf("NHIST %s %s%n", label, sb);
        if (dSampled > 0) {
            out.printf("DEFLATE %s records=%d in=%d level1=%d (%.3f) level6=%d (%.3f)%n", label,
                    dSampled, dIn, dOut1, (double) dOut1 / dIn, dOut6, (double) dOut6 / dIn);
        }
        if (dIdxIn > 0) {
            out.printf("DEFLATE-INDEX %s in=%d level6=%d (%.3f)%n", label, dIdxIn, dIdxOut,
                    (double) dIdxOut / dIdxIn);
        }
        if (dNodeIn > 0) {
            out.printf("DEFLATE-NODE %s in=%d level6=%d (%.3f)%n", label, dNodeIn, dNodeOut,
                    (double) dNodeOut / dNodeIn);
        }
        out.flush();
    }

    public static void run(File dir, long from, long ops, int deflate, String label, PrintStream out)
            throws IOException {
        run(dir, from, ops, deflate, label, out, null, 0);
    }

    /** As run() above; dumps the first dumpN key nodes of the window to dumpFile (pos, size, bytes). */
    public static void run(File dir, long from, long ops, int deflate, String label, PrintStream out,
            String dumpFile, int dumpN) throws IOException {
        Scan s = new Scan();
        if (dumpFile != null) {
            s.dump = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(dumpFile)));
            s.dumpLeft = dumpN;
        }
        s.deflateEvery = deflate;
        s.open(dir);
        long t0 = System.nanoTime();
        s.scan(from);
        s.report(out, label, ops);
        out.printf("SCANTIME %s %.1f s%n", label, (System.nanoTime() - t0) / 1e9);
        for (FileChannel c : s.chans) c.close();
        if (s.dump != null) s.dump.close();
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> p = new HashMap<String, String>();
        for (String a : args) {
            int i = a.indexOf('=');
            p.put(a.substring(0, i), a.substring(i + 1));
        }
        run(new File(p.get("dir")), Long.parseLong(p.getOrDefault("from", "0")),
                Long.parseLong(p.getOrDefault("ops", "0")),
                Integer.parseInt(p.getOrDefault("deflate", "1")), p.getOrDefault("label", "x"),
                System.out);
    }
}
