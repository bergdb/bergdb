package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.RandomAccessFile;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;

/**
 * StreamScan, Java's scanner of a BergDB stream (bergdb 012-02; 012-01, section 6.4,
 * check 2). It reads a database directory (FileStream's *.bergdb files) or a flat file
 * that holds a stream from position 0, and prints one line per item of the stream: every
 * byte of it is shown by some field, from the raw bytes, as the format document 012-02
 * describes them. C's scanner (012-06) prints the same text, so that two scans can be
 * compared with diff. It only reads; it writes nothing and takes no lock.
 *
 * <p>Besides its own decoding, it runs Java's parsers on each committed record
 * (StoredTrans.parse, which checks the node checksums and the formats) and Java's record
 * walk (NodeStream.TransIterator, from the stream's first position), and prints an error
 * line where they refuse a record or disagree with the raw fields.</p>
 *
 * <pre>
 * Usage: java -ea -cp CLASSES bergdb.core.StreamScan PATH
 *   PATH  a directory with *.bergdb files, or a flat file (the stream from position 0)
 *
 * TEXT FORMAT, version 1
 * One item per line: a word, then fields "name=value" separated by one space. Lines of
 * the parts of an item (klongs, skip pointers, got-dirty pairs) are indented by two
 * spaces and follow their item. Numbers are decimal; a "pointer" (a stream position
 * stored in the stream: refs, root, skip pointers, prevPos, startupPos, topPos, a
 * got-dirty position, lastTrans) is printed as decimal/0xhex, except -1 (Spos.NULL),
 * printed as -1. Klongs are printed raw as 0x and 16 hex digits, then decoded. Hex is
 * lower case. pos is a stream position (meta blocks counted), off an offset in the
 * record's bytes (meta blocks not counted). Items come in the order of their first byte;
 * a meta block inside a record comes after the item that it falls in or after.
 *
 * streamscan 1
 * file name=NAME first=P size=S        a .bergdb file of a directory, in name order
 * other name=NAME size=S               any other file of the directory
 * stream first=P length=L              the stream's first readable position and length
 * meta pos=P magic=HEX8 version=V time=T lastTrans=PTR id=HEX32 startupDistance=D
 *      maxNodeSize=N reserved=zero|HEX last=B
 *                                      a complete meta block (128 bytes); version is the
 *                                      int at bytes 4 to 7; reserved, bytes 46 to 126
 * meta pos=P partial=N bytes=HEX       the first N bytes of a meta block cut by the end
 * gap from=P to=Q                      bytes not scanned: in a cut stream, from the first
 *                                      position to the record that a meta block names
 * record pos=P size=S format=F b5=HEX6 time=T startupPos=PTR topPos=PTR last=10
 *      lastPos=P next=P                a committed record and its 32-byte header; b5 is
 *                                      bytes 5 to 7; lastPos the position of its last byte
 * record pos=P size=S last=B sha256=H next=P
 *                                      a record that is not committed (last byte not 10):
 *                                      nothing in it is parsed
 * torn pos=P size=S have=N             a record cut by the end of the stream (N of its S
 *                                      bytes present); size=? if fewer than 4 bytes
 * top pos=P off=O size=S type=10 format=2 sum=HEX4 sumOk=B h=H b9=N ordinal=N id=I
 *      rootTime=T root=PTR
 *   skip i=I pos=PTR time=T            skip pointer I (I from 0 to h-1)
 * key pos=P off=O size=S type=20 format=2 sum=HEX4 sumOk=B prevPos=PTR leaf=B n=N
 *      reserved=zero|HEX id=I          reserved: bytes 19 to 23
 *   klong i=I raw=0xHEX16 time=T ref=PTR              type 0
 *   klong i=I raw=0xHEX16 key len=L bytes=HEX ref=PTR type 1 (bytes= empty if L is 0)
 *   klong i=I raw=0xHEX16 type2 ref=PTR               type 2 (not used)
 *   klong i=I raw=0xHEX16 del ref=PTR                 type 3, a delete bitmap
 * value pos=P off=O size=S type=30 format=4 sum=HEX4 sumOk=B id=I offset=O length=L
 *      sha256=H keySize=K segs=HEX16,... key=HEX ikey=TEXT pad=N padZero=B
 * delete pos=P off=O size=S type=40 format=4 sum=HEX4 sumOk=B id=I offset=O
 *      keySize=K segs=HEX16,... key=HEX ikey=TEXT pad=N padZero=B
 *                                      offset: the stored offset in the record's bytes;
 *                                      key: the bkey's bytes; ikey=TEXT only when every
 *                                      ikey byte is printable ASCII 0x21 to 0x7e, but '='
 * nodes-end pos=P off=O                the 4 zero bytes after the nodes
 * gotdirty pos=P off=O count=N
 *   dirty i=I id=ID pos=PTR
 * padding pos=P off=O count=N zero=B   the zeros that align the record to 8
 * last pos=P byte=B                    the record's last byte
 * end length=L                         the end of the scan
 * error ...                            a check failed; the text after "error" is the
 *                                      implementation's own, the line's place is not
 * </pre>
 *
 * Bergdb 012-02 documents every field. Format changes are logged in 012-02's progress.
 */
public class StreamScan {
    static final int MBS = RecoverableStream.META_BLOCK_SIZE;
    static final int MBD = RecoverableStream.META_BLOCK_DISTANCE;

    private final View view;
    private final PrintStream out;
    private long nextMeta;          // The position of the next meta block to print.
    private int errors = 0;

    StreamScan(View view, PrintStream out) {
        this.view = view;
        this.out = out;
        this.nextMeta = (view.getFirstPos() + MBD - 1) / MBD * MBD;
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            System.err.println("Usage: java -ea -cp CLASSES bergdb.core.StreamScan PATH");
            System.exit(2);
        }
        PrintStream out = new PrintStream(new java.io.BufferedOutputStream(System.out, 1 << 16),
                false, "UTF-8");
        out.println("streamscan 1");
        View view = View.open(new File(args[0]), out);
        StreamScan scan = new StreamScan(view, out);
        scan.run();
        view.close();
        out.flush();
        System.exit(scan.errors == 0 ? 0 : 1);
    }

    // ======== The walk ========

    void run() throws IOException {
        final long first = view.getFirstPos();
        final long length = view.getLength();
        out.println("stream first=" + first + " length=" + length);

        long pos = startOfWalk();
        if (pos > first && pos != Spos.NULL) {
            long from = first % MBD < MBS ? first - first % MBD + MBS : first;
            if (pos > from) {
                flushMetas(from);
                out.println("gap from=" + from + " to=" + pos);
            }
        }

        List<Long> committed = new ArrayList<Long>();
        boolean torn = length - first < MBS;     // Not even a meta block.
        while (pos != Spos.NULL && pos < length) {
            long next = record(pos, committed);
            if (next < 0) {
                torn = true;
                break;
            }
            pos = next;
        }
        flushMetas(Long.MAX_VALUE);
        checkJavaWalk(committed, torn);
        out.println("end length=" + length);
    }

    /**
     * Where the walk starts: as Java's (RecoverableStream.getPosOfTransCompletedBefore of
     * the first position), the record that the first valid meta block at or after the
     * first position names, if at or after that position; the first record of the stream
     * if it names none.
     */
    private long startOfWalk() throws IOException {
        final long first = view.getFirstPos();
        final long length = view.getLength();
        for (long m = nextMeta; m + MBS <= length; m += MBD) {
            byte[] b = read(m, MBS);
            if (b[MBS - 1] != RecoverableStream.LAST_BYTE) {
                continue;
            }
            long last = le64(b, 16);
            if (last == Spos.NULL) {
                if (length <= MBS) {
                    return Spos.NULL;
                }
                last = MBS;     // The first record; in a cut stream, only if not cut away.
            }
            if (last >= first) {
                return last;
            }
        }
        if (length - first < MBS) {
            return Spos.NULL;       // Not even a meta block: an incomplete creation.
        }
        if (first == 0 && length > MBS) {
            error("no valid meta block; the walk starts at " + MBS);
            return MBS;
        }
        error("no valid meta block names a record at or after the first position " + first);
        return Spos.NULL;
    }

    /** Prints the meta blocks that start before 'pos'. */
    private void flushMetas(long pos) throws IOException {
        final long length = view.getLength();
        while (nextMeta < pos && nextMeta < length) {
            meta(nextMeta);
            nextMeta += MBD;
        }
    }

    private void meta(long p) throws IOException {
        final long length = view.getLength();
        if (p + MBS > length) {
            int n = (int) (length - p);
            out.println("meta pos=" + p + " partial=" + n + " bytes=" + hex(read(p, n)));
            return;
        }
        byte[] b = read(p, MBS);
        StringBuilder s = new StringBuilder("meta pos=" + p);
        s.append(" magic=").append(hex(b, 0, 4));
        s.append(" version=").append(le32(b, 4));
        s.append(" time=").append(le64(b, 8));
        s.append(" lastTrans=").append(ptr(le64(b, 16)));
        s.append(" id=").append(hex(b, 24, 16));
        s.append(" startupDistance=").append(le32(b, 40));
        s.append(" maxNodeSize=").append(le16u(b, 44));
        s.append(" reserved=").append(zeroOrHex(b, 46, 81));
        s.append(" last=").append(b[127] & 0xff);
        out.println(s);
        if (b[127] == RecoverableStream.LAST_BYTE
                && !Arrays.equals(Arrays.copyOf(b, 4), MetaBlock.MAGIC)) {
            error("meta block at " + p + " is valid but its magic bytes are not berg");
        }
    }

    /**
     * Prints the record at 'pos' and returns the position after it, or -1 if the walk
     * cannot go on.
     */
    private long record(long pos, List<Long> committed) throws IOException {
        final long length = view.getLength();
        long have = transBytesBetween(pos, length);
        if (have < 4) {
            flushMetas(pos + 1);
            out.println("torn pos=" + pos + " size=? have=" + have);
            return -1;
        }
        int size = le32(read(pos, 4, true), 0);
        if (size < RecoverableStream.MIN_TRANS_SIZE) {
            flushMetas(pos + 1);
            error("record at " + pos + " has size " + size + ", below "
                    + RecoverableStream.MIN_TRANS_SIZE);
            return -1;
        }
        if (have < size) {
            flushMetas(pos + 1);
            out.println("torn pos=" + pos + " size=" + size + " have=" + have);
            return -1;
        }
        byte[] r = read(pos, size, true);
        long next = RecoverableStream.getSpos(pos, size);
        long lastPos = RecoverableStream.getSpos(pos, size - 1);
        int last = r[size - 1] & 0xff;
        flushMetas(pos + 1);
        if (last != RecoverableStream.LAST_BYTE) {
            out.println("record pos=" + pos + " size=" + size + " last=" + last + " sha256="
                    + sha256(r, 0, size) + " next=" + next);
            if (last != 0) {
                error("record at " + pos + " has last byte " + last + ", neither 10 nor 0");
            }
            return next;
        }
        committed.add(pos);
        if (size < 32 + 4 + 4 + 1) {
            error("committed record at " + pos + " of size " + size + " is too short");
            return next;
        }
        StringBuilder s = new StringBuilder("record pos=" + pos);
        s.append(" size=").append(size);
        s.append(" format=").append(r[4] & 0xff);
        s.append(" b5=").append(hex(r, 5, 3));
        s.append(" time=").append(le64(r, 8));
        s.append(" startupPos=").append(ptr(le64(r, 16)));
        s.append(" topPos=").append(ptr(le64(r, 24)));
        s.append(" last=").append(last);
        s.append(" lastPos=").append(lastPos);
        s.append(" next=").append(next);
        out.println(s);

        RecordParse parsed = new RecordParse(pos);
        int off = 32;
        while (true) {
            if (off + 4 > size - 1) {
                error("record at " + pos + ": no end of nodes before offset " + off);
                return next;
            }
            int nodeSize = le32(r, off);
            if (nodeSize == 0) {
                break;
            }
            if (nodeSize < 8 || off + (long) nodeSize > size - 1) {
                error("record at " + pos + ": bad node size " + nodeSize + " at offset " + off);
                return next;
            }
            if (!node(pos, r, off, nodeSize, parsed)) {
                return next;
            }
            off += nodeSize;
        }
        long p = RecoverableStream.getSpos(pos, off);
        flushMetas(p + 1);
        out.println("nodes-end pos=" + p + " off=" + off);
        off += 4;

        if (off + 4 > size - 1) {
            error("record at " + pos + ": no got-dirty count");
            return next;
        }
        int count = le32(r, off);
        p = RecoverableStream.getSpos(pos, off);
        flushMetas(p + 1);
        out.println("gotdirty pos=" + p + " off=" + off + " count=" + count);
        off += 4;
        if (count < 0 || off + 16L * count > size - 1) {
            error("record at " + pos + ": bad got-dirty count " + count);
            return next;
        }
        long[] dirty = new long[2 * count];
        for (int i = 0; i < count; i++) {
            dirty[2 * i] = le64(r, off);
            dirty[2 * i + 1] = le64(r, off + 8);
            out.println("  dirty i=" + i + " id=" + dirty[2 * i] + " pos=" + ptr(dirty[2 * i + 1]));
            off += 16;
        }

        int pad = size - 1 - off;
        p = RecoverableStream.getSpos(pos, off);
        flushMetas(p + 1);
        out.println("padding pos=" + p + " off=" + off + " count=" + pad + " zero="
                + isZero(r, off, pad));
        if (pad >= 8) {
            error("record at " + pos + ": " + pad + " bytes after the got-dirty list");
        }
        flushMetas(lastPos + 1);
        out.println("last pos=" + lastPos + " byte=" + last);

        parsed.gotDirty = dirty;
        parsed.time = le64(r, 8);
        parsed.startupPos = le64(r, 16);
        parsed.topPos = le64(r, 24);
        checkJavaParse(pos, r, parsed, lastPos);
        return next;
    }

    /** Prints a node; returns false if the record cannot be parsed further. */
    private boolean node(long tpos, byte[] r, int off, int size, RecordParse parsed)
            throws IOException {
        long pos = RecoverableStream.getSpos(tpos, off);
        flushMetas(pos + 1);
        int type = r[off + 4] & 0xff;
        int format = r[off + 5] & 0xff;
        int sum = le16u(r, off + 6);
        int computed = NodeChecksum.sumWithZeroReplace(r, off, size, off + 6);
        String head = " pos=" + pos + " off=" + off + " size=" + size + " type=" + type
                + " format=" + format + " sum=" + String.format("%04x", sum)
                + " sumOk=" + (sum == computed);
        RawNode raw = new RawNode();
        raw.pos = pos;
        raw.type = type;
        switch (type) {
        case Node.TYPE_TOP_NODE: {
            if (size < 40) {
                error("top node at " + pos + " of size " + size);
                return false;
            }
            int h = r[off + 8];
            long ordinal = le64(r, off + 8) >>> 16;
            raw.id = le64(r, off + 16);
            raw.time = le64(r, off + 24);
            raw.ordinal = ordinal;
            long root = le64(r, off + 32);
            out.println("top" + head + " h=" + h + " b9=" + (r[off + 9] & 0xff) + " ordinal="
                    + ordinal + " id=" + raw.id + " rootTime=" + raw.time + " root=" + ptr(root));
            if (h < 0 || 40 + 16 * h != size) {
                error("top node at " + pos + ": h " + h + " does not fit size " + size);
                return false;
            }
            raw.refs = new long[1 + h];
            raw.times = new long[h];
            raw.refs[0] = root;
            for (int i = 0; i < h; i++) {
                long p = le64(r, off + 40 + 16 * i);
                long t = le64(r, off + 48 + 16 * i);
                raw.refs[1 + i] = p;
                raw.times[i] = t;
                out.println("  skip i=" + i + " pos=" + ptr(p) + " time=" + t);
            }
            break;
        }
        case Node.TYPE_KEY_NODE: {
            if (size < 32) {
                error("key node at " + pos + " of size " + size);
                return false;
            }
            long prev = le64(r, off + 8);
            int leaf = r[off + 16] & 0xff;
            int n = le16(r, off + 17);
            raw.id = le64(r, off + 24);
            raw.prevPos = prev;
            raw.leaf = leaf;
            out.println("key" + head + " prevPos=" + ptr(prev) + " leaf=" + leaf + " n=" + n
                    + " reserved=" + zeroOrHex(r, off + 19, 5) + " id=" + raw.id);
            if (n < 0 || 32 + 16 * n != size) {
                error("key node at " + pos + ": n " + n + " does not fit size " + size);
                return false;
            }
            raw.klongs = new long[n];
            raw.refs = new long[n];
            for (int i = 0; i < n; i++) {
                long k = le64(r, off + 32 + 8 * i);
                long ref = le64(r, off + 32 + 8 * n + 8 * i);
                raw.klongs[i] = k;
                raw.refs[i] = ref;
                out.println("  klong i=" + i + " raw=0x" + hex16(k) + " " + klong(k)
                        + " ref=" + ptr(ref));
            }
            break;
        }
        case Node.TYPE_VALUE:
        case Node.TYPE_DELETE: {
            boolean isValue = type == Node.TYPE_VALUE;
            int o = off + 8;
            raw.id = le64(r, o);
            o += 8;
            int stored = le32(r, o);
            raw.offset = stored;
            o += 4;
            StringBuilder s = new StringBuilder(isValue ? "value" : "delete");
            s.append(head).append(" id=").append(raw.id).append(" offset=").append(stored);
            if (isValue) {
                int len = le32(r, o);
                o += 4;
                if (len < 0 || o + (long) len + 4 > off + size) {
                    out.println(s);
                    error("value node at " + pos + ": bad value length " + len);
                    return false;
                }
                raw.value = Arrays.copyOfRange(r, o, o + len);
                s.append(" length=").append(len).append(" sha256=").append(sha256(r, o, len));
                o += len;
            }
            int keySize = le32(r, o);
            o += 4;
            s.append(" keySize=").append(keySize);
            if (keySize <= 0 || keySize % 8 != 0 || o + (long) keySize > off + size) {
                out.println(s);
                error("value node at " + pos + ": bad key size " + keySize);
                return false;
            }
            long[] segs = new long[keySize / 8];
            StringBuilder segText = new StringBuilder();
            for (int i = 0; i < segs.length; i++) {
                segs[i] = le64(r, o + 8 * i);
                segText.append(i == 0 ? "" : ",").append(hex16(segs[i]));
            }
            o += keySize;
            raw.key = segs;
            byte[] bkey = bkeyOf(segs);
            s.append(" segs=").append(segText).append(" key=").append(hex(bkey));
            String ikey = ikeyText(bkey);
            if (ikey != null) {
                s.append(" ikey=").append(ikey);
            }
            int pad = off + size - o;
            s.append(" pad=").append(pad).append(" padZero=").append(isZero(r, o, pad));
            out.println(s);
            if (pad < 0 || pad >= 4) {
                error("value node at " + pos + ": " + pad + " bytes of padding");
            }
            break;
        }
        default:
            out.println("node" + head);
            error("unknown node type " + type + " at " + pos);
            return false;
        }
        parsed.nodes.add(raw);
        return true;
    }

    // ======== Java's own parsers, as a check of the raw fields ========

    /** The fields of a node as the scan decoded them. */
    static class RawNode {
        long pos;
        int type;
        long id;
        long time;          // a top node's root time
        long ordinal;
        long prevPos;
        int leaf;
        long offset;        // a value node's stored offset
        long[] klongs;
        long[] refs;        // a top node's root and skip pointers; a key node's refs
        long[] times;
        byte[] value;
        long[] key;
    }

    static class RecordParse {
        final long pos;
        final List<RawNode> nodes = new ArrayList<RawNode>();
        long[] gotDirty;
        long time;
        long startupPos;
        long topPos;
        RecordParse(long pos) { this.pos = pos; }
    }

    private void checkJavaParse(long tpos, byte[] r, RecordParse raw, long lastPos) {
        StoredTrans t;
        try {
            t = StoredTrans.parse(tpos, r);
        } catch (RuntimeException | AssertionError e) {
            error("Java's parser refuses the record at " + tpos + ": " + e);
            return;
        }
        String where = "record at " + tpos + ": Java's parser and the scan disagree on ";
        if (t.tt != raw.time) error(where + "the time");
        if (t.startupPos != raw.startupPos) error(where + "startupPos");
        if (t.topPos != raw.topPos) error(where + "topPos");
        if (t.lastPos != lastPos) error(where + "lastPos, " + t.lastPos + " and " + lastPos);
        if (!Arrays.equals(t.gotDirtyIdsAndSpos, raw.gotDirty)) error(where + "got-dirty list");
        if (t.nodes.length != raw.nodes.size()) {
            error(where + "the node count, " + t.nodes.length + " and " + raw.nodes.size());
            return;
        }
        for (int i = 0; i < t.nodes.length; i++) {
            StoredNode sn = t.nodes[i];
            Node n = sn.getNode();
            RawNode x = raw.nodes.get(i);
            String w = where + "node " + i + " at " + x.pos + ", ";
            if (n.getSpos() != x.pos) error(w + "spos " + n.getSpos());
            if ((n.getType() & 0xff) != x.type) error(w + "type " + n.getType());
            if (n.getId() != x.id) error(w + "id " + n.getId());
            if (n instanceof TopNode) {
                TopNode top = (TopNode) n;
                if (top.topNodeId != x.ordinal) error(w + "ordinal");
                if (top.rootTime != x.time) error(w + "root time");
                if (top.getPointerPos(0) != x.refs[0]) error(w + "root pointer");
                for (int j = 0; j < top.pointersLength; j++) {
                    if (top.pointersPos[j] != x.refs[1 + j]) error(w + "skip pointer " + j);
                    long time = x.refs[1 + j] == Spos.NULL ? -1 : x.times[j];
                    if (top.pointersTime[j] != time) error(w + "skip time " + j);
                    if (x.refs[1 + j] == Spos.NULL && x.times[j] != -1) {
                        error(w + "an unset skip pointer with time " + x.times[j]);
                    }
                }
            } else if (n instanceof KeyNode) {
                KeyNode k = (KeyNode) n;
                if (sn.getPrevPos() != x.prevPos) error(w + "prevPos");
                if (k.isSegmentLeaf() != (x.leaf == 1)) error(w + "leaf");
                if (k.size != x.klongs.length) error(w + "size");
                for (int j = 0; j < k.size && j < x.klongs.length; j++) {
                    if (k.klongs[j] != x.klongs[j]) error(w + "klong " + j);
                    if (k.getPointerPos(j) != x.refs[j]) error(w + "ref " + j);
                }
            } else if (n instanceof ValueNode) {
                ValueNode v = (ValueNode) n;
                StoredValueNode sv = (StoredValueNode) sn;
                if (!Arrays.equals(v.value, x.value)) error(w + "value");
                if (!Arrays.equals(sv.getKey(), x.key)) error(w + "key");
                if (v.getTpos() != tpos) error(w + "tpos from the offset, " + v.getTpos());
                if (RecoverableStream.getSpos(tpos, x.offset) != x.pos) {
                    error(w + "the stored offset " + x.offset);
                }
            }
        }
    }

    /**
     * Java's walk over the committed records, from the first position, as startup's. On a
     * stream that ends in a torn record, which Java recovers before it reads, the walk
     * may fail at that record, after the same committed records.
     */
    private void checkJavaWalk(List<Long> committed, boolean torn) {
        List<Long> java = new ArrayList<Long>();
        try {
            RecoverableStream rs = new RecoverableStream(view, new MetaBlock());
            Object lock = new Object();
            NodeStream ns = new NodeStream(rs, lock);
            synchronized (lock) {
                NodeStream.TransIterator it = ns.createTransIterator(view.getFirstPos());
                while (it.next()) {
                    java.add(it.tpos);
                }
            }
        } catch (RuntimeException | AssertionError e) {
            if (!(torn && java.equals(committed))) {
                error("Java's record walk fails: " + e);
            }
            return;
        }
        if (!java.equals(committed)) {
            error("Java's record walk finds " + java.size() + " committed records, the scan "
                    + committed.size() + (java.isEmpty() || committed.isEmpty() ? ""
                    : ", first " + java.get(0) + " and " + committed.get(0)));
        }
    }

    // ======== Reading ========

    /** The number of record bytes (meta blocks not counted) from 'pos' to 'end'. */
    static long transBytesBetween(long pos, long end) {
        return transPos(end) - transPos(pos);
    }

    private static long transPos(long spos) {
        long blocks = spos / MBD;
        long offset = spos % MBD;
        return blocks * (MBD - MBS) + (offset > MBS ? offset - MBS : 0);
    }

    /** Raw bytes, meta blocks included. */
    private byte[] read(long pos, int n) throws IOException {
        byte[] b = new byte[n];
        view.read(pos, b, 0, n);
        return b;
    }

    /** Record bytes from 'pos', meta blocks skipped (RecoverableStream.read). */
    private byte[] read(long pos, int n, boolean recordBytes) {
        byte[] b = new byte[n];
        new RecoverableStream(view, new MetaBlock()).read(pos, b, 0, n);
        return b;
    }

    /**
     * The stream as an AppendOnlyStream that only reads: the .bergdb files of a directory
     * at their positions (the name's index times 100,000), or a flat file from 0.
     */
    static class View implements AppendOnlyStream {
        final List<Long> starts = new ArrayList<Long>();
        final List<RandomAccessFile> files = new ArrayList<RandomAccessFile>();
        long first;
        long length;

        static View open(File path, PrintStream out) throws IOException {
            View v = new View();
            if (path.isDirectory()) {
                File[] all = path.listFiles();
                Arrays.sort(all, (a, b) -> a.getName().compareTo(b.getName()));
                long expected = -1;
                for (File f : all) {
                    String name = f.getName();
                    if (!name.endsWith(".bergdb")) {
                        out.println("other name=" + name + " size=" + f.length());
                        continue;
                    }
                    String digits = name.substring(0, name.length() - ".bergdb".length());
                    long start = digits.matches("[0-9]{14}") ? Long.parseLong(digits) * 100000 : -1;
                    out.println("file name=" + name + " first=" + start + " size=" + f.length());
                    if (start < 0) {
                        throw new IOException("bad file name " + name);
                    }
                    if (expected >= 0 && start != expected) {
                        throw new IOException("file " + name + " starts at " + start
                                + ", the files before it end at " + expected);
                    }
                    if (expected < 0) {
                        v.first = start;
                    }
                    v.starts.add(start);
                    v.files.add(new RandomAccessFile(f, "r"));
                    expected = start + f.length();
                }
                v.length = expected < 0 ? 0 : expected;
                for (int i = 0; i + 1 < v.files.size(); i++) {
                    if (v.files.get(i).length() % 100000 != 0) {
                        throw new IOException("a file before the last has a size that is not a "
                                + "multiple of 100,000");
                    }
                }
            } else {
                v.starts.add(0L);
                RandomAccessFile f = new RandomAccessFile(path, "r");
                v.files.add(f);
                v.first = 0;
                v.length = f.length();
            }
            return v;
        }

        public long getLength() { return length; }
        public long getFirstPos() { return first; }

        public void read(long pos, byte[] dest, int destOffset, int len) throws IOException {
            if (pos < first || pos + len > length) {
                throw new IOException("read of " + len + " bytes at " + pos + ", outside "
                        + first + " to " + length);
            }
            while (len > 0) {
                int i = files.size() - 1;
                while (starts.get(i) > pos) {
                    i--;
                }
                RandomAccessFile f = files.get(i);
                long inFile = pos - starts.get(i);
                int n = (int) Math.min(len, f.length() - inFile);
                f.seek(inFile);
                f.readFully(dest, destOffset, n);
                pos += n;
                destOffset += n;
                len -= n;
            }
        }

        public void append(byte[] s, int o, int l) { throw new UnsupportedOperationException(); }
        public void pretruncate(long p) { throw new UnsupportedOperationException(); }
        public void seekFirstPos(long p) { throw new UnsupportedOperationException(); }

        public void close() throws IOException {
            for (RandomAccessFile f : files) {
                f.close();
            }
        }
    }

    // ======== Text ========

    private void error(String text) {
        errors++;
        out.println("error " + text);
    }

    /** A klong's decoded fields: its type and what the type holds. */
    static String klong(long k) {
        int type = (int) (k >>> 62);
        switch (type) {
        case 0:
            return "time=" + (k & 0x3fffffffffffffffL);
        case 1: {
            int len = (int) ((k >>> 3) & 7);
            byte[] b = new byte[len];
            for (int i = 0; i < len; i++) {
                b[i] = (byte) (k >>> (54 - 8 * i));
            }
            return "key len=" + len + " bytes=" + hex(b);
        }
        case 2:
            return "type2";
        default:
            return "del";
        }
    }

    /** The bkey of a key's segments (Keys.toBytes): each segment's bytes, by its length. */
    static byte[] bkeyOf(long[] segs) {
        java.io.ByteArrayOutputStream b = new java.io.ByteArrayOutputStream();
        for (long s : segs) {
            int len = (int) ((s >>> 3) & 7);
            for (int i = 0; i < len; i++) {
                b.write((int) (s >>> (54 - 8 * i)) & 0xff);
            }
        }
        return b.toByteArray();
    }

    /** The ikey's bytes as text, if all are printable ASCII but '='; else null. */
    static String ikeyText(byte[] bkey) {
        StringBuilder s = new StringBuilder();
        for (byte x : bkey) {
            int c = x == 1 ? '/' : (x - 2) & 0xff;
            if (c < 0x21 || c > 0x7e || c == '=') {
                return null;
            }
            s.append((char) c);
        }
        return s.toString();
    }

    static String ptr(long p) {
        return p == Spos.NULL ? "-1" : p + "/0x" + Long.toHexString(p);
    }

    static String hex16(long x) {
        return String.format("%016x", x);
    }

    static String hex(byte[] b) {
        return hex(b, 0, b.length);
    }

    static String hex(byte[] b, int off, int n) {
        StringBuilder s = new StringBuilder(2 * n);
        for (int i = 0; i < n; i++) {
            s.append(String.format("%02x", b[off + i] & 0xff));
        }
        return s.toString();
    }

    static String zeroOrHex(byte[] b, int off, int n) {
        return isZero(b, off, n) ? "zero" : hex(b, off, n);
    }

    static boolean isZero(byte[] b, int off, int n) {
        for (int i = 0; i < n; i++) {
            if (b[off + i] != 0) {
                return false;
            }
        }
        return true;
    }

    static String sha256(byte[] b, int off, int n) {
        try {
            MessageDigest d = MessageDigest.getInstance("SHA-256");
            d.update(b, off, n);
            return hex(d.digest());
        } catch (java.security.NoSuchAlgorithmException e) {
            throw new Error(e);
        }
    }

    static long le64(byte[] b, int o) {
        long x = 0;
        for (int i = 7; i >= 0; i--) {
            x = (x << 8) | (b[o + i] & 0xff);
        }
        return x;
    }

    static int le32(byte[] b, int o) {
        return (b[o] & 0xff) | (b[o + 1] & 0xff) << 8 | (b[o + 2] & 0xff) << 16
                | (b[o + 3] & 0xff) << 24;
    }

    static int le16u(byte[] b, int o) {
        return (b[o] & 0xff) | (b[o + 1] & 0xff) << 8;
    }

    static int le16(byte[] b, int o) {
        return (short) le16u(b, o);
    }
}
