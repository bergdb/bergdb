package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.Bytes;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): a refused start
 * changes no file, whatever it refuses for, on a file database that gives the start all of
 * its work at once (bergdb 028-70 with 028-66, 028-60 and 028-81): a torn last record to
 * complete (the header whole, 40 bytes), a tail of zeros after it that the open leaves out
 * and the first append or cut truncates, files that reclaim's cut took off and a power loss
 * kept (the start's own cut deletes them), with or without a gap among them (the files
 * before it are checked and deleted), and created.txt.
 *
 * Each case damages one thing in that image, starts the database through the Core API with
 * created.txt, and prints the refusal, every write, truncation, delete and rename that the
 * stream made during the start (there must be none), and whether the directory's files,
 * created.txt among them, are byte for byte as before (bergdb.lock is left out). The control,
 * the image as it is, must start with every key of the records before the torn one, and
 * prints the start's calls in their order.
 *
 * The cases: the last committed record of record format 10; with a startup pos after itself;
 * with a time not after the record's before it; the last valid meta block with a negative
 * time; a byte changed in the record before the last committed one (the walk parses only the
 * last); the files up to the one that holds reclaim's cut removed (the stream then begins
 * after the cut); every file but the last removed (the last valid meta block then names a
 * record before the stream's first position);
 * created.txt of another database ID, alone and with the next case's damage (created.txt's
 * refusal must come first); created.txt removed (the start writes it again); and
 * the record before the torn one with its last byte 0 changed to 7 (a tail to cut).
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/RefusedStartProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.RefusedStartProbe OUT [SEED]
 */
public class RefusedStartProbe {
    static final long SEC = FileStreamPowerLossTester.SEC;
    static final long MD = 200000;

    static class Io extends FileStreamIo {
        final Object gate = new Object();
        boolean held;
        final List<String> calls = new ArrayList<String>();
        boolean record;
        protected void forceFile(File file, RandomAccessFile handle) { }
        protected void forceDirectory(File directory) { }
        void release() { synchronized (gate) { held = false; gate.notifyAll(); } }
        synchronized void call(String what) { if (record) calls.add(what); }
        protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
                throws IOException {
            call("write " + length + " bytes to " + file.getName() + " at " + handle.getFilePointer());
            super.write(file, handle, bytes, offset, length);
        }
        protected void truncate(File file, RandomAccessFile handle, long length) throws IOException {
            call("truncate " + file.getName() + " from " + handle.length() + " to " + length);
            super.truncate(file, handle, length);
        }
        protected boolean rename(File file, File destination) throws IOException {
            call("rename " + file.getName());
            return super.rename(file, destination);
        }
        protected boolean delete(File file) throws IOException {
            synchronized (gate) {
                while (held) {
                    try { gate.wait(); } catch (InterruptedException e) { throw new IOException(e); }
                }
            }
            call("delete " + file.getName());
            return super.delete(file);
        }
    }

    static class Rec {
        long tpos, lastPos; String key; byte[] value;
    }

    static int bad;
    static DatabaseId id;
    static CoreTestClock clock;

    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        long seed = args.length > 1 ? Long.parseLong(args[1]) : 1;
        File dir = new File(base, "db");
        rm(dir);
        dir.mkdirs();
        Random r = new Random(seed);
        id = DatabaseId.createRandom();
        clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Io io = new Io();
        FileStream stream = new FileStream(dir, io, true);
        Db db = Db.builder().testSetup(stream).id(id).createdTxt(dir).clock(clock).start();
        db.setStartupDistance(20000);
        db.setRetainDuration(2 * SEC);
        List<Rec> recs = new ArrayList<Rec>();
        for (int i = 0; i < 1500; i++) {
            if (i == 800) io.held = true;       // the files of the later cuts stay
            // The last 300 commits within the retain duration: no cut after them, so that
            // the stream has files after the one that holds reclaim's cut.
            time += i < 1200 ? SEC / 10 : SEC / 1000;
            clock.setTime(time);
            Rec x = new Rec();
            x.key = "/k/" + r.nextInt(12);
            x.value = new byte[300 + r.nextInt(2700)];
            r.nextBytes(x.value);
            Trans t = db.trans().put(x.key, x.value).build();
            db.execute(t);
            x.tpos = t.tpos;
            x.lastPos = t.lastPos;
            recs.add(x);
        }
        db.sync(SyncLevel.ORDINARY);
        long firstPos = stream.getFirstPos();
        long cut = db.getFirstAvailablePos();
        Map<String, byte[]> whole = files(dir);
        byte[] txt = Files.readAllBytes(new File(dir, "created.txt").toPath());
        io.release();
        db.close();
        List<String> taken = new ArrayList<String>();
        for (String name : whole.keySet()) if (start(name) < firstPos) taken.add(name);
        System.out.println("the stream: files from " + start(whole.keySet().iterator().next()) + ", the first"
                + " position " + firstPos + ", reclaim's cut " + cut + "; " + taken.size()
                + " files that the cuts took off are kept: " + taken);
        if (taken.size() < 3) throw new AssertionError("too few files taken off, another seed");

        // The torn last record (its header whole), and zeros after it within the file.
        int last = recs.size() - 1;
        while (recs.get(last).tpos % MD > MD - 4000 || recs.get(last).tpos % MD < 128
                || recs.get(last - 1).tpos % MD > MD - 4000 || recs.get(last - 2).tpos % MD > MD - 4000) last--;
        Rec torn = recs.get(last), c = recs.get(last - 1), b = recs.get(last - 2);
        long tear = torn.tpos + 40;
        TreeMap<String, byte[]> model = new TreeMap<String, byte[]>();
        for (Rec x : recs) if (x.lastPos < tear) model.put(x.key, x.value);
        for (String gap : new String[] {"no gap", "a gap"}) {
            Map<String, byte[]> image = new TreeMap<String, byte[]>(whole);
            if (gap.equals("a gap")) image.remove(taken.get(taken.size() / 2));
            cutAt(image, tear);
            String lastName = null;
            for (String name : image.keySet()) lastName = name;
            byte[] lastFile = image.get(lastName);
            int zeros = (4096 - lastFile.length % 4096) % 4096 + 4096;
            image.put(lastName, Arrays.copyOf(lastFile, lastFile.length + zeros));
            System.out.println("== " + gap + ": the stream cut at " + tear + ", 40 bytes into the record at "
                    + torn.tpos + ", and " + zeros + " zeros after it; the last committed record at " + c.tpos);

            byte[] header = get(image, c.tpos, 32);
            byte[] f10 = header.clone();
            f10[4] = StoredTrans.RECORD_FORMAT + 1;
            byte[] sp = header.clone();
            Bytes.longToBytesLE(c.tpos + 8, sp, 16);
            byte[] tt = header.clone();
            System.arraycopy(get(image, b.tpos, 32), 8, tt, 8, 8);
            for (byte[] h : new byte[][] {f10, sp, tt}) StoredTrans.setHeaderCheck(id.getBytes(), c.tpos, h, 0);
            long lastBlock = tear / MD * MD;
            byte[] blockTime = new byte[8];
            Bytes.longToBytesLE(-1, blockTime, 0);
            byte[] flipped = get(image, b.tpos + 60, 1);
            flipped[0] ^= 0x55;
            // The files up to the one that holds reclaim's cut: without them the stream begins
            // after the cut.
            List<String> toCut = new ArrayList<String>();
            for (String name : image.keySet()) if (start(name) <= cut) toCut.add(name);
            String otherTxt = new String(txt, "ISO-8859-1").replace(id.idToString(),
                    DatabaseId.createRandom().idToString());

            refused(dir, image, txt, "the last committed record of format 10", c.tpos, f10, null, null);
            refused(dir, image, txt, "its startup pos after itself", c.tpos, sp, null, null);
            refused(dir, image, txt, "its time the time of the record before it", c.tpos, tt, null, null);
            refused(dir, image, txt, "the last valid meta block, at " + lastBlock + ", with the time -1",
                    lastBlock + 8, blockTime, null, null);
            refused(dir, image, txt, "a byte changed in the record at " + b.tpos + ", before the last"
                    + " committed one", b.tpos + 60, flipped, null, null);
            refused(dir, image, txt, "the files up to the one that holds reclaim's cut removed, " + toCut,
                    -1, null, toCut, null);
            List<String> butLast = new ArrayList<String>(image.keySet());
            butLast.remove(butLast.size() - 1);
            refused(dir, image, txt, "every stream file but the last removed", -1, null, butLast, null);
            refused(dir, image, txt, "created.txt of another database ID", -1, null, null,
                    otherTxt.getBytes("ISO-8859-1"));
            // created.txt's comparison comes before every other check: with a tail to cut too.
            refused(dir, image, txt, "created.txt of another database ID, and the last byte of the last"
                    + " committed record 7", c.lastPos, new byte[] {7}, null, otherTxt.getBytes("ISO-8859-1"));
            byte[] lastByte = {7};
            refused(dir, image, txt, "the last byte of the last committed record 7", c.lastPos, lastByte, null, null);

            // The control: the image as it is, and without created.txt.
            for (boolean withTxt : new boolean[] {true, false}) {
                restore(dir, image, withTxt ? txt : null);
                Io rec = new Io();
                rec.record = true;
                FileStream s = new FileStream(dir, rec, true);
                long before = s.getLength();
                Db d = Db.builder().testSetup(s).id(id).createdTxt(dir).clock(clock).start();
                List<String> calls;
                synchronized (rec) { calls = new ArrayList<String>(rec.calls); }
                String wrong = null;
                for (int i = 0; i < 12; i++) {
                    byte[] got = DbUtil.get(d, Long.MAX_VALUE, "/k/" + i);
                    if (!Arrays.equals(got, model.get("/k/" + i))) wrong = "/k/" + i;
                }
                d.sync(SyncLevel.ORDINARY);
                long after = d.getStreamLength();
                d.close();
                byte[] now = new File(dir, "created.txt").isFile()
                        ? Files.readAllBytes(new File(dir, "created.txt").toPath()) : null;
                boolean txtOk = now != null && new String(now, "ISO-8859-1").contains(id.idToString());
                if (wrong != null || !txtOk || after <= before) bad++;
                System.out.println("  the control" + (withTxt ? "" : ", created.txt removed") + ": started, "
                        + (wrong == null ? "every key as the model" : "WRONG VALUE of " + wrong)
                        + "; the stream " + before + " at the open, " + after + " after the start; created.txt "
                        + (txtOk ? "names the ID" : "DOES NOT NAME THE ID") + "; the stream's calls until"
                        + " start() returned: " + calls + "; all its calls: " + rec.calls);
                Db again = Db.builder().testSetup(new FileStream(dir, new Io(), true)).id(id).createdTxt(dir)
                        .clock(clock).start();
                for (int i = 0; i < 12; i++) {
                    if (!Arrays.equals(DbUtil.get(again, Long.MAX_VALUE, "/k/" + i), model.get("/k/" + i))) {
                        bad++;
                        System.out.println("  WRONG VALUE at the second start, /k/" + i);
                    }
                }
                again.close();
            }
        }
        System.out.println("REFUSEDSTART DONE: " + (bad == 0 ? "no start changed a file before it refused,"
                + " and the controls started" : bad + " BAD"));
    }

    /**
     * A start on 'image' with 'bytes' at stream position 'pos' (if 0 or more), without the
     * file 'remove' (if not null), with created.txt 'otherTxt' (if not null, else 'txt'):
     * it must refuse, and change nothing.
     */
    static void refused(File dir, Map<String, byte[]> image, byte[] txt, String what, long pos,
            byte[] bytes, List<String> remove, byte[] otherTxt) throws IOException {
        Map<String, byte[]> m = new TreeMap<String, byte[]>();
        for (Map.Entry<String, byte[]> e : image.entrySet()) m.put(e.getKey(), e.getValue().clone());
        if (pos >= 0) put(m, pos, bytes);
        if (remove != null) for (String name : remove) m.remove(name);
        restore(dir, m, otherTxt != null ? otherTxt : txt);
        Map<String, byte[]> before = all(dir);
        Io rec = new Io();
        rec.record = true;
        FileStream s = null;
        String outcome;
        try {
            s = new FileStream(dir, rec, true);
            Db d = Db.builder().testSetup(s).id(id).createdTxt(dir).clock(clock).start();
            d.close();
            outcome = "STARTED";
            bad++;
        } catch (Throwable e) {
            if (s != null) { try { s.close(); } catch (Throwable x) { } }
            StringBuilder sb = new StringBuilder();
            for (Throwable t = e; t != null; t = t.getCause()) {
                String msg = String.valueOf(t.getMessage());
                sb.append(t.getClass().getSimpleName()).append(": ").append(msg, 0, Math.min(msg.length(), 900)).append(" | ");
            }
            outcome = "refused, " + sb;
        }
        Map<String, byte[]> after = all(dir);
        boolean same = before.keySet().equals(after.keySet());
        for (String name : before.keySet()) same = same && Arrays.equals(before.get(name), after.get(name));
        if (!same || !rec.calls.isEmpty()) bad++;
        System.out.println("  " + what + ": the stream's calls " + rec.calls + (rec.calls.isEmpty() ? "" : " CALLS")
                + "; the files " + (same ? "as before" : "CHANGED") + "; " + outcome);
    }

    static long start(String name) { return Long.parseLong(name.substring(0, 14)) * 100000; }

    static byte[] get(Map<String, byte[]> image, long pos, int n) {
        for (Map.Entry<String, byte[]> e : image.entrySet()) {
            long s = start(e.getKey());
            if (s <= pos && pos + n <= s + e.getValue().length) {
                return Arrays.copyOfRange(e.getValue(), (int) (pos - s), (int) (pos - s) + n);
            }
        }
        throw new IllegalArgumentException("no file holds " + pos);
    }

    static void put(Map<String, byte[]> image, long pos, byte[] bytes) {
        for (Map.Entry<String, byte[]> e : image.entrySet()) {
            long s = start(e.getKey());
            if (s <= pos && pos + bytes.length <= s + e.getValue().length) {
                System.arraycopy(bytes, 0, e.getValue(), (int) (pos - s), bytes.length);
                return;
            }
        }
        throw new IllegalArgumentException("no file holds " + pos);
    }

    static void cutAt(Map<String, byte[]> files, long p) {
        for (String name : new ArrayList<String>(files.keySet())) {
            long s = start(name);
            if (s >= p) files.remove(name);
            else if (s + files.get(name).length > p) files.put(name, Arrays.copyOf(files.get(name), (int) (p - s)));
        }
    }

    static Map<String, byte[]> files(File dir) throws IOException {
        return new TreeMap<String, byte[]>(FileStreamPowerLossTester.streamFiles(dir));
    }

    /** Every file of 'dir' but bergdb.lock. */
    static Map<String, byte[]> all(File dir) throws IOException {
        Map<String, byte[]> m = new TreeMap<String, byte[]>();
        for (File f : dir.listFiles()) {
            if (!f.getName().equals("bergdb.lock")) m.put(f.getName(), Files.readAllBytes(f.toPath()));
        }
        return m;
    }

    static void restore(File dir, Map<String, byte[]> files, byte[] txt) throws IOException {
        for (File f : dir.listFiles()) if (!f.getName().equals("bergdb.lock")) f.delete();
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            Files.write(new File(dir, e.getKey()).toPath(), e.getValue());
        }
        if (txt != null) Files.write(new File(dir, "created.txt").toPath(), txt);
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
