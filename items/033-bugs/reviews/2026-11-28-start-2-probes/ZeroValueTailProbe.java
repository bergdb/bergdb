package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): the bound of the
 * tail of zeros that FileStream's open leaves out of the stream, 8 MB (ZERO_TAIL_MAX; bergdb
 * 028-60, part 2), against a kill's zeros that follow zeros of the database's own. The open
 * measures the run of zero bytes at the end of the last file. A kill's zeros are within the
 * write that it cuts, at most 5 MB (WRITE_MAX; bergdb 028-80), but the bytes before them can
 * be zeros too: a value of zeros. Then the run is longer than the kill's zeros.
 *
 * The probe fills a file database until its stream files are of 20 MB (a stream of 200 MB or
 * more), with values of random bytes, then commits a value of VALUE_BYTES bytes (default
 * 8,388,608, the largest value) under the key "z" and a small one under "s", with no sync
 * between, and syncs. The stream's writes are recorded. The image of the kill: the files as
 * they were after the write that holds the end of z's record, that write's bytes zero from the
 * first page boundary (16 KiB) in it to its end, as bergdb 028-60 and 031-02 saw a kill on
 * macOS leave them. Two databases are made so, z's value of zeros in one and of random bytes
 * in the other (the control), and each image is started.
 *
 * It prints, for each: the write, the run of zeros at the end of the last file, the start's
 * outcome, and after a refusal with a BadTailException the start of the stream cut at its P.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/ZeroValueTailProbe.java
 *   java -ea -Xmx2g -cp CLASSES:build/bergdb.jar bergdb.core.ZeroValueTailProbe OUT [VALUE_BYTES]
 * It writes about 500 MB under OUT and removes it.
 */
public class ZeroValueTailProbe {
    static final int PAGE = 16384;

    static class Io extends FileStreamIo {
        final List<long[]> writes = new ArrayList<long[]>();    // the file's first position, offset, length
        boolean record;
        protected void forceFile(File file, RandomAccessFile handle) { }
        protected void forceDirectory(File directory) { }
        protected synchronized void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
                throws IOException {
            if (record) {
                writes.add(new long[] {Long.parseLong(file.getName().substring(0, 14)) * 100000,
                    handle.getFilePointer(), length});
            }
            super.write(file, handle, bytes, offset, length);
        }
    }

    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        int valueBytes = args.length > 1 ? Integer.parseInt(args[1]) : 8 * 1024 * 1024;
        boolean refused = one(new File(base, "zeros"), valueBytes, true);
        boolean control = one(new File(base, "random"), valueBytes, false);
        System.out.println("ZEROVALUETAIL DONE: z's value of zeros: " + (refused ? "the start REFUSED" : "started")
                + "; of random bytes: " + (control ? "the start REFUSED" : "started"));
    }

    /** Returns whether the start of the image refused. */
    static boolean one(File dir, int valueBytes, boolean zeros) throws Exception {
        rm(dir);
        dir.mkdirs();
        Random r = new Random(7);
        CoreTestClock clock = new CoreTestClock();
        long time = 1000;
        clock.setTime(time);
        Io io = new Io();
        FileStream stream = new FileStream(dir, io, false);
        Db db = builder(stream, clock).start();
        TreeMap<String, byte[]> model = new TreeMap<String, byte[]>();
        byte[] big = new byte[8 * 1024 * 1024];
        // Until the last file is of 20 MB and has room for z's record and the small one.
        for (int i = 0; ; i++) {
            long length = db.getStreamLength();
            if (length > 225L * 1000 * 1000 && length % (20L * 1000 * 1000) < 2L * 1000 * 1000) break;
            r.nextBytes(big);
            byte[] v = Arrays.copyOf(big, 1000 * 1000 + r.nextInt(1000 * 1000));
            String key = "/fill/" + (i % 40);
            clock.setTime(++time);
            db.execute(db.trans().put(key, v).build());
            model.put(key, v);
        }
        db.sync(SyncLevel.ORDINARY);
        byte[] z = new byte[valueBytes];
        if (!zeros) r.nextBytes(z);
        byte[] small = new byte[2000];
        r.nextBytes(small);
        io.record = true;
        clock.setTime(++time);
        Trans tz = db.trans().put("z", z).build();
        db.execute(tz);
        clock.setTime(++time);
        Trans ts = db.trans().put("s", small).build();
        db.execute(ts);
        db.sync(SyncLevel.ORDINARY);
        io.record = false;
        db.close();

        File[] files = dir.listFiles((d, name) -> name.endsWith(".bergdb"));
        Arrays.sort(files);
        File last = files[files.length - 1];
        long lastStart = Long.parseLong(last.getName().substring(0, 14)) * 100000;
        System.out.println("== z's value of " + valueBytes + (zeros ? " zeros" : " random bytes") + ": "
                + files.length + " stream files, the last at " + lastStart + ", " + last.length() + " bytes, the one"
                + " before it " + files[files.length - 2].length() + "; z's record " + tz.tpos + " to "
                + tz.lastPos + ", s's " + ts.tpos + " to " + ts.lastPos);
        StringBuilder w = new StringBuilder();
        long[] cutWrite = null;
        for (long[] x : io.writes) {
            w.append(" [").append(x[0] + x[1]).append(", ").append(x[2]).append(" bytes]");
            if (cutWrite == null && x[0] + x[1] <= tz.lastPos && tz.lastPos < x[0] + x[1] + x[2]) cutWrite = x;
        }
        System.out.println("   the writes of the two records:" + w);
        if (cutWrite == null || cutWrite[0] != lastStart || tz.tpos < lastStart) {
            System.out.println("   NOT RUN: z's record is not whole in the last file");
            return false;
        }
        long writeEnd = cutWrite[1] + cutWrite[2];      // in the file
        long p = (cutWrite[1] + PAGE - 1) / PAGE * PAGE;
        try (RandomAccessFile f = new RandomAccessFile(last, "rw")) {
            f.setLength(writeEnd);
            f.seek(p);
            f.write(new byte[(int) (writeEnd - p)]);
        }
        long run = 0;
        try (RandomAccessFile f = new RandomAccessFile(last, "r")) {
            byte[] all = new byte[(int) f.length()];
            f.readFully(all);
            while (run < all.length && all[all.length - 1 - (int) run] == 0) run++;
        }
        System.out.println("   the kill: in the write at " + (lastStart + cutWrite[1]) + " of " + cutWrite[2]
                + " bytes, which holds the end of z's record and " + (lastStart + writeEnd - tz.lastPos - 1)
                + " bytes after it; its bytes zero from the page boundary at " + (lastStart + p) + ", "
                + (writeEnd - p) + " zeros; the run of zeros at the end of the last file: " + run + " bytes");
        byte[] before = Files.readAllBytes(last.toPath());
        boolean refused = false;
        long cutAt = -1;
        FileStream s = null;
        try {
            s = new FileStream(dir, new Io(), false);
            long open = s.getLength();
            Db d = builder(s, clock).start();
            System.out.println("   started: the stream " + open + " at the open (" + (lastStart + writeEnd - open)
                    + " zeros left out), z " + (DbUtil.get(d, Long.MAX_VALUE, "z") == null ? "not there" : "THERE")
                    + ", s " + (DbUtil.get(d, Long.MAX_VALUE, "s") == null ? "not there" : "THERE") + ", "
                    + wrong(d, model));
            d.close();
        } catch (Throwable e) {
            refused = true;
            long open = s == null ? -1 : s.getLength();
            if (s != null) { try { s.close(); } catch (Throwable x) { } }
            bergdb.storage.BadTailException tail = null;
            for (Throwable t = e; t != null; t = t.getCause()) {
                if (t instanceof bergdb.storage.BadTailException) tail = (bergdb.storage.BadTailException) t;
            }
            System.out.println("   REFUSED: the stream " + open + " at the open (" + (lastStart + writeEnd - open)
                    + " zeros left out); the last file " + (Arrays.equals(before, Files.readAllBytes(last.toPath()))
                    ? "as before" : "CHANGED") + "; " + e.getClass().getSimpleName() + ": " + e.getMessage());
            if (tail != null) cutAt = tail.getCutPos();
        }
        if (cutAt >= 0) {
            try (RandomAccessFile f = new RandomAccessFile(last, "rw")) {
                f.setLength(cutAt - lastStart);
            }
            Db d = builder(new FileStream(dir, new Io(), false), clock).start();
            System.out.println("   cut at P, " + cutAt + ", as the message says: started, z "
                    + (DbUtil.get(d, Long.MAX_VALUE, "z") == null ? "not there" : "THERE") + ", s "
                    + (DbUtil.get(d, Long.MAX_VALUE, "s") == null ? "not there" : "THERE") + ", " + wrong(d, model));
            d.close();
        }
        rm(dir);
        return refused;
    }

    /** The test setup, with the buffer of a user's database: 10 MB, 50 ms (StorageManager's defaults). */
    static DbBuilder builder(FileStream stream, CoreTestClock clock) {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        return b.stream("main", stream, 10 * 1000 * 1000, 50).clock(clock);
    }

    static String wrong(Db d, TreeMap<String, byte[]> model) {
        for (String key : model.keySet()) {
            if (!Arrays.equals(DbUtil.get(d, Long.MAX_VALUE, key), model.get(key))) return "WRONG VALUE of " + key;
        }
        return "the " + model.size() + " keys before z as written";
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
