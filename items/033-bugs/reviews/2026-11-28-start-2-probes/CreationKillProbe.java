package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Review probe (bergdb 033, the second review of the start, 2026-11-28): a kill at every
 * byte of a creation, on a file database started through the Core API with created.txt
 * (bergdb 028-80 with 028-60, 028-18, 028-81 and 015-01). A creation is run once with the
 * stream's writes recorded; each image is the files before one of the writes and the first n
 * of its bytes, for every n, in five shapes: as a kill leaves a prefix; with zeros after it
 * to the next page boundary and a page; with the whole write's length, zeros after the first n
 * bytes; the first n bytes zero and the rest right ("a hole", outside the contract: counted
 * apart); and the write's first n bytes as zeros only. created.txt is not there (a creation
 * writes it after its sync), and for the first shape and the last also there: no kill
 * leaves that, as created.txt says that the creation was synced; a storage that lost the
 * bytes does, or a stream file put in the place of the database's.
 *
 * Each image is started. It must start and read and write, with created.txt written, or be
 * refused as a creation that did not complete (DatabaseNotCreatedException) with no file
 * changed; after the refusal the files are removed, as its message says, and the start must
 * create a database. Any other outcome is printed.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/CreationKillProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.CreationKillProbe OUT
 */
public class CreationKillProbe {
    static class Io extends FileStreamIo {
        final File dir;
        final List<Map<String, byte[]>> before = new ArrayList<Map<String, byte[]>>();
        final List<String> names = new ArrayList<String>();
        final List<byte[]> written = new ArrayList<byte[]>();
        boolean record;
        Io(File dir) { this.dir = dir; }
        protected void forceFile(File file, RandomAccessFile handle) { }
        protected void forceDirectory(File directory) { }
        protected synchronized void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
                throws IOException {
            if (record) {
                before.add(new TreeMap<String, byte[]>(FileStreamPowerLossTester.streamFiles(dir)));
                names.add(file.getName());
                written.add(Arrays.copyOfRange(bytes, offset, offset + length));
            }
            super.write(file, handle, bytes, offset, length);
        }
    }

    static TreeMap<String, Integer> kinds = new TreeMap<String, Integer>();
    static int bad;

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0], "db");
        rm(dir);
        dir.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(1000);
        DatabaseId id = DatabaseId.createRandom();
        Io io = new Io(dir);
        io.record = true;
        Db db = Db.builder().testSetup(new FileStream(dir, io, true)).id(id).createdTxt(dir).clock(clock).start();
        io.record = false;
        byte[] txt = Files.readAllBytes(new File(dir, "created.txt").toPath());
        db.close();
        int total = 0;
        for (byte[] w : io.written) total += w.length;
        System.out.println("the creation: " + io.written.size() + " writes, " + total + " bytes, the creation's"
                + " first record ends at " + Db.CREATION_LENGTH);
        for (int i = 0; i < io.written.size(); i++) {
            byte[] w = io.written.get(i);
            String name = io.names.get(i);
            byte[] was = io.before.get(i).get(name);
            if (was == null) was = new byte[0];
            for (int n = 0; n <= w.length; n++) {
                byte[] prefix = Arrays.copyOf(was, was.length + n);
                System.arraycopy(w, 0, prefix, was.length, n);
                int page = (4096 - prefix.length % 4096) % 4096 + 4096;
                byte[] zerosAfter = Arrays.copyOf(prefix, prefix.length + page);
                byte[] wholeLength = Arrays.copyOf(prefix, was.length + w.length);
                byte[] hole = Arrays.copyOf(was, was.length + w.length);
                System.arraycopy(w, n, hole, was.length + n, w.length - n);
                byte[] zerosOnly = Arrays.copyOf(was, was.length + n);
                boolean whole = n == w.length && i == io.written.size() - 1;
                one(dir, io.before.get(i), name, prefix, null, clock, id, "a prefix", whole);
                one(dir, io.before.get(i), name, prefix, txt, clock, id, "a prefix, created.txt there", whole);
                one(dir, io.before.get(i), name, zerosAfter, null, clock, id, "a prefix and zeros after it", whole);
                if (n < w.length) {
                    one(dir, io.before.get(i), name, wholeLength, null, clock, id, "the write's length, zeros after"
                            + " the prefix", false);
                }
                if (n > 0 && n < w.length) {
                    one(dir, io.before.get(i), name, hole, null, clock, id, "outside the contract: n zeros,"
                            + " then the write's bytes", false);
                }
                if (n > 0) one(dir, io.before.get(i), name, zerosOnly, null, clock, id, "zeros only", false);
                if (n > 0 && i == 0) {
                    // Not a kill's image: created.txt is written after the creation's sync.
                    one(dir, io.before.get(i), name, zerosOnly, txt, clock, id, "zeros only, created.txt there", false);
                }
            }
        }
        for (Map.Entry<String, Integer> e : kinds.entrySet()) System.out.println(e.getValue() + ": " + e.getKey());
        System.out.println("CREATIONKILL DONE: " + (bad == 0 ? "every image started or was refused as a creation"
                + " that did not complete, with no file changed" : bad + " BAD"));
    }

    static void one(File dir, Map<String, byte[]> before, String name, byte[] file, byte[] txt,
            CoreTestClock clock, DatabaseId id, String shape, boolean whole) throws IOException {
        rm(dir);
        dir.mkdirs();
        Map<String, byte[]> image = new TreeMap<String, byte[]>(before);
        image.put(name, file);
        for (Map.Entry<String, byte[]> e : image.entrySet()) Files.write(new File(dir, e.getKey()).toPath(), e.getValue());
        if (txt != null) Files.write(new File(dir, "created.txt").toPath(), txt);
        String outcome;
        FileStream s = null;
        try {
            s = new FileStream(dir, new Io(dir), true);
            Db db = Db.builder().testSetup(s).id(id).createdTxt(dir).clock(clock).start();
            db.execute(db.trans().put("k", new byte[] {1, 2, 3}).build());
            db.sync(SyncLevel.ORDINARY);
            boolean ok = Arrays.equals(DbUtil.get(db, Long.MAX_VALUE, "k"), new byte[] {1, 2, 3});
            db.close();
            boolean txtOk = new File(dir, "created.txt").isFile();
            outcome = file.length == 0 ? "started (an empty file: the start creates the database)"
                    : ok && txtOk ? (whole ? "started" : "started, though the creation's writes were not whole")
                    : "STARTED, " + (ok ? "" : "WRONG VALUE ") + (txtOk ? "" : "NO created.txt");
            if (!ok || !txtOk) bad++;
        } catch (DatabaseNotCreatedException e) {
            if (s != null) { try { s.close(); } catch (Throwable x) { } }
            boolean same = Arrays.equals(Files.readAllBytes(new File(dir, name).toPath()), file)
                    && new File(dir, "created.txt").isFile() == (txt != null);
            for (File f : dir.listFiles()) f.delete();
            String again;
            try {
                Db db = Db.builder().testSetup(new FileStream(dir, new Io(dir), true)).id(id).createdTxt(dir)
                        .clock(clock).start();
                db.close();
                again = "";
            } catch (Throwable x) {
                again = "; AFTER THE FILES WERE REMOVED: " + x;
                bad++;
            }
            if (!same) bad++;
            outcome = "DatabaseNotCreatedException" + (same ? "" : ", THE FILES CHANGED") + again
                    + (whole ? ", THOUGH THE CREATION WAS WHOLE" : "");
            if (whole) bad++;
        } catch (Throwable e) {
            if (s != null) { try { s.close(); } catch (Throwable x) { } }
            String m = String.valueOf(e.getMessage());
            outcome = "OTHER REFUSAL: " + e.getClass().getSimpleName() + ": " + m.substring(0, Math.min(m.length(), 160));
            if (!shape.startsWith("outside")) bad++;
            if (kinds.get(shape + ": " + outcome) == null) {
                System.out.println("first: " + shape + ", the file " + file.length + " bytes: " + outcome);
            }
        }
        kinds.merge(shape + ": " + outcome, 1, Integer::sum);
    }

    static void rm(File f) {
        File[] c = f.listFiles();
        if (c != null) for (File x : c) rm(x);
        f.delete();
    }
}
