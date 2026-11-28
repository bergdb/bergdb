import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;

import java.io.File;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * 031-08, part B, UB-3 and UB-4: a stream file of another database, of the same name and
 * length, put in place of one of a stopped database's files. Two databases A and B are made
 * with the same puts (keys and value lengths), each value beginning with its database's
 * name; a copy C of A gets B's file of the same name: the first file (mode first) or the
 * file in the middle (mode middle). C is started with open().
 *   first:  the refusal, and then its way out followed as the message gives it (cut the
 *           stream at P, remove the later files): what the start then holds.
 *   middle: what the start holds: every key's value, and whose it is.
 *
 * Usage (from the repository's root, after java/build.sh):
 *   javac -cp java/build/bergdb-release.jar -d /tmp/p items/031-release-2026-7/08-user-apps/probes/ForeignFileProbe.java
 *   java -cp java/build/bergdb-release.jar:/tmp/p ForeignFileProbe first /tmp/p/db
 *   java -cp java/build/bergdb-release.jar:/tmp/p ForeignFileProbe middle /tmp/p/db
 */
public class ForeignFileProbe {
    public static void main(String[] a) throws Exception {
        String mode = a[0];
        File base = new File(a[1]);
        rmrf(base);
        File A = new File(base, "A"), B = new File(base, "B"), C = new File(base, "C");
        for (File d : new File[] {A, B}) {
            try (Database db = Factory.database().create(d.getPath()).start()) {
                db.setStartupDistanceInMb(5);
                Connection c = db.connection();
                Random r = new Random(1);
                for (int i = 0; i < 600; i++) {
                    byte[] v = new byte[20_000 + r.nextInt(40_000)];
                    byte[] h = (d.getName() + ":" + i + ":").getBytes();
                    System.arraycopy(h, 0, v, 0, h.length);
                    c.put("/k/x" + (i % 300) + ".bin", v);
                }
                c.sync();
            }
        }
        System.out.println("A's created.txt: " + new String(Files.readAllBytes(new File(A, "created.txt").toPath()))
                .replace('\n', ' '));
        C.mkdirs();
        for (File f : A.listFiles()) if (!f.getName().equals("bergdb.lock")) Files.copy(f.toPath(), new File(C, f.getName()).toPath());
        List<String> names = new ArrayList<>();
        for (File f : C.listFiles()) if (f.getName().endsWith(".bergdb")) names.add(f.getName());
        Collections.sort(names);
        String name = mode.equals("first") ? names.get(0) : names.get(names.size() / 2);
        Files.copy(new File(B, name).toPath(), new File(C, name).toPath(), StandardCopyOption.REPLACE_EXISTING);
        System.out.println("B's " + name + " in place of A's (" + names.size() + " files)");
        long p = -1;
        try (Database db = Factory.database().open(C.getPath()).start()) {
            System.out.println("accepted: " + census(db));
        } catch (Exception e) {
            System.out.println("refused: " + e.getClass().getName() + ": " + e.getMessage());
            Matcher m = Pattern.compile("records end at stream position (\\d+)").matcher(String.valueOf(e.getMessage()));
            if (m.find()) p = Long.parseLong(m.group(1));
        }
        if (p < 0) return;
        // The way out, as the message gives it.
        for (String n : names) {
            File f = new File(C, n);
            long s0 = Long.parseLong(n.substring(0, 14)) * 100_000L;
            if (s0 > p) Files.delete(f.toPath());
            else if (s0 + f.length() > p) try (RandomAccessFile raf = new RandomAccessFile(f, "rw")) { raf.setLength(p - s0); }
        }
        try (Database db = Factory.database().open(C.getPath()).start()) {
            System.out.println("after the way out: accepted: " + census(db));
        } catch (Exception e) {
            System.out.println("after the way out: refused: " + e);
        }
    }

    static String census(Database db) {
        Map<String, Integer> whose = new TreeMap<>();
        int n = 0;
        for (Kv<byte[]> kv : db.connection().usePrimary(byte[].class).dir("/k/").kvs()) {
            String h = new String(kv.value(), 0, 2);
            whose.merge(h, 1, Integer::sum);
            n++;
        }
        return n + " keys, by the first bytes of their values: " + whose;
    }

    static void rmrf(File f) throws Exception {
        if (!f.exists()) return;
        if (f.isDirectory()) for (File c : f.listFiles()) rmrf(c);
        Files.delete(f.toPath());
    }
}
