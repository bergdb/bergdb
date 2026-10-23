package bergdb.core;

import java.io.File;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Arrays;

import bergdb.storage.RecoverableStream;
import bergdb.stream.FileStream;

/**
 * Bergdb 005-27 (2026-10-23), on disk: a transaction that ends exactly at a meta block's
 * position that is also the end of a FileStream file (1,200,000: six files of 200,000
 * bytes), and the crash images there: the next file not created, or created and empty.
 * Each image is started, checked, given a put, and restarted. Prints what it finds.
 *
 * Usage: tools/run.sh DIR (DIR must not exist), or
 *   java -ea -cp bergdb.jar:CLASSES bergdb.core.FileBoundaryProbe DIR
 */
public class FileBoundaryProbe {
    static final long TARGET = 1200 * 1000;

    static Db start(File dir) throws Exception {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", new FileStream(dir), 100 * 1000, 10);
        return b.start();
    }

    static String list(File dir) {
        File[] fs = dir.listFiles();
        Arrays.sort(fs);
        StringBuilder sb = new StringBuilder();
        for (File f : fs) sb.append(' ').append(f.getName()).append('=').append(f.length());
        return sb.toString();
    }

    public static void main(String[] args) throws Exception {
        File root = new File(args[0]);
        if (root.exists()) throw new IllegalArgumentException(root + " exists");
        File dir = new File(root, "main");
        final int dist = RecoverableStream.META_BLOCK_DISTANCE;
        Db db = start(dir);
        db.execute(db.trans().put("key1", "value1"));
        Trans trans = db.trans().put("key2", new byte[1000]).build();
        db.execute(trans);
        long overhead = trans.nextPos - trans.tpos - 1000;
        while (TARGET - trans.nextPos > 150 * 1000) {
            trans = db.trans().put("key2", new byte[100 * 1000]).build();
            db.execute(trans);
        }
        // The last put of key2 is sized to end at TARGET; 128 bytes more per meta block in it.
        long blocks = (TARGET - 1) / dist - trans.nextPos / dist;
        byte[] v2 = new byte[(int) (TARGET - trans.nextPos - overhead
                - blocks * RecoverableStream.META_BLOCK_SIZE)];
        v2[0] = 2;
        trans = db.trans().put("key2", v2).build();
        db.execute(trans);
        db.execute(db.trans().put("key3", "value3"));
        db.sync(SyncLevel.STRONG);
        db.close();
        System.out.println("key2's last put ends at " + (trans.lastPos + 1) + " (target " + TARGET
                + "); files:" + list(dir));

        for (String kind : new String[] {"no next file", "next file empty"}) {
            File img = new File(root, kind.replace(' ', '-'));
            img.mkdirs();
            for (File f : dir.listFiles()) {
                long fpos = Long.parseLong(f.getName().replace(".bergdb", "")) * 100 * 1000;
                File g = new File(img, f.getName());
                if (fpos < TARGET) {
                    Files.copy(f.toPath(), g.toPath());
                } else if (fpos == TARGET && kind.equals("next file empty")) {
                    new RandomAccessFile(g, "rw").close();
                }
            }
            System.out.println("Image, " + kind + ":" + list(img));
            try {
                Db d = start(img);
                System.out.println("  started: key2 " + (Arrays.equals(v2, DbUtil.get(d, "key2"))
                        ? "right" : "WRONG") + ", key3 " + DbUtil.getString(d, "key3"));
                d.execute(d.trans().put("key4", "value4"));
                d.sync(SyncLevel.STRONG);
                d.close();
                System.out.println("  after a put of key4, files:" + list(img));
                Db d2 = start(img);
                System.out.println("  restarted: key2 " + (Arrays.equals(v2, DbUtil.get(d2, "key2"))
                        ? "right" : "WRONG") + ", key4 " + DbUtil.getString(d2, "key4"));
                d2.close();
            } catch (Exception e) {
                System.out.println("  startup FAILED: " + e);
            }
        }
    }
}
