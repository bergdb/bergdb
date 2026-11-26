import java.io.*;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.*;
import java.util.*;

/**
 * EfaultProbe (bergdb 035-02). Without BergDB and without a kill: a write whose source memory
 * ends inside it, so that the kernel's copy of the write fails there (EFAULT), as 035-01's
 * hypothesis has the copy fail when a kill takes the process's memory (035-01, section 9).
 *
 * Each try: a file "old" of 8 MiB, every byte 0x5a, written, forced (FileChannel.force(true))
 * and deleted; then a file "src" of 8 MiB, every byte this try's own value (never 0 or 0x5a),
 * mapped (MappedByteBuffer, read only) and truncated to a random cutoff, a multiple of PAGE above
 * 1 MiB; then FileChannel.write of the whole mapping into a new file "dst", which the kernel copies
 * from the mapping until the cutoff, where the copy faults; dst forced, read and compared: its
 * length, and how many of its bytes are not the try's value: zeros, 0x5a (the deleted file's) or
 * other (an older file's). One line per try for the first few, then the totals.
 *
 * Usage: java EfaultProbe.java DIR TRIES [seed=N] [page=BYTES]
 *   page  the page size, for the cutoffs (default 16384, macOS on Apple silicon; 4096 on Linux)
 *
 * 2026-11-26.
 */
public class EfaultProbe {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int tries = Integer.parseInt(a[1]);
        Map<String, String> o = new HashMap<>();
        for (int i = 2; i < a.length; i++) o.put(a[i].substring(0, a[i].indexOf('=')), a[i].substring(a[i].indexOf('=') + 1));
        Random r = new Random(Long.parseLong(o.getOrDefault("seed", "1")));
        int page = Integer.parseInt(o.getOrDefault("page", "16384"));
        final int size = 8 << 20;
        dir.mkdirs();
        byte[] old = new byte[size];
        Arrays.fill(old, (byte) 0x5a);
        long errors = 0, shortWrites = 0, fullWrites = 0, wrongFiles = 0, zero = 0, oldBytes = 0, other = 0;
        for (int j = 0; j < tries; j++) {
            File of = new File(dir, "old");
            try (RandomAccessFile f = new RandomAccessFile(of, "rw")) {
                f.setLength(0);
                f.write(old);
                f.getChannel().force(true);
            }
            of.delete();
            byte v = (byte) (0x60 + r.nextInt(150));
            File src = new File(dir, "src");
            byte[] s = new byte[size];
            Arrays.fill(s, v);
            try (RandomAccessFile f = new RandomAccessFile(src, "rw")) {
                f.setLength(0);
                f.write(s);
            }
            long cutoff = (long) page * ((1 << 20) / page + 1 + r.nextInt(size / page - (1 << 20) / page - 2));
            File dst = new File(dir, "dst");
            dst.delete();
            String res;
            try (FileChannel sc = FileChannel.open(src.toPath(), StandardOpenOption.READ, StandardOpenOption.WRITE);
                 FileChannel dc = FileChannel.open(dst.toPath(), StandardOpenOption.CREATE, StandardOpenOption.WRITE)) {
                MappedByteBuffer mb = sc.map(FileChannel.MapMode.READ_ONLY, 0, size);
                sc.truncate(cutoff);
                try {
                    int w = dc.write(mb);
                    res = "wrote " + w;
                    if (w < size) shortWrites++; else fullWrites++;
                } catch (IOException e) {
                    res = "IOException " + e.getMessage();
                    errors++;
                }
                dc.force(true);
            }
            byte[] d = Files.readAllBytes(dst.toPath());
            long bad = 0, firstBad = -1;
            for (int q = 0; q < d.length; q++) {
                if (d[q] == v) continue;
                if (firstBad < 0) firstBad = q;
                bad++;
                if (d[q] == 0) zero++; else if (d[q] == 0x5a) oldBytes++; else other++;
            }
            if (bad > 0) wrongFiles++;
            if (j < 5) System.out.println(j + ": cutoff " + cutoff + ", " + res + ", length " + d.length + ", wrong bytes " + bad
                    + (firstBad >= 0 ? " from " + firstBad : ""));
            src.delete();
            dst.delete();
        }
        System.out.println("tries " + tries + ": IOException " + errors + ", short writes " + shortWrites + ", whole writes "
                + fullWrites + "; files with a wrong byte " + wrongFiles + "; wrong bytes zero " + zero + ", 0x5a " + oldBytes
                + ", other " + other);
    }
}
