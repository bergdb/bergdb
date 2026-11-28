package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;

import bergdb.stream.FileStream;

/**
 * Review probe (bergdb 033, review of the start, 2026-11-28): a kill during a creation's
 * writes. The creation's bytes are taken from a new database (the first meta block and
 * the primordial record, Db.CREATION_LENGTH bytes, then the record of the startup
 * distance). For each image of the first stream file,
 * a start is tried and its refusal printed: the first K bytes (a cut creation, 005-33), and
 * the first K bytes followed by zeros to 4,096 (the zeros of 028-60, where the cut write's
 * bytes should be), K from 0 to one less than the two records of the creation.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/StartChain.java PROBES/CreationZerosProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.CreationZerosProbe OUT
 */
public class CreationZerosProbe {
    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        StartChain.rm(base);
        File made = new File(base, "made");
        made.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(FileStreamPowerLossTester.SEC);
        try (Db db = Db.builder().testSetup(new FileStream(made)).clock(clock).start()) { }
        byte[] creation = Files.readAllBytes(new File(made, "00000000000000.bergdb").toPath());
        System.out.println("a new database's stream: " + creation.length + " bytes");
        // In the first meta block, in the primordial record, at its end, in the second record.
        int[] cuts = {0, 1, 4, 8, 60, 128, 130, 200, (int) Db.CREATION_LENGTH - 1,
            (int) Db.CREATION_LENGTH, (int) Db.CREATION_LENGTH + 2, (int) Db.CREATION_LENGTH + 40,
            creation.length - 1};
        for (int zeros = 0; zeros < 2; zeros++) {
            for (int k : cuts) {
                if (k == 0 && zeros == 0) continue;
                File dir = new File(base, "k" + k + "z" + zeros);
                dir.mkdirs();
                byte[] image = Arrays.copyOf(Arrays.copyOf(creation, k), zeros == 1 ? 4096 : k);
                Files.write(new File(dir, "00000000000000.bergdb").toPath(), image);
                String result;
                try (Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).start()) {
                    result = "started";
                } catch (RuntimeException e) {
                    String m = String.valueOf(e.getMessage());
                    result = e.getClass().getSimpleName() + ": " + m.substring(0, Math.min(110, m.length()));
                }
                boolean same = Arrays.equals(image, Files.readAllBytes(new File(dir, "00000000000000.bergdb").toPath()));
                System.out.println(k + " bytes of the creation" + (zeros == 1 ? ", zeros to 4096" : "")
                        + ": " + result + (same ? "" : " (THE FILE CHANGED)"));
            }
        }
        StartChain.rm(base);
    }
}
