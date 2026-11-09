package bergdb.core;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Map;
import java.util.Random;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Java's power-loss images for C (bergdb 012-14, done item 2, the other way;
 * 14-robustness.md, 6.5 point 3): FileStreamPowerLossTester.runTrace's
 * workload, on Java's Db through the tester's ModelIo, with its images
 * (Image.files: the files a power loss leaves at each event) written as
 * directories OUT/NNNNNN with image.txt ("event=E ack=0 acktime=T"), for
 * test/stress/power.sh (JAVAIMG=1) to start by both dumpers and compare.
 * Java's own test checks that each image keeps every acknowledged
 * transaction; power.sh checks that C recovers each to Java's state.
 *
 * Usage: java -cp CLASSES:OUT bergdb.core.PowerImages SEED TRANSACTIONS PER_EVENT OUT
 * Compiled by power.sh against build/java/classes (the tester is
 * package-private, so this class is in bergdb.core).
 */
public class PowerImages {
    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int transactions = Integer.parseInt(args[1]);
        int perEvent = Integer.parseInt(args[2]);
        File out = new File(args[3]);
        final long SEC = FileStreamPowerLossTester.SEC;

        // As FileStreamPowerLossTester.runTrace, without its verification.
        File dir = Files.createTempDirectory("bergdb-power-images-").toFile();
        FileStreamPowerLossTester.ModelIo io = new FileStreamPowerLossTester.ModelIo(dir, seed,
                perEvent);
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        FileStream stream = new FileStream(dir, io);
        Db db = FileStreamPowerLossTester.start(stream, clock);
        Random random = new Random(seed);
        long previousIteration = 0, previousStartup = 0, previousFrontier = 0;
        int keys = 12;
        long time = SEC;
        for (int i = 0; i < transactions; i++) {
            time += SEC / 10;
            io.logicalNow.set(time);
            clock.setTime(time);
            String key = FileStreamPowerLossTester.key(random.nextInt(keys));
            Trans transaction;
            if (i % 11 == 0) {
                transaction = db.trans().delete(key).build();
            } else {
                byte[] value = new byte[i % 37 == 0 ? 18000 : 1000 + random.nextInt(1000)];
                random.nextBytes(value);
                transaction = db.trans().put(key, value).build();
            }
            db.execute(transaction);
            stream.awaitDeletes();
            long iteration = db.getReclaimIterationCount();
            long startup = db.internal().getStartupPosForEvict();
            long frontier = db.getFirstAvailableLookupTime();
            if (io.recording) {
                io.checkpoint("after_user_commit");
                if (iteration != previousIteration) io.checkpoint("after_iteration_end");
                if (startup != previousStartup) io.checkpoint("after_writeout_progress");
                if (frontier != previousFrontier) io.checkpoint("after_cut_decision");
            }
            previousIteration = iteration;
            previousStartup = startup;
            previousFrontier = frontier;
            if (i % 5 == 0) {
                db.sync(SyncLevel.ORDINARY);
                io.acknowledged.set(db.lookupTime(Long.MAX_VALUE));
                io.acknowledgedFrontier.set(db.getFirstAvailableLookupTime());
                if (i >= 30 && !io.recording) {
                    io.recording = true;
                }
                io.checkpoint("after_durable_publication");
            }
        }
        db.sync(SyncLevel.ORDINARY);
        io.acknowledged.set(db.lookupTime(Long.MAX_VALUE));
        io.checkpoint("final_acknowledgement");
        db.stop();

        int k = 0;
        out.mkdirs();
        for (FileStreamPowerLossTester.Image image : io.snapshots()) {
            File d = new File(out, String.format("%06d", k++));
            if (!d.mkdirs()) throw new IOException("cannot make " + d);
            for (Map.Entry<String, byte[]> e : image.files.entrySet()) {
                try (FileOutputStream o = new FileOutputStream(new File(d, e.getKey()))) {
                    o.write(e.getValue());
                }
            }
            try (FileOutputStream o = new FileOutputStream(new File(d, "image.txt"))) {
                o.write(("event=" + image.event + " ack=0 acktime=" + image.acknowledgedTime
                        + " end=" + image.end() + "\n").getBytes("UTF-8"));
            }
        }
        System.out.println("power images=" + k + " lost=0 deletes=" + io.deletes + " stages="
                + io.seen + " lasttime=" + time);
        FileStreamPowerLossTester.remove(dir);
    }
}
