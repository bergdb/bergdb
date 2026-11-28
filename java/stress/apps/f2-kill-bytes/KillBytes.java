import bergdb.core.Db;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.SyncLevel;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * App f2 of 031-08 (part B): the README's "One stream" under kills. f1's actions (the same
 * seed gives the same list, SameBytes.makeActs) run first in this process as the ref, with
 * the stream read after each action. Then chains of child JVMs run the same actions on one
 * directory, each child killed with SIGKILL (Process.destroyForcibly), and this process
 * starts the database after each kill:
 *   between  the child, after a chosen action and its sync, prints P and waits: the kill
 *            comes between two actions;
 *   unsynced the same without the sync: the write buffer may hold the last action;
 *   random   a kill after 30 to 1,500 ms, at any point of the actions, starts and syncs.
 * Checks:
 *   K1  at each kill the stream files hold a prefix of the ref's stream, byte for byte, but
 *       for a run of zeros at the end of the last file (Database, "What a crash keeps":
 *       APFS can leave zeros there), and every action that a sync returned for;
 *   K2  the start after the kill: if the stream, without such zeros, ends where an action of
 *       the ref ended, the start writes nothing (every file's bytes as before) and holds the
 *       state after those actions; if it ends inside an action's records, the start holds
 *       the state after the actions before it (each transaction whole or not at all), at
 *       least to the last synced, and its writes leave the bytes before the cut as they were;
 *   K3  a chain whose starts all found the stream at an action's end ends, after all the
 *       actions, with the ref's files, byte for byte (a kill and a restart change no byte);
 *   K5  after such a kill, children that only start the database are killed 0 to 200 ms after
 *       they begin to start, one to three times; a start then holds the same state, and the stream
 *       is that of a start that no kill cut (027-11, section 1.3);
 *   K4  after a start that wrote (a torn end completed), two copies of the files as the kill
 *       left them, each started and given the same next actions, end with the same bytes:
 *       the recovery's bytes too are decided by the stream so far. The chain then ends.
 *
 * Usage: java -cp bergdb-release.jar:out KillBytes SEED ACTIONS DIR KILLS [KEYS]
 *        (the child: KillBytes child SEED ACTIONS DIR PAUSE SYNCPAUSE KEYS)
 */
public class KillBytes {
    static long seed;
    static int nActs, nKeys;
    static File base;
    static SameBytes.Result ref;
    static long kills, betweenKills, randomKills, boundaryStarts, writingStarts, chains, chainsWhole,
            zeroTails, k4Checks, childEnds, notCreated, deadDeleted, layoutNotes, k5Checks, k5Kills;

    public static void main(String[] a) throws Exception {
        if (a[0].equals("child")) {
            child(a);
            return;
        }
        if (a[0].equals("recover")) {
            // A start and a close only: the parent kills it during the start (K5).
            SameBytes.Run x = new SameBytes.Run();
            x.name = "recover";
            x.r = new Random(1);
            x.dir = new File(a[3]);
            System.out.println("U");
            System.out.flush();
            SameBytes.start(x);
            x.db.close();
            System.out.println("D");
            return;
        }
        seed = Long.parseLong(a[0]);
        nActs = Integer.parseInt(a[1]);
        base = new File(a[2]);
        int maxKills = Integer.parseInt(a[3]);
        nKeys = a.length > 4 ? Integer.parseInt(a[4]) : 1200;
        Common.rmrf(base);
        base.mkdirs();
        setUp(seed, nActs, nKeys, base);
        long t0 = System.currentTimeMillis();
        Random r = new Random(seed * 13 + 5);
        try {
            ref = SameBytes.run("ref");
            Common.rmrf(new File(base, "ref"));
            StringBuilder sb = new StringBuilder();
            for (long l : ref.lens) sb.append(l).append('\n');
            Files.write(new File(base, "lens-" + seed).toPath(), sb.toString().getBytes());
            Files.write(new File(base, "lens-" + seed + ".created").toPath(), ("" + ref.createdLen + "\n").getBytes());
            log("ref: " + nActs + " actions, stream " + ref.length + ", " + ref.files.size() + " files");
            while (kills < maxKills) {
                chain(r, maxKills);
            }
        } catch (Common.Fail e) {
            System.out.println("FAILED seed " + seed + ": " + e.getMessage());
            System.exit(1);
        }
        Common.rmrf(base);
        System.out.println("OK KillBytes seed " + seed + ", " + nActs + " actions, " + kills + " kills (" + betweenKills
                + " between actions, " + randomKills + " random), " + boundaryStarts + " starts at an action's end, "
                + writingStarts + " starts that completed a torn end (" + k4Checks + " K4 checks, " + k5Checks + " K5 checks after "
                + k5Kills + " kills during the completion, " + invalidBlocks + " meta blocks completed as invalid ones), " + zeroTails
                + " zero tails, " + deadDeleted + " files of a decided cut deleted by a start, " + layoutNotes
                + " chains with other files (NOTE), " + notCreated + " kills before the creation was durable, " + chains + " chains, " + chainsWhole + " whole chains equal to the ref, "
                + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static void setUp(long s, int n, int keys, File dir) {
        SameBytes.seed = s;
        SameBytes.nKeys = keys;
        SameBytes.base = dir;
        SameBytes.universe.clear();
        SameBytes.acts.clear();
        SameBytes.makeUniverse();
        SameBytes.makeActs(n);
    }

    // ------------------------------------------------------------------ the parent

    static void chain(Random r, int maxKills) throws Exception {
        chains++;
        File dir = new File(base, "chain" + chains);
        Common.rmrf(dir);
        dir.mkdirs();
        int done = 0;            // actions in the database, at an action's end
        while (kills < maxKills) {
            int mode = r.nextInt(3);          // 0 between, 1 unsynced, 2 random
            int pause = done + 1 + r.nextInt(Math.max(1, Math.min(nActs - done, 120)));
            if (pause >= nActs) pause = -1;   // run to the end
            if (mode == 2) pause = -1;
            new File(dir.getPath() + ".progress").delete();
            Files.write(new File(dir.getPath() + ".progress").toPath(), new byte[0]);
            Process p = spawn(dir, mode == 2 ? -1 : pause, mode == 0);
            BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()));
            int lastA = done - 1, lastS = done - 1;    // the actions before the child's start are synced (a close)
            boolean ended = false, paused = false;
            long killAt = mode == 2 ? System.currentTimeMillis() + 30 + r.nextInt(1470) : Long.MAX_VALUE;
            StringBuilder out = new StringBuilder();
            while (true) {
                if (mode == 2 && System.currentTimeMillis() >= killAt) break;
                if (!in.ready()) {
                    if (!p.isAlive() && !in.ready()) break;
                    Thread.sleep(1);
                    continue;
                }
                String line = in.readLine();
                if (line == null) break;
                if (line.startsWith("A ")) lastA = Integer.parseInt(line.substring(2));
                else if (line.startsWith("S ")) lastS = Integer.parseInt(line.substring(2));
                else if (line.startsWith("P ")) { paused = true; break; }
                else if (line.equals("END")) { ended = true; }
                else out.append(line).append('\n');
                if (out.length() > 20_000) out.setLength(20_000);
            }
            if (ended) {
                p.waitFor(60, TimeUnit.SECONDS);
                childEnds++;
                // K3: all actions done through kills and restarts at actions' ends.
                compareWithRef(dir, "chain " + chains + " at its end");
                chainsWhole++;
                log("chain " + chains + ": all " + nActs + " actions, equal to the ref's files");
                Common.rmrf(dir);
                return;
            }
            p.destroyForcibly();
            p.waitFor(60, TimeUnit.SECONDS);
            // The child's progress file: every line it wrote before the kill (a write per line).
            for (String line : Files.readAllLines(new File(dir.getPath() + ".progress").toPath())) {
                // A line cut by the kill has fewer digits: max() leaves it out.
                if (line.startsWith("A ")) lastA = Math.max(lastA, parse(line.substring(2)));
                else if (line.startsWith("S ")) lastS = Math.max(lastS, parse(line.substring(2)));
            }
            if (!paused && mode != 2) {
                throw new Common.Fail("chain " + chains + ": the child ended without END or P (exit " + p.exitValue()
                        + "):\n" + out);
            }
            if (out.length() > 0 && out.indexOf("Exception") >= 0) {
                throw new Common.Fail("chain " + chains + ": the child wrote:\n" + out);
            }
            kills++;
            if (mode == 2) randomKills++; else betweenKills++;
            int synced = mode == 0 && paused ? pause : lastS;
            int after = afterKill(dir, synced, lastA, mode, r);
            if (after < 0) {
                Common.rmrf(dir);
                return;              // the chain ended at a start that wrote (K4 done)
            }
            done = after;
        }
        Common.rmrf(dir);
    }

    static int parse(String s) {
        try { return Integer.parseInt(s.trim()); } catch (NumberFormatException e) { return -1; }
    }

    static Process spawnRecover(File dir) throws IOException {
        String java = System.getProperty("java.home") + "/bin/java";
        ProcessBuilder pb = new ProcessBuilder(java, "-ea", "-Xmx1g", "-cp", System.getProperty("java.class.path"), "KillBytes",
                "recover", "" + seed, "" + nActs, dir.getPath(), "" + nKeys);
        pb.redirectErrorStream(true);
        return pb.start();
    }

    static Process spawn(File dir, int pause, boolean syncPause) throws IOException {
        String java = System.getProperty("java.home") + "/bin/java";
        List<String> cmd = new ArrayList<>(Arrays.asList(java, "-ea", "-Xmx1g", "-XX:+ExitOnOutOfMemoryError",
                "-Df1.big=" + SameBytes.BIG, "-cp",
                System.getProperty("java.class.path"), "KillBytes", "child", "" + seed, "" + nActs, dir.getPath(),
                "" + pause, "" + syncPause, "" + nKeys));
        ProcessBuilder pb = new ProcessBuilder(cmd);
        pb.redirectErrorStream(true);
        return pb.start();
    }

    /**
     * The checks after a kill: K1 on the files, then the start (K2). Returns the actions in
     * the database when the start found the stream at an action's end, else -1 after K4.
     */
    static int afterKill(File dir, int synced, int lastA, int mode, Random r) throws Exception {
        TreeMap<String, byte[]> files = readFiles(dir);
        // K1: a prefix of the ref's stream, but for zeros at the end of the last file.
        long end = 0;
        long zeros = 0;
        String lastName = files.isEmpty() ? null : files.lastKey();
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            long s0 = SameBytes.fileStart(e.getKey());
            byte[] b = e.getValue();
            int n = b.length;
            if (e.getKey().equals(lastName)) {
                while (n > 0 && b[n - 1] == 0) n--;      // the zeros at the end, of the last file
                zeros = b.length - n;
            }
            if (s0 + n > ref.stream.length) {
                throw new Common.Fail("K1: chain " + chains + ": file " + e.getKey() + " ends at " + (s0 + n)
                        + ", after the ref's stream (" + ref.stream.length + ")");
            }
            int mm = Arrays.mismatch(b, 0, n, ref.stream, (int) s0, (int) (s0 + n));
            if (mm >= 0) {
                // A zero byte inside may be a zero of the ref too: only a true difference fails.
                throw new Common.Fail("K1: chain " + chains + ": file " + e.getKey() + " differs from the ref's stream at "
                        + (s0 + mm) + " (" + actionAt(s0 + mm) + ")" + ", kill mode " + mode);
            }
            end = s0 + b.length;
        }
        if (zeros > 0) zeroTails++;
        long kept = end - zeros;
        // Every synced action's records are in the files (a record ends in the byte 10, not a zero).
        if (synced >= 0 && kept < ref.lens[synced]) {
            throw new Common.Fail("K1: chain " + chains + ": the files end at " + kept + " (" + zeros + " zeros after), before the"
                    + " end of synced action " + synced + " (" + ref.lens[synced] + ")");
        }
        // "The database appends nothing by itself": paused after an action and its sync, the
        // files end where that action's records end.
        if (mode == 0 && synced >= 0 && kept != ref.lens[synced]) {
            throw new Common.Fail("K1: chain " + chains + ": paused after action " + synced + " and its sync, the files end at "
                    + kept + " (" + zeros + " zeros after), the action's records at " + ref.lens[synced]);
        }
        // K2: the start.
        File before = new File(base, "torn");
        SameBytes.copyFiles(dir, before);
        if (files.isEmpty() || end == 0) {
            // Killed before the creation's first byte (no file, or an empty one): a start on an
            // empty stream creates the database (Db.start()); the next child does.
            notCreated++;
            for (File f : SameBytes.listStreamFiles(dir)) Files.delete(f.toPath());
            Common.rmrf(before);
            return 0;
        }
        Db db;
        try {
            db = startParent(dir);
        } catch (bergdb.pub.util.DatabaseNotCreatedException e) {
            // DbBuilder.start(): a crash inside the creating start; remove the files and start again.
            String d = diffFiles(files, readFiles(dir));
            if (d != null) throw new Common.Fail("K2: chain " + chains + ": the refused start (not created) changed the files: " + d);
            notCreated++;
            for (File f : SameBytes.listStreamFiles(dir)) Files.delete(f.toPath());
            Common.rmrf(before);
            return 0;
        }
        long len = db.getStreamLength();
        long fap = db.getFirstAvailablePos();
        db.close();
        TreeMap<String, byte[]> afterStart = readFiles(dir);
        String wrote = diffStart(files, afterStart, fap);
        // The actions whose records end at or before the kept end: the state must be theirs.
        int k = 0;
        while (k < ref.lens.length && ref.lens[k] <= kept) k++;
        if (kept < ref.createdLen) k = -1;
        Db db2 = startParent(dir);
        try {
            if (k >= 0) checkState(db2, k, "K2: chain " + chains + ": the start after a kill (files end " + end + ", zeros "
                    + zeros + ", " + actionAt(kept) + ", the start " + (wrote == null ? "wrote nothing" : "wrote") + ")");
        } finally {
            db2.close();
        }
        String d2 = diffFiles(afterStart, readFiles(dir));
        if (d2 != null) throw new Common.Fail("K2: chain " + chains + ": a second start changed the files: " + d2);
        if (k < 0) {
            throw new Common.Fail("K2: chain " + chains + ": the start took a stream that ends inside the creation (" + kept
                    + " of " + ref.createdLen + " bytes, " + zeros + " zeros after); Db.start(): DatabaseNotCreatedException");
        }
        if (k < synced + 1) {
            throw new Common.Fail("K2: chain " + chains + ": the start holds " + k + " actions, the child synced action " + synced);
        }
        if (mode == 2 && k > lastA + 2) {
            throw new Common.Fail("K2: chain " + chains + ": the start holds " + k + " actions, the child reported " + (lastA + 1));
        }
        if (wrote == null) {
            if (len != kept) throw new Common.Fail("K2: chain " + chains + ": the start wrote nothing, its stream length " + len
                    + ", the files' kept end " + kept);
            boolean atEnd = (k > 0 && ref.lens[k - 1] == kept) || (k == 0 && kept == ref.createdLen);
            boundaryStarts++;
            Common.rmrf(before);
            if (atEnd) return k;
            log("chain " + chains + ": the kill came between two records of " + actionAt(kept) + "; the start wrote nothing;"
                    + " the chain ends");
            return -1;
        }
        // The start wrote: the bytes before the cut are as they were.
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            byte[] now = afterStart.get(e.getKey());
            long s0 = SameBytes.fileStart(e.getKey());
            int n = (int) Math.max(0, Math.min(e.getValue().length, kept - s0));
            if (now == null && s0 + e.getValue().length <= fap) continue;
            if (now == null) throw new Common.Fail("K2: chain " + chains + ": the start removed " + e.getKey());
            if (now.length < n || Arrays.mismatch(now, 0, n, e.getValue(), 0, n) >= 0) {
                throw new Common.Fail("K2: chain " + chains + ": the start changed " + e.getKey() + " before the cut at " + kept);
            }
        }
        writingStarts++;
        log("chain " + chains + ": a kill inside " + actionAt(kept) + ": files end " + end + ", zeros " + zeros
                + "; the start wrote (" + wrote + "), the stream now " + len + "; K4");
        // K5: kills during the start that completes the torn end (a child that only starts and
        // closes, killed 0 to 200 ms after it begins the start); then a start here must take what
        // the killed completion wrote, and end with the bytes of a completion that no kill cut
        // (027-11, section 1.3: "Every later start takes what a start's completion wrote").
        {
            File plain = new File(base, "k5plain");
            SameBytes.copyFiles(before, plain);
            Db pd = startParent(plain);
            pd.close();
            TreeMap<String, byte[]> want = readFiles(plain);
            for (int t = 0; t < 3; t++) {
                File kd = new File(base, "k5");
                SameBytes.copyFiles(before, kd);
                int kills5 = 0;
                for (int u = 0; u < 1 + r.nextInt(3); u++) {
                    Process cp = spawnRecover(kd);
                    BufferedReader cin = new BufferedReader(new InputStreamReader(cp.getInputStream()));
                    String l;
                    while ((l = cin.readLine()) != null && !l.equals("U")) { }
                    Thread.sleep(r.nextInt(200));
                    cp.destroyForcibly();
                    cp.waitFor(60, TimeUnit.SECONDS);
                    kills5++;
                }
                k5Kills += kills5;
                Db kdb = startParent(kd);
                try {
                    checkState(kdb, k, "K5: chain " + chains + ": a start after " + kills5 + " kills during the completion");
                } finally {
                    kdb.close();
                }
                // The same bytes but in meta blocks: "but for a meta block that the kill cut, completed
                // as an invalid block" (027-11, section 1.3), the magic and the version, zeros after.
                String d5 = diffStreamsButMetaBlocks(readFiles(kd), want);
                if (d5 != null) throw new Common.Fail("K5: chain " + chains + ": after " + kills5 + " kills during the start that"
                        + " completes the torn end, the stream is not that of a completion with no kill: " + d5);
                k5Checks++;
                Common.rmrf(kd);
            }
            Common.rmrf(plain);
        }
        // K4: two copies, each started and given the next actions, end the same.
        int next = Math.min(nActs, k + 25 + r.nextInt(40));
        File c1 = new File(base, "k4a"), c2 = new File(base, "k4b");
        SameBytes.copyFiles(before, c1);
        SameBytes.copyFiles(before, c2);
        runActions(c1, k, next);
        runActions(c2, k, next);
        String d = diffStreams(readFiles(c1), readFiles(c2));
        if (d != null) throw new Common.Fail("K4: chain " + chains + ": two copies of the torn files, started and given actions "
                + k + " to " + (next - 1) + ", differ: " + d);
        k4Checks++;
        Common.rmrf(c1);
        Common.rmrf(c2);
        Common.rmrf(before);
        return -1;
    }

    static String actionAt(long pos) {
        int i = 0;
        while (i < ref.lens.length && ref.lens[i] <= pos) i++;
        return "action " + i + (i < SameBytes.acts.size() ? ", " + SameBytes.acts.get(i) : "") + ", records from "
                + (i == 0 ? 0 : ref.lens[i - 1]) + " to " + (i < ref.lens.length ? ref.lens[i] : -1);
    }

    static Db startParent(File dir) throws IOException {
        SameBytes.Run x = new SameBytes.Run();
        x.name = "parent";
        x.r = new Random(1);
        x.dir = dir;
        SameBytes.start(x);
        return x.db;
    }

    /** Actions from..to-1 on the database in dir, in this process, with the ref's clock. */
    static void runActions(File dir, int from, int to) throws IOException {
        SameBytes.Run x = new SameBytes.Run();
        x.name = "k4";
        x.r = new Random(2);
        x.dir = dir;
        SameBytes.start(x);
        for (int i = from; i < to; i++) {
            SameBytes.Act act = SameBytes.acts.get(i);
            x.clock.t.set(act.time);
            SameBytes.apply(x, act);
        }
        x.db.close();
    }

    static void checkState(Db db, int actions, String what) {
        TreeMap<Common.K, byte[]> exp = new TreeMap<>();
        for (int i = 0; i < actions; i++) {
            SameBytes.Act act = SameBytes.acts.get(i);
            if (act.kind != 'T') continue;
            for (int k = 0; k < act.keys.size(); k++) {
                Common.K key = new Common.K(act.keys.get(k));
                if (act.vals.get(k) == null) exp.remove(key); else exp.put(key, act.vals.get(k));
            }
        }
        List<Kvt> got = Common.scanAll(db, Long.MAX_VALUE, null);
        Iterator<Map.Entry<Common.K, byte[]>> it = exp.entrySet().iterator();
        int i = 0;
        for (Kvt kv : got) {
            Common.K k = new Common.K(Keys.toBytes(kv.key));
            if (!it.hasNext()) throw new Common.Fail(what + ": an extra key " + k + " (expected " + exp.size() + " keys after "
                    + actions + " actions)");
            Map.Entry<Common.K, byte[]> e = it.next();
            if (!e.getKey().equals(k) || !Arrays.equals(e.getValue(), kv.value)) {
                throw new Common.Fail(what + ": key " + i + " is " + k + " = " + Common.hex(kv.value) + ", expected "
                        + e.getKey() + " = " + Common.hex(e.getValue()) + " (after " + actions + " actions)");
            }
            i++;
        }
        if (it.hasNext()) throw new Common.Fail(what + ": a missing key " + it.next().getKey() + " (got " + got.size()
                + ", expected " + exp.size() + " after " + actions + " actions)");
    }

    static void compareWithRef(File dir, String what) throws IOException {
        TreeMap<String, byte[]> files = readFiles(dir);
        long end = 0;
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            long s0 = SameBytes.fileStart(e.getKey());
            byte[] b = e.getValue();
            if (s0 + b.length > ref.stream.length || Arrays.mismatch(b, 0, b.length, ref.stream, (int) s0, (int) (s0 + b.length)) >= 0) {
                int mm = s0 + b.length > ref.stream.length ? -1 : Arrays.mismatch(b, 0, b.length, ref.stream, (int) s0, (int) (s0 + b.length));
                throw new Common.Fail("K3: " + what + ": file " + e.getKey() + " is not the ref's stream there"
                        + (mm >= 0 ? ": it differs at " + (s0 + mm) + " (" + actionAt(s0 + mm) + ")" : ": it ends after the ref's"));
            }
            end = s0 + b.length;
        }
        if (end != ref.length) throw new Common.Fail("K3: " + what + ": the stream ends at " + end + ", the ref's at " + ref.length);
        if (diffFiles(files, ref.files) != null) {
            layoutNotes++;
            System.out.println("NOTE " + what + ": the ref's stream, other files: " + SameBytes.summary(files) + "; the ref's "
                    + SameBytes.summary(ref.files));
        }
    }

    /** The start's changes: none, but for files wholly before the first available position, deleted (its cut). */
    static String diffStart(TreeMap<String, byte[]> before, TreeMap<String, byte[]> after, long fap) {
        for (String f : after.keySet()) {
            if (!before.containsKey(f)) return "the start made " + f;
            int mm = Arrays.mismatch(after.get(f), before.get(f));
            if (mm >= 0) return "file " + f + " (" + before.get(f).length + " bytes before, " + after.get(f).length
                    + " after) changed at " + (SameBytes.fileStart(f) + mm);
        }
        for (String f : before.keySet()) {
            if (!after.containsKey(f)) {
                if (SameBytes.fileStart(f) + before.get(f).length > fap) return "the start deleted " + f + ", not before the first"
                        + " available position " + fap;
                deadDeleted++;
            }
        }
        return null;
    }

    /**
     * As diffStreams(), but a difference inside a meta block (the 128 bytes at each multiple of
     * 200,000) is taken where a's block is an invalid one: the 5 bytes of the magic and the
     * version as b's, zeros after (027-11, section 1.3).
     */
    static String diffStreamsButMetaBlocks(TreeMap<String, byte[]> a, TreeMap<String, byte[]> b) {
        long ea = 0, eb = 0;
        for (Map.Entry<String, byte[]> e : a.entrySet()) ea = SameBytes.fileStart(e.getKey()) + e.getValue().length;
        for (Map.Entry<String, byte[]> e : b.entrySet()) eb = SameBytes.fileStart(e.getKey()) + e.getValue().length;
        if (ea != eb) return "the streams end at " + ea + " and " + eb;
        for (Map.Entry<String, byte[]> e : a.entrySet()) {
            long s0 = SameBytes.fileStart(e.getKey());
            byte[] x = e.getValue();
            byte[] y = b.get(e.getKey());
            if (y == null) continue;
            int n = Math.min(x.length, y.length);
            for (int i = 0; i < n; i++) {
                if (x[i] == y[i]) continue;
                long pos = s0 + i;
                long block = pos - pos % 200_000;
                if (pos - block >= 128) return "the streams differ at " + pos + ", outside a meta block";
                int bi = (int) (block - s0);
                for (int j = 0; j < 128 && bi + j < x.length; j++) {
                    if (j < 5 ? x[bi + j] != y[bi + j] : x[bi + j] != 0) {
                        return "the meta block at " + block + " differs and is not an invalid block";
                    }
                }
                invalidBlocks++;
                i = bi + 127;
            }
        }
        return null;
    }

    static long invalidBlocks;

    /** Two directories' streams: the same length and the same bytes where both have files. */
    static String diffStreams(TreeMap<String, byte[]> a, TreeMap<String, byte[]> b) {
        long ea = 0, eb = 0;
        for (Map.Entry<String, byte[]> e : a.entrySet()) ea = SameBytes.fileStart(e.getKey()) + e.getValue().length;
        for (Map.Entry<String, byte[]> e : b.entrySet()) eb = SameBytes.fileStart(e.getKey()) + e.getValue().length;
        if (ea != eb) return "the streams end at " + ea + " and " + eb;
        for (Map.Entry<String, byte[]> e : a.entrySet()) {
            long s0 = SameBytes.fileStart(e.getKey());
            for (Map.Entry<String, byte[]> f : b.entrySet()) {
                long s1 = SameBytes.fileStart(f.getKey());
                long lo = Math.max(s0, s1), hi = Math.min(s0 + e.getValue().length, s1 + f.getValue().length);
                if (lo >= hi) continue;
                int mm = Arrays.mismatch(e.getValue(), (int) (lo - s0), (int) (hi - s0), f.getValue(), (int) (lo - s1), (int) (hi - s1));
                if (mm >= 0) return "the streams differ at " + (lo + mm);
            }
        }
        return null;
    }

    static TreeMap<String, byte[]> readFiles(File dir) throws IOException {
        TreeMap<String, byte[]> m = new TreeMap<>();
        for (File f : SameBytes.listStreamFiles(dir)) m.put(f.getName(), Files.readAllBytes(f.toPath()));
        return m;
    }

    static String diffFiles(TreeMap<String, byte[]> a, TreeMap<String, byte[]> b) {
        if (!a.keySet().equals(b.keySet())) return "files " + SameBytes.summary(a) + " against " + SameBytes.summary(b);
        for (String f : a.keySet()) {
            int mm = Arrays.mismatch(a.get(f), b.get(f));
            if (mm >= 0) return "file " + f + " (" + a.get(f).length + " and " + b.get(f).length + " bytes) differs at "
                    + (SameBytes.fileStart(f) + mm);
        }
        return null;
    }

    // ------------------------------------------------------------------ the child

    static void child(String[] a) throws Exception {
        long s = Long.parseLong(a[1]);
        int n = Integer.parseInt(a[2]);
        File dir = new File(a[3]);
        int pause = Integer.parseInt(a[4]);
        boolean syncPause = Boolean.parseBoolean(a[5]);
        int keys = Integer.parseInt(a[6]);
        setUp(s, n, keys, dir.getParentFile());
        // The child finds its place by the stream length, in the ref's lengths that the parent wrote.
        SameBytes.Run x = new SameBytes.Run();
        x.name = "child";
        x.r = new Random(s);
        x.dir = dir;
        boolean fresh = SameBytes.listStreamFiles(dir).isEmpty();
        x.clock.t.set(SameBytes.T0);
        SameBytes.start(x);
        if (fresh) x.db.sync(SyncLevel.ORDINARY);
        long len = x.db.getStreamLength();
        int from = findPlace(len, n);
        if (from < 0) {
            System.out.println("OFF " + len);
            System.exit(3);
        }
        System.out.println("R " + from);
        java.io.FileOutputStream progress = new java.io.FileOutputStream(dir.getPath() + ".progress", false);
        Random r = new Random(s * 7 + from);
        for (int i = from; i < n; i++) {
            SameBytes.Act act = SameBytes.acts.get(i);
            x.clock.t.set(act.time);
            SameBytes.apply(x, act);
            progress.write(("A " + i + "\n").getBytes());
            System.out.println("A " + i);
            if (i == pause) {
                if (syncPause) {
                    x.db.sync(SyncLevel.ORDINARY);
                    progress.write(("S " + i + "\n").getBytes());
                }
                System.out.println("P " + i);
                System.out.flush();
                Thread.sleep(600_000);
            }
            if (r.nextInt(6) == 0) {
                x.db.sync(SyncLevel.ORDINARY);
                progress.write(("S " + i + "\n").getBytes());
                System.out.println("S " + i);
            }
        }
        x.db.close();
        System.out.println("END");
        System.out.flush();
    }

    /** The child's place: the actions whose end, in the ref, is the stream length; -1 if none. */
    static int findPlace(long len, int n) throws IOException {
        File f = new File(SameBytes.base, "lens-" + SameBytes.seed);
        List<String> ls = Files.readAllLines(f.toPath());
        long created = Long.parseLong(Files.readAllLines(new File(SameBytes.base, "lens-" + SameBytes.seed + ".created")
                .toPath()).get(0).trim());
        if (len == created) return 0;
        for (int i = 0; i < ls.size(); i++) if (Long.parseLong(ls.get(i).trim()) == len) return i + 1;
        return -1;
    }

    static void log(String s) {
        Common.log(s);
    }
}
