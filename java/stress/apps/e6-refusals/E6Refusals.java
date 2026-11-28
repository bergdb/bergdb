import bergdb.pub.*;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;

import java.io.File;
import java.util.*;
import java.util.concurrent.atomic.*;

/**
 * App e6 of 031-08: the refusals that the Javadoc promises around maintain(budget), the
 * settings and reclaim, and the database's state after each (Pub API, file databases).
 *
 * Scenarios, each on a database of its own with data that the oracle knows, and each ending
 * with a restart and a check of every key:
 *  1. maintain() after stop() and after close(): IllegalDbStateException, nothing changed;
 *     setRetainDuration() and setStartupDistanceInMb() the same.
 *  2. A stop() from another thread while a thread runs maintain(100,000) calls on a
 *     database with much to rewrite (a mass delete under a retain duration of 1 s): each call
 *     returns, or throws IllegalDbStateException (Database.maintain(): "If the database is
 *     stopping or stopped"); the database does not fail; every transaction is there after
 *     the restart. The kinds of exception seen are counted and printed.
 *  3. maintain() with the thread's interrupt flag set: it returns, or throws a DbException
 *     ("if the thread is interrupted during a sync"); the flag is still set after; the
 *     database goes on.
 *  4. setRetainDuration() of null, 0 s and 0.999 s: IllegalArgumentException, the value
 *     unchanged and nothing written.
 *  5. An Error thrown in an rw() action fails the database (Database, "Errors"); then
 *     maintain(), setRetainDuration() and a put throw DbFailedException, close() returns,
 *     and the restart has every transaction that a sync() returned for.
 *  6. The end of the clock: a test clock near 2^56 - 1 (Clock.getTime()); transactions and
 *     maintain() calls until they are refused with a DbException; then reads, sync(),
 *     close() and a restart work, with every committed transaction; a refused call wrote
 *     nothing.
 *
 * Usage: java E6Refusals SEED DIR [ROUNDS]
 */
public class E6Refusals {
    static final long SEC = 10_000_000L;
    final long seed;
    final Random rnd;
    final File base;
    final Map<String, Integer> kinds = new TreeMap<>();
    long checks;

    E6Refusals(long seed, File base) { this.seed = seed; rnd = new Random(seed); this.base = base; }

    void count(String k) { kinds.merge(k, 1, Integer::sum); }

    /** Puts n keys of random values; returns the oracle. */
    TreeMap<String, byte[]> load(Connection c, String dir, int n, TreeMap<String, byte[]> m) {
        for (int done = 0; done < n; ) {
            WBuilder w = c.w();
            for (int j = 0; j < 300 && done < n; j++, done++) {
                String k = dir + "k" + rnd.nextInt(n * 2) + ".bin";
                byte[] v = EOracle.value(rnd, rnd.nextInt(800));
                w.put(k, v);
                m.put(k, v);
            }
            w.execute();
        }
        return m;
    }

    void verify(Database db, TreeMap<String, byte[]> m, String dir, String what) {
        Connection c = db.newConnection();
        Iterator<Map.Entry<String, byte[]>> it = m.entrySet().iterator();
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir(dir).kvs()) {
            EOracle.check(it.hasNext(), what + ": an extra key " + kv.key());
            Map.Entry<String, byte[]> e = it.next();
            EOracle.check(e.getKey().equals(kv.key()) && Arrays.equals(e.getValue(), kv.value()), what + ": " + kv.key() + ", expected " + e.getKey());
        }
        EOracle.check(!it.hasNext(), what + ": a missing key " + (it.hasNext() ? it.next().getKey() : ""));
        checks++;
    }

    static void expectState(Runnable r, String what) {
        try { r.run(); throw new EOracle.Fail(what + " was taken after stop()"); }
        catch (DbFailedException bad) { throw new EOracle.Fail(what + " after stop() threw DbFailedException: " + bad); }
        catch (IllegalDbStateException good) { }
    }

    void s1(File dir) {
        TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
        Database db = Factory.database().create(dir.getPath()).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        load(db.connection(), "/e6/", 2000, m);
        boolean closeFirst = rnd.nextBoolean();
        if (closeFirst) db.close(); else db.stop();
        expectState(() -> db.maintain(100), "maintain(100)");
        expectState(() -> db.maintain(100_000), "maintain(100000)");
        expectState(() -> db.setRetainDuration(Duration.seconds(5)), "setRetainDuration()");
        expectState(() -> db.setStartupDistanceInMb(7), "setStartupDistanceInMb()");
        db.close();
        expectState(() -> db.maintain(0), "maintain(0) after close()");
        Database db2 = Factory.database().open(dir.getPath()).start();
        EOracle.check(db2.getRetainDuration().equals(Duration.seconds(1)), "s1: the retain duration changed by a refused call");
        EOracle.check(db2.getStartupDistanceInMb() == 5, "s1: the startup distance changed by a refused call");
        verify(db2, m, "/e6/", "s1");
        db2.close();
    }

    void s2(File dir) throws Exception {
        TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-05-01"));
        Database db = Factory.database().create(dir.getPath()).clock(clock).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        Connection c = db.connection();
        load(c, "/e6/", 20_000 + rnd.nextInt(20_000), m);
        // a mass delete of most keys
        List<String> ks = new ArrayList<>(m.keySet());
        Collections.shuffle(ks, rnd);
        for (int i = 0; i < ks.size() * 9 / 10; ) {
            WBuilder w = c.w();
            for (int j = 0; j < 400 && i < ks.size() * 9 / 10; j++, i++) { w.delete(ks.get(i)); m.remove(ks.get(i)); }
            w.execute();
        }
        long last = c.currentTime().units();
        AtomicReference<String> fail = new AtomicReference<>();
        AtomicInteger calls = new AtomicInteger();
        AtomicBoolean running = new AtomicBoolean(true);
        Thread t = new Thread(() -> {
            try {
                while (true) {
                    clock.setTime(Time.units(clock.getTime() + SEC / 3));
                    db.maintain(100_000);
                    calls.incrementAndGet();
                }
            } catch (DbFailedException e) {    // a subclass of IllegalDbStateException
                fail.set("s2: maintain() at a stop failed the database: " + e);
            } catch (IllegalDbStateException e) {
                count("s2 maintain at a stop: " + e.getClass().getSimpleName());
            } catch (DbException e) {
                count("s2 maintain at a stop: " + e.getClass().getSimpleName() + " (" + e.getMessage() + ")");
            } catch (Throwable e) {
                fail.set("s2: maintain() at a stop threw " + e);
            } finally {
                running.set(false);
            }
        });
        t.start();
        Thread.sleep(rnd.nextInt(80));
        if (rnd.nextBoolean()) db.stop(); else db.close();
        t.join(120_000);
        EOracle.check(!t.isAlive(), "s2: maintain() did not return in 120 s after the stop");
        if (fail.get() != null) throw new EOracle.Fail(fail.get());
        db.close();
        Database db2 = Factory.database().open(dir.getPath()).clock(clock).start();
        verify(db2, m, "/e6/", "s2 after " + calls.get() + " calls");
        EOracle.check(db2.currentTime().units() >= last, "s2: the restart lost transactions");
        db2.close();
    }

    void s3(File dir) {
        TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-05-01"));
        Database db = Factory.database().create(dir.getPath()).clock(clock).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        Connection c = db.connection();
        load(c, "/e6/", 5000, m);
        List<String> ks = new ArrayList<>(m.keySet());
        for (int i = 0; i < ks.size() / 2; i++) { c.delete(ks.get(i)); m.remove(ks.get(i)); }
        for (int i = 0; i < 40; i++) {
            clock.setTime(Time.units(clock.getTime() + SEC / 2));
            Thread.currentThread().interrupt();
            try {
                db.maintain(new int[] {100, 5000, 100_000}[rnd.nextInt(3)]);
                count("s3 maintain interrupted: returned");
            } catch (DbFailedException e) {
                throw new EOracle.Fail("s3: an interrupt failed the database: " + e);
            } catch (DbException e) {
                count("s3 maintain interrupted: " + e.getClass().getSimpleName());
            }
            EOracle.check(Thread.interrupted(), "s3: the interrupt flag was not set after maintain() (Database, \"Interrupts\")");
            if (rnd.nextInt(4) == 0) { String k = "/e6/x" + i + ".bin"; c.put(k, new byte[] {(byte) i}); m.put(k, new byte[] {(byte) i}); }
        }
        verify(db, m, "/e6/", "s3");
        db.close();
        Database db2 = Factory.database().open(dir.getPath()).clock(clock).start();
        verify(db2, m, "/e6/", "s3 restarted");
        db2.close();
    }

    void s4(File dir) {
        Database db = Factory.database().create(dir.getPath()).start();
        db.setRetainDuration(Duration.seconds(30));
        long ss = db.getStreamSize();
        for (Duration d : new Duration[] {null, Duration.seconds(0), Duration.seconds(0.999), Duration.units(SEC - 1)}) {
            try {
                db.setRetainDuration(d);
                throw new EOracle.Fail("s4: setRetainDuration(" + d + ") was taken");
            } catch (IllegalArgumentException good) { }
            EOracle.check(db.getRetainDuration().equals(Duration.seconds(30)), "s4: a refused setRetainDuration() changed the value");
            EOracle.check(db.getStreamSize() == ss, "s4: a refused setRetainDuration() wrote");
        }
        db.setRetainDuration(Duration.units(SEC));
        EOracle.check(db.getRetainDuration().equals(Duration.units(SEC)), "s4: one second exactly was not taken");
        long ss2 = db.getStreamSize();
        db.setRetainDuration(Duration.units(SEC));
        EOracle.check(db.getStreamSize() == ss2, "s4: a call with the value in force wrote (\"A call with the value in force writes nothing\")");
        db.close();
        checks++;
    }

    public static class Bomb { public long x; public Bomb() {} }

    void s5(File dir) {
        TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
        Database db = Factory.database().create(dir.getPath()).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        Connection c = db.connection();
        load(c, "/e6/", 3000, m);
        db.sync();
        TreeMap<String, byte[]> synced = new TreeMap<>(m);
        try {
            c.rw(env -> { env.put("/e6/bomb.bin", new byte[1]); throw new StackOverflowError("e6's test error"); });
            throw new EOracle.Fail("s5: the rw() with an Error returned");
        } catch (StackOverflowError expected) { }
        for (Runnable r : new Runnable[] {() -> db.maintain(100), () -> db.setRetainDuration(Duration.seconds(9)), () -> c.put("/e6/y.bin", new byte[1])}) {
            try { r.run(); throw new EOracle.Fail("s5: a call after the failure was taken"); }
            catch (DbFailedException good) { }
        }
        db.close();
        Database db2 = Factory.database().open(dir.getPath()).start();
        verify(db2, synced, "/e6/", "s5 restarted");
        EOracle.check(db2.getRetainDuration().equals(Duration.seconds(1)), "s5: the retain duration");
        db2.close();
    }

    void s6(File dir) {
        TreeMap<String, byte[]> m = new TreeMap<>(EOracle.ORDER);
        TestClock clock = new TestClock();
        long max = (1L << 56) - 1;
        int margin = 20 + rnd.nextInt(200);
        clock.setTime(Time.units(max - margin));
        Database db = Factory.database().create(dir.getPath()).clock(clock).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(1));
        Connection c = db.connection();
        int taken = 0, refusedTx = 0, refusedM = 0, maintained = 0;
        for (int i = 0; i < 3 * margin + 100 && refusedTx < 8; i++) {
            long ss = db.getStreamSize();
            if (rnd.nextInt(3) == 0) {
                try {
                    db.maintain(new int[] {100, 100_000}[rnd.nextInt(2)]);
                    maintained++;
                } catch (DbFailedException e) {
                    throw new EOracle.Fail("s6: maintain() at the end of the clock failed the database: " + e);
                } catch (DbException e) {
                    refusedM++;
                    EOracle.check(db.getStreamSize() == ss, "s6: a refused maintain() wrote " + (db.getStreamSize() - ss) + " bytes");
                    count("s6 maintain refused: " + e.getClass().getSimpleName());
                }
            } else {
                String k = "/e6/t" + rnd.nextInt(50) + ".bin";
                byte[] v = EOracle.value(rnd, rnd.nextInt(200));
                try {
                    Transaction t = c.put(k, v);
                    EOracle.check(t.getTime().units() <= max, "s6: a transaction time after 2^56 - 1: " + t.getTime().units());
                    m.put(k, v);
                    taken++;
                } catch (DbFailedException e) {
                    throw new EOracle.Fail("s6: a put at the end of the clock failed the database: " + e);
                } catch (DbException e) {
                    refusedTx++;
                    EOracle.check(db.getStreamSize() == ss, "s6: a refused put wrote");
                }
            }
        }
        EOracle.check(refusedTx > 0, "s6: no put was refused after " + taken + " at the end of the clock");
        verify(db, m, "/e6/", "s6");
        db.sync();
        db.close();
        Database db2 = Factory.database().open(dir.getPath()).clock(clock).start();
        verify(db2, m, "/e6/", "s6 restarted");
        db2.close();
        count("s6 taken " + (taken > 0 ? "some" : "none") + ", maintain returned " + (maintained > 0 ? "some" : "none"));
        EOracle.log("  s6: margin " + margin + ": " + taken + " puts taken, " + refusedTx + " refused, maintain " + maintained + " returned, "
                + refusedM + " refused");
    }

    void run(int rounds) throws Exception {
        EOracle.log("E6Refusals seed " + seed + ", rounds " + rounds);
        for (int r = 0; r < rounds; r++) {
            int s = r % 6 + 1;
            File dir = new File(base, "s" + s + "-" + r);
            EOracle.rmrf(dir);
            switch (s) {
                case 1: s1(dir); break;
                case 2: s2(dir); break;
                case 3: s3(dir); break;
                case 4: s4(dir); break;
                case 5: s5(dir); break;
                default: s6(dir);
            }
            EOracle.rmrf(dir);
        }
        EOracle.log("  outcomes: " + kinds);
        EOracle.log("OK E6Refusals seed " + seed + ": " + rounds + " scenarios, " + checks + " checks");
    }

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        File dir = new File(a[1]);
        int rounds = a.length > 2 ? Integer.parseInt(a[2]) : 24;
        E6Refusals app = new E6Refusals(seed, dir);
        try {
            app.run(rounds);
        } catch (Throwable t) {
            System.out.println("FAIL E6Refusals seed " + seed + ": " + t);
            t.printStackTrace(System.out);
            System.exit(1);
        }
        System.exit(0);
    }
}
