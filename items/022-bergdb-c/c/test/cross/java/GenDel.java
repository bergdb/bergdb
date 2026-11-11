package bergdb.cross;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

/**
 * Cross workloads for the delete path of release 2026.4 (bergdb 022-07; 023-07, section 5:
 * the upward unlink, the empty key first, root collapse, the take-back), from a seed: rounds
 * of a fill, a delete pattern, mixed transactions and a drive of single puts, on keys of
 * one shape, so that deletes empty leaves, inner nodes, whole segment trees and the whole
 * database, from the left (the child of the empty key), from the right, from both ends, in
 * key order, shuffled, every k-th, in ranges, and all but the first and the last key (a
 * chain of single children, which the delete of the first collapses over several levels);
 * in transactions of one operation and of up to a thousand; with restarts, checks at the
 * latest and at earlier times, and reclaim (a retain duration, with enough transactions
 * after the deletes for its iterations and cuts to pass over what the deletes left). A
 * transaction has one operation a key. Each parameter not given is drawn from the seed.
 * The workload is the interface: C never runs this class.
 *
 * <pre>
 * Usage: java -cp CLASSES bergdb.cross.GenDel SEED [NAME=VALUE...]
 *   keys     distinct keys                    shape    the keys' form, 0 to 4 (below)
 *   maxnode  8, 14, 30 or 62                  sd       startup distance in bytes
 *   retain   seconds, 0 for forever           rounds   rounds of fill, delete, mix, drive
 *   tx       operations a transaction at most pattern  the delete pattern, 0 to 8; -1: drawn
 *   mix      mixed transactions a round       drive    single puts after a round
 *   restarts percent of phases followed by a restart
 *   valmax   the largest value                empty    1: every key deleted at the end
 * Shapes: 0 one segment (one tree at the space root); 1 two segments, trees of up to 100
 * keys; 2 a few trees of many keys; 3 long keys of several segments, half of them with a
 * tail; 4 keys in a scattered order.
 * Patterns: 0 every key ascending; 1 descending; 2 shuffled; 3 every k-th; 4 a range;
 * 5 all but the first and the last, then the first, then the last; 6 from both ends
 * inward; 7 a random share; 8 every key but each k-th (thinned out), then the rest.
 * Prints the workload ("bergdb-workload 1") on standard output.
 * </pre>
 */
public final class GenDel {
    static final long UNITS_PER_SEC = 10 * 1000 * 1000L;

    public static void main(String[] args) {
        PrintStream out = System.out;
        Map<String, String> p = new TreeMap<String, String>();
        for (int i = 1; i < args.length; i++) {
            int eq = args[i].indexOf('=');
            p.put(args[i].substring(0, eq), args[i].substring(eq + 1));
        }
        generate(Long.parseLong(args[0]), p, out);
        out.flush();
    }

    private static long get(Map<String, String> p, String name, long drawn) {
        String v = p.get(name);
        return v == null ? drawn : Long.parseLong(v);
    }

    private final Random rnd;
    private final PrintStream out;
    private final String[] keys;
    private final boolean[] live;
    private final int tx;
    private final int valmax;
    private final long step;
    private final int restarts;
    private long time;
    private final List<Long> times = new ArrayList<Long>();

    private GenDel(Random rnd, PrintStream out, String[] keys, int tx, int valmax, long step,
            int restarts, long time) {
        this.rnd = rnd;
        this.out = out;
        this.keys = keys;
        this.live = new boolean[keys.length];
        this.tx = tx;
        this.valmax = valmax;
        this.step = step;
        this.restarts = restarts;
        this.time = time;
    }

    public static void generate(long seed, Map<String, String> params, PrintStream out) {
        Random rnd = new Random(seed * 0x9E3779B97F4A7C15L + 777);
        final int keyCount = (int) get(params, "keys", 100 + rnd.nextInt(2400));
        final int shape = (int) get(params, "shape", rnd.nextInt(5));
        final int maxNode = (int) get(params, "maxnode", new int[] {8, 8, 14, 30, 62}[rnd.nextInt(5)]);
        final int sd = (int) get(params, "sd", (long) Math.pow(10, 2 + 4 * rnd.nextDouble()));
        final long retainSec = get(params, "retain", rnd.nextInt(10) < 5 ? 0 : 1 + rnd.nextInt(3));
        final int rounds = (int) get(params, "rounds", 1 + rnd.nextInt(4));
        final int tx = (int) get(params, "tx", new int[] {1, 3, 10, 50, 200, 1000}[rnd.nextInt(6)]);
        final int pattern = (int) get(params, "pattern", -1);
        final int mix = (int) get(params, "mix", rnd.nextInt(60));
        final int drive = (int) get(params, "drive",
                retainSec > 0 ? 60 + rnd.nextInt(300) : rnd.nextInt(20));
        final int restarts = (int) get(params, "restarts", rnd.nextInt(40));
        final int valmax = (int) get(params, "valmax", 1 + rnd.nextInt(120));
        final int empty = (int) get(params, "empty", rnd.nextInt(2));

        out.println("bergdb-workload 1");
        out.println("# GenDel seed=" + seed + " keys=" + keyCount + " shape=" + shape
                + " maxnode=" + maxNode + " sd=" + sd + " retain=" + retainSec + " rounds="
                + rounds + " tx=" + tx + " pattern=" + pattern + " mix=" + mix + " drive="
                + drive + " restarts=" + restarts + " valmax=" + valmax + " empty=" + empty
                + " (bergdb 022-07)");
        out.println("set maxnode " + maxNode);
        out.println("set sd " + sd);
        if (retainSec > 0) {
            out.println("set retain " + retainSec * UNITS_PER_SEC);
            if (rnd.nextInt(3) == 0) {
                out.println("set fraction 0." + (10 + rnd.nextInt(40)));
            }
        }
        if (rnd.nextInt(4) == 0) {
            out.println("set budget " + (10000 + rnd.nextInt(1000000)));
        }
        String[] keys = new String[keyCount];
        for (int i = 0; i < keyCount; i++) {
            keys[i] = key(shape, i, keyCount);
        }
        long time = 1 + rnd.nextInt(1000000);
        out.println("clock " + time);
        GenDel g = new GenDel(rnd, out, keys, tx, valmax,
                retainSec > 0 ? UNITS_PER_SEC / 100 : 1, restarts, time);
        for (int r = 0; r < rounds; r++) {
            g.fill();
            g.between();
            g.delete(pattern < 0 ? rnd.nextInt(9) : pattern);
            g.between();
            g.mix(mix);
            g.between();
            g.drive(drive, r);
            g.between();
        }
        if (empty == 1) {
            g.delete(rnd.nextInt(3));       // every key: the database emptied
            g.drive(drive, rounds);
            out.println("check latest");
            out.println("sync");
            out.println("restart");
            g.drive(3, rounds + 1);
        }
        out.println("check latest");
        out.println("sync");
    }

    static String key(int shape, int i, int n) {
        switch (shape) {
        case 0: return "/" + String.format("%05d", i);
        case 1: return "/k/" + String.format("%06d", i);
        case 2: return "/pref" + String.format("%02d", i * 5 / Math.max(n, 1)) + "/x"
                + String.format("%05d", i);
        case 3: return "/longprefix/abcdefgh/" + String.format("%05d", i)
                + (i % 2 == 0 ? "/tail/more" : "");
        default: return "/h/" + Integer.toHexString((int) ((i * 2654435761L) & 0x7fffffff));
        }
    }

    /** The operations, in transactions of 1 to tx: each int is a key's index, put if >= 0,
     *  else a delete of key -(x + 1). */
    private void emit(List<Integer> ops) {
        int i = 0;
        StringBuilder line = new StringBuilder();
        while (i < ops.size()) {
            int n = tx == 1 ? 1 : 1 + rnd.nextInt(tx);
            if (rnd.nextInt(4) == 0) {
                n = tx;
            }
            time += (1 + rnd.nextInt(20)) * step;
            times.add(time);
            line.setLength(0);
            line.append("t ").append(time);
            for (int k = 0; k < n && i < ops.size(); k++, i++) {
                int x = ops.get(i);
                if (x >= 0) {
                    line.append(" p ").append(keys[x]).append(' ')
                            .append(Gen.value(rnd, valmax, 0));
                    live[x] = true;
                } else {
                    line.append(" d ").append(keys[-(x + 1)]);
                    live[-(x + 1)] = false;
                }
            }
            out.println(line);
        }
    }

    /** Puts every key that is not live, or a share of them, ascending or shuffled. */
    private void fill() {
        List<Integer> ops = new ArrayList<Integer>();
        int share = rnd.nextInt(3) == 0 ? 30 + rnd.nextInt(70) : 100;
        for (int i = 0; i < keys.length; i++) {
            if (!live[i] && rnd.nextInt(100) < share) {
                ops.add(i);
            }
        }
        if (rnd.nextInt(3) == 0) {
            Collections.shuffle(ops, rnd);
        }
        emit(ops);
    }

    private List<Integer> liveKeys() {
        List<Integer> l = new ArrayList<Integer>();
        for (int i = 0; i < keys.length; i++) {
            if (live[i]) {
                l.add(i);
            }
        }
        return l;
    }

    private static List<Integer> deletes(List<Integer> l) {
        List<Integer> ops = new ArrayList<Integer>();
        for (int x : l) {
            ops.add(-(x + 1));
        }
        return ops;
    }

    private void delete(int pattern) {
        List<Integer> l = liveKeys();
        if (l.isEmpty()) {
            return;
        }
        out.println("# delete pattern " + pattern + ", " + l.size() + " live keys");
        List<Integer> d = new ArrayList<Integer>();
        switch (pattern) {
        case 0:
            d.addAll(l);
            break;
        case 1:
            d.addAll(l);
            Collections.reverse(d);
            break;
        case 2:
            d.addAll(l);
            Collections.shuffle(d, rnd);
            break;
        case 3: {
            int k = 2 + rnd.nextInt(8);
            for (int i = 0; i < l.size(); i += k) {
                d.add(l.get(i));
            }
            break;
        }
        case 4: {
            int lo = rnd.nextInt(l.size()), hi = lo + rnd.nextInt(l.size() - lo + 1);
            d.addAll(l.subList(lo, hi));
            if (rnd.nextBoolean()) {
                Collections.reverse(d);
            }
            break;
        }
        case 5:
            if (l.size() > 2) {
                emit(deletes(l.subList(1, l.size() - 1)));
                check();
            }
            emit(deletes(l.subList(0, 1)));
            check();
            d.add(l.get(l.size() - 1));
            break;
        case 6:
            for (int a = 0, b = l.size() - 1; a <= b; a++, b--) {
                d.add(l.get(a));
                if (b != a) {
                    d.add(l.get(b));
                }
            }
            break;
        case 7: {
            int share = rnd.nextInt(101);
            for (int x : l) {
                if (rnd.nextInt(100) < share) {
                    d.add(x);
                }
            }
            break;
        }
        default: {
            int k = 2 + rnd.nextInt(30);
            List<Integer> rest = new ArrayList<Integer>();
            for (int i = 0; i < l.size(); i++) {
                (i % k == 0 ? rest : d).add(l.get(i));
            }
            emit(deletes(d));
            check();
            d = rest;
            if (rnd.nextBoolean()) {
                Collections.reverse(d);
            }
            break;
        }
        }
        emit(deletes(d));
    }

    /** Transactions of puts (new keys and live ones) and deletes of live keys, one
     *  operation a key; about a third of them a swap: a range of the keys, of up to twice
     *  tx, whose dead keys are put and whose live keys are deleted, so that one
     *  transaction splits nodes and empties what it split (the take-back). */
    private void mix(int count) {
        for (int m = 0; m < count; m++) {
            int n = 1 + rnd.nextInt(Math.min(tx, 40));
            List<Integer> ops = new ArrayList<Integer>();
            if (rnd.nextInt(3) == 0) {
                int span = 1 + rnd.nextInt(Math.max(1, Math.min(2 * tx, keys.length)));
                int lo = rnd.nextInt(keys.length - span + 1);
                for (int x = lo; x < lo + span; x++) {
                    ops.add(live[x] ? -(x + 1) : x);
                }
                emitOne(ops);
                continue;
            }
            boolean[] used = new boolean[keys.length];
            for (int k = 0; k < n; k++) {
                int x = rnd.nextInt(keys.length);
                if (used[x]) {
                    continue;
                }
                used[x] = true;
                ops.add(live[x] && rnd.nextInt(100) < 60 ? -(x + 1) : x);
            }
            Collections.sort(ops, new java.util.Comparator<Integer>() {
                public int compare(Integer a, Integer b) {
                    return Integer.compare(a >= 0 ? a : -(a + 1), b >= 0 ? b : -(b + 1));
                }
            });
            emitOne(ops);
        }
    }

    private void emitOne(List<Integer> ops) {
        time += (1 + rnd.nextInt(20)) * step;
        times.add(time);
        StringBuilder line = new StringBuilder("t ").append(time);
        for (int x : ops) {
            if (x >= 0) {
                line.append(" p ").append(keys[x]).append(' ').append(Gen.value(rnd, valmax, 0));
                live[x] = true;
            } else {
                line.append(" d ").append(keys[-(x + 1)]);
                live[-(x + 1)] = false;
            }
        }
        out.println(line);
    }

    /** Single puts of a key after every other, so that time passes, takes are made and
     *  reclaim's iterations and cuts go on over what the deletes left. */
    private void drive(int count, int round) {
        for (int i = 0; i < count; i++) {
            time += (1 + rnd.nextInt(20)) * step;
            times.add(time);
            out.println("t " + time + " p /zz/drive/" + (i % 7) + " s:r" + round + "i" + i);
        }
    }

    private void check() {
        if (rnd.nextInt(3) == 0) {
            out.println("check latest");
        }
    }

    /** Between two phases: reads, at the latest time and at an earlier one, and a restart. */
    private void between() {
        int r = rnd.nextInt(10);
        if (r < 4) {
            out.println("check latest");
        } else if (r < 6 && !times.isEmpty()) {
            // A check at an earlier time is refused alike by both sides once reclaim has
            // made it unavailable; the runner prints the refusal.
            out.println("check " + times.get(times.size() - 1 - rnd.nextInt(Math.min(times.size(), 50))));
        } else if (r < 8) {
            StringBuilder b = new StringBuilder("get latest");
            for (int i = 0; i < 4; i++) {
                b.append(' ').append(keys[rnd.nextInt(keys.length)]);
            }
            out.println(b);
        } else if (r < 9) {
            out.println("now");
        }
        if (rnd.nextInt(100) < restarts) {
            if (rnd.nextBoolean()) {
                out.println("sync");
            }
            out.println("restart");
        }
    }
}
