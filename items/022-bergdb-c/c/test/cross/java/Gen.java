package bergdb.cross;

import java.io.PrintStream;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

/**
 * Random cross workloads from a seed (bergdb 012-05, section 3, step 4): transactions of
 * puts and deletes on short and long keys (more than one segment), values of every form
 * and size, big and empty transactions, deletes of missing keys, node sizes 8 to 62,
 * startup distances from 100 bytes to 1 MB, retain durations (reclaim), restarts, now
 * lines, checks and gets, and calls of the setters. Each parameter not given is drawn
 * from the seed, so that seeds differ in their shapes too. The workload is the
 * interface: C never runs this class.
 *
 * <pre>
 * Usage: java -cp CLASSES bergdb.cross.Gen SEED [NAME=VALUE...]
 *   n        transactions                     keys     distinct keys
 *   maxnode  8, 14, 30 or 62                  sd       startup distance in bytes
 *   retain   seconds, 0 for forever           restarts restart lines
 *   valmax   the largest ordinary value       big      percent of big transactions
 *   del      percent of deletes               long     percent of long keys
 *   empty    percent of empty transactions    huge     per mille of values of 10 to 300 kB
 *   setters  setter calls                     reads    check and get lines
 * Prints the workload ("bergdb-workload 1") on standard output.
 * </pre>
 */
public final class Gen {
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

    public static void generate(long seed, Map<String, String> params, PrintStream out) {
        Random rnd = new Random(seed * 0x9E3779B97F4A7C15L + 12345);
        final int n = (int) get(params, "n", 200 + rnd.nextInt(1800));
        final int keyCount = (int) get(params, "keys", 20 + rnd.nextInt(2000));
        final int maxNode = (int) get(params, "maxnode", new int[] {8, 14, 30, 62}[rnd.nextInt(4)]);
        final int sd = (int) get(params, "sd", (long) Math.pow(10, 2 + 4 * rnd.nextDouble()));
        final long retainSec = get(params, "retain", rnd.nextInt(10) < 6 ? 0 : 1 + rnd.nextInt(20));
        final int restarts = (int) get(params, "restarts", rnd.nextInt(6));
        final int valmax = (int) get(params, "valmax", 1 + rnd.nextInt(400));
        final int big = (int) get(params, "big", rnd.nextInt(11));
        final int del = (int) get(params, "del", rnd.nextInt(31));
        final int longKeys = (int) get(params, "long", rnd.nextInt(51));
        final int empty = (int) get(params, "empty", rnd.nextInt(6));
        final int huge = (int) get(params, "huge", rnd.nextInt(6));
        final int setters = (int) get(params, "setters", rnd.nextInt(4));
        final int reads = (int) get(params, "reads", rnd.nextInt(6));

        out.println("bergdb-workload 1");
        out.println("# Gen seed=" + seed + " n=" + n + " keys=" + keyCount + " maxnode=" + maxNode
                + " sd=" + sd + " retain=" + retainSec + " restarts=" + restarts + " valmax="
                + valmax + " big=" + big + " del=" + del + " long=" + longKeys + " empty="
                + empty + " huge=" + huge + " setters=" + setters + " reads=" + reads);
        out.println("set maxnode " + maxNode);
        out.println("set sd " + sd);
        if (retainSec > 0) {
            out.println("set retain " + retainSec * UNITS_PER_SEC);
        }
        if (rnd.nextInt(4) == 0) {
            out.println("set budget " + (10000 + rnd.nextInt(1000000)));
        }
        if (retainSec > 0 && rnd.nextInt(3) == 0) {
            out.println("set fraction " + fraction(rnd));
        }

        // The positions (transaction indexes) of the restarts, setters and reads.
        int[] restartAt = positions(rnd, restarts, n);
        int[] setterAt = positions(rnd, setters, n);
        int[] readAt = positions(rnd, reads, n);

        final long step = retainSec > 0 ? UNITS_PER_SEC / 100 : 1;
        long time = rnd.nextInt(3) == 0 ? 0 : 1 + rnd.nextInt(1000000);
        if (time > 0) {
            out.println("clock " + time);
        }
        StringBuilder line = new StringBuilder();
        for (int i = 0; i < n; i++) {
            int r = rnd.nextInt(100);
            if (r < 2) {
                out.println("now");
            } else if (r < 3) {
                time += (1 + rnd.nextInt(20)) * step;
                out.println("clock " + time);
            }
            line.setLength(0);
            if (rnd.nextInt(100) < 5 && i > 0) {
                line.append("t -");
            } else {
                time += (1 + rnd.nextInt(20)) * step;
                line.append("t ").append(time);
            }
            if (rnd.nextInt(100) >= empty) {
                int ops = 1 + rnd.nextInt(3);
                if (rnd.nextInt(100) < big) {
                    ops = 1 + rnd.nextInt(40);
                }
                for (int o = 0; o < ops; o++) {
                    String key = key(rnd, keyCount, longKeys);
                    if (rnd.nextInt(100) < del) {
                        line.append(" d ").append(rnd.nextInt(10) == 0 ? "/missing/" + i : key);
                    } else {
                        line.append(" p ").append(key).append(' ').append(value(rnd, valmax, huge));
                    }
                }
            }
            out.println(line);
            for (int k = 0; k < setterAt.length; k++) {
                if (setterAt[k] == i) setter(rnd, retainSec, out);
            }
            for (int k = 0; k < readAt.length; k++) {
                if (readAt[k] == i) read(rnd, keyCount, longKeys, time, out);
            }
            for (int k = 0; k < restartAt.length; k++) {
                if (restartAt[k] == i) {
                    if (rnd.nextBoolean()) out.println("sync");
                    out.println("restart");
                }
            }
        }
        out.println("check latest");
        out.println("sync");
    }

    /** k positions in 0 to n-1, drawn. */
    private static int[] positions(Random rnd, int k, int n) {
        int[] result = new int[k];
        for (int i = 0; i < k; i++) {
            result[i] = rnd.nextInt(n);
        }
        return result;
    }

    private static String fraction(Random rnd) {
        return String.format(Locale.ROOT, "%.2f", 0.05 + 0.45 * rnd.nextDouble());
    }

    private static final String LONG = "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

    static String key(Random rnd, int keyCount, int longKeys) {
        int k = rnd.nextInt(keyCount);
        if (rnd.nextInt(100) < longKeys) {
            // More than one segment (7 bytes a segment): 7 to 60 bytes, by the key's number.
            int len = 1 + k % 54;
            return "/long/" + LONG.substring(0, len) + "/" + k;
        }
        switch (k % 50) {
        case 0: return "/sp%20ace/" + k;
        case 1: return "/%C3%BCml/" + k;           // a UTF-8 character
        case 2: return "/%23hash/" + k;            // '#', escaped
        default: return "/k/" + k;
        }
    }

    static String value(Random rnd, int valmax, int huge) {
        if (rnd.nextInt(1000) < huge) {
            int size = 10000 + rnd.nextInt(290000);
            return rnd.nextBoolean() ? "z:" + size : "r:" + (rnd.nextLong() >>> 1) + ":" + size;
        }
        int size = rnd.nextInt(valmax + 1);
        switch (rnd.nextInt(4)) {
        case 0: {
            StringBuilder b = new StringBuilder("s:");
            for (int i = 0; i < size; i++) b.append((char) ('a' + rnd.nextInt(26)));
            return b.toString();
        }
        case 1: {
            StringBuilder b = new StringBuilder("x:");
            for (int i = 0; i < size; i++) {
                b.append(String.format("%02x", rnd.nextInt(256)));
            }
            return b.toString();
        }
        case 2: return "z:" + size;
        default: return "r:" + (rnd.nextLong() >>> 1) + ":" + size;
        }
    }

    private static void setter(Random rnd, long retainSec, PrintStream out) {
        switch (rnd.nextInt(retainSec > 0 ? 4 : 2)) {
        case 0: out.println("setsd " + (long) Math.pow(10, 2 + 4 * rnd.nextDouble())); break;
        case 1: out.println("setbudget " + (10000 + rnd.nextInt(100000000))); break;
        case 2: out.println("setretain " + (rnd.nextInt(4) == 0 ? "forever"
                : Long.toString((1 + rnd.nextInt(20)) * UNITS_PER_SEC))); break;
        default: out.println("setfraction " + fraction(rnd)); break;
        }
    }

    private static void read(Random rnd, int keyCount, int longKeys, long time,
            PrintStream out) {
        out.println("check latest");
        if (time > 2) {
            out.println("check " + (1 + rnd.nextLong(time)));
        }
        StringBuilder b = new StringBuilder("get latest");
        for (int i = 0; i < 10; i++) b.append(' ').append(key(rnd, keyCount, longKeys));
        out.println(b);
        if (time > 2) {
            b.setLength(0);
            b.append("get ").append(1 + rnd.nextLong(time));
            for (int i = 0; i < 10; i++) b.append(' ').append(key(rnd, keyCount, longKeys));
            out.println(b);
        }
    }
}
