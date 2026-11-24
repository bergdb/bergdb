# Adds a dump of reclaim's iterations, cuts and records (user, step, table; from the start) (Reclaim.Stats, by reflection) to Perf.java
# of a run clone; not committed. Usage: python3 patch-perf.py CLONE
import sys, re
p = sys.argv[1] + "/java/stress/Perf.java"
s = open(p).read()
if "dumpReclaimStats" in s:
    print("already"); sys.exit(0)
anchor = 'metrics.put("reclaim.cuts_physical", (long) sampler.physicalCuts);'
assert s.count(anchor) == 1
s = s.replace(anchor, anchor + "\n        dumpReclaimStats(rstats);")
helper = '''
    static void dumpReclaimStats(Object rstats) {
        try {
            for (String list : new String[] {"iterations", "cuts"}) {
                java.lang.reflect.Field f = rstats.getClass().getDeclaredField(list);
                f.setAccessible(true);
                for (Object o : (List<?>) f.get(rstats)) System.out.println((list.equals("cuts") ? "CUT " : "ITER ") + dumpFields(o));
            }
            for (String rec : new String[] {"user", "step", "table"}) {
                java.lang.reflect.Field f = rstats.getClass().getDeclaredField(rec);
                f.setAccessible(true);
                System.out.println("REC " + rec + " " + dumpFields(f.get(rstats)));
            }
        } catch (Exception e) {
            System.out.println("DUMP failed: " + e);
        }
    }

    static String dumpFields(Object o) throws Exception {
        StringBuilder sb = new StringBuilder();
        for (java.lang.reflect.Field f : o.getClass().getDeclaredFields()) {
            if (java.lang.reflect.Modifier.isStatic(f.getModifiers())) continue;
            f.setAccessible(true);
            Object v = f.get(o);
            if (v == null || v instanceof Number || v instanceof Boolean) sb.append(f.getName()).append('=').append(v).append(' ');
            else if (!(v instanceof Collection) && !(v instanceof Map)) sb.append(f.getName()).append(".{").append(dumpFields(v)).append("} ");
        }
        return sb.toString().trim();
    }
}
'''
i = s.rstrip().rfind("}")
s = s[:i] + helper.lstrip("\n")
open(p, "w").write(s)
print("patched", p)
