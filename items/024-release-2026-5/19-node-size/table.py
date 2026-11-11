#!/usr/bin/env python3
"""024-19: tables from out/c1m-SET-nB.txt and out/c10m-SET-nB.txt.
python3 -I table.py [c1m|c10m] [SETS]"""
import os, re, sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
SIZES = [8, 14, 30, 62, 126, 254]


def kv(line):
    return dict(re.findall(r"(\S+?)=(\S+)", line))


def parse(path):
    r = {}
    for line in open(path):
        for tag in ("FILL", "TREE-FILL", "UPD", "TREE-UPD", "RESTART"):
            if re.search(r"\] %s " % tag, line):
                r[tag] = kv(line)
        m = re.search(r"\] (WARM|COLD) (\S+) (.*)", line)
        if m:
            r[m.group(1) + "-" + m.group(2)] = kv(m.group(3))
        if line.startswith("MEM "):
            d = kv(line)
            r["MEM-" + d["shape"]] = float(line.split()[-2])
        if "Exception" in line or "Error" in line:
            r["ERR"] = line.strip()[:80]
    return r


def f(x, nd=0):
    try:
        return ("%." + str(nd) + "f") % float(x)
    except (TypeError, ValueError):
        return "-"


def main():
    pre = sys.argv[1] if len(sys.argv) > 1 else "c1m"
    sets = sys.argv[2:] or ["A", "B", "C", "D", "E", "F", "M"]
    for s in sets:
        rows = []
        for b in SIZES:
            p = os.path.join(D, "%s-%s-n%d.txt" % (pre, s, b))
            if os.path.exists(p):
                rows.append((b, parse(p)))
        if not rows:
            continue
        print("set", s)
        if s == "M":
            print("| B | MEM mem keys | MEM k24 keys |")
            for b, r in rows:
                print("| %d | %s | %s |" % (b, f(r.get("MEM-mem"), 1), f(r.get("MEM-k24"), 1)))
            continue
        print("| B | fill B/put | tx B/put | nodes | path | live/node | stored/key | upd B/put"
              " | nodes | live/node | stored/key | kept/key |")
        for b, r in rows:
            fl, tf, u, tu = (r.get(k, {}) for k in ("FILL", "TREE-FILL", "UPD", "TREE-UPD"))
            txb = float(fl.get("bytesPerTx", "nan")) / float(fl.get("batch", "100") or 100) \
                if fl else None
            print("| %d | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |%s" % (
                b, f(fl.get("bytesPerPut")), f(txb), tf.get("keyNodes", "-"), f(tf.get("path"), 1),
                f(tf.get("livePerNode"), 1), f(tf.get("storedPerKey"), 1),
                f(u.get("bytesPerPut")), tu.get("keyNodes", "-"), f(tu.get("livePerNode"), 1),
                f(tu.get("storedPerKey"), 1), f(u.get("keptPerKey")),
                (" " + r["ERR"]) if "ERR" in r else ""))
        extra = [(b, r) for b, r in rows if "WARM-gets2" in r or "RESTART" in r]
        if extra:
            print("| B | warm us/get | loads/get | scan ns/key | restart ms | cold loads/get"
                  " | cold us/get | fill puts/s | upd puts/s |")
            for b, r in extra:
                w, c, sc = r.get("WARM-gets2", {}), r.get("COLD-cold-gets", {}), \
                    r.get("WARM-scan2", {})
                print("| %d | %s | %s | %s | %s | %s | %s | %s | %s |" % (
                    b, f(w.get("us/get"), 2), f(w.get("loads/get"), 2), sc.get("ns/key", "-"),
                    r.get("RESTART", {}).get("ms", "-"), f(c.get("loads/get"), 2),
                    f(c.get("us/get"), 2), f(r.get("FILL", {}).get("puts/s")),
                    f(r.get("UPD", {}).get("puts/s"))))
        print()


main()
