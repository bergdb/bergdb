"""bergdb 005-64, question 4: the table of night/trickle.sh's results. Per buffer time, the median
over the rounds of, in the trickle window and in the idle window: interrupt wake-ups a second
(and package idle wake-ups), CPU ms a second, the energy the kernel attributes to the process
(ri_energy_nj) as an average power in uW; and from the probe, over each phase, the consumer
thread's CPU (BufferedStream-consumer) and the forces a second. After 005-14's idle-table.py.
Written 2026-10-28 by Claude (Opus 5.5, Claude Code).

Usage: python3 -I tools/trickle-table.py OUT > OUT/table.md
       python3 -I tools/trickle-table.py --check OUT
The check fails (exit 1) unless db-20, db-50, db-100 (trickle and idle) and jvm-0 (idle) each
have every cell parsed, and each window lies inside its phase; CHECK OK or CHECK FAILED at the end.
"""
import glob, os, re, statistics, sys

EXPECTED = [("db", 20), ("db", 50), ("db", 100), ("jvm", 0)]


def procstat(path):
    for line in open(path):
        kv = dict(x.split("=", 1) for x in line.split() if "=" in x)
        if "cpu_ns" in kv:
            return {k: int(v) for k, v in kv.items() if v.isdigit()}
    return None


def window(out, name, a, b):
    """The rates over a procstat window a..b (t0/t1 or i0/i1), or None."""
    pa, pb = os.path.join(out, name + "." + a), os.path.join(out, name + "." + b)
    ta, tb = os.path.join(out, name + ".time-" + a), os.path.join(out, name + ".time-" + b)
    if not all(os.path.exists(p) for p in (pa, pb, ta, tb)):
        return None
    x, y = procstat(pa), procstat(pb)
    sec = int(open(tb).read()) - int(open(ta).read())
    if not x or not y or sec <= 0:
        return None
    d = {k: y[k] - x[k] for k in x if k in y}
    return {"wk": d["interrupt_wkups"] / sec, "pkg": d["pkg_idle_wkups"] / sec, "cpu": d["cpu_ns"] / 1e6 / sec,
            "uw": d["energy_nj"] / 1e3 / sec, "t_start": int(open(ta).read()), "t_end": int(open(tb).read())}


def line_kv(text, tag):
    for line in text.splitlines():
        if line.startswith(tag + " "):
            return {k: float(v) for k, v in (x.split("=", 1) for x in line.split()[1:] if "=" in x)}
    return None


def load(out):
    rows = {}
    for log in sorted(glob.glob(os.path.join(out, "*-r*.log"))):
        name = os.path.basename(log)[:-4]
        m = re.match(r"(db|jvm)-(\d+)-r\d+$", name)
        if not m:
            continue
        text = open(log, errors="replace").read()
        r = {"valid": True}
        tr, idle, ist = line_kv(text, "TRICKLE"), line_kv(text, "IDLE"), line_kv(text, "IDLESTAT")
        if m.group(1) == "db":
            w = window(out, name, "t0", "t1")
            if w and tr:
                el = tr["elapsed_s"]
                r.update({"t_" + k: v for k, v in w.items()})
                r["t_tps"] = tr["transactions"] / el
                r["t_forces"] = tr["forces"] / el
                r["t_cons"] = tr["consumer_cpu_ms"] / el
                if w["t_end"] > tr["end_epoch_ms"] / 1000.0:
                    r["valid"] = False      # the window ran past the trickle phase
        w = window(out, name, "i0", "i1")
        if w and ist and idle:
            el = ist["elapsed_s"]
            r.update({"i_" + k: v for k, v in w.items()})
            r["i_forces"] = ist["forces"] / el
            r["i_cons"] = ist["consumer_cpu_ms"] / el
            if w["t_start"] < idle["epoch_ms"] / 1000.0:
                r["valid"] = False          # the window began before the idle phase
        rows.setdefault((m.group(1), int(m.group(2))), []).append(r)
    return rows


def med(rs, k, f):
    v = [r[k] for r in rs if k in r and r["valid"]]
    if not v:
        return "-"
    m = statistics.median(v)
    s = f.format(m)
    if len(v) > 1 and m and (max(v) - min(v)) / abs(m) > 0.15:
        s += " (" + f.format(min(v)) + "–" + f.format(max(v)) + ")"
    return s


T_COLS = [("transactions/s", "t_tps", "{:.1f}"), ("wake-ups/s", "t_wk", "{:.0f}"), ("pkg idle wake-ups/s", "t_pkg", "{:.0f}"),
          ("CPU ms/s", "t_cpu", "{:.2f}"), ("energy uW", "t_uw", "{:.0f}"), ("consumer CPU ms/s", "t_cons", "{:.2f}"),
          ("forces/s", "t_forces", "{:.1f}")]
I_COLS = [("wake-ups/s", "i_wk", "{:.0f}"), ("pkg idle wake-ups/s", "i_pkg", "{:.0f}"), ("CPU ms/s", "i_cpu", "{:.2f}"),
          ("energy uW", "i_uw", "{:.0f}"), ("consumer CPU ms/s", "i_cons", "{:.2f}"), ("forces/s", "i_forces", "{:.2f}")]


def label(mode, bt):
    return "JVM only, no database" if mode == "jvm" else "database, %d ms" % bt


def cells(rows, key, cols):
    return [med(rows.get(key, []), k, f) for (_, k, f) in cols]


def tables(rows):
    n = max([len(v) for v in rows.values()] or [0])
    out = ["Medians of up to %d rounds (range when wider than 15 %%). Wake-ups, CPU and energy from "
           "proc_pid_rusage over the window; the consumer's CPU and the forces from the probe over the whole phase.\n" % n]
    out.append("Trickle: small transactions, no sync, at the rate of the first column.\n")
    out.append("| process | runs | " + " | ".join(c[0] for c in T_COLS) + " |")
    out.append("|---|---:|" + "---:|" * len(T_COLS))
    for key in EXPECTED:
        if key[0] == "db" and key in rows:
            out.append("| %s | %d | %s |" % (label(*key), len(rows[key]), " | ".join(cells(rows, key, T_COLS))))
    out.append("")
    out.append("Idle: after the trickle, nothing written.\n")
    out.append("| process | runs | " + " | ".join(c[0] for c in I_COLS) + " |")
    out.append("|---|---:|" + "---:|" * len(I_COLS))
    for key in EXPECTED:
        if key in rows:
            out.append("| %s | %d | %s |" % (label(*key), len(rows[key]), " | ".join(cells(rows, key, I_COLS))))
    bad = [r for v in rows.values() for r in v if not r["valid"]]
    if bad:
        out.append("\n%d runs left out: a window outside its phase." % len(bad))
    return "\n".join(out)


def check(out):
    rows = load(out)
    nbad = 0
    for key in EXPECTED:
        cols = (T_COLS if key[0] == "db" else []) + I_COLS
        c = cells(rows, key, cols)
        rs = rows.get(key, [])
        invalid = sum(1 for r in rs if not r["valid"])
        ok = rs and "-" not in c and invalid == 0
        nbad += 0 if ok else 1
        print("%s %s: %d runs%s%s" % ("ok     " if ok else "MISSING", label(*key), len(rs),
              "" if "-" not in c else ", unparsed: " + ", ".join(cc[0] for cc, v in zip(cols, c) if v == "-"),
              "" if not invalid else ", %d windows outside their phase" % invalid))
    if nbad:
        print("CHECK FAILED: %d of %d rows missing, not parsed or invalid" % (nbad, len(EXPECTED)))
        return 1
    print("CHECK OK: %d rows, every cell parsed" % len(EXPECTED))
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--check":
        sys.exit(check(sys.argv[2]))
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    print(tables(load(sys.argv[1])))
