"""bergdb 005-64: the tables of the buffer-time runs (night/run-f53.sh, night/s1-runner.sh),
from a results directory OUT of night/rounds.sh: OUT/rounds/rN/SCENARIO-bBT/run1/
write.result.json and write.stdout.txt (the CPU agent's CPU64 line), and OUT/mixed/
rN-CONFIG-bBT.txt (MixedProbe's MIXED line). Each cell is the median over the rounds, with the
range when it is wider than 10 percent. After 005-48's tools/table.py. Written 2026-10-28 by
Claude (Opus 5.5, Claude Code).

Usage: python3 -I tools/table.py OUT > OUT/table.md
       python3 -I tools/table.py --check SUITEFILE MIXEDFILE OUT
The check builds the same rows and fails (exit 1) unless every scenario of SUITEFILE and every
configuration of MIXEDFILE has a row at 20, 50 and 100 ms with every cell parsed (no "-"); it
prints one line per row and, at the end, CHECK OK or CHECK FAILED.
"""
import glob, json, os, re, statistics, sys

BTS = (20, 50, 100)


def load(out):
    runs = {}    # (base, bt) -> list of metric dicts
    for f in sorted(glob.glob(os.path.join(out, "rounds", "r*", "*", "run*", "write.result.json"))):
        scen = f.split(os.sep)[-3]
        m = re.match(r"(.*)-b(\d+)$", scen)
        if not m:
            continue
        try:
            met = dict(json.load(open(f))["metrics"])
        except (ValueError, KeyError):
            continue
        so = os.path.join(os.path.dirname(f), "write.stdout.txt")
        if os.path.exists(so):
            for line in open(so, errors="replace"):
                if line.startswith("CPU64 "):
                    for kv in line.split()[1:]:
                        k, v = kv.split("=", 1)
                        met["cpu64." + k] = float(v)
        runs.setdefault((m.group(1), int(m.group(2))), []).append(met)
    mixed = {}   # (config, bt) -> list of dicts
    for f in sorted(glob.glob(os.path.join(out, "mixed", "r*-*-b*.txt"))):
        m = re.match(r"r\d+-(.*)-b(\d+)\.txt$", os.path.basename(f))
        if not m:
            continue
        text = open(f, errors="replace").read()
        if "\nMIXED OK" not in "\n" + text:
            continue
        for line in text.splitlines():
            if line.startswith("MIXED ") and "=" in line:
                d = {}
                for kv in line.split()[1:]:
                    k, v = kv.split("=", 1)
                    d[k] = float(v)
                mixed.setdefault((m.group(1), int(m.group(2))), []).append(d)
    return runs, mixed


def cell(rows, key, scale=1.0, fmt="{:,.0f}"):
    vals = [r[key] * scale for r in rows if key in r]
    if not vals:
        return "-"
    med = statistics.median(vals)
    s = fmt.format(med)
    lo, hi = min(vals), max(vals)
    if med and (hi - lo) / abs(med) > 0.10:
        s += " (" + fmt.format(lo) + "–" + fmt.format(hi) + ")"
    return s


A_COLS = [("puts/s", "puts_per_s", 1, "{:,.0f}"), ("user MB/s", "user_mb_per_s", 1, "{:.1f}"),
          ("append p50 us", "commit.append.p50_us", 1, "{:.1f}"),
          ("p99.9 us", "commit.append.p999_us", 1, "{:.1f}"),
          ("max ms", "commit.append.max_us", 1e-3, "{:.2f}"),
          ("forces/s", "forces_per_s", 1, "{:.1f}"), ("KB per force", "bytes_per_force", 1e-3, "{:,.0f}"),
          ("ms per force", "force_ms_mean", 1, "{:.2f}"), ("force busy", "force_busy_fraction", 100, "{:.0f} %"),
          ("consumer CPU ms", "cpu64.consumer_cpu_ms", 1, "{:,.0f}"),
          ("process CPU s", "cpu64.process_cpu_ms", 1e-3, "{:.1f}")]
D_COLS = [("commits/s", "commits_per_s", 1, "{:,.0f}"),
          ("sync p50 ms", "commit.durable.p50_us", 1e-3, "{:.1f}"),
          ("p99 ms", "commit.durable.p99_us", 1e-3, "{:.1f}"),
          ("max ms", "commit.durable.max_us", 1e-3, "{:.1f}"),
          ("forces/s", "forces_per_s", 1, "{:.1f}"), ("KB per force", "bytes_per_force", 1e-3, "{:,.1f}"),
          ("ms per force", "force_ms_mean", 1, "{:.2f}"),
          ("consumer CPU ms", "cpu64.consumer_cpu_ms", 1, "{:,.0f}"),
          ("process CPU s", "cpu64.process_cpu_ms", 1e-3, "{:.1f}")]
M_SYNC = [("sync commits/s", "sync_commits_per_s", 1, "{:,.0f}"), ("sync p50 ms", "sync_p50_ms", 1, "{:.1f}"),
          ("p99 ms", "sync_p99_ms", 1, "{:.1f}"), ("max ms", "sync_max_ms", 1, "{:.1f}")]
M_PLAIN = [("plain puts/s", "plain_puts_per_s", 1, "{:,.0f}"),
           ("append p99.9 us", "plain_append_p999_us", 1, "{:.1f}"),
           ("max ms", "plain_append_max_ms", 1, "{:.2f}")]
M_REST = [("forces/s", "forces_per_s", 1, "{:.1f}"), ("KB per force", "bytes_per_force", 1e-3, "{:,.1f}"),
          ("ms per force", "force_ms_mean", 1, "{:.2f}"),
          ("CPU ms/s", "process_cpu_ms_per_s", 1, "{:.0f}"),
          ("consumer CPU ms/s", "consumer_cpu_ms_per_s", 1, "{:.1f}")]
M_COLS = M_SYNC + M_PLAIN + M_REST


def row(name, bt, rows, cols):
    cells = [cell(rows, k, sc, f) for (_, k, sc, f) in cols]
    return cells, "| %s | %d ms | %d | %s |" % (name, bt, len(rows), " | ".join(cells))


def header(cols):
    return ("| scenario | buffer time | runs | " + " | ".join(c[0] for c in cols) + " |\n"
            + "|---|---:|---:|" + "---:|" * len(cols))


def tables(runs, mixed):
    lines = []
    n = max([len(v) for v in list(runs.values()) + list(mixed.values())] or [0])
    lines.append("Medians of up to %d rounds (range when wider than 10 %%); the CPU is of the whole "
                 "run (load, warm-up, measured phase, verification), the consumer's from the CPU agent.\n" % n)
    bases = sorted({b for (b, _) in runs}, key=lambda s: (s[0] != "a", s))
    lines.append("Writers that do not sync: one thread; x100 is 100 puts per transaction (question 1).\n")
    lines.append(header(A_COLS))
    for b in bases:
        if b.startswith("d-"):
            continue
        for bt in BTS:
            if (b, bt) in runs:
                lines.append(row(b, bt, runs[(b, bt)], A_COLS)[1])
    lines.append("")
    lines.append("Writers that sync (sync(ORDINARY)) after each transaction, 1 KB values (question 2).\n")
    lines.append(header(D_COLS))
    for b in bases:
        if not b.startswith("d-"):
            continue
        for bt in BTS:
            if (b, bt) in runs:
                lines.append(row(b, bt, runs[(b, bt)], D_COLS)[1])
    lines.append("")
    lines.append("Mixed writers (MixedProbe, question 3): threads that sync after each transaction beside "
                 "threads that never sync, 1 KB values; see night/mixed.txt. The CPU is over the measured seconds.\n")
    lines.append(header(M_COLS))
    for c in sorted({c for (c, _) in mixed}):
        for bt in BTS:
            if (c, bt) in mixed:
                lines.append(row(c, bt, mixed[(c, bt)], M_COLS)[1])
    return "\n".join(lines)


def names(path):
    out = []
    for line in open(path):
        line = line.strip()
        if line and not line.startswith("#"):
            out.append(line.split())
    return out


def check(suitef, mixedf, out):
    runs, mixed = load(out)
    bad = 0
    total = 0
    for parts in names(suitef):
        m = re.match(r"(.*)-b(\d+)$", parts[0])
        base, bt = m.group(1), int(m.group(2))
        cols = D_COLS if base.startswith("d-") else A_COLS
        rows = runs.get((base, bt), [])
        cells = row(base, bt, rows, cols)[0] if rows else ["-"]
        ok = rows and "-" not in cells
        total += 1
        bad += 0 if ok else 1
        print("%s %s at %d ms: %d runs%s" % ("ok     " if ok else "MISSING", base, bt, len(rows),
              "" if ok else ", unparsed: " + ", ".join(c[0] for c, v in zip(cols, cells) if v == "-")))
    for parts in names(mixedf):
        cfg, st, pt = parts[0], int(parts[1]), int(parts[3])
        cols = (M_SYNC if st > 0 else []) + (M_PLAIN if pt > 0 else []) + M_REST
        for bt in BTS:
            rows = mixed.get((cfg, bt), [])
            cells = row(cfg, bt, rows, cols)[0] if rows else ["-"]
            ok = rows and "-" not in cells
            total += 1
            bad += 0 if ok else 1
            print("%s %s at %d ms: %d runs%s" % ("ok     " if ok else "MISSING", cfg, bt, len(rows),
                  "" if ok else ", unparsed: " + ", ".join(c[0] for c, v in zip(cols, cells) if v == "-")))
    if bad:
        print("CHECK FAILED: %d of %d rows missing or not parsed" % (bad, total))
        return 1
    print("CHECK OK: %d rows, every cell parsed" % total)
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "--check":
        sys.exit(check(sys.argv[2], sys.argv[3], sys.argv[4]))
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    print(tables(*load(sys.argv[1])))
