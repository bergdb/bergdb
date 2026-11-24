# bergdb 028-19: the counts of Perf write runs with reclaim (run.sh's OUT/LABEL.txt with the
# ITER and CUT lines of patch-perf.py, and OUT/LABEL/write.result.json). Usage:
#   python3 summ.py OUT LABEL...
import json, re, sys

out = sys.argv[1]
KEYS = ["bytes_appended_per_put", "rec.user_bytes_per_put", "rec.user_index_bytes_per_put",
        "rec.user_value_bytes_per_put", "rec.step_bytes_per_put", "rec.table_bytes_per_put",
        "rec.other_bytes_per_put", "index_nodes_per_commit", "reclaim.steps",
        "reclaim.iterations_done", "reclaim.cuts_logical", "reclaim.cuts_physical",
        "kept_mb_max", "kept_mb_mean", "stream_appended_mb", "commits_per_s", "load.puts_per_s",
        "commit.append.max_us", "commit.append.p99_us", "commit.append.p999_us",
        "gc.mxbean.count", "gc.mxbean.time_ms", "heap.after_gc_mb_max", "rss_mb_max"]


def fields(line):
    d = {}
    for k, v in re.findall(r"([A-Za-z.]+)=(-?[0-9]+|true|false|null)", line):
        d[k] = v if v in ("true", "false", "null") else int(v)
    return d


rows = {}
for lab in sys.argv[2:]:
    m = json.load(open(f"{out}/{lab}/write.result.json"))["metrics"]
    its, cuts = [], []
    for line in open(f"{out}/{lab}.txt"):
        if line.startswith("ITER "):
            its.append(fields(line))
        elif line.startswith("CUT "):
            cuts.append(fields(line))
    rows[lab] = (m, its, cuts)

w = max(len(k) for k in KEYS)
print("metric".ljust(w), *[lab.rjust(12) for lab in rows])
for k in KEYS:
    vals = []
    for lab in rows:
        v = rows[lab][0].get(k)
        vals.append(("-" if v is None else (f"{v:.1f}" if isinstance(v, float) else str(v))).rjust(12))
    print(k.ljust(w), *vals)

TSTEP = 10_000     # Perf's tstep at n = 10M, retain 0.1: 1 ms in units of 100 ns
for lab, (m, its, cuts) in rows.items():
    print(f"\n{lab}: iterations (p in MB, t in transactions of the clock, bytes in MB)")
    print("  pStart   tStart    pEnd     tEnd  len_MB   steps     kvs  values valMB recMB tabMB dirtMB afterRowMB rows charge/len")
    for it in its:
        ps, pe = it["pStart"] / 1e6, it["pEnd"] / 1e6 if it["pEnd"] >= 0 else float("nan")
        ts, te = it["tStart"] // TSTEP, it["tEnd"] // TSTEP if it["tEnd"] >= 0 else -1
        ln = pe - ps
        vb = it.get("valueBytes", 0) / 1e6
        db = it.get("dirtiedStored", it.get("dirtiedBytes", 0)) / 1e6
        rw = (vb + 32 * it["values"] / 1e6 + db) / ln if ln == ln and ln > 0 else float("nan")   # VN 32
        print(f"  {ps:7.0f} {ts:8d} {pe:7.0f} {te:8d} {ln:7.0f} {it['steps']:7d} {it['kvs']:8d} {it['values']:8d}"
              f" {vb:5.0f} {it['recordBytes']/1e6:5.0f} {it.get('tableBytes',0)/1e6:5.0f}"
              f" {it.get('dirtiedBytes',0)/1e6:6.0f} {it.get('dirtiedAfterRow',0)/1e6:10.0f}"
              f" {it.get('rowRecords',0):5d} {rw:6.3f}")
    for c in cuts:
        print(f"  CUT pos {c['pos']/1e6:.0f} MB, tEnd {c['tEnd']//TSTEP}, decided at {c['decidedAt']/1e6:.0f} MB,"
              f" t {c['decidedTime']//TSTEP}")
