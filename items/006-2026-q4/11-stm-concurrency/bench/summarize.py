"""Summarize completed RwBench sessions; raw JVM results remain authoritative."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import statistics as st


def group_key(session, result):
    return (session, result["run"]["job"]["case"], result["variant"],
            result["mode"], result["threads"], result["storage"],
            result["durable"], result["cache_bytes"])


def main(args):
    args.out.mkdir(parents=True, exist_ok=True)
    grouped, rows = {}, []
    for item in args.session:
        name, path = item.split("=", 1)
        results = json.loads((Path(path) / "results.json").read_text())
        for result in results:
            if not result["verification"]["passed"]:
                raise ValueError("unchecked result")
            grouped.setdefault(group_key(name, result), []).append(result)
            m = result["measured"]
            workers = m["per_worker_active_commits"]
            rows.append({"session": name, "case": result["run"]["job"]["case"],
                "repeat": result["run"]["job"]["repeat"], "variant": result["variant"],
                "mode": result["mode"], "threads": result["threads"],
                "reads": result["reads"], "work_iterations": result["work"],
                "storage": result["storage"], "durable": result["durable"],
                "cache_bytes": result["cache_bytes"],
                "rate": m["active_commits_per_second"],
                "drained_rate": m["batch_commits_per_second"],
                "drain_seconds": m["drain_seconds"],
                "attempts_per_commit": m["attempts_per_commit"],
                "mean_us": m["latency"]["mean_ns"] / 1000,
                "p50_us": m["latency"]["p50_ns_upper"] / 1000,
                "p99_us": m["latency"]["p99_ns_upper"] / 1000,
                "max_ms": m["latency"]["max_ns"] / 1e6,
                "minimum_worker_commits": min(workers),
                "maximum_worker_commits": max(workers),
                "worker_cpu_cores": m["worker_cpu_ns"] / (m["batch_seconds"] * 1e9),
                "process_cpu_cores": m["process_cpu_ns"] / (m["batch_seconds"] * 1e9),
                "allocated_bytes_per_commit": m["allocated_bytes"] / max(1, m["commits"]),
                "gc_ms": m["gc_ms"], "stream_loads": m["stream_loads"],
                "heap_bytes": m["heap_used_bytes"],
                "locked_storage_reads": m.get("storage_read_calls_with_write_lock", ""),
                "locked_storage_read_ns": m.get("storage_read_ns_with_write_lock", ""),
                "unlocked_storage_reads": m.get("storage_read_calls_without_write_lock", ""),
                "calibration_us": result["calibration"]["ns_per_compute"] / 1000,
                "directory": result["run"]["directory"]})
    if not rows:
        raise ValueError("no results")
    with (args.out / "all-runs.csv").open("w", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    summaries = []
    for key, values in sorted(grouped.items()):
        rates = [r["measured"]["active_commits_per_second"] for r in values]
        med = st.median(rates)
        entry = dict(zip(["session", "case", "variant", "mode", "threads",
                          "storage", "durable", "cache_bytes"], key))
        entry.update({"runs": len(values), "median_rate": med,
                      "minimum_rate": min(rates), "maximum_rate": max(rates),
                      "cv_percent": 100 * st.pstdev(rates) / st.mean(rates),
                      "median_drained_rate": st.median(r["measured"]["batch_commits_per_second"] for r in values),
                      "median_attempts_per_commit": st.median(r["measured"]["attempts_per_commit"] for r in values),
                      "median_p99_us": st.median(r["measured"]["latency"]["p99_ns_upper"] / 1000 for r in values),
                      "maximum_latency_ms": max(r["measured"]["latency"]["max_ns"] / 1e6 for r in values),
                      "maximum_drain_seconds": max(r["measured"]["drain_seconds"] for r in values),
                      "minimum_worker_active": min(min(r["measured"]["per_worker_active_commits"]) for r in values),
                      "median_process_cpu_cores": st.median(r["measured"]["process_cpu_ns"] / (r["measured"]["batch_seconds"] * 1e9) for r in values),
                      "median_allocated_bytes_per_commit": st.median(r["measured"]["allocated_bytes"] / max(1, r["measured"]["commits"]) for r in values),
                      "median_calibration_us": st.median(r["calibration"]["ns_per_compute"] / 1000 for r in values)})
        summaries.append(entry)
    (args.out / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
    by_key = {(r["session"], r["case"], r["variant"], r["mode"], r["threads"]): r for r in summaries}
    lines = ["# 006-11 benchmark aggregates", "",
             "Rates are medians of fresh JVM runs, successful transactions/s. "
             "Percentiles are medians of per-run histogram upper bounds; max is across runs.", ""]
    cases = sorted({r["case"] for r in summaries if r["session"] == "main"})
    if cases:
        lines += ["## Main resident runs", "",
                  "| Workload | Serial 1 | Optimistic 1 | Optimistic 2 | Optimistic 4 | Optimistic 8 | O8 / S1 | O8 / S8 |",
                  "|---|---:|---:|---:|---:|---:|---:|---:|"]
        for case in cases:
            def lookup(mode, threads):
                return by_key.get(("main", case, "stock", mode, threads))
            serial = lookup("serial", 1)
            opt = [lookup("optimistic", t) for t in [1, 2, 4, 8]]
            serial8 = lookup("serial", 8)
            cells = [case, f"{serial['median_rate']:,.0f}" if serial else "pending"]
            cells += [f"{r['median_rate']:,.0f}" if r else "pending" for r in opt]
            cells += [f"{opt[-1]['median_rate']/serial['median_rate']:.2f}x" if opt[-1] and serial else "pending",
                      f"{opt[-1]['median_rate']/serial8['median_rate']:.2f}x" if opt[-1] and serial8 else "pending"]
            lines.append("| " + " | ".join(cells) + " |")
        lines += ["", "## Main runs: eight-worker latency and fairness", "",
                  "| Workload | Mode | Rate | Drained rate | Attempts/commit | p99 us | Max ms | Worst worker active commits | Rate min–max | CV |",
                  "|---|---|---:|---:|---:|---:|---:|---:|---|---:|"]
        for r in summaries:
            if r["session"] != "main" or r["threads"] != 8:
                continue
            lines.append(f"| {r['case']} | {r['mode']} | {r['median_rate']:,.0f} | {r['median_drained_rate']:,.0f} | "
                         f"{r['median_attempts_per_commit']:.5f} | {r['median_p99_us']:,.1f} | {r['maximum_latency_ms']:,.1f} | "
                         f"{r['minimum_worker_active']:,} | {r['minimum_rate']:,.0f}–{r['maximum_rate']:,.0f} | {r['cv_percent']:.1f}% |")
    costs = sorted({(r["case"], r["threads"]) for r in summaries if r["session"] == "cost"})
    if costs:
        lines += ["", "## Serial-only bypass controls", "",
                  "| Workload | Threads | Stock | Bypass validation/recording | Bypass + no warm-up | Partial runtime stripping | Narrow gain | Stripped gain |",
                  "|---|---:|---:|---:|---:|---:|---:|---:|"]
        for case, threads in costs:
            found = [by_key.get(("cost", case, v, "serial", threads)) for v in
                     ["stock", "serial-bypass", "serial-bypass-no-warmup"]]
            if not all(found):
                continue
            a, b, c = [x["median_rate"] for x in found]
            stripped = by_key.get(("cost", case, "serial-stripped", "serial", threads))
            last = f"{stripped['median_rate']:,.0f}" if stripped else "pending"
            gain = f"{(stripped['median_rate']/a-1)*100:+.1f}%" if stripped else "pending"
            lines.append(f"| {case} | {threads} | {a:,.0f} | {b:,.0f} | {c:,.0f} | {last} | {(b/a-1)*100:+.1f}% | {gain} |")
        lines += ["", "## Optimistic actions versus the stripped single-caller control", "",
                  "| Workload | Stripped serial 1 | Stock optimistic 4 | Ratio | Stock optimistic 8 | Ratio |",
                  "|---|---:|---:|---:|---:|---:|"]
        for case, threads in costs:
            if threads != 1:
                continue
            control = by_key.get(("cost", case, "serial-stripped", "serial", 1))
            o4 = by_key.get(("main", case, "stock", "optimistic", 4))
            o8 = by_key.get(("main", case, "stock", "optimistic", 8))
            if control and o4 and o8:
                c, a, b = control["median_rate"], o4["median_rate"], o8["median_rate"]
                lines.append(f"| {case} | {c:,.0f} | {a:,.0f} | {a/c:.2f}x | {b:,.0f} | {b/c:.2f}x |")
    extra = [r for r in summaries if r["session"] not in ["main", "cost"]]
    if extra:
        lines += ["", "## Supplementary sessions", "",
                  "| Session | Workload | Threads | Mode | Rate | Drained | Attempts/commit | p99 us | Max ms |",
                  "|---|---|---:|---|---:|---:|---:|---:|---:|"]
        for r in extra:
            lines.append(f"| {r['session']} | {r['case']} | {r['threads']} | {r['mode']} | {r['median_rate']:,.0f} | "
                         f"{r['median_drained_rate']:,.0f} | {r['median_attempts_per_commit']:.5f} | "
                         f"{r['median_p99_us']:,.1f} | {r['maximum_latency_ms']:,.1f} |")
    lines += ["", f"Verified result files: {len(rows)}. "
              f"Summary script SHA-256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}.", ""]
    (args.out / "summary.md").write_text("\n".join(lines))
    print(f"Summarized {len(rows)} checked runs in {args.out}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--session", action="append", required=True)
    parser.add_argument("--out", type=Path, required=True)
    main(parser.parse_args())
