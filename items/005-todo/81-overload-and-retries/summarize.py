#!/usr/bin/env python3
"""bergdb 005-81: tables from a RetryBench session (run-s1.sh's out/SESSION directory).

Usage: summarize.py SESSION_DIR. Prints Markdown: one row per run, the probe runs' sleeps, the
probe2 runs' lock waits and refusal reasons, then the retried requests of 5 or more attempts. Reads result.json and
retried-requests.csv in each run directory; checks that every run passed its verification.
"""
import csv, json, pathlib, sys

root = pathlib.Path(sys.argv[1])
runs = []
for d in sorted(root.iterdir()):
    f = d / "result.json"
    if not d.is_dir() or not f.exists():
        continue
    text = f.read_text().strip()
    if not text:
        print(f"{d.name}: no result (see stderr.txt)")
        continue
    r = json.loads(text)
    assert r["verification"]["passed"], d
    assert r.get("reopen_verification", {"passed": True})["passed"], d
    m = r["measured"]
    runs.append((d, r, m))

def key(item):
    d, r, m = item
    return (r["workload"], r["threads"], r["variant"], d.name)

print("| Run | Active/s | Drained/s | Requests | Retried | Requests by attempts | Max latency ms "
      "| Longest completion gap ms | Between attempts, % of worker time | Drain s | Reopen check |")
print("|---|--:|--:|--:|--:|---|--:|--:|--:|--:|---|")
for d, r, m in sorted(runs, key=key):
    print(f"| {d.name} | {m['active_commits_per_second']:.0f} | {m['batch_commits_per_second']:.0f} "
          f"| {m['commits']} | {m['retried_requests']} | {m['requests_by_attempts']} "
          f"| {m['latency']['max_ns'] / 1e6:.1f} | {m['max_completion_gap_ns'] / 1e6:.1f} "
          f"| {100 * m['between_attempts_share_of_worker_time']:.1f} | {m['drain_seconds']:.2f} "
          f"| {'passed, %.0f ms' % r['reopen_verification']['reopen_ms'] if 'reopen_verification' in r else '-'} |")

print()
print("| Run | Retries | Requested sleep ms | Measured sleep ms | Oversleep ms per retry "
      "| Refused execute us per retry | Between attempts ms | Per-worker sleep ms | Per-worker longest gap ms |")
print("|---|--:|--:|--:|--:|--:|--:|---|---|")
for d, r, m in sorted(runs, key=key):
    if r["variant"] == "stock" or m["probe_retries"] == 0:
        continue
    n = m["probe_retries"]
    req, slept = m["probe_requested_sleep_ms"], m["probe_slept_ns"] / 1e6
    print(f"| {d.name} | {n} | {req} | {slept:.1f} | {(slept - req) / n:.3f} "
          f"| {m['probe_refused_execute_ns'] / 1e3 / n:.1f} | {m['between_attempts_ns'] / 1e6:.1f} "
          f"| {m['per_worker_sleep_ms']} | {m['per_worker_max_completion_gap_ms']} |")

print()
print("| Run | Refused, changed key | Refused, history | Lock wait us per refusal "
      "| Lock wait ns per other attempt | Longest lock wait us |")
print("|---|--:|--:|--:|--:|--:|")
for d, r, m in sorted(runs, key=key):
    if r["variant"] != "probe2":
        continue
    refused = m["probe_refused_conflict"] + m["probe_refused_history"]
    other = m["probe_lock_waits"] - refused
    per_refusal = m["probe_lock_wait_ns_refused"] / 1e3 / refused if refused else 0
    per_other = (m["probe_lock_wait_ns"] - m["probe_lock_wait_ns_refused"]) / other if other else 0
    print(f"| {d.name} | {m['probe_refused_conflict']} | {m['probe_refused_history']} | {per_refusal:.1f} "
          f"| {per_other:.0f} | {m['probe_max_lock_wait_ns'] / 1e3:.0f} |")

print()
print("Retried requests with 5 or more attempts (all runs):")
print()
print("| Run | Worker | Begin ms | Latency ms | Attempts | Between attempts ms | Requested sleep ms | Measured sleep ms |")
print("|---|--:|--:|--:|--:|--:|--:|--:|")
for d, r, m in sorted(runs, key=key):
    f = d / "retried-requests.csv"
    if not f.exists():
        continue
    for row in csv.DictReader(f.open()):
        if int(row["attempts"]) >= 5:
            probe = r["variant"] != "stock"
            print(f"| {d.name} | {row['worker']} | {float(row['begin_ms']):.0f} | {float(row['latency_ms']):.1f} "
                  f"| {row['attempts']} | {float(row['between_attempts_ms']):.1f} "
                  f"| {row['requested_sleep_ms'] if probe else '-'} | {row['slept_ms'] if probe else '-'} |")
