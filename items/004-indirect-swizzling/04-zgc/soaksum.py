#!/usr/bin/env python3
"""A compact copy of a Soak result.json, for 004-04: the workload, the metrics, the latency
summaries (no histograms), the GC log's summary of the measured phase, the eviction line and
the slowest commits with the pauses that overlapped them.

Usage: soaksum.py RESULT.json > SUMMARY.json
"""
import json
import sys

d = json.load(open(sys.argv[1]))
out = {
    "ok": d.get("ok"),
    "params": d.get("params"),
    "collector": d.get("info", {}).get("jvm", {}).get("collector"),
    "vmFlags": d.get("info", {}).get("jvm", {}).get("vmFlags"),
    "phases": d.get("phases"),
    "windows_uptime_s": d.get("windows_uptime_s"),
    "metrics": d.get("metrics"),
    "latency": d.get("latency"),
    "gcLog_measured": d.get("gcLog", {}).get("measured"),
    "gcLog_heap_after_gc_measured": d.get("gcLog", {}).get("heap_after_gc_measured"),
    "eviction": d.get("eviction"),
    "restarts": d.get("restarts"),
    "slowest_commits_with_pauses": d.get("slowest_commits_with_pauses", [])[:10],
}
json.dump(out, sys.stdout, indent=1)
print()
