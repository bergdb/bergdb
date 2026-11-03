"""Compact tables from 005-64's raw performance results for this fix.

Usage: python3 summarize.py runs/f53/metrics.json runs/s1/metrics.json
Each JSON is a list of {scenario, round, metrics}, extracted from the original
write.result.json files; original sessions and force probes are kept beside it.
"""
import json
from pathlib import Path
import statistics
import sys


def table(headers, rows):
    widths = [max(len(row[i]) for row in rows) for i in range(len(headers))]
    print("| " + " | ".join(headers) + " |")
    print("|" + "---|" * len(headers))
    for row in rows:
        print("| " + " | ".join(f"{cell:<{width}}" for cell, width in zip(row, widths)) + " |")
    print()


for name in sys.argv[1:]:
    path = Path(name)
    rows = json.loads(path.read_text())
    assert len(rows) == 18, (name, "expected 18 runs")
    print(path.parent.name + ": medians of three rotated rounds, followed by min and max.\n")
    for metric, title, scale, fmt in (
        ("puts_per_s", "puts/s", 1, ",.0f"),
        ("commit.append.p999_us", "append p99.9 ms", .001, ".3f"),
    ):
        print(title + "\n")
        medians = []
        ranges = []
        for scenario in ("a-1k", "a-1k-x100"):
            cells = []
            for bt in (20, 50, 100):
                selected = [r for r in rows if r["scenario"] == f"{scenario}-b{bt}"]
                assert len(selected) == 3 and {r["round"] for r in selected} == {1, 2, 3}
                vals = [r["metrics"][metric] * scale for r in selected]
                cells.append(format(statistics.median(vals), fmt))
                ranges.append([scenario, str(bt), format(min(vals), fmt), format(max(vals), fmt)])
            medians.append([scenario] + cells)
        table(["workload", "20 ms", "50 ms", "100 ms"], medians)
        table(["workload", "buffer ms", "min", "max"], ranges)
