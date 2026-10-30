"""Continue the authorized experiments after the frozen main session finishes.

This driver never edits production sources. It records/builds the additional
serial-only control, extends only the item-local harness for eviction, then
runs the remaining plans sequentially.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RUNS = Path("/private/tmp/bergdb-006-11-runs")
OLD_BUILDS = Path("/private/tmp/bergdb-006-11-builds-l66cxw25/builds.json")
NEW_BUILD = Path("/private/tmp/bergdb-006-11-stripped-build")


def command(args):
    print("COMMAND", " ".join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=ROOT, check=True)


def main():
    print("Waiting for main's frozen session to finish", flush=True)
    timeout = time.monotonic() + 5400
    while True:
        metadata_path = RUNS / "main/metadata.json"
        if metadata_path.exists():
            metadata = json.loads(metadata_path.read_text())
            if metadata.get("finished_utc"):
                if metadata.get("completed_jobs") != 168:
                    raise RuntimeError("main session did not complete its plan")
                break
        if time.monotonic() > timeout:
            raise RuntimeError("main did not finish")
        time.sleep(5)
    frozen_sha = hashlib.sha256((HERE / "RwBench.java").read_bytes()).hexdigest()
    if frozen_sha != metadata["harness_sha256"]:
        raise RuntimeError("main harness changed before extension")
    old = json.loads(OLD_BUILDS.read_text())
    command(["python3", "-B", HERE / "build.py", "--out", NEW_BUILD,
             "--variants", "serial-stripped", "--commit", old["commit"]])
    extra = json.loads((NEW_BUILD / "builds.json").read_text())
    if old["commit"] != extra["commit"]:
        raise RuntimeError("variant source snapshot differs")
    old["variants"].update(extra["variants"])
    master = RUNS / "all-builds.json"
    master.write_text(json.dumps(old, indent=2) + "\n")
    command(["git", "apply", "--check", HERE / "eviction-startup.patch"])
    command(["git", "apply", HERE / "eviction-startup.patch"])
    harness = HERE / "RwBench.java"
    text = harness.read_text()
    anchor = '            out.put("heap_used_bytes", Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory());'
    if text.count(anchor) != 1:
        raise RuntimeError("resident metric anchor changed")
    text = text.replace(anchor, anchor
        + '\n            out.put("resident_cache_bytes", core.internal().cache().residents().bytes());'
        + '\n            out.put("eviction_summary", core.internal().eviction().summary());')
    harness.write_text(text)

    smoke = json.loads((HERE / "file-smoke-plan.json").read_text())
    smoke["jobs"] = [
        {"name": "stripped-serial-point-rw", "case": "stripped-smoke", "repeat": 1,
         "variant": "serial-stripped", "params": {"threads": 4, "mode": "serial",
             "workload": "partitioned", "storage": "memory", "durable": False}},
        {"name": "stock-small-eviction", "case": "eviction-smoke", "repeat": 1,
         "variant": "stock", "params": {"threads": 4, "mode": "optimistic",
             "workload": "partitioned", "storage": "file", "durable": False,
             "keys": 16384, "startupBytes": 200000, "cacheBytes": 1000000}},
    ]
    smoke_path = HERE / "extended-smoke-plan.json"
    smoke_path.write_text(json.dumps(smoke, indent=2) + "\n")
    command(["python3", "-B", HERE / "run.py", "--builds", master,
             "--plan", smoke_path, "--out", RUNS / "extended-smoke", "--cooldown", "0"])
    for name in ["cost", "file", "eviction"]:
        command(["python3", "-B", HERE / "run.py", "--builds", master,
                 "--plan", HERE / f"{name}-plan.json", "--out", RUNS / name, "--quiet"])
    print("ALL FOLLOW-UP BENCHMARK SESSIONS PASSED", flush=True)


if __name__ == "__main__":
    main()
