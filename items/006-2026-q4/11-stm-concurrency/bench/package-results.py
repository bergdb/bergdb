"""Preserve checked results, exact sources and raw logs of this experiment."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RUNS = Path("/private/tmp/bergdb-006-11-runs")
OUT = HERE / "results"
sessions = {"main": 168, "cost": 60, "file": 36, "eviction": 12}
metadata, checks = {}, {}
for name, expected in sessions.items():
    result = json.loads((RUNS / name / "results.json").read_text())
    assert len(result) == expected
    assert len({r["run"]["job"]["name"] for r in result}) == expected
    assert all(r["verification"]["passed"] for r in result)
    assert all(r["verification"]["sum_counters"]
               == r["warmup"]["commits"] + r["measured"]["commits"] for r in result)
    assert all(sum(r["measured"]["per_worker_commits"]) == r["measured"]["commits"]
               for r in result)
    assert all(r["variant"] == "stock" or r["mode"] == "serial" for r in result)
    assert all(r["run"]["minimum_idle_before_run"] >=
               (90 if name == "main" and r["run"].get("source_session") == "main" else 80)
               for r in result)
    (OUT / f"{name}-results.json").write_text(json.dumps(result, indent=2) + "\n")
    metadata[name] = json.loads((RUNS / name / "metadata.json").read_text())
    distinct = {(r["run"]["job"]["case"], r["variant"], r["mode"], r["threads"])
                for r in result}
    assert len(distinct) * 3 == len(result)
    checks[name] = {"unique_checked_runs": len(result),
                    "distinct_configurations": len(distinct),
                    "all_counter_invariants_passed": True,
                    "all_stored_computations_verified": True,
                    "worker_totals_match": True,
                    "experimental_variants_serial_only": True,
                    "idle_thresholds_checked": True}
assert sum(c["unique_checked_runs"] for c in checks.values()) == 276
assert sum(c["distinct_configurations"] for c in checks.values()) == 92
metadata["main-resume"] = json.loads((RUNS / "main-resume/metadata.json").read_text())
(OUT / "environments.json").write_text(json.dumps(metadata, indent=2) + "\n")
(OUT / "verification.json").write_text(json.dumps(checks, indent=2) + "\n")
builds = json.loads((RUNS / "all-builds.json").read_text())
(OUT / "builds.json").write_text(json.dumps(builds, indent=2) + "\n")

# A separate summary of the original >=90%-idle prefix checks that the
# conclusions do not depend on replacing clean runs with background-load runs.
clean = [r for r in json.loads((RUNS / "main/results.json").read_text())
         if r["run"].get("source_session") == "main"]
assert len(clean) == 141
clean_dir = Path(tempfile.mkdtemp(prefix="bergdb-006-11-clean-", dir="/private/tmp"))
(clean_dir / "results.json").write_text(json.dumps(clean))
subprocess.run(["python3", "-B", str(HERE / "summarize.py"), "--session",
                "main=" + str(clean_dir), "--out", str(clean_dir / "summary")], check=True)
for suffix in ["json", "md"]:
    shutil.copy2(clean_dir / f"summary/summary.{suffix}", OUT / f"clean-main-summary.{suffix}")

with tarfile.open(OUT / "raw-evidence.tar.gz", "w:gz", compresslevel=6) as archive:
    for session in ["main", "main-resume", "cost", "file", "eviction", "extended-smoke"]:
        for path in sorted((RUNS / session).rglob("*")):
            if path.is_file() and path.suffix != ".class" and "data" not in path.relative_to(RUNS / session).parts:
                archive.add(path, arcname="sessions/" + str(path.relative_to(RUNS)), recursive=False)
    smoke = Path("/private/tmp/bergdb-006-11-file-smoke")
    for path in sorted(smoke.rglob("*")):
        if path.is_file() and path.suffix != ".class" and "data" not in path.relative_to(smoke).parts:
            archive.add(path, arcname="sessions/file-smoke/" + str(path.relative_to(smoke)), recursive=False)
    for name, build in builds["variants"].items():
        directory = Path(build["dir"])
        for filename in ["experiment.diff", "source-manifest.json", "build.log"]:
            archive.add(directory / filename, arcname=f"builds/{name}/{filename}", recursive=False)
        if name == "stock":
            for path in sorted((directory / "java/build/before-commit").glob("*.txt")):
                archive.add(path, arcname="baseline/" + path.name, recursive=False)
    for path in sorted(HERE.iterdir()):
        if path.is_file() and path.suffix in [".py", ".java", ".json", ".patch", ".txt", ".md"]:
            archive.add(path, arcname="experiment/" + path.name, recursive=False)
    archive.add(HERE.parent.parent / "11-stm-concurrency.md",
                arcname="report/006-11.md", recursive=False)

with (OUT / "SHA256SUMS").open("w") as file:
    for path in sorted(OUT.iterdir()):
        if path.is_file() and path.name != "SHA256SUMS":
            file.write(hashlib.sha256(path.read_bytes()).hexdigest() + "  " + path.name + "\n")
print("Packaged276 checked runs, clean-prefix summary, source diffs and raw evidence")
