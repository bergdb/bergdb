"""Join the clean main prefix and explicitly labelled resumed main suffix.

Original metadata, partial results and all raw session outputs are preserved.
The completion flag signals finish-runs.py only after every planned job passed.
"""
import datetime as dt
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
RUNS = Path("/private/tmp/bergdb-006-11-runs")
main = RUNS / "main"
resume = RUNS / "main-resume"
original = json.loads((main / "results-before-resume.json").read_text())
remaining = json.loads((resume / "results.json").read_text())
meta = json.loads((main / "metadata-interrupted.json").read_text())
rest_meta = json.loads((resume / "metadata.json").read_text())
assert rest_meta.get("finished_utc"), "resume not finished"
assert meta["harness_sha256"] == rest_meta["harness_sha256"]
assert meta["builds"]["commit"] == rest_meta["builds"]["commit"]
for result in original:
    result["run"]["source_session"] = "main"
for result in remaining:
    result["run"]["source_session"] = "main-resume"
    result["run"]["directory"] = "../main-resume/" + result["run"]["directory"]
all_results = original + remaining
names = [r["run"]["job"]["name"] for r in all_results]
planned = [j["name"] for j in json.loads((HERE / "main-plan.json").read_text())["jobs"]]
assert len(names) == len(set(names)) == 168
assert set(names) == set(planned)
assert all(r["verification"]["passed"] for r in all_results)
meta.update({"finished_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
             "completed_jobs": len(all_results),
             "completion_mode": "resumed-and-aggregated",
             "original_completed_jobs": len(original),
             "resumed_completed_jobs": len(remaining),
             "resume_idle_threshold_percent": rest_meta["idle_threshold_percent"],
             "resume_metadata": "../main-resume/metadata.json",
             "interruption": "90% CPU-idle gate refused next job; no correctness failure"})
(main / "results.json").write_text(json.dumps(all_results, indent=2) + "\n")
(main / "metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
print("ALL168 MAIN JOBS VERIFIED; clean/resumed", len(original), len(remaining))
