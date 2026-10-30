"""Run RwBench plans sequentially, preserving every JVM's output and identity.

Example: python3 -B run.py --builds /private/tmp/.../builds.json
  --plan main-plan.json --out runs/main --quiet

--quiet uses read-only macOS top samples; it requires permission to inspect
system activity. No production sources or existing benchmark data are edited.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def capture(command):
    proc = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
    return {"command": command, "returncode": proc.returncode, "output": proc.stdout}


def idle_sample():
    sample = capture(["/usr/bin/top", "-l", "2", "-s", "1", "-n", "0"])
    values = re.findall(r"([0-9.]+)% idle", sample["output"])
    sample["idle_percent"] = float(values[-1]) if values else None
    return sample


def main(args):
    builds = json.loads(args.builds.read_text())
    plan = json.loads(args.plan.read_text())
    if args.idle is None:
        args.idle = float(plan.get("minimum_idle_percent", 90))
    if args.out.exists():
        raise RuntimeError("choose a new output directory: " + str(args.out))
    args.out.mkdir(parents=True)
    metadata = {
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "builds": builds, "plan": plan,
        "harness_sha256": sha(HERE / "RwBench.java"),
        "runner_sha256": sha(Path(__file__)), "plan_sha256": sha(args.plan),
        "quiet_gate": args.quiet, "idle_threshold_percent": args.idle,
        "idle_threshold_rationale": plan.get("idle_threshold_rationale", "normal idle gate"),
        "cooldown_seconds": args.cooldown,
        "commands": [capture(["sw_vers"]), capture(["uname", "-a"]),
                     capture(["sysctl", "hw.model", "hw.memsize", "hw.ncpu",
                              "machdep.cpu.brand_string", "hw.perflevel0.physicalcpu",
                              "hw.perflevel1.physicalcpu"]),
                     capture(["pmset", "-g", "batt"]), capture(["java", "-version"])],
    }
    (args.out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    shutil.copy2(HERE / "RwBench.java", args.out / "RwBench.java")
    shutil.copy2(Path(__file__), args.out / "run.py")
    shutil.copy2(args.plan, args.out / "plan.json")
    classes = {}
    for variant in sorted({job.get("variant", "stock") for job in plan["jobs"]}):
        jar = Path(builds["variants"][variant]["jar"])
        if sha(jar) != builds["variants"][variant]["jar_sha256"]:
            raise RuntimeError("build changed: " + variant)
        dest = args.out / "classes" / variant
        dest.mkdir(parents=True)
        proc = capture(["javac", "--release", "17", "-Xlint:-options", "-cp", str(jar),
                        "-d", str(dest), str(HERE / "RwBench.java")])
        (dest / "compile.json").write_text(json.dumps(proc, indent=2) + "\n")
        if proc["returncode"]:
            raise RuntimeError("harness compile failed: " + variant)
        classes[variant] = str(dest)

    # Prevent idle sleep only while this runner is alive; do not change power settings.
    awake = subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    all_results = []
    try:
        for index, job in enumerate(plan["jobs"], 1):
            if sha(HERE / "RwBench.java") != metadata["harness_sha256"]:
                raise RuntimeError("harness changed during a session")
            variant = job.get("variant", "stock")
            params = dict(plan.get("defaults", {}), **job.get("params", {}))
            if variant != "stock" and params.get("mode") != "serial":
                raise RuntimeError("bypass build outside whole-action serialization")
            name = f"{index:03d}-{job['name']}"
            dest = args.out / name
            dest.mkdir()
            quiet = []
            if args.quiet:
                for trial in range(60):
                    sample = idle_sample()
                    quiet.append(sample)
                    if sample["idle_percent"] is None:
                        raise RuntimeError("cannot obtain CPU-idle sample")
                    if sample["idle_percent"] >= args.idle:
                        break
                    print(f"WAIT quiet {name}: {sample['idle_percent']:.1f}% idle", flush=True)
                    time.sleep(3)
                else:
                    (dest / "quiet.json").write_text(json.dumps(quiet, indent=2) + "\n")
                    raise RuntimeError("machine did not become quiet")
            (dest / "quiet.json").write_text(json.dumps(quiet, indent=2) + "\n")
            data = dest / "data"
            if params.get("storage") == "file":
                params["dir"] = str(data)
            jar = Path(builds["variants"][variant]["jar"])
            command = ["java", *plan.get("jvm_flags", ["-Xms512m", "-Xmx2g", "-XX:+UseZGC"]),
                       f"-Dbench.variant={variant}",
                       f"-Xlog:gc,safepoint:file={dest / 'gc.log'}:uptime,level,tags",
                       "-cp", str(jar) + ":" + classes[variant], "RwBench"]
            command.extend(str(key) + "=" + str(value).lower() if isinstance(value, bool)
                           else str(key) + "=" + str(value) for key, value in sorted(params.items()))
            info = {"job": job, "params": params, "command": command,
                    "started_utc": dt.datetime.now(dt.timezone.utc).isoformat()}
            (dest / "command.json").write_text(json.dumps(info, indent=2) + "\n")
            print(f"RUN {index}/{len(plan['jobs'])} {job['name']}", flush=True)
            started = time.monotonic()
            with (dest / "stdout.txt").open("w") as stdout, (dest / "stderr.txt").open("w") as stderr:
                try:
                    proc = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr,
                                          timeout=plan.get("timeout_seconds", 120))
                except subprocess.TimeoutExpired:
                    raise RuntimeError("JVM timed out: " + name) from None
            output = (dest / "stdout.txt").read_text()
            lines = [line[7:] for line in output.splitlines() if line.startswith("RESULT ")]
            if proc.returncode or len(lines) != 1:
                raise RuntimeError("JVM failed: " + name + "; " + (dest / "stderr.txt").read_text()[-3000:])
            result = json.loads(lines[0])
            if not result["verification"]["passed"]:
                raise RuntimeError("invariant failed: " + name)
            if result["variant"] != variant:
                raise RuntimeError("variant mismatch")
            result["run"] = {"job": job, "directory": name,
                             "elapsed_seconds": time.monotonic() - started,
                             "minimum_idle_before_run": quiet[-1]["idle_percent"] if quiet else None}
            (dest / "result.json").write_text(json.dumps(result, indent=2) + "\n")
            all_results.append(result)
            (args.out / "results.json").write_text(json.dumps(all_results, indent=2) + "\n")
            measured = result["measured"]
            print(f"OK {job['name']}: {measured['active_commits_per_second']:.0f}/s "
                  f"drained={measured['batch_commits_per_second']:.0f}/s "
                  f"attempts={measured['attempts_per_commit']:.4f} "
                  f"max={measured['latency']['max_ns']/1e6:.1f}ms", flush=True)
            if data.exists() and not args.keep_data:
                shutil.rmtree(data)
            time.sleep(args.cooldown)
        metadata["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        metadata["completed_jobs"] = len(all_results)
        (args.out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        print("ALL BENCHMARK JOBS PASSED", len(all_results), flush=True)
    finally:
        awake.terminate()
        awake.wait(timeout=5)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--builds", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--idle", type=float, help="override plan's idle threshold (normally90)")
    parser.add_argument("--cooldown", type=float, default=1)
    parser.add_argument("--keep-data", action="store_true")
    main(parser.parse_args())
