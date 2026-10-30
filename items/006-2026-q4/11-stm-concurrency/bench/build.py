"""Build immutable-source STM benchmark variants in a disposable directory.

Production sources are never edited. The bypass variants are valid only for
serialized whole actions; RwBench rejects using them optimistically.
"""
import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(out, selected, commit_ref):
    out.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(["git", "rev-parse", commit_ref or "HEAD"], cwd=ROOT,
                                     text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--", "java"],
                                    cwd=ROOT, text=True).strip()
    if dirty and not commit_ref:
        raise RuntimeError("java/ has local changes: use a deliberate new snapshot")
    variants = {}
    for variant in selected:
        dest = out / variant
        if dest.exists():
            raise RuntimeError(f"refusing to replace existing build {dest}")
        dest.mkdir()
        archive = subprocess.Popen(["git", "archive", commit, "java"], cwd=ROOT,
                                   stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", str(dest)], stdin=archive.stdout,
                       check=True)
        archive.stdout.close()
        if archive.wait():
            raise RuntimeError("git archive failed")
        source = dest / "java/src/bergdb/core/Db.java"
        original = source.read_text()
        modified = original
        if variant != "stock":
            for statement in ["            stmCheckConflicts(t);",
                              "                stmRecordKeys(t);"]:
                if modified.count(statement) != 1:
                    raise RuntimeError("bypass anchor changed: " + statement)
                modified = modified.replace(statement,
                    statement[:len(statement) - len(statement.lstrip())]
                    + "// 006-11 experiment: serialized whole actions only.")
        if variant.endswith("no-warmup") or variant == "serial-stripped":
            for statement in ["        t.warmupGetData.pointerFollower = x.getData.pointerFollower;",
                              "        warmup(t);"]:
                if modified.count(statement) != 1:
                    raise RuntimeError("warmup anchor changed: " + statement)
                modified = modified.replace(statement,
                    "        // 006-11 experiment: serialized action, no warm-up.")
        if modified != original:
            source.write_text(modified)
        patch = "".join(difflib.unified_diff(
            original.splitlines(True), modified.splitlines(True),
            fromfile="a/java/src/bergdb/core/Db.java",
            tofile="b/java/src/bergdb/core/Db.java"))
        if variant == "serial-stripped":
            # This control supports only the benchmark's serialized byte[] point
            # reads/puts. Indexes, ranges, virtual keys and late key transforms are
            # outside its contract; snapshot selection itself is preserved.
            path = dest / "java/src/bergdb/pubimp/RwEnvironmentImp.java"
            before = path.read_text()
            pair = ("        long[] keySegments = Keys.toSegments(ikey);\n"
                    "        addReadHash(Keys.hash(keySegments));\n")
            if before.count(pair) != 2:
                raise RuntimeError("read hashing anchors changed")
            after = before.replace(pair, "")
            old = ("    private void addReadHash(long hash) {\n"
                   "        this.readHashes.add(hash);\n"
                   "    }")
            new = ("    private void addReadHash(long hash) {\n"
                   "        // 006-11 serial point-action experiment: no read tracking.\n"
                   "    }")
            if after.count(old) != 1:
                raise RuntimeError("read tracking anchor changed")
            after = after.replace(old, new)
            path.write_text(after)
            patch += "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                fromfile="a/java/src/bergdb/pubimp/RwEnvironmentImp.java",
                tofile="b/java/src/bergdb/pubimp/RwEnvironmentImp.java"))
            path = dest / "java/src/bergdb/core/Trans.java"
            before = path.read_text()
            old = "            t.writeKeyHashes = computeWriteHashes(t.kvs);"
            if before.count(old) != 1:
                raise RuntimeError("write hashing anchor changed")
            after = before.replace(old, "            t.writeKeyHashes = new long[0];")
            path.write_text(after)
            patch += "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                fromfile="a/java/src/bergdb/core/Trans.java", tofile="b/java/src/bergdb/core/Trans.java"))
        (dest / "experiment.diff").write_text(patch)
        manifest = {}
        for path in sorted((dest / "java").rglob("*")):
            if path.is_file():
                manifest[str(path.relative_to(dest))] = sha(path)
        (dest / "source-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        with (dest / "build.log").open("w") as log:
            subprocess.run(["sh", "build.sh"], cwd=dest / "java", stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        jar = dest / "java/build/bergdb.jar"
        variants[variant] = {"dir": str(dest), "jar": str(jar),
                             "jar_sha256": sha(jar),
                             "patch_sha256": sha(dest / "experiment.diff")}
        print("Built", variant, flush=True)
    info = {"commit": commit, "production_java_clean": not bool(dirty),
            "java_version": subprocess.run(["java", "-version"], text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True).stdout,
            "variants": variants}
    (out / "builds.json").write_text(json.dumps(info, indent=2) + "\n")
    print("BUILD_METADATA", out / "builds.json", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--commit", help="explicit tracked source snapshot; preserves local edits")
    parser.add_argument("--variants", nargs="+", default=["stock", "serial-bypass",
        "serial-bypass-no-warmup", "serial-stripped"], choices=["stock", "serial-bypass",
        "serial-bypass-no-warmup", "serial-stripped"])
    args = parser.parse_args()
    build(args.out or Path(tempfile.mkdtemp(prefix="bergdb-006-11-builds-",
                                          dir="/private/tmp")), args.variants, args.commit)
