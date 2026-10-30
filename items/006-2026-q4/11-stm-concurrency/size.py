"""006-11: count identifiable STM code, excluding comments and test code.

Run from the BergDB root: python3 -B items/006-2026-q4/11-stm-concurrency/size.py
Uses 006-08's existing test stripper and code-line convention. This is a
source count, not a measurement of the code removable with another design.
"""
import importlib.util
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location(
    "size_strip", ROOT / "items/006-2026-q4/08-core-layer/strip.py")
stripper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stripper)


def count(source):
    return sum(bool(line.strip()) for line in stripper.mask(source).splitlines())


print("commit", subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip())
print("code lines after 006-08's test stripping; package/import/braces count")
base = ROOT / "java/src/bergdb"
for name in ["core/IKeyModSet.java", "core/KeyModSet.java",
             "core/RerunException.java", "core/Trans.java", "core/DbClock.java",
             "pub/Action.java", "pubimp/RwTransaction.java",
             "pubimp/RwEnvironmentImp.java"]:
    print(f"{count(stripper.strip((base / name).read_text())):4d}  {name}")

source = stripper.strip((base / "core/Db.java").read_text())
masked = stripper.mask(source)
for name in ["stmCheckConflicts", "stmRecordKeys", "warmup", "executeInner"]:
    match = re.search(r"(?m)^    private[^\n]*\b" + name
                      + r"\s*\([^)]*\)\s*\{", masked)
    if match is None:
        raise ValueError("method not found: " + name)
    start = masked.find("{", match.start())
    end = stripper.match_brace(masked, start) + 1
    print(f"{count(source[match.start():end]):4d}  Db.{name}")

total = files = 0
for path in sorted((ROOT / "java/src").rglob("*.java")):
    if (path.parent.name == "nanotest" or "Tester" in path.name
            or path.name in ["Pack.java", "PackForPub.java"]):
        continue
    files += 1
    total += count(stripper.strip(path.read_text()))
print(f"{total}  java/src production, {files} files (strip heuristic)")
