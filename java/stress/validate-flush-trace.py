#!/usr/bin/env python3
"""Validate the probe's native syscall trace; no simulated force events."""
import os
import re
import sys

platform = sys.argv[2] if len(sys.argv) > 2 else "macos"
events = []
if platform == "linux":
    unfinished = {}
    for seq, line in enumerate(open(sys.argv[1], encoding="utf-8"), 1):
        process = re.match(r"^(\d+)\s+(.*)$", line.strip())
        if not process:
            continue
        pid, call = process.groups()
        if "<unfinished ...>" in call:
            unfinished[pid] = call.split("<unfinished ...>")[0]
            continue
        if call.startswith("<...") and "resumed>" in call:
            call = unfinished.pop(pid, "") + call.split("resumed>", 1)[1]
        result = re.search(r"= (-?\d+)", call)
        if not result:
            continue
        rc = int(result.group(1))
        if call.startswith("openat(") and "O_CREAT" in call:
            name = re.search(r'"([^"\n]+\.bergdb)"', call)
            if name:
                path = os.path.realpath(name.group(1))
                if not any(e[1] == "CREATE" and e[5] == path for e in events):
                    events.append((seq, "CREATE", "file", 0 if rc >= 0 else rc, 0, path))
        elif call.startswith(("fsync(", "fdatasync(", "write(")):
            name = re.search(r"<([^>]+)>", call)
            if not name:
                continue
            path = os.path.realpath(name.group(1))
            if call.startswith("write("):
                amount = re.search(r", (\d+)\)\s*=", call)
                if path.endswith(".bergdb") and amount:
                    events.append((seq, "WRITE", "file", rc, int(amount.group(1)), path))
            else:
                kind = "file" if path.endswith(".bergdb") else "dir"
                op = "FSYNC" if call.startswith("fsync(") else "FDATASYNC"
                events.append((seq, op, kind, rc, 0, path))
        elif call.startswith(("unlink(", "unlinkat(")):
            name = re.search(r'"([^"\n]+\.bergdb)"', call)
            if name:
                events.append((seq, "UNLINK", "file", rc, 0, os.path.realpath(name.group(1))))
else:
    for line in open(sys.argv[1], encoding="utf-8"):
        match = re.fullmatch(r"(\d+) (\w+) (file|dir) rc=(-?\d+) n=(\d+) path=(.*)\n", line)
        if not match:
            raise SystemExit("Malformed native trace: " + line)
        seq, op, kind, rc, amount, path = match.groups()
        events.append((int(seq), op, kind, int(rc), int(amount), os.path.realpath(path)))
force_operation = "FSYNC" if platform == "linux" else "F_FULLFSYNC"

created, written, forced, directories = {}, {}, {}, {}
data_forces = directory_forces = writes = deletions = 0
last_delete = 0
last_delete_directory = None
for seq, op, kind, rc, amount, path in events:
    if op == "CREATE":
        assert rc == 0
        created[path] = seq
    elif op == "WRITE":
        assert rc == amount and amount > 0, (op, rc, amount, path)
        written[path] = seq
        writes += 1
    elif op == force_operation:
        assert rc == 0, ("full force failed", path, rc)
        if kind == "dir":
            directories[path] = seq
            directory_forces += 1
        elif path.endswith(".bergdb"):
            forced[path] = seq
            data_forces += 1
    elif op == "FSYNC" and platform != "linux":
        raise AssertionError("Unexpected weaker fsync fallback in the local macOS probe: " + path)
    elif op == "FDATASYNC":
        raise AssertionError("Expected fsync for force(true), found fdatasync: " + path)
    elif op == "UNLINK":
        assert rc == 0
        if last_delete:
            assert directories.get(last_delete_directory, 0) > last_delete, "unforced prefix deletion before next unlink"
        survivors = [p for p in created if p > path]
        assert survivors, ("no surviving replacement file", path)
        for survivor in survivors:
            assert forced.get(survivor, 0) > written.get(survivor, 0), survivor
            assert directories.get(os.path.dirname(survivor), 0) > created[survivor], survivor
        created.pop(path, None)
        deletions += 1
        last_delete = seq
        last_delete_directory = os.path.dirname(path)

for path, seq in written.items():
    assert forced.get(path, 0) > seq, ("unforced append", path)
assert data_forces >= 8 and directory_forces >= 4 and writes >= 4 and deletions >= 2
assert directories.get(last_delete_directory, 0) > last_delete, "last deletion was not forced"
print(f"NATIVE FLUSH ORDER OK: {writes} writes, {data_forces} successful file {force_operation}, "
      f"{directory_forces} successful directory {force_operation}, {deletions} deletions")
