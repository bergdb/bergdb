#!/usr/bin/env python3
"""bergdb 005-81: adds the Db probes to a copy already patched by make-probe.py (never the repo's).

Usage: make-probe-db.py JAVA_DIR. Adds to Db two static hooks, called on the committing thread:
lockWaitProbe(ns), the wait for Db.writeLock in executeInner(), for every attempt; and
rerunReasonProbe(reason) just before a RerunException, 1 for a changed key, 2 for history
exhaustion (the read time older than KeyModSet's oldest bin, where modifiedAfter() answers
true for any key). Nothing else changes. Fails unless every anchor is found exactly once.
"""
import pathlib, sys

path = pathlib.Path(sys.argv[1]) / "src/bergdb/core/Db.java"
text = path.read_text()
edits = [
    ("    private final KeyModSet keyModSet;\n",
     "    private final KeyModSet keyModSet;\n\n"
     "    /** bergdb 005-81 probe build only: the wait for writeLock in executeInner(), ns. */\n"
     "    public static volatile java.util.function.LongConsumer lockWaitProbe;\n"
     "    /** bergdb 005-81 probe build only: 1 changed key, 2 history exhausted. */\n"
     "    public static volatile java.util.function.IntConsumer rerunReasonProbe;\n"),
    ("        writersWaiting.incrementAndGet();\n        synchronized (writeLock) {\n            writersWaiting.decrementAndGet();\n",
     "        writersWaiting.incrementAndGet();\n        long probeWait = System.nanoTime();\n"
     "        synchronized (writeLock) {\n            writersWaiting.decrementAndGet();\n"
     "            java.util.function.LongConsumer probeL = lockWaitProbe;\n"
     "            if (probeL != null) probeL.accept(System.nanoTime() - probeWait);\n"),
    ("            if (keyModSet.modifiedAfter(t.readTime, hash)) {\n                throw new RerunException(hash);\n",
     "            if (keyModSet.modifiedAfter(t.readTime, hash)) {\n"
     "                java.util.function.IntConsumer probeR = rerunReasonProbe;\n"
     "                if (probeR != null) probeR.accept(t.readTime < keyModSet.getFirstTime() ? 2 : 1);\n"
     "                throw new RerunException(hash);\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit("make-probe-db.py: anchor not found exactly once: " + old.strip()[:80])
    text = text.replace(old, new)
path.write_text(text)
print("make-probe-db.py: patched", path)
