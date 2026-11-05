#!/usr/bin/env python3
"""bergdb 005-81: makes the probe build's source from a copy of the stock source.

Usage: make-probe.py JAVA_DIR, the java/ directory of a git archive copy (never the repo's).
Adds to RwTransaction.executeRw() a static hook, retryProbe, called on the caller's thread
after each retry sleep with {runCount, requestedMs, sleptNs, failedExecuteNs}:
failedExecuteNs is the refused Db.execute() call, sleptNs the measured Thread.sleep().
The retry policy itself is unchanged. Fails unless every anchor is found exactly once.
"""
import pathlib, sys

path = pathlib.Path(sys.argv[1]) / "src/bergdb/pubimp/RwTransaction.java"
text = path.read_text()
edits = [
    ("    public static Trans executeRw(RwEnvironmentImp env, ConnectionImp connection, RwTransaction rw) {\n",
     "    /** bergdb 005-81 probe build only: {runCount, requestedMs, sleptNs, failedExecuteNs}. */\n"
     "    public static volatile java.util.function.Consumer<long[]> retryProbe;\n\n"
     "    public static Trans executeRw(RwEnvironmentImp env, ConnectionImp connection, RwTransaction rw) {\n"),
    ("                connection.getDb().execute(trans);      // Writes are executed.\n",
     "                probeExecute = System.nanoTime();\n"
     "                connection.getDb().execute(trans);      // Writes are executed.\n"),
    ("            } catch (RerunException e) {\n",
     "            } catch (RerunException e) {\n"
     "                long probeRefused = System.nanoTime();\n"),
    ("                    Thread.sleep(sleepTime);\n",
     "                    long probeSleep = System.nanoTime();\n"
     "                    Thread.sleep(sleepTime);\n"
     "                    java.util.function.Consumer<long[]> p = retryProbe;\n"
     "                    if (p != null) p.accept(new long[] {runCount, sleepTime,\n"
     "                            System.nanoTime() - probeSleep, probeRefused - probeExecute});\n"),
    ("        Trans trans;\n        \n        while (true) {\n",
     "        Trans trans;\n        long probeExecute = 0;\n        \n        while (true) {\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit("make-probe.py: anchor not found exactly once: " + old.strip())
    text = text.replace(old, new)
path.write_text(text)
print("make-probe.py: patched", path)
