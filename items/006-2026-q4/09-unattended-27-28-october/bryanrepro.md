# BryanRepro fails in level2.sh full (006-09, W13)

By Claude (Opus 5.5, Claude Code), 2026-10-27. Code in the clone
`/Users/f/fl/bench/006-09/w13` (from main at 2eaaa45; main's 49f99a1 has the
same `java/` and `lean/`).


## 1. The failure

`java/stress/level2.sh` full, step 6 (`BryanRepro 40 0 dir`):

    FAILED in cycle 39 of 40: bergdb.pub.util.DbFailedException: A read failed
    on the storage (the cause). ...
    Caused by: java.io.IOException: Cound not delete file .../00000000000030.bergdb.
        at bergdb.stream.FileStream$DbFile.delete(FileStream.java:987)
        at bergdb.stream.FileStream.runCuts(FileStream.java:410)

Every run on 005-46's code fails, in cycle 37 to 39: 5 of 5 in the
bisect's `w10/bryan-runs` (`b-eaec93e`, `b-e611709`, `b-a175840`, `h1`,
`p1`), and 3 of 3 here on 2eaaa45 (two of them with a FileStream that
prints, below). eaec93e's parent bf19075 passed twice (`b-bf19075`,
`b2-bf19075`). `level2.sh quick` passes: its 15 cycles end before the run's
first cut.


## 2. The cause

BryanRepro ends each cycle with `db.sync(); db.stop();`, and the next cycle
starts a database on the same directory at once. `stop()` returns before the
database is closed (005-35); a thread of its own closes it. Since 005-46,
`FileStream.pretruncate()` only takes the cut's files off the list, and a
thread of the stream's own (`FileStream-cut`) deletes them, with a directory
force after each; `FileStream.close()` waits for that thread, but here that
close runs in the background close that `stop()` began.

What happens, from a run with a FileStream that prints at open, cut, close
and a failed delete (the patch is `w13/runs/instrument.diff`; not committed;
times in ms):

    cycle 38      fs@405de81d [main] cut 60 files, first=00000000000000 last=00000000000950
    +74 ms        fs@405de81d [BufferedStream-consumer] close begins, cutThread=true
    +87 ms        cycle 39: fs@2548435e [main] open files=52 first=00000000000028
                      threads alive: Db-close-111 FileStream-cut
    +336 ms       fs@405de81d close: cut thread done
    +1253 ms      fs@2548435e [main] cut 46 files, first=00000000000028 last=00000000000950
    +1255 ms      fs@2548435e [FileStream-cut] DELETE FAILED 00000000000028 exists=false

1. The run's first cut comes in cycle 38 (37 in some runs): Reclaim cuts 60
   files at once, 0 to 950 (about 95 MB), in the cycle's last transactions.
   Its thread needs about 330 ms to delete them.
2. The cycle's `sync()` and `stop()` return within 90 ms. Cycle 39's
   FileStream lists the directory while the old thread is at file 28, and
   takes the 52 files left as its stream; the old database's close and cut
   threads are still alive.
3. The old thread deletes the rest of its 60 files, among them 46 that the new
   stream holds.
4. Reclaim's start finds the stream's first position below the cut in its
   table and cuts again (`Reclaim.initFromDb`, "A crash came between the
   table write and the cut"): the same 46 files. Its thread's first delete
   fails, as the file is gone (`exists=false`). That is the stream's failure,
   and the cycle's first read fails the database (P7).

A second printing run, with the call site of each cut: cycle 38's cut is
`Reclaim.cutIfDurable` in `transactionCompleted` of a put; cycle 39's is
`Reclaim.initFromDb` in `Db.startInner`, called from `BryanRepro.runJob`'s
start; then `DELETE FAILED 00000000000022 exists=false`.

Before 005-46, `pretruncate()` deleted the files on the thread of the commit
that made the cut, so they were gone when `sync()` returned, and the
background close only closed the files.


## 3. Whose fault

The test's. Two databases used the directory at once: the stopped one, still
closing, and the new one. `Database.stop()`'s Javadoc says that it returns at
once and that `close()` waits until the database is closed.

No data was at risk. The files that both threads delete lie wholly below the
cut that Reclaim's table marks, and that table is durable before the cut is
made (`Reclaim.cutIfDurable()`); the new database needs none of them, and
cuts them itself. It failed, as P7 wants when a file it holds vanishes.
BergDB itself has no guard against two databases on one directory: no lock
file; `DbFile.append` checks the file's length, which catches a second
writer's appends (Frans, 2013).


## 4. The fix

`BryanRepro.runJob` calls `db.close()` (`Database.close()`, 005-59) instead of
`db.stop()`, with a comment that says why; only `java/stress/BryanRepro.java`
changes. Commit 107abef in `/Users/f/fl/bench/006-09/w13`, on main's 49f99a1
(`git diff -w` the same as `git diff`).


## 5. Gates

In the clone, on 2026-10-27 between 18:46 and 19:06:

* Step 6 alone: 6 runs in a row pass (`Done: 40 cycles, 0 failures, 47 s` to
  49 s), and 3 more side by side while `level2.sh` ran (55 to 56 s).
* `level2.sh` full: `bryan: Done: 40 cycles, 0 failures, 48 s.` and
  `LEVEL 2 OK`.
* `before-commit.sh`: `BEFORE COMMIT OK (94 s)`; `java/src` is unchanged.


## 6. The same pattern elsewhere

Stress programs that start a database on a disk directory right after
`stop()`:

* `ReclaimReaders` with `disk=1` (level3 step 5, level4 step 4):
  `sync(STRONG); stop(); start(false)` with a new FileStream. A run with the
  printing FileStream, 12 rounds as in level3 full: 1,349 cuts, 318 starts,
  and no start with an old cut thread alive (one with an old close thread
  alive). Passes; not changed.
* `LargerThanMemory` (level4 step 6): `sync(STRONG); stop(); System.gc();`
  then a new FileStream. A printing run with level4 full's options: one cut,
  30 s before the restart, its thread long done; the restart's start saw no
  old thread alive. `LARGER THAN MEMORY OK`; not changed.
* `RestartStress` with `file=true` (level1, level2): no reclaim, so no cuts.
  Its restart without stop runs two databases on purpose, as a crash after
  sync.


## 7. For 005-46 and for Frans

* 005-46 needs no reopening. Its code does what its Javadoc says:
  `FileStream.close()` waits for the cut's thread, and `stop()` returns at
  once. Its gates left `level2.sh` and `level4.sh` to `night.sh`, at Frans's
  word; tonight's would have been the first `level2.sh` full on it. A line
  in 005-46 that points here is enough.
* To decide later, not done: (a) a sentence in `Database.stop()`'s and
  `Db.stop()`'s Javadoc: start a database on the same directory only after
  this one is closed; `close()` waits. (b) A lock file in the directory, so
  that a second database is refused, also from another process; P9 rules
  out a registry of directories in the JVM. (c) Not recommended: a
  `DbFile.delete` that takes a file already gone as deleted; it would hide
  this failure, not the two databases.
