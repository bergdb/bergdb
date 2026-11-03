015-24. Fix: a refused open through another class loader releases the active directory lock
===========================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by
Frans Lundberg.

For 2026.2: new in this release.

What: Two class loaders that each load bergdb.jar (two webapps, a hot redeploy): the second `start()` on the same directory is refused, and its cleanup drops the first database's directory lock, so another process could then open the directory and write beside it. New in 2026.2 (005-63).

Source: review R2, R2-F1 (016-06/R2, items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R2-F1), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R2-F1, made a test.


State
-----

2026-11-03, 20:01: fixed in `/Users/f/fl/bench/016/015-24/repo`, with two
tests, gated (`BEFORE COMMIT OK`); the hand-off for the review is in
`/Users/f/fl/bench/016/015-24/handoff/` (016-05, section 4, step 1).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 19:46 to 20:01, in `/Users/f/fl/bench/016/015-24/repo` from
`main` at `c657764`:

* **The cause**, as R2-F1 and verify-1 have it. `LOCKED_DIRS` is a static
  field, so each class loader that loads `FileStream` has a set of its
  own. A copy in another loader finds its set empty, opens `bergdb.lock`,
  and `tryLock` throws `OverlappingFileLockException`: the JDK's table of
  locks belongs to the JVM. The handler closes the channel, and on macOS
  and Linux that close drops the process's lock, which the first copy's
  stream holds through its own channel (POSIX record locks belong to the
  process and the file; 005-63, Outcome). Another process could then
  open the directory beside the first database.
* **The fix**, `stream/FileStream.java`: the JVM's system properties hold
  the directories of every copy of the class, one property per locked
  directory, `bergdb.lock.` and `lockKey()` (on macOS and Linux the
  directory's device and inode, as `(dev=...,ino=...)`), whose value is
  the holder's copy (`COPY`, unique among the JVM's copies: `nanoTime()`
  and an identity hash at class load). `lockDir()`, after `LOCKED_DIRS`
  and before the lock file is made or opened, puts it with
  `putIfAbsent`: if another copy's value is there, the open is refused
  with `DirectoryInUseException` ("... in this JVM, in another class
  loader ..."), without touching the file. A failed open removes the
  property with `remove(name, COPY)`, so only its own; `unlockDir()`
  removes it after it has closed the lock file and before the directory
  leaves `LOCKED_DIRS`. Within a copy nothing changes: `LOCKED_DIRS`
  refuses first, with the same message. This copy's own value, which
  `LOCKED_DIRS` does not hold, refuses nothing: a program that puts back
  older system properties (as some test frameworks do) can leave it, and
  a refusal then would last until the JVM ends.
* **Why the system properties.** The registry must be the JVM's, seen
  by every class loader, with an atomic test-and-set, and it must not
  open `bergdb.lock`. The JDK's lock table is the JVM's, but it is
  reached only through a channel of the file, whose close is the fault.
  A channel kept open instead is closed by its `Cleaner` once
  unreachable, at a time no one chooses. The platform MBean server would
  do, at the price of `java.management` and its start. A second lock
  file changes the directory's files. `Properties.putIfAbsent` and
  `remove(key, value)` are atomic (a `ConcurrentHashMap` inside, since
  JDK 9), and `System` is loaded by the bootstrap loader, so every copy
  sees the same object. Global state, as `LOCKED_DIRS` is: the class
  Javadoc says so, beside 010-P9.
* **What is left.** A program that replaces the system properties
  (`System.setProperties`) while a database is open loses the refusal
  across class loaders; the class Javadoc says so. A lock on
  `bergdb.lock` that other code in the JVM takes (not a `FileStream`)
  still meets the `OverlappingFileLockException` path, whose close drops
  that lock for other processes, as before; nothing in `FileStream` can
  avoid it (see the `Cleaner` above).
* **`common/SeedGenerator.java`**: `addMachineData()` lists the system
  properties' names, then reads each value; a property that a close
  removes meanwhile gave `null`, and `writeUTF(null)` a
  `NullPointerException` in `DatabaseId`'s or `CryptoKey`'s seed. It now
  skips a value that is gone.
* **The tests.** `FileStream.testLockAcrossClassLoaders`, an f-test (it
  needs a child process: a process's own locks never refuse it, so only
  another process sees whether the lock is still held; each child JVM
  takes about 0.1 s, too slow for the unit tests' 100 ms): a
  `URLClassLoader` over `FileStream`'s code source (`build/bergdb.jar`
  in the gate; parent the platform loader) loads a second copy of the
  class. Each copy is refused on a directory that the other holds, a
  child's open (`runLockChild`, as in `testLockAcrossProcesses`) is
  refused after each refusal, the first copy still appends, and after
  both closes this copy opens again. 0.28 s. On the base it fails at the
  first child: "Expected 'refused', got 'opened'.", the fault itself.
  `FileStream.testOtherCopyRefusedFirst`, a unit test (20 ms): another
  copy's property refuses the open before `bergdb.lock` is made, and
  stays; this copy's own value refuses nothing, and the close removes
  it. Mutations (`/Users/f/fl/bench/016/015-24/mut/mutate.py`): M1, no
  check of the property (the base's behaviour): both fail, the f-test as
  on the base; M2, this copy's own value refuses too: the unit test
  fails; M3, `unlockDir()` leaves the property: both fail.
* **The gate**, `java/before-commit.sh`, 19:58:48 to 20:00:32: `BEFORE
  COMMIT OK (104 s)`, 1,124 unit tests and 79 f-tests.
* Not changed: the stream format, the lock file (its name, text and
  locked byte), the Pub API, `docs/levels.md`. Not in this patch:
  010-01's list under P9, "Where BergDB stands", names `LOCKED_DIRS`
  only; a line on the system properties beside it is for the
  coordinator.

2026-11-03, 20:05, by the coordinator (016-05, H5): reviewed, no faults.
`putIfAbsent` on the system properties is atomic across the JVM's copies
of the class; a refusal by `LOCKED_DIRS` comes before the property and
leaves it; a failed open and a close remove only this copy's value. A
copy of an older BergDB (2026.1) does not know the property: two
versions in one JVM keep the old fault, as the class Javadoc says. The
mechanism (a system property per locked directory) is a design choice
made tonight; it is on Frans's list in 016-02, section 7.
