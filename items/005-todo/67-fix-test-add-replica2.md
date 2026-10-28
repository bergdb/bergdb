005-67. Fix: `StorageManagerTester.testAddReplica2` fails about one run in twelve
================================================================================

Status: open. Kind: fix. Created 2026-10-28.

Registered at Frans's request (2026-10-28, through 006-10's session: the
test fails nights, and is to be fixed today), by Claude (Opus 5.5, Claude
Code).


The issue
---------

The unit test `StorageManagerTester.testAddReplica2`
(`java/src/bergdb/storage/`) fails now and then, "Expected 700, got 200."
It starts a `StorageManager` on a main `MemoryStream` of 700 bytes, adds a
replica, a `MemoryStream` of 200 bytes (`addReplica`, a buffer of 1,000
bytes and 10 ms), has a thread copy the main's bytes to it
(`syncReplica`), polls until the replica's status is `STATUS_ACTIVE`,
appends 100 bytes, asserts that both streams have 700 bytes, closes the
manager and asserts 800 for both.

Replication is experimental (005-11), but this is a unit test: it runs in
`java/before-commit.sh`, in the level scripts, and twice a night since
2026-10-28, in `before-commit.sh` (step 1 of `java/night.sh`) and in
`java/stress/core-build.sh unit f` (step 2, 005-56's follow-ups). A
failure fails a night step.

History:

* 2015-07-23: Frans's note in the test, "got non-reproducable unit test
  error, on Cissi": "Expected 800, got 1200", the replica's length after
  `close()`. In the same commit (`7c458d1` of the 2013 to 2017 history, the
  bundle in F1-007) he added the two assertions of 700 after the append.
* 2026-10-17, 001-02 (R8's change 2): `level3.sh` failed twice on it,
  "Expected 700, got 200", and "the storage tests fail 1 time in 12 also
  with `l34-base`'s jar"; R8's changes 3 and 4 (2026-10-17) and J6 and J7
  (2026-10-18) each had a gate run fail on it once, on a loaded machine.
  001-05, point 6: "four gates run it four times".
* 2026-10-22: the night's `before-commit.sh` failed on it, "Expected 700,
  got 200" (`java/build/night/2026-10-22-0200/`).
* 005-11's report (what the tests cover): the note of 2015 "records a
  failure on 2015-07-23 that was not reproduced".
* 2026-10-28: a run of `core-build.sh unit f` in 005-56's follow-ups
  failed on it.

The question is whether the test is wrong (it reads a length before the
asynchronous write it depends on, or assumes that a write has not happened
yet) or the code (a race in adding a replica: bytes lost or written twice,
a wrong confirmed length). 005-48's group commit (`e611709`: a sync starts
the flush) changed the timing of syncs; the test makes none.


Done when
---------

The cause is found and shown, with an instrumented copy or a forced
interleaving that makes the failure certain; the fault is fixed where it
is, in the code with a test that fails before if the code is wrong,
without weakening what the test checks; the test alone in a loop, at
least 10 times the runs that showed the failures before, has no failure,
also with the forced interleaving where it still applies;
`java/before-commit.sh`, `java/stress/core-build.sh unit f` and
`java/stress/level2.sh quick` pass; committed.


First step
----------

Run the test alone in a loop until it fails, to know the failure rate,
and read `StorageManager.addReplica`, `SynchingStorage.sync` and
`BufferedStream`'s flush against the test's assertions.
