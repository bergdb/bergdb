005-09. Fix the race that lets the node table name a released object
====================================================================

Status: done (2026-10-20). Kind: fix. Created 2026-10-19.


The issue
---------

`EvictionReaderTester.testReaderPausedInsideAFollow` fails now and then:
"INV-CAN: the node table names a snapshot of node N". Found in 005-02
([02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md), "Found on the
way"): the first `level3.sh` run there failed 1 of its 947 unit tests on
it, and passed when run again. So a gate can fail on it.

It is not 005-02's. Repeated under load (four JVMs per build beside four
busy loops, 150 runs each), the test failed once in 600 runs on the code
before 005-02 (`8c5a106`), with the same message, and in none of 600 with
005-02. The other three gates' unit runs passed it.

INV-CAN (the audit, `Audit.check`) says that the node table names canonical
objects only. The register row M31 and item 001's J1 and J3 rest on it
([level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md)): a release clears
the canonical flag and takes the table's entry, and a later read loads the
version from the slot's position.


A likely cause
--------------

From reading the code at `8c5a106`, not tested:

* A reader's follow of a stream pointer
  (`NodeCollection.followStreamPointer`) takes the canonical object from the
  node table (step 3), then swizzles the slot (step 4):
  `if (result.isCanonical()) cache.pointerCreated(predecessor, pointerIndex, result)`.
* `Cache3.pointerCreated` checks `to.isCanonical()` outside the table's
  per-id lock, and then, under the lock, enters the object when the table has
  no entry for the node.
* A sweep releases an object that only the node table holds without the
  slot's pointer lock (`Eviction`, `release` and the loop over the table's
  objects): it clears the canonical flag, then `Cache3.released` removes the
  entry under the per-id lock.

If the release comes between the reader's check and its insertion, the
table gets back an object that is no longer canonical: a snapshot. The test
opens that window: it pauses a reader just before step 4 (the
`firstTouchListener`), starts a sweep of every evictable object, and lets
the reader go after 500 ms; when the sweep is slowed by load, it is still
running then.

Readers and sweeps overlap like this outside tests too (Q8: readers do not
take the write lock; a sweep runs under it). What a snapshot in the table
leads to is not known: a reader does not take it (step 3 wants a canonical
object), but the writer's `makeCanonical` and later releases meet it.


The task
--------

1. Reproduce: a probe that runs the test in a loop under load (as 005-02
   did: about 1 in 600), or better a deterministic test that makes the
   release come between the check and the insertion (a hook in
   `Cache3.pointerCreated`, as the test's hook in the follow).
2. Confirm the cause, or find the real one. Look also for the other
   check-then-act steps on the canonical flag and the table: `makeCanonical`,
   `isBetter`, the loader, and `released` itself.
3. Find out what a snapshot in the table can do: wrong records, two
   canonical objects, a lost entry, or nothing but the audit's failure.
4. Fix it, for example: check the flag again under the per-id lock in
   `pointerCreated` (and clear it under the same lock in the release), so
   that the check and the insertion are one step against a release.
5. Say in docs/level4-alignment.md (a register row, or M31's) and in
   docs/levels.md what it was.


Done when
---------

* A test that fails without the fix and passes with it; the flaky test
  passes many times under load (thousands of runs, not one in 600).
* No stream changes: StreamDigest the same as R8's; `EvictionInvariance`
  prints its OK, and `java/before-commit.sh` prints `BEFORE COMMIT OK`.
* No loss of performance. Props (`bergdb.dev.props.Props`: MEM, CORE and
  SS) within noise of the code before the fix, in matched runs (ABBA, as in
  005-08); so too Core's `get`, `get4t`, `set` and `getmany`. The fix is on
  the readers' path (a follow's `pointerCreated`), so `get` and `get4t` matter
  most. `performance.sh`'s quick suite against the code before the fix gives
  no alerts.
* The register and docs/levels.md say what was found and fixed.


First step
----------

Write the deterministic test of step 1, and see whether it gives the
audit's message.


Size and order
--------------

S, if the cause is the one above. Independent of the other entries; it
touches `Cache3`, which 005-08 changed (the maps, not `pointerCreated`).
005-07 (synchronization) should list it among the races found.


Outcome
-------

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-20, at
Frans's request ("Fix 005-09"). Other sessions worked on bergdb at the same
time (a nightly run, and 005-13's buffer time sweep), so the builds, the
checks and the measurements ran in a local clone of `8039d4a` with the
change, and the measurements waited until the machine was free of the other
sessions' runs. Before it was copied here, the clone was brought to
`f2a1c18` (005-13's buffer time, which touches other files) and
`before-commit.sh` was run again there. Left for Frans to commit.

**The cause** is the one above. A reader's follow of a stream pointer
(`NodeCollection.followStreamPointer`, step 4) calls
`Cache3.pointerCreated` for the canonical object it took from the node
table. `pointerCreated` read the canonical flag, then took the table's
lock and entered the object if the table had no entry for the node. A
sweep, which runs under the write lock that readers do not take, released
an object that only the table held without the reader's pointer lock: the
flag cleared, then `Cache3.released` removed the entry under the table's
lock. A release between the reader's read of the flag and its lock left the
table without an entry, and the reader then entered the released object, a
snapshot.

**The other check-then-act steps** on the flag and the table (task, step 2):

* `makeCanonical`, `register`, `resolvePointers`, `linkToCanonical` and the
  writer's follower run in the writer (or at startup), under the write lock,
  as every sweep does (the transaction's end, the capacity controller, a
  reader's load-triggered sweep, `evictNow`); so no release comes between
  their steps.
* `isBetter` runs under the table's lock, in `pointerCreated` and
  `register`; it reads the old object's flag, which a release now clears
  under that lock too.
* The loader (step 3) reads the table's object under the lock and its flag
  after it. A release in between gives the reader a released object, which
  is the version at its position: the race of a reader and a release that
  `testReleasedObjectPutIntoASlot` already tests (Q8; level4-alignment.md,
  7.4), and which stays allowed. Only the entry into the table was wrong.
* `released` itself: it compares the entry with the object under the lock.
  The flag was cleared before, outside the lock; it is now cleared inside.

**What a snapshot in the table did** (task, step 3), measured with the
deterministic test on the code before the fix, with ten more transactions
after the race in each of four databases: the audit failed ("INV-CAN: the
node table names a snapshot of node N"); in one of the four, the audit
after each of the next three transactions failed the same way, until the
writer reached the node and made the object canonical again; in the other
three the next transaction did that. The stream was the same byte for byte
as without eviction, and every read the same. By reading the code: while
the snapshot is in the table, a reader that follows a stream pointer to
the node does not take it (it wants a canonical object) and loads the
version from the stream; the writer's `makeCanonical` replaces it or makes
it canonical, so there is still one canonical object per node; a later
release of it only removes the entry. So: no wrong records, no two
canonical objects, no lost entry; a failed audit, and loads that the table
could have saved.

The criteria of "Done when", point by point:

* **A test that fails without the fix and passes with it: met.**
  `EvictionReaderTester.testReleaseBeforeTheTableEntry`: a hook in
  `Cache3.pointerCreated` (`Cache3.EntryListener`, for tests only, just
  before the table's lock) runs a sweep of every detachable object in the
  reader's thread, which holds the pointer lock (reentrant), so the release
  comes exactly in the window. Four databases; with the hook and the test on
  the code before the fix it fails at the first, "INV-CAN: the node table
  names a snapshot of node 35387"; with the fix it passes.
* **The flaky test under load: met, with a caveat.** [probe.sh](09-fix-node-table-snapshot-race/probe.sh)
  ([Probe009.java](09-fix-node-table-snapshot-race/Probe009.java)): four
  JVMs per build at once, both builds at once, beside four busy loops.
  The f-test version (`testReaderPausedInsideAFollowF`: three tries, 500
  ms for the sweep; the unit test of 005-02's day, before 006-03 split it):
  before the fix 1 failure in 2,000 runs, with the audit's message; with
  the fix 0 in 2,000. Today's unit test (one try, 50 ms): 0 in 6,000 on
  both builds, so it hardly meets the race on this machine. In all, 8,000
  runs with the fix and no failure. The window is short (a few
  instructions), so the probe shows the rate only roughly; the
  deterministic test is the evidence that the race is gone.
* **No stream changes: met.** StreamDigest `all` against R8's digests
  (`java/build/digest/r8-c4.txt`): `DIGESTS IDENTICAL (36 of 36)`.
  `level4.sh quick`: EvictionInvariance OK in its three configurations
  (node8, node8-r, rec-every1; 0 audit failures), and `LEVEL 4 OK`.
  `before-commit.sh`: `BEFORE COMMIT OK` (934 unit tests, 59 f-tests), on
  `8039d4a` and on `f2a1c18` with the change.
* **No loss of performance: met.** Props, eight runs a build in ABBA
  order (four blocks), medians and ranges, the same for both builds:

  | Measure | Before | After |
  |---|---|---|
  | MEM, bytes per KV | 191 (191–191) | 191 (191–192) |
  | CORE | 0.285 (0.28–0.29) | 0.285 (0.28–0.29) |
  | `get` | 0.26 (0.26–0.26) | 0.26 (0.23–0.26) |
  | `get4t` | 0.32 (0.32–0.33) | 0.32 (0.32–0.33) |
  | `set` | 0.25 (0.25–0.26) | 0.25 (0.25–0.28) |
  | `getmany` | 0.31 (0.31–0.31) | 0.31 (0.31–0.32) |
  | SS | 1.50 | 1.50 |

  `performance.sh ab` with the quick suite, the code before the fix
  against the fix: `NO ALERTS`; every throughput within 1.1 percent. It
  asks to explain one thing, the slowest commit of `w-uni-1k-inf` (30 to
  65 ms, with 81 to 113 percent variation between runs: a maximum, from the
  writes, not the readers' path). The readers' path has no new lock: the
  flag is still read first without it, and again only where the lock was
  taken anyway.
* **The register and docs/levels.md: met.** M31's row and section 7.4 in
  [level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md); docs/levels.md,
  "Bugs found by the alignment of Levels 3 and 4", 3, and its Level 4
  readers.


The change
----------

* [Cache3.java](../../java/src/bergdb/core/Cache3.java): `pointerCreated`
  reads the flag again under the table's lock and returns if the object is
  no longer canonical; `released` clears the flag under the same lock, so
  that the check and the entry are one step against a release. The test
  hook `EntryListener` (package-private, null unless a test sets it).
* [Eviction.java](../../java/src/bergdb/core/Eviction.java): the two
  releases no longer clear the flag themselves; `Cache3.released` does.
* [EvictionReaderTester.java](../../java/src/bergdb/core/EvictionReaderTester.java):
  `testReleaseBeforeTheTableEntry`.

No record changes, no format change.


Files
-----

In [09-fix-node-table-snapshot-race/](09-fix-node-table-snapshot-race/):

* `probe.sh`, `Probe009.java`: the flaky test under load;
  `probe-f.txt`, `probe-unit.txt`: its two runs.
* `run.sh`: 005-08's Props runner, for this item; `runs/`: the sixteen
  Props runs; `props-ab.txt`: their summary.
* `perf-quick-ab.txt`: the output of `performance.sh ab` (its sessions were
  in the clone and are not kept).
* `digest-fix-0509.txt`, `digest-compare.txt`: StreamDigest, the fix's
  jar with `pre-0509`'s stress classes, against R8's.
* `level4-quick.txt`, `before-commit.txt`: the checks, in the clone.
