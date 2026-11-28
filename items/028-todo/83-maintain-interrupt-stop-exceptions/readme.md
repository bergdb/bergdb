028-83. Fix: maintain() spins with the interrupt flag set; a write at a stop throws StreamIoException; e3 seed 101's restart changed the first available time
==========================================================================================================================================================

Status: open (built and gated on the branch `028-83`, to land).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: the open question and the product findings of the user apps of
031-08, part A (`08-user-apps/apps-a.md`, section 4), in this order:

1. **e3 seed 101's FAIL** (soak 1): "round 234: the restart changed the
   first available time", at a restart with no build running; its cause
   was not shown by the record (section 3). A restart must change
   nothing the user reads (010-01, P2; `Database`'s Javadoc: "A restart
   after stop() or close() keeps the time").
2. **UA-9** (S4): a `maintain()` call whose thread has its interrupt
   flag set spins on a core while it gives way to commits
   (`Db.giveWayToWriters`; the probe `MaintainSpins`: 3,961 ms of CPU in
   5 s).
3. **UA-10 and UA-2**: a put, a `w().execute()` or a `maintain()` call
   at a stop throws StreamIoException ("Storage is closing."), from
   `Db.warmup` and from `maintain()`'s sync of a cut's table, where
   `Database.stop()` and `maintain()` name IllegalDbStateException;
   nothing is written.
4. **UA-8** (a question): `maintain()` grows a tiny new database from 704
   to 199,728 bytes and keeps it (the probe `FreshMaintain`).

Why: a FAIL of a restart is priority 1 until explained; UA-9 burns a
core in an application that interrupts its threads at shutdown; UA-10
and UA-2 give an exception that the Javadoc does not name; UA-8 is a
cost that no document states.

Frans: none.

Done when: e3 seed 101's cause is found and judged (product bug, a
document, or the app); UA-9 waits without spinning, the flag kept, with
a test that fails before, by a count; UA-10 and UA-2 give the documented
exception with the cause kept, with tests that fail before; UA-8 is
explained and stated; `java/before-commit.sh`, `java/stress/level3.sh`,
`java/stress/apps.sh quick` and the apps of section 3 pass.

First step: the kept data of the FAIL, the app's code at 621c7a53, and
a run of that code with the times printed at each restart.

Found by: the user apps of 031-08, part A (2026-11-28).


1. e3 seed 101: a background commit before close(), not the restart
--------------------------------------------------------------------

**What happened.** The app as it ran at 07:18 (its code at `621c7a53`)
read `getFirstAvailableLookupTime()` before `close()` and compared it
with the time after the start. Its run is deterministic but for the
interleaving of the database's own threads: the reruns give the same
first available times at rounds 99 and 199 as the FAIL's log. A copy of
that code, which prints at each restart the time before `close()`,
after it and after the start, and the database's threads named
`Index*`, failed at round 234 in 2 of 3 runs on 2026-11-28, F53 under a
load of 20 (the other passed): the thread `IndexCleanup-ix1-...` (the
removal of the entries of ix1, deleted after the restart of round 221)
was alive; the time moved from 17723234481991529 to 17723234555358742
after the app's read, in one run before `close()` began and in the
other during it, and the start gave exactly the time that `close()`
left, in all 28 and 23 restarts of the runs.

**The cause.** `IndexManager.startCleanup` removes a deleted index's
entries in a daemon thread of its own, in transactions of 100 keys and
one that deletes the marker, with pauses between them. Each such commit
is a commit: since 031-06 its record carries reclaim's maintenance, and
it decides a cut when one is due. The app had moved its test clock by up
to R/3 at the round's start, so the cleanup's next commit found a done
iteration older than the retain duration and cut: the time moved with no
commit of the application's, between its read and `close()`. `IndexBuilderImp`'s build steps
commit the same way (seed 105's FAIL, a restart during a build; the app's
fix of `04f69f6d`).

**The start moves nothing.** `Reclaim.initFromDb` takes the first
available time from the row marked cut in the table that the deciding
record stored, the same row whose `tEnd` `applyCut` gave the running
database; `close()` writes nothing (010-01, P2), so the time after
`close()` is the time after the start. A cut that the record decided
and `close()` left unmade (031-08, UB-1 of part B: the files stay until
the next start) is made by the start (`pretruncate(firstPos)`), which
moves no time. The probe `probes/CleanupCutProbe.java` sets the order:
a database with a retain duration of 1 s brought to rest by
`maintain()` calls with the clock standing; an index deleted, its
cleanup held at its first step (IndexManager's test hook); the clock
moved 3 s; the time read; the cleanup let go: its commits move the time
from 17723232379200000 to 17723232400000020 (the stream kept from
1,888,104 to 943,168 bytes), with no commit of the application's;
`close()` moves nothing; the time right after the Core's start
(`DatabaseImp.testHookAfterStart`, before the index manager resumes any
job) and after the start is the same. Three runs, PROBE OK each.

**Judgment: the app's, and a document that misled.** No product bug:
the restart keeps the time. The app read the time before `close()`
while the database's own commits could still run. The Javadoc misled
it: `getFirstAvailableLookupTime()` said "without commits it stays,
also over a restart", and `deleteIndex()` "its entries are removed in
the background", with nothing on those removals being commits that move
the time, or on a start resuming them.

* **The Javadoc** (`Database`): `getFirstAvailableLookupTime()` says
  that the commits include the database's own for the user indexes,
  the build's steps and the removal of a deleted index's entries, which
  a stop ends and the next start resumes, so that the time can move
  with no commit of the application's, between a read and `close()` and
  right after a start; and that the start gives the time that the
  getters give after `close()`. `deleteIndex()` says that the removal
  runs in transactions of the database's own, resumed by the next
  start, which may let reclaim cut.
* **The app** (`java/stress/apps/e3-index-reclaim`): `04f69f6d` reads the
  time after `close()` and allows a later time after a start that
  resumed a build or followed a deletion since the last restart. A
  removal that a start resumed can run past the next restart too (it
  ends only when its marker is deleted; the Pub API does not tell when),
  and its commit at that start could cut: e3 then failed wrongly. Since
  028-83 a deletion allows a later time at every later restart
  (`deletedOnce`); an earlier time is a FAIL at every restart, and the
  time after `close()` must equal the time before the start's jobs, as
  `CleanupCutProbe` checks.


2. UA-9: the handover's wait parks with the flag cleared
---------------------------------------------------------

`Db.giveWayToWriters` waits while a commit waits for the write lock:
100 spins, then parks of 20 us. `LockSupport.parkNanos` returns at once
while the thread's interrupt flag is set, so the wait spun. Since 028-83
the wait clears the flag before each park and sets it again when the
wait ends, also when an interrupt comes during it. That is the handling
that `Database`, "Interrupts", promises for every call but the three
that only wait: maintain() ignores an interrupt until it is done, and
the flag is set when it returns or throws (005-46). The call still
waits as long as commits come (UA-7, 031-04's Q9, not changed here); its
sync of a cut's table still throws a StreamIoException whose cause is an
InterruptedIOException when the flag is set, as its Javadoc says.
Eviction's own thread clears the flag the same way (019-41), without
setting it again, as no caller waits for it.

The test, `ReclaimMaintainTester.testInterruptedCallWaits`: the write
lock held with a commit waiting for it, a call of `maintain()` started
with its flag set, the lock held 200 ms after the call begins to give
way (the hook `givingWay`), then let go. A new hook, `gaveWay(parks)`,
gives the parks of the wait, which the hooks time. A park waits 20 us
or more unless the flag is set or it is woken, so the bound is twice the
wait's time over 20 us, and 1,000 more: it does not depend on the
machine's speed, as a slow machine parks longer and counts fewer. Before
the fix: "the wait of 203220 us made 6527736 parks, more than 21322: it
spun". After it, passes, and the flag is set after the call.
`MaintainSpins` after the fix: 375 and 606 ms of CPU in 5 s with the
flag set, 530 ms without (before: 3,961 and 310 ms); the rest is the 20
us parks beside 8 writers, UA-7's handover.


3. UA-10 and UA-2: the refusal at a stop, with the storage's exception as its cause
-------------------------------------------------------------------------------------

A read or a sync that fails on the storage throws a StreamIoException
only when the database is no longer active (`Db.failOnStorage`): while it
is active the failure fails the database, a DbFailedException. So such
an exception in a call before its commit means a stop, whatever the
storage met as it closed: "Storage is closing.", a stream that the
stop's close has closed ("File closed"), or an I/O error, which stays
the cause. It can be told apart, and the call is refused as
`Database.stop()` says.

* `Db.refusedAtStop(method, e)`: a DbStoppingException (an
  IllegalDbStateException) with `assertDbStateIsActive`'s message and
  `e` as its cause, while the state is STOPPING; `e` itself otherwise.
* `Db.warmup` (the KVs' keys) and `Db.warmupStep` (the record's reclaim
  step, a commit's or a part's): a StreamIoException ends the call with
  it. Before the go point: nothing is written.
* `Db.maintain`'s sync of a decided cut's table (`syncForCut`): at a
  stop, the call ends with it, as at its next part's lock; the parts
  that ran stay written; an interrupt's StreamIoException is thrown as
  before.
* The Pub's own reads before a commit, the old values whose index
  entries a put of an object or an rw() deletes
  (`RwTransaction.indexEntries`, through `Db.Internal.refusedAtStop`).
  A read in an rw()'s action is the application's read, which
  `Database.stop()` lets throw a StreamIoException, and is unchanged.
* The Javadoc: `Database.stop()` (the refusal also when the database's
  own reads before the commit meet the closing storage, the cause then;
  maintain() a call that the stop ends, its parts written),
  `Database.maintain()`'s @throws, `Db.execute()`'s and `Db.maintain()`'s.

The tests, each failing before the fix (run on `main`'s code with the
new tests, 2026-11-28) and passing after it, and one changed:

* `DbTesterFailure.testPutDuringStop`: a transaction of 20 keys spread
  over an evicting database; the stream closes the database right after
  the warm-up's first load; the next load meets the closed storage.
  Before: "refused as at a stop: bergdb.storage.StreamIoException:
  Storage is closing.". After: a DbStoppingException whose cause is a
  StreamIoException, the stream's length unchanged.
* `DbTesterFailure.testMaintainSyncDuringStop`: calls of `maintain()` on
  an emptied database with a retain duration of 1 s until one syncs a
  cut's table; at that sync (`StorageManager.testHookSync`) the stream
  holds its appends and the database stops. Before: "ended as at a
  stop: bergdb.storage.StreamIoException: StorageManager has error:
  Storage is closing.". After: a DbStoppingException with the sync's
  StreamIoException as its cause; a later transaction is refused with
  DbStoppingException, the database not failed.

* `StorageFaultTester.testStopWhileReading` (019-43) expected the
  StreamIoException ("File closed") of a transaction whose warm-up meets
  the stream that the stop's close has closed (call 1); it now expects a
  DbStoppingException with that StreamIoException as its cause; the
  get's read (call 3) throws the StreamIoException as before. It failed
  on the first form of the fix: "call 1: the read did not meet the
  closed stream: execute 20 threw bergdb.core.DbStoppingException".

Not tested by a test of its own: the step's warm-up and the Pub's index
reads, which take the same path; e8 with `-De8.cache=4` (gates) puts
writers and transfers with an index at every stop.


4. UA-8: maintain()'s filler, up to a meta block
-------------------------------------------------

From the code (`Reclaim.planPart`, M1 to M6; 027-13, section 1.10): on
a new database with a finite retain duration, the first call begins a
pass (M1: no iteration runs, and the stream kept holds a record of the
application's, `appA` at or after the first available position; the
setters' records count), with pStart = pCut = L0, the stream's length.
The pass rewrites nothing (no value before it) and is done; its cut
waits for the retain duration and then for a meta block that names a
transaction at or after pCut (027-13, 1.6). Meta blocks come every
200,000 bytes, and none follows a pCut of 704, so M5 writes the table
with spaces up to the next meta block (031-03, R2): about 195 kB to cut
704 bytes. After the cut, `appA` is before the first available position,
and no call begins another pass: the database keeps 199,728 bytes, a
meta block distance and a few records. An emptied database ends the
same way, within one meta block distance of its last pass's pCut (e1's
29 to 241 kB).

031-04's design says so in part: M1 "No condition on the stream's growth
or on R div 4", no MIN_RELEASE, and M5's filler; it does not state the
cost for a database below a meta block distance, and neither did
`getStreamSize()` or `maintain()`.

Judgment: by design, bounded (once per pass, at most a meta block
distance, and a pass begins only after the application has written),
and now stated: `Database.maintain()` (a paragraph: a pass's cut needs a
meta block after its start; a database below 200 kB grows to about 200
kB by the calls, with FreshMaintain's numbers), `getStreamSize()` (at
least about 200 kB after the calls), and 027-13's M5. It looks wrong for
a tiny database only as a trade, a pass that writes more than its cut
gives back; 028-75's decided (c), a pass only when the stream kept is
both k times the live bytes and a floor over them, would begin no pass
there. Recommendation: no change here; 028-75's design takes
`FreshMaintain` among its checks (a new database stays at its 704 bytes,
or within the floor).


Gates
-----

On F53 beside other sessions' runs (a load of 15 to 25), 2026-11-28, on
the branch rebased onto `main` at `16c64d9a` (028-81 and 028-82), its
five commits before this section:

* `java/before-commit.sh`: BEFORE COMMIT OK (120 s). Before the rebase,
  on the first form of the fix, it failed at
  `StorageFaultTester.testStopWhileReading` (section 3), then passed
  (128 s).
* `java/stress/level3.sh`: LEVEL 3 OK; InterruptStress: "60 s, 8010931
  calls, 84232 of them with an interrupt, the flag kept by all".
* `java/stress/apps.sh quick`: APPS OK (12:20 to 12:26).
* The apps of 031-08 (`java/stress/apps/e1` to `e8`, compiled against
  the branch's release jar), 64 runs in two lanes from 12:26 to 12:52,
  all OK: e3 seed 101 twenty times at its soak size (800 rounds, 54
  restarts each), e3 seeds 102 to 110 (800 rounds) and 201 and 202
  (2,000); e8 seeds 601 to 612 with `-De8.cache=4 -De8.value=3000` (80
  rounds, 960 stops) and 201 to 204 (60 rounds); e1 seeds 101 to 110
  (3,000 keys, 3,000 rounds) and 201 (10,000, 6,000); e5 seeds 101 to 104
  (60 s, with their writers and readers) and 201 and 202 (120 s). In
  e8's 960 stops of seeds 601 to 612, where 031-08 met 391 calls that
  threw a StreamIoException, 5,745 calls were refused with
  IllegalDbStateException, nothing of them there after the restart, and
  15 threw another DbException, none of them there after the restart:
  each stack that e8 printed is a transfer's read in its rw() action
  (`RwEnvironmentImp.get`), which `Database.stop()` lets throw a
  StreamIoException; none came from `Db.warmup` or a writer.


Log
---

2026-11-28. Registered by lead-1127 from 031-08, part A (UA-2, UA-8,
UA-9, UA-10 and e3 seed 101's FAIL); taken by an agent of lead-1127 in
a clone, branch `028-83`.

2026-11-28. e3 seed 101's cause found (the removal of a deleted index's
entries committed between the app's read and `close()`; the start keeps
the time), reproduced by `CleanupCutProbe`; the Javadoc and e3 changed.
UA-9, UA-10 and UA-2 fixed with tests that fail before; UA-8 explained
and stated.

2026-11-28. Rebased onto `main` (028-81, 028-82); the gates passed
(above). To land.
