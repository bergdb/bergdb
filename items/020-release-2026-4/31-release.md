# 020-31. The release of 2026.4

Created 2026-11-10 by Frans Lundberg. Status: done 2026-11-11: the night
clean on A' (section 6), release 2026.4 made.

Frans, 2026-11-10, 19:33: "If the night is clean, merge into main, push,
and make the commit. Complete everything if the night is clean. I want
release 2026.4 created in the bergdb/releases/ directory before 07:00 in
the morning. When night is clean, make the release as soon as possible."

The release is made as 2026.3's was (018-09), with the scripts of the
candidate night of 9 November (006-17, section 3c) adapted. Its candidate
of 9 November, `03ce6ec`, was not tagged: 2026.4 waited for item 023,
the cleanup of deleted keys (020-30; 023-09). Everything is in
`/Users/f/fl/bench/2026-11-10/rel/` (`README.md` there for the night,
`morning/README.md` for the morning).


## 1. Commit A

A is made in a clone of `main` (`rel/clone`), not in `main`. It reaches
`main` only after a clean night (section 5).

| Commit     | What                                                                  |
|------------|-----------------------------------------------------------------------|
| `0c300bb0` | `git merge --no-ff 023-core`: 023-core's head `b7874541` (023-09)     |
| `cf135967` | BuildInfo: 2026.4, 264, build 2026.4.261110.1938                      |
| `d99ff27c` | The JDK 17 test fix of 006-17, section 6.3, point 5 (tests only)      |
| `414d5859` | releases/next.md with 023; StreamDigest's digests in 023-09's folder  |
| `5d60cc5d` | docs/levels.md and docs/sis-model.md on format 6 and the deletes      |
| `72c8e0ec` | A test race of DbTesterFailure fixed (section 1.1; tests only) (A)    |

* The base is `main`'s `329d78f3`. `main`'s `java/` and `lean/` had not
  changed since 023-core's base `22b6ce4c`, so the merge had no conflict.
* The test fix: `close()`, not `stop()`, in the three tests of
  `FileStreamPowerLossTester` that remove their directory after a failed
  storage. No product class changes.
* releases/next.md: format 6 and the refusal of 2026.3's databases; a
  delete removes the index nodes it empties; a forward scan ends at its
  end key; the dead hand releases the memory of ended versions after
  each cut; a transaction's KVs are sorted by key after its key
  transformations, one operation a key; the known issues revised
  (section 4); the two named allowances (023-08, Q5; 023-03, section
  10); a rare `DirectoryInUseException` on Linux (006-17, section 6.3,
  point 5).
* The docs that 023-09, section 6, lists as not changed: docs/levels.md
  (format 6, the delete's climb, reclaim's touch, the dead hand) and
  docs/sis-model.md (section 3.4 and section 11).
* The gate of A: `before-commit.sh` in a new clone of A
  (`candidate/repo`): BEFORE COMMIT OK (252 s), 20:33 (FREEZE OK). The first A, `5d60cc5d`, had
  BEFORE COMMIT OK (254 s) at 19:57.

### 1.1 A made again at 20:29

The night started on `5d60cc5d` at 20:04. At 20:05 s1's unit tests with
JDK 27 failed one test of 1,643:
`DbTesterFailure.testUncheckedCloseErrorAfterFailedWriteFailsSync`, "the
close's error was met, expected true, but was false". A race of the test,
not of the product: 015-81 gives the failed storage its error before it
closes the stream, so the sync fails, and the test can read the fault
count before the storage thread's close has thrown its error. The test is
from 2026-11-05 (015-81) and passed on s1 on 9 November; it is not from
023. A failed test on s1 would leave the night not clean, so at 20:27 the
night was stopped (`night.sh large` had run 18 minutes, s1's tests 23),
the test made to wait for the close, at most 5 seconds, as it waits for
the sync (`72c8e0ec`), and the night started again on it. The first
night's outputs are in `rel/first/`.

### 1.2 A made again: A' (22:40 to 23:00)

The night of A (`72c8e0ec`) failed one night test, on F53 and on s1
with JDK 27 and 17: `CorruptStreamTester.testFull`, the day's seed
20767. A copy of a stream with a key node's `prevPos` damaged, its
checksum made right, named the version of its own child before the
startup section; the start's rule R made the node's pointer to that
child a pointer to the node itself, and a read's descent looped for ever.
`databasesStopped` failed after it, as that test's database was left
running. Not from 023: `main`'s `329d78f3` hangs on the same copy. The
fixes are on branch `fix-cst` (`/Users/f/fl/bench/2026-11-10/cst/clone`),
both BEFORE COMMIT OK there:

* `4b36218a`: every descent and scan keeps a cycle check on the node ids
  it passes; a read that comes back to a node fails with a
  `StreamFormatException`, and the database fails.
* `4df672f4`: the start's check of rule 4 (`NodeCollection.checkLinkById`,
  with `-ea`) refuses a damaged `prevPos` with a `StreamFormatException`
  where it threw an `AssertionError` (seeds 20769 and 20770, 12 and 13
  November). `NodeCollection.testLinkToCanonicalCheck` now expects the
  `StreamFormatException`.

A' is made as 018-09, section 4, made 2026.3's A again, in a second
clone, `rel/clone2`, so that `rel/clone` stays under the running
`night.sh large` (`a2/make-a2.sh`):

| Commit     | What                                                                  |
|------------|-----------------------------------------------------------------------|
| `4b36218a` | fix-cst: a cycle check in every descent and scan                      |
| `4df672f4` | fix-cst: checkLinkById refuses a damaged prevPos                      |
| `6649f080` | releases/next.md: the two fixes (Core API), the test changes          |
| `bb8da6dc` | BuildInfo's build made new: "Release 2026.4, made again" (A')         |

The two fix commits are on A already (A is their parent), so A' takes
them as they are, by a fast-forward. The gate of A': BEFORE COMMIT OK (263 s), 22:58.

What runs on which commit, as 018-09, section 4, allows:

* On A: `night.sh large` (the large conformance set), jcstress, checks
  and Android; s1's tests (they failed on the same night test); the
  first UnlinkFuzz, ended early by its `STOP` at the go.
* On A': the regular `night.sh` (about 95 minutes, after the steps on A,
  about 03:30 to 05:05), checks and Android; s1's tests (about 83
  minutes from the go) and UnlinkFuzz until 04:30, seeds from 2,000,001.
* The morning's `clean.sh` judges A' by its own night, checks, Android,
  s1's tests and fuzz, and A's large night by its conformance set and
  its night tests, whose only failures must be the two that A' fixes.


## 2. The night

A conductor runs the night outside any session (`rel/conductor.sh`,
started again 20:35 with `nohup caffeinate -i`, its quiet check at most
120 s). F53 runs one step at a time;
s1 runs its steps beside them, one after the other.

| Step        | Where | What                                                   | Expected      |
|-------------|-------|--------------------------------------------------------|---------------|
| night-large | F53   | `night.sh large` on A, from `rel/clone`                | 20:37 to 03:15 |
| jcstress    | F53   | the 8 jcstress tests, default mode                     | 5 to 10 min   |
| checks      | F53   | StreamDigest against 2026.3; the Lean axioms           | 1 min         |
| android     | F53   | A's `java/stress/android.sh`: unit tests and demos     | 2 to 3 min    |
| s1-jartests | s1    | Unit, F, Night with JDK 27 and 17; the user's program  | 20:35 to 22:15 |
| s1-fuzz     | s1    | UnlinkFuzz in 8 configurations until 04:30             | to 04:30      |

* The Android step was added at 20:17: Frans asked on 2026-11-09 for an
  Android test before a release (006-18-03), and the notes need it.
* The quiet check of the first start waited its 5 minutes and started
  `night.sh large` at 20:09, not quiet (the sessions were busy); on 9
  November the check waited 30 minutes. The second start waits at most
  2 minutes.
* UnlinkFuzz (023-09, sections 5 and 8.1): two lanes, one a CPU of s1;
  seeds from 1,000,001 (023-09 ran from 1). The configurations: 023-09's
  four (long shuffle dup 10; long sorted dup 10; random shuffle dup 20;
  long shuffle dup 10 at node size 14) and four with larger
  transactions (random, 200 operations, 500 keys; long, 150 operations,
  node size 4; fifo, 60 operations, 1,000 keys; long, 120 operations,
  dup 20, node size 30). `s1-fuzz-run.sh` has the exact properties.
* Each step was smoke-tested on A's build before its READY marker
  (`rel/README.md`).


## 3. StreamDigest

A's decided digests differ from 2026.3's in all 12 configurations, 48
of 48 digests: format 6 changes every record. The four modes agree in
each configuration. 2026.3's jar, run again, gives its release's digests,
so the workloads are the same. The digests before and after are in
023-09's folder (`digests-base.txt`, `digests-new.txt`, `compare.txt`),
as 018-01, section 2, asks, and next.md's format bullet names `l2-*` and
`l3-*`: next-match.py finds all 12 named.


## 4. The FIFO of 021-25

021-25's own workload (`ReclaimFifo.java`, its settings: a startup
distance of 2 MB, a retain duration of 20 s, 1,024 live keys of 80 to
479 bytes in time order), on A's build, 19:45:

| Run                      | Cuts | First available | Directory | Largest record |
|--------------------------|------|-----------------|-----------|----------------|
| main before 023, 300,000 | 15   | 182 s back      | 135 MB    | 4.17 MB        |
| A, 300,000               | 39   | 22.5 s back     | 16 MB     | 4,056 bytes    |
| A, 1,000,000             | 139  | 22.0 s back     | 15 MB     | 4,056 bytes    |

So the stall is fixed by 023's deletes, and next.md says so (a "Fixed"
bullet in its known issues). The outputs: `rel/fifo/`; main's:
`/Users/f/fl/bench/2026-11-09/g30/run-main.txt`. 021-25 is still open in
021's readme.


## 5. The morning

In `rel/morning/` (its `README.md`). Each script prints one result line.

1. `sh clean.sh`: the night is clean if every step ended and night.sh
   large is NIGHT OK on A with its large conformance set, jcstress has 8
   tests OK, checks is CHECKS OK (every differing configuration named by
   next.md, A's digests 023-09's, the axioms standard), Android is OK,
   s1's tests are OK with JDK 27 and 17, and the fuzz has no failure.
   `NIGHT CLEAN`, `NIGHT NOT CLEAN` or `NIGHT NOT DONE`.
2. `COMMIT=1 sh to-main.sh`: A into `main`, a fast-forward if `main` has
   not moved, else a merge in Frans's name if it moved in `items/` only;
   never a force; then `git push origin main`.
3. `COMMIT=1 sh release.sh`: the jar (the night's users' jar), the zips,
   `baseline.zip`, `SHA256SUMS`, the notes, then in a new clone of
   `main` the files of `releases/2026.4/`, next.md emptied, README.md,
   BuildInfo 2026.5-dev, docs/log.md's entry and this subitem; the gate,
   commit B, the tag `release-2026.4` on A, and
   `git push origin main release-2026.4`. If the notes have a fill-in
   marker it stops: edit `out/readme.md`, then `FROM=stage`.


## 6. Results

2026-11-11, 04:49, `morning/clean.sh`: NIGHT CLEAN on A' `bb8da6dc`.

| Step                  | On   | Result                                                   |
|---|---|---|
| `night.sh` (regular)  | A'   | NIGHT OK, 12 steps ok, 100 minutes (03:01 to 04:41)      |
| checks                | A'   | CHECKS OK: the digests' differences all named; axioms OK |
| Android               | A'   | ANDROID OK, 1,641 tests (4 skipped), 10 demo runs         |
| s1's tests            | A'   | S1 TESTS OK: JDK 27 and 17: Unit 1,645, F 89, Night 26   |
| s1's user's program   | A'   | OK with JDK 27 and 17                                    |
| s1's fuzz             | A'   | S1 FUZZ OK: 34,650 seeds in 8 configurations, 0 failures |
| `night.sh large`      | A    | conformance-large ok (16,112 s); every step ok but the night tests |
| (its night tests)     | A    | only the two tests that A' fixes failed (below)          |
| jcstress              | A    | 8 tests OK                                               |
| s1's fuzz             | A    | 5,950 seeds in 8 configurations, 0 failures (stopped 22:54) |

* The only failure of the night, CorruptStreamTester.testFull with
  tonight's seed 20767 (and databasesStopped after it), on F53 and on s1
  with both JDKs, is an old weakness, on `main` before 023 too: a
  damaged prevPos with a right checksum made a descent loop. A' fixes it
  (4b36218a: a cycle check in every descent, the read then fails with a
  `StreamFormatException`) and the same class at the start with -ea
  (4df672f4: a refusal where `NodeCollection.checkLinkById` asserted;
  `NodeCollection.testLinkToCanonicalCheck` now expects the refusal). The
  full CorruptStreamTester set passes on seeds 20766 to 20774. The
  diagnosis: /Users/f/fl/bench/2026-11-10/cst/notes.md.
* Seed 20775 (the night of 18 November) shows a third old weakness of the
  same class, not fixed in 2026.4: a damaged time klong's unused bits 56
  to 61 make a start with -ea fail an assertion in `KeyNode.addKlong`;
  without -ea the database starts and answers right. A known issue; for
  2026.5 (024's readme).
* `main`: 746f2d00, the merge of A' (morning/to-main.sh, 04:51), pushed.
