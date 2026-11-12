# 024-38. The release of 2026.5

Created 2026-11-12 by Frans Lundberg. Status: the night runs (from
15:18); the morning's scripts are ready; the tag is Frans's.

The release night of 2026.5, made as 2026.4's (020-31) by the agent
"rel5" of the day's coordinator (coord-1112), from 15:03: the release
notes completed, commit A in a clone, the night's conductor with its
steps and READY markers, the morning's scripts. Frans tags in the morning
himself (the coordinator's brief): no script here makes or pushes the tag
`release-2026.5`. Everything is in `/Users/f/fl/bench/2026-11-12/rel/`
(`README.md` there for the night, `morning/README.md` for the morning).


## 1. Commit A

A is made in a clone of `main` (`rel/clone`, branch `release-2026.5-a`),
not in `main`. It reaches `main` only after a clean night (section 4).

| Commit     | What                                                                  |
|------------|-----------------------------------------------------------------------|
| `a180a6b6` | main's head at 15:03 (024-37 landed): the base                        |
| `b63b1b73` | BuildInfo: 2026.5, 265, build 2026.5.261112.1505                      |
| `bf9ab5af` | releases/next.md complete; StreamDigest's digests in 024-38's folder  |

* **releases/next.md** (section 2) and, in `items/024-release-2026-5/
  38-release/` (in A only), `digests-base.txt` (release 2026.4's digests,
  from its `baseline.zip`), `digests-new.txt` (A's code, StreamDigest
  `all`) and `compare.txt`: all 48 decided digests of the 12
  configurations differ, every mode; the four modes agree in each.
  `next-match.py` finds all 12 named by next.md's Format bullet (`l2-*`,
  `l3-*`), as 018-01, section 2 asks.
* Nothing else: 2026.4's A also carried docs, but `docs/` holds only
  `log.md` since 027 (its entry is commit B's, section 4), and no test
  fix was pending.
* **The gate of A**, `freeze.sh` in a new clone (`rel/candidate/repo`),
  15:08 to 15:14, in a heavy-run slot: BEFORE COMMIT OK (63 s); `lake
  build` OK (248 jobs); 52 `#print axioms` lines; the jcstress classes and
  A's StreamDigest compiled against 2026.4's jar. The jars' SHA-256 are in
  `candidate/commit.txt` (users' jar `8535743d...`).


## 2. releases/next.md

Added at 15:07, from today's landings and decisions (006-23, section 5;
024-35, findings 3 to 7):

* **Pub API**: `Database.maintain()`, a new method (024-32), what a call
  does, that it is optional, G5's result.
* **Core API**: the take's pace cap (024-31, with its figures at 10M
  keys); `Db.maintain()`; the cache's tables that shrink (024-33);
  reclaim's second reads skipped (024-34). 021-27 (with Q27-1), 024-36
  (OT2) and 024-37 (CA3) were there already.
* **Format**: StreamDigest's 48 changed digests, named, with their causes
  and the files above.
* **Tests and gates**: G4 counts ST6; G5 and the conformance
  configurations `r-maint` and `e-r-maint`.
* **Documentation**: `docs/` moved into item 027.
* **Known issues and limits**: each of 2026.4's known issues restated as
  fixed, changed or still so; new: aim 4's open proofs (TP7, TP10, TP30
  to TP33, TP11 refuted as stated with its keyWf fix decided, T4;
  conformance at every night's gate, Frans 12:22), ST6's floor of about
  256 kB, ST8 and P8 moved to 2026.6, OP5 (a single put's record of about
  0.25 MB at 10M keys), a value transformation that throws or passes 8
  MiB fails the database (R5, to change in 2026.6, Frans 14:42), QF3's
  curve of a put's bytes by the startup distance a key (017-11, 2.1;
  about 270 bytes for 32-byte KVs at 1M keys and 50 MB, 867 at 10M, 1,244
  at 50M; 854 at 1M and 5 MB), QF1's bound (the fraction stays 1/4; G3:
  up to about 6 times the live data beyond the history).


## 3. The night

A conductor runs it outside any session (`rel/conductor.sh`, started
15:18 with `nohup caffeinate -i`, its quiet check at most 120 s). It
holds both heavy-run slots of `slot.sh` (owner "rel5 timing: release
night of 2026.5") from its start until its F53 steps end, so that no
agent starts heavy work beside them. F53 runs one step at a time; s1 runs
its steps beside them, one after the other.

| Step        | Where | What                                            | Expected       |
|-------------|-------|-------------------------------------------------|----------------|
| night-large | F53   | `night.sh large` on A, from `rel/clone`         | 15:20 to 23:00 |
| perf        | F53   | `performance.sh ab`, quick suite, A vs 2026.4   | to 23:40       |
| jcstress    | F53   | the 8 jcstress tests, default mode              | 5 to 10 min    |
| checks      | F53   | StreamDigest against 2026.4; the Lean axioms    | 1 min          |
| android     | F53   | `java/stress/android.sh`: unit tests and demos  | 2 to 3 min     |
| queue       | F53   | 024-07's queue in time order at 10M keys        | 5 to 10 min    |
| frac        | F53   | 026-04's fraction runs at 10M keys              | 1.5 to 2.5 h   |
| s1-jartests | s1    | Unit, F, Night, JDK 27 and 17; the user program | 15:18 to 17:00 |
| s1-ot2      | s1    | OT2's probe (024-36, section 5)                 | about 8 min    |
| s1-fuzz     | s1    | UnlinkFuzz in 8 configurations until 04:30      | to 04:30       |

* **night-large** includes `night.sh`'s steps (before-commit, the
  levels, count-gates G1 to G5, the night tests, the fuzzers,
  kill-restart, conformance medium) and the large conformance set; it
  took 396 minutes on 9 November. Started 15:20:37. The regular `night.sh`
  is not run separately: night.sh large is a superset of it.
* **perf**: right after night.sh large, so that it runs on a quiet F53
  (the conductor holds the slots; the day's agents have ended by then,
  but the second prover's run, which takes no slot, may still use F53). Its preserved builds were made before the night
  (`rel/perf/r264`, at `release-2026.4`; `rel/perf/repo`, at A). It waits
  up to 30 minutes for 90 % idle CPU, then runs with `FORCE=1` and says
  so. PERF OK means that the suite ran and compared; its alerts are
  figures to name in the notes and to repeat, not a fault of the night
  (024-35, finding 6: "Name any figure more than 10 % worse in the
  notes").
* **queue**: 024-07's probe T7 and method (section 8) on A's jar: a fill
  of 10M keys in key order, then 200,000 FIFO transactions of 100 puts
  and 100 deletes; QUEUE OK if no record passes 1 MB (G1's limit) and two
  iterations ran. The slowest commit and the percentiles are printed, not
  judged.
* **frac**: only if it starts before 03:30; 024-29's `FracRuns` (branch
  024-29-fraction-runs, `d7bd3bb5`, built in `rel/frac/clone`), the four
  workloads at n = 10M and f = 1/4, 3/8, 1/2, two JVMs at a time, each
  stopped at 06:15 at the latest; counts only. Its outputs go to
  `items/026-release-2026-6/04-reclaim-fraction-settings/10m-work-*.txt`.
  Not a check of the release: clean.sh prints it and does not judge it.
* **s1-ot2 before s1-fuzz**, though the brief lists the fuzz first: the
  fuzz runs to a fixed end, 04:30, and the probe takes minutes, so this
  order lets both end in the window. The probe uses 024-36's jars on s1
  (`/opt/bergdb-bench/2026-11-12-ot2/`): their `FileStream` is A's (`git
  diff 6103608d bf9ab5af -- java/src/bergdb/stream/FileStream.java` is
  empty). Five rounds of two JVMs with the fix (300,000 tests), one
  without it as the control; OK if the fix has 0 refusals.
* **s1-fuzz**: as 2026.4's (020-31, section 2), seeds from 3,000,001
  (2026.4's nights ran from 1,000,001 and 2,000,001).
* **Smoke tests**, 15:12 to 15:20, each before its READY marker (`rel/
  smoke/`): night-large's report check, jcstress's sanity mode, checks
  (DIGESTS OK, AXIOMS OK, 12 s), android (the SDK and AVD), queue and
  frac at 20,000 keys, perf with the smoke suite on both builds, s1's user
  program on JDK 27 and 17, OT2's probe at 200 rounds (0 with the fix, 2
  without), 5 fuzz seeds of each configuration; the conductor with stub
  steps and its slot handling.
* **Outputs**: `rel/out/LABEL.txt` for each step, `rel/results.txt`,
  `rel/conductor.log`, `rel/status.txt`; night.sh's report in
  `rel/clone/java/build/night/2026-11-12-1520/report.txt`. The conductor
  writes one news.md entry when every step has ended, and one at 06:40 if
  the coordinator has not written its summary (`rel/summary-written`).


## 4. The morning

In `rel/morning/` (its `README.md`). Each script prints one result line.

1. `sh clean.sh`: NIGHT CLEAN only if every step but frac ended with its
   OK line on A, not a smoke run: night.sh large NIGHT OK with
   conformance-large ok, PERF OK, jcstress 8 OK, CHECKS OK (every
   differing configuration named, A's digests 024-38's, the axioms
   standard), ANDROID OK, QUEUE OK, S1 TESTS OK, OT2 PROBE OK, S1 FUZZ OK
   with 0 failures. `NIGHT CLEAN`, `NIGHT NOT CLEAN` or `NIGHT NOT DONE`.
2. `COMMIT=1 sh to-main.sh`: A into `main`, a fast-forward if `main` has
   not moved, else a merge in Frans's name if it moved in `items/` only;
   never a force; then `git push origin main`. If `main`'s code moved
   since `a180a6b6` (a landing in the night), it stops for a look: A was
   not tested with that code.
3. `COMMIT=1 sh release.sh`: the jar (the night's users' jar), the zips,
   `baseline.zip`, `SHA256SUMS`, the notes (`notes/readme-template.md`
   with next.md's sections and the night's figures; a `[[ ]]` marker
   stops it), then in a new clone of `main` `releases/2026.5/`, next.md
   emptied, README.md's latest release, docs/log.md's entry, BuildInfo
   2026.6-dev; the gate, commit B, `git push origin main`. **No tag.** It
   prints last, for Frans:

       git -C /Users/f/fl/repos/bergdb tag -a release-2026.5 bf9ab5afa6b32948563b8229f1db38ae4c8a690b -m "BergDB 2026.5, internal release, DATE"
       git -C /Users/f/fl/repos/bergdb push origin release-2026.5

Smoke-tested 15:24 to 15:28 on scratch repositories (`morning/
notes-test/`): to-main.sh's merge path, build-a.sh, notes.py, finish.sh,
stage-b.sh, commit-b.sh with NOGATE=1 (no tag made, the commands
printed), release.sh stopping at COLLECT INCOMPLETE while the night runs.


## 5. For the coordinator and Frans

* **021's readme still lists 021-27 as open** (024-35, finding 12). The
  notes take 021's open table from A's tree; they will say that the known
  issues name 021-27 (as fixed). An items-only edit of 021's readme on
  `main` does not change A; it is cosmetic for the notes.
* **A landing on `main` outside `items/` tonight** (the second prover's
  Lean checkpoints, a night fix) makes to-main.sh stop: the release is A
  as tested; such a landing goes after commit B, or A is made again.
* **The performance comparison's alerts** are to be named in the notes
  (024-35, finding 6); notes.py prints the compared figures in the
  Baseline section, and a figure more than 10 % worse is listed there
  with its status. Whether one blocks the release is Frans's.


## 6. State

2026-11-12, 15:30, by the agent "rel5" of coord-1112.

* **Done**: next.md; commit A `bf9ab5af` on branch `release-2026.5-a` in
  `/Users/f/fl/bench/2026-11-12/rel/clone` (not pushed, not in `main`);
  A's gate (BEFORE COMMIT OK, lake build OK); the night's step scripts,
  smoke-tested, with READY markers; the conductor running since 15:18 (pid
  in `rel/conductor.log`'s first line), night.sh large since 15:20; the
  morning's scripts, smoke-tested.
* **Not done**: the night's results (the conductor's `results.txt`); the
  morning (clean.sh, to-main.sh, release.sh); the tag (Frans's).
* **To continue**: read `rel/status.txt` and `rel/results.txt`; to stop
  or change the night, `rel/README.md`, "How to stop or change it"; in
  the morning, `rel/morning/README.md`. If a step fails, its output is
  `rel/out/LABEL.txt`; a fix that changes A means a new A in a new clone
  (020-31, section 1.2's way) and its steps again.
