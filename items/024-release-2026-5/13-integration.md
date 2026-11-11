# 024-13. The integration of 11 November

Created 2026-11-11 by Frans Lundberg. Status: open.

The integration branch of the changes to Java and Lean that Frans
approved on 2026-11-11 at 09:25, merged into one tree and gated as one:
first a fix of `java/doubles.py`, which made `java/before-commit.sh`
take 4.3 minutes; then 024-10 (the last operation wins) and 024-07 (the
last touch of a reclaim iteration); later in the day 024-09 (the tie of
the model and the code repaired) and 024-12 (the tree's model). The
coordinator lands each gated head on `main`.


## 1. In short

* **First landing**, on `main` as `a780b957` (10:36). Branch
  `024-13-int` in `/Users/f/fl/bench/2026-11-11/int/clone`, from
  `main`'s `1fe5f180`, three commits on it:

  | Commit     | What                                                       |
  |---|---|
  | `108432d5` | `doubles.py` in 3 s, not 188 s (section 2)                 |
  | `15cc9379` | merge of `024-10-last-operation-wins`, head `3ad9fa1e`     |
  | `524732d8` | merge of `024-07-last-touch`, head `5bbdbf6e`              |

* **The merges** were clean: no conflict, no change of mine in them.
  `main`'s `java/` and `lean/` have not changed since `e7aa50f7`, the
  older of the two branches' bases. The merged tree is each branch's
  tree with the other's changes beside it; its `lean/` is `5bbdbf6e`'s.
* **Gates:** section 3.
* **Second landing**, 024-09: section 4.


## 2. The fix of doubles.py

**The diagnosis, checked.** `method_regions` finds an allowed method's
declaration with one regular expression over the whole file, in
multiline mode, so that it tries every line start. Its declaration part
was `^[ \t]*(modifiers\s+)*(<generics>\s*)?([\w.\[\]<>, ]+\s+)?NAME\s*\(`:
the indentation, the type and the space after the type all match spaces,
and `\s+` also matches line ends. `deps.strip` blanks comments out to
spaces, and `core/Db.java`'s class Javadoc has grown to about 300 lines
(9 and 10 November): at each of its line starts the search tries every
way to split the blank run among the three parts before it fails. Timed
on `Db.java` alone at 09:27 to 09:30: 89.8 s for
`setReclaimInternalFraction` and 90.0 s for `getInternalFraction`, the
two allowed methods of that file; both found at the same place (lines
671 and 687) by the old and the new pattern.

**The fix** (`108432d5`): the type now starts with a character that is
not a space, `([\w.\[\]<>,][\w.\[\]<>, ]*\s+)?`, so the indentation alone
takes a line's leading spaces, and a blank line fails at once. A
docstring in `method_regions` says why; the header's "Under a second"
is now "A few seconds".

**The evidence**, on the tree of `1fe5f180`:

| Run                         | Time        | Exit | Output                          |
|---|---|---|---|
| old `doubles.py`, 09:26     | 188 s       | 0    | kept                            |
| new `doubles.py`, 09:27     | 2.9 s       | 0    | the same, byte for byte (diff)  |
| new, a planted copy, 09:28  | 2.8 s       | 1    | the 4 planted uses REFUSED      |

The planted copy was `java/src` in a scratch directory with, in
`Db.getStartupDistance`, `double planted = 0.5;` and
`long g = (long) getInternalFraction();`, and in `BufferedStream` a
method with `Math.sqrt`: refused as "floating point type or method:
double", "floating literal: 0.5", "an allowed method's name outside the
allowed places ... getInternalFraction" and "Math method on doubles:
sqrt"; the self-test's 16 snippets pass too. Of the 2.9 s, about 2.4 s
are `deps.strip`'s loop over every character of the 467 files that
`deps.scan` and the check read; not changed.

`before-commit.sh`'s header still says doubles.py takes "under a
second"; left as it is (a comment of a shell script; 3 s).


## 3. Gates

On `524732d8`, under the heavy lock, by
`/Users/f/fl/bench/2026-11-11/int/gate.sh` (logs in
`/Users/f/fl/bench/2026-11-11/int/logs/`, and the scripts' own in the
clone's `java/build/`).

| Gate                          | When           | Result                                        |
|---|---|---|
| `lake build`, `lean/`         | 09:35 to 09:36 | OK, 149 jobs (60 s)                           |
| `lean/test-traces/run.sh`     | 09:36          | TRACE TESTS OK, 41 checks (8 s)               |
| `java/before-commit.sh`       | 09:36 to 09:37 | BEFORE COMMIT OK (80 s)                       |
| `java/stress/level1.sh`, full | 09:37 to 09:40 | LEVEL 1 OK, MEM 129, SS 1.51 (160 s)          |
| `java/stress/level2.sh`, full | 09:46 to 09:57 | LEVEL 2 OK, 70 traces TRACECHECK OK (667 s)   |
| `java/stress/level3.sh`, full | 09:57 to 10:06 | LEVEL 3 OK, 25 traces, C-CUT 0 of 310 (500 s) |

* **before-commit.sh:** unit 1,651 tests, f 89, DEMOS OK (14 runs),
  Deps and Doubles as before; 80 s, where 024-07 measured 259 s and
  024-10 262 s before the fix of section 2.
* **level2.sh and level3.sh:** every stress step with 0 failures
  (crash, bryan; reclaim with a cut in every round, readers 36 rounds);
  conformance with the Lean model built from the merged `lean/`.
* **`git diff -w`:** no whitespace noise. The merged tree's diff from
  `main` is the same with `--ignore-space-at-eol` (no trailing
  whitespace lost); `-w` drops only two lines of `Db.java`, closing
  braces that 024-07 moved to another depth (real changes).
* **Not run:** `level4.sh`, `night.sh` (not asked).


## 4. The second landing: 024-09

The coordinator's message (10:36): Frans approved landing `024-09-tie`,
head `e6b6bda6` (024-09, its State in section 8), which had merged
`main`'s `a780b957`, the first landing, already.

* **The branch brought to `main`:** `024-13-int` fast-forwarded to
  `main`'s `cffb6a75` (the first landing and items-only commits after
  it).
* **The merge** (`bc2ba891`, `--no-ff`): clean, no conflict. Its
  `java/`, `lean/` and `docs/` are exactly `e6b6bda6`'s (`git diff`
  empty), so the branch agent's `lake build`, `before-commit.sh` and
  `level2.sh` full on `e6b6bda6` stand for them. The merge's diff from
  `cffb6a75` is the same with `-w` and with `--ignore-space-at-eol`: no
  whitespace noise.
* **One commit of mine** (`e74bb8ff`): `before-commit.sh`'s header says
  doubles.py takes "a few seconds", not "under a second" (a comment).

Gates on `e74bb8ff`, each its own hold of the heavy lock (the runs that
the branch agent did not make after its merge of `main`, where 024-10
changed `UnlinkFuzz.java`):

| Gate                            | When           | Result                                 |
|---|---|---|
| `lake build`, `lean/`           | 10:49          | OK, 151 jobs (9 s)                     |
| `java/before-commit.sh`         | 10:49 to 10:51 | BEFORE COMMIT OK (84 s)                |
| `java/stress/level1.sh`, full   | 10:51 to 10:53 | LEVEL 1 OK, MEM 129, SS 1.51 (156 s)   |
| `java/stress/unlinkfuzz.sh`     | 11:06 to 11:11 | UNLINKFUZZ OK, 3,226 rounds (300 s)    |
| `conformance.sh reclaim`, whole | 11:11 to 11:13 | OK, 30 traces, C-CUT 0 of 326 (152 s)  |
| `conformance.sh evict`, whole   | 11:13 to 11:14 | OK, 51 traces TRACECHECK OK (55 s)     |
| `java/stress/level3.sh`, full   | 11:14 to 11:22 | LEVEL 3 OK, 30 traces, C-CUT 0 of 326  |

* **The slots:** the first four in heavy2.lock, which the coordinator
  reserved at 10:50; the rest in a slot taken again at 11:06, with the
  other slot running 024-14's counts beside it, so the times are not
  timings. No failure, so no rerun was needed.
* **unlinkfuzz.sh** is mode 644 in Git, where the other scripts of
  `java/stress/` are 755; its header's usage line names it as a command.
  `night.sh` runs it with `sh`, and so did this gate (a first attempt
  without `sh` got "Permission denied"). Not changed here; a `chmod +x`
  for 024-09's agent or the next commit that touches it.
* **level3.sh:** reclaim with a cut in every round, readers 36 rounds,
  every stress step with 0 failures; its conformance 30 traces, with
  the drain configuration of 024-09.
* **Not rerun:** `level2.sh` full; the merge's `java/`, `lean/` and
  `docs/` are `e6b6bda6`'s, where the branch agent ran it (LEVEL 2 OK),
  and my one commit after it changes a comment.

## 5. The third landing: 024-15

The coordinator's message (12:03): Frans allowed landing
`024-15-key-shape-cost`, head `877ddf20` (024-15), once gated; to land
before 024-16, on a branch of its own from `main`.

* **The branch:** `024-13-int-b`, in a worktree of the clone,
  `/Users/f/fl/bench/2026-11-11/int/wt-b` (the clone's own tree held
  024-16's gates then), from `main`'s `26cb90da`.
* **The merge** (`251cd1e0`, `--no-ff`): no conflict. `docs/levels.md`,
  `Db.java`'s and `Connection.java`'s Javadoc had been edited by today's
  landings too, in other paragraphs; Git kept both texts, and each reads
  as one text (024-15's paragraphs on key nodes beside 024-07's and
  024-16's). The diff from `main` is the same with `-w` and with
  `--ignore-space-at-eol`.

Gates on `251cd1e0`, one slot each:

| Gate                          | When           | Result                                  |
|---|---|---|
| `java/before-commit.sh`       | 12:18 to 12:20 | BEFORE COMMIT OK (102 s)                |
| `java/stress/level1.sh`, full | 12:20 to 12:23 | LEVEL 1 OK (212 s)                      |

* **level1.sh's Props step:** MEM 130 (at most 131); the new SEG 226.4
  (MEM with keys `%07d` 355.9 minus MEM 129.5; at most 230); the new
  MEM10M 127.0 at 10M keys `/k/%010d` (at most 131); SS 1.51.
* **before-commit.sh:** unit 1,651, f 89, DEMOS OK. Both ran beside
  024-14's counting JVMs in the other slot, so the times are not
  timings.


## 6. The fourth landing: 024-16

The coordinator's message (11:58): Frans allowed landing
`024-16-one-operation-a-key`, head `d5617d45` (024-16), once gated in
full. Merged on `main`'s `9a2318bc` (`4b934e3e`, no conflict; no file
changed by both 024-16 and 024-09 since their common base `68c3917e`;
`-w` drops lines only where 024-16 moved code into `try` blocks).
Before-commit.sh on `4b934e3e`: BEFORE COMMIT OK (106 s, 12:01 to
12:03). Then, at 12:03, its chain was stopped so that 024-15 could take
the slots first, and at 12:18 the coordinator said the review asks for
four small fixes, so a new head replaces `d5617d45`: no more gates on
it. The merge `ce562af7` (024-15's `251cd1e0` into it) is left in the
clone and is not to be landed.

**The fixed head** (the coordinator, 13:08): `3412ee7a`, three commits
on `main`'s `6bda69b0` (`190fe6f1` the change, `7177bc0e` six expected
values, `3412ee7a` the review's four fixes). `024-13-int` was reset to
`main`'s `210e5b60` (the old merge kept as the branch
`024-13-int-d5617d45-old`, not to be landed) and `3412ee7a` merged with
`--no-ff`: `3af7513e`, no conflict. Its `java/`, `lean/` and `docs/` are
`3412ee7a`'s with exactly 024-15's five files beside them (`git diff
--stat` against `3412ee7a` is 024-15's own); `Db.java` and
`docs/levels.md` keep both texts. No trailing whitespace lost.

Gates on `3af7513e`, one slot a run:

| Gate                            | When           | Result                                  |
|---|---|---|
| `lake build`, `lean/`           | 13:07          | OK, 151 jobs                            |
| `java/before-commit.sh`         | 13:07 to 13:09 | BEFORE COMMIT OK (103 s), unit 1,654    |
| `java/stress/level1.sh`, full   | 13:09 to 13:12 | LEVEL 1 OK, MEM 130, SEG 226.4, MEM10M 127.1 |
| `sh stress/unlinkfuzz.sh`       | 13:12 to 13:18 | UNLINKFUZZ OK, 3,226 rounds (310 s)     |
| `conformance.sh drain`          | 13:18          | OK, 15 traces, each takes a node back   |
| `java/stress/level2.sh`, full   | 13:18 to 13:31 | LEVEL 2 OK, 70 + 50 traces, TAKECHECK OK |
| `java/stress/level3.sh`, full   | 13:31 to 13:40 | LEVEL 3 OK, 30 traces, C-CUT 0 of 326   |
| `java/stress/level4.sh`, full   | 13:56 to 14:10 | LEVEL 4 OK, 51 traces, C-P and C-H 0    |

* **UnlinkFuzz's `dup` mode** drives the Dag directly, not `Db`, so
  024-16's refusal does not reach it: it makes, for a share of a
  transaction's keys, a second operation on the key, and then keeps one
  operation a key, the last, at the key's first place, which is what
  the Dag gets from `Db` for a key with one operation. 024-16 changed
  only its comments (no line of code since `e74bb8ff`), and with the
  same seeds every configuration's result is the same as on `e74bb8ff`,
  before 024-16, line for line: the seven `dup` configurations pass and
  take back 0 to 1,124 nodes, as before. So it exercises what it did.
* **024-16 is gated** on `3af7513e` (14:10): every gate the
  coordinator listed passed, none needed a rerun.
* **Order of the slots** (the coordinator, 13:35): 024-12's gates go
  first, for Frans's approval at 14:30; `level4.sh` of 024-16 waits for
  them or for 14:15.


## 7. 024-12, the tree model: for Frans's approval at 14:30

The coordinator's message (12:28): prepare `024-12-tree-model`, head
`d90586d0` (024-12, State in section 9), for Frans, who approves it
himself; not landed by this subitem.

* **The branch:** `024-13-int-c`, in the worktree
  `/Users/f/fl/bench/2026-11-11/int/wt-c` of the clone, from `main`'s
  `2108aa2d`; the merge **`ca3824aa`** (`--no-ff`), no conflict
  (`docs/levels.md` and `Db.java`, also changed by 024-15, merged in
  other paragraphs). `d90586d0` already holds 024-07, 024-09 and
  024-10; the merged tree's `java/`, `lean/` and `docs/` differ from
  `d90586d0`'s by exactly 024-15's five files, the same `git diff
  --stat` as 024-15's own commit. Hence `level2.sh` full is not rerun:
  it rests on the branch agent's run on `d90586d0` (024-12, section 7),
  and 024-15 changes no product logic (Javadoc, a dev tool, level1's
  checks), which `level1.sh` here covers.
* **The change against `main`** (`git diff --stat 2108aa2d ca3824aa`):
  29 files, 4,303 lines added, 51 removed.

  | Part   | Files | Added | Removed | What                                        |
  |---|---|---|---|---|
  | lean/  | 21    | 3,806 | 49      | SIS/Tree (2,400 lines), Check/Tree*, proofs |
  | java/  | 6     | 411   | 2       | TraceExport, treeconf.sh, level2.sh, Db.java |
  | docs/  | 2     | 86    | 0       | trace-format.md section 4, levels.md        |

  The largest files: `lean/SIS/Tree/Exec.lean` 823, `Node.lean` 380,
  `TreeTest.lean` 374, `Check/Tree.lean` 339, `Props.lean` 325,
  `Read.lean` 290, `Bound.lean` 246; `java/stress/TraceExport.java` 176,
  `treeconf.sh` 169.

Gates on `ca3824aa`, one slot a run:

| Gate                              | When           | Result                                  |
|---|---|---|
| `lake build` and `lake build treetest` | 12:52 to 12:53 | OK, 179 and 72 jobs (61 s)    |
| `sorry`, `admit`, `axiom`, `native_decide` | 12:54 | 0 in `lean/`, by grep              |
| `collectAxioms`, every theorem    | 12:55          | 142 theorems, only the three standard   |
| `lean/test-traces/run.sh`         | 12:53          | TRACE TESTS OK                          |
| `java/before-commit.sh`           | 12:53 to 12:55 | BEFORE COMMIT OK (87 s), unit 1,651     |
| `java/stress/level1.sh`, full     | 12:55 to 12:58 | LEVEL 1 OK, MEM 130, SEG 225.6, MEM10M 127.1 |
| `stress/treeconf.sh all 5`        | 13:46 to 13:47 | TREECONF OK (55 s)                      |
| `java/stress/level3.sh`, full     | 13:47 to 13:55 | LEVEL 3 OK, 30 traces, C-CUT 0 of 326   |

* **treeconf.sh all 5:** small 3,550 transactions (20,129 operations,
  9 key nodes taken back), drain 6,950 (126,418 operations, 282 taken
  back), reclaim 14,669 (45,949 operations, 624 touches); every trace
  TREE OK, the exporter without errors.
* **024-12 is gated** on `ca3824aa` (13:55): every gate the
  coordinator listed passed; `level2.sh` rests on `d90586d0`'s run (as
  above).

* **The axioms:** a Lean file run with `lake env lean` collects, with
  `Lean.collectAxioms`, the axioms of every theorem whose module is one
  of the 15 that the branch adds or changes under `SIS/` and `Check/`:
  142 theorems; the axioms are propext, Classical.choice and Quot.sound,
  none other (`sorryAx` would show).

**What a reader approving it should look at first:**

1. **The one change in product code:** `Db.putKvs` calls
   `TestHooks.kvApplied(key, value)` for each operation just before
   `Dag.putKv`, when a test hook is set (a read of `testHooks` and a
   null check per KV otherwise), and `TestHooks` gains the default
   method. Everything else in `java/` is in `stress/` and `night.sh`.
2. **`level2.sh` gains a step 8,** `treeconf.sh` on its small, drain and
   reclaim sets, so the tree model becomes a gate of Level 2 (024-12
   says about 12 minutes for the whole script on its head); `night.sh`
   gains a step `tree-tests` (`lake exe treetest`, one core).
3. **`BVal`, `bptrs` and `blive` move** from `Check/Trace.lean` to
   `SIS/Tree/Val.lean` with their names (the 59 lines changed in
   `Check/Trace.lean`); no line of the existing model or its proofs
   changes otherwise.
4. **27 properties are stated, 4 proved** (TP13, TP17, TP18, the run's
   P): the model is checked against Java by running (115 traces, 25,169
   transactions, no difference), not proved (024-12, sections 1 and 6).
5. **With 024-16:** 024-16 (section 6) changes `Db.putKvs` near the
   same lines (the key transformations move to `Db.transformKeys`,
   before the go point). A trial merge (`git merge-tree` of `3af7513e`
   and `ca3824aa`, 13:35) has no conflict, and `kvApplied` stays where
   it belongs: after the value transformation, before `Dag.putKv`. If
   024-16 lands first, 024-12 is merged onto it and gated again.

## 8. 024-12 again, on main with 024-16

024-16 landed as `main`'s `47c93e34` (14:10); the coordinator's message
(14:12): merge `d90586d0` again on `main`'s `b7f1b1cf`, as a new
branch, `ca3824aa` kept as it is. Frans approved 024-12 for landing
at 14:28 (the coordinator, 14:29); it lands once these gates pass.

* **The branch:** `024-13-int-e`, in the worktree
  `/Users/f/fl/bench/2026-11-11/int/wt-e` of the clone; the merge
  **`480f83da`** (`--no-ff`), no conflict. Its `java/`, `lean/` and
  `docs/` are exactly those of the trial merge of 13:35 (section 7,
  point 5). The change against `main` is the same as in section 7: 29
  files, 4,303 lines added, 51 removed (`lean/` 21 files, 3,806 and 49;
  `java/` 6, 411 and 2; `docs/` 2, 86); no trailing whitespace lost.
* **`kvApplied` in the combined `Db.putKvs`:** after the value
  transformation (`kv.transformValue`), before `dag.putKv`; the key
  transformations are done before the go point by 024-16's
  `Db.transformKeys`, so the hook sees the key and value the Dag gets.

Gates on `480f83da`; the Lean build and the static checks without a
slot (the coordinator, 14:12), the rest one slot a run:

| Gate                                   | When           | Result                          |
|---|---|---|
| `lake build` and `lake build treetest` | 14:13 to 14:14 | OK, 179 and 72 jobs             |
| `sorry`, `admit`, `axiom`, `native_decide` | 14:14      | 0 in `lean/`, by grep           |
| `collectAxioms`, every theorem         | 14:14          | 142, only the three standard    |
| `lean/test-traces/run.sh`              | 14:14          | TRACE TESTS OK                  |
| `java/before-commit.sh`                |                | (waiting for a slot)            |
| `java/stress/level1.sh`, full          |                |                                 |
| `java/stress/level2.sh`, full          |                | with its step 8, treeconf.sh    |
| `java/stress/level3.sh`, full          |                |                                 |


## 9. State

2026-11-11, 14:16.

* **Landed:** the first landing as `main`'s `a780b957`, 024-09 as
  `379d8acf`, 024-15 as `1e77cfc6`, 024-16 as `47c93e34`.
* **024-12, for Frans's yes:** branch `024-13-int-e`, head
  **`480f83da`**, worktree `/Users/f/fl/bench/2026-11-11/int/wt-e`, on
  `main`'s `b7f1b1cf`; the slot gates run by
  `/Users/f/fl/bench/2026-11-11/int/gated.sh` (logs `e-*` in
  `/Users/f/fl/bench/2026-11-11/int/logs/`), one waiting take at a time.
  When they pass, `480f83da` is the head to land after Frans's yes.
  `ca3824aa` (`024-13-int-c`, on `2108aa2d`) is superseded, kept.
* **Later:** the C clone's branch if sent. Owner lines say "gates
  only", never the word for a timing run. Stop by 19:00.
