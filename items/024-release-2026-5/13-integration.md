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

## 5. State

2026-11-11, 11:24.

* **Done:** the first landing (sections 1 to 3), on `main` as
  `a780b957`; the merge of 024-09 and the header's comment, every gate
  of section 4 passed on `e74bb8ff`.
* **To land:** branch `024-13-int`, head **`e74bb8ff`**, in
  `/Users/f/fl/bench/2026-11-11/int/clone`; two commits on `main`'s
  `cffb6a75` (`bc2ba891` the merge of `e6b6bda6`, `e74bb8ff` the
  comment). The working tree is clean.
* **Next:** `024-12-tree-model`, when the coordinator sends its head
  (merge notes in 024-09 and 024-12: a two-line conflict in
  `TraceExport.key()`, import lines in `lean/SIS.lean` and
  `lean/Check.lean`, 024-09's `Check/Live.lean` against 024-12's
  `SIS/Tree/Val.lean`); and `022-07-c-2026-4` (`items/022-bergdb-c/c/`
  only). Bring the branch to `main` first, merge with `--no-ff`, gate
  one run a hold with `/Users/f/fl/bench/2026-11-11/int/gate2.sh`
  (after `slot.sh take`; owner lines say "gates only", never the word
  for a timing run).
