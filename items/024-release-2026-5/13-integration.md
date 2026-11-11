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


## 6. 024-16 (first head, not landed)

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


## 7. State

2026-11-11, 12:24.

* **Landed:** the first landing as `main`'s `a780b957`, the second
  (024-09) as `379d8acf`.
* **To land:** 024-15, branch `024-13-int-b`, head **`251cd1e0`**, in
  the worktree `/Users/f/fl/bench/2026-11-11/int/wt-b` of the clone;
  one merge on `main`'s `26cb90da`; gated (section 5).
* **Next:** 024-16's new head, when the coordinator sends it: reset
  `024-13-int` (now `ce562af7`, not to be landed) to `main`'s head, merge
  the new head with `--no-ff`, and gate in full, one run a slot with
  `/Users/f/fl/bench/2026-11-11/int/gate3.sh LABEL CMD...`: `lake
  build`, `before-commit.sh`, `level1.sh` to `level4.sh` full,
  `sh stress/unlinkfuzz.sh` (mode 644), `conformance.sh drain`. Owner
  lines say "gates only", never the word for a timing run. Then
  `024-12-tree-model` and the C clone's branch, when sent (merge notes
  in 024-09 and 024-12).
