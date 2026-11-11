# 024-13. The integration of 11 November

Created 2026-11-11 by Frans Lundberg. Status: open.

The integration branch of the changes to Java and Lean that Frans
approved on 2026-11-11 at 09:25, merged into one tree and gated as one:
first a fix of `java/doubles.py`, which made `java/before-commit.sh`
take 4.3 minutes; then 024-10 (the last operation wins) and 024-07 (the
last touch of a reclaim iteration). The coordinator lands the branch on
`main`.


## 1. In short

* **Branch** `024-13-int` in `/Users/f/fl/bench/2026-11-11/int/clone`,
  from `main`'s `1fe5f180`, three commits on it:

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


## 4. State

2026-11-11, 10:07.

* **Done:** the fix of `doubles.py`, the merges of 024-10 and 024-07,
  every gate passed on `524732d8` (section 3). Nothing changed by me in
  the merges.
* **To land:** branch `024-13-int`, head **`524732d8`**, in
  `/Users/f/fl/bench/2026-11-11/int/clone`; three commits on `main`'s
  `1fe5f180` (section 1). The working tree is clean.
* **Later, when the coordinator sends them:** `024-09-tie` and
  `024-12-tree-model` (adapted onto `main` by their agents after this
  head lands; 024-12's State has merge notes), and `022-07-c-2026-4`
  (`items/022-bergdb-c/c/` only); merge each with `--no-ff` and gate as
  in section 3.
