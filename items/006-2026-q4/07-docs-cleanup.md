006-07. The docs/ cleanup
=========================

Status: done. Created 2026-10-26.

At Frans's request, 2026-10-26: "bergdb/docs/ needs a cleanup. We now use
the items/ with their numbering for most documentation. I like this. Clear,
short, stable references are important. Make a plan (here in the session
output only) for how to clean this up. I want most docs moved to items/.
Feel free to suggest removing docs." And, to the plan: "Everything as
recommended, except the log. Keep log.md as is. I committed, so execute
this plan and commit when you are done. We might give other important
things an id too. Like the sis-model. But this plan is good step. Execute
it." Planned and done by Claude (Opus 5.5, Claude Code).


What changed
------------

* `docs/` holds what is kept up to date with the code:
  [levels.md](../../docs/levels.md), rewritten from 1,805 lines to 390, the
  current state level by level with the evidence by item ID;
  `sis-model.md`; [trace-format.md](../../docs/trace-format.md), new, section
  9 of the Level 2 alignment; `log.md`, kept as it was, with an entry for
  this; `sources/`; and [readme.md](../../docs/readme.md), new, with the
  table of the former files.
* The other 17 documents became subitems, by one rule: a document written in
  an item went to that item (001-07 to 001-11, 009-05); those that no item
  owns went to the new item
  [011-docs-archive](../011-docs-archive/readme.md) (011-01 to 011-11),
  with `docs/levels.md` as it was until today as 011-04. A file keeps its old
  name after its number, got one line on where it came from, and its
  evidence went with it. `lean/References/`, the exploratory Lean model of
  011-08 outside the default build, went beside it; its `check.sh` finds
  `lean/` from there.
* The references, by [relink.py](07-docs-cleanup/relink.py), in 136 files:
  * every relative link to a moved file, and every link of a moved file,
    resolves again;
  * in living text (`java/`, `lean/`, `README.md`, `AGENTS.md`, `docs/`
    except `log.md`, `items/readme.md`), a mention of a moved document is its
    ID: `bergdb 001-08, section 5.5` in code, `001-08` in Markdown;
  * a mention of a section of `levels.md` (W1, "Level 3 cost", level 2, ...)
    is 011-04, the text it was written against; a bare `docs/levels.md` stays;
  * "level2-alignment.md, 9.N" is "docs/trace-format.md, N";
  * history (the items, the moved files, `docs/log.md`, `releases/`) keeps
    its wording; only its links changed.
  By hand: the citations of the trace format in other forms, the intro of
  `docs/log.md` (its link to the current `levels.md`), and one old
  `Theory/levels.md, W5c` in `Reclaim.java`.
* The rules: `AGENTS.md` (what `docs/` holds, a new document is a subitem,
  cite by ID), [items/readme.md](../readme.md) (the same, how a result
  reaches `docs/`, the index), `README.md`.
* Open threads carried forward before freezing:
  * The problem statement's open questions (011-01, with a note there): Q4
    is 007's, Q10 and Q11 are answered by item 001, Q12 is 005-06's; Q1, Q2,
    Q3, Q5 and Q8 became [005-54](../005-todo/54-open-bounds.md).
  * The old `levels.md`'s "Next": done or held elsewhere (the handle state
    check, 009's step 4c; the stream file's lock, 005-46; the write overhead,
    005-38, 005-49 and 005-54; the startup bound, 007).
  * The alignment registers' rows still marked open (M47 of 011-11; M32,
    M33, M36, M41 and M48 of 001-07): argued, or checked and not proved, as
    item 001's K5 accepted; stated in `docs/levels.md` among the limits, not
    new entries.
* Removed: no tracked file. In the main tree, an untracked tree of 57 empty
  directories at the repository root, named `README.md`, a newline, `docs`
  and so on (made 2026-10-25 12:13).

Not done: f1's F1-008 names `bergdb/docs/` paths (history, another
repository), left as they are; `docs/readme.md` maps them. Frans's idea of
IDs for the living documents too, such as `sis-model.md`, is for later.


Checks
------

* Commit 1 of 2, `3b60dde`: 38 renames, nothing else, so that each file's
  history follows it (`git log --follow`).
* Commit 2 of 2: no change that is whitespace only (`git diff --stat` and
  `git diff --ignore-space-at-eol --stat` agree).
* Links, by [linkcheck.py](07-docs-cleanup/linkcheck.py): 1,091 relative
  links in the tracked Markdown, none broken by the move. The five that do
  not resolve did not before either: four to Java files deleted earlier
  (`Cache2.java` twice, `PointerLocks.java` twice) and 007-05's output
  directory, which its run makes.
* `java/before-commit.sh`: BEFORE COMMIT OK (1,023 unit tests, 71 f-tests,
  130 s); `cd lean && lake build`: 162 jobs, clean; `sh test-traces/run.sh`:
  TRACE TESTS OK; `sh -n` on the eight shell scripts edited. The level
  scripts were not run: in `java/` and `lean/` only comments changed, and one
  string, the message for a refused record format, which names 011-11 now.
* The moved reference model: `sh items/011-docs-archive/08-reference-theory/check.sh`
  passes (6 s); `--sis`, which builds the SIS library, was not run.
