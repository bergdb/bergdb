Tools of 005-10
===============

Written 2026-10-19 by Claude (Opus 5.5, Claude Code) for the search for
unused code. They run on a clone of bergdb, never on the main tree, and
need a JDK with `jmods` (27 was used), python3, elan for the Lean part,
and ProGuard 7.10.0 (`lib/proguard.jar` of the release zip from
github.com/Guardsquare/proguard, 2026-08-24; not kept here).

The search
----------

    sh java-analysis.sh <clone> <out> <proguard.jar>

builds the clone (`java/build.sh`) and runs, in order:

* `classes.py`: class-level reachability over the class files, from the
  public API, the scripts' main classes and the test suites; per source
  file (`files.tsv`). A first view; `combine.py` supersedes it.
* `Index.java` (run with `java Index.java`): javac's tree API over all
  sources; every declaration with its position and the methods it
  overrides (`decls.tsv`), every reference (`refs.tsv`).
* `pg.py`: the ProGuard configurations, one per set of entry points:
  `api`, `run` (API, scripts, unit and f-tests), `noapi`, `all` (every main
  method and every test group) and `keep` (`all` without the perf tests).
  Then ProGuard's `-printusage` for each.
* `combine.py`: ProGuard's unused declarations on the source index, less
  what used code refers to in the source; per declaration
  (`decls-status.tsv`) and per file (`file-status.tsv`).

For Lean, from `lean/` after `lake build`:

    lake env lean --run LeanDeps.lean <deps.tsv>
    python3 -I lean_unused.py <clone> <deps.tsv> <out>

`users.py` prints which top-level classes refer to a class (used to tell
code that only its own tests use from test fixtures).

The patch
---------

    sh make-patch.sh <repo> <work> <plan> <proguard.jar>
    sh gates.sh <work>/patch <log dir>

`make-patch.sh` clones the repo, deletes the files of
`plan/delete-files.txt`, makes the edits of `plan/edits-*.py` (with
`edit.py`: exact replacements, each must match once), adds the files of
`plan/add/`, then repeats until nothing more is found: `java-analysis.sh`,
`members.py` (which unused members go, and why the others stay; its
`SKIP_FILES`, `FORCE` and `KEEP`, and the plan's `skip-files.txt`, are
the choices by hand; the plan's `config.txt` names the set of entry
points) and `remove.py` (removes them by position, with their Javadoc,
and the imports only they used). Then `lean_remove.py` removes the Lean
declarations of `plan/lean-remove.txt`. That is stage 1, committed in the
clone. Stage 2, if the plan has `api-remove.txt`: `api_remove.py` finds
those public API members, `remove.py` removes them, and the member rounds
run again; committed as stage 2. The header of `make-patch.sh` lists the
plan's files. `gates.sh` runs the build, the unit and f-tests, the four
level scripts and `lake build`.

`report.py` makes the tables of the proposal from the patch clone.
