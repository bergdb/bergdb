# 034-01. The release process

Created 2026-11-24 by Frans Lundberg. Status: open, maintained: kept
current, a change dated here.

How a release of BergDB is made, from its planning to after it: the
rules, the steps in order with who does each and how it is checked, and
the scripts. Gathered on 2026-11-24 from 026's "How the release is
made", 026-27 (the release plan of 2026.6 and its steps 1 to 16), 024-38
(the release of 2026.5), 033's rules, AGENTS.md's release runs and
028-49. A release item, from 031 (2026.7) on, holds its plan, scope and
decisions, not the process: it follows this text, and says where it
departs from it. What to update at and after the release, line by line, is
034-02.


## 1. Rules

Each rule with its home; a rule whose home is elsewhere is cited, not
copied.

* **No release with a known bug** (Frans, 2026-11-24, 13:12). Fixing
  bugs is always priority 1, and as a rule a release is not made with a
  known bug; an exception is Frans's decision, recorded in the release
  item. Release 2026.6 was made with no known bug, and 2026.5 with none
  counted a bug at the time (RB-001, named in 2026.5's known issues, was
  counted a bug on 2026-11-20; 033). Checked before the tag (step 4): 033
  has no open entry for the code being released, unless Frans's recorded
  exception names it, and 028 has no open entry of a fault in it.
* **A release item for each release** (items/readme.md, "Todos and
  release items"): its plan, scope and decisions, and the 028 entries it
  takes, by ID. The theme and the scope settle as the work does (031).
* **The release runs**: `java/night.sh`, `java/week.sh` and
  `java/timing.sh` on a commit near the release, not necessarily the one
  that ships; a minor change after them is acceptable (AGENTS.md, Code;
  Frans, 2026-11-19; 028-23, 028-27).
* **Released bugs**: 033, Rules. The commit that registers or fixes a
  fault of a released version updates 033; the release checks 033 before
  its tag; its notes name the released bugs it fixes by ID and the ones
  known in it under its known issues.
* **The notes** are collected in `releases/next.md` as the changes are
  made (its introduction). A change of the stream's bytes names the
  StreamDigest configurations whose digests changed (018-01, section 2).
  Every timing figure more than 10 % worse than the previous release is
  named (024-35, finding 6); whether one blocks the release is Frans's,
  in the release plan (for 2026.6, only a large loss at 1M or 10M keys,
  006-32, section 6). The notes are public at once when pushed, so Frans
  reads them before commit B is pushed (026-27, step 13).
* **The notes are kept as published** (Frans, 2026-11-24, 12:58; 033,
  Rules, "Where they are published"): after the release day,
  `releases/V/readme.md` changes only in its section "After the
  release" (section 5).
* **The files** (Frans, 2026-11-17; 029): the jar and the Javadoc zip go
  to the GitHub release of the tag, with `SHA256SUMS`, not into the
  repository; `releases/V/` holds `readme.md` and `SHA256SUMS` only; no
  source zip (GitHub archives each tag); `baseline.zip`, if made, is not
  published.
* **Commits A and B** (024-38; 018-09): A is the release's code,
  `BuildInfo` V and the notes complete, made in a clone and gated before
  it reaches `main`; the tag names A. B follows A on `main`:
  `releases/V/`, `next.md` emptied, README.md, `docs/log.md`, `BuildInfo`
  the next version, `YYYY.(N+1)-dev`.
* **The tag** `release-V` is made and pushed by Frans; no script makes
  or pushes it. Its message: `BergDB V, DATE` (026-27, D5).
* **The proofs' statement is current before the tag** (Frans,
  2026-11-20): 030-26 says what commit A proves and tests. For 2026.6 a
  closed list of user guarantees (030-38) was reviewed independently
  against the pinned statements before the tag (006-32, section 6;
  030-39); the release plan says whether its release makes its own.
* **Public text**: AGENTS.md, "Public repository" (no private data;
  decisions as dated facts; commits in Frans's name, no AI attribution).


## 2. Who and where

* **Frans**: the decisions of the release plan; reads the notes before
  commit B is pushed; makes and pushes the tag; the GitHub release, or
  the lead on his word.
* **The lead** (013-04) runs the plan with agents: the release runs, the
  checks, the notes, commits A and B with the scripts, the text of
  README.md for after the release, and the checklist (034-02).
* **The release item**, `items/NNN-release-YYYY-N/`, and its release
  plan, a subitem written some days before the release (as 026-27).
* **`releases/next.md`**, the notes in the making; **`releases/V/`**,
  the published notes and `SHA256SUMS`.
* **033**, the register of released bugs; **028**, the todo entries.
* **The scripts**, in `items/034-releases/scripts/` (section 6); their
  work directory R, outside the repository,
  `/Users/f/fl/bench/DATE/release` by default.
* **bergdb.org**, the repository `bergdb/bergdb.github.io`.


## 3. Planning

* The release item is created before the previous release is made (031
  and 032 were created on 2026-11-20, before 2026.6): work meant for
  after a release has a place before its release is planned.
* While the work goes on: each change adds its lines to
  `releases/next.md`; each fault of a released version registered or
  fixed updates 033; the release item lists the 028 entries it takes.
* Some days before the release: the release plan, a subitem of the
  release item, with what stands (the release runs, the known bugs, the
  proofs), the steps of section 4 left, each with what, when, by whom and
  how it is checked, and the decisions for Frans (D1 and on), as 026-27.


## 4. The steps

Before the release day (the lead, with agents):

1. **The release plan** written; Frans's decisions recorded in it.
2. **The release runs** on a commit near A: `java/night.sh` (NIGHT OK),
   `java/week.sh` (WEEK OK) and `java/timing.sh` on a quiet F53 or s1,
   against the previous release (CORE, the pause probe, `performance.sh
   ab` at 1M and 10M keys). A failure is fixed and its run repeated, or
   Frans decides. Their figures go into the notes.
3. **The proofs' statement current** (030-26: its theorem counts from
   GATE OK's line, its sections against `main`), and the guarantee list
   with its independent review, its findings closed, if the release makes
   one.
4. **No known bug; 033 current.** `git log release-PREV..main --
   java/src` read for fixes of faults that a released version has: each
   has its RB entry, and the counts agree (026-27, step 8). 033 has no
   open entry for the code being released, and 028 no open entry of a
   fault in it, but Frans's recorded exception (section 1).
5. **The notes complete in `releases/next.md`**: the theme and its
   evidence; the released bugs fixed, by ID, and those known, under the
   known issues; what landed after the release runs; the timing figures,
   each more than 10 % worse named; the known issues and limits; the
   StreamDigest configurations whose digests changed; whether older
   databases open; the platforms tested; where the files are. No `[[`
   marker left.
6. **The scripts ready.** If they changed since the last release, a
   smoke test on scratch repositories (section 6).
7. **Commit A**, in a clone of `main`: `sh set-buildinfo.sh CLONE V INT`
   (034's scripts); `java/src/overview-pub.html` names the jar
   `bergdb-V.jar`; next.md complete. Its gate, in a new clone:
   `java/before-commit.sh` (BEFORE COMMIT OK), `lake build` in `lean/`,
   `lean/contract/gate.sh` (GATE OK), the Lean axioms check, StreamDigest
   (`java/stress/StreamDigest.java`) against the previous release's jar,
   each differing configuration named in the notes. A `news.md` entry
   with A's hash and each gate's line.
8. **The extra checks on A** that the three release runs do not make
   (026-27, D4; 2026.5's night, 024-38, section 3): the eight jcstress
   tests (`java/stress/jcstress/run.sh`); the jar's tests on s1 with JDK
   27 and 17 (Unit, F, Night, the user program). A failure stops the
   release for a look.

The release day (Frans, with the lead):

9. **A into `main`**: `sh to-main.sh SRC A`, then with `COMMIT=1`: a
   fast-forward, or a merge if `main` moved in `items/` only; it stops if
   `main` moved elsewhere, since A was not tested with that change.
   Pushed. TO MAIN OK.
10. **Commit B.** The lead writes README.md as it is to be after the
    release (its Status names "the latest release, V (DATE, tag
    `release-V`)" and says how V was tested) and passes it as `READMEMD`.
    `sh release.sh A`: the jar, the Javadoc zip, `SHA256SUMS` and the
    notes, then RELEASE WAITS; Frans reads `R/out/readme.md`, edited
    there if needed; the second call, `FROM=stage COMMIT=1`, makes B,
    gates it with `before-commit.sh` and pushes `main`. RELEASE OK.
11. **The tag**, by Frans: `git tag -a release-V A -m "BergDB V, DATE"`
    and its push; `release.sh` prints both commands.
12. **The GitHub release**: `gh release create release-V --verify-tag
    --title "BergDB V" --notes-file BODY` with the jar, the Javadoc zip
    and `SHA256SUMS` as its assets (as printed by `release.sh`). BODY is
    `releases/V/readme.md` with every relative link made absolute
    (`https://github.com/bergdb/bergdb/blob/main/` and the path the link
    resolves to), since the relative links give 404 on the release's
    page: `R/out/body-V.md`, made by `body.sh` (section 6; 028-49).
    Checked: before the release is made, every link of the body answers
    200 (`CHECK=1 sh body.sh V`, BODY OK, as printed by `release.sh`,
    once B and the tag are pushed); the three files downloaded from the
    release, its `SHA256SUMS` the repository's and `shasum -a 256 -c
    SHA256SUMS` OK; the tag's archive builds with `java/build.sh` and
    `BuildInfo` says V.
13. **After the release**, the same day: the lines of 034-02 that follow
    the tag, each checked; then the release item done.


## 5. After the release

* **The section "After the release"** of `releases/V/readme.md` (Frans,
  2026-11-24, 12:58; 033, Rules): added with its first entry, so a
  release with no later update has no empty heading; a setext heading as
  the notes' other sections; its first line "Added after YYYY-MM-DD; the
  notes above are as published on that day.", then dated bullets, oldest
  first, appended only: a released bug found after the release (its ID,
  severity, state and a link to 033) and errata ("Corrected: ... reads
  ...; it should read ..."). The text above it stays as published.
* **The GitHub release's body** is the notes with that section, made
  again and set with `gh release edit` when an entry is added (028-49):
  once the entry is pushed to `main`, `CHECK=1 sh body.sh V` in
  `items/034-releases/scripts/` (BODY OK: the body from `main`'s
  `releases/V/readme.md`, every link answering 200), then the command it
  prints, `gh release edit release-V --notes-file BODY`.
* **A released bug found after a release**: its 033 entry; a bullet in
  the latest release's notes; one pointer bullet to 033, with the IDs, in
  an older release's notes that has it (033, Rules). README.md and
  bergdb.org list no known issues; they point to the notes and to 033.


## 6. The scripts

In `items/034-releases/scripts/` since 2026-11-24, moved from 026-27's
directory, where 024-38's scripts were adapted for 2026.6; each header
says what it does and how it is called.

* `set-buildinfo.sh CLONE VERSION INT` (steps 7 and 10): `BuildInfo`'s
  three lines, `RELEASE_INT` (YYYY - 2000) * 10 + N, such as 267 for
  2026.7.
* `to-main.sh SRC A` (step 9).
* `release.sh A` (step 10), in two calls; it calls `build-a.sh` (a new
  clone at A, `java/build.sh`, `java/javadoc-pub.sh`, the jar and the
  Javadoc zip), `finish.sh` (`SHA256SUMS`), `notes.sh` (the notes from
  A's next.md, with Files and Identity), `stage-b.sh` (B's files in a new
  clone of `main`) and `commit-b.sh` (the gate, commit B, the push, and
  the commands for Frans of steps 11 and 12).
* `body.sh V` (steps 12 and 13, section 5; 028-49, 2026-11-24): the
  GitHub release's body, `R/out/body-V.md`, from `MAIN`'s
  `releases/V/readme.md`: each relative link, outside code, made
  `https://github.com/bergdb/bergdb/blob/main/` and the path it resolves
  to from `releases/V/`, a link text equal to its target made that path;
  refused if a target leaves the repository or is not in its tree, or if
  a relative link is left. `CHECK=1` checks that every link answers 200
  (`curl -sIL`). `commit-b.sh` makes the body from B's notes before its
  gate (BODY OK, or COMMIT B FAILED) and prints the check and the `gh
  release create` with it. `sh body.sh test` converts the notes of
  2026.6 and 2026.5 and checks the result link by link against them:
  each link the same file in the repository (`os.path.samefile`), no
  relative link left, the text otherwise the same.

Made release-independent on 2026-11-24 (034):

* The release V is what A's `BuildInfo` says (a `-dev` version is
  refused); `build-a.sh` writes "release: V" in `R/out/build-a.txt`,
  which `finish.sh` and `notes.sh` read. PREV is the newest
  `releases/YYYY.N/`; the next version is `YYYY.(N+1)-dev` with its int
  (`NEXT` and `NEXTINT` for another, such as after YYYY.9).
* R is `/Users/f/fl/bench/DATE/release` by default, DATE the release's
  date (today); RELEASE WAITS prints the second call with DATE and R.
* The release item is found in A's `items/` as `NNN-release-YYYY-N`
  (`ITEM` for `notes.sh` if there is not exactly one): the notes' first
  line, the merge's and B's messages and the default `docs/log.md` entry
  name it. The default entry has no theme; `LOGENTRY` gives one.
* New checks and output: `build-a.sh` refuses an A whose
  `java/src/overview-pub.html` names another release's jar (in 2026.6 it
  named `bergdb-2026.4.jar`); `commit-b.sh` prints the GitHub release
  with `SHA256SUMS` as an asset and BODY in place of the notes (step 12),
  and its check compares the downloaded `SHA256SUMS` with the
  repository's. `to-main.sh`'s merge message says "commit A (A) is BASE
  with ..." where it said "commit A is BASE with ...".

**The smoke test** (as 024-38 and 026-27, section 4): in a temporary
directory, a bare clone of the repository as `origin`, its clone on
`main` as MAIN, and a third clone with commit A (`set-buildinfo.sh`,
the overview's jar name). Every call sets `MAIN`, `R` and `DATE`, never
the defaults, so that nothing touches the main tree or github.com; the
second call of `release.sh` runs with `NOGATE=1`, once with `COMMIT=0`
and once with `COMMIT=1` (which pushes to the scratch `origin`).

The smoke run of 2026-11-24, 13:12 to 13:14, on clones of `main` at
`42618952`, with A at `BuildInfo` 2026.7 (267):

* `to-main.sh`: an A with `BuildInfo` 2026.7-dev: TO MAIN FAILED ("not a
  release YYYY.N"); TO MAIN READY (COMMIT=0), a fast-forward; after an
  `items/` commit on `main`, with an untracked file there that stayed:
  TO MAIN OK, a merge in Frans's name "(031; 034-01, step 9)", pushed to
  the scratch origin; after a `java/` commit on `main`: TO MAIN FAILED
  ("main moved outside items/"); a fast-forward with `PUSH=0`: TO MAIN
  OK.
* `build-a.sh` on an A whose overview names `bergdb-2026.6.jar`: BUILD A
  FAILED.
* `release.sh` without `READMEMD`: RELEASE FAILED before the build. With
  `READMEMD`: BUILD A OK (jar 2.1 MB, Javadoc zip 4.2 MB), FINISH OK,
  NOTES OK (57 lines; "as planned in bergdb item 031"), RELEASE WAITS.
  The second call, `COMMIT=0 NOGATE=1`: STAGE B OK, COMMIT B READY,
  RELEASE READY, `main` unchanged; `COMMIT=1 NOGATE=1`: STAGE B OK,
  RELEASE OK, the scratch origin's `main` at B, no tag made, and the FOR
  FRANS lines. B changed its six paths only: `releases/2026.7/` with
  `readme.md` and `SHA256SUMS` (`shasum -a 256 -c` OK against the
  files), next.md emptied ("after 2026.7"), README.md, the
  `docs/log.md` entry naming 031, `BuildInfo` 2026.8-dev, 268.
* A `[[` marker in next.md: NOTES NEED EDITS, RELEASE WAITS; the second
  call: STAGE B FAILED on the marker.

The smoke run of `body.sh` (028-49), 2026-11-24, 14:21, as above on
clones of the branch `028-49`, A at `BuildInfo` 2026.7: `sh body.sh
test`: BODY TEST OK (2026.6 and 2026.5, 10 of 10 links each made
absolute); the bodies of 2026.6 and 2026.5 the same text as those set
on their GitHub releases on 2026-11-24 (`gh release view`, but for one
final empty line), and with `CHECK=1` all
their links answer 200 (7 and 6). In the second call of `release.sh`,
with a link to a file not in the tree added to `R/out/readme.md`:
COMMIT B FAILED ("body.sh: BODY FAILED: the target ... is not in R/B");
without it, `COMMIT=0` and then `COMMIT=1`: RELEASE OK, the FOR FRANS
lines with the body's check and `--notes-file R/out/body-2026.7.md`. The
printed check: BODY FAILED, the release's page
`.../releases/tag/release-2026.7` answering 404, since no such tag is
on github.com (a tag without a release answers 200, as
`proofs-2026-11-17`); the other three links 200. An entry of "After the
release" added to the notes: the body made again holds it, its link
absolute. Refused by hand-made notes: a target outside the repository, a
target not in the tree, a link `]( path)` the script does not parse, a
`[[` marker; a link with a title, an image, a reference definition, a
link text over two lines and a link in a code span (kept) converted as
expected.

Not tested: the push of the tag, `gh release create`, `gh release
edit` and `gh release download` (printed only, never run against
github.com); a push to
github.com; a merge conflict in `to-main.sh`; `before-commit.sh` in
`commit-b.sh` (skipped by `NOGATE=1`; it ran in 2026.6's commit B).

`clean.sh` and `collect.sh` of 2026.5 are not carried over: they read
2026.5's release night, which 2026.6 did not have.


## Log

2026-11-24. Written (Frans, 13:05: one standing item for releases),
from 026's "How the release is made", 026-27, 024-38, 033's rules,
AGENTS.md and 028-49. The rule of no release with a known bug (Frans,
13:12). The scripts moved here from 026-27's directory, made
release-independent and smoke-tested (section 6).

2026-11-24. `body.sh` (028-49): the GitHub release's body made by a
script, with every relative link absolute and checked; `commit-b.sh`
makes it and prints its check and `--notes-file` of it; steps 12 and
section 5 say how it is used, section 6 its smoke run.
