# 026-27. The release plan for 2026.6

Created 2026-11-22 by Frans Lundberg. Status: open.

The work left before the tag `release-2026.6`, in order: what, when, by
whom and how each step is checked. The release is planned for Tuesday 24
November 2026. The week's AI usage is nearly spent until its reset on
Monday 23 November at 22:00, so Monday's daytime work is light (Frans's
own, scripts that need no agent, or one small agent) and the rest starts
after 22:00. The rules it follows are 026's "How the release is made";
the decisions it carries out are 006-32, section 6 (Frans, 2026-11-20).


## 1. Where things stand (2026-11-22)

* **The release runs passed**, on commits near the release (028-23):
  `night.sh` NIGHT OK on `2bb2b851` (2026-11-20); `week.sh` WEEK OK on
  `2bb2b851` (488 minutes, ended 2026-11-21); `timing.sh` on `40cb9ae9`
  (2026-11-21) against 2026.5: CORE 1.060, the longest pause 14.5 ms, one
  unconfirmed alert (`get_longkey` -5.4 %); the figures are in 028-19.
* **Landed after those runs:** 030-34 and 030-35 (C-STEP checks the
  values a reclaim step writes back; reclaim keeps the users' values,
  proved), 026-26 (eight new Pub API apps, no database fault), 028-41
  (`build.sh`), 028-42 (a timing scenario's setting), 028-43 (a long run
  at 10M keys with reclaim, week.sh's step 10; its full run passed, 100M
  transactions, 89 cuts), 030-36 and 030-37 (the dirty-node bound proved
  further), 028-34 (`transactionInfo()` kept as it is for 2026.6; Frans,
  2026-11-22).
* **What those landings changed:** in `java/src`, one Javadoc
  (`TransCheck`); otherwise the test harnesses and scripts under
  `java/stress/`, `build.sh`, the trace checker's C-STEP
  (`lean/Check/Steps.lean`) and the proofs in `lean/contract/`. The code
  a user runs is the code the three runs tested.
* **Bugs:** none known. 033 lists RB-001 to RB-003, bugs of 2026.5, each
  fixed on `main`. 028's open entries are 028-01, 028-19 and 028-34;
  none blocks the release.
* **The proofs:** 030-26 states them. The dirty-node bound is proved for
  puts, for deletes without joins, and through every join of leaves and
  of the inner nodes just above them (030-29, 030-36, 030-37); joins of
  inner nodes at height two and above stay tested.


## 2. The work left, in order

Monday 23 November, daytime (light):

1. **night.sh once more, on `main`'s head.** Frans starts it by hand (the
   command is in its header); it needs no agent and may run beside other
   work, about 2.5 hours. Reason: C-STEP's new checks (030-34) and
   `build.sh`'s change (028-41) landed after the night run; 030-34 was
   gated by `level2.sh` and `level3.sh` only. Checked by: NIGHT OK in its
   report and its `news.md` entry. See D1.
2. **The guarantee list, 030-38** (a new 030 subitem; 006-32, section
   6): 030-26's "What it means for a user" as a closed, numbered list G1
   to Gn; each guarantee marked proved (its theorem, by name, as pinned in
   `lean/contract/statements.pin`) or tested on purpose (its assumption
   in 030-26, section 5, and its check, with the script that runs it).
   Written by one agent (Opus, high), in `items/` only. Checked by:
   step 3.
3. **The independent review of 030-38** against the pinned statements,
   as 030-33 reviewed 030-26: a reviewer that did not write the list
   (Codex, on its own quota; see D3) reads each Gi against its theorem's
   statement in Lean and its check's script, and reports each place where
   the list says more than is proved or checked. Checked by: a findings
   list, as a 030 subitem; step 5 closes each finding.
4. **Frans reads `releases/next.md`** and this plan's section 3, and
   answers D1 to D5.

Monday 23 November, after 22:00 (the day's coordinator, unattended; its
agents Opus, high):

5. **The review's findings closed:** each one corrected in 030-38, in
   030-26, or in the checks, or recorded as accepted with its reason. A
   finding that needs a change to a statement or a checker goes through
   `lean/contract/gate.sh` (GATE OK) and `level2.sh` (LEVEL 2 OK).
6. **030's goal 2 recorded as done** in 030's readme, by 006-32's rule
   (done when 030-36 lands): 030-36 and 030-37 are on `main`; the higher
   inner joins are left tested, and a further link is a new decision.
7. **030-26 current:** its theorem counts from GATE OK's line, its
   sections 2.5, 2.7 and 5 against `main`, its date, the note "Under
   correction" turned into a log line, a link to 030-38. Checked by:
   the coordinator reads it against the gate's output and 030-38.
8. **033 current:** `git log release-2026.5..main` read for fixes of
   faults that 2026.5 has; each has its RB entry, the counts table
   agrees. Expected result: RB-001 to RB-003, no new entry.
9. **The notes complete in `releases/next.md`:** the theme with 030-26
   and 030-38 cited; the fixed released bugs by ID; what landed since
   2026-11-20 (section 1); the timing figures of 028-19, every figure
   more than 10 % worse named (024-35, finding 6); the known issues and
   limits (the higher inner joins tested, 028's open entries, older
   databases refused); the StreamDigest configurations whose digests
   changed (018-01, section 2); where the files are (GitHub Releases).
10. **The release scripts** of 024-38 (`to-main.sh`, `release.sh`,
    `stage-b.sh`, `finish.sh`) adapted as 026's readme says: no binaries
    in `releases/2026.6/`, `SHA256SUMS` for the jar and the Javadoc zip
    only, the `gh release create` command printed after the tag's.
    Checked by: a smoke run on scratch repositories, as 024-38, section 4.
11. **Commit A**, in a clone of `main`: BuildInfo 2026.6 and next.md
    complete. Its gate, in a new clone: `java/before-commit.sh` (BEFORE
    COMMIT OK), `lake build` in `lean/`, `lean/contract/gate.sh` (GATE
    OK), the axioms check, StreamDigest against 2026.5's baseline (every
    differing configuration named in the notes). The extra checks of D4
    run on A in the night. No week.sh and no timing.sh on A (D1). A
    `news.md` entry for Frans's morning: A's hash, each gate's line,
    anything that stopped.

Tuesday 24 November (Frans, with the day's coordinator):

12. **A into `main`** (`to-main.sh`: a fast-forward, or a merge if `main`
    moved in `items/` only; it stops if code moved) and pushed.
13. **Commit B** (`release.sh`): the jar and the Javadoc zip built from A,
    `releases/2026.6/readme.md` and `SHA256SUMS`, next.md emptied,
    README.md's latest release, `docs/log.md`'s entry, BuildInfo
    2026.7-dev; `before-commit.sh` passes; pushed. Frans reads the notes
    before the push: they are public at once.
14. **The tag, by Frans:** `release-2026.6` on A, pushed. No script makes
    or pushes it.
15. **The release on GitHub:** the `gh release create` command of 026's
    readme, with the two files. Checked by: both files downloaded from
    the release and `shasum -a 256 -c SHA256SUMS` OK; the tag's archive
    builds with `java/build.sh`.
16. **After the release:** 026's status done with its log line, the
    index line in `items/readme.md`, this plan done, the site's link to
    the release; 028-19 and 028-34 stay open for a later release.


## 3. For Frans to decide

* **D1. Which release runs are repeated.** Recommended: none of week.sh
  and timing.sh. The Java code a user runs is unchanged since both
  (section 1), so the rule of 2026-11-19 holds: a run near the release,
  a minor change after it. week.sh's new step 10 needs no run of its
  own: 028-43's full run (10M keys, 100M transactions) is that step on
  the same Java code. One night.sh on Monday (step 1), since the trace
  checker changed after the night run and the run costs machine time
  only. On A itself: step 11's gate.
* **D2. timing.sh's figures.** Against 2026.5: writes with reclaim 10 to
  27 % faster, writes without reclaim 6 to 10 % slower, reads 1 to 5 %
  slower, `r-100-fin`'s mixed gets 12.3 % slower, one unconfirmed alert.
  Recommended: not blocking (006-32: only a large loss at 1M or 10M
  blocks); the notes name them; 028-19 stays open after the release.
* **D3. The reviewer of 030-38.** Recommended: Codex, as for 030-33; it
  did not write the list, and its quota is not the week's, so the review
  can run on Monday before 22:00 if step 2 is done by then. Otherwise an
  agent (Opus, xhigh) that has not read 030-38's drafts, after 22:00.
* **D4. The extra checks of 2026.5's night** (024-38, section 3) that
  night.sh, week.sh and timing.sh do not run: the eight jcstress tests
  and the jar's tests on JDK 27 and 17 on s1. Recommended: both once on
  A in the night of Monday, about 2 hours of machine time; a failure
  stops the release for a look.
* **D5. The tag's message.** 2026.5's said "internal release"; the
  repository is public since 2026-11-17. Recommended: `BergDB 2026.6,
  2026-11-24`.


## 4. The release scripts (step 10)

024-38's morning scripts, adapted for 2026.6 on 2026-11-23, are in this
plan's directory, `27-release-plan/`; each header says what it does and
how it is called. Their work directory is `R`, by default
`/Users/f/fl/bench/2026-11-24/release` (outside the repository).

* `to-main.sh SRC A` (step 12): A from the clone SRC into `main`, a
  fast-forward, or a merge if `main` moved in `items/` only; it stops if
  `main` moved elsewhere. New: A is given by its hash, and A's BuildInfo
  must say 2026.6. It no longer runs 2026.5's `clean.sh`: A's gate and
  the D4 checks are the lead's to read before the call.
* `release.sh A` (step 13), in two calls: the first builds the files and
  the notes, and stops at `RELEASE WAITS` so that Frans reads the notes,
  `R/out/readme.md`; the second, `FROM=stage COMMIT=1`, makes commit B,
  gates it with `before-commit.sh` and pushes `main`. It calls:
  * `build-a.sh`: the jar and the Javadoc zip from a new clone at A; no
    source zip.
  * `finish.sh`: `SHA256SUMS` of the jar and the Javadoc zip only;
    `baseline.zip` from `R/out/baseline/` if there is one, not published.
  * `notes.sh` (new, in place of 2026.5's template and `notes.py`): the
    notes from A's `releases/next.md`, with Files (the GitHub release,
    each file's SHA-256) and Identity (tag, commit, BuildInfo, JDK).
  * `stage-b.sh`: `releases/2026.6/` with `readme.md` and `SHA256SUMS`
    only; next.md emptied; docs/log.md's entry; BuildInfo 2026.7-dev,
    267 (`set-buildinfo.sh`).
  * `commit-b.sh`: commit B. It prints last, for Frans, the tag's command
    (message `BergDB 2026.6, DATE`, D5) and its push, then the `gh release
    create` command of 026's readme with the two files from `R/out`, then
    the download of the release's files and `shasum -a 256 -c SHA256SUMS`
    (step 15). It runs none of them.
* **README.md needs a text written for it.** Its section on the latest
  release says how that release was tested, which no script knows; the
  lead writes README.md as it is to be after the release and passes the
  file as `READMEMD` to both calls of `release.sh`. Without it the first
  call stops before the build.
* `clean.sh` and `collect.sh` of 2026.5 are not carried over: they read
  2026.5's release night, which 2026.6 does not have.

The smoke run, 2026-11-23, 22:19 to 22:21, on scratch repositories in a
temporary directory (a bare clone of `main` at `004382f9` as `origin`,
its clone as `MAIN`, a commit A with BuildInfo 2026.6 in a third clone):

* `to-main.sh`: the fast-forward (TO MAIN READY, then TO MAIN OK, pushed
  to the scratch origin); the merge after an `items/` commit, with an
  untracked file in `MAIN` that stayed (TO MAIN OK); a change in `java/`
  stopped it (TO MAIN FAILED: main moved outside items/).
* `release.sh` without `READMEMD`: RELEASE FAILED before the build.
* `release.sh` with `READMEMD`: BUILD A OK (jar 2.1 MB, Javadoc zip 4.2
  MB), FINISH OK, NOTES OK (207 lines), RELEASE WAITS; then, after an
  edit of the notes, `FROM=stage COMMIT=1`: STAGE B OK, BEFORE COMMIT OK
  (62 s, the real gate), RELEASE OK, the scratch origin's `main` at B,
  no tag made, and the FOR FRANS lines. B changed its six paths only;
  `releases/2026.6/` held `readme.md` and `SHA256SUMS`; the jar and
  the zip, copied beside B's `SHA256SUMS`, passed `shasum -a 256 -c`.
* A `[[` marker in next.md: NOTES NEED EDITS, and `stage-b.sh` refused
  the notes; a relative link of next.md moved one directory down.

Not tested: the push of the tag, `gh release create` and `gh release
download` (printed only, never run against github.com); a push to
github.com; a merge conflict in `to-main.sh`; `commit-b.sh` with
`COMMIT=0`.


## Log

2026-11-22. Written, from 006-32, section 6, and 026's release steps.

2026-11-23. Step 10: the release scripts adapted in `27-release-plan/`
and smoke-tested on scratch repositories (section 4).

2026-11-24. Steps 1 to 11 done (006-33): NIGHT OK on 8056d259 (step 1);
030-38 (step 2), reviewed by Codex in 030-39 (step 3), its findings
closed and 030-26 current (steps 5, 7); 030's goal 2 done (step 6); 033
checked, RB-001 to RB-003, no new entry (step 8); `releases/next.md`
complete (step 9). Step 11: commit A, `bbcd802f` on `d8ac615c`
(BuildInfo 2026.6; next.md in line with 030-38 and 030-39), not yet on
`main`. Its gate in a new clone: BEFORE COMMIT OK; `lake build` OK; GATE
OK (254 theorems, 144 pinned files); MODEL AXIOMS OK; StreamDigest: all
12 configurations differ from 2026.5 in every mode, each named in the
notes (2026.5's jars reproduce 024-38's digests, 48 of 48). D4: the
eight jcstress tests OK; the jar's tests on s1, JDK 27 and 17: Unit
1738, F 89, Night 26, userprog OK on each. Steps 12 to 16 follow with
Frans.
