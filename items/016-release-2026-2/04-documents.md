016-04. Plan: the documents
===========================

Created 2026-11-03 by Frans Lundberg. Status: planned, not started.

The plan for W3 of 016-01 (section 5), and for replication's wording in
the Javadoc and the notes (016-01, section 3; section 4.1, items 9 and 10):
the documents current with the code of the release, and replication
described as Frans decided. Only what is out of date with the code is
changed. It fits the one night of the coordinator's timeline (Frans,
15:40): written in the evening, with the lines that depend on the night's
runs added in the morning.

Who: a documents agent, in a scratch clone `/Users/f/fl/bench/016/docs/`
(D below), in the evening; recommended: the notes agent of 016-03
(016-01's A1), D1 and D2 first, then 016-03's N1 to N3, then D4, D6 and
D3, late, when most of the night's entries are committed (016-03, "Who").
About 3.5 agent-hours. The coordinator commits.


## 1. Facts found on 2026-11-03

**Replication's wording today.** Frans: "This should be considered
experimental in 2026.2, known issues are allowed for this, the API will
change. Should absolutely not be used in production." The four things to
say: experimental, known faults, its API will change, not to be used in
production. Today's text says the first two, and "not for data that
matters", which is weaker than the fourth; none says the third.

* `java/src/bergdb/pub/DatabaseBuilder.java`, `replica`, line 53:
  "Experimental, with known faults; not for data that matters (2026-10-25,
  bergdb 005-11)", then the list of the faults.
* `java/src/bergdb/pub/Database.java`: `addReplica`, line 315, the same
  words and its own faults; `removeReplica`, line 336, and
  `getStorageInfos`, line 344: "Experimental, as addReplica() (bergdb
  005-11)".
* Replication is also named in `bergdb.pub.util`'s `BadReplicaException`,
  `SyncLevel` (`STRONG` waits for the replicas) and
  `DatabaseNotCreatedException`; `java/src/overview-pub.html` does not
  name it.
* README.md, line 93: "A known limit (2026-10-25). Replication
  (`DatabaseBuilder.replica`, `Database.addReplica`) is experimental, with
  known faults, and not for data that matters (005-11)."
* docs/levels.md, section 9, says it is experimental with known faults,
  and lists them; "kept as it is for release 2026.1".

**docs/levels.md** (as 016-01, section 4.1, item 10 found, with line
numbers of 2026-11-03):

* line 19: the status table's date, "Status, 2026-10-26";
* section 3, lines 90 to 102: a read that fails on corrupt data fails the
  database, "in `getOne`, `getMany`, `getTrans` (`transactionInfo()`) and
  `sync()`". For `getTrans` this was not true (005-82); it is after
  005-82's fix;
* section 7, line 440: 005-65's case "not yet explained";
* section 8, line 466: holes in an unforced tail, "recovery for this
  fault class is open (005-83, ...)", now 014-01;
* section 8, line 493: "Open: group commit (005-48), and a durability of
  "written, not forced" (005-47)". Group commit is in `main` since
  `d8ed1aa`;
* section 9: "kept as it is for release 2026.1".

**README.md**: line 26, the latest release is 2026.1; line 37, "Needs a
JDK 17 or later"; line 93, replication (above); the status table, lines
77 to 83, copies docs/levels.md's.

**lean/README.md** has 44 `#print axioms` lines: 27 theorems in the first
list (lines 124 to 150), T3 for the take among them, and 17 over handles
after it. The
level scripts still run Lean's conformance (`level2.sh` to `level4.sh`
need elan; AGENTS.md), and `night.sh` builds every proof, so the list
stays a step of the release's verification (016-09, R8). Frans, 15:31:
Lean is a tool, not an output; lean/README.md changes only if a theorem
of the list changes name, or the night adds one.

**Code markers.** `java/src-dev/bergdb/dev/package.html` ("Code markers"):
"XXX are temporary and should be gone before each commit. Most TODOs
should be gone before a release." Since 2026.1, `git diff
release-2026.1..HEAD -- java/src java/src-dev` adds no line with `TODO`
or `XXX`; 2026.1's markers were reviewed on 2026-10-25 (docs/log.md).

**docs/log.md** has 2026.1's entry on 2026-10-25 (line 1160): the tag,
`BuildInfo`, the night run, the tests on the jar, what `releases/2026.1/`
holds, and the Props.


## 2. The steps

### D1. Replication's Javadoc (documents agent, 17:00 to 17:45; S)

* In D (`git clone /Users/f/fl/repos/bergdb D`), the first paragraph of
  each of the four methods' replication notes becomes, keeping the list
  of faults that follows it:

      <p>Experimental, with known faults, and not to be used in production;
      its API will change in a later release (2026-11-03; bergdb 005-11, and
      bergdb 016-01, section 3).</p>

  `removeReplica` and `getStorageInfos`: "Experimental, as addReplica():
  not to be used in production, and its API will change (bergdb 005-11)."
* `BadReplicaException`'s class Javadoc gets one sentence: "Replication is
  experimental (see Database.addReplica())." `SyncLevel.STRONG` the same,
  if its Javadoc names replicas. Nothing else in the code.
* Gates: `java/javadoc-pub.sh` prints `JAVADOC PUB OK`, and
  `java/before-commit.sh` prints `BEFORE COMMIT OK`. Check that the diff
  touches comments only: `git diff -U0 -- java | grep '^[+-]' | grep -v
  '^[+-][+-]' | grep -v -E '^[+-][[:space:]]*(\*|/\*\*|//)'` prints
  nothing.
* Review (H5): another agent reads the diff against Frans's words above,
  10 minutes; the findings are answered in 016-02.
* Hand-over: the patch to the coordinator, who commits it ("Replication:
  experimental, not for production, its API will change (016-04)").
* Mind the trailing whitespace of the Java files: edit them with exact
  strings, and compare with `git diff -w` that only the intended lines
  changed.

### D2. README.md and docs/levels.md, section 9 (documents agent, 17:45 to 18:15; S)

* README.md, line 93: "A known limit. Replication (`DatabaseBuilder.replica`,
  `Database.addReplica`) is experimental, with known faults; its API will
  change, and it must not be used in production (005-11; Frans,
  2026-11-03)."
* docs/levels.md, section 9: "kept as it is for release 2026.1" becomes
  "kept as it is for releases 2026.1 and 2026.2; in 2026.2 its API may
  change, and it must not be used in production (016-01, section 3)".
* The notes' known issue (016-03, section 2, item 12) uses the same four
  statements.
* Check: `grep -n -i 'replica' README.md docs/levels.md` shows each place
  with the four statements, or a link to the place that has them.

### D3. docs/levels.md current (documents agent, 23:45 to 01:00; M)

The lines of section 1, each only if the code has changed it:

* section 3, `getTrans`: unchanged if 005-82's fix is in; otherwise a
  sentence that `getTrans` is the exception, with 005-82. 005-82's entry
  owns the change; this step checks it.
* section 8, line 466: "(014-01; found in 005-83)", and that it is a known
  issue of 2026.2.
* section 8, line 493: "Open: a durability of "written, not forced"
  (005-47)." Group commit is described where `BufferedStream` and the sync
  are (lines 468 to 492); if it is not, one sentence: "A sync that waits
  has the buffer written at once (group commit, 005-48)."
* Each entry made tonight, by its own "Done when", changes docs/levels.md
  where its mechanism is described (005-79 the take's arithmetic, 005-78
  the retain duration, 015-01 the start of an empty directory). This step
  checks that each did: `grep -n` for its ID in docs/levels.md after its
  commit; a missing line is reported to the coordinator, not written by
  this agent, as the entry's author knows the change.
* The Lean model and the C clone (Frans, 15:31): where docs/levels.md says
  that a mechanism is "aligned with the proved Lean model" and tonight's
  Java change is not in the model (005-79's integers, if its Lean part is
  not made), one clause that names the difference as 005-79's entry states
  it, for example that Java's take computes in fixed point since 005-79
  and the model's `share` and `dither` do not. The same for the C clone,
  if docs/levels.md names it as following Java's bytes: it writes those
  of the Java it last ported (012's log), not 005-79's take.
* The status date, line 19, becomes the release's date, once the other
  lines are checked; the table's rows change only where a level's status
  changed.
* Check: a list in 016-02 of each line changed, with the commit or entry
  that made it out of date. `git diff docs/levels.md` has no other change.

### D4. lean/README.md (documents agent, 23:00 to 23:15; S)

* Check that each theorem named in the `#print axioms` lists exists at
  `main`: `grep -rn "theorem NAME\b" lean/SIS` for each name (no Lean
  build).
* If tonight's Lean work (005-79, if made) adds a theorem that the release
  should check, it goes into the list, by that entry.
* Otherwise lean/README.md does not change. Check: the grep finds each
  name.

### D5. The morning lines (coordinator, 06:05 to 06:35; S)

In commit B (016-09, R9), drafted by the documents agent in the evening as
`D/out/morning.md` with markers `[[...]]`:

* docs/levels.md, section 7, line 440: 005-65's case as the rerun of the
  quiet block explains it (005-65's entry), or "not yet explained" kept if
  the rerun does not explain it.
* README.md, line 26: "The latest is [2026.2](releases/2026.2/readme.md),
  internal, of 2026-11-04"; line 37: the JDKs the jar was tested on
  (016-09, R4 and R5).
* docs/log.md, the release's entry, as 2026.1's: "2026-11-04. Release
  2026.2, internal, as planned in item 016: the tag `release-2026.2` on
  A, where `BuildInfo` says 2026.2. The night run passed on it, and the
  tests again on the jar itself, on F53 and s1, with JDK 27 and 17.
  `releases/2026.2/` holds the jar, the source, the Javadoc, the release
  notes with the numbers against 2026.1 in turns (Props: MEM, CORE, SS;
  ...), and the outputs of the runs. After the tag, `BuildInfo` says
  2026.3-dev." No author other than Frans is named.
* Check: `grep -c '\[\[' README.md docs/levels.md docs/log.md` prints 0.

### D6. sis-model.md and trace-format.md (documents agent, 23:15 to 23:45; S)

* docs/sis-model.md describes the Lean model; it changes only if tonight's
  Lean work changes the model. docs/trace-format.md changes only if an
  entry changes the trace that Java writes (005-79 may, if the take's
  values are in the trace). Check by `git diff --stat release-2026.1..main
  -- java | grep -i trace` and by each entry's outcome.
* Check: a line in 016-02 for each file: "unchanged, because ..." or the
  change.


## 3. What is a stop for Frans

* None expected. The wording of replication is his (section 1); a change
  of it beyond the four statements is not made.
* If docs/levels.md would claim less than before for a level (a status
  row), the coordinator writes it in 016-02's "For Frans to decide"
  rather than changing the table.


## 4. Done when

* The four methods' Javadoc, README.md and docs/levels.md, section 9 say
  the four things of section 1, and `JAVADOC PUB OK` and `BEFORE COMMIT
  OK` passed on the change.
* Each statement of section 1 is current at A, or stays by a reason given
  in 016-02.
* Commit B has README's line, docs/log.md's entry and the morning lines,
  with no marker left.
* No document claims an alignment with the Lean model or the C clone that
  tonight's Java changes broke.


## 5. State

2026-11-03, 16:05: the plan is written; nothing of D1 to D6 is done. The
line numbers of section 1 are from 2026-11-03 at `9d34ac1`; they move as
entries are committed, so the agent finds each line by its text.

2026-11-03, 20:19, the documents agent (in `/Users/f/fl/bench/016/docs/repo`,
with 016-03): **D1 done** on `main` at `347f823` (its `java/` as at
`8c6b8bd`). `DatabaseBuilder.replica` and `Database.addReplica` begin
with section 2's paragraph; the faults follow in a paragraph of their own,
"Its known faults: ...", unchanged but for those two words and a reflow.
`removeReplica` and `getStorageInfos` say "Experimental, as addReplica():
not to be used in production, and its API will change (bergdb 005-11)".
`BadReplicaException` gets the sentence; `SyncLevel.STRONG`, which names
replicas, says "experimental (see Database.addReplica(); bergdb 005-11)".
The diff touches comments only (section 2's grep prints nothing; `git
diff -w` shows the same lines). Gates in the clone: `build.sh` OK,
`JAVADOC PUB OK`, `BEFORE COMMIT OK (105 s)`. The review (H5) is the
coordinator's to start (016-05, section 4: subagents start no agents).
Hand-off: `/Users/f/fl/bench/016/docs/handoff-D1/`.

2026-11-03, 20:24, the documents agent: **D2 done** on `main` at
`a25be75`. README.md's known limit and docs/levels.md, section 9 have the
four statements, in section 2's words but for one: section 9 says "its API
will change", not "may change", as Frans said it and as D1's Javadoc and
the notes' known issue say it. The check: `grep -n -i 'replica' README.md
docs/levels.md` shows README.md, lines 93 to 96, and section 9 with the
four; docs/levels.md, line 28 links to section 9, and line 469 lists
replication among what power-loss testing has not established, which
stays. The draft notes (016-03, N2) have the same four in their known
issues. Hand-off: `/Users/f/fl/bench/016/docs/handoff-D2/`.

2026-11-03, 20:23, the documents agent: **D3 done for what is in `main`
at `60289ee`**; the lines that tonight's open fixes may change are listed
below for their entries. Each line changed in docs/levels.md, with what
made it out of date (the list for 016-02):

* Section 1, the status date: 2026-10-26 to 2026-11-04, the release's
  date. No row changed: no level's status changed.
* Section 2, `before-commit.sh`: it also runs `deps.py` (005-56,
  `8752cf0`) and `doubles.py` (005-79, `6bc348d`); one sentence.
* Section 3, the second bullet and a new third: the claim that "the
  transaction's time never becomes a lookup time" after any failure past
  the go point is true only for a failure in `putKvs()`; the new bullet
  says what a read may see of a transaction that fails later, an append
  error above all, as the code does it (015-27, review R3's R3-F8,
  confirmed in verify-1; the same in 2026.1). The code stays. `getTrans`
  in the next bullet is right since 005-82 (`5672e5a`), and corrupt
  inner fields since 015-07 (`de4b0b2`): unchanged.
* Section 5, the Lean model's take: one clause, that the model's share
  and dither are the double rule and Java's take computes in integers
  since 005-79, with lean/README.md's figures (300 cases the same; 13 of 3
  million differ) and 015-03; `T3_take` holds for any share.
* Section 8, holes in an unforced tail: "(014-01; found in 005-83, ...), a
  known issue of release 2026.2".
* Section 8, `sync()`: group commit (005-48, `d8ed1aa`), with its figures
  on s1; the F53 figures of 005-13 marked as before it, as F53 is not
  measured with it.
* Section 8, "Open": group commit removed; 005-47 stays.

Checked, not changed: 005-79's other lines are in section 6 (its own
commit); section 5 describes no arithmetic of the take. 015-15 changed
section 7 itself (`f070403`). 015-01: docs/levels.md describes no start
of a directory and no `created.txt` (`grep -n -i creat` finds none), so
nothing is missing; the same for 015-24 (no directory lock in it), as its
entry says. 005-82, 015-07, 015-10, 015-12 and 015-17 each found
docs/levels.md right. 005-78 is not made. The C clone is named nowhere in
docs/levels.md. Section 7's 005-65 line is D5's, in the morning.

For the open fixes, not written by this agent (section 2, D3: the entry's
author knows the change):

* 015-14: section 7, "Readers", says the fast path's plain read of a
  pointer to a handle rests on 009-02, section 3.4's barriers. If 015-14's
  fix (acquire reads) gets in, the bullet changes with it; if not, it must
  say that the plain read rests on the address dependency that HotSpot
  keeps, not on the JMM (Frans, 17:18: "clearly documented").
* 015-13: section 7, "What is in memory", counts each object with its
  values; if the handles are counted (009-02, 4.7), the bullet says so,
  and the 130 bytes per KV are unchanged (the heap, not the count).
* 015-20 and 015-22 (indexes): docs/levels.md does not describe indexes;
  nothing expected.

Hand-off: `/Users/f/fl/bench/016/docs/handoff-D3/`.

2026-11-03, 20:28, the documents agent: **D4 and D6 done, with no
change**, on `main` at `16bb031`. The lines for 016-02:

* lean/README.md: unchanged, because each of the 44 theorems of its
  `#print axioms` lists (the indented lines; 39 in lean/SIS, 5 in
  lean/Check: `markOf_eq_fast`, `writeAll_eq_fast`, `reachList_eq_fast`,
  `step_eq_fast`, `r4Fast_sound`) exists at `main` (`grep -rn "theorem
  NAME"`), and tonight's Lean work added none: since `9d34ac1` only
  005-79's `6bc348d` touched `lean/`, a sentence of lean/README.md on the
  integer take. 005-79's step 8 (Lean) is not made (015-03).
* docs/sis-model.md: unchanged, because the model is unchanged tonight;
  it says T3 holds "with any share", which stays true of the integer
  take, and it names no arithmetic of Java's.
* docs/trace-format.md: unchanged, because no Java change since `9d34ac1`
  touches the trace (`git diff --stat 9d34ac1..main -- java | grep -i
  trace` prints nothing); since 2026.1, `TraceExport`'s format 2 and its
  handles' lines (009, `2966bca`, `b5e8f2b`) are in it already (its
  section 2). 005-79 changes the values in `REC` lines, not the format.

Hand-off: `/Users/f/fl/bench/016/docs/handoff-D4-D6/` (this State only).

