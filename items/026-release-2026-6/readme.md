026-release-2026-6
==================

Created 2026-11-11 by Frans Lundberg. Status: open.

Release 2026.6 of BergDB, after 2026.5 (024): its plan, its decisions and
the work towards it. Its theme: **proven algorithms** (Frans,
2026-11-19), after 2026.5's "solid algorithms": BergDB's core algorithms
are proved, given tested assumptions (030). The preliminary theme was
simpler algorithms (Frans, 2026-11-16; the study behind it is 006-28).

The stable stream format is not in this release: it waits for a later
one, perhaps more than one release later, to be looked at together with
encryption and replication (Frans, 2026-11-19).

The stream format's draft specification is 027-03 (024-02 until
2026-11-13), kept up to date with the code.

Work moved here from 2026.5:

* **A compact stored form of the index nodes** (026-01): moved to
  2026.8 (032) on 2026-11-20 (Frans), with the stream format; its ID and
  file stay here.

* **The 10 MB write buffer of a started database** (024-05, ST8; 024-01,
  PA7; Frans, 2026-11-12, 12:10, "As recommended"): a buffer that grows
  with use or a setting, and the cost per database in the Javadoc.
* **Each reclaim step scans at its own time** (024-05, OP9: P8 of 023-05,
  the prototype `p8-steptime`; Frans, 2026-11-12, 12:10, "as
  recommended"): a shorter lag after a mass delete; 024-30's G4 shows
  back to empty converging without it.
* **G4's lag as a gate** (024-30, Q30-3; decided by the coordinator
  under Frans's delegation, 2026-11-12, 12:33): after runs at 100,000
  and 3M keys show how back to empty's lag grows with the keys; printed,
  not gated, until then. A gate at 2 R once 026-05 is on `main` (Frans,
  2026-11-13, 09:41, 026-05's Q4); made in 026-11.
* **A value transformation that throws or passes 8 MiB refuses the
  transaction instead of failing the database** (024-35, finding 2;
  010-04, R5; Frans, 2026-11-12, 14:42: "Yes to R5 and for 2026.6. I
  don't see it as a bug, but something to change anyhow."): run the
  Core's value transformations before the go point, as 024-16 did for
  key transformations (`Db.transformKeys`). 2026.5 names it in its
  Known issues.
* **The node size fixed at 30 for users** (026-08; Frans, 2026-11-13,
  09:17 and 09:21): the stable format and both APIs know one node size,
  30; 8, 14 and 62 stay for BergDB's own tests only. Replaces the
  proposal that a start read B from the meta block (024-19, Q5).
* **Merges "in place and net", studied and decided with the stable
  format** (024-22, QM1): moved to 2026.8 (032) on 2026-11-20 (Frans),
  with the stream format.
* **The startup distance out of the meta block, into an internal KV**
  (028-15; 026-12, SF7 (a); 024-01, OT4; Frans, 2026-11-16, 10:32:
  "There is still a stream format change that I want to get in place in
  the next release. The startup distance!"): the meta block's bytes 40
  to 43 reserved, and `/#i/-dummy`'s 200 kB at each change gone. Option
  A (Frans, 2026-11-18, 10:50, "SF4 (a), 028-15 A"): 2026.6 refuses
  2026.5's databases and older, with a message that names 2026.5, the
  meta version raised to 155; made in 028-15.
* **2026.5's databases refused, the stable format set aside** (026-12,
  SF4): Frans chose SF4 (a) at 10:50 on 2026-11-18, and at 11:51: "Let's
  forget about stable format for the stream. I decide to not focus on
  this for this release. The focus for the release are the algorithsm,
  simplifying them, proving them. If possible." So SF4 is open again,
  not this release's focus; what stands is 028-15's option A, older
  databases refused (above).
* **The versioning and compatibility rule and the corpus of saved
  databases** (027-03, section 21, V-A to V-D, and 21.3; Frans,
  2026-11-13, 09:23: "Yes, decided work."): a stable format needs its
  rule; 026-08's node-size field, kept as a hook for a later release,
  is a first case.


How the release is made
=======================

As 2026.5's (024-38: commit A, the night, the morning's scripts), with
the changes of the public repository (029; Frans, 2026-11-17, 11:40):

* **The binaries go to GitHub Releases, not into the repository.** After
  Frans has pushed the tag `release-2026.6`, the morning makes the
  release on GitHub with the jar and the Javadoc zip as its assets:

      gh release create release-2026.6 --verify-tag --title "BergDB 2026.6" \
          --notes-file releases/2026.6/readme.md \
          bergdb-2026.6.jar bergdb-2026.6-javadoc.zip

  The script prints this command after the tag's, for Frans, as 024-38's
  `release.sh` printed the tag's; it does not run it itself.
* **`releases/2026.6/` in commit B holds `readme.md` and `SHA256SUMS`
  only.** `SHA256SUMS` lists the jar and the Javadoc zip as uploaded;
  a user checks a download with `shasum -a 256 -c SHA256SUMS`. The
  notes say that the files are on the GitHub release of the tag.
* **No source zip.** GitHub makes an archive of each tag; the notes
  name the tag and commit A.
* **`baseline.zip` is not published.** It is made as before and kept
  with the night's outputs, outside the repository; it is not in
  `SHA256SUMS`. The notes' numbers stay in `readme.md`.
* 024-38's scripts (`release.sh`, `stage-b.sh`, `finish.sh`), adapted for
  2026.6, stage no binaries in `releases/2026.6/` and write
  `SHA256SUMS` for the two uploaded files only.
* **030-26 is current before the tag.** The public statement that the
  core algorithms are proved (030-26) says what commit A proves and
  tests: its theorem counts, its tested assumptions with their checks,
  and where they run match `main` (Frans, 2026-11-20). The notes cite it.
* **033 is current before the tag.** The register of released bugs
  (033) has an entry for each fault of a released version that `main`
  fixes; the notes name those 2026.6 fixes by ID, RB-001 and on (Frans,
  2026-11-20).
* **week.sh and timing.sh run before the release** (028-23): `java/week.sh`,
  the functional run (night's steps, the large conformance set, the user
  apps, more kills and fuzzing; about 11 hours), in place of 024-38's
  `night.sh large`; and `java/timing.sh` on a quiet F53 or s1 (CORE, the
  pause probe, `performance.sh ab` against 2026.5 at 1M and 10M keys), in
  place of the night's perf step. Both on a commit near commit A, not
  necessarily A itself. Frans, 2026-11-19, 10:25: "It would always run
  before a release. Near a release, at least. Not necessarily on the exact
  version that ships in the release. Minor change after can be
  acceptable."
  Since 2026-11-19 (028-27), week.sh no longer runs night's steps, and it
  runs the Android tests (`java/stress/android.sh`, with `ANDROID_SDK`
  set): `java/night.sh`, `java/week.sh` and `java/timing.sh`, disjoint
  sets of tests, all run before the release, on a commit near commit A.


Proposed for 2026.6, not decided
================================

Each stays where it is until Frans decides; recommended for 2026.6
there, or implied by this release's theme.

* **The stable format's open questions of the first theme**: the
  startup distance in a KV was decided and made in this release (028-15,
  above); the place reserved for objects' storage and encryption (024-01,
  PA5 and PA9) moved to 2026.8 (032) on 2026-11-20 (Frans).
* **Commits give a mass delete's space back by the clock, as
  `maintain()` does** (026-13, U13-4 and Q1, option B; Frans, 2026-11-13,
  13:07): a commit begins a reclaim iteration also on `maintain()`'s rule
  (a quarter of R, a cut that releases 400 kB), so that `maintain()` is
  optional in effect for a slowly written database. A study first: G4 at
  026-13 C2's settings and at its own, before and after; taken only for a
  clear gain. The Javadoc of today's behaviour is 028-06.


Files
=====

* 01-compact-nodes.md. 026-01, for 2026.8 (032) since 2026-11-20; a
  more compact stored form of an index node, moved from 024-20 on
  2026-11-12: measured on record format 7,
  encoding C keeps 38 to 47 % of the index bytes in every workload; with
  compact value nodes, frames and top nodes the stream 19 to 52 %
  smaller; for 2026.6 (Frans, 2026-11-12, QC1). QC2 to QC5 wait for
  this release. The probe in 01-compact-nodes/.
* 02-public-key-check.md. 026-02, a public key check, so that a user can
  test a key (and maybe a value or a transaction) against the limits
  before a call (Frans, 2026-11-12, 09:34; from 024-27, QR1): the
  options and a recommendation; done 2026-11-13 as decided (Frans,
  09:11, QK1 to QK4): `bergdb.pub.Limits`, the limits as constants,
  `keyBytes` and `checkKey`, no `levelBytes`; on main since 2026-11-13
  (6e27cf17).
* 03-single-maintenance-step.md. 026-03, one maintenance step for a
  commit and for `maintain()`, and the simple form (ordinary
  transactions with filler) to consider (Frans, 2026-11-12, 13:44 and
  13:52; from 024-32).
* 04-reclaim-fraction-settings.md. 026-04, reclaim's fraction: measured
  at larger databases, three recommended values and one default
  (Frans, 2026-11-12, 14:07; 2026.5 keeps 1/4).
* 05-reclaim-step-time.md. 026-05, each reclaim step scans at its own
  time (P8 of 023-05, with 023-08's fault 13 fixed): the change, the
  cut's argument, the gates, and back to empty's lag after a
  mass delete before and after (024-05, OP9; 026-04, section 4); done, on
  main since 2026-11-13 (Q1 to Q4 yes, Frans 09:41).
* 06-value-transformation-refusal.md. 026-06, a value transformation
  that throws or passes 8 MiB refuses its transaction, before the go
  point (`Db.transformValues`), and the database goes on (010-04, R5);
  also a key transformation that throws (Q2); done, on main since
  2026-11-13 (Q1 to Q4 yes, Frans 08:45).
* 07-write-buffer.md. 026-07, the write buffer grows with use: 64 KiB
  at the start, doubled when an append does not fit, up to 10 MB, back
  after 2 idle seconds; a small file database holds 0.67 MB of heap, not
  11.1 MB (024-05, ST8; 024-01, PA7). On main since 2026-11-13
  (ad5b0861); the probes in 07-write-buffer/.
* 08-fixed-node-size.md. 026-08, the node size fixed at 30 for users,
  the other sizes for tests only (Frans, 2026-11-13, 09:21): the four
  `DbBuilder.maxNodeSize` setters package-private, `TestNodeSize` for
  the tests outside `bergdb.core`; on main since 2026-11-13 (04ee9336);
  done, Frans's answers to Q1 and Q2 on 2026-11-18 (10:52).
* 09-keys-only-scan.md. 026-09, reclaim's scan without the values it
  does not rewrite (024-34, Q34-1, option b; Frans, 2026-11-13, 09:38):
  `GetMany.valuesBefore`; the steps' loads 44 to 60 % fewer, the steps
  14 to 20 % fewer, at 10M keys 1 to 4 % more stream written; on branch
  `026-09-keys-only-scan`, to land (Q1, recommended) with Q2 to Q4.
* 10-node-id-cache-after-empty.md. 026-10, `NodeCollection.idByPos`
  after back to empty (found by 026-07): a decided cut forgets the node
  ids below it and `KeyModSet`'s key hashes before it (the 2.2 MB of
  `long[]`), and G4 and G5 gate the plain heaps. On main since
  2026-11-13 (557b2255); the probes in 10-node-id-cache-after-empty/.
* 11-lag-gate.md. 026-11, G4's back-to-empty lag a gate of
  `count-gates.sh`: at most 2 R (2,000 drive transactions) at 1M keys;
  1,281 on `main` (margin 1.56), 4,395 without 026-05 (fails); on main
  since 2026-11-13 (00eca320).
* 12-stable-format-plan.md. 026-12, for 2026.8 (032) since 2026-11-20;
  the stable stream format: a draft plan for Frans (10:24): 11 questions, SF1 to SF11, merged from 027-03's
  Q1 to Q23 and section 21, 026-01's QC2 to QC5, 024-22's QM1, 024-01's
  OT4, PA5 and PA9, 017-08 and 017-11; each with its options, what it
  depends on and a recommendation; the decisions already taken quoted;
  the order, and three measurements (M1 to M3); none decided.
* 13-user-apps.md. 026-13, a round of "AI as the user" testing (006-20)
  against 2026.6's changes on `main` (026-02, 026-05, 026-06, 026-07,
  026-08): twelve programs with their own oracles, SIGKILLs of child
  JVMs; no bug in BergDB; U13-1 to U13-6, Javadoc findings and one
  question (Q1: commits pace reclaim by the stream, `maintain()` by the
  clock); proposed 028-todo entries. The logs in 13-user-apps/; the
  apps maintained in java/stress/apps/ since 2026-11-19 (028-23).

* 14-model-scope.md. 026-14, the Lean model's scope: the boundary as it
  is, three additions in order of value (reclaim as a whole, the stream
  format as bytes, the commit's conflict check), the assumption list, what
  stays out; proposed, for Frans to decide (2026-11-13, 12:11).

* 15-timing-10m.md. 026-15, the timing pass at 10M keys: what 2026.6's
  changes to reclaim (026-05, 026-09) cost or save in time; run from
  2026-11-14, 15:00, to Sunday morning.

* 16-simpler-for-proofs.md. 026-16, a study: what could change in
  BergDB's algorithms to make the remaining Lean premises simpler to
  prove, without a significant loss of function or speed (P11, P13);
  only the premises still open, not what is proved (Frans, 2026-11-14,
  12:53).

* 17-mt-trial.md. 026-17, MT's trial: maintenance transactions (006-28,
  section 7.5) in the Lean model only, beside today's writer, run and
  counted before any design, proof or Java (Frans, 2026-11-16, 10:29 and
  10:47); its result goes to the choice between MT, NW and neither, with
  SF10. Done 2026-11-16, 13:36: MT passes every check of the plan in the
  model (no node made and left out; the fixing ends in today's
  invariants; at node size 30, 0.08 fix steps a deleted key, bytes 1.01
  to 1.03 times today's for mixed work, 1.17 for mass deletes), with one
  rule added (A1, a scan budget in the model) for Frans to rule on; the
  evidence in 17-mt-trial/, the branch `026-17-mt-trial` kept.

* 18-main-and-subtransactions.md. 026-18, an idea of Frans's (2026-11-16,
  12:54): a main transaction is an atomic sequence of subtransactions,
  one user subtransaction and zero or more maintenance subtransactions;
  readers see only the states between main transactions. Written down
  to pick up later, with the coordinator's view, the open questions and
  a proposed short proof trial; nothing decided.

* 19-proof-trial.md. 026-19, the proof trial of 026-18 (Frans,
  2026-11-16, 13:48): one fix step keeps the in-between invariant, and
  gets and scans are right at visible times, proved on MT's rules of
  026-17; done in the night of 16 to 17 November (22:03 to 00:55):
  reduced, not proved; by its rule the proofs' gain is not supported, nor
  refuted; the frames are the largest new cost; the evidence and the
  Lean as text in 19-proof-trial/, the branch `026-19-proof-trial` kept.

* 20-step-times-net-change.md. 026-20, two designs for 2026.6's writer
  that remove (step times) or reduce (net change) the take-back inside a
  transaction, from coord-1117's discussion with Frans (2026-11-18, 06:43
  to 08:49): the terms, the time klong's layout, the risks, a comparison
  and a proposed first study; nothing decided.

* 21-step-times-study.md. 026-21, a first study of both designs of 026-20
  in the Lean model (Frans, 2026-11-18, 08:49 and 08:56: "simplification is
  the overall goal"): net change is today's Java already; step times need
  the delete cut into pieces (risk 2) and then remove the take-back and its
  books; the costs on the traces and on a bulk load and a Pub-like index;
  the evidence in 21-step-times-study/, the branch `026-21-study`. Done
  2026-11-18, 10:55: (b), step times with the delete in pieces, is
  recommended; at node size 30 it costs nothing on random work and a few
  per cent on index updates, and up to 1.4 times the bytes on sorted
  loads in large transactions; Frans decides.

* 22-mt-contract-check.md. 026-22, a short check of MT (026-17) against
  the contract of `lean/contract` (coord-1118's brief, 2026-11-18, 11:53;
  90 minutes): MT's in-between states run with the contract checked at
  every step, which read theorem needs a live key below every index
  node, the entries' take-back left (`toPrev`), what of the writer proof
  at the tag carries over, and the stream format. Done 2026-11-18: the
  in-between states fail the contract only by NonEmptyOK (empty leaves),
  which the scan's proof needs; every group's end meets it; the evidence
  in 22-mt-contract-check/, the branch `026-22-mt-contract`.

* 23-second-opinion.md. 026-23, a second opinion on a simpler writer for
  a complete proof (Frans, 2026-11-18): four proposals of an agent that
  had not read 026-17 to 026-22 (PE, plan then emit; GS, ghosts and
  structure transactions; CC, the commit check; FR, fewer kinds of things
  in a node), a recommendation, and a comparison with 026-17 to 026-21:
  PE is 006-28's NW, which 026-20's "net change" is not, and it has had
  no spike; a count on Java's traces in 23-second-opinion/ (writing each
  node's last list once never adds more klongs than Java does). Done.

* 24-pe-trial.md. 026-24, the PE trial (Frans, 2026-11-18, 12:47: "The PE
  trial. Yes, do it as recommended."): 026-23's PE, plan then emit, in the
  model: on paper (today's one-operation result is the last list but for a
  full node's cut, count and layout, F1 to F4), on 026-21's 288 traces (no
  fault of the contract or the shape at any transaction; bytes 0.96 to 0.99
  of today's, no set above 1.004; go), and a proof spike in Lean (the
  lemmas of emit and settle, 1,086 lines; beyond them, for keys of one
  segment, the plan's keys and order and the whole contract reduced to what
  emit writes; 3,288 lines of its own); a complete proof estimated at 6,500
  to 9,500 lines. The evidence in 24-pe-trial/, the branch
  `026-24-pe-trial`.

* 25-pe-java.md. 026-25, Java's writer as PE, "plan, then emit", the writer
  that 030-21 proved (Frans, 2026-11-18, 21:42: "feel free to do the Java
  implementation too"): Java's write half replaced by PeWriter.lean's
  program, the tree checker's oracle made PE, the record format, the old
  writer's code removed; record format 8. Gated d64e5638 on the branch
  `026-25-pe-java`, not merged; on s1 about 8 % slower than main's
  writer in CCBench, for Frans.

* 26-pub-app-hunt.md. 026-26, an independent hunt, with apps designed
  apart from the earlier ones (024-26, 026-13): eight Pub API apps with
  their own oracles on `main` at `bdf7c1ba`, 31 runs with 160 forced
  stops of a child JVM; no database fault. One finding outside the
  database, S4-B1: `java/build.sh` failed falsely with
  `JAVA_TOOL_OPTIONS` set, fixed as 028-41. The apps maintained in
  java/stress/apps/d1-* to d8-*, run by apps.sh since 2026-11-20.

* 27-release-plan.md. 026-27, the release plan for 2026.6, of
  2026-11-22: where things stand (the release runs passed, no known
  bug), the work left in order with who does it, when and how it is
  checked (the guarantee list 030-38 and its independent review, 030-26
  and 033 current, the notes, commit A and its gate, commit B, the tag,
  the release on GitHub), and five decisions for Frans, D1 to D5.


Log
===

2026-11-11. Created the item (Frans, 06:56), theme "a stable stream"
(preliminary).

2026-11-12. 024-20 moved here as 026-01 (Frans, 07:39: "go through the
current work and move things for 2026.6 to 026. In particular this
024-20 should move there."); the rest of 2026.5's work proposed for
2026.6 but not decided listed above.

2026-11-13. 024-02, the stream format's draft, moved to 027 as 027-03
(Frans, 08:50: "Yes"), kept current there; this readme cites 027-03,
the same sections.

2026-11-13. 026-08 registered: the node size fixed at 30 for users
(Frans, 09:17 and 09:21); 024-19's Q5 dropped from the proposals.

2026-11-13. 024-22's QM1 and 027-03's section 21 moved from the
proposals to the decided work (Frans, 09:23: "Yes, decided work.").

2026-11-13. 026-09 registered: 024-34's Q34-1, option (b), after 026-05
(Frans, 09:38).

2026-11-13. 026-10 registered (026-07's Q4; Frans, 09:48).

2026-11-16. Preliminary theme: simpler algorithms (Frans, 10:26), from
006-28.

2026-11-16. 028-15, the startup distance in an internal KV, taken by
2026.6 (Frans, 10:32).

2026-11-16. 026-17 registered: MT's trial, the plan first (Frans, 10:47).

2026-11-16. 026-18 written down: main transactions and subtransactions,
Frans's idea (12:54, 13:11).

2026-11-16. 026-17 done: MT's trial, the result for Frans.

2026-11-16. 026-19 registered: 026-18's proof trial, the plan first
(Frans, 13:48).

2026-11-17. 026-19 done: the proof trial's result (00:55 to 01:10).

2026-11-17. How the release is made: the binaries to GitHub Releases,
`releases/2026.6/` with the notes and `SHA256SUMS` only, no source zip,
`baseline.zip` not published (029; Frans, 11:40).

2026-11-18. The writer proof (030-10, 030-16) taken off main, tagged
`writer-proof-2026-11-18` (Frans, 08:42; 006-31). 026-20 written down:
step times and net change (Frans, 08:49: "Either we start investigating
Net Change. Or we investigate Step Times. Not sure which to start with,
or a first study of both, before we decide the direction of the
implementation.").

2026-11-18. 026-21 registered: the first study of both designs, one
combined study (Frans, 08:56), by an agent of coord-1118.

2026-11-18. 026-21 done: the result for Frans (10:55).

2026-11-18. 028-15 option A and 026-12's SF4 (a) (Frans, 10:50: "SF4
(a), 028-15 A"); the stable format then set aside for 2026.6 (11:51:
"Let's forget about stable format for the stream."), so SF4 open again;
028-15 made on the branch `028-15-sd-kv` (coord-1118).

2026-11-18. 026-23 registered: a second opinion on a simpler writer, by an
agent of coord-1118 (Frans, 11:51).

2026-11-18. 026-23 done: the comparison and a count on Java's traces.

2026-11-18. 026-22 registered and done: MT against the contract, a short
check by an agent of coord-1118 (11:53 to 12:40).

2026-11-18. 026-08 done: Frans's answers (10:52, "As recommended"); its
work on main since 2026-11-13, nothing to port (agent of coord-1118).

2026-11-18. 026-24 registered: the PE trial, by an agent of coord-1118
(Frans, 12:47).

2026-11-18. 026-24 done: the PE trial's result for Frans (go).

2026-11-19. Theme: proven algorithms (Frans), after the proofs of the
writer (030-21) and of reclaim (030-23 to 030-25). The stable stream
format waits for a later release, perhaps more than one release later,
together with encryption and replication (Frans).

2026-11-20. 026-01, 026-12, QM1 and PA5/PA9 moved to release 2026.8
(032), with the stream format, encryption and replication; their IDs
kept (Frans). Releases 2026.7 (031) and 2026.8 (032) created.

2026-11-20. 026-26 done: an independent hunt with eight Pub API apps, no
database fault; S4-B1 fixed as 028-41; the apps landed in apps.sh (an
agent of coord-1120).

2026-11-22. 026-27 written: the release plan, for the release on Tuesday
24 November.
