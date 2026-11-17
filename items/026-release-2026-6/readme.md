026-release-2026-6
==================

Created 2026-11-11 by Frans Lundberg. Status: open.

Release 2026.6 of BergDB, after 2026.5 (024): its plan, its decisions and
the work towards it. Its preliminary theme: **simpler algorithms**
(Frans, 2026-11-16, 10:26; the study behind it is 006-28).

The stream format's draft specification is 027-03 (024-02 until
2026-11-13), kept up to date with the code.

Work moved here from 2026.5:

* **A compact stored form of the index nodes** (026-01, moved from
  024-20 on 2026-11-12; Frans, 2026-11-12, 07:26, QC1: "For 2026.6 as
  recommended. QC2,3,4,5 should wait since it is for 2026.6."; 07:39:
  "In particular this 024-20 should move there."): encoding C keeps 38
  to 47 % of the index bytes; with compact value nodes, frames and top
  nodes the stream is 19 to 52 % smaller. Its questions QC2 to QC5 (the
  accounting, the startup distance's unit, reclaim's charge, delta
  writes) wait for this release's work on the format.

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
  format** (024-22, QM1; Frans, 2026-11-13, 09:23: "Yes, decided work."):
  the other way than P5's new nodes and take-back, which changes what a
  record means; 2026.5 has P5's way (Frans, 2026-11-11, 14:34). Decided
  work means it is settled in 2026.6, with measurements, not that the
  merge changes.
* **The startup distance out of the meta block, into an internal KV**
  (028-15; 026-12, SF7 (a); 024-01, OT4; Frans, 2026-11-16, 10:32:
  "There is still a stream format change that I want to get in place in
  the next release. The startup distance!"): the meta block's bytes 40
  to 43 reserved, and `/#i/-dummy`'s 200 kB at each change gone.
* **The versioning and compatibility rule and the corpus of saved
  databases** (027-03, section 21, V-A to V-D, and 21.3; Frans,
  2026-11-13, 09:23: "Yes, decided work."): a stable format needs its
  rule; 026-08's node-size field, kept as a hook for a later release,
  is a first case.


Proposed for 2026.6, not decided
================================

Each stays where it is until Frans decides; recommended for 2026.6
there, or implied by this release's theme.

* **The stable format's open questions of the first theme** (024's Log,
  2026-11-10, the reading of 19:52, accepted for "a stable stream
  format"): the startup distance in a KV (024-01, OT4, "with a format
  change"; decided 2026-11-16, 028-15, above) and a place reserved
  for objects' storage and encryption (024-01, PA5, "study only", and
  PA9, "not in 2026.5").
* **Commits give a mass delete's space back by the clock, as
  `maintain()` does** (026-13, U13-4 and Q1, option B; Frans, 2026-11-13,
  13:07): a commit begins a reclaim iteration also on `maintain()`'s rule
  (a quarter of R, a cut that releases 400 kB), so that `maintain()` is
  optional in effect for a slowly written database. A study first: G4 at
  026-13 C2's settings and at its own, before and after; taken only for a
  clear gain. The Javadoc of today's behaviour is 028-06.


Files
=====

* 01-compact-nodes.md. 026-01, a more compact stored form of an index
  node, moved from 024-20 on 2026-11-12: measured on record format 7,
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
  (59c6e4b6).
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
  (bfb6d018); the probes in 07-write-buffer/.
* 08-fixed-node-size.md. 026-08, the node size fixed at 30 for users,
  the other sizes for tests only (Frans, 2026-11-13, 09:21): the four
  `DbBuilder.maxNodeSize` setters package-private, `TestNodeSize` for
  the tests outside `bergdb.core`; on main since 2026-11-13 (000fca5b).
* 09-keys-only-scan.md. 026-09, reclaim's scan without the values it
  does not rewrite (024-34, Q34-1, option b; Frans, 2026-11-13, 09:38):
  `GetMany.valuesBefore`; the steps' loads 44 to 60 % fewer, the steps
  14 to 20 % fewer, at 10M keys 1 to 4 % more stream written; on branch
  `026-09-keys-only-scan`, to land (Q1, recommended) with Q2 to Q4.
* 10-node-id-cache-after-empty.md. 026-10, `NodeCollection.idByPos`
  after back to empty (found by 026-07): a decided cut forgets the node
  ids below it and `KeyModSet`'s key hashes before it (the 2.2 MB of
  `long[]`), and G4 and G5 gate the plain heaps. On main since
  2026-11-13 (e4ac051f); the probes in 10-node-id-cache-after-empty/.
* 11-lag-gate.md. 026-11, G4's back-to-empty lag a gate of
  `count-gates.sh`: at most 2 R (2,000 drive transactions) at 1M keys;
  1,281 on `main` (margin 1.56), 4,395 without 026-05 (fails); on main
  since 2026-11-13 (343fff05).
* 12-stable-format-plan.md. 026-12, the stable stream format: a draft
  plan for Frans (10:24): 11 questions, SF1 to SF11, merged from 027-03's
  Q1 to Q23 and section 21, 026-01's QC2 to QC5, 024-22's QM1, 024-01's
  OT4, PA5 and PA9, 017-08 and 017-11; each with its options, what it
  depends on and a recommendation; the decisions already taken quoted;
  the order, and three measurements (M1 to M3); none decided.
* 13-user-apps.md. 026-13, a round of "AI as the user" testing (006-20)
  against 2026.6's changes on `main` (026-02, 026-05, 026-06, 026-07,
  026-08): twelve programs with their own oracles, SIGKILLs of child
  JVMs; no bug in BergDB; U13-1 to U13-6, Javadoc findings and one
  question (Q1: commits pace reclaim by the stream, `maintain()` by the
  clock); proposed 028-todo entries. The apps in 13-user-apps/.

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
