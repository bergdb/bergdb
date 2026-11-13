026-release-2026-6
==================

Created 2026-11-11 by Frans Lundberg. Status: open.

Release 2026.6 of BergDB, after 2026.5 (024): its plan, its decisions and
the work towards it. Its preliminary theme: **a stable stream** (Frans,
2026-11-11, 06:56: "Create an item for release-2026-6. The preliminary
theme of the release is "a stable stream". Keep it short, we will add to
it later.").

The theme was first that of 2026.5 (Frans, 2026-11-10, 19:54) and moved
here when 2026.5 became "solid algorithms" (024-04): the stream format is
the algorithms' output, so it is made stable when they have stopped
moving. The specification's draft is 027-03 (024-02 until 2026-11-13),
kept up to date with the code.

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
  change") and a place reserved for objects' storage and encryption
  (024-01, PA5, "study only", and PA9, "not in 2026.5").


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
  `keyBytes` and `checkKey`, no `levelBytes`; on branch `026-02-limits`,
  to land.
* 03-single-maintenance-step.md. 026-03, one maintenance step for a
  commit and for `maintain()`, and the simple form (ordinary
  transactions with filler) to consider (Frans, 2026-11-12, 13:44 and
  13:52; from 024-32).
* 04-reclaim-fraction-settings.md. 026-04, reclaim's fraction: measured
  at larger databases, three recommended values and one default
  (Frans, 2026-11-12, 14:07; 2026.5 keeps 1/4).
* 05-reclaim-step-time.md. 026-05, each reclaim step scans at its own
  time (P8 of 023-05, with 023-08's fault 13 fixed): the change on a
  branch, the cut's argument, the gates, and back to empty's lag after a
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
  11.1 MB (024-05, ST8; 024-01, PA7). Code on branch
  `026-07-write-buffer`; the probes in 07-write-buffer/.
* 08-fixed-node-size.md. 026-08, the node size fixed at 30 for users,
  the other sizes for tests only (Frans, 2026-11-13, 09:21): the four
  `DbBuilder.maxNodeSize` setters package-private, `TestNodeSize` for
  the tests outside `bergdb.core`; on branch `026-08-node-size`, to
  land.
* 09-keys-only-scan.md. 026-09, reclaim's scan without the values it
  does not rewrite (024-34, Q34-1, option b; Frans, 2026-11-13, 09:38);
  registered, after 026-05.
* 10-node-id-cache-after-empty.md. 026-10, `NodeCollection.idByPos`
  after back to empty (found by 026-07; G4 and G5 then gate the plain
  heaps); registered.
* 11-lag-gate.md. 026-11, G4's back-to-empty lag a gate of
  `count-gates.sh`: at most 2 R (2,000 drive transactions) at 1M keys;
  1,281 on `main` (margin 1.56), 4,395 without 026-05 (fails); on branch
  `026-11-lag-gate`, to land.
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
