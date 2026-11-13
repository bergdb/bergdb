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
moving. The specification's draft is 024-02, kept up to date until then.

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
  not gated, until then.
* **A value transformation that throws or passes 8 MiB refuses the
  transaction instead of failing the database** (024-35, finding 2;
  010-04, R5; Frans, 2026-11-12, 14:42: "Yes to R5 and for 2026.6. I
  don't see it as a bug, but something to change anyhow."): run the
  Core's value transformations before the go point, as 024-16 did for
  key transformations (`Db.transformKeys`). 2026.5 names it in its
  Known issues.


Proposed for 2026.6, not decided
================================

Each stays where it is until Frans decides; recommended for 2026.6
there, or implied by this release's theme.

* **The node size read from the meta block** (024-19, Q5; 024-02, Q19):
  a start takes B from the meta block. Recommended "yes, but in 2026.6
  with the stable stream format"; open.
* **Merges "in place and net"** (024-22, QM1): the other way than P5's
  new nodes and take-back, which changes what a record means. Decided:
  P5's way in 2026.5 (Frans, 2026-11-11, 14:34); the other way "a
  candidate for when the format is made stable (2026.6)".
* **The versioning and compatibility rule** (024-02, section 21, V-A to
  V-D, "2026.5's rule", none decided) and the corpus of saved databases
  (024-02, section 21.3): the stable format's own questions, written
  under 2026.5's first theme; 024-02 stays in 024 until then.
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
  options and a recommendation, no code yet.
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
  mass delete before and after (024-05, OP9; 026-04, section 4).
* 06-value-transformation-refusal.md. 026-06, a value transformation
  that throws or passes 8 MiB refuses its transaction, before the go
  point (`Db.transformValues`), and the database goes on (010-04, R5);
  also a key transformation that throws (Q2); done, on main since
  2026-11-13 (Q1 to Q4 yes, Frans 08:45).


Log
===

2026-11-11. Created the item (Frans, 06:56), theme "a stable stream"
(preliminary).

2026-11-12. 024-20 moved here as 026-01 (Frans, 07:39: "go through the
current work and move things for 2026.6 to 026. In particular this
024-20 should move there."); the rest of 2026.5's work proposed for
2026.6 but not decided listed above.
