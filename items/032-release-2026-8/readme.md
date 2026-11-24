032-release-2026-8
==================

Created 2026-11-20 by Frans Lundberg. Status: open.

Release 2026.8 of BergDB, after 2026.7 (031): its plan, its decisions and
the work towards it. Preliminary theme: **the stream format, with
encryption and replication**. The stable stream format waits for a
later release than 2026.6, perhaps more than one release later, and is
to be looked at together with encryption and replication (Frans,
2026-11-19). If 2026.7 turns out to be the time for it, the work moves
there; work may move between 2026.6, 2026.7 and 2026.8 until a release's
scope settles (Frans, 2026-11-20).

The stream format's draft specification is 027-03, kept up to date with
the code.

The release is made as 034 says, the process for every release (Frans,
2026-11-24).


Work for this release
=====================

Moved from 2026.6 on 2026-11-20 (Frans). The subitems keep their IDs and
stay in 026's folder, so that the many citations of them stay valid;
this list is where they belong now.

* **The stable stream format's plan** (026-12,
  `../026-release-2026-6/12-stable-format-plan.md`): the draft plan of
  2026-11-16, eleven questions SF1 to SF11 with options and
  recommendations, merged from 027-03's Q1 to Q23 and section 21,
  026-01's QC2 to QC5, 024-22's QM1, 024-01's OT4, PA5 and PA9, 017-08
  and 017-11; the start of this release's work on the format. SF4 and
  SF7 (a), the startup distance in an internal KV, were decided and made
  in 2026.6 (028-15).
* **A compact stored form of the index nodes** (026-01,
  `../026-release-2026-6/01-compact-nodes.md`, moved from 024-20 on
  2026-11-12): measured on record format 7, encoding C keeps 38 to 47 %
  of the index bytes; with compact value nodes, frames and top nodes the
  stream is 19 to 52 % smaller. A change of the stored form, best made
  once, with the rest of the format. Its questions QC2 to QC5 (the
  accounting, the startup distance's unit, reclaim's charge, delta
  writes) are part of 026-12.
* **Merges "in place and net", studied and decided with the stable
  format** (024-22, QM1; decided work since 2026-11-13: settled with
  measurements, not that the merge changes). Since record format 8 the
  writer is PE (026-25), which has its own joins; the study starts from
  PE.
* **A place reserved for objects' storage and encryption** (024-01, PA5,
  a study, and PA9): one of the stable format's open questions of
  2026.5's first theme.

* **The versioning and compatibility rule and the corpus of saved
  databases** (027-03, section 21, V-A to V-D, and 21.3): decided work
  for 2026.6 (Frans, 2026-11-13), not made there; moved here on
  2026-11-24 (Frans), with the stable format it belongs to. 026-08's
  node-size field, kept as a hook, is a first case.

To register when the work starts: a study of encryption and a study of
replication, each with what it asks of the stream format.


Log
===

2026-11-20. Created (Frans), with 031. 026-12, 026-01, QM1 and PA5/PA9
moved here from 2026.6 (Frans), their IDs kept.

2026-11-24. The versioning rule and the corpus (027-03, section 21)
moved here from 2026.6 (Frans).

2026-11-24. The release is made as 034 says (Frans); 034 created.
