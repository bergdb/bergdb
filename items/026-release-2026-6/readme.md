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

* **A compact stored form of the index nodes** (024-20; Frans,
  2026-11-12, QC1: "For 2026.6 as recommended"): encoding C keeps 38 to
  47 % of the index bytes; with compact value nodes, frames and top nodes
  the stream is 19 to 52 % smaller. Its questions QC2 to QC5 (the
  accounting, the startup distance's unit, reclaim's charge, delta
  writes) wait for this release's work on the format.


Files
=====

None yet.
