028-06. Fix: what maintain() adds, and how reclaim is paced, in the Core's Javadoc
==================================================================================

Status: done (2026-11-13). Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: `Db.maintain()` speaks only of a database no longer written to, and
calls its result "about the stream of a fresh one";
`Db.setRetainDuration()` and `Db.setStartupDistance()` do not say that the
startup distance paces reclaim.

Why: after a mass delete with slow writes, calls bring the space back many
times sooner (C2: 1.2 MB kept at 2 R with them, 6.4 MB at 10 R without),
as the Pub's `Database.maintain()` says in part ("deleted much and then
writes little or nothing"); and "about" is within about 400 kB, by
`maintain()`'s own 400 kB rule.

Frans: none.

Done when: `Db.maintain()` says, as the Pub's does, that calls help a
database written to slowly, and "within about 400 kB";
`Db.setRetainDuration()` says how commits pace reclaim (the Pub's
paragraph in the Core's terms).

First step: C2's two runs.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-4, U13-5; Q1, option A).

2026-11-13. Frans (13:07) chose 026-13's Q1, A: this entry, now; B, the
behaviour change, is a proposal in 026's readme.

2026-11-13. Done by an agent of coord-1113, in the commit "028-03, 028-05, 028-06: the write buffer, the transformations and
maintain() in the Javadoc (documentation only)" on branch 028-jdoc:
`Db.maintain()` now says that commits give the space back only as they
grow the stream (an iteration begins after more than twice the startup
distance), that calls begin iterations by the clock and so help a
database written to slowly after a mass delete, with C2's figures (6.4
MB at 10 R without calls, 1.2 MB at 2 R with them), and "within about
400 kB of the stream of a fresh one", by `Reclaim.MAINTAIN_MIN_RELEASE`.
`Db.setRetainDuration()` has a paragraph on how commits pace reclaim,
the Pub's in the Core's terms, checked against
`Reclaim.transactionCompleted()` and 027-13, sections 1.2 to 1.7;
`Db.setStartupDistance()` says that the setting paces reclaim. The Pub's
`Database.maintain()` says "within about 400 kB" too. `java/before-commit.sh` printed `BEFORE COMMIT OK`.
