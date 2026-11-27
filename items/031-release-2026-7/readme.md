031-release-2026-7
==================

Created 2026-11-20 by Frans Lundberg. Status: open.

Release 2026.7 of BergDB, after 2026.6 (026): its plan, its decisions and
the work towards it. No theme yet: as with 2026.5 and 2026.6, the theme
and the scope settle as the work does, not in advance (Frans,
2026-11-20).

Created together with 2026.8 (032), so that work meant for after 2026.6
has a place before its release is planned. Work may move between 2026.6,
2026.7 and 2026.8 until a release's scope settles. Short tasks that no
release owns stay in 028; a release item says which 028 entries it
takes.

The release is made as 034 says, the process for every release (Frans,
2026-11-24): its steps (034-01), its checklist (034-02) and its scripts
(`items/034-releases/scripts/`). This item holds the release's plan,
scope and decisions, and says where it departs from 034.


Work for this release
=====================

What 2026.6 does not finish comes here, unless Frans decides otherwise.

* 026-03, a single maintenance step: not started in 2026.6; carried here
  on 2026-11-24 (026 done). Designed together with 028-53's
  fix in 031-01 (Frans, 2026-11-25).
* 026-04, the settings of reclaim's fraction: the values and the default
  not chosen in 2026.6 (1/4 kept); carried here on 2026-11-24.
* 026-14, the Lean model's scope and three additions: not decided in
  2026.6; carried here on 2026-11-24 (Frans).
* 028-49, the release scripts make the GitHub release's body with
  absolute links: needed before this release is made (from the review of
  2026.6, 2026-11-24); in 034's scripts since 2026-11-24.
* 028-67, a stale tail at a start: C1 and C3 (Frans, 2026-11-27),
  built in 031-06's landing, with the format's other changes.
* 031-07, the stream's checksums reviewed, the new 3-byte check of
  028-67 with them (Frans, 2026-11-27).


Files
=====

* [031-01](01-one-maintenance-path/readme.md): one maintenance path for a commit
  and `maintain()`, back to empty and quiet when done; the design of
  026-03 with 028-53's fix (RB-007).
* [031-02](02-app-hunt/readme.md): an app hunt on `main` before 2026.7, with
  new user applications and their oracles.
* [031-03](03-elegant-maintain/readme.md): an elegant `maintain()`: back to
  empty, quiet when done, through crashes and restarts without recovery
  machinery of its own.
* [031-04](04-maintain-budget/readme.md): `maintain(budget)`, a study: a
  call with a cost budget and passes that end by construction; a study
  before any decision (Frans, 2026-11-26).
* [031-05](05-writes-from-the-stream/readme.md): every write a function of
  the stream and the user actions, a study: P2 extended to maintenance and
  to anything that writes (Frans, 2026-11-26); answers 028-54.
* [031-06](06-one-record-an-action/readme.md): one record an action: an
  accepted action (a transaction, a setter, a part of `maintain()`)
  appends exactly one record, which holds the maintenance that reclaim
  owes; A1's (e), decided by Frans on 2026-11-27. Its files:
  * `readme.md`: the design as built in the prototype, its evidence, the
    decision, and the landing's plan (section 9);
  * `history.md`: why reclaim's writes were records of their own, from
    Frans's notes and logs of 2008 to 2016 and the Git history (quoted
    with his approval, 2026-11-27);
  * `study.md` and `study-d.md`: the studies of (e) and of (d), the
    compound unit, not taken; `codex-studies.md`: Codex's opinion on
    them;
  * `prototype.diff`, `probes/`, `runs/`: the prototype's code against
    031-05's, its probes and their output;
  * `review-fable.md`, `review-probes/`: the independent review of the
    prototype and its probes;
  * `p2-draft.md`: a draft of P2's extended wording, a proposal.
* [031-07](07-checksums/readme.md): the stream's checksums, a review: what
  each check detects and costs, and whether the node checksums stay, go
  or become one a record (Frans, 2026-11-27).


Log
===

2026-11-20. Created (Frans), with 032.

2026-11-24. 026-03 and 026-04 carried here from 2026.6, open (026 done).

2026-11-24. 026-14 carried here from 2026.6, open (Frans).

2026-11-24. 028-49 taken, for the release scripts (review of 2026.6).

2026-11-24. The release is made as 034 says, the process for every
release (Frans); 034 created.

2026-11-25. 031-01 created: 026-03 and 028-53's fix designed together
(Frans).

2026-11-25. A review by Codex of the Java changed since 2026.6 (11
commits, to `4ce8f942`): no new bug; RB-007 reproduced independently;
STM (028-01, 028-48), 028-50's refusal, PE's writes (028-19, the same
bytes as 2026.6's writer) and 028-51 found sound by probes that ran
(006-35).

2026-11-25. 031-02 created: an app hunt on `main` (lead-1125).

2026-11-25. 031-03 created: a search for an elegant `maintain()`; neither
028-53's A nor B (Frans).

2026-11-26. 031-04 created: a study of `maintain(int budget)`, from the
discussion of 031-03 with Frans; 031-03's F1 to F5 wait for it.

2026-11-26. 031-05 created: every write to the stream a function of the
stream and the user actions (Frans); a study on 031-04's prototype, which
answers 028-54.

2026-11-27. The release's focus (Frans): the algorithms in place,
`maintain()` and reclaim included; a bug hunt; clean-up; quality; the
documentation's update. The theme's wording is Frans's and not set yet.
031-06, a prototype of one record an action, is built (006-37); its
files come with its landing.

2026-11-27. 031-06 created: one record an action. Frans's focus of the
day was how a commit's maintenance is written (006-37, A1); the options
(c), (d) and (e) were studied, a prototype of (e) built and reviewed,
and A1 decided as (e) (031-06, section 8). The landing's plan is its
section 9. The internal crypto code left the tree the same day (028-69).

2026-11-27. 031-06: `history.md` added, the history of reclaim's own
records, with the passages of Frans's notes and logs that he approved
for publishing.

2026-11-27. A2 and A3 decided (Frans, 14:36; 031-06, section 8):
`maintain(int budget)` replaces `maintain()` in the Core and the Pub API,
and 2026.7 does not open a database of 2026.6. 028-67's C1 and C3 taken
into 2026.7, built in 031-06's landing (Frans, 16:02). 031-07 created:
the stream's checksums, a review.
