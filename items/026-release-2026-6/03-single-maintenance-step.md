# 026-03. One maintenance step, for a commit and for maintain()

Created 2026-11-12 by Frans Lundberg. Status: open, carried to release
2026.7 (031), which takes what 2026.6 does not finish: registered only,
not started in 2026.6.

For release 2026.6. Registered by the coordinator at Frans's request
(2026-11-12, 13:52: "For 2026.6, a new item for the single maintenance
step. Register it in 026 as recommended. Include the "the simple form,
ordinary transactions with filler" as a thing to consider.").


## 1. The question

Frans, 2026-11-12, 13:44, on `maintain()` (024-32): "Shouldn't
maintain() just do things already implemented. Could it use ordinary
transactions only for its actions? [...] Is maintain() called from
internal code. If not, should it? Could we have one single way to do a
maintain step?"

Release 2026.5 has `maintain()` as 024-32 built it (Frans, 13:52: "For
2026.5, land maintain() as built."): one call takes the write lock and
does at most one of each of M1 to M7 (024-32, section 2): begin an
iteration, one reclaim step without the commit's fraction allowance,
safe positions, a take to pEnd or pSafe (`TransSeq.takeTo`), a filler of
up to 200 kB when a cut waits only for a meta block, the cut (with a sync
outside the lock when the cut's table is not yet durable), one step of
eviction's dead hand. A commit does its own maintenance on its own path:
the take's share, reclaim's step within the fraction of the growth, the
cut when due, eviction. No internal code calls `maintain()`.


## 2. What to consider

* **One step with a budget.** One maintenance step that both paths call:
  a commit with a budget from its growth (reclaim's fraction of its
  bytes, the take's share of its own bytes), `maintain()` with a fixed
  budget. One mechanism for the tests, the conformance traces and the
  Lean model (010-01, P13; P4 maintenance proportional to the user's
  work). Its cost: a change at the heart of the commit path.
* **The simple form: ordinary transactions with filler** (Frans,
  13:52). `maintain()` commits an ordinary internal transaction, a put
  and a delete of an internal key with some filler bytes, and the
  ordinary per-commit maintenance does the rest: the growth gives
  reclaim's step its allowance, the record's own bytes give the take its
  share, the stream reaches the next meta block, and the sync follows the
  database's sync policy as for any commit. Its cost: stream bytes for
  each call. Not tested: whether the cut's wait for a durable table is
  met in an idle database without `maintain()`'s own sync.
* **The sync inside `maintain()`** (024-32, Q32-4): needed today because
  an idle database has no commit that makes reclaim's table durable; it
  may go with either form above.
* **The tests to keep**: 024-30's G5 (back to empty by `maintain()`
  alone, 254 MB to 83 kB of stream at 1M keys), G4, and 024-32's
  conformance configurations `r-maint` and `e-r-maint`.


## 3. State

2026-11-12, 13:52: registered only; nothing started. Sources: 024-32
(the design note, section 2; Q32-1 to Q32-5, accepted as built for
2026.5), 024-30 (G4, G5).

2026-11-24. Status set after the release (lead-1124).
