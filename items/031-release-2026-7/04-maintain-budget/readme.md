# 031-04. maintain(budget): a study

Created 2026-11-26 by Frans Lundberg. Status: open.

A study of a simpler `maintain()`: a call with a cost budget, and
reclaim passes that end by construction, so that BergDB no longer
decides by itself when its maintenance is done. Frans decided
(2026-11-26) to study this direction as a possible simple solution
before any decision on `maintain()`'s design: nothing of it is decided
for implementation. The study comes first; Frans decides the next steps
from it.

What was known: 031-03 (the witness, O-1, and Codex's review of it,
section 14), 031-01, 028-53, 028-54, 027-13 (reclaim, section 1.10 for
`maintain()`), 010-01 (P1, P2).


## 1. Why

`maintain()`'s difficulty is that BergDB decides, without being told,
when there is work and when it is done. That decision gave `main` its
two stretches and the 400 kB threshold (MIN_RELEASE), gave 031-03 its
drain for an emptied database, whose end is argued but not proved
(Codex's finding 1: with a step reserve of 1 the drain repeats), and is
the cause of RB-007. The direction below takes the decision away: the
application grants a budget, and a pass that a call begins ends by its
own construction.


## 2. The direction studied

As discussed with Frans on 2026-11-26; to be designed, built as a
prototype and measured, not decided.

* **The idle-time hook.** `maintain()` is the application's general
  call for the database's maintenance while it is idle: reclaim, the
  take (index nodes of the startup section), and later possibly the
  cache (dropping cold nodes) and other cleanup; not only reclaim.
* **A cost budget.** `void maintain(int budget)`. The budget is an
  indication of the work allowed in the call, in cost units; one unit
  is about the work of writing 1 kB to the stream. The value is clamped
  to a range, about 100 to 100,000 (100 kB to 100 MB). The database may
  use less than the budget, or none, depending on its state. The Pub
  API defines it loosely on purpose, so that the implementation may
  change without the API changing.
* **No return value.** A returned cost or boolean invites a loop that
  waits for it to drop, which a later release could break; users
  observe the effect on the database instead (the stream kept, below).
* **The old `maintain()` removed** (the Pub API is not yet kept
  constant between releases).
* **The cost model is internal** and may change: bytes read (perhaps
  charged less than written), bytes written to the stream, and other
  counts. What decides what is written is charged only by deterministic
  counts (bytes read as the logic reads them, cache hit or not; bytes
  written; KVs scanned; nodes visited), so that the stream's bytes do
  not depend on timing (P2). Charges of time or CPU only for work that
  writes nothing.
* **One iteration at a time.** A call continues an iteration in
  progress, also one that a commit began, by its steps within the
  budget; it begins none while an iteration runs or a done one waits
  for its cut.
* **A pass that a call begins cuts at its own start** (pCut := pStart,
  as the first iteration does today): one pass rewrites every live value
  stored before it, and its cut drops the stream before it. A commit's
  iterations keep today's pCut, the pStart of the iteration before.
* **When a call begins a pass:** no iteration runs or waits for its
  cut, and the stream kept still holds a record of the application's:
  w >= fp, with w read off the stream as 031-03's R1 to R3 do (no store
  of its own, no recovery case). After such a pass, with the
  application idle, w < fp and the calls go quiet; after a commit's
  iteration, at most one more pass. No drain, no MIN_RELEASE.
* **The user's model.** A full pass takes at most about the stream kept
  divided by the budget's bytes in calls, since a pass scans every live
  KV once and all live data lies in the stream kept; the space comes
  back once R has passed since the pass ended. Calls after that do
  little until the application writes again.
* **The stream kept** (L - fp) in the Pub API, as a getter: exact and
  free. With the live bytes, summed by an iteration's scan, kept / live
  is the space amplification; history (states the retain duration keeps
  readable) is not waste. In a database not written to for longer than
  R, kept - live is exactly the stream that reclaim can give back.


## 3. The study

By one agent of lead-1126 (Opus, xhigh), in a clone of `main`; Codex
reviews the result before Frans reads it. Its answers go in the
sections it adds here; a prototype on a branch, not on `main`.

1. **The design text**: each rule with what, when, by whom and how it is
   checked; the cost model and its determinism rule; what stays of
   `main`'s `maintain()` (the take, the filler, the sync, the cut).
2. **A prototype** on `main`, with the old `maintain()` removed and
   `maintain(int budget)` and the stream kept's getter added.
3. **Measurements**: RB-007's case (031-03's `HoleProbe`) and an
   emptied database; a database with live values not written to (quiet
   when done); Codex's case of 031-03 (step reserve 1, 150 keys of 111
   bytes at node size 8), which must end; the calls of a full pass
   against kept / budget, from small databases to 10 million keys; the
   longest call at 10 million keys and the budget's range; the same
   bytes over restarts between calls; stops and crashes at every record
   (031-03's probes, section 7).
4. **The Lean proofs**: whether the reclaim theorems, the contract and
   the checkers accept pCut = pStart for any iteration, not only the
   first; what would change.
5. **The counts and the format**: new state, stores, recovery cases and
   lines, next to `main` and 031-03's O-1; what changes in the stream's
   internal format.
6. **Open questions for Frans**, each with options and a
   recommendation: the getter's name; the live bytes in the rows; the
   cache's part; a commit's maintenance next to the calls'; the budget's
   range and default.


## Log

2026-11-26. Created by lead-1126 at Frans's request, from the
discussion of 031-03 with him: a study of the direction, not a decision.
