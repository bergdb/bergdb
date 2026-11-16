# 006-28 Simpler algorithms for simpler proofs: a study

Created 2026-11-16 by Frans Lundberg. Status: open.

Where the complexity of BergDB's algorithms really is, measured by the
Lean model and its proofs, and the changes to the Java code that would
make the proving significantly easier: the top three.

Frans, 2026-11-16, 08:26: "Simpler algorithms for simpler proofs. Study
the current algorithms of BergDB and how they could be simplified to
simplify the proofing. We have measured complexity and API surface,
amount of Java code and so on. But now when we have a Lean model, it
seems like a good time to check where to complexity is really. Can we
make changes to the Java code to make the prooving significantly easier.
What are the top three changes that would simplify the most. The
assumption is that the Core layer stays approximately the same or scans
are removed. Scans at the Core layer could be removed and we would still
be able to implement scans on top of getOne(). We would not get O(1)
amortized per kv, but O(log(n)) per kv where n is the database size
(total number of kvs)."

**The coordinator's defaults** (coord-1116, 08:40; Frans may overturn
them):

* The whole model, not only the open premises. 026-16 was the narrow
  study (the premises open on 14 November, keeping what is proved); its
  section 9 lists leads for this one.
* Two measures of "easier": the work left from today's `lean/` to the
  goals of 006-26, section 8; and the size of the proofs from scratch
  for the changed algorithm (025-01's model-first rewrite).
* Changes to the stream format may be proposed, marked as such (026-12).
* Lower performance may buy simplicity (Frans, 2026-11-14, in 026-16:
  "The KISS principle allows us to buy simplicity with lower
  performance."), but not a significant loss at large databases (1M to
  100M keys); the cost of each change is stated.

The study follows.
