005-54. Investigate the bounds still open in the problem statement
==================================================================

Status: open. Kind: investigate. Created 2026-10-26.

Carried forward from the problem statement of 2026-10-12,
[011-01](../011-docs-archive/01-problem.md), "Open questions", when it left
`docs/` (006-07, as Frans approved: "Everything as recommended"). Of its
open questions, Q4 is item 007's, Q10 and Q11 are answered by item 001, and
Q12 is 005-06's. These five have no other home.


Questions
---------

1. Q1, the lookup bound. What is n in O(log n)? Nodes are split but never
   merged, so the tree keeps the size it once had, and nodes with no live
   keys stay in it. Decide which bound BergDB promises; the multiversion
   B-tree merges underfull nodes and gets O(log_B n_t).
2. Q2, long keys. Each 7-byte key segment has its own tree; state the bound
   with the key length as a parameter.
3. Q3, the cost model. Define the cost of a lookup (node accesses, cache
   misses, stream reads) and the model behind "cache-aware".
4. Q5, write overhead. Derive it as a function of D, n, B and the update
   pattern. Measured since 2026-10-12: with uniform random updates, 6 bytes
   appended per user byte at 1M keys and 9.9 at 10M keys, at a startup
   distance of 20 MB (011-04, "Level 2 under load"); 180 to 670 bytes of
   stream a put at 200 to 1000 MB, with 10M and 50M keys (005-38).
5. Q8, the space bound with reclaim. Derive a bound for the algorithm as
   built (the cut point before the scan, iterations a quarter of the retain
   duration apart) and choose its budget f by the trade-off between write
   and store efficiency. Measured: reclaim adds 26 to 38 percent of the
   stream writes (011-04, W4).


Done when
---------

Each question has an answer: a bound stated and proved (in Lean, as T3 is
in item 007), a measurement that Frans accepts as the answer, or Frans's
word that it is dropped.


First step
----------

Ask Frans which of them matter now. Item 007, bounds on BergDB's costs, is
the natural home for Q1, Q3 and Q5 (its T4).
