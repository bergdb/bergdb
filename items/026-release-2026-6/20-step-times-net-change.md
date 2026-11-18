# 026-20. Two writer designs for 2026.6: step times and net change

Created 2026-11-18 by Frans Lundberg. Status: written down; a first study
of both proposed (026-21), for Frans to decide.

From coord-1117's discussion with Frans, 2026-11-18, 06:43 to 08:49, in a closed
session. For coord-1118. The reasoning is coord-1117's; Frans's words are quoted.

## Frans's decision and question (08:49, verbatim)

"About the "step times" design idea. The writer's proofs are deleted and we go back
to the contract. Today, I see two ways forward. Either we start investigating Net
Change. Or we investigate Step Times. Not sure which to start with, or a first study
of both, before we decide the direction of the implementation."

Earlier (06:33): "I am planning on working with other things. Want to consolidate and
stabilize. So, I am considering either to remove the writer's proof or finish it. I
want a proven model." And (07:31): "Would be good to get rid of the take-back."

So: the writer proofs (030-10, 030-16: lean/contract's Writer*, TreeRules*, the link
books; about 36,000 of lean/contract's 58,300 lines, 44 files) are to be removed from
main (a tag first, so they can come back); the contract and its proofs stay (about
22,300 lines: reads, scans, top search, recovery, restarts, lazy reading, eviction,
safe cuts, reads after each, the checkers). Those proofs do not depend on how the
writer applies a transaction, so they hold for either design below; only a few bridge
clauses that describe how changes are marked (touch rules, A-COPY, W1-W5, "made by
transaction i at time i", at most one new root per transaction, D) might need
restating. The checkers (contractcheck, bridgecheck, Java's TransCheck) show it
mechanically on the new writer's traces. Note: lean/contract's writer files import two
files of lean/SIS/Tree (the old proofs); with them gone, the old proof line can go too.

## Why: where the writer's complexity is (from tonight's proofs)

Within one transaction, the writer applies the operations one at a time, all at the same
time i. A node holds one version per time, so a later operation rewrites the version an
earlier one made, and a node made earlier in the transaction that a later operation
makes unreachable must be removed before the record is written: the take-back. Between
operations the writer is in a half-finished state; 13 to 14 books (B1-B14), the link
books (WcrLink, WmgFresh, ...), R3 and ValOld all describe those states. Also complex:
the merges' cascade (a merge with a full parent; MergeVirt; WmgRestOk still open), the
same recursion proved three times in the puts (about 5,000 lines could go), the
variants of each split (in place, dead klongs), segments. The fill rule is not needed
for correctness (the contract has none): merges only keep the index small.

## Design 1: net change

Compute the transaction's final operation per key first (the last put or a delete),
then apply each key's final change once.

- Removes: churn on the same key (put then delete of k).
- Does not remove: the take-back between different keys at the same time (a split made
  for one key can be emptied by a delete of another key in the same transaction). So it
  reduces the take-back; it does not end it. (coord-1117 first said it would remove it;
  that was wrong, corrected in the session.)
- Format: no change. Reads: no change.
- Variant, "deletes apart": a transaction's deletes and puts at two internal times (after
  the net change): removes put/delete interactions, keeps delete/delete ones (merges make
  nodes); needs internal times like design 2; the Pub layer's updates (delete the old
  index entry, put the new) make most transactions mixed.

## Design 2: step times

Terms (Frans, 08:14: liked "step", "internal time", "step time"; not "sealed"):
- transaction time: what users see and look up at;
- step: a counter within a transaction;
- step time (internal time): the packed time, transaction time and step together, what
  klongs carry;
- fresh node: a node made at the current step.

The rule: the writer never changes or drops a fresh node; it starts a new step first.
Entries added to an old node at the current step are fine (a new version of an existing
node), so most operations share a step; a new step starts only after a split or merge
made nodes that a later operation (or the same operation) reaches.

- Removes the take-back entirely, and with it most of the books, R3, ValOld: each step
  goes from a finished tree to a finished tree; the writer proof becomes per step, with
  the contract's invariants only.
- Format (Klong.java): a time klong is 2 bits of type, 6 reserved bits (56-61, zero
  today) and a 56-bit time: 62 bits for time. Pack 48 bits transaction time (2.8e14
  transactions; 89 years at 100,000 a second) + 14 bits step (16,384 steps; bound:
  500 operations x a few bumps each; the writer refuses a transaction past it, as past
  500 operations). Klongs stay 64 bits; only the time klong's layout changes (key klongs
  carry no time). Comparisons stay one 64-bit compare.
- Lookups: the API keeps transaction times; one function maps a user time T to
  (T << 14) | 0x3FFF, "the end of T": users cannot name an internal time, no table of
  external times, no rounding. Records stay one per transaction (recovery unchanged).
- The proofs: reads are proved at every step time, so they hold at the external ones.
- Risks, most serious first:
  1. bytes and node fill: after a bump, later changes add versions (time klong +
     entries) instead of rewriting in place; nodes fill faster, more time splits, more
     dead klongs, more stream bytes, more of the startup distance; possible feedback
     (splits make fresh nodes make bumps). Bad cases: sorted bulk loads; the Pub
     layer's index updates.
  2. the rule inside one operation: a bump in the middle of an operation (a merge
     cascade) would end a step in a state that is not a finished tree, bringing back
     half-finished invariants. Safer: bump only between operations, and make each
     operation never change or drop nodes it made itself; whether every delete path
     (merge cascade, root collapse) can work so must be checked in Dag.java. The main
     open design question.
  3. time arithmetic bugs (t+1, t-1, "the time before" on raw times: retention, first
     available time, lookup time, the Pub layer's history): use a Time type.
  4. top nodes and skip pointers: several top nodes per transaction possible; TP24's
     proof (about 420 lines) and "at most one new root per transaction" restated.
  5. reclaim's cuts, the first available time and the startup position must fall on
     transaction ends.
  6. known costs: the trace format and its checkers, TransCheck, the Lean model writer,
     the C clone (012).

## The comparison (coord-1117's table)

| Option | Take-back left | Extra internal times |
|---|---|---|
| today | everywhere | none |
| net change only | between different keys | none |
| deletes apart (+ net change) | between deletes | at most 2 per transaction |
| step times | none | after splits or merges that later operations reach |
| unique operation times | none | one per operation |

A fixed cap (at most m operations per time) does not help the proofs: m = 2 already
has all the half-finished states.

## coord-1117's suggestion for the first study

Both can be measured cheaply in the Lean model before any Java change: change the
model's executable writer (lean/SIS/Tree, Exec.lean, which matches Java node for node on
traces) to (a) apply the net change and (b) follow the step-times rule, and run both on
the existing traces (level 2, reclaim, medium, large; and a Pub-like workload of index
updates, and a sorted bulk load). Count: take-backs left (net change); steps, extra
versions, extra stream bytes, node fill, splits (step times); any operation that would
have to touch its own fresh nodes (step times, risk 2). About a day for one agent each;
the numbers decide 2026.6's writer. The contract's checkers run on the new traces too.
