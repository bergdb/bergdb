# 026-18. Main transactions and subtransactions: an idea

Created 2026-11-16 by Frans Lundberg. Status: open (an idea, written
down to pick up later; nothing decided, nothing started).

A main transaction is an atomic sequence of subtransactions: one user
subtransaction, then zero or more maintenance subtransactions. Readers
see only the states between main transactions, never the states between
its subtransactions. Each subtransaction is simpler to understand,
model, change, implement and prove than one transaction that does
everything. Frans's idea of 16 November, from MT's trial (026-17).


# 1. Frans's words

Frans, 2026-11-16, 12:54, on the coordinator's remark that under MT the
readers' proofs "would also have to cover trees with empty nodes at those
in-between moments":

> I thought about this already. There is no reason to expose these
> "in-between" states to readers. In general we can think of it like the
> following.
>
> A user transaction specificiation is checked for correctness at entry
> (can throw IllegalArgumentException if badly specified, as an
> example). Then is it checked against the STM state. If approved, it is
> given a transaction time and passes the go-point from which it cannot
> be cancelled. It than runs its read and write (put and delete)
> operations. We can all this a user transaction, a subtransaction of the
> whole transaction. Then zero or more maintenance transactions are run,
> also subtransactions of the main transaction. The main transaction runs
> the sequence of subtransactions as one atomic unit. Read operations do
> not see state between subtransactions, only between the main
> transactions.
>
> The reason to split the main transaction into a sequence of
> subtransactions is to make each transaction step (subtransaction)
> simpler. Simpler to understand, model, change, implement, and prove.
>
> Let me know what you think about this concept. Don't go ahead and
> change the current plans. I just want your opinion of this for now.

Frans, 13:11: "For now, I just want this idea written down somewhere so
we can pick it up later. A "short proof trial" does seem reasonable.
Perhaps starting tonight after 22.00, we will see. Depends on other
work."


# 2. Where it comes from

- **MT** (006-28, section 7.5): a user transaction makes no merge, no
  upward delete and no root collapse; each of those is a fix step, a
  transaction of its own, run right after it. Nothing is then made and
  left out inside one transaction, the take-back's cause.
- **MT's trial** (026-17), in the Lean model only. By 12:34 every check
  that the plan makes held: no node made and left out, gets and scans
  right, the fixing ending in a tree with today's invariants, at node
  size 30 (families A to H, 32,017 boundaries) and node size 8 (298,235
  boundaries). The cost at 30: 0.082 fix steps a deleted key; the bytes
  1.05 to 1.06 times today's (1.15 to 1.17 for mass deletes, 1.01 to
  1.02 for the mixed family C). The definitions are about the size of
  today's writer (step T7). The result, step T8, is not written yet.
- **The finding that led here.** After a mass delete, a scan at a
  boundary between a user transaction and its last fix step crosses many
  empty leaves. Java's scan has no step budget and stays right, by
  reading; the model's scan has one, which assumes a live key below
  every index node (TP27), and ran out. The trial went on with "rule
  added A1", a larger budget in the model. With this idea the readers
  never see those states, and no reader changes.


# 3. The coordinator's view

Given to Frans on 16 November, before 13:11 (coord-1116). An opinion,
not checked in Lean or Java.

**Why it is right.**

- **It settles the trial's open point.** Readers that see only the
  states between main transactions never meet the in-between trees.
  Every check at those boundaries was green in all of the trial's runs.
- **It gives the proofs a good shape: two invariants.** Between main
  transactions, today's full invariant (the fill, the live counts, the
  heights, a live key below every index node). Between subtransactions,
  the same with holes on the paths of the keys still being fixed. Each
  kind of subtransaction gets its own small step lemma. The readers'
  theorems are stated only where the full invariant holds, so today's
  proofs of gets and scans carry over. The holes are small to state: the
  trial's check of them (K5) is about 20 lines. Splitting one big atomic
  step into small ones with a stated invariant between them is a known
  way to make proofs tractable.
- **BergDB already has the pattern.** Reclaim writes only in internal
  transactions of its own, up to five after a user transaction, each
  with its own time (027-13). The idea gives that pattern one meaning:
  MT's fix steps, reclaim's steps, `maintain()`'s filler and the
  startup distance's KV (028-15) are all maintenance subtransactions.
- **It fits how reading works.** Readers read at a time that is
  committed; the idea moves "committed" to the end of the main
  transaction.

**How it could be made exact** (for a design note):

- **Each subtransaction keeps its own internal time and record**, as in
  the trial. The abstract model's theorems (recovery, restarts, lazy
  reading, eviction) then hold for each subtransaction as they are, and
  one notion is added: a visible time, one that ends a main
  transaction. Readers and the user's API use only visible times.
- **Atomic in the stream means whole groups.** A start drops a main
  transaction that did not end, as it drops a torn tail. That is simpler
  than 006-28's "the start goes on with the fixing", and readers and
  recovery then use the same notion of a boundary. The stream must show
  where a group ends.
- **The order:** the structure's fix steps first, then reclaim's steps,
  so that reclaim always starts from a tidy tree and its argument (which
  uses TP27) stays as it is.
- **The words:** "transaction" is one record with one time in today's
  code, 027 and the model. Names for the whole and for its parts, chosen
  early, keep 027 clear.

**What it does not solve, and what it costs.**

- **The user subtransaction keeps a little bookkeeping.** A node changed
  by one operation and split by a later one in the same user
  subtransaction still loses entries by `toPrev` (026-17, step T7). The
  idea could go further: the splits too as maintenance, so that a user
  subtransaction only writes entries. The catch: a node above the size
  limit between subtransactions, which memory and the format must allow.
- **Bytes:** in the model, about 5 % more over all workloads, 15 to 17 %
  more for mass deletes (stand-ins for the records' bytes). Not measured
  in Java.
- **New mechanisms:** where a group ends in the stream; visible times in
  the API (`getTrans` at an internal time); a proof that the fixing ends
  (the trial's fuel is a guard, not a proved bound).
- **The definitions are not smaller** (026-17, step T7: MT's writer
  about the size of today's). The gain is in the proofs, and that is an
  estimate so far.


# 4. Open questions

- Internal times for each subtransaction and visible times, or one time
  for all of a main transaction's subtransactions.
- How the stream marks a group's end; what a start does with a group
  that did not end.
- What the API shows of internal times (`getTrans`, the time a commit
  returns).
- Which maintenance belongs: MT's fix steps, reclaim's steps,
  `maintain()`'s filler, the startup distance's KV (028-15); the splits?
- The bound on a group's fix steps, and its proof.
- The cost in Java at 10M keys, worst cases first.
- The names.


# 5. A next step, proposed

**A short proof trial**, one or two prover-days, on the trial's branch
`026-17-mt-trial` (`Mt.lean`):

1. A step lemma: one fix step (a merge) keeps the in-between invariant,
   the full invariant with holes on the paths of the keys still being
   fixed.
2. Gets and scans right at visible times from the full invariant,
   reusing today's proofs.
3. If time allows: the holes close when the driver ends, for one key.

It turns the proofs' gain from an estimate into evidence before a
decision. Frans, 13:11: "Perhaps starting tonight after 22.00, we will
see. Depends on other work." Not decided.


# Log

2026-11-16. Written by coord-1116 from Frans's words (12:54 and 13:11)
and the coordinator's reply to the first; nothing else done.
