/-
Self-indexed streams in Lean: bounds, part 1, BergDB's take with its byte limit
(`TransSeq.take`'s `maxBytes`; bergdb item 007; 007-09's second review).
Trusted part: the definitions. The theorems are in
SIS/BoundTakeBytesTheorems.lean, the proofs in SIS/Proof/BoundTakeBytes.lean,
the counterexamples in SIS/BoundTakeBytesExample.lean. Added 2026-11-13.

Why. `takeLoop` (SIS/Bound.lean) leaves the byte limit out ("Left out of the
model, as 007-03's step 4 says: the record limit (`take`'s `maxBytes`), which
stops the take before a transaction whose nodes would not fit in the record,
also past the deadline"). The second review: "the abstract take always honors
its deadline; Java's `TransSeq.take` says a transaction exceeding `maxBytes` is
skipped 'also after the deadline'. Establish that this cannot interrupt
required progress before applying T3 to current Java."

Java (`TransSeq.take`, java/src/bergdb/core/TransSeq.java): "The taken nodes
add at most 'maxBytes' bytes to the record (2026-10-21, bergdb 005-17): a node
counts its size in the stream and 16 bytes, for its entry in the got-dirty
list if it is still dirty. The first transaction that does not fit is not
taken, also after the deadline." In its loop, after the deadline-and-share
test:

    if (maxBytes != Long.MAX_VALUE) {
        final long cost = recordBytes(first);
        if (bytes + cost > maxBytes) {
            break;
        }
        bytes += cost;
    }

So it is not a skip: the take ends there, and the transactions after it are
not taken either.

Here a transaction's cost is `nodeB` per got-dirty node (D's entries with d(x)
= j, as `takeLoop` counts them): BergDB's nodes have a bounded size in the
stream, so `nodeB` is that bound plus 16. The limit `maxB` is a constant here
(in Java, the record limit less the record's own part).
-/
import SIS.Bound

namespace SIS

variable {V T : Type}

/-- The take's loop with the byte limit (`TransSeq.take`'s `while` with
`maxBytes`): as `takeLoop`, with `used` the bytes taken so far; a transaction
j that the deadline or the pace takes is taken only if its nodes, `nodeB`
bytes each, fit in what is left of `maxB`; else the take ends. -/
def takeLoopB (size : Record V T → Nat) (d : Nat) (pace : Nat → Nat → Bool) (nodeB maxB : Nat)
    (S : Stream V T) (D : Dirty) : List Nat → Nat → Nat → Nat → Nat
  | [], _, _, acc => acc
  | j :: js, taken, used, acc =>
    let count := (D.filter (fun e => e.2 == j)).length
    if d ≤ S.cost size j S.length ∨ pace taken count = true then
      if used + count * nodeB ≤ maxB then
        takeLoopB size d pace nodeB maxB S D js (taken + count) (used + count * nodeB) j
      else acc
    else acc

/-- BergDB's take with the byte limit as a startup pos policy: `takePolicy`
with `takeLoopB` in place of `takeLoop`. -/
def takePolicyB (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T) (nodeB maxB : Nat) :
    Stream V T → Dirty → Time → T → Nat :=
  fun S D i tr =>
    takeLoopB size (max (2 * sd i) (S.span size)) (pace S D i tr) nodeB maxB S D
      (sectionIdx S (lastSp S)) 0 0 (lastSp S)

end SIS
