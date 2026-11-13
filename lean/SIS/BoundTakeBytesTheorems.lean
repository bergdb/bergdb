/-
Self-indexed streams in Lean: bounds, part 1, BergDB's take with its byte limit
(bergdb item 007; 007-09's second review). Trusted part: the statements. The
definitions they are about are in SIS/BoundTakeBytes.lean (`takePolicyB`) and
SIS/Bound.lean; the proofs in SIS/Proof/BoundTakeBytes.lean. Added 2026-11-13.

In plain words. Java's take ends at the first transaction whose nodes do not
fit in `maxBytes`, also after the deadline (`TransSeq.take`). Three facts:

1. Progress (`takeB_progress`): while the section's span is at least twice the
   setting, its oldest transaction is past the deadline, and the take takes it
   if that transaction's own nodes fit in the limit. So the limit cannot stop
   the take when each transaction's nodes fit (005-31).
2. No progress without that: a transaction whose nodes do not fit is never
   taken, and the startup pos stays where it is for ever
   (SIS/BoundTakeBytesExample.lean, case 1).
3. T3's bound needs more than progress: with every transaction fitting, the
   span can still exceed 2 M for a while (the example's case 2). It holds
   (`T3_takeB`) where the whole debt before each transaction fits in the limit:
   then the limit never stops the take.
-/
import SIS.Proof.BoundTakeBytes

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Progress of BergDB's take with its byte limit: in transaction i, with S
the stream before R(i), D the debt and s = s(i-1): if T(s + 1), the oldest
transaction of the section, exists, the span is at least twice the setting,
and T(s + 1)'s got-dirty nodes fit in the limit, the take asks for s + 1 or a
later startup pos. -/
theorem takeB_progress (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T)
    (nodeB maxB : Nat) (S : Stream V T) (D : Dirty) (i : Time) (tr : T)
    (hne : lastSp S + 1 < S.length) (hspan : 2 * sd i ≤ S.span size)
    (hfit : (D.filter (fun e => e.2 == lastSp S + 1)).length * nodeB ≤ maxB) :
    lastSp S + 1 ≤ takePolicyB size sd pace nodeB maxB S D i tr :=
  takePolicyB_progress_span size sd pace nodeB maxB S D i tr hne hspan hfit

/-- T3 for BergDB's take with its byte limit: with settings at most M > 0 in
T(1), ..., T(k), and the debt before each transaction fitting in the limit
(`nodeB` bytes a node), the startup section without its last record costs less
than 2 M after T(k), as `T3_take` says without the limit. -/
theorem T3_takeB (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
    (pace : Pace V T) (nodeB maxB : Nat) (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M : Nat) (hM0 : 0 < M) (ts : List T) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hfit : ∀ j < ts.length, nodeB * (run sp al (ts.take j)).D.length ≤ maxB) :
    (run sp al ts).S.span size < 2 * M :=
  takeB_bound sp al size sd pace nodeB maxB hp M hM0 ts hM hfit

end SIS
