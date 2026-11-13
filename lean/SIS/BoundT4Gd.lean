/-
Self-indexed streams in Lean: bounds, part 2, T4's records with all of gd(i)
counted (bergdb item 007; 007-01, section 5.1; 007-09's second review). Trusted
part: the definition. The theorems are in SIS/BoundT4GdTheorems.lean, the
proofs in SIS/Proof/BoundT4Gd.lean. Added 2026-11-13.

Why. `RecordBound` (SIS/BoundT4.lean) bounds only the ids of gd(i) that are in
D: "`RecordBound` limits only `R.gd.filter (inD db.D)`. Arbitrarily many
unrelated, repeated IDs outside D satisfy it. Thus 007-01 §5.1's 'cost at most
a transaction plus the debt' needs more: constrain and count fresh got-dirty
IDs" (the second review, items/007-bounds/09-t4-in-lean/second-review.md).

The prose (007-01, 5.1): "A record holds T(i), its value nodes, gd(i) and the
versions of the nodes taken, which come from D. So R(s) and R(k) cost at most
a transaction plus the debt." gd(i) is "the ids of the index nodes that got
dirty in T(i)" (`Record.gd`): those that step 3 finds (not in D before T(i))
and those that step 7 puts back (taken from D). `RecordGdBound` says that the
first are distinct and on the access path of T(i)'s change, which counts them
by T(i) (with TREE, `T4_record_gd_height`), and that the rest are at most |D|.
-/
import SIS.BoundT4

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The got-dirty ids of R, the record of T(j + 1) in the run ts, with D the
debt before T(j + 1):

1. the ids of R's gd that are not in D are distinct;
2. every id of R's gd is in D, or on the access path of T(j + 1)'s change
   (`onAccessPath`: the changed nodes and their ancestors at j + 1, or the
   nodes it touches);
3. R's gd has at most (its ids not in D) + |D| ids. -/
def RecordGdBound (sp : Spec V T) (al : Algo V T) (ts : List T) (j : Nat) (R : Record V T) :
    Prop :=
  let D := (run sp al (ts.take j)).D
  (R.gd.filter (fun x => !inD D x)).Nodup ∧
    (∀ x ∈ R.gd, inD D x = true ∨ onAccessPath sp al ts (j + 1) x) ∧
    R.gd.length ≤ (R.gd.filter (fun x => !inD D x)).length + D.length

end SIS
