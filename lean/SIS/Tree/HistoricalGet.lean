import SIS.Tree.HistoricalRead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem within_snoc_prefix (p : Params) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) : Within p ts := by
  have hh := within_take p (ts ++ [tx]) hw ts.length
  simpa only [List.take_append_of_le_length (Nat.le_refl _), List.take_length] using hh

/-- Conditional on TP7, any successful later transaction preserves all
earlier gets. High-node kinds and data-entry availability are already proved
for every actual run and add no hypotheses here. -/
theorem treeRun_get_snoc_past (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (t : Time) (ht : t ≤ ts.length)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (treeRun p (ts ++ [tx]))) t key = get p (viewOf (treeRun p ts)) t key := by
  have hwpre := within_snoc_prefix p ts tx hw
  have hi := (hinv ts hwpre t ht).1
  have hi' := (hinv (ts ++ [tx]) hw t (by simp only [List.length_append, List.length_singleton]; omega)).1
  have hh := treeRun_highKindsOK p (ts ++ [tx])
  rw [treeRun_snoc] at hi' hh ⊢
  exact get_apply_past_of_invariants p (treeRun p ts) (ts.length + 1) t _ (by omega)
    (treeRun_highKindsOK p ts) hh (treeRun_dataEntriesOK p ts) hi hi' key hkey

theorem treeRun_get_eq_prefix (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (hw : Within p ts) (t : Time) (ht : t ≤ ts.length)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (treeRun p ts)) t key = get p (viewOf (treeRun p (ts.take t))) t key := by
  have hf : ∀ revts : List Tx, Within p revts.reverse → ∀ u ≤ revts.reverse.length,
      get p (viewOf (treeRun p revts.reverse)) u key =
        get p (viewOf (treeRun p (revts.reverse.take u))) u key := by
    intro revts
    induction revts with
    | nil => intro h u hu; simp only [List.reverse_nil, List.take_nil]
    | cons tx revts ih =>
      intro h u hu
      simp only [List.reverse_cons] at h hu ⊢
      by_cases hle : u ≤ revts.reverse.length
      · rw [treeRun_get_snoc_past p hinv revts.reverse tx h u hle key hkey,
          List.take_append_of_le_length hle]
        exact ih (within_snoc_prefix p revts.reverse tx h) u hle
      · have he : u = (revts.reverse ++ [tx]).length := by
          simp only [List.length_append, List.length_singleton] at hu ⊢
          omega
        rw [he, List.take_length]
  simpa only [List.reverse_reverse] using hf ts.reverse (by simpa using hw) t (by simpa using ht)

/-- The remaining map refinement only needs the latest state of each run;
the historical part follows from TP7 and append-only history semantics. -/
def LatestGetOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ key, keyWf key = true →
    get p (viewOf (treeRun p ts)) ts.length key = refGet ts ts.length key

theorem getOK_of_latest (p : Params) (hinv : InvPreserved p) (hlatest : LatestGetOK p) : GetOK p := by
  intro ts hw t ht key hkey
  rw [treeRun_get_eq_prefix p hinv ts hw t ht key hkey]
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have he := hlatest (ts.take t) (within_take p ts hw t) key hkey
  rw [hlen, refGet_take_eq ts t t (Nat.le_refl _) key] at he
  exact he

end SIS.Tree
