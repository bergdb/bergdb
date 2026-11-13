import SIS.Tree.HistoricalPrefix
import SIS.Tree.KlongWellFormed
import SIS.Tree.ListCongr

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Extending a well-formed physical prefix does not change any of its
checks: every bitmap reference in that prefix points back into the prefix. -/
theorem klongsWfStep_append_source (ks more : List Klong) (hw : klongsWf ks = true)
    (acc : Bool × Option Time × List Nat) (q : Klong × Nat) (hq : q ∈ ks.zipIdx) :
    klongsWfStep (ks ++ more) acc q = klongsWfStep ks acc q := by
  rcases q with ⟨k, i⟩
  have hk := List.mem_zipIdx_iff_getElem?.mp hq
  have hi : i < ks.length := (List.getElem?_eq_some_iff.mp hk).1
  cases k with
  | time t => rfl
  | key c y => rfl
  | del bits =>
    have hb := (klongsWf_bitmapRules ks hw i bits hk).1
    have hnew : (bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt (ks ++ more)) =
        (bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt ks) := by
      apply filterMap_congr_mem
      intro b hmem
      have hbit := (List.mem_filter.mp hmem).1
      exact cvAt_append_left ks more b (by have hh := (hb b hbit).1; omega)
    have hall : bits.all (fun b => decide (b < i) && (cvAt (ks ++ more) b).isSome) =
        bits.all (fun b => decide (b < i) && (cvAt ks b).isSome) := by
      apply all_congr_mem
      intro b hbit
      rw [cvAt_append_left ks more b (by have hh := (hb b hbit).1; omega)]
    have hclosed : (List.range i).all (fun j => match cvAt (ks ++ more) j with
        | some c => !((bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt ks)).contains c || bits.contains j
        | none => true) =
        (List.range i).all (fun j => match cvAt ks j with
        | some c => !((bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt ks)).contains c || bits.contains j
        | none => true) := by
      apply all_congr_mem
      intro j hj
      rw [cvAt_append_left ks more j (by have hh := List.mem_range.mp hj; omega)]
    simp only [klongsWfStep, hnew, hall]
    congr 2

theorem klongsWf_fold_append_source (ks more : List Klong) (hw : klongsWf ks = true)
    (init : Bool × Option Time × List Nat) :
    ks.zipIdx.foldl (klongsWfStep (ks ++ more)) init =
      ks.zipIdx.foldl (klongsWfStep ks) init :=
  foldl_congr_mem ks.zipIdx _ _ init
    (fun acc q hq => klongsWfStep_append_source ks more hw acc q hq)

theorem klongsWf_fold_lastTime (ks : List Klong) :
    (ks.zipIdx.foldl (klongsWfStep ks) (true, none, [])).2.1 = lastTimeOf ks := by
  have hh := List.foldl_hom (fun acc : Bool × Option Time × List Nat => acc.2.1)
    (g₁ := klongsWfStep ks) (g₂ := fun cur q => lastTimeStep cur q.1)
    (l := ks.zipIdx) (init := (true, none, [])) (by
      intro acc q
      rcases q with ⟨k, i⟩
      cases k <;> rfl)
  rw [← hh]
  have hf : ∀ (pre : List Klong) (start : Nat) (cur : Option Time),
      (pre.zipIdx start).foldl (fun cur q => lastTimeStep cur q.1) cur =
        pre.foldl lastTimeStep cur := by
    intro pre
    induction pre with
    | nil => intro start cur; rfl
    | cons k pre ih =>
      intro start cur
      simp only [List.zipIdx_cons, List.foldl_cons]
      exact ih (start + 1) _
  exact hf ks 0 none

theorem klongsWf_append_time (ks : List Klong) (t : Time) (hw : klongsWf ks = true)
    (ht : ∀ u, lastTimeOf ks = some u → u < t) : klongsWf (ks ++ [.time t]) = true := by
  rw [klongsWf_eq_fold, List.zipIdx_append, List.foldl_append,
    klongsWf_fold_append_source ks [.time t] hw]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
    klongsWfStep]
  rw [← klongsWf_eq_fold, hw, klongsWf_fold_lastTime]
  cases he : lastTimeOf ks with
  | none => rfl
  | some u => simp [ht u he]

theorem klongsWf_append_key (ks : List Klong) (cv : Nat) (y : NodeId)
    (hw : klongsWf ks = true) (ht : (lastTimeOf ks).isSome = true) :
    klongsWf (ks ++ [.key cv y]) = true := by
  rw [klongsWf_eq_fold, List.zipIdx_append, List.foldl_append,
    klongsWf_fold_append_source ks [.key cv y] hw]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
    klongsWfStep]
  rw [← klongsWf_eq_fold, hw, klongsWf_fold_lastTime, ht]
  rfl

/-- A physical key write preserves well-formed klongs. The append routine
introduces a time marker only when its time grows. -/
theorem KNode.add_key_wf (n : KNode) (t cv : Nat) (y : NodeId)
    (hw : klongsWf n.ks = true) :
    klongsWf (n.add t (.key cv y)).ks = true := by
  unfold KNode.add
  cases he : n.lastTime with
  | none =>
    change klongsWf (n.ks ++ [.time t, .key cv y]) = true
    rw [← List.singleton_append, ← List.append_assoc]
    apply klongsWf_append_key
    · exact klongsWf_append_time n.ks t hw (by
        intro u hu
        change n.lastTime = some u at hu
        rw [he] at hu
        cases hu)
    · rw [lastTimeOf_append_time]; rfl
  | some u =>
    by_cases hu : u < t
    · simp only [hu, ↓reduceIte]
      rw [← List.singleton_append, ← List.append_assoc]
      apply klongsWf_append_key
      · exact klongsWf_append_time n.ks t hw (by
          intro a ha
          have heq : a = u := Option.some.inj (ha.symm.trans he)
          omega)
      · rw [lastTimeOf_append_time]; rfl
    · simp only [hu, ↓reduceIte]
      apply klongsWf_append_key n.ks cv y hw
      change n.lastTime.isSome = true
      rw [he]
      rfl

end SIS.Tree
