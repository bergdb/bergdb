import SIS.Tree.WalkComplete

namespace SIS.Tree

open SIS SIS.Check

def UpperBound (hi : Option Nat) (c : Nat) : Prop :=
  match hi with
  | none => True
  | some b => c < b

def childBounds (pairs : List (Nat × NodeId)) (hi : Option Nat) :
    List ((Nat × NodeId) × Option Nat) :=
  pairs.zip ((pairs.drop 1).map (fun q => some q.1) ++ [hi])

theorem childBounds_cons_cons (q r : Nat × NodeId) (rest : List (Nat × NodeId))
    (hi : Option Nat) :
    childBounds (q::r::rest) hi = (q,some r.1)::childBounds (r::rest) hi := rfl

theorem childBounds_fst (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (q : Nat × NodeId) (b : Option Nat) (h : (q,b) ∈ childBounds pairs hi) : q ∈ pairs :=
  (List.of_mem_zip h).1

theorem childBounds_high (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (q : Nat × NodeId) (b : Option Nat) (h : (q,b) ∈ childBounds pairs hi) :
    b = hi ∨ ∃ r ∈ pairs, b = some r.1 := by
  have hb := (List.of_mem_zip h).2
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hb
    exact Or.inr ⟨r,List.mem_of_mem_drop hr,he.symm⟩
  · exact Or.inl (List.mem_singleton.mp hb)

theorem childBounds_exists (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (q : Nat × NodeId) (hq : q ∈ pairs) : ∃ b, (q,b) ∈ childBounds pairs hi := by
  apply mem_zip_left_witness _ _ _ q hq
  simp only [List.length_append,List.length_map,List.length_drop,List.length_singleton]
  omega

/-- The upper bound immediately after a separator is no greater than any
later separator in a strictly ordered node. -/
theorem childBounds_next_le (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (q : Nat × NodeId) (b : Option Nat) (hq : (q,b) ∈ childBounds pairs hi)
    (r : Nat × NodeId) (hr : r ∈ pairs) (hqr : q.1 < r.1) :
    ∃ upper, b = some upper ∧ upper ≤ r.1 := by
  induction pairs with
  | nil => simp [childBounds] at hq
  | cons a rest ih =>
    cases rest with
    | nil =>
      have heq : q = a ∧ b = hi := by simpa [childBounds] using hq
      have hr' : r = a := List.mem_singleton.mp hr
      simp [heq.1,hr'] at hqr
    | cons d ds =>
      rw [childBounds_cons_cons] at hq
      have hsa := (List.pairwise_cons.mp hs).1
      have hsd := (List.pairwise_cons.mp hs).2
      rcases List.mem_cons.mp hq with he | hq
      · have heq : q = a ∧ b = some d.1 := Prod.mk.inj he
        obtain ⟨rfl,rfl⟩ := heq
        have hr' : r ∈ d::ds := by
          rcases List.mem_cons.mp hr with rfl | hr
          · omega
          · exact hr
        refine ⟨d.1,rfl,?_⟩
        rcases List.mem_cons.mp hr' with rfl | hr'
        · omega
        · have hlt := (List.pairwise_cons.mp hsd).1 r hr'
          omega
      · have hq' : q ∈ d::ds := childBounds_fst _ _ _ _ hq
        have hr' : r ∈ d::ds := by
          rcases List.mem_cons.mp hr with rfl | hr
          · have hlt := hsa q hq'
            omega
          · exact hr
        exact ih hsd hq hr'

/-- A compare value in this child's interval makes its separator the
greatest separator at or below that value. -/
theorem childBounds_dominates (pairs : List (Nat × NodeId)) (hi : Option Nat)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (q : Nat × NodeId) (b : Option Nat) (hq : (q,b) ∈ childBounds pairs hi)
    (cv : Nat) (hhi : UpperBound b cv) :
    ∀ r ∈ pairs, r.1 ≤ cv → r.1 ≤ q.1 := by
  intro r hr hrcv
  by_cases hrq : r.1 ≤ q.1
  · exact hrq
  · obtain ⟨upper,hub,hurb⟩ := childBounds_next_le pairs hi hs q b hq r hr (by omega)
    rw [hub] at hhi
    dsimp only [UpperBound] at hhi
    omega

def NodeRange (n : KNode) (t lo : Nat) (hi : Option Nat) : Prop :=
  ∀ q ∈ n.liveAt t,
    (if n.leaf then lo ≤ q.1 else q.1 = 0 ∨ lo < q.1) ∧ UpperBound hi q.1

theorem KNode.liveAt_order (n : KNode) (t : Time) :
    (n.liveAt t).Pairwise (fun a b => a.1 < b.1) := by
  rw [n.liveAt_eq_live_prefix]
  exact KNode.live_order _

theorem walk_current_range (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    NodeRange ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ t lo hi := by
  intro q hq
  let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
  let low := if n.leaf then decide (lo ≤ q.1) else (q.1 == 0 || decide (lo < q.1))
  let high := match hi with | some b => decide (q.1 < b) | none => true
  have hpass : (low && high) = true := by
    cases hb : low && high with
    | true => rfl
    | false =>
      have hm : s!"RangeOK: key node {x} has the live compare value {q.1} outside [{lo}, {hi})" ∈
          walk p v t (f+1) x lo hi isRoot space := by
        rw [walk]
        simp only [hv,hd,Bool.false_eq_true,↓reduceIte,List.mem_append]
        left; right
        apply List.mem_filterMap.mpr
        exact ⟨q,hq,by change (if low && high then none else some _) = some _; simp [hb]⟩
      simp [hw] at hm
  have hpair : low = true ∧ high = true := by
    simpa only [Bool.and_eq_true] using hpass
  constructor
  · cases hh : n.leaf <;> simpa [low,hh] using hpair.1
  · cases hi <;> simpa [high,UpperBound] using hpair.2

/-- The logical abstraction of one segment tree. Segment links in leaves
are payloads here; only inner-node links recurse. -/
def SegmentSound (p : Params) (v : View BVal) (t : Time) :
    Nat → NodeId → Nat → Option Nat → Prop
  | 0, _, _, _ => False
  | f+1, x, lo, hi => ∃ n, knodeOf p v x = some n ∧ klongsWf n.ks = true ∧
      NodeRange n t lo hi ∧ (n.leaf = false → ∀ q ∈ childBounds (n.liveAt t) hi,
        SegmentSound p v t f q.1.2 (if q.1.1 == 0 then lo else q.1.1) q.2)

end SIS.Tree
