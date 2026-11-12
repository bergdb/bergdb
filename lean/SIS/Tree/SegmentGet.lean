import SIS.Tree.SegmentRange
import SIS.Tree.SearchEqProof

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.liveAt_keys_nodup (n : KNode) (t : Time) :
    ((n.liveAt t).map Prod.fst).Nodup := by
  rw [n.liveAt_eq_live_prefix]
  exact KNode.live_keys_nodup _

/-- An inner search selects exactly the child whose interval contains the
query, including the selected pointer and its separator. -/
theorem KNode.searchLte_child (n : KNode) (t : Time) (hi : Option Nat)
    (q : Nat × NodeId) (b : Option Nat) (hq : (q,b) ∈ childBounds (n.liveAt t) hi)
    (cv : Nat) (hlo : q.1 ≤ cv) (hhi : UpperBound b cv) :
    ∃ fd, n.searchLte t cv = some fd ∧ fd.c = q.1 ∧ fd.y = q.2 := by
  have hmem := childBounds_fst _ _ _ _ hq
  have hspec := n.searchLte_spec t cv
  cases hf : n.searchLte t cv with
  | none =>
    have hno := (hspec.2.mp hf) q hmem
    simp only [decide_eq_false_iff_not] at hno
    omega
  | some fd =>
    obtain ⟨hfd,hle,hmax⟩ := hspec.1 fd hf
    have hqle := hmax q hmem (by simp; omega)
    have hfdle : fd.c ≤ q.1 := childBounds_dominates (n.liveAt t) hi
      (n.liveAt_order t) q b hq cv hhi (fd.c,fd.y) hfd (by
        simp only [decide_eq_true_eq] at hle
        omega)
    have heq : fd.c = q.1 := by
      simp only [decide_eq_true_eq] at hqle
      omega
    have hlookup := lookup_some_of_mem (n.liveAt_keys_nodup t) hmem
    have hlookup' := lookup_some_of_mem (n.liveAt_keys_nodup t) hfd
    rw [heq,hlookup] at hlookup'
    exact ⟨fd,rfl,heq,(Option.some.inj hlookup').symm⟩

/-- The leaf pairs of one segment tree, enumerated by all inner children
rather than by a reader's selected path. -/
def segmentEntries (p : Params) (v : View BVal) (t : Time) :
    Nat → NodeId → List (Nat × NodeId)
  | 0, _ => []
  | f+1, x => match knodeOf p v x with
    | none => []
    | some n => if n.leaf then n.liveAt t else
        (n.liveAt t).flatMap (fun q => segmentEntries p v t f q.2)

theorem segmentEntries_range (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : SegmentSound p v t f x lo hi) :
    ∀ q ∈ segmentEntries p v t f x, lo ≤ q.1 ∧ UpperBound hi q.1 := by
  induction f generalizing x lo hi with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n,hn,hwf,hr,hchildren⟩ := hs
    simp only [segmentEntries,hn]
    cases hleaf : n.leaf with
    | true =>
      simp only [hleaf,↓reduceIte]
      intro q hq
      simpa only [hleaf,↓reduceIte] using hr q hq
    | false =>
      simp only [hleaf,Bool.false_eq_true,↓reduceIte]
      intro q hq
      obtain ⟨r,hrmem,hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi r hrmem
      obtain ⟨hlow,hhigh⟩ := ih r.2 _ b (hchildren hleaf (r,b) hb) q hq
      dsimp only at hlow hhigh
      have hrrange := hr r hrmem
      simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hrrange
      constructor
      · split at hlow
        · exact hlow
        · rcases hrrange.1 with hz | hlt
          · simp [hz] at *
          · omega
      · rcases childBounds_high (n.liveAt t) hi r b hb with he | ⟨s,hsm,he⟩
        · rwa [he] at hhigh
        · rw [he] at hhigh
          have hsbound := (hr s hsm).2
          cases hi with
          | none => trivial
          | some upper =>
            dsimp only [UpperBound] at hhigh hsbound ⊢
            omega

/-- A search through one sound segment tree returns a pointer exactly when
the corresponding compare-value/pointer pair is among its leaves. -/
theorem getEq_segmentEntries (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : SegmentSound p v t f x lo hi) (cv : Nat) (y : NodeId) :
    getEq p v t cv f x = some y ↔ (cv,y) ∈ segmentEntries p v t f x := by
  induction f generalizing x lo hi with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n,hn,hwf,hr,hchildren⟩ := hs
    simp only [getEq,segmentEntries,hn]
    cases hleaf : n.leaf with
    | true =>
      simp only [hleaf,↓reduceIte]
      rw [searchEqSpec n t cv hwf]
      exact ⟨lookup_some_mem,lookup_some_of_mem (n.liveAt_keys_nodup t)⟩
    | false =>
      simp only [hleaf,Bool.false_eq_true,↓reduceIte]
      constructor
      · intro he
        cases hf : n.searchLte t cv with
        | none => simp [hf] at he
        | some fd =>
          have hfd := (n.searchLte_spec t cv).1 fd hf |>.1
          obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c,fd.y) hfd
          have hchild := hchildren hleaf ((fd.c,fd.y),b) hb
          have hget : getEq p v t cv f fd.y = some y := by simpa only [hf] using he
          exact List.mem_flatMap.mpr ⟨(fd.c,fd.y),hfd,(ih _ _ _ hchild).mp hget⟩
      · intro hm
        obtain ⟨q,hq,hmem⟩ := List.mem_flatMap.mp hm
        obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi q hq
        have hchild := hchildren hleaf (q,b) hb
        obtain ⟨hlow,hhigh⟩ := segmentEntries_range p v t f q.2 _ b hchild (cv,y) hmem
        have hsep : q.1 ≤ cv := by
          split at hlow
          · rename_i hz
            have hzero : q.1 = 0 := by simpa using hz
            omega
          · exact hlow
        obtain ⟨fd,hfd,_,hptr⟩ := n.searchLte_child t hi q b hb cv hsep hhigh
        simp only [hfd]
        rw [hptr]
        exact (ih _ _ _ hchild).mpr hmem

/-- The segment-tree lookup equals lookup in all its leaf pairs. -/
theorem getEq_lookup_segmentEntries (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : SegmentSound p v t f x lo hi) (cv : Nat) :
    getEq p v t cv f x = (segmentEntries p v t f x).lookup cv := by
  cases he : (segmentEntries p v t f x).lookup cv with
  | some y => exact (getEq_segmentEntries p v t f x lo hi hs cv y).mpr (lookup_some_mem he)
  | none =>
    cases hg : getEq p v t cv f x with
    | none => rfl
    | some y =>
      have hm := (getEq_segmentEntries p v t f x lo hi hs cv y).mp hg
      have hn := List.lookup_eq_none_iff.mp he (cv,y) hm
      simp at hn

/-- On a fault-free actual tree, getEq is the lookup of its segment leaves. -/
theorem getEq_lookup_of_walk (p : Params) (P : Struct BVal) (t f x lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) (hP : HighKindsOK p P)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) (cv : Nat) :
    getEq p (viewOf P) t cv f x = (segmentEntries p (viewOf P) t f x).lookup cv :=
  getEq_lookup_segmentEntries p _ t f x lo hi
    (segmentSound_of_walk p P t f hP x lo hi isRoot space hw) cv

end SIS.Tree
