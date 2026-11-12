import SIS.Tree.SplitLiveFill

namespace SIS.Tree

open SIS SIS.Check

theorem newKlongs_cnt_of_sorted (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) : (⟨leaf,newKlongs t pairs⟩ : KNode).cnt = pairs.length := by
  apply KNode.newKlongs_cnt
  exact List.pairwise_map.mpr (hs.imp (by intro a b hab; omega))

/-- The merge's size and order facts give actual live counts of its output
nodes, rather than just counts of physical klongs. -/
theorem mergeKlongs_live_fill (p : Params) (hp : MergeParamsOK p)
    (inner : Bool) (t : Time) (cR : Nat) (left right : List (Nat × NodeId))
    (hL : CvSorted left) (hR : CvSorted right)
    (hLc : ∀ q ∈ left, q.1 < cR) (hRt : ∀ q ∈ right.tail, cR < q.1)
    (hRl : inner = false → ∀ q ∈ right, cR ≤ q.1)
    (hlo : p.mergeBelow ≤ left.length+right.length)
    (hhi : left.length+right.length ≤ p.mergeBelow-1+(p.M-1)) :
    let r := mergeKlongs inner p.mergeMax cR left right
    p.mergeBelow ≤ (⟨!inner,newKlongs t r.1⟩ : KNode).cnt ∧
      (⟨!inner,newKlongs t r.1⟩ : KNode).size ≤ p.M ∧
      ∀ rest g, r.2 = some (rest,g) →
        p.mergeBelow ≤ (⟨!inner,newKlongs t rest⟩ : KNode).cnt ∧
          (⟨!inner,newKlongs t rest⟩ : KNode).size ≤ p.M := by
  have hcap : 1 ≤ p.mergeMax := by have := hp.1; have := hp.2.1; omega
  obtain ⟨hfirst,hsecond⟩ := mergeOrderOK inner p.mergeMax cR left right hcap hL hR hLc hRt hRl
  obtain ⟨hfill,hsize,htwo⟩ := mergeFillOK p inner cR left right hp hlo hhi
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rwa [newKlongs_cnt_of_sorted _ _ _ hfirst]
  · simpa only [KNode.size,newKlongs,List.length_cons,List.length_map] using hsize
  · intro rest g hg
    obtain ⟨_,hs⟩ := hsecond rest g hg
    obtain ⟨hf,hsize⟩ := htwo rest g hg
    constructor
    · rwa [newKlongs_cnt_of_sorted _ _ _ hs]
    · simpa only [KNode.size,newKlongs,List.length_cons,List.length_map] using hsize

end SIS.Tree
