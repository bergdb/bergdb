import SIS.Tree.KlongRoundTripBits
import SIS.Tree.MergeLiveKeys

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.mem_bitsOf_iff (n : KNode) (c i : Nat) :
    i ∈ n.bitsOf c ↔ ∃ y, (.key c y,i) ∈ n.ks.zipIdx := by
  constructor
  · intro hi
    obtain ⟨⟨k,j⟩,hj,hf⟩ := List.mem_filterMap.mp hi
    cases k with
    | time t => simp at hf
    | del bits => simp at hf
    | key a y =>
      simp only at hf
      split at hf
      · rename_i hac
        have hac' : a = c := by simpa using hac
        have hji : j = i := Option.some.inj hf
        subst a
        subst j
        exact ⟨y,hj⟩
      · cases hf
  · rintro ⟨y,hy⟩
    exact List.mem_filterMap.mpr ⟨(.key c y,i),hy,by simp⟩

end SIS.Tree
