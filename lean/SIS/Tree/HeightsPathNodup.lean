/-
The key access path's nodes are pairwise distinct (bergdb 024-22; toward
`OpDelChkOK`'s `checkPathFree`): along the path a node's segment and height
strictly fall in the order of segments up, heights down. Below an inner node
its child is one height lower in the same segment (the heights' `PathHt`, the
kinds' `PathKinds`); below a segment leaf the child is a key node of the next
segment (`PathKinds`; a value is no node of the path). A node has one segment
and height (`gh`), so no node is twice on the path (`ht_path_nodup`).
-/
import SIS.Tree.WriterHeightsRules
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section PathNodup

variable {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {K : KindOracle} {w : W}

/-- A node of `gh` is no value. -/
theorem kd_not_val_of_gh (hb : Book B c w) (hk : ViewKinds K B c) (hi : KdInv K B w)
    {y : NodeId} {g h : Nat} (hm : (y, g, h) ∈ w.gh) (hv : IsValId K w y) : False := by
  rcases hv with ⟨hh, hvm⟩ | hv
  · exact (hi.vals (y, hh) hvm).2.2 (ht_mem_ids hm)
  · rcases hb.tag y g h hm with ⟨nd, hnd, hd, hlv, _, _⟩ | ⟨hB, _, _⟩
    · exact hk.notBoth y _ (hk.node y nd hnd hd hlv) hv
    · have := hk.oldVal y hv; omega

/-- One step down the path: the child's segment and height. -/
theorem ht_path_step (hb : Book B c w) (hvo : ViewHtOK H B c) (hi : HtInv H B c w)
    (hk : ViewKinds K B c) (hki : KdInv K B w) (hpf : PathFreeTo w w.path.length)
    {d : Nat} {a : Option Nat} {q y : NodeId} {cv : Nat}
    (hq : w.path[d]? = some (a, q)) (hy : w.path[d + 1]? = some (some cv, y))
    {g h g' h' : Nat} (hmq : (q, g, h) ∈ w.gh) (hmy : (y, g', h') ∈ w.gh) :
    (h ≠ 0 → g' = g ∧ h' = h - 1) ∧ (h = 0 → g' = g + 1) := by
  have hqf : w.taken.contains q = false := by
    have := (List.getElem?_eq_some_iff.mp hy).1
    exact hpf d a q (by omega) hq
  have hkk := hki.path d a q cv y hq hy g h hmq
  refine ⟨fun h0 => ⟨?_, ?_⟩, fun h0 => ?_⟩
  · exact (kd_seg_unique hb hk hmy (hkk.1 h0))
  · exact hasHt_tag hb hvo.heights hmy (hi.path d a q cv y hq hy g h hmq hqf h0)
  · by_cases h7 : segLen cv = 7
    · exact kd_seg_unique hb hk hmy ((hkk.2 h0).1 h7)
    · exact absurd ((hkk.2 h0).2 h7) (fun hv => kd_not_val_of_gh hb hk hki hmy hv)

/-- Along the path, segments rise and, within a segment, heights fall. -/
theorem ht_path_order (hb : Book B c w) (hvo : ViewHtOK H B c) (hi : HtInv H B c w)
    (hk : ViewKinds K B c) (hki : KdInv K B w) (hpf : PathFreeTo w w.path.length)
    (hall : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1))
    (j : Nat) (a : Option Nat) (q : NodeId) (g h : Nat) (hq : w.path[j]? = some (a, q))
    (hmq : (q, g, h) ∈ w.gh) :
    ∀ n (b : Option Nat) (q' : NodeId) (g' h' : Nat), w.path[j + 1 + n]? = some (b, q') →
      (q', g', h') ∈ w.gh → g < g' ∨ (g = g' ∧ h' < h) := by
  intro n
  induction n with
  | zero =>
    intro b q' g' h' hq' hm'
    obtain ⟨cv, rfl⟩ : ∃ cv, b = some cv := by
      cases b with
      | none => exact absurd rfl (hi.pathSome j none q' hq')
      | some cv => exact ⟨cv, rfl⟩
    have := ht_path_step hb hvo hi hk hki hpf hq hq' hmq hm'
    by_cases h0 : h = 0
    · left; have := this.2 h0; omega
    · right; obtain ⟨e1, e2⟩ := this.1 h0; exact ⟨e1.symm, by omega⟩
  | succ n ih =>
    intro b q' g' h' hq' hm'
    have hlt : j + 1 + n < w.path.length := by
      have := (List.getElem?_eq_some_iff.mp hq').1; omega
    obtain ⟨⟨b0, q0⟩, hq0⟩ : ∃ e, w.path[j + 1 + n]? = some e :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨⟨q0', g0, h0⟩, hm0, he0⟩ := List.mem_map.mp (hall _ b0 q0 hq0)
    simp only at he0
    subst he0
    have h1 := ih b0 q0' g0 h0 hq0 hm0
    obtain ⟨cv, rfl⟩ : ∃ cv, b = some cv := by
      cases b with
      | none =>
        exact absurd rfl (hi.pathSome (j + 1 + n) none q' (by rw [← hq']; congr 1))
      | some cv => exact ⟨cv, rfl⟩
    have hq'' : w.path[j + 1 + n + 1]? = some (some cv, q') := by
      rw [← hq']; congr 1
    have h2 := ht_path_step hb hvo hi hk hki hpf hq0 hq'' hm0 hm'
    by_cases hz : h0 = 0
    · have := h2.2 hz; omega
    · obtain ⟨e1, e2⟩ := h2.1 hz; omega

/-- The path's nodes are pairwise distinct when they are all cached. -/
theorem ht_path_nodup (hb : Book B c w) (hvo : ViewHtOK H B c) (hi : HtInv H B c w)
    (hk : ViewKinds K B c) (hki : KdInv K B w) (hpf : PathFreeTo w w.path.length)
    (hall : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1))
    {j k : Nat} (hjk : j < k) {a b : Option Nat} {q : NodeId}
    (hq : w.path[j]? = some (a, q)) (hq' : w.path[k]? = some (b, q)) : False := by
  obtain ⟨⟨q0, g, h⟩, hm, he⟩ := List.mem_map.mp (hall j a q hq)
  simp only at he
  subst he
  obtain ⟨n, rfl⟩ : ∃ n, k = j + 1 + n := ⟨k - j - 1, by omega⟩
  have := ht_path_order hb hvo hi hk hki hpf hall j a q0 g h hq hm n b q0 g h hq' hm
  omega

/-- Two depths of the path hold two nodes (`checkPathFree`'s use: the upward
delete's loop takes back nodes below the stop node only, so the nodes at the
stop node and above stay not taken back). -/
theorem ht_path_ne (hb : Book B c w) (hvo : ViewHtOK H B c) (hi : HtInv H B c w)
    (hk : ViewKinds K B c) (hki : KdInv K B w) (hpf : PathFreeTo w w.path.length)
    (hall : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1))
    {j k : Nat} (hjk : j ≠ k) {a b : Option Nat} {q q' : NodeId}
    (hq : w.path[j]? = some (a, q)) (hq' : w.path[k]? = some (b, q')) : q ≠ q' := by
  rintro rfl
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · exact ht_path_nodup hb hvo hi hk hki hpf hall h hq hq'
  · exact ht_path_nodup hb hvo hi hk hki hpf hall h hq' hq

end PathNodup

end SIS.Tree
