/-
The steps of a cascade of splits for `LiveEdges` (bergdb 024-12, TP7, toward
`QLive` of the put into a full leaf): each takes the hypotheses of the matching
step of the writer's tree (`treeOK_timeSplit_gen`, `treeOK_spaceSplit_gen`,
`treeOK_spaceInPlaceStep` and the others), uses its reach, and adds what the
counts need: the kinds kept, no live klong lost, and a space split's halves
with the counts of `HalfOK` (`halves_lastVersionGivenDel_live_fill`).

Their common step: every link of the tree after keeps
`ChildOK` directly, or stands for a link of the tree before whose ends have
the same kinds, the node named having no fewer live klongs after.
-/
import SIS.Tree.LiveEdgesBase
import SIS.Tree.WriterTreeChainTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem rootOK_grow (t : Time) (rn rn' : KNode) (h : RootOK t rn) (hl : rn'.leaf = rn.leaf)
    (hlen : (rn.liveAt t).length ≤ (rn'.liveAt t).length) : RootOK t rn' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hE => ?_, fun hl' => ?_⟩
  · have h0 : (rn'.liveAt t).length = 0 := by rw [hE]; rfl
    rw [hl]; exact h1 (List.eq_nil_of_length_eq_zero (by omega))
  · rw [hl] at hl'; have := h2 hl'; omega

/-! ## A time split in place -/

theorem updN_updN_same (N : NodeId → Option KNode) (x : NodeId) (m m' : KNode) :
    updN (updN N x m) x m' = updN N x m' := by
  funext z
  by_cases hz : z = x
  · subst hz; rw [updN_self, updN_self]
  · rw [updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz]

/-! ## The space splits in place and below a segment leaf -/

/-- A node named by a segment leaf and holding two live klongs or more may be an
inner segment root. -/
theorem childOK_segRoot (p : Params) (t : Time) (un rn : KNode) (hul : un.leaf = true)
    (hrn2 : 2 ≤ (rn.liveAt t).length) : ChildOK p t un rn := by
  refine ⟨fun hE => ?_, fun _ _ => hrn2, fun hl _ => ?_⟩
  · rw [hE] at hrn2; simp at hrn2
  · rw [hul] at hl; cases hl

theorem rootOK_two (t : Time) (rn : KNode) (hrn2 : 2 ≤ (rn.liveAt t).length) : RootOK t rn := by
  refine ⟨fun hE => ?_, fun _ => hrn2⟩
  rw [hE] at hrn2; simp at hrn2

end SIS.Tree
