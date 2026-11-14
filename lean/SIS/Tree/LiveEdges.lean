/-
`LiveCounts` edge by edge (bergdb 024-12, TP7, `LiveCounts.lean`): `LiveEdges`
(`LiveEdgesBase.lean`) and `LiveCounts` are equivalent
(`liveCounts_of_edges`, `edges_of_liveCounts`), so a step of the writer checks
only the links it changes.
-/
import SIS.Tree.LiveCases
import SIS.Tree.LiveEdgesBase

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem fReach_tReach {N : NodeId → Option KNode} {t : Time} {r x : NodeId} {b s : Bool}
    (h : FReach N t r x b s) : TReach N t r x := by
  induction h with
  | root => exact TReach.root
  | inner x _ _ n c y _ hn _ hc ih => exact TReach.link ih ⟨n, hn, hc⟩
  | seg x _ _ n c y _ hn _ hc ih => exact TReach.link ih ⟨n, hn, hc⟩

theorem tReach_fReach {N : NodeId → Option KNode} {t : Time} {r x : NodeId}
    (h : TReach N t r x) : ∃ b s, FReach N t r x b s := by
  induction h with
  | root => exact ⟨true, true, FReach.root⟩
  | @link u c y _ hl ih =>
    obtain ⟨b, s, hu⟩ := ih
    obtain ⟨n, hn, hc⟩ := hl
    cases hl : n.leaf with
    | true => exact ⟨true, false, FReach.seg u b s n c y hu hn hl hc⟩
    | false => exact ⟨false, s, FReach.inner u b s n c y hu hn hl hc⟩

theorem liveCounts_of_edges (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : LiveEdges p N t r) : LiveCounts p N t r := by
  intro x b s n hx hn
  cases hx with
  | root =>
    obtain ⟨h1, h2⟩ := h.1 n hn
    exact ⟨fun hE => ⟨rfl, rfl, h1 hE⟩, fun hl _ => h2 hl, fun _ hb => (by cases hb)⟩
  | inner u _ _ un c _ hu hun hul hc =>
    obtain ⟨h1, _, h3⟩ := h.2 u un c x n (fReach_tReach hu) hun hc hn
    exact ⟨fun hE => absurd hE h1, fun _ hb => (by cases hb), fun hm _ => h3 hul hm⟩
  | seg u _ _ un c _ hu hun hul hc =>
    obtain ⟨h1, h2, _⟩ := h.2 u un c x n (fReach_tReach hu) hun hc hn
    exact ⟨fun hE => absurd hE h1, fun hl _ => h2 hul hl, fun _ hb => (by cases hb)⟩

theorem edges_of_liveCounts (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hC : LiveCounts p N t r) : LiveEdges p N t r := by
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · obtain ⟨h1, h2, _⟩ := hC r true true rn FReach.root hrn
    exact ⟨fun hE => (h1 hE).2.2, fun hl => h2 hl rfl⟩
  · obtain ⟨b, s, hfu⟩ := tReach_fReach hu
    cases hl : un.leaf with
    | true =>
      obtain ⟨h1, h2, _⟩ := hC y true false yn (FReach.seg u b s un c y hfu hun hl hc) hyn
      refine ⟨fun hE => ?_, fun _ hyl => h2 hyl rfl, fun h => (by rw [hl] at h; cases h)⟩
      have := (h1 hE).2.1
      cases this
    | false =>
      obtain ⟨h1, _, h3⟩ := hC y false s yn (FReach.inner u b s un c y hfu hun hl hc) hyn
      refine ⟨fun hE => ?_, fun h => (by rw [hl] at h; cases h), fun _ hm => h3 hm rfl⟩
      have := (h1 hE).1
      cases this

end SIS.Tree
