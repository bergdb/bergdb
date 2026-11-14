/-
The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsDelete.lean:
a merge, the merges after a delete, and the delete (`deleteUpward`).
-/
import SIS.Tree.WriterKindsDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The sibling: named by a klong of p, of the merged node's kind. -/
theorem kd_sibling (K : KindOracle) (B : NodeId) (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) :
    WriterWP (sibling p pn i inner) c w (fun r v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ pn.ptr? i = some r.1 ∧ v.nodes.lookup r.1 = some r.2 ∧
      r.2.leaf = !inner) := by
  unfold sibling
  kdSimp
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    kdSimp
    refine writerWP_mono (kd_getNode K B s c w hv hk hb hi) ?_
    rintro sn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hne
      rw [writerWP_pure]
      refine ⟨hb1, hi1, hle1, hp1, hs, hl1, ?_⟩
      cases hsl : sn.leaf <;> cases inner <;> simp_all

/-- A node named by a klong of an inner node p is of p's segment; its entry
in `gh` and leaf flag. -/
theorem kd_sib_facts {K : KindOracle} {B : NodeId} {c : Ctx} {vr v : W} {p s : NodeId}
    {pn sn : KNode} {gp hp i : Nat} (hb : Book B c v) (hk : ViewKinds K B c) (hir : KdInv K B vr)
    (hpn : vr.nodes.lookup p = some pn) (hpt : (p, gp, hp) ∈ vr.gh) (hh : hp ≠ 0)
    (hle : KdLe vr v) (hptr : pn.ptr? i = some s) (hls : v.nodes.lookup s = some sn) :
    ∃ hs, (s, gp, hs) ∈ v.gh ∧ sn.leaf = (hs == 0) := by
  obtain ⟨c0, hc0⟩ := kd_ptr_mem hptr
  have hseg : IsKeySeg K v s gp :=
    ((kd_cache_node hir hpn hpt c0 s (kd_mem_of_get hc0)).1 hh).kdMono hle
  obtain ⟨gs, hs, hm⟩ := kd_tag_of_lookup hb hls
  have := kd_seg_unique hb hk hm hseg
  subst this
  exact ⟨hs, hm, kd_leaf hb hls hm⟩

/-- The live klongs of a merged node, of x's segment and of a height with x's
leaf flag, are of the right kind for the new nodes. -/
theorem kd_live_kinds {K : KindOracle} {B : NodeId} {vr v : W} {o : NodeId} {on : KNode}
    {g ho h : Nat} (hl : vr.nodes.lookup o = some on) (hi : KdInv K B vr) (hm : (o, g, ho) ∈ vr.gh)
    (hon : on.leaf = (ho == 0)) (hxn : on.leaf = (h == 0)) (hk : KdLe vr v) :
    kdPairs (KindKlong K v g h) on.live := by
  have hph := kdPairs_live (kd_cache_node hi hl hm)
  have hiff : ho = 0 ↔ h = 0 := by
    rw [hon] at hxn
    constructor
    · intro h0; subst h0; simp at hxn; exact hxn.symm ▸ rfl
    · intro h0; subst h0; simp at hxn; exact hxn
  intro q hq
  have hk' := (hph q hq).kdMono hk
  refine ⟨fun h0 => hk'.1 (fun h1 => h0 (hiff.mp h1)), fun h0 => hk'.2 (hiff.mpr h0)⟩

theorem kd_sib_leaf {sn xn : KNode} {hx : Nat} (hsl : sn.leaf = !!xn.leaf)
    (hxl : xn.leaf = (hx == 0)) : sn.leaf = (hx == 0) := by
  rw [hsl, Bool.not_not, hxl]

/-- The sibling, with its entry in `gh` (p's segment) and its leaf flag (x's). -/
macro "kdSibM " hl1:term:max hpt:term:max hh:term:max hxl:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_sibling ?kdK ?kdB _ _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  rintro ⟨_, _⟩ _ ⟨hkdB, hkdI, hkdL, _, hkdP, hkdS, hkdSl⟩
  obtain ⟨_, _, _⟩ := kd_sib_facts hkdB (by assumption) (by assumption) $hl1 $hpt $hh
    (by kdChain) hkdP hkdS
  have := kd_sib_leaf hkdSl $hxl))

/-- The segment and height of x, known. -/
macro "kdGhX " hxt:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (kd_ghOf ?kdK ?kdB _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  rintro ⟨_, _⟩ _ ⟨hkdB, _, _, _, _, hkdT, _⟩
  obtain ⟨hkdG, hkdH⟩ := kd_tag_eq hkdB (KdLe.gh' $hxt (by kdChain)) hkdT
  subst hkdG
  subst hkdH))

/-- The klongs of a merge's new nodes. -/
theorem kd_free_inner' {K : KindOracle} {w : W} {g h : Nat} {leaf : Bool} (hl : leaf = (h == 0))
    (hin : (!leaf) = true) : kdFree (KindKlong K w g h) := by
  apply kd_free_of_leaf hl
  cases leaf
  · rfl
  · simp at hin

theorem kd_merge_snd' {P : Nat → NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b ks2 : List (Nat × NodeId)} {g2 : Nat}
    (hs : (mergeKlongs inner cap cR a b).2 = some (ks2, g2)) (hP : inner = true → kdFree P)
    (ha : kdPairs P a) (hb : kdPairs P b) : kdPairs P ks2 :=
  (kdPairs_mergeKlongs inner cap cR hP ha hb).2 _ hs

macro "kdLive" : tactic => `(tactic| exact kd_live_kinds (by assumption) (by assumption) (by kdTag) (by assumption) (by assumption) (by kdChain))

macro "kdKsMerge" : tactic => `(tactic| first
  | (refine kdKs_newKlongs _ (kdPairs_mergeKlongs _ _ _ ?kdF ?kdA1 ?kdA2).1
     case kdF => (intro hkdIn; refine kd_free_inner' ?kdLl hkdIn; assumption)
     case kdA1 => kdLive
     case kdA2 => kdLive)
  | (refine kdKs_newKlongs _ (kd_merge_snd' (by assumption) ?kdF ?kdA1 ?kdA2)
     case kdF => (intro hkdIn; refine kd_free_inner' ?kdLl hkdIn; assumption)
     case kdA1 => kdLive
     case kdA2 => kdLive))

macro "kdCreateM" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ (newKlongs _ _)) _ _ _)
  (refine writerWP_mono (kd_newKey ?kdK ?kdB _ _ _ _ _ _ ?kdBook ?kdInv ?kdH ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdH => kdHeight
  case kdKs => kdKsMerge
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

macro "kdMPm " hpp:term:max hpt:term:max hh:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_mergeParent ?kdK ?kdB _ _ _ _ _ _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv _ (kd_path_at $hpp ?kdPe) _ _ (KdLe.gh' $hpt ?kdKt) $hh ?kdM1 ?kdM2) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdPe => kdPathEq
  case kdKt => kdChain
  case kdM1 => exact kd_isKey (by kdTag)
  case kdM2 => (intro _ _ hkdE; (cases hkdE) <;> exact kd_isKey (by kdTag))
  rintro _ _ ⟨_, _, _, _⟩))

macro "kdRet" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (retarget _ _ _) _ _ _)
  (refine writerWP_mono (kd_retarget ?kdK ?kdB _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv _ _ (by kdTag) (kd_isKey (by kdTag))) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 20000 in
/-- A merge of x, the path's node at depth d, below an inner node. -/
theorem kd_merge (K : KindOracle) (B : NodeId) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w)
    (hd : d ≠ 0) (ax : Option Nat) (hpx : w.path[d]? = some (ax, x))
    (hpq : ∀ a q, w.path[d - 1]? = some (a, q) →
      ∃ nq, w.nodes.lookup q = some nq ∧ nq.leaf = false) :
    WriterWP (merge x d) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold merge
  kdSimp
  refine writerWP_mono (kd_pathNode (e + 1 - 1) c w) ?_
  rintro p w0 ⟨hw0, ap, hpp⟩
  rw [hw0]
  clear hw0
  simp only [Nat.add_sub_cancel] at hpp hpq
  obtain ⟨nq, hnq, hnql⟩ := hpq ap p hpp
  have hpg : p ∈ w.gh.map (·.1) := hi.pathGh e ap p hpp (List.getElem?_eq_some_iff.mp hpx).1
  obtain ⟨⟨p', gp, hp⟩, hpt, hpe⟩ := List.mem_map.mp hpg
  simp only at hpe
  subst hpe
  have hh : hp ≠ 0 := by
    intro h0; subst h0
    have := kd_leaf hb hnq hpt
    rw [hnql] at this; simp at this
  obtain ⟨k, hak⟩ : ∃ k, ax = some k := by
    cases ax with
    | none => exact absurd rfl (hi.pathSome e none x hpx)
    | some k => exact ⟨k, rfl⟩
  subst hak
  have hxs : IsKeySeg K w x gp := (hi.path e ap p' k x hpp hpx gp hp hpt).1 hh
  refine writerWP_mono (kd_getNode K B p' c w hv hk hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hpt1 := KdLe.gh' hpt hle1
  refine writerWP_mono (kd_getNode K B x c w1 hv hk hb1 hi1) ?_
  rintro xn w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
  obtain ⟨gx, hx, hxt⟩ := kd_tag_of_lookup hb2 hl2
  have := kd_seg_unique hb2 hk hxt (hxs.kdMono (hle1.trans hle2))
  subst this
  have hxl : xn.leaf = (hx == 0) := kd_leaf hb2 hl2 hxt
  have hpp2 : w.path[e]? = some (ap, p') := hpp
  clear hpq hnq hnql hpx hxs
  repeat' first
    | kdSimp
    | simp only [List.forIn_cons, List.forIn_nil]
    | kdSibM hl1 hpt1 hh hxl
    | kdGhX hxt
    | kdCreateM
    | kdMPm hpp2 hpt hh
    | kdRet
    | kdTake
    | kdUseP (kd_unlink _ _ _)
    | kdCore
    | wpSplit
    | split
    | contradiction

end SIS.Tree
