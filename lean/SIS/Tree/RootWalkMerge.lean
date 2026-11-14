/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsDelete.lean:
a merge, the merges after a delete, and the delete (`deleteUpward`).
-/
import SIS.Tree.RootWalkDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The sibling: named by a klong of p, of the merged node's kind. -/
theorem kr_sibling (K : KindOracle) (B : NodeId) (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) :
    WriterWP (sibling p pn i inner) c w (fun r v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧
      v.path = w.path ∧ pn.ptr? i = some r.1 ∧ v.nodes.lookup r.1 = some r.2 ∧
      r.2.leaf = !inner) := by
  unfold sibling
  krSimp
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    krSimp
    refine writerWP_mono (kr_getNode K B s c w hv hk hb hi) ?_
    rintro sn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hne
      rw [writerWP_pure]
      refine ⟨hb1, hi1, hle1, hp1, hs, hl1, ?_⟩
      cases hsl : sn.leaf <;> cases inner <;> simp_all

/-- A node named by a klong of an inner node p is of p's segment; its entry
in `gh` and leaf flag. -/
theorem kr_sib_facts {K : KindOracle} {B : NodeId} {c : Ctx} {vr v : W} {p s : NodeId}
    {pn sn : KNode} {gp hp i : Nat} (hb : Book B c v) (hk : ViewKinds K B c) (hir : KrInv K B vr)
    (hpn : vr.nodes.lookup p = some pn) (hpt : (p, gp, hp) ∈ vr.gh) (hh : hp ≠ 0)
    (hle : KrLe vr v) (hptr : pn.ptr? i = some s) (hls : v.nodes.lookup s = some sn) :
    ∃ hs, (s, gp, hs) ∈ v.gh ∧ sn.leaf = (hs == 0) := by
  obtain ⟨c0, hc0⟩ := kr_ptr_mem hptr
  have hseg : IsKeySeg K v s gp :=
    ((kr_cache_node hir hpn hpt c0 s (kr_mem_of_get hc0)).1 hh).krMono hle
  obtain ⟨gs, hs, hm⟩ := kr_tag_of_lookup hb hls
  have := kr_seg_unique hb hk hm hseg
  subst this
  exact ⟨hs, hm, kr_leaf hb hls hm⟩

/-- The live klongs of a merged node, of x's segment and of a height with x's
leaf flag, are of the right kind for the new nodes. -/
theorem kr_live_kinds {K : KindOracle} {B : NodeId} {vr v : W} {o : NodeId} {on : KNode}
    {g ho h : Nat} (hl : vr.nodes.lookup o = some on) (hi : KrInv K B vr) (hm : (o, g, ho) ∈ vr.gh)
    (hon : on.leaf = (ho == 0)) (hxn : on.leaf = (h == 0)) (hk : KrLe vr v) :
    krPairs (KindKlong K v g h) on.live := by
  have hph := krPairs_live (kr_cache_node hi hl hm)
  have hiff : ho = 0 ↔ h = 0 := by
    rw [hon] at hxn
    constructor
    · intro h0; subst h0; simp at hxn; exact hxn.symm ▸ rfl
    · intro h0; subst h0; simp at hxn; exact hxn
  intro q hq
  have hk' := (hph q hq).krMono hk
  refine ⟨fun h0 => hk'.1 (fun h1 => h0 (hiff.mp h1)), fun h0 => hk'.2 (hiff.mpr h0)⟩

theorem kr_merge_first {P : Nat → NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b f : List (Nat × NodeId)} {s : Option (List (Nat × NodeId) × Nat)}
    (he : mergeKlongs inner cap cR a b = (f, s)) (hP : inner = true → krFree P)
    (ha : krPairs P a) (hb : krPairs P b) : krPairs P f := by
  have h := (krPairs_mergeKlongs inner cap cR hP ha hb).1
  rw [he] at h; exact h

theorem kr_merge_second {P : Nat → NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b f ks2 : List (Nat × NodeId)} {s : Option (List (Nat × NodeId) × Nat)} {g2 : Nat}
    (he : mergeKlongs inner cap cR a b = (f, s)) (hs : s = some (ks2, g2))
    (hP : inner = true → krFree P) (ha : krPairs P a) (hb : krPairs P b) : krPairs P ks2 := by
  have h := (krPairs_mergeKlongs inner cap cR hP ha hb).2
  rw [he] at h; exact h _ hs

theorem kr_sib_leaf {sn xn : KNode} {hx : Nat} (hsl : sn.leaf = !!xn.leaf)
    (hxl : xn.leaf = (hx == 0)) : sn.leaf = (hx == 0) := by
  rw [hsl, Bool.not_not, hxl]

/-- The sibling, with its entry in `gh` (p's segment) and its leaf flag (x's). -/
macro "krSibM " hl1:term:max hpt:term:max hh:term:max hxl:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_sibling ?krK ?krB _ _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro ⟨_, _⟩ _ ⟨hkdB, hkdI, hkdL, _, hkdP, hkdS, hkdSl⟩
  obtain ⟨_, _, _⟩ := kr_sib_facts hkdB (by assumption) (by assumption) $hl1 $hpt $hh
    (by krChain) hkdP hkdS
  have := kr_sib_leaf hkdSl $hxl))

/-- The segment and height of x, known. -/
macro "krGhX " hxt:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (kr_ghOf ?krK ?krB _ _ _ ?krView ?krKinds ?krBook ?krInv) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro ⟨_, _⟩ _ ⟨hkdB, _, _, _, _, hkdT, _⟩
  obtain ⟨hkdG, hkdH⟩ := kr_tag_eq hkdB (KrLe.gh' $hxt (by krChain)) hkdT
  subst hkdG
  subst hkdH))

/-- The klongs of a merge's new nodes. -/
theorem kr_free_inner' {K : KindOracle} {w : W} {g h : Nat} {leaf : Bool} (hl : leaf = (h == 0))
    (hin : (!leaf) = true) : krFree (KindKlong K w g h) := by
  apply kr_free_of_leaf hl
  cases leaf
  · rfl
  · simp at hin

theorem kr_merge_snd' {P : Nat → NodeId → Prop} {inner : Bool} {cap cR : Nat}
    {a b ks2 : List (Nat × NodeId)} {g2 : Nat}
    (hs : (mergeKlongs inner cap cR a b).2 = some (ks2, g2)) (hP : inner = true → krFree P)
    (ha : krPairs P a) (hb : krPairs P b) : krPairs P ks2 :=
  (krPairs_mergeKlongs inner cap cR hP ha hb).2 _ hs

theorem kr_live_kinds' {K : KindOracle} {B : NodeId} {vr v : W} {o : NodeId} {on : KNode}
    {g ho h : Nat} (hl : vr.nodes.lookup o = some on) (hi : KrInv K B vr) (hm : (o, g, ho) ∈ vr.gh)
    (hon : on.leaf = (ho == 0)) (hxn : on.leaf = (h == 0)) (hk : KrLe vr v) :
    krPairs (KindKlong K v g h) on.live := kr_live_kinds hl hi hm hon hxn hk

macro "krLive" : tactic => `(tactic| exact kr_live_kinds (by assumption) (by assumption) (by krTag) (by assumption) (by assumption) (by krChain))

macro "krKsMerge" : tactic => `(tactic| first
  | (refine krKs_newKlongs _ (krPairs_mergeKlongs _ _ _ ?krF ?krA1 ?krA2).1
     case krF => (intro hkdIn; refine kr_free_inner' ?krLl hkdIn; assumption)
     case krA1 => krLive
     case krA2 => krLive)
  | (refine krKs_newKlongs _ (kr_merge_snd' (by assumption) ?krF ?krA1 ?krA2)
     case krF => (intro hkdIn; refine kr_free_inner' ?krLl hkdIn; assumption)
     case krA1 => krLive
     case krA2 => krLive))

macro "krCreateM" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ (newKlongs _ _)) _ _ _)
  (refine writerWP_mono (kr_newKey ?krK ?krB _ _ _ _ _ _ ?krBook ?krInv ?krH ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krH => krHeight
  case krKs => krKsMerge
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

macro "krMPm " hpp:term:max hpt:term:max hh:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_mergeParent ?krK ?krB _ _ _ _ _ _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ (kr_path_at $hpp ?krPe) _ _ (KrLe.gh' $hpt ?krKt) $hh ?krM1 ?krM2) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krPe => krPathEq
  case krKt => krChain
  case krM1 => exact kr_isKey (by krTag)
  case krM2 => (intro _ _ hkdE; (cases hkdE) <;> exact kr_isKey (by krTag))
  rintro _ _ ⟨_, _, _, _⟩))

macro "krRet" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (retarget _ _ _) _ _ _)
  (refine writerWP_mono (kr_retarget ?krK ?krB _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ _ (by krTag) (kr_isKey (by krTag))) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 20000 in
/-- A merge of x, the path's node at depth d, below an inner node. -/
theorem kr_merge (K : KindOracle) (B : NodeId) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KrInv K B w)
    (hd : d ≠ 0) (ax : Option Nat) (hpx : w.path[d]? = some (ax, x))
    (hpq : ∀ a q, w.path[d - 1]? = some (a, q) →
      ∃ nq, w.nodes.lookup q = some nq ∧ nq.leaf = false) :
    WriterWP (merge x d) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold merge
  krSimp
  refine writerWP_mono (kr_pathNode (e + 1 - 1) c w) ?_
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
    have := kr_leaf hb hnq hpt
    rw [hnql] at this; simp at this
  obtain ⟨k, hak⟩ : ∃ k, ax = some k := by
    cases ax with
    | none => exact absurd rfl (hi.pathSome e none x hpx)
    | some k => exact ⟨k, rfl⟩
  subst hak
  have hxs : IsKeySeg K w x gp := (hi.path e ap p' k x hpp hpx gp hp hpt).1 hh
  refine writerWP_mono (kr_getNode K B p' c w hv hk hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hpt1 := KrLe.gh' hpt hle1
  refine writerWP_mono (kr_getNode K B x c w1 hv hk hb1 hi1) ?_
  rintro xn w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
  obtain ⟨gx, hx, hxt⟩ := kr_tag_of_lookup hb2 hl2
  have := kr_seg_unique hb2 hk hxt (hxs.krMono (hle1.trans hle2))
  subst this
  have hxl : xn.leaf = (hx == 0) := kr_leaf hb2 hl2 hxt
  have hpp2 : w.path[e]? = some (ap, p') := hpp
  clear hpq hnq hnql hpx hxs
  repeat' first
    | krSimp
    | simp only [List.forIn_cons, List.forIn_nil]
    | krSibM hl1 hpt1 hh hxl
    | krGhX hxt
    | krCreateM
    | krMPm hpp2 hpt hh
    | krRet
    | krTake
    | krUseP (kr_unlink _ _ _)
    | krCore
    | wpSplit
    | split
    | contradiction

end SIS.Tree
