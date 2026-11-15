/-
The fit after a merge of the merges' loop (bergdb 024-12, section 1, toward
hMSF's true form): from the heights' books with their bound at the merge's
start (`HtJ`), its end fits the fuel (`mergeFits_of_htJ`), as
`delFullFitsOKR_of` is for the bitmap. The heights' walk goes through the merge
with no holder premise (`ht_merge_of_J`); the bound through it is an `SBInvS`
walk (`sbS_merge`: the merged nodes get x's height, the parent's cascade at
most one above the path), with the nodes not taken back at the end not taken
back at the start (`writerWP_merge_untaken_before`). The same for a step of
root collapse, toward hCoF's true form (`collapseFits_of_htJ`, `sbS_replaceRoot`).
-/
import SIS.Tree.DelMergeUp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section SBMerge

variable {S : NodeId → Prop}

theorem sbS_takenBack (b : Nat) (x : NodeId) : KeepsSBS b S (takenBack x) := sbS_of_frame (by sbFrameTac)

theorem sbS_modMerges (b : Nat) : KeepsSBS b S (modify (fun w : W => { w with merges := w.merges + 1 })) :=
  sbS_of_frame (by sbFrameTac)

theorem sbS_unlink (b : Nat) (x : NodeId) : KeepsSBS b S (unlink x) := by
  intro c w0 w hH hw
  unfold unlink
  repeat' first
    | wpSimplify
    | sbsCore
    | wpSplit
    | split
    | contradiction

theorem sbS_retarget (b : Nat) (p src dst : NodeId) : KeepsSBS b S (retarget p src dst) := by
  intro c w0 w hH hw
  unfold retarget
  repeat' first
    | wpSimplify
    | sbsCore
    | wpSplit
    | split
    | contradiction

theorem sbS_sibling (b : Nat) (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsSBS b S (sibling p pn i inner) := by
  intro c w0 w hH hw
  unfold sibling
  repeat' first
    | wpSimplify
    | sbsCore
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem sbS_mergeParent (b : Nat) (p : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (c : Ctx) (w0 w : W) (hH : c.p.H < b) (hw : SBInvS c.p b S w0 w)
    (hpb : PathBelowSB b w0) (a : Option Nat) (hpx : w0.path[depth]? = some (a, p)) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w (fun _ v => SBInvS c.p b S w0 v) := by
  unfold mergeParent
  repeat' first
    | wpSimplify
    | sbsCore
    | (refine writerWP_mono (sbS_handleFull b depth p _ _ c w0 _ hH (by sbsState) hpb a hpx) ?_;
       intro _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 3200000 in
/-- A merge at the path's node at depth d keeps the heights of the ids S picks
at most b when the path's nodes are below b: the merged nodes get x's height,
the parent's cascade at most one above the path (`sbS_mergeParent`). -/
theorem sbS_merge (b : Nat) (x : NodeId) (d : Nat) (c : Ctx) (w0 w : W) (hH : c.p.H < b)
    (hw : SBInvS c.p b S w0 w) (hpb : PathBelowSB b w0) (ax : Option Nat)
    (hpx : w0.path[d]? = some (ax, x)) :
    WriterWP (merge x d) c w (fun _ v => SBInvS c.p b S w0 v) := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_pathNode (d - 1) c w) ?_
  rintro p w' ⟨hw', ap, hpp⟩
  subst hw'
  have hpp0 : w0.path[d - 1]? = some (ap, p) := by rw [← hw.2.2.1]; exact hpp
  repeat' first
    | simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
    | sbsUse (sbS_modMerges _)
    | simp only [List.forIn_cons, List.forIn_nil]
    | (with_unfolding_none refine writerWP_mono (sbS_ghOf b x c w0 _ hH (by sbsState)) ?_
       rintro ⟨g, h⟩ _ ⟨_, hm⟩
       have hhb := sbS_path_lt hH (by assumption) hpb hpx hm)
    | sbsCore
    | sbsUse (sbS_unlink _ _)
    | sbsUse (sbS_retarget _ _ _ _)
    | sbsUse (sbS_takenBack _ _)
    | sbsUse (sbS_sibling _ _ _ _ _)
    | (refine writerWP_mono (sbS_mergeParent b p (d - 1) _ _ _ _ _ _ c w0 _ hH (by sbsState) hpb ap hpp0) ?_;
       intro _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The nodes taken back only grow in a merge -/

theorem takenP_takenBack_mono (Pt : List NodeId → Prop) (hmono : ∀ l y, Pt l → Pt (y :: l)) (x : NodeId) :
    KeepsTakenP Pt (takenBack x) := by
  intro c w hw
  unfold takenBack
  simp only [writerWP_modify]
  exact hmono _ _ hw

set_option maxHeartbeats 1600000 in
theorem takenP_merge_mono (Pt : List NodeId → Prop) (hmono : ∀ l y, Pt l → Pt (y :: l)) (x : NodeId) (d : Nat) :
    KeepsTakenP Pt (merge x d) := by
  intro c w hw
  unfold merge
  repeat' first
    | tkSimplifyP
    | simp only [List.forIn_cons, List.forIn_nil]
    | tkCoreP
    | tkUseP (takenP_ghOf _ _)
    | tkUseP (takenP_sibling _ _ _ _ _)
    | tkUseP (takenP_mergeParent _ _ _ _ _ _ _ _ _)
    | tkUseP (takenP_retarget _ _ _ _)
    | tkUseP (takenP_unlink _ _)
    | tkUseP (takenP_takenBack_mono _ hmono _)
    | wpSplit
    | split
    | contradiction

/-- A node not taken back after a merge was not taken back before it. -/
theorem writerWP_merge_untaken_before (x : NodeId) (d : Nat) (c : Ctx) (w : W) :
    WriterWP (merge x d) c w (fun _ v => ∀ y, v.taken.contains y = false → w.taken.contains y = false) := by
  refine writerWP_mono (takenP_merge_mono (fun l => ∀ y, w.taken.contains y = true → l.contains y = true)
    (fun l z h y hy => by have h1 := h y hy; simp at h1 ⊢; exact Or.inr h1) x d c w (fun _ h => h)) ?_
  intro _ v hv y hy
  cases h : w.taken.contains y with
  | false => rfl
  | true => have := hv y h; rw [hy] at this; cases this

set_option maxHeartbeats 1600000 in
/-- The fit after a merge of the merges' loop from the heights' books with
their bound at its start (`HtJ`), as `delFullFitsOKR_of` is for the bitmap:
the heights' walk through the merge (`ht_merge_of_J`), the heights of the ids
not taken back at most p.fuel at its end (`sbS_merge`), so the end fits p.fuel
(`segFits_of_heightsU`). -/
theorem mergeFits_of_htJ {H : NodeId → Nat → Prop} (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (f : Nat) (hcap : 1 ≤ c.p.mergeMax) (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hvo : ViewHtOK H B c) (hbase : BaseHeights c H base)
    (hHb : ∀ y h, H y h → h ≤ c.p.H)
    (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hIJ : DelInvJF c base w0 key f B v) (hb : PutBook c B top0 v) (hd : 0 < d)
    (hx : (v.path[d]?).map (·.2) = some x) (hq : (v.path[d - 1]?).map (·.2) = some q)
    (hqn : v.nodes.lookup q = some qn) (hql : qn.leaf = false) (hxn : v.nodes.lookup x = some xn)
    (hcnt : xn.cnt < c.p.mergeBelow) (hP : PathOK c v d X K Nn) (hXd : X d = x)
    (hJ : HtJ c H B v) (hlen : v.path.length = d + 1) :
    WriterWP (merge x d) c v (fun _ v' => SegFits (wNode c.p base v') c.i c.p.fuel v'.top.rootKey) := by
  obtain ⟨ax, hpx⟩ : ∃ a, v.path[d]? = some (a, x) := by
    cases he : v.path[d]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨e.1, by rw [← hx]⟩
  have hfuel : c.p.H + 2 < c.p.fuel := fuel_gt_H c.p
  have hpg := ht_pathGh_all hJ.book hJ.inv (x := x) ⟨ax, by rw [hlen, Nat.add_sub_cancel]; exact hpx⟩ hxn
  have hpb : PathBelowSB c.p.fuel v := by
    intro d' a' q' hq'
    obtain ⟨⟨q'', g', h'⟩, hm', he⟩ := List.mem_map.mp (hpg d' a' q' hq')
    simp only at he
    subst he
    refine ⟨hJ.book.bound _ hm', fun g2 h2 hm2 => ?_⟩
    have hqf := hJ.free d' a' q'' (List.getElem?_eq_some_iff.mp hq').1 hq'
    have := hJ.bound q'' g2 h2 hm2 hqf
    omega
  have hS0 : SBInvS c.p c.p.fuel (fun y => v.taken.contains y = false) v v :=
    ⟨fun y g' h' hm' hy => Nat.le_trans (hJ.bound y g' h' hm' hy) (Nat.sub_le _ _), Nat.le_refl _,
      rfl, fun _ _ _ hm' _ => Or.inl hm'⟩
  have hpf : PathFreeTo v (d + 1) := by rw [← hlen]; exact hJ.free
  refine writerWP_mono (writerWP_and (writerWP_and
    (ht_merge_of_J c base hvc f hcap hsa2 B top0 hB B hvo w0 key x q d v qn xn hJ.book hJ.inv X K Nn hIJ hb hd
      hx hq hqn hql hxn hcnt hP hXd ax hpx hpf)
    (sbS_merge c.p.fuel x d c v v (by omega) hS0 hpb ax hpx))
    (writerWP_merge_untaken_before x d c v)) ?_
  rintro _ v' ⟨⟨⟨hbv, hiv, -, -⟩, hsv⟩, hut⟩
  refine segFits_of_heightsU hbv hiv.cache hvo.heights base hbase c.p.fuel _ ?_
  intro y n hn k hk
  rcases hk with ⟨g', hm'⟩ | hk
  · exact hsv.1 y g' k hm' (hut y (wNode_cases _ _ _ _ _ hn).1)
  · have := hHb y k hk; omega

end SBMerge

/-! ## A step of root collapse -/

section SBCollapse

variable {S : NodeId → Prop}

set_option maxHeartbeats 1600000 in
/-- A replaceRoot at the path's node at depth keeps the heights of the ids S
picks at most b when the path's nodes are below b (the cascade of the holder's
new klong, `sbS_appendKlongs`). -/
theorem sbS_replaceRoot (b : Nat) (x : NodeId) (depth only : Nat) (c : Ctx) (w0 w : W) (hH : c.p.H < b)
    (hw : SBInvS c.p b S w0 w) (hpb : PathBelowSB b w0) :
    WriterWP (replaceRoot x depth only) c w (fun _ v => SBInvS c.p b S w0 v) := by
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
  intro n w1 hw1
  split
  · exact writerWP_throw _ _ _ _
  · split
    · repeat' first
        | wpSimplify
        | sbsCore
        | sbsUse (sbS_unlink _ _)
    · rename_i d
      simp only [writerWP_bind]
      refine writerWP_mono (sbS_note b _ c w0 w1 hH hw1) ?_
      intro _ w2 hw2
      refine writerWP_mono (writerWP_and (sbS_pathNode b d c w0 w2 hH hw2) (kd_pathNode d c w2)) ?_
      rintro leaf w3 ⟨hw3, -, al, hpl⟩
      have hpl0 : w0.path[d]? = some (al, leaf) := by rw [← hw2.2.2.1]; exact hpl
      refine writerWP_mono (sbS_klongAt b (d + 1) c w0 w3 hH hw3) ?_
      intro k w4 hw4
      refine writerWP_mono (sbS_unlink b x c w0 w4 hH hw4) ?_
      intro _ w5 hw5
      exact sbS_appendKlongs b d leaf _ c w0 w5 hH hw5 hpb ⟨al, hpl0⟩

end SBCollapse

set_option maxHeartbeats 1600000 in
/-- `hCoF`'s true form for one step of root collapse: from the heights' books
with their bound at a replaceRoot's start (`HtJ`), at the path's last node x, a
segment root below a segment leaf, its end fits p.fuel (`ht_replaceRoot`,
`sbS_replaceRoot`; replaceRoot takes nothing back). -/
theorem collapseFits_of_htJ {H : NodeId → Nat → Prop} (c : Ctx) (base : View BVal) (B : NodeId)
    (hvo : ViewHtOK H B c) (hbase : BaseHeights c H base) (hHb : ∀ y h, H y h → h ≤ c.p.H)
    (hpos : 0 < c.i) (v : W) (x : NodeId) (n : KNode) (only : Nat) (hJ : HtJ c H B v)
    (hn : v.nodes.lookup x = some n) (hnl : n.leaf = false) (honly : n.onlyLiveKlong = some only)
    (hcv0 : n.cv? only = some 0) (a : Option Nat) (hpx : v.path[v.path.length - 1]? = some (a, x))
    (hseg : ∀ a' q, v.path.length - 1 ≠ 0 → v.path[v.path.length - 1 - 1]? = some (a', q) →
      ∃ g', (q, g', 0) ∈ v.gh) :
    WriterWP (replaceRoot x (v.path.length - 1) only) c v
      (fun _ v' => SegFits (wNode c.p base v') c.i c.p.fuel v'.top.rootKey) := by
  have hfuel : c.p.H + 2 < c.p.fuel := fuel_gt_H c.p
  have hlen0 : 0 < v.path.length := by
    have := (List.getElem?_eq_some_iff.mp hpx).1; omega
  have hpg := ht_pathGh_all hJ.book hJ.inv (x := x) ⟨a, hpx⟩ hn
  have hpb : PathBelowSB c.p.fuel v := by
    intro d' a' q' hq'
    obtain ⟨⟨q'', g', h'⟩, hm', he⟩ := List.mem_map.mp (hpg d' a' q' hq')
    simp only at he
    subst he
    refine ⟨hJ.book.bound _ hm', fun g2 h2 hm2 => ?_⟩
    have hqf := hJ.free d' a' q'' (List.getElem?_eq_some_iff.mp hq').1 hq'
    have := hJ.bound q'' g2 h2 hm2 hqf
    omega
  have hS0 : SBInvS c.p c.p.fuel (fun y => v.taken.contains y = false) v v :=
    ⟨fun y g' h' hm' hy => Nat.le_trans (hJ.bound y g' h' hm' hy) (Nat.sub_le _ _), Nat.le_refl _,
      rfl, fun _ _ _ hm' _ => Or.inl hm'⟩
  obtain ⟨⟨x', gx, hx⟩, hmx, hex⟩ := List.mem_map.mp (hpg _ a x hpx)
  simp only at hex
  subst hex
  have hpf : PathFreeTo v (v.path.length - 1 + 1) := by rw [Nat.sub_add_cancel hlen0]; exact hJ.free
  refine writerWP_mono (writerWP_and (writerWP_and
    (ht_replaceRoot B x' (v.path.length - 1) only c v hvo hpos hJ.book hJ.inv gx hx hmx n hn hnl honly hcv0
      a hpx hpf hseg)
    (sbS_replaceRoot c.p.fuel x' (v.path.length - 1) only c v v (by omega) hS0 hpb))
    (takenP_replaceRoot (fun l => l = v.taken) x' (v.path.length - 1) only c v rfl)) ?_
  rintro _ v' ⟨⟨⟨hbv, hiv, -⟩, hsv⟩, htv⟩
  refine segFits_of_heightsU hbv hiv.cache hvo.heights base hbase c.p.fuel _ ?_
  intro y m hm k hk
  rcases hk with ⟨g', hm'⟩ | hk
  · exact hsv.1 y g' k hm' (by rw [← htv]; exact (wNode_cases _ _ _ _ _ hm).1)
  · have := hHb y k hk; omega

end SIS.Tree
