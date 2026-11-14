/-
Step 4 (B), part 3 (bergdb 024-22; 024-12's (4)): a put adds at most one to
the heights. A put descends (loads, at most H), and makes at most one cascade:
the leaf's klongs, or a new segment leaf's klong in the leaf above, after which
the new segment leaves below have room (`seenHeight_putKv_put`).
-/
import SIS.Tree.HeightsFuelMerge
import SIS.Tree.WriterHeightsPut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A step that keeps every cached height at most m. -/
def KeepsSHB (m : Nat) {α : Type} (f : M α) : Prop :=
  ∀ c w, c.p.H ≤ m → SeenHeightBound m w → WriterWP f c w (fun _ v => SeenHeightBound m v)

/-- `SeenHeightBound` asked only of the ids S picks (for the fuel after a
delete's cascade: S the ids not taken back). The descent's lemmas below are
proved for every S; `KeepsSHB` is the case of every id (`keepsSHB_of_S`). -/
def SeenHeightBoundS (m : Nat) (S : NodeId → Prop) (w : W) : Prop :=
  ∀ x g h, (x, g, h) ∈ w.gh → S x → h ≤ m

def KeepsSHBS (m : Nat) (S : NodeId → Prop) {α : Type} (f : M α) : Prop :=
  ∀ c w, c.p.H ≤ m → SeenHeightBoundS m S w → WriterWP f c w (fun _ v => SeenHeightBoundS m S v)

theorem keepsSHB_of_S {m : Nat} {α : Type} {f : M α} (h : KeepsSHBS m (fun _ => True) f) :
    KeepsSHB m f :=
  fun c w hH hw => writerWP_mono (h c w hH (fun x g k hm _ => hw x g k hm))
    (fun _ _ hv x g k hm => hv x g k hm trivial)

theorem shbS_of_gh {α : Type} {m : Nat} {S : NodeId → Prop} {f : M α}
    (hf : ∀ c w, WriterWP f c w (fun _ v => v.gh = w.gh)) : KeepsSHBS m S f := by
  intro c w _ hw
  refine writerWP_mono (hf c w) ?_
  intro _ v hg x g h hm hs
  exact hw x g h (by rw [← hg]; exact hm) hs

theorem shbS_getNode (m : Nat) (S : NodeId → Prop) (x : NodeId) : KeepsSHBS m S (getNode x) := by
  intro c w hH hw
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]; exact hw
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        intro a g d hd hs
        simp only [List.mem_cons, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl, rfl⟩ | hd
        · exact Nat.le_trans (heightOf_le c.p _) hH
        · exact hw a g d hd hs
    · exact writerWP_throw _ _ _ _

theorem shb_of_gh {α : Type} {m : Nat} {f : M α}
    (hf : ∀ c w, WriterWP f c w (fun _ v => v.gh = w.gh)) : KeepsSHB m f :=
  keepsSHB_of_S (shbS_of_gh hf)

theorem shb_getNode (m : Nat) (x : NodeId) : KeepsSHB m (getNode x) :=
  keepsSHB_of_S (shbS_getNode m _ x)

theorem shb_newKey (m g h : Nat) (leaf : Bool) (ks : List Klong) (hh : h ≤ m) :
    KeepsSHB m (newKey g h leaf ks) := by
  intro c w _ hw
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    intro a g' d hd
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl, rfl⟩ | hd
    · exact hh
    · exact hw a g' d hd

macro "shbGhTac" : tactic => `(tactic| (
  intro c w
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
        writerWP_set, writerWP_modify, note, fresh, putNode, newValue, pathAdd, pathSize]
    | exact writerWP_throw _ _ _ _
    | rfl
    | wpSplit
    | split))

theorem shb_note (m : Nat) (s : String) : KeepsSHB m (note s) := shb_of_gh (by shbGhTac)
theorem shb_newValue (m : Nat) (h : Nat) : KeepsSHB m (newValue h) := shb_of_gh (by shbGhTac)
theorem shb_putNode (m : Nat) (x : NodeId) (n : KNode) : KeepsSHB m (putNode x n) :=
  shb_of_gh (by shbGhTac)
theorem shbS_pathAdd (m : Nat) (S : NodeId → Prop) (a : Option Nat) (x : NodeId) :
    KeepsSHBS m S (pathAdd a x) :=
  shbS_of_gh (by shbGhTac)
theorem shb_pathAdd (m : Nat) (a : Option Nat) (x : NodeId) : KeepsSHB m (pathAdd a x) :=
  keepsSHB_of_S (shbS_pathAdd m _ a x)

theorem shb_ghOf (m : Nat) (x : NodeId) (c : Ctx) (w : W) (hH : c.p.H ≤ m)
    (hw : SeenHeightBound m w) :
    WriterWP (ghOf x) c w (fun r v => SeenHeightBound m v ∧ r.2 ≤ m) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (shb_getNode m x c w hH hw) ?_
  intro _ v hv
  simp only [writerWP_get]
  split
  · rename_i gh hh
    simp only [writerWP_pure]
    exact ⟨hv, hv x gh.1 gh.2 (gh_lookup_mem hh)⟩
  · exact writerWP_throw _ _ _ _

theorem shbS_descendLte (m cv : Nat) (S : NodeId → Prop) :
    ∀ (fuel : Nat) (x : NodeId), KeepsSHBS m S (descendLte cv fuel x) := by
  intro fuel
  induction fuel with
  | zero => intro x c w _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hH hw
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (shbS_getNode m S x c w hH hw) ?_
    intro n v hv
    split
    · rw [writerWP_pure]; exact hv
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind]
        refine writerWP_mono (shbS_pathAdd m S _ _ c v hH hv) ?_
        intro _ u hu
        exact ih _ c u hH hu

theorem shb_descendLte (m cv : Nat) : ∀ (fuel : Nat) (x : NodeId), KeepsSHB m (descendLte cv fuel x) :=
  fun fuel x => keepsSHB_of_S (shbS_descendLte m cv _ fuel x)

section Put

variable {H : NodeId → Nat → Prop}

/-- The path's nodes are cached when its last node is (at a state with the
walk's state). -/
theorem ht_pathGh_all {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (hi : HtInv H B c w)
    {x : NodeId} {n : KNode} (hlast : HtPathLast w x) (hx : w.nodes.lookup x = some n) :
    ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) → q ∈ w.gh.map (·.1) := by
  intro d a q hq
  obtain ⟨a', ha'⟩ := hlast
  have hlt := (List.getElem?_eq_some_iff.mp hq).1
  by_cases hd : d + 1 < w.path.length
  · exact hi.pathGh d a q hq hd
  · have : d = w.path.length - 1 := by omega
    subst this
    rw [ha'] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨-, rfl⟩ := hq
    obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb hx
    exact ht_mem_ids hm

set_option maxHeartbeats 1600000 in
/-- A put's last segment: every cached height from m to m + 1. -/
theorem shb_setValue_put (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (hv0 : Nat)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (_hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (hM : 2 ≤ c.p.M) (hpf : PathFreeTo w w.path.length)
    (hr : HtPathLast w segRoot ∨ w.nodes.lookup segRoot = some ⟨true, []⟩)
    (m : Nat) (hH : c.p.H ≤ m) (hs : SeenHeightBound m w) :
    WriterWP (setValue segRoot cv key (some hv0)) c w (fun _ v => SeenHeightBound (m + 1) v) := by
  unfold setValue
  htSimp
  refine writerWP_mono (writerWP_and (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf hr)
    (shb_descendLte m cv c.p.fuel segRoot c w hH hs)) ?_
  rintro leaf w1 ⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hleaf0⟩, hpf1⟩, hs1⟩
  try htSimp
  refine writerWP_mono (writerWP_and (writerWP_and (ht_newValue B hv0 c w1 hvo hb1 hi1)
    (kd_newValue_nodes hv0 c w1)) (shb_newValue m hv0 c w1 hH hs1)) ?_
  rintro y w2 ⟨⟨⟨hb2, hi2, hk2, hp2, ht2, hy2⟩, hn2, -⟩, hs2⟩
  rcases hlast with ⟨a, ha⟩ | ⟨rfl, hp1, he⟩
  · refine writerWP_mono (writerWP_and (hw_getNode B leaf c w2 hvo hb2 hi2)
      (shb_getNode m leaf c w2 hH hs2)) ?_
    rintro n w3 ⟨⟨hb3, hi3, hle3, hl3, hp3⟩, hs3⟩
    split
    · htSimp
      refine writerWP_mono (shb_putNode m leaf _ c w3 hH hs3) ?_
      intro _ v hv
      exact hv.mono (Nat.le_succ m)
    · htSimp
      refine writerWP_mono (kd_pathSize c w3) ?_
      rintro sz w4 ⟨hw, hsz⟩
      rw [hw, hsz]
      have ha3 : w3.path[w3.path.length - 1]? = some (a, leaf) := by
        rw [hp3, hp2]; exact ha
      have hpg := ht_pathGh_all hb3 hi3 ⟨a, ha3⟩ hl3
      exact seenHeight_appendKlongs hb3 hs3 hH hpg leaf _ [(cv, y)] a ha3
  · have he2 : w2.nodes.lookup leaf = some ⟨true, []⟩ := by rw [hn2]; exact he
    refine writerWP_mono (kd_getNode_hit leaf _ c w2 he2) ?_
    rintro n w3 ⟨hn3, hw3⟩
    rw [hn3, hw3]
    split
    · htSimp
      refine writerWP_mono (shb_putNode m leaf _ c w2 hH hs2) ?_
      intro _ v hv
      exact hv.mono (Nat.le_succ m)
    · rename_i hfull
      exact absurd (kd_empty_ok c.p hM c.i cv y) hfull

/-! ## Below a new segment leaf: no split -/

theorem descendLte_leaf_hit (cv : Nat) (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hl : w.nodes.lookup x = some n) (hleaf : n.leaf = true) (f : Nat) :
    WriterWP (descendLte cv (f + 1) x) c w (fun r v => r = x ∧ v = w) := by
  unfold descendLte
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_getNode_hit x n c w hl) ?_
  rintro n' v ⟨rfl, rfl⟩
  rw [if_pos hleaf, writerWP_pure]
  exact ⟨rfl, rfl⟩

theorem newKey_next (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W) :
    WriterWP (newKey g h leaf ks) c w (fun x _ => x = w.next) := by
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify

theorem fuel_succ (p : Params) : p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 := rfl

set_option maxHeartbeats 1600000 in
/-- setNode from a new segment leaf: it has room; every height kept. -/
theorem shb_setNode_empty (B : NodeId) (m : Nat) (segRoot : NodeId) (cv : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hM : 2 ≤ c.p.M) (hH : c.p.H ≤ m) (hb : Book B c w)
    (hs : SeenHeightBound m w) (hl : w.nodes.lookup segRoot = some ⟨true, []⟩) :
    WriterWP (setNode segRoot cv true) c w (fun r v => Book B c v ∧ SeenHeightBound m v ∧
      ∀ y, r = some y → v.nodes.lookup y = some ⟨true, []⟩) := by
  unfold setNode
  simp only [writerWP_bind, writerWP_read]
  rw [fuel_succ]
  refine writerWP_mono (descendLte_leaf_hit cv segRoot _ c w hl rfl _) ?_
  rintro r w1 ⟨hr1, hw1⟩
  subst r w1
  refine writerWP_mono (kd_getNode_hit segRoot _ c w hl) ?_
  rintro n w2 ⟨hn2, hw2⟩
  subst n w2
  rw [nex_run_searchEq_nil _ _ _ rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
  refine writerWP_mono (writerWP_and (book_ghOf B segRoot c w hv hb) (shb_ghOf m segRoot c w hH hs)) ?_
  rintro ⟨g, h⟩ w3 ⟨⟨hb3, hk3⟩, hs3, -⟩
  refine writerWP_mono (writerWP_and (book_note B _ c w3 hv hb3) (shb_note m _ c w3 hH hs3)) ?_
  rintro _ w4 ⟨⟨hb4, hk4⟩, hs4⟩
  refine writerWP_mono (writerWP_and (writerWP_and (book_newKey B (g + 1) 0 true [] c w4 hb4 rfl)
    (shb_newKey m (g + 1) 0 true [] (Nat.zero_le _) c w4 hH hs4)) (newKey_next _ _ _ _ c w4)) ?_
  rintro child w5 ⟨⟨⟨hb5, hk5, hlc⟩, hs5⟩, hcn⟩
  rw [if_pos (kd_empty_lt c.p hM)]
  simp only [writerWP_bind]
  obtain ⟨n5, hl5, hlf5⟩ := (hk3.trans (hk4.trans hk5)).lookup hl
  have hrn : segRoot ≠ child := by
    intro he
    obtain ⟨g', h', hm'⟩ := kd_tag_of_lookup hb4 ((hk3.trans hk4).lookup hl).choose_spec.1
    have := hb4.bound _ hm'
    simp only at this
    omega
  refine writerWP_mono (writerWP_and (writerWP_and (book_putNode B segRoot _ c w5 hb5 ⟨n5, hl5, ?_⟩)
    (shb_putNode m segRoot _ c w5 hH hs5)) (kd_putNode_other segRoot _ n5 c w5 hl5)) ?_
  · rw [hlf5]; rfl
  rintro _ w6 ⟨⟨⟨hb6, -⟩, hs6⟩, hoth⟩
  rw [writerWP_pure]
  refine ⟨hb6, hs6, fun y hy => ?_⟩
  cases hy
  rw [hoth child (Ne.symm hrn)]
  exact hlc

/-- setValue on a new segment leaf: it has room; every height kept. -/
theorem shb_setValue_empty (m : Nat) (segRoot : NodeId) (cv : Nat) (key : Key) (hv0 : Nat)
    (c : Ctx) (w : W) (hM : 2 ≤ c.p.M) (hH : c.p.H ≤ m) (hs : SeenHeightBound m w)
    (hl : w.nodes.lookup segRoot = some ⟨true, []⟩) :
    WriterWP (setValue segRoot cv key (some hv0)) c w (fun _ v => SeenHeightBound m v) := by
  unfold setValue
  simp only [writerWP_bind, writerWP_read]
  rw [fuel_succ]
  refine writerWP_mono (descendLte_leaf_hit cv segRoot _ c w hl rfl _) ?_
  rintro r w1 ⟨hr1, hw1⟩
  subst r w1
  try simp only [writerWP_bind]
  refine writerWP_mono (writerWP_and (kd_newValue_nodes hv0 c w) (shb_newValue m hv0 c w hH hs)) ?_
  rintro y w2 ⟨⟨hn2, -⟩, hs2⟩
  have hl2 : w2.nodes.lookup segRoot = some ⟨true, []⟩ := by rw [hn2]; exact hl
  refine writerWP_mono (kd_getNode_hit segRoot _ c w2 hl2) ?_
  rintro n w3 ⟨hn3, hw3⟩
  subst n w3
  rw [if_pos (kd_empty_ok c.p hM c.i cv y)]
  try simp only [writerWP_bind]
  refine writerWP_mono (shb_putNode m segRoot _ c w2 hH hs2) ?_
  intro _ v hv
  rw [writerWP_pure]; exact hv

/-- The segments below a new segment leaf: no split; every height kept. -/
theorem shb_putSegs_empty (B : NodeId) (m : Nat) (key : Key) (hv0 : Nat) (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → 2 ≤ c.p.M → c.p.H ≤ m →
      Book B c w → SeenHeightBound m w → w.nodes.lookup r = some ⟨true, []⟩ →
      WriterWP (putSegs key (some hv0) segs r) c w (fun _ v => SeenHeightBound m v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hv hM hH hb hs hl
    cases rest with
    | nil =>
      unfold putSegs
      exact shb_setValue_empty m r cv key hv0 c w hM hH hs hl
    | cons d rest' =>
      unfold putSegs
      simp only [writerWP_bind]
      refine writerWP_mono (shb_setNode_empty B m r cv c w hv hM hH hb hs hl) ?_
      rintro res w1 ⟨hb1, hs1, hres⟩
      split
      · rw [writerWP_pure]; exact hs1
      · rename_i next
        exact ih next c w1 hv hM hH hb1 hs1 (hres next rfl)

set_option maxHeartbeats 3200000 in
/-- A put's setNode: every height at most m + 1; a found segment root leaves
them at most m, a new one is an empty segment leaf. -/
theorem shb_setNode_put (B : NodeId) (hframe : AppendFrameOK B) (segRoot : NodeId)
    (cv : Nat) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w)
    (hi : HtInv H B c w) (hM : 2 ≤ c.p.M) (hpf : PathFreeTo w w.path.length)
    (hr : HtPathLast w segRoot ∨ w.nodes.lookup segRoot = some ⟨true, []⟩)
    (m : Nat) (hH : c.p.H ≤ m) (hs : SeenHeightBound m w) :
    WriterWP (setNode segRoot cv true) c w (fun r v => SeenHeightBound (m + 1) v ∧
      ∀ y, r = some y → SeenHeightBound m v ∨ v.nodes.lookup y = some ⟨true, []⟩) := by
  unfold setNode
  htSimp
  refine writerWP_mono (writerWP_and (ht_descendLte B cv c.p.fuel segRoot c w hvo hb hi hpf hr)
    (shb_descendLte m cv c.p.fuel segRoot c w hH hs)) ?_
  rintro cur w1 ⟨⟨hb1, hi1, hle1, hlast, ⟨n0, hl0, hleaf0⟩, hpf1⟩, hs1⟩
  refine writerWP_mono (kd_getNode_hit cur n0 c w1 hl0) ?_
  rintro n w2 ⟨hn, hw⟩
  rw [hn, hw]
  split
  · htSimp
    refine writerWP_mono (shb_pathAdd m _ _ c w1 hH hs1) ?_
    intro _ v hv
    exact ⟨hv.mono (Nat.le_succ m), fun y _ => Or.inl hv⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    htSimp
    refine writerWP_mono (writerWP_and (hw_ghOf B cur c w1 hvo hb1 hi1) (shb_ghOf m cur c w1 hH hs1)) ?_
    rintro ⟨g, h⟩ w3 ⟨⟨hb3, hi3, hle3, hp3, -, -⟩, hs3, -⟩
    htSimp
    refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w3 hvo hb3 hi3)
      (shb_note m _ c w3 hH hs3)) ?_
    rintro _ w4 ⟨⟨hb4, hi4, hle4, hp4⟩, hs4⟩
    refine writerWP_mono (writerWP_and (hw_newKey B (g + 1) 0 true [] c w4 hb4 hi4 rfl
      (nodeHt_nil c w4 0 true)) (shb_newKey m (g + 1) 0 true [] (Nat.zero_le _) c w4 hH hs4)) ?_
    rintro child w5 ⟨⟨hb5, hi5, hle5, hp5, hlc, hmc, hcf, hcx⟩, hs5⟩
    have hle15 : HtLe w1 w5 := hle3.trans (hle4.trans hle5)
    obtain ⟨n5, hl5, hlf5⟩ := hle15.1.lookup hl0
    have hcg4 : cur ∈ w4.gh.map (·.1) := by
      obtain ⟨g', h', hm'⟩ := kd_tag_of_lookup hb1 hl0
      exact ht_mem_ids (HtLe.gh' hm' (hle3.trans hle4))
    have hcur : cur ≠ child := fun h => hcx (h ▸ hcg4)
    split
    · htSimp
      refine writerWP_mono (writerWP_and (shb_putNode m cur _ c w5 hH hs5)
        (kd_putNode_other cur _ n5 c w5 hl5)) ?_
      rintro _ v ⟨hv, hoth⟩
      refine ⟨hv.mono (Nat.le_succ m), fun y hy => ?_⟩
      cases hy
      exact Or.inr (by rw [hoth child (Ne.symm hcur)]; exact hlc)
    · rename_i hfull
      have hpl : HtPathLast w1 cur := by
        rcases hlast with h1 | ⟨hcr, hp, he⟩
        · exact h1
        · subst hcr
          rw [hl0] at he
          obtain rfl := Option.some.inj he
          exact absurd (kd_empty_lt c.p hM) hfull
      obtain ⟨a, ha⟩ := hpl
      have hpw : w5.path = w1.path := hp5.trans (hp4.trans hp3)
      have hpg1 := ht_pathGh_all hb1 hi1 ⟨a, ha⟩ hl0
      have hpg5 : ∀ (d : Nat) (a' : Option Nat) (q : NodeId), w5.path[d]? = some (a', q) →
          q ∈ w5.gh.map (·.1) := by
        intro d a' q hq
        rw [hpw] at hq
        obtain ⟨e, he, hee⟩ := List.mem_map.mp (hpg1 d a' q hq)
        exact List.mem_map.mpr ⟨e, HtLe.gh' he hle15, hee⟩
      have hpath : ∀ e ∈ w5.path, e.2 ≠ child := by
        intro e he hce
        rw [hpw] at he
        obtain ⟨d, hd⟩ := List.mem_iff_getElem?.mp he
        have := hpg1 d e.1 e.2 (by rw [hd])
        apply hcx
        rw [← hce]
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
        exact List.mem_map.mpr ⟨q, HtLe.gh' hq (hle3.trans hle4), hqe⟩
      htSimp
      refine writerWP_mono (kd_pathSize c w5) ?_
      rintro sz w6 ⟨hw6, hsz⟩
      rw [hw6, hsz]
      have ha5 : w5.path[w5.path.length - 1]? = some (a, cur) := by rw [hpw]; exact ha
      refine writerWP_mono (writerWP_and
        (seenHeight_appendKlongs hb5 hs5 hH hpg5 cur _ [(cv, child)] a ha5)
        (hframe _ cur [(cv, child)] c w5 child hvo.ids hb5 hlc (Ne.symm hcur) hpath)) ?_
      rintro _ v ⟨hv, hlcv⟩
      exact ⟨hv, fun y hy => by cases hy; exact Or.inr hlcv⟩

/-- The segments of a put: every cached height from m to m + 1. -/
theorem shb_putSegs_put (B : NodeId) (hframe : AppendFrameOK B) (key : Key) (hv0 : Nat)
    (segs : List Nat) (m : Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i → Book B c w → HtInv H B c w →
      2 ≤ c.p.M → ViewKlongsWf c.p c.view → WriterKlongsWf w → PathFreeTo w w.path.length →
      (HtPathLast w r ∨ w.nodes.lookup r = some ⟨true, []⟩) → c.p.H ≤ m →
      SeenHeightBound m w →
      WriterWP (putSegs key (some hv0) segs r) c w (fun _ v => SeenHeightBound (m + 1) v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ _ _ _ _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hvo hpos hb hi hM hkw hwf hpf hr hH hs
    cases rest with
    | nil =>
      unfold putSegs
      exact shb_setValue_put B r cv key hv0 c w hvo hpos hb hi hM hpf hr m hH hs
    | cons d rest' =>
      unfold putSegs
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and
        (ht_setNode_put B hframe r cv c w hvo hpos hb hi hM hkw hwf hpf hr)
        (klongsWf_setNode r cv true c w hkw hwf))
        (shb_setNode_put B hframe r cv c w hvo hb hi hM hpf hr m hH hs)) ?_
      rintro res w1 ⟨⟨⟨hb1, hi1, hle1, hpf1, hres⟩, hwf1⟩, hs1, hshb⟩
      split
      · rw [writerWP_pure]; exact hs1
      · rename_i next
        rcases hshb next rfl with hsm | hemp
        · exact ih next c w1 hvo hpos hb1 hi1 hM hkw hwf1 hpf1 (hres next rfl) hH hsm
        · exact shb_putSegs_empty B (m + 1) key hv0 (d :: rest') next c w1 hvo.ids hM
            (Nat.le_succ_of_le hH) hb1 hs1 hemp

theorem shb_pathClear (m : Nat) : KeepsSHB m pathClear := shb_of_gh (by
  intro c w; simp only [pathClear, writerWP_modify])

theorem shb_findRoot (m : Nat) : KeepsSHB m findRoot := shb_of_gh (by
  intro c w; simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure])

/-- (B) for a put: from every cached height at most m (and H at most m), a put
leaves every cached height at most m + 1. -/
theorem seenHeight_putKv_put (B : NodeId) (hframe : AppendFrameOK B) (key : Key) (hv0 : Nat)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (hM : 2 ≤ c.p.M) (hkw : ViewKlongsWf c.p c.view) (hwf : WriterKlongsWf w)
    (m : Nat) (hH : c.p.H ≤ m) (hs : SeenHeightBound m w) :
    WriterWP (putKv (.put key hv0)) c w (fun _ v => SeenHeightBound (m + 1) v) := by
  unfold putKv
  htSimp
  refine writerWP_mono (writerWP_and (writerWP_and (ht_pathClear B c w hvo hb hi)
    (klongsWf_pathClear c w hkw hwf)) (shb_pathClear m c w hH hs)) ?_
  rintro _ w1 ⟨⟨⟨hb1, hi1, hk1, hp1, ht1⟩, hwf1⟩, hs1⟩
  refine writerWP_mono (writerWP_and (writerWP_and (ht_findRoot B c w1 hvo hb1 hi1 hp1)
    (klongsWf_findRoot c w1 hkw hwf1)) (shb_findRoot m c w1 hH hs1)) ?_
  rintro root w2 ⟨⟨⟨hb2, hi2, hk2, hp2, ht2, hpf2⟩, hwf2⟩, hs2⟩
  have hl : HtPathLast w2 root := ⟨none, by rw [hp2]; rfl⟩
  exact shb_putSegs_put B hframe key hv0 key m root c w2 hvo hpos hb2 hi2 hM hkw hwf2
    (by rw [hp2]; exact hpf2) (Or.inl hl) hH hs2

end Put

end SIS.Tree
