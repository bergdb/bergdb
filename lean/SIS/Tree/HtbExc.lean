/-
`htb`'s sites (bergdb 025-05, step 8): the merges' loop's last merge with a tall parent q
(`tk_exc`). The merge keeps the tall nodes' frame but at q (`tk_mergeChk`), and q, a node
of the transaction that stays in place, names the second new node beside another node of
the transaction or has two live klongs (`qx_mergeChk`, the walk of HtbExcWalk.lean).
-/
import SIS.Tree.HtbExcWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section Q

variable {y : NodeId} {k N : Nat}

theorem wp_of_all {α : Type} {f : M α} {c : Ctx} {w : W} {post : α → W → Prop}
    (h : ∀ r v, post r v) : WriterWP f c w post :=
  fun r v _ => h r v

theorem qn_newKey2 {m : KNode} (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (newKey g h leaf ks) c w (fun r v => r = w.next ∧ N ≤ r ∧ (r, g, h) ∈ v.gh ∧ r < v.next ∧
      (∀ e ∈ w.gh, e ∈ v.gh) ∧ FrameD y m k N v) :=
  writerWP_mono (qn_newKey g h leaf ks c w hw) (fun r v h' => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h'
    subst h1
    exact ⟨rfl, hw.2.2.2.2, h2, h3, h4, h5⟩)

theorem qn_setMadeFor {m : KNode} (x : NodeId) (old : Option NodeId) (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (setMadeFor x old) c w (fun _ v => FrameD y m k N v ∧ v.gh = w.gh ∧ v.next = w.next) := by
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact ⟨hw.same (Nat.le_refl _) rfl rfl rfl, by simp, by simp⟩
  · simp only [writerWP_pure]; exact ⟨hw, by simp, by simp⟩

theorem wp_madeJ {β : Type} (b : Prop) [Decidable b] (o : NodeId) (J : Option NodeId → M β)
    (c : Ctx) (w : W) (post : β → W → Prop) (hJ : ∀ old, WriterWP (J old) c w post) :
    WriterWP (if b then (replacedBy o >>= J) else (pure (some o) >>= J)) c w post := by
  split
  · rw [writerWP_bind]
    refine writerWP_mono (kd_replacedBy o c w) ?_
    rintro old v ⟨rfl, -⟩
    exact hJ old
  · rw [writerWP_bind, writerWP_pure]
    exact hJ _

theorem fd_sibling {m : KNode} (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (sibling p pn i inner) c w (fun sn v => FrameD y m k N v ∧ pn.ptr? i = some sn.1) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (fd_getNode s c w hw) ?_
    intro sn v hv
    split
    · exact writerWP_throw _ _ _ _
    · exact (writerWP_pure _ _ _ _).mpr ⟨hv, hs⟩

end Q

theorem KNode.cv_of_key {n : KNode} {i cv : Nat} {z : NodeId} (h : n.ks[i]? = some (Klong.key cv z)) :
    n.cv? i = some cv := by
  simp [KNode.cv?, h]

macro "fdG " pat:term "," h:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP $pat _ _ _)
  fdUse $h))

set_option maxHeartbeats 12800000 in
/-- The merge's tail below a parent q of the transaction: after a merge into two, q, not
taken back, names m2 and m1 or one of S0, or has two live klongs. -/
theorem qx_mergeTailChk (B : NodeId) (q : NodeId) (pn : KNode) (S0 : NodeId → Prop) (N : Nat)
    (c : Ctx) (hmp : MergeParamsOK c.p) (hpos : 0 < c.i)
    (x : NodeId) (d : Nat) (xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat)
    (r : NodeId) (rn : KNode) (ir : Nat) (w : W)
    (hw : FrameD q pn (d - 1) N w) (hBN : B ≤ N) (hS0 : ∀ y, S0 y → y < N)
    (hnew : pn.firstTime = some c.i) (hleaf : pn.leaf = false)
    (htimes : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hS : ∀ cv y, (cv, y) ∈ pn.live → S0 y) (hlS : S0 l) (hrS : S0 r) (hlq : l ≠ q) (hrq : r ≠ q)
    (hLK : ∀ cL, pn.cv? il = some cL → pn.ks[il]? = some (Klong.key cL l))
    (hRK : ∀ cR, pn.cv? ir = some cR → pn.ks[ir]? = some (Klong.key cR r))
    (hc : ∀ cL cR, pn.cv? il = some cL → pn.cv? ir = some cR → cL ≠ cR) :
    WriterWP (mergeTailChk c x d q pn xn leftSome l ln il r rn ir) c w
      (fun k v => k = 2 → ∃ m1 m2 e1 e2, QW q m1 m2 S0 e1 e2 N c v ∧ e1.1 = m1 ∧ e2.1 = m2 ∧
        B ≤ m1 ∧ B ≤ m2 ∧ m1 ≠ m2) := by
  unfold mergeTailChk
  repeat' first
    | (with_reducible assumption)
    | wpSimplify
    | (with_unfolding_none exact writerWP_throw _ _ _ _)
    | fdG (note _), (fd_note _)
    | fdG (ghOf _), (fd_ghOf _)
    | wpSplit
    | ((with_unfolding_none fail_if_success guard_target = WriterWP (newKey _ _ _ _) _ _ _); split)
  all_goals
    have hL := hLK _ ‹pn.cv? il = some _›
    have hR := hRK _ ‹pn.cv? ir = some _›
    have hcLR := hc _ _ ‹pn.cv? il = some _› ‹pn.cv? ir = some _›
    refine writerWP_mono (qn_newKey2 _ _ _ _ c _ (by assumption)) ?_
    rintro m1 w6 ⟨-, hN1, he1, hlt1, -, hw6⟩
    refine wp_madeJ _ l _ c w6 _ (fun old => ?_)
    simp only [writerWP_bind]
    refine writerWP_mono (qn_setMadeFor m1 old c w6 hw6) ?_
    rintro _ w8 ⟨hw8, hg8, hn8⟩
    split
    · rename_i ks2 g2 _
      simp only [writerWP_bind]
      refine writerWP_mono (qn_newKey2 _ _ _ _ c w8 hw8) ?_
      rintro m2 w9 ⟨hm2, hN2, he2, hlt2, hgh2, hw9⟩
      have h12 : m1 ≠ m2 := by omega
      refine wp_madeJ _ r _ c w9 _ (fun old2 => ?_)
      simp only [writerWP_bind]
      refine writerWP_mono (qn_setMadeFor m2 old2 c w9 hw9) ?_
      rintro _ w11 ⟨hw11, hg11, hn11⟩
      simp only [writerWP_pure]
      rw [← hg8] at he1
      have he1' := hgh2 _ he1
      rw [← hg11] at he1' he2
      have he2' := he2
      refine writerWP_mono (writerWP_and (writerWP_and
        (qx_mergeParent q pn (d - 1) il _ m1 ir _ m2 g2 c w11 hw11 hnew)
        (@fields_mergeParent (ghHasFields _) q (d - 1) il _ m1 ir _ _ c w11 he1'))
        (@fields_mergeParent (ghHasFields _) q (d - 1) il _ m1 ir _ _ c w11 he2')) ?_
      rintro _ w12 ⟨⟨⟨mq, hw12, hmq⟩, he1''⟩, he2''⟩
      obtain ⟨hql, hqf, hsh⟩ := shape_mp c.p hmp pn c.i il _ m1 ir _ m2 g2 l r S0 hL hR hcLR hS
        (fun h => absurd (hS0 _ h) (by omega)) h12 hpos htimes hnew hleaf mq hmq
      refine writerWP_mono (qx_cleanup q m1 m2 S0 _ _ c h12 _ w12 ?_
        ⟨he1'', he2'', mq, hw12.zero, hql, hqf, hsh⟩) ?_
      · intro o ho
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl
        · refine ⟨hlq, ?_⟩
          intro e
          have := hS0 _ hlS
          simp only at e
          omega
        · refine ⟨hrq, ?_⟩
          intro e
          have := hS0 _ hrS
          simp only at e
          omega
      · intro _ v hv
        try simp only [writerWP_pure]
        intro _
        exact ⟨m1, m2, _, _, hv, rfl, rfl, by omega, by omega, h12⟩
    · simp only [writerWP_bind, writerWP_pure]
      refine wp_of_all (fun _ _ => wp_of_all (fun _ _ => ?_))
      intro hk
      rw [‹(mergeKlongs _ _ _ _ _).snd = none›] at hk
      simp at hk

set_option maxHeartbeats 3200000 in
/-- The merge of x below a parent q of the transaction, q at depth d - 1 of the path and
none of its first d - 1 nodes: after a merge into two, the walk's state at q. -/
theorem qx_mergeChk (B : NodeId) (x : NodeId) (d : Nat) (c : Ctx) (hmp : MergeParamsOK c.p)
    (hpos : 0 < c.i) (w : W) (q : NodeId) (nq : KNode) (S0 : NodeId → Prop) (aq : Option Nat)
    (hpq : w.path[d - 1]? = some (aq, q)) (hw : FrameD q nq (d - 1) w.next w)
    (hBN : B ≤ w.next) (hS0 : ∀ y, S0 y → y < w.next)
    (hnew : nq.firstTime = some c.i) (hleaf : nq.leaf = false)
    (htimes : ∀ s, Klong.time s ∈ nq.ks → s ≤ c.i)
    (hS : ∀ cv y, (cv, y) ∈ nq.live → S0 y) (hSq : ∀ y, S0 y → y ≠ q) :
    WriterWP (mergeChk x d) c w (fun k v => k = 2 → ∃ m1 m2 e1 e2, QW q m1 m2 S0 e1 e2 w.next c v ∧
      e1.1 = m1 ∧ e2.1 = m2 ∧ B ≤ m1 ∧ B ≤ m2 ∧ m1 ≠ m2) := by
  unfold mergeChk
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_pathNode (d - 1) c w) ?_
  rintro p w0 ⟨hw0, ap, hpp⟩
  subst w0
  rw [hpq] at hpp
  simp only [Option.some.injEq, Prod.mk.injEq] at hpp
  obtain ⟨-, rfl⟩ := hpp
  rw [writerWP_getNode_known q nq c w hw.2.1]
  have hchild : ∀ i cv y, LastLive nq.ks nq.lastBitmap i cv → nq.ptr? i = some y → S0 y :=
    fun i cv y hl hy => hS cv y (ht_live_of_last hl hy).2
  refine writerWP_mono (fd_getNode x c w hw) ?_
  intro xn w2 hw2
  refine writerWP_mono (kd_klongAt d c w2) ?_
  rintro cx w2' ⟨hw2', -⟩
  subst w2'
  generalize hmi : mergeIdx nq cx = mi
  obtain ⟨ixo, ia, ib⟩ := mi
  have hML := mergeIdx_last nq cx
  rw [hmi] at hML
  obtain ⟨hMx, hMa, hMb⟩ := hML
  have htail : ∀ (wb : W) (leftSome : Bool) (l : NodeId) (ln : KNode) (il cvl : Nat) (r : NodeId)
      (rn : KNode) (ir cvr : Nat), FrameD q nq (d - 1) w.next wb →
      LastLive nq.ks nq.lastBitmap il cvl → nq.ptr? il = some l →
      LastLive nq.ks nq.lastBitmap ir cvr → nq.ptr? ir = some r → cvl < cvr →
      WriterWP (mergeTailChk c x d q nq xn leftSome l ln il r rn ir) c wb
        (fun k v => k = 2 → ∃ m1 m2 e1 e2, QW q m1 m2 S0 e1 e2 w.next c v ∧
          e1.1 = m1 ∧ e2.1 = m2 ∧ B ≤ m1 ∧ B ≤ m2 ∧ m1 ≠ m2) := by
    intro wb leftSome l ln il cvl r rn ir cvr hwb hLl hpl hLr hpr hlt
    have hkl := (ht_live_of_last hLl hpl).1
    have hkr := (ht_live_of_last hLr hpr).1
    refine qx_mergeTailChk B q nq S0 w.next c hmp hpos x d xn leftSome l ln il r rn ir wb hwb hBN hS0
      hnew hleaf htimes hS (hchild _ _ _ hLl hpl) (hchild _ _ _ hLr hpr) (hSq _ (hchild _ _ _ hLl hpl))
      (hSq _ (hchild _ _ _ hLr hpr)) ?_ ?_ ?_
    · intro cL h
      rw [KNode.cv_of_key hkl] at h
      cases h
      exact hkl
    · intro cR h
      rw [KNode.cv_of_key hkr] at h
      cases h
      exact hkr
    · intro cL cR h1 h2
      rw [KNode.cv_of_key hkl] at h1
      rw [KNode.cv_of_key hkr] at h2
      cases h1
      cases h2
      omega
  split
  · rename_i ix hix
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    have hpx' : nq.ptr? ix = some x := by simpa using hptr
    have hLx := hMx ix hix
    have hright : ∀ (wb : W) (ia0 cva : Nat), FrameD q nq (d - 1) w.next wb →
        LastLive nq.ks nq.lastBitmap ia0 cva → cx < cva →
        WriterWP (do
          let __x ← sibling q nq ia0 !xn.leaf
          mergeTailChk c x d q nq xn false x xn ix __x.1 __x.2 ia0) c wb
          (fun k v => k = 2 → ∃ m1 m2 e1 e2, QW q m1 m2 S0 e1 e2 w.next c v ∧
            e1.1 = m1 ∧ e2.1 = m2 ∧ B ≤ m1 ∧ B ≤ m2 ∧ m1 ≠ m2) := by
      intro wb ia0 cva hb hLa hxa
      rw [writerWP_bind]
      refine writerWP_mono (fd_sibling q nq ia0 (!xn.leaf) c wb hb) ?_
      rintro ⟨rs, rsn⟩ w4 ⟨h4, hs4⟩
      exact htail w4 false x xn ix cx rs rsn ia0 cva h4 hLx hpx' hLa hs4 hxa
    split
    · rename_i ib0 cvb
      obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
      simp only [writerWP_bind]
      refine writerWP_mono (fd_sibling q nq ib0 (!xn.leaf) c w2 hw2) ?_
      rintro ⟨ls, lsn⟩ w3 ⟨h3, hs3⟩
      refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · exact htail w3 true ls lsn ib0 cvb x xn ix cx h3 hLb hs3 hLx hpx' hbx
      · rw [writerWP_bind, writerWP_pure]
        dsimp only
        split
        · rename_i ia0 cva _
          obtain ⟨hLa, hxa⟩ := hMa ia0 cva rfl
          exact hright w3 ia0 cva h3 hLa hxa
        · exact writerWP_throw _ _ _ _
    · rw [writerWP_bind, writerWP_pure]
      dsimp only
      split
      · rename_i ia0 cva
        obtain ⟨hLa, hxa⟩ := hMa ia0 cva rfl
        exact hright w2 ia0 cva hw2 hLa hxa
      · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
