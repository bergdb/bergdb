/-
A delete into a segment leaf keeps the writer's tree (bergdb 024-22,
`OpTreeOK`), as prover putinv's `putInv_del_leafBelow` (024-12): the bitmap
with room, or the leaf, full by its size or by its dead klongs, time split (in
place for a leaf the transaction made) to its last version without the key,
below an inner parent with room, the merges off: `treeOK_timeSplit_sub`,
`writerWP_appendDeleteKlong_tree`, `writerWP_del_leafBelow_tree`.
-/
import SIS.Tree.PutInvDelFull
import SIS.Tree.WriterTreeSpaceSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The tree after a time split of L below q to a new node y whose live klongs
are some of L's: q's klong k1 names y; L is left behind. -/
theorem treeOK_timeSplit_sub (N N' : NodeId → Option KNode) (t : Time) (r q L y : NodeId)
    (qn n m : KNode) (k1 : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n)
    (hN'q : N' q = some (qn.add t (.key k1 y))) (hN'y : N' y = some m)
    (hmsub : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y → N' z = N z)
    (hfy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y) :
    TreeOK N' t r := by
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hLy : L ≠ y := fun h => by rw [h, hfy] at hLn; cases hLn
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hql : ∀ c' z, TLink N' t q c' z → (c' = k1 ∧ z = y) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact KNode.add_key_liveAt_mem qn t k1 y hqwf hqt c' z hc
  have hyl : ∀ c' z, TLink N' t y c' z → TLink N t L c' z := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'y] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨n, hLn, hmsub c' z hc⟩
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ y → ∀ c' z, TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2 h3] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = y → ¬ TReach N t r z := by
    intro z hz; rw [hz]; exact not_reach_fresh N t r y hT hfy hfresh
  apply treeOK_transfer_gone N N' t r r (fun z => z = y) (fun z => z = L)
    (fun u c' => if u = L then (y, c') else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)⟩
  · intro u c' z hu hug hl
    have huL : u ≠ L := hug
    by_cases huy : u = y
    · rw [huy] at hl
      have hl0 := hyl c' z hl
      refine Or.inr ⟨fun hz => ?_, L, c', hL, hl0, by simp [huy]⟩
      have hz' : z = L := hz
      rw [hz'] at hl0
      exact hT.no_self_link L c' hL hl0
    · have huR : TReach N t r u := hu.elim id (fun h => absurd h huy)
      by_cases huq : u = q
      · rw [huq] at hl
        rcases hql c' z hl with ⟨_, h⟩ | ⟨hc, hm⟩
        · exact Or.inl h
        · have hl0 : TLink N t q c' z := ⟨qn, hqn, hm⟩
          refine Or.inr ⟨fun hz => ?_, q, c', hq, hl0, by simp [hqL, huq]⟩
          have hz' : z = L := hz
          rw [hz'] at hl0
          exact hc (hLpar q c' hq hl0).2
      · have hl0 := hOld u huL huq huy c' z hl
        refine Or.inr ⟨fun hz => ?_, u, c', huR, hl0, by simp [huL]⟩
        have hz' : z = L := hz
        rw [hz'] at hl0
        exact huq (hLpar u c' huR hl0).1
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hz' : z = y := hz
    have hone : ∀ v d, (TReach N t r v ∨ v = y) → v ≠ L → TLink N' t v d z → v = q ∧ d = k1 := by
      intro v d hv hvg hl
      rw [hz'] at hl
      by_cases hvy : v = y
      · rw [hvy] at hl; exact absurd (hyl d y hl) (hfresh L d hL)
      · have hvR : TReach N t r v := hv.elim id (fun h => absurd h hvy)
        by_cases hvq : v = q
        · rw [hvq] at hl
          rcases hql d y hl with ⟨hd, _⟩ | ⟨_, hm⟩
          · exact ⟨hvq, hd⟩
          · exact absurd ⟨qn, hqn, hm⟩ (hfresh q d hq)
        · exact absurd (hOld v hvg hvq hvy d y hl) (hfresh v d hvR)
    obtain ⟨a1, b1⟩ := hone u c' hu hug hl1
    obtain ⟨a2, b2⟩ := hone u' c'' hu' hug' hl2
    exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z hz hzg
    have h1 : z = y := hz
    have h2 : z = L := hzg
    exact hLy (h2.symm.trans h1)
  · by_cases hrq : r = q
    · rw [hrq, hN'q]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hry : r ≠ y := fun h => by rw [h, hfy] at hrm; cases hrm
      rw [hother r hrL hrq hry]; exact ⟨rm, hrm⟩

/-- A delete's bitmap in a node L below an inner parent q with room: by the
bitmap, or, full by its size or by its dead klongs, by a time split of L's last
version without the key (in place for a node the transaction made), the
writer's tree is kept. -/
theorem writerWP_appendDeleteKlong_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w3 : W) (cv k1 d' : Nat) (L q : NodeId) (n qn : KNode)
    (hT : TreeOK (wNode c.p base w3) c.i w3.top.rootKey)
    (hq : TReach (wNode c.p base w3) c.i w3.top.rootKey q)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hLt : w3.taken.contains L = false) (hqt' : w3.taken.contains q = false)
    (hql : qn.leaf = false) (hk1 : (k1, L) ∈ qn.liveAt c.i) (hqL : q ≠ L)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : wNode c.p base w3 w3.next = none) (hnyt : w3.taken.contains w3.next = false)
    (hfresh : ∀ u c', TReach (wNode c.p base w3) c.i w3.top.rootKey u →
      ¬ TLink (wNode c.p base w3) c.i u c' w3.next) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 =>
      TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
  have hwL : wNode c.p base w3 L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk3]
  have hwq : wNode c.p base w3 q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq3]
  have hnlive : n.liveAt c.i = n.live := KNode.liveAt_of_times n c.i hnt
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlsub
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hlsub hsplit
  have hlastsub : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z h
    rw [hleq, KNode.liveAt_of_times last c.i hlt] at h
    rw [hnlive]; exact hlsub c' z h
  -- the outcome of a time split of the full node
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
    intro compact hcs s
    have hlk3' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup L = some n := hlk3
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ (d' + 1) L n last compact c
        base hvc _ hlk3' hLt hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, hN4⟩
      rw [h4top]
      refine treeOK_of_node_shrink (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey L n
        ⟨n.leaf, last.ks⟩ hT hwL (by rw [hN4]; simp) ?_ hlastsub
      intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rfl
    · have hny' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup
          ({ w3 with trail := s :: w3.trail } : W).next = none := by
        show w3.nodes.lookup w3.next = none
        unfold wNode at hny; simp only [hnyt, Bool.false_eq_true, ↓reduceIte] at hny
        split at hny
        · cases hny
        · assumption
      refine writerWP_mono (writerWP_handleFullWith_timeSplit_nil d' L q n qn last k1 compact c _
        hlk3' hlq3 hqL hql hnew hcs hpq hpk hroomq hdeadq hny') ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [h4top]
      have h4t' : w4.taken = w3.taken := h4t
      have hLy : L ≠ w3.next := fun h => by rw [h, hny] at hwL; cases hwL
      have hqy : q ≠ w3.next := fun h => by rw [h, hny] at hwq; cases hwq
      apply treeOK_timeSplit_sub (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey q L
        w3.next qn n ⟨n.leaf, last.ks⟩ k1 hT hq hwq hk1 hqwf hqt hwL
      · simp only [wNode, h4t', hqt', Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · simp only [wNode, h4t', hnyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm, hqy.symm]
      · exact hlastsub
      · intro x hxL hxq hxy
        simp only [wNode, h4t', h4nodes, hxL, hxq, hxy, ↓reduceIte]
      · exact hny
      · exact hfresh
  -- the bitmap in L: a node that loses live klongs only
  have hshrink : ∀ (n' : KNode) (s : String),
      (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 =>
        TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
    intro n' s hsub
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine treeOK_of_node_shrink (wNode c.p base w3) _ c.i w3.top.rootKey L n n' hT hwL ?_ ?_ hsub
    · simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hy
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro old hold c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z, (c', z) ∈ (n.add c.i (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
      intro _
      by_cases hsz : n.size + 1 < c.p.M
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hsz)]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]; exact htime true _ (by simp)
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]; exact hshrink _ _ hadd
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hsz)]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i) with
        | false =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt)
        | true =>
          simp only [Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]; exact htime true _ (by simp)
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
            exact hshrink _ _ (hsetAt old hg)
      | _ =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- A delete of a key whose prefix is there, below an inner segment root and an
inner parent with room, by a bitmap in its segment leaf, which keeps a live
klong, the merges off, keeps the writer's tree: with room for the bitmap, or the
leaf full by its size or by its dead klongs, time split (in place for a leaf the
transaction made) when its last version without the key has at most h klongs
(as prover putinv's `putInv_del_leafBelow`). -/
theorem writerWP_del_leafBelow_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimes : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : w.taken.contains w.next = false := by
    cases h' : w.taken.contains w.next with
    | false => rfl
    | true => have := hidt _ h'; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  apply writerWP_del_seg_leaf c base hvc pre cv rk w hrk ht hidn hidv hinner
  intro L n q qn k1 d' w3 hL hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 _ hpq hpk _
  obtain ⟨hne, hkeep, hsplit⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    eqVisits_reach _ _ _ cv c.p.fuel rk L cv hrrk hL
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have hqt' : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  obtain ⟨hN3, htop3, htk3, _, hnext3⟩ := hr3
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_tree c base hvc w3 cv k1 d' L q n qn
    (by rw [hN3, htop3]; exact hT) (by rw [hN3, htop3]; exact reachS_tReach _ _ _ _ hrq) hlk3 hlq3
    (by rw [htk3]; exact hLt) (by rw [htk3]; exact hqt') hql hk1 hqL (htimes L n hrL hn)
    (htimes q qn hrq hqn) (hwf q qn hrq hqn) hpq hpk hne hsplit hroomq (hdeadq k1)
    (by rw [hN3, hnext3]; exact hfree _ (Nat.le_refl _)) (by rw [htk3, hnext3]; exact htn)
    (by rw [hN3, htop3, hnext3]; exact hfreshT _ (Nat.le_refl _))) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

end SIS.Tree
