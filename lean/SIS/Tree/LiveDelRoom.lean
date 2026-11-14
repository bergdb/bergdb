/-
`QLive` of a delete with the merges on that neither splits nor merges (bergdb
024-12, case (4a) of `l4`): the leaf has room for the bitmap and keeps a live
klong, and more than `mergeBelow` if an inner node names it, so after the
bitmap TP7's live counts hold as before (`liveCounts_updN_leaf`), and with them the merges' loop merges nothing
(`writerWP_afterDelete_none`). `l4` narrows to the deletes that split, empty
their leaf or merge (`opCaseOK_or`).
-/
import SIS.Tree.LiveNoMerge
import SIS.Tree.DelStepsWalk
import SIS.Tree.DelStepsTree
import SIS.Tree.GetCaseBridge
import SIS.Tree.WriterTreeVisits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A list without duplicates whose elements are all in l2 is no longer than l2. -/
theorem length_le_of_nodup_sub {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length := by
  intro l1
  induction l1 with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro l2 hn hs
    rw [List.nodup_cons] at hn
    have ha : a ∈ l2 := hs a List.mem_cons_self
    have ht : ∀ x ∈ t, x ∈ l2.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hs x (List.mem_cons_of_mem _ hx))
    have h1 := ih (l2.erase a) hn.2 ht
    rw [List.length_erase_of_mem ha] at h1
    have h2 : 0 < l2.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A node whose live klongs are another's but compare value cv's: its live
klongs are among the other's, and it has at most one fewer. -/
theorem live_shrink (n n' : KNode) (cv : Nat)
    (hl : ∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') :
    (∀ q ∈ n'.live, q ∈ n.live) ∧ n.live.length ≤ n'.live.length + 1 := by
  constructor
  · rintro ⟨a, b⟩ hq
    have h1 := lookup_of_mem_nodup n'.live n'.live_keys_nodup a b hq
    rw [hl a] at h1
    by_cases ha : a = cv
    · subst ha; simp at h1
    · have hb : (a == cv) = false := by simp [ha]
      rw [hb] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      exact mem_of_lookup_nodup n.live a b h1
  · have hK := n.live_keys_nodup
    have hsub : ∀ k ∈ (n.live.map Prod.fst).erase cv, k ∈ n'.live.map Prod.fst := by
      intro k hk
      rw [List.Nodup.mem_erase_iff hK] at hk
      obtain ⟨hkc, hkm⟩ := hk
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hkm
      have h1 := lookup_of_mem_nodup n.live hK a b hab
      have h2 : n'.live.lookup a = some b := by
        rw [hl a]
        have hb : (a == cv) = false := by simp [hkc]
        rw [hb]
        simpa using h1
      exact List.mem_map.mpr ⟨(a, b), mem_of_lookup_nodup _ a b h2, rfl⟩
    have h3 := length_le_of_nodup_sub _ _ (List.Nodup.erase cv hK) hsub
    rw [List.length_erase, List.length_map, List.length_map] at h3
    split at h3 <;> omega

/-- A node reached with flags after a leaf lost live klongs was reached so
before. -/
theorem fReach_updN_leaf (N : NodeId → Option KNode) (t : Time) (r L : NodeId) (n n' : KNode)
    (hL : N L = some n) (hnl : n.leaf = true) (hn'l : n'.leaf = true)
    (hsub : ∀ q ∈ n'.liveAt t, q ∈ n.liveAt t) :
    ∀ x b s, FReach (updN N L n') t r x b s → FReach N t r x b s := by
  intro x b s h
  induction h with
  | root => exact FReach.root
  | inner x b s m c y _ hm hml hcy ih =>
    by_cases hx : x = L
    · subst hx
      rw [updN_self] at hm
      cases hm
      rw [hn'l] at hml
      cases hml
    · rw [updN_ne _ _ _ _ hx] at hm
      exact FReach.inner x b s m c y ih hm hml hcy
  | seg x b s m c y _ hm hml hcy ih =>
    by_cases hx : x = L
    · subst hx
      rw [updN_self] at hm
      cases hm
      exact FReach.seg x b s n c y ih hL hnl (hsub _ hcy)
    · rw [updN_ne _ _ _ _ hx] at hm
      exact FReach.seg x b s m c y ih hm hml hcy

/-- TP7's live counts after a leaf lost live klongs but keeps one, and
`mergeBelow` with the merges on where an inner node names it. -/
theorem liveCounts_updN_leaf (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (n n' : KNode) (hLC : LiveCounts p N t r) (hL : N L = some n) (hnl : n.leaf = true)
    (hn'l : n'.leaf = true) (hsub : ∀ q ∈ n'.liveAt t, q ∈ n.liveAt t)
    (hpos : n'.liveAt t ≠ [])
    (hfill : ∀ b s, FReach N t r L b s → p.merges = true → b = false →
      p.mergeBelow ≤ (n'.liveAt t).length) :
    LiveCounts p (updN N L n') t r := by
  intro x b s m hfr hm
  have hfr0 := fReach_updN_leaf N t r L n n' hL hnl hn'l hsub x b s hfr
  by_cases hx : x = L
  · subst hx
    rw [updN_self] at hm
    cases hm
    exact ⟨fun h => absurd h hpos, (fun h => by rw [hn'l] at h; cases h),
      fun hm hb => hfill b s hfr0 hm hb⟩
  · rw [updN_ne _ _ _ _ hx] at hm
    exact hLC x b s m hfr0 hm

/-- (4a) A delete, the merges on, whose leaf has room for the bitmap and keeps a
live klong, and more than `mergeBelow` if an inner node names it (a segment
root's leaf need not): no split and no merge. -/
def DelRoomFillCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n ∧
    2 ≤ n.live.length ∧
    ∀ b s, FReach (wNode c.p base w) c.i w.top.rootKey L b s → b = false →
      c.p.mergeBelow + 1 ≤ n.live.length

/-- `QLive` of (4a): after the bitmap the leaf keeps a live klong, and at least
`mergeBelow` where an inner node names it, so the live counts hold, and the
merges' loop merges nothing. -/
theorem liveCase_delRoomFill (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) :
    OpCaseOK p R (QLive p) DelRoomFillCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI _ hPc
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0, hfill0⟩ := hPc
  subst hop'
  by_cases hLC0' : ¬ LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
  · intro _ _ _ _ h
    exact absurd h hLC0'
  have hLC0 : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey :=
    Classical.byContradiction hLC0'
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hleaf := keyLeaf_all2 hK hrk
      (fun L m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m ∧
        2 ≤ m.live.length ∧
        ∀ b s, FReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey L b s →
          b = false → p.mergeBelow + 1 ≤ m.live.length)
      ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0, hfill0⟩
  refine writerWP_mono (writerWP_del_roomM (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base
    top hB hbook hrk (hI.pathUntaken _)
    (fun L n hL hn hnl =>
      let ⟨a, b, c', d, e, _, _⟩ := hleaf L n hL hn hnl
      ⟨a, b, c', d, e⟩)
    (fun v => LiveCounts p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey)
    ?_ ?_) (fun _ _ h _ _ => h)
  · intro v hv
    unfold fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hv
  · intro L n w3 v g h hL hn hnl hr03 _ hLt hvt hvtop _ _ _ _ hex _
    obtain ⟨n', hnodes, hleafeq, hwf', htimes', hlive', _⟩ := hex
    obtain ⟨_, htn, _, _, _, h2, hfill⟩ := hleaf L n hL hn hnl
    have h3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
    have hN : wNode p (viewOf (treeRun p ts)) v = updN (wNode p (viewOf (treeRun p ts)) w) L n' := by
      have e3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
      rw [wNode_upsert_updN p _ w3 v L n' hnodes hvt h3t, e3]
    have hvtop' : v.top = w.top := hvtop.trans hr03.2.1
    obtain ⟨hsubl, hlen⟩ := live_shrink n n' cv hlive'
    have e1 : n.liveAt (ts.length + 1) = n.live := KNode.liveAt_of_times n _ htn
    have e2 : n'.liveAt (ts.length + 1) = n'.live := KNode.liveAt_of_times n' _ htimes'
    have hsub : ∀ q ∈ n'.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
      rw [e1, e2]; exact hsubl
    have hpos : n'.liveAt (ts.length + 1) ≠ [] := by
      rw [e2]
      intro h0
      rw [h0] at hlen
      simp at hlen
      omega
    have hLC1 : LiveCounts p (updN (wNode p (viewOf (treeRun p ts)) w) L n') (ts.length + 1)
        w.top.rootKey :=
      liveCounts_updN_leaf p _ _ _ L n n' hLC0 hn hnl (by rw [hleafeq]; exact hnl) hsub hpos
        (fun b s hfr _ hb => by rw [e2]; have := hfill b s hfr hb; omega)
    -- the links after are links before
    have hsubT : ∀ x c y, TLink (updN (wNode p (viewOf (treeRun p ts)) w) L n') (ts.length + 1) x c y →
        TLink (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) x c y := by
      rintro x c y ⟨m, hm, hc⟩
      by_cases hx : x = L
      · subst hx
        rw [updN_self] at hm
        cases hm
        exact ⟨n, hn, hsub _ hc⟩
      · rw [updN_ne _ _ _ _ hx] at hm
        exact ⟨m, hm, hc⟩
    refine writerWP_mono (writerWP_afterDelete_none (pre ++ [cv]) g h (ctxOf p ts) _
      (viewCoherent_ctxOf p ts) v ?_ ?_ ?_ ?_) ?_
    · intro y hy
      change TReach (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey y at hy
      rw [hN, hvtop'] at hy
      have hy0 := tReach_of_sublinks _ _ _ _ hsubT y hy
      change v.taken.contains y = false
      rw [hvt, hr03.2.2.1]
      exact hI.untaken y (tReach_reachS _ _ _ _ hy0)
    · intro y yn _ hyn
      change wNode p (viewOf (treeRun p ts)) v y = some yn at hyn
      rw [hN] at hyn
      by_cases hyL : y = L
      · subst hyL
        rw [updN_self] at hyn
        cases hyn
        exact hwf'
      · rw [updN_ne _ _ _ _ hyL] at hyn
        exact hI.wf y yn hyn
    · intro y yn hyn
      change wNode p (viewOf (treeRun p ts)) v y = some yn at hyn
      rw [hN] at hyn
      by_cases hyL : y = L
      · subst hyL
        rw [updN_self] at hyn
        cases hyn
        exact htimes'
      · rw [updN_ne _ _ _ _ hyL] at hyn
        exact hI.times y yn hyn
    · change LiveCounts p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey
      rw [hN, hvtop']
      exact hLC1
    · intro _ v' hrv
      change LiveCounts p (wNode p (viewOf (treeRun p ts)) v') (ts.length + 1) v'.top.rootKey
      have e4 : wNode p (viewOf (treeRun p ts)) v' = wNode p (viewOf (treeRun p ts)) v := hrv.1
      rw [e4, hrv.2.1, hN, hvtop']
      exact hLC1

/-- A case from two narrower cases that cover it. -/
theorem opCaseOK_or (p : Params) (R : Struct BVal → Time → Prop) (Q : List Tx → Op → W → W → Prop)
    (C C1 C2 : Ctx → View BVal → W → Op → Prop)
    (hcov : ∀ c base w op, C c base w op → C1 c base w op ∨ C2 c base w op)
    (h1 : OpCaseOK p R Q C1) (h2 : OpCaseOK p R Q C2) : OpCaseOK p R Q C :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC =>
    (hcov _ _ _ _ hC).elim
      (fun h => h1 ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO h)
      (fun h => h2 ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO h)

/-- (4) but (4a): a delete, the merges on, that splits its leaf, empties it, or
leaves it with at most `mergeBelow` live klongs (and so may merge). -/
def DelMergeRestCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelMergeCase c base w op ∧ ¬ DelRoomFillCase c base w op

/-- `l4` narrowed: `QLive` of the delete with the merges from `QLive` of the
deletes that are not (4a). -/
theorem liveCase_delMerge_of_rest (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hrest : OpCaseOK p R (QLive p) DelMergeRestCase) :
    OpCaseOK p R (QLive p) DelMergeCase :=
  opCaseOK_or p R (QLive p) DelMergeCase DelRoomFillCase _
    (fun c base w op h => (Classical.em (DelRoomFillCase c base w op)).elim Or.inl
      (fun hn => Or.inr ⟨h, hn⟩))
    (liveCase_delRoomFill p R hRL) hrest

end SIS.Tree
