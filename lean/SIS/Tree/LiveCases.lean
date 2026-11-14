/-
`QLive`, the obligation that an operation keeps `LiveCounts` (bergdb 024-12,
TP7, `LiveCounts.lean`), for the operation cases.

* (1) A put into its leaf with room (`liveCase_putLeafRoom`). The leaf gets
  a key klong. Its live klongs are the ones before and the new one, so it has
  at least as many (`KNode.add_key_liveAt_length`). The tree reached is the
  one before, plus the new pointee, which is no node
  (`fReach_updN_leafPut`).
* (3a) A put of a key with one new segment, below a leaf with room
  (`liveCase_putNewSeg1Room`). The leaf gets a key klong to a new segment
  leaf with one live klong, which is a segment root
  (`liveCounts_leafNew`).
* (3b) Two new segments or more below a leaf with room
  (`liveCase_putNewSegsRoom`): `rangeOrder_put_newSegs`'s walk with the new
  leaves' live klongs (`writerWP_putSegs_new_live`) and the general step
  (`liveCounts_leafAddNewSet`).
-/
import SIS.Tree.LiveCounts
import SIS.Tree.GetOpCases
import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A key klong put into a leaf -/

/-- A key klong added at time t keeps every live klong at t but the one of its
compare value, which it replaces. -/
theorem KNode.add_key_liveAt_keep (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (hc : c ≠ cv) (h : (c, y) ∈ n.liveAt t) : (c, y) ∈ (n.add t (.key cv v)).liveAt t := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [KNode.liveAt_of_times _ t ht']
  rw [KNode.liveAt_of_times _ t ht] at h
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t cv c v hw]
  have hb : (cv == c) = false := by simpa using (Ne.symm hc)
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c y h

/-- A key klong added at time t leaves at least as many live klongs at t. -/
theorem KNode.add_key_liveAt_length (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (n.liveAt t).length ≤ ((n.add t (.key cv v)).liveAt t).length := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  have hsub : ∀ c ∈ (n.liveAt t).map Prod.fst, c ∈ ((n.add t (.key cv v)).liveAt t).map Prod.fst := by
    intro c hc
    obtain ⟨⟨c', y⟩, hm, hcc⟩ := List.mem_map.mp hc
    simp only at hcc
    subst hcc
    by_cases hce : c' = cv
    · subst hce
      exact List.mem_map.mpr ⟨(c', v), KNode.add_key_liveAt_self n t c' v hw ht, rfl⟩
    · exact List.mem_map.mpr ⟨(c', y), KNode.add_key_liveAt_keep n t cv v hw ht c' y hce hm, rfl⟩
  have hnd : ((n.liveAt t).map Prod.fst).Nodup := by
    rw [KNode.liveAt_of_times _ t ht]; exact KNode.live_keys_nodup n
  have h := hnd.length_le_of_subset hsub
  simpa using h

/-- The tree reached after a key klong is put into a leaf L, with the flags, is
the tree before, but for the new pointee, which is no node. -/
theorem fReach_updN_leafPut (N : NodeId → Option KNode) (t : Time) (r L : NodeId) (n : KNode)
    (cv : Nat) (v : NodeId) (hL : N L = some n) (hnl : n.leaf = true)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hv : N v = none)
    (hvL : v ≠ L) :
    ∀ x b s, FReach (updN N L (n.add t (.key cv v))) t r x b s → FReach N t r x b s ∨ x = v := by
  intro x b s h
  induction h with
  | root => exact Or.inl FReach.root
  | inner x b s m c y _ hm hml hc ih =>
    rcases ih with ih | ih
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_self] at hm
        cases hm
        rw [KNode.add_leaf, hnl] at hml
        cases hml
      · rw [updN_ne _ _ _ _ hxL] at hm
        exact Or.inl (FReach.inner x b s m c y ih hm hml hc)
    · subst ih
      rw [updN_ne _ _ _ _ hvL, hv] at hm
      cases hm
  | seg x b s m c y _ hm hml hc ih =>
    rcases ih with ih | ih
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_self] at hm
        cases hm
        rcases KNode.add_key_liveAt_mem n t cv v hw ht c y hc with ⟨_, hy⟩ | ⟨_, hc'⟩
        · exact Or.inr hy
        · exact Or.inl (FReach.seg x b s n c y ih hL hnl hc')
      · rw [updN_ne _ _ _ _ hxL] at hm
        exact Or.inl (FReach.seg x b s m c y ih hm hml hc)
    · subst ih
      rw [updN_ne _ _ _ _ hvL, hv] at hm
      cases hm

/-- A key klong put into a leaf keeps `LiveCounts`. -/
theorem liveCounts_leafPut (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (n : KNode) (cv : Nat) (v : NodeId) (hL : N L = some n) (hnl : n.leaf = true)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hv : N v = none)
    (hvL : v ≠ L) (hC : LiveCounts p N t r) :
    LiveCounts p (updN N L (n.add t (.key cv v))) t r := by
  intro x b s m hx hm
  rcases fReach_updN_leafPut N t r L n cv v hL hnl hw ht hv hvL x b s hx with hx' | hx'
  · by_cases hxL : x = L
    · subst hxL
      rw [updN_self] at hm
      cases hm
      obtain ⟨_, _, h3⟩ := hC x b s n hx' hL
      have hself := KNode.add_key_liveAt_self n t cv v hw ht
      have hlen := KNode.add_key_liveAt_length n t cv v hw ht
      refine ⟨fun hE => ?_, fun hl => ?_, fun hm hb => ?_⟩
      · rw [hE] at hself; cases hself
      · rw [KNode.add_leaf, hnl] at hl; cases hl
      · have := h3 hm hb; omega
    · rw [updN_ne _ _ _ _ hxL] at hm
      exact hC x b s m hx' hm
  · subst hx'
    rw [updN_ne _ _ _ _ hvL, hv] at hm
    cases hm

/-! ## (1) A put into its leaf with room -/

/-- (1), `LiveCounts`. -/
theorem liveCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpCaseOK p R (QLive p) PutLeafRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have ht : ∀ q ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      (ctxOf p ts).p.fuel (pre ++ [cv]) w.top.rootKey, w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_room_after (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk
    w hrk ht (keyLeaf_all hK hrk (fun m => m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false) hroom)) ?_
  intro _ w' ⟨L', n', _, hn', hnl', _, h'top, hN'L, hN'⟩ _ hC
  rw [h'top]
  have hN'L2 : wNode p (viewOf (treeRun p ts)) w' L' =
      some (n'.add (ts.length + 1) (.key cv w.next)) := hN'L
  have hN'2 : ∀ x, x ≠ L' → wNode p (viewOf (treeRun p ts)) w' x =
      wNode p (viewOf (treeRun p ts)) w x := hN'
  have hfun : wNode p (viewOf (treeRun p ts)) w' =
      updN (wNode p (viewOf (treeRun p ts)) w) L' (n'.add (ts.length + 1) (.key cv w.next)) := by
    funext x
    by_cases hx : x = L'
    · subst hx; rw [hN'L2, updN_self]
    · rw [hN'2 x hx, updN_ne _ _ _ _ hx]
  rw [hfun]
  have hnone : wNode p (viewOf (treeRun p ts)) w w.next = none := hI.none_of_ge w.next (Nat.le_refl _)
  refine liveCounts_leafPut p _ _ _ L' n' cv w.next hn' hnl' (hI.wf L' n' hn') (hI.times L' n' hn')
    hnone (fun he => ?_) hC
  have hn'2 : wNode p (viewOf (treeRun p ts)) w L' = some n' := hn'
  rw [he, hn'2] at hnone
  cases hnone

/-! ## (3a) One new segment below a leaf with room -/

theorem fReach_reachS {N : NodeId → Option KNode} {t : Time} {r x : NodeId} {b s : Bool}
    (h : FReach N t r x b s) : ReachS N t r x := by
  induction h with
  | root => exact ReachS.root
  | inner x _ _ n c y _ hn _ hc ih => exact ReachS.step x n c y ih hn hc
  | seg x _ _ n c y _ hn _ hc ih => exact ReachS.step x n c y ih hn hc

/-- The tree reached after a leaf L gets a key klong to a new segment leaf v,
whose live pointees are no nodes: the tree before, v as a segment root, and
nodes that are none. -/
theorem fReach_leafNew (N : NodeId → Option KNode) (t : Time) (r L v : NodeId) (n m0 : KNode)
    (cv : Nat) (hL : N L = some n) (hnl : n.leaf = true) (hw : klongsWf n.ks = true)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hvL : v ≠ L) (hm0 : m0.leaf = true)
    (hm0c : ∀ c y, (c, y) ∈ m0.liveAt t → updN (updN N L (n.add t (.key cv v))) v m0 y = none) :
    ∀ x b s, FReach (updN (updN N L (n.add t (.key cv v))) v m0) t r x b s →
      FReach N t r x b s ∨ (x = v ∧ b = true) ∨
        updN (updN N L (n.add t (.key cv v))) v m0 x = none := by
  intro x b s h
  induction h with
  | root => exact Or.inl FReach.root
  | inner x b s m c y _ hm hml hc ih =>
    have hxv : x ≠ v := by
      intro he; subst he; rw [updN_self] at hm; cases hm; rw [hm0] at hml; cases hml
    have hxL : x ≠ L := by
      intro he; subst he; rw [updN_ne _ _ _ _ (Ne.symm hvL), updN_self] at hm; cases hm
      rw [KNode.add_leaf, hnl] at hml; cases hml
    have hmN : N x = some m := by rw [updN_ne _ _ _ _ hxv, updN_ne _ _ _ _ hxL] at hm; exact hm
    rcases ih with ih | ⟨ih, _⟩ | ih
    · exact Or.inl (FReach.inner x b s m c y ih hmN hml hc)
    · exact absurd ih hxv
    · rw [hm] at ih; cases ih
  | seg x b s m c y _ hm hml hc ih =>
    by_cases hxv : x = v
    · subst hxv
      rw [updN_self] at hm
      cases hm
      exact Or.inr (Or.inr (hm0c c y hc))
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_ne _ _ _ _ hxv, updN_self] at hm
        cases hm
        rcases ih with ih | ⟨ih, _⟩ | ih
        · rcases KNode.add_key_liveAt_mem n t cv v hw ht c y hc with ⟨_, hy⟩ | ⟨_, hc'⟩
          · exact Or.inr (Or.inl ⟨hy, rfl⟩)
          · exact Or.inl (FReach.seg x b s n c y ih hL hnl hc')
        · exact absurd ih hxv
        · rw [updN_ne _ _ _ _ hxv, updN_self] at ih; cases ih
      · have hmN : N x = some m := by rw [updN_ne _ _ _ _ hxv, updN_ne _ _ _ _ hxL] at hm; exact hm
        rcases ih with ih | ⟨ih, _⟩ | ih
        · exact Or.inl (FReach.seg x b s m c y ih hmN hml hc)
        · exact absurd ih hxv
        · rw [hm] at ih; cases ih

/-- A leaf L gets a key klong to a new segment leaf v with a live klong, whose
live pointees are no nodes: `LiveCounts` is kept. -/
theorem liveCounts_leafNew (p : Params) (N : NodeId → Option KNode) (t : Time) (r L v : NodeId)
    (n m0 : KNode) (cv : Nat) (hL : N L = some n) (hnl : n.leaf = true)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hvL : v ≠ L)
    (hm0 : m0.leaf = true) (hm0n : m0.liveAt t ≠ [])
    (hm0c : ∀ c y, (c, y) ∈ m0.liveAt t → updN (updN N L (n.add t (.key cv v))) v m0 y = none)
    (hvr : v ≠ r)
    (hfresh : ∀ u b s un c, FReach N t r u b s → N u = some un → (c, v) ∉ un.liveAt t)
    (hC : LiveCounts p N t r) :
    LiveCounts p (updN (updN N L (n.add t (.key cv v))) v m0) t r := by
  have hnv : ∀ b s, ¬ FReach N t r v b s := by
    intro b s h
    cases h with
    | root => exact hvr rfl
    | inner x b' _ un c _ hu hun _ hc => exact hfresh x b' _ un c hu hun hc
    | seg x b' _ un c _ hu hun _ hc => exact hfresh x b' _ un c hu hun hc
  intro x b s m hx hm
  rcases fReach_leafNew N t r L v n m0 cv hL hnl hw ht hvL hm0 hm0c x b s hx with hx' | ⟨hxv, hb⟩ | hx'
  · by_cases hxv : x = v
    · subst hxv; exact absurd hx' (hnv b s)
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_ne _ _ _ _ hxv, updN_self] at hm
        cases hm
        obtain ⟨_, _, h3⟩ := hC x b s n hx' hL
        have hself := KNode.add_key_liveAt_self n t cv v hw ht
        have hlen := KNode.add_key_liveAt_length n t cv v hw ht
        refine ⟨fun hE => ?_, fun hl => ?_, fun hm hb => ?_⟩
        · rw [hE] at hself; cases hself
        · rw [KNode.add_leaf, hnl] at hl; cases hl
        · have := h3 hm hb; omega
      · rw [updN_ne _ _ _ _ hxv, updN_ne _ _ _ _ hxL] at hm
        exact hC x b s m hx' hm
  · subst hxv hb
    rw [updN_self] at hm
    cases hm
    refine ⟨fun hE => absurd hE hm0n, fun hl => ?_, fun _ hb => ?_⟩
    · rw [hm0] at hl; cases hl
    · cases hb
  · rw [hm] at hx'; cases hx'

/-- (3a), `LiveCounts`. -/
theorem liveCase_putNewSeg1Room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QLive p) PutNewSeg1RoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, c0, cl, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  have ht : ∀ q ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      (ctxOf p ts).p.fuel (pre ++ [c0, cl]) w.top.rootKey, w.taken.contains q.1 = false :=
    fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_newSeg_after (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 cl
    h rk0 w hM hat.2.1 ht hI.ids.1 hI.ids.2.1 hI.ids.2.2.1
    (newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩)) ?_
  intro _ w' ⟨L', n', _, hn', hnl', _, h'top, hL', hy', hother⟩ _ hC
  rw [h'top]
  have hn'2 : wNode p (viewOf (treeRun p ts)) w L' = some n' := hn'
  have hL'2 : wNode p (viewOf (treeRun p ts)) w' L' =
      some (n'.add (ts.length + 1) (.key c0 w.next)) := hL'
  have hy'2 : wNode p (viewOf (treeRun p ts)) w' w.next =
      some ((⟨true, []⟩ : KNode).add (ts.length + 1) (.key cl (w.next + 2))) := hy'
  have hother2 : ∀ x, x ≠ L' → x ≠ w.next →
      wNode p (viewOf (treeRun p ts)) w' x = wNode p (viewOf (treeRun p ts)) w x := hother
  have hnone : ∀ z, w.next ≤ z → wNode p (viewOf (treeRun p ts)) w z = none :=
    fun z hz => hI.none_of_ge z hz
  have hvL : w.next ≠ L' := by
    intro he; have := hnone w.next (Nat.le_refl _); rw [he, hn'2] at this; cases this
  have hfun : wNode p (viewOf (treeRun p ts)) w' =
      updN (updN (wNode p (viewOf (treeRun p ts)) w) L' (n'.add (ts.length + 1) (.key c0 w.next)))
        w.next ((⟨true, []⟩ : KNode).add (ts.length + 1) (.key cl (w.next + 2))) := by
    funext x
    by_cases h1 : x = w.next
    · subst h1; rw [hy'2, updN_self]
    · by_cases h2 : x = L'
      · subst h2; rw [hL'2, updN_ne _ _ _ _ h1, updN_self]
      · rw [hother2 x h2 h1, updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2]
  rw [hfun]
  have hone : ∀ (c' : Nat) (z : NodeId), (c', z) ∈ ((⟨true, []⟩ : KNode).add (ts.length + 1)
      (.key cl (w.next + 2))).liveAt (ts.length + 1) → z = w.next + 2 := by
    intro c' z hm
    have he : (⟨true, []⟩ : KNode).add (ts.length + 1) (.key cl (w.next + 2)) =
        ⟨true, newKlongs (ts.length + 1) [(cl, w.next + 2)]⟩ := rfl
    rw [he] at hm
    have := liveAt_newKlongs_mem true (ts.length + 1) (ts.length + 1) _ c' z hm
    simp only [List.mem_singleton, Prod.mk.injEq] at this
    exact this.2
  have hrlt : w.top.rootKey < w.next := hI.ids.2.2.2.2
  refine liveCounts_leafNew p _ _ _ L' w.next n' _ c0 hn'2 hnl' (hI.wf L' n' hn'2)
    (hI.times L' n' hn'2) hvL rfl ?_ ?_ (by omega) ?_ hC
  · have h1 := KNode.add_key_liveAt_self (⟨true, []⟩ : KNode) (ts.length + 1) cl (w.next + 2) rfl
      (fun s hs => by cases hs)
    intro hE; rw [hE] at h1; cases h1
  · intro c' z hz
    rw [hone c' z hz, updN_ne _ _ _ _ (by omega)]
    have hz2 : w.next + 2 ≠ L' := by
      intro he; have := hnone (w.next + 2) (by omega); rw [he, hn'2] at this; cases this
    rw [updN_ne _ _ _ _ hz2]
    exact hnone _ (by omega)
  · intro u b s un c hu hun hc
    have := hI.links u un c w.next (fReach_reachS hu) hun hc
    omega

/-! ## (3b) New segments below a leaf with room -/

/-- `rangeOrder_leafAddNewSet` for `LiveCounts`: a leaf L gets a key klong to a
new node y; the new nodes are leaves with a live klong, named only by L and by
new nodes, and their live pointees are new or no nodes; the other nodes are
kept. -/
theorem liveCounts_leafAddNewSet (p : Params) (N N' : NodeId → Option KNode) (t : Time)
    (r L y : NodeId) (n : KNode) (cv : Nat) (New : NodeId → Prop) (hC : LiveCounts p N t r)
    (hn : N L = some n) (hnl : n.leaf = true) (hw : klongsWf n.ks = true)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hN'L : N' L = some (n.add t (.key cv y)))
    (hy : New y)
    (hnew : ∀ z, New z → N z = none ∧ z ≠ r ∧
      ∀ u b s un c, FReach N t r u b s → N u = some un → (c, z) ∉ un.liveAt t)
    (hNl : ∀ z m', New z → N' z = some m' → m'.leaf = true ∧ m'.liveAt t ≠ [])
    (hNk : ∀ z m' c z', New z → N' z = some m' → (c, z') ∈ m'.liveAt t → New z' ∨ N' z' = none)
    (hN' : ∀ z, z ≠ L → ¬ New z → N' z = N z) : LiveCounts p N' t r := by
  have hLnew : ¬ New L := fun h => by rw [(hnew L h).1] at hn; cases hn
  have htr : ∀ x b s, FReach N' t r x b s →
      (¬ New x ∧ FReach N t r x b s) ∨ (New x ∧ b = true) ∨ N' x = none := by
    intro x b s h
    induction h with
    | root => exact Or.inl ⟨fun h => (hnew r h).2.1 rfl, FReach.root⟩
    | inner x b s m c z _ hm hml hc ih =>
      rcases ih with ⟨hxn, ih⟩ | ⟨hxn, _⟩ | ih
      · have hxL : x ≠ L := by
          intro he; subst he; rw [hN'L] at hm; cases hm; rw [KNode.add_leaf, hnl] at hml; cases hml
        have hmN : N x = some m := by rw [← hN' x hxL hxn]; exact hm
        have hzn : ¬ New z := fun h => (hnew z h).2.2 x b s m c ih hmN hc
        exact Or.inl ⟨hzn, FReach.inner x b s m c z ih hmN hml hc⟩
      · rw [(hNl x m hxn hm).1] at hml; cases hml
      · rw [hm] at ih; cases ih
    | seg x b s m c z _ hm hml hc ih =>
      rcases ih with ⟨hxn, ih⟩ | ⟨hxn, _⟩ | ih
      · by_cases hxL : x = L
        · subst hxL
          rw [hN'L] at hm
          cases hm
          rcases KNode.add_key_liveAt_mem n t cv y hw ht c z hc with ⟨_, hz⟩ | ⟨_, hc'⟩
          · subst hz; exact Or.inr (Or.inl ⟨hy, rfl⟩)
          · have hzn : ¬ New z := fun h => (hnew z h).2.2 x b s n c ih hn hc'
            exact Or.inl ⟨hzn, FReach.seg x b s n c z ih hn hnl hc'⟩
        · have hmN : N x = some m := by rw [← hN' x hxL hxn]; exact hm
          have hzn : ¬ New z := fun h => (hnew z h).2.2 x b s m c ih hmN hc
          exact Or.inl ⟨hzn, FReach.seg x b s m c z ih hmN hml hc⟩
      · rcases hNk x m c z hxn hm hc with hz | hz
        · exact Or.inr (Or.inl ⟨hz, rfl⟩)
        · exact Or.inr (Or.inr hz)
      · rw [hm] at ih; cases ih
  intro x b s m hx hm
  rcases htr x b s hx with ⟨hxn, hx'⟩ | ⟨hxn, hb⟩ | hx'
  · by_cases hxL : x = L
    · subst hxL
      rw [hN'L] at hm
      cases hm
      obtain ⟨_, _, h3⟩ := hC x b s n hx' hn
      have hself := KNode.add_key_liveAt_self n t cv y hw ht
      have hlen := KNode.add_key_liveAt_length n t cv y hw ht
      refine ⟨fun hE => ?_, fun hl => ?_, fun hm hb => ?_⟩
      · rw [hE] at hself; cases hself
      · rw [KNode.add_leaf, hnl] at hl; cases hl
      · have := h3 hm hb; omega
    · have hmN : N x = some m := by rw [← hN' x hxL hxn]; exact hm
      exact hC x b s m hx' hmN
  · obtain ⟨hml, hmne⟩ := hNl x m hxn hm
    subst hb
    refine ⟨fun hE => absurd hE hmne, fun hl => ?_, fun _ hb => ?_⟩
    · rw [hml] at hl; cases hl
    · cases hb
  · rw [hm] at hx'; cases hx'

/-- `writerWP_putSegs_new_shape` with the new nodes' live klongs: putSegs down a
new segment leaf x leaves x and every node from the next id on with a live
klong. -/
theorem writerWP_putSegs_new_live (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
        wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
        (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
        (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
        ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
          m.liveAt c.i ≠ []) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  have hne1 : ∀ (a : Nat) (y : NodeId), ((⟨true, []⟩ : KNode).add c.i (.key a y)).liveAt c.i ≠ [] := by
    intro a y hE
    have h1 := KNode.add_key_liveAt_self (⟨true, []⟩ : KNode) c.i a y rfl (fun s hs => by cases hs)
    rw [hE] at h1; cases h1
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr
    cases tail' with
    | nil =>
      rw [putSegs.eq_2]
      refine writerWP_mono (post := fun _ wf => wf.nodes = upsert ws.nodes x
          ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) ∧ wf.vals = ws.vals ++ [(ws.next, h)] ∧
          wf.taken = ws.taken ∧ wf.top = ws.top ∧ wf.next = ws.next + 2) ?_ ?_
      · unfold setValue
        simp only [writerWP_bind, writerWP_read]
        rw [hf2]
        unfold descendLte
        simp only [writerWP_bind, writerWP_read]
        rw [writerWP_getNode_known _ _ c ws hx]
        simp only [↓reduceIte, writerWP_pure]
        unfold newValue fresh
        simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
        rw [writerWP_getNode_known _ _ c _ (by simpa using hx)]
        have hcond : (decide ((⟨true, []⟩ : KNode).size + 1 < c.p.M) &&
            !deadOver c.p ((⟨true, []⟩ : KNode).add c.i (.key a ws.next))) = true := by
          simp only [KNode.size, List.length_nil, deadOver_empty_add]
          simp; omega
        simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        all_goals (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
      · intro _ wf ⟨g1, _, g3, g4, g5⟩
        refine ⟨g3, g4, by omega, ?_, ?_, ?_⟩
        · intro z _ hzx; rw [g1, lookup_upsert]; simp [hzx]
        · intro z hz
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          exact (hfr z (by omega)).1
        · intro z m hz hm
          rw [g1, lookup_upsert] at hm
          by_cases hzx : z = x
          · simp only [hzx, ↓reduceIte, Option.some.injEq] at hm
            subst hm
            exact hne1 a ws.next
          · simp only [hzx, ↓reduceIte] at hm
            rcases hz with hz | hz
            · exact absurd hz hzx
            · rw [(hfr z hz).1] at hm; cases hm
    | cons a' tail'' =>
      have hv := hfr ws.next (Nat.le_refl _)
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf =>
            wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
            (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
            (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
            ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
              m.liveAt c.i ≠ []) := by
        intro ws1 g1 g2 g3 g4 g5
        have hch : ws1.nodes.lookup ws.next = some ⟨true, []⟩ := by
          rw [g1, lookup_upsert]
          simp only [show ws.next ≠ x by omega, ↓reduceIte]
          exact lookup_append_single_self _ _ _ hv.1
        refine writerWP_mono (ih (by simp) ws1 ws.next hch (by rw [g3]; exact hv.2.1) (by omega) ?_) ?_
        · intro z hz
          rw [g2] at hz
          have hz' := hfr z (by omega)
          refine ⟨?_, by rw [g3]; exact hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, by rw [g4]; exact hz'.2.2.2.2⟩
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          rw [lookup_append_single_ne _ _ _ _ (by omega)]; exact hz'.1
        · rintro _ wf ⟨k1, k2, k3, k4, k6, k7⟩
          have hxf : wf.nodes.lookup x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
            rw [k4 x (by omega) (by omega), g1, lookup_upsert]; simp
          refine ⟨by rw [k1, g3], by rw [k2, g5], by omega, ?_, k6, ?_⟩
          · intro z hz hzx
            rw [k4 z (by omega) (by omega), g1, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact lookup_append_single_ne _ _ _ _ (by omega)
          · intro z m hz hm
            by_cases hzx : z = x
            · rw [hzx, hxf] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              exact hne1 a ws.next
            · have hz2 : ws.next ≤ z := by rcases hz with hz | hz; exact absurd hz hzx; exact hz
              by_cases hz0 : z = ws.next
              · exact k7 z m (Or.inl hz0) hm
              · by_cases hz1 : z < ws.next + 2
                · rw [k4 z (by omega) hz0, g1, lookup_upsert] at hm
                  simp only [hzx, ↓reduceIte] at hm
                  rw [lookup_append_single_ne _ _ _ _ hz0, (hfr z hz2).1] at hm
                  cases hm
                · exact k7 z m (Or.inr (by omega)) hm
      rw [putSegs.eq_3 _ _ x a (a' :: tail'') (by simp)]
      unfold setNode
      simp only [writerWP_bind, writerWP_read]
      rw [hf2]
      unfold descendLte
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c ws hx]
      simp only [↓reduceIte, writerWP_pure]
      rw [writerWP_getNode_known _ _ c ws hx]
      have hse : ((⟨true, []⟩ : KNode).searchEq c.i a) = none := rfl
      simp only [hse, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      refine writerWP_ghOf_cached x _ c ws hx _ (fun gh => ?_)
      have hroom : (⟨true, []⟩ : KNode).size + 1 < c.p.M := by simp [KNode.size]; omega
      simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        exact hstep _ rfl rfl rfl rfl rfl

set_option maxHeartbeats 800000 in
/-- `rangeOrder_put_newSegs` for `LiveCounts`: a put of a key pre ++ c0 :: tail
whose leaf for c0 in the tree of pre has no klong of c0 and has room keeps
`LiveCounts`. -/
theorem liveCounts_put_newSegs (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ n.searchEq c.i c0 = none ∧
      n.size + 1 < c.p.M ∧
      (∀ key', keyWf key' = true →
        (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next)
    (hC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      LiveCounts c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have _ := hidr
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ c0 :: tail) (some h) (c0 :: tail) (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 tail htail]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht1)
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht1)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnwf, hnt, hnone, hroom, _, _⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  -- ids
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hLt : w.taken.contains L = false := ht (L, c0) (hvk _ hvisL)
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.vals = w3.vals → ws.top = w3.top →
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        LiveCounts c.p (wNode c.p base w') c.i w'.top.rootKey) := by
    intro ws h1 h2 h3 h4 h5
    rw [hnext3] at h1 h2
    rw [hnext3]
    have hw3n : w3.nodes.lookup w.next = none := by
      cases h' : w3.nodes.lookup w.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have hLne : L ≠ w.next := by omega
    have hlkc : ws.nodes.lookup w.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w.next ≠ L by omega, ↓reduceIte]
      exact lookup_append_single_self _ _ _ hw3n
    have htk : ∀ z, ws.taken.contains z = w.taken.contains z := by intro z; rw [h3, hr03.2.2.1]
    have hfrW : ∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none := by
      intro z hz
      rw [h2] at hz
      refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hbase z (by omega)).1,
        (hbase z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
      rw [h1, lookup_upsert]
      simp only [show z ≠ L by omega, ↓reduceIte]
      rw [lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_and (writerWP_putSegs_new_shape c base (pre ++ c0 :: tail) h hM
      hfuel tail htail ws w.next hlkc (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) hfrW)
      (writerWP_putSegs_new_live c base (pre ++ c0 :: tail) h hM hfuel tail htail ws w.next hlkc
        (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) hfrW)) ?_
    rintro _ wf ⟨⟨k1, k2, k3, k4, k6, k7⟩, ⟨_, _, _, k4', _, k8⟩⟩
    have _ := k4'
    have htkf : ∀ z, wf.taken.contains z = w.taken.contains z := by intro z; rw [k1, htk]
    have hLf : wf.nodes.lookup L = some (n.add c.i (.key c0 w.next)) := by
      rw [k4 L (by omega) hLne, h1, lookup_upsert]; simp
    have hnewshape : ∀ z m, w.next ≤ z → wf.nodes.lookup z = some m →
        m.leaf = true ∧ ∀ c' y, (c', y) ∈ m.liveAt c.i → w.next ≤ y := by
      intro z m hz hm
      by_cases hz0 : z = w.next
      · obtain ⟨h1', h2'⟩ := k7 z m (Or.inl hz0) hm
        exact ⟨h1', fun c' y hy => by have := h2' c' y hy; omega⟩
      · by_cases hz1 : z < w.next + 2
        · rw [k4 z (by omega) hz0, h1, lookup_upsert] at hm
          simp only [show z ≠ L by omega, ↓reduceIte] at hm
          rw [lookup_append_single_ne _ _ _ _ hz0] at hm
          cases h' : w3.nodes.lookup z with
          | none => rw [h'] at hm; cases hm
          | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
        · obtain ⟨h1', h2'⟩ := k7 z m (Or.inr (by omega)) hm
          exact ⟨h1', fun c' y hy => by have := h2' c' y hy; omega⟩
    have hwfz : ∀ z, w.next ≤ z → ∀ m, wNode c.p base wf z = some m → wf.nodes.lookup z = some m := by
      intro z hz m hm
      unfold wNode at hm
      rw [htkf, hntake z hz] at hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hm
      cases h' : wf.nodes.lookup z with
      | some m' => rw [h'] at hm; exact hm
      | none => rw [h'] at hm; simp only at hm; rw [(hbase z hz).1] at hm; cases hm
    have hnewlive : ∀ z m, w.next ≤ z → wf.nodes.lookup z = some m → m.liveAt c.i ≠ [] := by
      intro z m hz hm
      by_cases hz0 : z = w.next
      · exact k8 z m (Or.inl hz0) hm
      · by_cases hz1 : z < w.next + 2
        · rw [k4 z (by omega) hz0, h1, lookup_upsert] at hm
          simp only [show z ≠ L by omega, ↓reduceIte] at hm
          rw [lookup_append_single_ne _ _ _ _ hz0] at hm
          cases h' : w3.nodes.lookup z with
          | none => rw [h'] at hm; cases hm
          | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
        · exact k8 z m (Or.inr (by omega)) hm
    rw [k2, h5, hr03.2.1]
    refine liveCounts_leafAddNewSet c.p (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey L
      w.next n c0 (fun z => w.next ≤ z) hC hn hnl hnwf hnt
      (by simp only [wNode, htkf, hLt, Bool.false_eq_true, ↓reduceIte, hLf]) (Nat.le_refl _) ?_ ?_ ?_ ?_
    · intro z hz
      refine ⟨?_, by omega, ?_⟩
      · simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, (hbase z hz).1]
        cases h' : w.nodes.lookup z with
        | none => rfl
        | some _ => have := hidn z (by rw [h']; rfl); omega
      · intro u b s un c' hu hun hc
        have := hlinks u un c' z (fReach_reachS hu) hun hc
        omega
    · intro z m' hz hm
      have hm' := hwfz z hz m' hm
      exact ⟨(hnewshape z m' hz hm').1, hnewlive z m' hz hm'⟩
    · intro z m' c' z' hz hm hc
      exact Or.inl ((hnewshape z m' hz (hwfz z hz m' hm)).2 c' z' hc)
    · intro z hzL hzb
      have hzb' : z < w.next := by simpa using hzb
      rw [← hr03.1]
      have hx := k4 z (by omega) (by omega)
      rw [h1, lookup_upsert] at hx
      simp only [hzL, ↓reduceIte] at hx
      rw [lookup_append_single_ne _ _ _ _ (by omega)] at hx
      simp only [wNode, htkf, hr03.2.2.1, hx]
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl

/-- (3b), `LiveCounts`. -/
theorem liveCase_putNewSegsRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QLive p) PutNewSegsRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, c0, tail, h, rk0, L, n, hop, _, hat, hroom⟩ := hP
  subst hop
  obtain ⟨hkeys, hnotpre⟩ := newSeg_leaf_keys hI pre c0 rk0 L hat.2.1 hat.2.2.1
  intro a w' hrun _ hC
  exact liveCounts_put_newSegs (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 h tail hat.1 rk0 w hM
    hat.2.1 (hI.pathUntaken _) hI.ids hI.fresh
    (newSegAt_one hat (fun L' m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M ∧
      (∀ key', keyWf key' = true →
        (L', c0) ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
          (ctxOf p ts).p.fuel key' w.top.rootKey → ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L', c') ∉ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
        (ctxOf p ts).p.fuel pre w.top.rootKey)
      ⟨hI.wf L n hat.2.2.2.1, hI.times L n hat.2.2.2.1, hat.2.2.2.2.2, hroom, hkeys, hnotpre⟩)
    hI.links hC a w' hrun

end SIS.Tree
