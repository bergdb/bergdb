/-
The writer's merge keeps the writer's tree (bergdb 024-22, `OpTreeOK`;
024-11, M1 to M5): `merge x d` with a parent that has room and no compaction,
of two nodes that the transaction did not make (`writerWP_merge_tree`).
-/
import SIS.Tree.WriterTreeMergeW

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge after its two nodes are chosen: the code of `merge` from its note
of the side on. -/
def mergeTail (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode) (leftSome : Bool)
    (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat) : M Nat := do
  let tt := c.i
  let inner := !xn.leaf
  note (if leftSome then "merge.left" else "merge.right")
  let cL ← match pn.cv? il with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {il} in {p}"
  let cR ← match pn.cv? ir with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {ir} in {p}"
  let lvL := ln.live
  let lvR := rn.live
  if lvL.isEmpty || lvR.isEmpty then
    throw s!"Bug: merge at {tt}: key node {l} or {r} has no live klong"
  if inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0) then
    throw s!"Bug: merge at {tt}: inner node {l} or {r} has no live klong of the empty key first"
  let (first, second) := mergeKlongs inner c.p.mergeMax cR lvL lvR
  modify (fun w => { w with merges := w.merges + 1 })
  note (if second.isSome then "merge.two" else "merge.one")
  note (if inner then "merge.inner" else "merge.leaf")
  let (g, h) ← ghOf x
  let lMade := ln.firstTime == some tt
  let rMade := rn.firstTime == some tt
  if lMade then note "merge.made.left"
  if rMade then note "merge.made.right"
  let m1 ← newKey g h (!inner) (newKlongs tt first)
  setMadeFor m1 (← if lMade then replacedBy l else pure (some l))
  let m2 ← match second with
    | some (ks2, g2) => do
      let y ← newKey g h (!inner) (newKlongs tt ks2)
      setMadeFor y (← if rMade then replacedBy r else pure (some r))
      pure (some (y, g2))
    | none => pure none
  mergeParent p (d - 1) il cL m1 ir cR m2
  for (o, made) in [(l, lMade), (r, rMade)] do
    if made then
      retarget p o m1
      takenBack o
      note "merge.takeback"
    else unlink o
  pure (if second.isSome then 2 else 1)

theorem writerWP_ghOf_frame (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_frame x c w) ?_
  intro _ w1 h1
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact h1
  · exact writerWP_throw _ _ _ _

theorem KNode.repoint_times (n : KNode) (i : Nat) (y : NodeId) (t : Time)
    (h : ∀ s, Klong.time s ∈ n.ks → s ≤ t) : ∀ s, Klong.time s ∈ (n.repoint i y).ks → s ≤ t := by
  intro s hs
  unfold KNode.repoint at hs
  split at hs
  · simp only [KNode.setAt] at hs
    rcases List.mem_or_eq_of_mem_set hs with h1 | h1
    · exact h s h1
    · cases h1
  · exact h s hs

theorem mpNode_times (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool)
    (htdh : htd = true → ∃ old, pn.ks.getLast? = some (.del old))
    (h : ∀ s, Klong.time s ∈ pn.ks → s ≤ tt) :
    ∀ s, Klong.time s ∈ (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks → s ≤ tt := by
  have hn1 : ∀ (b : Bool) (U : List Nat), ∀ s, Klong.time s ∈ (if !b then pn else if htd then
      pn.setAt (pn.size - 1) (.del U) else pn.add tt (.del U)).ks → s ≤ tt := by
    intro b U
    have hA : ∀ s, Klong.time s ∈ (if htd then pn.setAt (pn.size - 1) (.del U)
        else pn.add tt (.del U)).ks → s ≤ tt := by
      cases htd with
      | true => obtain ⟨old, hl⟩ := htdh rfl; exact KNode.setAt_last_del_times pn tt old U hl h
      | false => exact KNode.add_times pn tt _ (fun s h => by cases h) h
    cases b with
    | false => exact h
    | true => exact hA
  have hn2 : ∀ n1 : KNode, (∀ s, Klong.time s ∈ n1.ks → s ≤ tt) →
      ∀ s, Klong.time s ∈ (if lip then n1.repoint il m1 else n1.add tt (.key cL m1)).ks → s ≤ tt := by
    intro n1 h1
    cases lip with
    | true => simp only [↓reduceIte]; exact KNode.repoint_times n1 il m1 tt h1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_times n1 tt _ (fun s h => by cases h) h1
  unfold mpNode
  cases m2 with
  | none => exact hn2 _ (hn1 _ _)
  | some yg =>
    obtain ⟨y, g⟩ := yg
    simp only
    cases rip with
    | true => simp only [↓reduceIte]; exact KNode.repoint_times _ ir y tt (hn2 _ (hn1 _ _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_times _ tt _ (fun s h => by cases h) (hn2 _ (hn1 _ _))

theorem htd_last (pn : KNode) (b : Bool)
    (h : ((match pn.ks.getLast? with
      | some (.del _) => true
      | _ => false) && b) = true) : ∃ old, pn.ks.getLast? = some (.del old) := by
  cases hg : pn.ks.getLast? with
  | none => rw [hg] at h; simp at h
  | some k =>
    cases k with
    | del old => exact ⟨old, rfl⟩
    | time t => rw [hg] at h; simp at h
    | key a y => rw [hg] at h; simp at h

theorem wNode_congr (p : Params) (base : View BVal) (v w : W) (y : NodeId)
    (ht : v.taken = w.taken) (hl : v.nodes.lookup y = w.nodes.lookup y) :
    wNode p base v y = wNode p base w y := by
  simp only [wNode, ht, hl]

/-- The merge's last loop when it made neither node, in the form its code
takes: each node is unlinked, nothing else changes but their lookups. -/
theorem writerWP_mergeCleanup_unmade' (A : NodeId × Bool → M (ForInStep PUnit)) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, q.2 = false) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then A q else do
      unlink q.1
      pure (ForInStep.yield PUnit.unit))) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ ∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) := by
  intro xs
  induction xs with
  | nil =>
    intro w _
    simp only [List.forIn_nil, writerWP_pure]
    refine ⟨?_, ?_, ?_, fun _ _ => ?_⟩ <;> first | rfl | trivial
  | cons q qs ih =>
    intro w hq
    rw [List.forIn_cons]
    have hq0 : q.2 = false := hq q List.mem_cons_self
    simp only [writerWP_bind, hq0, Bool.false_eq_true, ↓reduceIte]
    refine writerWP_mono (writerWP_unlink_frame q.1 c w) ?_
    intro _ w1 ⟨h1t, h1top, h1n, h1l⟩
    simp only [writerWP_pure]
    refine writerWP_mono (ih w1 (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))) ?_
    intro _ w2 ⟨h2t, h2top, h2n, h2l⟩
    refine ⟨h2t.trans h1t, h2top.trans h1top, h2n.trans h1n, fun y hy => ?_⟩
    rw [h2l y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
      h1l y (hy q List.mem_cons_self)]

theorem lookup_of_prefix (l1 l2 : List (NodeId × KNode)) (h : l1 <+: l2) (y : NodeId) (v : KNode)
    (hv : l1.lookup y = some v) : l2.lookup y = some v := by
  obtain ⟨t, rfl⟩ := h
  rw [List.lookup_append, hv]; rfl

/-- `getNode` reads: the node's lookup after, the reading unchanged, the
writer's nodes extended by nodes of P@(i - 1) at most. -/
theorem writerWP_getNode_all (x : NodeId) (c : Ctx) (w : W) (base : View BVal)
    (hvc : ViewCoherent c base) :
    WriterWP (getNode x) c w (fun n v => ReadsAs c.p base w v ∧ v.nodes.lookup x = some n ∧
      (w.taken.contains x = false → wNode c.p base w x = some n) ∧ w.nodes <+: v.nodes ∧
      (∀ z, (v.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true)) := by
  refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c w base hvc)
    (writerWP_getNode_cache2 x c w)) ?_
  intro n v ⟨⟨h1, h2, h3⟩, h4, h5⟩
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `sibling` reads the node that klong i of p names. -/
theorem writerWP_sibling_all (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (base : View BVal) (hvc : ViewCoherent c base) :
    WriterWP (sibling p pn i inner) c w (fun sn v => pn.ptr? i = some sn.1 ∧
      ReadsAs c.p base w v ∧ v.nodes.lookup sn.1 = some sn.2 ∧
      (w.taken.contains sn.1 = false → wNode c.p base w sn.1 = some sn.2) ∧ w.nodes <+: v.nodes ∧
      (∀ z, (v.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true)) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_all s c w base hvc) ?_
    intro sn v ⟨h1, h2, h3, h4, h5⟩
    split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_pure]
      exact ⟨hs, h1, h2, h3, h4, h5⟩

/-- The merge's tail keeps the writer's tree: two siblings l and r under a
reached parent p with room, which the transaction did not make, merged. -/
theorem writerWP_mergeTail_tree (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  obtain ⟨hlm, hlt⟩ := hch cL l ln hpL hln
  obtain ⟨hrm, hrt⟩ := hch cR r rn hpR hrn
  have hlm' : (ln.firstTime == some c.i) = false := by simpa using hlm
  have hrm' : (rn.firstTime == some c.i) = false := by simpa using hrm
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  unfold mergeTail
  simp only [hlm', hrm', hcvL, hcvR, Bool.false_eq_true, ↓reduceIte]
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_ghOf_frame x c _) ?_
  intro gh w4 ⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩
  simp only [writerWP_pure]
  refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
  intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
  refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
  intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
  -- the ids
  have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
  subst hm1
  have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hw6p : w6.nodes.lookup p = some pn := by
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
  have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
    rw [h6n, h5n, lookup_append_single_self]
    rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
    exact hnone3 m1 (Nat.le_refl _)
  have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
  have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
    intro y hyx hym
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
  have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hhtd := htd_last pn
  -- the parent after
  have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
      ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
      (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
    intro m2 cc z hm
    rw [KNode.liveAt_of_times _ c.i (by
      rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
  have hlm1 : l ≠ m1 := by omega
  have hrm1 : r ≠ m1 := by omega
  have hpm1 : p ≠ m1 := by omega
  have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
  rw [hw4m1] at hw6m1
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
  have hcl : ∀ y, (∀ q ∈ [(l, false), (r, false)], y ≠ (q : NodeId × Bool).1) ↔ (y ≠ l ∧ y ≠ r) := by
    intro y; simp
  have hoBool : ∀ q ∈ [(l, false), (r, false)], (q : NodeId × Bool).2 = false := by simp
  have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
    intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpL' : (cL, l) ∈ pn.liveAt c.i := hpL
  cases hsec : second with
  | none =>
    rw [hsec] at hmkd
    have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
      (hdead _ _ _ _ _ _)) ?_
    intro _ w7 ⟨h7n, h7t, h7top, _, _, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmade' _ c [(l, false), (r, false)] w7 hoBool) ?_
    intro _ w8 ⟨h8t, h8top, _, h8l⟩
    try simp only [writerWP_pure]
    have h8t' : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
    have h8l' : ∀ y, y ≠ l → y ≠ r → w8.nodes.lookup y =
        (upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none)).lookup y := by
      intro y hyl hyr; rw [h8l y ((hcl y).mpr ⟨hyl, hyr⟩), h7n]
    rw [h8top, h7top, h6top']
    apply treeOK_mergeOneAfter N (wNode c.p base w8) c.i root p l r m1 pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR none) ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
      hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
    · simp only [wNode, h8t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte, hw6m1]
    · intro cc z hm
      have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
      rw [hfirst] at this; exact this
    · simp only [wNode, h8t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' p hpl hpr, lookup_upsert]
      simp
    · intro cc z hm
      have hlk := hpliveAt none cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      simp only at hlk
      by_cases h1 : cc = cL
      · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inl ⟨h1, hlk.symm⟩
      · by_cases h2 : cc = cR
        · simp [h2, Ne.symm hc] at hlk
        · simp only [h1, h2, ↓reduceIte] at hlk
          right
          refine ⟨?_, h1, h2⟩
          rw [KNode.liveAt_of_times pn c.i hpt]
          exact mem_of_lookup_nodup _ cc z hlk
    · intro y hyp hyl hyr hym
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h8t'
      rw [h8l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      exact h6old y (hyx y hyl hyr) hym
  | some ksg =>
    obtain ⟨ks2, g2⟩ := ksg
    rw [hsec] at hmkd
    have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
      rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
    intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, _, _, _⟩
    have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
    subst hm2'
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c w7) ?_
    intro _ w8 ⟨h8n, h8t, h8top, _, _, _⟩
    try simp only [writerWP_pure]
    have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
        hlk4 _ (by omega)]
      exact hnone3 _ (by omega)
    have hw8p : w8.nodes.lookup p = some pn := by
      rw [h8n, h7n, h6next, h5next, hw4m1, lookup_append_single_ne _ _ _ _ (by omega)]
      exact hw6p
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
      w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
    intro _ w9 ⟨h9n, h9t, h9top, _, _, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmade' _ c [(l, false), (r, false)] w9 hoBool) ?_
    intro _ w10 ⟨h10t, h10top, _, h10l⟩
    try simp only [writerWP_pure]
    have h10t' : w10.taken = w3.taken := by rw [h10t, h9t, h8t, h7t, h6taken]
    have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
        ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
      intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
    have h10l' : ∀ y, y ≠ l → y ≠ r → w10.nodes.lookup y =
        (upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))).lookup y := by
      intro y hyl hyr; rw [h10l y ((hcl y).mpr ⟨hyl, hyr⟩), h9n]
    have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
    rw [h10top, h9top, h8top, h7top, h6top']
    apply treeOK_mergeTwoAfter N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) ⟨!!xn.leaf, newKlongs c.i first⟩
      ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
      hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
      (hfree _ (by omega)).1 (hfreshT _ (by omega)) (by omega) hE
    · simp only [wNode, h10t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
    · intro cc z hm
      exact liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
    · simp only [wNode, h10t', hm2T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' _ (by omega) (by omega), lookup_upsert]
      simp only [show m1 + 2 ≠ p by omega, ↓reduceIte]
      rw [h8l, lookup_append_single_self _ _ _ hw6m2]
    · intro cc z hm
      exact liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm
    · simp only [wNode, h10t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' p hpl hpr, lookup_upsert]
      simp
    · intro cc z hm
      have hlk := hpliveAt (some (m1 + 2, g2)) cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m1 + 2, g2)) _ _ _ l r
        hpwf hL hLL hR hRL hc ?htd ?hrip cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      case hrip =>
        intro h y g heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simp at h
        exact h.1.1
      simp only at hlk
      by_cases h0 : cc = g2
      · simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inr (Or.inl ⟨h0, hlk.symm⟩)
      · by_cases h1 : cc = cL
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨rfl, hlk.symm⟩
        · by_cases h2 : cc = cR
          · subst h2
            simp [h0, h1] at hlk
          · simp only [h0, h1, h2, ↓reduceIte] at hlk
            right; right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact mem_of_lookup_nodup _ cc z hlk
    · intro y hyp hyl hyr hym hym2
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h10t'
      rw [h10l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
      exact h6old y (hyx y hyl hyr) hym

theorem writerWP_merge_tree (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (merge x d) c w (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL ≠ cR →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR hRL hc hxlr hln hrn
      apply writerWP_mergeTail_tree c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR (hwn1 (hRt _ hpR)) hL hLL hR hRL hc hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
      · intro z hz
        exact ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩
      · exact hfreshT
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hsrcb hLa hax
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_all e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, _, hwn4, hpre4, hsrc4⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            (by omega) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_all e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, _, hwn3, hpre3, hsrc3⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              (by omega) (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 hLa hax
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hLa hax
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
