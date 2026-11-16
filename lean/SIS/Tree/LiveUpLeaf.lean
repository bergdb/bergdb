/-
The upward delete, for `l4` (bergdb 030-01, step 6): a delete that empties its
leaf.

* The leaf is the space root (`up.root-kept-empty`) and has room: after its
  bitmap the root is an empty leaf and reaches nothing, so the live counts hold
  (`liveDel_emptyRootRoom`).
* The emptied chain's frame (030-01's stall point R2, the live part): after the
  chain below the stop node is taken back or unlinked and the stop node's klong
  to it deleted, the tree is the start's without the chain, and the live counts
  hold but at the stop node, which keeps a live klong (`liveEdgesH_up`; the
  tree's mirror is `tReach_up_sub_tr`, WriterGetUpAll.lean).
-/
import SIS.Tree.LiveUpWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The emptied chain's frame -/

/-- The emptied chain's frame (030-01, R2): from `LiveEdges` at the start, after
the chain X (s + 1) .. X D below the stop node X s leaves the tree (N' agrees
with N off the chain and the stop node) and the stop node keeps its other live
klongs but the chain's, and at least one, the live counts hold but at the stop
node. -/
theorem liveEdgesH_up (p : Params) (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (hsl : sn'.leaf = (Nn s).leaf)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1))
    (hpos : sn'.liveAt t ≠ []) (h : LiveEdges p N t r) :
    LiveEdgesH p N' t r (fun y => y = X s) := by
  have hR := tReach_up_sub_tr N N' t r X Nn K s D hsD hT hXs hN hlinkK hdist hagree sn' hsn'
    (fun c z hz => ⟨c, (hlive' c z hz).1, (hlive' c z hz).2⟩)
  -- the chain's nodes are reached at N, each through its own link
  have hreach : ∀ k, s + k ≤ D → TReach N t r (X (s + k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hXs
    | succ k ih =>
      intro hk
      have hl := hlinkK (s + (k + 1)) (by omega) hk
      rw [show s + (k + 1) - 1 = s + k by omega] at hl
      exact TReach.link (ih (by omega)) ⟨Nn (s + k), hN (s + k) (by omega) (by omega), hl⟩
  have hXi : ∀ i, s ≤ i → i ≤ D → TReach N t r (X i) := by
    intro i h1 h2
    have := hreach (i - s) (by omega)
    rwa [show s + (i - s) = i by omega] at this
  -- a link of a reached node at N into the chain is the chain's own link
  have hinto : ∀ u c k, TReach N t r u → TLink N t u c (X k) → s < k → k ≤ D →
      u = X (k - 1) ∧ c = K k := by
    intro u c k hu hl h1 h2
    have hlk : TLink N t (X (k - 1)) (K k) (X k) :=
      ⟨Nn (k - 1), hN (k - 1) (by omega) (by omega), hlinkK k h1 h2⟩
    exact hT.oneLink u c (X (k - 1)) (K k) (X k) hu (hXi (k - 1) (by omega) (by omega)) hl hlk
  have hXsN : N (X s) = some (Nn s) := hN s (Nat.le_refl _) (by omega)
  refine ⟨fun rn hrn => ⟨fun hE => ?_, fun hnr hl => ?_⟩,
    fun u un c y yn hu hun hc hyn => ⟨fun hyS => ?_, fun hyS => ?_⟩⟩
  · by_cases hr : r = X s
    · rw [hr, hsn'] at hrn
      cases hrn
      exact absurd hE hpos
    · have hrc : ∀ i, s < i → i ≤ D → r ≠ X i := (hR r TReach.root).2
      rw [hagree r hr hrc] at hrn
      exact (h.1 rn hrn).1 hE
  · have hrc : ∀ i, s < i → i ≤ D → r ≠ X i := (hR r TReach.root).2
    rw [hagree r hnr hrc] at hrn
    exact (h.1 rn hrn).2 hl
  · -- a link to a node other than the stop node: off the chain, as at N
    obtain ⟨huN, huc⟩ := hR u hu
    by_cases huS : u = X s
    · rw [huS, hsn'] at hun
      cases hun
      obtain ⟨hc0, hcK⟩ := hlive' c y hc
      have hyc : ∀ i, s < i → i ≤ D → y ≠ X i := by
        intro i h1 h2 hy
        rw [hy] at hc0
        obtain ⟨e1, e2⟩ := hinto (X s) c i hXs ⟨Nn s, hXsN, hc0⟩ h1 h2
        have := hdist s (i - 1) (Nat.le_refl _) (by omega) (by omega) (by omega) e1
        rw [show i = s + 1 by omega] at e2
        exact hcK e2
      rw [hagree y hyS hyc] at hyn
      exact childOK_grow p t (Nn s) sn' yn yn (h.2 (X s) (Nn s) c y yn hXs hXsN hc0 hyn) hsl rfl
        (Nat.le_refl _)
    · rw [hagree u huS huc] at hun
      have hyc : ∀ i, s < i → i ≤ D → y ≠ X i := by
        intro i h1 h2 hy
        rw [hy] at hc
        obtain ⟨e1, _⟩ := hinto u c i huN ⟨un, hun, hc⟩ h1 h2
        rcases Nat.lt_or_ge s (i - 1) with h3 | h3
        · exact huc (i - 1) h3 (by omega) e1
        · rw [show i - 1 = s by omega] at e1
          exact huS e1
      rw [hagree y hyS hyc] at hyn
      exact h.2 u un c y yn huN hun hc hyn
  · rw [hyS, hsn'] at hyn
    cases hyn
    exact hpos

/-! ## The leaf at the space root, with room -/

/-- A delete, the merges on, that empties its leaf, the space root, which has room
for the bitmap. -/
def DelEmptyRootRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L = w.top.rootKey ∧ DelRoom c cv n

/-- A space root with no live klong reaches nothing: `LiveEdges`. -/
theorem liveEdges_emptyRoot (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (rn : KNode) (hr : N r = some rn) (hl : rn.leaf = true) (he : rn.liveAt t = []) :
    LiveEdges p N t r := by
  have hreach : ∀ u, TReach N t r u → u = r := by
    intro u hu
    induction hu with
    | root => rfl
    | link _ hlk ih =>
      obtain ⟨m, hm, hc⟩ := hlk
      rw [ih, hr] at hm
      cases hm
      rw [he] at hc
      cases hc
  refine ⟨fun rn' hrn' => ?_, fun u un c y yn hu hun hc _ => ?_⟩
  · rw [hr] at hrn'
    cases hrn'
    exact ⟨fun _ => hl, fun h' => by rw [hl] at h'; cases h'⟩
  · rw [hreach u hu, hr] at hun
    cases hun
    rw [he] at hc
    cases hc

set_option maxHeartbeats 1600000 in
/-- The leaf at the space root emptied, with room (bergdb 030-01, step 6): its
bitmap leaves an empty leaf as the space root, and the live counts hold. -/
theorem liveDel_emptyRootRoom (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
      DelEmptyRootRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx _ _ z top _ _ ops op post _ r w _ hI hPc
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0, hroom0⟩ := hPc
  subst hop'
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w (fun _ => True) trivial
    (fun s f x v _ _ => writerWP_true _ _ _) (fun _ _ _ _ _ _ _ _ _ => trivial) trivial hrk
    (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv
    unfold fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hv
  intro L n P w3 hL hn hnl hr03 _ hlk3 hp3' hlinkP hXD _
  obtain ⟨hne, hall, hLr, hroom⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey ∧
      DelRoom (ctxOf p ts) cv m)
    ⟨hne0, hall0, hroot0, hroom0⟩ L n hL hn hnl
  have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
  subst hPnil
  have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
  refine writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _ ?_
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  refine writerWP_mono
    (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom) ?_
  rintro _ v ⟨h1, h2, _, _, _, _, n', hnodes, hleafeq, _, htimes', hlive', _⟩
  have h3t : ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).taken.contains L = false := by
    show w3.taken.contains L = false
    rw [hr03.2.2.1]; exact hLt
  have hN : wNode p (viewOf (treeRun p ts)) v = updN (wNode p (viewOf (treeRun p ts)) w) L n' := by
    have e3 : wNode p (viewOf (treeRun p ts)) ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) =
        wNode p (viewOf (treeRun p ts)) w := hr03.1
    rw [wNode_upsert_updN p _ _ v L n' hnodes h1 h3t, e3]
  have hvtop : v.top.rootKey = L := by
    rw [h2]; show w3.top.rootKey = L; rw [hr03.2.1, hLr]
  -- the root keeps no live klong
  have hcvAll : ∀ c' z, (c', z) ∈ n.live → c' = cv := fun c' z hm => allKeysIn_live_cv n cv hall c' z hm
  have hempty : n'.liveAt (ts.length + 1) = [] := by
    rw [KNode.liveAt_of_times n' (ts.length + 1) htimes']
    cases hl' : n'.live with
    | nil => rfl
    | cons q rest =>
      exfalso
      have hq : q ∈ n'.live := by rw [hl']; exact List.mem_cons_self
      have hlk := lookup_of_mem_nodup n'.live n'.live_keys_nodup q.1 q.2 hq
      rw [hlive' q.1] at hlk
      by_cases hqc : q.1 = cv
      · rw [hqc] at hlk; simp at hlk
      · have hb : (q.1 == cv) = false := by simp [hqc]
        rw [hb] at hlk
        simp only [Bool.false_eq_true, ↓reduceIte] at hlk
        exact hqc (hcvAll q.1 q.2 (bk_mem_of_lookup _ _ _ hlk))
  rw [hN, hvtop]
  exact liveEdges_emptyRoot p _ _ L n' (updN_self _ _ _) (by rw [hleafeq]; exact hnl) hempty

/-! ## The leaf at the space root emptied, full -/

/-- A node's last version without the compare value cv whose live klongs are all
of cv has no live klong. -/
theorem lastVersionGivenDel_liveAt_nil (n : KNode) (cv : Nat) (t : Time)
    (hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true) :
    (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).liveAt t = [] := by
  have htimes : ∀ s, Klong.time s ∈ (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks →
      s ≤ t := by
    intro s hs
    simp only [KNode.lastVersionGivenDel, List.mem_cons, List.mem_map] at hs
    rcases hs with he | ⟨_, _, he⟩
    · cases he; exact Nat.le_refl _
    · cases he
  rw [KNode.liveAt_of_times _ t htimes]
  cases hl : (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).live with
  | nil => rfl
  | cons q rest =>
    exfalso
    have hq : q ∈ (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).live := by
      rw [hl]; exact List.mem_cons_self
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) q.1 q.2 hq
    rw [KNode.delete_live_lookup] at hlk
    by_cases hqc : q.1 = cv
    · rw [hqc] at hlk; simp at hlk
    · have hb : (q.1 == cv) = false := by simp [hqc]
      rw [hb] at hlk
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk
      exact hqc (allKeysIn_live_cv n cv hall q.1 q.2 (bk_mem_of_lookup _ _ _ hlk))

theorem foldl_fixed {α β : Type} (f : β → α → β) :
    ∀ (xs : List α) (acc : β), (∀ x ∈ xs, ∀ m, f m x = m) → xs.foldl f acc = acc := by
  intro xs
  induction xs with
  | nil => intro acc _; rfl
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self acc]
    exact ih acc (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem lastVersionGivenDel_ks_allIn (n : KNode) (t : Time) (del : List Nat)
    (hall : n.allKeysIn del = true) : (n.lastVersionGivenDel t del).ks = [.time t] := by
  unfold KNode.allKeysIn at hall
  unfold KNode.lastVersionGivenDel
  simp only []
  rw [foldl_fixed _ _ _ ?_]
  · simp
  · intro x hx m
    have hx' := List.all_eq_true.mp hall x hx
    rcases x with ⟨k, i⟩
    cases k with
    | key c y =>
      simp only at hx' ⊢
      have hi : i ∈ del := by simpa using hx'
      simp [hi]
    | time _ => rfl
    | del _ => rfl

set_option maxHeartbeats 1600000 in
/-- The leaf at the space root emptied (bergdb 030-01, step 6), with room or full:
after its bitmap, or its split in time when full (its last version without the key
has no key klong), the space root is an empty leaf, and the live counts hold. -/
theorem liveDel_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
      DelEmptyRootM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hPc
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hroot0⟩ := hPc
  by_cases hroom0 : DelRoom (ctxOf p ts) cv n0
  · exact liveDel_emptyRootRoom p R hRL ts tx hw hr z top hz htop ops op post hops r w hpre hI
      ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hroot0, hroom0⟩
  subst hop'
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w (fun _ => True) trivial
    (fun s f x v _ _ => writerWP_true _ _ _) (fun _ _ _ _ _ _ _ _ _ => trivial) trivial hrk
    (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv
    unfold fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hv
  intro L n P w3 hL hn hnl hr03 _ hlk3 hp3' hlinkP hXD _
  obtain ⟨hne, hall, hLr, hfull⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey ∧
      ¬ DelRoom (ctxOf p ts) cv m)
    ⟨hne0, hall0, hroot0, hroom0⟩ L n hL hn hnl
  have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
  subst hPnil
  have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
  refine writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _ ?_
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have hlk3' : ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).nodes.lookup L = some n := hlk3
  refine writerWP_appendDeleteKlong_full_of L 0 cv n _ _ hlk3' hne hfull _ ?_
  intro compact s
  generalize hw4 : ({ ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) with
    trail := s :: ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).trail } : W) = w4
  have h4n : w4.nodes = w3.nodes := by rw [← hw4]
  have h4t : w4.taken = w3.taken := by rw [← hw4]
  have h4top : w4.top = w3.top := by rw [← hw4]
  have h4next : w4.next = w3.next := by rw [← hw4]
  have hlk4 : w4.nodes.lookup L = some n := by rw [h4n]; exact hlk3
  have hL4t : w4.taken.contains L = false := by rw [h4t, hr03.2.2.1]; exact hLt
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
  have hlastks : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlastE : last.liveAt (ts.length + 1) = [] := by
    rw [← hlast]; exact lastVersionGivenDel_liveAt_nil n cv _ hall
  have hlastNode : (⟨n.leaf, last.ks⟩ : KNode) = last := by rw [← hlastks]
  have hcs : (!compact && decide (last.size > (ctxOf p ts).p.splitAbove)) = false := by
    have hsz : last.size = 1 := by
      rw [← hlast]
      simp only [KNode.size, lastVersionGivenDel_ks_allIn n _ _ hall, List.length_singleton]
    rw [hsz]
    have : ¬ (1 > (ctxOf p ts).p.splitAbove) := by simp only [ctxOf]; omega
    simp [this]
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  unfold handleFull
  cases hfirst : n.firstTime == some (ctxOf p ts).i with
  | true =>
    have hfirst' : n.firstTime = some (ctxOf p ts).i := by simpa using hfirst
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ 0 L n last compact (ctxOf p ts) _
      (viewCoherent_ctxOf p ts) w4 hlk4 hL4t hfirst' hcs) ?_
    rintro _ v ⟨_, hvtop, _, hvN⟩
    have hvr : v.top.rootKey = L := by rw [hvtop, h4top, hr03.2.1, hLr]
    rw [hvr]
    refine liveEdges_emptyRoot p _ _ L last ?_ (by rw [hlastks]; exact hnl) hlastE
    rw [show (ctxOf p ts).p = p from rfl] at hvN
    rw [hvN L]
    simp [hlastNode]
  | false =>
    have hfirst' : n.firstTime ≠ some (ctxOf p ts).i := by simpa using hfirst
    have hLn : L < w4.next := by
      rw [h4next]; exact hI3.ids.1 L (by rw [hlk3]; rfl)
    have hny : w4.nodes.lookup w4.next = none := by
      rw [h4n, h4next]
      cases h' : w3.nodes.lookup w3.next with
      | none => rfl
      | some m => have := hI3.ids.1 w3.next (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_handleFullWith_rootTimeSplit_nilV _ L n last compact (ctxOf p ts) w4 hlk4
      hfirst' hcs hLn hny) ?_
    rintro _ v ⟨⟨hvt, hvr, hvN⟩, _⟩
    rw [hvr]
    have hnt : v.taken.contains w4.next = false := by
      rw [hvt, h4t, h4next]
      cases h' : w3.taken.contains w3.next with
      | false => rfl
      | true => have := hI3.ids.2.2.1 w3.next h'; omega
    refine liveEdges_emptyRoot p _ _ w4.next last ?_ (by rw [hlastks]; exact hnl) hlastE
    have hx : w4.next ≠ L := by omega
    simp only [wNode, hnt, Bool.false_eq_true, ↓reduceIte, hvN w4.next, hx, hlastNode]

end SIS.Tree
