/-
The merge's tail where its parent goes `full`, the parent the space root (bergdb
030-01, step 3's rest): split in time, not in place, its copy becomes the space
root (`newSuperRoot`). Into one node the hole moves to the copy, which the next
round's descent finds at once (the key's segment is the first, so the descent
starts and stops at the space root); into two nodes there is no hole. The rest
is `MergeTailFullRest6OK`.
-/
import SIS.Tree.LiveMergeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The space root x, the only hole, replaced by a fresh node y of x's klongs: the
hole is the new space root y, and the nodes reached are y and the nodes reached
before but x. -/
theorem liveEdgesH_newRoot (p : Params) (V N' : NodeId → Option KNode) (t : Time) (x y : NodeId)
    (xl : KNode) (hT : TreeOK V t x) (h : LiveEdgesH p V t x (fun z => z = x)) (hxn : V x = some xl)
    (hyV : V y = none) (hyf : ∀ u c, TReach V t x u → ¬ TLink V t u c y)
    (hN'y : N' y = some xl) (hN' : ∀ z, z ≠ x → z ≠ y → N' z = V z) :
    LiveEdgesH p N' t y (fun z => z = y) ∧
      ∀ u, TReach N' t y u → (TReach V t x u ∧ u ≠ x ∧ u ≠ y) ∨ u = y := by
  have hyx : y ≠ x := fun he => by rw [he, hxn] at hyV; cases hyV
  have hR : ∀ u, TReach N' t y u → (TReach V t x u ∧ u ≠ x ∧ u ≠ y) ∨ u = y := by
    intro u hu
    induction hu with
    | root => exact Or.inr rfl
    | @link u c z _ hl ih =>
      obtain ⟨m, hm, hc⟩ := hl
      rcases ih with ⟨huR, hux, huy⟩ | huy
      · rw [hN' u hux huy] at hm
        have hl0 : TLink V t u c z := ⟨m, hm, hc⟩
        exact Or.inl ⟨TReach.link huR hl0, fun he => hT.rootFree u c huR (by rw [← he]; exact hl0),
          fun he => hyf u c huR (by rw [← he]; exact hl0)⟩
      · subst huy
        rw [hN'y] at hm
        cases hm
        have hl0 : TLink V t x c z := ⟨xl, hxn, hc⟩
        exact Or.inl ⟨TReach.link TReach.root hl0,
          fun he => hT.rootFree x c TReach.root (by rw [he] at hl0; exact hl0),
          fun he => hyf x c TReach.root (by rw [← he]; exact hl0)⟩
  refine ⟨⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩, hR⟩
  · rw [hN'y] at hrn
    cases hrn
    exact ⟨(h.1 xl hxn).1, fun hn => absurd rfl hn⟩
  · -- the link's ends before: u (or x for y) and z
    obtain ⟨u0, hu0R, hun0⟩ : ∃ u0, TReach V t x u0 ∧ V u0 = some un := by
      rcases hR u hu with ⟨huR, hux, huy⟩ | huy
      · exact ⟨u, huR, by rw [← hN' u hux huy]; exact hun⟩
      · subst huy; rw [hN'y] at hun; exact ⟨x, TReach.root, by rw [hun] at hxn; exact hxn⟩
    have hl0 : TLink V t u0 c z := ⟨un, hun0, hc⟩
    have hzx : z ≠ x := fun he => hT.rootFree u0 c hu0R (by rw [← he]; exact hl0)
    have hzy : z ≠ y := fun he => hyf u0 c hu0R (by rw [← he]; exact hl0)
    rw [hN' z hzx hzy] at hzn
    exact ⟨fun _ => (h.2 u0 un c z zn hu0R hun0 hc hzn).1 hzx, fun he => absurd he hzy⟩

/-- `newSuperRoot` sets the space root and keeps the nodes, the taken nodes, the
heights' cache and the path. -/
theorem writerWP_newSuperRoot_frameG (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (newSuperRoot y) c w (fun _ w' => w'.top.rootKey = y ∧ w'.taken = w.taken ∧
      w'.nodes = w.nodes ∧ w'.gh = w.gh ∧ w'.path = w.path) := by
  unfold newSuperRoot note fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · simp only [writerWP_set, writerWP_bind, writerWP_modify]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- The time split, not in place, of the node at the path's top (no parent): the
copy, x's entry in `gh`, becomes the space root. -/
theorem writerWP_handleFullWith_time_root_gh (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) (Q : W → Prop)
    (hup : ∀ (gh : Nat × Nat), w.gh.lookup x = some gh → ∀ w1 : W,
        w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, last.ks⟩)] → w1.gh = (w.next, gh.1, gh.2) :: w.gh →
        w1.taken = w.taken → w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 →
        WriterWP (newSuperRoot w.next) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith up 0 x [] last compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cachedL x n c w hlk _ (fun gh hgh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt
  simp only [writerWP_pure, writerWP_bind, hcs, Bool.false_eq_true, ↓reduceIte]
  split
  · simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        exact hup gh hgh _ rfl rfl rfl rfl rfl rfl
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        exact hup gh hgh _ rfl rfl rfl rfl rfl rfl


set_option maxHeartbeats 4000000 in
/-- The space root x, not made by the transaction, split in time with a last
version given: from the hole at x in the tree with x's node replaced by `last`,
the hole is at the copy w.next, the new space root, after; x is left behind. -/
theorem writerWP_handleFull_timeRoot_live (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (last : KNode) (compact : Bool) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxn : x < w.next)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hroot : w.top.rootKey = x)
    (hT : TreeOK (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i x)
    (hnx : wNode c.p base w w.next = none) (hnl : w.nodes.lookup w.next = none)
    (hnt : w.taken.contains w.next = false)
    (hfreshT : ∀ u c', TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i x u → ¬ TLink (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i u c' w.next)
    (hV : LiveEdgesH c.p (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i x (fun z => z = x)) :
    WriterWP (handleFullWith up 0 x [] last compact) c w
      (fun _ w' => LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun z => z = w.next) ∧
        w'.top.rootKey = w.next ∧
        (∀ u, TReach (wNode c.p base w') c.i w'.top.rootKey u →
          (TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i x u ∧ u ≠ x ∧ u ≠ w.next) ∨ u = w.next) ∧
        (∀ z, z ≠ x → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
        w'.gh.lookup w.next = w.gh.lookup x ∧ (∀ u, u ≠ w.next → w'.gh.lookup u = w.gh.lookup u)) := by
  have hxy : x ≠ w.next := by omega
  refine writerWP_handleFullWith_time_root_gh up x n last compact c w hlk hfirst hcs _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1path h1next
  refine writerWP_mono (writerWP_newSuperRoot_frameG w.next c w1) ?_
  intro _ w2 ⟨h2r, h2t, h2n, h2gh, h2path⟩
  have hlx2 : w2.nodes.lookup x = some n := by
    rw [h2n, h1n, lookup_append_single_ne _ _ _ _ hxy]; exact hlk
  rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
  simp only [putNode, writerWP_modify]
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
      w3.top = w2.top → w3.path = w2.path → w3.gh = w2.gh →
      LiveEdgesH c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
        w3.top.rootKey = w.next ∧
        (∀ u, TReach (wNode c.p base w3) c.i w3.top.rootKey u →
          (TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i x u ∧ u ≠ x ∧ u ≠ w.next) ∨ u = w.next) ∧
        (∀ z, z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z) ∧
        w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧ w3.taken = w.taken ∧ w3.path = w.path ∧
        w3.gh.lookup w.next = w.gh.lookup x ∧ (∀ u, u ≠ w.next → w3.gh.lookup u = w.gh.lookup u) := by
    intro w3 h3n h3t0 h3top0 h3path0 h3gh0
    have h3t : w3.taken = w.taken := by rw [h3t0, h2t, h1t]
    have h3r : w3.top.rootKey = w.next := by rw [h3top0, h2r]
    have hlook : ∀ z, z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z := by
      intro z hzx hzy
      rw [h3n, lookup_upsert, if_neg hzx, h2n, h1n, lookup_append_single_ne _ _ _ _ hzy]
    have hly : w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ := by
      rw [h3n, lookup_upsert, if_neg (Ne.symm hxy), h2n, h1n, lookup_append_single_self]
      exact hnl
    have hy3t : w3.taken.contains w.next = false := by rw [h3t]; exact hnt
    have hN'y : wNode c.p base w3 w.next = some ⟨n.leaf, last.ks⟩ := by
      simp only [wNode, hy3t, Bool.false_eq_true, ↓reduceIte, hly]
    have hN' : ∀ z, z ≠ x → z ≠ w.next → wNode c.p base w3 z = (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) z := by
      intro z hzx hzy
      rw [updN_ne _ _ _ _ hzx]
      simp only [wNode, h3t, hlook z hzx hzy]
    obtain ⟨hL, hR⟩ := liveEdgesH_newRoot c.p (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) (wNode c.p base w3) c.i x w.next ⟨n.leaf, last.ks⟩ hT hV
      (updN_self _ _ _) (by rw [updN_ne _ _ _ _ (Ne.symm hxy)]; exact hnx) hfreshT hN'y hN'
    refine ⟨by rw [h3r]; exact hL, h3r, by rw [h3r]; exact hR, hlook, hly, h3t,
      by rw [h3path0, h2path, h1path], ?_, ?_⟩
    · rw [h3gh0, h2gh, h1gh]; simp [hgh]
    · intro u hu
      rw [h3gh0, h2gh, h1gh]
      have hb : (u == w.next) = false := by simp [hu]
      simp only [List.lookup, hb]
  exact key _ rfl rfl rfl rfl rfl

set_option maxHeartbeats 16000000 in
/-- A merge into one node whose parent p, the space root (at depth 0), not made
by the transaction, goes `full` and splits in time: the hole moves from p to p's
copy nx + 2, the new space root; the merged nodes and p are left behind; the
copy has p's entry in the heights' cache. -/
theorem writerWP_mergeTail_liveFullRoot (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (x : NodeId) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hproot : root = p)
    (hpnew : pn.firstTime ≠ some c.i) (hone : mergeM2 c xn ln rn cR nx = none)
    (hnB : ¬ MergeParentRoom c pn il cL nx ir cR none)
    (htime : ∀ last, mergeFullLast pn c.i cL nx cR none = some last →
      pn.size + mergeParentNeed c.i pn il ir cR none ≤ c.p.M ∨ last.size ≤ c.p.splitAbove)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x 1 p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => res = 1 ∧
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = nx + 2) ∧
        w'.top.rootKey = nx + 2 ∧ (∃ yn, w'.nodes.lookup (nx + 2) = some yn) ∧
        w'.gh.lookup (nx + 2) = w3.gh.lookup p) := by
  obtain ⟨hpL, hpR, hc, hlink_l, hlink_r, hpl, hpr, hlr, hlt, hrt, hcvL, hcvR, hlt_nx, hlnx, hrnx,
    hpnx, hsib, hmb⟩ := mergeTail_treeFacts c x p pn ln rn l r il ir cL cR N root nx Hl hm hMP hT hp hpn
    hL hLL hR hRL hclt hxlr hln hrn hpt hch (fun z hz => (hfree z hz).1) hpleaf hLive hHl
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  obtain ⟨hsortE, hElen, hsrcE, hnewT, hnewSrc, hnewFill⟩ :=
    mergeTail_newFacts c xn ln rn cR hlt hrt hlrange hrrange hrhead hmb
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_and (writerWP_ghOf_reads x c _ base hvc) (writerWP_ghOf_ghL x c _))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4, h4gh⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  obtain ⟨hnone3, hpx, hxnx, hpT, hNw3, hcl', hne', hlr', hnoOld, hmpT⟩ :=
    mergeTail_frameFacts c base x p pn l r cL cR N root nx w3 lMade rMade hT hp hpn hxlr hpt hN3 h3src
      hlink_l hlink_r hpl hpr hlnx hrnx
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
      (writerWP_newKey_ghL _ _ _ _ c _)) ?_
    intro m1 w5 ⟨⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩, h5gh⟩
    refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
      (writerWP_setMadeFor_gh _ _ c _)) ?_
    intro _ w6 ⟨⟨h6n, h6t, h6top, h6next, h6v, h6p⟩, h6gh⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have h6path : w6.path = w3.path := by rw [h6p, h5p, h4p]
    have hw6N : ∀ y, y ≠ m1 → wNode c.p base w6 y = N y := by
      intro y hym
      have : wNode c.p base w6 y = wNode c.p base w4 y := by
        simp only [wNode, h6t, h5t, h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym]
      rw [this, hr4.1]; exact congrFun hN3 y
    cases hsec : second with
    | some ksg =>
      exfalso
      have h1 : mergeM2 c xn ln rn cR m1 = none := hone
      simp [mergeM2, hmk, hsec] at h1
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_fullB p pn 0 il cL m1 ir cR none c w6 _ hw6p hnB ?_
      intro last compact s7 hlast hcomp
      obtain ⟨hlastT, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hcLm1 : (cL, m1) ∈ last.liveAt c.i := by
        rw [KNode.liveAt_of_times last c.i hlastT]
        apply bk_mem_of_lookup
        rw [(mergeFullLast_lookup pn c.i cL m1 cR none last hlast).2.1 rfl cL]
        simp
      -- the tree with p's node replaced by its last version
      have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
      have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
        simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
      have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
        intro y hyp hym
        rw [updN_ne _ _ _ _ hyp, hw6N y hym]
      have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
          (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
        intro cc z hm'
        have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm'
        rw [hfirst] at this; exact this
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [hfirst] at hz; exact hz
      have hTV : TreeOK (updN (wNode c.p base w6) p last) c.i root :=
        treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
          (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
          hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym)
      have hVreach := mergeV_reach N (updN (wNode c.p base w6) p last) c.i root p l r m1 none pn ln rn
        last cL cR hT hp hpn hpL hpR hln hrn hVp
        (fun cc z hm' => by
          rcases hnoneL rfl cc z hm' with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))
        (fun m mn hm' hmn' cc z hz => by
          rcases hm' with hm' | hm'
          · rw [hm', hVm1] at hmn'
            cases hmn'
            exact hnewSrc first hsrc1 cc z hz
          · cases hm')
        (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm' => by cases hm')
      have hy0 : m1 + 2 ≠ m1 := by omega
      have hfreshV : ∀ u c', TReach (updN (wNode c.p base w6) p last) c.i root u →
          ¬ TLink (updN (wNode c.p base w6) p last) c.i u c' (m1 + 2) := by
        intro u c' hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hnoneL rfl c' (m1 + 2) hc' with ⟨_, h⟩ | ⟨h, _, _⟩
          · exact hy0 h
          · exact hfreshT (m1 + 2) (by omega) p c' hp ⟨pn, hpn, h⟩
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' (m1 + 2) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · exact hfreshT (m1 + 2) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
            · exact hfreshT (m1 + 2) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
          · rcases hu1 with hu1 | hu1 | hu1
            · rw [hVN u hup hum] at hun
              exact hfreshT (m1 + 2) (by omega) u c' hu1 ⟨un, hun, hc'⟩
            · exact hum hu1
            · cases hu1
      have hLV : LiveEdgesH c.p (updN (wNode c.p base w6) p last) c.i root (fun z => z = p) := by
        have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
        have hmlen : first.length = ln.live.length + rn.live.length := by rw [hfirst, hElen]
        obtain ⟨hmne, hmfill⟩ := hnewFill first hfirstS (by rw [hmlen]; exact hsib)
        refine liveEdgesH_mergeOne c.p N _ c.i root p l r m1 pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R hVm1
          (hnewSrc first hsrc1) (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
          (by rw [hrl, hll]) hmne hmfill hVp hleafl (hnoneL rfl) (fun h0 => by rw [h0] at hcLm1; cases hcLm1)
          (fun y hyp hyl hyr hym => hVN y hyp hym)
          (fun y hy => by
            have hyx := hHl y hy
            rcases hxlr with h | h
            · exact Or.inl (hyx.trans h)
            · exact Or.inr (hyx.trans h))
          hLive
      have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
        rcases htime last hlast with h | h
        · rw [hcomp, decide_eq_true h]; rfl
        · have h' : ¬ (last.size > c.p.splitAbove) := by omega
          simp [h']
      unfold handleFull
      rw [← hlasteq] at hTV hfreshV hLV hVreach
      rw [hproot] at hTV hfreshV hLV hVreach
      have hnx6 : w6.next = m1 + 2 := h6next'
      refine writerWP_mono (writerWP_handleFull_timeRoot_live _ p pn last compact c base
        ({ w6 with trail := s7 :: w6.trail } : W) hw6p
        (by show p < w6.next; omega) hpnew hcs
        (by show w6.top.rootKey = p; rw [h6top', hproot]) hTV
        (by show wNode c.p base w6 w6.next = none; rw [hnx6, hw6N (m1 + 2) hy0]; exact (hfree _ (by omega)).1)
        (by show w6.nodes.lookup w6.next = none
            rw [hnx6, h6old (m1 + 2) (by omega) hy0]; exact hnone3 _ (by omega))
        (by show w6.taken.contains w6.next = false; rw [hnx6, h6taken]; exact (hfree _ (by omega)).2)
        (by show ∀ u c', TReach _ c.i p u → ¬ TLink _ c.i u c' w6.next; rw [hnx6]; exact hfreshV)
        hLV) ?_
      rintro _ w8 ⟨hL8, h8r, hR8, h8l, h8y, h8t, _, h8gy, _⟩
      change w8.nodes.lookup w6.next = _ at h8y
      change w8.gh.lookup w6.next = w6.gh.lookup p at h8gy
      change w8.taken = w6.taken at h8t
      change w8.top.rootKey = w6.next at h8r
      change ∀ u, TReach (wNode c.p base w8) c.i w8.top.rootKey u →
        (TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i p u ∧ u ≠ p ∧ u ≠ w6.next) ∨
          u = w6.next at hR8
      change LiveEdgesH c.p (wNode c.p base w8) c.i w8.top.rootKey (fun z => z = w6.next) at hL8
      rw [hnx6] at h8y h8gy h8r hR8 hL8
      rw [h8r] at hL8 hR8
      have h8pT : w8.taken.contains p = false := by rw [h8t, h6taken]; exact hpT
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_wNode p m1 c base hvc _ w8 hne' h8pT)
        (writerWP_mergeCleanup_frameL p m1 c _ w8)) ?_
      rintro _ w9 ⟨⟨h9top, _, _, _, h9w, _, _⟩, _, _, h9fr⟩
      have hnot : ∀ z, TReach (wNode c.p base w8) c.i (m1 + 2) z → z ≠ p ∧ z ≠ l ∧ z ≠ r := by
        intro z hz
        rcases hR8 z hz with ⟨hzV, hzp, _⟩ | hzy
        · obtain ⟨_, hzl, hzr⟩ := hVreach z hzV
          exact ⟨hzp, hzl, hzr⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
      have hfr9 : ∀ y, y ≠ p → y ≠ l → y ≠ r →
          w9.gh.lookup y = w8.gh.lookup y ∧ w9.nodes.lookup y = w8.nodes.lookup y :=
        fun y hyp hyl hyr => h9fr y hyp (hcl' y hyl hyr)
      have h9r : w9.top.rootKey = m1 + 2 := by rw [h9top, h8r]
      refine ⟨rfl, ?_, h9r, ?_, ?_⟩
      · rw [h9r]
        exact liveEdgesH_congr_reach c.p (wNode c.p base w8) _ c.i (m1 + 2) _ hL8
          (fun z hz => by obtain ⟨hzp, hzl, hzr⟩ := hnot z hz; exact h9w z hzp (hcl' z hzl hzr))
      · exact ⟨_, by rw [(hfr9 (m1 + 2) (by omega) (by omega) (by omega)).2, h8y]⟩
      · rw [(hfr9 (m1 + 2) (by omega) (by omega) (by omega)).1, h8gy, h6gh, h5gh p hpm1,
          h4gh p hpx]


/-- The merges' descent after the space root p split in time (R1): the descent at
(g, h) from S found x at depth 1 below p, inner; on a state T whose space root y
reads with height h + 1, the descent at (g, h + 1) ends at y (the key's segment
is the first: p, inner, cannot be above a segment leaf on the path). -/
theorem descendToHeight_newRoot (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : d = 1)
    (p : NodeId) (pn : KNode) (hp : (S1.path[0]?).map (·.2) = some p) (hpn : rdN c S p = some pn)
    (hpl : pn.leaf = false) (y : NodeId) (hTr : T.top.rootKey = y)
    (hRy : ∃ yn, rdN c T y = some yn) (hGy : ∃ g', rdG c T y = some (g', h + 1)) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => (T1.path[d']?).map (·.2) = some y) := by
  obtain ⟨root, P0, cv, ext, hdsr, hcv, hdh, hp1, hd1, -⟩ :=
    writerWP_descendToHeight_rd key g h c S d S1 hS
  intro d' T1 hT
  obtain ⟨root', P0', cv', ext', hdsr', hcv', hdh', hp1', hd1', -⟩ :=
    writerWP_descendToHeight_rd key g (h + 1) c T d' T1 hT
  rw [hcv] at hcv'
  cases hcv'
  obtain ⟨hlast, hpre, hnil⟩ := dsrP_shape (rdN c S) c.i c.p.fuel key g _ root P0 hdsr
  obtain ⟨B, hB⟩ := List.getLast?_eq_some_iff.mp hlast
  have hL : S1.path.map (·.2) = B ++ (root :: ext.map (·.2)) := by
    rw [hp1, List.map_append, hB]; simp
  have hlenL : S1.path.length = B.length + 1 + ext.length := by
    have := congrArg List.length hL
    simp only [List.length_map, List.length_append, List.length_cons] at this
    omega
  have hdL : d = B.length + ext.length := by
    have h2 : (P0 ++ ext).length = B.length + 1 + ext.length := by rw [← hp1]; exact hlenL
    rw [hd1]; omega
  -- the key's segment is the first
  have hg : key.take g = [] := by
    by_cases hg : key.take g = []
    · exact hg
    · exfalso
      obtain ⟨yl, nl, hyl, hnl, hll⟩ := hpre hg
      rw [hB, List.dropLast_concat] at hyl
      have hB1 : B.length = 1 := by
        rcases Nat.lt_or_ge B.length 1 with h0 | h1
        · have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [this] at hyl; cases hyl
        · omega
      obtain ⟨b0, hb0⟩ : ∃ b0, B = [b0] := by
        cases B with
        | nil => simp at hB1
        | cons a l => cases l with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hB1
      rw [hb0] at hyl hL
      simp only [List.getLast?_singleton, Option.some.injEq] at hyl
      have hz : (S1.path.map (·.2))[0]? = some p := by rw [List.getElem?_map]; exact hp
      rw [hL] at hz
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, Option.some.injEq] at hz
      rw [← hz, hyl, hnl] at hpn
      cases hpn
      rw [hpl] at hll; cases hll
  have hP0' := (dsrP_shape (rdN c T) c.i c.p.fuel key g _ root' P0' hdsr').2.2 hg
  have hr' : root' = T.top.rootKey := by
    unfold dsrP at hdsr'
    rw [hg] at hdsr'
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hdsr'
    exact hdsr'.1.symm
  rw [hr', hTr] at hdh'
  obtain ⟨yn, hyn⟩ := hRy
  obtain ⟨gy, hgy⟩ := hGy
  have hfuel : 0 < c.p.fuel := by
    cases hfu : c.p.fuel with
    | zero => rw [hfu] at hdh; simp [dhP] at hdh
    | succ _ => omega
  obtain ⟨f, hf'⟩ : ∃ f, c.p.fuel = f + 1 := ⟨c.p.fuel - 1, by omega⟩
  rw [hf'] at hdh'
  simp only [dhP, hyn, hgy, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hdh'
  subst hdh'
  rw [hd1', hp1', hP0', hTr]
  simp

/-- The case of `MergeTailFullRest5OK` that `writerWP_mergeTail_liveFullRoot`
proves: a merge into one node whose parent p, the space root (d = 1), not made
by the transaction, goes `full` and splits in time. -/
def MergeFullTimeRoot1 (c : Ctx) (v3 : W) (d : Nat) (pn xn ln rn : KNode) (il cL ir cR : Nat) :
    Prop :=
  d = 1 ∧ pn.firstTime ≠ some c.i ∧ mergeM2 c xn ln rn cR v3.next = none ∧
  ∀ last, mergeFullLast pn c.i cL v3.next cR none = some last →
    pn.size + mergeParentNeed c.i pn il ir cR none ≤ c.p.M ∨ last.size ≤ c.p.splitAbove

set_option maxHeartbeats 16000000 in
/-- `MergeTailFullRest5OK`'s case `MergeFullTimeRoot1`: at a round with
`MergeLiveOK`'s facts, the merge's tail keeps the hole's form one height up, the
hole p's copy, the new space root, which the next round's descent finds at once
(`descendToHeight_newRoot`). -/
theorem writerWP_mergeTail_liveFullRootRound (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    {B : NodeId} {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode)
    (hS : descendToHeight key g h c v = .ok (d, v1))
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hJ3 : DelInvJ c base w0 k0 F KO B B v3) (hP3 : PathOK c v3 d X K Nn)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hx : (v3.path[d]?).map (·.2) = some x) (hpath : (v3.path[d - 1]?).map (·.2) = some p)
    (hplk : v3.nodes.lookup p = some pn) (hpleaf : pn.leaf = false)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (w3 : W) (hr3 : ReadsAs c.p base v3 w3)
    (h3p : w3.nodes.lookup p = some pn) (hk3 : ObsKept c v3 w3)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR) (hclt : cL < cR)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hxlr : x = l ∨ x = r) (hln : wNode c.p base v3 l = some ln) (hrn : wNode c.p base v3 r = some rn)
    (hnB : ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next))
    (hN : MergeFullTimeRoot1 c v3 d pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hd1, hpnew, hone, htime⟩ := hN
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, _, hS2, _, _⟩ := id hP3
  have hXi : ∀ i, i ≤ d → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d - 1) (by omega) p hpath
  have hxX := hXi d (Nat.le_refl _) x hx
  have hNlk : ∀ i, i ≤ d → wNode c.p base v3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hpnN : Nn (d - 1) = pn := by
    have := (hS2 (d - 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hpn : wNode c.p base v3 p = some pn := by rw [hpX, ← hpnN]; exact hNlk _ (by omega)
  have hdep : ∀ i, i ≤ d → PathLen (wNode c.p base v3) c.i v3.top.rootKey (X i) i :=
    pathOK_depth c base v3 d X K Nn hP3
  have hpP : PathLen (wNode c.p base v3) c.i v3.top.rootKey p (d - 1) := by
    rw [hpX]; exact hdep _ (by omega)
  have hpR := hpP.reach
  have hpRS := tReach_reachS _ c.i _ _ hpR
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  have hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z := by
    intro z hz u c' hu hl
    obtain ⟨un, hun, hc⟩ := hl
    have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
    omega
  have hmemL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hmemR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln
  obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn
  have hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc) := by
    intro cc z h'
    have h1 := hlr1 cc z h'
    rw [hll] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
        · rcases Nat.eq_zero_or_pos cc with hcc | hcc
          · exact Or.inl hcc
          · exact Or.inr (by omega)
        · exact Or.inr (h0 hc0)
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      rcases Nat.eq_zero_or_pos cL with hc0 | hc0
      · omega
      · exact h1.1 hxl hc0
  have hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc) := by
    intro cc z h'
    have h1 := hrr1 cc z h'
    rw [hrl] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h0 (by omega))
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      exact h1.1 hxl (by omega)
  -- the round's descent
  obtain ⟨_, _, _, _, _, _, _, _, _, hk01⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v _ v1 hS
  have hk03 := hk01.trans hk13
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have h1 := hy d v1 hS
    rw [← hp13, hx] at h1
    exact (Option.some.inj h1).symm
  have hN3 : wNode c.p base v3 = wNode c.p base v := by rw [hr13.1, hr01.1]
  have htop3 : v3.top = v.top := hk03.2.2
  have hLive : LiveEdgesH c.p (wNode c.p base v3) c.i v3.top.rootKey (HoleAtW key g h c v) := by
    rw [hN3, htop3]; exact hLH
  have hlP : PathLen (wNode c.p base v3) c.i v3.top.rootKey l (d - 1 + 1) :=
    PathLen.link hpP ⟨pn, hpn, hmemL⟩
  have hrP : PathLen (wNode c.p base v3) c.i v3.top.rootKey r (d - 1 + 1) :=
    PathLen.link hpP ⟨pn, hpn, hmemR⟩
  have hproot : v3.top.rootKey = p := by
    obtain ⟨_, _, _, _, h0⟩ := id hP3
    rw [← h0, hpX, hd1]
  rw [hone] at hnB
  rw [hd1]
  refine writerWP_mono (writerWP_mergeTail_liveFullRoot c base hvc x p pn xn leftSome l ln il r rn ir
    cL cR (wNode c.p base v3) v3.top.rootKey v3.next w3 (HoleAtW key g h c v) hm hMP hI.tree hpR hpn
    hL hLL hR hRL hclt hxlr hln hrn (hI.times p pn hpn) (fun cc z zn _ hzn => hI.times z zn hzn)
    hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
    (fun z hz => by
      rcases hsrc3 z hz with h' | h'
      · exact hI.ids.1 z h'
      · exact hI.ids.2.1 z h')
    (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hpleaf hll hrl
    (fun cc z h' => hlr2 cR r hmemR hclt cc z h') hrrange hproot hpnew hone hnB htime hLive hHl) ?_
  rintro res v4 ⟨hres, hL4, h4r, ⟨yn, hy4⟩, hgy4⟩
  subst hres
  refine ⟨fun _ => ?_, fun h' => absurd rfl h'⟩
  have hpnv : rdN c v p = some pn := by rw [← hk03.1]; exact rdN_of_lookup c v3 p pn hplk
  have hpc1 : PathCached v1 := writerWP_descendToHeight_path_cached key g h c v d v1 hS
  have hgr : GradedL (rdN c v) (rdG c v) (v1.path.map (·.2)) := by
    have := gradedL_of_ht hvo.heights hb1 hi1 hpf1 hpc1
    rw [hk01.1, hk01.2.1] at this
    exact this
  have hGy : ∃ g', rdG c v4 (v3.next + 2) = some (g', h + 1) := by
    obtain ⟨g1, h1, g2, h2, hG1, hG2, hh⟩ := gradedL_get (rdN c v) (rdG c v) _ (d - 1) p x pn hgr
      (by rw [List.getElem?_map, ← hp13]; exact hpath)
      (by rw [show d - 1 + 1 = d by omega, List.getElem?_map, ← hp13]; exact hx)
      hpnv hpleaf
    have hxv : (v1.path[d]?).map (·.2) = some x := by rw [← hp13]; exact hx
    obtain ⟨x', hx', _, ⟨gx, hgx'⟩, _⟩ := descend_exit_shape key g h c v v1 d hS
    rw [hxv] at hx'
    cases hx'
    rw [hgx'] at hG2; cases hG2
    refine ⟨g1, ?_⟩
    rw [rdG_of_lookup c v4 _ _ hy4, hgy4, ← rdG_of_lookup c w3 p pn h3p, hk3.2.1, hk03.2.1, hG1, hh]
  have hup : HoleAtW key g (h + 1) c v4 (v3.next + 2) := by
    intro d'' T1 hT1
    exact descendToHeight_newRoot key g h c v v1 v4 d hS hd1 p pn
      (by have h' := hpath; rw [hd1] at h'; rw [← hp13]; exact h') hpnv hpleaf (v3.next + 2) h4r
      ⟨yn, rdN_of_lookup c v4 _ _ hy4⟩ hGy d'' T1 hT1
  refine liveEdgesH_mono c.p _ c.i _ (fun y => y = v3.next + 2) _ (fun y hy => hy ▸ hup) ?_ hL4
  intro u un cc y yn' hu hun hcc hyn _ hyp
  exact ((hL4.2 u un cc y yn' hu hun hcc hyn).1 hyp).1


/-! ## What is left of `MergeTailFullRest5OK` -/

/-- `MergeTailFullRest5OK` but in its case `MergeFullTimeRoot1` (bergdb 030-01,
step 3's rest): the merge's tail where its parent p goes `full`, and p, not made
by the transaction, is the space root (d = 1) split in space, or split in time
with a merge into two nodes, or q has no room for p's new klongs or would compact
(the cascade); or p, made by the transaction, splits in space (in place). -/
def MergeTailFullRest6OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
    Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
      (ir cL cR : Nat) (w3 : W), ReadsAs c.p base v3 w3 →
    w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
    (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true) →
    pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
    pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
    (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
    v3.nodes <+: w3.nodes → w3.path = v3.path →
    ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
    ¬ MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullMadeTime c v3 pn xn ln rn il cL ir cR →
    ¬ MergeFullSpaceRoom c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullTimeRoomG c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullSpaceG c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullTimeRoot1 c v3 d pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRest5OK` from its rest: its case `MergeFullTimeRoot1` (the space
root split in time, a merge into one node) is proved
(`writerWP_mergeTail_liveFullRootRound`). -/
theorem mergeTailFullRest5OK_of_rest6 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullRest6OK c base B H) :
    MergeTailFullRest5OK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG
  by_cases hN : MergeFullTimeRoot1 c v3 d pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveFullRootRound c base hvc hm hMP hvo key g h v v1 v3 d F w0 k0 KO
      X K Nn x p pn xn hS hr13 hk13 hp13 hLH hJ3 hP3 hb1 hi1 hpf1 hx hpath hplk hpleaf
      leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3 hL hLL hR hRL hclt hll hrl hxlr hln hrn
      hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest6OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR6 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest6OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR5 key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRest5OK_of_rest6 c base hvc hm hMP hvo hF) v hJ hpb hhi hLH hR3

end SIS.Tree
