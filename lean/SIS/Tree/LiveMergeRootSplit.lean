/-
The merge's tail where its parent, the space root, not made by the transaction,
goes `full` and its split leaves no hole (bergdb 030-01, step 3's rest): a merge
into two nodes whatever the split (no hole before; the copy or the halves under a
new root), or into one node with a space split (the root's last version filled).
The split is the no-hole tail's premise (`SplitStepOKX`, LiveMergeSpace.lean) at
depth 0: l4b's root split (`writerWP_handleFull_root_live`, LiveDelRoot.lean) on
the merged tree. The rest is `MergeTailFullRest8OK`.
-/
import SIS.Tree.LiveMergeChain
import SIS.Tree.LiveDelRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
/-- l4b's `writerWP_handleFull_root_live` (LiveDelRoot.lean) on the tree V with the
space root L's node replaced by its last version (any node, inner or leaf): from
V's live counts the split (in time: a new root holds the last version; in space:
the halves under a new inner root) keeps them, and the nodes reached after were
reached in V or are new, not L. -/
theorem writerWP_handleFull_rootV_live (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i) (hLn : L < w.next)
    (hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.nodes.lookup z = none ∧
      w.taken.contains z = false)
    (hlinks : ∀ u c' z, TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L u → TLink (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i u c' z → z < w.next)
    (hT : TreeOK (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L)
    (hhalves : c.p.splitAbove < last.size → 0 < (halves n.leaf c.i last []).2.2 ∧
      (∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).1.liveAt c.i →
        c' < (halves n.leaf c.i last []).2.2 ∧ (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, (halves n.leaf c.i last []).2.2 ≤ c0 ∧
          c' = splitLocalCv n.leaf (halves n.leaf c.i last []).2.2 c0 ∧
          (c0, z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      HalfOK c.p c.i (halves n.leaf c.i last []).1 ∧ HalfOK c.p c.i (halves n.leaf c.i last []).2.1)
    (hL : LiveEdges c.p (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L) :
    WriterWP (handleFullWith up 0 L [] last compact) c w
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          (TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L z ∨ w.next ≤ z) ∧ z ≠ L) ∧
        w'.taken = w.taken) := by
  obtain ⟨hny0, hny, hnt⟩ := hfree w.next (Nat.le_refl _)
  have hLy : L ≠ w.next := by omega
  have hxV : (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) L = some ⟨n.leaf, last.ks⟩ := updN_self _ _ _
  by_cases hcs : (!compact && decide (last.size > c.p.splitAbove)) = false
  · -- a time split: a new root holds the last version
    refine writerWP_mono (writerWP_handleFullWith_rootTimeSplit_nil up L n last compact c w hlk hfirst
      hcs hLn hny) ?_
    rintro _ v ⟨hvt, hvr, hvn⟩
    have hN2y : wNode c.p base v w.next = some ⟨n.leaf, last.ks⟩ := by
      have hl : v.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ := by
        rw [hvn]; simp [Ne.symm hLy]
      have ht : v.taken.contains w.next = false := by rw [hvt]; exact hnt
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hother : ∀ z, z ≠ L → z ≠ w.next → wNode c.p base v z = (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) z := by
      intro z h1 h2
      rw [updN_ne _ _ _ _ h1]
      have hl : v.nodes.lookup z = w.nodes.lookup z := by rw [hvn]; simp [h1, h2]
      simp only [wNode, hvt, hl]
    have hfy : (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) w.next = none := by rw [updN_ne _ _ _ _ (Ne.symm hLy)]; exact hny0
    have hfr : ∀ u c', TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L u → ¬ TLink (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i u c' w.next := by
      intro u c' hu hl; have := hlinks u c' w.next hu hl; omega
    obtain ⟨_, hR2⟩ := treeOK_rootTimeStep (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) (wNode c.p base v) c.i L w.next ⟨n.leaf, last.ks⟩
      ⟨n.leaf, last.ks⟩ hT hxV hN2y (fun _ _ h => h) hother hfy hfr
    have hgen := liveEdgesX_rootTimeStep c.p (fun _ => False) (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) (wNode c.p base v) c.i L w.next
      ⟨n.leaf, last.ks⟩ ⟨n.leaf, last.ks⟩ hT hxV hN2y (fun _ _ h => h) hother hfy hfr rfl
      (Nat.le_refl _) ((liveEdgesX_false_iff _ _ _ _).mpr hL)
    refine ⟨by rw [hvr]; exact (liveEdgesX_false_iff _ _ _ _).mp hgen, fun z hz => ?_, hvt⟩
    rw [hvr] at hz
    obtain ⟨h1, h2⟩ := hR2 z hz
    exact ⟨h1.imp id (fun h => by omega), h2⟩
  · -- a space split: the halves under a new inner root
    have hc : compact = false := by
      cases compact
      · rfl
      · exact absurd (by simp) hcs
    subst hc
    have hsp : c.p.splitAbove < last.size := by simpa using hcs
    obtain ⟨hsc, hf, hs, hfH, hsH⟩ := hhalves hsp
    obtain ⟨hfl, hsl⟩ := halves_leaf_eq n.leaf c.i last []
    refine writerWP_mono (writerWP_handleFullWith_rootSpaceSplit_nil up L n last c w hlk hfirst hsp
      hLn) ?_
    rintro _ v ⟨hvt, hvr, hvn⟩
    generalize hout : halves n.leaf c.i last [] = out at hsc hf hs hfH hsH hfl hsl hvn
    have hL1 : L ≠ w.next := hLy
    have hL2 : L ≠ w.next + 2 := by omega
    have hL3 : L ≠ w.next + 2 + 2 := by omega
    have hwn : ∀ z, v.taken.contains z = w.taken.contains z := by intro z; rw [hvt]
    have hN2F : wNode c.p base v w.next = some out.1 := by
      have hl : v.nodes.lookup w.next = some out.1 := by rw [hvn]; simp [Ne.symm hL1]
      have ht : v.taken.contains w.next = false := by rw [hwn]; exact hnt
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN2S : wNode c.p base v (w.next + 2) = some out.2.1 := by
      have hl : v.nodes.lookup (w.next + 2) = some out.2.1 := by rw [hvn]; simp [Ne.symm hL2]
      have ht : v.taken.contains (w.next + 2) = false := by
        rw [hwn]; exact (hfree _ (by omega)).2.2
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN2R : wNode c.p base v (w.next + 2 + 2) = some ⟨false, [.time c.i, .key 0 w.next,
        .key out.2.2 (w.next + 2)]⟩ := by
      have hl : v.nodes.lookup (w.next + 2 + 2) = some ⟨false, [.time c.i, .key 0 w.next,
          .key out.2.2 (w.next + 2)]⟩ := by
        rw [hvn]
        simp [Ne.symm hL3, show w.next + 2 + 2 ≠ w.next by omega]
      have ht : v.taken.contains (w.next + 2 + 2) = false := by
        rw [hwn]; exact (hfree _ (by omega)).2.2
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hother : ∀ z, z ≠ L → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
        wNode c.p base v z = (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) z := by
      intro z h1 h2 h3 h4
      rw [updN_ne _ _ _ _ h1]
      have hl : v.nodes.lookup z = w.nodes.lookup z := by rw [hvn]; simp [h1, h2, h3, h4]
      simp only [wNode, hvt, hl]
    have hnd : ([(0, w.next), (out.2.2, w.next + 2)].map Prod.fst).Nodup := by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
      omega
    have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ :
        KNode).liveAt c.i → (c' = 0 ∧ z = w.next) ∨ (c' = out.2.2 ∧ z = w.next + 2) := by
      intro c' z h
      have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (out.2.2, w.next + 2)] hnd c'
        z).mp h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
      exact h'
    have hfreshV : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = w.next + 2 + 2) →
        (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) z = none ∧ ∀ u c', TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i L u → ¬ TLink (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i u c' z := by
      intro z hz
      have hzn : w.next ≤ z := by rcases hz with hz | hz | hz <;> omega
      refine ⟨by rw [updN_ne _ _ _ _ (by omega)]; exact (hfree z hzn).1, fun u c' hu hl => ?_⟩
      have := hlinks u c' z hu hl
      omega
    obtain ⟨_, hR2⟩ := treeOK_rootSpaceStep (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) (wNode c.p base v) c.i
      L w.next (w.next + 2) (w.next + 2 + 2) ⟨n.leaf, last.ks⟩ out.1 out.2.1
      ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ out.2.2
      (splitLocalCv n.leaf out.2.2) hsc hT hxV hN2R hrn hN2F hN2S hf hs hother hfreshV
      (by omega) (by omega) (by omega)
    have hgen := liveEdgesX_rootSpaceStep c.p (fun _ => False) (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) (wNode c.p base v) c.i
      L w.next (w.next + 2) (w.next + 2 + 2) ⟨n.leaf, last.ks⟩ out.1 out.2.1
      ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ out.2.2
      (splitLocalCv n.leaf out.2.2) hsc hT hxV hN2R hrn hN2F hN2S hf hs hother hfreshV
      (by omega) (by omega) (by omega) (fun h => h) (fun h => h) hfl hsl hfH hsH
      (newRoot_liveAt_two c.i w.next (w.next + 2) out.2.2 hsc)
      ((liveEdgesX_false_iff _ _ _ _).mpr hL)
    refine ⟨by rw [hvr]; exact (liveEdgesX_false_iff _ _ _ _).mp hgen, fun z hz => ?_, hvt⟩
    rw [hvr] at hz
    obtain ⟨h1, h2⟩ := hR2 z hz
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)

/-- The instance of `SplitStepOKX` at the space root p (depth 0), not made by the
transaction: l4b's root split on the merged tree (`writerWP_handleFull_rootV_live`),
the halves' facts from the last version's sorted klongs. -/
theorem splitStepOKX_root (c : Ctx) (base : View BVal) (hMP : MergeParamsOK c.p) (p : NodeId)
    (pn : KNode) (Lst : KNode → Prop) (C : Prop) (w3 : W) (x : NodeId)
    (hroot : w3.top.rootKey = p) (hpnew : pn.firstTime ≠ some c.i) :
    SplitStepOKX c base 0 p pn Lst C w3 x := by
  intro w last compact pairs hlk hpn _ _ hleafl hks hsrt hTV hfree hlinksV hLE _ _ _ _ htop _ _ hnone _ _
  have hr : w.top.rootKey = p := by rw [htop]; exact hroot
  rw [hr] at hTV hlinksV hLE ⊢
  unfold handleFull
  exact writerWP_handleFull_rootV_live _ p pn last compact c base w hlk hpnew hpn
    (fun z hz => ⟨(hfree z hz).1, hnone z hz, (hfree z hz).2⟩) hlinksV hTV
    (fun hsp => by
      obtain ⟨hfH1, hsH1, hfH, hsH⟩ := halves_mergeLast c hMP pn last pairs hleafl hks hsrt hsp
      exact ⟨halves_mergeLast_pos c hMP pn last pairs hleafl hks hsrt hsp, hfH1, hsH1, hfH, hsH⟩)
    hLE

/-- The merge's full parent p the space root (d = 1), not made by the transaction,
its split leaving no hole: a merge into two nodes, or into one with a space split. -/
def MergeFullRootX (c : Ctx) (v3 : W) (d : Nat) (p : NodeId) (pn xn ln rn : KNode)
    (il cL ir cR : Nat) : Prop :=
  pn.firstTime ≠ some c.i ∧ d = 1 ∧
  (mergeM2 c xn ln rn cR v3.next = none → ∀ last,
    mergeFullLast pn c.i cL v3.next cR none = some last → c.p.splitAbove < last.size)

set_option maxHeartbeats 4000000 in
/-- The case `MergeFullRootX` at a round with `MergeLiveOK`'s facts: the merge's tail
ends with the live counts, no hole. -/
theorem writerWP_mergeTail_liveRootSplitRound (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    {B : NodeId}
    (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hJ3 : DelInvJ c base w0 k0 F KO B B v3) (hP3 : PathOK c v3 d X K Nn)
    (hx : (v3.path[d]?).map (·.2) = some x) (hpath : (v3.path[d - 1]?).map (·.2) = some p)
    (hplk : v3.nodes.lookup p = some pn) (hpleaf : pn.leaf = false)
    (hxlk : v3.nodes.lookup x = some xn)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (w3 : W) (hr3 : ReadsAs c.p base v3 w3)
    (h3p : w3.nodes.lookup p = some pn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR) (hclt : cL < cR)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hxlr : x = l ∨ x = r) (hln : wNode c.p base v3 l = some ln) (hrn : wNode c.p base v3 r = some rn)
    (hpre3 : v3.nodes <+: w3.nodes) (hpath3 : w3.path = v3.path)
    (hnB : ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next))
    (hN : MergeFullRootX c v3 d p pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hpnew, hd1, hone⟩ := hN
  refine writerWP_mergeTail_liveSplitRoundX c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn x p
    pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL cR w3
    hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB ?_
    (fun hm2 last hl => Or.inl (hone hm2 last hl))
  subst hd1
  refine splitStepOKX_root c base hMP p pn _ _ w3 x ?_ hpnew
  obtain ⟨hX, _, _, _, h0⟩ := hP3
  have := hX 0 (by omega)
  rw [show (1 : Nat) - 1 = 0 from rfl] at hpath
  rw [hpath] at this
  rw [hr3.2.1, ← h0]
  exact (Option.some.inj this).symm

/-! ## What is left of `MergeTailFullRest7OK` -/

/-- `MergeTailFullRest7OK` but in its case `MergeFullRootX` (bergdb 030-01, step 3's
rest): the merge's tail where its parent p goes `full`, and p, not made by the
transaction, is not a segment root and q has no room for p's new klongs or would
compact (the cascade below an inner parent), or q has none for p's copy's klong
(a time split's cascade); or p, made by the transaction, splits in space (in
place). -/
def MergeTailFullRest8OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
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
    ¬ MergeFullSpaceSegChain c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullRootX c v3 d p pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRest7OK` from its rest: its case `MergeFullRootX` (the space root
split with no hole after: a merge into two nodes, or a space split) is proved
(`writerWP_mergeTail_liveRootSplitRound`). -/
theorem mergeTailFullRest7OK_of_rest8 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hF : MergeTailFullRest8OK c base B H) :
    MergeTailFullRest7OK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR hNC
  by_cases hN : MergeFullRootX c v3 d p pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveRootSplitRound c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn
      x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL
      cR w3 hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR hNC hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest8OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR8 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest8OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR7 key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRest7OK_of_rest8 c base hvc hm hMP hF) v hJ hpb hhi hLH hR3

end SIS.Tree
