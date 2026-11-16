/-
The delete's leaf full, for `l4` (bergdb 030-01, step 5): a leaf that the
transaction made, full, splits in time in place: its node becomes its last
version without the key, as the bitmap with room makes it, and the leaf is the
hole (`liveHoleW_leafChange`, the room case's argument for any change of the leaf
that keeps its kind and its other live klongs; `liveDel_fullMade`).
-/
import SIS.Tree.LiveUpRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1600000 in
/-- The leaf changed alone (bergdb 030-01, step 5): at a state v whose tree is the
delete's start with the key's leaf L replaced by a leaf n' that keeps n's live
klongs but the key's, and one, the live counts hold but at L, which the merges'
descent at L's pair finds. -/
theorem liveHoleW_leafChange (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hk : ViewKinds KO BK c) (w w3 v : W) (pre : List Nat) (cv : Nat) (rk L : NodeId) (n n' : KNode)
    (P : List (Option Nat × NodeId)) (g : Nat)
    (hI : PutInv c base w) (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true) (hkey : keyWf (pre ++ [cv]) = true)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n))
    (hN : wNode c.p base v = updN (wNode c.p base w) L n') (hvtop : v.top = w.top)
    (hlkv : v.nodes.lookup L = some n')
    (hnodes : ∀ q m, q ≠ L → w.taken.contains q = false → w3.nodes.lookup q = some m →
      v.nodes.lookup q = some m)
    (hn'l : n'.leaf = true) (hwf' : klongsWf n'.ks = true) (htimes' : ∀ s, Klong.time s ∈ n'.ks → s ≤ c.i)
    (hlive' : ∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c')
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hbv : Book BK c v) (hkv : KdInv KO BK v) (hgL : v.gh.lookup L = some (g, 0)) :
    LiveHoleW (pre ++ [cv]) g 0 c base v := by
  have hwf : klongsWf n.ks = true := hI.wf L n hn
  have htimes : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i := hI.times L n hn
  obtain ⟨hsubl, _⟩ := live_shrink n n' cv hlive'
  have e1 : n.liveAt c.i = n.live := KNode.liveAt_of_times n _ htimes
  have e2 : n'.liveAt c.i = n'.live := KNode.liveAt_of_times n' _ htimes'
  have hsub : ∀ q ∈ n'.liveAt c.i, q ∈ n.liveAt c.i := by
    rw [e1, e2]; exact hsubl
  have hpos : n'.liveAt c.i ≠ [] := by
    rw [e2]; exact live_ne_of_keep n n' cv hkeep hlive'
  have hE : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey (fun y => y = L) := by
    rw [hN, hvtop]
    exact liveEdgesH_leaf_shrink c.p _ _ _ L n n' (edges_of_liveCounts c.p _ _ _ hLC) hn hnl hn'l hsub hpos
  refine liveHoleW_of_hole (pre ++ [cv]) g 0 c _ v L hE ?_
  have hs := segRd_of _ BK c v hbv hkv hk
  have hwfw : ∀ x m, wNode c.p base w x = some m → klongsWf m.ks = true :=
    fun x m hm => hI.wf x m hm
  have hag2 : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      q.1 ≠ L → ∃ m, wNode c.p base w q.1 = some m ∧ rdN c v q.1 = some m := by
    intro q hq hqL
    obtain ⟨k, hk⟩ := fromVisits_reach_leaf _ _ _ cv L n hn hnl hwfw pre _ rk hrk hL q hq
    have hR : TReach (wNode c.p base w) c.i w.top.rootKey q.1 :=
      reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _ (fun x xn _ hx => hwfw x xn hx) _ _ q.1 q.2
        ReachS.root hq)
    obtain ⟨hkj, hqj⟩ := nodeAt_of_reach _ _ _ hI.tree P hlinkP q.1 L k hk hR P.length
      (Nat.le_refl _) hXD.symm
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, Nat.sub_zero, hXD] at hqj
      exact hqL hqj
    obtain ⟨_, m, _, hm0, _⟩ := LinkedFrom.get _ _ _ P hlinkP (P.length - k) (by omega)
    have hm : wNode c.p base w q.1 = some m := by rw [hqj]; exact hm0
    have hl3 : w3.nodes.lookup q.1 = some ((wNode c.p base w q.1).getD n) := by
      have := hlkX (P.length - k) (by omega)
      rw [← hqj] at this
      exact this
    rw [hm] at hl3
    exact ⟨m, hm, rdN_of_lookup _ v _ m (hnodes q.1 m hqL (hI.untaken _ (tReach_reachS _ _ _ _ hR)) hl3)⟩
  have hsearch : ∀ c', c' ≠ cv →
      (n.searchEq c.i c').map (·.y) = (n'.searchEq c.i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n c.i hwf htimes, KNode.searchEq_live n' c.i hwf' htimes', hlive' c']
    have : (c' == cv) = false := by simp [hc']
    rw [this]
    rfl
  have hdsr : ∃ P', pre.foldl (dsrStep (rdN c v) c.i c.p.fuel)
      (some (v.top.rootKey, [(none, v.top.rootKey)])) = some (rk, P') := by
    rw [hvtop]
    refine dsrFold_of_segRootR (wNode c.p base w) (rdN c v) _ _ cv pre w.top.rootKey _ rk ?_
      (keyWf_last_notin pre cv hkey) hrk
    intro q hq hq2
    by_cases hqL : q.1 = L
    · refine Or.inr ⟨n, n', by rw [hqL]; exact hn, by rw [hqL]; exact rdN_of_lookup _ v _ n' hlkv,
        hnl, hn'l, ?_⟩
      exact hsearch q.2 hq2
    · obtain ⟨m, hm, hr'⟩ := hag2 q hq hqL
      exact Or.inl (by rw [hm, hr'])
  have hlte : ∃ ext, lteP (rdN c v) c.i cv c.p.fuel rk = some (L, ext) :=
    lteP_of_eqVisits (wNode c.p base w) (rdN c v) _ cv L ⟨n', rdN_of_lookup _ v _ n' hlkv, hn'l⟩ _ rk hL
      (fun q hq m hm hqL => by
        obtain ⟨m', hm', hr'⟩ := hag2 q (fromVisits_append _ _ _ pre cv _ rk hrk q hq) hqL
        rw [hm] at hm'; cases hm'; exact hr')
  have hgL' : rdG c v L = some (g, 0) := by
    rw [rdG_of_lookup c v L n' hlkv]; exact hgL
  exact holeAtW_leaf c v pre cv rk L g 0 hs (keyWf_init_long pre cv hkey) hdsr hlte hgL'

/-! ## The leaf made by the transaction, full: split in time in place -/

/-- A delete, the merges on, whose leaf keeps a live klong, is full, and whose last
version without the key is no longer than a split's bound: the leaf splits in time
(in place if the transaction made it). -/
def DelFullTimeM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n ∧
    (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove

/-- The full leaf that the transaction made, split in time in place: its node
becomes its last version without the key. -/
theorem writerWP_appendDeleteKlong_fullMade (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (L : NodeId) (d cv : Nat) (n : KNode) (w : W) (hlk : w.nodes.lookup L = some n)
    (hLt : w.taken.contains L = false)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) (hfull : ¬ DelRoom c cv n)
    (hfirst : n.firstTime = some c.i)
    (hsz : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove) :
    WriterWP (appendDeleteKlong L d cv) c w (fun _ v => v.taken = w.taken ∧ v.top = w.top ∧
      ∀ y, wNode c.p base v y = if y = L then
        some ⟨n.leaf, (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩
        else wNode c.p base w y) := by
  refine writerWP_appendDeleteKlong_full_of L d cv n c w hlk hne hfull _ ?_
  intro compact s
  have hcs : (!compact && decide ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size >
      c.p.splitAbove)) = false := by
    have : ¬ ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size > c.p.splitAbove) := by
      omega
    simp [this]
  unfold handleFull
  refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ d L n _ compact c base hvc _ hlk hLt hfirst
    hcs) ?_
  rintro _ v ⟨hvt, hvtop, _, hvN⟩
  exact ⟨hvt, hvtop, fun y => by rw [hvN y]; rfl⟩

set_option maxHeartbeats 3200000 in
/-- The full leaf that the transaction made, split in time in place (bergdb 030-01,
step 5): the delete calls `afterDelete` at the leaf's pair (g, 0) from a state with
`DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`, the leaf the hole. -/
theorem liveDel_fullMade (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      (∀ pre' cv' L' n', op = .del (pre' ++ [cv']) →
        KeyLeaf (ctxOf p ts) (viewOf (treeRun p ts)) w pre' cv' L' n' → n'.firstTime = some (ts.length + 1)) →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hmade Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0, hsz0⟩ := hPc
  have hmade0 := hmade pre cv L0 n0 hop' hK
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hLC0 : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.2.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, hbw, hiw, hwfw0⟩ := hS.2.1
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧
      HtJ0 (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base v)
    (fun s f x v hJ hx => writerWP_and (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ.1 hx)
      (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ.1 hL hlk
        (kd_searchEq_mem n _ s fd hfd), htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0, htJ0_start hvo w hbw hiw hwfw0⟩
    hrk (hI.pathUntaken _) hI.wf _ hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hH3.book hlk3
  obtain ⟨hne, hkeep, hfull, hsz, hmadeL⟩ := keyLeaf_all2 hK hrk
    (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m ∧
      (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∧ m.firstTime = some (ts.length + 1))
    ⟨hne0, hkeep0, hfull0, hsz0, hmade0⟩ L n hL hn hnl
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have h3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
  have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
  have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
    (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
    (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
    (by rw [hr03.1, hr03.2.1]; exact hRO) hJ3' (by rw [hr03.2.2.2.2]; exact hSB) hsa2
    P.length _ _ _ hPOK cv n (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
    hnl hne hfull (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
  simp only [hXD] at hJ2
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
  have hlastl : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlastN : (⟨n.leaf, last.ks⟩ : KNode) = last := by rw [← hlastl]
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧ Kept w3 v ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧
      ∀ y, wNode p (viewOf (treeRun p ts)) v y = if y = L then some last
        else wNode p (viewOf (treeRun p ts)) w3 y)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp))))
      (writerWP_appendDeleteKlong_fullMade (ctxOf p ts) _ (viewCoherent_ctxOf p ts) L P.length cv n w3 hlk3 h3t
        hne hfull hmadeL hsz)) ?_
    rintro _ v ⟨⟨⟨⟨hDT, hJv⟩, hpbv⟩, ⟨_, hhiv, hlev, _⟩⟩, hvt, hvtop, hvN⟩
    refine ⟨⟨hDT, hJv⟩, hpbv, hhiv, hlev.1, hvt, hvtop, fun y => ?_⟩
    have := hvN y
    rw [show (ctxOf p ts).p = p from rfl] at this
    rw [this, hlast, hlastN]
  · intro g h v hgh ⟨hD, hpbv, hhiv, hkept, hvt, hvtop, hvN⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    apply hA g v hD hpbv hhiv
    have hbv : Book tx.base (ctxOf p ts) v := hD.1.2.2.2.2.2.1
    have hkv : KdInv (kindOracleOf p (treeRun p ts)) tx.base v := hD.1.2.2.2.2.2.2
    have hvt' : v.taken.contains L = false := by rw [hvt]; exact h3t
    have hN : wNode p (viewOf (treeRun p ts)) v = updN (wNode p (viewOf (treeRun p ts)) w) L last := by
      funext y
      rw [hvN y]
      unfold updN
      split
      · rfl
      · exact congrFun hr03.1 y
    have hlkv : v.nodes.lookup L = some last := by
      obtain ⟨m, hm, _⟩ := hkept.1 L n hlk3
      have h1 : wNode p (viewOf (treeRun p ts)) v L = some m := by
        simp only [wNode, hvt', Bool.false_eq_true, ↓reduceIte, hm]
      rw [hvN L] at h1
      simp only [↓reduceIte, Option.some.injEq] at h1
      rw [hm, h1]
    have hnodes : ∀ q m, q ≠ L → w.taken.contains q = false → w3.nodes.lookup q = some m →
        v.nodes.lookup q = some m := by
      intro q m hqL hqt hq
      have hqt3 : w3.taken.contains q = false := by rw [hr03.2.2.1]; exact hqt
      have hqtv : v.taken.contains q = false := by rw [hvt]; exact hqt3
      obtain ⟨m', hm', _⟩ := hkept.1 q m hq
      have h1 : wNode p (viewOf (treeRun p ts)) v q = some m' := by
        simp only [wNode, hqtv, Bool.false_eq_true, ↓reduceIte, hm']
      have h2 : wNode p (viewOf (treeRun p ts)) w3 q = some m := by
        simp only [wNode, hqt3, Bool.false_eq_true, ↓reduceIte, hq]
      rw [hvN q] at h1
      simp only [hqL, ↓reduceIte] at h1
      rw [h2] at h1
      rw [hm', h1]
    have hgL : v.gh.lookup L = some (g, 0) :=
      lookup_of_mem_nodup _ hbv.nodup L (g, 0) (hkept.2 _ (bk_mem_of_lookup _ _ _ hgh))
    have hlive' : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' := by
      intro c'; rw [← hlast]; exact KNode.delete_live_lookup n _ cv c'
    have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ (ctxOf p ts).i := by
      intro s hs
      rw [← hlast] at hs
      simp only [KNode.lastVersionGivenDel, List.mem_cons, List.mem_map] at hs
      rcases hs with he | ⟨_, _, he⟩
      · cases he; exact Nat.le_refl _
      · cases he
    exact liveHoleW_leafChange (ctxOf p ts) _ _ tx.base hk w w3 v pre cv rk L n last P g hI hLC0 hrk hL hn hnl
      hkey hlinkP hXD hlkX hN (hvtop.trans hr03.2.1) hlkv hnodes (by rw [hlastl]; exact hnl)
      (by rw [← hlast]; exact KNode.lastVersionGivenDel_wf _ _ _) htl hlive' hkeep hbv hkv hgL

/-- The full leaf that the transaction made keeps the live counts (bergdb 030-01,
steps 5, 3 and 4), with the merges' loop and root collapse from the hole, given
its live merge and root collapse (`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullMade_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hML : ∀ ts (tx : Tx), MergeLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts)))
    (hCL : ∀ ts (tx : Tx), CollapseLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      (∀ pre' cv' L' n', op = .del (pre' ++ [cv']) →
        KeyLeaf (ctxOf p ts) (viewOf (treeRun p ts)) w pre' cv' L' n' → n'.firstTime = some (ts.length + 1)) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc hmade
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨_, _, _, _, _, hm, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_fullMade p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key
    hop hPc hmade _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
