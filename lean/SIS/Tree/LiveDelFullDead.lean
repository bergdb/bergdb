/-
The delete's full leaf whose bitmap compacts ("bitmap.dead", "bitmap.inplace.dead"),
its last version without the key larger than a split's bound (bergdb 030-01,
step 5): a compacting split is in time, so the cases of a time split carry over,
with the split's kind taken from the bitmap's path (`writerWP_appendDeleteKlong_full_ofP`)
instead of the last version's size. `DelFullTimeGM` widens `DelFullTimeM` by
that path.
-/
import SIS.Tree.LiveDelFullCopy

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `writerWP_appendDeleteKlong_full_of` with the bitmap's path: the split is not
compacting only when the node's last klong is no bitmap of the transaction and
the node has no room for one ("bitmap.full"). -/
theorem writerWP_appendDeleteKlong_full_ofP (x : NodeId) (d cv : Nat) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) (hfull : ¬ DelRoom c cv n)
    (Q : W → Prop)
    (hQ : ∀ (compact : Bool) (s : String),
      (compact = false → ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
        c.p.M ≤ n.size + 1) →
      WriterWP (handleFull d x (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c
        ({ w with trail := s :: w.trail } : W) (fun _ v => Q v)) :
    WriterWP (appendDeleteKlong x d cv) c w (fun _ v => Q v) := by
  have hhf : ∀ (compact : Bool) (s : String),
      (compact = false → ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
        c.p.M ≤ n.size + 1) → WriterWP (do
      note s
      handleFull d x (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact
      pure false) c w (fun _ v => Q v) := by
    intro compact s hpath
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (hQ compact s hpath) ?_
    intro _ v hv
    simp only [writerWP_pure]; exact hv
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
    simp only [hno, Bool.not_false, ↓reduceIte]
    apply writerWP_if
    · intro htd
      apply writerWP_if
      · intro _; exact hhf true _ (fun h => by cases h)
      · intro hdead
        exfalso; apply hfull; left
        have hdead' : deadOver c.p (n.setAt (n.size - 1)
            (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by simpa using hdead
        cases hgl : n.ks.getLast? with
        | none => simp [hgl] at htd
        | some k =>
          cases k with
          | del old =>
            simp [hgl] at htd
            exact ⟨⟨old, rfl⟩, htd, hdead'⟩
          | time t => simp [hgl] at htd
          | key a y => simp [hgl] at htd
    · intro htd
      apply writerWP_if
      · intro hroom
        apply writerWP_if
        · intro _; exact hhf true _ (fun h => by cases h)
        · intro hdead
          exfalso; apply hfull; right
          refine ⟨?_, hroom, ?_⟩
          · rintro ⟨⟨old, hold⟩, hlt'⟩
            apply htd
            simp [hold, hlt']
          · simpa using hdead
      · intro hnoroom
        refine hhf false _ (fun _ => ⟨?_, by omega⟩)
        rintro ⟨⟨old, hold⟩, hlt'⟩
        apply htd
        simp [hold, hlt']

/-- `DelFullTimeM` with the split's kind from the bitmap's path: the last version
without the key within a split's bound, or a compacting bitmap (the transaction's
bitmap last, or room for a new one): either way the split is in time. -/
def DelFullTimeGM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n ∧
    ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove ∨
      ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∨ n.size + 1 < c.p.M)

/-- The split of a last version with a time-split path is not a space split. -/
theorem compact_time_of_path (n : KNode) (c : Ctx) (cv : Nat) (compact : Bool)
    (hsz : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove ∨
      ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∨ n.size + 1 < c.p.M)
    (hpath : compact = false → ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1) :
    (!compact && decide ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size >
      c.p.splitAbove)) = false := by
  cases compact with
  | true => rfl
  | false =>
    obtain ⟨h1, h2⟩ := hpath rfl
    have : ¬ ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size > c.p.splitAbove) := by
      rcases hsz with h | h | h
      · omega
      · exact absurd h h1
      · omega
    simp [this]

/-- `writerWP_appendDeleteKlong_fullMade` with the split's kind from the bitmap's
path (`DelFullTimeGM`). -/
theorem writerWP_appendDeleteKlong_fullMadeG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (L : NodeId) (d cv : Nat) (n : KNode) (w : W) (hlk : w.nodes.lookup L = some n)
    (hLt : w.taken.contains L = false)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) (hfull : ¬ DelRoom c cv n)
    (hfirst : n.firstTime = some c.i)
    (hsz : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove ∨
      ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∨ n.size + 1 < c.p.M) :
    WriterWP (appendDeleteKlong L d cv) c w (fun _ v => v.taken = w.taken ∧ v.top = w.top ∧
      ∀ y, wNode c.p base v y = if y = L then
        some ⟨n.leaf, (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩
        else wNode c.p base w y) := by
  refine writerWP_appendDeleteKlong_full_ofP L d cv n c w hlk hne hfull _ ?_
  intro compact s hpath
  have hcs := compact_time_of_path n c cv compact hsz hpath
  unfold handleFull
  refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ d L n _ compact c base hvc _ hlk hLt hfirst
    hcs) ?_
  rintro _ v ⟨hvt, hvtop, _, hvN⟩
  exact ⟨hvt, hvtop, fun y => by rw [hvN y]; rfl⟩

set_option maxHeartbeats 3200000 in
/-- `liveDel_fullMade` with the split's kind from the bitmap's path (`DelFullTimeGM`):
the full leaf that the transaction made, split in time in place (bergdb 030-01,
step 5): the delete calls `afterDelete` at the leaf's pair (g, 0) from a state with
`DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`, the leaf the hole. -/
theorem liveDel_fullMadeG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeGM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
      ((m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∨ ((∃ old, m.ks.getLast? = some (.del old)) ∧
        m.lastTime = some (ctxOf p ts).i) ∨ m.size + 1 < (ctxOf p ts).p.M) ∧ m.firstTime = some (ts.length + 1))
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
      (writerWP_appendDeleteKlong_fullMadeG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) L P.length cv n w3 hlk3 h3t
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

/-- `liveDel_fullMade_live` with the split's kind from the bitmap's path: the full
leaf that the transaction made keeps the live counts (bergdb 030-01,
steps 5, 3 and 4), with the merges' loop and root collapse from the hole, given
its live merge and root collapse (`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullMadeG_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelFullTimeGM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
  refine liveDel_fullMadeG p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key
    hop hPc hmade _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

/-! ## The case: the full leaf split in time below a parent with room, any time-split path -/

/-- A full leaf as in `DelFullTimeGM`, not made by the transaction, below the space
root, whose parent has room for the copy's klong. -/
def DelFullTimeRoomGM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeGM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false

set_option maxHeartbeats 6400000 in
/-- The full leaf not made by the transaction, split in time below a parent with
room (bergdb 030-01, step 5): the delete calls `afterDelete` at the leaf's pair
(g, 0) from a state with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`,
the copy the hole (l4a's `writerWP_handleFull_timeRoom_liveGh`, `holeAtW_copy`). -/
theorem liveDel_fullTimeRoomG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeRoomGM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0, hsz0⟩, hcase⟩ := hPc
  obtain ⟨hnm0, hnr0, hpar0⟩ := hcase pre cv L0 n0 hop' hK
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
  obtain ⟨hne, hkeep, hfull, hsz, hnm, hnr, hpar⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m ∧
      ((m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∨ ((∃ old, m.ks.getLast? = some (.del old)) ∧
        m.lastTime = some (ctxOf p ts).i) ∨ m.size + 1 < (ctxOf p ts).p.M) ∧
      m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.size + 2 ≤ (ctxOf p ts).p.M ∧
          deadOver (ctxOf p ts).p (qn.add (ctxOf p ts).i (.key k1 w.next)) = false)
    ⟨hne0, hkeep0, hfull0, hsz0, hnm0, hnr0, hpar0⟩ L n hL hn hnl
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
  -- the path: L below its parent q
  have hPpos : 0 < P.length := by
    cases hPe : P with
    | nil => rw [hPe] at hXD; simp [nodeAt] at hXD; exact absurd hXD.symm hnr
    | cons _ _ => simp
  obtain ⟨d', hd'⟩ : ∃ d', P.length = d' + 1 := ⟨P.length - 1, by omega⟩
  obtain ⟨kq, qm, hPq, hqm, hkq⟩ := LinkedFrom.get _ _ _ P hlinkP d' (by omega)
  rw [← hd', hXD] at hPq hkq
  have hqR : TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey (nodeAt w.top.rootKey P d') :=
    (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega)).reach
  obtain ⟨hroom, hdead⟩ := hpar _ qm kq hqR hqm hkq
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
  have hlastl : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlastN : (⟨n.leaf, last.ks⟩ : KNode) = last := by rw [← hlastl]
  have hlive' : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [← hlast]; exact KNode.delete_live_lookup n _ cv c'
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ (ctxOf p ts).i := by
    intro s hs
    rw [← hlast] at hs
    simp only [KNode.lastVersionGivenDel, List.mem_cons, List.mem_map] at hs
    rcases hs with he | ⟨_, _, he⟩
    · cases he; exact Nat.le_refl _
    · cases he
  have hwfl : klongsWf last.ks = true := by rw [← hlast]; exact KNode.lastVersionGivenDel_wf _ _ _
  have htn := hI.times L n hn
  obtain ⟨hsubl, _⟩ := live_shrink n last cv hlive'
  have hsub : ∀ q ∈ last.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
    rw [KNode.liveAt_of_times n (ts.length + 1) htn, KNode.liveAt_of_times last (ts.length + 1) htl]; exact hsubl
  have hposl : last.liveAt (ts.length + 1) ≠ [] := by
    rw [KNode.liveAt_of_times last (ts.length + 1) htl]; exact live_ne_of_keep n last cv hkeep hlive'
  -- names
  generalize hqdef : nodeAt w.top.rootKey P d' = q at hqm hkq hqR hroom hdead hPq
  have hqL : q ≠ L := by
    intro he
    rw [← hqdef, ← hXD] at he
    have := PathLen.depth_unique hI.tree _ _ _ (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega))
      (by rw [he]; exact LinkedFrom.pathLen _ _ _ P hlinkP P.length (Nat.le_refl _))
    omega
  have hqt : w.taken.contains q = false := hI.untaken q (tReach_reachS _ _ _ _ hqR)
  have hlq3 : w3.nodes.lookup q = some qm := by
    have := hlkX d' (by omega)
    rw [hqdef, hqm] at this
    exact this
  have hnx3 : w3.nodes.lookup w3.next = none := by
    cases h' : w3.nodes.lookup w3.next with
    | none => rfl
    | some m => have := hI3.ids.1 w3.next (by rw [h']; rfl); omega
  have hnt3 : w3.taken.contains w3.next = false := by
    cases h' : w3.taken.contains w3.next with
    | false => rfl
    | true => have := hI3.ids.2.2.1 w3.next h'; omega
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hNw3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
  -- the split's live part
  have hlive : WriterWP (appendDeleteKlong L P.length cv) (ctxOf p ts) w3 (fun _ v =>
      LiveEdgesH p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey (fun z => z = w3.next) ∧
      (∀ z, z ≠ q → z ≠ L → z ≠ w3.next → v.nodes.lookup z = w3.nodes.lookup z) ∧
      v.nodes.lookup w3.next = some last ∧
      v.nodes.lookup q = some (qm.add (ts.length + 1) (.key kq w3.next)) ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ v.gh.lookup w3.next = w3.gh.lookup L) := by
    refine writerWP_appendDeleteKlong_full_ofP L P.length cv n _ w3 hlk3 hne hfull _ ?_
    intro compact s hpath
    generalize hw4 : ({ w3 with trail := s :: w3.trail } : W) = w4
    have h4n : w4.nodes = w3.nodes := by rw [← hw4]
    have h4t : w4.taken = w3.taken := by rw [← hw4]
    have h4top : w4.top = w3.top := by rw [← hw4]
    have h4next : w4.next = w3.next := by rw [← hw4]
    have h4path : w4.path = w3.path := by rw [← hw4]
    have h4gh : w4.gh = w3.gh := by rw [← hw4]
    have hN4 : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 = wNode p (viewOf (treeRun p ts)) w := by
      rw [← hNw3]; unfold wNode; rw [h4n, h4t]; rfl
    have hroot4 : w4.top.rootKey = w.top.rootKey := by rw [h4top, hr03.2.1]
    have hcs : (!compact && decide (last.size > (ctxOf p ts).p.splitAbove)) = false := by
      rw [← hlast]; exact compact_time_of_path n (ctxOf p ts) cv compact hsz hpath
    rw [hlast]
    unfold handleFull
    rw [hd']
    have hn' : wNode p (viewOf (treeRun p ts)) w L = some n := hn
    have hTu : TreeOK (updN (wNode p (viewOf (treeRun p ts)) w) L n) (ts.length + 1) w.top.rootKey := by
      rw [updN_self_eq _ _ _ hn']; exact hI.tree
    obtain ⟨hTl, hRl⟩ := treeOK_updN_sub _ _ _ L n ⟨n.leaf, last.ks⟩ hTu
      (by rw [hlastN]; exact fun c z h => hsub (c, z) h)
    rw [updN_self_eq _ _ _ hn'] at hRl
    refine writerWP_mono (writerWP_handleFull_timeRoom_liveGh d' L q n qm kq last compact (ctxOf p ts)
      (viewOf (treeRun p ts)) w4
      (by rw [h4n]; exact hlk3) (by rw [h4t]; exact h3t) (by rw [h4n]; exact hlq3)
      (by rw [h4t, hr03.2.2.1]; exact hqt) hqL
      (by rw [h4next]; exact hI3.ids.1 L (by rw [hlk3]; rfl))
      (by rw [h4next]; exact hI3.ids.1 q (by rw [hlq3]; rfl)) hnm hcs
      (by
        rw [h4path, hp3']
        rw [← hqdef]
        simp only [nodeAt]
        cases d' with
        | zero => simp
        | succ e =>
          rw [List.getElem?_cons_succ]
          have hl : e < (P.map (·.2)).length := by simp; omega
          rw [← List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
          simp [List.getElem?_eq_getElem hl])
      (by rw [h4path, hp3', List.getElem?_cons_succ]; exact hPq)
      (hI.wf q qm hqm) (hI.times q qm hqm) hroom (by rw [h4next, hnext3]; exact hdead) hkq
      (by rw [hN4, hroot4]; exact hTl)
      (by
        rw [hN4, hroot4, ← hXD, ← hqdef]
        exact reach_path_updN_end _ _ _ P hlinkP hI.tree _ d' (by omega))
      (by
        simp only [wNode, h4t, hnt3, h4n, h4next, hnx3, Bool.false_eq_true, ↓reduceIte]
        exact (hI3.fresh w3.next (Nat.le_refl _)).1)
      (by rw [h4n, h4next]; exact hnx3) (by rw [h4t, h4next]; exact hnt3)
      (by
        rw [hN4, hroot4, h4next]
        intro u c' hu hl
        obtain ⟨mm, hmm, hcm⟩ := hl
        have huN := hRl u hu
        have hcm' : (c', w3.next) ∈ (Option.getD (wNode p (viewOf (treeRun p ts)) w u) n).liveAt (ts.length + 1) ∧
            wNode p (viewOf (treeRun p ts)) w u = some ((wNode p (viewOf (treeRun p ts)) w u).getD n) := by
          by_cases huL : u = L
          · rw [huL, updN_self] at hmm
            cases hmm
            rw [huL, hn']
            refine ⟨hsub _ (by rw [← hlastN]; exact hcm), rfl⟩
          · rw [updN_ne _ _ _ _ huL] at hmm
            rw [hmm]
            exact ⟨hcm, rfl⟩
        have := hI.links u _ c' w3.next (tReach_reachS _ _ _ _ huN) hcm'.2 hcm'.1
        rw [hnext3] at this
        omega)
      (by
        rw [hN4, hroot4]
        rw [hlastN]
        exact liveEdgesH_leaf_shrink p _ _ _ L n last (edges_of_liveCounts p _ _ _ hLC0) hn hnl
          (by rw [hlastl]; exact hnl) hsub hposl)) ?_
    rintro _ v ⟨hE, hfr, hny, hqv, hvt, hvtop, _, _, hgh, _⟩
    rw [h4next] at hE hfr hny hqv hgh
    refine ⟨hE, fun z h1 h2 h3 => by rw [hfr z h1 h2 h3, h4n], by rw [hny, hlastN], hqv,
      by rw [hvt, h4t], by rw [hvtop, h4top], by rw [hgh, h4gh]⟩
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧
      LiveEdgesH p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey (fun z => z = w3.next) ∧
      (∀ z, z ≠ q → z ≠ L → z ≠ w3.next → v.nodes.lookup z = w3.nodes.lookup z) ∧
      v.nodes.lookup w3.next = some last ∧
      v.nodes.lookup q = some (qm.add (ts.length + 1) (.key kq w3.next)) ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ v.gh.lookup w3.next = w3.gh.lookup L)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp)))) hlive) ?_
    rintro _ v ⟨⟨⟨⟨hDT, hJv⟩, hpbv⟩, ⟨_, hhiv, _, _⟩⟩, hE, hfr, hny, hqv, hvt, hvtop, hgh⟩
    exact ⟨⟨hDT, hJv⟩, hpbv, hhiv, hE, hfr, hny, hqv, hvt, hvtop, hgh⟩
  · intro g h v hgh ⟨hD, hpbv, hhiv, hE, hfr, hny, hqv, hvt, hvtop, hghn⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    apply hA g v hD hpbv hhiv
    refine liveHoleW_of_hole (pre ++ [cv]) g 0 (ctxOf p ts) _ v w3.next hE ?_
    have hbv : Book tx.base (ctxOf p ts) v := hD.1.2.2.2.2.2.1
    have hkv : KdInv (kindOracleOf p (treeRun p ts)) tx.base v := hD.1.2.2.2.2.2.2
    have hs := segRd_of _ tx.base (ctxOf p ts) v hbv hkv hk
    have hgy : rdG (ctxOf p ts) v w3.next = some (g, 0) := by
      rw [rdG_of_lookup _ v _ last hny, hghn]; exact hgh
    have hqv' : v.nodes.lookup (nodeAt w.top.rootKey P (P.length - 1)) =
        some (((wNode p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P (P.length - 1))).getD n).add
          (ctxOf p ts).i (.key (((P[P.length - 1]?).bind (·.1)).getD 0) w3.next)) := by
      have e1 : P.length - 1 = d' := by omega
      have hqm' : wNode p (viewOf (treeRun p ts)) w q = some qm := hqm
      rw [e1, hqdef, hqm']
      have e2 : ((P[d']?).bind (·.1)).getD 0 = kq := by rw [hPq]; rfl
      rw [e2]
      exact hqv
    exact holeAtW_copy (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w w3 v pre cv rk L n P w3.next g last
      hI.tree (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hI.times hrk hL hn hnl hr03 hp3'
      hlinkP hXD hlkX hkey hPpos hqv' hny (by rw [hlastl]; exact hnl) hnx3
      (fun z h1 h2 h3 => hfr z (by
        intro he; apply h1; rw [he, ← hqdef]; congr 1; omega) h2 h3) (hvtop.trans rfl) hs hgy

/-- The full leaf not made by the transaction, split in time below a parent with
room, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with the merges'
loop and root collapse from the hole, given its live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullTimeRoomG_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelFullTimeRoomGM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨⟨_, _, _, _, _, hm, _⟩, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_fullTimeRoomG p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ
    key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
