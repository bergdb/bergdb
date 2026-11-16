/-
The delete's full leaf not made by the transaction, split in space below an inner
parent with room (bergdb 030-01, step 5): the leaf's last version without the key
splits into two halves, new nodes that the parent names by the leaf's klong and
the divider instead. Both halves hold m live klongs and more (`MergeParamsOK`), so
the live counts hold after with no hole (`liveEdgesX_spaceSplit_gen`), and the
merges' loop starts from them.
-/
import SIS.Tree.LiveDelFullCopy
import SIS.Tree.GetCascadePut
import SIS.Tree.LiveStepsX
import SIS.Tree.SplitLiveFill
import SIS.Tree.PutInvSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A space split's halves are of the split node's kind. -/
theorem halves_leaf_eq (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.leaf = leaf ∧ (halves leaf t last ins).2.1.leaf = leaf := by
  unfold halves
  dsimp only
  constructor <;> (repeat' split) <;> rfl

/-- The halves of a delete's last version (`lastVersionGivenDel`) larger than h
hold m live klongs and more: `HalfOK` with the merges' thresholds. -/
theorem halves_del_halfOK (p : Params) (hp : MergeParamsOK p) (n : KNode) (t : Time) (del : List Nat)
    (hfull : p.splitAbove < (n.lastVersionGivenDel t del).size) :
    HalfOK p t (halves n.leaf t (n.lastVersionGivenDel t del) []).1 ∧
      HalfOK p t (halves n.leaf t (n.lastVersionGivenDel t del) []).2.1 := by
  obtain ⟨h1, h2⟩ := halves_lastVersionGivenDel_live_fill p hp n t del [] hfull
  have hfa := halves_flatAt n.leaf t (n.lastVersionGivenDel t del) []
    (KNode.lastVersionGivenDel_flat n t del)
  have ht1 := flatAt_times t _ hfa.1
  have ht2 := flatAt_times t _ hfa.2
  have hm : 2 ≤ p.mergeBelow := hp.1
  have hc1 : p.mergeBelow ≤ ((halves n.leaf t (n.lastVersionGivenDel t del) []).1.liveAt t).length := by
    rw [KNode.liveAt_of_times _ t ht1]; exact h1
  have hc2 : p.mergeBelow ≤ ((halves n.leaf t (n.lastVersionGivenDel t del) []).2.1.liveAt t).length := by
    rw [KNode.liveAt_of_times _ t ht2]; exact h2
  refine ⟨⟨fun hE => ?_, by omega, fun _ => hc1⟩, ⟨fun hE => ?_, by omega, fun _ => hc2⟩⟩
  · rw [hE] at hc1; simp at hc1; omega
  · rw [hE] at hc2; simp at hc2; omega

/-- `appendDeleteKlong` on a full node with no bitmap of the transaction last and
no room for one (note "bitmap.full"): the split of its last version without the
key, not compacting. -/
theorem writerWP_appendDeleteKlong_bitmapFull (x : NodeId) (d cv : Nat) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (htd : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i))
    (hsz : c.p.M ≤ n.size + 1) (Q : W → Prop)
    (hQ : WriterWP (handleFull d x (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)))
      false) c ({ w with trail := "bitmap.full" :: w.trail } : W) (fun _ v => Q v)) :
    WriterWP (appendDeleteKlong x d cv) c w (fun _ v => Q v) := by
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
    simp only [hno, Bool.not_false, ↓reduceIte]
    apply writerWP_if
    · intro h
      exfalso; apply htd
      cases hgl : n.ks.getLast? with
      | none => simp [hgl] at h
      | some k =>
        cases k with
        | del old =>
          simp [hgl] at h
          exact ⟨⟨old, rfl⟩, h⟩
        | time t => simp [hgl] at h
        | key a y => simp [hgl] at h
    · intro _
      apply writerWP_if
      · intro h; exfalso; omega
      · intro _
        simp only [note, writerWP_bind, writerWP_modify]
        refine writerWP_mono hQ ?_
        intro _ v hv
        simp only [writerWP_pure]; exact hv

set_option maxHeartbeats 4000000 in
/-- A full node x that the transaction did not make, split in space with a last
version given (a delete's), below an inner parent q with room for the halves'
klongs: from the live counts at the start, with halves that are `HalfOK` and hold
x's live klongs, they hold after, with no hole. -/
theorem writerWP_handleFull_spaceRoom_live (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hlq : w.nodes.lookup q = some qn) (hqt : w.taken.contains q = false) (hqx : q ≠ x)
    (hxn : x < w.next) (hqn : q < w.next)
    (hfirst : n.firstTime ≠ some c.i) (hql : qn.leaf = false)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hroom : qn.size + 3 ≤ c.p.M)
    (hdead : deadOver c.p ([(k1, w.next), ((halves n.leaf c.i last []).2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false)
    (hk : (k1, x) ∈ qn.liveAt c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hqR : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hn1 : wNode c.p base w w.next = none) (hn2 : wNode c.p base w (w.next + 2) = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (hlinks : ∀ u c' z, TReach (wNode c.p base w) c.i w.top.rootKey u →
      TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hf : ∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).1.liveAt c.i →
      c' < (halves n.leaf c.i last []).2.2 ∧ (c', z) ∈ n.liveAt c.i)
    (hs : ∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves n.leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv n.leaf (halves n.leaf c.i last []).2.2 c0 ∧ (c0, z) ∈ n.liveAt c.i)
    (hfH : HalfOK c.p c.i (halves n.leaf c.i last []).1)
    (hsH : HalfOK c.p c.i (halves n.leaf c.i last []).2.1)
    (hL : LiveEdges c.p (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x [] last false) c w
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  have hqy1 : q ≠ w.next := by omega
  have hqy2 : q ≠ w.next + 2 := by omega
  have hxy1 : x ≠ w.next := by omega
  have hxy2 : x ≠ w.next + 2 := by omega
  have h12 : w.next ≠ w.next + 2 := by omega
  obtain ⟨hfl, hsl⟩ := halves_leaf_eq n.leaf c.i last []
  apply writerWP_handleFullWith_space_up_last d' x q n qn k1 last c w hlk hlq hql hfirst hsplit hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  generalize hout : halves n.leaf c.i last [] = out at hdead hf hs hfH hsH hfl hsl h1n ⊢
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n]; simp only [hqy1, hqy2, ↓reduceIte]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_addKeys d' q qn _ c w1 hlq1 (by simp; omega) hdead) ?_
  intro _ w2 hw2
  have h2n : w2.nodes = upsert w1.nodes q ([(k1, w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by rw [hw2]
  have h2t : w2.taken = w1.taken := by rw [hw2]
  have h2top : w2.top = w1.top := by rw [hw2]
  have hlx2 : w2.nodes.lookup x = some n := by
    rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n]
    simp only [hxy1, hxy2, ↓reduceIte]; exact hlk
  rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
  simp only [putNode, writerWP_modify]
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
      w3.top = w2.top → LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    intro w3 h3n h3t0 h3top0
    have h3t : w3.taken = w.taken := by rw [h3t0, h2t, h1t]
    have h3top : w3.top = w.top := by rw [h3top0, h2top, h1top]
    have hlook : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → z ≠ w.next + 2 →
        w3.nodes.lookup z = w.nodes.lookup z := by
      intro z hzx hzq hz1 hz2
      rw [h3n, lookup_upsert, if_neg hzx, h2n, lookup_upsert, if_neg hzq, h1n]
      simp only [hz1, hz2, ↓reduceIte]
    have hqn' : wNode c.p base w q = some qn := by
      simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hlq]
    have hLn : wNode c.p base w x = some n := by
      simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
    have hN'q : wNode c.p base w3 q = some ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
      have hl : w3.nodes.lookup q = some ([(k1, w.next), (out.2.2, w.next + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
        rw [h3n, lookup_upsert, if_neg hqx, h2n, lookup_upsert]; simp
      have ht : w3.taken.contains q = false := by rw [h3t]; exact hqt
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN'1 : wNode c.p base w3 w.next = some out.1 := by
      have hl : w3.nodes.lookup w.next = some out.1 := by
        rw [h3n, lookup_upsert, if_neg (Ne.symm hxy1), h2n, lookup_upsert, if_neg (Ne.symm hqy1), h1n]
        simp
      have ht : w3.taken.contains w.next = false := by rw [h3t]; exact ht1
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN'2 : wNode c.p base w3 (w.next + 2) = some out.2.1 := by
      have hl : w3.nodes.lookup (w.next + 2) = some out.2.1 := by
        rw [h3n, lookup_upsert, if_neg (Ne.symm hxy2), h2n, lookup_upsert, if_neg (Ne.symm hqy2), h1n]
        simp
      have ht : w3.taken.contains (w.next + 2) = false := by rw [h3t]; exact ht2
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hother : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → z ≠ w.next + 2 →
        wNode c.p base w3 z = wNode c.p base w z := by
      intro z hzx hzq hz1 hz2
      simp only [wNode, h3t, hlook z hzx hzq hz1 hz2]
    have hq1wf := KNode.add_key_wf qn c.i k1 w.next hqwf
    have hq1t := KNode.add_times qn c.i (.key k1 w.next) (fun s h => by cases h) hqtm
    have hq' : ∀ c' z, (c', z) ∈ ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn).liveAt c.i →
        (c' = out.2.2 ∧ z = w.next + 2) ∨ (c' ≠ out.2.2 ∧ c' = k1 ∧ z = w.next) ∨
        (c' ≠ out.2.2 ∧ c' ≠ k1 ∧ (c', z) ∈ qn.liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtm c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hq'l : ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn).leaf = qn.leaf := by
      simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
    have hgen := liveEdgesX_spaceSplit_gen c.p (fun _ => False) (wNode c.p base w) (wNode c.p base w3)
      c.i w.top.rootKey q x w.next (w.next + 2) qn n out.1 out.2.1
      ([(k1, w.next), (out.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn)
      k1 out.2.2 (splitLocalCv n.leaf out.2.2) hT hqR hqn' hk hLn hN'q hq' hN'1 hN'2 hf hs
      (fun z h1 h2 h3 h4 => hother z h1 h2 h3 h4) hn1 hn2 h12
      (by
        intro z hz u c' hu hl
        have := hlinks u c' z hu hl
        rcases hz with hz | hz <;> omega)
      (fun h => h) (fun h => h) hfl hsl hfH hsH hq'l
      (addKeys_liveAt_length c.i [(k1, w.next), (out.2.2, w.next + 2)] qn hqwf hqtm)
      ((liveEdgesX_false_iff _ _ _ _).mpr hL)
    rw [h3top]
    exact (liveEdgesX_false_iff _ _ _ _).mp hgen
  exact key _ rfl rfl rfl

/-! ## The case: the full leaf split in space below an inner parent with room -/

/-- A delete, the merges on, whose leaf keeps a live klong, is full with no bitmap
of the transaction last ("bitmap.full"), and whose last version without the key is
larger than a split's bound: the leaf, not made by the transaction and below the
space root, splits in space; its parent is inner and has room for the halves'
klongs. -/
def DelFullSpaceRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
    ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧ c.p.M ≤ n.size + 1 ∧
    c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.leaf = false ∧ qn.size + 3 ≤ c.p.M ∧
      deadOver c.p ([(k1, w.next), ((halves n.leaf c.i
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false

set_option maxHeartbeats 4000000 in
/-- The full leaf not made by the transaction, split in space below an inner
parent with room, calls `afterDelete` with the live counts (no hole), in the
stratum (bergdb 030-01, step 5): any `afterDelete` that keeps the live counts from
the hole at (g, 0) gives them after. -/
theorem liveDel_fullSpaceRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullSpaceRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, htd0, hsz0, hsp0, hnm0, hnr0, hpar0⟩ := hPc
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
  obtain ⟨hne, hkeep, htd, hsz, hsp, hnm, hnr, hpar⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧
      ¬ ((∃ old, m.ks.getLast? = some (.del old)) ∧ m.lastTime = some (ctxOf p ts).i) ∧
      (ctxOf p ts).p.M ≤ m.size + 1 ∧
      (ctxOf p ts).p.splitAbove <
        (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ∧
      m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.leaf = false ∧ qn.size + 3 ≤ (ctxOf p ts).p.M ∧
        deadOver (ctxOf p ts).p ([(k1, w.next), ((halves m.leaf (ctxOf p ts).i
          (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))) []).2.2,
            w.next + 2)].foldl (fun n (cv, y) => n.add (ctxOf p ts).i (.key cv y)) qn) = false)
    ⟨hne0, hkeep0, htd0, hsz0, hsp0, hnm0, hnr0, hpar0⟩ L n hL hn hnl
  have hfull : ¬ DelRoom (ctxOf p ts) cv n := by
    rintro (⟨h1, h2, _⟩ | ⟨_, h2, _⟩)
    · exact htd ⟨h1, h2⟩
    · omega
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
  obtain ⟨hqleaf, hroom, hdead⟩ := hpar _ qm kq hqR hqm hkq
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  -- the halves
  obtain ⟨rr, _, _, hdiv, hfh, hsh⟩ := delLast_halves n (ctxOf p ts).i cv (ctxOf p ts).p.splitAbove hnl hsa2 hsp
  obtain ⟨hfH, hsH⟩ := halves_del_halfOK p hp n (ctxOf p ts).i _ hsp
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
    at hsp hfh hsh hfH hsH hdead hdiv
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
  have htn := hI.times L n hn
  obtain ⟨hsubl, _⟩ := live_shrink n last cv hlive'
  have hsub : ∀ q ∈ last.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
    rw [KNode.liveAt_of_times n (ts.length + 1) htn, KNode.liveAt_of_times last (ts.length + 1) htl]; exact hsubl
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
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hNw3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
  have hwfree : ∀ z, w.next ≤ z → wNode p (viewOf (treeRun p ts)) w z = none ∧
      w.taken.contains z = false := by
    intro z hz
    have hl : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some m => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    exact (hI.fresh z hz).1
  -- the split's live part
  have hlive : WriterWP (appendDeleteKlong L P.length cv) (ctxOf p ts) w3 (fun _ v =>
      LiveEdges p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey) := by
    refine writerWP_appendDeleteKlong_bitmapFull L P.length cv n _ w3 hlk3 hne htd hsz _ ?_
    generalize hw4 : ({ w3 with trail := "bitmap.full" :: w3.trail } : W) = w4
    have h4n : w4.nodes = w3.nodes := by rw [← hw4]
    have h4t : w4.taken = w3.taken := by rw [← hw4]
    have h4top : w4.top = w3.top := by rw [← hw4]
    have h4next : w4.next = w3.next := by rw [← hw4]
    have h4path : w4.path = w3.path := by rw [← hw4]
    have hN4 : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 = wNode p (viewOf (treeRun p ts)) w := by
      rw [← hNw3]; unfold wNode; rw [h4n, h4t]; rfl
    have hroot4 : w4.top.rootKey = w.top.rootKey := by rw [h4top, hr03.2.1]
    have hw4t : w4.taken = w.taken := by rw [h4t, hr03.2.2.1]
    have hw4n : w4.next = w.next := by rw [h4next, hnext3]
    rw [hlast]
    unfold handleFull
    rw [hd']
    refine writerWP_mono (writerWP_handleFull_spaceRoom_live d' L q n qm kq last (ctxOf p ts)
      (viewOf (treeRun p ts)) w4
      (by rw [h4n]; exact hlk3) (by rw [h4t]; exact h3t) (by rw [h4n]; exact hlq3)
      (by rw [hw4t]; exact hqt) hqL
      (by rw [h4next]; exact hI3.ids.1 L (by rw [hlk3]; rfl))
      (by rw [h4next]; exact hI3.ids.1 q (by rw [hlq3]; rfl)) hnm hqleaf hsp
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
      (hI.wf q qm hqm) (hI.times q qm hqm) hroom (by rw [hw4n]; exact hdead) hkq
      (by rw [hN4, hroot4]; exact hI.tree)
      (by rw [hN4, hroot4]; exact hqR)
      (by rw [hN4, hw4n]; exact (hwfree _ (Nat.le_refl _)).1)
      (by rw [hN4, hw4n]; exact (hwfree _ (by omega)).1)
      (by rw [hw4t, hw4n]; exact (hwfree _ (Nat.le_refl _)).2)
      (by rw [hw4t, hw4n]; exact (hwfree _ (by omega)).2)
      (by
        rw [hN4, hroot4, hw4n]
        intro u c' z' hu hl
        obtain ⟨m, hm, hc⟩ := hl
        exact hI.links u m c' z' (tReach_reachS _ _ _ _ hu) hm hc)
      (fun c' z' h => by
        obtain ⟨h1, h2⟩ := hfh c' z' h
        exact ⟨by rw [hdiv]; exact h1, hsub _ (by rw [← hlastN]; exact h2)⟩)
      (fun c' z' h => by
        obtain ⟨c0, h1, h2, h3⟩ := hsh c' z' h
        exact ⟨c0, by rw [hdiv]; exact h1, by rw [hdiv]; exact h2, hsub _ (by rw [← hlastN]; exact h3)⟩)
      hfH hsH
      (by rw [hN4, hroot4]; exact edges_of_liveCounts p _ _ _ hLC0)) ?_
    intro _ v hv
    exact hv
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧
      LiveEdges p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp)))) hlive) ?_
    rintro _ v ⟨⟨⟨⟨hDT, hJv⟩, hpbv⟩, ⟨_, hhiv, _, _⟩⟩, hE⟩
    exact ⟨⟨hDT, hJv⟩, hpbv, hhiv, hE⟩
  · intro g h v hgh ⟨hD, hpbv, hhiv, hE⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    exact hA g v hD hpbv hhiv (liveEdgesH_of_liveEdges _ _ _ _ _ hE)

/-- The full leaf not made by the transaction, split in space below an inner
parent with room, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with
the merges' loop and root collapse, given their live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullSpaceRoom_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hp : MergeParamsOK p)
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
      ∀ key, op = .del key → DelFullSpaceRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨_, _, _, _, _, hm, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_fullSpaceRoom p R hM hsa2 hp hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
    hS hJ key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
