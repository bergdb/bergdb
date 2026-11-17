/-
The delete's full leaf that the transaction made, split in space in place below
an inner parent with room (bergdb 030-01, step 5): the leaf keeps the first half
of its last version without the key, a new node the second, which the parent
names by the divider. Both halves are `HalfOK`, so the live counts hold after
with no hole (`liveEdgesX_spaceInPlaceStep`), and the merges' loop starts from
them.
-/
import SIS.Tree.LiveDelSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- A full node x that the transaction made, split in space in place with a last
version given (a delete's), below an inner parent q with room for the second
half's klong: x keeps the first half, a new node the second. From the live counts
at the start, with halves that are `HalfOK` and hold x's live klongs, they hold
after, with no hole. -/
theorem writerWP_handleFull_spaceInPlaceRoom_live (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hlq : w.nodes.lookup q = some qn) (hqt : w.taken.contains q = false) (hqx : q ≠ x)
    (hxn : x < w.next) (hqn : q < w.next)
    (hfirst : n.firstTime = some c.i) (hql : qn.leaf = false)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hroom : qn.size + 2 ≤ c.p.M)
    (hdead : deadOver c.p ([((halves n.leaf c.i last []).2.2, w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false)
    (hk : (k1, x) ∈ qn.liveAt c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hqR : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hn1 : wNode c.p base w w.next = none) (ht1 : w.taken.contains w.next = false)
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
  have hxy1 : x ≠ w.next := by omega
  obtain ⟨hfl, hsl⟩ := halves_leaf_eq n.leaf c.i last []
  apply writerWP_handleFullWith_spaceInPlace_up_last d' x q n qn last c w hlk hlq hql hfirst hsplit hpq hxn
  intro w1 h1n h1t h1top h1path h1next h1vals
  generalize hout : halves n.leaf c.i last [] = out at hdead hf hs hfH hsH hfl hsl h1n ⊢
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n]; simp only [hqx, hqy1, ↓reduceIte]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_addKeys d' q qn _ c w1 hlq1 (by simp; omega) hdead) ?_
  intro _ w2 hw2
  have h2n : w2.nodes = upsert w1.nodes q ([(out.2.2, w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by rw [hw2]
  have h2t : w2.taken = w.taken := by rw [hw2]; exact h1t
  have h2top : w2.top = w.top := by rw [hw2]; exact h1top
  have hlook : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → w2.nodes.lookup z = w.nodes.lookup z := by
    intro z hzx hzq hz1
    rw [h2n, lookup_upsert, if_neg hzq, h1n]
    simp only [hzx, hz1, ↓reduceIte]
  have hqn' : wNode c.p base w q = some qn := by
    simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hlq]
  have hxn' : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hN2q : wNode c.p base w2 q = some ([(out.2.2, w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
    have hl : w2.nodes.lookup q = some ([(out.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
      rw [h2n, lookup_upsert]; simp
    have ht : w2.taken.contains q = false := by rw [h2t]; exact hqt
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
  have hN2x : wNode c.p base w2 x = some out.1 := by
    have hl : w2.nodes.lookup x = some out.1 := by
      rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n]; simp
    have ht : w2.taken.contains x = false := by rw [h2t]; exact hxt
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
  have hN2S : wNode c.p base w2 w.next = some out.2.1 := by
    have hl : w2.nodes.lookup w.next = some out.2.1 := by
      rw [h2n, lookup_upsert, if_neg (Ne.symm hqy1), h1n]; simp [Ne.symm hxy1]
    have ht : w2.taken.contains w.next = false := by rw [h2t]; exact ht1
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
  have hother : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → wNode c.p base w2 z = wNode c.p base w z := by
    intro z hzx hzq hz1
    simp only [wNode, h2t, hlook z hzx hzq hz1]
  have hq' : ∀ c' z, (c', z) ∈ ([(out.2.2, w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn).liveAt c.i →
      (c' = out.2.2 ∧ z = w.next) ∨ (c' ≠ out.2.2 ∧ (c', z) ∈ qn.liveAt c.i) := by
    intro c' z h
    simp only [List.foldl_cons, List.foldl_nil] at h
    exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtm c' z h
  have hq'l : ([(out.2.2, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn).leaf = qn.leaf := by
    simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
  have hgen := liveEdgesX_spaceInPlaceStep c.p (fun _ => False) (wNode c.p base w) (wNode c.p base w2)
    c.i w.top.rootKey q x w.next qn n out.1 out.2.1
    ([(out.2.2, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn)
    k1 out.2.2 (splitLocalCv n.leaf out.2.2) hT hqR hqn' hk hxn' hN2q hq' hN2x hN2S hf hs hother hn1
    (by
      intro u c' hu hl
      have := hlinks u c' w.next hu hl
      omega)
    (fun h => h) (fun h => h) hfl hsl hfH hsH hq'l
    (addKeys_liveAt_length c.i [(out.2.2, w.next)] qn hqwf hqtm)
    ((liveEdgesX_false_iff _ _ _ _).mpr hL)
  rw [h2top]
  exact (liveEdgesX_false_iff _ _ _ _).mp hgen

/-! ## The case: the full leaf that the transaction made, split in space in place -/

/-- As `DelFullSpaceRoomM`, but the leaf made by the transaction: it splits in
space in place, keeping the first half; its parent is inner and has room for the
second half's klong. -/
def DelFullSpaceMadeRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
    ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧ c.p.M ≤ n.size + 1 ∧
    c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
    n.firstTime = some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.leaf = false ∧ qn.size + 2 ≤ c.p.M ∧
      deadOver c.p ([((halves n.leaf c.i
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false

set_option maxHeartbeats 4000000 in
/-- The full leaf that the transaction made, split in space in place below an
inner parent with room, calls `afterDelete` with the live counts (no hole), in the
stratum (bergdb 030-01, step 5): any `afterDelete` that keeps the live counts from
the hole at (g, 0) gives them after. -/
theorem liveDel_fullSpaceMadeRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullSpaceMadeRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
      m.firstTime = some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.leaf = false ∧ qn.size + 2 ≤ (ctxOf p ts).p.M ∧
        deadOver (ctxOf p ts).p ([((halves m.leaf (ctxOf p ts).i
          (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))) []).2.2,
            w.next)].foldl (fun n (cv, y) => n.add (ctxOf p ts).i (.key cv y)) qn) = false)
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
    refine writerWP_mono (writerWP_handleFull_spaceInPlaceRoom_live d' L q n qm kq last (ctxOf p ts)
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
      (hI.wf q qm hqm) (hI.times q qm hqm) hroom (by rw [hw4n]; exact hdead) hkq
      (by rw [hN4, hroot4]; exact hI.tree)
      (by rw [hN4, hroot4]; exact hqR)
      (by rw [hN4, hw4n]; exact (hwfree _ (Nat.le_refl _)).1)
      (by rw [hw4t, hw4n]; exact (hwfree _ (Nat.le_refl _)).2)
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

/-- The full leaf that the transaction made, split in space in place below an
inner parent with room, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with
the merges' loop and root collapse, given their live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullSpaceMadeRoom_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelFullSpaceMadeRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
  refine liveDel_fullSpaceMadeRoom p R hM hsa2 hp hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
    hS hJ key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
