/-
The delete with the merges on keeps the writer's tree, `PutInv` and the walk's
ranges (bergdb 024-12, `t4`, `i4`, `r4`): the reading's (4) route carries
`DelInvF3` through the delete, the merges' loop and root collapse, and it
holds `PutInv` and `RangeOrder`. The delete's steps with the post
`QdW` (`PutInv` and `RangeOrder`) are the generic-Post walk lemmas
(`writerWP_del_toLeafMK`, `writerWP_del_emptyRoomMK`, `writerWP_del_emptyAnyMK`,
`writerWP_del_toLeafMKH`) at that post.
-/
import SIS.Tree.DelStepsFullH
import SIS.Tree.PutInvDel
import SIS.Tree.RangeOps
import SIS.Tree.GetOpAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's tree invariants after a delete: `PutInv` and the walk's
ranges. -/
def QdW (p : Params) (ts : List Tx) (v : W) : Prop :=
  PutInv (ctxOf p ts) (viewOf (treeRun p ts)) v ∧
    RangeOrder (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey

/-- `PutInv` with a larger next id. -/
theorem putInv_next (c : Ctx) (base : View BVal) (w : W) (k : NodeId) (h : PutInv c base w)
    (hk : w.next ≤ k) : PutInv c base { w with next := k } := by
  obtain ⟨hT, hwf, ht, ⟨i1, i2, i3, i4, i5⟩, hf, hl, hu, hkv, ho⟩ := h
  exact ⟨hT, hwf, ht, ⟨fun z hz => Nat.lt_of_lt_of_le (i1 z hz) hk, fun z hz => Nat.lt_of_lt_of_le (i2 z hz) hk,
    fun z hz => Nat.lt_of_lt_of_le (i3 z hz) hk, fun q hq => Nat.lt_of_lt_of_le (i4 q hq) hk,
    Nat.lt_of_lt_of_le i5 hk⟩, fun z hz => hf z (Nat.le_trans hk hz),
    fun x xn cc z hx hxn hz => Nat.lt_of_lt_of_le (hl x xn cc z hx hxn hz) hk, hu, hkv, ho⟩

theorem qdW_fresh (p : Params) (ts : List Tx) (v : W) (h : QdW p ts v) :
    WriterWP fresh (ctxOf p ts) v (fun _ v' => QdW p ts v') := by
  unfold fresh
  wpSimplify
  exact ⟨putInv_next _ _ _ _ h.1 (by omega), h.2⟩

/-- A delete step case with the post `QdW`. -/
def DelStepsCaseQd (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ g h v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ g h merged v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ seg v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => QdW p ts w')

/-- No leaf: the state reads as before. -/
theorem delStepsCaseQd_noLeaf (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseQd p R DelNoLeafM := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI hRO _ key0 _ hP _ _ _
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
    subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_mono (writerWP_putSegs_del_noLeaf (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key
    key w.top.rootKey w2 hne ?_ ?_) ?_
  · intro q hq
    rw [hr02.2.2.1]
    rw [hr02.1] at hq
    exact hI.pathUntaken key q hq
  · rw [hr02.1]; exact hno'
  · intro _ w' hr'
    have hr : ReadsAs p (viewOf (treeRun p ts)) w w' := ReadsAs.trans _ _ _ _ _ hr02 hr'
    refine ⟨putInv_of_readsAs _ _ w w' hI hr, ?_⟩
    rw [hr.1, hr.2.1]; exact hRO

/-- A noop: the tree, `PutInv` and the ranges as before. -/
theorem delStepsCaseQd_noop (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) :
    DelStepsCaseQd p R DelNoopM := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hI hRO _ _ _ hP _ _ _
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hleaf := keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap) hnoop
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_del_noop_seg_tree (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w hrk (hI.pathUntaken _)
      hleaf hI.tree)
    (putInv_del_noop_seg (ctxOf p ts) _ tx.base top hB pre cv rk w hI hbook hrk hleaf))
    (rangeOrder_del_noop_seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w hI hRO hrk hleaf)) ?_
  rintro _ w' ⟨⟨hT, hPI⟩, hR⟩
  exact ⟨hPI hT, hR⟩

theorem delStepsCaseQd_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseQd p R DelRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · exact fun v hv' => qdW_fresh p ts v hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' _ hXD _
    obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0⟩ L n hL hn hnl
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _ ?_ ?_
    · refine writerWP_mono (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
      rintro _ v ⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩, hkv⟩
      exact ⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩
    · intro g h v hv'
      exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => ⟨hv''.1.1, hv''.1.2.2.1⟩)

theorem delStepsCaseQd_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseQd p R DelEmptyRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_emptyRoomMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hA hMU hCR (QdW p ts) (fun v hv' => qdW_fresh p ts v hv')
    (fun v hv' => ⟨hv'.1.1, hv'.1.2.2.1⟩)

set_option maxHeartbeats 1600000 in
/-- The reading of a delete that empties the leaf at the space root, the merges
on, on the F3 route: the root's bitmap, or its split when full; no merges'
loop. -/
theorem delStepsCaseQd_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseQd p R DelEmptyRootM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc _ _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  have hfuel : 1 ≤ p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · exact fun v hv' => qdW_fresh p ts v hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hall, hLr⟩ := keyLeaf_all2 hK hrk
      (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey)
      ⟨hne0, hall0, hroot0⟩ L n hL hn hnl
    have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
    subst hPnil
    have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
    refine writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _ ?_
    have hr03' : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w
        ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) :=
      ⟨hr03.1, hr03.2.1, hr03.2.2.1, hr03.2.2.2.1, hr03.2.2.2.2⟩
    have hb3' := putBook_note "up.root-kept-empty" (ctxOf p ts) _ tx.base top hB w3 hJ3.1
    have hn' : wNode p (viewOf (treeRun p ts)) w L = some n := hn
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    by_cases hroom : DelRoom (ctxOf p ts) cv n
    · refine writerWP_mono (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3')) ?_
      rintro _ v ⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩
      have hD := delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w _ v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03' hLt h1 h2 h3 h7 hbv
      exact ⟨hD.1, hD.2.2.1⟩
    · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W)
        [] n hI hr03' hp3' hlinkP hlkX
      have hNn : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey [] 0)).getD
          ⟨true, []⟩ = n := by
        rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hn]; rfl
      have hI3 := putInv_of_readsAs _ _ w _ hI hr03'
      have hG3 := putInvG_of_book _ _ tx.base top _ hB hb3'
      have hinv := delFullRootStepOK_ctx p ts _ hI3 hG3 (by rw [hr03'.1, hr03'.2.1]; exact hRO)
        (by rw [hr03'.1, hr03'.2.1]; exact hF) hsa2 _ _ _ hPOK pre cv rk hkey
        (by rw [hr03'.1, hr03'.2.1]; exact hrk)
        (by show (nodeAt w.top.rootKey [] 0, cv) ∈ _; rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hr03'.1]; exact hL)
        (by rw [hr03'.1, hr03'.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
        (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne) (by rw [hNn]; exact hroom)
      simp only [show nodeAt w.top.rootKey [] 0 = L from hXD] at hinv
      refine writerWP_mono (writerWP_and hinv (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3')) ?_
      rintro _ v ⟨⟨hTv, htv, _, _, hreachv, hRv, _⟩, hbv⟩
      have hun : ∀ y, ReachS (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey y →
          v.taken.contains y = false := by
        intro y hy
        rw [htv]
        rcases hreachv y (reachS_tReach _ _ _ _ hy) with h | h
        · exact hI3.untaken y (tReach_reachS _ _ _ _ h)
        · cases h' : ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).taken.contains y with
          | false => rfl
          | true => have := hI3.ids.2.2.1 y h'; dsimp only at this h; omega
      obtain ⟨hPv, _⟩ := putInv_after_step (ctxOf p ts) _ v tx.base top hB hbv hTv hun hRv
      exact ⟨hPv, hRv⟩

theorem delStepsCaseQd_fullH (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseQd p R DelFullM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · exact fun v hv' => qdW_fresh p ts v hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _
      (writerWP_appendDeleteKlong_full_delF3H (ctxOf p ts) _ (viewCoherent_ctxOf p ts) _ tx.base (hRoot ts) _
        (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
        hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO hF hkey hrk L n P w3 hL hn hnl hne hfull
        hr03 hJ3.1 hJ3.2 hp3' hlinkP hXD hlkX) ?_
    intro g h v hv'
    exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => ⟨hv''.1.1, hv''.1.2.2.1⟩)

end SIS.Tree
