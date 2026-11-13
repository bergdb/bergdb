/-
Case (4)'s delete steps on latest's F3 route (bergdb 024-12, TP10): the
reading's obligation `DelStepsOKF3` (the continuations keep `DelInvF3` =
`DelInvF` ∧ the kinds' books) by the delete's cases, the walk carrying the
put's books and the kinds' books (`KdJ`, `writerWP_del_toLeafMK`).
-/
import SIS.Tree.DelStepsKd
import SIS.Tree.DelStepsUpK

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `DelStepsOKF3` for the deletes of one case P. -/
def DelStepsCaseOKF3 (p : Params) (R : Struct BVal → Time → Prop)
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
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

/-- `DelStepsOKF3` from its five cases. -/
theorem delStepsOKF3_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (c5 : DelStepsCaseOKF3 p R DelNoLeafM) (c6 : DelStepsCaseOKF3 p R DelNoopM)
    (c7 : DelStepsCaseOKF3 p R DelEmptyM) (c8 : DelStepsCaseOKF3 p R DelRoomM)
    (c9 : DelStepsCaseOKF3 p R DelFullM) : DelStepsOKF3 p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hm hA hMU hCR
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

/-! ## The read-only cases -/

/-- No leaf: the reading. -/
theorem delStepsCaseOKF3_noLeaf (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseOKF3 p R DelNoLeafM := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ _ key0 _ hP _ _ _
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  have hnone : runGet p ts w key = none := by
    unfold runGet wGet
    exact getFromR_noLeaf _ _ _ _ key _ hne hno'
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
  · intro _ w' hr' _ key' _
    have hr : ReadsAs p (viewOf (treeRun p ts)) w w' := ReadsAs.trans _ _ _ _ _ hr02 hr'
    have hsame : runGet p ts w' key' = runGet p ts w key' := by
      unfold runGet wGet
      rw [hr.1, hr.2.1, ReadsAs.value _ _ _ _ hr]
    rw [hsame]
    by_cases hk : key = key'
    · subst hk
      simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
      exact hnone
    · have hk' : (key == key') = false := by simpa using hk
      simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]

/-- A noop: the reading. -/
theorem delStepsCaseOKF3_noop (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseOKF3 p R DelNoopM := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ _ _ _ hP _ _ _
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_del_noop_seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk
    w hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
      bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap)
      ⟨hI.wf L n hn, hI.times L n hn, hnoop⟩)) ?_
  intro _ w' hpost _ key hk
  exact hpost key hk

/-! ## The kinds' context of a delete -/

/-- The kinds' context at a state between operations of a transaction within
reach: the view's ids and kinds, and the books and the kinds' books there. -/
theorem kd_context (p : Params) (hM : 2 ≤ p.M) (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (top : Top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ViewIdsBelow tx.base (ctxOf p ts).view ∧
      ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
      Book tx.base (ctxOf p ts) w ∧ KdInv (kindOracleOf p (treeRun p ts)) tx.base w := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := treeRun_kindsAllOK p hM hP ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hP ts hwts) hK
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top) hv hk (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact ⟨hv, hk, hkd.1, hkd.2.1⟩

/-- The path's last entry at the walk's end, by its index. -/
theorem path_last_of_toLeaf (w w3 : W) (P : List (Option Nat × NodeId)) (L : NodeId)
    (hp3' : w3.path = (none, w.top.rootKey) :: P) (hXD : nodeAt w.top.rootKey P P.length = L) :
    ∃ a, w3.path[P.length]? = some (a, L) := by
  have h := kdPathLast_steps w3 [(none, w.top.rootKey)] P w.top.rootKey (by rw [hp3']; rfl) rfl
  rw [← nodeAt_last, hXD] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  have : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [this] at ha
  exact ha

/-! ## The leaf's bitmap: with room, and full -/

/-- The reading of a delete whose leaf keeps a live klong and has room, the
merges on, on the F3 route: the walk with the books and the kinds' books, the
bitmap keeping both (`kd_appendDeleteKlong`), for runs with their links and TP4
at every run. -/
theorem delStepsCaseOKF3_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOKF3 p R DelRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
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
      refine writerWP_mono (hA g h v hv') ?_
      intro _ v' hv'' hFv' key' hk'
      have := runGet_of_delInvF p ts w v' (pre ++ [cv]) hv''.1 hI hF hFv' key' hk'
      simpa [Op.key, Op.value] using this

/-- The reading of a delete into a full leaf, the merges on, on the F3 route,
from the obligation `DelFullStepOKF` (the delete's invariant after the leaf's
bitmap), the kinds' books by `kd_appendDeleteKlong`. -/
theorem delStepsCaseOKF3_full (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hStep : ∀ ts, DelFullStepOKF (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseOKF3 p R DelFullM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _ ?_ ?_
    · refine writerWP_mono (writerWP_and
        (hStep ts w pre cv rk tx.base top hB hI hRO hICE hF hkey hrk L n P w3 hL hn hnl
          hne hkeep hfull hr03 hJ3.1 hlk3 hp3' hlinkP hXD hlkX)
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
      rintro _ v ⟨hD, hkv⟩
      exact ⟨hD, hkv.1, hkv.2.1⟩
    · intro g h v hv'
      refine writerWP_mono (hA g h v hv') ?_
      intro _ v' hv'' hFv' key' hk'
      have := runGet_of_delInvF p ts w v' (pre ++ [cv]) hv''.1 hI hF hFv' key' hk'
      simpa [Op.key, Op.value] using this


/-! ## The invariant of the upward delete: the books, the kinds' books, the path -/

/-- `KdJ` with the key access path as it was where the upward delete starts. -/
def KdJP (c : Ctx) (B : NodeId) (top0 : Top) (KO : KindOracle) (BK : NodeId)
    (p0 : List (Option Nat × NodeId)) (v : W) : Prop :=
  KdJ c B top0 KO BK v ∧ v.path = p0

theorem kdJP_note (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (p0 : List (Option Nat × NodeId)) (s : String) (v : W) (hJ : KdJP c B top0 KO BK p0 v) :
    KdJP c B top0 KO BK p0 { v with trail := s :: v.trail } := by
  have h := kd_note KO BK s c v hv hk hJ.1.2.1 hJ.1.2.2
  simp only [note, writerWP_modify] at h
  exact ⟨⟨putBook_note s c base B top0 hB v hJ.1.1, h.1, h.2.1⟩, hJ.2⟩

theorem kdJP_takeBack (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (p0 : List (Option Nat × NodeId)) (x q : NodeId) (k : Nat) (v : W) (hJ : KdJP c B top0 KO BK p0 v)
    (hx : ∃ xn, v.nodes.lookup x = some xn) :
    WriterWP (takeBack x q k) c v (fun _ v' => KdJP c B top0 KO BK p0 v') := by
  obtain ⟨xn, hl⟩ := hx
  obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hJ.1.2.1 hl
  refine writerWP_mono (writerWP_and (putBook_takeBack x q k c base B top0 hB v hJ.1.1 ⟨xn, hl⟩)
    (kd_takeBack KO BK x q k c v hv hk hJ.1.2.1 hJ.1.2.2 g h hgh)) ?_
  rintro _ v' ⟨hb', hb2, hi2, _, hp⟩
  exact ⟨⟨hb', hb2, hi2⟩, hp.trans hJ.2⟩

theorem kdJP_unlink (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (p0 : List (Option Nat × NodeId)) (x : NodeId) (v : W) (hJ : KdJP c B top0 KO BK p0 v) :
    WriterWP (unlink x) c v (fun _ v' => KdJP c B top0 KO BK p0 v') := by
  refine writerWP_mono (writerWP_and (putBook_unlink x c base B top0 hB v hJ.1.1)
    (kd_unlink KO BK x c v hv hk hJ.1.2.1 hJ.1.2.2)) ?_
  rintro _ v' ⟨hb', hb2, hi2, _, hp⟩
  exact ⟨⟨hb', hb2, hi2⟩, hp.trans hJ.2⟩

theorem kdJP_appendDeleteKlong (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (p0 : List (Option Nat × NodeId)) (x : NodeId) (d k : Nat) (v : W)
    (hJ : KdJP c B top0 KO BK p0 v) (hx : (p0[d]?).map (·.2) = some x) :
    WriterWP (appendDeleteKlong x d k) c v (fun _ v' => KdJP c B top0 KO BK p0 v') := by
  obtain ⟨a, ha⟩ : ∃ a, v.path[d]? = some (a, x) := by
    rw [hJ.2]
    cases he : p0[d]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨e.1, by rw [← hx]⟩
  refine writerWP_mono (writerWP_and (putBook_appendDeleteKlong x d k c base B top0 hB v hJ.1.1)
    (kd_appendDeleteKlong KO BK x d k c v hv hk hJ.1.2.1 hJ.1.2.2 a ha)) ?_
  rintro _ v' ⟨hb', hb2, hi2, _, hp⟩
  exact ⟨⟨hb', hb2, hi2⟩, hp.trans hJ.2⟩

theorem kdJP_emptyKeyNext (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (p0 : List (Option Nat × NodeId)) (x : NodeId) (d : Nat) (v : W) (xn : KNode)
    (hJ : KdJP c B top0 KO BK p0 v) (hx : (p0[d]?).map (·.2) = some x)
    (hl : v.nodes.lookup x = some xn) (hxl : xn.leaf = false) :
    WriterWP (emptyKeyNext x d) c v (fun _ v' => KdJP c B top0 KO BK p0 v') := by
  obtain ⟨a, ha⟩ : ∃ a, v.path[d]? = some (a, x) := by
    rw [hJ.2]
    cases he : p0[d]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨e.1, by rw [← hx]⟩
  obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hJ.1.2.1 hl
  have hlf := kd_leaf hJ.1.2.1 hl hgh
  have hh : h ≠ 0 := by intro h0; rw [h0] at hlf; rw [hxl] at hlf; simp at hlf
  refine writerWP_mono (writerWP_and (putBook_emptyKeyNext x d c base B top0 hB v hJ.1.1)
    (kd_emptyKeyNext KO BK x d c v hv hk hJ.1.2.1 hJ.1.2.2 a ha g h hgh hh)) ?_
  rintro _ v' ⟨hb', hb2, hi2, _, hp⟩
  exact ⟨⟨hb', hb2, hi2⟩, hp.trans hJ.2⟩

set_option maxHeartbeats 1600000 in
theorem writerWP_del_emptyRoomMK (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hA : ∀ g h v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hMU : ∀ g h merged v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hCR : ∀ seg v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hJ0 : KdJ c B top0 KO BK w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (KdJ c B top0 KO BK) hJ0
    (fun s f x v hJ hx => kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ hL hlk hkm)
    (kdJ_start c base B top0 hB KO BK hvB w hJ0) hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hb3 hlk3 hp3' hlinkP hXD hlkX
  obtain ⟨hne, hall, hup⟩ := hleafC L n hL hn hnl
  obtain ⟨hdepth, hstopOK⟩ := hup P hlinkP hXD
  -- the path, at w
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hI.tree _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  -- the facts at w3
  have hN3 : ∀ i, i ≤ P.length → wNode c.p base w3 (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have htk3 : ∀ i, i ≤ P.length → w3.taken.contains (nodeAt w.top.rootKey P i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreachX i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hI.tree
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hRt3 : ∀ y, TReach (wNode c.p base w3) c.i w3.top.rootKey y → w3.taken.contains y = false := by
    intro y hy
    rw [hr03.1, hr03.2.1] at hy
    rw [hr03.2.2.1]
    exact hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hTimesR3 : ∀ y yn, TReach (wNode c.p base w3) c.i w3.top.rootKey y → wNode c.p base w3 y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i := fun y yn _ h => by rw [hr03.1] at h; exact hI.times y yn h
  have hICE3 : InnerChildrenExist (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hICE
  have hfit3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
  have hnovalAll3 : ∀ y yn, wNode c.p base w3 y = some yn → wValue base w3 y = none := by
    intro y yn h
    rw [hr03.1] at h
    rw [ReadsAs.value _ _ _ _ hr03]
    exact hI.keyNoValue y yn h
  have hreach3 : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w3) c.i w3.top.rootKey (nodeAt w.top.rootKey P i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreachX i hi
  have hlinkK : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i :=
    fun i h1 h2 => (hKP i h1 h2).2
  have hNnD : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n = n := by rw [hXD, hn]; rfl
  -- DelInvF at a continuation of the upward delete
  have hD : ∀ (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      w'.top = w3.top → w'.vals = w3.vals →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      sn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf →
      klongsWf sn'.ks = true → (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i →
        ∃ c0, (c0, z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).liveAt c.i ∧
          c0 ≠ ((P[stop + 1 - 1]?).bind (·.1)).getD 0 ∧ f c0 = c') →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      PutBook c B top0 w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key') →
      DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hread
    have hCG := collGetInv_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    exact delInvF_of_collGetInv c base B top0 hB w w3 w' (pre ++ [cv]) hI hF hr03 hCG hRO' hb' hread
  -- the frame facts at a continuation
  have hXs : ∀ stop, stop < P.length → ∀ k, stop < k → k ≤ P.length →
      nodeAt w.top.rootKey P stop ≠ nodeAt w.top.rootKey P k :=
    fun stop _ k h1 h2 he => by have := hdistP _ _ (by omega) h2 he; omega
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      (∀ u, u ≠ nodeAt w.top.rootKey P stop → (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w3 u) ∧
      wNode c.p base w' (nodeAt w.top.rootKey P stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht _ (hXs stop hsD), htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  rw [← hXD]
  refine writerWP_deleteUpward_upT_getJMBK c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk (madeForBound w3) w3 Post
    (KdJP c B top0 KO BK w3.path) ⟨hb3, rfl⟩ (fun s v hJ => kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ)
    (fun x q k v hJ hx => kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ hx)
    (fun x v hJ => kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ)
    (fun x d k v hJ hx => kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ x d k v hJ hx)
    (fun x d v xn hJ hx hl hxl => kdJP_emptyKeyNext c base B top0 hB KO BK hvB hk _ x d v xn hJ hx hl hxl)
    (madeFor_lt_bound w3) hdepth hfuel hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hreach3
    hlinkK (fun i hi => hnovalAll3 _ _ (hN3 i hi)) (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hstopOK hm ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hb'.1.2.1, hb'.1.2.2⟩) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    exact writerWP_mono (hA gs hs w' ⟨hDv, hb'.1.2.1, hb'.1.2.2⟩) (fun _ w2 hD2 => hpost w2 hD2)
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_leb (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    have hDv := hD stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩) hRO' hb'.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hb'.1.2.1, hb'.1.2.2⟩) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)

/-- The reading of a delete whose leaf empties, the upward delete with room, on
the F3 route. -/
theorem delStepsCaseOKF3_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOKF3 p R DelEmptyRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_emptyRoomMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hA hMU hCR _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

theorem delStepsCaseOKF3_or (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseOKF3 p R P1) (h2 : DelStepsCaseOKF3 p R P2) : DelStepsCaseOKF3 p R P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR

/-- `DelStepsOKF3` (latest's F3 route) with every case proved but the upward
delete without room (`DelEmptyOtherM`: the leaf is the space root, or the stop
node cascades), the full leaf's bitmap reduced to `DelFullStepOKF`. -/
theorem delStepsOKF3_of_open (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (c7 : DelStepsCaseOKF3 p R DelEmptyOtherM)
    (hStep : ∀ ts, DelFullStepOKF (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_cases p R (delStepsCaseOKF3_noLeaf p R) (delStepsCaseOKF3_noop p R)
    (delStepsCaseOKF3_or p R _ _ _ delEmptyM_split (delStepsCaseOKF3_emptyRoom p R hM hRL hP) c7)
    (delStepsCaseOKF3_room p R hM hRL hP) (delStepsCaseOKF3_full p R hM hRL hP hStep)

end SIS.Tree
