/-
A delete that empties its leaf with no room for the upward delete
(`DelEmptyOtherM`, bergdb 024-12, case (4)): the leaf is the space root, or
its stop node cascades (`DelEmptyCascM`, named). The space root kept empty:
its bitmap, or its split when full, then no merges' loop.
-/
import SIS.Tree.DelStepsFullRoot
import SIS.Tree.LinkedUnique

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete that empties its leaf, the space root. -/
def DelEmptyRootM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L = w.top.rootKey

/-- A delete that empties its leaf below the space root whose stop node has no
room: its bitmap or LE-b cascades. -/
def DelEmptyCascM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧
    ∃ P, LinkedFrom (wNode c.p base w) c.i w.top.rootKey P ∧ nodeAt w.top.rootKey P P.length = L ∧
      0 < P.length ∧ ¬ StopRoomP c (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length

theorem delEmptyOther_split (c : Ctx) (base : View BVal) (w : W) (op : Op) (h : DelEmptyOtherM c base w op) :
    DelEmptyRootM c base w op ∨ DelEmptyCascM c base w op := by
  obtain ⟨pre, cv, L, n, hop, hm, hK, hne, hall, hnr⟩ := h
  unfold UpRoom at hnr
  have : ∃ P, LinkedFrom (wNode c.p base w) c.i w.top.rootKey P ∧ nodeAt w.top.rootKey P P.length = L ∧
      ¬ (0 < P.length ∧ StopRoomP c (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length) := by
    apply Classical.byContradiction
    intro hno
    apply hnr
    intro P h1 h2
    apply Classical.byContradiction
    intro h3
    exact hno ⟨P, h1, h2, h3⟩
  obtain ⟨P, hlink, hend, hno⟩ := this
  cases hP : P with
  | nil =>
    left
    refine ⟨pre, cv, L, n, hop, hm, hK, hne, hall, ?_⟩
    rw [← hend, hP]; simp [nodeAt]
  | cons e P' =>
    right
    refine ⟨pre, cv, L, n, hop, hm, hK, hne, hall, P, hlink, hend, by rw [hP]; simp, fun h => hno ⟨by rw [hP]; simp, h⟩⟩

/-- The upward delete at the space root (depth 0): the root is kept empty by
its bitmap. -/
theorem writerWP_deleteUpward_rootEmpty (c : Ctx) (L : NodeId) (n : KNode) (cv : Nat) (key : Key) (w3 : W)
    (hlk3 : w3.nodes.lookup L = some n) (hp0 : (w3.path[0]?).map (·.2) = some L) (hnl : n.leaf = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true)
    (Post : W → Prop)
    (hbit : WriterWP (appendDeleteKlong L 0 cv) c ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W)
      (fun _ v => Post v)) :
    WriterWP (deleteUpward L 0 cv key) c w3 (fun _ v => Post v) := by
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w3 hlk3]
  have hne' : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  rw [writerWP_bind]
  have hcl : WriterWP (climb 0) c w3 (fun stop w' => w' = w3 ∧ stop = 0) := by
    unfold climb
    simp only [writerWP_bind, writerWP_read]
    unfold pathNode
    simp only [writerWP_bind, writerWP_get]
    cases he : w3.path[0]? with
    | none => rw [he] at hp0; cases hp0
    | some e =>
      rw [he] at hp0
      simp only [Option.map_some, Option.some.injEq] at hp0
      simp only [writerWP_pure]
      rw [hp0, writerWP_getNode_known _ _ c w3 hlk3]
      simp only [hnl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      first | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩ | exact ⟨trivial, trivial⟩ | simp
  refine writerWP_mono hcl ?_
  rintro stop w' ⟨rfl, rfl⟩
  simp only [beq_self_eq_true, ↓reduceIte, note, writerWP_bind, writerWP_modify]
  refine writerWP_mono hbit ?_
  intro _ v hv
  simp only [writerWP_pure]
  exact hv

/-- The walk's path to the space root is empty. -/
theorem path_nil_of_root (c : Ctx) (base : View BVal) (w : W) (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (P : List (Option Nat × NodeId)) (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = w.top.rootKey) : P = [] :=
  linkedFrom_unique _ _ _ hT P [] hlinkP (LinkedFrom.nil _) (by rw [hXD]; simp [nodeAt])

set_option maxHeartbeats 1600000 in
/-- The reading of a delete that empties the leaf at the space root, the merges
on: the root's bitmap, or its split when full; no merges' loop. -/
theorem delStepsCaseOK_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOK p R DelEmptyRootM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc _ _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
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
  have hfuel : 1 ≤ p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
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
      intro hFv key' hk'
      have := runGet_of_delInvF p ts w v (pre ++ [cv]) hD hI hF hFv key' hk'
      simpa [Op.key, Op.value] using this
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
      rintro _ v ⟨⟨hTv, htv, _, _, hreachv, hRv, hreadv⟩, hbv⟩
      intro hFv key' hk'
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
      have hr := hreadv (segFits_mono _ _ _ _ _ hFv (by simp only [ctxOf]; omega)) key' hk'
      have hwfv : ∀ x xn, ReachS (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey x →
          wNode p (viewOf (treeRun p ts)) v x = some xn → klongsWf xn.ks = true := fun x xn _ h => hPv.wf x xn h
      have hwfw : ∀ x xn, ReachS (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x →
          wNode p (viewOf (treeRun p ts)) w x = some xn → klongsWf xn.ks = true := fun x xn _ h => hI.wf x xn h
      have e1 := wGetAt_eq_wGet (ctxOf p ts) _ v ((ctxOf p ts).p.fuel + 1) (by omega) hwfv hFv key'
      have e2 := wGetAt_eq_wGet (ctxOf p ts) _ w ((ctxOf p ts).p.fuel + 1) (by omega) hwfw hF key'
      have e3 : wGetAt (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts))
          ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) ((ctxOf p ts).p.fuel + 1) key' =
          wGetAt (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts)) w ((ctxOf p ts).p.fuel + 1) key' := by
        unfold wGetAt
        rw [ReadsAs.value _ _ _ _ hr03', hr03'.1, hr03'.2.1]
      rw [e3, e2, e1] at hr
      unfold runGet
      simp only [ctxOf] at hr
      rw [hr]
      simp [Op.key, Op.value]

end SIS.Tree
