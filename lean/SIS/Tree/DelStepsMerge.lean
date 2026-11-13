/-
Case (4)'s delete steps with the merges on, the reading (cost's `DelStepsOKF`;
the take-back's are on the F3 route, TakeDelStepsF4.lean) (bergdb 024-12, TP7 and TP10). The
delete splits as the merges-off cases (5) to (9) do: no leaf, a noop, a leaf
that empties (the upward delete), a leaf that keeps a live klong with room for
the bitmap, or full. Each obligation is restricted to one of them
(`DelStepsCaseOKF`), and the obligation follows from the five
(`delStepsOKF_of_cases`). The read-only cases
are proved here.
-/
import SIS.Tree.TakeDelMerge
import SIS.Tree.GetCaseBridge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The delete's cases with the merges on -/

/-- A delete, the merges on, of a key that has no leaf. -/
def DelNoLeafM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ key, op = .del key ∧ c.p.merges = true ∧ ¬ ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n

/-- A delete, the merges on, whose bitmap changes nothing. -/
def DelNoopM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap

/-- A delete, the merges on, that empties its leaf: the upward delete. -/
def DelEmptyM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true

/-- A delete, the merges on, whose leaf keeps a live klong and has room for the
bitmap. -/
def DelRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n

/-- A delete, the merges on, whose leaf keeps a live klong and is full. -/
def DelFullM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n

/-- Every delete with the merges on is in one of the five cases. -/
theorem delMerge_cover (c : Ctx) (base : View BVal) (w : W) (key : Key) (hm : c.p.merges = true) :
    DelNoLeafM c base w (.del key) ∨ DelNoopM c base w (.del key) ∨ DelEmptyM c base w (.del key) ∨
    DelRoomM c base w (.del key) ∨ DelFullM c base w (.del key) := by
  by_cases hk : ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n
  · obtain ⟨pre, cv, L, n, hkey, hl⟩ := hk
    subst hkey
    by_cases hb : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
    · exact Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb⟩)
    · cases ha : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
      | true => exact Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb, ha⟩))
      | false =>
        by_cases hr : DelRoom c cv n
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))
  · exact Or.inl ⟨key, rfl, hm, hk⟩

/-! ## The obligations by case -/

/-- `DelStepsOKF` for the deletes of one case P. -/
def DelStepsCaseOKF (p : Params) (R : Struct BVal → Time → Prop)
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
    (∀ g h v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    (∀ g h merged v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    (∀ seg v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

/-- `DelStepsOKF` from its five cases. -/
theorem delStepsOKF_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (c5 : DelStepsCaseOKF p R DelNoLeafM) (c6 : DelStepsCaseOKF p R DelNoopM)
    (c7 : DelStepsCaseOKF p R DelEmptyM) (c8 : DelStepsCaseOKF p R DelRoomM)
    (c9 : DelStepsCaseOKF p R DelFullM) : DelStepsOKF p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hm hA hMU hCR
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

/-! ## The read-only cases -/

/-- No leaf: the reading. -/
theorem delStepsCaseOKF_noLeaf (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseOKF p R DelNoLeafM := by
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
theorem delStepsCaseOKF_noop (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseOKF p R DelNoopM := by
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

end SIS.Tree
