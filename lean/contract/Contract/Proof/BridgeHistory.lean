/-
The contract package (bergdb 030-07): what the bridge checker computes for a
whole trace (`bridgeHistoryOk`, BridgeHeap.lean) gives a history that meets
the contract and the bridge's clauses, and what eviction needs
(`bridgeHistoryOk_meets`). So the theorems of BridgeTheorems.lean hold for
every trace that the checker passes, for the tree that the trace's lines
give.
-/
import Mathlib.Tactic
import Contract.Proof.BridgeModel
import Contract.Proof.BridgeInv

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal)

/-- The start that the checker computes is the start of the bridge. -/
theorem startCheck_sound (c0 : Changes BVal) (h0 : Heap) (steps : List TStep)
    (hc : startCheck c0 h0 = true) : StartB (histOf h0 c0 steps) := by
  unfold startCheck at hc
  split at hc
  · rename_i l0 r lr z lz z' z'' r' hnew hadds
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
      List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hz', hz''⟩, hr'⟩, hr⟩, hz⟩, hzr⟩, hlr⟩, hlrz⟩, hlz0⟩, hlz⟩, hobj⟩, hall⟩,
      hroots⟩ := hc
    rw [hz', hz'', hr'] at hadds
    refine ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, ?_, hroots⟩
    intro x hx
    show h0.objs[x]? = none
    cases ho : h0.objs[x]? with
    | none => rfl
    | some o =>
      have hm : (x, o) ∈ h0.objs.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ho
      exact absurd (hall (x, o) hm) hx
  · cases hc

/-- The heap before the j-th of the transactions `steps` that start from the
heap h. -/
def heapAt (h : Heap) : List TStep → Nat → Heap
  | _, 0 => h
  | [], _ + 1 => h
  | st :: rest, j + 1 => heapAt st.heap rest j

/-- The model's structure before the j-th of the transactions `steps`, the
first at time i on the structure P. -/
def structAt (P : Struct BVal) (i : Nat) : List TStep → Nat → Struct BVal
  | _, 0 => P
  | [], _ + 1 => P
  | st :: rest, j + 1 => structAt (P.apply i st.c) (i + 1) rest j

theorem heapAt_zero (h : Heap) (steps : List TStep) : heapAt h steps 0 = h := by
  cases steps <;> rfl

theorem structAt_zero (P : Struct BVal) (i : Nat) (steps : List TStep) :
    structAt P i steps 0 = P := by
  cases steps <;> rfl

theorem heapAt_succ : ∀ (steps : List TStep) (h : Heap) (j : Nat) (hj : j < steps.length),
    heapAt h steps (j + 1) = steps[j].heap
  | [], _, _, hj => by simp at hj
  | st :: rest, h, 0, _ => by simp [heapAt, heapAt_zero]
  | st :: rest, h, j + 1, hj => by
    simp only [heapAt, List.getElem_cons_succ]
    exact heapAt_succ rest st.heap j (by simpa using hj)

theorem structAt_succ : ∀ (steps : List TStep) (P : Struct BVal) (i j : Nat)
    (hj : j < steps.length),
    structAt P i steps (j + 1) = (structAt P i steps j).apply (i + j) steps[j].c
  | [], _, _, _, hj => by simp at hj
  | st :: rest, P, i, 0, _ => by simp [structAt]
  | st :: rest, P, i, j + 1, hj => by
    simp only [structAt, List.getElem_cons_succ]
    rw [structAt_succ rest (P.apply i st.c) (i + 1) j (by simpa using hj)]
    congr 1
    omega

/-- The checks of the j-th transaction, from the verdict on all of them. -/
theorem stepsOk_nth (p : Params) (sp : Spec BVal Nat) : ∀ (steps : List TStep) (i : Nat)
    (h : Heap) (P : Struct BVal), stepsOk p sp i h P steps = true →
    ∀ j (hj : j < steps.length),
      checkTx p (i + j) (heapAt h steps j) steps[j].ops steps[j].D steps[j].heap = true ∧
      checkBridgeTx sp (structAt P i steps j) (i + j) (heapAt h steps j) steps[j].D
        steps[j].heap steps[j].c = true ∧
      checkEvictTx sp (structAt P i steps j) (i + j) steps[j].heap steps[j].c = true
  | [], _, _, _, _, j, hj => by simp at hj
  | st :: rest, i, h, P, hc, 0, _ => by
    simp only [stepsOk, Bool.and_eq_true] at hc
    simp only [heapAt_zero, structAt_zero, Nat.add_zero, List.getElem_cons_zero]
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2⟩
  | st :: rest, i, h, P, hc, j + 1, hj => by
    simp only [stepsOk, Bool.and_eq_true] at hc
    have := stepsOk_nth p sp rest (i + 1) st.heap (P.apply i st.c) hc.2 j (by simpa using hj)
    have he : i + 1 + j = i + (j + 1) := by omega
    rw [he] at this
    exact this

section Hist

variable (h0 : Heap) (c0 : Changes BVal) (steps : List TStep)

theorem histOf_length : (histOf h0 c0 steps).txs.length = steps.length := by
  simp [histOf]

theorem histOf_tree (j : Nat) (hj : j ≤ steps.length) :
    (histOf h0 c0 steps).tree j = (heapAt h0 steps j).tree := by
  cases j with
  | zero => rw [heapAt_zero]; rfl
  | succ j =>
    have hj' : j < (histOf h0 c0 steps).txs.length := by rw [histOf_length]; exact hj
    rw [BHist.tree_succ _ hj', heapAt_succ steps h0 j hj]
    simp [histOf]

theorem histOf_c (j : Nat) (hj : j < steps.length) :
    ((histOf h0 c0 steps).txs[j]'(by rw [histOf_length]; exact hj)).c = steps[j].c := by
  simp [histOf]

theorem histOf_P : ∀ (j : Nat), j ≤ steps.length →
    (histOf h0 c0 steps).P j = structAt (histOf h0 c0 steps).p0 1 steps j
  | 0, _ => by rw [structAt_zero]; rfl
  | j + 1, hj => by
    have hj' : j < (histOf h0 c0 steps).txs.length := by rw [histOf_length]; exact hj
    rw [BHist.P_succ _ hj', structAt_succ steps _ 1 j hj, histOf_P j (Nat.le_of_succ_le hj),
      histOf_c h0 c0 steps j hj, Nat.add_comm 1 j]

/-- What the bridge checker computes for a whole trace gives a history that
meets the contract and the bridge's clauses, and what eviction needs
besides. -/
theorem bridgeHistoryOk_meets (p : Params) (hc : bridgeHistoryOk p h0 c0 steps = true) :
    MeetsBridge p (histOf h0 c0 steps) ∧ MeetsEvict (histOf h0 c0 steps) := by
  simp only [bridgeHistoryOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hstart, htree0⟩, hadopt0⟩, hsteps⟩ := hc
  have hlen := histOf_length h0 c0 steps
  have nth := stepsOk_nth p (histOf h0 c0 steps).spec steps 1 h0 (histOf h0 c0 steps).p0 hsteps
  have step : ∀ j (hj : j < steps.length),
      Contract p (j + 1) ((histOf h0 c0 steps).tree j) steps[j].ops steps[j].D
        ((histOf h0 c0 steps).tree (j + 1)) ∧
      (bridgeOk (histOf h0 c0 steps).topLevel (j + 1) ((histOf h0 c0 steps).tree j)
        ((histOf h0 c0 steps).tree (j + 1)) steps[j].D steps[j].c = true ∧
       Made ((histOf h0 c0 steps).tree j) ((histOf h0 c0 steps).tree (j + 1)) steps[j].c ∧
       TopOK (histOf h0 c0 steps).spec ((histOf h0 c0 steps).P j) (j + 1)
        ((histOf h0 c0 steps).tree j) ((histOf h0 c0 steps).tree (j + 1)) steps[j].c ∧
       TouchOK (histOf h0 c0 steps).spec ((histOf h0 c0 steps).P j) (j + 1) steps[j].c) ∧
      (TreeOk (((histOf h0 c0 steps).tree (j + 1)).at (j + 1)) ∧
       SIS.adoptAt (histOf h0 c0 steps).spec ((histOf h0 c0 steps).P (j + 1)) (j + 1) ∧
       SIS.CopyStep (histOf h0 c0 steps).spec ((histOf h0 c0 steps).P j) (j + 1) steps[j].c) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := nth j hj
    rw [Nat.add_comm 1 j] at h1 h2 h3
    have ht := histOf_tree h0 c0 steps j (Nat.le_of_lt hj)
    have ht' : (histOf h0 c0 steps).tree (j + 1) = steps[j].heap.tree := by
      rw [histOf_tree h0 c0 steps (j + 1) hj, heapAt_succ steps h0 j hj]
    have hP := histOf_P h0 c0 steps j (Nat.le_of_lt hj)
    have hP' : (histOf h0 c0 steps).P (j + 1) =
        ((histOf h0 c0 steps).P j).apply (j + 1) steps[j].c := by
      rw [histOf_P h0 c0 steps (j + 1) hj, structAt_succ steps _ 1 j hj, ← hP, Nat.add_comm 1 j]
    rw [ht, ht', hP, hP', ← hP]
    rw [← hP] at h2 h3
    exact ⟨checkTx_sound p _ _ _ _ _ h1, checkBridgeTx_sound _ h2, checkEvictTx_sound _ h3⟩
  refine ⟨⟨startCheck_sound c0 h0 steps hstart, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro j hj
    have hj' : j < steps.length := by rw [← hlen]; exact hj
    have hs := step j hj'
    have hops : (histOf h0 c0 steps).txs[j].ops = steps[j].ops := by simp [histOf]
    have hD : (histOf h0 c0 steps).txs[j].D = steps[j].D := by simp [histOf]
    rw [hops, hD, histOf_c h0 c0 steps j hj']
    exact ⟨hs.1, hs.2.1.1, hs.2.1.2.1, hs.2.1.2.2.1, hs.2.1.2.2.2⟩
  · intro j hj
    cases j with
    | zero => exact treeOkB_sound _ htree0
    | succ j => exact (step j (by rw [← hlen]; exact hj)).2.2.1
  · intro j hj
    cases j with
    | zero => exact adoptB_sound _ hadopt0
    | succ j => exact (step j (by rw [← hlen]; exact hj)).2.2.2.1
  · intro j hj
    have hj' : j < steps.length := by rw [← hlen]; exact hj
    rw [histOf_c h0 c0 steps j hj']
    exact (step j hj').2.2.2.2

end Hist

/-! ## A whole trace, in the contract's words -/

theorem topBefore_zero (tp : Top) (steps : List TStep) : topBefore tp steps 0 = tp := by
  cases steps <;> rfl

theorem topBefore_succ : ∀ (steps : List TStep) (tp : Top) (j : Nat) (hj : j < steps.length),
    topBefore tp steps (j + 1) = steps[j].top
  | [], _, _, hj => by simp at hj
  | st :: rest, tp, 0, _ => by simp [topBefore, topBefore_zero]
  | st :: rest, tp, j + 1, hj => by
    simp only [topBefore, List.getElem_cons_succ]
    exact topBefore_succ rest st.top j (by simpa using hj)

/-- The checks of the j-th transaction, from the verdict on all of them. -/
theorem fullStepsOk_nth (p : Params) (tl : Nat) : ∀ (steps : List TStep) (i : Nat)
    (h : Heap) (tp : Top) (P : Struct BVal), fullStepsOk p tl i h tp P steps = true →
    ∀ j (hj : j < steps.length),
      fullTx p tl (structAt P i steps j) (i + j) (heapAt h steps j) (topBefore tp steps j) steps[j]
        = true
  | [], _, _, _, _, _, j, hj => by simp at hj
  | st :: rest, i, h, tp, P, hc, 0, _ => by
    simp only [fullStepsOk, Bool.and_eq_true] at hc
    simp only [heapAt_zero, structAt_zero, topBefore_zero, Nat.add_zero, List.getElem_cons_zero]
    exact hc.1
  | st :: rest, i, h, tp, P, hc, j + 1, hj => by
    simp only [fullStepsOk, Bool.and_eq_true] at hc
    have := fullStepsOk_nth p tl rest (i + 1) st.heap st.top (P.apply i st.c) hc.2 j
      (by simpa using hj)
    have he : i + 1 + j = i + (j + 1) := by omega
    rw [he] at this
    exact this

/-- What the bridge checker computes for a whole trace, in the contract's
words, gives a history that meets every clause in the contract's words
(`MeetsFull`): so it meets `MeetsBridge` and `MeetsEvict`
(Proof/BridgeWords.lean), and the theorems of BridgeTheorems.lean hold for
the tree and the top that the trace's lines give. -/
theorem fullHistoryOk_meets (p : Params) (h0 : Heap) (c0 : Changes BVal) (tp0 : Top)
    (steps : List TStep) (hc : fullHistoryOk p h0 c0 tp0 steps = true) :
    MeetsFull p (histOf h0 c0 steps) (topBefore tp0 steps) := by
  simp only [fullHistoryOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hstart, htop0⟩, htree0⟩, hadopt0⟩, hsteps⟩ := hc
  have hlen := histOf_length h0 c0 steps
  have nth := fullStepsOk_nth p _ steps 1 h0 tp0 (histOf h0 c0 steps).p0 hsteps
  have step : ∀ j (hj : j < steps.length),
      fullTx p (histOf h0 c0 steps).topLevel ((histOf h0 c0 steps).P j) (j + 1)
        (heapAt h0 steps j) (topBefore tp0 steps j) steps[j] = true ∧
      (histOf h0 c0 steps).tree j = (heapAt h0 steps j).tree ∧
      (histOf h0 c0 steps).tree (j + 1) = steps[j].heap.tree ∧
      topBefore tp0 steps (j + 1) = steps[j].top := by
    intro j hj
    have h1 := nth j hj
    rw [Nat.add_comm 1 j, ← histOf_P h0 c0 steps j (Nat.le_of_lt hj)] at h1
    refine ⟨h1, histOf_tree h0 c0 steps j (Nat.le_of_lt hj), ?_, topBefore_succ steps tp0 j hj⟩
    rw [histOf_tree h0 c0 steps (j + 1) hj, heapAt_succ steps h0 j hj]
  refine { start := startCheck_sound c0 h0 steps hstart, startTop := ?_, step := ?_, tree := ?_,
           adopt := ?_ }
  · rw [topBefore_zero]
    exact htop0
  · intro j hj
    have hj' : j < steps.length := by rw [← hlen]; exact hj
    obtain ⟨h1, ht, ht', htp'⟩ := step j hj'
    have hops : (histOf h0 c0 steps).txs[j].ops = steps[j].ops := by simp [histOf]
    have hD : (histOf h0 c0 steps).txs[j].D = steps[j].D := by simp [histOf]
    rw [hops, hD, histOf_c h0 c0 steps j hj', ht, ht', htp']
    simp only [fullTx, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, _⟩, _⟩ := h1
    exact ⟨checkTx_sound p _ _ _ _ _ a1, a2, madeCheck_sound _ _ _ a3, topStepB_sound _ _ _ a4,
      a5, a6, a7, a8⟩
  · intro j hj
    cases j with
    | zero => exact treeOkB_sound _ htree0
    | succ j =>
      have hj' : j < steps.length := by rw [← hlen]; exact hj
      obtain ⟨h1, _, ht', _⟩ := step j hj'
      simp only [fullTx, Bool.and_eq_true] at h1
      rw [ht']
      exact treeOkB_sound _ h1.1.2
  · intro j hj
    cases j with
    | zero => exact hadopt0
    | succ j =>
      have hj' : j < steps.length := by rw [← hlen]; exact hj
      obtain ⟨h1, _, ht', _⟩ := step j hj'
      simp only [fullTx, Bool.and_eq_true] at h1
      rw [ht']
      exact h1.2

end Contract
