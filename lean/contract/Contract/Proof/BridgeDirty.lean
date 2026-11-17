/-
The contract package (bergdb 030-07): D as state (bergdb 030-06, finding 5).
The contract's D is a parameter that nothing in the contract ties to the
transactions before. In the abstract model D is state: the dirty nodes after
the transaction before, and the nodes that the transaction's step 3 marks
(the access path of its change, and its touch). `frame_modelD` proves that
the frame, clause 3 of the contract, holds with the model's D: every key node
that a transaction changes or makes is in it.
-/
import Mathlib.Tactic
import SIS.Proof.Mark
import SIS.Proof.Util
import Contract.Proof.BridgeStep

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

section Step

variable {p : Params} {h : BHist} {j : Nat} {hj : j < h.txs.length}

/-- A key node of before that the transaction changed got at least one klong
after its time klong. -/
theorem StepFacts.ext_more (f : StepFacts p h j hj) {x : NodeId} {n n' : KNode}
    (hn : (h.tree j).obj x = some (.key n)) (hn' : (h.tree (j + 1)).obj x = some (.key n'))
    (hne : n'.ks ≠ n.ks) :
    ∃ k more, n'.ks = n.ks ++ Klong.time (j + 1) :: k :: more ∧
      (k :: more).all (fun k => !k.isTime) = true := by
  have hD : x ∈ h.txs[j].D := by
    by_contra hD
    obtain ⟨o', ho', _, hsame⟩ := f.contract.2.1 x _ hn
    have := hsame hD
    rw [this] at ho'
    rw [hn'] at ho'
    injection ho' with ho'
    injection ho' with ho'
    exact hne (by rw [ho'])
  have hl := (f.local_of hD hn').1
  rw [hn] at hl
  have hlen : n.ks.length + 1 < n'.ks.length := by
    simp only [extKs4, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hl
    rcases hl with hl | hl
    · exact absurd hl hne
    · exact hl.2
  rcases extKs4_sound hl with h1 | ⟨more, h1, h2⟩
  · exact absurd h1 hne
  · cases more with
    | nil =>
      rw [h1] at hlen
      simp at hlen
    | cons k more => exact ⟨k, more, h1, h2⟩

/-- A key node that the transaction changed or made is changed in the model:
it is made by the change, or gets an entry. -/
theorem StepFacts.changed_of (f : StepFacts p h j hj) {x : NodeId} {n' : KNode}
    (hn' : (h.tree (j + 1)).obj x = some (.key n'))
    (hch : (h.tree j).obj x ≠ some (.key n')) : SIS.changed h.txs[j].c x = true := by
  unfold SIS.changed
  rw [Bool.or_eq_true]
  cases ho : (h.tree j).obj x with
  | none =>
    left
    have hmem := f.made x ho (by rw [hn']; rfl)
    obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hmem
    exact List.any_eq_true.mpr ⟨nn, hnn, by simpa using hid⟩
  | some o =>
    right
    rcases f.key_cases hn' with ⟨n, hn, hlev, _⟩ | ⟨hno, _⟩
    · have hleaf : n'.leaf = n.leaf := by
        obtain ⟨o', ho', hext, _⟩ := f.contract.2.1 x _ hn
        rw [hn'] at ho'
        injection ho' with ho'
        subst ho'
        exact hext.2.1
      have hne : n'.ks ≠ n.ks := by
        intro heq
        apply hch
        rw [hn]
        cases n; cases n'
        simp_all
      obtain ⟨k, more, hks, hall⟩ := f.ext_more hn hn' hne
      have hK := f.adds_all x (by rw [hn']; rfl)
      unfold newVals at hK
      rw [hn', hn] at hK
      simp only at hK
      rw [hks, entriesOf_append, List.drop_left] at hK
      have hnonempty : (h.txs[j].c.adds.filter (fun a => a.1 == x)) ≠ [] := by
        intro hnil
        rw [hnil] at hK
        simp only [List.map_nil, entriesFrom] at hK
        simp only [List.all_cons, Bool.and_eq_true] at hall
        cases k with
        | time t => simp [Klong.isTime] at hall
        | key c y => simp [entriesFrom] at hK
        | del b => simp [entriesFrom] at hK
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hnonempty
      rw [List.mem_filter] at ha
      exact List.any_eq_true.mpr ⟨a, ha.1, ha.2⟩
    · rw [ho] at hno; cases hno

end Step

/-- D as state. For every transaction of a bridged history, the frame holds
with the model's D in place of the contract's: the dirty nodes after the
transaction before (the model's state), and the nodes that the model's step 3
marks for this transaction (with marking, BergDB's way). So the contract's D
need not be given: it is the model's. -/
theorem frame_modelD {p : Params} {h : BHist} (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hmk : al.mark = true) (j : Nat) (hj : j < h.txs.length) :
    let db := SIS.run h.spec al (h.ts.take j)
    let c := h.txs[j].c
    let P' := h.P (j + 1)
    let vs0 := SIS.writeAll h.spec db.S (j + 1) P' ((c.new.filter (·.isData)).map (·.id)) []
    Frame (j + 1) (h.tree j)
      (db.D.map (·.1) ++ SIS.gotDirty3 h.spec al db.S vs0 P' c db.D (j + 1)) (h.tree (j + 1)) := by
  intro db c P' vs0
  have f := hm.facts j hj
  have hi := hm.binv j (Nat.le_of_lt hj)
  have hi' := hm.binv (j + 1) hj
  have hstep := f.stepOK hi hi'
  obtain ⟨f1, f2, f3⟩ := f.contract.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs0, _⟩ := hi'.link
  have hP' : P' = (h.P j).apply (j + 1) c := h.P_succ hj
  -- A key node changed in the model is in the model's D.
  have key : ∀ x n', (h.tree (j + 1)).obj x = some (.key n') → SIS.changed c x = true →
      x ∈ db.D.map (·.1) ++ SIS.gotDirty3 h.spec al db.S vs0 P' c db.D (j + 1) := by
    intro x n' hn' hch
    rw [List.mem_append]
    by_cases hin : SIS.inD db.D x = true
    · left
      obtain ⟨d, hd⟩ := (SIS.inD_iff db.D x).mp hin
      exact List.mem_map.mpr ⟨(x, d), hd, rfl⟩
    · right
      have hNx : P'.get? x =
          some { level := n'.level, isData := false, hist := entriesOf n'.ks } := hi'.rep x _ hn'
      have hxr : x ≠ SIS.root := by
        rintro rfl
        rw [hs0] at hn'; cases hn'
      have hreach : SIS.reachable h.spec P' (j + 1) x = true := by
        rw [hP']
        unfold SIS.changed at hch
        rw [Bool.or_eq_true] at hch
        rcases hch with h1 | h1
        · obtain ⟨nn, hnn, hid⟩ := List.any_eq_true.mp h1
          have := hstep.newReachable nn hnn
          rwa [show nn.id = x by simpa using hid] at this
        · obtain ⟨a, ha, hid⟩ := List.any_eq_true.mp h1
          have := hstep.current a ha
          rwa [show a.1 = x by simpa using hid] at this
      unfold SIS.gotDirty3
      simp only [hmk, ite_true]
      rw [List.mem_filter]
      refine ⟨List.mem_append_left _ ?_, by simp [SIS.written, hxr]⟩
      unfold SIS.markOf
      rw [List.mem_mergeSort, List.mem_filter]
      refine ⟨(SIS.mem_allIds P' x).mpr (by rw [hNx]; rfl), ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨by simp [SIS.isIndex, hNx], by simpa using hin⟩, ?_⟩
      unfold SIS.marked
      rw [Bool.and_eq_true]
      refine ⟨hreach, ?_⟩
      rw [hNx]
      exact List.any_eq_true.mpr ⟨x, SIS.self_mem_reachFrom _ _ _ _ _, hch⟩
  refine ⟨?_, ?_, f3⟩
  · intro x o ho
    obtain ⟨o', ho', hext, _⟩ := f1 x o ho
    refine ⟨o', ho', hext, ?_⟩
    intro hnD
    by_contra hne
    cases o' with
    | val v' =>
      cases o with
      | val v => exact hne (by have : v' = v := hext; rw [this])
      | key n => exact absurd hext (by simp [Ext])
    | key n' =>
      exact hnD (key x n' ho' (f.changed_of ho' (by
        rw [ho]
        intro heq
        injection heq with heq
        exact hne heq.symm)))
  · intro x n hx hno
    exact key x n hx (f.changed_of hx (by rw [hno]; simp))

end Contract
