/-
Proofs, part 9: one transaction keeps the facts about the structure P.
-/
import SIS.Proof.StepFacts

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- A node after the transaction: an old node with entries added, or a new one. -/
theorem step_node_cases {k : Nat} (hlen : db.S.length = k + 1) {x : NodeId} {n' : Node V}
    (h : (parts sp al db tr).P.get? x = some n') :
    (∃ n, db.P.get? x = some n ∧ n' = { n with hist := n.hist ++ addsFor (parts sp al db tr).c (k + 1) x }) ∨
    (db.P.get? x = none ∧ ∃ nn ∈ (parts sp al db tr).c.new, nn.id = x ∧
      n' = { level := nn.level, isData := nn.isData, hist := addsFor (parts sp al db tr).c (k + 1) x }) := by
  cases hx : db.P.get? x with
  | some n =>
    left
    rw [step_P_old sp al db tr hlen hx] at h
    exact ⟨n, rfl, (Option.some.inj h).symm⟩
  | none =>
    right
    rw [step_P_new sp al db tr hlen hx] at h
    cases hm : newNodeOf (parts sp al db tr).c x with
    | none => rw [hm] at h; simp at h
    | some m =>
      rw [hm] at h
      obtain ⟨nn, hnn, hid, rfl⟩ := newNodeOf_some hm
      refine ⟨rfl, nn, hnn, hid, ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      simp

/-- The facts about P after the transaction. -/
structure PFacts (sp : Spec V T) (P : Struct V) (k : Nat) : Prop where
  times : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ k
  ptrs : PtrsOK sp P
  data : ∀ x n, P.get? x = some n → n.isData = true → ∀ e ∈ n.hist, sp.ptrs e.val = []
  er : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, reachable sp P e.time x = true
  rootIn : (P.get? root).isSome
  born : ∀ x, (P.get? x).isSome → ∃ t ≤ k, reachable sp P t x = true

theorem step_pfacts (hok : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    PFacts sp (parts sp al db tr).P (k + 1) := by
  have hlen := hinv.len
  have hg := step_grow sp al db tr hlen
  have hP := parts_P' sp al db tr hlen
  have hls : LiveSub sp := hok.liveSub
  have hreach : ∀ t ≤ k, ∀ x, reachable sp (parts sp al db tr).P t x = reachable sp db.P t x :=
    fun t ht x => reachable_grow hls hinv.ptrs hinv.rootIn hg ht x
  constructor
  · intro x n' hn' e he
    rcases step_node_cases sp al db tr hlen hn' with ⟨n, hn, rfl⟩ | ⟨-, nn, -, -, rfl⟩
    · simp only [List.mem_append] at he
      rcases he with he | he
      · have := hinv.times x n hn e he; omega
      · rw [mem_addsFor] at he; omega
    · rw [mem_addsFor] at he; omega
  · intro x n' hn' e he y hy
    rcases step_node_cases sp al db tr hlen hn' with ⟨n, hn, rfl⟩ | ⟨-, nn, -, -, rfl⟩
    · simp only [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨m, hm, hlt⟩ := hinv.ptrs x n hn e he y hy
        exact ⟨_, step_P_old sp al db tr hlen hm, hlt⟩
      · rw [mem_addsFor] at he
        obtain ⟨n2, m, h1, h2, h3⟩ := hstep.levels (x, e.val) he.2 y hy
        rw [← hP] at h1 h2
        rw [step_P_old sp al db tr hlen hn] at h1
        cases h1
        exact ⟨m, h2, h3⟩
    · rw [mem_addsFor] at he
      obtain ⟨n2, m, h1, h2, h3⟩ := hstep.levels (x, e.val) he.2 y hy
      rw [← hP] at h1 h2
      rw [hn'] at h1
      cases h1
      exact ⟨m, h2, h3⟩
  · intro x n' hn' hd e he
    rcases step_node_cases sp al db tr hlen hn' with ⟨n, hn, rfl⟩ | ⟨-, nn, hnn, hid, rfl⟩
    · simp only [List.mem_append] at he
      rcases he with he | he
      · exact hinv.data x n hn hd e he
      · rw [mem_addsFor] at he
        have := hstep.dataFixed (x, e.val) he.2 n hn
        simp at hd
        rw [hd] at this
        simp at this
    · rw [mem_addsFor] at he
      exact hstep.dataNoPtrs (x, e.val) he.2 nn hnn hid hd
  · intro x n' hn' e he
    rcases step_node_cases sp al db tr hlen hn' with ⟨n, hn, rfl⟩ | ⟨-, nn, -, -, rfl⟩
    · simp only [List.mem_append] at he
      rcases he with he | he
      · rw [hreach e.time (hinv.times x n hn e he)]
        exact hinv.er x n hn e he
      · rw [mem_addsFor] at he
        rw [he.1, hP]
        exact hstep.current (x, e.val) he.2
    · rw [mem_addsFor] at he
      rw [he.1, hP]
      exact hstep.current (x, e.val) he.2
  · obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    rw [step_P_old sp al db tr hlen h0]; rfl
  · intro x hx
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hx
    rcases step_node_cases sp al db tr hlen hn' with ⟨n, hn, -⟩ | ⟨-, nn, hnn, hid, -⟩
    · obtain ⟨t, ht, hr⟩ := hinv.born x (by simp [hn])
      exact ⟨t, by omega, by rw [hreach t ht]; exact hr⟩
    · refine ⟨k + 1, Nat.le_refl _, ?_⟩
      rw [hP, ← hid]
      exact hstep.newReachable nn hnn

/-- isIndex of an old node does not change. -/
theorem step_isIndex_old {k : Nat} (hlen : db.S.length = k + 1) {x : NodeId}
    (h : (db.P.get? x).isSome) : isIndex (parts sp al db tr).P x = isIndex db.P x := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
  simp only [isIndex, step_P_old sp al db tr hlen hn, hn]

end Step

end SIS
