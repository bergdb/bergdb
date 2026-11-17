/-
The contract package (bergdb 030-07): the computed clauses in the model's
words (BridgeModel.lean) give the clauses: `touchB_sound`, `adoptB_sound`,
`copyB_sound`, `virtB_sound`, `topLinkB_sound`, `topOkB_sound`.
-/
import SIS.Proof.Mark
import Contract.BridgeHeap

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal)

variable (sp : Spec BVal Nat)

/-! ## The touch -/

theorem touchB_sound {P : Struct BVal} {i : Nat} {c : Changes BVal}
    (h : touchB sp P i c = true) : TouchOK sp P i c := by
  simp only [touchB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun x hx => h2 x hx, ?_⟩
  intro x hx q nq hq hnq hsub
  rcases h3 with h3 | h3
  · rw [List.isEmpty_iff] at h3
    rw [h3] at hx
    simp at hx
  · have hq' : q ∈ SIS.reachList sp P (i - 1) := by
      simpa [SIS.reachable] using hq
    rcases h3 q hq' with (h4 | h4) | h4
    · exact Or.inl (by simpa using h4)
    · exact Or.inr (by simpa using h4)
    · exfalso
      rw [hnq] at h4
      have := List.all_eq_true.mp h4 x hx
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
      exact this hsub

/-! ## A6' -/

theorem adoptB_sound {P : Struct BVal} {i : Nat} (h : adoptB sp P i = true) :
    SIS.adoptAt sp P i := by
  simp only [adoptB, List.all_eq_true] at h
  intro x n hx hn y hy hnl
  have hx' : x ∈ SIS.reachList sp P i := by simpa [SIS.reachable] using hx
  have h1 := h x hx'
  rw [hn] at h1
  have h2 := List.all_eq_true.mp h1 y hy
  simp only [Bool.or_eq_true] at h2
  rcases h2 with ((h3 | h3) | h3) | h3
  · exact absurd (by simpa using h3) hnl
  · right; left
    simpa [SIS.reachable] using h3
  · left
    cases hy' : P.get? y with
    | none => rw [hy'] at h3; simp at h3
    | some ny =>
      rw [hy'] at h3
      exact ⟨ny, rfl, h3⟩
  · right; right
    simpa using h3

/-! ## A-COPY -/

theorem copyB_sound {P : Struct BVal} {i : Nat} {c : Changes BVal}
    (h : copyB sp P (P.apply i c) i c = true) : SIS.CopyStep sp P i c := by
  simp only [copyB, List.all_eq_true, Bool.or_eq_true] at h
  -- A node of S is a node of the writer's paths.
  have hS : ∀ z, z ∈ (SIS.reachList sp P (i - 1)).filter (fun z => SIS.changed c z ||
      c.touch.contains z || ((SIS.reachList sp P (i - 1)).contains z &&
        !(SIS.reachList sp (P.apply i c) i).contains z)) → z ∈ SIS.pathOf sp P c i := by
    intro z hz
    rw [List.mem_filter] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hr : SIS.reachable sp P (i - 1) z = true := by simpa [SIS.reachable] using hz1
    have hsome := ((SIS.reachable_iff sp P (i - 1) z).mp hr).isSome
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
    unfold SIS.pathOf
    simp only [List.mem_filter, List.mem_eraseDups]
    refine ⟨hz1, ?_⟩
    rw [hn]
    exact List.any_eq_true.mpr ⟨z, SIS.self_mem_reachFrom sp P (i - 1) z n, hz2⟩
  intro a ha y hy hnew
  rcases h a ha y hy with (h1 | h1) | h1
  · exact absurd (by simpa using h1) hnew
  · left
    exact hS y (by simpa using h1)
  · right
    obtain ⟨z, hz, hz2⟩ := List.any_eq_true.mp h1
    cases hnz : P.get? z with
    | none => rw [hnz] at hz2; simp at hz2
    | some nz =>
      rw [hnz] at hz2
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hz2
      exact ⟨z, hS z hz, nz, hnz, hz2.1, hz2.2⟩

/-! ## The top -/

theorem virtB_sound {P : Struct BVal} {i : Nat} {c : Changes BVal}
    (h : virtB sp P (P.apply i c) i c = true) : SIS.VirtStep sp P i c := by
  simp only [virtB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine { newTop := ?_, topFixed := ?_, rootAdds := ?_, closure := ?_, dead := ?_ }
  · intro nn hnn hl
    have := List.all_eq_true.mp h1 nn hnn
    simp only [hl, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Bool.not_eq_true'] at this
    obtain ⟨⟨h6, h7⟩, h8⟩ := this
    refine ⟨h6, ?_, ?_⟩
    · obtain ⟨a, ha, ha2⟩ := List.any_eq_true.mp h7
      exact ⟨a, ha, by simpa using ha2⟩
    · intro nn' hnn' hl'
      have := List.all_eq_true.mp h8 nn' hnn'
      simpa [hl'] using this
  · intro a ha n hn hne
    have := List.all_eq_true.mp h2 a ha
    rw [hn] at this
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with h6 | h6
    · exact absurd h6 hne
    · exact h6
  · exact of_decide_eq_true h3
  · intro nn hnn hl n hn y m hy hne hlm
    have := List.all_eq_true.mp h4 nn hnn
    simp only [hl, decide_true, Bool.not_true, Bool.false_or] at this
    rw [hn] at this
    have h6 := SIS.TopBridge.r4Fast_sound sp P i c nn.id n hn this
    rw [List.filter_eq_nil_iff] at h6
    have h7 := h6 y (SIS.TopBridge.mem_allIds_of_get? hy)
    have h8 : SIS.isTop sp P y = true := by simp [SIS.isTop, hy, hne, hlm]
    simpa [h8] using h7
  · intro z n hz htop y hy hytop
    have h6 := List.all_eq_true.mp h5 (z, n) (SIS.mem_of_get? hz)
    simp only [SIS.isTop, hz, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at htop
    simp only [Bool.or_eq_true, beq_iff_eq, htop.2, decide_true, Bool.not_true,
      Bool.false_eq_true, or_false] at h6
    rcases h6 with h6 | h6
    · exact absurd h6 htop.1
    · have h7 := List.all_eq_true.mp h6 y hy
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at h7
      rcases h7 with h7 | h7
      · simpa [SIS.reachable] using h7
      · rw [hytop] at h7; cases h7

theorem topLinkB_sound {P : Struct BVal} {i : Nat} {s : Tree} (h : topLinkB sp P i s = true) :
    TopLink sp P i s := by
  unfold topLinkB at h
  split at h
  · rename_i n0 h0
    split at h
    · rename_i z hl0
      split at h
      · rename_i nz hz
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hlt, h⟩ := h
        split at h
        · rename_i y hly
          simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
          obtain ⟨⟨⟨hroot, hy⟩, hs0⟩, hsz⟩ := h
          split at hy
          · rename_i n hobj
            exact ⟨n0, z, nz, y, n, h0, hl0, hz, hlt, hly, hroot, hobj, by simpa using hy, hs0, hsz⟩
          · cases hy
        · cases h
      · cases h
    · cases h
  · cases h

theorem topOkB_sound {P : Struct BVal} {i : Nat} {s s' : Tree} {c : Changes BVal}
    (h : topOkB sp P (P.apply i c) i s s' c = true) : TopOK sp P i s s' c := by
  simp only [topOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have adds : ∀ a ∈ c.adds, s'.obj a.1 = none →
      (SIS.reachList sp (P.apply i c) i).contains a.1 = true ∧
      (match P.get? a.1 with
        | some n => !n.isData
        | none => true) = true ∧
      (sp.ptrs a.2).all (fun y => match (P.apply i c).get? a.1, (P.apply i c).get? y with
        | some n, some m => decide (m.level < n.level)
        | _, _ => false) = true := by
    intro a ha hno
    have := List.all_eq_true.mp h3 a ha
    simp only [hno, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine { virt := virtB_sound sp h1, fresh := ?_, current := ?_, dataFixed := ?_, levels := ?_,
           newReachable := ?_, noRes := ?_, link := topLinkB_sound sp h6 }
  · intro nn hnn hno
    have := List.all_eq_true.mp h2 nn hnn
    simpa [hno] using this
  · intro a ha hno
    exact (adds a ha hno).1
  · intro a ha hno n hn
    have := (adds a ha hno).2.1
    rw [hn] at this
    simpa using this
  · intro a ha hno y hy
    have := List.all_eq_true.mp (adds a ha hno).2.2 y hy
    cases hn : (P.apply i c).get? a.1 with
    | none => rw [hn] at this; simp at this
    | some n =>
      cases hm : (P.apply i c).get? y with
      | none => rw [hn, hm] at this; simp at this
      | some m =>
        rw [hn, hm] at this
        exact ⟨n, m, rfl, rfl, by simpa using this⟩
  · intro nn hnn hno
    have := List.all_eq_true.mp h4 nn hnn
    simpa [hno, SIS.reachable] using this
  · intro y hno hy
    have hy' : y ∈ SIS.reachList sp (P.apply i c) i := by simpa [SIS.reachable] using hy
    have := List.all_eq_true.mp h5 y hy'
    simp only [hno, Option.isSome_none, Bool.false_or, Bool.or_eq_true] at this
    rcases this with h7 | h7
    · exact Or.inl h7
    · exact Or.inr (by simpa using h7)

/-! ## One traced transaction -/

/-- What the bridge checker computes for a transaction gives the bridge's
clauses for it. -/
theorem checkBridgeTx_sound {P : Struct BVal} {i : Nat} {h h' : Heap} {D : List NodeId}
    {c : Changes BVal} (hc : checkBridgeTx sp P i h D h' c = true) :
    bridgeOk sp.topLevel i h.tree h'.tree D c = true ∧ Made h.tree h'.tree c ∧
    TopOK sp P i h.tree h'.tree c ∧ TouchOK sp P i c := by
  simp only [checkBridgeTx, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, madeCheck_sound h h' c hc.1.1.2, topOkB_sound sp hc.1.2, touchB_sound sp hc.2⟩

/-- What the bridge checker computes for eviction gives TREE and A6' after the
transaction, and A-COPY for its change. -/
theorem checkEvictTx_sound {P : Struct BVal} {i : Nat} {h' : Heap} {c : Changes BVal}
    (hc : checkEvictTx sp P i h' c = true) :
    TreeOk (h'.tree.at i) ∧ SIS.adoptAt sp (P.apply i c) i ∧ SIS.CopyStep sp P i c := by
  simp only [checkEvictTx, Bool.and_eq_true] at hc
  exact ⟨treeOkB_sound _ hc.1.1, adoptB_sound sp hc.1.2, copyB_sound sp hc.2⟩

end Contract
