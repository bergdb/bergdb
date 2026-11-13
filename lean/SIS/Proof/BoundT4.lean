/-
Proofs for bounds, part 2 (bergdb item 007): T4, the records at the ends of
the startup section and the debt of D (SIS/BoundT4.lean).
-/
import SIS.BoundT4
import SIS.Proof.HandleCutLater
import SIS.Proof.HandleCutSkip
import SIS.Proof.LogicFacts
import SIS.Proof.BoundTake
import SIS.Theorems

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The record of a transaction -/

section Record

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The nodes of the versions of R(i): the data nodes that T(i) creates, then
the nodes taken. -/
theorem t4_vs_nodes :
    (parts sp al db tr).vs.map (·.node) =
      (((parts sp al db tr).c.new.filter (·.isData)).map (·.id)).filter
          (fun x => ((parts sp al db tr).P.get? x).isSome) ++
        (parts sp al db tr).taken.filter (fun x => ((parts sp al db tr).P.get? x).isSome) := by
  rw [parts_vs, writeAll_nodes, parts_vs0, writeAll_nodes]
  simp

/-- The nodes taken are nodes of D before the transaction. -/
theorem step_taken_of {k : Nat} (hlen : db.S.length = k + 1) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : inD db.D x = true := by
  obtain ⟨d, hd, hds⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hlen _).mp hd with h | ⟨h, -⟩
  · exact (inD_iff _ _).mpr ⟨d, h⟩
  · exfalso; simp only at h; have := step_s_le sp al db tr hlen; omega

/-- There are at most |D| nodes taken. -/
theorem step_taken_length {k : Nat} (hlen : db.S.length = k + 1) :
    (parts sp al db tr).taken.length ≤ db.D.length := by
  rw [parts_taken, (byLevel_perm _ _).length_eq, List.length_map, parts_D1, List.filter_append]
  have hs := step_s_le sp al db tr hlen
  have h2 : ((parts sp al db tr).gd3.map (fun x => (x, db.S.length))).filter
      (fun e : NodeId × Nat => decide (e.2 ≤ (parts sp al db tr).s)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
    simp only [decide_eq_true_eq]
    omega
  rw [h2, List.append_nil]
  exact List.length_filter_le _ _

/-- The nodes that got dirty in step 3 were not in D. -/
theorem step_gd3_not_inD {x : NodeId} (hx : x ∈ (parts sp al db tr).gd3) : inD db.D x = false := by
  rw [parts_gd3] at hx
  have hx' := (List.mem_filter.mp hx).1
  rcases List.mem_append.mp hx' with h | h
  · split at h
    · unfold markOf at h
      have := (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp h)).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    · unfold gotDirtyOf at h
      have := (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp h)).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
  · unfold touchOf at h
    have := (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp h)).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1.2

/-- T4 for one transaction: its record holds versions of the data nodes it
creates and of nodes of D, and of D's nodes in gd(i) at most |D|. -/
theorem recordByDebt_step {k : Nat} (hlen : db.S.length = k + 1) : RecordByDebt sp al db tr := by
  have hc : sp.exec tr db.S.length (view sp db.P (db.S.length - 1)) = (parts sp al db tr).c := rfl
  show ∃ R : Record V T, (step sp al db tr).S = db.S ++ [R] ∧ R.trans = some tr ∧
    (∀ v ∈ R.vers, v.node ∈ ((sp.exec tr db.S.length (view sp db.P (db.S.length - 1))).new.filter
        (·.isData)).map (·.id) ∨ inD db.D v.node = true) ∧
    R.vers.length ≤ ((sp.exec tr db.S.length (view sp db.P (db.S.length - 1))).new.filter
        (·.isData)).length + db.D.length ∧
    (R.gd.filter (inD db.D)).length ≤ db.D.length
  rw [hc]
  refine ⟨(parts sp al db tr).R, rfl, rfl, ?_, ?_, ?_⟩
  · intro v hv
    rw [parts_R] at hv
    have hn : v.node ∈ (parts sp al db tr).vs.map (·.node) := List.mem_map_of_mem hv
    rw [t4_vs_nodes] at hn
    rcases List.mem_append.mp hn with h | h
    · exact Or.inl (List.mem_filter.mp h).1
    · exact Or.inr (step_taken_of sp al db tr hlen (List.mem_filter.mp h).1)
  · rw [parts_R]
    show (parts sp al db tr).vs.length ≤ _
    rw [← List.length_map (f := (·.node)), t4_vs_nodes, List.length_append]
    have h1 := List.length_filter_le (fun x => ((parts sp al db tr).P.get? x).isSome)
      (((parts sp al db tr).c.new.filter (·.isData)).map (·.id))
    have h2 := List.length_filter_le (fun x => ((parts sp al db tr).P.get? x).isSome)
      (parts sp al db tr).taken
    have h3 := step_taken_length sp al db tr hlen
    rw [List.length_map] at h1
    omega
  · rw [parts_R]
    show (((parts sp al db tr).gd3 ++ (parts sp al db tr).r7.2).filter (inD db.D)).length ≤ _
    rw [List.filter_append]
    have h1 : (parts sp al db tr).gd3.filter (inD db.D) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      rw [step_gd3_not_inD sp al db tr hx]
      simp
    rw [h1, List.nil_append]
    have hsub : (parts sp al db tr).r7.2.Sublist (parts sp al db tr).taken := by
      obtain ⟨M, hM, h⟩ := stillDirtyOf_shape al (parts sp al db tr).S' (parts sp al db tr).P
        (parts sp al db tr).D2 db.S.length (parts sp al db tr).taken
      rw [← parts_r7] at h
      rw [h]; exact hM
    exact Nat.le_trans (List.length_filter_le _ _)
      (Nat.le_trans hsub.length_le (step_taken_length sp al db tr hlen))

end Record

/-! ### Histories and the nodes below a node -/

theorem upTo_eq_of_none_between (h : History V) {a b : Time} (hab : a ≤ b)
    (hn : ∀ e ∈ h, ¬(a < e.time ∧ e.time ≤ b)) : h.upTo a = h.upTo b := by
  unfold History.upTo
  apply List.filter_congr
  intro e he
  have := hn e he
  by_cases h1 : e.time ≤ a
  · have : e.time ≤ b := Nat.le_trans h1 hab
    simp [h1, this]
  · have : ¬ e.time ≤ b := fun h2 => this ⟨Nat.lt_of_not_le h1, h2⟩
    simp [h1, this]

/-- Lemma M' (the access path back in time): if a node z below x at t has an
entry at a time c ≤ t, then at some time τ from c to t a node below x at τ has
an entry at τ: x is on the access path of the change of T(τ) (if x is
reachable then). By induction on the path: where a node of the path has an
entry after the time found below it, that entry is the change. -/
theorem reachFrom_entry_back (sp : Spec V T) (P : Struct V) (t : Time) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → P.get? x = some n →
      ∀ z ∈ reachFrom sp P t x n, ∀ nz, P.get? z = some nz → ∀ e ∈ nz.hist, e.time ≤ t →
        ∃ τ, e.time ≤ τ ∧ τ ≤ t ∧ ∃ z' ∈ reachFrom sp P τ x n, ∃ nz', P.get? z' = some nz' ∧
          ∃ e' ∈ nz'.hist, e'.time = τ := by
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hx z hz nz hnz e he het
    have hz' := hz
    rw [reachFrom_eq] at hz'
    simp only [List.mem_cons, List.mem_flatMap] at hz'
    rcases hz' with rfl | ⟨y, hy, hzy⟩
    · rw [hx, Option.some.injEq] at hnz
      subst hnz
      exact ⟨e.time, Nat.le_refl _, het, z, self_mem_reachFrom sp P _ z n, n, hx, e, he, rfl⟩
    · split at hzy
      · rename_i m hm
        split at hzy
        · rename_i hlt
          obtain ⟨τ', h1, h2, z', hz', nz', hnz', e', he', het'⟩ :=
            ih y m (by omega) hm z hzy nz hnz e he het
          by_cases hex : ∃ e'' ∈ n.hist, τ' < e''.time ∧ e''.time ≤ t
          · obtain ⟨e'', he'', h3, h4⟩ := hex
            exact ⟨e''.time, by omega, h4, x, self_mem_reachFrom sp P _ x n, n, hx, e'', he'', rfl⟩
          · have hup : n.hist.upTo τ' = n.hist.upTo t :=
              upTo_eq_of_none_between n.hist h2 (fun e0 he0 h0 => hex ⟨e0, he0, h0⟩)
            have hy' : y ∈ sp.live (n.hist.upTo τ') := by rw [hup]; exact hy
            exact ⟨τ', h1, h2, z', reachFrom_child_sub sp hy' hm hlt z' hz', nz', hnz', e', he', het'⟩
        · simp at hzy
      · simp at hzy

/-! ### Runs: the nodes and entries of earlier states -/

section RunFacts

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- An entry at a time up to τ of a node in a later state is an entry of that
node after T(τ). -/
theorem st_entry_back (hok : RunOK sp al ts) (hst : AlgOK sp al) {τ : Nat} :
    ∀ d, τ + d ≤ ts.length → ∀ z n, (st sp al ts (τ + d)).P.get? z = some n →
      ∀ e ∈ n.hist, e.time ≤ τ → ∃ n0, (st sp al ts τ).P.get? z = some n0 ∧ e ∈ n0.hist := by
  intro d
  induction d with
  | zero => intro _ z n hn e he _; exact ⟨n, hn, he⟩
  | succ d ih =>
    intro hd z n hn e he het
    rw [show τ + (d + 1) = (τ + d) + 1 by omega, st_P_succ sp al ts hok hst (by omega), get?_apply] at hn
    cases h0 : (st sp al ts (τ + d)).P.get? z with
    | some n1 =>
      rw [h0] at hn
      simp only [Option.some_or, Option.map_some, Option.some.injEq] at hn
      subst hn
      rcases List.mem_append.mp he with h | h
      · exact ih (by omega) z n1 h0 e h het
      · have := (mem_addsFor.mp h).1; omega
    | none =>
      rw [h0] at hn
      simp only [Option.none_or] at hn
      cases h1 : newNodeOf (sp.exec ts[τ + d] (τ + d + 1)
          (view sp (st sp al ts (τ + d)).P (τ + d))) z with
      | none => rw [h1] at hn; cases hn
      | some m =>
        rw [h1] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        rw [newNodeOf_hist h1, List.nil_append] at he
        have := (mem_addsFor.mp he).1; omega

/-- An entry at time j + 1 of a node after T(j + 1) is one that T(j + 1)'s
change adds: the node is changed by it. -/
theorem st_entry_changed (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat} (hj : j < ts.length)
    {z : NodeId} {n : Node V} (hn : (st sp al ts (j + 1)).P.get? z = some n) {e : Entry V}
    (he : e ∈ n.hist) (het : e.time = j + 1) :
    changed (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j)) z = true := by
  have hinv := inv_st sp al ts hok hst j (by omega)
  rw [st_P_succ sp al ts hok hst hj, get?_apply] at hn
  have hadd : e ∈ addsFor (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j)) (j + 1) z := by
    cases h0 : (st sp al ts j).P.get? z with
    | some n1 =>
      rw [h0] at hn
      simp only [Option.some_or, Option.map_some, Option.some.injEq] at hn
      subst hn
      rcases List.mem_append.mp he with h | h
      · have := hinv.times z n1 h0 e h; omega
      · exact h
    | none =>
      rw [h0] at hn
      simp only [Option.none_or] at hn
      cases h1 : newNodeOf (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j)) z with
      | none => rw [h1] at hn; cases hn
      | some m =>
        rw [h1] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        rw [newNodeOf_hist h1, List.nil_append] at he
        exact he
  have hm := (mem_addsFor.mp hadd).2
  unfold changed
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
  exact Or.inr ⟨(z, e.val), hm, rfl⟩

/-- A node below x at t, x reachable at t, with an entry at a time c from 1 to
t: x is on the access path of the change of a transaction T(τ), c ≤ τ ≤ t. -/
theorem onAccessPath_of_below (hok : RunOK sp al ts) (hst : AlgOK sp al) {K : Nat}
    (hK : K ≤ ts.length) {x : NodeId} {nx : Node V} {t : Nat} (htK : t ≤ K)
    (hxr : reachable sp (st sp al ts K).P t x = true) (hnx : (st sp al ts K).P.get? x = some nx)
    {z : NodeId} (hz : z ∈ reachFrom sp (st sp al ts K).P t x nx) {nz : Node V}
    (hnz : (st sp al ts K).P.get? z = some nz) {e : Entry V} (he : e ∈ nz.hist)
    (h0 : 0 < e.time) (het : e.time ≤ t) :
    ∃ τ, e.time ≤ τ ∧ τ ≤ t ∧ onAccessPath sp al ts τ x := by
  have hls : LiveSub sp := hok.1.liveSub
  obtain ⟨τ, h1, h2, z', hz', nz', hnz', e', he', het'⟩ :=
    reachFrom_entry_back sp (st sp al ts K).P t (nx.level + 1) x nx (by omega) hnx z hz nz hnz e he het
  obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
  have hj : j < ts.length := by omega
  have hKd : j + 1 + (K - (j + 1)) = K := by omega
  -- x has an entry at a time up to τ, so it exists after T(τ).
  have hxe : ∃ e0 ∈ nx.hist, e0.time ≤ j + 1 := by
    have hz'' := hz'
    rw [reachFrom_eq] at hz''
    simp only [List.mem_cons, List.mem_flatMap] at hz''
    rcases hz'' with rfl | ⟨y, hy, -⟩
    · rw [hnx, Option.some.injEq] at hnz'
      subst hnz'
      exact ⟨e', he', by omega⟩
    · obtain ⟨e0, he0, -⟩ := hls _ _ hy
      exact ⟨e0, (mem_upTo.mp he0).1, (mem_upTo.mp he0).2⟩
  obtain ⟨e0, he0, he0t⟩ := hxe
  obtain ⟨n0, hn0, -⟩ := st_entry_back hok hst (τ := j + 1) (K - (j + 1)) (by omega) x nx
    (by rw [hKd]; exact hnx) e0 he0 he0t
  have hinvτ := inv_st sp al ts hok hst (j + 1) (by omega)
  have hg := st_grow sp al ts hok hst (j := j + 1) (j' := K) (by omega) hK
  have hrx : reachable sp (st sp al ts (j + 1)).P (j + 1) x = true :=
    reach_back_st hok hst (j1 := j + 1) (j := K) hK (t - (j + 1)) t (by omega) htK x hxr
      (by rw [hn0]; rfl)
  have hRF : reachFrom sp (st sp al ts K).P (j + 1) x nx = reachFrom sp (st sp al ts (j + 1)).P (j + 1) x n0 :=
    reachFrom_grow hls hinvτ.ptrs hg (Nat.le_refl _) (n0.level + 1) x n0 nx (by omega) hn0 hnx
  rw [hRF] at hz'
  obtain ⟨nz0, hnz0, he'0⟩ := st_entry_back hok hst (τ := j + 1) (K - (j + 1)) (by omega) z' nz'
    (by rw [hKd]; exact hnz') e' he' (by omega)
  have hch := st_entry_changed hok hst hj hnz0 he'0 het'
  refine ⟨j + 1, h1, h2, by omega, ts[j], ?_, ?_⟩
  · simp [List.getElem?_eq_getElem hj]
  · left
    show marked sp ((run sp al (ts.take j)).P.apply (j + 1)
      (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j))) _ (j + 1) x = true
    have hP : (run sp al (ts.take j)).P.apply (j + 1)
        (sp.exec ts[j] (j + 1) (view sp (run sp al (ts.take j)).P j)) = (st sp al ts (j + 1)).P :=
      (st_P_succ sp al ts hok hst hj).symm
    rw [hP]
    unfold marked
    rw [hrx, hn0]
    simp only [Bool.true_and, List.any_eq_true]
    exact ⟨z', hz', hch⟩

end RunFacts

/-! ### The startup positions of a run -/

section Sp

theorem lastSp_eq_spAt {S S' : Stream V T} (h : S' <+: S) {j : Nat} (hl : S'.length = j + 1) :
    lastSp S' = spAt S j := by
  obtain ⟨L, rfl⟩ := h
  unfold lastSp spAt
  rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel, List.getElem?_append_left (by omega)]

theorem spAt_prefix {S S' : Stream V T} (h : S' <+: S) {j : Nat} (hj : j < S'.length) :
    spAt S' j = spAt S j := by
  obtain ⟨L, rfl⟩ := h
  unfold spAt
  rw [List.getElem?_append_left hj]

variable (S : Stream V T) (K : Nat) (hle : ∀ j ≤ K, spAt S j ≤ j)
  (hmono : ∀ j j', j ≤ j' → j' ≤ K → spAt S j ≤ spAt S j')
include hle

theorem spIter_le : ∀ n j, j ≤ K → spIter S n j ≤ j
  | 0, _, _ => Nat.le_refl _
  | n + 1, j, hj => by
    show spIter S n (spAt S j) ≤ j
    have h1 := hle j hj
    exact Nat.le_trans (spIter_le n (spAt S j) (by omega)) h1

include hmono

theorem spIter_mono : ∀ n j j', j ≤ j' → j' ≤ K → spIter S n j ≤ spIter S n j'
  | 0, _, _, h, _ => h
  | n + 1, j, j', h, hj' => by
    show spIter S n (spAt S j) ≤ spIter S n (spAt S j')
    have h1 := hmono j j' h hj'
    have h2 := hle j' hj'
    exact spIter_mono n _ _ h1 (by omega)

theorem spIter_succ_le (n j : Nat) (hj : j ≤ K) : spIter S (n + 1) j ≤ spIter S n j := by
  show spIter S n (spAt S j) ≤ spIter S n j
  exact spIter_mono S K hle hmono n _ _ (hle j hj) hj

theorem spIter_anti (j : Nat) (hj : j ≤ K) : ∀ d n, spIter S (n + d) j ≤ spIter S n j
  | 0, _ => Nat.le_refl _
  | d + 1, n => Nat.le_trans (spIter_succ_le S K hle hmono (n + d) j hj) (spIter_anti j hj d n)

end Sp

theorem spIter_prefix {S S' : Stream V T} (h : S' <+: S) (K : Nat) (hK : K < S'.length)
    (hle : ∀ j ≤ K, spAt S' j ≤ j) : ∀ n j, j ≤ K → spIter S' n j = spIter S n j
  | 0, _, _ => rfl
  | n + 1, j, hj => by
    show spIter S' n (spAt S' j) = spIter S n (spAt S j)
    rw [← spAt_prefix h (by omega : j < S'.length)]
    exact spIter_prefix h K hK hle n _ (by have := hle j hj; omega)

section RunSp

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem spAt_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {K j : Nat} (hK : K ≤ ts.length)
    (hj : j ≤ K) : spAt (st sp al ts K).S j = lastSp (st sp al ts j).S :=
  (lastSp_eq_spAt (st_S_prefix sp al ts hj hK) (st_len sp al ts hok hst (by omega))).symm

theorem spAt_st_le (hok : RunOK sp al ts) (hst : AlgOK sp al) {K : Nat} (hK : K ≤ ts.length) :
    ∀ j ≤ K, spAt (st sp al ts K).S j ≤ j := by
  intro j hj
  rw [spAt_st hok hst hK hj]
  rcases (inv_st sp al ts hok hst j (by omega)).spLt with h | ⟨h1, h2⟩ <;> omega

theorem lastSp_st_succ (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat} (hj : j < ts.length) :
    lastSp (st sp al ts j).S ≤ lastSp (st sp al ts (j + 1)).S := by
  have hinv := inv_st sp al ts hok hst j (by omega)
  rw [st_succ sp al ts hj, step_S, step_lastSp]
  exact step_s_ge sp al _ _ hinv.len hinv.spLt

theorem spAt_st_mono (hok : RunOK sp al ts) (hst : AlgOK sp al) {K : Nat} (hK : K ≤ ts.length) :
    ∀ j j', j ≤ j' → j' ≤ K → spAt (st sp al ts K).S j ≤ spAt (st sp al ts K).S j' := by
  intro j j' h hj'
  rw [spAt_st hok hst hK (by omega), spAt_st hok hst hK hj']
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + d := ⟨j' - j, by omega⟩
  clear h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega)) (lastSp_st_succ hok hst (j := j + d) (by omega))

end RunSp

/-! ### A stale version and a change below its node (lemma G) -/

/-- A version good for r' but not for a later t: a node below its node at t
has an entry after r', at t or before. -/
theorem Inv.stale_entry {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) :
    ∀ (b : Nat) (ρ : Nat) (y : NodeId) (v : Version V) (n : Node V), n.level < b →
      db.S.versionAt ρ y = some v → db.P.get? y = some n → ∀ r' t, ρ ≤ r' → r' < t →
      good sp db.S db.P r' v = true → good sp db.S db.P t v = false →
      ∃ z ∈ reachFrom sp db.P t y n, ∃ nz, db.P.get? z = some nz ∧
        ∃ e ∈ nz.hist, r' < e.time ∧ e.time ≤ t := by
  intro b
  induction b with
  | zero => intro ρ y v n h; omega
  | succ b ih =>
    intro ρ y v n hb hv hn r' t hρ hrt hg hng
    obtain ⟨hvy, hvr, n', hn', hvh, hvl, -⟩ := hinv.version_node hv
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    by_cases hex : ∃ e ∈ n.hist, r' < e.time ∧ e.time ≤ t
    · obtain ⟨e, he, h1, h2⟩ := hex
      exact ⟨y, self_mem_reachFrom sp db.P t y n, n, hn, e, he, h1, h2⟩
    · have hup : n.hist.upTo r' = n.hist.upTo t :=
        upTo_eq_of_none_between n.hist (Nat.le_of_lt hrt) (fun e he h => hex ⟨e, he, h⟩)
      have hvt : v.hist.upTo t = v.hist.upTo r' := by
        rw [hvh, upTo_upTo' _ (by omega : ρ ≤ t), upTo_upTo' _ hρ]
      rw [good_iff] at hg
      obtain ⟨⟨n1, hn1, hh1⟩, hc⟩ := hg
      rw [hvy, hn, Option.some.injEq] at hn1
      subst hn1
      have hvn : v.hist.upTo t = n.hist.upTo t := by rw [hvt, hh1, hup]
      have hng' : ¬ (good sp db.S db.P t v = true) := by rw [hng]; simp
      rw [good_iff] at hng'
      obtain ⟨w, hw, hwf⟩ : ∃ w ∈ sp.live (v.hist.upTo t), ¬ ∃ r u, v.ref? w = some r ∧
          db.S.versionAt r w = some u ∧ u.level < v.level ∧ good sp db.S db.P t u = true := by
        apply Classical.byContradiction
        intro hcon
        apply hng'
        refine ⟨⟨n, by rw [hvy]; exact hn, hvn⟩, fun w hw => ?_⟩
        apply Classical.byContradiction
        intro h
        exact hcon ⟨w, hw, h⟩
      have hw' : w ∈ sp.live (v.hist.upTo r') := by rw [← hvt]; exact hw
      obtain ⟨r, u, h1, h2, h3, h4⟩ := hc w hw'
      have hgu : good sp db.S db.P t u = false := by
        cases hgt : good sp db.S db.P t u with
        | false => rfl
        | true => exact absurd ⟨r, u, h1, h2, h3, hgt⟩ hwf
      obtain ⟨-, -, m, hm, -, hul, -⟩ := hinv.version_node h2
      have hrρ : r ≤ ρ := hvr ▸ hinv.ref_le_recNo hv h1
      have hlt : m.level < n.level := by rw [← hul, ← hvl]; exact h3
      obtain ⟨z, hz, nz, hnz, e, he, h5, h6⟩ :=
        ih r w u m (by omega) h2 hm r' t (by omega) hrt h4 hgu
      have hwn : w ∈ sp.live (n.hist.upTo t) := by rw [← hvn]; exact hw
      exact ⟨z, reachFrom_child_sub sp hwn hm hlt z hz, nz, hnz, e, he, h5, h6⟩

/-! ### The records of a run -/

/-- Every record R(i + 1) of a run is bounded by the debt before T(i + 1). -/
theorem recordBound_run (sp : Spec V T) (al : Algo V T) (ts : List T) (i : Nat)
    (hi : i < ts.length) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R := by
  have hlen : (st sp al ts i).S.length = i + 1 := by
    rw [st, run_length, List.length_take]; omega
  obtain ⟨R, hR, hb⟩ := recordByDebt_step sp al (st sp al ts i) ts[i] hlen
  refine ⟨R, ?_, hb⟩
  have hpre := st_S_prefix sp al ts (j := i + 1) (j' := ts.length) (by omega) (Nat.le_refl _)
  rw [st_length, st_succ sp al ts hi, hR] at hpre
  obtain ⟨L, hL⟩ := hpre
  rw [← hL, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hlen]
  simp

end SIS
