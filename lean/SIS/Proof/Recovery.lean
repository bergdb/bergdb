/-
Proofs, part 16: T1, recovery, in the strong form: startup gives back every node.
-/
import SIS.Proof.Base

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

theorem node_cut_eq {n n0 : Node V} {s : Nat} (h1 : n.level = n0.level) (h2 : n.isData = n0.isData)
    (h3 : n.hist.upTo s = n0.hist.upTo s) (h4 : n0.hist.upTo s = n0.hist) :
    ({ n with hist := n.hist.upTo s } : Node V) = n0 := by
  cases n; cases n0
  simp only at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]

/-- P up to s, as startup reads it, is the run's P after T(s). -/
theorem base_sameNodes (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) {k : Nat}
    (hk : k ≤ ts.length) :
    SameNodes (baseStruct sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)
      (st sp al ts (lastSp (st sp al ts k).S)).P := by
  have hinv := inv_st sp al ts hok hex k hk
  have hls : LiveSub sp := hok.1.liveSub
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hinvs := inv_st sp al ts hok hex _ (Nat.le_trans hsk hk)
  have hgrow := st_grow sp al ts hok hex hsk hk
  intro x
  rw [hinv.base_get? hls]
  have hreach : ∀ t ≤ lastSp (st sp al ts k).S, ∀ y,
      reachable sp (st sp al ts k).P t y = reachable sp (st sp al ts (lastSp (st sp al ts k).S)).P t y :=
    fun t ht y => reachable_grow hls hinvs.ptrs hinvs.rootIn hgrow ht y
  by_cases hex' : ∃ t ≤ lastSp (st sp al ts k).S, reachable sp (st sp al ts k).P t x = true
  · rw [ite_eq_left_iff.mpr (fun h => absurd hex' h)]
    obtain ⟨t, ht, hr⟩ := hex'
    rw [hreach t ht x, reachable_iff] at hr
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hr.isSome
    obtain ⟨n, hn, h1, h2, h3⟩ := hgrow x n0 hn0
    rw [hn, hn0]
    simp only [Option.map_some, Option.some.injEq]
    exact node_cut_eq h1 h2 h3 (upTo_of_forall _ _ (hinvs.times x n0 hn0))
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hex')]
    cases hn0 : (st sp al ts (lastSp (st sp al ts k).S)).P.get? x with
    | none => rfl
    | some n0 =>
      exfalso
      obtain ⟨t, ht, hr⟩ := hinvs.born x (by simp [hn0])
      exact hex' ⟨t, ht, by rw [hreach t ht x]; exact hr⟩

/-- The rerun of the section gives back the run's P. -/
theorem rerun_sameNodes (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) {k : Nat}
    (hk : k ≤ ts.length) {P0 : Struct V}
    (h0 : SameNodes P0 (st sp al ts (lastSp (st sp al ts k).S)).P) :
    SameNodes (rerun sp (st sp al ts k).S (lastSp (st sp al ts k).S) P0) (st sp al ts k).P := by
  have hinv := inv_st sp al ts hok hex k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  generalize hs : lastSp (st sp al ts k).S = s at h0 hsk
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  unfold rerun
  rw [hidx]
  have key : ∀ m, m ≤ k - s →
      SameNodes ((List.range' (s + 1) m).foldl (fun P j =>
        match (st sp al ts k).S[j]?.bind (·.trans) with
        | some tr => P.apply j (sp.exec tr j (view sp P (j - 1)))
        | none => P) P0) (st sp al ts (s + m)).P := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
      intro hm
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      have hj : s + 1 + m = (s + m) + 1 := by omega
      rw [hj, st_trans sp al ts hok hex (by omega) (by omega) hk]
      simp only [Nat.add_sub_cancel]
      have ih' := ih (by omega)
      rw [show s + (m + 1) = (s + m) + 1 by omega, st_P_succ sp al ts hok hex (by omega),
        ih'.view (s + m)]
      exact ih'.apply _ _
  have := key (k - s) (Nat.le_refl _)
  rwa [show s + (k - s) = k by omega] at this

/-- T1, strong form: startup from the stream of any prefix of a run gives
back every node of P, and D. -/
theorem T1_strong (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) {k : Nat}
    (hk : k ≤ ts.length) :
    SameNodes (startup sp (st sp al ts k).S).P (st sp al ts k).P ∧
      (startup sp (st sp al ts k).S).D = (st sp al ts k).D := by
  have hinv := inv_st sp al ts hok hex k hk
  refine ⟨?_, ?_⟩
  · show SameNodes (rerun sp (st sp al ts k).S (lastSp (st sp al ts k).S)
      (baseStruct sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)) (st sp al ts k).P
    exact rerun_sameNodes sp al ts hok hex hk (base_sameNodes sp al ts hok hex hk)
  · rw [startup, startup_D, hinv.inv1]

end Run

end SIS
