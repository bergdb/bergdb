/-
Proofs about reclaim, part 4 (bergdb item 001, WP R4): the rerun of the startup
section from a structure that agrees with the run's for lookups from f on.
-/
import SIS.Proof.CutAgree
import SIS.Proof.Recovery

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The root's node in a view holds entries of the root's node in P. -/
theorem view_root_hist {sp : Spec V T} {P : Struct V} {t : Time} {n : Node V}
    (h : view sp P t root = some n) : ∃ n0, P.get? root = some n0 ∧ ∀ e ∈ n.hist, e ∈ n0.hist := by
  simp only [view] at h
  split at h
  · obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨n0, hn0, fun e he => (mem_upTo.mp he).1⟩
  · simp at h

/-- The change of a transaction is the same on two structures that agree for
lookups at the time it reads, with a virtual root seen only through its live
children (`ExecRootOK`). -/
theorem exec_cutAgree {sp : Spec V T} (hex : ExecRootOK sp) {f j : Time} {P P' : Struct V}
    (h : CutAgree sp f j P P') (hfj : f ≤ j) (hls : LiveSub sp) (hp : PtrsOK sp P)
    (hroot : sp.virt = true → ∀ n, P.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z)
    (tr : T) (i : Time) :
    sp.exec tr i (view sp P' j) = sp.exec tr i (view sp P j) := by
  have hsf := h.sameFrom hls hp j hfj (Nat.le_refl _)
  by_cases hv : sp.virt = true
  · refine hex hv tr i _ _ ?_ ?_ (fun x hx => hsf.1 x (fun _ => hx)) (hsf.2 hv)
    · intro n hn e he
      obtain ⟨n0, hn0, hsub⟩ := view_root_hist hn
      exact h.rootVals' hv n0 hn0 e (hsub e he)
    · intro n hn e he
      obtain ⟨n0, hn0, hsub⟩ := view_root_hist hn
      exact hroot hv n0 hn0 e (hsub e he)
  · have : view sp P' j = view sp P j := by
      funext x; exact hsf.1 x (fun h' => absurd h' hv)
    rw [this]

/-- With a virtual root, the root's new entries are entries for root children (R2). -/
theorem VirtStep.root_adds {sp : Spec V T} {P : Struct V} {i : Time} {c : Changes V}
    (h : VirtStep sp P i c) : ∀ a ∈ c.adds, a.1 = root → ∃ z, a.2 = sp.rootVal z := by
  intro a ha har
  have hm : a ∈ c.adds.filter (fun a => a.1 == root) := List.mem_filter.mpr ⟨ha, by simp [har]⟩
  rw [h.rootAdds] at hm
  obtain ⟨nn, -, hnn⟩ := List.mem_map.mp hm
  exact ⟨nn.id, by rw [← hnn]⟩

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

/-- The rerun of the section from a structure that agrees with the run's at the
startup pos s for lookups from f to s agrees with the run's for lookups from f
to k, and has the run's node for each node for which the structure had the
run's at s (bergdb item 001, WP R5: the nodes of D for T12). The stream is cut
at or before s. -/
theorem rerun_cutAgree_nodes (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat}
    (hk : k ≤ ts.length) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) {c f : Nat}
    (hcs : c ≤ lastSp (st sp al ts k).S) (hfs : f ≤ lastSp (st sp al ts k).S) {P0 : Struct V}
    (h0 : CutAgree sp f (lastSp (st sp al ts k).S) (st sp al ts (lastSp (st sp al ts k).S)).P P0)
    (X : NodeId → Prop)
    (hX : ∀ x, X x → P0.get? x = (st sp al ts (lastSp (st sp al ts k).S)).P.get? x) :
    CutAgree sp f k (st sp al ts k).P
        (rerun sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) P0) ∧
      ∀ x, X x → (rerun sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) P0).get? x =
        (st sp al ts k).P.get? x := by
  have hinv := inv_st sp al ts hok hst k hk
  have hls : LiveSub sp := hok.1.liveSub
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  generalize hs : lastSp (st sp al ts k).S = s at h0 hX hsk hcs hfs
  have hidx : sectionIdx (cutStream c (st sp al ts k).S) s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, cutStream_length, hinv.len]
  unfold rerun
  rw [hidx]
  have key : ∀ m, m ≤ k - s →
      CutAgree sp f (s + m) (st sp al ts (s + m)).P ((List.range' (s + 1) m).foldl (fun P j =>
        match (cutStream c (st sp al ts k).S)[j]?.bind (·.trans) with
        | some tr => P.apply j (sp.exec tr j (view sp P (j - 1)))
        | none => P) P0) ∧
      ∀ x, X x → ((List.range' (s + 1) m).foldl (fun P j =>
        match (cutStream c (st sp al ts k).S)[j]?.bind (·.trans) with
        | some tr => P.apply j (sp.exec tr j (view sp P (j - 1)))
        | none => P) P0).get? x = (st sp al ts (s + m)).P.get? x := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simpa using h0, by simpa using hX⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih', ihX⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      have hj : s + 1 + m = (s + m) + 1 := by omega
      rw [hj, cutStream_getElem?_ge (by omega), st_trans sp al ts hok hst (by omega) (by omega) hk]
      simp only [Nat.add_sub_cancel]
      have hinvm := inv_st sp al ts hok hst (s + m) (by omega)
      rw [exec_cutAgree hex ih' (by omega) hls hinvm.ptrs (fun hv n hn e he => by
          obtain ⟨z, -, -, hval⟩ := (hinvm.vr hv).rootEntry n hn e he
          exact ⟨z, hval⟩), show s + (m + 1) = (s + m) + 1 by omega,
        st_P_succ sp al ts hok hst (by omega)]
      have hstep := hok.2 (s + m) (by omega)
      simp only at hstep
      have hstep' : StepOK sp (st sp al ts (s + m)).P (s + m + 1)
          (sp.exec ts[s + m] (s + m + 1) (view sp (st sp al ts (s + m)).P (s + m))) := hstep
      refine ⟨ih'.apply (by omega) hls hinvm.ptrs hinvm.times hstep' hvl ?_ ?_, ?_⟩
      · intro hv n hn e he
        obtain ⟨z, -, -, hval⟩ := (hinvm.vr hv).rootEntry n hn e he
        exact ⟨z, hval⟩
      · intro hv
        exact (hstep'.virt hv).root_adds
      · intro x hx
        rw [get?_apply, get?_apply, ihX x hx]
  have := key (k - s) (Nat.le_refl _)
  rwa [show s + (k - s) = k by omega] at this

/-- The rerun of the section from a structure that agrees with the run's at the
startup pos s for lookups from f to s agrees with the run's for lookups from f
to k. The stream is cut at or before s. -/
theorem rerun_cutAgree (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length)
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) {c f : Nat} (hcs : c ≤ lastSp (st sp al ts k).S)
    (hfs : f ≤ lastSp (st sp al ts k).S) {P0 : Struct V}
    (h0 : CutAgree sp f (lastSp (st sp al ts k).S) (st sp al ts (lastSp (st sp al ts k).S)).P P0) :
    CutAgree sp f k (st sp al ts k).P
      (rerun sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) P0) :=
  (rerun_cutAgree_nodes sp al ts hok hst hk hex hvl hcs hfs h0 (fun _ => False)
    (fun _ h => h.elim)).1

end Run

end SIS
