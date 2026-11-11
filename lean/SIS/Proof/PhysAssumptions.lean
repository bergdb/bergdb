/-
Proofs: the assumptions of the physical layer (`PhysStep`, `PhysRunOK`;
SIS/Phys.lean) follow from the other assumptions (bergdb 024-09, step A2).

Until bergdb 024-09 `PhysRunOK` was an assumption of its own of the theorems of
lazy reading and of the theorems with handles, argued for BergDB in a text
(bergdb 011-11, section 13.3) and checked on no trace. This file proves it, for
any `Spec`, from what the model assumes besides it:

* `adopt` (`physStep_adopt`): from TREE after the transaction (`treeAt`), A5
  (`StepOK.noRes`), A4 after the transaction (`PtrsOK`) and the times of the
  entries before it. In plain words: a new live child y at i of a node x
  reachable at i is reachable at i; the change does not create it, so it was
  reachable at i - 1 (A5), and so it had a parent z reachable then, as every
  reachable node but the root has. If the change left z alone and z were still
  reachable at i, y would be a live child at i of both x and z, against TREE.
  TREE before the transaction is not needed.
* `liveNew` (`physStep_liveNew`): from one property of the Spec's `live`,
  `LiveAppend`: entries added at the end of a history give no live child but
  their own pointees. It is a property of the function `live` alone, not of a
  run; Check/Live.lean proves it for the trace checker's `blive`.

So `PhysRunOK` holds in every run that meets `RunOK`, with TREE after every
transaction and `LiveAppend` (`physRunOK_of_tree`), and in every run that meets
`RunOK` and `EvictRunOK`, with `LiveAppend` (`physRunOK_of_evict`); and a
theorem that assumes the three holds without `PhysRunOK` (`without_physRunOK`).
The trusted statements are unchanged: they still name `PhysRunOK`.
-/
import SIS.Proof.LogicFacts
import SIS.Proof.PhysFrozen

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Live children come from entries: a live child of a history h followed by
the entries h' is a live child of h, or a pointee of an entry of h'. So entries
added to a node make none of its other pointees live again. With `LiveSub` this
is what `PhysStep.liveNew` needs of the function `live`. -/
def LiveAppend (sp : Spec V T) : Prop :=
  ∀ (h h' : History V) (y : NodeId), y ∈ sp.live (h ++ h') →
    y ∈ sp.live h ∨ ∃ e ∈ h', y ∈ sp.ptrs e.val

/-- A node that the change neither creates nor gives entries gets no entries. -/
theorem addsFor_of_not_changed {c : Changes V} {z : NodeId} (h : changed c z = false) (i : Time) :
    addsFor c i z = [] := by
  simp only [changed, Bool.or_eq_false_iff, List.any_eq_false] at h
  simp only [addsFor, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  exact h.2

/-- A node reachable at t, the root aside, is a live child at t of a node
reachable at t. -/
theorem reachable_parent {sp : Spec V T} {P : Struct V} {t : Time} {y : NodeId}
    (hr : reachable sp P t y = true) (hy : y ≠ root) :
    ∃ z nz, P.get? z = some nz ∧ reachable sp P t z = true ∧ y ∈ sp.live (nz.hist.upTo t) := by
  rw [reachable_iff] at hr
  cases hr with
  | root n hn => exact absurd rfl hy
  | child hp hn hyl hm hlt => exact ⟨_, _, hn, (reachable_iff _ _ _ _).mpr hp, hyl⟩

section Step

variable {sp : Spec V T} {P : Struct V} {k : Nat} {c : Changes V}

/-- `PhysStep.liveNew` for the change c at time k + 1 to a structure with no
entry after k: a node's live children at k + 1 are its live children at k or
pointees of its new entries. -/
theorem physStep_liveNew (hls : LiveSub sp) (hla : LiveAppend sp)
    (htimes : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ k) :
    ∀ x n, (P.apply (k + 1) c).get? x = some n → ∀ y ∈ sp.live (n.hist.upTo (k + 1)),
      (∃ n0, P.get? x = some n0 ∧ y ∈ sp.live (n0.hist.upTo (k + 1 - 1))) ∨
        ∃ a ∈ c.adds, a.1 = x ∧ y ∈ sp.ptrs a.2 := by
  intro x n hn y hy
  cases hx : P.get? x with
  | some n0 =>
    rw [get?_apply_of_get? hx] at hn
    cases hn
    simp only at hy
    have h0 : n0.hist.upTo (k + 1) = n0.hist :=
      upTo_of_forall _ _ (fun e he => by have := htimes x n0 hx e he; omega)
    have h1 : (addsFor c (k + 1) x).upTo (k + 1) = addsFor c (k + 1) x :=
      upTo_of_forall _ _ (fun e he => by rw [mem_addsFor] at he; omega)
    rw [upTo_append, h0, h1] at hy
    rcases hla _ _ _ hy with h | ⟨e, he, hye⟩
    · left
      refine ⟨n0, rfl, ?_⟩
      rw [Nat.add_sub_cancel, upTo_of_forall _ _ (htimes x n0 hx)]
      exact h
    · right
      rw [mem_addsFor] at he
      exact ⟨(x, e.val), he.2, rfl, hye⟩
  | none =>
    right
    rw [get?_apply, hx] at hn
    cases hm : newNodeOf c x with
    | none => rw [hm] at hn; simp at hn
    | some m =>
      rw [hm] at hn
      obtain ⟨nn, -, -, rfl⟩ := newNodeOf_some hm
      simp only [Option.none_or, Option.map_some, Option.some.injEq] at hn
      subst hn
      obtain ⟨e, he, hye⟩ := hls _ _ hy
      have he' := (mem_upTo.mp he).1
      simp only [List.nil_append] at he'
      rw [mem_addsFor] at he'
      exact ⟨(x, e.val), he'.2, rfl, hye⟩

/-- `PhysStep.adopt` for the change c at time k + 1 to a structure with no
entry after k, from A4 and TREE after the change and A5: a new live child of a
node reachable after the change, that the change does not create, was a live
child of a node reachable before it that the change changes or that is not
reachable after it. -/
theorem physStep_adopt (hls : LiveSub sp)
    (htimes : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ k)
    (hptrs : PtrsOK sp (P.apply (k + 1) c))
    (hnoRes : ∀ y, reachable sp (P.apply (k + 1) c) (k + 1) y = true →
      reachable sp P (k + 1 - 1) y = true ∨ y ∈ c.new.map (·.id))
    (htree : treeAt sp (P.apply (k + 1) c) (k + 1)) :
    ∀ x n, reachable sp (P.apply (k + 1) c) (k + 1) x = true → (P.apply (k + 1) c).get? x = some n →
      ∀ y ∈ sp.live (n.hist.upTo (k + 1)),
        (∀ n0, P.get? x = some n0 → y ∉ sp.live (n0.hist.upTo (k + 1 - 1))) →
        y ∉ c.new.map (·.id) →
        ∃ z nz, P.get? z = some nz ∧ reachable sp P (k + 1 - 1) z = true ∧
          (changed c z = true ∨ reachable sp (P.apply (k + 1) c) (k + 1) z = false) ∧
          y ∈ sp.live (nz.hist.upTo (k + 1 - 1)) := by
  intro x n hrx hn y hy hnot hynew
  simp only [Nat.add_sub_cancel] at hnot hnoRes ⊢
  -- y is a node on a lower level than x (A4), so it is reachable after the change, and not the root.
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  obtain ⟨m, hm, hlt⟩ := hptrs x n hn e (mem_upTo.mp he).1 y hye
  have hRx := (reachable_iff sp _ _ x).mp hrx
  have hry : reachable sp (P.apply (k + 1) c) (k + 1) y = true :=
    (reachable_iff sp _ _ y).mpr (Reach.child hRx hn hy hm hlt)
  have hyroot : y ≠ root := by
    intro hyr
    rw [hyr] at hm
    rcases reach_level_root hRx hm n hn with h | h
    · rw [h, hm] at hn
      cases hn
      omega
    · omega
  -- A5: y was reachable before the change, so it had a parent z reachable then.
  rcases hnoRes y hry with hry0 | h
  · obtain ⟨z, nz, hnz, hrz, hyz⟩ := reachable_parent hry0 hyroot
    refine ⟨z, nz, hnz, hrz, ?_, hyz⟩
    cases hch : changed c z with
    | true => exact Or.inl rfl
    | false =>
      right
      cases hrz' : reachable sp (P.apply (k + 1) c) (k + 1) z with
      | false => rfl
      | true =>
        -- z is unchanged and still reachable: y has two parents after the change, against TREE.
        exfalso
        have hnz' := get?_apply_of_get? (i := k + 1) (c := c) hnz
        have hyz' : y ∈ sp.live
            (({ nz with hist := nz.hist ++ addsFor c (k + 1) z } : Node V).hist.upTo (k + 1)) := by
          simp only
          rw [addsFor_of_not_changed hch, List.append_nil,
            upTo_of_forall _ _ (fun e he => by have := htimes z nz hnz e he; omega)]
          rw [upTo_of_forall _ _ (htimes z nz hnz)] at hyz
          exact hyz
        have hxz : x = z := treeAt_unique htree hry hyroot hrx hrz' hn hnz' hy hyz'
        subst hxz
        exact hnot nz hnz hyz
  · exact absurd h hynew

/-- `PhysStep` for the change c at time k + 1 to a structure with no entry
after k: from `LiveSub` and `LiveAppend` of the function `live`, A4 and TREE
after the change, and A5. -/
theorem physStep_of_tree (hls : LiveSub sp) (hla : LiveAppend sp)
    (htimes : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ k)
    (hptrs : PtrsOK sp (P.apply (k + 1) c))
    (hnoRes : ∀ y, reachable sp (P.apply (k + 1) c) (k + 1) y = true →
      reachable sp P (k + 1 - 1) y = true ∨ y ∈ c.new.map (·.id))
    (htree : treeAt sp (P.apply (k + 1) c) (k + 1)) : PhysStep sp P (k + 1) c :=
  ⟨physStep_liveNew hls hla htimes, physStep_adopt hls htimes hptrs hnoRes htree⟩

end Step

section Run

variable {sp : Spec V T} {ts : List T}

/-- The structures of a run do not depend on the algorithm's choices (the
startup pos, the still-dirty test, marking): two algorithms give the same P
after every transaction. -/
theorem st_P_algo (al al' : Algo V T) : ∀ j, j ≤ ts.length →
    (st sp al ts j).P = (st sp al' ts j).P ∧
      (st sp al ts j).S.length = (st sp al' ts j).S.length := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero, st_zero]; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hjt
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [st_succ sp _ ts (by omega), st_succ sp _ ts (by omega), step_P_eq, step_P_eq,
      step_S_length, step_S_length, h1, h2]
    exact ⟨rfl, rfl⟩

variable {al : Algo V T}

/-- `PhysRunOK` is no assumption of its own: it holds in every run that meets
`RunOK`, with TREE after every transaction (TREE for R(0) is not needed) and
`LiveAppend`. -/
theorem physRunOK_of_tree (hok : RunOK sp al ts) (hla : LiveAppend sp)
    (htree : ∀ j < ts.length, treeAt sp (run sp al (ts.take (j + 1))).P (j + 1)) :
    PhysRunOK sp al ts := by
  -- The invariant of a run is proved for BergDB's still-dirty test; P is the same with it.
  let al' : Algo V T := { al with stillDirty := javaTest sp }
  have hst : AlgOK sp al' := algOK_of sp al' (Or.inl rfl)
  have hP : ∀ j ≤ ts.length, (st sp al ts j).P = (st sp al' ts j).P :=
    fun j hj => (st_P_algo al al' j hj).1
  have hok' : RunOK sp al' ts := by
    refine ⟨hok.1, fun j hj => ?_⟩
    have h := hok.2 j hj
    have hPj := hP j (by omega)
    simp only [st] at hPj
    simp only
    rw [← hPj]
    exact h
  intro j hj
  have hinv := inv_st sp al' ts hok' hst j (by omega)
  have hinv' := inv_st sp al' ts hok' hst (j + 1) (by omega)
  have hPs := st_P_succ sp al' ts hok' hst hj
  have hstep : StepOK sp (st sp al' ts j).P (j + 1)
      (sp.exec ts[j] (j + 1) (view sp (st sp al' ts j).P j)) := hok'.2 j hj
  show PhysStep sp (st sp al ts j).P (j + 1) (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j))
  rw [hP j (by omega)]
  refine physStep_of_tree hok.1.liveSub hla hinv.times ?_ hstep.noRes ?_
  · rw [← hPs]
    exact hinv'.ptrs
  · rw [← hPs, ← hP (j + 1) hj]
    exact htree j hj

/-- `PhysRunOK` from `RunOK`, `EvictRunOK` (its TREE) and `LiveAppend`: the
theorems with handles (SIS/HandleTheorems.lean, SIS/HandleReclaimTheorems.lean)
assume the first two besides `PhysRunOK`. -/
theorem physRunOK_of_evict (hok : RunOK sp al ts) (hla : LiveAppend sp)
    (hev : EvictRunOK sp al ts) : PhysRunOK sp al ts :=
  physRunOK_of_tree hok hla (fun j hj => (hev.1 (j + 1) hj).tree)

/-- A statement that assumes `RunOK`, `PhysRunOK` and `EvictRunOK` of a run,
as the theorems with handles do, holds without `PhysRunOK` for a Spec with
`LiveAppend`. For example `without_physRunOK hla (tr_handles sp al)` is T-READ
with handles from `RunOK` and `EvictRunOK`. -/
theorem without_physRunOK {ι : Type} {f : ι → List T} {Q : ι → Prop} (hla : LiveAppend sp)
    (h : ∀ x, RunOK sp al (f x) → PhysRunOK sp al (f x) → EvictRunOK sp al (f x) → Q x) :
    ∀ x, RunOK sp al (f x) → EvictRunOK sp al (f x) → Q x :=
  fun x hok hev => h x hok (physRunOK_of_evict hok hla hev) hev

end Run

end SIS
