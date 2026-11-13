/-
Proofs for bounds, part 3 (bergdb item 007): the handles that the lazy startup
gives out (SIS/BoundCold.lean). Every step of the startup takes at most one new
handle per node it reads or creates.
-/
import SIS.BoundCold
import SIS.Handle
import SIS.Proof.PhysMem
import SIS.Proof.PhysPath
import SIS.Proof.Recovery
import SIS.Proof.BoundT4Tree

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Next

variable (sp : Spec V T) (S : Stream V T)

theorem Mem.register_next (m : Mem V) (h : Nat) : (m.register h).1.next = m.next := by
  unfold Mem.register
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rfl

theorem Mem.makeCanonical_next (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) :
    (m.makeCanonical hp y h).1.next = m.next := by
  unfold Mem.makeCanonical
  simp only
  split <;> split <;> simp

theorem Mem.follow_next (m : Mem V) (hp : Nat) (y : NodeId) (w : Bool) :
    (m.follow sp S hp y w).1.next ≤ m.next + 1 := by
  unfold Mem.follow
  split
  · simp
  · split
    · split
      · simp [Mem.makeCanonical_next]
      · simp
    · simp
  · rename_i r hr
    simp only
    split
    · simp
    · rename_i m1 h1 hl
      have hm1 : m1.next ≤ m.next + 1 := by
        split at hl
        · simp at hl; rw [← hl.1]; omega
        · split at hl
          · simp at hl
          · split at hl
            · simp at hl
            · simp only [Option.some.injEq] at hl
              have := congrArg (fun p => p.1.next) hl
              simp only [Mem.register_next, Mem.addObj_next] at this
              omega
      split
      · split
        · split <;> simp [Mem.makeCanonical_next] <;> omega
        · split <;> simp <;> omega
      · split <;> simp <;> omega

theorem Mem.reachOnPath_next (P : Struct V) (j : Time) (path : List NodeId) (m : Mem V)
    (x : NodeId) : (m.reachOnPath sp S P j path x).next ≤ m.next + 1 := by
  unfold Mem.reachOnPath
  split
  · omega
  · simp only
    split
    · split
      · exact Mem.follow_next sp S _ _ _ _
      · omega
    · omega

theorem foldl_next_le {α : Type} (f : Mem V → α → Mem V) (k : Nat)
    (hf : ∀ m a, (f m a).next ≤ m.next + k) :
    ∀ (l : List α) (m : Mem V), (l.foldl f m).next ≤ m.next + k * l.length := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (f m a)
    have h2 := hf m a
    rw [Nat.mul_succ]
    omega

theorem Mem.applyChange_next (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
    (m.applyChange sp P j c).next ≤ m.next + c.new.length := by
  unfold Mem.applyChange
  simp only
  refine Nat.le_trans (foldl_next_le _ 0 ?_ c.adds _) ?_
  · intro m a
    split
    · omega
    · split
      · omega
      · rw [Mem.setObj_next]; omega
  · rw [Nat.zero_mul, Nat.add_zero]
    refine Nat.le_trans (foldl_next_le _ 1 ?_ c.new m) (by simp)
    intro m nn
    simp

theorem Mem.canonicalNode_next (m : Mem V) (x : NodeId) :
    (m.canonicalNode sp S x).next ≤ m.next + 1 := by
  unfold Mem.canonicalNode
  split
  · omega
  · split
    · simp
    · omega

@[simp] theorem Mem.linkCanonical_next (m : Mem V) : m.linkCanonical.next = m.next := rfl

end Next

/-- Two folds side by side: the startup's rerun, on the memory and P, and the
count of what it reaches, on a number and P. -/
theorem fold_rel {f : Mem V × Struct V → Nat → Mem V × Struct V}
    {g : Nat × Struct V → Nat → Nat × Struct V}
    (hfg : ∀ acc n j, (f acc j).2 = (g (n, acc.2) j).2 ∧
      (f acc j).1.next + n ≤ acc.1.next + (g (n, acc.2) j).1) :
    ∀ (l : List Nat) (acc : Mem V × Struct V) (n : Nat),
      (l.foldl f acc).1.next + n ≤ acc.1.next + (l.foldl g (n, acc.2)).1 := by
  intro l
  induction l with
  | nil => intro acc n; simp
  | cons j l ih =>
    intro acc n
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := hfg acc n j
    have hg : g (n, acc.2) j = ((g (n, acc.2) j).1, (f acc j).2) := by
      rw [h1]
    have := ih (f acc j) (g (n, acc.2) j).1
    rw [← hg] at this
    omega

theorem fold_rel_goal {f : Mem V × Struct V → Nat → Mem V × Struct V}
    {g : Nat × Struct V → Nat → Nat × Struct V} {l : List Nat} {acc : Mem V × Struct V} {c : Nat}
    (hfg : ∀ acc n j, (f acc j).2 = (g (n, acc.2) j).2 ∧
      (f acc j).1.next + n ≤ acc.1.next + (g (n, acc.2) j).1)
    (hacc : acc.1.next ≤ c + 2) :
    (l.foldl f acc).1.next ≤ c + (l.foldl g (0, acc.2)).1 + 2 := by
  have := fold_rel hfg l acc 0
  omega

/-- The handles that the lazy startup gives out. -/
theorem lazyStartup_next (sp : Spec V T) (S : Stream V T) :
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length + rerunReach sp S + 2 := by
  unfold lazyStartup rerunReach
  simp only
  apply fold_rel_goal
  · intro acc n j
    cases hS : S[j]? with
    | none => simp
    | some R =>
      cases hR : R.trans with
      | none => simp [hR]
      | some tr =>
        simp only [hR]
        refine ⟨by first | rfl | trivial, ?_⟩
        have h1 := foldl_next_le _ 1 (Mem.reachOnPath_next sp S acc.2 j
          (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j))
          ((pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).mergeSort fun a b =>
            decide ((Option.map (fun x => x.level) (acc.2.get? b)).getD 0 ≤
              (Option.map (fun x => x.level) (acc.2.get? a)).getD 0)) acc.1
        rw [List.length_mergeSort] at h1
        have h2 := Mem.applyChange_next sp acc.2 j (sp.exec tr j (view sp acc.2 (j - 1)))
          (List.foldl (Mem.reachOnPath sp S acc.2 j
            (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j)) acc.1
            ((pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).mergeSort fun a b =>
              decide ((Option.map (fun x => x.level) (acc.2.get? b)).getD 0 ≤
                (Option.map (fun x => x.level) (acc.2.get? a)).getD 0)))
        have h3 := foldl_next_le _ 1 (Mem.canonicalNode_next sp S) R.gd
          (Mem.applyChange sp acc.2 j (sp.exec tr j (view sp acc.2 (j - 1)))
            (List.foldl (Mem.reachOnPath sp S acc.2 j
              (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j)) acc.1
              ((pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).mergeSort fun a b =>
                decide ((Option.map (fun x => x.level) (acc.2.get? b)).getD 0 ≤
                  (Option.map (fun x => x.level) (acc.2.get? a)).getD 0))))
        omega
  · have hF : ∀ (F : Mem V → NodeId → Mem V), (∀ m x, (F m x).next ≤ m.next + 1) →
        ∀ k, (List.foldl F ({ objs := [], table := [], s := lastSp S, root := 0, next := 1 } : Mem V)
          (sectionNodes S (lastSp S))).next + k ≤ (sectionNodes S (lastSp S)).length + 1 + k := by
      intro F hF k
      have := foldl_next_le F 1 hF (sectionNodes S (lastSp S))
        ({ objs := [], table := [], s := lastSp S, root := 0, next := 1 } : Mem V)
      simp only [Nat.one_mul] at this
      omega
    have hstep : ∀ (m : Mem V) (x : NodeId), ∀ (o : Option (Version V)),
        (match o with
        | some w =>
          if List.isEmpty (w.hist.upTo (lastSp S)) = true then m
          else
            (m.addObj (canonOfVersion sp S (lastSp S) w)).fst.setTable x
              (m.addObj (canonOfVersion sp S (lastSp S) w)).snd
        | none => m).next ≤ m.next + 1 := by
      intro m x o
      split
      · split
        · omega
        · simp
      · omega
    simp only [Mem.linkCanonical_next]
    split
    · simp only [Mem.setTable_next, Mem.addObj_next]
      exact Nat.le_trans (hF _ (fun m x => hstep m x _) 1) (by omega)
    · split
      · dsimp only
        exact Nat.le_trans (hF _ (fun m x => hstep m x _) 0) (by omega)
      · split
        · simp only [Mem.setTable_next, Mem.addObj_next]
          exact Nat.le_trans (hF _ (fun m x => hstep m x _) 1) (by omega)
        · exact Nat.le_trans (hF _ (fun m x => hstep m x _) 0) (by omega)

/-! ### For a run: the run's own paths and D -/

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- On the stream after T(k) of a run, `rerunReach` is, over the transactions
T(j) of the section, the writer's paths in the run's P after T(j - 1), the
nodes T(j) creates and gd(j). -/
theorem rerunReach_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length) :
    rerunReach sp (st sp al ts k).S =
      ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).map (fun j =>
        (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length +
          (((st sp al ts k).S[j]?).map (fun R => R.gd.length)).getD 0)).sum := by
  have hinv := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have h0 := base_sameNodes sp al ts hok hst hk
  unfold rerunReach
  simp only
  generalize hs : lastSp (st sp al ts k).S = s at h0 hsk
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ m, m ≤ k - s →
      ((List.range' (s + 1) m).foldl (fun (acc : Nat × Struct V) j =>
        match (st sp al ts k).S[j]? with
        | some R =>
          match R.trans with
          | some tr =>
            (acc.1 + (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).length +
              (sp.exec tr j (view sp acc.2 (j - 1))).new.length + R.gd.length,
              acc.2.apply j (sp.exec tr j (view sp acc.2 (j - 1))))
          | none => acc
        | none => acc) (0, baseStruct sp (st sp al ts k).S s true)).1 =
        ((List.range' (s + 1) m).map (fun j =>
          (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length +
            (changeAt sp al ts j).new.length +
            (((st sp al ts k).S[j]?).map (fun R => R.gd.length)).getD 0)).sum ∧
      SameNodes ((List.range' (s + 1) m).foldl (fun (acc : Nat × Struct V) j =>
        match (st sp al ts k).S[j]? with
        | some R =>
          match R.trans with
          | some tr =>
            (acc.1 + (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).length +
              (sp.exec tr j (view sp acc.2 (j - 1))).new.length + R.gd.length,
              acc.2.apply j (sp.exec tr j (view sp acc.2 (j - 1))))
          | none => acc
        | none => acc) (0, baseStruct sp (st sp al ts k).S s true)).2 (st sp al ts (s + m)).P := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.map_append, List.sum_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      have hj : s + 1 + m = (s + m) + 1 := by omega
      rw [hj]
      have hjl : s + m < ts.length := by omega
      have hR := st_rec hok hst (i := s + m) (j := k) (by omega) hk
      have htr : (parts sp al (st sp al ts (s + m)) ts[s + m]).R.trans = some ts[s + m] := by
        rw [parts_R]
      rw [hR]
      simp only [htr]
      rw [Nat.add_sub_cancel, ih2.view (s + m), pathOf_congr ih2, changeAt_succ (s + m) hjl]
      refine ⟨?_, ?_⟩
      · rw [ih1]
        simp only [Option.map_some, Option.getD_some, chg]
        omega
      · rw [show s + (m + 1) = (s + m) + 1 by omega, st_P_succ sp al ts hok hst hjl]
        exact ih2.apply _ _
  exact (key (k - s) (Nat.le_refl _)).1

/-- The gd's of the section are D. -/
theorem sum_gd_eq_D (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length) :
    ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).map (fun j =>
      (((st sp al ts k).S[j]?).map (fun R => R.gd.length)).getD 0)).sum =
      (st sp al ts k).D.length := by
  have hinv := inv_st sp al ts hok hst k hk
  rw [hinv.inv1, sectionD_eq, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  cases (st sp al ts k).S[j]? with
  | none => rfl
  | some R => simp

end Run

theorem sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map (fun j => f j + g j)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]; omega

/-- A cold start's reads after a run: the section's nodes, the run's writer
paths and new nodes of the section's transactions, and D. -/
theorem coldReads_run_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum + (run sp al ts).D.length + 2 := by
  have h1 := lazyStartup_next sp (run sp al ts).S
  have h2 := rerunReach_st hok hst (k := ts.length) (Nat.le_refl _)
  have h3 := sum_gd_eq_D hok hst (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h2 h3
  rw [h2, sum_map_add] at h1
  rw [h3] at h1
  simp only [st] at h1
  omega

end SIS
