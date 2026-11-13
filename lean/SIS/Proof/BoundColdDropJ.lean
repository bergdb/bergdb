/-
Proofs for the nodes a change makes unreachable with `DropStepJ` (bergdb item
007; SIS/BoundColdDropJ.lean). Added 2026-11-13.

Every node z that a change makes unreachable has a parent p at j - 1 (a
reachable node with z as a live child), and z is one of p's lost children
(`lostTo`). Either p stays reachable, and its lost children are charged to the
weights of p's entries (`DropStepJ.kept`), or p is made unreachable too, and
its lost children are counted by `DropStepJ.dropped`.
-/
import SIS.BoundColdDropJ
import SIS.Proof.BoundHeight

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem sum_ite_le_val (a : NodeId) (x : Nat) : ∀ W : List NodeId, W.Nodup →
    (W.map (fun p => if a = p then x else 0)).sum ≤ x := by
  intro W
  induction W with
  | nil => intro _; simp
  | cons q W ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases haq : a = q
    · subst haq
      have : (W.map (fun p => if a = p then x else 0)).sum = 0 := by
        have h0 : W.map (fun p => if a = p then x else 0) = W.map (fun _ => 0) := by
          apply List.map_congr_left
          intro p hp
          have : a ≠ p := fun h => hnd.1 (h ▸ hp)
          simp [this]
        rw [h0, sum_map_const]; simp
      simp [this]
    · simp only [haq, ite_false]
      have := ih hnd.2
      omega

/-- Over distinct nodes, the weights of the entries for each node add up to at
most the weights of all entries. -/
theorem sum_weight_le (w : V → Nat) (l : List (NodeId × V)) : ∀ W : List NodeId, W.Nodup →
    (W.map (fun p => ((l.filter (fun a => a.1 == p)).map (fun a => w a.2)).sum)).sum ≤
      (l.map (fun a => w a.2)).sum := by
  induction l with
  | nil => intro W _; simp [sum_map_const]
  | cons a l ih =>
    intro W hnd
    have h1 : W.map (fun p => (((a :: l).filter (fun a => a.1 == p)).map (fun a => w a.2)).sum) =
        W.map (fun p => (if a.1 = p then w a.2 else 0) +
          ((l.filter (fun a => a.1 == p)).map (fun a => w a.2)).sum) := by
      apply List.map_congr_left
      intro p _
      by_cases h : a.1 = p
      · simp [h]
      · simp [h]
    rw [h1, sum_map_add]
    have := sum_ite_le_val a.1 (w a.2) W hnd
    have := ih W hnd
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_filter_le (l : List Nat) (f : Nat → Bool) (g : Nat → Nat) :
    ((l.filter f).map g).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : f a = true
    · simp [h]; omega
    · simp [h]; omega

theorem sum_map_congr_mem (l : List Nat) (f g : Nat → Nat) (h : ∀ j ∈ l, f j = g j) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

/-- With `DropStepJ`, a change makes at most as many nodes unreachable as the
weights of its entries plus k. -/
theorem removedAt_le_J (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V)
    (k : Nat) (hd : DropStepJ sp w P j c k) :
    (removedAt sp P c j).length ≤ (c.adds.map (fun a => w a.2)).sum + k := by
  classical
  let surv : NodeId → Bool := fun p => reachable sp P (j - 1) p && reachable sp (P.apply j c) j p
  let N : NodeId → Nat := fun p => if surv p then addsWeight w c p else (lostTo sp P (P.apply j c) j p).length
  have hrem : ∀ z ∈ removedAt sp P c j, ∃ p ∈ (((c.adds.map (·.1)).eraseDups).filter surv) ++ removedAt sp P c j, z ∈ lostTo sp P (P.apply j c) j p := by
    intro z hz
    have hz' := hz
    unfold removedAt at hz'
    rw [List.mem_filter, List.mem_eraseDups] at hz'
    obtain ⟨hzr, hzn⟩ := hz'
    have hzr' : reachable sp P (j - 1) z = true := by
      unfold reachable; exact List.contains_iff_mem.mpr hzr
    have hzn' : reachable sp (P.apply j c) j z = false := by simpa using hzn
    have hzroot : z ≠ root := by
      intro h
      subst h
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hzr'))
      have : reachable sp (P.apply j c) j root = true :=
        (reachable_iff _ _ _ _).mpr (Reach.root _ (get?_apply_of_get? hn))
      rw [hzn'] at this; cases this
    obtain ⟨p, np, nz, hpr, hnp, hnz, hlt, hzl⟩ := reach_parent hzr' hzroot
    have hzlost : z ∈ lostTo sp P (P.apply j c) j p := by
      unfold lostTo
      rw [hnp]
      simp only
      rw [List.mem_filter, List.mem_eraseDups]
      refine ⟨hzl, ?_⟩
      simpa using hzn'
    refine ⟨p, ?_, hzlost⟩
    cases hp' : reachable sp (P.apply j c) j p with
    | true =>
      apply List.mem_append_left
      rw [List.mem_filter]
      refine ⟨?_, by simp [surv, hpr, hp']⟩
      rw [List.mem_eraseDups]
      have hpos : 0 < addsWeight w c p := by
        have := hd.kept p hpr hp'
        have : 0 < (lostTo sp P (P.apply j c) j p).length := List.length_pos_of_mem hzlost
        omega
      unfold addsWeight at hpos
      have hne : c.adds.filter (fun a => a.1 == p) ≠ [] := by
        intro h; rw [h] at hpos; simp at hpos
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
      rw [List.mem_filter, beq_iff_eq] at ha
      exact List.mem_map.mpr ⟨a, ha.1, ha.2⟩
    | false =>
      apply List.mem_append_right
      unfold removedAt
      rw [List.mem_filter, List.mem_eraseDups]
      refine ⟨?_, by simpa using hp'⟩
      unfold reachable at hpr
      exact List.contains_iff_mem.mp hpr
  have hnd : (removedAt sp P c j).Nodup := by
    unfold removedAt
    exact (nodup_eraseDups _).filter _
  have h1 := nodup_length_le_sum (fun p z => z ∈ lostTo sp P (P.apply j c) j p) N
    (fun p L hL hLp => by
      have hsub : L.length ≤ (lostTo sp P (P.apply j c) j p).length := by
        have hlnd : (lostTo sp P (P.apply j c) j p).Nodup := by
          unfold lostTo
          split
          · exact (nodup_eraseDups _).filter _
          · exact List.nodup_nil
        exact nodup_length_le_sub hL hLp
      by_cases hs : surv p = true
      · have hpr : reachable sp P (j - 1) p = true ∧ reachable sp (P.apply j c) j p = true := by
          simpa [surv] using hs
        have := hd.kept p hpr.1 hpr.2
        simp only [N, hs, ite_true]
        omega
      · simpa [N, hs] using hsub)
    ((((c.adds.map (·.1)).eraseDups).filter surv) ++ removedAt sp P c j) (removedAt sp P c j) hnd hrem
  rw [List.map_append, List.sum_append] at h1
  have hW1 : ((((c.adds.map (·.1)).eraseDups).filter surv).map N).sum ≤ (c.adds.map (fun a => w a.2)).sum := by
    have e1 : ((((c.adds.map (·.1)).eraseDups).filter surv).map N).sum = ((((c.adds.map (·.1)).eraseDups).filter surv).map (addsWeight w c)).sum := by
      apply sum_map_congr_mem
      intro p hp
      have hs : surv p = true := (List.mem_filter.mp hp).2
      simp only [N, hs, ite_true]
    rw [e1]
    have := sum_filter_le ((c.adds.map (·.1)).eraseDups) surv (addsWeight w c)
    have := sum_weight_le w c.adds ((c.adds.map (·.1)).eraseDups) (nodup_eraseDups _)
    unfold addsWeight
    unfold addsWeight at *
    omega
  have hR : ((removedAt sp P c j).map N).sum ≤ k := by
    have e2 : ((removedAt sp P c j).map N).sum =
        ((removedAt sp P c j).map (fun z => (lostTo sp P (P.apply j c) j z).length)).sum := by
      apply sum_map_congr_mem
      intro z hz
      unfold removedAt at hz
      rw [List.mem_filter] at hz
      have hs : surv z = false := by
        have h2 := hz.2
        simp only [Bool.not_eq_true'] at h2
        simp [surv, h2]
      simp only [N, hs]
      simp
    rw [e2]
    exact hd.dropped
  omega

/-- The weight of the entries of T(j) in a run. -/
theorem coldReads_height_dropJ_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length)).sum + 2 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have h := coldReads_run_noD_of sp al ts hok hla htree hj
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
      (changeAt sp al ts j).new.length)
    (fun j => (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length) (by
      intro j hj
      simp only [sectionIdx, List.mem_range'_1, run_length] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < ts.length := by omega
      have htj : treeAt sp (run sp al (ts.take j')).P j' := by
        rcases Nat.eq_zero_or_pos j' with h0' | hpos
        · subst h0'; rw [List.take_zero]; exact htree0
        · obtain ⟨j'', hj''⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
          subst hj''
          exact htree j'' (by omega)
      have hinvj := inv_st sp al ts hok hst j' (by omega)
      obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hinvj.rootIn
      have hp := pathOf_count_height (P := (st sp al ts j').P) (j := j' + 1)
        (by simpa [st] using htj) hnr (by simpa [st] using hH j' (by omega))
        (changeAt sp al ts (j' + 1))
      have hr := removedAt_le_J sp w _ _ _ _ (hdrop j' hj')
      rw [changeAt_succ j' hj'] at hp ⊢
      simp only [Nat.add_sub_cancel, chg, st] at hp hr ⊢
      have := Nat.mul_le_mul_left (H + 1)
        (show (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            (removedAt sp (run sp al (List.take j' ts)).P
              (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')) (j' + 1)).length ≤
          (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            ((sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.map
              (fun a => w a.2)).sum + k (j' + 1) by
          omega)
      omega)
  omega

end SIS

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- `DropStepJ` by running: `kept` for the nodes reachable at j - 1 (the only
ones it asks about), and `dropped`. -/
def dropStepJB (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V) (k : Nat) :
    Bool :=
  (reachList sp P (j - 1)).all (fun p => !reachable sp (P.apply j c) j p ||
      decide ((lostTo sp P (P.apply j c) j p).length ≤ addsWeight w c p)) &&
    decide (((removedAt sp P c j).map (fun z => (lostTo sp P (P.apply j c) j z).length)).sum ≤ k)

theorem dropStepJ_of_B (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V)
    (k : Nat) (h : dropStepJB sp w P j c k = true) : DropStepJ sp w P j c k := by
  unfold dropStepJB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun p hp hp' => ?_, h.2⟩
  have hm : p ∈ reachList sp P (j - 1) := by
    unfold reachable at hp; exact List.contains_iff_mem.mp hp
  have := h.1 p hm
  simpa [hp'] using this

end SIS
