/-
Proofs for bounds, part 3 (bergdb item 007; 007-03, step 6): a cold start's
reads after a run without the |D| term. Added 2026-11-13.

With BergDB's still-dirty test, TREE and `LiveAppend`, the lazy startup's rerun
keeps its memory invariant (`rerunStep_ok`), by which every node of gd(j) has a
canonical object once T(j)'s change is applied (`MemInv.coverGd`): the
writer's paths and the new nodes cover the nodes that got dirty, and a node put
back by step 7 has a canonical object from an earlier step, the section or the
change. So step 3's `canonicalNode` makes no object, and the handles are the
section's nodes, the writer's paths and the new nodes.
-/
import SIS.Proof.BoundCold
import SIS.Proof.PhysT1
import SIS.Proof.PhysAssumptions
import SIS.BoundColdDrop

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The memory before the rerun gives out at most the section's nodes + 2
handles (as in `lazyStartup_next`). -/
theorem lazyBase_next (sp : Spec V T) (S : Stream V T) :
    (lazyBase sp S).next ≤ (sectionNodes S (lastSp S)).length + 2 := by
  unfold lazyBase lazyRoot lazySec secStep mem0
  have hF : ∀ (F : Mem V → NodeId → Mem V), (∀ m x, (F m x).next ≤ m.next + 1) →
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

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The rerun after T(k), with the invariant, gives out per transaction T(j)
at most its writer's paths in the run's P after T(j - 1) and its new nodes. -/
theorem rerun_fold_next (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) {k : Nat} (hk : k ≤ ts.length) {m0 : Mem V} {P0 : Struct V}
    (hm0 : MemInv sp (st sp al ts k) (lastSp (st sp al ts k).S) m0)
    (hP0 : SameNodes P0 (st sp al ts (lastSp (st sp al ts k).S)).P) :
    ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl
      (rerunStep sp (st sp al ts k).S) (m0, P0)).1.next ≤ m0.next +
      ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).map (fun j =>
        (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ n, n ≤ k - s →
      MemInv sp (st sp al ts k) (s + n)
          ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, P0)).1 ∧
        SameNodes ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, P0)).2
          (st sp al ts (s + n)).P ∧
        ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, P0)).1.next ≤
          m0.next + ((List.range' (s + 1) n).map (fun j =>
            (pathOf sp (st sp al ts (j - 1)).P (changeAt sp al ts j) j).length +
              (changeAt sp al ts j).new.length)).sum := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hm0, hP0, by simp⟩
    | succ n ih =>
      intro hn
      rw [List.range'_concat, List.foldl_append, List.map_append, List.sum_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      generalize hacc : (List.foldl (rerunStep sp (st sp al ts k).S) (m0, P0)
        (List.range' (s + 1) n)) = acc at h1 h2 h3
      have hK : s + n < ts.length := by omega
      have hKk : s + n < k := by omega
      obtain ⟨g1, g2⟩ := rerunStep_ok hok hph hj hk (K := s + n) (by rw [hs]; omega) hKk h1 h2
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      refine ⟨g1, g2, ?_⟩
      -- The count of the step.
      have htr := st_trans sp al ts hok hst (j := s + n + 1) (k := k) (by omega) (by omega) hk
      simp only [Nat.add_sub_cancel] at htr
      obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[s + n + 1]? = some R ∧ R.trans = some ts[s + n] := by
        cases h : (st sp al ts k).S[s + n + 1]? with
        | none => rw [h] at htr; cases htr
        | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
      have hm2 := rerun_apply_ok hok hph hj hk hKk h1 h2 (tr := ts[s + n])
        (List.getElem?_eq_getElem hK)
      rw [rerunStep_eq sp _ acc hR hRt]
      simp only [Nat.add_sub_cancel]
      rw [foldl_canonicalNode_noop sp _ _ R.gd
        (fun x hx => hm2.coverGd (s + n + 1) R x (by omega) (Nat.le_refl _) hR hx)]
      have e1 := foldl_next_le _ 1 (Mem.reachOnPath_next sp (st sp al ts k).S acc.2 (s + n + 1)
        (pathOf sp acc.2 (sp.exec ts[s + n] (s + n + 1) (view sp acc.2 (s + n))) (s + n + 1)))
        ((pathOf sp acc.2 (sp.exec ts[s + n] (s + n + 1) (view sp acc.2 (s + n))) (s + n + 1)).mergeSort
          fun a b => decide (lev acc.2 b ≤ lev acc.2 a)) acc.1
      rw [List.length_mergeSort] at e1
      have e2 := Mem.applyChange_next sp acc.2 (s + n + 1)
        (sp.exec ts[s + n] (s + n + 1) (view sp acc.2 (s + n)))
        (List.foldl (Mem.reachOnPath sp (st sp al ts k).S acc.2 (s + n + 1)
          (pathOf sp acc.2 (sp.exec ts[s + n] (s + n + 1) (view sp acc.2 (s + n))) (s + n + 1)))
          acc.1 ((pathOf sp acc.2 (sp.exec ts[s + n] (s + n + 1) (view sp acc.2 (s + n)))
            (s + n + 1)).mergeSort fun a b => decide (lev acc.2 b ≤ lev acc.2 a)))
      rw [h2.view (s + n), pathOf_congr h2] at e1 e2 ⊢
      rw [changeAt_succ (s + n) hK]
      simp only [chg] at e1 e2 ⊢
      omega
  have := (key (k - s) (Nat.le_refl _)).2.2
  exact this

end Run

/-- A cold start's reads after a run, without D: the lazy startup gives out at
most the section's nodes, the run's writer paths and new nodes of the section's
transactions, and 2. -/
theorem coldReads_run_noD_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (htree : TreeRunOK sp al ts) (hj : al.stillDirty = javaTest sp) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum + 2 := by
  have hph := physRunOK_of_tree hok hla htree
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hk : ts.length ≤ ts.length := Nat.le_refl _
  have hctx := pctx_st hok hst hk
  have hsk : lastSp (st sp al ts ts.length).S ≤ ts.length := by have := hctx.inv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  have h1 := rerun_fold_next hok hph hj hk (hctx.base_ok hkS) (base_sameNodes sp al ts hok hst hk)
  have h2 := lazyBase_next sp (st sp al ts ts.length).S
  rw [lazyStartup_eq]
  rw [st_length] at h1 h2
  simp only [st] at h1
  omega

/-- A cold start's reads after a run with TREE, without D: as `coldReads_tree`,
without its |D| term. -/
theorem coldReads_tree_noD_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (n0.level + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          (removedAt sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length) +
        (changeAt sp al ts j).new.length)).sum + 2 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have h := coldReads_run_noD_of sp al ts hok hla htree hj
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
      (changeAt sp al ts j).new.length)
    (fun j => (n0.level + 1) * ((changeAt sp al ts j).new.length +
      (changeAt sp al ts j).adds.length + (changeAt sp al ts j).touch.length +
      (removedAt sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length) +
      (changeAt sp al ts j).new.length) (by
      intro j hj
      simp only [sectionIdx, List.mem_range'_1, run_length] at hj
      have hj1 : j - 1 ≤ ts.length := by omega
      have htj : treeAt sp (run sp al (ts.take (j - 1))).P (j - 1) := by
        rcases Nat.eq_zero_or_pos (j - 1) with h0' | hpos
        · rw [h0', List.take_zero]; exact htree0
        · obtain ⟨j', hj'⟩ : ∃ j', j - 1 = j' + 1 := ⟨j - 2, by omega⟩
          rw [hj']
          exact htree j' (by omega)
      have hinvj := inv_st sp al ts hok hst (j - 1) hj1
      obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hinvj.rootIn
      have hg := st_grow sp al ts hok hst (j := j - 1) (j' := ts.length) hj1 hK
      obtain ⟨nrK, hnrK, hl, -, -⟩ := hg root nr hnr
      rw [st_length, h0, Option.some.injEq] at hnrK
      subst hnrK
      have := pathOf_count (P := (st sp al ts (j - 1)).P) (j := j) htj hnr (changeAt sp al ts j)
      rw [← hl] at this
      simp only [st] at this
      omega)
  omega

/-! ### The nodes a change makes unreachable -/

theorem sum_ite_le_one (a : NodeId) : ∀ W : List NodeId, W.Nodup →
    (W.map (fun p => if a = p then 1 else 0)).sum ≤ 1 := by
  intro W
  induction W with
  | nil => intro _; simp
  | cons q W ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases haq : a = q
    · subst haq
      have : (W.map (fun p => if a = p then 1 else 0)).sum = 0 := by
        have h0 : W.map (fun p => if a = p then 1 else 0) = W.map (fun _ => 0) := by
          apply List.map_congr_left
          intro p hp
          have : a ≠ p := fun h => hnd.1 (h ▸ hp)
          simp [this]
        rw [h0, sum_map_const]; simp
      simp [this]
    · simp only [haq, ite_false]
      have := ih hnd.2
      omega

/-- Over distinct nodes, the entries for each node add up to at most all
entries. -/
theorem sum_count_le (l : List (NodeId × V)) : ∀ W : List NodeId, W.Nodup →
    (W.map (fun p => (l.filter (fun a => a.1 == p)).length)).sum ≤ l.length := by
  induction l with
  | nil => intro W _; simp [sum_map_const]
  | cons a l ih =>
    intro W hnd
    have h1 : W.map (fun p => ((a :: l).filter (fun a => a.1 == p)).length) =
        W.map (fun p => (if a.1 = p then 1 else 0) + (l.filter (fun a => a.1 == p)).length) := by
      apply List.map_congr_left
      intro p _
      by_cases h : a.1 = p
      · simp [h]; omega
      · simp [h]
    rw [h1, sum_map_add]
    have := sum_ite_le_one a.1 W hnd
    have := ih W hnd
    simp only [List.length_cons]
    omega

theorem nodup_length_le_sub {L M : List NodeId} (hL : L.Nodup) (h : ∀ x ∈ L, x ∈ M) :
    L.length ≤ M.length := by
  have := nodup_length_le_sum (fun y x => x = y) (fun _ => 1)
    (fun y L' hnd' hL' => length_le_one_of_nodup hnd' (fun a ha b hb => by
      rw [hL' a ha, hL' b hb])) M L hL (fun x hx => ⟨x, h x hx, rfl⟩)
  rwa [sum_map_const, Nat.mul_one] at this

/-- With `DropStep`, a change makes at most as many nodes unreachable as it adds
entries. -/
theorem removedAt_le_adds (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (hd : DropStep sp P j c) : (removedAt sp P c j).length ≤ c.adds.length := by
  classical
  have hrem : ∀ z ∈ removedAt sp P c j, ∃ p ∈ (c.adds.map (·.1)).eraseDups,
      (reachable sp P (j - 1) p = true ∧ reachable sp (P.apply j c) j p = true) ∧
        z ∈ lostLive sp P (P.apply j c) j p := by
    intro z hz
    unfold removedAt at hz
    rw [List.mem_filter, List.mem_eraseDups] at hz
    obtain ⟨hzr, hzn⟩ := hz
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
    have hpr' : reachable sp (P.apply j c) j p = true := by
      cases h : reachable sp (P.apply j c) j p with
      | true => rfl
      | false =>
        have := hd.adopted p np hpr h hnp z hzl
        rw [hzn'] at this; cases this
    have hnl : z ∉ sp.live (({ np with hist := np.hist ++ addsFor c j p } : Node V).hist.upTo j) := by
      intro hin
      have : reachable sp (P.apply j c) j z = true :=
        (reachable_iff _ _ _ _).mpr (Reach.child ((reachable_iff _ _ _ _).mp hpr')
          (get?_apply_of_get? hnp) hin (get?_apply_of_get? hnz) hlt)
      rw [hzn'] at this; cases this
    have hzlost : z ∈ lostLive sp P (P.apply j c) j p := by
      unfold lostLive
      rw [hnp, get?_apply_of_get? hnp]
      simp only
      rw [List.mem_filter, List.mem_eraseDups]
      refine ⟨hzl, ?_⟩
      simpa using hnl
    refine ⟨p, ?_, ⟨hpr, hpr'⟩, hzlost⟩
    rw [List.mem_eraseDups]
    have hpos : 0 < (c.adds.filter (fun a => a.1 == p)).length := by
      have := hd.lost p hpr hpr'
      have : 0 < (lostLive sp P (P.apply j c) j p).length :=
        List.length_pos_of_mem hzlost
      omega
    obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hpos
    rw [List.mem_filter, beq_iff_eq] at ha
    exact List.mem_map.mpr ⟨a, ha.1, ha.2⟩
  have hnd : (removedAt sp P c j).Nodup := by
    unfold removedAt
    exact (nodup_eraseDups _).filter _
  have h1 := nodup_length_le_sum (fun p z =>
      (reachable sp P (j - 1) p = true ∧ reachable sp (P.apply j c) j p = true) ∧
        z ∈ lostLive sp P (P.apply j c) j p)
    (fun p => (c.adds.filter (fun a => a.1 == p)).length)
    (fun p L hL hLp => by
      cases L with
      | nil => exact Nat.zero_le _
      | cons z0 L' =>
        have hpr := (hLp z0 (by simp)).1
        have hsub := nodup_length_le_sub hL (fun x hx => (hLp x hx).2)
        exact Nat.le_trans hsub (hd.lost p hpr.1 hpr.2))
    ((c.adds.map (·.1)).eraseDups) (removedAt sp P c j) hnd hrem
  have h2 := sum_count_le c.adds ((c.adds.map (·.1)).eraseDups) (nodup_eraseDups _)
  omega

/-- A cold start's reads after a run with TREE, without D and with `DropRunOK`:
as `coldReads_tree`, with no |D| term and an entry in place of each node made
unreachable. -/
theorem coldReads_tree_drop_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts) (hdrop : DropRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (n0.level + 1) * ((changeAt sp al ts j).new.length + 2 * (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length)).sum + 2 := by
  have h := coldReads_tree_noD_of sp al ts hok hla hj htree0 htree n0 h0
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (n0.level + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          (removedAt sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length) +
        (changeAt sp al ts j).new.length)
    (fun j => (n0.level + 1) * ((changeAt sp al ts j).new.length +
        2 * (changeAt sp al ts j).adds.length + (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length) (by
      intro j hj
      simp only [sectionIdx, List.mem_range'_1, run_length] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < ts.length := by omega
      have hd := hdrop j' hj'
      rw [changeAt_succ j' hj', Nat.add_sub_cancel]
      have hr := removedAt_le_adds sp _ _ _ hd
      simp only [chg, st]
      have := Nat.mul_le_mul_left (n0.level + 1)
        (show (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            (removedAt sp (run sp al (List.take j' ts)).P
              (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')) (j' + 1)).length ≤
          (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            2 * (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length by
          omega)
      omega)
  omega

end SIS
