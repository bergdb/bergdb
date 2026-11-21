/-
bergdb 030-37: carry fill of next-segment roots through the leaf runs.
The extra run property is conditional on fill of its old root, so the
existing routing and write ownership facts remain available unchanged.
-/
import Contract.Proof.DnbFillTransfer

namespace Contract.PE

open DNB PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

def TreeFilled (cf : Cfg) (i : Time) (s : Tree) (root : Option NodeId)
    (acc acc' : Acc) (res : Option NodeId) : Prop :=
  ∀ W, WOkV i s (Ro s root) acc acc' W → ∀ T, After s T W (Ro s root) →
    ∀ y, res = some y → Filled cf T true y

def FillTreeIH (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ f < F, ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc)
    (res : Option NodeId) (acc' : Acc), SegPre cf i s g root ops acc →
    (∀ y, root = some y → Filled cf s true y) →
    planTree cf i s f root g ops acc = some (res, acc') → TreeFilled cf i s root acc acc' res

def RunFilled (cf : Cfg) (i : Time) (s : Tree) (y0 : Option NodeId) (r : Run) : Prop :=
  isLong r.c = true → (∀ y, y0 = some y → Filled cf s true y) →
    TreeFilled cf i s y0 r.a r.a' r.res

theorem d_run_long_filled {f g c : Nat} {ops : List Op} {y0 : Option NodeId}
    {acc acc1 : Acc} {res : Option NodeId}
    (hIH : FillTreeIH cf i s (f + 1)) (hs : SOk cf i s)
    (hfresh : ∀ z, acc.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) (hc : isLong c = true)
    (hroot : ∀ y, y0 = some y →
      Shaped cf s (g + 1) (htIn cf s y) y ∧ Good s y 0 none ∧ (R s y).Nodup)
    (hp : planTree cf i s f y0 (g + 1) (ops.filter (fun op => segAt g op == c)) acc =
      some (res, acc1)) : RunFilled cf i s y0 ⟨c, res, acc, acc1⟩ := by
  intro _ hfill
  have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
    have := (hops op hop).1
    simp only [keyOk, Bool.and_eq_true] at this
    exact this.1
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
  have hpre : SegPre cf i s (g + 1) y0 (ops.filter (fun op => segAt g op == c)) acc := by
    refine ⟨hs, hfresh, fun op hop => ⟨(hops op (mem_grp hop).1).1, ?_⟩, hroot⟩
    obtain ⟨hm1, hm2⟩ := mem_grp hop
    have he := endsAt_of_keyWf (hw op hm1) (hg op hm1)
    rw [hm2, hc] at he
    have := hg op hm1
    simp only [endsAt, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at he
    omega
  exact hIH f (Nat.lt_succ_self f) y0 (g + 1) _ acc res acc1 hpre hfill hp

theorem d_ag_filled : ∀ (f g : Nat) (es0 : List (Nat × NodeId)) (cvs : List Nat)
    (ops : List Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    TreeIH cf i s f → FillTreeIH cf i s f → SOk cf i s → (∀ z, acc.next ≤ z → s.obj z = none) →
    (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    cvs.Nodup → (∀ c ∈ cvs, ∃ op ∈ ops, segAt g op = c) →
    (∀ c ∈ cvs, ∀ y0, es0.lookup c = some y0 → isLong c = true →
      Shaped cf s (g + 1) (htIn cf s y0) y0 ∧ Good s y0 0 none ∧ (R s y0).Nodup) →
    applyGroups cf i s f g es0 cvs ops acc = some (es, acc') →
    (∀ c, c ∉ cvs → es.lookup c = es0.lookup c) ∧
    ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cvs ∧
      ∀ r ∈ runs, (RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
        (es0.lookup r.c) r ∧ RunFilled cf i s (es0.lookup r.c) r) ∧ es.lookup r.c = r.res
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [applyGroups] at h
  | f + 1, g, es0, [], ops, acc, es, acc', _, _, _, _, _, _, _, _, h => by
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => rfl, [], rfl, rfl, by simp⟩
  | f + 1, g, es0, cv :: cvs, ops, acc, es, acc', hIH, hFill, hs, hfresh, hops, hnd, hne, hroot, h => by
    have hIH' : TreeIH cf i s f := fun f' hf' => hIH f' (by omega)
    have hFill' : FillTreeIH cf i s f := fun f' hf' => hFill f' (by omega)
    rw [List.nodup_cons] at hnd
    have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
      have := (hops op hop).1
      simp only [keyOk, Bool.and_eq_true] at this
      exact this.1
    have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
    have fin : ∀ (es1 : List (Nat × NodeId)) (acc1 : Acc) (res : Option NodeId),
        (RunOk cf i s g (ops.filter (fun op => segAt g op == cv)) (es0.lookup cv)
          ⟨cv, res, acc, acc1⟩ ∧ RunFilled cf i s (es0.lookup cv) ⟨cv, res, acc, acc1⟩) →
        acc.next ≤ acc1.next → (∀ a, a ≠ cv → es1.lookup a = es0.lookup a) →
        es1.lookup cv = res → applyGroups cf i s f g es1 cvs ops acc1 = some (es, acc') →
        (∀ c, c ∉ cv :: cvs → es.lookup c = es0.lookup c) ∧
        ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cv :: cvs ∧
          ∀ r ∈ runs, (RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
            (es0.lookup r.c) r ∧ RunFilled cf i s (es0.lookup r.c) r) ∧ es.lookup r.c = r.res := by
      intro es1 acc1 res hrun hnext hlk hres h2
      obtain ⟨hout, runs, hch, hmap, hruns⟩ := d_ag_filled f g es1 cvs ops acc1 es acc' hIH' hFill' hs
        (fun z hz => hfresh z (by nomega)) hops hnd.2
        (fun c hc => hne c (List.mem_cons_of_mem _ hc))
        (fun c hc y0 hy0 hl => hroot c (List.mem_cons_of_mem _ hc) y0
          (by rw [← hlk c (fun h => hnd.1 (h ▸ hc))]; exact hy0) hl) h2
      refine ⟨fun a ha => ?_, ⟨cv, res, acc, acc1⟩ :: runs, ⟨rfl, hnext, hch⟩,
        by simp [hmap], ?_⟩
      · simp only [List.mem_cons, not_or] at ha
        rw [hout a ha.2, hlk a ha.1]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hrun, by rw [hout cv hnd.1]; exact hres⟩
        · have hrc : r.c ∈ cvs := hmap ▸ List.mem_map_of_mem hr
          have hne' : r.c ≠ cv := fun h => hnd.1 (h ▸ hrc)
          obtain ⟨a1, a2⟩ := hruns r hr
          rw [hlk r.c hne'] at a1
          exact ⟨a1, a2⟩
    unfold applyGroups at h
    simp only at h
    generalize hq : List.foldl _ (es0, acc) _ = q at h
    obtain ⟨es1, acc1⟩ := q
    simp only at h
    cases hcl : isLong cv with
    | false =>
      rw [(grp_short hw hg hcl).1] at hq
      obtain ⟨hrun, hnext, hlk⟩ := d_run_short (y0 := es0.lookup cv) _ hq
        (by intro q k hv; rfl) (by intro q k; rfl) hfresh hops (hne cv List.mem_cons_self) hcl
      split at h
      · exact fin es1 acc1 _ ⟨hrun, by intro hl; rw [hcl] at hl; cases hl⟩ hnext hlk rfl h
      · rename_i hsub
        exfalso
        apply hsub
        rw [(grp_short hw hg hcl).2]
        rfl
    | true =>
      rw [(grp_long hw hg hcl).1, List.foldl_nil, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      split at h
      · rename_i hsub
        exfalso
        rw [(grp_long hw hg hcl).2, List.isEmpty_iff] at hsub
        obtain ⟨op0, hop0, hc0⟩ := hne cv List.mem_cons_self
        have : op0 ∈ ops.filter (fun op => segAt g op == cv) :=
          List.mem_filter.mpr ⟨hop0, by simp [hc0]⟩
        rw [hsub] at this
        simp at this
      · split at h
        · cases h
        · rename_i y acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 (some y) ⟨hrun, d_run_long_filled hFill hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp⟩ hnext
            (fun a ha => by rw [setEntry_lookup, ite_eq_right ha])
            (by rw [setEntry_lookup, ite_eq_left rfl]) h
        · rename_i acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 none ⟨hrun, d_run_long_filled hFill hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp⟩ hnext
            (fun a ha => by rw [removeEntry_lookup, ite_eq_right ha])
            (by rw [removeEntry_lookup, ite_eq_left rfl]) h


end Contract.PE
