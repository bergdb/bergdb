/-
bergdb 030-37: prepare old and fresh segment plans with the additional
dead-klong safety of their leaf runs, retaining the existing writer books.
-/
import Contract.Proof.DnbDeadRuns

namespace Contract.PE

open DNB PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

theorem f_hAG_dead (_hcf : cf.Ok) {f g : Nat} (IH : TreeIH cf i s f)
    (IF : DeadTreeIH cf i s f) (hs : SOk cf i s) :
    ∀ f' < f, ∀ (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat)
      (ops : List Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
      s.obj x = some (.key n) → Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup →
      (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
      (∀ z, acc.next ≤ z → s.obj z = none) →
      applyGroups cf i s f' g (live n.ks) (touched g ops) ops acc = some (es, acc') →
      ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = touched g ops ∧
        ∀ r ∈ runs, (RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
          ((live n.ks).lookup r.c) r ∧ RunDeadSafe cf r) ∧
          es.lookup r.c = r.res := by
  intro f' hf' x n lo hi ops acc es acc' hobj hsh hg hnd hq hfr hap
  obtain ⟨_, runs, hc, hm, hr⟩ := d_ag_dead f' g (live n.ks) (touched g ops) ops acc es acc'
    (f_ih_mono IH (by omega)) (fun ff hff => IF ff (by omega)) hs hfr hq
    (nodup_touched g ops) (fun c hc => mem_touched.mp hc) (fun c _ y hy hl =>
      f_long hobj hsh hg hnd c y (lookup_mem hy) hl) hap
  exact ⟨runs, hc, hm, hr⟩

theorem f_old_dead (hcf : cf.Ok) {f g h : Nat} {r : NodeId} {ops : List Contract.Op} {acc acc1 : Acc}
    {v : VN} (IH : TreeIH cf i s f) (IF : DeadTreeIH cf i s f) (hpre : SegPre cf i s g (some r) ops acc)
    (hsh : Shaped cf s g h r) (hg : Good s r 0 none) (hnd : (R s r).Nodup)
    (hp : plan cf i s f r g h ops acc = some (v, acc1)) :
    ∃ runs, OldSeg cf s g (some r) (content h (view h s r)) ∧
      PlanSeg cf i s g (some r) (content h (view h s r)) ops h v runs acc acc1 ∧ (∀ run ∈ runs, RunDeadSafe cf run) := by
  obtain ⟨sops, runs, hplan, hcv, hvok, hch, hperm, hsops, hrun, hout⟩ :=
    plan_runs hcf (fun grp y0 r => RunOk cf i s g grp y0 r ∧ RunDeadSafe cf r)
      (fun op => keyOk cf op.key = true ∧ g < op.key.length)
      (f_hAG_dead hcf IH IF hpre.sok) r h ops acc v acc1 0 none hp hsh hg hnd hpre.ops hpre.fresh
  obtain ⟨heok, hown, _, hunt⟩ := plan_own hcf hp hsh hg
  have hwfe := (view_wfe h hg hsh).1
  have hopsB : ∀ op ∈ sops, 0 ≤ op.cv ∧ Below op.cv none :=
    fun _ _ => ⟨Nat.zero_le _, trivial⟩
  refine ⟨runs, ?_, ?_, ?_⟩
  · exact
      { sorted := view_sorted h hg hsh
        pay := view_pay h hg hsh
        nodup := hnd
        walks := ((content_walks h hsh hg).trans (List.tail_sublist _)).subperm
        exist := fun z hz => reach_exists _ hg z hz
        below := walk_below h hsh hg
        keys := view_L_pays h hg hsh }
  · exact
      { vok := hvok
        eok := heok
        sops := ⟨sops, Plan.keys h 0 none _ _ _ hplan (f_holds h hsh hg) hopsB, hcv, hsops⟩
        wfe := Plan.wf h 0 none _ _ _ hplan hwfe hopsB
        own := hown
        untouched := hunt
        chain := hch
        perm := hperm
        run := fun run hr => (hrun run hr).1
        outUi := hout }

  · exact fun run hr => (hrun run hr).2

theorem f_new_dead (hcf : cf.Ok) {f g : Nat} {ops : List Contract.Op} {acc acc1 : Acc} {v : VN}
    {es : List (Nat × NodeId)} (IH : TreeIH cf i s f) (IF : DeadTreeIH cf i s f) (hpre : SegPre cf i s g none ops acc)
    (hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc1))
    (hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    ∃ runs, OldSeg cf s g none [] ∧ PlanSeg cf i s g none [] ops 0 v runs acc acc1 ∧ (∀ r ∈ runs, RunDeadSafe cf r) := by
  obtain ⟨_, runs, hch, hmap, hrun⟩ := d_ag_dead f g [] (touched g ops) ops acc es acc1 IH IF
    hpre.sok hpre.fresh hpre.ops (nodup_touched g ops) (fun c hc => mem_touched.mp hc)
    (by intro c hc y0 h hl; simp at h) hag
  obtain ⟨heok, hui, hpo, htch, _⟩ := plan_new_own hag hmk
  obtain ⟨⟨F, dec, rfl⟩, hvok⟩ := mkNode_leaf hcf hmk (by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨a, _, rfl⟩ := he
    exact ⟨_, rfl⟩)
  obtain ⟨hsorted, hlk⟩ := applyGroups_spec f g [] _ ops acc es acc1 hag List.Pairwise.nil
  have habs : absV s 0 (.node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) F dec) = es := by
    show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    apply List.map_congr_left
    intro e _
    rfl
  refine ⟨runs, ?_, ?_, ?_⟩
  · exact
      { sorted := List.Pairwise.nil
        pay := by simp
        nodup := List.nodup_nil
        walks := by simp [Ro]
        exist := by simp [Ro]
        below := by simp
        keys := rfl }
  · refine
      { vok := hvok
        eok := heok
        sops := ⟨finalOps (touched g ops) es, ?_, finalOps_cv _ _, ?_⟩
        wfe := ?_
        own := ?_
        untouched := fun p hp ht => absurd (htch p hp) ht
        chain := hch
        perm := by rw [hmap]
        run := fun r hr => (hrun r hr).1.1
        outUi := ?_ }
    · show absV s 0 _ = _
      rw [habs]
      exact (applyOps_finalOps (touched g ops) [] es List.Pairwise.nil hsorted
        (fun c hc => hlk c hc)).symm
    · intro o ho
      simp only [finalOps, List.mem_map] at ho
      obtain ⟨c, hc, rfl⟩ := ho
      rw [← hmap] at hc
      simp only [List.mem_map] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      refine ⟨r, hr, ?_, ?_⟩
      · split <;> rfl
      · rw [(hrun r hr).2]
        cases r.res <;> rfl
    · rw [habs]
      by_cases he : es = []
      · exact Or.inl he
      · exact Or.inr ⟨he, hsorted, fun e _ => ⟨Nat.zero_le _, trivial⟩⟩
    · rw [hui, hpo]
      exact List.nil_subperm
    · intro r _ y0 hy0
      simp at hy0

  · intro run hr
    simpa using (hrun run hr).1.2

end Contract.PE
