/-
bergdb 030-37: emit one segment with filled next-segment payloads.
The existing writer books separate emit's writes from the leaf runs and
supply each run's after-state. The final abstract fill gives Filled.
-/
import Contract.Proof.DnbFillRuns

namespace Contract.PE

open DNB PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

theorem seg_some_filled {b G H : Nat} (hb : 8 ≤ b) (hjava : cf = Cfg.java b G H) (hcf : cf.Ok)
    {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v v' : VN} {runs : List Run} {acc0 acc1 acc2 : Acc} {space : Bool}
    {c0 r' : NodeId}
    (hs : SOk cf i s) (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hfillPlan : VFill cf i s g true h v)
    (hfillOld : ∀ p ∈ E, isLong p.1 = true → Filled cf s true p.2)
    (hfillRuns : ∀ r ∈ runs, RunFilled cf i s (E.lookup r.c) r)
    (hset : settleRoot cf i s f g v space = some (some v'))
    (he : emit cf i s v' acc1 = some ([(c0, r')], acc2)) :
    ∃ W, WOkV i s (Ro s root) acc0 acc2 W ∧
      ∀ T, After s T W (Ro s root) → Filled cf T true r' := by
  have hnd := e_runs_nodup hp
  have h01 : acc0.next ≤ acc1.next := chain_next hp.chain
  have hE's : (content h (absV s h v)).Pairwise CvLtA := e_content_sorted hp.wfe
  have hPs : (pays v).Pairwise CvLtA := hE's.sublist (pays_sublist h hp.vok)
  obtain ⟨h', hroot, hrok', heok', hB', hpv', hpin'⟩ :=
    settle_root_own hcf (Or.inr hp.vok) hp.eok (e_hB hp hPs) hset
  obtain ⟨_, _, hUi', _, _⟩ := settle_own f g space h v v' (fun _ => []) (Ui s v) hp.eok
    (by
      have : (pays v).flatMap (fun _ => ([] : List NodeId)) = [] :=
        List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
      rw [this, List.append_nil]) hset
  have hUiv : ∀ z ∈ Ui s v', z ∈ Ui s v := fun z hz => hUi'.subset (List.mem_append_left _ hz)
  have hUiR : ∀ z ∈ Ui s v, z ∈ Ro s root := fun z hz => hp.own.subset (List.mem_append_left _ hz)
  have hvok' : VOk cf s g h' v' := settle_vok hcf hp.vok hset hrok'
  have hkeys' : content h' (fin s h' v') = content h (absV s h v) := Root.keys hroot
  have hwfe' : WFE h' 0 none (fin s h' v') := Root.wf hroot 0 hp.wfe
  have hBnd := e_B_nodup ho hfresh (acc1.next - acc0.next)
  have hUnd : (Ui s v').Nodup :=
    e_subperm_nodup ((List.sublist_append_left _ _).subperm.trans hB') hBnd
  have hfresh1 : ∀ x, acc1.next ≤ x → s.obj x = none := fun x hx => hfresh x (le_trans h01 hx)
  obtain ⟨We, hwse, hnexte, hnde, hidse, htimese, hframee, hshe, hforme, hTe⟩ :=
    emit_spec_w hcf hvok' heok' hs hfresh1 hUnd (wfe_inord hwfe') he
  obtain ⟨_, hwsub⟩ := e_walks ho hnd
  obtain ⟨Wr, hWr, hWrun, hWmem⟩ := e_runs_W hfresh ho hp
  have hEex : ∀ e ∈ E, ∀ z ∈ R s e.2, z ∈ Ro s root := fun e he z hz =>
    ho.walks.subset (List.mem_flatMap.mpr ⟨e, he, hz⟩)
  have hEnd : (E.flatMap (fun e => R s e.2)).Nodup := e_subperm_nodup ho.walks ho.nodup
  -- emit writes no node of an old entry's walk
  have hWe_old : ∀ p ∈ We, ∀ e ∈ E, p.1 ∉ R s e.2 := by
    intro p hpW e he hz
    have hex := ho.exist _ (hEex e he _ hz)
    obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.mp hex
    obtain ⟨n, h'', rfl, hsh⟩ := hshe p hpW o ho'
    obtain ⟨n', hn', hlev, _⟩ := shaped_obj hsh
    rw [ho'] at hn'
    obtain rfl : n = n' := by simpa using hn'
    have hb := ho.below e he _ hz n ho'
    have hle : cf.lev g 0 ≤ cf.lev g h'' := by
      unfold Cfg.lev; exact Nat.add_le_add_left (Nat.zero_le h'') _
    omega
  -- a run writes no node of an untouched old entry's walk
  have hWr_old : ∀ p ∈ Wr, ∀ e ∈ E, e.1 ∉ touched g ops → p.1 ∉ R s e.2 := by
    intro p hpW e he hc hz
    have hex := ho.exist _ (hEex e he _ hz)
    rcases hWr.ids p.1 (List.mem_map_of_mem hpW) with ⟨hlo, _⟩ | hU
    · exact hex (hfresh _ hlo)
    · obtain ⟨r, hr, hzr⟩ := List.mem_flatMap.mp hU
      cases hl : E.lookup r.c with
      | none => rw [hl] at hzr; simp [Ro] at hzr
      | some y0 =>
        rw [hl] at hzr
        have hrc : r.c ∈ touched g ops := hp.perm.subset (List.mem_map_of_mem hr)
        refine e_disj' hEnd (lookup_mem hl) he ?_ hzr hz
        rintro rfl
        exact hc hrc
  -- the runs' writes on no node of Ui s v'
  have hWr_Ui : ∀ z ∈ Ui s v', z ∉ Wr.map (·.1) := by
    intro z hz h1
    rcases hWr.ids z h1 with ⟨hlo, _⟩ | hU
    · exact ho.exist z (hUiR z (hUiv z hz)) (hfresh z hlo)
    · obtain ⟨r, hr, hzr⟩ := List.mem_flatMap.mp hU
      cases hl : E.lookup r.c with
      | none => rw [hl] at hzr; simp [Ro] at hzr
      | some y0 => rw [hl] at hzr; exact hp.outUi r hr y0 hl z hzr (hUiv z hz)
  have hWall : WOkV i s (Ro s root) acc0 acc2 (We ++ Wr) := {
    ws := by rw [hwse, hWr.ws, List.append_assoc]
    next := le_trans h01 hnexte
    nodup := by
      rw [List.map_append, List.nodup_append]
      refine ⟨hnde, hWr.nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      rcases hidse a ha with ⟨hlo, hhi⟩ | hUa
      · rcases hWr.ids a hb with ⟨hlo', hhi'⟩ | hUb
        · nomega
        · exact ho.exist a (hwsub a hUb) (hfresh a (le_trans h01 hlo))
      · exact hWr_Ui a hUa hb
    ids := by
      intro w hw
      rw [List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · rcases hidse w hw with ⟨hlo, hhi⟩ | hU
        · exact Or.inl ⟨by nomega, hhi⟩
        · exact Or.inr (hUiR w (hUiv w hU))
      · rcases hWr.ids w hw with ⟨hlo, hhi⟩ | hU
        · exact Or.inl ⟨hlo, by nomega⟩
        · exact Or.inr (hwsub w hU)
    times := by
      intro p hp' n hpn
      rcases List.mem_append.mp hp' with hpe | hpr
      · obtain ⟨n', hn', ht⟩ := htimese p hpe
        rw [hpn] at hn'
        obtain rfl : n = n' := by simpa using hn'
        exact ht
      · exact hWr.times p hpr n hpn
    frame := by
      intro p hp' n hpn
      rcases List.mem_append.mp hp' with hpe | hpr
      · exact hframee p hpe n hpn
      · exact hWr.frame p hpr n hpn
    form := by
      intro p hp'
      rcases List.mem_append.mp hp' with hpe | hpr
      · exact hforme p hpe
      · exact hWr.form p hpr }
  refine ⟨We ++ Wr, hWall, ?_⟩
  intro T hT
  -- each run's writes: the only ones on its old nodes
  have hAfter : ∀ r ∈ runs, ∀ Wr' : List (NodeId × Obj), (∀ p ∈ Wr', p ∈ Wr) →
      (∀ p ∈ Wr, p.1 ∈ Ro s (E.lookup r.c) → p ∈ Wr') → After s T Wr' (Ro s (E.lookup r.c)) := by
    intro r hr Wr' hsub hown
    refine e_after_sub hT (fun p hp' => List.mem_append_right _ (hsub p hp'))
      (fun z hz => hwsub z (List.mem_flatMap.mpr ⟨r, hr, hz⟩)) ?_
    intro p hpW hpz
    rcases List.mem_append.mp hpW with hpe | hpr
    · exfalso
      cases hl : E.lookup r.c with
      | none => rw [hl] at hpz; simp [Ro] at hpz
      | some y0 => rw [hl] at hpz; exact hWe_old p hpe (r.c, y0) (lookup_mem hl) hpz
    · exact hown p hpr hpz
  have hrunT : ∀ r ∈ runs, ∃ Wr' : List (NodeId × Obj),
      e_runW cf s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r Wr' ∧
        After s T Wr' (Ro s (E.lookup r.c)) := by
    intro r hr
    obtain ⟨Wr', _, hS, hsub, hown⟩ := hWrun r hr
    exact ⟨Wr', hS, hAfter r hr Wr' hsub hown⟩
  -- an untouched old entry's walk is as in s
  have hunt : ∀ e ∈ E, e.1 ∉ touched g ops → ∀ z ∈ R s e.2, T.obj z = s.obj z := by
    intro e he hc z hz
    refine hT.keep z (hEex e he z hz) ?_
    intro hzW
    obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp hzW
    rcases List.mem_append.mp hpW with hpe | hpr
    · exact hWe_old p hpe e he hz
    · exact hWr_old p hpr e he hc hz
  -- the planned leaf level's payloads in T
  have hpayT : ∀ q ∈ content h (absV s h v), PayGood cf T g q.1 q.2 ∧
      (isLong q.1 = true → Shaped cf T (g + 1) (htIn cf T q.2) q.2 ∧ NOk cf.params T q.2) := by
    intro q hq
    have hlq : (content h (absV s h v)).lookup q.1 = some q.2 := Contract.PE.lookup_of_mem hE's hq
    by_cases hc : q.1 ∈ touched g ops
    · obtain ⟨r, hr, hrc⟩ := e_run_of_touched hp hc
      obtain ⟨Wr', hS, hA⟩ := hrunT r hr
      have hres : r.res = some q.2 := by rw [← e_run_res hp hr, hrc, hlq]
      obtain ⟨_, _, hy, _⟩ := hS.2 T hA
      obtain ⟨_, hpg, hlong, _⟩ := hy q.2 hres
      rw [hrc] at hpg hlong
      exact ⟨hpg, hlong⟩
    · have hqE : q ∈ E := by
        have := e_out_res hp hc
        rw [hlq] at this
        exact lookup_mem this.symm
      have hag := hunt q hqE hc
      obtain ⟨hpg, hsh⟩ := ho.pay q hqE
      have hht : htIn cf T q.2 = htIn cf s q.2 := by
        unfold htIn; rw [hag q.2 (mem_reachAt_self' s _ q.2)]
      exact ⟨payGood_transfer hpg hag, fun hl => ⟨hht ▸ shaped_transfer (hsh hl) hag,
        nok_transfer (fun x n hx => (hs x n hx).1) hT.exist hag⟩⟩
  have hpayFilled : ∀ q ∈ content h (absV s h v), isLong q.1 = true → Filled cf T true q.2 := by
    intro q hq hlong
    have hlq : (content h (absV s h v)).lookup q.1 = some q.2 := Contract.PE.lookup_of_mem hE's hq
    by_cases hc : q.1 ∈ touched g ops
    · obtain ⟨r, hr, hrc⟩ := e_run_of_touched hp hc
      obtain ⟨Wr', hWr', hS, hsub, hown⟩ := hWrun r hr
      have hA := hAfter r hr Wr' hsub hown
      have hres : r.res = some q.2 := by rw [← e_run_res hp hr, hrc, hlq]
      have hrlong : isLong r.c = true := by rwa [hrc]
      exact hfillRuns r hr hrlong (fun y hy =>
        hfillOld (r.c, y) (lookup_mem hy) hrlong) Wr' hWr' T hA q.2 hres
    · have hqE : q ∈ E := by
        have hh := e_out_res hp hc
        rw [hlq] at hh
        exact lookup_mem hh.symm
      obtain ⟨m, hm, hlev, hne, hgd⟩ := (ho.pay q hqE).1.2 hlong
      exact (hfillOld q hqE hlong).transfer hgd (hunt q hqE hc)
  -- emit's premise on the payloads
  have hPB : ∀ p ∈ pays v', T.obj p.2 ≠ none ∧ ∀ f, cf.lev g 0 ≤ f →
      (reachAt T f p.2).Subperm (oldPart s E p ++ e_RG runs p) := by
    intro p hp'
    have hq : p ∈ content h (absV s h v) := hkeys' ▸ hpin' p hp'
    have hlq := Contract.PE.lookup_of_mem hE's hq
    obtain ⟨c, y⟩ := p
    by_cases hc : c ∈ touched g ops
    · obtain ⟨r, hr, rfl⟩ := e_run_of_touched hp hc
      obtain ⟨Wr', hS, hA⟩ := hrunT r hr
      have hres : r.res = some y := by rw [← e_run_res hp hr]; exact hlq
      obtain ⟨_, _, hy, _⟩ := hS.2 T hA
      obtain ⟨hex, _, _, hreach⟩ := hy y hres
      refine ⟨hex, fun f hf => ?_⟩
      rw [e_oldPart, e_RG_run hnd hr]
      exact hreach f hf
    · have hpv : (c, y) ∈ pays v := hpv' _ hp'
      have hlE : E.lookup c = some y := hp.untouched _ hpv hc
      have hpE : (c, y) ∈ E := lookup_mem hlE
      have hag := hunt _ hpE hc
      have hsex : s.obj y ≠ none := ho.exist _ (hEex _ hpE y (mem_reachAt_self' s _ y))
      refine ⟨hT.exist _ hsex, fun f hf => ?_⟩
      have hop : oldPart s E (c, y) = R s y := by rw [e_oldPart]; simp only [hlE]; rfl
      rw [hop]
      refine List.Subperm.trans ?_ (List.sublist_append_left _ _).subperm
      cases hl : isLong c with
      | true =>
        obtain ⟨m, hm, hlev, _, hgd⟩ := (ho.pay _ hpE).1.2 hl
        rw [payload_old hgd hag f (by simp only [Tree.fuel, hm]; omega)]
      | false =>
        obtain ⟨w, hw⟩ := (ho.pay _ hpE).1.1 hl
        have hTw : T.obj y = some (.val w) := by rw [hag y (mem_reachAt_self' s _ y), hw]
        exact (payload_val hTw f).trans (List.singleton_subperm_iff.mpr (mem_reachAt_self' s _ y))
  have hkeep : ∀ z ∈ Ui s v', z ∉ We.map (·.1) → T.obj z = s.obj z := by
    intro z hz hzn
    refine hT.keep z (hUiR z (hUiv z hz)) ?_
    intro hzW
    rw [List.map_append, List.mem_append] at hzW
    rcases hzW with h1 | h1
    · exact hzn h1
    · exact hWr_Ui z hz h1
  obtain ⟨hcv, hholds, _, hreach, hnokW⟩ := hTe T (fun p => oldPart s E p ++ e_RG runs p)
    (fun p hp' => hT.ws p (List.mem_append_left _ hp')) hkeep hT.exist hPB
  -- the one entry emit gives
  have hfe : finEnts 0 v' (fin s h' v') = [(0, fin s h' v')] := by
    apply finEnts_single
    have := congrArg List.length hcv
    simpa [renameHead] using this.symm
  have hHo : Holds cf T g h' r' (fin s h' v') := by
    rw [hfe] at hholds
    exact hholds ((c0, r'), (0, fin s h' v')) (by simp)
  have hnf : NodeFill cf h' true (fin s h' v') := by
    rw [hjava]
    exact settleRoot_nodeFill_at hb
      (by simpa only [hjava] using hfillPlan)
      (by simpa only [hjava] using hset)
      (by simpa only [hjava] using hvok')
  exact filled_of_holds h' hHo hnf (fun q hq hl => hpayFilled q (hkeys' ▸ hq) hl)

end Contract.PE
