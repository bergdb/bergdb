/-
Proofs about the physical layer, part 17: the writer after a lazy startup, CC
and T2-L (bergdb item 001, WP L4).
-/
import SIS.Proof.PhysFrozen

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem step_eq_stepWith' (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr =
      stepWith sp al db tr (sp.exec tr db.S.length (view sp db.P (db.S.length - 1))) := rfl

/-- A read list of P's reachable nodes, each with its node at t, looked up: P@t. -/
theorem lookup_reach_view {sp : Spec V T} (P : Struct V) (t : Time) (x : NodeId) :
    ((reachList sp P t).map (fun z => (z, nodeAt P z t))).lookup x = view sp P t x := by
  by_cases hx : x ∈ reachList sp P t
  · rw [view_of_mem_reachList hx]
    have key : ∀ (L : List NodeId), x ∈ L → (L.map (fun z => (z, nodeAt P z t))).lookup x =
        some (nodeAt P x t) := by
      intro L hL
      induction L with
      | nil => cases hL
      | cons z L ih =>
        rw [List.map_cons, lookup_cons_eq]
        by_cases hz : x = z
        · subst hz; simp
        · simp only [hz, ↓reduceIte]
          exact ih (by rcases List.mem_cons.mp hL with h | h; exact absurd h hz; exact h)
    exact key _ hx
  · have hr : reachable sp P t x = false := by
      simp only [reachable]
      simpa using hx
    simp only [view, hr, Bool.false_eq_true, ↓reduceIte]
    have key : ∀ (L : List NodeId), x ∉ L → (L.map (fun z => (z, nodeAt P z t))).lookup x = none := by
      intro L hL
      induction L with
      | nil => rfl
      | cons z L ih =>
        rw [List.map_cons, lookup_cons_eq]
        have hz : x ≠ z := fun h => hL (h ▸ List.mem_cons_self)
        simp only [hz, ↓reduceIte]
        exact ih (fun h => hL (List.mem_cons_of_mem z h))
    exact key _ hx

section Agree

variable {sp : Spec V T} {al : Algo V T} {ts : List T} {k1 : Nat}

local notation "fz" => st sp (frozenAlgo al k1) ts

/-- After k1, the frozen run's stream says the same as the stream at k1 about
the nodes that existed at k1, with the same startup pos. -/
theorem frozen_agree (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hk1 : k1 ≤ ts.length) :
    ∀ j, k1 ≤ j → j ≤ ts.length →
      lastSp (fz j).S = lastSp (st sp al ts k1).S ∧
      ∀ y, ((st sp al ts k1).P.get? y).isSome →
        (∀ r, (fz j).S.versionAt r y = (st sp al ts k1).S.versionAt r y) ∧
        newest (fz j).S (lastSp (st sp al ts k1).S) y =
          newest (st sp al ts k1).S (lastSp (st sp al ts k1).S) y := by
  intro j
  induction j with
  | zero =>
    intro hk _
    have : k1 = 0 := by omega
    subst this
    rw [frozen_st_le 0 0 (Nat.le_refl _) (by omega)]
    exact ⟨rfl, fun y _ => ⟨fun _ => rfl, rfl⟩⟩
  | succ j ih =>
    intro hk hjt
    rcases Nat.lt_or_ge j k1 with hlt | hge
    · have : k1 = j + 1 := by omega
      subst this
      rw [frozen_st_le (j + 1) (j + 1) (Nat.le_refl _) hjt]
      exact ⟨rfl, fun y _ => ⟨fun _ => rfl, rfl⟩⟩
    · obtain ⟨h1, h2⟩ := ih hge (by omega)
      have hg := frozen_grow (k1 := k1) hok hj hge (by omega)
      refine ⟨by rw [hg.lastSpEq, h1], fun y hy => ?_⟩
      -- y is a node of the frozen state at j.
      have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
      have hyj : ((fz j).P.get? y).isSome := by
        rw [(frozen_P (sp := sp) (al := al) (ts := ts) k1 j (by omega)).1]
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hy
        obtain ⟨n', hn', -⟩ := st_grow sp al ts hok hst hge (by omega) y n hn
        simp [hn']
      obtain ⟨o1, o2, -⟩ := hg.old y hyj
      obtain ⟨g1, g2⟩ := h2 y hy
      refine ⟨fun r => by rw [o1 r, g1 r], ?_⟩
      rw [← h1, o2, h1, g2]

/-- The memory after a lazy startup at k1 reads the same from the stream at k1
as from the frozen run's stream at j, if the nodes created after k1 have
canonical objects. -/
theorem frozen_streamAgree (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {j : Nat} (hkj : k1 ≤ j) (hjt : j ≤ ts.length) {m : Mem V}
    (hms : m.s = lastSp (st sp al ts k1).S)
    (hnew : ∀ y, (st sp al ts k1).P.get? y = none → ((st sp al ts j).P.get? y).isSome →
      m.canonicalOf y ≠ none) :
    StreamAgree m (st sp al ts k1).S (fz j).S := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hok' := frozen_runOK (sp := sp) k1 hok
  have hst' : AlgOK sp (frozenAlgo al k1) := algOK_of sp _ (Or.inl hj)
  have hinvj := inv_st sp _ ts hok' hst' j hjt
  have hinvk := inv_st sp al ts hok hst k1 (by omega)
  have hPj := (frozen_P (sp := sp) (al := al) (ts := ts) k1 j hjt).1
  intro y hy
  rw [hms]
  cases hyk : (st sp al ts k1).P.get? y with
  | some n =>
    obtain ⟨-, h2⟩ := frozen_agree hok hj (by omega) j hkj hjt
    obtain ⟨g1, g2⟩ := h2 y (by simp [hyk])
    exact ⟨g2.symm, fun r => (g1 r).symm⟩
  | none =>
    -- y does not exist at j: no version anywhere.
    have hyj : (st sp al ts j).P.get? y = none := by
      cases h : (st sp al ts j).P.get? y with
      | none => rfl
      | some _ => exact absurd (hnew y hyk (by simp [h])) (by simp [hy])
    have hnone1 : ∀ r, (st sp al ts k1).S.versionAt r y = none := by
      intro r
      cases hv : (st sp al ts k1).S.versionAt r y with
      | none => rfl
      | some w =>
        obtain ⟨-, -, n, hn, -⟩ := hinvk.version_node hv
        rw [hyk] at hn; cases hn
    have hnone2 : ∀ r, (fz j).S.versionAt r y = none := by
      intro r
      cases hv : (fz j).S.versionAt r y with
      | none => rfl
      | some w =>
        obtain ⟨-, -, n, hn, -⟩ := hinvj.version_node hv
        rw [hPj, hyj] at hn; cases hn
    refine ⟨?_, fun r => by rw [hnone1 r, hnone2 r]⟩
    rw [(newest_eq_none_iff _ _ _).mpr (fun r _ => hnone1 r),
      (newest_eq_none_iff _ _ _).mpr (fun r _ => hnone2 r)]

end Agree

section Lazy

variable {sp : Spec V T} {al : Algo V T}

/-- What holds after the first j transactions of a run with lazy restarts, with
the last restart (or the start) after k1 transactions: the stream of the last
startup is the run's after k1; ⟨P, D, S⟩ is the run's after j; the memory meets
the invariant at j for the frozen run from k1; and the nodes created after k1
have canonical objects. -/
def LazyInv (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) (j : Nat)
    (r : DB V T × Mem V × Stream V T) : Prop :=
  ∃ k1, k1 ≤ j ∧ r.2.2 = (st sp al (ts.map (·.1)) k1).S ∧ Rel r.1 (st sp al (ts.map (·.1)) j) ∧
    MemInv sp (st sp (frozenAlgo al k1) (ts.map (·.1)) j) j r.2.1 ∧
    ∀ y, (st sp al (ts.map (·.1)) k1).P.get? y = none →
      ((st sp al (ts.map (·.1)) j).P.get? y).isSome → r.2.1.canonicalOf y ≠ none

theorem runLazy_succ (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) {j : Nat}
    (hj : j < ts.length) :
    runLazy sp al (ts.take (j + 1)) =
      (if ts[j].2 then
        (startup sp (lazyTrans sp al (runLazy sp al (ts.take j)).2.2 (runLazy sp al (ts.take j)).1
            (runLazy sp al (ts.take j)).2.1 ts[j].1).1.S,
          lazyStartup sp (lazyTrans sp al (runLazy sp al (ts.take j)).2.2 (runLazy sp al (ts.take j)).1
            (runLazy sp al (ts.take j)).2.1 ts[j].1).1.S,
          (lazyTrans sp al (runLazy sp al (ts.take j)).2.2 (runLazy sp al (ts.take j)).1
            (runLazy sp al (ts.take j)).2.1 ts[j].1).1.S)
      else
        ((lazyTrans sp al (runLazy sp al (ts.take j)).2.2 (runLazy sp al (ts.take j)).1
            (runLazy sp al (ts.take j)).2.1 ts[j].1).1,
          (lazyTrans sp al (runLazy sp al (ts.take j)).2.2 (runLazy sp al (ts.take j)).1
            (runLazy sp al (ts.take j)).2.1 ts[j].1).2,
          (runLazy sp al (ts.take j)).2.2)) := by
  have h1 : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runLazy
  rw [h1, List.foldl_append]
  rfl

/-- One transaction of a run with lazy restarts keeps `LazyInv`. -/
theorem lazyInv_step {ts : List (T × Bool)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) {j : Nat}
    (hjt : j < ts.length) {acc : DB V T × Mem V × Stream V T} (hI : LazyInv sp al ts j acc) :
    LazyInv sp al ts (j + 1)
      (if ts[j].2 then
        (startup sp (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          lazyStartup sp (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2, acc.2.2)) := by
  obtain ⟨k1, hk1, hS0, hrel, hm, hnew⟩ := hI
  unfold LazyInv
  generalize hts1 : ts.map (·.1) = ts1 at hok hph hS0 hrel hm hnew ⊢
  have hlen1 : ts1.length = ts.length := by rw [← hts1]; simp
  have hjt1 : j < ts1.length := by omega
  have htr : ts1[j] = ts[j].1 := by subst hts1; simp
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  -- The frozen run from k1.
  have hok' := frozen_runOK (sp := sp) k1 hok
  have hph' := frozen_physRunOK (sp := sp) k1 hph
  have hj' : (frozenAlgo al k1).stillDirty = javaTest sp := hj
  have hst' : AlgOK sp (frozenAlgo al k1) := algOK_of sp _ (Or.inl hj')
  have hPj := (frozen_P (sp := sp) (al := al) (ts := ts1) k1 j (by omega)).1
  have hPj1 := (frozen_P (sp := sp) (al := al) (ts := ts1) k1 (j + 1) (by omega)).1
  have hctxj := pctx_st hok' hst' (k := j) (by omega)
  have hkj := kctx_st sp _ ts1 hok' hj' (Nat.le_refl j) (by omega)
  have hlenj := st_len sp al ts1 hok hst (j := j) (by omega)
  obtain ⟨hrS, hrD, hrP⟩ := hrel
  have hdblen : acc.1.S.length = j + 1 := by rw [hrS, hlenj]
  have hPs : SameNodes acc.1.P (st sp (frozenAlgo al k1) ts1 j).P := by
    rw [hPj]; exact hrP
  -- The startup pos of the memory.
  have hms : acc.2.1.s = lastSp (st sp al ts1 k1).S := by
    rw [hm.sEq, (frozen_agree hok hj (by omega) j hk1 (by omega)).1]
  -- 1. The writer's view, read through the physical layer, is P@j.
  have hag := frozen_streamAgree hok hj hk1 (by omega) hms hnew
  rw [← hS0] at hag
  obtain ⟨hm1, hle1, hl1⟩ := hm.read_ok hctxj hkj.fixedLe (Nat.le_refl j) hag
  have hview : (acc.2.1.view sp acc.2.2 j).2 = view sp acc.1.P j := by
    funext x
    show ((acc.2.1.read sp acc.2.2 j).2).lookup x = _
    rw [hl1, lookup_reach_view, hPs.view]
  -- The change is the run's.
  have hc : sp.exec ts[j].1 (j + 1) (acc.2.1.view sp acc.2.2 j).2 =
      (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c := by
    rw [hview, parts_c, (inv_st sp _ ts1 hok' hst' j (by omega)).len, Nat.add_sub_cancel,
      hPs.view j, htr]
  -- The logical step is the run's step.
  have hlog : (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 = step sp al acc.1 ts[j].1 := by
    unfold lazyTrans
    simp only
    rw [hdblen, Nat.add_sub_cancel, hview, step_eq_stepWith', hdblen, Nat.add_sub_cancel]
  have hrel' : Rel (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al ts1 (j + 1)) := by
    rw [hlog, st_succ sp al ts1 hjt1, htr]
    exact step_congr sp al hst ⟨hrS, hrD, hrP⟩ _
  -- 2. The memory: the writer reaches the paths, then the change is applied.
  have hstepK : StepOK sp (st sp (frozenAlgo al k1) ts1 j).P (j + 1)
      (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c := by
    rw [parts_c, (inv_st sp _ ts1 hok' hst' j (by omega)).len, Nat.add_sub_cancel]
    exact hok'.2 j hjt1
  have hphK : PhysStep sp (st sp (frozenAlgo al k1) ts1 j).P (j + 1)
      (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c := by
    rw [parts_c, (inv_st sp _ ts1 hok' hst' j (by omega)).len, Nat.add_sub_cancel]
    exact hph' j hjt1
  generalize hcdef : (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c = c
    at hc hstepK hphK
  have hpath : ∀ p ∈ pathOf sp acc.1.P c (j + 1),
      reachable sp (st sp (frozenAlgo al k1) ts1 j).P j p = true := by
    intro p hp
    have := (mem_pathOf hp).1
    rw [Nat.add_sub_cancel, hPs.reachable] at this
    exact this
  have hparent : ∀ x ∈ pathOf sp acc.1.P c (j + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp acc.1.P c (j + 1), ∃ np nx, acc.1.P.get? p = some np ∧
        acc.1.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo j) := by
    intro x hx hxr
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent (mem_pathOf hx).1 hxr
    refine ⟨p, pathOf_parent hx hrp hnp hxl hnx hlt, np, nx, hnp, hnx, hlt, ?_⟩
    simpa using hxl
  have hag1 : StreamAgree (acc.2.1.read sp acc.2.2 j).1 acc.2.2
      (st sp (frozenAlgo al k1) ts1 j).S := hag.le hle1 (by rw [hm1.sEq, hm.sEq])
  obtain ⟨hm2, hle2, hcan2⟩ := MemInv.reachPath_ok hctxj hkj hPs hpath hparent
    ((pathOf sp acc.1.P c (j + 1)).mergeSort (fun a b => decide (lev acc.1.P b ≤ lev acc.1.P a))) []
    _ hm1 (by simp) (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact pairwise_byLevelDesc _ _)
  have hfold := MemInv.reachFold_congr hctxj hkj hPs hpath (S_f := acc.2.2)
    ((pathOf sp acc.1.P c (j + 1)).mergeSort (fun a b => decide (lev acc.1.P b ≤ lev acc.1.P a)))
    _ hm1 hag1
  -- The invariant moves to the frozen state after j + 1, still at j.
  have hm2' := hm2.transfer hctxj (frozen_grow (k1 := k1) hok hj hk1 hjt1)
  -- The change applied.
  have hkK := kctx_st sp _ ts1 hok' hj' (K := j) (k := j + 1) (by omega) (by omega)
  have hkJ : KCtx sp (st sp (frozenAlgo al k1) ts1 (j + 1))
      (step sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]) (j + 1) :=
    st_succ sp _ ts1 hjt1 ▸ kctx_st sp _ ts1 hok' hj' (K := j + 1) (k := j + 1) (Nat.le_refl _) (by omega)
  have hctxj1 := pctx_st hok' hst' (k := j + 1) (by omega)
  subst hcdef
  have hm3 := hm2'.applyChange_ok hctxj1 hkK hkJ hok.1 hj' hstepK hphK
    (fun x hx => hcan2 x (by rw [pathOf_congr hPs]; exact hx))
  have hmem : (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2 =
      (((pathOf sp acc.1.P (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c
          (j + 1)).mergeSort (fun a b => decide (lev acc.1.P b ≤ lev acc.1.P a))).foldl
        (Mem.reachOnPath sp (st sp (frozenAlgo al k1) ts1 j).S acc.1.P (j + 1)
          (pathOf sp acc.1.P (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c
            (j + 1))) (acc.2.1.read sp acc.2.2 j).1).applyChange sp
        (st sp (frozenAlgo al k1) ts1 j).P (j + 1)
        (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c := by
    rw [← hfold, ← applyChange_congr hPs, ← hc]
    unfold lazyTrans
    simp only
    rw [hdblen, Nat.add_sub_cancel]
    rfl
  -- The nodes created after k1 have canonical objects.
  have hnew' : ∀ y, (st sp al ts1 k1).P.get? y = none →
      ((st sp al ts1 (j + 1)).P.get? y).isSome →
      (lazyTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2.canonicalOf y ≠ none := by
    intro y hyk hyj1
    rw [hmem, applyChange_canonicalOf]
    cases hyj : (st sp al ts1 j).P.get? y with
    | some ny =>
      -- an old node: canonical before, and kept
      have h0 := hnew y hyk (by simp [hyj])
      have h1 := hle1.ne_none h0
      have h2 := hle2.ne_none h1
      have hyn : y ∉ (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c.new.map
          (·.id) := by
        intro hy
        obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
        have := hstepK.fresh nn hnn
        rw [hid, hPj, hyj] at this; cases this
      rw [addNew_canonicalOf_old _ _ hm2.fresh (fun y h ht => by
        obtain ⟨o, ho, -⟩ := hm2.tbl y h ht; simp [ho]) hyn]
      exact h2
    | none =>
      -- a new node of the transaction
      rw [st_P_succ sp al ts1 hok hst hjt1, get?_apply, hyj, Option.none_or] at hyj1
      cases hnn : newNodeOf (sp.exec ts1[j] (j + 1) (view sp (st sp al ts1 j).P j)) y with
      | none => rw [hnn] at hyj1; cases hyj1
      | some n0 =>
        obtain ⟨nn, hnnm, hid, -⟩ := newNodeOf_some hnn
        have hceq : (parts sp (frozenAlgo al k1) (st sp (frozenAlgo al k1) ts1 j) ts1[j]).c =
            sp.exec ts1[j] (j + 1) (view sp (st sp al ts1 j).P j) := by
          rw [parts_c, (inv_st sp _ ts1 hok' hst' j (by omega)).len, Nat.add_sub_cancel, hPj]
        rw [← hceq] at hnnm
        obtain ⟨h, -, hch, -⟩ := addNew_canonicalOf_new (V := V) _ _ hstepK.distinct hnnm
        rw [← hid, hch]
        simp
  -- 3. A restart, or not.
  split
  · -- A restart after j + 1: the lazy startup from the stream.
    refine ⟨j + 1, Nat.le_refl _, by simp only; rw [hrel'.1], ?_, ?_, ?_⟩
    · simp only
      rw [hrel'.1]
      have hT1 := T1_strong sp al ts1 hok hst (k := j + 1) (by omega)
      exact ⟨rfl, hT1.2, hT1.1⟩
    · simp only
      rw [hrel'.1, frozen_st_le (j + 1) (j + 1) (Nat.le_refl _) (by omega)]
      exact lazy_ok hok hph hj (by omega)
    · intro y hy1 hy2
      rw [hy1] at hy2; cases hy2
  · -- No restart: the same startup.
    refine ⟨k1, by omega, hS0, hrel', ?_, hnew'⟩
    simp only
    rw [hmem]
    exact hm3

end Lazy

section LazyRun

variable {sp : Spec V T} {al : Algo V T}

/-- `LazyInv` holds after every prefix of a run with lazy restarts. -/
theorem lazyInv_all {ts : List (T × Bool)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) :
    ∀ j ≤ ts.length, LazyInv sp al ts j (runLazy sp al (ts.take j)) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runLazy sp al (ts.take 0) = (init sp, lazyStartup sp (init sp).S, (init sp).S) := by
      simp [runLazy]
    rw [h0]
    refine ⟨0, Nat.le_refl _, by rw [st_zero], by rw [st_zero]; exact ⟨rfl, rfl, SameNodes.refl _⟩,
      ?_, ?_⟩
    · have := lazy_ok hok hph hj (k := 0) (by omega)
      rw [frozen_st_le 0 0 (Nat.le_refl _) (by omega)]
      rw [st_zero] at this ⊢
      exact this
    · intro y hy1 hy2
      rw [hy1] at hy2; cases hy2
  | succ j ih =>
    intro hjt
    rw [runLazy_succ sp al ts (by omega)]
    exact lazyInv_step hok hph hj (by omega) (ih (by omega))

/-- T2-L, strong form: after every prefix of a run with lazy restarts, ⟨P, D, S⟩
is the run's, and every canonical object holds its node's whole history. -/
theorem T2_lazy_strong {ts : List (T × Bool)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) {j : Nat}
    (hjt : j ≤ ts.length) :
    Rel (runLazy sp al (ts.take j)).1 (st sp al (ts.map (·.1)) j) ∧
      ∀ h o, (runLazy sp al (ts.take j)).2.1.obj? h = some o → o.canonical = true →
        ((st sp al (ts.map (·.1)) j).P.get? o.node).map (·.hist) = some o.hist := by
  obtain ⟨k1, hk1, -, hrel, hm, -⟩ := lazyInv_all hok hph hj j hjt
  refine ⟨hrel, fun h o ho hc => ?_⟩
  have hok' := frozen_runOK (sp := sp) k1 hok
  have hst' : AlgOK sp (frozenAlgo al k1) := algOK_of sp _ (Or.inl hj)
  have hinv := inv_st sp _ _ hok' hst' j (by simp; omega)
  obtain ⟨-, ⟨n, hn, hh, -, -⟩, -⟩ := hm.canon h o ho hc
  rw [← (frozen_P (sp := sp) (al := al) (ts := ts.map (·.1)) k1 j (by simp; omega)).1, hn, hh,
    upTo_of_forall _ _ (hinv.times o.node n hn)]
  rfl

end LazyRun

end SIS
