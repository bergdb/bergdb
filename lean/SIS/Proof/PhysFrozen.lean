/-
Proofs about the physical layer, part 16: the frozen run (bergdb item 001, WP
L4). After a lazy startup at k1, the writer's memory is, transaction after
transaction, the memory of a lazy startup of another run: the same
transactions, with the startup pos frozen from k1 on. That run takes no node
after k1 and writes only the versions of new data nodes, so its stream adds
nothing that the memory reads.
-/
import SIS.Proof.PhysT1

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The algorithm al with its startup pos frozen after T(k1): from T(k1 + 1) on,
the policy keeps the last startup pos. -/
def frozenAlgo (al : Algo V T) (k1 : Nat) : Algo V T :=
  { al with policy := fun S D i tr => if i ≤ k1 then al.policy S D i tr else lastSp S }

section Frozen

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A step whose startup pos is the same is the same step. -/
theorem frozen_policy (al : Algo V T) (k1 : Nat) (S : Stream V T) (D : Dirty) (i : Time) (tr : T) :
    (frozenAlgo al k1).policy S D i tr = if i ≤ k1 then al.policy S D i tr else lastSp S := rfl

theorem step_frozen_of_s (al : Algo V T) (k1 : Nat) (db : DB V T) (tr : T)
    (hs : (parts sp (frozenAlgo al k1) db tr).s = (parts sp al db tr).s) :
    step sp (frozenAlgo al k1) db tr = step sp al db tr := by
  have htaken : (parts sp (frozenAlgo al k1) db tr).taken = (parts sp al db tr).taken := by
    rw [parts_taken, parts_taken, hs]; rfl
  have hD2 : (parts sp (frozenAlgo al k1) db tr).D2 = (parts sp al db tr).D2 := by
    rw [parts_D2, parts_D2, hs]; rfl
  have hvs : (parts sp (frozenAlgo al k1) db tr).vs = (parts sp al db tr).vs := by
    rw [parts_vs, parts_vs, htaken]; rfl
  have hS' : (parts sp (frozenAlgo al k1) db tr).S' = (parts sp al db tr).S' := by
    rw [parts_S', parts_S', hvs]
  have hr7 : (parts sp (frozenAlgo al k1) db tr).r7 = (parts sp al db tr).r7 := by
    rw [parts_r7, parts_r7, hS', hD2, htaken]; rfl
  have hfa : (parts sp (frozenAlgo al k1) db tr).fa = (parts sp al db tr).fa := by
    rw [parts_fa, parts_fa, hs]; rfl
  have hR : (parts sp (frozenAlgo al k1) db tr).R = (parts sp al db tr).R := by
    rw [parts_R, parts_R, hs, hvs, hr7, hS', hfa]; rfl
  rw [step_eq_parts, step_eq_parts, hr7, hR]
  rfl

theorem step_frozen_le (al : Algo V T) (k1 : Nat) (db : DB V T) (tr : T) (hi : db.S.length ≤ k1) :
    step sp (frozenAlgo al k1) db tr = step sp al db tr := by
  apply step_frozen_of_s
  rw [parts_s, parts_s]
  have hD1 : (parts sp (frozenAlgo al k1) db tr).D1 = (parts sp al db tr).D1 := rfl
  rw [hD1]
  simp only [startupPos, frozenAlgo, hi, ↓reduceIte]

theorem step_S_length (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (step sp al db tr).S.length = db.S.length + 1 := by
  rw [step_eq_parts]; simp

theorem step_P_eq (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (step sp al db tr).P =
      db.P.apply db.S.length (sp.exec tr db.S.length (view sp db.P (db.S.length - 1))) := rfl

/-- Before k1, the frozen run is the run. -/
theorem frozen_st_le (k1 : Nat) : ∀ j, j ≤ k1 → j ≤ ts.length →
    st sp (frozenAlgo al k1) ts j = st sp al ts j := by
  intro j
  induction j with
  | zero => intro _ _; rw [st_zero, st_zero]
  | succ j ih =>
    intro hj hjt
    rw [st_succ sp _ ts (by omega), st_succ sp _ ts (by omega), ih (by omega) (by omega)]
    apply step_frozen_le
    have : (st sp al ts j).S.length = j + 1 := by
      clear ih
      induction j with
      | zero => rw [st_zero]; rfl
      | succ j ih2 =>
        rw [st_succ sp _ ts (by omega), step_S_length, ih2 (by omega) (by omega)]
    omega

/-- The frozen run has the run's structures and stream lengths. -/
theorem frozen_P (k1 : Nat) : ∀ j, j ≤ ts.length →
    (st sp (frozenAlgo al k1) ts j).P = (st sp al ts j).P ∧
      (st sp (frozenAlgo al k1) ts j).S.length = (st sp al ts j).S.length := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero, st_zero]; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hjt
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [st_succ sp _ ts (by omega), st_succ sp _ ts (by omega), step_P_eq, step_P_eq,
      step_S_length, step_S_length, h1, h2]
    exact ⟨rfl, rfl⟩

theorem frozen_runOK (k1 : Nat) (hok : RunOK sp al ts) : RunOK sp (frozenAlgo al k1) ts := by
  refine ⟨hok.1, fun j hj => ?_⟩
  have := hok.2 j hj
  have hP := (frozen_P (sp := sp) (al := al) (ts := ts) k1 j (by omega)).1
  simp only [st] at hP
  simp only
  rw [hP]
  exact this

theorem frozen_physRunOK (k1 : Nat) (hph : PhysRunOK sp al ts) :
    PhysRunOK sp (frozenAlgo al k1) ts := by
  intro j hj
  have := hph j hj
  have hP := (frozen_P (sp := sp) (al := al) (ts := ts) k1 j (by omega)).1
  simp only [st] at hP
  simp only
  rw [hP]
  exact this

end Frozen

/-! ### The invariant for a final state that only grows (the frozen run's next state) -/

/-- db' extends db at time K without changing what the memory sees of the nodes
of db: the same startup pos; the same nodes up to K; the same records up to K;
for each node of db, the same versions, newest version and latest version; and
a new node's versions are of data nodes and its entries after K. -/
structure DbGrow (sp : Spec V T) (db db' : DB V T) (K : Nat) : Prop where
  lastSpEq : lastSp db'.S = lastSp db.S
  grow : Grow db.P K db'.P
  ext : SExt db.S db'.S
  recEq : ∀ d, d ≤ K → db'.S[d]? = db.S[d]?
  old : ∀ y, (db.P.get? y).isSome → (∀ r, db'.S.versionAt r y = db.S.versionAt r y) ∧
    newest db'.S (lastSp db.S) y = newest db.S (lastSp db.S) y ∧ db'.S.lv y = db.S.lv y
  newData : ∀ y, db.P.get? y = none → ∀ r w, db'.S.versionAt r y = some w → w.isData = true
  newLate : ∀ y, db.P.get? y = none → ∀ n, db'.P.get? y = some n → ∀ e ∈ n.hist, K < e.time
  reach : ∀ t ≤ K, ∀ y, reachable sp db'.P t y = reachable sp db.P t y

section Transfer

variable {sp : Spec V T} {db db' : DB V T} {K k : Nat} {m : Mem V}

theorem DbGrow.ruleR (hg : DbGrow sp db db' K) {y : NodeId} (hy : (db.P.get? y).isSome)
    (r : Option Nat) :
    ruleRRef db'.S (lastSp db'.S) y r = ruleRRef db.S (lastSp db.S) y r := by
  rw [hg.lastSpEq]; exact ruleRRef_congr (hg.old y hy).2.1 r

theorem DbGrow.histAt (hg : DbGrow sp db db' K) (y : NodeId) :
    histAt db'.P y K = histAt db.P y K := by
  unfold SIS.histAt
  cases hn : db.P.get? y with
  | some n =>
    obtain ⟨n', hn', -, -, hh⟩ := hg.grow y n hn
    rw [hn', Option.map_some, Option.map_some, Option.getD_some, Option.getD_some, hh]
  | none =>
    cases hn' : db'.P.get? y with
    | none => rfl
    | some n' =>
      simp only [Option.map_some, Option.getD_some, Option.map_none, Option.getD_none]
      apply upTo_eq_nil
      intro e he
      exact hg.newLate y hn n' hn' e he

theorem SnapOK.transfer (hg : DbGrow sp db db' K) {h : Nat} {o : Obj V} {w : Version V}
    (hs : SnapOK db m K h o w) (ho : (db.P.get? o.node).isSome) : SnapOK db' m K h o w := by
  obtain ⟨r, hp, hv, hl, hd, h5⟩ := hs
  refine ⟨r, hp, by rw [(hg.old _ ho).1 r]; exact hv, hl, hd, ?_⟩
  rcases h5 with h6 | ⟨h6, h7, h8, h9⟩
  · exact Or.inl h6
  · exact Or.inr ⟨by rw [hg.lastSpEq]; exact h6, by rw [(hg.old _ ho).2.2]; exact h7, h8,
      by rw [hg.histAt]; exact h9⟩

theorem Readable.transfer (hg : DbGrow sp db db' K)
    (hobj : ∀ h o, m.obj? h = some o → (db.P.get? o.node).isSome) {t : Time} (ht : t ≤ K)
    {h : Nat} {y : NodeId} (hr : Readable sp db m K t h y) : Readable sp db' m K t h y := by
  obtain ⟨o, ho, hy, hc⟩ := hr
  refine ⟨o, ho, hy, ?_⟩
  rcases hc with hc | ⟨w, hw, hgw⟩
  · exact Or.inl hc
  · exact Or.inr ⟨w, hw.transfer hg (hobj h o ho),
      fun he => good_mono' sp hg.ext hg.grow ht (hgw he)⟩

theorem SlotGood.transfer (hg : DbGrow sp db db' K)
    (hobj : ∀ h o, m.obj? h = some o → (db.P.get? o.node).isSome) {t : Time} (ht : t ≤ K)
    {y : NodeId} (hy : (db.P.get? y).isSome) {sl : Slot} (hs : SlotGood sp db m K t y sl) :
    SlotGood sp db' m K t y sl := by
  cases sl with
  | mem h' => exact Readable.transfer hg hobj ht hs
  | stream r =>
    rcases hs with hc | ⟨r', w, h1, h2, h3⟩
    · exact Or.inl hc
    · exact Or.inr ⟨r', w, by rw [hg.ruleR hy]; exact h1, by rw [(hg.old y hy).1]; exact h2,
        good_mono' sp hg.ext hg.grow ht h3⟩

theorem SlotFresh.transfer (hg : DbGrow sp db db' K) {y : NodeId} (hy : (db.P.get? y).isSome)
    {sl : Slot} (hs : SlotFresh db m y sl) : SlotFresh db' m y sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho, hc⟩ := hs
    exact ⟨o, ho, by rw [(hg.old y hy).2.2]; exact hc⟩
  | stream r =>
    rcases hs with hc | ⟨n, r', w, h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · exact Or.inl hc
    · obtain ⟨n', hn', -, hd, -⟩ := hg.grow y n h1
      exact Or.inr (Or.inl ⟨n', r', w, hn', by rw [hd]; exact h2, by rw [hg.ruleR hy]; exact h3,
        by rw [(hg.old y hy).1]; exact h4⟩)
    · exact Or.inr (Or.inr ⟨by rw [hg.ruleR hy, (hg.old y hy).2.2]; exact h1,
        by rw [(hg.old y hy).2.2]; exact h2⟩)

theorem SnapSlots.transfer (hg : DbGrow sp db db' K)
    (hobj : ∀ h o, m.obj? h = some o → (db.P.get? o.node).isSome) {o : Obj V} {w : Version V}
    (hs : SnapSlots sp db m o w) : SnapSlots sp db' m o w := by
  refine ⟨hs.1, fun y sl hsl => ?_⟩
  rcases hs.2 y sl hsl with h1 | ⟨h', h1, hal⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h', h1, ?_⟩
    have hy : (db.P.get? y).isSome := by
      obtain ⟨o', ho', hy', -⟩ := hal
      rw [← hy']; exact hobj h' o' ho'
    rw [hg.ruleR hy]
    exact hal

/-- The invariant at K carries over to a final state that only grows. -/
theorem MemInv.transfer (hm : MemInv sp db K m) (hctx : PCtx sp db k) (hg : DbGrow sp db db' K) :
    MemInv sp db' K m := by
  have hls := hctx.ls
  -- Every object's node is a node of db.
  have hobj : ∀ h o, m.obj? h = some o → (db.P.get? o.node).isSome := by
    intro h o ho
    obtain ⟨t, -, hr⟩ := hm.born h o ho
    exact Reach.isSome ((reachable_iff _ _ _ _).mp hr)
  -- A live child at t of a node of db is a node of db.
  have hchild : ∀ (x : NodeId) (n : Node V) (t : Time), db.P.get? x = some n →
      ∀ y ∈ sp.live (n.hist.upTo t), (db.P.get? y).isSome := by
    intro x n t hn y hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨ny, hny, -⟩ := hctx.inv.ptrs x n hn e (mem_upTo.mp he).1 y hye
    simp [hny]
  refine ⟨by rw [hg.lastSpEq]; exact hm.sEq, by rw [hg.lastSpEq]; exact hm.sK, hm.fresh, hm.nodup, hm.root,
    hm.tbl, ?_, ?_, ?_, hm.memSlot, ?_, ?_, ?_⟩
  · intro h o ho
    obtain ⟨t, ht, hr⟩ := hm.born h o ho
    exact ⟨t, ht, by rw [hg.reach t ht]; exact hr⟩
  · intro h o ho hc
    obtain ⟨c1, ⟨n, hn, hh, hl, hd⟩, c3, c4, c5⟩ := hm.canon h o ho hc
    obtain ⟨n', hn', hl', hd', hh'⟩ := hg.grow o.node n hn
    refine ⟨c1, ⟨n', hn', by rw [hh, hh'], by rw [hl, hl'], by rw [hd, hd']⟩, ?_, ?_, ?_⟩
    · intro p hp
      rw [(hg.old _ (hobj h o ho)).1]
      exact c3 p hp
    · intro t ht hr y hy
      rw [hg.reach t ht] at hr
      obtain ⟨sl, hsl, hsg⟩ := c4 t ht hr y hy
      have hy' : y ∈ sp.live (n.hist.upTo t) := by rw [hh, upTo_upTo _ ht] at hy; exact hy
      exact ⟨sl, hsl, hsg.transfer hg hobj ht (hchild o.node n t hn y hy')⟩
    · intro hr y hy
      rw [hg.reach K (Nat.le_refl _)] at hr
      obtain ⟨sl, hsl, hsf⟩ := c5 hr y hy
      have hy' : y ∈ sp.live (n.hist.upTo K) := by rw [hh] at hy; exact hy
      exact ⟨sl, hsl, hsf.transfer hg (hchild o.node n K hn y hy')⟩
  · intro h o ho hc
    obtain ⟨w, hw, hss⟩ := hm.snap h o ho hc
    exact ⟨w, hw.transfer hg (hobj h o ho), hss.transfer hg hobj⟩
  · intro d R x h1 h2 h3 h4
    rw [hg.lastSpEq] at h1
    rw [hg.recEq d h2] at h3
    exact hm.coverGd d R x h1 h2 h3 h4
  · intro x w hw hd hne
    rw [hg.lastSpEq] at hw hne
    cases hx : db.P.get? x with
    | some n =>
      rw [(hg.old x (by simp [hx])).2.1] at hw
      exact hm.coverSec x w hw hd hne
    | none =>
      exfalso
      obtain ⟨r, -, hr⟩ := newest_some hw
      rw [hg.newData x hx r w hr] at hd
      cases hd
  · intro x n' e hn' he h1 h2
    rw [hg.lastSpEq] at h1
    cases hx : db.P.get? x with
    | some n =>
      obtain ⟨n'', hn'', -, -, hh⟩ := hg.grow x n hx
      rw [hn', Option.some.injEq] at hn''
      subst hn''
      have : e ∈ n.hist.upTo K := by rw [← hh]; exact mem_upTo.mpr ⟨he, h2⟩
      exact hm.coverNew x n e hx (mem_upTo.mp this).1 h1 h2
    | none =>
      exfalso
      have := hg.newLate x hx n' hn' e he
      omega

end Transfer

/-! ### After k1, the frozen run only grows -/

theorem lastSp_snoc (S : Stream V T) (R : Record V T) : lastSp (S ++ [R]) = R.sp := by
  simp [lastSp]

/-- A record with no version of y adds nothing about y. -/
theorem snoc_noVersion {S : Stream V T} {R : Record V T} {y : NodeId}
    (hR : R.vers.find? (fun v => v.node == y) = none) :
    (∀ r, (S ++ [R]).versionAt r y = S.versionAt r y) ∧
      (∀ s, s ≤ S.length → newest (S ++ [R]) s y = newest S s y) ∧ (S ++ [R]).lv y = S.lv y := by
  have hlv1 : Stream.lv [R] y = none := by simp [Stream.lv, hR]
  refine ⟨fun r => ?_, fun s hs => ?_, ?_⟩
  · rcases Nat.lt_or_ge r S.length with h | h
    · exact versionAt_append_left h y
    · rcases Nat.lt_or_ge S.length r with h2 | h2
      · rw [versionAt_ge_length (by simp; omega), versionAt_ge_length h]
      · have : r = S.length := by omega
        subst this
        rw [versionAt_snoc_self, hR, versionAt_ge_length (Nat.le_refl _)]
  · rw [newest_eq, newest_eq, List.drop_append_of_le_length hs, lv_append, hlv1, Option.none_or]
  · rw [lv_append, hlv1, Option.none_or]

section FrozenLate

variable {sp : Spec V T} {al : Algo V T} {ts : List T} {k1 : Nat}

local notation "fz" => st sp (frozenAlgo al k1) ts

/-- After k1, a transaction of the frozen run keeps the startup pos, takes no
node, and writes versions of new data nodes only. -/
theorem frozen_late (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {j : Nat}
    (hkj : k1 ≤ j) (hjt : j < ts.length) :
    (parts sp (frozenAlgo al k1) (fz j) ts[j]).s = lastSp (fz j).S ∧
    (parts sp (frozenAlgo al k1) (fz j) ts[j]).taken = [] ∧
    ∀ w ∈ (parts sp (frozenAlgo al k1) (fz j) ts[j]).vs, (fz j).P.get? w.node = none ∧
      ∃ n, (parts sp (frozenAlgo al k1) (fz j) ts[j]).P.get? w.node = some n ∧ n.isData = true := by
  have hok' := frozen_runOK (sp := sp) k1 hok
  have hst' : AlgOK sp (frozenAlgo al k1) := algOK_of sp _ (Or.inl hj)
  have hinv := inv_st sp _ ts hok' hst' j (by omega)
  have hlen := hinv.len
  have hsp : lastSp (fz j).S ≤ j := by have := hinv.spLt; omega
  have hs : (parts sp (frozenAlgo al k1) (fz j) ts[j]).s = lastSp (fz j).S := by
    rw [parts_s]
    unfold startupPos
    rw [frozen_policy, hlen]
    simp only [show ¬ (j + 1 ≤ k1) by omega, ↓reduceIte]
    omega
  have htaken : (parts sp (frozenAlgo al k1) (fz j) ts[j]).taken = [] := by
    rw [parts_taken]
    have hnil : (parts sp (frozenAlgo al k1) (fz j) ts[j]).D1.filter
        (fun e : NodeId × Nat => decide (e.2 ≤ (parts sp (frozenAlgo al k1) (fz j) ts[j]).s)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      rw [hs]
      rcases (step_D1_mem sp _ (fz j) ts[j] hlen e).mp he with h | ⟨h2, -⟩
      · have := (sectionD_mem (hinv.inv1 ▸ h)).1
        simp only [decide_eq_true_eq]; omega
      · simp only [decide_eq_true_eq]; omega
    rw [hnil]
    simp [byLevel]
  refine ⟨hs, htaken, ?_⟩
  intro w hw
  have hstep : StepOK sp (fz j).P (j + 1) (parts sp (frozenAlgo al k1) (fz j) ts[j]).c := by
    rw [parts_c, hlen, Nat.add_sub_cancel]
    exact hok'.2 j hjt
  have hwr := (step_written_iff sp _ (fz j) ts[j] hinv hstep w.node).mp ⟨w, hw, rfl⟩
  rw [htaken] at hwr
  rcases hwr with h | h
  · exact step_dataIds_spec sp _ (fz j) ts[j] hinv hstep h
  · cases h

/-- After k1, the frozen run's next state only grows (`DbGrow`). -/
theorem frozen_grow (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {j : Nat}
    (hkj : k1 ≤ j) (hjt : j < ts.length) : DbGrow sp (fz j) (fz (j + 1)) j := by
  have hok' := frozen_runOK (sp := sp) k1 hok
  have hst' : AlgOK sp (frozenAlgo al k1) := algOK_of sp _ (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinv := inv_st sp _ ts hok' hst' j (by omega)
  have hinv1 := inv_st sp _ ts hok' hst' (j + 1) (by omega)
  have hlen := hinv.len
  have hsp : lastSp (fz j).S ≤ j := by have := hinv.spLt; omega
  obtain ⟨hs, -, hvs⟩ := frozen_late hok hj hkj hjt
  have hS := st_S_succ sp (frozenAlgo al k1) ts hjt
  have hgrow := st_grow sp _ ts hok' hst' (Nat.le_succ j) (by omega)
  -- No version of an old node in the new record.
  have hno : ∀ y, ((fz j).P.get? y).isSome →
      (parts sp (frozenAlgo al k1) (fz j) ts[j]).R.vers.find? (fun v => v.node == y) = none := by
    intro y hy
    rw [parts_R, List.find?_eq_none]
    intro w hw hwy
    have := (hvs w hw).1
    rw [show w.node = y by simpa using hwy] at this
    rw [this] at hy; cases hy
  refine ⟨?_, hgrow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS, lastSp_snoc, parts_R]; exact hs
  · rw [hS]; exact SExt.append _ _
  · intro d hd
    rw [hS, List.getElem?_append_left (by omega)]
  · intro y hy
    obtain ⟨h1, h2, h3⟩ := snoc_noVersion (S := (fz j).S) (hno y hy)
    refine ⟨fun r => by rw [hS]; exact h1 r, by rw [hS]; exact h2 _ (by omega), by rw [hS]; exact h3⟩
  · intro y hy r w hw
    -- y is new: its version is in the new record, of a new data node.
    obtain ⟨-, -, n, hn, -, -, hwd⟩ := hinv1.version_node hw
    rw [hS] at hw
    rcases Nat.lt_or_ge r (fz j).S.length with hr | hr
    · rw [versionAt_append_left hr] at hw
      obtain ⟨-, -, n0, hn0, -⟩ := hinv.version_node hw
      rw [hn0] at hy; cases hy
    · rcases Nat.lt_or_ge (fz j).S.length r with hr2 | hr2
      · rw [versionAt_ge_length (by simp; omega)] at hw; cases hw
      · have : r = (fz j).S.length := by omega
        subst this
        rw [versionAt_snoc_self, parts_R] at hw
        have hwm : w ∈ (parts sp (frozenAlgo al k1) (fz j) ts[j]).vs := List.mem_of_find?_eq_some hw
        have hwy : w.node = y := by have := List.find?_some hw; simpa using this
        obtain ⟨-, n', hn', hd'⟩ := hvs w hwm
        rw [hwy] at hn'
        rw [st_succ sp _ ts hjt, step_P, hn', Option.some.injEq] at hn
        subst hn
        rw [hwd, hd']
  · intro y hy n hn e he
    rw [st_succ sp _ ts hjt, step_P, parts_P' sp _ (fz j) ts[j] hlen, get?_apply, hy,
      Option.none_or] at hn
    cases hnn : newNodeOf (parts sp (frozenAlgo al k1) (fz j) ts[j]).c y with
    | none => rw [hnn] at hn; cases hn
    | some n0 =>
      rw [hnn, Option.map_some, Option.some.injEq] at hn
      subst hn
      obtain ⟨nn, -, -, h0⟩ := newNodeOf_some hnn
      subst h0
      simp only [List.nil_append] at he
      have := (mem_addsFor.mp he).1
      omega
  · intro t ht y
    exact reachable_grow hls hinv.ptrs hinv.rootIn hgrow ht y

end FrozenLate

end SIS
