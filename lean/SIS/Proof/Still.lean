/-
Proofs, part 10c: the still-dirty test of step 7. What the proofs need of it
(`StillOK`): it looks at P only through its nodes, and it puts back every
written node that is still dirty. The exact test has both. So has BergDB's
test (`javaTest`, Rule A over all pointers), because step 7 tests the written
nodes lowest level first: a written node that is still dirty has a pointee in
D after step 5, or a pointee written before it in the record that is still
dirty itself.

Written 2026-10-15 for F1-008-11, WP E2 (docs/level2-alignment.md, M3).
-/
import SIS.Proof.Mark

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The fold of step 7 -/

/-- Step 7 appends a sublist M of the tested nodes to D. -/
theorem fold_shape (al : Algo V T) (S : Stream V T) (P : Struct V) (i : Time) :
    ∀ (l : List NodeId) (D : Dirty) (L : List NodeId), ∃ M, M.Sublist l ∧
      l.foldl (fun (acc : Dirty × List NodeId) x =>
        if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L) =
        (D ++ M.map (fun x => (x, i)), L ++ M) := by
  intro l
  induction l with
  | nil => intro D L; exact ⟨[], List.Sublist.slnil, by simp⟩
  | cons x l ih =>
    intro D L
    rw [List.foldl_cons]
    by_cases hx : al.stillDirty S P D i x = true
    · simp only [hx, ↓reduceIte]
      obtain ⟨M, hM, h⟩ := ih (D ++ [(x, i)]) (L ++ [x])
      exact ⟨x :: M, hM.cons_cons x, by rw [h]; simp⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨M, hM, h⟩ := ih D L
      exact ⟨M, hM.cons x, h⟩

theorem stillDirtyOf_shape (al : Algo V T) (S : Stream V T) (P : Struct V) (D : Dirty) (i : Time)
    (taken : List NodeId) :
    ∃ M, M.Sublist taken ∧ stillDirtyOf al S P D i taken = (D ++ M.map (fun x => (x, i)), M) := by
  obtain ⟨M, hM, h⟩ := fold_shape al S P i taken D []
  refine ⟨M, hM, ?_⟩
  unfold stillDirtyOf
  rw [h]
  simp

/-- A still-dirty test that looks at P only through its nodes gives the same
step 7 for two structures with the same nodes. -/
theorem stillDirtyOf_congr (al : Algo V T)
    (hc : ∀ (S : Stream V T) (P P' : Struct V) (D : Dirty) (i : Time) (x : NodeId),
      SameNodes P P' → al.stillDirty S P D i x = al.stillDirty S P' D i x)
    {P P' : Struct V} (h : SameNodes P P') (S : Stream V T) (D : Dirty) (i : Time)
    (taken : List NodeId) : stillDirtyOf al S P D i taken = stillDirtyOf al S P' D i taken := by
  unfold stillDirtyOf
  congr 1
  funext acc x
  rw [hc S P P' acc.1 i x h]

/-- What the proofs need of the still-dirty test of step 7. -/
structure StillOK (sp : Spec V T) (al : Algo V T) : Prop where
  /-- It looks at P only through its nodes (for restarts, T2). -/
  congr : ∀ (S : Stream V T) (P P' : Struct V) (D : Dirty) (i : Time) (x : NodeId),
    SameNodes P P' → al.stillDirty S P D i x = al.stillDirty S P' D i x
  /-- It puts back every written node that is still dirty (for inv2). -/
  complete : ∀ (db : DB V T) (k : Nat) (tr : T), SpecOK sp → Inv sp db k →
    StepOK sp db.P (k + 1) (parts sp al db tr).c → ∀ x ∈ (parts sp al db tr).taken,
      dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = true →
        x ∈ (parts sp al db tr).r7.2

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- Step 7 puts back a sublist of the taken nodes, with d = k + 1. -/
theorem step_r7_shape {k : Nat} (hlen : db.S.length = k + 1) :
    (parts sp al db tr).r7 =
      ((parts sp al db tr).D2 ++ (parts sp al db tr).r7.2.map (fun x => (x, k + 1)),
        (parts sp al db tr).r7.2) ∧
    (parts sp al db tr).r7.2.Sublist (parts sp al db tr).taken := by
  obtain ⟨M, hM, h⟩ := stillDirtyOf_shape al (parts sp al db tr).S' (parts sp al db tr).P
    (parts sp al db tr).D2 db.S.length (parts sp al db tr).taken
  rw [← parts_r7, hlen] at h
  rw [h]
  exact ⟨rfl, hM⟩

end Step

/-- The exact test has what the proofs need. -/
theorem exact_stillOK (sp : Spec V T) (al : Algo V T) (hex : al.stillDirty = exactTest sp) :
    StillOK sp al where
  congr := by
    intro S P P' D i x h
    rw [hex]
    exact h.dirty i x
  complete := by
    intro db k tr _ hinv _ x hx hd
    rw [step_r7 sp al db tr hex hinv.len]
    exact List.mem_filter.mpr ⟨hx, hd⟩

/-! ### BergDB's test -/

/-- The level of a node, as `byLevel` sorts by it. -/
def lvlOf (P : Struct V) (z : NodeId) : Nat := ((P.get? z).map (·.level)).getD 0

theorem byLevel_sorted (P : Struct V) (xs : List NodeId) :
    (byLevel P xs).Pairwise (fun a b => lvlOf P a ≤ lvlOf P b) := by
  unfold byLevel
  have h := List.pairwise_mergeSort
    (le := fun a b => decide (((P.get? a).map (·.level)).getD 0 ≤ ((P.get? b).map (·.level)).getD 0))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  exact h.imp (fun hab => by simpa [lvlOf] using hab)

theorem writeAll_split (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) {x : NodeId}
    {n : Node V} (hx : P.get? x = some n) (l1 l2 : List NodeId) (vs : List (Version V)) :
    writeAll sp S i P (l1 ++ x :: l2) vs =
      writeAll sp S i P l2 (writeAll sp S i P l1 vs ++
        [mkVersion sp (S.building (writeAll sp S i P l1 vs)) i x n]) := by
  unfold writeAll
  rw [List.foldl_append, List.foldl_cons]
  simp only [hx]

theorem mem_pointees (sp : Spec V T) (h : History V) (y : NodeId) :
    y ∈ pointees sp h ↔ ∃ e ∈ h, y ∈ sp.ptrs e.val := by
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]

/-- A version of a data node with the node's whole history is good: a data
node has no pointers. -/
theorem good_data (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) {y : NodeId}
    {n : Node V} (hy : P.get? y = some n) (hls : LiveSub sp)
    (hnp : ∀ e ∈ n.hist, sp.ptrs e.val = []) {u : Version V} (hu : u.node = y)
    (hh : u.hist = n.hist) : good sp S P t u = true := by
  rw [good_iff]
  refine ⟨⟨n, by rw [hu]; exact hy, by rw [hh]⟩, ?_⟩
  intro z hz
  exfalso
  obtain ⟨e, he, hze⟩ := hls _ _ hz
  rw [hh] at he
  rw [hnp e (mem_upTo.mp he).1] at hze
  simp at hze

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The taken nodes around x: before it, nodes on lower or equal levels; after
it, nodes on higher or equal levels; no repeats. -/
theorem step_taken_split {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) :
    ∃ pre post, (parts sp al db tr).taken = pre ++ x :: post ∧ x ∉ pre ∧ x ∉ post ∧
      (∀ z ∈ pre, z ∉ post) ∧
      (∀ z ∈ post, lvlOf (parts sp al db tr).P x ≤ lvlOf (parts sp al db tr).P z) := by
  obtain ⟨pre, post, h⟩ := List.append_of_mem hx
  have hnd := step_taken_nodup sp al db tr hinv
  have hs : (parts sp al db tr).taken.Pairwise
      (fun a b => lvlOf (parts sp al db tr).P a ≤ lvlOf (parts sp al db tr).P b) := by
    rw [parts_taken]; exact byLevel_sorted _ _
  rw [h] at hnd hs
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdis⟩ := hnd
  rw [List.nodup_cons] at hnd2
  rw [List.pairwise_append] at hs
  obtain ⟨-, hs2, -⟩ := hs
  rw [List.pairwise_cons] at hs2
  refine ⟨pre, post, h, ?_, hnd2.1, ?_, hs2.1⟩
  · intro hxp
    exact hdis x hxp x (List.mem_cons_self) rfl
  · intro z hz hzp
    exact hdis z hz z (List.mem_cons_of_mem x hzp) rfl

/-- A node of D1 that is not taken is in D2. -/
theorem step_D2_of_not_taken {y : NodeId} {d : Nat} (hD1 : (y, d) ∈ (parts sp al db tr).D1)
    (ht : y ∉ (parts sp al db tr).taken) : inD (parts sp al db tr).D2 y = true := by
  rw [inD_iff]
  refine ⟨d, (step_D2_mem sp al db tr _).mpr ⟨hD1, ?_⟩⟩
  simp only
  exact Nat.lt_of_not_le (fun hle => ht ((step_taken_mem sp al db tr y).mpr ⟨d, hD1, hle⟩))

/-- An index node that is dirty after step 3 and not taken is in D2. -/
theorem step_D2_of_dirty (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {y : NodeId}
    (hy : isIndex (parts sp al db tr).P y = true) (hw : written sp y = true)
    (hd : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) y = true)
    (ht : y ∉ (parts sp al db tr).taken) : inD (parts sp al db tr).D2 y = true := by
  cases hD : inD db.D y
  · have hg : y ∈ (parts sp al db tr).gd3 :=
      (step_gd3_mem' sp al db tr hsp hinv hstep y).mpr ⟨isSome_of_isIndex hy, hy, hD, hw, Or.inl hd⟩
    exact step_D2_of_not_taken sp al db tr
      ((step_D1_mem sp al db tr hinv.len _).mpr (Or.inr ⟨rfl, hg⟩)) ht
  · obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hD
    exact step_D2_of_not_taken sp al db tr
      ((step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd')) ht

/-- A written node that is still dirty has a pointee in D2, or a pointee written
before it in the record, on a lower level, that is still dirty itself. -/
theorem step_java_child (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId} {pre post : List NodeId}
    (hsplit : (parts sp al db tr).taken = pre ++ x :: post)
    (hpost : ∀ z ∈ post, lvlOf (parts sp al db tr).P x ≤ lvlOf (parts sp al db tr).P z)
    (hd : dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = true) :
    ∃ nx, (parts sp al db tr).P.get? x = some nx ∧ ∃ y ∈ pointees sp nx.hist,
      inD (parts sp al db tr).D2 y = true ∨
      (y ∈ pre ∧ dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) y = true ∧
        lvlOf (parts sp al db tr).P y < lvlOf (parts sp al db tr).P x) := by
  have hlen := hinv.len
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  have hxt : x ∈ (parts sp al db tr).taken := by rw [hsplit]; simp
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp
    (isSome_of_isIndex (step_taken_index sp al db tr hinv hxt))
  refine ⟨nx, hnx, ?_⟩
  -- The versions written before x: the data versions, then those of pre.
  obtain ⟨wpre, hwpre⟩ : ∃ w, w = writeAll sp db.S (k + 1) (parts sp al db tr).P pre
      (parts sp al db tr).vs0 := ⟨_, rfl⟩
  obtain ⟨vx, hvx⟩ : ∃ v, v = mkVersion sp (db.S.building wpre) (k + 1) x nx := ⟨_, rfl⟩
  have hvs : (parts sp al db tr).vs =
      writeAll sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [vx]) := by
    rw [parts_vs, hlen, hsplit, writeAll_split sp _ _ _ hnx, ← hwpre, ← hvx]
  have hpre_vs : wpre ++ [vx] <+: (parts sp al db tr).vs := by
    rw [hvs]; exact writeAll_prefix sp _ _ _ _ _
  have hw_vs : wpre <+: (parts sp al db tr).vs := (List.prefix_append _ _).trans hpre_vs
  have hvx_mem : vx ∈ (parts sp al db tr).vs := hpre_vs.subset (by simp)
  have hnodup := step_vs_nodup sp al db tr hinv hstep
  have hwnodup : (wpre.map (·.node)).Nodup := (hw_vs.sublist.map _).nodup hnodup
  have hvxnode : vx.node = x := by rw [hvx]; rfl
  have hvxh : vx.hist = nx.hist := by rw [hvx]; rfl
  have hvxl : vx.level = nx.level := by rw [hvx]; rfl
  have hlvx : (Snew sp al db tr).lv x = some vx := by
    rw [← hvxnode]; exact lv_Snew_written sp al db tr hnodup hvx_mem
  have hvs0_w : (parts sp al db tr).vs0 <+: wpre := by
    rw [hwpre]; exact writeAll_prefix sp _ _ _ _ _
  -- The nodes of wpre.
  have hwnodes : ∀ z, (∃ u ∈ wpre, u.node = z) ↔ z ∈ dataIds sp al db tr ∨ z ∈ pre := by
    intro z
    have h1 : wpre.map (·.node) = (parts sp al db tr).vs0.map (·.node) ++
        pre.filter (fun z => ((parts sp al db tr).P.get? z).isSome) := by
      rw [hwpre, writeAll_nodes]
    have h2 : (parts sp al db tr).vs0.map (·.node) = (dataIds sp al db tr).filter
        (fun z => ((parts sp al db tr).P.get? z).isSome) := by
      rw [parts_vs0, writeAll_nodes]; simp [dataIds]
    have h3 : (dataIds sp al db tr).filter (fun z => ((parts sp al db tr).P.get? z).isSome) =
        dataIds sp al db tr := by
      apply List.filter_eq_self.mpr
      intro z hz
      obtain ⟨-, n, hn, -⟩ := step_dataIds_spec sp al db tr hinv hstep hz
      simp [hn]
    have h4 : pre.filter (fun z => ((parts sp al db tr).P.get? z).isSome) = pre := by
      apply List.filter_eq_self.mpr
      intro z hz
      have : z ∈ (parts sp al db tr).taken := by rw [hsplit]; simp [hz]
      exact isSome_of_isIndex (step_taken_index sp al db tr hinv this)
    rw [h2, h3, h4] at h1
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : u.node ∈ wpre.map (·.node) := List.mem_map_of_mem hu
      rw [h1] at this
      exact List.mem_append.mp this
    · intro hz
      have : z ∈ wpre.map (·.node) := by rw [h1]; exact List.mem_append.mpr hz
      simpa using this
  -- The streams.
  have hext : SExt (db.S.building wpre) (Snew sp al db tr) :=
    (SExt.building hw_vs).trans (SExt.building_complete (parts sp al db tr).R (by rw [parts_R]))
  have hext0 : SExt (db.S.building (parts sp al db tr).vs0) (Snew sp al db tr) :=
    (SExt.building (step_vs0_prefix sp al db tr)).trans
      (SExt.building_complete (parts sp al db tr).R (by rw [parts_R]))
  -- Where x is dirty: a time t, reachable, its version not good.
  have hbad : ∃ t ≤ k + 1, reachable sp (parts sp al db tr).P t x = true ∧
      good sp (Snew sp al db tr) (parts sp al db tr).P t vx = false := by
    apply Classical.byContradiction
    intro hno
    have : dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = false := by
      rw [dirty_false_iff]
      refine ⟨vx, hlvx, fun t ht hr => ?_⟩
      cases hg : good sp (Snew sp al db tr) (parts sp al db tr).P t vx
      · exact absurd ⟨t, ht, hr, hg⟩ hno
      · rfl
    rw [hd] at this; simp at this
  obtain ⟨t, ht, hrt, hng⟩ := hbad
  -- A live child y of x at t whose reference is not good.
  have hchild : ∃ y ∈ sp.live (vx.hist.upTo t), ¬ ∃ r w, vx.ref? y = some r ∧
      (Snew sp al db tr).versionAt r y = some w ∧ w.level < vx.level ∧
      good sp (Snew sp al db tr) (parts sp al db tr).P t w = true := by
    apply Classical.byContradiction
    intro hno
    have : good sp (Snew sp al db tr) (parts sp al db tr).P t vx = true := by
      rw [good_iff]
      refine ⟨⟨nx, by rw [hvxnode]; exact hnx, by rw [hvxh]⟩, fun y hy => ?_⟩
      apply Classical.byContradiction
      intro hnot
      exact hno ⟨y, hy, hnot⟩
    rw [hng] at this; simp at this
  obtain ⟨y, hy, hnot⟩ := hchild
  have hyl : y ∈ sp.live (nx.hist.upTo t) := by rw [← hvxh]; exact hy
  obtain ⟨e, he, hye⟩ := hsp.liveSub _ _ hyl
  have hyp : y ∈ pointees sp nx.hist := (mem_pointees sp _ y).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
  obtain ⟨ny, hny, hlt⟩ := hpf.ptrs x nx hnx e (mem_upTo.mp he).1 y hye
  have hry : reachable sp (parts sp al db tr).P t y = true := by
    rw [reachable_iff] at hrt ⊢
    exact Reach.child hrt hnx hyl hny hlt
  have hlvl : lvlOf (parts sp al db tr).P y < lvlOf (parts sp al db tr).P x := by
    simp [lvlOf, hny, hnx, hlt]
  refine ⟨y, hyp, ?_⟩
  have href : vx.ref? y = ((db.S.building wpre).lv y).map (·.recNo) := by
    rw [hvx, ref?_mkVersion]
    simp only [hyp, ↓reduceIte]
  -- A version u of y that the reference names, on a lower level, is not good at t.
  have hnotgood : ∀ u, (db.S.building wpre).lv y = some u →
      (db.S.building wpre).versionAt u.recNo y = some u → u.level = ny.level →
      good sp (Snew sp al db tr) (parts sp al db tr).P t u = false := by
    intro u hu hua hul
    cases hg : good sp (Snew sp al db tr) (parts sp al db tr).P t u
    · rfl
    · exfalso
      apply hnot
      exact ⟨u.recNo, u, by rw [href, hu]; rfl, hext.versionAt hua,
        by rw [hul, hvxl]; exact hlt, hg⟩
  -- Versions in wpre are versions of the record: built.
  have hbuilt := step_vs_built sp al db tr hlen
  -- y is an index node: a data node's version is good.
  have hydata : ny.isData = false := by
    cases hyd : ny.isData
    · rfl
    · exfalso
      cases hy0 : db.P.get? y with
      | some n0 =>
        -- An old data node: no new entries, its one version is in the stream.
        have hP0 := step_P_old sp al db tr hlen hy0
        have hadds : addsFor (parts sp al db tr).c (k + 1) y = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro e' he'
          rw [mem_addsFor] at he'
          have := hstep.dataFixed (y, e'.val) he'.2 n0 hy0
          rw [hny, Option.some.injEq] at hP0
          have hd0 : n0.isData = true := by rw [← hyd, hP0]
          rw [hd0] at this; simp at this
        rw [hadds, List.append_nil, hny, Option.some.injEq] at hP0
        have hd0 : n0.isData = true := by rw [← hyd, hP0]
        obtain ⟨v, hv, hvh⟩ := hinv.dataV y n0 hy0 hd0
        have hnotw : ¬ ∃ u ∈ wpre, u.node = y := by
          rw [hwnodes]
          rintro (h | h)
          · have := (step_dataIds_spec sp al db tr hinv hstep h).1
            rw [hy0] at this; simp at this
          · have hyt : y ∈ (parts sp al db tr).taken := by rw [hsplit]; simp [h]
            have := step_taken_index sp al db tr hinv hyt
            simp [isIndex, hny, hyd] at this
        have hlvw : (db.S.building wpre).lv y = some v := by
          rw [lv_building]
          have : wpre.find? (fun u => u.node == y) = none := by
            rw [List.find?_eq_none]
            intro u hu huy
            exact hnotw ⟨u, hu, by simpa using huy⟩
          rw [this, Option.none_or]; exact hv
        obtain ⟨r, hr⟩ := lv_versionAt hv
        obtain ⟨hrk, hvnode, n1, hn1, hvh1, hvl1, -⟩ := version_old_facts hinv hr
        rw [hy0, Option.some.injEq] at hn1
        subst hn1
        have hrv : v.recNo = r := by
          obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hr
          exact hinv.recNo r R hR v hvR
        have hgood : good sp (Snew sp al db tr) (parts sp al db tr).P t v = true :=
          good_data sp _ _ t hny hsp.liveSub (hpf.data y ny hny hyd) hvnode
            (by rw [hvh, hP0])
        have := hnotgood v hlvw (by
            rw [hrv, versionAt_building_lt (by rw [hlen]; omega)]; exact hr)
          (by rw [hvl1, hP0])
        rw [hgood] at this; simp at this
      | none =>
        -- A new data node: its version is in wpre.
        rcases step_node_cases sp al db tr hlen hny with ⟨n1, hn1, -⟩ | ⟨-, nn, hnn, hid, hn'⟩
        · rw [hy0] at hn1; simp at hn1
        · have hyd' : nn.isData = true := by rw [hn'] at hyd; simpa using hyd
          have hyD : y ∈ dataIds sp al db tr := by
            simp only [dataIds, List.mem_map, List.mem_filter]
            exact ⟨nn, ⟨hnn, hyd'⟩, hid⟩
          obtain ⟨u, hu, huy⟩ := (hwnodes y).mpr (Or.inl hyD)
          have hlvw : (db.S.building wpre).lv y = some u := by
            rw [lv_building, find?_node_of_mem hwnodup hu huy, Option.some_or]
          obtain ⟨n2, -, hn2, -, hrec, hh, hl, -, -⟩ := built_mem hbuilt (hw_vs.subset hu)
          rw [huy, hny, Option.some.injEq] at hn2
          subst hn2
          have hgood : good sp (Snew sp al db tr) (parts sp al db tr).P t u = true :=
            good_data sp _ _ t hny hsp.liveSub (hpf.data y _ hny hyd) huy hh
          have := hnotgood u hlvw (by
              rw [hrec, ← hlen, versionAt_building_eq]
              exact find?_node_of_mem hwnodup hu huy) hl
          rw [hgood] at this; simp at this
  have hyidx : isIndex (parts sp al db tr).P y = true := by simp [isIndex, hny, hydata]
  by_cases hyt : y ∈ (parts sp al db tr).taken
  · -- y is written before x: it is in pre.
    have hypre : y ∈ pre := by
      rw [hsplit] at hyt
      rcases List.mem_append.mp hyt with h | h
      · exact h
      · exfalso
        rcases List.mem_cons.mp h with h | h
        · subst h; omega
        · have := hpost y h; omega
    right
    refine ⟨hypre, ?_, hlvl⟩
    obtain ⟨u, hu, huy⟩ := (hwnodes y).mpr (Or.inr hypre)
    have hlvw : (db.S.building wpre).lv y = some u := by
      rw [lv_building, find?_node_of_mem hwnodup hu huy, Option.some_or]
    obtain ⟨n2, -, hn2, -, hrec, -, hl, -, -⟩ := built_mem hbuilt (hw_vs.subset hu)
    rw [huy, hny, Option.some.injEq] at hn2
    subst hn2
    have hng' := hnotgood u hlvw (by
        rw [hrec, ← hlen, versionAt_building_eq]
        exact find?_node_of_mem hwnodup hu huy) hl
    have hlvu : (Snew sp al db tr).lv y = some u := by
      rw [← huy]; exact lv_Snew_written sp al db tr hnodup (hw_vs.subset hu)
    cases hdy : dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) y
    · rw [dirty_false_iff] at hdy
      obtain ⟨u', hu', hgood⟩ := hdy
      rw [hlvu, Option.some.injEq] at hu'
      subst hu'
      rw [hgood t ht hry] at hng'
      simp at hng'
    · rfl
  · -- y is not written in the record: it is dirty after step 3, and in D2.
    left
    apply step_D2_of_dirty sp al db tr hsp hinv hstep hyidx
      (written_of_ne_root sp (PFacts.ptr_ne_root sp hpf hnx (mem_upTo.mp he).1 hye)) _ hyt
    have hnotw : ¬ ∃ u ∈ wpre, u.node = y := by
      rw [hwnodes]
      rintro (h | h)
      · have := (step_dataIds_spec sp al db tr hinv hstep h).2
        obtain ⟨n3, hn3, hd3⟩ := this
        rw [hny, Option.some.injEq] at hn3
        rw [← hn3, hydata] at hd3; simp at hd3
      · apply hyt; rw [hsplit]; simp [h]
    have hlvw : (db.S.building wpre).lv y = db.S.lv y := by
      rw [lv_building]
      have : wpre.find? (fun u => u.node == y) = none := by
        rw [List.find?_eq_none]
        intro u hu huy
        exact hnotw ⟨u, hu, by simpa using huy⟩
      rw [this, Option.none_or]
    have hlv0 : (db.S.building (parts sp al db tr).vs0).lv y = db.S.lv y := by
      rw [lv_building]
      have : (parts sp al db tr).vs0.find? (fun u => u.node == y) = none := by
        rw [List.find?_eq_none]
        intro u hu huy
        exact hnotw ⟨u, hvs0_w.subset hu, by simpa using huy⟩
      rw [this, Option.none_or]
    cases hlv : db.S.lv y with
    | none => simp [dirty, hlv0, hlv]
    | some u =>
      obtain ⟨r, hr⟩ := lv_versionAt hlv
      obtain ⟨hrk, hunode, n0, hn0, -, hul, -⟩ := version_old_facts hinv hr
      have hrv : u.recNo = r := by
        obtain ⟨R, hR, huR, -⟩ := versionAt_spec hr
        exact hinv.recNo r R hR u huR
      have hP0 := step_P_old sp al db tr hlen hn0
      rw [hny, Option.some.injEq] at hP0
      have hng' := hnotgood u (by rw [hlvw, hlv]) (by
          rw [hrv, versionAt_building_lt (by rw [hlen]; omega)]; exact hr)
        (by rw [hul, hP0])
      cases hdy : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) y
      · rw [dirty_false_iff] at hdy
        obtain ⟨u', hu', hgood⟩ := hdy
        rw [hlv0, hlv, Option.some.injEq] at hu'
        subst hu'
        have := good_mono' sp hext0 (Grow.refl _ (k + 1)) ht (hgood t ht hry)
        rw [hng'] at this; simp at this
      · rfl

/-- BergDB's test puts back every written node that is still dirty: by
induction on the level, using `step_java_child`. -/
theorem step_java_complete (hj : al.stillDirty = javaTest sp) (hsp : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ x ∈ (parts sp al db tr).taken,
      dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = true →
        x ∈ (parts sp al db tr).r7.2 := by
  have hlen := hinv.len
  suffices h : ∀ b x, lvlOf (parts sp al db tr).P x < b → x ∈ (parts sp al db tr).taken →
      dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x = true →
        x ∈ (parts sp al db tr).r7.2 from
    fun x hx hd => h _ x (Nat.lt_succ_self _) hx hd
  intro b
  induction b with
  | zero => intro x h; omega
  | succ b ih =>
    intro x hb hx hd
    obtain ⟨pre, post, hsplit, -, -, hdis, hpost⟩ := step_taken_split sp al db tr hinv hx
    obtain ⟨nx, hnx, y, hyp, hy⟩ := step_java_child sp al db tr hsp hinv hstep hsplit hpost hd
    obtain ⟨M0, -, hst⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) pre
      (parts sp al db tr).D2 []
    have hr7 : (parts sp al db tr).r7 = stillDirtyOf al (parts sp al db tr).S'
        (parts sp al db tr).P (parts sp al db tr).D2 (k + 1) (pre ++ x :: post) := by
      rw [parts_r7, hlen, hsplit]
    unfold stillDirtyOf at hr7
    rw [List.foldl_append, hst, List.foldl_cons] at hr7
    by_cases htest : al.stillDirty (parts sp al db tr).S' (parts sp al db tr).P
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) (k + 1) x = true
    · simp only [htest, ↓reduceIte] at hr7
      obtain ⟨M1, -, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++ [(x, k + 1)]) ([] ++ M0 ++ [x])
      rw [h1] at hr7
      rw [hr7]
      simp
    · exfalso
      simp only [htest, Bool.false_eq_true, ↓reduceIte] at hr7
      obtain ⟨M1, hM1, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) ([] ++ M0)
      rw [h1] at hr7
      apply htest
      rw [hj]
      simp only [javaTest, hnx]
      apply List.any_eq_true.mpr
      refine ⟨y, hyp, ?_⟩
      rw [inD_iff]
      rcases hy with hy | ⟨hypre, hyd, hyl⟩
      · obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hy
        exact ⟨d, List.mem_append_left _ hd'⟩
      · have hyr := ih y (by omega) (by rw [hsplit]; simp [hypre]) hyd
        rw [hr7] at hyr
        simp only [List.nil_append, List.mem_append] at hyr
        rcases hyr with hyr | hyr
        · exact ⟨k + 1, List.mem_append_right _ (List.mem_map.mpr ⟨y, hyr, rfl⟩)⟩
        · exact absurd (hM1.subset hyr) (hdis y hypre)

end Step

/-- BergDB's test has what the proofs need. -/
theorem java_stillOK (sp : Spec V T) (al : Algo V T) (hj : al.stillDirty = javaTest sp) :
    StillOK sp al where
  congr := by
    intro S P P' D i x h
    rw [hj]
    simp only [javaTest, h x]
  complete := by
    intro db k tr hsp hinv hstep
    exact step_java_complete sp al db tr hj hsp hinv hstep

/-- The still-dirty tests the theorems are stated for: the exact one, and
BergDB's. -/
theorem stillOK_of (sp : Spec V T) (al : Algo V T)
    (h : al.stillDirty = exactTest sp ∨ al.stillDirty = javaTest sp) : StillOK sp al := by
  rcases h with h | h
  · exact exact_stillOK sp al h
  · exact java_stillOK sp al h

end SIS
