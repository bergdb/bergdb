/-
Proofs about the physical layer, part 2: clean nodes have fresh references
(bergdb item 001, WP L3). With BergDB's still-dirty test, the latest version of
a node that is reachable and not in D names the latest version of each of its
live children, and these are not in D either. The writer relies on it when it
makes a node's latest version its canonical object after a restart.
-/
import SIS.Proof.Restart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Freshness after transaction k: a node reachable at k and not in D, with
latest version v: each live child z of v is not in D, and v names z's latest
version. -/
def CleanFresh (sp : Spec V T) (db : DB V T) (k : Nat) : Prop :=
  ∀ y v, reachable sp db.P k y = true → inD db.D y = false → db.S.lv y = some v →
    ∀ z ∈ sp.live v.hist, inD db.D z = false ∧ v.ref? z = (db.S.lv z).map (·.recNo)

/-! ### Lists of versions -/

theorem find?_node_append_none {vs ws : List (Version V)} {z : NodeId}
    (h : ∀ w ∈ ws, w.node ≠ z) :
    (vs ++ ws).find? (fun v => v.node == z) = vs.find? (fun v => v.node == z) := by
  rw [List.find?_append]
  cases hf : vs.find? (fun v => v.node == z) with
  | some u => rfl
  | none =>
    simp only [Option.none_or]
    rw [List.find?_eq_none]
    intro w hw hwz
    exact h w hw (by simpa using hwz)

/-- The nodes of the versions that writeAll adds. -/
theorem writeAll_node_mem (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V)
    (xs : List NodeId) (vs : List (Version V)) {w : Version V}
    (hw : w ∈ writeAll sp S i P xs vs) : w ∈ vs ∨ w.node ∈ xs := by
  have h := writeAll_nodes sp S i P xs vs
  obtain ⟨L, hL⟩ := writeAll_prefix sp S i P xs vs
  rw [← hL] at hw h
  rcases List.mem_append.mp hw with h1 | h1
  · exact Or.inl h1
  · right
    rw [List.map_append] at h
    have := List.append_cancel_left h
    have hm : w.node ∈ L.map (·.node) := List.mem_map_of_mem h1
    rw [this] at hm
    exact (List.mem_filter.mp hm).1

/-- The reference that a version of x, written after the versions of the nodes
before it, has for a pointee z that is not written after it in the record:
z's latest version in the stream with the whole record. -/
theorem ref_fresh_of_split (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V)
    (pre post : List NodeId) (vs0 : List (Version V)) {x : NodeId} {nx : Node V}
    (hnx : P.get? x = some nx) {z : NodeId} (hz : z ∈ pointees sp nx.hist) (hzx : z ≠ x)
    (hzpost : z ∉ post) :
    (mkVersion sp (S.building (writeAll sp S i P pre vs0)) i x nx).ref? z =
      ((S.building (writeAll sp S i P (pre ++ x :: post) vs0)).lv z).map (·.recNo) := by
  rw [ref?_mkVersion]
  simp only [hz, ↓reduceIte]
  rw [writeAll_split sp S i P hnx pre post vs0]
  congr 1
  rw [lv_building, lv_building]
  congr 1
  obtain ⟨L, hL⟩ := writeAll_prefix sp S i P post
    (writeAll sp S i P pre vs0 ++ [mkVersion sp (S.building (writeAll sp S i P pre vs0)) i x nx])
  rw [← hL, List.append_assoc]
  rw [find?_node_append_none]
  intro w hw
  rcases List.mem_append.mp hw with h1 | h1
  · rw [List.mem_singleton] at h1
    rw [h1]
    exact fun h => hzx h.symm
  · intro hwz
    have hw' : w ∈ writeAll sp S i P post
        (writeAll sp S i P pre vs0 ++ [mkVersion sp (S.building (writeAll sp S i P pre vs0)) i x nx]) := by
      rw [← hL]; exact List.mem_append_right _ h1
    rcases writeAll_node_mem sp S i P post _ hw' with h2 | h2
    · -- w is in the prefix, not in L: it would be in both.
      have hnd := writeAll_nodes sp S i P post
        (writeAll sp S i P pre vs0 ++ [mkVersion sp (S.building (writeAll sp S i P pre vs0)) i x nx])
      rw [← hL, List.map_append] at hnd
      have hLn := List.append_cancel_left hnd
      have hm : w.node ∈ L.map (·.node) := List.mem_map_of_mem h1
      rw [hLn] at hm
      exact hzpost (by rw [← hwz]; exact (List.mem_filter.mp hm).1)
    · exact hzpost (by rw [← hwz]; exact h2)

/-- A list sorted by level, without repeats, split at x: the nodes after x are
on its level or higher. -/
theorem sorted_split {P : Struct V} {xs : List NodeId} (hnd : xs.Nodup)
    (hs : xs.Pairwise (fun a b => lvlOf P a ≤ lvlOf P b)) {x : NodeId} (hx : x ∈ xs) :
    ∃ pre post, xs = pre ++ x :: post ∧ x ∉ post ∧ ∀ z ∈ post, lvlOf P x ≤ lvlOf P z := by
  obtain ⟨pre, post, h⟩ := List.append_of_mem hx
  rw [h] at hnd hs
  rw [List.nodup_append] at hnd
  rw [List.pairwise_append] at hs
  obtain ⟨-, hs2, -⟩ := hs
  rw [List.pairwise_cons] at hs2
  exact ⟨pre, post, h, (List.nodup_cons.mp hnd.2.1).1, hs2.1⟩

/-- The latest version in a stream whose last record has the versions vs. -/
theorem lv_snoc_vers (S : Stream V T) (R : Record V T) (x : NodeId) :
    (S ++ [R]).lv x = (S.building R.vers).lv x := by
  rw [lv_append, lv_building]
  simp [Stream.lv]

/-- Freshness after T(0): D is empty, and R(0) writes the nodes lowest level
first. -/
theorem cleanFresh_init (sp : Spec V T) (hok : SpecOK sp) : CleanFresh sp (init sp) 0 := by
  intro y v _ _ hv z hz
  refine ⟨rfl, ?_⟩
  rw [lv_init sp hok] at hv
  have hv_mem := List.mem_of_find?_eq_some hv
  have hvy : v.node = y := by have := List.find?_some hv; simpa using this
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = byLevel sp.init ((sp.init.map (·.1)).filter (written sp)) :=
    ⟨_, rfl⟩
  have hxsnd : xs.Nodup := by
    rw [hxs]; exact (byLevel_perm _ _).nodup_iff.mpr (List.Pairwise.filter _ hok.initDistinct)
  have hsorted : xs.Pairwise (fun a b => lvlOf sp.init a ≤ lvlOf sp.init b) := by
    rw [hxs]; exact byLevel_sorted _ _
  have hyx : y ∈ xs := by
    have : v.node ∈ (initVers sp).map (·.node) := List.mem_map_of_mem hv_mem
    rw [initVers_nodes sp hok, ← hxs, hvy] at this
    exact this
  obtain ⟨pre, post, hsplit, -, hpost⟩ := sorted_split hxsnd hsorted hyx
  obtain ⟨ny, pre', hny, -, -, hvh, -, -, -⟩ := built_mem (initVers_built sp) hv_mem
  rw [hvy] at hny
  have hinit : initVers sp = writeAll sp [] 0 sp.init (pre ++ y :: post) [] := by
    unfold initVers; rw [← hxs, hsplit]
  have hvs : initVers sp = writeAll sp [] 0 sp.init post
      (writeAll sp [] 0 sp.init pre [] ++
        [mkVersion sp (Stream.building ([] : Stream V T) (writeAll sp [] 0 sp.init pre [])) 0 y ny]) := by
    rw [hinit, writeAll_split sp _ _ _ hny]
  have hvy_mem : mkVersion sp (Stream.building ([] : Stream V T) (writeAll sp [] 0 sp.init pre [])) 0 y ny ∈
      initVers sp := by
    rw [hvs]; exact (writeAll_prefix sp _ _ _ _ _).subset (by simp)
  have hveq : v = mkVersion sp (Stream.building ([] : Stream V T) (writeAll sp [] 0 sp.init pre [])) 0 y ny := by
    have h1 := find?_node_of_mem (initVers_nodup sp hok) hv_mem hvy
    have h2 := find?_node_of_mem (initVers_nodup sp hok) hvy_mem (y := y) rfl
    rw [h1] at h2; exact Option.some.inj h2
  obtain ⟨e, he, hze⟩ := hok.liveSub _ _ hz
  rw [hvh] at he
  have hzp : z ∈ pointees sp ny.hist := (mem_pointees sp _ z).mpr ⟨e, he, hze⟩
  obtain ⟨nz, hnz, hlt⟩ := hok.initLevels (y, ny) (mem_of_get? hny) e he z hze
  have hzlvl : lvlOf sp.init z < lvlOf sp.init y := by simp [lvlOf, hnz, hny, hlt]
  have hzpost : z ∉ post := fun h => by have := hpost z h; omega
  have hzy : z ≠ y := fun h => by rw [h] at hzlvl; omega
  rw [hveq, ref_fresh_of_split sp [] 0 sp.init pre post [] hny hzp hzy hzpost, ← hinit,
    lv_init sp hok, lv_building, lv_nil, Option.or_none]

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- Step 3 gives the marked index nodes not in D, but a virtual root (T13). -/
theorem step_gd3_marked (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (x : NodeId) :
    x ∈ (parts sp al db tr).gd3 ↔
      ((parts sp al db tr).P.get? x).isSome ∧ isIndex (parts sp al db tr).P x = true ∧
        inD db.D x = false ∧ written sp x = true ∧
        marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = true := by
  rw [step_gd3_mem' sp al db tr hsp hinv hstep]
  constructor
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨a, b, c, d, by rw [step_marked_iff sp al db tr hsp hinv hstep b c d]; exact e⟩
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨a, b, c, d, by rw [← step_marked_iff sp al db tr hsp hinv hstep b c d]; exact e⟩

/-- A node of D after the step: in D before, or got dirty in it, or put back
(then taken). -/
theorem step_D_cases {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (h : inD (parts sp al db tr).r7.1 x = true) :
    inD db.D x = true ∨ x ∈ (parts sp al db tr).gd3 ∨ x ∈ (parts sp al db tr).r7.2 := by
  obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
  rw [(step_r7_shape sp al db tr hinv.len).1] at hd
  rcases List.mem_append.mp hd with h1 | h1
  · obtain ⟨hD1, -⟩ := (step_D2_mem sp al db tr _).mp h1
    rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h2 | ⟨-, h2⟩
    · exact Or.inl ((inD_iff _ _).mpr ⟨d, h2⟩)
    · exact Or.inr (Or.inl h2)
  · obtain ⟨z, hz, hze⟩ := List.mem_map.mp h1
    cases hze
    exact Or.inr (Or.inr hz)

/-- A taken node was in D before, or got dirty in the step. -/
theorem step_taken_D {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : inD db.D x = true ∨ x ∈ (parts sp al db tr).gd3 := by
  obtain ⟨d, hd, -⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨-, h⟩
  · exact Or.inl ((inD_iff _ _).mpr ⟨d, h⟩)
  · exact Or.inr h

/-- Freshness is kept by a transaction, with BergDB's still-dirty test. -/
theorem step_cleanFresh (hj : al.stillDirty = javaTest sp) (hsp : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hfr : CleanFresh sp db k) : CleanFresh sp (step sp al db tr) (k + 1) := by
  have hlen := hinv.len
  have hls : LiveSub sp := hsp.liveSub
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  intro y v hr hD hv z hz
  rw [step_P] at hr
  rw [step_D] at hD ⊢
  rw [step_S] at hv ⊢
  have hnd := step_vs_nodup sp al db tr hinv hstep
  -- y has a node in P, and z is a pointee of v on a lower level.
  obtain ⟨ry, hry⟩ := lv_versionAt hv
  obtain ⟨R, hR, hvR, hvy⟩ := versionAt_spec hry
  have hinv' := inv_step sp al (java_stillOK sp al hj) (fun _ => hj) hsp hinv tr
    (by have := hstep; rwa [parts_c, hlen] at this)
  obtain ⟨-, -, ny, hny, hvh, hvl, hvd⟩ := hinv'.version_node (by rw [step_S]; exact hry)
  rw [step_P] at hny
  obtain ⟨e, he, hze⟩ := hls _ _ hz
  have he' : e ∈ ny.hist := by rw [hvh] at he; exact (mem_upTo.mp he).1
  obtain ⟨nz, hnz, hlt⟩ := hpf.ptrs y ny hny e he' z hze
  have hzp : z ∈ pointees sp ny.hist := (mem_pointees sp _ z).mpr ⟨e, he', hze⟩
  have hydata : ny.isData = false := by
    cases hd : ny.isData
    · rfl
    · have := hpf.data y ny hny hd e he'
      rw [this] at hze; simp at hze
  have hyidx : isIndex (parts sp al db tr).P y = true := by simp [isIndex, hny, hydata]
  by_cases hw : ∃ w ∈ (parts sp al db tr).vs, w.node = y
  · -- y is written in the step: it was taken, and it did not stay dirty.
    obtain ⟨w, hwv, hwy⟩ := hw
    have hlvw := lv_Snew_written sp al db tr hnd hwv
    rw [hwy, hv] at hlvw
    cases hlvw
    rcases (step_written_iff sp al db tr hinv hstep y).mp ⟨v, hwv, hwy⟩ with hdat | hty
    · obtain ⟨-, n, hn, hnd'⟩ := step_dataIds_spec sp al db tr hinv hstep hdat
      rw [hny, Option.some.injEq] at hn
      subst hn
      rw [hydata] at hnd'; cases hnd'
    · obtain ⟨pre, post, hsplit, -, -, -, hpost⟩ := step_taken_split sp al db tr hinv hty
      have hzlvl : lvlOf (parts sp al db tr).P z < lvlOf (parts sp al db tr).P y := by
        simp [lvlOf, hnz, hny, hlt]
      have hzpost : z ∉ post := fun h => by have := hpost z h; omega
      have hzy : z ≠ y := fun h => by rw [h] at hzlvl; omega
      -- The version of y.
      obtain ⟨wpre, hwpre⟩ : ∃ w, w = writeAll sp db.S (k + 1) (parts sp al db tr).P pre
          (parts sp al db tr).vs0 := ⟨_, rfl⟩
      have hvs : (parts sp al db tr).vs = writeAll sp db.S (k + 1) (parts sp al db tr).P post
          (wpre ++ [mkVersion sp (db.S.building wpre) (k + 1) y ny]) := by
        rw [parts_vs, hlen, hsplit, writeAll_split sp _ _ _ hny, ← hwpre]
      have hvy_mem : mkVersion sp (db.S.building wpre) (k + 1) y ny ∈ (parts sp al db tr).vs := by
        rw [hvs]; exact (writeAll_prefix sp _ _ _ _ _).subset (by simp)
      have hveq : v = mkVersion sp (db.S.building wpre) (k + 1) y ny := by
        have h1 := find?_node_of_mem hnd hwv hwy
        have h2 := find?_node_of_mem hnd hvy_mem (y := y) rfl
        rw [h1] at h2; exact Option.some.inj h2
      refine ⟨?_, ?_⟩
      · -- z is not in D: y's test saw no pointee in D.
        obtain ⟨M0, -, hst⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) pre
          (parts sp al db tr).D2 []
        have hr7 : (parts sp al db tr).r7 = stillDirtyOf al (parts sp al db tr).S'
            (parts sp al db tr).P (parts sp al db tr).D2 (k + 1) (pre ++ y :: post) := by
          rw [parts_r7, hlen, hsplit]
        unfold stillDirtyOf at hr7
        rw [List.foldl_append, hst, List.foldl_cons] at hr7
        by_cases htest : al.stillDirty (parts sp al db tr).S' (parts sp al db tr).P
            ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) (k + 1) y = true
        · exfalso
          simp only [htest, ↓reduceIte] at hr7
          obtain ⟨M1, -, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1)
            post ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++ [(y, k + 1)])
            ([] ++ M0 ++ [y])
          rw [h1] at hr7
          have : inD (parts sp al db tr).r7.1 y = true := by
            rw [hr7, inD_iff]
            exact ⟨k + 1, by simp⟩
          rw [hD] at this; cases this
        · simp only [htest, Bool.false_eq_true, ↓reduceIte] at hr7
          obtain ⟨M1, hM1, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1)
            post ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) ([] ++ M0)
          rw [h1] at hr7
          rw [hj] at htest
          simp only [javaTest, hny, List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at htest
          have hz0 := htest z hzp
          rw [hr7]
          simp only
          cases hzD : inD ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++
              M1.map (fun z => (z, k + 1))) z
          · rfl
          · exfalso
            obtain ⟨d, hd⟩ := (inD_iff _ _).mp hzD
            rcases List.mem_append.mp hd with h2 | h2
            · rw [(inD_iff _ _).mpr ⟨d, h2⟩] at hz0; cases hz0
            · obtain ⟨u, hu, hue⟩ := List.mem_map.mp h2
              cases hue
              exact hzpost (hM1.subset hu)
      · -- The reference names z's latest version.
        rw [hveq, hwpre, ref_fresh_of_split sp db.S (k + 1) (parts sp al db tr).P pre post
          (parts sp al db tr).vs0 hny hzp hzy hzpost]
        unfold Snew
        rw [lv_snoc_vers, parts_R]
        simp only
        rw [parts_vs, hlen, hsplit]
  · -- y is not written in the step: it was not in D and not marked, and nor is z.
    have hlvy : (Snew sp al db tr).lv y = db.S.lv y :=
      lv_Snew_not_written sp al db tr (fun w hw' hwy => hw ⟨w, hw', hwy⟩)
    rw [hlvy] at hv
    obtain ⟨-, -, ny0, hny0, hvh0, -, -⟩ := hinv.version_node (hinv.lv_at hv)
    have hnyy := step_P_old sp al db tr hlen hny0
    rw [hny, Option.some.injEq] at hnyy
    have hyt : y ∉ (parts sp al db tr).taken := by
      intro ht
      apply hw
      have : y ∈ (parts sp al db tr).vs.map (·.node) := by
        rw [step_vs_nodes]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨ht, by simp [hny]⟩)
      simpa using this
    have hyD : inD db.D y = false := by
      cases h : inD db.D y
      · rfl
      · exfalso
        obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
        have h2 := step_D2_of_not_taken sp al db tr
          ((step_D1_mem sp al db tr hlen _).mpr (Or.inl hd)) hyt
        have : inD (parts sp al db tr).r7.1 y = true := by
          rw [(step_r7_shape sp al db tr hlen).1]
          obtain ⟨d', hd'⟩ := (inD_iff _ _).mp h2
          exact (inD_iff _ _).mpr ⟨d', List.mem_append_left _ hd'⟩
        rw [hD] at this; cases this
    have hyg : y ∉ (parts sp al db tr).gd3 := by
      intro hg
      have h2 := step_D2_of_not_taken sp al db tr
        ((step_D1_mem sp al db tr hlen _).mpr (Or.inr ⟨rfl, hg⟩)) hyt
      have : inD (parts sp al db tr).r7.1 y = true := by
        rw [(step_r7_shape sp al db tr hlen).1]
        obtain ⟨d', hd'⟩ := (inD_iff _ _).mp h2
        exact (inD_iff _ _).mpr ⟨d', List.mem_append_left _ hd'⟩
      rw [hD] at this; cases this
    have hrk : reachable sp db.P k y = true := by
      rcases hstep.noRes y (by rw [← parts_P' sp al db tr hlen]; exact hr) with h | h
      · simpa using h
      · obtain ⟨nn, hnn, hnnid⟩ := List.mem_map.mp h
        have := hstep.fresh nn hnn
        rw [hnnid, hny0] at this; cases this
    have hfr' := hfr y v hrk hyD hv z hz
    -- z's node before the step.
    obtain ⟨nz0, hnz0⟩ : ∃ n, db.P.get? z = some n := by
      have he0 : e ∈ ny0.hist := by rw [hvh0] at he; exact (mem_upTo.mp he).1
      obtain ⟨n, hn, -⟩ := hinv.ptrs y ny0 hny0 e he0 z hze
      exact ⟨n, hn⟩
    have hzg : z ∉ (parts sp al db tr).gd3 := by
      intro hg
      obtain ⟨-, -, -, -, hmz⟩ := (step_gd3_marked sp al db tr hsp hinv hstep z).mp hg
      apply hyg
      refine (step_gd3_marked sp al db tr hsp hinv hstep y).mpr
        ⟨by rw [hny]; rfl, hyidx, hyD, hinv.written_of_lv hv, ?_⟩
      unfold marked at hmz ⊢
      rw [Bool.and_eq_true] at hmz ⊢
      refine ⟨hr, ?_⟩
      rw [hnz] at hmz
      rw [hny]
      simp only at hmz ⊢
      obtain ⟨-, hmz⟩ := hmz
      by_cases hcy : changed (parts sp al db tr).c y = true
      · exact List.any_eq_true.mpr ⟨y, self_mem_reachFrom sp _ _ y ny, hcy⟩
      · -- y is not changed: its history is v's, and z is a live child of it.
        have hadds : addsFor (parts sp al db tr).c (k + 1) y = [] := by
          simp only [addsFor, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
          intro a ha hay
          apply hcy
          simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
          exact Or.inr ⟨a, ha, hay⟩
        rw [hadds, List.append_nil] at hnyy
        -- v is good at k: y is clean.
        have hidx0 : isIndex db.P y = true := by
          rw [hnyy] at hydata; simp [isIndex, hny0]; exact hydata
        have hcl : dirty sp db.S db.P k y = false := by
          cases hc : dirty sp db.S db.P k y
          · rfl
          · have := hinv.inv2 y hidx0 (hinv.written_of_lv hv) hc
            rw [hyD] at this; cases this
        obtain ⟨v', hv', hg⟩ := (dirty_false_iff sp db.S db.P k y).mp hcl
        rw [hv] at hv'; cases hv'
        have hgk := hg k (Nat.le_refl _) hrk
        rw [good_iff] at hgk
        obtain ⟨⟨n', hn', hc⟩, -⟩ := hgk
        rw [(hinv.version_node (hinv.lv_at hv)).1, hny0, Option.some.injEq] at hn'
        subst hn'
        have hvk : v.hist.upTo k = v.hist := by
          apply upTo_of_forall
          intro e1 he1
          rw [hvh0] at he1
          have := (mem_upTo.mp he1).2
          have : v.recNo ≤ k := by
            obtain ⟨R0, hR0, -, -⟩ := versionAt_spec (hinv.lv_at hv)
            obtain ⟨hlt0, -⟩ := List.getElem?_eq_some_iff.mp hR0
            omega
          omega
        have hnk : ny0.hist.upTo k = ny0.hist := upTo_of_forall _ _ (hinv.times y ny0 hny0)
        have hvn : v.hist = ny.hist := by
          rw [hnyy]; simp only; rw [← hvk, hc, hnk]
        have hzl : z ∈ sp.live (ny.hist.upTo (k + 1)) := by
          rw [upTo_of_forall _ _ (hpf.times y ny hny), ← hvn]; exact hz
        apply List.any_eq_true.mpr
        obtain ⟨w, hw1, hw2⟩ := List.any_eq_true.mp hmz
        exact ⟨w, reachFrom_child_sub sp hzl hnz hlt w hw1, hw2⟩
    have hzt : z ∉ (parts sp al db tr).taken := by
      intro ht
      rcases step_taken_D sp al db tr hinv ht with h | h
      · rw [hfr'.1] at h; cases h
      · exact hzg h
    refine ⟨?_, ?_⟩
    · cases h : inD (parts sp al db tr).r7.1 z
      · rfl
      · exfalso
        rcases step_D_cases sp al db tr hinv h with h1 | h1 | h1
        · rw [hfr'.1] at h1; cases h1
        · exact hzg h1
        · exact hzt ((step_r7_shape sp al db tr hlen).2.subset h1)
    · rw [hfr'.2]
      congr 1
      symm
      apply lv_Snew_not_written
      intro w hw' hwz
      rcases (step_written_iff sp al db tr hinv hstep z).mp ⟨w, hw', hwz⟩ with h1 | h1
      · obtain ⟨h2, -⟩ := step_dataIds_spec sp al db tr hinv hstep h1
        rw [hnz0] at h2; cases h2
      · exact hzt h1

end Step

/-- Freshness after every transaction of a run, with BergDB's still-dirty test. -/
theorem cleanFresh_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) : ∀ j ≤ ts.length, CleanFresh sp (st sp al ts j) j := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _
    rw [st_zero]
    exact cleanFresh_init sp hok.1
  | succ j ih =>
    intro hj'
    rw [st_succ sp al ts (by omega)]
    have hinv := inv_st sp al ts hok hst j (by omega)
    apply step_cleanFresh sp al _ _ hj hok.1 hinv _ (ih (by omega))
    have := hok.2 j (by omega)
    rw [parts_c, hinv.len]
    simpa [st] using this

/-! ### A data node has one version -/

theorem versionAt_snoc_self (S : Stream V T) (R : Record V T) (x : NodeId) :
    (S ++ [R]).versionAt S.length x = R.vers.find? (fun v => v.node == x) := by
  unfold Stream.versionAt
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Every version of a data node is its latest. -/
def DataOnce (db : DB V T) : Prop :=
  ∀ x n r w, db.P.get? x = some n → n.isData = true → db.S.versionAt r x = some w →
    db.S.lv x = some w

theorem dataOnce_init (sp : Spec V T) : DataOnce (init sp) := by
  intro x n r w _ _ hw
  rw [init_eq] at hw ⊢
  cases r with
  | zero =>
    simp only [Stream.versionAt, List.getElem?_cons_zero] at hw
    simp only [Stream.lv, List.reverse_singleton, List.findSome?_singleton]
    exact hw
  | succ r => simp [Stream.versionAt] at hw

theorem step_dataOnce (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hd : DataOnce db) : DataOnce (step sp al db tr) := by
  have hlen := hinv.len
  intro x n r w hn hdat hw
  rw [step_P] at hn
  rw [step_S] at hw ⊢
  have hnd := step_vs_nodup sp al db tr hinv hstep
  rcases Nat.lt_or_ge r db.S.length with hr | hr
  · -- An old version: x is not written now.
    have hw0 : db.S.versionAt r x = some w := by
      rw [← versionAt_append_left hr x]; exact hw
    obtain ⟨-, -, n0, hn0, -, -, hd0⟩ := hinv.version_node hw0
    have hnn := step_P_old sp al db tr hlen hn0
    rw [hn, Option.some.injEq] at hnn
    have hdat0 : n0.isData = true := by rw [hnn] at hdat; exact hdat
    rw [lv_Snew_not_written sp al db tr]
    · exact hd x n0 r w hn0 hdat0 hw0
    · intro u hu hux
      rcases (step_written_iff sp al db tr hinv hstep x).mp ⟨u, hu, hux⟩ with h1 | h1
      · obtain ⟨h2, -⟩ := step_dataIds_spec sp al db tr hinv hstep h1
        rw [hn0] at h2; cases h2
      · have := step_taken_index sp al db tr hinv h1
        simp [isIndex, hn, hdat] at this
  · -- A version of the new record.
    have hr' : r = db.S.length := by
      have := (step_Snew_len sp al db tr hinv)
      obtain ⟨R, hR, -, -⟩ := versionAt_spec hw
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hR
      rw [this] at hlt
      omega
    subst hr'
    unfold Snew at hw
    rw [versionAt_snoc_self] at hw
    have hwv : w ∈ (parts sp al db tr).vs := by
      rw [parts_R] at hw; exact List.mem_of_find?_eq_some hw
    have hwx : w.node = x := by
      rw [parts_R] at hw; have := List.find?_some hw; simpa using this
    rw [← hwx]
    exact lv_Snew_written sp al db tr hnd hwv

theorem dataOnce_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) : ∀ j ≤ ts.length, DataOnce (st sp al ts j) := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero]; exact dataOnce_init sp
  | succ j ih =>
    intro hj'
    rw [st_succ sp al ts (by omega)]
    have hinv := inv_st sp al ts hok hst j (by omega)
    apply step_dataOnce sp al _ _ hinv _ (ih (by omega))
    have := hok.2 j (by omega)
    rw [parts_c, hinv.len]
    simpa [st] using this

end SIS
