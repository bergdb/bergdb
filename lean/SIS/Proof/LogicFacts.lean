/-
Proofs: logical facts and list lemmas that the proofs of the physical layer
share (bergdb 005-62, from the proof files of the design before handles): D's
got-dirty indices (`dOf`), Rule R's bounds (`Inv.ruleR_bound`, `Inv.ruleR_lv0`)
and the latest versions (`Inv.lv_whole`, `Inv.ref_versionAt`), a clean node's
latest version good for every time it is reachable (`Inv.clean_good`), TREE's
one current parent (`treeAt_unique`), the parts of a transaction from step 3 on
(`D1Of`, `takenOf`, `stepOf`) and that they depend on P only through its nodes.
-/
import SIS.Proof.EvLogic
import SIS.Proof.PhysMem
import SIS.Proof.VRead
import SIS.Proof.PhysT2

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem lookup_map_val {β : Type} (g : NodeId → β → β) :
    ∀ (l : List (NodeId × β)) (y : NodeId),
      (l.map (fun q => (q.1, g q.1 q.2))).lookup y = (l.lookup y).map (g y)
  | [], _ => rfl
  | (a, b) :: l, y => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hya : y = a
    · subst hya; simp
    · have : (y == a) = false := by simp [hya]
      simp only [this]
      exact lookup_map_val g l y

/-- The got-dirty index of x in D, if x is in D. -/
def dOf (D : Dirty) (x : NodeId) : Option Nat := (D.find? (fun e => e.1 == x)).map (·.2)

theorem ruleRRef_some_ge {S0 : Stream V T} {s : Nat} {y : NodeId} {r r0 : Nat}
    (h : ruleRRef S0 s y (some r) = some r0) : r ≤ r0 := by
  unfold ruleRRef at h
  cases hn : newest S0 s y with
  | none => rw [hn] at h; simp at h; omega
  | some w =>
    rw [hn] at h
    simp only at h
    split at h
    · simp at h; omega
    · simp at h; omega

section

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The reference of a version names a version of the pointee. -/
theorem Inv.ref_versionAt (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt r x = some v) {y : NodeId} {r1 : Nat} (h1 : v.ref? y = some r1) :
    ∃ u, db.S.versionAt r1 y = some u := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
  rw [href y] at h1
  split at h1
  · cases hl : (Stream.building (db.S.take r) pre).lv y with
    | none => rw [hl] at h1; cases h1
    | some u =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      obtain ⟨r0, hr0⟩ := lv_versionAt hl
      have hu0 := (sext_building_take hR hpre).versionAt hr0
      obtain ⟨-, hur, -⟩ := hinv.version_node hu0
      rw [← h1, hur]
      exact ⟨u, hu0⟩
  · cases h1

/-- Rule R of the stream of the last startup, a prefix of the stream, leaves the
reference to the latest version. -/
theorem Inv.ruleR_lv0 (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    (y : NodeId) : ruleRRef S0 s y ((db.S.lv y).map (·.recNo)) = (db.S.lv y).map (·.recNo) := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some w =>
    simp only
    obtain ⟨r0, -, hr0⟩ := newest_some hn
    have hr0' := versionAt_prefix hpre hr0
    obtain ⟨-, hrec, -⟩ := hinv.version_node hr0'
    obtain ⟨v, hv, hle⟩ := hinv.le_lv hr0'
    rw [hv]
    simp only [Option.map_some]
    have : ¬ v.recNo < w.recNo := by omega
    simp [this]

/-- Rule R of the stream of the last startup on a reference to a version gives a
version, at most the latest. -/
theorem Inv.ruleR_bound (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    {y : NodeId} {r : Option Nat} (hr : ∀ r', r = some r' → ∃ u, db.S.versionAt r' y = some u)
    {r0 : Nat} (h : ruleRRef S0 s y r = some r0) :
    (∃ u, db.S.versionAt r0 y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r0 ≤ v.recNo := by
  have hver : ∃ u, db.S.versionAt r0 y = some u := by
    unfold ruleRRef at h
    cases hn : newest S0 s y with
    | none => rw [hn] at h; exact hr r0 h
    | some w =>
      rw [hn] at h
      obtain ⟨r1, -, hr1⟩ := newest_some hn
      have hr1' := versionAt_prefix hpre hr1
      obtain ⟨-, hrec, -⟩ := hinv.version_node hr1'
      simp only at h
      cases r with
      | none =>
        simp only [Option.some.injEq] at h
        rw [← h, hrec]; exact ⟨w, hr1'⟩
      | some r' =>
        simp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [← h, hrec]; exact ⟨w, hr1'⟩
        · simp only [Option.some.injEq] at h
          rw [← h]; exact hr r' rfl
  obtain ⟨u, hu⟩ := hver
  exact ⟨⟨u, hu⟩, hinv.le_lv hu⟩

/-- A clean node's latest version holds its whole history. -/
theorem Inv.lv_whole (hinv : Inv sp db k) {y : NodeId} {n : Node V} (hn : db.P.get? y = some n)
    (hw : written sp y = true) (hD : inD db.D y = false) (hr : reachable sp db.P k y = true) :
    ∃ v, db.S.lv y = some v ∧ v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
  have hwhole : ∀ v, db.S.lv y = some v → v.hist.upTo k = n.hist.upTo k →
      v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
    intro v hv hup
    have hva := hinv.lv_at hv
    obtain ⟨-, hrec, n', hn', hh, hl, hd⟩ := hinv.version_node hva
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hrk : v.recNo ≤ k := by
      obtain ⟨R, hR, -, -⟩ := versionAt_spec hva
      have := (List.getElem?_eq_some_iff.mp hR).1
      rw [hinv.len] at this; omega
    refine ⟨?_, hl, hd⟩
    have h1 : v.hist.upTo k = v.hist := by rw [hh, upTo_upTo' _ hrk]
    have h2 : n.hist.upTo k = n.hist := upTo_of_forall _ _ (hinv.times y n hn)
    rw [← h1, hup, h2]
  by_cases hd : n.isData = true
  · obtain ⟨v, hv, hvh⟩ := hinv.dataV y n hn hd
    obtain ⟨h1, h2, h3⟩ := hwhole v hv (by rw [hvh])
    exact ⟨v, hv, h1, h2, h3⟩
  · have hix : isIndex db.P y = true := by simp [isIndex, hn, hd]
    have hdirty : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => rw [hinv.inv2 y hix hw hdy] at hD; cases hD
    obtain ⟨v, hv, hgood⟩ := (dirty_false_iff sp db.S db.P k y).mp hdirty
    have hg := hgood k (Nat.le_refl k) hr
    rw [good_eq] at hg
    simp only [Bool.and_eq_true] at hg
    have hup : v.hist.upTo k = n.hist.upTo k := by
      have h1 := hg.1
      have hvn : v.node = y := by
        obtain ⟨-, -, -⟩ := hinv.version_node (hinv.lv_at hv)
        exact (hinv.version_node (hinv.lv_at hv)).1
      rw [hvn, hn] at h1
      simpa using h1
    obtain ⟨h1, h2, h3⟩ := hwhole v hv hup
    exact ⟨v, hv, h1, h2, h3⟩

end

section

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem lookup_filter_self {β : Type} (l : List (Nat × β)) (h : Nat) :
    List.lookup h (l.filter (fun p => p.1 != h)) = none := by
  apply lookup_none_of_not_mem
  intro hm
  obtain ⟨p, hp, hph⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hph] at this
  simp at this

theorem lookup_filter_snd (l : List (NodeId × Nat)) (hnd : (l.map (·.1)).Nodup) (a : NodeId)
    (h : Nat) :
    List.lookup a (l.filter (fun p => p.2 != h)) =
      if List.lookup a l = some h then none else List.lookup a l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨b, c⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons, lookup_cons_eq]
    by_cases hab : a = b
    · subst hab
      have hl : List.lookup a l = none := lookup_none_of_not_mem hnd.1
      by_cases hc : c = h
      · subst hc
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [ih hnd.2, hl]; simp
      · have : (c != h) = true := by simp [hc]
        simp only [this, ↓reduceIte, lookup_cons_eq, Option.some.injEq, hc]
    · simp only [hab, ↓reduceIte]
      split
      · rw [lookup_cons_eq]; simp only [hab, ↓reduceIte]; exact ih hnd.2
      · exact ih hnd.2

end

theorem mem_pointees_of_live' {sp : Spec V T} (hls : LiveSub sp) {h : History V} {y : NodeId}
    (hy : y ∈ sp.live h) : y ∈ pointees sp h := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, hye⟩

/-- A nodup list with two different members has two elements at least. -/
theorem two_le_length {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
    a ≠ b → 2 ≤ l.length
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: l, hnd, a, b, ha, hb, hab => by
    simp only [List.nodup_cons] at hnd
    simp only [List.length_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · have : 0 < l.length := List.length_pos_of_mem hb
        omega
    · have : 0 < l.length := List.length_pos_of_mem ha
      omega

/-- Node x has z as a live child at t. -/
def liveParentB (sp : Spec V T) (P : Struct V) (t : Time) (z x : NodeId) : Bool :=
  match P.get? x with
  | some n => (sp.live (n.hist.upTo t)).contains z
  | none => false

/-- TREE: a reachable node other than the root is the live child of one reachable
node only. -/
theorem treeAt_unique {sp : Spec V T} {P : Struct V} {t : Time} (htr : treeAt sp P t) {z : NodeId}
    (hz : reachable sp P t z = true) (hzr : z ≠ root) {x1 x2 : NodeId} {n1 n2 : Node V}
    (h1 : reachable sp P t x1 = true) (h2 : reachable sp P t x2 = true) (hn1 : P.get? x1 = some n1)
    (hn2 : P.get? x2 = some n2) (hz1 : z ∈ sp.live (n1.hist.upTo t)) (hz2 : z ∈ sp.live (n2.hist.upTo t)) :
    x1 = x2 := by
  by_cases hne : x1 = x2
  · exact hne
  exfalso
  have hlen : ((reachList sp P t).eraseDups.filter (liveParentB sp P t z)).length = 1 := htr z hz hzr
  have hmem : ∀ x n, reachable sp P t x = true → P.get? x = some n → z ∈ sp.live (n.hist.upTo t) →
      x ∈ (reachList sp P t).eraseDups.filter (liveParentB sp P t z) := by
    intro x n hr hn hzl
    rw [List.mem_filter, List.mem_eraseDups]
    refine ⟨by simpa [reachable] using hr, ?_⟩
    unfold liveParentB
    rw [hn]; exact List.contains_iff_mem.mpr hzl
  have := two_le_length (nodup_filter (nodup_eraseDups _) _) (hmem x1 n1 h1 hn1 hz1)
    (hmem x2 n2 h2 hn2 hz2) hne
  omega

section

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- A node of the structure is not new. -/
theorem not_new_of_get? (hstep : StepOK sp db.P (k + 1) c) {y : NodeId} {n : Node V}
    (hn : db.P.get? y = some n) : y ∉ c.new.map (·.id) := by
  intro hy
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
  have := hstep.fresh nn hnn
  rw [hid, hn] at this; cases this

/-- The new node with a given id. -/
theorem new_unique : ∀ {N : List NewNode}, (N.map (·.id)).Nodup → ∀ {nn nn' : NewNode}, nn ∈ N → nn' ∈ N →
    nn.id = nn'.id → nn = nn'
  | [], _, _, _, h1, _, _ => by cases h1
  | a :: l, hnd, nn, nn', h1, h2, he => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exfalso; apply hnd.1; rw [he]; exact List.mem_map.mpr ⟨nn', h2', rfl⟩
    · exfalso; apply hnd.1; rw [← he]; exact List.mem_map.mpr ⟨nn, h1', rfl⟩
    · exact new_unique hnd.2 h1' h2' he

end

theorem pointees_append_mem {sp : Spec V T} {h1 h2 : History V} {y : NodeId}
    (hy : y ∈ pointees sp (h1 ++ h2)) : y ∈ pointees sp h1 ∨ y ∈ pointees sp h2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ((mem_pointees sp h1 y).mpr ⟨e, he, hye⟩)
  · exact Or.inr ((mem_pointees sp h2 y).mpr ⟨e, he, hye⟩)

theorem pointees_adds_mem {sp : Spec V T} {L : List (NodeId × V)} {j : Time} {y : NodeId}
    (hy : y ∈ pointees sp (L.map (fun a => (⟨j, a.2⟩ : Entry V)))) :
    ∃ a ∈ L, y ∈ sp.ptrs a.2 := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact ⟨a, ha, hye⟩

section

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- The nodes taken are in D. -/
theorem step_taken_inD {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s := by
  obtain ⟨d, hd, hds⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨h, -⟩
  · exact ⟨d, h, hds⟩
  · exfalso; simp only at h; have := step_s_le sp al db tr hinv.len; omega

theorem dOf_of_mem : ∀ {D : Dirty}, (D.map (·.1)).Nodup → ∀ {z : NodeId} {d : Nat}, (z, d) ∈ D →
    dOf D z = some d
  | [], _, _, _, h => by cases h
  | e :: D, hnd, z, d, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold dOf
    simp only [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : e.1 ≠ z := by
        intro he; apply hnd.1; rw [he]; exact List.mem_map.mpr ⟨(z, d), h, rfl⟩
      have : (e.1 == z) = false := by simp [hne]
      simp only [this]
      exact dOf_of_mem hnd.2 h

theorem mem_of_dOf {D : Dirty} {z : NodeId} {d : Nat} (h : dOf D z = some d) : (z, d) ∈ D := by
  unfold dOf at h
  cases hf : D.find? (fun e => e.1 == z) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    have hm := List.mem_of_find?_eq_some hf
    rw [← he, ← h]
    exact hm

theorem dOf_inD {D : Dirty} {z : NodeId} (h : inD D z = true) : ∃ d, dOf D z = some d := by
  obtain ⟨d, hd⟩ := (inD_iff D z).mp h
  unfold dOf
  cases hf : D.find? (fun e => e.1 == z) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact hf (z, d) hd (by simp)
  | some e => exact ⟨e.2, rfl⟩

/-- An entry of D after the transaction: got dirty in it, or an entry of D before
that was not taken. -/
theorem step_D'_entry {k : Nat} (hinv : Inv sp db k) {z : NodeId} {d : Nat}
    (h : (z, d) ∈ (parts sp al db tr).r7.1) : d = k + 1 ∨ ((z, d) ∈ db.D ∧ (parts sp al db tr).s < d) := by
  rw [(step_r7_shape sp al db tr hinv.len).1] at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨hD1, hs⟩ := (step_D2_mem sp al db tr _).mp h
    rcases (step_D1_mem sp al db tr hinv.len _).mp hD1 with h1 | ⟨h1, -⟩
    · exact Or.inr ⟨h1, hs⟩
    · exact Or.inl h1
  · obtain ⟨x, -, hx⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hx
    exact Or.inl hx.2.symm

theorem lv_building_Snew (z : NodeId) :
    (db.S.building (parts sp al db tr).vs).lv z = (Snew sp al db tr).lv z := by
  unfold Snew Stream.building
  rw [lv_append, lv_append]
  simp [Stream.lv, parts_R]

theorem Inv.D_le {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {x : NodeId} {d : Nat}
    (h : (x, d) ∈ db.D) : d ≤ k := by
  rw [hinv.inv1] at h
  have := (sectionD_mem h).2.1
  rw [hinv.len] at this
  omega

end

/-- Steps 3 to 8 of a transaction, from the versions of step 2 (vs0), and the
record's versions (vs): as `stepWith`. -/
def D1Of (sp : Spec V T) (al : Algo V T) (db : DB V T) (c : Changes V) (vs0 : List (Version V)) : Dirty :=
  let i := db.S.length
  let P := db.P.apply i c
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  db.D ++ gd3.map (fun x => (x, i))

def takenOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) (c : Changes V) (vs0 : List (Version V)) :
    List NodeId :=
  let i := db.S.length
  let P := db.P.apply i c
  let D1 := D1Of sp al db c vs0
  let s : Nat := startupPos al db.S D1 i tr
  byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))

def stepOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) (c : Changes V)
    (vs0 vs : List (Version V)) : DB V T :=
  let i := db.S.length
  let P := db.P.apply i c
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let S' : Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  { P := P, D := r7.1, S := db.S ++ [R] }

theorem step_eq_stepOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr = stepOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 (parts sp al db tr).vs :=
  rfl

theorem parts_D1Of (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).D1 = D1Of sp al db (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

theorem parts_takenOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).taken = takenOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

section

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem D1Of_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (c : Changes V) (vs0 : List (Version V)) :
    D1Of sp al ⟨P, D, S⟩ c vs0 = D1Of sp al ⟨P', D, S⟩ c vs0 := by
  have hPP := hP.apply S.length c
  unfold D1Of
  simp only [gotDirty3_congr sp al _ _ hPP]

theorem takenOf_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (tr : T) (c : Changes V)
    (vs0 : List (Version V)) :
    takenOf sp al ⟨P, D, S⟩ tr c vs0 = takenOf sp al ⟨P', D, S⟩ tr c vs0 := by
  have hPP := hP.apply S.length c
  unfold takenOf
  simp only [D1Of_congr hP, byLevel_congr hPP]

theorem stepOf_congr (al : Algo V T) (hst : AlgOK sp al) (D : Dirty) (S : Stream V T) (tr : T)
    (c : Changes V) (vs0 vs : List (Version V)) :
    Rel (stepOf sp al ⟨P, D, S⟩ tr c vs0 vs) (stepOf sp al ⟨P', D, S⟩ tr c vs0 vs) := by
  have hPP := hP.apply S.length c
  unfold stepOf
  simp only [gotDirty3_congr sp al _ _ hPP, byLevel_congr hPP,
    stillDirtyOf_congr al hst.still.congr hPP, topOf_sameNodes sp hPP]
  exact ⟨rfl, rfl, hPP⟩

end

/-- INV-SLOT's second half: y and x are in D, x got dirty no later. -/
def DLater (D : Dirty) (x y : NodeId) : Prop :=
  inD D y = true ∧ inD D x = true ∧ ∃ a b, dOf D x = some a ∧ dOf D y = some b ∧ a ≤ b

section

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A written node not in D, reachable at t ≤ k, has a latest version, good for
t: it is clean (INV-2). -/
theorem Inv.clean_good (hinv : Inv sp db k) (hls : LiveSub sp) {y : NodeId} (hyD : inD db.D y = false)
    (hyw : written sp y = true) {t : Time} (ht : t ≤ k) (hr : reachable sp db.P t y = true) :
    ∃ v, db.S.lv y = some v ∧ good sp db.S db.P t v = true := by
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  cases hd : ny.isData with
  | true =>
    obtain ⟨v, hv, -⟩ := hinv.dataV y ny hny hd
    exact ⟨v, hv, hinv.good_data hls hny hd hv t⟩
  | false =>
    have hidx : isIndex db.P y = true := by simp [isIndex, hny, hd]
    have hcl : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => have := hinv.inv2 y hidx hyw hdy; rw [hyD] at this; cases this
    unfold dirty at hcl
    cases hl : db.S.lv y with
    | none => rw [hl] at hcl; cases hcl
    | some v =>
      rw [hl] at hcl
      simp only [List.any_eq_false, List.mem_range] at hcl
      refine ⟨v, rfl, ?_⟩
      have := hcl t (by omega)
      simp only [hr, Bool.true_and, Bool.not_eq_true'] at this
      cases hg : good sp db.S db.P t v
      · rw [hg] at this; exact absurd rfl this
      · rfl

theorem ruleRRef_some_some (S0 : Stream V T) (s : Nat) (y : NodeId) (r : Nat) :
    ∃ r', ruleRRef S0 s y (some r) = some r' := by
  unfold ruleRRef
  cases newest S0 s y with
  | none => exact ⟨r, rfl⟩
  | some w =>
    simp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- A live child at t of a node reachable at t is reachable at t, below it, and
not the root. -/
theorem Inv.reach_child (hinv : Inv sp db k) (hls : LiveSub sp) {x : NodeId} {n : Node V}
    (hn : db.P.get? x = some n) {t : Time} (hr : reachable sp db.P t x = true) {y : NodeId}
    (hy : y ∈ sp.live (n.hist.upTo t)) :
    reachable sp db.P t y = true ∧ y ≠ root ∧ ∃ ny, db.P.get? y = some ny ∧ ny.level < n.level := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs x n hn e (mem_upTo.mp he).1 y hye
  refine ⟨?_, hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye, ny, hny, hlt⟩
  rw [reachable_iff] at hr ⊢
  exact Reach.child hr hn hy hny hlt

end

end SIS
