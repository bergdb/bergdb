/-
Proofs, part 3: versions in the stream, latest versions, `good` and `dirty`.
-/
import SIS.Proof.Reach

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type}

/-! ### Versions in records and streams -/

/-- Within a record without repeated nodes, the version of y found is the
one version of y. -/
theorem find?_node_of_mem {vs : List (Version V)} (hnd : (vs.map (·.node)).Nodup)
    {w : Version V} (hw : w ∈ vs) {y : NodeId} (hy : w.node = y) :
    vs.find? (fun v => v.node == y) = some w := by
  induction vs with
  | nil => simp at hw
  | cons a vs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hw with rfl | hw'
    · simp [hy]
    · have hne : a.node ≠ y := by
        intro h
        exact hnd.1 ⟨w, hw', by rw [hy, h]⟩
      have : (a.node == y) = false := by simp [hne]
      simp only [this]
      exact ih hnd.2 hw'

theorem find?_node_spec {vs : List (Version V)} {y : NodeId} {w : Version V}
    (h : vs.find? (fun v => v.node == y) = some w) : w ∈ vs ∧ w.node = y := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem versionAt_spec {S : Stream V T} {r : Nat} {y : NodeId} {w : Version V}
    (h : S.versionAt r y = some w) : ∃ R, S[r]? = some R ∧ w ∈ R.vers ∧ w.node = y := by
  unfold Stream.versionAt at h
  split at h
  · rename_i R hR
    exact ⟨R, hR, find?_node_spec h⟩
  · simp at h

theorem versionAt_of_mem {S : Stream V T} {r : Nat} {R : Record V T} (hR : S[r]? = some R)
    (hnd : (R.vers.map (·.node)).Nodup) {w : Version V} (hw : w ∈ R.vers) :
    S.versionAt r w.node = some w := by
  unfold Stream.versionAt
  rw [hR]
  exact find?_node_of_mem hnd hw rfl

theorem versionAt_append_left {S S₂ : Stream V T} {r : Nat} (hr : r < S.length) (y : NodeId) :
    (S ++ S₂).versionAt r y = S.versionAt r y := by
  unfold Stream.versionAt
  rw [List.getElem?_append_left hr]

theorem versionAt_ge_length {S : Stream V T} {r : Nat} (hr : S.length ≤ r) (y : NodeId) :
    S.versionAt r y = none := by
  unfold Stream.versionAt
  rw [List.getElem?_eq_none hr]

theorem versionAt_cons_zero (R : Record V T) (S : Stream V T) (x : NodeId) :
    Stream.versionAt (R :: S) 0 x = R.vers.find? (fun v => v.node == x) := rfl

theorem versionAt_cons_succ (R : Record V T) (S : Stream V T) (r : Nat) (x : NodeId) :
    Stream.versionAt (R :: S) (r + 1) x = Stream.versionAt S r x := rfl

theorem lv_cons (R : Record V T) (S : Stream V T) (x : NodeId) :
    Stream.lv (R :: S) x = (S.lv x).or (R.vers.find? (fun v => v.node == x)) := by
  simp [Stream.lv]

theorem lv_append (S S₂ : Stream V T) (x : NodeId) :
    (S ++ S₂).lv x = (S₂.lv x).or (S.lv x) := by
  simp [Stream.lv, List.reverse_append, List.findSome?_append]

theorem lv_nil (x : NodeId) : Stream.lv ([] : Stream V T) x = none := rfl

theorem lv_eq_none_iff (S : Stream V T) (x : NodeId) :
    S.lv x = none ↔ ∀ r, S.versionAt r x = none := by
  induction S with
  | nil => simp [lv_nil, Stream.versionAt]
  | cons R S ih =>
    rw [lv_cons, Option.or_eq_none_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ r
      cases r with
      | zero => simp [Stream.versionAt, h2]
      | succ r => simpa [Stream.versionAt] using h1 r
    · intro h
      refine ⟨fun r => ?_, ?_⟩
      · have := h (r + 1)
        simpa [Stream.versionAt] using this
      · have := h 0
        simpa [Stream.versionAt] using this

theorem lv_eq_some_iff (S : Stream V T) (x : NodeId) : ∀ (v : Version V),
    S.lv x = some v ↔ ∃ r, S.versionAt r x = some v ∧ ∀ r', r < r' → S.versionAt r' x = none := by
  induction S with
  | nil => simp [lv_nil, Stream.versionAt]
  | cons R S ih =>
    intro v
    rw [lv_cons]
    cases hS : Stream.lv S x with
    | some u =>
      simp only [Option.some_or, Option.some.injEq]
      obtain ⟨r, hr1, hr2⟩ := (ih u).mp hS
      constructor
      · rintro rfl
        refine ⟨r + 1, by simpa [Stream.versionAt] using hr1, fun r' hr' => ?_⟩
        cases r' with
        | zero => omega
        | succ r' => simpa [Stream.versionAt] using hr2 r' (by omega)
      · rintro ⟨r0, h1, h2⟩
        cases r0 with
        | zero =>
          have := h2 (r + 1) (by omega)
          rw [versionAt_cons_succ, hr1] at this
          simp at this
        | succ r0 =>
          have h1' : Stream.versionAt S r0 x = some v := by simpa [Stream.versionAt] using h1
          have : Stream.lv S x = some v := (ih v).mpr ⟨r0, h1', fun r' hr' => by
            simpa [Stream.versionAt] using h2 (r' + 1) (by omega)⟩
          rw [hS] at this
          exact Option.some.inj this
    | none =>
      simp only [Option.none_or]
      have hall := (lv_eq_none_iff S x).mp hS
      constructor
      · intro h
        refine ⟨0, by simpa [Stream.versionAt] using h, fun r' hr' => ?_⟩
        cases r' with
        | zero => omega
        | succ r' => simpa [Stream.versionAt] using hall r'
      · rintro ⟨r0, h1, -⟩
        cases r0 with
        | zero => simpa [Stream.versionAt] using h1
        | succ r0 =>
          have : Stream.versionAt S r0 x = some v := by simpa [Stream.versionAt] using h1
          rw [hall r0] at this
          simp at this

/-- The latest version is found in its record. -/
theorem lv_versionAt {S : Stream V T} {x : NodeId} {v : Version V} (h : S.lv x = some v) :
    ∃ r, S.versionAt r x = some v := by
  obtain ⟨r, h1, -⟩ := (lv_eq_some_iff S x v).mp h
  exact ⟨r, h1⟩

/-- The stream extends: every record of S is in S', with the same versions
first (the record under construction may get more versions). -/
def SExt (S S' : Stream V T) : Prop :=
  ∀ (r : Nat) (R : Record V T), S[r]? = some R → ∃ R' : Record V T, S'[r]? = some R' ∧ R.vers <+: R'.vers

theorem SExt.refl (S : Stream V T) : SExt S S := fun _ R h => ⟨R, h, List.prefix_refl _⟩

theorem SExt.trans {S S' S'' : Stream V T} (h : SExt S S') (h' : SExt S' S'') : SExt S S'' := by
  intro r R hR
  obtain ⟨R', h1, h2⟩ := h r R hR
  obtain ⟨R'', h1', h2'⟩ := h' r R' h1
  exact ⟨R'', h1', h2.trans h2'⟩

theorem SExt.append (S S₂ : Stream V T) : SExt S (S ++ S₂) := by
  intro r R hR
  have hr : r < S.length := by
    rcases Nat.lt_or_ge r S.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hR; simp at hR
  exact ⟨R, by rw [List.getElem?_append_left hr]; exact hR, List.prefix_refl _⟩

theorem SExt.versionAt {S S' : Stream V T} (h : SExt S S') {r : Nat} {y : NodeId}
    {w : Version V} (hw : S.versionAt r y = some w) : S'.versionAt r y = some w := by
  unfold Stream.versionAt at hw ⊢
  split at hw
  · rename_i R hR
    obtain ⟨R', h1, h2⟩ := h r R hR
    rw [h1]
    exact h2.find?_eq_some hw
  · simp at hw

/-- A record under construction with versions vs, extended by more versions,
or completed. -/
theorem SExt.building {S : Stream V T} {vs vs' : List (Version V)} (h : vs <+: vs') :
    SExt (S.building vs) (S.building vs') := by
  intro r R hR
  unfold Stream.building at hR ⊢
  rcases Nat.lt_or_ge r S.length with hr | hr
  · rw [List.getElem?_append_left hr] at hR
    exact ⟨R, by rw [List.getElem?_append_left hr]; exact hR, List.prefix_refl _⟩
  · rw [List.getElem?_append_right hr] at hR ⊢
    have : r - S.length = 0 := by
      cases h' : r - S.length with
      | zero => rfl
      | succ k => rw [h'] at hR; simp at hR
    rw [this] at hR ⊢
    simp at hR
    subst hR
    exact ⟨_, rfl, h⟩

theorem SExt.building_complete {S : Stream V T} {vs : List (Version V)} (R : Record V T)
    (h : R.vers = vs) : SExt (S.building vs) (S ++ [R]) := by
  intro r R0 hR
  unfold Stream.building at hR
  rcases Nat.lt_or_ge r S.length with hr | hr
  · rw [List.getElem?_append_left hr] at hR
    exact ⟨R0, by rw [List.getElem?_append_left hr]; exact hR, List.prefix_refl _⟩
  · rw [List.getElem?_append_right hr] at hR
    have : r - S.length = 0 := by
      cases h' : r - S.length with
      | zero => rfl
      | succ k => rw [h'] at hR; simp at hR
    rw [this] at hR
    simp at hR
    subst hR
    refine ⟨R, ?_, by simp [h]⟩
    rw [List.getElem?_append_right hr, this]
    simp

/-- The latest version, in a stream under construction. -/
theorem lv_building (S : Stream V T) (vs : List (Version V)) (x : NodeId) :
    (S.building vs).lv x = (vs.find? (fun v => v.node == x)).or (S.lv x) := by
  unfold Stream.building
  rw [lv_append]
  simp [Stream.lv]

theorem versionAt_building_lt {S : Stream V T} {vs : List (Version V)} {r : Nat}
    (hr : r < S.length) (y : NodeId) : (S.building vs).versionAt r y = S.versionAt r y :=
  versionAt_append_left hr y

theorem versionAt_building_eq (S : Stream V T) (vs : List (Version V)) (y : NodeId) :
    (S.building vs).versionAt S.length y = vs.find? (fun v => v.node == y) := by
  unfold Stream.versionAt Stream.building
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-! ### Good versions -/

section Good

variable [DecidableEq V]

theorem good_eq (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) (v : Version V) :
    good sp S P t v =
      ((match P.get? v.node with
        | some n => v.hist.upTo t == n.hist.upTo t
        | none => false) &&
      (sp.live (v.hist.upTo t)).all (fun y =>
        match v.ref? y with
        | none => false
        | some r =>
          match S.versionAt r y with
          | none => false
          | some w => if w.level < v.level then good sp S P t w else false)) := by
  rw [good]; rfl

theorem good_iff (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) (v : Version V) :
    good sp S P t v = true ↔
      (∃ n, P.get? v.node = some n ∧ v.hist.upTo t = n.hist.upTo t) ∧
      ∀ y ∈ sp.live (v.hist.upTo t), ∃ r w, v.ref? y = some r ∧ S.versionAt r y = some w ∧
        w.level < v.level ∧ good sp S P t w = true := by
  rw [good_eq, Bool.and_eq_true, List.all_eq_true]
  apply and_congr
  · split
    · rename_i n hn
      simp [hn]
    · rename_i hn
      simp [hn]
  · apply forall_congr'
    intro y
    apply imp_congr_right
    intro _
    split
    · rename_i hr
      simp [hr]
    · rename_i r hr
      split
      · rename_i hw
        simp [hr, hw]
      · rename_i w hw
        split
        · rename_i hlt
          simp [hr, hw, hlt]
        · rename_i hlt
          simp [hr, hw, hlt]

/-- A good version stays good when the stream and the structure grow:
versions never change, and the past of P never changes (5.1, stability). -/
theorem good_mono (sp : Spec V T) {S S' : Stream V T} {P P' : Struct V} {k t : Time}
    (hS : SExt S S') (hP : Grow P k P') (ht : t ≤ k) :
    ∀ (b : Nat) (v : Version V), v.level < b → good sp S P t v = true →
      good sp S' P' t v = true := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb hg
    rw [good_iff] at hg ⊢
    obtain ⟨⟨n, hn, hh⟩, hc⟩ := hg
    obtain ⟨n', hn', -, -, hh'⟩ := hP _ _ hn
    refine ⟨⟨n', hn', ?_⟩, ?_⟩
    · rw [hh, upTo_eq_of_le ht hh']
    · intro y hy
      obtain ⟨r, w, h1, h2, h3, h4⟩ := hc y hy
      exact ⟨r, w, h1, hS.versionAt h2, h3, ih w (by omega) h4⟩

theorem good_mono' (sp : Spec V T) {S S' : Stream V T} {P P' : Struct V} {k t : Time}
    (hS : SExt S S') (hP : Grow P k P') (ht : t ≤ k) {v : Version V}
    (hg : good sp S P t v = true) : good sp S' P' t v = true :=
  good_mono sp hS hP ht (v.level + 1) v (by omega) hg

/-- `good` only looks at P through its nodes. -/
theorem SameNodes.good {sp : Spec V T} {S : Stream V T} {P P' : Struct V} (h : SameNodes P P')
    (t : Time) (v : Version V) : SIS.good sp S P t v = SIS.good sp S P' t v := by
  have key : ∀ (b : Nat) (v : Version V), v.level < b →
      (SIS.good sp S P t v = true ↔ SIS.good sp S P' t v = true) := by
    intro b
    induction b with
    | zero => intro v h; omega
    | succ b ih =>
      intro v hb
      rw [good_iff, good_iff, h v.node]
      apply and_congr Iff.rfl
      apply forall_congr'
      intro y
      apply imp_congr_right
      intro _
      constructor
      · rintro ⟨r, w, h1, h2, h3, h4⟩
        exact ⟨r, w, h1, h2, h3, (ih w (by omega)).mp h4⟩
      · rintro ⟨r, w, h1, h2, h3, h4⟩
        exact ⟨r, w, h1, h2, h3, (ih w (by omega)).mpr h4⟩
  exact Bool.eq_iff_iff.mpr (key (v.level + 1) v (by omega))

/-! ### Dirty nodes -/

theorem dirty_false_iff (sp : Spec V T) (S : Stream V T) (P : Struct V) (i : Time) (x : NodeId) :
    dirty sp S P i x = false ↔
      ∃ v, S.lv x = some v ∧ ∀ t ≤ i, reachable sp P t x = true → good sp S P t v = true := by
  unfold dirty
  split
  · rename_i h
    simp [h]
  · rename_i v h
    simp only [h, Option.some.injEq, exists_eq_left', List.any_eq_false, List.mem_range,
      Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false]
    constructor
    · intro hh t ht hr
      exact hh t (by omega) hr
    · intro hh t ht hr
      exact hh t (by omega) hr

theorem SameNodes.dirty {sp : Spec V T} {S : Stream V T} {P P' : Struct V} (h : SameNodes P P')
    (i : Time) (x : NodeId) : SIS.dirty sp S P i x = SIS.dirty sp S P' i x := by
  unfold SIS.dirty
  split
  · rfl
  · rename_i v _
    apply List.any_congr rfl
    intro t
    rw [h.reachable t x, h.good t v]

end Good

end SIS
