/-
Proofs for bergdb item 001, WP L2: lemma M (bergdb 011-11, M8). A
version of a node written at or after a version that is good for a time is
good for that time too; and a version cut back to a time s serves the times
up to s as the whole version does.
-/
import SIS.Proof.Recon
import SIS.Phys

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A history that agrees with itself up to a and up to c agrees up to every b
between: it has no entry in (a, c]. -/
theorem upTo_between (h : History V) {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c)
    (he : h.upTo a = h.upTo c) : h.upTo b = h.upTo c := by
  unfold History.upTo
  apply List.filter_congr
  intro e hmem
  by_cases h1 : e.time ≤ b
  · have : e.time ≤ c := Nat.le_trans h1 hbc
    simp [h1, this]
  · by_cases h2 : e.time ≤ c
    · exfalso
      have hc : e ∈ h.upTo c := mem_upTo.mpr ⟨hmem, h2⟩
      rw [← he] at hc
      have := (mem_upTo.mp hc).2
      omega
    · simp [h1, h2]

/-- A live child at some time is a pointee. -/
theorem mem_pointees_of_live {sp : Spec V T} (hls : LiveSub sp) {h : History V} {t : Time}
    {y : NodeId} (hy : y ∈ sp.live (h.upTo t)) : y ∈ pointees sp h := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, (mem_upTo.mp he).1, hye⟩

/-- If a stream has a version of y in record r, its latest version of y is in
a record at or after r. -/
theorem lv_recNo_ge {S : Stream V T} {y : NodeId} {r : Nat} {u : Version V}
    (hu : S.versionAt r y = some u) :
    ∃ r' u', S.versionAt r' y = some u' ∧ S.lv y = some u' ∧ r ≤ r' := by
  cases hl : S.lv y with
  | none =>
    have := (lv_eq_none_iff S y).mp hl r
    rw [hu] at this; simp at this
  | some u' =>
    obtain ⟨r', h1, h2⟩ := (lv_eq_some_iff S y u').mp hl
    refine ⟨r', u', h1, rfl, ?_⟩
    rcases Nat.lt_or_ge r' r with h | h
    · have := h2 r h
      rw [hu] at this; simp at this
    · exact h

/-- The record that a stream under construction holds a version in. -/
theorem versionAt_building_le {S : Stream V T} {vs : List (Version V)} {r : Nat} {y : NodeId}
    {u : Version V} (h : (S.building vs).versionAt r y = some u) : r ≤ S.length := by
  rcases Nat.lt_or_ge S.length r with hr | hr
  · rw [versionAt_ge_length (by simp [Stream.building]; omega)] at h; simp at h
  · exact hr

/-- The newest version of y in R(s), ... is in a record at or after every
record that holds a version of y. -/
theorem newest_ge {S : Stream V T} {s : Nat} {y : NodeId} {w : Version V}
    (h : newest S s y = some w) {r : Nat} {u : Version V} (hu : S.versionAt r y = some u) :
    ∃ r', s ≤ r' ∧ S.versionAt r' y = some w ∧ r ≤ r' := by
  rw [newest_eq] at h
  obtain ⟨r0, h1, h2⟩ := (lv_eq_some_iff (S.drop s) y w).mp h
  rw [versionAt_drop] at h1
  refine ⟨s + r0, by omega, h1, ?_⟩
  rcases Nat.lt_or_ge r s with hr | hr
  · omega
  · rcases Nat.lt_or_ge (s + r0) r with h3 | h3
    · exfalso
      have := h2 (r - s) (by omega)
      rw [versionAt_drop, show s + (r - s) = r by omega, hu] at this
      simp at this
    · exact h3

section Newer

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The stream as it was when a version of record r was written extends to the
whole stream. -/
theorem sext_building_take {S : Stream V T} {R : Record V T} {r : Nat} (hR : S[r]? = some R)
    {pre : List (Version V)} (hpre : pre <+: R.vers) :
    SExt (Stream.building (S.take r) pre) S := by
  have hr : r < S.length := by
    rcases Nat.lt_or_ge r S.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hR; simp at hR
  have hlen : (S.take r).length = r := by rw [List.length_take]; omega
  intro r0 R0 h0
  unfold Stream.building at h0
  rcases Nat.lt_or_ge r0 r with h | h
  · rw [List.getElem?_append_left (by omega), List.getElem?_take] at h0
    simp only [h, ite_true] at h0
    exact ⟨R0, h0, List.prefix_refl _⟩
  · rw [List.getElem?_append_right (by omega), hlen] at h0
    have h00 : r0 - r = 0 := by
      cases h' : r0 - r with
      | zero => rfl
      | succ m => rw [h'] at h0; simp at h0
    rw [h00] at h0
    simp at h0
    subst h0
    have : r0 = r := by omega
    subst this
    exact ⟨R, hR, hpre⟩

/-- The reference of a version for a pointee: the latest version of the pointee
when the version was written, in the stream before its record and the versions
before it in its record. -/
theorem Inv.ref_lv (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt r x = some v) {y : NodeId} (hy : y ∈ pointees sp v.hist) :
    ∃ pre R, db.S[r]? = some R ∧ pre <+: R.vers ∧
      v.ref? y = ((Stream.building (db.S.take r) pre).lv y).map (·.recNo) := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
  refine ⟨pre, R, hR, hpre, ?_⟩
  rw [href y]
  simp [hy]

/-- A version written in a later record than another, of the same node, names
for a common pointee a version at or after the one the other names. -/
theorem Inv.ref_mono (hinv : Inv sp db k) {r r' : Nat} {x : NodeId} {v w : Version V}
    (hv : db.S.versionAt r x = some v) (hw : db.S.versionAt r' x = some w) (hrr : r < r')
    {y : NodeId} (hyv : y ∈ pointees sp v.hist) (hyw : y ∈ pointees sp w.hist)
    {r1 : Nat} (h1 : v.ref? y = some r1) :
    ∃ r2 u', w.ref? y = some r2 ∧ db.S.versionAt r2 y = some u' ∧ r1 ≤ r2 := by
  obtain ⟨pre, R, hR, hpre, hrefv⟩ := hinv.ref_lv hv hyv
  obtain ⟨pre', R', hR', hpre', hrefw⟩ := hinv.ref_lv hw hyw
  have hS1 := sext_building_take hR hpre
  have hS2 := sext_building_take hR' hpre'
  have hr'len : r' < db.S.length := by
    rcases Nat.lt_or_ge r' db.S.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hR'; simp at hR'
  rw [h1] at hrefv
  cases hl : (Stream.building (db.S.take r) pre).lv y with
  | none => rw [hl] at hrefv; simp at hrefv
  | some u =>
    rw [hl] at hrefv
    simp only [Option.map_some, Option.some.injEq] at hrefv
    obtain ⟨r0, hr0⟩ := lv_versionAt hl
    have hr0r : r0 ≤ r := by
      have := versionAt_building_le hr0
      rw [List.length_take] at this; omega
    have hu0 := hS1.versionAt hr0
    obtain ⟨-, hur, -⟩ := hinv.version_node hu0
    -- The stream that w saw has u in record r0 < r'.
    have hu2 : (Stream.building (db.S.take r') pre').versionAt r0 y = some u := by
      rw [versionAt_building_lt (by rw [List.length_take]; omega), versionAt_take]
      simp only [show r0 < r' by omega, ite_true]
      exact hu0
    obtain ⟨r2, u', h2a, h2b, h2c⟩ := lv_recNo_ge hu2
    have hu' := hS2.versionAt h2a
    obtain ⟨-, hu'r, -⟩ := hinv.version_node hu'
    refine ⟨r2, u', ?_, hu', by omega⟩
    rw [hrefw, h2b]
    simp [hu'r]

/-- Lemma M: a version of a node written at or after a version that is good for
time t is good for t too. By induction on the level. -/
theorem Inv.newer (hinv : Inv sp db k) (hls : LiveSub sp) :
    ∀ (b : Nat) (r r' : Nat) (x : NodeId) (v w : Version V), v.level < b →
      db.S.versionAt r x = some v → db.S.versionAt r' x = some w → r ≤ r' → ∀ t,
      good sp db.S db.P t v = true → good sp db.S db.P t w = true := by
  intro b
  induction b with
  | zero => intro r r' x v w h; omega
  | succ b ih =>
    intro r r' x v w hb hv hw hrr t hg
    obtain ⟨hvx, -, n, hn, hvh, hvl, -⟩ := hinv.version_node hv
    obtain ⟨hwx, -, n', hn', hwh, hwl, -⟩ := hinv.version_node hw
    rw [hn] at hn'
    cases hn'
    rcases Nat.lt_or_ge r r' with hlt | hge
    · rw [good_iff] at hg ⊢
      obtain ⟨⟨n0, hn0, hc⟩, hch⟩ := hg
      rw [hvx, hn] at hn0
      cases hn0
      -- The history: w agrees with x's history up to t.
      have hcw : w.hist.upTo t = n.hist.upTo t := by
        rw [hwh]
        rcases Nat.lt_or_ge r' t with h' | h'
        · rw [upTo_upTo' _ (by omega)]
          rw [hvh, upTo_upTo' _ (by omega)] at hc
          exact upTo_between n.hist (by omega) (by omega) hc
        · exact upTo_upTo _ h'
      refine ⟨⟨n, by rw [hwx]; exact hn, hcw⟩, ?_⟩
      -- The children: the same ones, at newer versions.
      intro y hy
      have hy' : y ∈ sp.live (v.hist.upTo t) := by rw [hc, ← hcw]; exact hy
      obtain ⟨r1, u, h1, h2, h3, h4⟩ := hch y hy'
      obtain ⟨r2, u', h5, h6, h7⟩ := hinv.ref_mono hv hw hlt (mem_pointees_of_live hls hy')
        (mem_pointees_of_live hls hy) h1
      obtain ⟨-, -, m, hm, -, hul, -⟩ := hinv.version_node h2
      obtain ⟨-, -, m', hm', -, hu'l, -⟩ := hinv.version_node h6
      rw [hm] at hm'
      cases hm'
      refine ⟨r2, u', h5, h6, by omega, ?_⟩
      exact ih r1 r2 y u u' (by omega) h2 h6 h7 t h4
    · have : r = r' := by omega
      subst this
      rw [hv] at hw
      cases hw
      exact hg

end Newer

/-- A version cut back to time s serves every time t ≤ s as the whole version
does: the history up to t, the live children at t and the references are the
same. -/
theorem good_cutTo (sp : Spec V T) (S : Stream V T) (P : Struct V) (w : Version V)
    {s t : Time} (ht : t ≤ s) : good sp S P t (w.cutTo s) = good sp S P t w := by
  rw [good_eq, good_eq]
  have hh : (w.cutTo s).hist.upTo t = w.hist.upTo t := by
    simp only [Version.cutTo]
    exact upTo_upTo _ ht
  simp only [hh]
  rfl

end SIS
