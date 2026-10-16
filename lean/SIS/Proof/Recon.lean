/-
Proofs, part 14: reading the stream with Rule R (L-OUT, L-SEC, L-RECON).
-/
import SIS.Proof.RunFacts

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Newest versions and following pointers -/

theorem newest_eq (S : Stream V T) (s : Nat) (y : NodeId) :
    newest S s y = Stream.lv (S.drop s) y := rfl

theorem versionAt_drop (S : Stream V T) (s r : Nat) (y : NodeId) :
    Stream.versionAt (S.drop s) r y = S.versionAt (s + r) y := by
  unfold Stream.versionAt
  rw [List.getElem?_drop]

theorem newest_eq_none_iff (S : Stream V T) (s : Nat) (y : NodeId) :
    newest S s y = none ↔ ∀ r, s ≤ r → S.versionAt r y = none := by
  rw [newest_eq, lv_eq_none_iff]
  constructor
  · intro h r hr
    have := h (r - s)
    rw [versionAt_drop] at this
    rwa [show s + (r - s) = r by omega] at this
  · intro h r
    rw [versionAt_drop]
    exact h _ (by omega)

theorem newest_some {S : Stream V T} {s : Nat} {y : NodeId} {w : Version V}
    (h : newest S s y = some w) : ∃ r, s ≤ r ∧ S.versionAt r y = some w := by
  rw [newest_eq] at h
  obtain ⟨r, hr⟩ := lv_versionAt h
  rw [versionAt_drop] at hr
  exact ⟨_, by omega, hr⟩

/-- A version that a pointer is followed to is a version of that node, in the stream. -/
theorem follow_spec {S : Stream V T} {s : Nat} {y : NodeId} {ref : Option Nat}
    {w : Version V} (h : follow S s true y ref = some w) :
    w.node = y ∧ ∃ r, S.versionAt r y = some w := by
  unfold follow at h
  simp only [ite_true] at h
  cases hn : newest S s y with
  | some v =>
    rw [hn] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, -, hr⟩ := newest_some hn
    obtain ⟨R, -, -, hwy⟩ := versionAt_spec hr
    exact ⟨hwy, r, hr⟩
  | none =>
    rw [hn] at h
    cases ref with
    | none => simp at h
    | some r =>
      simp only [Option.bind_some] at h
      obtain ⟨R, -, -, hwy⟩ := versionAt_spec h
      exact ⟨hwy, r, h⟩

theorem follow_newest {S : Stream V T} {s : Nat} {y : NodeId} {ref : Option Nat}
    {w : Version V} (h : newest S s y = some w) : follow S s true y ref = some w := by
  unfold follow
  simp [h]

theorem follow_old {S : Stream V T} {s : Nat} {y : NodeId} {r : Nat}
    (h : newest S s y = none) : follow S s true y (some r) = S.versionAt r y := by
  unfold follow
  simp [h]

/-- Two streams with the same versions of x have the same latest version of x. -/
theorem lv_congr_node {S S' : Stream V T} {x : NodeId}
    (h : ∀ r, S.versionAt r x = S'.versionAt r x) : S.lv x = S'.lv x := by
  cases h1 : S.lv x with
  | none =>
    have := (lv_eq_none_iff S x).mp h1
    symm
    exact (lv_eq_none_iff S' x).mpr (fun r => by rw [← h]; exact this r)
  | some v =>
    obtain ⟨r, hr1, hr2⟩ := (lv_eq_some_iff S x v).mp h1
    symm
    exact (lv_eq_some_iff S' x v).mpr ⟨r, by rw [← h]; exact hr1, fun r' hr' => by rw [← h]; exact hr2 r' hr'⟩

theorem versionAt_take (S : Stream V T) (r r' : Nat) (y : NodeId) :
    Stream.versionAt (S.take r) r' y = if r' < r then S.versionAt r' y else none := by
  unfold Stream.versionAt
  rw [List.getElem?_take]
  by_cases hr : r' < r <;> simp [hr]

theorem lv_take {S : Stream V T} {r : Nat} {y : NodeId}
    (h : ∀ r', r ≤ r' → S.versionAt r' y = none) : Stream.lv (S.take r) y = S.lv y := by
  apply lv_congr_node
  intro r'
  rw [versionAt_take]
  by_cases hr : r' < r
  · simp [hr]
  · simp only [hr, ite_false]
    exact (h r' (by omega)).symm

/-! ### Facts from the invariant -/

section Inv

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The latest version of x is found in the record its record number names. -/
theorem Inv.lv_at (hinv : Inv sp db k) {x : NodeId} {v : Version V} (h : db.S.lv x = some v) :
    db.S.versionAt v.recNo x = some v := by
  obtain ⟨r, hr⟩ := lv_versionAt h
  obtain ⟨R, hR, hv, -⟩ := versionAt_spec hr
  rw [hinv.recNo r R hR v hv]
  exact hr

theorem Inv.version_node (hinv : Inv sp db k) {r : Nat} {y : NodeId} {w : Version V}
    (h : db.S.versionAt r y = some w) :
    w.node = y ∧ w.recNo = r ∧ ∃ n, db.P.get? y = some n ∧ w.hist = n.hist.upTo r ∧
      w.level = n.level ∧ w.isData = n.isData := by
  obtain ⟨R, hR, hw, hwy⟩ := versionAt_spec h
  obtain ⟨n, hn, h1, h2, h3⟩ := hinv.vh r R hR w hw
  rw [hwy] at hn
  exact ⟨hwy, hinv.recNo r R hR w hw, n, hn, h1, h2, h3⟩

/-- A data node's version is good at every time. -/
theorem Inv.good_data (hinv : Inv sp db k) (hls : LiveSub sp) {x : NodeId} {n : Node V}
    (hn : db.P.get? x = some n) (hd : n.isData = true) {v : Version V} (hv : db.S.lv x = some v)
    (t : Time) : good sp db.S db.P t v = true := by
  obtain ⟨v', hv', hvh⟩ := hinv.dataV x n hn hd
  rw [hv] at hv'
  cases hv'
  have hvx := (hinv.version_node (hinv.lv_at hv)).1
  rw [good_iff]
  refine ⟨⟨n, by rw [hvx]; exact hn, by rw [hvh]⟩, ?_⟩
  intro y hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  rw [hvh] at he
  have := hinv.data x n hn hd e (mem_upTo.mp he).1
  rw [this] at hye
  simp at hye

/-- A node with a version is not a virtual root. -/
theorem Inv.written_of_versionAt (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (h : db.S.versionAt r x = some v) : written sp x = true := by
  cases hv : sp.virt
  · simp [written, hv]
  · obtain ⟨R, hR, hvR, hvx⟩ := versionAt_spec h
    have := (hinv.vr hv).rootNV r R hR v hvR
    rw [hvx] at this
    simp [written, this]

theorem Inv.written_of_lv (hinv : Inv sp db k) {x : NodeId} {v : Version V}
    (h : db.S.lv x = some v) : written sp x = true := by
  obtain ⟨r, hr⟩ := lv_versionAt h
  exact hinv.written_of_versionAt hr

/-- A version points to no root. -/
theorem Inv.pointee_ne_root (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (h : db.S.versionAt r x = some v) {y : NodeId} (hy : y ∈ pointees sp v.hist) : y ≠ root := by
  obtain ⟨-, -, n, hn, hvh, -⟩ := hinv.version_node h
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap] at hy
  obtain ⟨e, he, hye⟩ := hy
  rw [hvh] at he
  exact hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye

/-- L-OUT: a latest version written before the section is good for every
time up to s at which its node is reachable. -/
theorem Inv.lout (hinv : Inv sp db k) (hls : LiveSub sp) {x : NodeId} {v : Version V}
    (hv : db.S.lv x = some v) (hs : v.recNo ≤ lastSp db.S) {t : Time} (ht : t ≤ lastSp db.S)
    (hr : reachable sp db.P t x = true) : good sp db.S db.P t v = true := by
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hv)
  cases hD : inD db.D x
  · cases hdata : n.isData
    · -- An index node outside D is clean.
      have hidx : isIndex db.P x = true := by simp [isIndex, hn, hdata]
      have hcl : dirty sp db.S db.P k x = false := by
        cases hc : dirty sp db.S db.P k x
        · rfl
        · have := hinv.inv2 x hidx (hinv.written_of_lv hv) hc; rw [hD] at this; simp at this
      rw [dirty_false_iff] at hcl
      obtain ⟨v', hv', hg⟩ := hcl
      rw [hv] at hv'; cases hv'
      exact hg t (by omega) hr
    · exact hinv.good_data hls hn hdata hv t
  · -- A node in D got dirty after s; its version was good before that.
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD
    have hsd := (sectionD_mem (hinv.inv1 ▸ hd)).1
    rcases hinv.inv3 x d v hd hv with h | h
    · omega
    · exact h t (by omega) hr

end Inv

/-! ### Good versions, read with Rule R -/

/-- Version v is good for time t when the stream is read with Rule R, from
startup pos s (6.2, step 4). -/
inductive GoodR (sp : Spec V T) (S : Stream V T) (P : Struct V) (s : Nat) (t : Time) :
    Version V → Prop
  | mk (v : Version V) (n : Node V) : P.get? v.node = some n → v.hist.upTo t = n.hist.upTo t →
      (∀ y ∈ sp.live (v.hist.upTo t), (follow S s true y (v.ref? y)).isSome) →
      (∀ y ∈ sp.live (v.hist.upTo t), ∀ w, follow S s true y (v.ref? y) = some w →
        w.level < v.level) →
      (∀ y ∈ sp.live (v.hist.upTo t), ∀ w, follow S s true y (v.ref? y) = some w →
        GoodR sp S P s t w) →
      GoodR sp S P s t v

/-- Build GoodR from one good version per child. -/
theorem GoodR.intro {sp : Spec V T} {S : Stream V T} {P : Struct V} {s : Nat} {t : Time}
    (v : Version V) (n : Node V) (hn : P.get? v.node = some n) (hc : v.hist.upTo t = n.hist.upTo t)
    (h : ∀ y ∈ sp.live (v.hist.upTo t), ∃ w, follow S s true y (v.ref? y) = some w ∧
      w.level < v.level ∧ GoodR sp S P s t w) : GoodR sp S P s t v := by
  refine GoodR.mk v n hn hc ?_ ?_ ?_
  · intro y hy
    obtain ⟨w, hw, -⟩ := h y hy
    simp [hw]
  · intro y hy w hw
    obtain ⟨w', hw', h1, -⟩ := h y hy
    rw [hw] at hw'; cases hw'; exact h1
  · intro y hy w hw
    obtain ⟨w', hw', -, h2⟩ := h y hy
    rw [hw] at hw'; cases hw'; exact h2

section Recon

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- A child of a reachable node, through a version that gives its content. -/
theorem reach_child_of_version (hinv : Inv sp db k) (hls : LiveSub sp) {t : Time}
    {v : Version V} {n : Node V} (hn : db.P.get? v.node = some n)
    (hc : v.hist.upTo t = n.hist.upTo t) (hr : reachable sp db.P t v.node = true)
    {y : NodeId} (hy : y ∈ sp.live (v.hist.upTo t)) :
    ∃ m, db.P.get? y = some m ∧ m.level < n.level ∧ reachable sp db.P t y = true ∧
      y ∈ pointees sp v.hist := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  have he' : e ∈ n.hist := by
    rw [hc] at he; exact (mem_upTo.mp he).1
  obtain ⟨m, hm, hlt⟩ := hinv.ptrs _ n hn e he' y hye
  refine ⟨m, hm, hlt, ?_, ?_⟩
  · rw [reachable_iff] at hr ⊢
    exact Reach.child hr hn (by rw [← hc]; exact hy) hm hlt
  · simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨e, (mem_upTo.mp he).1, hye⟩

/-- L-SEC, together with: a good version is good with Rule R. By induction
on the level. -/
theorem Inv.recon (hinv : Inv sp db k) (hls : LiveSub sp) :
    ∀ (b : Nat),
      (∀ r v, lastSp db.S ≤ r → db.S.versionAt r v.node = some v → v.level < b →
        ∀ t ≤ lastSp db.S, reachable sp db.P t v.node = true →
          GoodR sp db.S db.P (lastSp db.S) t v) ∧
      (∀ r v, db.S.versionAt r v.node = some v → v.level < b →
        ∀ t ≤ lastSp db.S, reachable sp db.P t v.node = true → good sp db.S db.P t v = true →
          GoodR sp db.S db.P (lastSp db.S) t v) := by
  intro b
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  induction b with
  | zero => exact ⟨fun r v _ _ h => by omega, fun r v _ h => by omega⟩
  | succ b ih =>
    obtain ⟨ihA, ihB⟩ := ih
    -- Following a pointer to a child y with Rule R gives a good version.
    have hchild : ∀ (v : Version V) (n : Node V) (t : Time), t ≤ lastSp db.S → db.P.get? v.node = some n →
        v.level = n.level → v.level < b + 1 → reachable sp db.P t v.node = true →
        v.hist.upTo t = n.hist.upTo t → ∀ y ∈ sp.live (v.hist.upTo t),
          (∀ w', newest db.S (lastSp db.S) y = some w' → ∃ w, follow db.S (lastSp db.S) true y (v.ref? y) = some w ∧
            w.level < v.level ∧ GoodR sp db.S db.P (lastSp db.S) t w) := by
      intro v n t ht hn hlev hb hr hc y hy w' hw'
      obtain ⟨m, hm, hlt, hry, -⟩ := reach_child_of_version hinv hls hn hc hr hy
      obtain ⟨r', hr', hw'r⟩ := newest_some hw'
      obtain ⟨hw'y, -, m', hm', -, hlev', -⟩ := hinv.version_node hw'r
      rw [hm] at hm'; cases hm'
      refine ⟨w', follow_newest hw', by omega, ?_⟩
      exact ihA r' w' hr' (by rw [hw'y]; exact hw'r) (by omega) t ht (by rw [hw'y]; exact hry)
    refine ⟨?_, ?_⟩
    · -- L-SEC: a version in the section.
      intro r v hr hv hb t ht hreach
      obtain ⟨-, hrec, n, hn, hvh, hlev, -⟩ := hinv.version_node hv
      have hc : v.hist.upTo t = n.hist.upTo t := by rw [hvh, upTo_upTo _ (by omega)]
      refine GoodR.intro v n hn hc ?_
      intro y hy
      cases hnw : newest db.S (lastSp db.S) y with
      | some w' => exact hchild v n t ht hn hlev hb hreach hc y hy w' hnw
      | none =>
        obtain ⟨m, hm, hlt, hry, hyp⟩ := reach_child_of_version hinv hls hn hc hreach hy
        have hnone := (newest_eq_none_iff db.S (lastSp db.S) y).mp hnw
        -- The reference names the latest version of y.
        obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
        obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
        have hpre_none : pre.find? (fun w => w.node == y) = none := by
          rw [List.find?_eq_none]
          intro w hw hwy
          have hwR : w ∈ R.vers := hpre.subset hw
          have := hnone r hr
          rw [← (show w.node = y by simpa using hwy)] at this
          rw [versionAt_of_mem hR (hinv.versNodup r R hR) hwR] at this
          simp at this
        have hlvy : Stream.lv (Stream.building (db.S.take r) pre) y = db.S.lv y := by
          rw [lv_building, hpre_none, Option.none_or]
          exact lv_take (fun r' hr' => hnone r' (by omega))
        rw [href y, ite_eq_left_iff.mpr (fun h => absurd hyp h), hlvy]
        cases hly : db.S.lv y with
        | none =>
          exfalso
          -- y has no version: it is dirty, in D after s, and not reachable before then.
          have hidx : isIndex db.P y = true := by
            cases hd : m.isData
            · simp [isIndex, hm, hd]
            · obtain ⟨v', hv', -⟩ := hinv.dataV y m hm hd
              rw [hly] at hv'; simp at hv'
          have hdirty : dirty sp db.S db.P k y = true := by simp [dirty, hly]
          obtain ⟨d, hd⟩ := (inD_iff _ _).mp (hinv.inv2 y hidx
            (written_of_ne_root sp (hinv.pointee_ne_root hv hyp)) hdirty)
          have hsd := (sectionD_mem (hinv.inv1 ▸ hd)).1
          have := hinv.inv4 y d hd hly t (by omega)
          rw [hry] at this; simp at this
        | some u =>
          have hu := hinv.lv_at hly
          have hus : u.recNo ≤ lastSp db.S := by
            cases Nat.lt_or_ge u.recNo (lastSp db.S) with
            | inl h => exact Nat.le_of_lt h
            | inr h => have := hnone u.recNo h; rw [hu] at this; simp at this
          obtain ⟨huy, -, m', hm', -, hlevu, -⟩ := hinv.version_node hu
          rw [hm] at hm'; cases hm'
          refine ⟨u, ?_, by omega, ?_⟩
          · simp only [Option.map_some]
            rw [follow_old hnw]
            exact hu
          · exact ihB u.recNo u (by rw [huy]; exact hu) (by omega) t ht (by rw [huy]; exact hry)
              (hinv.lout hls hly hus ht hry)
    · -- A good version is good with Rule R.
      intro r v hv hb t ht hreach hg
      obtain ⟨-, -, n, hn, -, hlev, -⟩ := hinv.version_node hv
      rw [good_iff] at hg
      obtain ⟨⟨n', hn', hc⟩, hch⟩ := hg
      rw [hn] at hn'; cases hn'
      refine GoodR.intro v n hn hc ?_
      intro y hy
      cases hnw : newest db.S (lastSp db.S) y with
      | some w' => exact hchild v n t ht hn hlev hb hreach hc y hy w' hnw
      | none =>
        obtain ⟨m, hm, hlt, hry, -⟩ := reach_child_of_version hinv hls hn hc hreach hy
        obtain ⟨r', w, h1, h2, h3, h4⟩ := hch y hy
        obtain ⟨hwy, -, -⟩ := hinv.version_node h2
        refine ⟨w, by rw [h1, follow_old hnw]; exact h2, h3, ?_⟩
        exact ihB r' w (by rw [hwy]; exact h2) (by omega) t ht (by rw [hwy]; exact hry) h4

end Recon

end SIS
