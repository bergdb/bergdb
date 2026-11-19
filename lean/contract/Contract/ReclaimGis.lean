/-
The contract package (bergdb 030-23, sections 4.2 and 5.1): the invariant
GIS-J, found by running, and that it gives `CutOK`'s part 2, the open half of
T-SCHEME (`TSchemeReads`).

GIS's I holds of a version at c or later that is at or after a version of its
node that is good at a time from e to k at which the node is reachable
(`GisI`). GIS-J's J holds of a version with I, or of a version that Rule A put
back, still in D, at c or later, whose live children lead by Rule R to
versions with J (`GisJ`). Its three clauses (`GisClauses`) say, in the state
after k and at every time t from the first available time to k: the latest
version of every node reachable at t has J; a version with I not put back in
D leads, for each child live at t, to versions with I (every version of the
child at or after the record it names); and one with I that is in D leads by
Rule R to versions with J.

`reads_of_gis`: in a reached state, every version that a read may follow
(`ReadsPhys`) has J, so it is at c or later. `TSchemeGis` is T-SCHEME through
GIS-J, a definition: for runs with A6', RC gives GIS-J's clauses; with it,
`tschemeReads_of_gis` gives `TSchemeReads`.
-/
import Contract.ReclaimScheme

namespace Contract

open SIS (Spec Algo DB Version reachable good follow lastSp lastFa run ReadsPhys RunOK javaTest)

variable {V T : Type} [DecidableEq V]

/-- A version w of node w.node is at or after one of its node's versions that
is good for a time t' of [e, k] at which the node is reachable, in the state db
(bergdb 030-23, section 4.2, GIS's threshold). -/
def AfterGood (sp : Spec V T) (db : DB V T) (e k : Nat) (w : Version V) : Prop :=
  ∃ t' r g, e ≤ t' ∧ t' ≤ k ∧ reachable sp db.P t' w.node = true ∧
    db.S.versionAt r w.node = some g ∧ r ≤ w.recNo ∧ good sp db.S db.P t' g = true

/-- GIS's I: at c or later, and after a good version (bergdb 030-23, 4.2). -/
def GisI (sp : Spec V T) (db : DB V T) (c e k : Nat) (w : Version V) : Prop :=
  c ≤ w.recNo ∧ AfterGood sp db e k w

/-- GIS-J's J at time t: I, or a version that Rule A put back and that is
still in D, at c or later, whose children live at t lead by Rule R to
versions with J. -/
inductive GisJ (sp : Spec V T) (db : DB V T) (c e k t : Nat) : Version V → Prop
  | ofI (w : Version V) : GisI sp db c e k w → GisJ sp db c e k t w
  | putBack (w : Version V) : (w.node, w.recNo) ∈ db.D → c ≤ w.recNo →
      (∀ y ∈ sp.live (w.hist.upTo t), ∀ u, follow db.S (lastSp db.S) true y (w.ref? y) = some u →
        GisJ sp db c e k t u) → GisJ sp db c e k t w

/-- GIS-J's three clauses in the state db after k, at every time t from the
first available time to k (bergdb 030-23, section 4.2): (i) the latest version
of every node reachable at t has J; (ii) a version of the stream with I that is
not put back in D leads, for each child live at t, to versions with I: every
version of the child at or after the record it names; (iii) one with I that is
in D leads by Rule R to versions with J. -/
def GisClauses (sp : Spec V T) (db : DB V T) (c e k : Nat) : Prop :=
  ∀ t, lastFa db.S ≤ t → t ≤ k →
    (∀ x w, reachable sp db.P t x = true → db.S.lv x = some w → GisJ sp db c e k t w) ∧
    (∀ r w, db.S.versionAt r w.node = some w → GisI sp db c e k w → (w.node, w.recNo) ∉ db.D →
      ∀ y ∈ sp.live (w.hist.upTo t), ∀ r' u, db.S.versionAt r' y = some u →
        (∀ r0, w.ref? y = some r0 → r0 ≤ r') → GisI sp db c e k u) ∧
    (∀ r w, db.S.versionAt r w.node = some w → GisI sp db c e k w → (w.node, w.recNo) ∈ db.D →
      ∀ y ∈ sp.live (w.hist.upTo t), ∀ u, follow db.S (lastSp db.S) true y (w.ref? y) = some u →
        GisJ sp db c e k t u)

/-- A version with J is at c or later. -/
theorem GisJ.le {sp : Spec V T} {db : DB V T} {c e k t : Nat} {w : Version V}
    (h : GisJ sp db c e k t w) : c ≤ w.recNo := by
  cases h with
  | ofI _ hI => exact hI.1
  | putBack _ _ hc _ => exact hc

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- In a reached state, a pointer of a version of the stream that Rule R
follows leads to a version of the child at or after the record that the
pointer names: the newest version in the section is at or after every version
of the child, and the version at the record named exists. -/
theorem follow_ge (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k : Nat}
    (hk : k ≤ ts.length) {r : Nat} {v : Version V}
    (hv : (run sp al (ts.take k)).S.versionAt r v.node = some v) {y : NodeId} {u : Version V}
    (hf : follow (run sp al (ts.take k)).S (lastSp (run sp al (ts.take k)).S) true y (v.ref? y) =
      some u) :
    ∃ r', (run sp al (ts.take k)).S.versionAt r' y = some u ∧
      ∀ r0, v.ref? y = some r0 → r0 ≤ r' := by
  have hinv := SIS.inv_st sp al ts hok (SIS.algOK_of sp al (Or.inl hj)) k hk
  cases hn : SIS.newest (run sp al (ts.take k)).S (lastSp (run sp al (ts.take k)).S) y with
  | some w =>
    rw [SIS.follow_newest hn, Option.some.injEq] at hf
    subst hf
    cases hr : v.ref? y with
    | none =>
      obtain ⟨r', -, hr'⟩ := SIS.newest_some hn
      exact ⟨r', hr', fun r0 h => by cases h⟩
    | some r0 =>
      obtain ⟨u0, hu0⟩ := hinv.ref_versionAt hv hr
      obtain ⟨r', -, hr', hle⟩ := SIS.newest_ge hn hu0
      refine ⟨r', hr', fun r1 h => ?_⟩
      rw [Option.some.injEq] at h
      omega
  | none =>
    cases hr : v.ref? y with
    | none =>
      rw [hr] at hf
      unfold follow at hf
      simp [hn] at hf
    | some r0 =>
      rw [hr, SIS.follow_old hn] at hf
      exact ⟨r0, hf, fun r1 h => by rw [Option.some.injEq] at h; omega⟩

/-- GIS-J gives part 2 (section 5.1): in a reached state, every version that a
read may follow has J, so it is at c or later. -/
theorem reads_of_gis (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {c e k : Nat}
    (hk : k ≤ ts.length) (hg : GisClauses sp (run sp al (ts.take k)) c e k) :
    let db := run sp al (ts.take k)
    ∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P db.D t w → c ≤ w.recNo := by
  dsimp only
  intro t w hft htk hR
  have hinv := SIS.inv_st sp al ts hok (SIS.algOK_of sp al (Or.inl hj)) k hk
  obtain ⟨hi, hii, hiii⟩ := hg t hft htk
  -- Every version a read follows is a version of the stream, with J.
  have key : (∃ r, (run sp al (ts.take k)).S.versionAt r w.node = some w) ∧
      GisJ sp (run sp al (ts.take k)) c e k t w := by
    induction hR with
    | latest x v hr hlv =>
      have hva := hinv.lv_at hlv
      have hvn := (hinv.version_node hva).1
      exact ⟨⟨v.recNo, by rw [hvn]; exact hva⟩, hi x v hr hlv⟩
    | child v y w _ hy hor ih =>
      obtain ⟨⟨r, hvr⟩, hJ⟩ := ih
      -- w is a version of y in the stream.
      have hw : w.node = y ∧ ∃ r', (run sp al (ts.take k)).S.versionAt r' y = some w := by
        rcases hor with hf | ⟨-, r', hr', -⟩
        · exact SIS.follow_spec hf
        · obtain ⟨-, -, -, hwy⟩ := SIS.versionAt_spec hr'
          exact ⟨hwy, r', hr'⟩
      obtain ⟨hwn, r', hr'⟩ := hw
      refine ⟨⟨r', by rw [hwn]; exact hr'⟩, ?_⟩
      cases hJ with
      | ofI _ hI =>
        by_cases hD : (v.node, v.recNo) ∈ (run sp al (ts.take k)).D
        · rcases hor with hf | ⟨hnD, -⟩
          · exact hiii r v hvr hI hD y hy w hf
          · exact absurd hD hnD
        · apply GisJ.ofI
          rcases hor with hf | ⟨-, r1, hr1, hle⟩
          · obtain ⟨r2, hr2, hle⟩ := follow_ge hok hj hk hvr hf
            exact hii r v hvr hI hD y hy r2 w hr2 hle
          · exact hii r v hvr hI hD y hy r1 w hr1 hle
      | putBack _ hD _ hall =>
        rcases hor with hf | ⟨hnD, -⟩
        · exact hall y hy w hf
        · exact absurd hD hnD
  exact key.2.le

end

/-- T-SCHEME through GIS-J: for runs with A6', RC gives GIS-J's clauses. -/
def TSchemeGis (sp : Spec V T) (al : Algo V T) : Prop :=
  al.stillDirty = javaTest sp → al.mark = true →
  ∀ ts : List T, RunOK sp al ts → SIS.EvictRunOK sp al ts → ∀ c e k, k ≤ ts.length →
    RC sp al ts c e k → GisClauses sp (run sp al (ts.take k)) c e k

/-- T-SCHEME through GIS-J gives the open half as it stands, `TSchemeReads`:
GIS-J's clauses give part 2 (`reads_of_gis`). -/
theorem tschemeReads_of_gis {sp : Spec V T} {al : Algo V T} (h : TSchemeGis sp al) :
    TSchemeReads sp al := by
  intro hj hmk ts hok hev c e k hk hrc
  exact reads_of_gis hok hj hk (h hj hmk ts hok hev c e k hk hrc)

end Contract
