/-
Proofs about what reclaim's rewrites cover without a touch of a key range
(bergdb 024-07, section 4).

Until 024-07 a reclaim step of Java touched every index node of its key range,
so that each got a version after the iteration's start (`Changes.touch`; the
scheme's condition `touchCoverB` in SIS/ReclaimExample.lean). Since 024-07 a
step makes dirty only the index nodes on the paths of its own puts. What then
puts the index nodes at the cut or later is in the model already, in the
definition of a good version: a node that is not in D is clean, its latest
version is good, and a good version leads, reference by reference, to a good
version of every node below it, each in a record at or before the one above
(`Inv.good_below`). So a clean node's latest version is at or after the one
version of every data node below it (`Inv.clean_ge_data`): where the rewrites
have put the data nodes at c or later, and every index node has a data node
below it, every index node is in D or at c or later (`cover_st`). And once the
startup pos has reached the iteration's end, every node reachable from then on
has its latest version at c or later (`latest_st`).
-/
import SIS.Proof.LogicFacts
import SIS.Proof.Fresh
import SIS.Proof.HandleCutSkip
import SIS.Proof.HandleCutLater

namespace SIS

variable {V T : Type} [DecidableEq V]

section

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- A version of x that is good for t leads to a version good for t of every
node reachable from x at t, in a record at or before its own: its references
name records at or before its record (`Inv.ref_le_recNo`), and a good version's
references for its live children lead to good versions (`good_iff`). -/
theorem Inv.good_below (hinv : Inv sp db k) {t : Time} :
    ∀ (b : Nat) (r : Nat) (x : NodeId) (v : Version V) (n : Node V), n.level < b →
      db.S.versionAt r x = some v → db.P.get? x = some n → good sp db.S db.P t v = true →
      ∀ y ∈ reachFrom sp db.P t x n,
        ∃ r' w, r' ≤ r ∧ db.S.versionAt r' y = some w ∧ good sp db.S db.P t w = true := by
  intro b
  induction b with
  | zero => intro r x v n h; omega
  | succ b ih =>
    intro r x v n hb hv hn hg y hy
    rw [reachFrom_eq] at hy
    simp only [List.mem_cons, List.mem_flatMap] at hy
    rcases hy with rfl | ⟨z, hz, hy⟩
    · exact ⟨r, v, Nat.le_refl r, hv, hg⟩
    · split at hy
      · rename_i m hm
        split at hy
        · rename_i hlt
          have hvx := (hinv.version_node hv).1
          rw [good_iff] at hg
          obtain ⟨⟨n', hn', hh⟩, hc⟩ := hg
          rw [hvx, hn] at hn'
          cases hn'
          rw [← hh] at hz
          obtain ⟨r1, w1, h1, h2, -, h4⟩ := hc z hz
          have hle : r1 ≤ r := hinv.ref_le_recNo hv h1
          obtain ⟨r', w, hr', hw, hgw⟩ := ih r1 z w1 m (by omega) h2 hm h4 y hy
          exact ⟨r', w, by omega, hw, hgw⟩
        · simp at hy
      · simp at hy

/-- A written node x that is not in D and is reachable at t ≤ k has its latest
version at or after the version of every data node reachable from it at t. A
node that is not in D is clean (`Inv.clean_good`, INV-2), and a data node has
one version (`DataOnce`). -/
theorem Inv.clean_ge_data (hinv : Inv sp db k) (hls : LiveSub sp) (hdo : DataOnce db)
    {x : NodeId} (hxD : inD db.D x = false) (hxw : written sp x = true) {t : Time} (ht : t ≤ k)
    (hr : reachable sp db.P t x = true) {n : Node V} (hn : db.P.get? x = some n)
    {d : NodeId} {m : Node V} (hd : d ∈ reachFrom sp db.P t x n) (hm : db.P.get? d = some m)
    (hmd : m.isData = true) :
    ∃ v u, db.S.lv x = some v ∧ db.S.lv d = some u ∧ u.recNo ≤ v.recNo := by
  obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hxD hxw ht hr
  obtain ⟨r', w, hle, hw, -⟩ :=
    hinv.good_below (n.level + 1) v.recNo x v n (by omega) (hinv.lv_at hv) hn hg d hd
  have hlw : db.S.lv d = some w := hdo d m r' w hm hmd hw
  have hwr : w.recNo = r' := (hinv.version_node hw).2.1
  exact ⟨v, w, hv, hlw, by omega⟩

end

/-- The cover of an iteration that ends at e, with a cut at c, without a touch
of a key range (bergdb 024-07): in the state after transaction e of a run, if
every data node reachable at e has its version at c or later (the rewrites:
`rewritesB` in SIS/ReclaimExample.lean), and every written index node reachable
at e has a data node below it at e (BergDB's upward unlink at a delete leaves
no index node without a live key below it), then every written index node
reachable at e is in D or has its latest version at c or later. -/
theorem cover_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) (e c : Nat) (he : e ≤ ts.length)
    (hrw : ∀ d m, (st sp al ts e).P.get? d = some m → m.isData = true →
      reachable sp (st sp al ts e).P e d = true →
      ∃ u, (st sp al ts e).S.lv d = some u ∧ c ≤ u.recNo)
    (hlb : ∀ x n, (st sp al ts e).P.get? x = some n → n.isData = false → written sp x = true →
      reachable sp (st sp al ts e).P e x = true →
      ∃ d m, d ∈ reachFrom sp (st sp al ts e).P e x n ∧ (st sp al ts e).P.get? d = some m ∧
        m.isData = true) :
    ∀ x, isIndex (st sp al ts e).P x = true → written sp x = true →
      reachable sp (st sp al ts e).P e x = true →
      inD (st sp al ts e).D x = true ∨ ∃ v, (st sp al ts e).S.lv x = some v ∧ c ≤ v.recNo := by
  intro x hidx hxw hr
  have hinv : Inv sp (st sp al ts e) e := inv_st sp al ts hok hst e he
  have hdo : DataOnce (st sp al ts e) := dataOnce_st sp al ts hok hst e he
  cases hD : inD (st sp al ts e).D x with
  | true => exact Or.inl rfl
  | false =>
    right
    unfold isIndex at hidx
    cases hn : (st sp al ts e).P.get? x with
    | none => rw [hn] at hidx; cases hidx
    | some n =>
      rw [hn] at hidx
      have hnd : n.isData = false := by simpa using hidx
      obtain ⟨d, m, hd, hm, hmd⟩ := hlb x n hn hnd hxw hr
      have hrd : reachable sp (st sp al ts e).P e d = true :=
        (reachable_iff _ _ _ _).mpr
          (reach_of_mem_reachFrom sp _ e (n.level + 1) x n (by omega) hn
            ((reachable_iff _ _ _ _).mp hr) d hd)
      obtain ⟨u, hu, hcu⟩ := hrw d m hm hmd hrd
      obtain ⟨v, u', hv, hu', hle⟩ :=
        hinv.clean_ge_data hok.1.liveSub hdo hD hxw (Nat.le_refl e) hr hn hd hm hmd
      rw [hu] at hu'
      cases hu'
      exact ⟨v, hv, by omega⟩

/-! ## From the iteration's end on (bergdb 024-07, section 4.2)

With the cover at the iteration's end e, and the startup pos at e or later:
every node that is reachable at a time from e on has its latest version, if it
has one, at the cut c or later. Steps 1 and 5 of the scheme's argument (bergdb 001-07,
section 5) for the latest versions, now proved; the versions that a physical
read may follow besides the latest ones, and the references of D's nodes, are
still T-SCHEME's part that is checked by running. -/

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A version of a node that does not exist after T(e) is in a record after e. -/
theorem st_version_after (hok : RunOK sp al ts) (hst : AlgOK sp al) {e k : Nat} (hek : e ≤ k)
    (hk : k ≤ ts.length) {x : NodeId} (hx : (st sp al ts e).P.get? x = none) {r : Nat}
    {w : Version V} (hw : (st sp al ts k).S.versionAt r x = some w) : e < r := by
  rcases Nat.lt_or_ge e r with h | h
  · exact h
  · exfalso
    have hinve := inv_st sp al ts hok hst e (by omega)
    obtain ⟨l, hl⟩ := st_S_prefix sp al ts hek hk
    rw [← hl, versionAt_append_left (by rw [hinve.len]; omega)] at hw
    obtain ⟨-, -, n, hn, -⟩ := hinve.version_node hw
    rw [hx] at hn
    cases hn

/-- The latest version of a node in a state is at or after each of its versions
in an earlier state. -/
theorem st_lv_ge (hok : RunOK sp al ts) (hst : AlgOK sp al) {e k : Nat} (hek : e ≤ k)
    (hk : k ≤ ts.length) {x : NodeId} {r : Nat} {u v : Version V}
    (hu : (st sp al ts e).S.versionAt r x = some u) (hv : (st sp al ts k).S.lv x = some v) :
    r ≤ v.recNo := by
  have hinvk := inv_st sp al ts hok hst k hk
  have h1 := versionAt_prefix (st_S_prefix sp al ts hek hk) hu
  obtain ⟨r', u', h2, h3, hle⟩ := lv_recNo_ge h1
  rw [hv] at h3
  cases h3
  have := (hinvk.version_node h2).2.1
  omega

end

/-- From the iteration's end on: with the two premises of `cover_st` at e, the
end of an iteration with its cut at c ≤ e, in every state after T(k), e ≤ k,
whose startup pos is at e or later (the take has taken T(e)'s nodes; Java's
`startupPos >= pEnd`), every node reachable at a time t from e to k has its
latest version, if it has one, at c or later.

A node that did not exist after T(e) has its versions after e. A node that
existed then was reachable at e (no resurrection, `reach_back_st`): a data node
is at c or later by the rewrites; an index node is at c or later then, and so
later too, or was in D then (`cover_st`) with a got-dirty index at most e, and
a node of D stays in D with that index until it is written (`D_later`), while
the indexes of D are after the startup pos: so it was written after e. -/
theorem latest_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) (e k c : Nat) (hce : c ≤ e) (hek : e ≤ k) (hk : k ≤ ts.length)
    (hrw : ∀ d m, (st sp al ts e).P.get? d = some m → m.isData = true →
      reachable sp (st sp al ts e).P e d = true →
      ∃ u, (st sp al ts e).S.lv d = some u ∧ c ≤ u.recNo)
    (hlb : ∀ x n, (st sp al ts e).P.get? x = some n → n.isData = false → written sp x = true →
      reachable sp (st sp al ts e).P e x = true →
      ∃ d m, d ∈ reachFrom sp (st sp al ts e).P e x n ∧ (st sp al ts e).P.get? d = some m ∧
        m.isData = true)
    (hsp : e ≤ lastSp (st sp al ts k).S) :
    ∀ t x, e ≤ t → t ≤ k → reachable sp (st sp al ts k).P t x = true →
      ∀ v, (st sp al ts k).S.lv x = some v → c ≤ v.recNo := by
  intro t x het htk hr v hv
  have hinvk := inv_st sp al ts hok hst k hk
  have hinve := inv_st sp al ts hok hst e (by omega)
  have hvat := hinvk.lv_at hv
  cases hx : (st sp al ts e).P.get? x with
  | none =>
    have := st_version_after hok hst hek hk hx hvat
    omega
  | some n0 =>
    have hre : reachable sp (st sp al ts e).P e x = true :=
      reach_back_st hok hst hk (t - e) t (by omega) htk x hr (by simp [hx])
    have hxw : written sp x = true := hinvk.written_of_versionAt hvat
    have hcase : inD (st sp al ts e).D x = true ∨
        ∃ u, (st sp al ts e).S.lv x = some u ∧ c ≤ u.recNo := by
      cases hd : n0.isData with
      | true => exact Or.inr (hrw x n0 hx hd hre)
      | false =>
        exact cover_st sp al ts hok hst e c (by omega) hrw hlb x (by simp [isIndex, hx, hd]) hxw hre
    rcases hcase with hD | ⟨u, hu, hcu⟩
    · obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD
      have hde : d ≤ e := by
        have h1 : (x, d) ∈ sectionD (st sp al ts e).S := by rw [← hinve.inv1]; exact hd
        obtain ⟨-, h2, -⟩ := sectionD_mem h1
        have := hinve.len
        omega
      rcases D_later sp al ts hok hst hd k hek hk with h | ⟨r, w, hr1, -, hw⟩
      · have h1 : (x, d) ∈ sectionD (st sp al ts k).S := by rw [← hinvk.inv1]; exact h
        obtain ⟨h2, -, -⟩ := sectionD_mem h1
        omega
      · have := st_lv_ge hok hst (Nat.le_refl k) hk hw hv
        omega
    · have := st_lv_ge hok hst hek hk (hinve.lv_at hu) hv
      omega

end SIS
