/-
Proofs about reclaim, part 5 (bergdb item 001, WP R4): what startup reads from
a stream cut safely, at the times from the first available time to the startup
pos.
-/
import SIS.Proof.CutRerun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Read

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The version of a node found in record r has record number r. -/
theorem Inv.recNo_of_versionAt (hinv : Inv sp db k) {r : Nat} {y : NodeId} {w : Version V}
    (h : db.S.versionAt r y = some w) : w.recNo = r := by
  obtain ⟨R, hR, hw, -⟩ := versionAt_spec h
  exact hinv.recNo r R hR w hw

/-- A safe cut gives the same reads from every version that lookups from f on
may read, at every time from f to the startup pos. -/
theorem Inv.readFrom_cut (hinv : Inv sp db k) {c : Nat} (hcut : CutOK sp c db k) {t : Time}
    (hft : lastFa db.S ≤ t) (hts : t ≤ lastSp db.S) {v : Version V} (hv : ReadsAt sp db.S db.P t v) :
    readFrom sp (cutStream c db.S) (lastSp db.S) true t v = readFrom sp db.S (lastSp db.S) true t v := by
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 (Nat.le_trans hft hts)
  apply SIS.readFrom_cut sp db.S hcs t (v.level + 1) v (by omega)
  intro p hp y hy hn r hr hsome
  have hpR := readFrom_readsAt sp db.S db.P t (v.level + 1) v (by omega) hv p hp
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  have hf : follow db.S (lastSp db.S) true y (p.2.ref? y) = some w := by
    rw [hr, follow_old hn]; exact hw
  have := hcut.2.1 t w hft (by omega) (ReadsAt.child p.2 y w hpR hy hf).phys
  rw [hinv.recNo_of_versionAt hw] at this
  exact this

/-- Following the reference of the latest version, or Rule R, gives the latest
version. -/
theorem Inv.follow_latest (hinv : Inv sp db k) {y : NodeId} {u : Version V} (hu : db.S.lv y = some u) :
    follow db.S (lastSp db.S) true y (some u.recNo) = some u := by
  cases hn : newest db.S (lastSp db.S) y with
  | some w => rw [follow_newest hn, ← newest_lv hn, hu]
  | none => rw [follow_old hn]; exact hinv.lv_at hu

/-- Without a virtual root: startup's read of a stream cut safely, at a time from
f to the startup pos, is the read of the whole stream. -/
theorem Inv.readAt_cut_nv (hinv : Inv sp db k) (hv : sp.virt = false) {c : Nat} (hcut : CutOK sp c db k)
    {t : Time} (hft : lastFa db.S ≤ t) (hts : t ≤ lastSp db.S) :
    readAt sp (cutStream c db.S) (lastSp db.S) true t = readAt sp db.S (lastSp db.S) true t := by
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  obtain ⟨u, hu⟩ := hinv.lv_root hv
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 (Nat.le_trans hft hts)
  obtain ⟨R, hR⟩ : ∃ R, db.S.getLast? = some R := by
    cases hl : db.S.getLast? with
    | none =>
      have : db.S = [] := List.getLast?_eq_none_iff.mp hl
      have := hinv.len; simp_all
    | some R => exact ⟨R, rfl⟩
  have htop : R.top = some (root, u.recNo) := by
    rw [hinv.top R hR]; simp [topOf, hv, hu]
  have hcr : c ≤ u.recNo := hcut.2.2.2 R root u.recNo hR htop
  have htop' : (cutStream c db.S).getLast?.bind (·.top) = some (root, u.recNo) := by
    rw [getLast?_cut, hR]
    simp only [Option.map_some, Option.bind_some]
    split <;> exact htop
  have hfu := hinv.follow_latest hu
  have hfu' : follow (cutStream c db.S) (lastSp db.S) true root (some u.recNo) = some u := by
    rw [follow_cut hcs root _ (fun _ r hr _ => by cases hr; exact hcr), hfu]
  have hReads : ReadsAt sp db.S db.P t u := ReadsAt.latest root u (reachable_root hn0 t) hu
  unfold readAt startVersion topVersion
  rw [htop', hR]
  simp only [hv, Bool.false_eq_true, ↓reduceIte, Option.bind_some, htop, hfu', hfu]
  exact hinv.readFrom_cut hcut hft hts hReads

end Read

end SIS
