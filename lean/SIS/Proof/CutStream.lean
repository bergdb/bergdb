/-
Proofs about reclaim, part 1 (bergdb item 001, WP R4): the stream after a cut.
What a cut keeps of a stream: every record at the cut or later, and of every
record before it, its startup pos, top, first available time, and the node and
record number of every version.
-/
import SIS.Reclaim
import SIS.Proof.Recon

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Cut

variable {c : Nat} {S : Stream V T}

theorem cutStream_length (c : Nat) (S : Stream V T) : (cutStream c S).length = S.length := by
  simp [cutStream]

theorem cutStream_getElem? (c : Nat) (S : Stream V T) (r : Nat) :
    (cutStream c S)[r]? = S[r]?.map (fun R => if r < c then R.cut else R) := by
  simp [cutStream]

theorem cutStream_getElem?_ge {r : Nat} (h : c ≤ r) : (cutStream c S)[r]? = S[r]? := by
  rw [cutStream_getElem?]
  cases S[r]? with
  | none => rfl
  | some R => simp [show ¬ r < c by omega]

theorem cutStream_getElem?_lt {r : Nat} (h : r < c) : (cutStream c S)[r]? = S[r]?.map Record.cut := by
  rw [cutStream_getElem?]
  cases S[r]? with
  | none => rfl
  | some R => simp [h]

theorem find?_stub (vs : List (Version V)) (y : NodeId) :
    (vs.map Version.stub).find? (fun v => v.node == y) = (vs.find? (fun v => v.node == y)).map Version.stub := by
  induction vs with
  | nil => rfl
  | cons a vs ih =>
    simp only [List.map_cons, List.find?_cons]
    have : (Version.stub a).node = a.node := rfl
    rw [this]
    cases a.node == y with
    | true => rfl
    | false => exact ih

theorem versionAt_cut_ge {r : Nat} (h : c ≤ r) (y : NodeId) :
    (cutStream c S).versionAt r y = S.versionAt r y := by
  unfold Stream.versionAt
  rw [cutStream_getElem?_ge h]

theorem versionAt_cut_lt {r : Nat} (h : r < c) (y : NodeId) :
    (cutStream c S).versionAt r y = (S.versionAt r y).map Version.stub := by
  unfold Stream.versionAt
  rw [cutStream_getElem?_lt h]
  cases S[r]? with
  | none => rfl
  | some R => simp only [Option.map_some]; exact find?_stub R.vers y

theorem stub_node (v : Version V) : v.stub.node = v.node := rfl
theorem stub_recNo (v : Version V) : v.stub.recNo = v.recNo := rfl
theorem stub_level (v : Version V) : v.stub.level = v.level := rfl

/-- A cut keeps the record of each version of every node. -/
theorem versionAt_cut_isSome (r : Nat) (y : NodeId) :
    ((cutStream c S).versionAt r y).isSome = (S.versionAt r y).isSome := by
  rcases Nat.lt_or_ge r c with h | h
  · rw [versionAt_cut_lt h]; cases S.versionAt r y <;> rfl
  · rw [versionAt_cut_ge h]

/-- A cut keeps the record of the latest version of every node. -/
theorem lv_cut_recNo (c : Nat) (S : Stream V T) (x : NodeId) :
    ((cutStream c S).lv x).map (·.recNo) = (S.lv x).map (·.recNo) := by
  cases hS : S.lv x with
  | none =>
    have h1 := (lv_eq_none_iff S x).mp hS
    have : (cutStream c S).lv x = none := by
      apply (lv_eq_none_iff _ x).mpr
      intro r
      have := versionAt_cut_isSome (c := c) (S := S) r x
      rw [h1 r] at this
      cases h : (cutStream c S).versionAt r x with
      | none => rfl
      | some _ => rw [h] at this; simp at this
    rw [this]
  | some v =>
    obtain ⟨r, hr, hlast⟩ := (lv_eq_some_iff S x v).mp hS
    have hc : ∃ w, (cutStream c S).versionAt r x = some w ∧ w.recNo = v.recNo := by
      rcases Nat.lt_or_ge r c with h | h
      · exact ⟨v.stub, by rw [versionAt_cut_lt h, hr]; rfl, rfl⟩
      · exact ⟨v, by rw [versionAt_cut_ge h, hr], rfl⟩
    obtain ⟨w, hw, hwr⟩ := hc
    have : (cutStream c S).lv x = some w := by
      apply (lv_eq_some_iff _ x w).mpr
      refine ⟨r, hw, fun r' hr' => ?_⟩
      have := versionAt_cut_isSome (c := c) (S := S) r' x
      rw [hlast r' hr'] at this
      cases h : (cutStream c S).versionAt r' x with
      | none => rfl
      | some _ => rw [h] at this; simp at this
    rw [this]
    simp only [Option.map_some, hwr]

theorem getLast?_cut (c : Nat) (S : Stream V T) :
    (cutStream c S).getLast? = S.getLast?.map (fun R => if S.length - 1 < c then R.cut else R) := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, cutStream_length, cutStream_getElem?]

theorem lastSp_cut (c : Nat) (S : Stream V T) : lastSp (cutStream c S) = lastSp S := by
  unfold lastSp
  rw [getLast?_cut]
  cases S.getLast? with
  | none => rfl
  | some R => simp only [Option.map_some]; split <;> rfl

theorem lastFa_cut (c : Nat) (S : Stream V T) : lastFa (cutStream c S) = lastFa S := by
  unfold lastFa
  rw [getLast?_cut]
  cases S.getLast? with
  | none => rfl
  | some R => simp only [Option.map_some]; split <;> rfl

/-- The newest version in R(s), ..., R(k) is the same after a cut at or before s. -/
theorem newest_cut {s : Nat} (h : c ≤ s) (y : NodeId) : newest (cutStream c S) s y = newest S s y := by
  rw [newest_eq, newest_eq]
  apply lv_congr_node
  intro r
  rw [versionAt_drop, versionAt_drop, versionAt_cut_ge (by omega)]

end Cut

end SIS
