import SIS.Tree.Read

namespace SIS.Tree

/-- The segment-length shape, independently of compare-value encoding. -/
def keyShape : Key → Bool
  | [] => false
  | [c] => segLen c != 7
  | c :: r => segLen c == 7 && keyShape r

theorem keyWf_singleton (c : Nat) :
    keyWf [c] = true ↔ c < 2^62 ∧ c % 8 = 0 ∧ segLen c ≠ 7 := by
  simp only [keyWf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne]
  simp only [and_assoc]

theorem keyWf_cons_cons (c d : Nat) (rest : Key) :
    keyWf (c :: d :: rest) = true ↔
      c < 2^62 ∧ c % 8 = 0 ∧ segLen c = 7 ∧ keyWf (d :: rest) = true := by
  simp only [keyWf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [and_assoc]

theorem keyWf_shape (key : Key) (hw : keyWf key = true) : keyShape key = true := by
  induction key with
  | nil => cases hw
  | cons c rest ih =>
    cases rest with
    | nil => simpa only [keyShape, bne_iff_ne] using ((keyWf_singleton c).mp hw).2.2
    | cons d rest =>
      obtain ⟨_, _, hlen, htail⟩ := (keyWf_cons_cons c d rest).mp hw
      simp only [keyShape, hlen, beq_self_eq_true, Bool.true_and]
      exact ih htail

theorem keyWf_segment_encoding (key : Key) (hw : keyWf key = true) :
    ∀ c ∈ key, c < 2^62 ∧ c % 8 = 0 := by
  induction key with
  | nil => cases hw
  | cons c rest ih =>
    cases rest with
    | nil =>
      intro d hd
      have he : d = c := by simpa only [List.mem_singleton] using hd
      subst d
      exact ⟨((keyWf_singleton c).mp hw).1, ((keyWf_singleton c).mp hw).2.1⟩
    | cons d rest =>
      obtain ⟨hbound, halign, _, htail⟩ := (keyWf_cons_cons c d rest).mp hw
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hbound, halign⟩
      · exact ih htail e he

/-- Every encoded segment lies strictly between the scan's sentinels. -/
theorem keyWf_segment_sentinels (key : Key) (hw : keyWf key = true)
    (c : Nat) (hc : c ∈ key) : cvLo < (c : Int) ∧ (c : Int) < cvHi := by
  have hb := (keyWf_segment_encoding key hw c hc).1
  change c < 4611686018427387904 at hb
  change -1 < (c : Int) ∧ (c : Int) < 9223372036854775807
  omega

end SIS.Tree
