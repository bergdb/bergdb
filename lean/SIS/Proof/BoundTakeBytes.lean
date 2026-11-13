/-
Proofs for BergDB's take with its byte limit (bergdb item 007;
SIS/BoundTakeBytes.lean). Added 2026-11-13.
-/
import SIS.BoundTakeBytes
import SIS.Proof.BoundTake
import SIS.Proof.BoundColdD

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Loop

variable (size : Record V T → Nat) (d : Nat) (pace : Nat → Nat → Bool) (nodeB maxB : Nat)
  (S : Stream V T) (D : Dirty)

/-- The take with the byte limit never asks for a startup pos before the one it
starts from. -/
theorem takeLoopB_ge : ∀ (n a taken used acc : Nat), acc < a →
    acc ≤ takeLoopB size d pace nodeB maxB S D (List.range' a n) taken used acc
  | 0, _, _, _, _, _ => by simp [takeLoopB]
  | n + 1, a, taken, used, acc, h => by
    rw [List.range'_succ]
    simp only [takeLoopB]
    split
    · split
      · exact Nat.le_trans (Nat.le_of_lt h) (takeLoopB_ge n (a + 1) _ _ a (by omega))
      · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- The first transaction a of the list is taken if the deadline or the pace
takes it and its nodes fit in the limit. -/
theorem takeLoopB_first (n a acc : Nat)
    (hdl : d ≤ S.cost size a S.length ∨ pace 0 (D.filter (fun e => e.2 == a)).length = true)
    (hfit : (D.filter (fun e => e.2 == a)).length * nodeB ≤ maxB) :
    a ≤ takeLoopB size d pace nodeB maxB S D (List.range' a (n + 1)) 0 0 acc := by
  rw [List.range'_succ]
  simp only [takeLoopB]
  split
  · split
    · exact takeLoopB_ge size d pace nodeB maxB S D n (a + 1) _ _ a (by omega)
    · rename_i h; exact absurd (by omega) h
  · rename_i h; exact absurd hdl h

end Loop

theorem cost_mono_right (size : Record V T → Nat) (S : Stream V T) (a b b' : Nat) (h : b ≤ b') :
    S.cost size a b ≤ S.cost size a b' := by
  unfold Stream.cost
  generalize S.drop a = l
  have hn : b - a ≤ b' - a := by omega
  generalize b - a = n at hn
  generalize b' - a = m at hn
  induction l generalizing n m with
  | nil => simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases m with
      | zero => omega
      | succ m =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        have := ih n m (by omega)
        omega

/-- Progress of the take with the byte limit: if the section of S is not empty,
its oldest transaction T(s + 1) is past the deadline or taken by the pace, and
its nodes fit in the limit, the take takes it: the startup pos moves. -/
theorem takePolicyB_progress (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T)
    (nodeB maxB : Nat) (S : Stream V T) (D : Dirty) (i : Time) (tr : T)
    (hne : lastSp S + 1 < S.length)
    (hdl : max (2 * sd i) (S.span size) ≤ S.cost size (lastSp S + 1) S.length ∨
      pace S D i tr 0 (D.filter (fun e => e.2 == lastSp S + 1)).length = true)
    (hfit : (D.filter (fun e => e.2 == lastSp S + 1)).length * nodeB ≤ maxB) :
    lastSp S + 1 ≤ takePolicyB size sd pace nodeB maxB S D i tr := by
  unfold takePolicyB sectionIdx
  obtain ⟨n, hn⟩ : ∃ n, S.length - 1 - lastSp S = n + 1 := ⟨S.length - 2 - lastSp S, by omega⟩
  rw [hn]
  exact takeLoopB_first size _ _ nodeB maxB S D n (lastSp S + 1) (lastSp S) hdl hfit

/-- While the span of the section is at least twice the setting, the deadline is
the span, and the oldest transaction of the section is past it: so the take
takes it if its nodes fit in the limit. -/
theorem takePolicyB_progress_span (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T)
    (nodeB maxB : Nat) (S : Stream V T) (D : Dirty) (i : Time) (tr : T)
    (hne : lastSp S + 1 < S.length) (hspan : 2 * sd i ≤ S.span size)
    (hfit : (D.filter (fun e => e.2 == lastSp S + 1)).length * nodeB ≤ maxB) :
    lastSp S + 1 ≤ takePolicyB size sd pace nodeB maxB S D i tr := by
  apply takePolicyB_progress size sd pace nodeB maxB S D i tr hne _ hfit
  left
  have : max (2 * sd i) (S.span size) = S.span size := by omega
  rw [this]
  unfold Stream.span
  exact cost_mono_right size S _ _ _ (by omega)

/-! ### When the debt fits in the limit, the take is `takePolicy` -/

theorem takeLoopB_eq (size : Record V T → Nat) (d : Nat) (pace : Nat → Nat → Bool)
    (nodeB maxB : Nat) (S : Stream V T) (D : Dirty) :
    ∀ (js : List Nat) (taken used acc : Nat),
      used + nodeB * (js.map (fun j => (D.filter (fun e => e.2 == j)).length)).sum ≤ maxB →
      takeLoopB size d pace nodeB maxB S D js taken used acc = takeLoop size d pace S D js taken acc
  | [], _, _, _, _ => by simp [takeLoopB, takeLoop]
  | j :: js, taken, used, acc, h => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add] at h
    simp only [takeLoopB, takeLoop]
    split
    · have hc : used + (D.filter (fun e => e.2 == j)).length * nodeB ≤ maxB := by
        rw [Nat.mul_comm]; omega
      simp only [hc, ↓reduceIte]
      apply takeLoopB_eq size d pace nodeB maxB S D js
      rw [Nat.mul_comm (D.filter (fun e => e.2 == j)).length nodeB]
      omega
    · rfl

/-- Over distinct indices, D's entries with each index add up to at most |D|. -/
theorem sum_count_D_le (D : Dirty) : ∀ L : List Nat, L.Nodup →
    (L.map (fun j => (D.filter (fun e => e.2 == j)).length)).sum ≤ D.length := by
  induction D with
  | nil => intro L _; simp [sum_map_const]
  | cons e D ih =>
    intro L hnd
    have h1 : L.map (fun j => ((e :: D).filter (fun e => e.2 == j)).length) =
        L.map (fun j => (if e.2 = j then 1 else 0) + (D.filter (fun e => e.2 == j)).length) := by
      apply List.map_congr_left
      intro j _
      by_cases h : e.2 = j
      · simp [h]; omega
      · simp [h]
    rw [h1, sum_map_add]
    have := sum_ite_le_one e.2 L hnd
    have := ih L hnd
    simp only [List.length_cons]
    omega

/-- In a step, the take with the byte limit is the take without it when the
debt before the step, `nodeB` bytes a node, fits in the limit. -/
theorem takePolicyB_eq_step (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (nodeB maxB : Nat) (db : DB V T) (tr : T)
    (hfit : nodeB * db.D.length ≤ maxB) :
    takePolicyB size sd pace nodeB maxB db.S (parts sp al db tr).D1 db.S.length tr =
      takePolicy size sd pace db.S (parts sp al db tr).D1 db.S.length tr := by
  unfold takePolicyB takePolicy
  apply takeLoopB_eq
  rw [Nat.zero_add]
  apply Nat.le_trans _ hfit
  apply Nat.mul_le_mul_left
  have hnd : (sectionIdx db.S (lastSp db.S)).Nodup := by
    unfold sectionIdx; exact List.nodup_range'
  have e : (sectionIdx db.S (lastSp db.S)).map
      (fun j => ((parts sp al db tr).D1.filter (fun e => e.2 == j)).length) =
      (sectionIdx db.S (lastSp db.S)).map (fun j => (db.D.filter (fun e => e.2 == j)).length) := by
    apply List.map_congr_left
    intro j hj
    simp only [sectionIdx, List.mem_range'_1] at hj
    rw [parts_D1, List.filter_append, List.length_append]
    have : ((parts sp al db tr).gd3.map (fun x => (x, db.S.length))).filter
        (fun e => e.2 == j) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      simp only [beq_iff_eq]
      omega
    rw [this]; rfl
  rw [e]
  exact sum_count_D_le db.D _ hnd

/-- T3 for BergDB's take with its byte limit, in a run where the debt before
each transaction fits in the limit: the section without its last record costs
less than 2 M. -/
theorem takeB_bound (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
    (pace : Pace V T) (nodeB maxB : Nat) (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M : Nat) (hM0 : 0 < M) (ts : List T) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hfit : ∀ j < ts.length, nodeB * (run sp al (ts.take j)).D.length ≤ maxB) :
    (run sp al ts).S.span size < 2 * M := by
  have key : ∀ j ≤ ts.length, (st sp al ts j).S.span size < 2 * M := by
    intro j
    induction j with
    | zero => intro _; rw [st_zero, init_span]; omega
    | succ j ih =>
      intro hj
      have h0 := ih (by omega)
      rw [st_succ sp al ts (by omega)]
      have hlen : (st sp al ts j).S.length = j + 1 := by
        rw [st, run_length, List.length_take]; omega
      have hk : sdTarget size (max (2 * sd (st sp al ts j).S.length) ((st sp al ts j).S.span size))
          (st sp al ts j).S ≤
          al.policy (st sp al ts j).S (parts sp al (st sp al ts j) ts[j]).D1
            (st sp al ts j).S.length ts[j] := by
        rw [hp, takePolicyB_eq_step sp al size sd pace nodeB maxB (st sp al ts j) ts[j]
          (by simpa [st] using hfit j (by omega))]
        exact takePolicy_keepsUp size sd pace _ _ _ _
      have hstep := section_step_of sp al size (st sp al ts j) ts[j] _ hk
      have hsd := hM (j + 1) (by omega) hj
      rw [hlen] at hstep
      rcases hstep with h1 | h1
      · rcases Nat.le_total (2 * sd (j + 1)) ((st sp al ts j).S.span size) with h2 | h2
        · rw [Nat.max_eq_right h2] at h1; omega
        · rw [Nat.max_eq_left h2] at h1; omega
      · omega
  have := key ts.length (Nat.le_refl _)
  rwa [st_length] at this

end SIS
