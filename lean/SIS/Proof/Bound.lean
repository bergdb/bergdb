/-
Proofs for bounds, part 1 (bergdb item 007): the cost of a part of the
stream, the startup distance's target, and the startup section after a
transaction (T3).
-/
import SIS.Bound
import SIS.Proof.Util

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The cost of a part of the stream -/

section Cost

variable (size : Record V T → Nat)

theorem cost_eq_zero (S : Stream V T) {a b : Nat} (h : b ≤ a) : S.cost size a b = 0 := by
  unfold Stream.cost
  rw [Nat.sub_eq_zero_of_le h, List.take_zero]
  rfl

/-- Records after b do not change the cost of R(a), ..., R(b-1). -/
theorem cost_append_left (S L : Stream V T) (a : Nat) {b : Nat} (hb : b ≤ S.length) :
    (S ++ L).cost size a b = S.cost size a b := by
  unfold Stream.cost
  by_cases ha : a ≤ S.length
  · rw [List.drop_append_of_le_length ha,
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), List.take_zero, List.take_zero]

theorem cost_split (S : Stream V T) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    S.cost size a c = S.cost size a b + S.cost size b c := by
  unfold Stream.cost
  have hc : c - a = (b - a) + (c - b) := by omega
  rw [hc, List.take_add, List.map_append, List.sum_append, List.drop_drop]
  have hb : a + (b - a) = b := by omega
  rw [hb]

theorem cost_le_of_le (S : Stream V T) {a a' b : Nat} (h : a ≤ a') :
    S.cost size a' b ≤ S.cost size a b := by
  by_cases h' : a' ≤ b
  · rw [cost_split size S h h']; omega
  · rw [cost_eq_zero size S (by omega)]; omega

theorem cost_one (S : Stream V T) {a : Nat} (h : a < S.length) :
    S.cost size a (a + 1) = size S[a] := by
  unfold Stream.cost
  rw [List.drop_eq_getElem_cons h, Nat.add_sub_cancel_left, List.take_succ_cons, List.take_zero]
  simp

theorem sum_ge_count {m : Nat} : ∀ (l : List (Record V T)), (∀ R ∈ l, m ≤ size R) →
    l.length * m ≤ (l.map size).sum
  | [], _ => by simp
  | R :: l, h => by
    have h1 := h R (by simp)
    have h2 := sum_ge_count l (fun R' hR' => h R' (by simp [hR']))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

theorem sum_le_count {M : Nat} : ∀ (l : List (Record V T)), (∀ R ∈ l, size R ≤ M) →
    (l.map size).sum ≤ l.length * M
  | [], _ => by simp
  | R :: l, h => by
    have h1 := h R (by simp)
    have h2 := sum_le_count l (fun R' hR' => h R' (by simp [hR']))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- If every record costs at least m, R(a), ..., R(b-1) cost at least (b - a) m. -/
theorem cost_ge_count (S : Stream V T) {m a b : Nat} (hb : b ≤ S.length)
    (hm : ∀ R ∈ S, m ≤ size R) : (b - a) * m ≤ S.cost size a b := by
  unfold Stream.cost
  have hlen : ((S.drop a).take (b - a)).length = b - a := by
    rw [List.length_take, List.length_drop]; omega
  have h := sum_ge_count size ((S.drop a).take (b - a))
    (fun R hR => hm R (List.mem_of_mem_drop (List.mem_of_mem_take hR)))
  rw [hlen] at h
  exact h

/-- If every record costs at most M, R(a), ..., R(b-1) cost at most (b - a) M. -/
theorem cost_le_count (S : Stream V T) {M : Nat} (a b : Nat)
    (hM : ∀ R ∈ S, size R ≤ M) : S.cost size a b ≤ (b - a) * M := by
  unfold Stream.cost
  have hlen : ((S.drop a).take (b - a)).length ≤ b - a := by
    rw [List.length_take]; omega
  have h := sum_le_count size ((S.drop a).take (b - a))
    (fun R hR => hM R (List.mem_of_mem_drop (List.mem_of_mem_take hR)))
  exact Nat.le_trans h (Nat.mul_le_mul_right M hlen)

end Cost

/-! ### The startup distance's target -/

theorem le_foldl_max_init : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], a => by simp
  | y :: l, a => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left a y) (le_foldl_max_init l (max a y))

theorem le_foldl_max_of_mem : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | y :: l, a, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (le_foldl_max_init l (max a x))
    · exact le_foldl_max_of_mem l (max a y) x h

/-- No transaction after the target begins d or more before the end of the
stream: R(j), ..., R(i-1) cost less than d. -/
theorem sdTarget_max (size : Record V T → Nat) (d : Nat) (S : Stream V T) {j : Nat}
    (hj : sdTarget size d S < j) (hjl : j < S.length) : S.cost size j S.length < d := by
  apply Nat.lt_of_not_le
  intro hd
  have hmem : j ∈ (List.range S.length).filter
      (fun j => decide (d ≤ S.cost size j S.length)) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr hjl, by simp [hd]⟩
  have := le_foldl_max_of_mem _ 0 j hmem
  unfold sdTarget at hj
  omega

theorem sdPolicy_keepsUp (size : Record V T → Nat) (d : Nat) (al : Algo V T)
    (hp : al.policy = sdPolicy size d) : KeepsUp size d al := by
  intro S D i tr
  rw [hp]
  exact Nat.le_refl _

/-! ### The startup section after a transaction -/

theorem step_S_snoc (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (step sp al db tr).S = db.S ++ [(parts sp al db tr).R] := rfl

theorem lastSp_step (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    lastSp (step sp al db tr).S = (parts sp al db tr).s := by
  rw [step_S_snoc, lastSp_append]; rfl

/-- T3 for one transaction: after it, with a policy that keeps up with d > 0,
the startup section without its last record costs less than d. -/
theorem section_step (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (db : DB V T) (tr : T) :
    (step sp al db tr).S.cost size (lastSp (step sp al db tr).S + 1)
      ((step sp al db tr).S.length - 1) < d := by
  rw [lastSp_step]
  have hlen : (step sp al db tr).S.length - 1 = db.S.length := by
    rw [step_S_snoc, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [hlen, step_S_snoc, cost_append_left size _ _ _ (Nat.le_refl _)]
  have hs := parts_s sp al db tr
  have ht := hk db.S (parts sp al db tr).D1 db.S.length tr
  unfold startupPos at hs
  by_cases h1 : (parts sp al db tr).s + 1 < db.S.length
  · apply sdTarget_max size d db.S _ h1
    omega
  · rw [cost_eq_zero size _ (by omega)]
    exact hd

/-- The startup pos of the last record is before its end: s(k) ≤ k. -/
theorem lastSp_lt_step (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    lastSp (step sp al db tr).S < (step sp al db tr).S.length := by
  rw [lastSp_step, step_S_snoc, List.length_append, List.length_singleton, parts_s]
  unfold startupPos
  omega

/-- A run is T(0) or a run followed by one more transaction. -/
theorem run_cases (sp : Spec V T) (al : Algo V T) (ts : List T) :
    run sp al ts = init sp ∨ ∃ ts' tr, run sp al ts = step sp al (run sp al ts') tr := by
  rcases List.eq_nil_or_concat ts with h | ⟨ts', tr, h⟩
  · left; rw [h]; rfl
  · right
    refine ⟨ts', tr, ?_⟩
    rw [h, List.concat_eq_append]
    simp [run, List.foldl_append]

theorem init_S (sp : Spec V T) : ∃ R : Record V T, (init sp).S = [R] ∧ R.sp = 0 :=
  ⟨_, rfl, rfl⟩

/-- T3 for runs: after every run whose policy keeps up with d > 0, the startup
section without its last record costs less than d. -/
theorem section_run (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T) :
    (run sp al ts).S.cost size (lastSp (run sp al ts).S + 1) ((run sp al ts).S.length - 1) < d := by
  rcases run_cases sp al ts with h | ⟨ts', tr, h⟩
  · rw [h]
    obtain ⟨R, hR, _⟩ := init_S sp (T := T)
    rw [hR, cost_eq_zero size _ (by simp)]
    exact hd
  · rw [h]
    exact section_step sp al size d hd hk (run sp al ts') tr

theorem lastSp_lt_run (sp : Spec V T) (al : Algo V T) (ts : List T) :
    lastSp (run sp al ts).S < (run sp al ts).S.length := by
  rcases run_cases sp al ts with h | ⟨ts', tr, h⟩
  · rw [h]
    obtain ⟨R, hR, hsp⟩ := init_S sp (T := T)
    rw [hR]
    simp [lastSp, hsp]
  · rw [h]
    exact lastSp_lt_step sp al (run sp al ts') tr

/-- A restart keeps the stream: after a transaction, with or without a
restart, the stream is the one the transaction appended to. -/
theorem runRestarts_S_snoc (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) (p : T × Bool) :
    (runRestarts sp al (ts ++ [p])).S = (step sp al (runRestarts sp al ts) p.1).S := by
  unfold runRestarts
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  split <;> rfl

/-- T3 for runs with restarts: the same bound, with restarts after any
transactions; nothing more is assumed. -/
theorem section_runRestarts (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List (T × Bool)) :
    (runRestarts sp al ts).S.cost size (lastSp (runRestarts sp al ts).S + 1)
      ((runRestarts sp al ts).S.length - 1) < d := by
  rcases List.eq_nil_or_concat ts with h | ⟨ts', p, h⟩
  · rw [h]
    obtain ⟨R, hR, _⟩ := init_S sp (T := T)
    have h0 : (runRestarts sp al []).S = (init sp).S := rfl
    rw [h0, hR, cost_eq_zero size _ (by simp)]
    exact hd
  · rw [h, List.concat_eq_append, runRestarts_S_snoc]
    exact section_step sp al size d hd hk _ _

/-! ### From the section to what startup reads and reruns -/

section Startup

variable (size : Record V T → Nat) (S : Stream V T) {d : Nat}

/-- Startup reads R(s), ..., R(k): R(s), the section without its last record,
and R(k). -/
theorem reads_of_section (h3 : S.cost size (lastSp S + 1) (S.length - 1) < d)
    (hlt : lastSp S < S.length) :
    S.cost size (lastSp S) S.length <
      S.cost size (lastSp S) (lastSp S + 1) + d + S.cost size (S.length - 1) S.length := by
  by_cases h : lastSp S + 1 ≤ S.length - 1
  · rw [cost_split size S (Nat.le_add_right (lastSp S) 1) (Nat.le_trans h (Nat.sub_le _ 1)),
      cost_split size S h (Nat.sub_le _ 1)]
    omega
  · have he : S.length = lastSp S + 1 := by omega
    rw [he]
    omega

/-- Startup reruns T(s+1), ..., T(k): if every record costs at least m, fewer
than d / m + 1 of them, and their records cost less than d and the cost of R(k). -/
theorem rerun_of_section {m : Nat} (h3 : S.cost size (lastSp S + 1) (S.length - 1) < d)
    (hm : ∀ R ∈ S, m ≤ size R) :
    ((sectionIdx S (lastSp S)).length - 1) * m < d ∧
      S.cost size (lastSp S + 1) S.length < d + S.cost size (S.length - 1) S.length := by
  refine ⟨?_, ?_⟩
  · have hc := cost_ge_count size S (a := lastSp S + 1) (Nat.sub_le S.length 1) hm
    have hl : (sectionIdx S (lastSp S)).length - 1 = S.length - 1 - (lastSp S + 1) := by
      unfold sectionIdx
      rw [List.length_range']
      omega
    rw [hl]
    exact Nat.lt_of_le_of_lt hc h3
  · by_cases h : lastSp S + 1 ≤ S.length - 1
    · rw [cost_split size S h (Nat.sub_le _ 1)]
      exact Nat.add_lt_add_right h3 _
    · rw [cost_eq_zero size S (by omega)]
      omega

/-- With records that cost at most M: startup reads less than d + 2 M, and
reruns transactions whose records cost less than d + M. -/
theorem bounded_of_section {M : Nat} (h3 : S.cost size (lastSp S + 1) (S.length - 1) < d)
    (hlt : lastSp S < S.length) (hM : ∀ R ∈ S, size R ≤ M) :
    S.cost size (lastSp S) S.length < d + 2 * M ∧
      S.cost size (lastSp S + 1) S.length < d + M := by
  have hr := reads_of_section size S h3 hlt
  have hx := (rerun_of_section size S (m := 0) h3 (fun _ _ => Nat.zero_le _)).2
  have h1 := cost_le_count size S (lastSp S) (lastSp S + 1) hM
  have h2 := cost_le_count size S (S.length - 1) S.length hM
  have e1 : lastSp S + 1 - lastSp S = 1 := by omega
  rw [e1, Nat.one_mul] at h1
  have e2 : S.length - (S.length - 1) ≤ 1 := by omega
  have h2' : S.cost size (S.length - 1) S.length ≤ M :=
    Nat.le_trans h2 (by have := Nat.mul_le_mul_right M e2; rw [Nat.one_mul] at this; exact this)
  exact ⟨by omega, by omega⟩

end Startup

end SIS
