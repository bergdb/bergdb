/-
The contract package (bergdb 030-17): a key node's klongs as a reader at time
t sees them (`prefixAt`, the klongs before the first time klong after t).

* Well-formed klongs stay well formed when cut at t (`klongsWf_prefixAt`,
  `fullOk_prefixAt`): W1 to W5 look only backwards, at the klongs before.
* The entries of the klongs cut at t are the entries of the whole klongs up
  to t (`entriesOf_prefixAt`, under W1: the time klongs increase, so every
  entry after the cut is after t).

So a tree that holds a node whole holds it at every time (030-14's State
note, item 3; Proof/RecoverWhole.lean).
-/
import Mathlib.Tactic
import Contract.Proof.BridgeMap

namespace Contract

open SIS (History)
open SIS.Check (BVal)

/-! ## The check of the times (W1), as steps

From Proof/NodeAlg.lean of the writer proof (bergdb 030-10), which left `main`
on 2026-11-18 (030-18); the writer proof is at the tag `writer-proof-2026-11-18`. -/

/-- The step of the check of the times (W1). -/
def tStep (acc : Bool × Option Time) (k : Klong) : Bool × Option Time :=
  match k with
  | .time t => (acc.1 && (match acc.2 with
      | some t0 => decide (t0 < t)
      | none => true), some t)
  | _ => acc

/-- The check of the first klong (W1). -/
def headOk (ks : List Klong) : Bool :=
  match ks with
  | .time _ :: _ => true
  | [] => true
  | _ => false

theorem timesOk_eq (ks : List Klong) :
    timesOk ks = (headOk ks && (ks.foldl tStep (true, none)).1) := rfl

theorem headOk_append {ks : List Klong} (hne : ks ≠ []) (l : List Klong) :
    headOk (ks ++ l) = headOk ks := by
  cases ks with
  | nil => exact absurd rfl hne
  | cons k r => cases k <;> rfl

/-! ## W2 to W5 of a prefix -/

theorem bmFold_of (ks : List Klong) (l : List Klong)
    (h : ∀ l1 b l2, l = l1 ++ Klong.del b :: l2 → bitmapOk ks l1.length (lastBitmap l1) b = true) :
    (l.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, [])).1 = true := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l k ih =>
    rw [foldl_zipIdx_snoc]
    have ih' := ih (fun l1 b l2 he => h l1 b (l2 ++ [k]) (by rw [he]; simp))
    cases k with
    | time t => exact ih'
    | key c y => exact ih'
    | del bits =>
      have h1 := (bmFold_spec ks l).1
      revert ih' h1
      generalize (l.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, [])) = F
      intro ih' h1
      simp only [bmStep, Bool.and_eq_true]
      refine ⟨ih', ?_⟩
      rw [h1]
      exact h l bits [] (by simp)

theorem fullFold_of (ks : List Klong) (l : List Klong)
    (h : ∀ l1 b l2, l = l1 ++ Klong.del b :: l2 → bmFull ks l1.length (lastBitmap l1) b = true) :
    (l.zipIdx.foldl (fun acc ki => fullStep ks acc ki.1 ki.2) (true, [])).1 = true := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l k ih =>
    rw [foldl_zipIdx_snoc]
    have ih' := ih (fun l1 b l2 he => h l1 b (l2 ++ [k]) (by rw [he]; simp))
    cases k with
    | time t => exact ih'
    | key c y => exact ih'
    | del bits =>
      have h1 := (fullFold_spec ks l).1
      revert ih' h1
      generalize (l.zipIdx.foldl (fun acc ki => fullStep ks acc ki.1 ki.2) (true, [])) = F
      intro ih' h1
      simp only [fullStep, Bool.and_eq_true]
      refine ⟨ih', ?_⟩
      rw [h1]
      exact h l bits [] (by simp)

theorem bitmapOk_prefix {p q : List Klong} {i : Nat} (hi : i ≤ p.length) {before bits : List Nat}
    (h : bitmapOk (p ++ q) i before bits = true) : bitmapOk p i before bits = true := by
  have hcv : ∀ j, j < i → cvAt (p ++ q) j = cvAt p j :=
    fun j hj => cvAt_append_left p q (by omega)
  simp only [bitmapOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨fun j hj => ⟨(h1 j hj).1, by rw [← hcv j (h1 j hj).1]; exact (h1 j hj).2⟩, h2⟩, ?_⟩
  intro j hj j' hj'
  have hji := (h1 j hj).1
  rw [← hcv j hji, ← hcv j' (by omega)]
  exact h3 j hj j' hj'

theorem bmFull_prefix {p q : List Klong} {i : Nat} (hi : i ≤ p.length) {before bits : List Nat}
    (hb : ∀ j ∈ bits, j < i) (h : bmFull (p ++ q) i before bits = true) :
    bmFull p i before bits = true := by
  have hcv : ∀ j, j < i → cvAt (p ++ q) j = cvAt p j :=
    fun j hj => cvAt_append_left p q (by omega)
  simp only [bmFull, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.mem_range,
    bne_iff_ne, ne_eq] at h ⊢
  intro j hj
  rcases h j hj with h1 | h1
  · exact Or.inl h1
  · right
    intro j' hj'
    rw [← hcv j (hb j hj), ← hcv j' hj']
    exact h1 j' hj'

theorem length_le_of_eq {p l1 l2 : List Klong} {b : List Nat} (he : p = l1 ++ Klong.del b :: l2) :
    l1.length ≤ p.length := by
  rw [he]; simp

theorem bitmapsOk_prefix {p q : List Klong} (h : bitmapsOk (p ++ q) = true) :
    bitmapsOk p = true := by
  unfold bitmapsOk at h ⊢
  apply bmFold_of
  intro l1 b l2 he
  have he' : p ++ q = l1 ++ Klong.del b :: (l2 ++ q) := by rw [he]; simp
  exact bitmapOk_prefix (length_le_of_eq he) ((bmFold_spec (p ++ q) (p ++ q)).2 h l1 b (l2 ++ q) he')

theorem fullOk_prefix {p q : List Klong} (hb : bitmapsOk (p ++ q) = true)
    (h : fullOk (p ++ q) = true) : fullOk p = true := by
  unfold fullOk at h ⊢
  unfold bitmapsOk at hb
  apply fullFold_of
  intro l1 b l2 he
  have he' : p ++ q = l1 ++ Klong.del b :: (l2 ++ q) := by rw [he]; simp
  have h2 := bitmapOk_iff ((bmFold_spec (p ++ q) (p ++ q)).2 hb l1 b (l2 ++ q) he')
  exact bmFull_prefix (length_le_of_eq he) h2.1 ((fullFold_spec (p ++ q) (p ++ q)).2 h l1 b (l2 ++ q) he')

/-! ## W1 of a prefix -/

theorem tFold_true : ∀ (l : List Klong) (a : Bool × Option Time),
    (l.foldl tStep a).1 = true → a.1 = true
  | [], _, h => h
  | k :: l, a, h => by
    rw [List.foldl_cons] at h
    have := tFold_true l _ h
    cases k with
    | time t =>
      simp only [tStep, Bool.and_eq_true] at this
      exact this.1
    | key c y => exact this
    | del b => exact this

theorem timesOk_prefix {p q : List Klong} (h : timesOk (p ++ q) = true) : timesOk p = true := by
  rw [timesOk_eq, Bool.and_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · by_cases hne : p = []
    · subst hne; rfl
    · rw [← headOk_append hne q]; exact h.1
  · rw [List.foldl_append] at h
    exact tFold_true q _ h.2

theorem klongsWf_prefix {p q : List Klong} (h : klongsWf (p ++ q) = true) : klongsWf p = true := by
  simp only [klongsWf, Bool.and_eq_true] at h ⊢
  exact ⟨timesOk_prefix h.1, bitmapsOk_prefix h.2⟩

theorem prefixAt_append (ks : List Klong) (t : Time) :
    ∃ q, ks = prefixAt ks t ++ q :=
  ⟨_, (List.takeWhile_append_dropWhile).symm⟩

theorem klongsWf_prefixAt {ks : List Klong} (h : klongsWf ks = true) (t : Time) :
    klongsWf (prefixAt ks t) = true := by
  obtain ⟨q, hq⟩ := prefixAt_append ks t
  rw [hq] at h
  exact klongsWf_prefix h

theorem fullOk_prefixAt {ks : List Klong} (hw : klongsWf ks = true) (h : fullOk ks = true)
    (t : Time) : fullOk (prefixAt ks t) = true := by
  obtain ⟨q, hq⟩ := prefixAt_append ks t
  rw [hq] at h hw
  simp only [klongsWf, Bool.and_eq_true] at hw
  exact fullOk_prefix hw.2 h

/-! ## The entries of a prefix -/

/-- The time klongs of a list increase, each after `o`. -/
def IncFrom : Option Time → List Klong → Prop
  | _, [] => True
  | o, .time x :: r => (∀ t0, o = some t0 → t0 < x) ∧ IncFrom (some x) r
  | o, _ :: r => IncFrom o r

theorem incFrom_of : ∀ (l : List Klong) (b : Bool) (o : Option Time),
    (l.foldl tStep (b, o)).1 = true → IncFrom o l
  | [], _, _, _ => trivial
  | k :: l, b, o, h => by
    rw [List.foldl_cons] at h
    cases k with
    | time x =>
      have h1 := tFold_true l _ h
      simp only [tStep, Bool.and_eq_true] at h1
      refine ⟨?_, incFrom_of l _ (some x) h⟩
      intro t0 ht0
      subst ht0
      simpa using h1.2
    | key c y => exact incFrom_of l b o h
    | del bs => exact incFrom_of l b o h

theorem incFrom_after : ∀ (l : List Klong) (t0 : Time), IncFrom (some t0) l →
    ∀ x, Klong.time x ∈ l → t0 < x
  | [], _, _, _, hx => by simp at hx
  | k :: l, t0, h, x, hx => by
    rcases List.mem_cons.mp hx with he | hl
    · subst he
      exact h.1 t0 rfl
    · cases k with
      | time y => exact lt_trans (h.1 t0 rfl) (incFrom_after l y h.2 x hl)
      | key c z => exact incFrom_after l t0 h x hl
      | del bs => exact incFrom_after l t0 h x hl

/-- Every entry of the klongs from a time after t on is after t. -/
theorem entriesFrom_after {t : Time} : ∀ (l : List Klong) (pre : List Klong) (t0 : Time)
    (before : List Nat), t < t0 → (∀ x, Klong.time x ∈ l → t < x) →
    ∀ e ∈ entriesFrom pre t0 before l, t < e.time
  | [], _, _, _, _, _, e, he => by simp [entriesFrom] at he
  | k :: l, pre, t0, before, ht0, hl, e, he => by
    have hl' : ∀ x, Klong.time x ∈ l → t < x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases k with
    | time x =>
      simp only [entriesFrom] at he
      exact entriesFrom_after l _ x before (hl x List.mem_cons_self) hl' e he
    | key c y =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ht0
      · exact entriesFrom_after l _ t0 before ht0 hl' e he
    | del bs =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ht0
      · exact entriesFrom_after l _ t0 bs ht0 hl' e he

/-- The predicate of `prefixAt`. -/
def atPred (t : Time) (k : Klong) : Bool :=
  match k with
  | .time x => decide (x ≤ t)
  | _ => true

theorem prefixAt_eq (ks : List Klong) (t : Time) : prefixAt ks t = ks.takeWhile (atPred t) := rfl

theorem entriesFrom_takeWhile {t : Time} : ∀ (l : List Klong) (pre : List Klong) (t0 : Time)
    (before : List Nat) (o : Option Time), t0 ≤ t → IncFrom o l →
    entriesFrom pre t0 before (l.takeWhile (atPred t)) = History.upTo (entriesFrom pre t0 before l) t
  | [], _, _, _, _, _, _ => rfl
  | k :: l, pre, t0, before, o, ht0, hl => by
    cases k with
    | time x =>
      by_cases hx : x ≤ t
      · have hp : atPred t (.time x) = true := by simp [atPred, hx]
        rw [List.takeWhile_cons_of_pos hp]
        simp only [entriesFrom]
        exact entriesFrom_takeWhile l _ x before (some x) hx hl.2
      · have hp : ¬ atPred t (.time x) = true := by simp [atPred, hx]
        rw [List.takeWhile_cons_of_neg hp]
        simp only [entriesFrom]
        symm
        unfold History.upTo
        rw [List.filter_eq_nil_iff]
        intro e he
        have hxt : t < x := Nat.lt_of_not_le hx
        have := entriesFrom_after l _ x before hxt
          (fun y hy => lt_trans hxt (incFrom_after l x hl.2 y hy)) e he
        simp only [decide_eq_true_eq, not_le]
        exact this
    | key c y =>
      have hp : atPred t (.key c y) = true := rfl
      rw [List.takeWhile_cons_of_pos hp]
      simp only [entriesFrom]
      unfold History.upTo
      rw [List.filter_cons_of_pos (by simpa using ht0)]
      congr 1
      exact entriesFrom_takeWhile l _ t0 before o ht0 hl
    | del bs =>
      have hp : atPred t (.del bs) = true := rfl
      rw [List.takeWhile_cons_of_pos hp]
      simp only [entriesFrom]
      unfold History.upTo
      rw [List.filter_cons_of_pos (by simpa using ht0)]
      congr 1
      exact entriesFrom_takeWhile l _ t0 bs o ht0 hl

/-- The entries of a key node's klongs as a reader at t sees them are the
entries of its klongs up to t (W1). -/
theorem entriesOf_prefixAt {ks : List Klong} (h : timesOk ks = true) (t : Time) :
    entriesOf (prefixAt ks t) = History.upTo (entriesOf ks) t := by
  rw [timesOk_eq, Bool.and_eq_true] at h
  have hi := incFrom_of ks true none h.2
  unfold entriesOf
  rw [prefixAt_eq]
  exact entriesFrom_takeWhile ks [] 0 [] none (Nat.zero_le _) hi

end Contract
