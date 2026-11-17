/-
The contract package (bergdb 030-07): the map from klongs to entries. The
model's live children of the entries of well-formed klongs (`blive`, with W5)
are the pointees of the live klongs (`mem_blive_entriesOf`); the entries of
klongs added are added at the end (`entriesOf_append`), with the time of
their time klong; an entry's pointer is a key klong's.
-/
import Mathlib.Tactic
import Check.Live
import Contract.Bridge
import Contract.Proof.Node

namespace Contract

open SIS (Entry History)
open SIS.Check (BVal bptrs blive bstep bout Has setAssoc LState)

/-! ## The entries of klongs put together -/

/-- The time of the last time klong of ks, t if it has none. -/
def lastTimeOr (t : Nat) (ks : List Klong) : Nat :=
  ks.foldl (fun t k => match k with
    | .time x => x
    | _ => t) t

/-- The last bitmap of ks, b if it has none. -/
def lastBmOr (b : List Nat) (ks : List Klong) : List Nat :=
  ks.foldl (fun d k => match k with
    | .del b => b
    | _ => d) b

theorem lastBitmap_eq (ks : List Klong) : lastBitmap ks = lastBmOr [] ks := rfl

theorem entriesFrom_append : ∀ (r1 pre : List Klong) (t : Nat) (b : List Nat) (r2 : List Klong),
    entriesFrom pre t b (r1 ++ r2) =
      entriesFrom pre t b r1 ++ entriesFrom (pre ++ r1) (lastTimeOr t r1) (lastBmOr b r1) r2
  | [], pre, t, b, r2 => by simp [entriesFrom, lastTimeOr, lastBmOr]
  | k :: r1, pre, t, b, r2 => by
    cases k with
    | time t' =>
      simp only [List.cons_append, entriesFrom]
      rw [entriesFrom_append r1]
      simp [lastTimeOr, lastBmOr]
    | key c y =>
      simp only [List.cons_append, entriesFrom]
      rw [entriesFrom_append r1]
      simp [lastTimeOr, lastBmOr]
    | del bits =>
      simp only [List.cons_append, entriesFrom]
      rw [entriesFrom_append r1]
      simp [lastTimeOr, lastBmOr]

/-- The entries of klongs with more klongs after them. -/
theorem entriesOf_append (ks more : List Klong) :
    entriesOf (ks ++ more) =
      entriesOf ks ++ entriesFrom ks (lastTimeOr 0 ks) (lastBitmap ks) more := by
  unfold entriesOf
  rw [entriesFrom_append]
  simp [lastBitmap_eq]

/-- Without a time klong, every entry has the time given. -/
theorem entriesFrom_time : ∀ (r pre : List Klong) (t : Nat) (b : List Nat),
    r.all (fun k => !k.isTime) = true → ∀ e ∈ entriesFrom pre t b r, e.time = t
  | [], _, _, _, _, e, he => by simp [entriesFrom] at he
  | k :: r, pre, t, b, h, e, he => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases k with
    | time t' => simp [Klong.isTime] at h
    | key c y =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact entriesFrom_time r _ t b h.2 e he
    | del bits =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact entriesFrom_time r _ t _ h.2 e he

/-- Every entry has the time given or the time of a time klong. -/
theorem entriesFrom_time_mem : ∀ (r pre : List Klong) (t : Nat) (b : List Nat),
    ∀ e ∈ entriesFrom pre t b r, e.time = t ∨ Klong.time e.time ∈ r
  | [], _, _, _, e, he => by simp [entriesFrom] at he
  | k :: r, pre, t, b, e, he => by
    cases k with
    | time t' =>
      simp only [entriesFrom] at he
      rcases entriesFrom_time_mem r _ t' b e he with h | h
      · right; rw [h]; exact List.mem_cons_self
      · right; exact List.mem_cons_of_mem _ h
    | key c y =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl rfl
      · rcases entriesFrom_time_mem r _ t b e he with h | h
        · exact Or.inl h
        · right; exact List.mem_cons_of_mem _ h
    | del bits =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl rfl
      · rcases entriesFrom_time_mem r _ t bits e he with h | h
        · exact Or.inl h
        · right; exact List.mem_cons_of_mem _ h

/-- An entry with a pointer is a key klong's. -/
theorem entriesFrom_ptr : ∀ (r pre : List Klong) (t : Nat) (b : List Nat),
    ∀ e ∈ entriesFrom pre t b r, ∀ y ∈ bptrs e.val, ∃ c, Klong.key c y ∈ r
  | [], _, _, _, e, he, _, _ => by simp [entriesFrom] at he
  | k :: r, pre, t, b, e, he, y, hy => by
    cases k with
    | time t' =>
      simp only [entriesFrom] at he
      obtain ⟨c, hc⟩ := entriesFrom_ptr r _ t' b e he y hy
      exact ⟨c, List.mem_cons_of_mem _ hc⟩
    | key c y' =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · simp only [bptrs, List.mem_singleton] at hy
        subst hy
        exact ⟨c, List.mem_cons_self⟩
      · obtain ⟨c', hc⟩ := entriesFrom_ptr r _ t b e he y hy
        exact ⟨c', List.mem_cons_of_mem _ hc⟩
    | del bits =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · simp [bptrs] at hy
      · obtain ⟨c', hc⟩ := entriesFrom_ptr r _ t bits e he y hy
        exact ⟨c', List.mem_cons_of_mem _ hc⟩

/-- An entry of a key node is a key entry or a delete entry. -/
theorem entriesFrom_kind : ∀ (r pre : List Klong) (t : Nat) (b : List Nat),
    ∀ e ∈ entriesFrom pre t b r, (∃ c y, e.val = .key c y) ∨ ∃ cs, e.val = .del cs
  | [], _, _, _, e, he => by simp [entriesFrom] at he
  | k :: r, pre, t, b, e, he => by
    cases k with
    | time t' =>
      simp only [entriesFrom] at he
      exact entriesFrom_kind r _ t' b e he
    | key c y' =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inl ⟨c, y', rfl⟩
      · exact entriesFrom_kind r _ t b e he
    | del bits =>
      simp only [entriesFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact Or.inr ⟨_, rfl⟩
      · exact entriesFrom_kind r _ t bits e he

/-! ## Lookups in the state of `blive` -/

theorem lookup_isSome_any (m : List (Nat × Option Nat)) (c : Nat) :
    (m.lookup c).isSome = m.any (fun p => p.1 == c) := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    obtain ⟨k, v⟩ := a
    rw [List.lookup_cons, List.any_cons]
    by_cases h : c = k
    · subst h; simp
    · have h1 : (c == k) = false := by simpa using h
      have h2 : (k == c) = false := by simpa using fun h' => h h'.symm
      simp [h1, h2, ih]

theorem lookup_map_set (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat) (c' : Nat) :
    (m.map (fun p => if p.1 == c then (c, v) else p)).lookup c' =
      if c' = c then (m.lookup c).map (fun _ => v) else m.lookup c' := by
  induction m with
  | nil => simp
  | cons a m ih =>
    obtain ⟨k, w⟩ := a
    simp only [List.map_cons]
    by_cases hk : k = c
    · subst hk
      simp only [beq_self_eq_true, ite_true, List.lookup_cons]
      by_cases h : c' = k
      · subst h; simp
      · have h1 : (c' == k) = false := by simpa using h
        simp only [h1, h, ite_false]
        rw [ih]
        simp [h]
    · have h2 : (k == c) = false := by simpa using hk
      simp only [h2, Bool.false_eq_true, ite_false, List.lookup_cons]
      by_cases h : c' = k
      · subst h
        have : ¬ c' = c := hk
        simp [this]
      · have h1 : (c' == k) = false := by simpa using h
        simp only [h1]
        rw [ih]
        by_cases h4 : c' = c
        · subst h4
          have h5 : (c' == k) = false := h1
          simp [h5]
        · simp [h4]

theorem lookup_setAssoc (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat) (c' : Nat) :
    (setAssoc m c v).lookup c' = if c' = c then some v else m.lookup c' := by
  unfold setAssoc
  split
  · rename_i h
    rw [lookup_map_set]
    by_cases hc : c' = c
    · simp only [hc, ite_true]
      have : (m.lookup c).isSome = true := by rw [lookup_isSome_any]; exact h
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      rw [hw]; rfl
    · simp [hc]
  · rename_i h
    rw [List.lookup_append]
    by_cases hc : c' = c
    · subst hc
      have : (m.lookup c').isSome = false := by
        rw [lookup_isSome_any]; exact (Bool.not_eq_true _).mp h
      have hn : m.lookup c' = none := by simpa using this
      simp [hn]
    · have h1 : (c' == c) = false := by simpa using hc
      simp [hc, List.lookup_cons, h1]

/-- One compare value of a delete entry. -/
def delStep (m : List (Nat × Option Nat)) (c : Nat) : List (Nat × Option Nat) :=
  if m.any (fun p => p.1 == c) then setAssoc m c none else m

theorem lookup_delStep (m : List (Nat × Option Nat)) (c c' : Nat) :
    (delStep m c).lookup c' = if c' = c then (m.lookup c).map (fun _ => none) else m.lookup c' := by
  unfold delStep
  split
  · rename_i h
    rw [lookup_setAssoc]
    by_cases hc : c' = c
    · simp only [hc, ite_true]
      have : (m.lookup c).isSome = true := by rw [lookup_isSome_any]; exact h
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
      rw [hw]; rfl
    · simp [hc]
  · rename_i h
    by_cases hc : c' = c
    · subst hc
      have : (m.lookup c').isSome = false := by
        rw [lookup_isSome_any]; exact (Bool.not_eq_true _).mp h
      have hn : m.lookup c' = none := by simpa using this
      simp [hn]
    · simp [hc]

theorem lookup_delFold (cs : List Nat) : ∀ (m : List (Nat × Option Nat)) (c' : Nat),
    (cs.foldl delStep m).lookup c' =
      if c' ∈ cs then (m.lookup c').map (fun _ => none) else m.lookup c' := by
  induction cs with
  | nil => intro m c'; simp
  | cons c cs ih =>
    intro m c'
    simp only [List.foldl_cons]
    rw [ih, lookup_delStep]
    by_cases h1 : c' = c
    · subst h1
      by_cases h2 : c' ∈ cs
      · cases List.lookup c' m <;> simp [h2]
      · simp [h2]
    · by_cases h2 : c' ∈ cs
      · simp [h1, h2]
      · simp [h1, h2]

theorem keys_setAssoc (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat)
    (h : (m.map (·.1)).Nodup) : ((setAssoc m c v).map (·.1)).Nodup := by
  unfold setAssoc
  split
  · have : (m.map (fun p => if p.1 == c then (c, v) else p)).map (·.1) = m.map (·.1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp]
      by_cases hp : p.1 = c
      · simp [hp]
      · have : (p.1 == c) = false := by simpa using hp
        simp [this]
    rw [this]; exact h
  · rename_i hn
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    intro hab
    subst hab
    apply hn
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
    exact List.any_eq_true.mpr ⟨p, hp, by simpa using hpa⟩

theorem keys_delFold (cs : List Nat) : ∀ (m : List (Nat × Option Nat)),
    (m.map (·.1)).Nodup → ((cs.foldl delStep m).map (·.1)).Nodup := by
  induction cs with
  | nil => intro m h; exact h
  | cons c cs ih =>
    intro m h
    simp only [List.foldl_cons]
    apply ih
    unfold delStep
    split
    · exact keys_setAssoc m c none h
    · exact h

theorem mem_iff_lookup {m : List (Nat × Option Nat)} (hn : (m.map (·.1)).Nodup) (c : Nat)
    (v : Option Nat) : (c, v) ∈ m ↔ m.lookup c = some v := by
  induction m with
  | nil => simp
  | cons a m ih =>
    obtain ⟨k, w⟩ := a
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.lookup_cons]
    by_cases h : c = k
    · subst h
      simp only [List.mem_cons, Prod.mk.injEq, true_and, beq_self_eq_true, Option.some.injEq]
      constructor
      · rintro (h1 | h1)
        · exact h1.symm
        · exact absurd (List.mem_map.mpr ⟨(c, v), h1, rfl⟩) hn.1
      · intro h1; exact Or.inl h1.symm
    · have h1 : (c == k) = false := by simpa using h
      simp only [List.mem_cons, Prod.mk.injEq, h, false_and, false_or, h1]
      exact ih hn.2

/-! ## The live children of the entries of klongs -/

/-- The rules of the bitmaps that the map needs: W2, W3 and W5, for every
bitmap of the klongs, with the klongs before it. -/
def WF5 (ks : List Klong) : Prop :=
  ∀ l1 b l2, ks = l1 ++ Klong.del b :: l2 →
    (∀ j ∈ b, j < l1.length) ∧ (∀ j ∈ lastBitmap l1, j ∈ b) ∧
    (∀ j ∈ b, j ∉ lastBitmap l1 → ∀ j', j' < l1.length → cvAt l1 j' = cvAt l1 j → j' ∈ b)

theorem WF5.init {l : List Klong} {k : Klong} (h : WF5 (l ++ [k])) : WF5 l :=
  fun l1 b l2 he => h l1 b (l2 ++ [k]) (by rw [he]; simp)

theorem WF5.bmW {l : List Klong} (h : WF5 l) : BmW l :=
  fun l1 b l2 he => ⟨(h l1 b l2 he).1, (h l1 b l2 he).2.1⟩

theorem cvAt_append_left (l1 l2 : List Klong) {j : Nat} (hj : j < l1.length) :
    cvAt (l1 ++ l2) j = cvAt l1 j := by
  unfold cvAt
  rw [List.getElem?_append_left hj]

/-- What the check of W5 computes, as `bmFold_spec`. -/
theorem fullFold_spec (ks : List Klong) (l : List Klong) :
    (l.zipIdx.foldl (fun acc ki => fullStep ks acc ki.1 ki.2) (true, [])).2 = lastBitmap l ∧
    ((l.zipIdx.foldl (fun acc ki => fullStep ks acc ki.1 ki.2) (true, [])).1 = true →
      ∀ l1 b l2, l = l1 ++ Klong.del b :: l2 →
        bmFull ks l1.length (lastBitmap l1) b = true) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro _ l1 b l2 he
    simp at he
  | append_singleton l k ih =>
    rw [foldl_zipIdx_snoc, lastBitmap_snoc]
    obtain ⟨ih1, ih2⟩ := ih
    cases k with
    | time t =>
      refine ⟨ih1, ?_⟩
      intro hok l1 b l2 he
      rcases snoc_eq_append_cons he with ⟨_, _, h3⟩ | ⟨l2', _, h2⟩
      · simp at h3
      · exact ih2 hok l1 b l2' h2
    | key c y =>
      refine ⟨ih1, ?_⟩
      intro hok l1 b l2 he
      rcases snoc_eq_append_cons he with ⟨_, _, h3⟩ | ⟨l2', _, h2⟩
      · simp at h3
      · exact ih2 hok l1 b l2' h2
    | del bits =>
      refine ⟨rfl, ?_⟩
      intro hok l1 b l2 he
      simp only [fullStep, Bool.and_eq_true] at hok
      rcases snoc_eq_append_cons he with ⟨_, h2, h3⟩ | ⟨l2', _, h2⟩
      · injection h3 with h3
        subst h2 h3
        rw [← ih1]
        exact hok.2
      · exact ih2 hok.1 l1 b l2' h2

/-- Well-formed klongs with W5 meet `WF5`. -/
theorem wf5_of (ks : List Klong) (hwf : klongsWf ks = true) (hfull : fullOk ks = true) :
    WF5 ks := by
  simp only [klongsWf, Bool.and_eq_true] at hwf
  have hb := (bmFold_spec ks ks).2 hwf.2
  have hf := (fullFold_spec ks ks).2 hfull
  intro l1 b l2 he
  have h1 := bitmapOk_iff (hb l1 b l2 he)
  have h2 := hf l1 b l2 he
  refine ⟨h1.1, h1.2.1, ?_⟩
  intro j hj hnb j' hj' hcv
  simp only [bmFull, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.mem_range,
    bne_iff_ne, ne_eq] at h2
  rcases h2 j hj with h3 | h3
  · exact absurd h3 hnb
  · rcases h3 j' hj' with h4 | h4
    · exfalso
      apply h4
      rw [he, cvAt_append_left _ _ hj', cvAt_append_left _ _ (h1.1 j hj)]
      exact hcv
    · exact h4

theorem mem_newCvs {pre : List Klong} {before bits : List Nat} {c : Nat} :
    c ∈ newCvs pre before bits ↔ ∃ j ∈ bits, j ∉ before ∧ cvAt pre j = some c := by
  simp only [newCvs, List.mem_mergeSort, List.mem_eraseDups, List.mem_filterMap, List.mem_filter,
    Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h3⟩; exact ⟨j, h1, h2, h3⟩
  · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, ⟨h1, h2⟩, h3⟩

/-- The state of `blive`'s fold after the entries of the klongs. -/
def stOf (ks : List Klong) : LState := (entriesOf ks).foldl bstep ([], none, none)

theorem stOf_snoc (l : List Klong) (k : Klong) :
    stOf (l ++ [k]) = match k with
      | .time _ => stOf l
      | .key c y => (setAssoc (stOf l).1 c (some y), (stOf l).2.1, (stOf l).2.2)
      | .del bits => ((newCvs l (lastBitmap l) bits).foldl delStep (stOf l).1,
          (stOf l).2.1, (stOf l).2.2) := by
  unfold stOf
  rw [entriesOf_append, List.foldl_append]
  cases k with
  | time t => simp [entriesFrom]
  | key c y => simp [entriesFrom, bstep]
  | del bits => simp [entriesFrom, bstep]; rfl

/-- The state of `blive`'s fold after the entries of klongs that meet `WF5`:
for each compare value, the pointee of its last key klong, none if the last
bitmap deletes that klong. -/
theorem stOf_spec (ks : List Klong) : WF5 ks →
    (stOf ks).2.1 = none ∧ (stOf ks).2.2 = none ∧ ((stOf ks).1.map (·.1)).Nodup ∧
    ∀ c, (stOf ks).1.lookup c = ((kc c ks.zipIdx).getLast?).map
      (fun a => if (lastBitmap ks).contains a.1 then none else some a.2) := by
  induction ks using List.reverseRecOn with
  | nil => intro _; exact ⟨rfl, rfl, List.nodup_nil, fun c => rfl⟩
  | append_singleton l k ih =>
    intro hw
    obtain ⟨i1, i2, i3, i4⟩ := ih hw.init
    have hlt := hw.init.bmW.lt_length
    have hns : l.length ∉ lastBitmap l := fun hc => by have := hlt _ hc; omega
    rw [stOf_snoc]
    cases k with
    | time t =>
      refine ⟨i1, i2, i3, ?_⟩
      intro c
      rw [i4 c, lastBitmap_snoc, kc_snoc]
      simp
    | key c0 y0 =>
      refine ⟨i1, i2, keys_setAssoc _ _ _ i3, ?_⟩
      intro c
      simp only
      rw [lookup_setAssoc, lastBitmap_snoc, kc_snoc]
      by_cases hc : c = c0
      · subst hc
        simp [hns]
      · have hc' : ¬ c0 = c := fun h => hc h.symm
        simp [hc, hc', i4 c]
    | del bits =>
      refine ⟨i1, i2, keys_delFold _ _ i3, ?_⟩
      intro c
      simp only
      rw [lookup_delFold, lastBitmap_snoc, kc_snoc, i4 c]
      simp only [List.append_nil]
      obtain ⟨hw1, hw2, hw3⟩ := hw l bits [] rfl
      cases hk : (kc c l.zipIdx).getLast? with
      | none => simp
      | some a =>
        obtain ⟨j, y⟩ := a
        have hmem : (j, y) ∈ kc c l.zipIdx := List.mem_of_getLast? hk
        have hcv : cvAt l j = some c := mem_kc hmem
        have hjl : j < l.length := by
          unfold cvAt at hcv
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hcv
          simp at hcv
        by_cases hin : c ∈ newCvs l (lastBitmap l) bits
        · obtain ⟨j0, hj0, hj0n, hj0c⟩ := mem_newCvs.mp hin
          have : j ∈ bits := hw3 j0 hj0 hj0n j hjl (by rw [hcv, hj0c])
          simp [hin, this]
        · have hiff : j ∈ bits ↔ j ∈ lastBitmap l := by
            constructor
            · intro hb
              by_contra hnb
              exact hin (mem_newCvs.mpr ⟨j, hb, hnb, hcv⟩)
            · exact hw2 j
          by_cases hb : j ∈ bits
          · simp [hin, hb, hiff.mp hb]
          · have : j ∉ lastBitmap l := fun h => hb (hiff.mpr h)
            simp [hin, hb, this]

/-- The lookup of a compare value in the live klongs of well-formed klongs:
the pointee of its last key klong, unless the last bitmap deletes it. -/
theorem lookup_live (ks : List Klong) (h : klongsWf ks = true) (c : Nat) :
    (live ks).lookup c = (((kc c ks.zipIdx).getLast?).filter
      (fun a => !(lastBitmap ks).contains a.1)).map (·.2) := by
  rw [← searchEq_spec ks h c]
  simp only [klongsWf, Bool.and_eq_true] at h
  have hb := (bmFold_spec ks ks).2 h.2
  have hw : BmW ks := by
    intro l1 b l2 he
    have := bitmapOk_iff (hb l1 b l2 he)
    exact ⟨this.1, this.2.1⟩
  unfold searchEq
  rw [eqFold_spec c ks hw]

/-- The map keeps the live children: the model's live children of the entries
of a key node's klongs, well formed and with W5, are the pointees of its live
klongs. -/
theorem mem_blive_entriesOf (ks : List Klong) (hwf : klongsWf ks = true)
    (hfull : fullOk ks = true) (y : NodeId) :
    y ∈ blive (entriesOf ks) ↔ ∃ c, (c, y) ∈ live ks := by
  obtain ⟨s1, s2, s3, s4⟩ := stOf_spec ks (wf5_of ks hwf hfull)
  rw [SIS.Check.blive_eq, SIS.Check.mem_bout]
  change Has (stOf ks) y ↔ _
  unfold Has
  rw [s1, s2]
  simp only [reduceCtorEq, or_false]
  constructor
  · rintro ⟨⟨c, v⟩, hp, hv⟩
    simp only at hv
    subst hv
    refine ⟨c, ?_⟩
    rw [mem_iff_lookup s3, s4 c] at hp
    rw [← lookup_iff_mem (live_sorted ks), lookup_live ks hwf]
    cases hk : (kc c ks.zipIdx).getLast? with
    | none => rw [hk] at hp; simp at hp
    | some a =>
      obtain ⟨j, y'⟩ := a
      rw [hk] at hp
      by_cases hd : j ∈ lastBitmap ks
      · simp [hd] at hp
      · simp [hd] at hp
        simp [Option.filter, hd, hp]
  · rintro ⟨c, hc⟩
    rw [← lookup_iff_mem (live_sorted ks), lookup_live ks hwf] at hc
    refine ⟨(c, some y), ?_, rfl⟩
    rw [mem_iff_lookup s3, s4 c]
    cases hk : (kc c ks.zipIdx).getLast? with
    | none => rw [hk] at hc; simp at hc
    | some a =>
      obtain ⟨j, y'⟩ := a
      rw [hk] at hc
      by_cases hd : j ∈ lastBitmap ks
      · simp [Option.filter, hd] at hc
      · simp [Option.filter, hd] at hc
        simp [hd, hc]

end Contract
