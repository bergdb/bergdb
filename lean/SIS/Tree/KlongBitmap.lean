import SIS.Tree.SearchFold

namespace SIS.Tree

open SIS SIS.Check

/-- The state transition in klongsWf, exposed for prefix induction. -/
def klongsWfStep (ks : List Klong) (acc : Bool × Option Time × List Nat)
    (q : Klong × Nat) : Bool × Option Time × List Nat :=
  match q.1 with
  | .time t => (acc.1 && (match acc.2.1 with
      | some t0 => decide (t0 < t)
      | none => true), some t, acc.2.2)
  | .key _ _ => (acc.1 && acc.2.1.isSome, acc.2.1, acc.2.2)
  | .del bits =>
    let newCvs := (bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt ks)
    (acc.1 && acc.2.1.isSome && acc.2.2.all (fun b => bits.contains b) &&
      decide (acc.2.2.length < bits.length) &&
      (bits.zip (bits.drop 1)).all (fun q => decide (q.1 < q.2)) &&
      bits.all (fun b => decide (b < q.2) && (cvAt ks b).isSome) &&
      (List.range q.2).all (fun j => match cvAt ks j with
        | some c => !newCvs.contains c || bits.contains j
        | none => true), acc.2.1, bits)

def klongsWfState (ks : List Klong) (j : Nat) : Bool × Option Time × List Nat :=
  (ks.take j).zipIdx.foldl (klongsWfStep ks) (true,none,[])

theorem klongsWf_eq_fold (ks : List Klong) :
    klongsWf ks = (ks.zipIdx.foldl (klongsWfStep ks) (true,none,[])).1 := rfl

theorem klongsWfStep_ok (ks : List Klong) (acc : Bool × Option Time × List Nat)
    (q : Klong × Nat) (h : (klongsWfStep ks acc q).1 = true) : acc.1 = true := by
  rcases q with ⟨k,i⟩
  cases k <;> simp_all [klongsWfStep,Bool.and_eq_true]

theorem klongsWf_fold_ok (ks : List Klong) (xs : List (Klong × Nat))
    (acc : Bool × Option Time × List Nat)
    (h : (xs.foldl (klongsWfStep ks) acc).1 = true) : acc.1 = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons q qs ih => exact klongsWfStep_ok ks acc q (ih _ h)

theorem klongsWfState_ok (ks : List Klong) (h : klongsWf ks = true) (j : Nat) :
    (klongsWfState ks j).1 = true := by
  rw [klongsWf_eq_fold] at h
  have he : ks.zipIdx = (ks.take j).zipIdx ++
      (ks.drop j).zipIdx (ks.take j).length := by
    simpa only [List.take_append_drop,Nat.zero_add] using
      (List.zipIdx_append (xs := ks.take j) (ys := ks.drop j) (k := 0))
  rw [he,List.foldl_append] at h
  exact klongsWf_fold_ok ks _ _ h

theorem bitmap_fold_zipIdx (pre : List Klong) (start : Nat) (bits : List Nat) :
    (pre.zipIdx start).foldl (fun bits q => match q.1 with | .del b => b | _ => bits) bits =
      pre.foldl (fun bits k => match k with | .del b => b | _ => bits) bits := by
  induction pre generalizing start bits with
  | nil => rfl
  | cons k pre ih =>
    cases k <;> simpa only [List.zipIdx_cons,List.foldl_cons] using ih (start+1) _

theorem klongsWfState_bitmap (ks : List Klong) (j : Nat) :
    (klongsWfState ks j).2.2 = lastBitmapOf (ks.take j) := by
  have he := List.foldl_hom (fun acc : Bool × Option Time × List Nat => acc.2.2)
    (g₁ := klongsWfStep ks)
    (g₂ := fun (bits : List Nat) (q : Klong × Nat) =>
      match q.1 with | .del b => b | _ => bits)
    (l := (ks.take j).zipIdx) (init := (true,none,[])) (by
      intro acc q
      rcases q with ⟨k,i⟩
      cases k <;> rfl)
  unfold klongsWfState
  rw [← he]
  exact bitmap_fold_zipIdx (ks.take j) 0 []

theorem klongsWfState_succ (ks : List Klong) (i : Nat) (k : Klong)
    (hk : ks[i]? = some k) :
    klongsWfState ks (i+1) = klongsWfStep ks (klongsWfState ks i) (k,i) := by
  have hi : i < ks.length := List.getElem?_eq_some_iff.mp hk |>.1
  simp only [klongsWfState,List.take_add_one,hk,Option.toList_some,
    List.zipIdx_append,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi),
    Nat.zero_add,List.zipIdx_cons,List.zipIdx_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- The bitmap rules needed by the equality search. A bitmap extends its
predecessor, names only earlier key klongs, and deletes every earlier klong
of each compare value newly deleted by it. -/
def BitmapRules (ks : List Klong) : Prop :=
  ∀ i bits, ks[i]? = some (.del bits) →
    (∀ b ∈ bits, b < i ∧ (cvAt ks b).isSome = true) ∧
    (∀ b ∈ lastBitmapOf (ks.take i), b ∈ bits) ∧
    (∀ b ∈ bits, b ∉ lastBitmapOf (ks.take i) → ∀ c, cvAt ks b = some c →
      ∀ j < i, cvAt ks j = some c → j ∈ bits)

theorem klongsWf_bitmapRules (ks : List Klong) (h : klongsWf ks = true) :
    BitmapRules ks := by
  intro i bits hk
  have hs := klongsWfState_ok ks h (i+1)
  rw [klongsWfState_succ ks i (.del bits) hk] at hs
  simp only [klongsWfStep,Bool.and_eq_true] at hs
  have hbits := hs.1.2
  have hclosed := hs.2
  have hmono := hs.1.1.1.1.2
  rw [klongsWfState_bitmap] at hclosed hmono
  refine ⟨?_,?_,?_⟩
  · intro b hb
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using List.all_eq_true.mp hbits b hb
  · intro b hb
    simpa only [List.contains_eq_mem,decide_eq_true_eq] using List.all_eq_true.mp hmono b hb
  · intro b hb hbold c hcv j hj hjcv
    have hc : c ∈ (bits.filter (fun b => !(lastBitmapOf (ks.take i)).contains b)).filterMap
        (cvAt ks) := by
      exact List.mem_filterMap.mpr ⟨b,by simp [hb,hbold],hcv⟩
    have hj' := List.all_eq_true.mp hclosed j (List.mem_range.mpr hj)
    have hcontains : ((bits.filter (fun b => !(lastBitmapOf (ks.take i)).contains b)).filterMap
        (cvAt ks)).contains c = true := by simpa using hc
    simp only [hjcv] at hj'
    rw [hcontains] at hj'
    simpa using hj'

theorem cvAt_append_left (pre post : List Klong) (j : Nat) (hj : j < pre.length) :
    cvAt (pre ++ post) j = cvAt pre j := by
  simp only [cvAt,List.getElem?_append_left hj]

theorem bitmapRules_prefix {pre ks : List Klong} (hp : pre.IsPrefix ks)
    (hr : BitmapRules ks) : BitmapRules pre := by
  obtain ⟨post,rfl⟩ := hp
  intro i bits hk
  have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hk).1
  have hk' : (pre ++ post)[i]? = some (.del bits) := by
    rwa [List.getElem?_append_left hi]
  obtain ⟨hb,hm,hc⟩ := hr i bits hk'
  rw [List.take_append_of_le_length (Nat.le_of_lt hi)] at hm hc
  refine ⟨?_,hm,?_⟩
  · intro b hbits
    obtain ⟨hbi,hcv⟩ := hb b hbits
    rw [cvAt_append_left pre post b (by omega)] at hcv
    exact ⟨hbi,hcv⟩
  · intro b hbits hbold c hcv j hj hjcv
    have hbi := (hb b hbits).1
    apply hc b hbits hbold c
    · rwa [cvAt_append_left pre post b (by omega)]
    · exact hj
    · rwa [cvAt_append_left pre post j (by omega)]

def bitmapNext (bits : List Nat) (k : Klong) : List Nat :=
  match k with | .del b => b | _ => bits

theorem lastBitmap_take_step (ks : List Klong) (i : Nat) (k : Klong)
    (hk : ks[i]? = some k) :
    lastBitmapOf (ks.take (i+1)) = bitmapNext (lastBitmapOf (ks.take i)) k := by
  rw [List.take_add_one,hk]
  cases k <;> simp only [bitmapNext,Option.toList_some,lastBitmapOf,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem bitmapRules_bounds (ks : List Klong) (hr : BitmapRules ks)
    (j : Nat) (hj : j ≤ ks.length) :
    ∀ b ∈ lastBitmapOf (ks.take j), b < j ∧ (cvAt ks b).isSome = true := by
  induction j with
  | zero => simp [lastBitmapOf]
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    rw [lastBitmap_take_step ks j ks[j] hk]
    cases he : ks[j] with
    | time t =>
      simp only [bitmapNext]
      intro b hb
      obtain ⟨hbi,hcv⟩ := ih (by omega) b hb
      exact ⟨by omega,hcv⟩
    | key c y =>
      simp only [bitmapNext]
      intro b hb
      obtain ⟨hbi,hcv⟩ := ih (by omega) b hb
      exact ⟨by omega,hcv⟩
    | del bits =>
      simp only [bitmapNext]
      intro b hb
      rw [he] at hk
      obtain ⟨hbi,hcv⟩ := (hr j bits hk).1 b hb
      exact ⟨by omega,hcv⟩

/-- Deleted physical occurrences of a compare value form an initial prefix
of its occurrences. A later undeleted klong may resurrect that value. -/
def BitmapDownward (ks : List Klong) (bits : List Nat) : Prop :=
  ∀ a b c, a ≤ b → cvAt ks a = some c → cvAt ks b = some c → b ∈ bits → a ∈ bits

theorem bitmapRules_downward (ks : List Klong) (hr : BitmapRules ks)
    (j : Nat) (hj : j ≤ ks.length) :
    BitmapDownward ks (lastBitmapOf (ks.take j)) := by
  induction j with
  | zero => simp [BitmapDownward,lastBitmapOf]
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    rw [lastBitmap_take_step ks j ks[j] hk]
    cases he : ks[j] with
    | time t => exact ih (by omega)
    | key c y => exact ih (by omega)
    | del bits =>
      simp only [bitmapNext]
      rw [he] at hk
      obtain ⟨hb,hm,hc⟩ := hr j bits hk
      intro a b c hab hac hbc hbb
      by_cases hbold : b ∈ lastBitmapOf (ks.take j)
      · exact hm a (ih (by omega) a b c hab hac hbc hbold)
      · have hbj := (hb b hbb).1
        exact hc b hbb hbold c hbc a (by omega) hac

end SIS.Tree
