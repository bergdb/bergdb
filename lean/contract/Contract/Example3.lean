/-
The contract package (bergdb 030-06, the review of 030-05): a history of three
transactions that meets the writer's contract, so that the premises of the
theorems are not met by one transaction only. It has what Example.lean lacks:
an inner node, a new space root (a split of the root at time 2), a delete that
unlinks a leaf (a bitmap in the inner root at time 3, leaving a dead klong to
a node that is no longer reached), and reads at three earlier times.
-/
import Contract.Theorems

namespace Contract.Example3

open Contract

def p : Params := { M := 8 }

/-- The leaf of the empty tree, and after the put of key [8] at time 1. -/
def leaf0 : KNode := { level := 1, leaf := true, ks := [.time 0] }
def leaf1 : KNode := { level := 1, leaf := true, ks := [.time 0, .time 1, .key 8 2] }
/-- The new leaf of time 2, for key [16] (value node 3). -/
def leaf6 : KNode := { level := 1, leaf := true, ks := [.time 2, .key 16 3] }
/-- The new inner root of time 2, and after the delete of key [8] at time 3. -/
def inner2 : KNode := { level := 2, leaf := false, ks := [.time 2, .key 0 1, .key 16 6] }
def inner3 : KNode :=
  { level := 2, leaf := false, ks := [.time 2, .key 0 1, .key 16 6, .time 3, .del [1]] }

def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf0) else none, roots := [(0, 1)] }

def s1 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf1) else if x = 2 then some (.val 5) else none,
    roots := [(0, 1)] }

def s2 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf1) else if x = 2 then some (.val 5)
      else if x = 3 then some (.val 6) else if x = 4 then some (.key inner2)
      else if x = 6 then some (.key leaf6) else none,
    roots := [(0, 1), (2, 4)] }

def s3 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf1) else if x = 2 then some (.val 5)
      else if x = 3 then some (.val 6) else if x = 4 then some (.key inner3)
      else if x = 6 then some (.key leaf6) else none,
    roots := [(0, 1), (2, 4)] }

def ops1 : List Op := [.put [8] 5]
def ops2 : List Op := [.put [16] 6]
def ops3 : List Op := [.del [8]]

theorem start : Start p s0 := by constructor <;> decide

theorem frame1 : Frame 1 s0 [1] s1 := by
  refine ⟨?_, ?_, ⟨[], by simp [s0, s1], by simp⟩⟩
  · intro x o hx
    by_cases h1 : x = 1
    · subst h1
      simp only [s0, ite_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.key leaf1, by simp [s1], ⟨rfl, rfl, Or.inr ⟨[.key 8 2], rfl⟩⟩, fun h => by simp at h⟩
    · simp [s0, h1] at hx
  · intro x n hx hno
    by_cases h1 : x = 1
    · simp [h1]
    · by_cases h2 : x = 2 <;> simp [s1, h1, h2] at hx

theorem frame2 : Frame 2 s1 [4, 6] s2 := by
  refine ⟨?_, ?_, ⟨[(2, 4)], by simp [s1, s2], by simp⟩⟩
  · intro x o hx
    by_cases h1 : x = 1
    · subst h1
      simp only [s1, ite_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.key leaf1, by simp [s2], ⟨rfl, rfl, Or.inl rfl⟩, fun _ => rfl⟩
    · by_cases h2 : x = 2
      · subst h2
        simp [s1] at hx
        subst hx
        exact ⟨.val 5, by simp [s2], rfl, fun _ => rfl⟩
      · simp [s1, h1, h2] at hx
  · intro x n hx hno
    by_cases h4 : x = 4
    · simp [h4]
    · by_cases h6 : x = 6
      · simp [h6]
      · by_cases h1 : x = 1
        · simp [s1, h1] at hno
        · by_cases h2 : x = 2
          · simp [s2, h2] at hx
          · by_cases h3 : x = 3 <;> simp [s2, h1, h2, h3, h4, h6] at hx

theorem frame3 : Frame 3 s2 [4] s3 := by
  refine ⟨?_, ?_, ⟨[], by simp [s2, s3], by simp⟩⟩
  · intro x o hx
    by_cases h4 : x = 4
    · subst h4
      simp [s2] at hx
      subst hx
      exact ⟨.key inner3, by simp [s3], ⟨rfl, rfl, Or.inr ⟨[.del [1]], rfl⟩⟩,
        fun h => by simp at h⟩
    · refine ⟨o, ?_, ?_, fun _ => rfl⟩
      · have : s3.obj x = s2.obj x := by simp [s2, s3, h4]
        rw [this, hx]
      · cases o with
        | key n => exact ⟨rfl, rfl, Or.inl rfl⟩
        | val v => rfl
  · intro x n hx hno
    have : s3.obj x = none := by
      by_cases h4 : x = 4
      · simp [s2, h4] at hno
      · have : s3.obj x = s2.obj x := by simp [s2, s3, h4]
        rw [this, hno]
    simp [this] at hx

theorem meets : Meets p [ops1, ops2, ops3] s3 :=
  Meets.step [ops1, ops2] s2 ops3 [4] s3
    (Meets.step [ops1] s1 ops2 [4, 6] s2
      (Meets.step [] s0 ops1 [1] s1 (Meets.start s0 start) ⟨by decide, frame1⟩)
      ⟨by decide, frame2⟩)
    ⟨by decide, frame3⟩

/-- What the theorems say of it, at each of the four times. -/
example : get (s3.at 0) [16] = none := by rw [get_right meets 0 (by decide)]; decide
example : get (s3.at 1) [8] = some 5 := by rw [get_right meets 1 (by decide)]; decide
example : get (s3.at 2) [16] = some 6 := by rw [get_right meets 2 (by decide)]; decide
example : get (s3.at 3) [8] = none := by rw [get_right meets 3 (by decide)]; decide
example : scan (s3.at 2) {} 10 = [([8], 5), ([16], 6)] := by
  rw [scan_right meets 2 (by decide) {} (by decide)]; decide
example : scan (s3.at 3) { forward := false } 10 = [([16], 6)] := by
  rw [scan_right meets 3 (by decide) _ (by decide)]; decide

end Contract.Example3
