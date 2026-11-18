/-
The contract package (bergdb 030-10): the premises of `runs_meetsTop_put`
(Proof/WriterPutAll.lean) can be met with keys of two segments. A run of the
model's writer (`RunsPut`) with Java's node size 8 and the level bounds G = 1,
H = 0 (two segment levels): from the primordial tree (key node 1, a segment
leaf of segment 0 with the one time klong of time 0; top node 2 names it), a
transaction at time 1 that puts the key [56, 8] (56 a segment of 7 bytes: the
put makes a new segment leaf, node 3, for the second segment), and one at
time 2 that puts the key [56, 16] into that segment leaf. Each `putKv` is
evaluated (`rfl`); the run is a history that meets the writer's contract,
TREE and the top's clauses (`meets`), and the theorems on Java's reads speak
about it. The top is that of WriterExample.lean.
-/
import Contract.WriterExample
import Contract.Proof.WriterPutAll

namespace Contract.WriterExample2

open Contract
open SIS (View)
open SIS.Check (BVal)
open Contract.WriterExample (zn0 tp0 t0 topStart0)

/-! ## The parameters and the start -/

/-- Java's node size 8; two segment levels (G = 1), one height (H = 0); h is
the default M / 2 = 4. A key node of segment 0 has level 2, of segment 1
level 1. -/
def p : MParams := { M := 8, G := 1, H := 0 }

theorem paramsOK : ParamsOK p := ⟨by decide, by decide, by decide⟩

/-- The primordial key node: a segment leaf of segment 0 with a time klong of 0. -/
def leaf0 : KNode := { level := 2, leaf := true, ks := [.time 0] }

/-- The start tree: key node 1, the space root of time 0. -/
def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf0) else none, roots := [(0, 1)] }

/-- The primordial top node in the abstract structure, at these parameters. -/
def top2 : SIS.Node BVal := { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] }

/-- The view of the primordial structure without the root. -/
def v0 : View BVal := fun x =>
  if x = 1 then some { level := p.keyLevel 0 0, isData := false, hist := [⟨0, SIS.Tree.marker⟩] }
  else if x = 2 then some top2 else none

theorem top0 : SIS.Tree.topOf p v0 2 = .ok t0 := rfl

theorem s0_key {x : NodeId} {n : KNode} (h : s0.obj x = some (.key n)) : x = 1 ∧ n = leaf0 := by
  by_cases e : x = 1
  · subst e
    simp only [s0, ite_true, Option.some.injEq, Obj.key.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [s0, e] at h

theorem before0 : Before p 1 3 s0 tp0 where
  inv := by decide
  tree := by decide
  balanced := by
    intro x _ n hx
    obtain ⟨-, rfl⟩ := s0_key hx
    exact ⟨by decide, by decide, fun h => absurd h (by decide)⟩
  books := {
    first := fun x n hx => by
      obtain ⟨-, rfl⟩ := s0_key hx
      exact ⟨0, [], rfl⟩
    times := fun x n hx => by
      obtain ⟨-, rfl⟩ := s0_key hx
      rfl
    rootTimes := by decide
    ids := fun x hx => by
      have h1 : x ≠ 1 := by omega
      have h2 : x ≠ 2 := by omega
      simp [s0, tp0, Top.node, h1, h2]
    roots := rfl
    skips := fun z zn h q hq => by
      simp only [tp0, List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [zn0] at hq }

theorem shows0 : Shows p v0 2 s0 tp0 where
  key := by
    intro x _ n hx
    obtain ⟨rfl, rfl⟩ := s0_key hx
    exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
  top := ⟨t0, zn0, top0, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem named0 : SNamed s0 := by
  intro x n hx c y hk
  obtain ⟨-, rfl⟩ := s0_key hx
  simp [leaf0] at hk

theorem runs0 : RunsPut p [] s0 tp0 := RunsPut.start s0 tp0 3 before0 (by decide) topStart0

/-! ## The transaction at time 1: a put of the key [56, 8], a new segment leaf -/

/-- The writer's state at the start of the transaction: first id 3. -/
def w0 : MW := { next := 3, top := t0 }

def op1 : MOp := .put [56, 8] 5

/-- The state after the put: key node 1 read and given a klong of 56 to the
new segment leaf 3 of segment 1, which has the key klong of 8 to the value,
node 5. -/
def w1 : MW :=
  { nodes := [(1, ⟨true, [.time 0, .time 1, .key 56 3]⟩), (3, ⟨true, [.time 1, .key 8 5]⟩)],
    gh := [(3, 1, 0), (1, 0, 0)], made := [⟨3, 1, false⟩, ⟨5, 0, true⟩], vals := [(5, 5)],
    next := 7, path := [(none, 1)], top := t0, trail := ["segment.new"] }

theorem put1 : SIS.Tree.putKv op1 { p := p, i := 1, view := v0 } w0 = .ok (false, w1) := rfl

theorem run1 : OpsRun { p := p, i := 1, view := v0 } w0 [op1] w1 :=
  OpsRun.cons w0 w1 w1 op1 [] false (by decide) put1 rfl (OpsRun.nil w1)

/-- The two key nodes after the put. -/
def leaf1 : KNode := { level := 2, leaf := true, ks := [.time 0, .time 1, .key 56 3] }
def seg1 : KNode := { level := 1, leaf := true, ks := [.time 1, .key 8 5] }

/-- The tree after the transaction at time 1. -/
def s1 : Tree :=
  { obj := fun x =>
      if x = 1 then some (.key leaf1) else if x = 3 then some (.key seg1)
      else if x = 5 then some (.val 5) else none,
    roots := [(0, 1)] }

/-- The map of the writer's last state is s1. -/
theorem treeOf_w1 : treeOf 1 s0 w1 = s1 := by
  refine prim_tree_ext (fun x => ?_) rfl
  by_cases h1 : x = 1
  · subst h1
    rfl
  · by_cases h3 : x = 3
    · subst h3
      rfl
    · by_cases h5 : x = 5
      · subst h5
        rfl
      · have e1 : (x == 1) = false := by simpa using h1
        have e3 : (x == 3) = false := by simpa using h3
        simp [treeOf, w1, s0, s1, h1, h3, h5, List.lookup, e1, e3]

theorem runs1 : RunsPut p [[.put [56, 8] 5]] s1 tp0 := by
  have h : RunsPut p [[.put [56, 8] 5]] (treeOf 1 s0 w1) (topOf 1 tp0 w1) :=
    RunsPut.step [] s0 tp0 [op1] 3 v0 2 t0 w1 runs0 named0 (by simp [op1]) shows0 top0
      before0.books.ids run1
  rwa [treeOf_w1, show topOf 1 tp0 w1 = tp0 from rfl] at h

/-! ## The transaction at time 2: a put of the key [56, 16] into segment leaf 3 -/

/-- The view of the structure at time 1, without the root. -/
def v1 : View BVal := fun x =>
  if x = 1 then
    some { level := 2, isData := false, hist := [⟨0, SIS.Tree.marker⟩, ⟨1, .key 56 3⟩] }
  else if x = 2 then some top2
  else if x = 3 then some { level := 1, isData := false, hist := [⟨1, .key 8 5⟩] }
  else if x = 5 then some { level := 0, isData := true, hist := [⟨1, .data 5⟩] }
  else none

theorem top1 : SIS.Tree.topOf p v1 2 = .ok t0 := rfl

theorem s1_key {x : NodeId} {n : KNode} (h : s1.obj x = some (.key n)) :
    (x = 1 ∧ n = leaf1) ∨ (x = 3 ∧ n = seg1) := by
  by_cases e1 : x = 1
  · subst e1
    simp only [s1, ite_true, Option.some.injEq, Obj.key.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  · by_cases e3 : x = 3
    · subst e3
      simp [s1] at h
      exact Or.inr ⟨rfl, h.symm⟩
    · by_cases e5 : x = 5 <;> simp [s1, e1, e3, e5] at h

theorem shows1 : Shows p v1 2 s1 tp0 where
  key := by
    intro x _ n hx
    rcases s1_key hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
  top := ⟨t0, zn0, top1, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem named1 : SNamed s1 := by
  intro x n hx c y hk
  rcases s1_key hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp only [leaf1, List.mem_cons, reduceCtorEq, Klong.key.injEq, List.not_mem_nil,
      or_false, false_or] at hk
    obtain ⟨-, rfl⟩ := hk
    rfl
  · simp only [seg1, List.mem_cons, reduceCtorEq, Klong.key.injEq, List.not_mem_nil,
      or_false, false_or] at hk
    obtain ⟨-, rfl⟩ := hk
    rfl

theorem ids1 : ∀ x : Nat, 7 ≤ x → s1.obj x = none ∧ tp0.node x = none := by
  intro x hx
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  have h5 : x ≠ 5 := by omega
  simp [s1, tp0, Top.node, h1, h2, h3, h5]

/-- The writer's state at the start of the transaction: first id 7. -/
def w0' : MW := { next := 7, top := t0 }

def op2 : MOp := .put [56, 16] 6

/-- The state after the put: the descent by the klong of 56 to segment leaf 3,
which gets a time klong of 2 and the key klong of 16 to the value, node 7. -/
def w2 : MW :=
  { nodes := [(1, ⟨true, [.time 0, .time 1, .key 56 3]⟩),
      (3, ⟨true, [.time 1, .key 8 5, .time 2, .key 16 7]⟩)],
    gh := [(3, 1, 0), (1, 0, 0)], made := [⟨7, 0, true⟩], vals := [(7, 6)], next := 9,
    path := [(none, 1), (some 56, 3)], top := t0 }

theorem put2 : SIS.Tree.putKv op2 { p := p, i := 2, view := v1 } w0' = .ok (false, w2) := rfl

theorem run2 : OpsRun { p := p, i := 2, view := v1 } w0' [op2] w2 :=
  OpsRun.cons w0' w2 w2 op2 [] false (by decide) put2 rfl (OpsRun.nil w2)

/-- Segment leaf 3 after the second put. -/
def seg2 : KNode := { level := 1, leaf := true, ks := [.time 1, .key 8 5, .time 2, .key 16 7] }

/-- The tree after the transaction at time 2. -/
def s2 : Tree :=
  { obj := fun x =>
      if x = 1 then some (.key leaf1) else if x = 3 then some (.key seg2)
      else if x = 5 then some (.val 5) else if x = 7 then some (.val 6) else none,
    roots := [(0, 1)] }

theorem treeOf_w2 : treeOf 2 s1 w2 = s2 := by
  refine prim_tree_ext (fun x => ?_) rfl
  by_cases h1 : x = 1
  · subst h1
    rfl
  · by_cases h3 : x = 3
    · subst h3
      rfl
    · by_cases h5 : x = 5
      · subst h5
        rfl
      · by_cases h7 : x = 7
        · subst h7
          rfl
        · have e1 : (x == 1) = false := by simpa using h1
          have e3 : (x == 3) = false := by simpa using h3
          simp [treeOf, w2, s1, s2, h1, h3, h5, h7, List.lookup, e1, e3]

theorem runs2 : RunsPut p [[.put [56, 8] 5], [.put [56, 16] 6]] s2 tp0 := by
  have h : RunsPut p [[.put [56, 8] 5], [.put [56, 16] 6]] (treeOf 2 s1 w2) (topOf 2 tp0 w2) :=
    RunsPut.step [[.put [56, 8] 5]] s1 tp0 [op2] 7 v1 2 t0 w2 runs1 named1 (by simp [op2])
      shows1 top1 ids1 run2
  rwa [treeOf_w2, show topOf 2 tp0 w2 = tp0 from rfl] at h

/-! ## The run meets the contract -/

/-- The run of the two transactions meets the writer's contract, TREE and the
top's clauses. -/
theorem meets : MeetsTop (cpOf p) [[.put [56, 8] 5], [.put [56, 16] 6]] s2 tp0 :=
  runs_meetsTop_put paramsOK runs2

/-- What the theorems on reads say of it: Java's get of [56, 16] at times 1
and 2, and of [56, 8] at time 2. -/
example : jget s2 tp0 1 false [56, 16] = none := by
  rw [jget_right meets 1 (by decide)]; decide

example : jget s2 tp0 2 false [56, 16] = some 6 := by
  rw [jget_right meets 2 (by decide)]; decide

example : jget s2 tp0 2 false [56, 8] = some 5 := by
  rw [jget_right meets 2 (by decide)]; decide

end Contract.WriterExample2
