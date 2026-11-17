/-
The contract package (bergdb 030-10): the premises of `runs_meetsTop_put1`
(Proof/WriterPut.lean) can be met, so the theorem is not vacuous. A run of the
model's writer (`Runs`, Writer.lean, section 4) with Java's node size 8 and the
level bounds G = H = 0: from the primordial tree (key node 1, a segment leaf
with the one time klong of time 0, the space root of time 0; top node 2 names
it; the writer's view is the model's `initStruct`, `v0_init`), a transaction at
time 1 that puts the key [8], and one at time 2 that puts the key [16]. Each
`putKv` is evaluated (`rfl`); the run is a history that meets the writer's
contract, TREE and the top's clauses (`meets`, `meets2`), and the theorems on
Java's reads speak about it.
-/
import Contract.Proof.WriterPut
import Contract.TheoremsTop
import SIS.Tree.Spec

namespace Contract.WriterExample

open Contract
open SIS (View)
open SIS.Check (BVal)

/-! ## The parameters and the start -/

/-- Java's node size 8, one segment level and one height (G = H = 0); h is the
default M / 2 = 4. -/
def p : MParams := { M := 8, G := 0, H := 0 }

theorem paramsOK : ParamsOK p := ⟨by decide, by decide, by decide⟩

/-- The primordial key node: a segment leaf of level 1 with a time klong of 0. -/
def leaf0 : KNode := { level := 1, leaf := true, ks := [.time 0] }

/-- The start tree: key node 1, the space root of time 0. -/
def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf0) else none, roots := [(0, 1)] }

/-- Top node 2 of the start, of time 0, naming key node 1. -/
def zn0 : TopNode := { time := 0, root := 1, skips := [] }

def tp0 : Top := [(2, zn0)]

/-- The primordial top node in the abstract structure (`SIS.Tree.initStruct`). -/
def top2 : SIS.Node BVal := { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] }

/-- The view of the primordial structure without the root: the key node is
the marker alone. -/
def v0 : View BVal := fun x =>
  if x = 1 then some { level := p.keyLevel 0 0, isData := false, hist := [⟨0, SIS.Tree.marker⟩] }
  else if x = 2 then some top2 else none

/-- The writer's super root at the start. -/
def t0 : SIS.Tree.Top := { id := 2, ord := 0, time := 0, rootKey := 1, skips := [] }

theorem top0 : SIS.Tree.topOf p v0 2 = .ok t0 := rfl

/-- v0 is the model's primordial structure (`SIS.Tree.initStruct`) as the
writer sees it, without the root (`SIS.Tree.rootless`); its super root is top
node 2 (`SIS.Tree.lastTop`). -/
theorem v0_init : (∀ x, v0 x = SIS.Tree.rootless (SIS.Tree.initStruct p).get? x) ∧
    SIS.Tree.lastTop (SIS.Tree.initStruct p).get? = some 2 := by
  refine ⟨fun x => ?_, rfl⟩
  by_cases h0 : x = 0
  · subst h0
    rfl
  · by_cases h1 : x = 1
    · subst h1
      rfl
    · by_cases h2 : x = 2
      · subst h2
        rfl
      · have e0 : (x == 0) = false := by simpa using h0
        have e1 : (x == 1) = false := by simpa using h1
        have e2 : (x == 2) = false := by simpa using h2
        simp [v0, SIS.Tree.rootless, SIS.Tree.initStruct, SIS.Struct.get?, List.lookup, e0,
          e1, e2, h1, h2, SIS.root]

/-! ## The start meets `Before`, and the view shows it -/

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
    intro x n hx
    obtain ⟨rfl, rfl⟩ := s0_key hx
    exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
  top := ⟨t0, zn0, top0, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem topStart0 : TopStart tp0 := ⟨2, zn0, rfl, rfl, rfl⟩

theorem runs0 : Runs p [] s0 tp0 := Runs.start s0 tp0 3 before0 (by decide) topStart0

/-! ## The transaction at time 1: a put of the key [8] -/

/-- The writer's state at the start of the transaction: first id 3. -/
def w0 : MW := { next := 3, top := t0 }

def op1 : MOp := .put [8] 5

/-- The state after the put: key node 1 read and given a time klong of 1 and
the key klong of 8 to the value, node 3. -/
def w1 : MW :=
  { nodes := [(1, ⟨true, [.time 0, .time 1, .key 8 3]⟩)], gh := [(1, 0, 0)],
    made := [⟨3, 0, true⟩], vals := [(3, 5)], next := 5, path := [(none, 1)], top := t0 }

theorem put1 : SIS.Tree.putKv op1 { p := p, i := 1, view := v0 } w0 = .ok (false, w1) := rfl

theorem run1 : OpsRun { p := p, i := 1, view := v0 } w0 [op1] w1 :=
  OpsRun.cons w0 w1 w1 op1 [] false (by decide) put1 rfl (OpsRun.nil w1)

/-- The leaf after the put. -/
def leaf1 : KNode := { level := 1, leaf := true, ks := [.time 0, .time 1, .key 8 3] }

/-- The tree after the transaction at time 1. -/
def s1 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf1) else if x = 3 then some (.val 5) else none,
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
    · have e1 : (x == 1) = false := by simpa using h1
      simp [treeOf, w1, s0, s1, h1, h3, List.lookup, e1]

/-- The writer made no top node. -/
theorem topOf_w1 : topOf 1 tp0 w1 = tp0 := rfl

theorem runs1 : Runs p [[.put [8] 5]] s1 tp0 := by
  have h : Runs p [[.put [8] 5]] (treeOf 1 s0 w1) (topOf 1 tp0 w1) :=
    Runs.step [] s0 tp0 [op1] 3 v0 2 t0 w1 runs0 shows0 top0 before0.books.ids run1
  rwa [treeOf_w1, topOf_w1] at h

/-- The run of one transaction meets the writer's contract, TREE and the top's
clauses. -/
theorem meets : MeetsTop (cpOf p) [[.put [8] 5]] s1 tp0 :=
  runs_meetsTop_put1 paramsOK runs1 (by simp)

/-! ## The transaction at time 2: a put of the key [16] -/

/-- The view of the structure at time 1: key node 1 has the marker of time 0
and the key entry of time 1; value node 3. -/
def v1 : View BVal := fun x =>
  if x = 1 then
    some { level := 1, isData := false, hist := [⟨0, SIS.Tree.marker⟩, ⟨1, .key 8 3⟩] }
  else if x = 2 then some top2
  else if x = 3 then some { level := 0, isData := true, hist := [⟨1, .data 5⟩] }
  else none

theorem top1 : SIS.Tree.topOf p v1 2 = .ok t0 := rfl

theorem s1_key {x : NodeId} {n : KNode} (h : s1.obj x = some (.key n)) : x = 1 ∧ n = leaf1 := by
  by_cases e : x = 1
  · subst e
    simp only [s1, ite_true, Option.some.injEq, Obj.key.injEq] at h
    exact ⟨rfl, h.symm⟩
  · by_cases e3 : x = 3 <;> simp [s1, e, e3] at h

theorem shows1 : Shows p v1 2 s1 tp0 where
  key := by
    intro x n hx
    obtain ⟨rfl, rfl⟩ := s1_key hx
    exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
  top := ⟨t0, zn0, top1, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ids1 : ∀ x : Nat, 5 ≤ x → s1.obj x = none ∧ tp0.node x = none := by
  intro x hx
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  simp [s1, tp0, Top.node, h1, h2, h3]

/-- The writer's state at the start of the transaction: first id 5. -/
def w0' : MW := { next := 5, top := t0 }

def op2 : MOp := .put [16] 6

/-- The state after the put: key node 1 read and given a time klong of 2 and
the key klong of 16 to the value, node 5. -/
def w2 : MW :=
  { nodes := [(1, ⟨true, [.time 0, .time 1, .key 8 3, .time 2, .key 16 5]⟩)], gh := [(1, 0, 0)],
    made := [⟨5, 0, true⟩], vals := [(5, 6)], next := 7, path := [(none, 1)], top := t0 }

theorem put2 : SIS.Tree.putKv op2 { p := p, i := 2, view := v1 } w0' = .ok (false, w2) := rfl

theorem run2 : OpsRun { p := p, i := 2, view := v1 } w0' [op2] w2 :=
  OpsRun.cons w0' w2 w2 op2 [] false (by decide) put2 rfl (OpsRun.nil w2)

/-- The leaf after the second put. -/
def leaf2 : KNode :=
  { level := 1, leaf := true, ks := [.time 0, .time 1, .key 8 3, .time 2, .key 16 5] }

/-- The tree after the transaction at time 2. -/
def s2 : Tree :=
  { obj := fun x =>
      if x = 1 then some (.key leaf2) else if x = 3 then some (.val 5)
      else if x = 5 then some (.val 6) else none,
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
      · have e1 : (x == 1) = false := by simpa using h1
        simp [treeOf, w2, s1, s2, h1, h3, h5, List.lookup, e1]

theorem runs2 : Runs p [[.put [8] 5], [.put [16] 6]] s2 tp0 := by
  have h : Runs p [[.put [8] 5], [.put [16] 6]] (treeOf 2 s1 w2) (topOf 2 tp0 w2) :=
    Runs.step [[.put [8] 5]] s1 tp0 [op2] 5 v1 2 t0 w2 runs1 shows1 top1 ids1 run2
  rwa [treeOf_w2, show topOf 2 tp0 w2 = tp0 from rfl] at h

/-- The run of two transactions meets the writer's contract, TREE and the
top's clauses. -/
theorem meets2 : MeetsTop (cpOf p) [[.put [8] 5], [.put [16] 6]] s2 tp0 :=
  runs_meetsTop_put1 paramsOK runs2 (by simp)

/-- What the theorems on reads say of it: Java's get at times 1 and 2. -/
example : jget s2 tp0 1 false [16] = none := by
  rw [jget_right meets2 1 (by decide)]; decide

example : jget s2 tp0 2 false [16] = some 6 := by
  rw [jget_right meets2 2 (by decide)]; decide

end Contract.WriterExample
