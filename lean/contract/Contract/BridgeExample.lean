/-
The contract package (bergdb 030-07): the premises of the bridge's theorems
can be met. The history of Example.lean (the empty tree as Java makes it, and
one transaction that puts one key) with the model's changes beside it: the
primordial structure (the root, node 0; key node 1; top node 3), and the
put's change (value node 2 made, its entry, and a key entry for node 1). It
meets the contract and the bridge's clauses (`meets`), so the theorems of
BridgeTheorems.lean speak about it: they are not vacuous.
-/
import Contract.BridgeTheorems
import Contract.Example

namespace Contract.BridgeExample

open Contract
open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

/-- The change of TX 0: the root on level 9, key node 1 on level 1, top node
3 on level 8; the root's entry for the top node, the top node's root
pointer. -/
def c0 : Changes BVal :=
  { new := [⟨0, 9, false⟩, ⟨1, 1, false⟩, ⟨3, 8, false⟩], adds := [(0, .top 3), (3, .rootKey 1)] }

/-- The change of the put: value node 2 is made, key node 1 gets a key entry
for it, and it gets its data entry. -/
def c1 : Changes BVal :=
  { new := [⟨2, 0, true⟩], adds := [(1, .key 8 2), (2, .data 5)] }

/-- The history. -/
def h : BHist :=
  { s0 := Example.s0, c0 := c0,
    txs := [{ ops := Example.ops, D := [1], s := Example.s1, c := c1 }] }

theorem startB : StartB h :=
  ⟨1, 3, 1, 8, 9, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, fun x hx => by simp [h, Example.s0, hx], rfl⟩

theorem startFacts : StartFacts h 1 3 1 8 9 :=
  { hr := by decide, hz := by decide, hzr := by decide, hlr := by decide, hlrz := by decide,
    hlz0 := by decide, p0 := rfl, top := rfl, get0 := rfl, getr := rfl, getz := rfl, obj := rfl,
    none := fun x hx => by simp [h, Example.s0, hx], roots := rfl }

/-- The model's structure after the put. -/
def P1 : Struct BVal :=
  [(0, { level := 9, isData := false, hist := [⟨0, .top 3⟩] }),
   (1, { level := 1, isData := false, hist := [⟨1, .key 8 2⟩] }),
   (3, { level := 8, isData := false, hist := [⟨0, .rootKey 1⟩] }),
   (2, { level := 0, isData := true, hist := [⟨1, .data 5⟩] })]

theorem P1_eq : (h.P 0).apply 1 c1 = P1 := rfl

theorem mem_P1 {x : NodeId} {n : Node BVal} (hx : P1.get? x = some n) :
    (x = 0 ∧ n = { level := 9, isData := false, hist := [⟨0, .top 3⟩] }) ∨
    (x = 1 ∧ n = { level := 1, isData := false, hist := [⟨1, .key 8 2⟩] }) ∨
    (x = 3 ∧ n = { level := 8, isData := false, hist := [⟨0, .rootKey 1⟩] }) ∨
    (x = 2 ∧ n = { level := 0, isData := true, hist := [⟨1, .data 5⟩] }) := by
  have := SIS.mem_of_get? hx
  simpa [P1] using this

/-- What the model reaches after the put: the root, the top node, the key
node and the value. -/
theorem reach_P1 {y : NodeId} (hy : Reach h.spec P1 1 y) : y = 0 ∨ y = 3 ∨ y = 1 ∨ y = 2 := by
  induction hy with
  | root _ _ => exact Or.inl rfl
  | @child x y n m _ hn hy _ _ ih =>
    rcases mem_P1 hn with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have : y ∈ [3] := hy
      simp at this; simp [this]
    · have : y ∈ [2] := hy
      simp at this; simp [this]
    · have : y ∈ [1] := hy
      simp at this; simp [this]
    · have : y ∈ ([] : List Nat) := hy
      simp at this

theorem made : Made Example.s0 Example.s1 c1 := by
  intro x h0 h1
  by_cases hx1 : x = 1
  · simp [Example.s0, hx1] at h0
  · by_cases hx2 : x = 2
    · simp [c1, hx2]
    · simp [Example.s1, hx1, hx2] at h1

theorem topOK : TopOK h.spec (h.P 0) 1 Example.s0 Example.s1 c1 := by
  have htl : h.spec.topLevel = 8 := rfl
  refine { virt := ?_, fresh := ?_, current := ?_, dataFixed := ?_, levels := ?_,
           newReachable := ?_, noRes := ?_, link := ?_ }
  · refine { newTop := ?_, topFixed := ?_, rootAdds := rfl, closure := ?_, dead := ?_ }
    · intro nn hnn hl
      simp only [c1, List.mem_singleton] at hnn
      subst hnn
      rw [htl] at hl
      simp at hl
    · intro a ha n hn _
      simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [htl]
      rcases ha with rfl | rfl
      · have : (h.P 0).get? 1 = some { level := 1, isData := false, hist := [] } := rfl
        rw [this] at hn
        injection hn with hn
        rw [← hn]
        decide
      · have : (h.P 0).get? 2 = none := rfl
        rw [this] at hn
        cases hn
    · intro nn hnn hl
      simp only [c1, List.mem_singleton] at hnn
      subst hnn
      rw [htl] at hl
      simp at hl
    · intro z n hz htop y hy hytop
      rw [P1_eq] at hz htop hytop
      rcases mem_P1 hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd htop (by decide)
      · exact absurd htop (by decide)
      · have : y ∈ [1] := hy
        simp only [List.mem_singleton] at this
        subst this
        exact absurd hytop (by decide)
      · exact absurd htop (by decide)
  · intro nn hnn _
    simp only [c1, List.mem_singleton] at hnn
    subst hnn
    rfl
  · intro a ha hno
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [Example.s1] at hno
  · intro a ha hno
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [Example.s1] at hno
  · intro a ha hno
    simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [Example.s1] at hno
  · intro nn hnn hno
    simp only [c1, List.mem_singleton] at hnn
    subst hnn
    simp [Example.s1] at hno
  · intro y hno hy
    rw [P1_eq, SIS.reachable_iff] at hy
    left
    rw [SIS.reachable_iff]
    rcases reach_P1 hy with rfl | rfl | rfl | rfl
    · exact startFacts.reach0
    · exact startFacts.reachz
    · simp [Example.s1] at hno
    · simp [Example.s1] at hno
  · rw [P1_eq]
    exact ⟨_, 3, _, 1, _, rfl, rfl, rfl, by decide, rfl, rfl, rfl, by decide, rfl, rfl⟩

theorem touchOK : TouchOK h.spec (h.P 0) 1 c1 :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => absurd hx List.not_mem_nil,
    fun _ hx => absurd hx List.not_mem_nil⟩

/-- The computed clauses of the bridge, for the put. -/
theorem bridge : bridgeOk h.topLevel 1 Example.s0 Example.s1 [1] c1 = true := by decide

/-- The history meets the contract and the bridge's clauses. -/
theorem meets : MeetsBridge Example.p h where
  start := startB
  step := by
    intro j hj
    have hj0 : j = 0 := by
      have : j < 1 := hj
      omega
    subst hj0
    exact ⟨Example.contract, bridge, made, topOK, touchOK⟩

/-- What the theorems say of it, for BergDB's algorithm with any take: after
a crash at the end, startup from the stream gives a structure that holds the
tree with the key. -/
example (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) :
    Rep (SIS.startup h.spec (SIS.run h.spec al h.ts).S).P Example.s1 :=
  (bridge_recovery meets al hst).2.2

end Contract.BridgeExample
