/-
The contract package (bergdb 030-11, the review of 030-07 to 030-09): one
history that meets every statement at once, `MeetsFull`, `MeetsBridge`,
`MeetsEvict`, `MeetsTop`, `MeetsShape` and `Meets`, with a fourth
transaction that the earlier examples lack: the three transactions of
BridgeExample3.lean (a put; a put that makes a new inner root and with it a
top node with a skip pointer; a delete by a bitmap), then at time 4 a put of
a key that is there (an overwrite: a second key klong of one compare value,
the first then dead, naming the old value) with a touch of reclaim's kind
(`Db.touchPaths`: the super root and the path of the put, `TOUCH 7 4 6`).
Before this file no Lean example met the touch rules with a touched node.

So the premises of the reads' theorems (`jget_right`, `jscan_right`) and of
the bridge's (`full_recovery`, `full_restart`, `full_eviction`, `full_cut`)
are met together by one history, and the theorems give the reads at the
times 0 to 4 through the top node's skip pointer.
-/
import Contract.BridgeFull
import Contract.BridgeExample3

namespace Contract.BridgeExample4

open Contract Contract.Example3 Contract.BridgeExample3
open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

/-- Leaf 6 after the overwrite of key [16] at time 4: a second key klong of
compare value 16, naming the new value node 8; the first is dead. -/
def leaf6b : KNode := { level := 1, leaf := true, ks := [.time 2, .key 16 3, .time 4, .key 16 8] }

/-- The tree after the fourth transaction. -/
def s4 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf1) else if x = 2 then some (.val 5)
      else if x = 3 then some (.val 6) else if x = 4 then some (.key inner3)
      else if x = 6 then some (.key leaf6b) else if x = 8 then some (.val 9) else none,
    roots := [(0, 1), (2, 4)] }

/-- The put of key [16] with the value 9: it is there, with the value 6. -/
def ops4 : List Op := [.put [16] 9]

/-- Its change: the value node 8, the key entry in leaf 6, the value's entry,
and the touch: the super root 7 and the put's path, inner root 4 and leaf 6. -/
def c4 : Changes BVal :=
  { new := [⟨8, 0, true⟩], adds := [(6, .key 16 8), (8, .data 9)], touch := [7, 4, 6] }

/-- The history: BridgeExample3's three transactions and the fourth. -/
def h4 : BHist :=
  { s0 := s0, c0 := c0,
    txs := [{ ops := ops1, D := [1], s := s1, c := c1 },
            { ops := ops2, D := [4, 6], s := s2, c := c2 },
            { ops := ops3, D := [4], s := s3, c := c3 },
            { ops := ops4, D := [6], s := s4, c := c4 }] }

theorem startB4 : StartB h4 :=
  ⟨1, 5, 1, 8, 20, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, fun x hx => by simp [h4, s0, hx], rfl⟩

theorem frame4 : Frame 4 s3 [6] s4 := by
  refine ⟨?_, ?_, ⟨[], by simp [s3, s4], by simp⟩⟩
  · intro x o hx
    by_cases h6 : x = 6
    · subst h6
      simp [s3] at hx
      subst hx
      exact ⟨.key leaf6b, by simp [s4], ⟨rfl, rfl, Or.inr ⟨[.key 16 8], rfl⟩⟩,
        fun h => by simp at h⟩
    · have h8 : x ≠ 8 := by
        intro h8
        subst h8
        simp [s3] at hx
      refine ⟨o, ?_, ?_, fun _ => rfl⟩
      · have : s4.obj x = s3.obj x := by simp [s3, s4, h6, h8]
        rw [this, hx]
      · cases o with
        | key n => exact ⟨rfl, rfl, Or.inl rfl⟩
        | val v => rfl
  · intro x n hx hno
    by_cases h6 : x = 6
    · simp [h6]
    · by_cases h8 : x = 8
      · simp [s4, h8] at hx
      · have : s4.obj x = s3.obj x := by simp [s3, s4, h6, h8]
        rw [this, hno] at hx
        cases hx

theorem contract4 : Contract p 4 s3 ops4 [6] s4 := ⟨by decide, frame4⟩

theorem made4 : Made s3 s4 c4 := by
  intro x h0 h1
  by_cases hx8 : x = 8
  · simp [c4, hx8]
  · exfalso
    by_cases hx6 : x = 6
    · simp [s3, hx6] at h0
    · have : s4.obj x = s3.obj x := by simp [s3, s4, hx6, hx8]
      rw [this, h0] at h1
      cases h1

theorem bridge4 : bridgeOk h4.topLevel 4 s3 s4 [6] c4 = true := by decide

/-- The top after the first j transactions: as BridgeExample3's. -/
def top4 (j : Nat) : Top := if j < 2 then tp0 else tp2

theorem bridge1' : bridgeOk h4.topLevel 1 s0 s1 [1] c1 = true := by decide
theorem bridge2' : bridgeOk h4.topLevel 2 s1 s2 [4, 6] c2 = true := by decide
theorem bridge3' : bridgeOk h4.topLevel 3 s2 s3 [4] c3 = true := bridge3
theorem topChange1' : topChangeOk h4.topLevel (h4.P 0) s1 tp0 tp0 c1 = true := by decide
theorem topChange2' : topChangeOk h4.topLevel (h4.P 1) s2 tp0 tp2 c2 = true := by decide
theorem topChange3' : topChangeOk h4.topLevel (h4.P 2) s3 tp2 tp2 c3 = true := by decide

theorem topChange4 : topChangeOk h4.topLevel (h4.P 3) s4 tp2 tp2 c4 = true := by decide

/-- The touch: the super root and the put's path. -/
theorem touch4 : touchOk (s3.at 3) tp2 [7, 4, 6] = true := by decide

theorem copy4 : copyOk 4 s3 s4 tp2 c4 = true := by decide

/-- The history meets every clause in the contract's words, with a touched
node, an overwrite, a top node made and its skip pointer, and a delete. -/
theorem meetsFull : MeetsFull p h4 top4 where
  start := startB4
  startTop := by decide
  step := by
    intro j hj
    have hj4 : j < 4 := hj
    match j, hj with
    | 0, _ =>
      exact ⟨contract1, bridge1', made1, Or.inl rfl, rfl, topChange1', touch1, copy1⟩
    | 1, _ =>
      exact ⟨contract2, bridge2', made2, topStepB_sound 2 tp0 tp2 (by decide), rfl, topChange2',
        touch2, copy2⟩
    | 2, _ =>
      exact ⟨contract3, bridge3', made3, Or.inl rfl, rfl, topChange3', touch3, copy3⟩
    | 3, _ =>
      exact ⟨contract4, bridge4, made4, Or.inl rfl, rfl, topChange4, touch4, copy4⟩
  tree := by
    intro j hj
    have hj4 : j ≤ 4 := hj
    interval_cases j
    · show TreeOk (s0.at 0); decide
    · show TreeOk (s1.at 1); decide
    · show TreeOk (s2.at 2); decide
    · show TreeOk (s3.at 3); decide
    · show TreeOk (s4.at 4); decide
  adopt := by
    intro j hj
    have hj4 : j ≤ 4 := hj
    interval_cases j
    · show adoptOk (s0.at 0) = true; decide
    · show adoptOk (s1.at 1) = true; decide
    · show adoptOk (s2.at 2) = true; decide
    · show adoptOk (s3.at 3) = true; decide
    · show adoptOk (s4.at 4) = true; decide

/-- The four transactions' operations. -/
def txs4 : List (List Op) := [ops1, ops2, ops3, ops4]

/-- One history meets every statement at once: `MeetsFull` (so `MeetsBridge`
and `MeetsEvict`, the bridge's theorems' premises), and `MeetsTop`,
`MeetsShape` and `Meets` (the reads' theorems' premises). -/
theorem meetsAll :
    MeetsFull p h4 top4 ∧ MeetsBridge p h4 ∧ MeetsEvict h4 ∧ MeetsTop p txs4 s4 tp2 ∧
      MeetsShape p txs4 s4 ∧ Meets p txs4 s4 := by
  have hT : MeetsTop p txs4 s4 tp2 := meetsFull.meetsTop (by decide) 4 (le_refl _)
  exact ⟨meetsFull, meetsFull.meetsBridge, meetsFull.meetsEvict, hT, hT.shape, hT.meets⟩

/-- What the reads' theorems give: Java's get through the top's search at
every time, between two records too (`mid`): at time 1 through the skip
pointer of top node 7 to top node 5, at time 3 the delete, at time 4 the
overwrite. -/
example : jget s4 tp2 1 true [8] = some 5 := by
  rw [jget_right meetsAll.2.2.2.1 1 (by decide) true [8]]; decide
example : jget s4 tp2 3 false [8] = none := by
  rw [jget_right meetsAll.2.2.2.1 3 (by decide) false [8]]; decide
example : jget s4 tp2 3 true [16] = some 6 := by
  rw [jget_right meetsAll.2.2.2.1 3 (by decide) true [16]]; decide
example : jget s4 tp2 4 false [16] = some 9 := by
  rw [jget_right meetsAll.2.2.2.1 4 (by decide) false [16]]; decide
example : jscan s4 tp2 2 false {} 10 = [([8], 5), ([16], 6)] := by
  rw [jscan_right meetsAll.2.2.2.1 2 (by decide) false {} (by decide) 10]; decide

/-- What the bridge's theorems give: after a crash after the fourth
transaction, startup from the whole stream gives a structure that holds the
tree of then, with the overwrite and the touch's transaction. -/
example (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h4.spec) :
    Rep (SIS.startup h4.spec ((SIS.run h4.spec al h4.ts).S.take 5)).P s4 :=
  (full_recovery meetsFull al hst 4 (by decide)).2.2

/-- The map from klongs to entries forgets a time klong that no klong follows
(bergdb 030-11, finding 3): two lists of klongs, both well formed, with the
same entries. So the model's structure, which recovery gives back
(`full_recovery`, `Rep`), fixes a key node's entries, not its klongs; that
the two read the same at every time is not stated in Lean. -/
theorem entries_forget :
    entriesOf [.time 0, .time 1, .key 8 2] = entriesOf [.time 1, .key 8 2] ∧
      ([.time 0, .time 1, .key 8 2] : List Klong) ≠ [.time 1, .key 8 2] ∧
      klongsWf [.time 0, .time 1, .key 8 2] = true ∧ klongsWf [.time 1, .key 8 2] = true := by
  decide

end Contract.BridgeExample4
