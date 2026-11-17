/-
The contract package (bergdb 030-07): a longer history that meets the bridge
with the contract's top (`MeetsBridgeTop`, BridgeTop.lean): the three
transactions of Example3.lean (a put; a put that makes a new inner root, a
new space root and with it a top node with a skip pointer; a delete by a
bitmap), with the model's changes and the contract's top beside them. So the
premises of the bridge's theorems are met by a history in which a top node is
made, the root gets its entry, and a bitmap is a delete entry: `meetsBridge`
gives `MeetsBridge` for it, with the top's clauses in the model's words
(R1 to R4, the dead top nodes, the link) proved, not assumed.
-/
import Contract.Proof.BridgeTop
import Contract.BridgeTheorems
import Contract.Example3

namespace Contract.BridgeExample3

open Contract Contract.Example3
open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

/-- TX 0: the root on level 20, key node 1, top node 5 on level 8. -/
def c0 : Changes BVal :=
  { new := [⟨0, 20, false⟩, ⟨1, 1, false⟩, ⟨5, 8, false⟩], adds := [(0, .top 5), (5, .rootKey 1)] }

/-- The put of key [8]: value node 2. -/
def c1 : Changes BVal :=
  { new := [⟨2, 0, true⟩], adds := [(1, .key 8 2), (2, .data 5)] }

/-- The put of key [16]: value node 3, the new inner root 4, the new leaf 6,
and top node 7 on level 9, which names the new space root 4 and, by its skip
pointer 0, top node 5. -/
def c2 : Changes BVal :=
  { new := [⟨3, 0, true⟩, ⟨4, 2, false⟩, ⟨6, 1, false⟩, ⟨7, 9, false⟩],
    adds := [(0, .top 7), (3, .data 6), (4, .key 0 1), (4, .key 16 6), (6, .key 16 3),
             (7, .rootKey 4), (7, .skip 0 5)] }

/-- The delete of key [8]: a delete entry for compare value 0 in the inner
root (its bitmap deletes the klong of the leaf that held the key). -/
def c3 : Changes BVal := { new := [], adds := [(4, .del [0])] }

/-- The history. -/
def h : BHist :=
  { s0 := s0, c0 := c0,
    txs := [{ ops := ops1, D := [1], s := s1, c := c1 },
            { ops := ops2, D := [4, 6], s := s2, c := c2 },
            { ops := ops3, D := [4], s := s3, c := c3 }] }

/-- The top at the start and after the first put: top node 5. -/
def tp0 : Top := [(5, { time := 0, root := 1, skips := [] })]

/-- The top from the second put on: top node 7 too, with its skip pointer to
top node 5 and that node's root time cached. -/
def tp2 : Top := tp0 ++ [(7, { time := 2, root := 4, skips := [(0, 5, 0)] })]

/-- The top after the first j transactions. -/
def top (j : Nat) : Top := if j < 2 then tp0 else tp2

theorem startB : StartB h :=
  ⟨1, 5, 1, 8, 20, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, fun x hx => by simp [h, s0, hx], rfl⟩

theorem made1 : Made s0 s1 c1 := by
  intro x h0 h1
  by_cases hx1 : x = 1
  · simp [s0, hx1] at h0
  · by_cases hx2 : x = 2
    · simp [c1, hx2]
    · simp [s1, hx1, hx2] at h1

theorem made2 : Made s1 s2 c2 := by
  intro x h0 h1
  by_cases hx1 : x = 1
  · simp [s1, hx1] at h0
  · by_cases hx2 : x = 2
    · simp [s1, hx2] at h0
    · by_cases hx3 : x = 3
      · simp [c2, hx3]
      · by_cases hx4 : x = 4
        · simp [c2, hx4]
        · by_cases hx6 : x = 6
          · simp [c2, hx6]
          · simp [s2, hx1, hx2, hx3, hx4, hx6] at h1

theorem made3 : Made s2 s3 c3 := by
  intro x h0 h1
  exfalso
  have : s3.obj x = none := by
    by_cases hx4 : x = 4
    · simp [s2, hx4] at h0
    · have : s3.obj x = s2.obj x := by simp [s2, s3, hx4]
      rw [this, h0]
  rw [this] at h1
  cases h1

theorem contract1 : Contract p 1 s0 ops1 [1] s1 := ⟨by decide, frame1⟩
theorem contract2 : Contract p 2 s1 ops2 [4, 6] s2 := ⟨by decide, frame2⟩
theorem contract3 : Contract p 3 s2 ops3 [4] s3 := ⟨by decide, frame3⟩

theorem bridge1 : bridgeOk h.topLevel 1 s0 s1 [1] c1 = true := by decide
theorem bridge2 : bridgeOk h.topLevel 2 s1 s2 [4, 6] c2 = true := by decide

theorem entries2 : entriesOf inner2.ks = [⟨2, .key 0 1⟩, ⟨2, .key 16 6⟩] := by decide

theorem entries3 : entriesOf inner3.ks = [⟨2, .key 0 1⟩, ⟨2, .key 16 6⟩, ⟨3, .del [0]⟩] := by
  simp [inner3, entriesOf, entriesFrom, newCvs, cvAt, List.eraseDups_cons]

theorem adds3 : addsOk s2 s3 [4] c3 = true := by
  simp [addsOk, newVals, s2, s3, c3, entries2, entries3]

theorem bridge3 : bridgeOk h.topLevel 3 s2 s3 [4] c3 = true := by
  simp only [bridgeOk, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨by decide, adds3⟩, by decide⟩, by decide⟩, by decide⟩, by decide⟩

theorem topChange1 : topChangeOk h.topLevel (h.P 0) s1 tp0 tp0 c1 = true := by decide
theorem topChange2 : topChangeOk h.topLevel (h.P 1) s2 tp0 tp2 c2 = true := by decide
theorem topChange3 : topChangeOk h.topLevel (h.P 2) s3 tp2 tp2 c3 = true := by decide

theorem touchOK (P : Struct BVal) (i : Nat) (c : Changes BVal) (hc : c.touch = []) :
    TouchOK h.spec P i c :=
  ⟨fun _ hx => by rw [hc] at hx; simp at hx, fun _ hx => by rw [hc] at hx; simp at hx,
    fun _ hx => by rw [hc] at hx; simp at hx⟩

/-- The history meets the contract, the bridge's clauses and the top's
clauses of 030-08 with clause TB. -/
theorem meetsTop : MeetsBridgeTop p h top where
  start := startB
  startTop := by decide
  step := by
    intro j hj
    have hj3 : j < 3 := hj
    match j, hj with
    | 0, _ =>
      exact ⟨contract1, bridge1, made1, Or.inl rfl, rfl, topChange1,
        touchOK _ _ _ rfl⟩
    | 1, _ =>
      exact ⟨contract2, bridge2, made2, topStepB_sound 2 tp0 tp2 (by decide), rfl,
        topChange2, touchOK _ _ _ rfl⟩
    | 2, _ =>
      exact ⟨contract3, bridge3, made3, Or.inl rfl, rfl, topChange3,
        touchOK _ _ _ rfl⟩

/-- So it meets `MeetsBridge`: the top's premise in the model's words holds
for it, with a top node made and its skip pointer. -/
theorem meetsBridge : MeetsBridge p h := meetsTop.meetsBridge

/-- What the theorems say of it, for BergDB's algorithm with any take: after
a crash after the second transaction, startup from the first three records
gives a structure that holds the tree of then, with its new root. -/
example (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) :
    Rep (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take 3)).P s2 :=
  (bridge_crash meetsBridge al hst 2 (by decide)).2.2

end Contract.BridgeExample3
