/-
Self-indexed streams in Lean: examples and checks of T3 (bergdb item 007).

Not part of the trusted part. These are tests: they run the definitions of
SIS/Bound.lean on the structures of SIS/Example.lean. Added 2026-10-23.
Since 2026-10-28 (bergdb 007-08) also BergDB's take as bergdb 007-07 left it
(`takePolicy`, `javaTake`): its share and dither against Java's, bit for bit,
and its runs, with a constant setting, with restarts and with a decrease of the
setting, against T3_take, T3_take_restarts and T3_take_decrease; and the take
before 007-07, with its node limit, which does not keep up (`oldTake`).
-/
import SIS.BoundTheorems
import SIS.Example

namespace SIS.Example

open SIS

/-! ## Section 7: the policy is a startup distance of two records

With every record costing 1, a startup distance of 2 asks for s(i) = i - 2,
the policy of the example of section 7 (`algo1`). -/

def algo1sd : Algo Val Tr1 := { algo1 with policy := sdPolicy (fun _ => 1) 2 }

#guard (run spec1 algo1sd [.add 1 10, .add 2 20, .add 1 30, .add 1 40]).S == run1.S

/-! ## Example 2: a cost like bytes, the startup distance, and the take before 007-07 -/

/-- A cost of a version like its bytes: a header, 8 per entry, 8 per reference. -/
def vbytes (v : Version Val) : Nat := 16 + 8 * v.hist.length + 8 * v.refs.length

/-- A cost of a record like its bytes: a header, the transaction, 8 per
got-dirty id, and its versions. -/
def bytes2 (R : Record Val Tr2) : Nat :=
  32 + (if R.trans.isSome then 16 else 0) + 8 * R.gd.length + (R.vers.map vbytes).sum

/-- A sketch of BergDB's take before bergdb 007-07 (`TransSeq.take` until
`f89846d`), for these checks: from s(i-1) + 1 on, take whole transactions
while they begin at least d before the end of the stream, and fewer than two
have been taken or their got-dirty ids are fewer than `lim`. Java's limit was
4 per value of the transaction and 1 per KB; Java's limit on the size of a
record is left out. Since 007-07 the take is `takePolicy` (below). -/
def oldTake {V T : Type} (size : Record V T → Nat) (d lim : Nat) (S : Stream V T) : Nat :=
  go (lastSp S + 1) 0 0 (lastSp S)
where
  go (j taken nodes acc : Nat) : Nat :=
    if h : j < S.length then
      if d ≤ S.cost size j S.length ∧ (taken < 2 ∨ nodes < lim) then
        go (j + 1) (taken + 1) (nodes + S[j].gd.length) j
      else acc
    else acc
  termination_by S.length - j

/-- The cost of the startup section without its last record, R(s+1), ..., R(k-1). -/
def sec2 (S : Stream Val Tr2) : Nat := S.cost bytes2 (lastSp S + 1) (S.length - 1)

/-- BergDB's still-dirty test and marking, with the policy p. -/
def algo2 (p : Stream Val Tr2 → Dirty → Time → Tr2 → Nat) : Algo Val Tr2 :=
  { policy := p, stillDirty := javaTest spec2, mark := true }

/-- The states of a random run of example 2 with `algo2 p`. -/
def states2 (p : Stream Val Tr2 → Dirty → Time → Tr2 → Nat) (seed n : Nat) : List (DB Val Tr2) :=
  states spec2 (algo2 p) ((randomTs seed n).map (·.1))

-- T3, checked by running: with the startup distance policy, the section
-- without its last record costs less than d = 400 in every state.
#guard (states2 (sdPolicy bytes2 400) 1 60).all (fun db => sec2 db.S < 400)
#guard (states2 (sdPolicy bytes2 400) 2 60).all (fun db => sec2 db.S < 400)
-- And with restarts (T3_restarts).
#guard sec2 (runRestarts spec2 (algo2 (sdPolicy bytes2 400)) (randomTs 1 60)).S < 400

-- The take before 007-07 with a tight limit does not keep up: in some state
-- the section without its last record costs more than d (560 here, at the end).
#guard (states2 (fun S _ _ _ => oldTake bytes2 400 1 S) 1 60).any (fun db => 400 < sec2 db.S)

/-! ## BergDB's take since 007-07 (bergdb 007-08)

`takePolicy` and `javaTake` of SIS/Bound.lean on example 2. First the share's
arithmetic against Java's; then runs. -/

/-! Java's share and dither, bit for bit. The numbers on the right are Java's
`Double.doubleToLongBits` of `TransSeq.dither(p)` (a copy of its five lines)
and of the share's expression, printed by JDK 27 on 2026-10-28; Lean's `Float`
gives the same bits. The share 25 and the dithers of 1300 and 1200 are those
of `TransSeq.testShare`. -/

#guard [0, 1, 1200, 1300, 123456789, 50000000000, 9007199254740993].map (fun p => (dither p).toBits)
  == [0, 4606131375998723001, 4607131743264829540, 4600978861501654284, 4603666215157931066,
      4605233888489268388, 4603104620836595471]
#guard (share 100 100 1000 2000 800).toBits == 4627730092099895296
#guard (share 7 333 1001 12345 997).toBits == 4628809252918152948
#guard (share 123457 48 9999991 50000017 50000000).toBits == 4603512834796201358

/-- BergDB's pace's test for the next transaction, with the share and the
dither given, as `javaPace` computes it. -/
def paceTest (sh u : Float) (taken count : Nat) : Bool :=
  !(decide (sh < (taken + count).toFloat) && decide (sh - taken.toFloat ≤ u * count.toFloat))

-- `TransSeq.testShare`: a share of 25 nodes and transactions of 10 take two
-- transactions; the third, half of which fits, if the dither is below 0.5:
-- it is 0.41 for the stream's length 1300 and 0.99 for 1200.
#guard paceTest 25 (dither 1300) 0 10 && paceTest 25 (dither 1300) 10 10 &&
  paceTest 25 (dither 1300) 20 10 && !paceTest 25 (dither 1300) 30 10
#guard paceTest 25 (dither 1200) 10 10 && !paceTest 25 (dither 1200) 20 10
-- A transaction with no got-dirty nodes is taken while the share is not used
-- up (007-07, 2.4), and not after.
#guard paceTest 25 (dither 1200) 25 0 && !paceTest 25 (dither 1200) 26 0

/-- The own bytes of a transaction of example 2, as `bytes2` counts its
record: 48 for the header and the transaction, and 24 for its one data node's
version (`TransSeq.ownBytes`: 48 and the value nodes). -/
def own2 (_ : Tr2) : Nat := 72

/-- A constant setting of the startup distance. -/
def sdConst (c : Nat) : Time → Nat := fun _ => c

/-- A decrease of the setting from a to b after T(m): `Db.setStartupDistance`
in T(m+1). -/
def sdDecrease (a b m : Nat) : Time → Nat := fun i => if i ≤ m then a else b

/-- The deadline alone: a pace that never takes. -/
def noPace : Pace Val Tr2 := fun _ _ _ _ _ _ => false

/-- The section, `Stream.span`, after each transaction of a run. -/
def spans (sts : List (DB Val Tr2)) : List Nat := sts.map (fun db => db.S.span bytes2)

/-- T3_take_step by running: after every transaction of the states sts, the
section is shorter than the larger of twice the setting and the section
before. -/
def stepBoundB (sd : Time → Nat) (sts : List (DB Val Tr2)) : Bool :=
  (sts.zip sts.tail).all (fun (a, b) => b.S.span bytes2 < max (2 * sd a.S.length) (a.S.span bytes2))

/-- T3_take_decrease by running, for a change of the setting to b after T(m):
after every T(k), k ≥ m, the section is shorter than 2 b, or at least k - m
shorter than after T(m). -/
def decreaseB (b m : Nat) (sts : List (DB Val Tr2)) : Bool :=
  let xs := spans sts
  (List.range xs.length).all (fun k =>
    decide (k < m) || decide (xs[k]! < 2 * b) || decide (xs[k]! + (k - m) ≤ xs[m]!))

-- With a constant setting of 1000 (d_h = 2000), BergDB's take keeps the
-- section below d_h after every transaction (T3_take), and every step meets
-- T3_take_step; the section reaches 848, at 0.85 sd.
#guard (states2 (javaTake bytes2 own2 (sdConst 1000)) 1 60).all (fun db => db.S.span bytes2 < 2000)
#guard (states2 (javaTake bytes2 own2 (sdConst 1000)) 2 60).all (fun db => db.S.span bytes2 < 2000)
#guard stepBoundB (sdConst 1000) (states2 (javaTake bytes2 own2 (sdConst 1000)) 1 60)
#guard (spans (states2 (javaTake bytes2 own2 (sdConst 1000)) 1 60)).foldl max 0 == 848
-- With restarts: the same stream as without, since the take depends on S, D,
-- i and T(i) only (T2; Java's P2), and the bound holds (T3_take_restarts).
#guard (runRestarts spec2 (algo2 (javaTake bytes2 own2 (sdConst 1000))) (randomTs 1 60)).S ==
  (run spec2 (algo2 (javaTake bytes2 own2 (sdConst 1000))) ((randomTs 1 60).map (·.1))).S
#guard (runRestarts spec2 (algo2 (javaTake bytes2 own2 (sdConst 1000))) (randomTs 2 60)).S.span
  bytes2 < 2000

-- A decrease from 2000 to 400 after T(40), with BergDB's pace. Before it the
-- section is below 4000; right after it, 1016 and 816, above the new d_h of 800,
-- so "below twice the new setting at once" is false; the deadline is at the span
-- there, and the section shrinks until it is below 800 at T(43) and stays below
-- (T3_take_decrease); every step meets T3_take_step.
#guard stepBoundB (sdDecrease 2000 400 40) (states2 (javaTake bytes2 own2 (sdDecrease 2000 400 40)) 1 90)
#guard decreaseB 400 40 (states2 (javaTake bytes2 own2 (sdDecrease 2000 400 40)) 1 90)
#guard ((spans (states2 (javaTake bytes2 own2 (sdDecrease 2000 400 40)) 1 90)).drop 40).take 4 ==
  [1296, 1016, 816, 680]
-- The same with restarts: the same stream as without.
#guard (runRestarts spec2 (algo2 (javaTake bytes2 own2 (sdDecrease 2000 400 40))) (randomTs 1 90)).S ==
  (run spec2 (algo2 (javaTake bytes2 own2 (sdDecrease 2000 400 40))) ((randomTs 1 90).map (·.1))).S

-- The deadline alone (no pace), from 400 to 100 after T(30): the section is
-- above the new d_h, 200, for five transactions, and shrinks at each of them.
#guard stepBoundB (sdDecrease 400 100 30) (states2 (takePolicy bytes2 (sdDecrease 400 100 30) noPace) 1 80)
#guard decreaseB 100 30 (states2 (takePolicy bytes2 (sdDecrease 400 100 30) noPace) 1 80)
#guard ((spans (states2 (takePolicy bytes2 (sdDecrease 400 100 30) noPace) 1 80)).drop 30).take 7 ==
  [672, 616, 608, 456, 328, 280, 0]

-- `KeepsUp size (2 * sd)` does not hold for the take: in transaction 31 of
-- that run, the stream's span, 672, is longer than d_h = 200, and the take asks
-- for an earlier startup pos than a startup distance of 200 does.
#guard
  let db := ((states2 (takePolicy bytes2 (sdDecrease 400 100 30) noPace) 1 80)[30]?).getD (init spec2)
  db.S.length == 31 && db.S.span bytes2 == 672 &&
  takePolicy bytes2 (sdDecrease 400 100 30) noPace db.S db.D 31 ⟨0, 0⟩ < sdTarget bytes2 200 db.S

end SIS.Example
