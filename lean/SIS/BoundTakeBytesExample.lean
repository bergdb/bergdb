/-
Self-indexed streams in Lean: BergDB's take with its byte limit, by running
(bergdb item 007; SIS/BoundTakeBytes.lean). Not part of the trusted part:
checks by running, not proofs. Added 2026-11-13.

The structure: a root (level 1) with eight leaves 1, ..., 8 (level 0, index
nodes that take data entries, as in example 1 of SIS/Example.lean). A
transaction (y, b) writes leaf y and costs b (its record's own bytes, `own`);
step 3 marks the leaf and the root. BergDB's still-dirty test, the take with no
pace (the deadline alone), a constant setting sd = 3: T3_take's assumptions
with M = 3, so without the byte limit the span stays below 2 M = 6.

1. A transaction whose nodes do not fit: with 1 byte a node and a limit of 1
   byte, T(1)'s two got-dirty nodes (the leaf and the root) never fit. Java's
   take ends at the first transaction that does not fit, also after the
   deadline: the startup pos stays 0 for ever and the span grows by one a
   record (12 after 13 transactions). So the byte limit can stop the take's
   progress, unless every transaction's nodes fit in the limit
   (`takePolicyB_progress`), which Java's own part of a record below 1/16 of
   the limit gives (005-31, as SIS/Bound.lean says).
2. Every transaction fits, yet T3_take's bound fails: a limit of 2 bytes takes
   one or two transactions a record. Eight cheap transactions, then one of
   cost 100, then cheap ones. After the costly record every cheap one before it
   is past the deadline, but each record takes only what fits, so the costly
   one stays in the section for several records, and the span is above 100 >
   2 M. Without the limit (`takePolicy`) the same run keeps the span below 6
   (T3_take). The take still moves every record (progress), but T3's bound on
   the span needs a bound on the transactions that wait behind the limit.
-/
import SIS.BoundTakeBytes
import SIS.Example

namespace SIS.BoundTakeBytesExample

open SIS SIS.Example

/-- A transaction: the leaf it writes and its own bytes. -/
abbrev TrB := Nat × Nat

def specB : Spec Val TrB where
  ptrs := ptrs
  live := live
  exec := fun tr i _ => { new := [], adds := [(tr.1, .dat i)] }
  init := (0, mk 1 ((List.range 8).map (fun y => .ref (y + 1)))) ::
    (List.range 8).map (fun y => (y + 1, mk 0 []))
  rootVal := .ref

/-- The cost of a record: its transaction's own bytes, 1 for R(0). -/
def own (R : Record Val TrB) : Nat := (R.trans.map (·.2)).getD 1

def noPace : Pace Val TrB := fun _ _ _ _ _ _ => false

def algoB (nodeB maxB : Nat) : Algo Val TrB :=
  { policy := takePolicyB own (fun _ => 3) noPace nodeB maxB, stillDirty := javaTest specB,
    mark := true }

def algoT : Algo Val TrB :=
  { policy := takePolicy own (fun _ => 3) noPace, stillDirty := javaTest specB, mark := true }

/-- The spans after each transaction of the run. -/
def spans (al : Algo Val TrB) (ts : List TrB) : List Nat :=
  (List.range (ts.length + 1)).map (fun j => (run specB al (ts.take j)).S.span own)

/-- Case 1: thirteen transactions of cost 1. -/
def ts1 : List TrB := (List.range 13).map (fun j => (j % 8 + 1, 1))

#guard runOKB specB (algoB 1 1) ts1
#guard lastSp (run specB (algoB 1 1) ts1).S == 0
#guard spans (algoB 1 1) ts1 == (List.range 14).map (· - 1)
#guard (run specB (algoB 1 1) ts1).S.span own == 12
-- T(1)'s got-dirty nodes, the leaf 1 and the root: 2 bytes, above the limit.
#guard ((run specB (algoB 1 1) ts1).D.filter (fun e => e.2 == 1)).length == 2
-- Without the limit, the span stays below 2 M = 6.
#guard (spans algoT ts1).all (· < 6)

/-- Case 2: eight of cost 1, one of cost 100, eight of cost 1. -/
def ts2 : List TrB :=
  (List.range 8).map (fun j => (j + 1, 1)) ++ [(1, 100)] ++ (List.range 8).map (fun j => (j + 1, 1))

#guard runOKB specB (algoB 1 2) ts2
#guard (spans (algoB 1 2) ts2).any (fun x => 100 ≤ x)
#guard (spans algoT ts2).all (· < 6)
-- Every transaction's got-dirty nodes fit in the limit of 2 bytes...
#guard (List.range (ts2.length + 1)).all (fun j =>
  let db := run specB (algoB 1 2) (ts2.take j)
  (List.range (j + 1)).all (fun t => decide ((db.D.filter (fun e => e.2 == t)).length ≤ 2)))
-- ...and the startup pos moves in every record once the span is 2 M or more.
#guard (List.range ts2.length).all (fun j =>
  let S := (run specB (algoB 1 2) (ts2.take j)).S
  let S' := (run specB (algoB 1 2) (ts2.take (j + 1))).S
  !(decide (6 ≤ S.span own) && decide (lastSp S + 1 < S.length)) || decide (lastSp S < lastSp S'))

end SIS.BoundTakeBytesExample
