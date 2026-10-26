/-
A reachable historical-reference obligation in the existing SIS algorithm.
Executable checks, not a Java Dag trace or a new universal theorem.
-/
import SIS.Example

namespace BergDB.References.SISCase

open SIS SIS.Example

inductive Transaction where
  | moveChild
  | edit (nodeId value : Nat)
  | idle
  deriving DecidableEq, Repr

/-- Every current non-root node has one current parent. Moving child 3
leaves a dead slot in parent 1, which remains current through its other child. -/
def spec : Spec Val Transaction where
  ptrs := ptrs
  live := live
  init := [(0, mk 3 [.ref 1, .ref 2]),
           (1, mk 2 [.slot 0 3, .slot 1 4]),
           (2, mk 2 [.slot 0 5]),
           (3, mk 1 [.dat 0]), (4, mk 1 [.dat 0]), (5, mk 1 [.dat 0])]
  exec := fun transaction _ current =>
    match transaction with
    | .moveChild =>
      { new := [], adds := [(1, .slot 0 5), (2, .slot 0 3)] }
    | .edit nodeId value =>
      if (current nodeId).isSome then { new := [], adds := [(nodeId, .dat value)] }
      else { new := [], adds := [] }
    | .idle => { new := [], adds := [] }

def algorithm : Algo Val Transaction :=
  { policy := fun _ _ i => i - 1, stillDirty := exactTest spec }

def transactions : List Transaction :=
  [.moveChild, .edit 3 10, .idle, .idle, .idle, .idle, .edit 4 20, .idle]

def before : DB Val Transaction := run spec algorithm (transactions.take 6)
def after : DB Val Transaction := run spec algorithm transactions

def currentParents (P : Struct Val) (time nodeId : Nat) : List NodeId :=
  P.filterMap (fun parent =>
    if reachable spec P time parent.1 &&
       (live (parent.2.hist.upTo time)).contains nodeId then some parent.1 else none)

-- This concrete run meets the existing executable A1--A4/data checks.
#guard runOKB spec algorithm transactions
#guard (states spec algorithm transactions).all (fun db =>
  let time := db.S.length - 1
  (db.P.map Prod.fst).all (fun nodeId => nodeId == 0 ||
    (currentParents db.P time nodeId).length == 1))

-- Parent 1's last stored image still names child 3's original image.
#guard ((before.S.lv 1).bind (fun image => image.ref? 3)) = some 0
-- The child has since been updated and written through its current parent 2.
#guard (before.S.lv 3).map Version.recNo = some 3
-- It is clean, outside dirty authority, and absent from the recent suffix.
#guard !inD before.D 3
#guard !(before.S.drop (lastSp before.S + 1)).any
  (fun record => record.vers.any (fun image => image.node == 3))

-- A later edit of the other child writes parent 1 again. mkVersion requires
-- the latest address of its dead child, despite that child's empty suffix entry.
#guard ((after.S.versionAt 8 1).bind (fun image => image.ref? 3)) = some 3
#guard !(live ((((before.P.get? 1).map Node.hist).getD []).upTo 6)).contains 3

-- The original image is already complete for the sole time at which P's
-- dead edge to Y is followed in this trace (time 0).
#guard (before.S.versionAt 0 3).any (good spec before.S before.P 0)

/-- A single alternative record keeps that complete historical anchor.
This is a constructed record experiment, not an implemented write algorithm. -/
def frozenStream : SIS.Stream Val Transaction := after.S.map (fun record =>
  { record with vers := record.vers.map (fun image =>
      if image.node == 1 && image.recNo == 8 then
        { image with refs := image.refs.map (fun ref =>
            if ref.1 == 3 then (3, 0) else ref) }
      else image) })
#guard ((frozenStream.versionAt 8 1).bind (fun image => image.ref? 3)) = some 0
#guard checkT1 spec true { after with S := frozenStream }

-- Original Rule R/replay recovery and byte-independent abstract T2 still work.
#guard (states spec algorithm transactions).all (checkT1 spec true)
#guard (runRestarts spec algorithm
  (transactions.map (fun transaction => (transaction, true)))).S == after.S

-- A compact executable trace: record, startup position, written nodes/refs.
#eval after.S.zipIdx.map (fun (entry : Record Val Transaction × Nat) =>
  (entry.2, entry.1.sp, entry.1.vers.map (fun image => (image.node, image.refs))))

end BergDB.References.SISCase
