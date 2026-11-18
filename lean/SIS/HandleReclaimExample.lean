/-
Reclaim with handles by running (bergdb 005-62): ReclaimExample.lean's runs of
example 4 with cuts, on the memory with handles (SIS/Handle.lean). After every
transaction the records are the run's, cut at the largest cut so far, and D is
the run's (T12 over handles); reads from the first available time on give P;
at a cut, reads on the cut stream from the running memory give P (T9 over
handles), and so do reads after the restart from the cut stream; at the end,
the lookups from the first available time on are the run's. Under the five
eviction schedules of HandleExample.lean. Also rule 4 by position after a cut
(bergdb 005-62, question 2): at every restart, with Java's skip of the pointers
below the stream's first position, it links what rule 4 by node id links, and
the pointers it skips name no node with a canonical object (`posCutCounts`).
Not part of the trusted part.
-/
import SIS.ReclaimExample
import SIS.HandleExample
import SIS.HandleReclaimTheorems

namespace SIS.HandleReclaimExample

open SIS SIS.Example SIS.PhysExample SIS.ReclaimExample SIS.HandleExample

variable {T : Type}

/-- The pointers of each object of m, which rule 4 changes and nothing else. -/
def hPtrsOf (m : HMem Val) : List (Nat × List (NodeId × HPtr)) := m.objs.map (fun p => (p.1, p.2.ptrs))

/-- With `HandleExample`'s schedule `policy`: the run with handles that restarts
from cut streams (`runHandlesCut`, with the operations computed from the memory).
After every transaction: the records are the run's, cut at the largest cut so
far, and D is the run's; the schedule, reads at three times from the first
available time on (they give P), the schedule again. At a cut: reads on the cut
stream from the running memory at every time from the first available time on
(T9), then the restart from the cut stream and its reads; and rule 4 by position
with the cut as the stream's first position, at the restart's cut and at the
largest cut so far, links what rule 4 by node id links (`Rule4PosCut_handles`,
bergdb 005-62, at the tag `proofs-2026-11-17`). At the end: the lookups from the first available time on are the
run's. Returns (transactions, failures). -/
def checkHandleCut [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Option Nat))
    (policy seed : Nat) : Nat × Nat :=
  let ts1 := ts.map (·.1)
  let r := ts.zipIdx.foldl
    (fun (acc : (DB Val T × HMem Val × SIS.Stream Val T) × Nat × Nat × Nat) (p, j) =>
      let ((db, m, S0), cm, n, bad) := acc
      let (db', m') := handleTrans sp al S0 db m p.1
      let after := run sp al (ts1.take (j + 1))
      let k := db'.S.length - 1
      let f := lastFa after.S
      let m1 := hschedule policy seed j db'.D m'
      let (m2, readsOK) := readsH sp S0 db' m1 [k, (f + k) / 2, f + lcg (seed + j) % (k + 1 - f)]
      let m3 := hschedule policy (seed + 7) j db'.D m2
      let ok := db'.S == cutStream cm after.S && db'.D == after.D && readsOK
      match p.2 with
      | some c =>
        let cut := cutStream c db'.S
        let (_, t9) := readsH sp S0 { db' with S := cut } m3 (List.range' f (k + 1 - f))
        let db2 := startup sp cut
        let m4 := handleStartup sp cut
        let (_, r2) := readsH sp cut db2 m4 (List.range' f (k + 1 - f))
        let pos := hPtrsOf (handleStartupPosFrom sp c cut) == hPtrsOf m4 &&
          hPtrsOf (handleStartupPosFrom sp (max cm c) cut) == hPtrsOf m4
        let ok' := ok && t9 && r2 && pos
        (((db2, m4, cut), max cm c, n + 1, bad + (if ok' then 0 else 1)))
      | none => (((db', m3, S0), cm, n + 1, bad + (if ok then 0 else 1))))
    ((init sp, handleStartup sp (init sp).S, (init sp).S), 0, 0, 0)
  let whole := run sp al ts1
  let same := equivFromB sp (lastFa whole.S) ts1.length r.1.1.P whole.P
  (r.2.2.1, r.2.2.2 + (if same then 0 else 1))

-- The fixed run of example 4 with a cut at 3 (ReclaimExample's `tsCut4`), the five
-- schedules.
#guard [0, 1, 2, 3, 4].all (fun pol => checkHandleCut spec4 al4 tsCut4 pol 1 == (15, 0))

-- Example 4 with cuts (largest cuts 10 and 5), two policies, the five schedules.
#guard [0, 1, 2, 3, 4].all (fun pol =>
  checkHandleCut spec4 (algo4 (fun _ _ i _ => i - 2)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 2))
    (randomTs4 5 20)) pol 5 == (20, 0))
#guard [0, 1, 2, 3, 4].all (fun pol =>
  checkHandleCut spec4 (algo4 (fun _ _ i _ => i - 1)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 1))
    (randomTs4 6 20)) pol 6 == (20, 0))

/-! ## Rule 4 by position after a cut (bergdb 005-62), by running

`rule4PosCut_handles` (SIS/Proof/HandleCutPos.lean) proves that rule 4 by
position on a stream cut safely, with any first position up to the cut
(`HMem.linkDPosFrom`), links what rule 4 by node id links. Here, at the restarts
of runs with cuts, the pointers that Java's rule skips: those of the canonical
objects of D's nodes that hold no handle and name a record below the cut. -/

/-- At each restart of the run with cuts cs (from `cutsFor`), from the stream of
the run without restarts cut at the largest cut so far, with the memory before
rule 4: [restarts; those with a cut above 0; pointers of the canonical objects of
D's nodes that hold no handle and name a record below the cut; of those, the
ones to a node with a canonical object (none, by `Rule4PosCut_handles`, at the tag `proofs-2026-11-17`);
restarts where rule 4 by position with the largest cut as the first position
differs from rule 4 by node id (none); with the restart's own cut (none); and
without the skip, `handleStartupPos` (none)]. -/
def posCutCounts [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (cs : List (T × Option Nat)) :
    List Nat :=
  let tr := cs.map (·.1)
  let add := fun (l : List Nat) (i n : Nat) => l.set i (l.getD i 0 + n)
  cs.zipIdx.foldl (fun (acc : List Nat) (p, j) => match p.2 with
    | some c =>
      let cm := cutMax ((cs.take (j + 1)).map (·.2))
      let S := cutStream cm (run sp al (tr.take (j + 1))).S
      let m := ((lazyStartup sp S).sectionPos S).toH
      let D := (startup sp S).D
      let below := m.objs.foldl (fun (n : Nat × Nat) o =>
        if !(o.2.canonical && inD D o.2.node) then n else
        o.2.ptrs.foldl (fun (n : Nat × Nat) q =>
          match q.2.handle, q.2.ref with
          | none, some r =>
            if r < cm then (n.1 + 1, n.2 + (if (m.canonicalOf q.1).isSome then 1 else 0)) else n
          | _, _ => n) n) (0, 0)
      let byId := hPtrsOf (handleStartup sp S)
      let acc := add acc 0 1
      let acc := add acc 1 (if cm > 0 then 1 else 0)
      let acc := add acc 2 below.1
      let acc := add acc 3 below.2
      let acc := add acc 4 (if hPtrsOf (handleStartupPosFrom sp cm S) == byId then 0 else 1)
      let acc := add acc 5 (if hPtrsOf (handleStartupPosFrom sp c S) == byId then 0 else 1)
      add acc 6 (if hPtrsOf (handleStartupPos sp S) == byId then 0 else 1)
    | none => acc) [0, 0, 0, 0, 0, 0, 0]

-- The fixed runs above: 9 and 2 pointers below the cut, none to a node with a canonical object.
#guard posCutCounts spec4 (algo4 (fun _ _ i _ => i - 2)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 2))
    (randomTs4 5 20)) == [5, 4, 9, 0, 0, 0, 0]
#guard posCutCounts spec4 (algo4 (fun _ _ i _ => i - 1)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 1))
    (randomTs4 6 20)) == [4, 1, 2, 0, 0, 0, 0]

end SIS.HandleReclaimExample
