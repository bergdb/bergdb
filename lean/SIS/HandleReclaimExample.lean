/-
Reclaim with handles by running (bergdb 005-62): ReclaimExample.lean's runs of
example 4 with cuts, on the memory with handles (SIS/Handle.lean). After every
transaction the records are the run's, cut at the largest cut so far, and D is
the run's (T12 over handles); reads from the first available time on give P;
at a cut, reads on the cut stream from the running memory give P (T9 over
handles), and so do reads after the restart from the cut stream; at the end,
the lookups from the first available time on are the run's. Under the five
eviction schedules of HandleExample.lean. Not part of the trusted part.
-/
import SIS.ReclaimExample
import SIS.HandleExample
import SIS.HandleReclaimTheorems

namespace SIS.HandleReclaimExample

open SIS SIS.Example SIS.PhysExample SIS.EvictExample SIS.ReclaimExample SIS.HandleExample

variable {T : Type}

/-- As ReclaimExample's `checkEvictCut`, with handles and `HandleExample`'s
schedule `policy`: the run with handles that restarts from cut streams
(`runHandlesCut`, with the operations computed from the memory). After every
transaction: the records are the run's, cut at the largest cut so far, and D is
the run's; the schedule, reads at three times from the first available time on
(they give P), the schedule again. At a cut: reads on the cut stream from the
running memory at every time from the first available time on (T9), then the
restart from the cut stream and its reads. At the end: the lookups from the
first available time on are the run's. Returns (transactions, failures). -/
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
        let ok' := ok && t9 && r2
        (((db2, m4, cut), max cm c, n + 1, bad + (if ok' then 0 else 1)))
      | none => (((db', m3, S0), cm, n + 1, bad + (if ok then 0 else 1))))
    ((init sp, handleStartup sp (init sp).S, (init sp).S), 0, 0, 0)
  let whole := run sp al ts1
  let same := equivFromB sp (lastFa whole.S) ts1.length r.1.1.P whole.P
  (r.2.2.1, r.2.2.2 + (if same then 0 else 1))

-- Example 4 with cuts (largest cuts 10 and 5), two policies, the five schedules.
#guard [0, 1, 2, 3, 4].all (fun pol =>
  checkHandleCut spec4 (algo4 (fun _ _ i _ => i - 2)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 2))
    (randomTs4 5 20)) pol 5 == (20, 0))
#guard [0, 1, 2, 3, 4].all (fun pol =>
  checkHandleCut spec4 (algo4 (fun _ _ i _ => i - 1)) (cutsFor spec4 (algo4 (fun _ _ i _ => i - 1))
    (randomTs4 6 20)) pol 6 == (20, 0))

end SIS.HandleReclaimExample
