/-
The contract package (bergdb 030-11, the review of 030-07 to 030-09): the cut's
premise on the algorithm, `PolicyCutOK`, proved for every algorithm whose two
policies do not read the stream.

The theorems of reclaim's cut (`bridge_cut_restart`, `bridge_cut_handles`,
`full_cut`) assume `PolicyCutOK al`: the startup pos and the first available
time that the algorithm chooses are the same on a stream cut at or before its
first available time. A cut keeps every record's startup pos and first
available time (`SIS.Record.cut` empties only the versions, the transaction
and the gd list), so the clamps of `startupPos` and `firstAvail`, which read
the last record's, are unchanged; a policy that does not read the stream then
chooses the same (`policyCutOK_of_blind`). The trace checker's algorithm is
such a one: it takes Java's startup pos and first available time of each
transaction from the trace (`SIS.Check.algoOf`, lean/Check/Steps.lean). So
for the model's run that `tracecheck` compares with Java's records, the cut's
theorem needs no premise on the policy (`full_cut_blind`).
-/
import Contract.BridgeFull

namespace Contract

open SIS (cutStream Record lastSp lastFa Algo PolicyCutOK startupPos firstAvail)

variable {V T : Type}

/-- A cut keeps every record's startup pos and first available time. -/
theorem cut_map_sp (c : Nat) (S : SIS.Stream V T) :
    (cutStream c S).map (·.sp) = S.map (·.sp) ∧ (cutStream c S).map (·.fa) = S.map (·.fa) := by
  constructor <;>
  · apply List.ext_getElem (by simp [cutStream])
    intro n h1 h2
    simp only [cutStream, List.getElem_map, List.getElem_mapIdx]
    split <;> simp [Record.cut]

theorem cut_lastSp (c : Nat) (S : SIS.Stream V T) : lastSp (cutStream c S) = lastSp S := by
  unfold lastSp
  rw [← List.getLast?_map, ← List.getLast?_map, (cut_map_sp c S).1]

theorem cut_lastFa (c : Nat) (S : SIS.Stream V T) : lastFa (cutStream c S) = lastFa S := by
  unfold lastFa
  rw [← List.getLast?_map, ← List.getLast?_map, (cut_map_sp c S).2]

/-- An algorithm whose startup pos policy and first available time policy do
not read the stream meets `PolicyCutOK`. -/
theorem policyCutOK_of_blind (al : Algo V T)
    (hp : ∀ S S' D i tr, al.policy S D i tr = al.policy S' D i tr)
    (hf : ∀ S S' D i tr, al.faPolicy S D i tr = al.faPolicy S' D i tr) : PolicyCutOK al := by
  intro c S D i tr s _
  refine ⟨?_, ?_⟩
  · unfold startupPos
    rw [cut_lastSp, hp (cutStream c S) S]
  · unfold firstAvail
    rw [cut_lastFa, hf (cutStream c S) S]

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- Reclaim's cut with eviction, for a history in the contract's words, with
policies that do not read the stream (as the trace checker's, which takes
Java's choices from the trace): `full_cut` without the premise `PolicyCutOK`. -/
theorem full_cut_blind (hm : MeetsFull p h top) (al : SIS.Algo SIS.Check.BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hp : ∀ S S' D i tr, al.policy S D i tr = al.policy S' D i tr)
    (hf : ∀ S S' D i tr, al.faPolicy S D i tr = al.faPolicy S' D i tr)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2.1)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) :
    let db := (SIS.runHandlesCut h.spec al cs).1
    let r := SIS.run h.spec al (cs.map (·.1))
    db.S = SIS.cutStream (SIS.cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P :=
  full_cut hm al hj hmk (policyCutOK_of_blind al hp hf) cs hcs hcut hreads

end Contract
