/-
The contract package (bergdb 030-14): the reads after a crash, after
restarts and under eviction, for one history that meets their premises
(`BridgeExample4.h4`, bergdb 030-11: a put; a put that makes a new inner root
and with it a top node with a skip pointer; a delete by a bitmap; an
overwrite with a touch). So the theorems of RecoverTheorems.lean are not
vacuous: the premises hold for a history with every kind of change, and the
theorems give the reads of the model's view at the times 0 to 4.

The algorithm is any one with BergDB's still-dirty test, here `h4.al0`
(startup pos 0), with the access path marked for the run with handles. The
kinds come from the levels: the leaves are on level 1, the inner root on
level 2, so K-LEVEL holds with the TREE line's h = 1 (`kinds4`). The
statements below are closed: no premise is left.
-/
import Contract.RecoverJavaTheorems
import Contract.BridgeExample4

namespace Contract.RecoverExample

open Contract Contract.Example3 Contract.BridgeExample3 Contract.BridgeExample4

/-- An algorithm with BergDB's still-dirty test that marks the access path. -/
def alm : SIS.Algo SIS.Check.BVal Nat := { h4.al0 with mark := true }

/-- The run with handles: no restart and no cache operation after the first
two transactions, a restart after the third, a read at time 1 and an
eviction of handle 0 after the fourth. -/
def ts4 : List (Nat × Bool × List SIS.HCacheOp) :=
  [(1, false, []), (2, false, []), (3, true, []), (4, false, [.read 1, .evict 0])]

theorem ts4_map : ts4.map (·.1) = h4.ts := by decide

/-- The kinds by level, as a trace's TREE line with h = 1 gives them. -/
abbrev kind4 : Nat → Bool := kindOfHeight 1

/-- K-LEVEL: every key node has the kind of its level. -/
theorem kinds4 : KindsOK kind4 h4 := by
  refine ⟨?_, ?_⟩
  · intro x n hx
    by_cases h1 : x = 1
    · subst h1
      simp [h4, s0] at hx
      subst hx
      decide
    · simp [h4, s0, h1] at hx
  · intro j hj
    have hj4 : j < 4 := hj
    interval_cases j <;> rfl

/-- After a crash after the fourth transaction, a startup from the five
records: a get at time 3 of the key [16] gives 6, and at time 4 (the
overwrite) 9; the key [8] is gone at time 3 (the delete). -/
theorem crash_get16 :
    let V := SIS.view h4.spec (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 5)).P 3
    vget V (kindOf kind4 V) [16] = some 6 := by
  intro V
  rw [(crash_reads BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 4) (t := 3)
    (by decide) (by decide)).1 [16]]
  decide

theorem crash_get16_4 :
    let V := SIS.view h4.spec (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 5)).P 4
    vget V (kindOf kind4 V) [16] = some 9 := by
  intro V
  rw [(crash_reads BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 4) (t := 4)
    (by decide) (le_refl _)).1 [16]]
  decide

theorem crash_get8 :
    let V := SIS.view h4.spec (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 5)).P 3
    vget V (kindOf kind4 V) [8] = none := by
  intro V
  rw [(crash_reads BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 4) (t := 3)
    (by decide) (by decide)).1 [8]]
  decide

/-- After a crash after the second transaction (three records kept): a scan
at time 2 gives both keys, with their values of then. -/
theorem crash_scan2 :
    let V := SIS.view h4.spec (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 3)).P 2
    vscan V (kindOf kind4 V) {} 10 = [([8], 5), ([16], 6)] := by
  intro V
  rw [(crash_reads BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 2) (t := 2)
    (by decide) (le_refl _)).2 {} (by decide) 10]
  decide

/-- With restarts after the first and the third transaction and a crash after
the fourth: the scan at time 4 gives the one key left, with its new value. -/
theorem restart_scan4 :
    let V := SIS.view h4.spec (SIS.startup h4.spec
      ((SIS.runRestarts h4.spec h4.al0 [(1, true), (2, false), (3, true), (4, false)]).S.take 5)).P 4
    vscan V (kindOf kind4 V) {} 10 = [([16], 9)] := by
  intro V
  rw [(restart_reads BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl _ (by decide) (k := 4)
    (t := 4) (by decide) (le_refl _)).2 {} (by decide) 10]
  decide

/-- Under eviction with handles (`ts4`: a restart after the third transaction,
a read and an eviction after the fourth): after the fourth transaction, a
read through the handles at time 2 returns a view on which the scan gives
both keys of then. -/
theorem evict_scan2 :
    let V := viewOfList ((SIS.runHandles h4.spec alm (ts4.take 4)).2.1.read h4.spec
      (SIS.runHandles h4.spec alm (ts4.take 4)).2.2
      (SIS.run h4.spec alm ((ts4.take 4).map (·.1))).S 2).2
    vscan V (kindOf kind4 V) {} 10 = [([8], 5), ([16], 6)] := by
  intro V
  rw [(evict_reads BridgeExample4.meetsFull (by decide) kinds4 alm rfl rfl ts4 ts4_map (j := 4)
    (t := 2) (by decide) (by decide)).2 {} (by decide) 10]
  decide

/-- Java's reader after a crash after the fourth transaction, with the top
that the startup gives back: at time 1, between the records 1 and 2, its
search goes from top node 7 through the skip pointer to top node 5, and the
get of [8] gives 5; at time 3 the get of [16] gives 6. -/
theorem crash_java_get8 :
    let P' := (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 5)).P
    jget (h4.tree 4) (topOfP P') 1 true [8] = some 5 := by
  intro P'
  rw [(crash_java_tree BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 4) (t := 1)
    (by decide) (by decide) true).1 [8]]
  decide

theorem crash_java_get16 :
    let P' := (SIS.startup h4.spec ((SIS.run h4.spec h4.al0 h4.ts).S.take 5)).P
    jget (h4.tree 4) (topOfP P') 3 false [16] = some 6 := by
  intro P'
  rw [(crash_java_tree BridgeExample4.meetsFull (by decide) kinds4 h4.al0 rfl (k := 4) (t := 3)
    (by decide) (by decide) false).1 [16]]
  decide

end Contract.RecoverExample
