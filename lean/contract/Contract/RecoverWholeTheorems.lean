/-
The contract package (bergdb 030-17): Java's reads after a crash, after
restarts and under eviction, with one premise for every time: Java's tree
holds the model's structure whole (`HoldsP`, RecoverWhole.lean), not its view
at each time (030-14's `HoldsView`). For a history that meets `MeetsFull` and
K-LEVEL.

Each theorem: if Java's tree after the startup (or the writer's, under
eviction) holds the structure that the model gives back whole, with each key
node's kind from its level, then Java's get and scan from its search through
the skip pointers are right at every time up to the last transaction, at a
record's time or between two records. The premise is met by the tree as
written (`crash_java_tree_whole`).

Proved: these theorems, from 030-14's and RecoverCutTheorems.lean's, and
`MeetsFull.holdsView_whole` (Proof/RecoverWhole.lean). Assumed, for a claim
about Java: 030-04, 3.5, item 13 (Java's startup gives each key node klongs
whose entries are the node's in the stream, its kind, and each value its
value; the bytes decode to what was written, item 5).
-/
import Contract.RecoverCutTheorems
import Contract.Proof.RecoverWhole

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}

/-- **Java's reads after a crash, one premise for every time.** A crash after
transaction k keeps the first k + 1 records. A tree that holds the startup's
structure whole, with the kinds of the levels, read with the top that the
startup's structure holds: Java's get and scan at every time t up to k, at
the record's time or after it, are right. -/
theorem crash_java_whole (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k : Nat}
    (hk : k ≤ h.txs.length) (s : Tree) :
    let P' := (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P
    HoldsP h.spec P' (kindOfP kind P') s →
      ∀ t, t ≤ k → ∀ mid, JReadsRight s (topOfP P') t mid (h.txs.map (·.ops)) := by
  intro P' hs t htk mid
  have hP := (full_recovery hm al hst k hk).1
  rw [run_P h al k hk] at hP
  exact crash_java_reads hm hM hkd al hst hk htk mid s (hm.holdsView_same hk htk hP hs)

/-- **Java's reads after restarts and a crash, one premise for every time.** -/
theorem restart_java_whole (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec)
    (ts : List (Nat × Bool)) (hts : ts.map (·.1) = h.ts) {k : Nat} (hk : k ≤ h.txs.length)
    (s : Tree) :
    let P' := (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P
    HoldsP h.spec P' (kindOfP kind P') s →
      ∀ t, t ≤ k → ∀ mid, JReadsRight s (topOfP P') t mid (h.txs.map (·.ops)) := by
  intro P' hs t htk mid
  have hPP : P' = (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P := by
    show (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P = _
    rw [full_restart hm al hst ts hts]
  have hP := (full_recovery hm al hst k hk).1
  rw [run_P h al k hk, ← hPP] at hP
  exact restart_java_reads hm hM hkd al hst ts hts hk htk mid s (hm.holdsView_same hk htk hP hs)

/-- **Java's reads under eviction, one premise for every time.** In a run with
handles (reads and evictions after each transaction, restarts after any),
after the first j transactions: a tree that holds the writer's structure
whole, with the kinds of the levels, read with any top that holds the
history's top after j from t: Java's get and scan at every time t up to j are
right. -/
theorem handles_java_whole (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j : Nat}
    (hjl : j ≤ ts.length) (s : Tree) :
    let P := (SIS.runHandles h.spec al (ts.take j)).1.P
    HoldsP h.spec P (kindOfP kind P) s →
      ∀ t, t ≤ j → ∀ mid (tp : Top), TopFrom t (top j) tp →
        JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  intro P hs t htj mid tp htp
  have hjn := len_of_ts hts hjl
  have h1 := (bridge_handles_records hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl).2.2
  rw [take_map_ts ts hts j, run_P h al j hjn] at h1
  exact handles_java_reads hm hM hkd al hj hmk ts hts hjl htj mid s tp
    (hm.holdsView_same hjn htj h1 hs) htp

/-- The premise is met by the tree as written: after a crash after transaction
k, the tree after k holds the startup's structure whole, with the kinds of the
levels. -/
theorem crash_java_tree_whole (hm : MeetsFull p h top) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k : Nat}
    (hk : k ≤ h.txs.length) :
    let P' := (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P
    HoldsP h.spec P' (kindOfP kind P') (h.tree k) := by
  intro P'
  have hP := (full_recovery hm al hst k hk).1
  rw [run_P h al k hk] at hP
  rw [kindOfP_congr kind hP]
  exact holdsP_congr hP (hm.tree_holdsP hkd hk)

end Contract
