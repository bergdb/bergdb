/-
The contract package (bergdb 030-14): Java's readers after a crash and after
restarts, end to end, for a history that meets every clause in the contract's
words (`MeetsFull`) and K-LEVEL (`KindsOK`, Recover.lean).

After a startup from the records, Java holds a tree of key nodes and values
and a top: the top nodes with their root pointers and skip pointers. The
theorems here say: if Java's tree holds the view that the model's startup
gives back, at a time t (`HoldsView`, RecoverJava.lean: every key node with
its level, the kind of its level, and klongs at t that are well formed and
whose entries are the view's; every value), and Java's top is the top that
the startup's structure holds (`topOfP`: the root's entries and the top
nodes' root and skip pointers), then Java's get and scan from its search
through the skip pointers (`jget`, `jscan`, Top.lean), at t, at a record's
time or between two records, give what the plain map after the first t
transactions gives.

Proved: these theorems. That the startup's structure holds the history's top
is proved (`MeetsFull.topOfP_eq`, Proof/RecoverTop.lean), with recovery; so is
that Java's search through it finds the view's space root. What is assumed,
for a claim about Java: that Java's startup builds a tree and a top that hold
these (030-04, 3.5, items 5 and 13: the bytes decode to what was written).
-/
import Contract.RecoverTheorems
import Contract.Proof.RecoverTop

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}

/-- **Java's reads after a crash.** A crash after transaction k keeps the first
k + 1 records. A tree that holds the view of the startup's structure at a time
t up to k, with the kinds of the levels, read with the top that the startup's
structure holds: Java's get and scan at t, at the record's time or after it
(`mid`), give what the plain map after the first t transactions gives. -/
theorem crash_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (mid : Bool) (s : Tree) :
    let P' := (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P
    let V := SIS.view h.spec P' t
    HoldsView V (kindOf kind V) t s → JReadsRight s (topOfP P') t mid (h.txs.map (·.ops)) := by
  intro P' V hs
  have hP := (full_recovery hm al hst k hk).1
  rw [run_P h al k hk] at hP
  have hV : V = SIS.view h.spec (h.P k) t := SIS.SameNodes.view hP t
  have htp : topOfP P' = top k := by
    rw [topOfP_congr hP]
    exact hm.topOfP_eq hM hk
  rw [hV] at hs
  rw [htp]
  exact hm.meetsBridge.java_reads hM hkd hk htk hs (hm.findRoot_view hM hk htk mid)

/-- **Java's reads after restarts and a crash.** The same, for the records that
a run with a crash and a startup after any transactions wrote. -/
theorem restart_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec)
    (ts : List (Nat × Bool)) (hts : ts.map (·.1) = h.ts) {k t : Nat} (hk : k ≤ h.txs.length)
    (htk : t ≤ k) (mid : Bool) (s : Tree) :
    let P' := (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P
    let V := SIS.view h.spec P' t
    HoldsView V (kindOf kind V) t s → JReadsRight s (topOfP P') t mid (h.txs.map (·.ops)) := by
  intro P' V
  have hP : P' = (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P := by
    show (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P = _
    rw [full_restart hm al hst ts hts]
  have hV : V = SIS.view h.spec
      (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P t := by
    show SIS.view h.spec P' t = _
    rw [hP]
  rw [hV, hP]
  exact crash_java_reads hm hM hkd al hst hk htk mid s

/-- The premise is met by the tree as written: after a crash after
transaction k, Java's get and scan on the tree after k, read at any time t up
to k with the top that the startup's structure holds, are right. -/
theorem crash_java_tree (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (mid : Bool) :
    let P' := (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P
    JReadsRight (h.tree k) (topOfP P') t mid (h.txs.map (·.ops)) := by
  intro P'
  have hP := (full_recovery hm al hst k hk).1
  rw [run_P h al k hk] at hP
  apply crash_java_reads hm hM hkd al hst hk htk mid (h.tree k)
  show HoldsView (SIS.view h.spec P' t) (kindOf kind (SIS.view h.spec P' t)) t (h.tree k)
  rw [SIS.SameNodes.view hP t]
  exact hm.meetsBridge.tree_holds hkd hk htk

end Contract
