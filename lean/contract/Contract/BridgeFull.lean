/-
The contract package (bergdb 030-07): the bridge's theorems for a history
that meets every clause in the contract's words (`MeetsFull`,
BridgeTop.lean): the writer's contract, the bridge's clauses about key nodes
and values, the top's clauses of bergdb 030-08 with clause TB, the touch,
TREE, A6' and A-COPY. No clause is in the abstract model's words, but TB
reads the top nodes' and the root's levels, which the contract's top does
not have, from the change's NEW lines through the model's structure
(bergdb 030-11, finding 5).

Such a history meets `MeetsBridge` and `MeetsEvict` (`MeetsFull.meetsBoth`),
so every theorem of BridgeTheorems.lean holds for it; the main ones are
stated here again for it. It also meets 030-08's `MeetsTop`
(`MeetsFull.meetsTop`), so Java's readers, which start from the search
through the skip pointers, are right on it at every time (`jget_right`,
`jscan_right`, TheoremsTop.lean).

Proved: these theorems from `MeetsFull`. Tested, not proved: that Java's
writer meets `MeetsFull` (the bridge checker computes it for every trace:
`fullHistoryOk_meets`), and that Java's records are the model's
(`tracecheck`, on the same instance of the model). Each transaction's change
is given: that Java's writer makes the same change after a restart or with
eviction is 030-04, 3.5, item 9 (bergdb 030-11, finding 1).
-/
import Contract.BridgeTheorems
import Contract.TheoremsTop
import Contract.Proof.BridgeWords

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- A history that meets every clause in the contract's words meets the
bridge's clauses and what eviction needs, with the clauses about the top,
the touch, A6' and A-COPY in the model's words proved. -/
theorem MeetsFull.meetsBoth (hm : MeetsFull p h top) : MeetsBridge p h ∧ MeetsEvict h :=
  ⟨hm.meetsBridge, hm.meetsEvict⟩

/-- The start's top, computed, is 030-08's start of the top, and the start
tree's space roots are its root pointers. -/
theorem topStartOk_sound {c0 : Changes BVal} {tp0 : Top} {s0 : Tree}
    (ht : topStartOk c0 tp0 s0 = true) : TopStart tp0 ∧ s0.roots = rootsOf tp0 := by
  unfold topStartOk at ht
  split at ht
  · rename_i z n z' _ _ _
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ht
    exact ⟨⟨z, n, rfl, ht.1.1.2, ht.1.2⟩, ht.2⟩
  · cases ht

/-- A history that meets every clause in the contract's words meets the
contract with TREE and the top of bergdb 030-08 (`MeetsTop`): after the first
j transactions, for every j. So Java's readers are right on it
(TheoremsTop.lean). -/
theorem MeetsFull.meetsTop (hm : MeetsFull p h top) (hM : 1 ≤ p.M) : ∀ j, j ≤ h.txs.length →
    MeetsTop p ((h.txs.take j).map (·.ops)) (h.tree j) (top j)
  | 0, _ => by
    obtain ⟨h1, h2⟩ := topStartOk_sound hm.startTop
    exact MeetsTop.start _ _ (hm.start.start hM) (hm.tree 0 (Nat.zero_le _)) h1 h2
  | j + 1, hj => by
    have ih := hm.meetsTop hM j (Nat.le_of_succ_le hj)
    obtain ⟨hc, _, _, hts, hroots, _⟩ := hm.step j hj
    have hlen : ((h.txs.take j).map (·.ops)).length = j := by simp; omega
    have hstep := MeetsTop.step _ _ _ _ _ _ _ ih (by rw [hlen]; exact hc)
      (by rw [hlen]; exact hm.tree (j + 1) hj) (by rw [hlen]; exact hts) hroots
    have htake : h.txs.take (j + 1) = h.txs.take j ++ [h.txs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [htake, List.map_append]
    exact hstep

/-- Recovery, for a history in the contract's words. After a crash that keeps
the first k + 1 records (k the last transaction: no crash, or any earlier
one), startup from them gives back every node of the model's structure after
transaction k with its whole history, and D; so the structure after startup
holds the tree after transaction k. -/
theorem full_recovery (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) (k : Nat) (hk : k ≤ h.txs.length) :
    let S := (SIS.run h.spec al h.ts).S.take (k + 1)
    let db := SIS.run h.spec al (h.ts.take k)
    (∀ x, (SIS.startup h.spec S).P.get? x = db.P.get? x) ∧
    (SIS.startup h.spec S).D = db.D ∧
    Rep (SIS.startup h.spec S).P (h.tree k) :=
  bridge_crash hm.meetsBridge al hst k hk

/-- Restart invariance, for a history in the contract's words: restarts after
any transactions change no record. -/
theorem full_restart (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) (ts : List (Nat × Bool))
    (hts : ts.map (·.1) = h.ts) :
    (SIS.runRestarts h.spec al ts).S = (SIS.run h.spec al h.ts).S :=
  bridge_restart hm.meetsBridge al hst ts hts

/-- Eviction, for a history in the contract's words: with any reads and
evictions after each transaction and restarts after any of them, the records
and D are those of the run without them, and a read through the handles at
any time t up to the last record reaches exactly the nodes reachable at t,
each with its node at t. -/
theorem full_eviction (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) (j : Nat)
    (hjl : j ≤ ts.length) (t : Nat) (ht : t ≤ j) :
    let db := SIS.run h.spec al ((ts.take j).map (·.1))
    let r := SIS.runHandles h.spec al (ts.take j)
    let m := r.2.1
    (r.1.S = db.S ∧ r.1.D = db.D) ∧
    (m.read h.spec r.2.2 db.S t).2.map (·.1) = SIS.reachList h.spec db.P t ∧
      ∀ q ∈ (m.read h.spec r.2.2 db.S t).2, SIS.view h.spec db.P t q.1 = some q.2 := by
  intro db r m
  have h1 := bridge_handles_records hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl
  have h2 := bridge_handles_read hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl t ht
  exact ⟨⟨h1.1, h1.2.1⟩, h2⟩

/-- Reclaim's cut with eviction, for a history in the contract's words: the
run with handles, any reads from the first available time on and evictions,
and restarts from safe cut streams (`CutOK`), appends the records of the run
without restarts, cut at the largest cut; its D is the run's, and so are its
lookups from the first available time on. -/
theorem full_cut (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
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
  bridge_cut_handles hm.meetsBridge hm.meetsEvict al hj hmk hpol cs hcs hcut hreads

end Contract
