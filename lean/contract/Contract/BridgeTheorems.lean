/-
The contract package (bergdb 030-07): the theorems of the bridge.

For any history that meets the writer's contract and the bridge's clauses
(`MeetsBridge`, Bridge.lean), the abstract model's assumptions hold for the
model's instance of the history (`bridge_runOK`), and its structure is the
history's tree, klong for entry (`bridge_rep`). So the abstract model's
theorems (lean/SIS/Theorems.lean, proved there, not here) speak of BergDB's
key tree:

* recovery (T1): after any run, and after a crash that keeps a prefix of
  whole records, startup from the stream gives back every node of the tree
  with all its entries, and D (`bridge_recovery`, `bridge_crash`);
* restart invariance (T2): a run with restarts after any transactions writes
  exactly the records of the run without restarts (`bridge_restart`).

The model's algorithm `al` is any: its startup pos policy (the take) is free.
Its still-dirty test is BergDB's (`javaTest`).

What is proved: these theorems, with no premise but `MeetsBridge`. What is
not: that Java's writer meets `MeetsBridge` (tested per transaction on the
traces, BridgeCheck.lean; the clauses in the model's words by `tracecheck`),
and that Java's records are the model's (tested by `tracecheck`).
-/
import SIS.Theorems
import Contract.Theorems
import Contract.Proof.BridgeStep

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

variable {p : Params} {h : BHist}

/-! ## The history meets the contract -/

/-- The start of a bridged history is a start of the contract (the node size
is at least 1). -/
theorem StartB.start (hs : StartB h) (hM : 1 ≤ p.M) : Start p h.s0 := by
  obtain ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, hnone, hroots⟩ := hs
  have hroot : (h.s0.at 0).root = some r := by simp [Tree.root, Tree.at, hroots]
  have hobj0 : (h.s0.at 0).obj r = some (.key { level := lr, leaf := true, ks := [.time 0] }) := by
    simp [Tree.at, hobj, Obj.at, prefixAt]
  constructor
  · unfold invOk
    rw [hroot]
    simp only [hobj0]
    simp only [Bool.true_or, Bool.true_and]
    unfold walk
    simp only [hobj0]
    have hlive : live [Klong.time 0] = [] := by decide
    simp [nodeOk, hlive, kidsOk, hM]
    decide
  · unfold contents
    rw [hroot]
    simp only [Tree.fuel, hobj0]
    unfold listAt
    simp only [hobj0]
    have hlive : live [Klong.time 0] = [] := by decide
    simp [hlive]

/-- A history that meets the bridge's clauses meets the contract (`Meets`), so
the theorems on reads (Theorems.lean) hold for it: after the first j
transactions, for every j. -/
theorem MeetsBridge.meets (hm : MeetsBridge p h) (hM : 1 ≤ p.M) : ∀ j, j ≤ h.txs.length →
    Meets p ((h.txs.take j).map (·.ops)) (h.tree j)
  | 0, _ => Meets.start _ (hm.start.start hM)
  | j + 1, hj => by
    have ih := hm.meets hM j (Nat.le_of_succ_le hj)
    have hc := (hm.step j hj).1
    have hlen : ((h.txs.take j).map (·.ops)).length = j := by simp; omega
    have hstep := Meets.step _ _ _ _ _ ih (by rw [hlen]; exact hc)
    have htake : h.txs.take (j + 1) = h.txs.take j ++ [h.txs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [htake, List.map_append]
    exact hstep

/-! ## The model's assumptions -/

/-- The abstract model's assumptions on a run (`RunOK`: on the structure, and
A2 to A5, the data node rules, fresh ids, the root's rules and the touch
rules for every transaction) hold for the model's instance of a history that
meets the contract and the bridge's clauses, whatever the algorithm's
choices. -/
theorem bridge_runOK (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat) :
    SIS.RunOK h.spec al h.ts :=
  hm.runOK al

/-- The model's structure after the first j transactions of the model's run
holds the history's tree after them: every key node as an index node with its
level and the entries of its klongs, every value as a data node with its one
entry. -/
theorem bridge_rep (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat) (j : Nat)
    (hj : j ≤ h.txs.length) : Rep (SIS.run h.spec al (h.ts.take j)).P (h.tree j) := by
  rw [run_P h al j hj]
  exact (hm.binv j hj).rep.rep

theorem BHist.ts_length (h : BHist) : h.ts.length = h.txs.length := by simp [BHist.ts]

theorem Rep.congr {P P' : Struct BVal} {s : Tree} (hr : Rep P s) (hsame : ∀ x, P'.get? x = P.get? x) :
    Rep P' s := by
  intro x o hx
  have := hr x o hx
  cases o with
  | key n => simp only at this ⊢; rw [hsame]; exact this
  | val v =>
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [hsame]; exact ht⟩

/-! ## Recovery and restarts, for BergDB's key tree -/

/-- T1, recovery, for BergDB's key tree. After any history that meets the
contract and the bridge's clauses, startup from the stream that the model's
run wrote gives back every node of the model's structure with its whole
history, and the same D. So the structure after startup holds the tree: every
key node with the entries of all its klongs, every value. -/
theorem bridge_recovery (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) :
    let db := SIS.run h.spec al h.ts
    (∀ x, (SIS.startup h.spec db.S).P.get? x = db.P.get? x) ∧
    (SIS.startup h.spec db.S).D = db.D ∧
    Rep (SIS.startup h.spec db.S).P (h.tree h.txs.length) := by
  intro db
  have hok := hm.runOK al
  have h1 : ∀ x, (SIS.startup h.spec db.S).P.get? x = db.P.get? x :=
    fun x => SIS.T1_nodes h.spec al h.ts hok (Or.inl hst) x
  refine ⟨h1, (SIS.T1_recovery h.spec al h.ts hok (Or.inl hst)).2, ?_⟩
  have hrep := bridge_rep hm al h.txs.length (Nat.le_refl _)
  have htake : h.ts.take h.txs.length = h.ts := by
    rw [← h.ts_length]; exact List.take_length
  rw [htake] at hrep
  exact hrep.congr h1

/-- T1 after a crash, for BergDB's key tree. A crash after transaction k keeps
the first k + 1 records of the stream. Startup from them gives back every
node of the model's structure after transaction k with its whole history, and
the D of then. So the structure after startup holds the tree after
transaction k. -/
theorem bridge_crash (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) (k : Nat) (hk : k ≤ h.txs.length) :
    let S := (SIS.run h.spec al h.ts).S.take (k + 1)
    let db := SIS.run h.spec al (h.ts.take k)
    (∀ x, (SIS.startup h.spec S).P.get? x = db.P.get? x) ∧
    (SIS.startup h.spec S).D = db.D ∧
    Rep (SIS.startup h.spec S).P (h.tree k) := by
  intro S db
  have hok := hm.runOK al
  have hal := SIS.algOK_of h.spec al (Or.inl hst)
  have hk' : k ≤ h.ts.length := by rw [h.ts_length]; exact hk
  have hpre := SIS.st_S_prefix h.spec al h.ts (j := k) (j' := h.ts.length) hk' (Nat.le_refl _)
  have hlen := SIS.st_len h.spec al h.ts hok hal hk'
  rw [SIS.st_length] at hpre
  have htake : S = (SIS.st h.spec al h.ts k).S := by
    show (SIS.run h.spec al h.ts).S.take (k + 1) = _
    rw [← hlen]; exact (List.prefix_iff_eq_take.mp hpre).symm
  have h2 := SIS.T1_strong h.spec al h.ts hok hal hk'
  rw [← htake] at h2
  have h1 : ∀ x, (SIS.startup h.spec S).P.get? x = db.P.get? x := h2.1
  exact ⟨h1, h2.2, (bridge_rep hm al k hk).congr h1⟩

/-- T2, restart invariance, for BergDB's key tree. A run of the history's
transactions with a crash and a startup after any of them (the ones marked
true) appends exactly the records of the run without restarts. -/
theorem bridge_restart (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) (ts : List (Nat × Bool))
    (hts : ts.map (·.1) = h.ts) :
    (SIS.runRestarts h.spec al ts).S = (SIS.run h.spec al h.ts).S := by
  have hok := hm.runOK al
  rw [← hts] at hok ⊢
  exact SIS.T2_restart h.spec al ts hok (Or.inl hst)

end Contract
