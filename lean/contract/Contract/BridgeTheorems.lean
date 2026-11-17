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

With TREE (bergdb 030-08), A6' and A-COPY besides (`MeetsEvict`), the model's
assumptions for lazy reading and eviction hold too (`bridge_treeRunOK`,
`bridge_evictRunOK`), and so:

* lazy reading: after a startup that reads nodes from the stream at first
  touch, a read at any time gives the structure, and the records are those
  of the run without restarts (`bridge_lazy_read`, `bridge_lazy_restart`);
* eviction with handles: under any reads and evictions between transactions,
  and restarts, the writer appends the model's records and leaves the model's
  D; a read through the handles at any time gives the structure; every
  object that is not pinned may be evicted (`bridge_handles_records`,
  `bridge_handles_read`, `bridge_handles_evict`); and Java's startup by
  position gives the memory of the startup by node id
  (`bridge_handles_pos`);
* reclaim's cut: after a safe cut (`CutOK`, a premise: that BergDB's waits
  give a safe cut is tested, 006-26, section 3.3), startup from the cut
  stream gives every lookup from the first available time on, and the
  records stay those of the run without cuts, also with eviction
  (`bridge_cut_recover`, `bridge_cut_restart`, `bridge_cut_handles`).

D as state (bergdb 030-06, finding 5): the frame, clause 3 of the contract,
holds with the model's D in place of the contract's free D (`frame_modelD`,
Proof/BridgeDirty.lean): every key node that a transaction changes or makes
is in the model's D when the transaction ends.

The model's algorithm `al` is any: its startup pos policy (the take) is free.
Its still-dirty test is BergDB's (`javaTest`).

A history that meets every clause in the contract's words (`MeetsFull`,
BridgeTop.lean) meets `MeetsBridge` and `MeetsEvict`
(Proof/BridgeWords.lean); BridgeFull.lean states the main theorems for it.

What is proved: these theorems, with no premise but `MeetsBridge`. What is
not: that Java's writer meets `MeetsBridge` (tested per transaction on the
traces, BridgeCheck.lean; the clauses in the model's words by `tracecheck`),
and that Java's records are the model's (tested by `tracecheck`).

The change is given (bergdb 030-11, finding 1): the instance takes each
transaction's change from the history (`bspec`'s `exec` reads nothing, so
`bridge_execRootOK` is `rfl`). The restart, lazy and handle theorems prove
that startup and eviction keep the structure and D such that the same
changes write the same records; that Java's writer makes the same change
after a restart or with eviction is 030-04, 3.5, item 9, tested.
-/
import SIS.Theorems
import SIS.PhysTheorems
import SIS.HandleTheorems
import SIS.ReclaimTheorems
import SIS.HandleReclaimTheorems
import SIS.Proof.HandleRestart
import SIS.Proof.HandlePin
import SIS.Proof.HandleLinkPos
import SIS.Proof.HandleCutT12
import Contract.Theorems
import Contract.TheoremsShape
import Contract.Proof.BridgeTree
import Contract.Proof.BridgeDirty

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

/-! ## Lazy reading, eviction and the cut, for BergDB's key tree -/

/-- The contract's TREE after every transaction and at the start (bergdb
030-08's clause, here for the history's trees) makes the history one that
meets the contract with TREE (`MeetsShape`). -/
theorem MeetsBridge.meetsShape (hm : MeetsBridge p h) (he : MeetsEvict h) (hM : 1 ≤ p.M) :
    ∀ j, j ≤ h.txs.length → MeetsShape p ((h.txs.take j).map (·.ops)) (h.tree j)
  | 0, _ => MeetsShape.start _ (hm.start.start hM) (he.tree 0 (Nat.zero_le _))
  | j + 1, hj => by
    have ih := hm.meetsShape he hM j (Nat.le_of_succ_le hj)
    have hc := (hm.step j hj).1
    have hlen : ((h.txs.take j).map (·.ops)).length = j := by simp; omega
    have hstep := MeetsShape.step _ _ _ _ _ ih (by rw [hlen]; exact hc)
      (by rw [hlen]; exact he.tree (j + 1) hj)
    have htake : h.txs.take (j + 1) = h.txs.take j ++ [h.txs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [htake, List.map_append]
    exact hstep

/-- The model's TREE after every transaction (`TreeRunOK`): every node
reachable but the root is the live child of exactly one reachable node. From
the contract's TREE (bergdb 030-08). -/
theorem bridge_treeRunOK (hm : MeetsBridge p h) (he : MeetsEvict h) (al : SIS.Algo BVal Nat) :
    SIS.TreeRunOK h.spec al h.ts := by
  intro j hj
  have hj' : j + 1 ≤ h.txs.length := by rw [h.ts_length] at hj; omega
  rw [run_P h al (j + 1) hj']
  have hi := hm.binv (j + 1) hj'
  have ht := he.tree (j + 1) hj'
  rw [hi.timely.at_eq] at ht
  exact hi.treeAt ht

/-- The model's assumptions for eviction (`EvictRunOK`): TREE and A6' after
every transaction and at the start, A-COPY for every change. -/
theorem bridge_evictRunOK (hm : MeetsBridge p h) (he : MeetsEvict h) (al : SIS.Algo BVal Nat) :
    SIS.EvictRunOK h.spec al h.ts := by
  refine ⟨?_, ?_⟩
  · intro j hj
    have hj' : j ≤ h.txs.length := by rw [h.ts_length] at hj; exact hj
    rw [run_P h al j hj']
    have hi := hm.binv j hj'
    have ht := he.tree j hj'
    rw [hi.timely.at_eq] at ht
    exact ⟨hi.treeAt ht, he.adopt j hj'⟩
  · intro j hjl
    have hj : j < h.txs.length := by simpa [BHist.ts] using hjl
    simp only
    rw [run_P h al j (Nat.le_of_lt hj), h.ts_get hj, h.exec_eq hj]
    exact he.copy j hj

/-- An entry added to a node makes no other pointee of the node a live child
(`LiveAppend`): a fact of the trace checker's `blive` (lean/Check/Live.lean). -/
theorem bridge_liveAppend (h : BHist) : SIS.LiveAppend h.spec :=
  SIS.Check.bspec_liveAppend h.chs h.p0 true

/-- A transaction's change does not depend on what it reads (it is given), so
it sees the root only through its live children (`ExecRootOK`). -/
theorem bridge_execRootOK (h : BHist) : SIS.ExecRootOK h.spec :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- The root's live children are those of its last entry (`VirtLiveOK`): a
fact of `blive`. -/
theorem bridge_virtLiveOK (h : BHist) : SIS.VirtLiveOK h.spec := by
  intro _ hst hall
  show blive hst = (hst.getLast?.map (fun e => bptrs e.val)).getD []
  rw [SIS.Check.blive_eq, blive_tops hst hall]
  cases hl : hst.getLast? with
  | none => rfl
  | some e =>
    obtain ⟨z, hz⟩ := hall e (List.mem_of_getLast? hl)
    simp [SIS.Check.bout, hz, bptrs]
    rfl

/-- Lazy reading (T1-L), for BergDB's key tree. After Java's lazy startup from
the stream after transaction k (the whole stream, or the prefix that a crash
leaves), and any reads and writer follows that the model admits, a read at
any time t up to k through the first-touch rule reaches exactly the nodes
reachable at t, each with its node at t. -/
theorem bridge_lazy_read (hm : MeetsBridge p h) (he : MeetsEvict h) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (k : Nat) (hk : k ≤ h.ts.length)
    (ops : List SIS.Op)
    (hops : SIS.OpsOK h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))
      (SIS.run h.spec al (h.ts.take k)).P k
      (SIS.lazyStartup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))) ops) :
    let S : SIS.Stream BVal Nat := (SIS.run h.spec al h.ts).S.take (k + 1)
    let P := (SIS.run h.spec al (h.ts.take k)).P
    let m := ops.foldl (SIS.Mem.step h.spec S) (SIS.lazyStartup h.spec S)
    ∀ t ≤ k, (m.read h.spec S t).2.map (·.1) = SIS.reachList h.spec P t ∧
      ∀ q ∈ (m.read h.spec S t).2, SIS.view h.spec P t q.1 = some q.2 :=
  (SIS.T1_lazy h.spec al h.ts (hm.runOK al) (bridge_liveAppend h) (bridge_treeRunOK hm he al) hj k hk
    ops hops).1

/-- Restarts with a lazy startup (T2-L), for BergDB's key tree: the run with
restarts after any transactions, each a lazy startup, whose writer reads
through the physical layer, appends exactly the records of the run without
restarts. -/
theorem bridge_lazy_restart (hm : MeetsBridge p h) (he : MeetsEvict h) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (ts : List (Nat × Bool))
    (hts : ts.map (·.1) = h.ts) :
    (SIS.runLazy h.spec al ts).1.S = (SIS.run h.spec al h.ts).S := by
  have hok := hm.runOK al
  have htree := bridge_treeRunOK hm he al
  rw [← hts] at hok htree ⊢
  exact SIS.T2_lazy h.spec al ts hok (bridge_liveAppend h) htree hj

/-- Eviction with handles (T2-C), for BergDB's key tree. With any reads and
evictions after each transaction and restarts after any of them, after every
transaction and its operations or its restart the state is that of the run
without restarts or eviction: the same records, the same D, and a structure
with the same nodes. -/
theorem bridge_handles_records (hm : MeetsBridge p h) (he : MeetsEvict h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) (j : Nat)
    (hjl : j ≤ ts.length) :
    let db := SIS.run h.spec al ((ts.take j).map (·.1))
    let r := SIS.runHandles h.spec al (ts.take j)
    r.1.S = db.S ∧ r.1.D = db.D ∧ ∀ x, r.1.P.get? x = db.P.get? x := by
  have hok := hm.runOK al
  have hev := bridge_evictRunOK hm he al
  rw [← hts] at hok hev
  have := SIS.t2_handles h.spec al ts hok (bridge_liveAppend h) hev hj hmk j hjl
  exact ⟨this.1, this.2.1, this.2.2.1⟩

/-- Reads under eviction (T-READ with handles and restarts), for BergDB's key
tree. In such a run, after any transaction and its operations or its restart,
a read through the handles at any time t up to the last record reaches
exactly the nodes reachable at t, each with its node at t. Eviction changes
no answer. -/
theorem bridge_handles_read (hm : MeetsBridge p h) (he : MeetsEvict h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) (j : Nat)
    (hjl : j ≤ ts.length) (t : Nat) (ht : t ≤ j) :
    let db := SIS.run h.spec al ((ts.take j).map (·.1))
    let r := SIS.runHandles h.spec al (ts.take j)
    let m := r.2.1
    (m.read h.spec r.2.2 db.S t).2.map (·.1) = SIS.reachList h.spec db.P t ∧
      ∀ q ∈ (m.read h.spec r.2.2 db.S t).2, SIS.view h.spec db.P t q.1 = some q.2 := by
  have hok := hm.runOK al
  have hev := bridge_evictRunOK hm he al
  rw [← hts] at hok hev
  exact SIS.tr_handles_restarts h.spec al ts hok (bridge_liveAppend h) hev hj hmk j hjl t ht

/-- What may be evicted (T-PIN), for BergDB's key tree. In such a run, every
live handle whose object is not pinned (the objects of the nodes of D, and
the root's) may be evicted, and one eviction removes the object from memory
and kills the handle. -/
theorem bridge_handles_evict (hm : MeetsBridge p h) (he : MeetsEvict h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) (j : Nat)
    (hjl : j ≤ ts.length) :
    let r := SIS.runHandles h.spec al (ts.take j)
    let m := r.2.1
    ∀ n hd a, m.handle? n = some hd → hd.dead = false → hd.obj = some a →
      m.pinned r.1.D a = false →
      m.evictable r.1.D n = true ∧
      (m.cacheOp h.spec r.2.2 r.1.S r.1.D (.evict n)).obj? a = none ∧
      ((m.cacheOp h.spec r.2.2 r.1.S r.1.D (.evict n)).handle? n).map (·.dead) = some true := by
  have hok := hm.runOK al
  have hev := bridge_evictRunOK hm he al
  rw [← hts] at hok hev
  exact SIS.tp_handles h.spec al ts hok (bridge_liveAppend h) hev hj hmk j hjl

/-- Startup by position, for BergDB's key tree: Java's startup with handles
and rule 4 by position, from the stream after any transaction k, gives the
memory of the startup with rule 4 by node id. -/
theorem bridge_handles_pos (hm : MeetsBridge p h) (he : MeetsEvict h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (k : Nat) (hk : k ≤ h.ts.length) :
    SIS.handleStartupPos h.spec (SIS.run h.spec al (h.ts.take k)).S =
      SIS.handleStartup h.spec (SIS.run h.spec al (h.ts.take k)).S :=
  SIS.rule4Pos_handles h.spec al h.ts (hm.runOK al) (bridge_liveAppend h)
    (bridge_evictRunOK hm he al) hj hmk k hk

/-- T8, reclaim's cut, for BergDB's key tree. After a safe cut (`CutOK`) at c
in the state after transaction k, startup from the cut stream gives the same
lookups at every time from the first available time to k, and the same D. -/
theorem bridge_cut_recover (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hst : al.stillDirty = SIS.javaTest h.spec) (k c : Nat) (hk : k ≤ h.ts.length)
    (hcut : SIS.CutOK h.spec c (SIS.run h.spec al (h.ts.take k)) k) :
    let db := SIS.run h.spec al (h.ts.take k)
    SIS.SameFrom h.spec (SIS.lastFa db.S) k (SIS.startup h.spec (SIS.cutStream c db.S)).P db.P ∧
      (SIS.startup h.spec (SIS.cutStream c db.S)).D = db.D :=
  SIS.T8_recoverCut h.spec al h.ts (hm.runOK al) (Or.inl hst) (bridge_execRootOK h)
    (bridge_virtLiveOK h) k c hk hcut

/-- T12, restarts from cut streams, for BergDB's key tree. A run that
restarts from safe cut streams appends the records of the run without
restarts: its stream is that run's, cut at the largest cut; its D is the
run's, and so are its lookups from the first available time on. -/
theorem bridge_cut_restart (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat)) (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1)) :
    let db := SIS.runRestartsCut h.spec al cs
    let r := SIS.run h.spec al (cs.map (·.1))
    db.S = SIS.cutStream (SIS.cutMax (cs.map (·.2))) r.S ∧ db.D = r.D ∧
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P := by
  have hok := hm.runOK al
  rw [← hcs] at hok
  exact SIS.T12_restartCut h.spec al cs hok hj hmk (bridge_execRootOK h) (bridge_virtLiveOK h)
    hpol hcut

/-- T12 with eviction, for BergDB's key tree. The run with handles, any reads
(from the first available time on) and evictions between transactions, and
restarts from safe cut streams, appends the records of the run without
restarts, cut at the largest cut; its D is the run's, and so are its lookups
from the first available time on. -/
theorem bridge_cut_handles (hm : MeetsBridge p h) (he : MeetsEvict h) (al : SIS.Algo BVal Nat)
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
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P := by
  have hok := hm.runOK al
  have hev := bridge_evictRunOK hm he al
  rw [← hcs] at hok hev
  exact SIS.t12_handles h.spec al cs hok (bridge_liveAppend h) hev hj hmk (bridge_execRootOK h)
    (bridge_virtLiveOK h) hpol hcut hreads

end Contract
