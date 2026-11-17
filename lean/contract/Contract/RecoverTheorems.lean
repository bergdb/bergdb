/-
The contract package (bergdb 030-14): reads after a crash, after restarts,
after a lazy startup, under eviction with handles and after reclaim's safe
cuts, end to end, for a history that meets every clause in the contract's
words (`MeetsFull`, BridgeTop.lean).

Each theorem says, in the words of Recover.lean: the reader that reads the
model's view at time t (`ReadsRight`) is right, at every time t that is still
available. The view is the one that the abstract model's theorem gives back
in each case (BridgeFull.lean, BridgeTheorems.lean): the structure after a
startup from the records, the structure that the writer holds after restarts
and evictions, what a read through the handles or a lazy read returns, the
structure after a startup from a cut stream. The kinds of the key nodes come
from their levels in the view (`kindOf kind`), for a history that meets
K-LEVEL (`KindsOK kind`, Recover.lean): nothing of the reader is taken from
the history's tree.

The step from the bridge's theorems to these is proved once, for the model's
structure of the history (`MeetsBridge.view_reads`, Proof/RecoverModel.lean):
the past is fixed in the model; at the latest time the view's tree has the
history's tree's space root and, at every node that the tree reaches, the same
live klongs (the map keeps them, W1 to W5); so the view reads as the tree,
which reads as the plain map (Theorems.lean).

Proved: these theorems, from `MeetsFull` (or `MeetsBridge` with
`MeetsEvict`), K-LEVEL, and the premises of the bridge's theorems. Tested, not
proved, for a claim about Java: that Java's writer meets the clauses, that its
records are the model's (030-04, 3.5, items 1, 10, 12), that it makes the same
change after a restart or with eviction (item 9), that a cut is safe (item 11),
that its startup gives each key node its entries and its kind as written (item
5), and that its readers are the package's (item 6).
-/
import Contract.BridgeFull
import Contract.BridgePolicy
import Contract.Proof.RecoverModel

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top}

/-! ## Views that read alike -/

/-- Two views with the same nodes but the root, and the same live children of
the root, with kinds that agree but at the root, have one tree. -/
theorem viewTree_congr {V1 V2 : View BVal} {lf1 lf2 : NodeId → Bool}
    (hx : ∀ x, x ≠ SIS.root → V1 x = V2 x)
    (h0 : (V1 SIS.root).map (fun n => blive n.hist) = (V2 SIS.root).map (fun n => blive n.hist))
    (hlf : ∀ x, x ≠ SIS.root → lf1 x = lf2 x) :
    viewTree V1 lf1 = viewTree V2 lf2 := by
  have hr : viewRoot V1 = viewRoot V2 := by
    unfold viewRoot
    rw [h0]
    split
    · rename_i z _ _
      split
      · rfl
      · rename_i hz
        rw [hx z hz]
    · rfl
  unfold viewTree
  congr 1
  · funext x
    by_cases hx0 : x = SIS.root
    · simp [hx0]
    · simp only [hx0, ite_false]
      rw [hx x hx0, hlf x hx0]
  · rw [hr]

/-- A list of nodes with their contents, exactly the nodes reachable at t
each with its content at t, is the view at t. -/
theorem viewOfList_eq {sp : SIS.Spec BVal Nat} {P : Struct BVal} {t : Nat}
    {L : List (NodeId × Node BVal)} (h1 : L.map (·.1) = SIS.reachList sp P t)
    (h2 : ∀ q ∈ L, SIS.view sp P t q.1 = some q.2) : viewOfList L = SIS.view sp P t := by
  funext x
  unfold viewOfList
  cases hl : L.lookup x with
  | some n =>
    obtain ⟨l1, l2, hL, _⟩ := List.lookup_eq_some_iff.mp hl
    have hm : (x, n) ∈ L := by rw [hL]; simp
    exact (h2 _ hm).symm
  | none =>
    have hx : x ∉ SIS.reachList sp P t := by
      rw [← h1]
      intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have := List.lookup_eq_none_iff.mp hl q hq
      simp at this
    simp [SIS.view, SIS.reachable, hx]

/-! ## The reader of the model's view -/

variable {kind : Nat → Bool}

/-- For a history that meets the bridge's clauses and K-LEVEL: the reader of
the view of the model's structure after transaction k, at every time t up to
k, with the kinds that the view's levels give, gives what the plain map after
the first t transactions gives (`MeetsBridge.view_reads`). -/
theorem view_reads (hm : MeetsBridge p h) (hM : 1 ≤ p.M) (hkd : KindsOK kind h) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) :
    ReadsRight (SIS.view h.spec (h.P k) t) (kindOf kind (SIS.view h.spec (h.P k) t))
      (h.txs.map (·.ops)) t :=
  hm.view_reads hM hkd hk htk

/-- The same, for a structure with the same nodes as the model's run after
the first k transactions. -/
theorem same_reads (hm : MeetsBridge p h) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) {k t : Nat} (hk : k ≤ h.txs.length) (htk : t ≤ k) {P : Struct BVal}
    (hP : ∀ x, P.get? x = (SIS.run h.spec al (h.ts.take k)).P.get? x) :
    ReadsRight (SIS.view h.spec P t) (kindOf kind (SIS.view h.spec P t)) (h.txs.map (·.ops)) t := by
  rw [run_P h al k hk] at hP
  rw [SIS.SameNodes.view hP t]
  exact view_reads hm hM hkd hk htk

/-! ## After a crash, after restarts -/

/-- **Reads after a crash.** A crash after transaction k (k the last one: no
crash, or any earlier one) keeps the first k + 1 records. After a startup from
them, every get and every scan at every time t up to k, with each key node's
kind from its level, gives what the plain map after the first t transactions
gives. -/
theorem crash_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) :
    let V := SIS.view h.spec (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P t
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t :=
  same_reads hm.meetsBridge hM hkd al hk htk (full_recovery hm al hst k hk).1

/-- **Reads after restarts and a crash.** In a run with a crash and a startup
after any of the transactions (restarts), a crash after transaction k keeps
the first k + 1 records that it wrote; after a startup from them, every get
and every scan at every time t up to k gives what the plain map gives. -/
theorem restart_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec)
    (ts : List (Nat × Bool)) (hts : ts.map (·.1) = h.ts) {k t : Nat} (hk : k ≤ h.txs.length)
    (htk : t ≤ k) :
    let V := SIS.view h.spec
      (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P t
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t := by
  intro V
  have hV : V = SIS.view h.spec
      (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P t := by
    show SIS.view h.spec (SIS.startup h.spec ((SIS.runRestarts h.spec al ts).S.take (k + 1))).P t = _
    rw [full_restart hm al hst ts hts]
  rw [hV]
  exact crash_reads hm hM hkd al hst hk htk

/-! ## Under eviction with handles -/

theorem take_map_ts {α : Type} (ts : List (Nat × α)) (hts : ts.map (·.1) = h.ts) (j : Nat) :
    (ts.take j).map (·.1) = h.ts.take j := by
  rw [List.map_take, hts]

/-- **Reads under eviction, through the handles.** In a run with handles, with
any reads and evictions after each transaction and restarts after any of
them: after the first j transactions, a read through the handles at any time
t up to j returns a view on which every get and every scan gives what the
plain map after the first t transactions gives. -/
theorem evict_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j t : Nat}
    (hjl : j ≤ ts.length) (htj : t ≤ j) :
    let db := SIS.run h.spec al ((ts.take j).map (·.1))
    let r := SIS.runHandles h.spec al (ts.take j)
    let V := viewOfList (r.2.1.read h.spec r.2.2 db.S t).2
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t := by
  intro db r V
  have hjn : j ≤ h.txs.length := by
    have := congrArg List.length hts
    simp only [List.length_map, BHist.ts_length] at this
    omega
  obtain ⟨_, h1, h2⟩ := full_eviction hm al hj hmk ts hts j hjl t htj
  have hV : V = SIS.view h.spec db.P t := viewOfList_eq h1 h2
  have hP : db.P = h.P j := by
    show (SIS.run h.spec al ((ts.take j).map (·.1))).P = _
    rw [take_map_ts ts hts j, run_P h al j hjn]
  rw [hV, hP]
  exact view_reads hm.meetsBridge hM hkd hjn htj

/-- **Reads after restarts and evictions, of the writer's structure.** In such
a run, after the first j transactions, the structure that the writer holds
reads right at every time t up to j. -/
theorem handles_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j t : Nat}
    (hjl : j ≤ ts.length) (htj : t ≤ j) :
    let V := SIS.view h.spec (SIS.runHandles h.spec al (ts.take j)).1.P t
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t := by
  have hjn : j ≤ h.txs.length := by
    have := congrArg List.length hts
    simp only [List.length_map, BHist.ts_length] at this
    omega
  have h1 := (bridge_handles_records hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl).2.2
  rw [take_map_ts ts hts j] at h1
  exact same_reads hm.meetsBridge hM hkd al hjn htj h1

/-- **Reads after a lazy startup.** After Java's lazy startup from the records
of the first k transactions (the whole stream, or what a crash leaves), with
any reads and writer follows that the model admits, a read at any time t up
to k through the first-touch rule returns a view on which every get and every
scan gives what the plain map after the first t transactions gives. -/
theorem lazy_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) {k : Nat}
    (hk : k ≤ h.ts.length) (ops : List SIS.Op)
    (hops : SIS.OpsOK h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))
      (SIS.run h.spec al (h.ts.take k)).P k
      (SIS.lazyStartup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))) ops) {t : Nat}
    (htk : t ≤ k) :
    let S : SIS.Stream BVal Nat := (SIS.run h.spec al h.ts).S.take (k + 1)
    let m := ops.foldl (SIS.Mem.step h.spec S) (SIS.lazyStartup h.spec S)
    let V := viewOfList (m.read h.spec S t).2
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t := by
  intro S m V
  have hkn : k ≤ h.txs.length := by rw [← h.ts_length]; exact hk
  obtain ⟨h1, h2⟩ := bridge_lazy_read hm.meetsBridge hm.meetsEvict al hj k hk ops hops t htk
  have hV : V = SIS.view h.spec (SIS.run h.spec al (h.ts.take k)).P t := viewOfList_eq h1 h2
  rw [hV, run_P h al k hkn]
  exact view_reads hm.meetsBridge hM hkd hkn htk

/-! ## After reclaim's safe cuts -/

/-- **Reads after safe cuts.** The run with handles, any reads from the first
available time on and evictions, and restarts from safe cut streams
(`CutOK`): after it, every get and every scan at every time t from the first
available time to the last transaction gives what the plain map after the
first t transactions gives. -/
theorem cut_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2.1)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t := by
  intro V
  obtain ⟨_, _, hsame⟩ := full_cut hm al hj hmk hpol cs hcs hcut hreads
  have hlen : cs.length = h.txs.length := by
    have := congrArg List.length hcs
    simp only [List.length_map, BHist.ts_length] at this
    exact this
  rw [hcs] at hsame
  obtain ⟨hx, h0⟩ := hsame t hft (by rw [hlen]; exact htn)
  let V2 := SIS.view h.spec (SIS.run h.spec al h.ts).P t
  have hv : viewTree V (kindOf kind V) = viewTree V2 (kindOf kind V2) := by
    apply viewTree_congr (fun x hx0 => hx x (fun _ => hx0)) (h0 rfl)
    intro x hx0
    simp only [kindOf]
    show (match V x with | some n => kind n.level | none => false) =
      (match V2 x with | some n => kind n.level | none => false)
    rw [show V x = V2 x from hx x (fun _ => hx0)]
  have hP : (SIS.run h.spec al h.ts).P = h.P h.txs.length := by
    have := run_P h al h.txs.length (le_refl _)
    have ht : h.ts.take h.txs.length = h.ts := by rw [← h.ts_length]; exact List.take_length
    rwa [ht] at this
  have hr := view_reads hm.meetsBridge hM hkd (le_refl h.txs.length) htn
  rw [← hP] at hr
  obtain ⟨hg, hs⟩ := hr
  refine ⟨fun key => ?_, fun req hreq limit => ?_⟩
  · unfold vget; rw [hv]; exact hg key
  · unfold vscan; rw [hv]; exact hs req hreq limit

/-- Reads after safe cuts, for policies that do not read the stream (as the
trace checker's, which takes Java's choices from the trace): `cut_reads`
without the premise `PolicyCutOK`. -/
theorem cut_reads_blind (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hp : ∀ S S' D i tr, al.policy S D i tr = al.policy S' D i tr)
    (hf : ∀ S S' D i tr, al.faPolicy S D i tr = al.faPolicy S' D i tr)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2.1)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    ReadsRight V (kindOf kind V) (h.txs.map (·.ops)) t :=
  cut_reads hm hM hkd al hj hmk (policyCutOK_of_blind al hp hf) cs hcs hcut hreads hft htn

end Contract
