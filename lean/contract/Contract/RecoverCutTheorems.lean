/-
The contract package (bergdb 030-17): Java's readers, with Java's search
through the skip pointers, under eviction through the handles, after a lazy
startup and after reclaim's safe cuts, end to end, for a history that meets
every clause in the contract's words (`MeetsFull`) and K-LEVEL (`KindsOK`).
030-14 proved them after a crash and restarts (`crash_java_reads`,
`restart_java_reads`, RecoverJavaTheorems.lean).

What Java's search reads (`java_search_from`). At a lookup time t, Java's
search reads the super root, the top nodes made at or after t (along the skip
pointers whose cached time is at or after t) and the top node of time t (the
target of a lowest skip pointer): nothing else. So on any top that holds the
history's top from a time f at or before t (`TopFrom`, RecoverCut.lean: the
super root, every top node made at or after f and the top node of time f, as
written), it finds the space root of time t, as on the whole top. The other
top nodes may be evicted or gone.

* Under eviction (`evict_java_reads`, `handles_java_reads`): Java's top
  needs to hold, as written, only what its search at t reads (`TopFrom t`);
  a top node it evicted and loads again through its handle is the top node
  as written (030-04, 3.5, items 5 and 13). The writer's structure under
  eviction holds the history's top (`handles_top`).
* After a lazy startup (`lazy_java_reads`): the same, with the view that a
  read through the first-touch rule returns.
* After reclaim's safe cuts (`cut_java_reads`): the records before the cut
  are gone, and with them the top nodes made before the first available time
  f, but the top node of time f. Java's search at any time t from f on reads
  none of the gone ones, and finds the space root of time t. The stream
  after the cut keeps every top node that the search reads, with its root
  pointer and skip pointers as written: at every time t from f on, the cut
  structure's root has the top node of time t as its live child, with its
  entries (`cut_keeps_top`). Before f the search may need a gone top node;
  reads before the first available time are not allowed (`hreads`, the API).

Each theorem: if Java's tree holds the view that the model's theorem gives
back at t (`HoldsView`, RecoverJava.lean) and Java's top holds the history's
top from f (`TopFrom f`), then Java's get and scan at t, at a record's time
or between two records, give what the plain map after the first t
transactions gives (`JReadsRight`). The premises are met by the tree as
written and the history's top (`evict_java_tree`, `cut_holds`,
`TopGood.topFrom`), so the theorems are not vacuous.

Proved: these theorems. Assumed, for a claim about Java (030-04, 3.5, item
13): that Java's tree and top after a startup, a lazy startup, a startup from
a cut stream, or with objects evicted and loaded again, hold these (the
bytes decode to what was written: item 5). Tested by runs B and E and the
reclaim sets (030-17, section 4).
-/
import Contract.RecoverJavaTheorems
import Contract.Proof.RecoverCut

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}

/-! ## What Java's search reads -/

/-- **Java's search from a top that holds the history's top from f.** At any
time t from f up to k, at a record's time or between two records, Java's
search through the skip pointers of any top that holds the history's top
after transaction k from f (the super root, the top nodes made at or after f
and the top node of time f, as written; any other top node missing or
anything) finds the space root of the tree after t. -/
theorem java_search_from (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {k t f : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (hft : f ≤ t) {tp : Top} (htp : TopFrom f (top k) tp)
    (mid : Bool) : findRoot tp t mid = (h.tree t).root :=
  hm.findRoot_from hM hk htk hft htp mid

/-! ## Under eviction, after a lazy startup -/

theorem len_of_ts {α : Type} {ts : List (Nat × α)} (hts : ts.map (·.1) = h.ts) {j : Nat}
    (hjl : j ≤ ts.length) : j ≤ h.txs.length := by
  have := congrArg List.length hts
  simp only [List.length_map, BHist.ts_length] at this
  omega

/-- The writer's structure in a run with handles, after the first j
transactions with any reads, evictions and restarts, holds the history's top
after j. -/
theorem handles_top (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j : Nat}
    (hjl : j ≤ ts.length) : topOfP (SIS.runHandles h.spec al (ts.take j)).1.P = top j := by
  have hjn := len_of_ts hts hjl
  have h1 := (bridge_handles_records hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl).2.2
  rw [take_map_ts ts hts j, run_P h al j hjn] at h1
  rw [topOfP_congr h1]
  exact hm.topOfP_eq hM hjn

/-- **Java's reads under eviction, through the handles.** In a run with
handles, with any reads and evictions after each transaction and restarts
after any of them: after the first j transactions, a tree that holds the view
that a read through the handles at a time t up to j returns, with the kinds
of the levels, read with any top that holds the history's top after j from t
(the top nodes that Java's search at t reads, as written; any other may be
evicted): Java's get and scan at t are right. -/
theorem evict_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j t : Nat}
    (hjl : j ≤ ts.length) (htj : t ≤ j) (mid : Bool) (s : Tree) (tp : Top) :
    let db := SIS.run h.spec al ((ts.take j).map (·.1))
    let r := SIS.runHandles h.spec al (ts.take j)
    let V := viewOfList (r.2.1.read h.spec r.2.2 db.S t).2
    HoldsView V (kindOf kind V) t s → TopFrom t (top j) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  intro db r V hs htp
  have hjn := len_of_ts hts hjl
  obtain ⟨_, h1, h2⟩ := full_eviction hm al hj hmk ts hts j hjl t htj
  have hV : V = SIS.view h.spec db.P t := viewOfList_eq h1 h2
  have hP : db.P = h.P j := by
    show (SIS.run h.spec al ((ts.take j).map (·.1))).P = _
    rw [take_map_ts ts hts j, run_P h al j hjn]
  rw [hV, hP] at hs
  exact hm.java_reads_from hM hkd hjn htj (le_refl t) mid hs htp

/-- **Java's reads of the writer's structure after restarts and evictions.**
In such a run, after the first j transactions, a tree that holds the view of
the structure that the writer holds, at a time t up to j, read with any top
that holds the history's top after j from t: Java's get and scan at t are
right. -/
theorem handles_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j t : Nat}
    (hjl : j ≤ ts.length) (htj : t ≤ j) (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandles h.spec al (ts.take j)).1.P t
    HoldsView V (kindOf kind V) t s → TopFrom t (top j) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  intro V hs htp
  have hjn := len_of_ts hts hjl
  have h1 := (bridge_handles_records hm.meetsBridge hm.meetsEvict al hj hmk ts hts j hjl).2.2
  rw [take_map_ts ts hts j, run_P h al j hjn] at h1
  have hV : V = SIS.view h.spec (h.P j) t := SIS.SameNodes.view h1 t
  rw [hV] at hs
  exact hm.java_reads_from hM hkd hjn htj (le_refl t) mid hs htp

/-- **Java's reads after a lazy startup.** After Java's lazy startup from the
records of the first k transactions (the whole stream, or what a crash
leaves), with any reads and writer follows that the model admits: a tree that
holds the view that a read at a time t up to k through the first-touch rule
returns, read with any top that holds the history's top after k from t (a
startup from those records gives that top back: `topOfP_eq`), gives Java's
get and scan at t right. -/
theorem lazy_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) {k : Nat}
    (hk : k ≤ h.ts.length) (ops : List SIS.Op)
    (hops : SIS.OpsOK h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))
      (SIS.run h.spec al (h.ts.take k)).P k
      (SIS.lazyStartup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))) ops) {t : Nat}
    (htk : t ≤ k) (mid : Bool) (s : Tree) (tp : Top) :
    let S : SIS.Stream BVal Nat := (SIS.run h.spec al h.ts).S.take (k + 1)
    let m := ops.foldl (SIS.Mem.step h.spec S) (SIS.lazyStartup h.spec S)
    let V := viewOfList (m.read h.spec S t).2
    HoldsView V (kindOf kind V) t s → TopFrom t (top k) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  intro S m V hs htp
  have hkn : k ≤ h.txs.length := by rw [← h.ts_length]; exact hk
  obtain ⟨h1, h2⟩ := bridge_lazy_read hm.meetsBridge hm.meetsEvict al hj k hk ops hops t htk
  have hV : V = SIS.view h.spec (SIS.run h.spec al (h.ts.take k)).P t := viewOfList_eq h1 h2
  rw [hV, run_P h al k hkn] at hs
  exact hm.java_reads_from hM hkd hkn htk (le_refl t) mid hs htp

/-- The premises are met by the tree as written and the history's top: in a
run with handles, after the first j transactions, Java's get and scan on the
tree after j, with any top that holds the history's top after j from t, are
right at every time t up to j. -/
theorem evict_java_tree (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (ts : List (Nat × Bool × List SIS.HCacheOp)) (hts : ts.map (·.1) = h.ts) {j t : Nat}
    (hjl : j ≤ ts.length) (htj : t ≤ j) (mid : Bool) (tp : Top) (htp : TopFrom t (top j) tp) :
    JReadsRight (h.tree j) tp t mid (h.txs.map (·.ops)) := by
  have hjn := len_of_ts hts hjl
  apply evict_java_reads hm hM hkd al hj hmk ts hts hjl htj mid (h.tree j) tp _ htp
  obtain ⟨_, h1, h2⟩ := full_eviction hm al hj hmk ts hts j hjl t htj
  rw [viewOfList_eq h1 h2]
  have hP : (SIS.run h.spec al ((ts.take j).map (·.1))).P = h.P j := by
    rw [take_map_ts ts hts j, run_P h al j hjn]
  rw [hP]
  exact hm.meetsBridge.tree_holds hkd hjn htj

/-! ## After reclaim's safe cuts -/

/-- **The cut keeps the top nodes that Java's search reads.** After the run
with handles, reads from the first available time f on, evictions, and
restarts from safe cut streams: at every time t from f to the last
transaction, the root of the structure (what a startup from the cut stream
gives back) has as its live child the top node of time t, which holds its
root pointer and its skip pointers as written. Every top node made at or
after f is the top node of its own time, and the top node of time f is the
one of f: so the cut stream holds every top node that `TopFrom f` names. -/
theorem cut_keeps_top (hm : MeetsFull p h top)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2.1)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    {zn : NodeId × TopNode} (hz : topAt (top h.txs.length) t = some zn) :
    let P' := (SIS.runHandlesCut h.spec al cs).1.P
    viewTop (SIS.view h.spec P' t) = some zn.1 ∧
      ∃ nz, SIS.view h.spec P' t zn.1 = some nz ∧ nz.hist = topEntries zn.2 := by
  intro P'
  obtain ⟨_, _, hsame⟩ := full_cut hm al hj hmk hpol cs hcs hcut hreads
  have hlen : cs.length = h.txs.length := by
    have := congrArg List.length hcs
    simp only [List.length_map, BHist.ts_length] at this
    exact this
  rw [hcs] at hsame
  obtain ⟨hx, h0⟩ := hsame t hft (by rw [hlen]; exact htn)
  have hP : (SIS.run h.spec al h.ts).P = h.P h.txs.length := by
    have := run_P h al h.txs.length (le_refl _)
    have ht : h.ts.take h.txs.length = h.ts := by rw [← h.ts_length]; exact List.take_length
    rwa [ht] at this
  rw [hP] at hx h0
  obtain ⟨htop, nz, hv, hnz⟩ := hm.top_view (le_refl _) hz
  have ti := (hm.meetsBridgeTop.inv _ (le_refl h.txs.length)).2
  obtain ⟨_, _, _, hne, _⟩ := ti.topNode zn (topAt_max ti.good hz).1
  refine ⟨?_, nz, ?_, hnz⟩
  · rw [viewTop_congr (h0 rfl)]; exact htop
  · rw [hx zn.1 (fun _ => hne)]; exact hv

/-- **Java's reads after safe cuts.** After the run with handles, reads from
the first available time f on, evictions, and restarts from safe cut
streams: a tree that holds the view of the structure (what a startup from
the cut stream gives back) at a time t from f to the last transaction, with
the kinds of the levels, read with any top that holds the history's top from
f (the top nodes made before f, but the top node of time f, may be gone):
Java's get and scan at t are right. -/
theorem cut_java_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hcut : ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      SIS.CutOK h.spec (SIS.cutMax ((cs.take (j + 1)).map (·.2.1)))
        (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  intro V hs htp
  obtain ⟨_, _, hsame⟩ := full_cut hm al hj hmk hpol cs hcs hcut hreads
  have hlen : cs.length = h.txs.length := by
    have := congrArg List.length hcs
    simp only [List.length_map, BHist.ts_length] at this
    exact this
  rw [hcs] at hsame
  obtain ⟨hx, h0⟩ := hsame t hft (by rw [hlen]; exact htn)
  have hP : (SIS.run h.spec al h.ts).P = h.P h.txs.length := by
    have := run_P h al h.txs.length (le_refl _)
    have ht : h.ts.take h.txs.length = h.ts := by rw [← h.ts_length]; exact List.take_length
    rwa [ht] at this
  rw [hP] at hx h0
  have hx' : ∀ x, x ≠ SIS.root →
      SIS.view h.spec (h.P h.txs.length) t x = V x := fun x hx0 => (hx x (fun _ => hx0)).symm
  have hs2 := holdsView_congr hx' (h0 rfl).symm (kindOf_congr kind hx') hs
  exact hm.java_reads_from hM hkd (le_refl _) htn hft mid hs2 htp

/-- The premise is met by the tree as written: after the run with safe cuts,
the tree after the last transaction holds the view of the structure that a
startup from the cut stream gives back, at every time t from the first
available time on. -/
theorem cut_holds (hm : MeetsFull p h top) (hkd : KindsOK kind h)
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
    HoldsView V (kindOf kind V) t (h.tree h.txs.length) := by
  intro V
  obtain ⟨_, _, hsame⟩ := full_cut hm al hj hmk hpol cs hcs hcut hreads
  have hlen : cs.length = h.txs.length := by
    have := congrArg List.length hcs
    simp only [List.length_map, BHist.ts_length] at this
    exact this
  rw [hcs] at hsame
  obtain ⟨hx, h0⟩ := hsame t hft (by rw [hlen]; exact htn)
  have hP : (SIS.run h.spec al h.ts).P = h.P h.txs.length := by
    have := run_P h al h.txs.length (le_refl _)
    have ht : h.ts.take h.txs.length = h.ts := by rw [← h.ts_length]; exact List.take_length
    rwa [ht] at this
  rw [hP] at hx h0
  have hx' : ∀ x, x ≠ SIS.root → V x = SIS.view h.spec (h.P h.txs.length) t x :=
    fun x hx0 => hx x (fun _ => hx0)
  exact holdsView_congr hx' (h0 rfl) (kindOf_congr kind hx')
    (hm.meetsBridge.tree_holds hkd (le_refl _) htn)

end Contract
