/-
The contract package (bergdb 030-14): the model's structure holds the top as
written. For a history that meets `MeetsFull`, the root's entries in the
model's structure after transaction j are the entries for the top nodes of
`top j`, in order, each at its root time, and each top node holds its root
pointer and its skip pointers at its root time (`TopHeld`); so the top that the
structure holds (`topOfP`, RecoverJava.lean) is the history's top
(`MeetsFull.topOfP_eq`). With recovery, a startup gives back that top, and
Java's search through it finds the view's space root at every time.
-/
import Mathlib.Tactic
import Contract.Proof.RecoverJava
import Contract.BridgeFull

namespace Contract

open SIS (Struct Entry History Node View Changes NewNode Reach)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- The entries of a top node: its root pointer, then its skip pointers, at
its root time. -/
def topEntries (n : TopNode) : History BVal := (topVals n).map (fun v => ⟨n.time, v⟩)

/-- The root's entry for a top node. -/
def rootEntry (zn : NodeId × TopNode) : Entry BVal := ⟨zn.2.time, .top zn.1⟩

/-- What the model's structure after transaction j holds of the top. -/
structure TopHeld (h : BHist) (top : Nat → Top) (j : Nat) : Prop where
  root : ∃ n0, (h.P j).get? SIS.root = some n0 ∧ n0.hist = (top j).map rootEntry
  nodes : ∀ zn ∈ top j, ∃ nz, (h.P j).get? zn.1 = some nz ∧ nz.hist = topEntries zn.2
  notTree : ∀ zn ∈ top j, (h.tree j).obj zn.1 = none
  notRoot : ∀ zn ∈ top j, zn.1 ≠ SIS.root

theorem addsFor_vals (c : Changes BVal) (i : Nat) (x : NodeId) :
    SIS.addsFor c i x = ((c.adds.filter (fun a => a.1 == x)).map (·.2)).map (fun v => ⟨i, v⟩) := by
  simp [SIS.addsFor, List.map_map]

theorem addsFor_nil {c : Changes BVal} {i : Nat} {x : NodeId} (h : ∀ a ∈ c.adds, a.1 ≠ x) :
    SIS.addsFor c i x = [] := by
  unfold SIS.addsFor
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro a ha
  simpa using h a ha

theorem newNodeOf_of_mem {c : Changes BVal} {nn : NewNode} (hm : nn ∈ c.new) :
    ∃ m, SIS.newNodeOf c nn.id = some m ∧ m.hist = [] := by
  unfold SIS.newNodeOf
  generalize c.new = l at hm
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    simp only [List.map_cons]
    rw [SIS.get?_cons]
    by_cases ha : nn.id = a.id
    · simp [ha]
    · simp only [ha, ite_false]
      rcases List.mem_cons.mp hm with he | he
      · exact absurd (by rw [he]) ha
      · exact ih he

/-- The start: the primordial top node, with its root pointer. -/
theorem MeetsFull.topHeld0 (hm : MeetsFull p h top) : TopHeld h top 0 := by
  obtain ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, hnone, hroots⟩ :=
    hm.start
  have hp0 := p0_eq hr hz hzr hnew hadds
  have hts := hm.startTop
  unfold topStartOk at hts
  rw [hadds] at hts
  cases ht0 : top 0 with
  | nil => rw [ht0] at hts; simp at hts
  | cons a l =>
    cases l with
    | cons b l => rw [ht0] at hts; simp at hts
    | nil =>
      obtain ⟨z', n⟩ := a
      rw [ht0] at hts
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hts
      obtain ⟨⟨⟨hz', htime⟩, hsk⟩, hrt⟩ := hts
      subst hz'
      rw [hroots] at hrt
      simp only [rootsOf, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
        and_true] at hrt
      obtain ⟨_, hroot⟩ := hrt
      have hP0 : h.P 0 = h.p0 := rfl
      have hg0 : (h.P 0).get? SIS.root =
          some { level := l0, isData := false, hist := [⟨0, .top z'⟩] } := by
        rw [hP0, hp0]; simp [SIS.get?_cons, SIS.root]
      have hgz : (h.P 0).get? z' =
          some { level := lz, isData := false, hist := [⟨0, .rootKey r⟩] } := by
        rw [hP0, hp0]; simp [SIS.get?_cons, hz, hzr]
      refine ⟨⟨_, hg0, ?_⟩, ?_, ?_, ?_⟩
      · rw [ht0]; simp [rootEntry, htime]
      · intro zn hzn
        rw [ht0] at hzn
        simp only [List.mem_singleton] at hzn
        subst hzn
        refine ⟨_, hgz, ?_⟩
        simp [topEntries, topVals, hsk, htime, hroot]
      · intro zn hzn
        rw [ht0] at hzn
        simp only [List.mem_singleton] at hzn
        subst hzn
        exact hnone _ hzr
      · intro zn hzn
        rw [ht0] at hzn
        simp only [List.mem_singleton] at hzn
        subst hzn
        exact hz

/-- One more transaction keeps it: the top node made, if any, gets its entries
and the root's entry for it; no other top node and no other root entry. -/
theorem MeetsFull.topHeld_step (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {j : Nat}
    (hj : j < h.txs.length) (ih : TopHeld h top j) : TopHeld h top (j + 1) := by
  obtain ⟨hc, _, hmade, hts, _, htc, _, _⟩ := hm.step j hj
  have hg : TopGood (top j) := (hm.meetsTop hM j (Nat.le_of_lt hj)).good.1
  have hfresh := (hm.meetsBridge.step j hj).2.2.2.1.fresh
  have hs0' : (h.tree (j + 1)).obj SIS.root = none := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs0, _⟩ := (hm.meetsBridge.binv (j + 1) hj).link
    exact hs0
  have hP' := h.P_succ hj
  generalize hcdef : h.txs[j].c = c at hmade htc hfresh hP'
  unfold topChangeOk at htc
  simp only [Bool.and_eq_true, List.all_eq_true] at htc
  obtain ⟨hnew1, hrest⟩ := htc
  have hnew : ∀ nn ∈ c.new, nn.id ≠ SIS.root ∧ (top j).node nn.id = none := by
    intro nn hnn
    have := hnew1 nn hnn
    simp only [bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at this
    exact ⟨this.1.1, this.1.2⟩
  have hnotTree : ∀ zn ∈ top j, (h.tree (j + 1)).obj zn.1 = none := by
    intro zn hzn
    cases hso : (h.tree (j + 1)).obj zn.1 with
    | none => rfl
    | some o =>
      have hm' := hmade zn.1 (ih.notTree zn hzn) (by rw [hso]; rfl)
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hm'
      have h1 := (hnew nn hnn).2
      rw [hid, hg.lookup hzn] at h1
      cases h1
  have hold : ∀ zn ∈ top j, (∀ a ∈ c.adds, a.1 ≠ zn.1) →
      ∃ nz, (h.P (j + 1)).get? zn.1 = some nz ∧ nz.hist = topEntries zn.2 := by
    intro zn hzn hadd
    obtain ⟨nz, h1, h2⟩ := ih.nodes zn hzn
    refine ⟨_, by rw [hP', SIS.get?_apply_of_get? h1], ?_⟩
    simp only
    rw [addsFor_nil hadd, List.append_nil, h2]
  rcases hts with htp | ⟨z, n, htp, hzn, htime, hsk⟩
  · -- no top node made
    rw [htp] at hrest
    simp only [beq_self_eq_true, ite_true, Bool.and_eq_true, List.all_eq_true] at hrest
    have hadds : ∀ a ∈ c.adds, ((h.tree (j + 1)).obj a.1).isSome = true := hrest.2
    obtain ⟨n0, h0, hh0⟩ := ih.root
    refine ⟨⟨_, by rw [hP', SIS.get?_apply_of_get? h0], ?_⟩, ?_, ?_, ?_⟩
    · simp only
      rw [addsFor_nil (fun a ha he => by have := hadds a ha; rw [he, hs0'] at this; cases this),
        List.append_nil, hh0, htp]
    · intro zn hzn
      rw [htp] at hzn
      exact hold zn hzn (fun a ha he => by
        have := hadds a ha; rw [he, hnotTree zn hzn] at this; cases this)
    · intro zn hzn; rw [htp] at hzn; exact hnotTree zn hzn
    · intro zn hzn; rw [htp] at hzn; exact ih.notRoot zn hzn
  · -- the top node z made
    have hne : (top (j + 1) == top j) = false := by
      rw [htp]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg List.length he
      simp at this
    rw [hne] at hrest
    simp only [Bool.false_eq_true, ite_false] at hrest
    rw [htp, List.getLast?_append_of_ne_nil _ (by simp)] at hrest
    simp only [List.getLast?_singleton] at hrest
    cases hfl : c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) with
    | nil => rw [hfl] at hrest; simp at hrest
    | cons nn rest =>
      cases rest with
      | cons _ _ => rw [hfl] at hrest; simp at hrest
      | nil =>
      rw [hfl] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
        Bool.or_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨hid, _⟩, _⟩, hzv⟩, hrv⟩, hall⟩ := hrest
      have hnnm : nn ∈ c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
        rw [hfl]; simp
      rw [List.mem_filter] at hnnm
      have hsz : (h.tree (j + 1)).obj z = none := by
        rw [← hid]; simpa using hnnm.2
      have hsz0 : (h.tree j).obj z = none := by
        cases hso : (h.tree j).obj z with
        | none => rfl
        | some o =>
          obtain ⟨o', ho', _⟩ := hc.2.1 z o hso
          rw [hsz] at ho'; cases ho'
      have hPz : (h.P j).get? z = none := by
        rw [← hid]; exact hfresh nn hnnm.1 (by rw [hid]; exact hsz0)
      have hzt : ∀ zn ∈ top j, zn.1 ≠ z := by
        intro zn hzn' he
        have := hg.lookup hzn'
        rw [he, hzn] at this; cases this
      obtain ⟨n0, h0, hh0⟩ := ih.root
      refine ⟨⟨_, by rw [hP', SIS.get?_apply_of_get? h0], ?_⟩, ?_, ?_, ?_⟩
      · simp only
        rw [addsFor_vals, hrv, hh0, htp, List.map_append]
        simp [rootEntry, htime]
      · intro zn hzn'
        rw [htp] at hzn'
        rcases List.mem_append.mp hzn' with hzn' | hzn'
        · exact hold zn hzn' (fun a ha he => by
            rcases hall a ha with (h1 | h1) | h1
            · rw [he, hnotTree zn hzn'] at h1; cases h1
            · exact hzt zn hzn' (he.symm.trans h1)
            · exact ih.notRoot zn hzn' (he.symm.trans h1))
        · simp only [List.mem_singleton] at hzn'
          subst hzn'
          obtain ⟨m, hm1, hm2⟩ := newNodeOf_of_mem hnnm.1
          rw [hid] at hm1
          refine ⟨_, by rw [hP', SIS.get?_apply, hPz, Option.none_or, hm1]; rfl, ?_⟩
          simp only
          rw [hm2, List.nil_append, addsFor_vals, hzv, topEntries, htime]
      · intro zn hzn'
        rw [htp] at hzn'
        rcases List.mem_append.mp hzn' with hzn' | hzn'
        · exact hnotTree zn hzn'
        · simp only [List.mem_singleton] at hzn'
          subst hzn'
          exact hsz
      · intro zn hzn'
        rw [htp] at hzn'
        rcases List.mem_append.mp hzn' with hzn' | hzn'
        · exact ih.notRoot zn hzn'
        · simp only [List.mem_singleton] at hzn'
          subst hzn'
          rw [← hid]
          exact (hnew nn hnnm.1).1

/-- After every transaction. -/
theorem MeetsFull.topHeld (hm : MeetsFull p h top) (hM : 1 ≤ p.M) :
    ∀ j, j ≤ h.txs.length → TopHeld h top j
  | 0, _ => hm.topHeld0
  | j + 1, hj => hm.topHeld_step hM (by omega) (hm.topHeld hM j (by omega))

/-! ## The top that the structure holds -/

theorem find?_fst (y : NodeId) : ∀ tp : Top,
    (tp.find? (fun zn => zn.1 == y)).map (·.2) = tp.lookup y
  | [] => rfl
  | (z, n) :: r => by
    simp only [List.find?_cons, List.lookup_cons]
    by_cases hz : z = y
    · subst hz; simp
    · have h1 : (z == y) = false := by simpa using hz
      have h2 : (y == z) = false := by simpa using fun h => hz h.symm
      simp only [h1, h2]
      exact find?_fst y r

theorem topTime_eq {tp : Top} (hg : TopGood tp) {y : NodeId} {ny : TopNode} (hm : (y, ny) ∈ tp) :
    topTime (tp.map rootEntry) y = ny.time := by
  unfold topTime
  rw [List.find?_map]
  have hf : (fun e : Entry BVal => e.val == BVal.top y) ∘ rootEntry = (fun zn => zn.1 == y) := by
    funext zn
    simp [rootEntry]
  rw [hf]
  have := find?_fst y tp
  have hl : tp.lookup y = some ny := hg.lookup hm
  rw [hl] at this
  cases hfd : tp.find? (fun zn => zn.1 == y) with
  | none => rw [hfd] at this; cases this
  | some zn =>
    rw [hfd] at this
    simp only [Option.map_some, Option.some.injEq] at this
    simp [rootEntry, this]

theorem topNodeOf_eq {tp : Top} (hg : TopGood tp) {z : NodeId} {n : TopNode} (hm : (z, n) ∈ tp) :
    topNodeOf (tp.map rootEntry) n.time (topEntries n) = n := by
  obtain ⟨time, root, skips⟩ := n
  have hsk : ∀ q ∈ skips, topTime (tp.map rootEntry) q.2.1 = q.2.2 := by
    intro q hq
    obtain ⟨ny, hny, hnt, _⟩ := hg.skip hm hq
    rw [topTime_eq hg hny, hnt]
  simp only [topNodeOf, topEntries, topVals, List.map_cons, List.map_map, TopNode.mk.injEq,
    true_and]
  refine ⟨by simp [rootPtrOf], ?_⟩
  simp only [List.filterMap_cons, List.filterMap_map]
  conv_rhs => rw [← List.filterMap_some (l := skips)]
  apply List.filterMap_congr
  intro q hq
  obtain ⟨j, y, ty⟩ := q
  simp only [Function.comp, Option.some.injEq, Prod.mk.injEq, true_and]
  exact hsk _ hq

/-- The top that a structure holds depends only on its nodes. -/
theorem topOfP_congr {P P' : Struct BVal} (hP : ∀ x, P.get? x = P'.get? x) :
    topOfP P = topOfP P' := by
  simp only [topOfP, hP]

/-- The model's structure after transaction j holds the history's top. -/
theorem MeetsFull.topOfP_eq (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {j : Nat}
    (hj : j ≤ h.txs.length) : topOfP (h.P j) = top j := by
  have hi := hm.topHeld hM j hj
  have hg : TopGood (top j) := (hm.meetsTop hM j hj).good.1
  obtain ⟨n0, h0, hh0⟩ := hi.root
  unfold topOfP
  rw [h0]
  simp only
  rw [hh0, List.filterMap_map]
  conv_rhs => rw [← List.filterMap_some (l := top j)]
  apply List.filterMap_congr
  intro zn hzn
  obtain ⟨nz, hnz, hnzh⟩ := hi.nodes zn hzn
  simp only [Function.comp, rootEntry, hnz, Option.map_some, hnzh]
  rw [← hh0, hh0, topNodeOf_eq hg (z := zn.1) (n := zn.2) hzn]

/-! ## The space roots at earlier times -/

/-- The tree after transaction k, read at an earlier time t, has the space
roots of the tree after t. -/
theorem MeetsBridge.roots_at (hm : MeetsBridge p h) {t : Nat} :
    ∀ k, t ≤ k → k ≤ h.txs.length → ((h.tree k).at t).roots = (h.tree t).roots
  | 0, htk, hk => by
    have : t = 0 := by omega
    subst this
    rw [(hm.binv 0 hk).timely.at_eq]
  | k + 1, htk, hk => by
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · have ih := hm.roots_at (t := t) k (by omega) (by omega)
      obtain ⟨new, hn, ht⟩ := (hm.step k (by omega)).1.2.2.2
      rw [← ih]
      simp only [Tree.at, hn, List.filter_append]
      have : new.filter (fun r => decide (r.1 ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro r hr
        rw [ht r hr]
        simp
        omega
      rw [this, List.append_nil]
    · have : t = k + 1 := by omega
      subst this
      rw [(hm.binv (k + 1) hk).timely.at_eq]

/-- Java's search through the history's top at a time t up to k finds the
view's space root. -/
theorem MeetsFull.findRoot_view (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (mid : Bool) :
    findRoot (top k) t mid = viewRoot (SIS.view h.spec (h.P k) t) := by
  rw [top_right (hm.meetsTop hM k hk) t mid, hm.meetsBridge.viewRoot_eq hk htk]
  simp only [Tree.root]
  rw [hm.meetsBridge.roots_at k htk hk]

/-! ## The tree as written holds the view -/

theorem Sub.trans' {s1 s2 s3 : Tree} (h1 : Sub s1 s2) (h2 : Sub s2 s3) : Sub s1 s3 :=
  ⟨fun x o hx => h2.1 x o (h1.1 x o hx), h2.2.trans h1.2⟩

/-- The tree after transaction k, read at an earlier time t, holds the tree
after t, read at t. -/
theorem MeetsBridge.sub_at (hm : MeetsBridge p h) {t : Nat} :
    ∀ k, t ≤ k → k ≤ h.txs.length → Sub ((h.tree t).at t) ((h.tree k).at t)
  | 0, htk, _ => by
    have : t = 0 := by omega
    subst this
    exact ⟨fun _ _ hx => hx, rfl⟩
  | k + 1, htk, hk => by
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · exact (hm.sub_at (t := t) k (by omega) (by omega)).trans'
        ((hm.step k (by omega)).1.2.sub hlt)
    · have : t = k + 1 := by omega
      subst this
      exact ⟨fun _ _ hx => hx, rfl⟩

/-- The tree as written holds the view: the tree after transaction k holds
the view of the model's structure after k at every time t up to k, with the
kinds of the levels. So the premise of Java's reads is met by the tree that
the history wrote. -/
theorem MeetsBridge.tree_holds (hm : MeetsBridge p h) {kind : Nat → Bool} (hkd : KindsOK kind h)
    {k t : Nat} (hk : k ≤ h.txs.length) (htk : t ≤ k) :
    HoldsView (SIS.view h.spec (h.P k) t) (kindOf kind (SIS.view h.spec (h.P k) t)) t (h.tree k) := by
  have ht : t ≤ h.txs.length := le_trans htk hk
  have hi := hm.binv t ht
  have hsub := hm.sub_at k htk hk
  rw [hi.timely.at_eq] at hsub
  rw [view_later hm htk hk]
  intro x n hx0 hxz hv
  obtain ⟨n0, z, nz, y, ny, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  have hvz : viewTop (SIS.view h.spec (h.P t) t) = some z := by
    have hr0 : Reach h.spec (h.P t) t SIS.root := Reach.root n0 h0
    have hv0 := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hr0) h0
    have hl0' : blive (n0.hist.upTo t) = [z] := hl0
    simp [viewTop, hv0, hl0']
  have hrx : SIS.reachable h.spec (h.P t) t x = true := by
    by_contra hnr
    simp [SIS.view, hnr] at hv
  rw [SIS.reachable_iff] at hrx
  rcases hi.reach3 h0 hl0 hz hly hroot hy hrx with h1 | h1 | h1
  · exact absurd h1 hx0
  · exact absurd (by rw [hvz, h1]) hxz
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hi.reach_obj h1)
    have hko := hsub.1 x o ho
    have hrx' := hi.mem_reach_model h1
    cases o with
    | key nt =>
      have hP : (h.P t).get? x = some ⟨nt.level, false, entriesOf nt.ks⟩ := hi.rep x _ ho
      have hup : (entriesOf nt.ks).upTo t = entriesOf nt.ks := by
        apply SIS.upTo_of_forall
        intro e he
        rcases entriesFrom_time_mem nt.ks [] 0 [] e he with h2 | h2
        · omega
        · exact hi.timely.1 x nt ho e.time h2
      rw [view_of_reachable hrx' hP, hup] at hv
      injection hv with hv
      subst hv
      simp only [Tree.at, Option.map_eq_some_iff] at hko
      obtain ⟨o', ho', hat⟩ := hko
      cases o' with
      | val v => simp [Obj.at] at hat
      | key kn =>
        simp only [Obj.at, Obj.key.injEq] at hat
        obtain ⟨wf1, wf2⟩ := hi.wf x nt ho
        refine ⟨fun _ => ⟨kn, ho', ?_, ?_, ?_, ?_, ?_⟩, fun hd => by simp at hd⟩
        · rw [← hat]
        · have : kindOf kind (SIS.view h.spec (h.P t) t) x = kind nt.level := by
            simp [kindOf, view_of_reachable hrx' hP]
          rw [this, ← hm.kinds hkd t ht x nt ho, ← hat]
        · rw [show prefixAt kn.ks t = nt.ks by rw [← hat]]; exact wf1
        · rw [show prefixAt kn.ks t = nt.ks by rw [← hat]]; exact wf2
        · rw [show prefixAt kn.ks t = nt.ks by rw [← hat]]
    | val v =>
      obtain ⟨t0, ht0, hP⟩ := hi.rep x _ ho
      have hup : SIS.History.upTo [(⟨t0, .data v⟩ : Entry BVal)] t = [⟨t0, .data v⟩] := by
        apply SIS.upTo_of_forall
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        exact ht0
      rw [view_of_reachable hrx' hP, hup] at hv
      injection hv with hv
      subst hv
      simp only [Tree.at, Option.map_eq_some_iff] at hko
      obtain ⟨o', ho', hat⟩ := hko
      cases o' with
      | key kn => simp [Obj.at] at hat
      | val v' =>
        simp only [Obj.at, Obj.val.injEq] at hat
        subst hat
        exact ⟨fun hd => by simp at hd, fun _ => ⟨v', by simp [dataOf], ho'⟩⟩

end Contract
