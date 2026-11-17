/-
The contract package (bergdb 030-14): the reader of the model's view is right
for a history that meets the bridge's clauses (`MeetsBridge.view_reads`).

* The past is fixed in the model (`view_later`): the view at time t of the
  structure after transaction k is the view at t of the structure after
  transaction t (the abstract model's `Grow`, `reachable_grow`).
* At the latest time (`BInv.view_agree`): the tree of the view after
  transaction t has the tree's space root, and every node that the tree
  reaches as the tree has it, with the same live klongs (`live_klongsOfE`).
* The kinds are fixed (`MeetsBridge.leaf_later`): a key node keeps its kind
  (the frame).
* So the reader of the view reads as the tree, which reads as the plain map
  (`get_contents`, `scan_contents`, `Meets.at_time`).
-/
import Mathlib.Tactic
import SIS.Proof.StepInv
import Contract.Proof.Recover
import Contract.Proof.BridgeReach
import Contract.Proof.BridgeStep
import Contract.Theorems
import Contract.BridgeTheorems

namespace Contract

open SIS (Struct Entry History Node View Reach)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist}

/-! ## The past is fixed -/

/-- The model's structure after transaction t grows, up to time t, into the
structure after any later transaction k. -/
theorem BHist.grow (h : BHist) {t : Nat} : ∀ k, t ≤ k → k ≤ h.txs.length →
    SIS.Grow (h.P t) t (h.P k)
  | 0, htk, _ => by
    have : t = 0 := by omega
    subst this
    exact SIS.Grow.refl _ _
  | k + 1, htk, hk => by
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · have h1 := h.grow (t := t) k (by omega) (by omega)
      rw [h.P_succ (by omega : k < h.txs.length)]
      exact SIS.Grow.trans h1 (SIS.grow_apply (k := k) _ _ _ (by omega)) (by omega)
    · have : t = k + 1 := by omega
      subst this
      exact SIS.Grow.refl _ _

/-- An algorithm with BergDB's still-dirty test, to reach the model's
invariant of a run. -/
def BHist.al0 (h : BHist) : SIS.Algo BVal Nat :=
  { policy := fun _ _ _ _ => 0, stillDirty := SIS.javaTest h.spec }

/-- A4 in the model: every pointer of every entry of the structure after
transaction t names a node on a lower level (the model's invariant). -/
theorem MeetsBridge.ptrsOK (hm : MeetsBridge p h) {t : Nat} (ht : t ≤ h.txs.length) :
    SIS.PtrsOK h.spec (h.P t) := by
  have hinv := SIS.inv_st h.spec h.al0 h.ts (hm.runOK _) (SIS.algOK_of h.spec _ (Or.inl rfl)) t
    (by rw [h.ts_length]; exact ht)
  have := hinv.ptrs
  unfold SIS.st at this
  rwa [run_P h _ t ht] at this

theorem liveSub (h : BHist) : SIS.LiveSub h.spec :=
  fun hst y hy => SIS.Check.blive_sub hst y hy

/-- The past is fixed: the view at time t of the structure after transaction
k is the view at t of the structure after transaction t. -/
theorem view_later (hm : MeetsBridge p h) {t k : Nat} (htk : t ≤ k) (hk : k ≤ h.txs.length) :
    SIS.view h.spec (h.P k) t = SIS.view h.spec (h.P t) t := by
  have hg := h.grow k htk hk
  have hp := hm.ptrsOK (le_trans htk hk)
  have hi := hm.binv t (le_trans htk hk)
  obtain ⟨n0, _, _, _, _, h0, _⟩ := hi.link
  have hroot : ((h.P t).get? SIS.root).isSome := by rw [h0]; rfl
  funext x
  unfold SIS.view
  rw [SIS.reachable_grow (liveSub h) hp hroot hg (le_refl t) x]
  split
  · rename_i hr
    rw [SIS.reachable_iff] at hr
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hr.isSome
    obtain ⟨n', h1, h2, h3, h4⟩ := hg x n hn
    rw [h1, hn]
    obtain ⟨l, d, hs⟩ := n
    obtain ⟨l', d', hs'⟩ := n'
    simp only at h2 h3 h4
    simp [h2, h3, h4]
  · rfl

/-! ## The kinds are fixed -/

/-- A key node keeps its kind in every later tree of the history. -/
theorem MeetsBridge.leaf_later (hm : MeetsBridge p h) {t : Nat} : ∀ k, t ≤ k → k ≤ h.txs.length →
    ∀ x n, (h.tree t).obj x = some (.key n) →
      ∃ n', (h.tree k).obj x = some (.key n') ∧ n'.leaf = n.leaf
  | 0, htk, _, x, n, hx => by
    have : t = 0 := by omega
    subst this
    exact ⟨n, hx, rfl⟩
  | k + 1, htk, hk, x, n, hx => by
    rcases Nat.lt_or_ge t (k + 1) with hlt | hge
    · obtain ⟨n', h1, h2⟩ := hm.leaf_later (t := t) k (by omega) (by omega) x n hx
      have hfr := (hm.step k (by omega)).1.2
      obtain ⟨o', ho', hext, _⟩ := hfr.1 x _ h1
      cases o' with
      | val v => exact absurd hext (by simp [Ext])
      | key n'' => exact ⟨n'', ho', by rw [hext.2.1, h2]⟩
    · have : t = k + 1 := by omega
      subst this
      exact ⟨n, hx, rfl⟩

/-! ## At the latest time -/

theorem view_of_reachable {sp : SIS.Spec BVal Nat} {P : Struct BVal} {t : Nat} {x : NodeId}
    {n : Node BVal} (hr : SIS.reachable sp P t x = true) (hn : P.get? x = some n) :
    SIS.view sp P t x = some { n with hist := n.hist.upTo t } := by
  simp [SIS.view, hr, hn]

/-- The tree of the view after transaction t, at t, has the tree's space root,
and every node that the tree reaches as the tree has it: a key node with the
same level, kind and live klongs, a value with its value. -/
theorem BInv.view_agree {t : Nat} (hi : BInv h t) (lf : NodeId → Bool)
    (hlf : ∀ x n, (h.tree t).obj x = some (.key n) → lf x = n.leaf) :
    (viewTree (SIS.view h.spec (h.P t) t) lf).root = (h.tree t).root ∧
    ∀ x o, x ∈ reach (h.tree t) → (h.tree t).obj x = some o →
      ∃ o', (viewTree (SIS.view h.spec (h.P t) t) lf).obj x = some o' ∧ ObjAgree o o' := by
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  have hr0 : Reach h.spec (h.P t) t SIS.root := Reach.root n0 h0
  have hrz : Reach h.spec (h.P t) t z :=
    Reach.child hr0 h0 (by rw [hl0]; exact List.mem_singleton_self z) hz hlz
  have hzr : z ≠ SIS.root := by
    intro he
    rw [he, h0] at hz
    injection hz with hz
    subst hz
    exact absurd hlz (lt_irrefl _)
  constructor
  · have hv0 := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hr0) h0
    have hvz := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hrz) hz
    have hvr : viewRoot (SIS.view h.spec (h.P t) t) = some y := by
      unfold viewRoot
      rw [hv0]
      have hl0' : blive (n0.hist.upTo t) = [z] := hl0
      have hly' : blive (nz.hist.upTo t) = [y] := hly
      simp only [Option.map_some, hl0', hzr, ite_false, hvz, hly', List.head?_cons]
    rw [hroot]
    simp [viewTree, Tree.root, hvr]
  · intro x o hx ho
    have hx0 : x ≠ SIS.root := by
      intro he; rw [he, hs0] at ho; cases ho
    have hrx := hi.mem_reach_model hx
    have hrep := hi.rep x o ho
    cases o with
    | key nx =>
      have hP : (h.P t).get? x = some { level := nx.level, isData := false, hist := entriesOf nx.ks } :=
        hrep
      have hup : (entriesOf nx.ks).upTo t = entriesOf nx.ks := by
        apply SIS.upTo_of_forall
        intro e he
        rcases entriesFrom_time_mem nx.ks [] 0 [] e he with h1 | h1
        · omega
        · exact hi.timely.1 x nx ho e.time h1
      have hv := view_of_reachable hrx hP
      refine ⟨.key { level := nx.level, leaf := lf x, ks := klongsOfE (entriesOf nx.ks) }, ?_, ?_⟩
      · simp only [viewTree, hx0, ite_false, hv, hup, Option.bind_some, objOf]
        rfl
      · obtain ⟨hwf, hfull⟩ := hi.wf x nx ho
        exact ⟨rfl, hlf x nx ho, live_klongsOfE nx.ks hwf hfull, klongsOfE_wf _⟩
    | val v =>
      obtain ⟨t0, ht0, hP⟩ := hrep
      have hv := view_of_reachable hrx hP
      have hup : SIS.History.upTo [(⟨t0, .data v⟩ : Entry BVal)] t = [⟨t0, .data v⟩] := by
        apply SIS.upTo_of_forall
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        exact ht0
      refine ⟨.val v, ?_, rfl⟩
      simp only [viewTree, hx0, ite_false, hv, hup, Option.bind_some, objOf]
      rfl

/-! ## The reader of the view is right -/

/-- A tree that meets the invariants has a space root, sound. -/
theorem invOk_good {s : Tree} (h : invOk p s = true) : ∃ r, s.root = some r ∧ Good s r 0 none := by
  unfold invOk at h
  cases hr : s.root with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        exact ⟨r, rfl, walk_good _ _ _ _ h.2⟩

/-- For a history that meets the bridge's clauses: the reader of the view of
the model's structure after transaction k, at any time t up to k, with the
kinds of the tree after k, is right. -/
theorem MeetsBridge.view_reads (hm : MeetsBridge p h) (hM : 1 ≤ p.M) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) :
    ReadsRight (SIS.view h.spec (h.P k) t) (leafOf (h.tree k)) (h.txs.map (·.ops)) t := by
  rw [view_later hm htk hk]
  have ht : t ≤ h.txs.length := le_trans htk hk
  have hi := hm.binv t ht
  have hmt := hm.meets hM t ht
  have hlen : ((h.txs.take t).map (·.ops)).length = t := by simp; omega
  obtain ⟨hinv, hcont⟩ := hmt.at_time t (by rw [hlen])
  rw [hi.timely.at_eq] at hinv hcont
  have htake : ((h.txs.take t).map (·.ops)).take t = (h.txs.map (·.ops)).take t := by
    rw [List.take_of_length_le (by rw [hlen]), List.map_take]
  rw [htake] at hcont
  obtain ⟨r, hr, hG⟩ := invOk_good hinv
  have hlf : ∀ x n, (h.tree t).obj x = some (.key n) → leafOf (h.tree k) x = n.leaf := by
    intro x n hx
    obtain ⟨n', h1, h2⟩ := hm.leaf_later k htk hk x n hx
    simp [leafOf, h1, h2]
  obtain ⟨hroot, hag⟩ := hi.view_agree (leafOf (h.tree k)) hlf
  have hr' : (viewTree (SIS.view h.spec (h.P t) t) (leafOf (h.tree k))).root = some r := by
    rw [hroot, hr]
  obtain ⟨n0, hobj0⟩ : ∃ n0, (h.tree t).obj r = some (.key n0) := by
    cases hG with
    | mk _ _ _ n hobj _ _ _ _ _ _ _ => exact ⟨n, hobj⟩
  have hreach : reach (h.tree t) = reachAt (h.tree t) ((h.tree t).fuel r) r := by
    unfold reach; rw [hr]
  have hR : ∀ x n c y, x ∈ reach (h.tree t) → (h.tree t).obj x = some (.key n) →
      (c, y) ∈ live n.ks → y ∈ reach (h.tree t) := by
    intro x n c y hx hn hy
    rw [hreach] at hx ⊢
    exact reachAt_closed hi.lev _ r _ hobj0 (by simp [Tree.fuel, hobj0, lvl]) x n c y hx hn hy
  have hRr : r ∈ reach (h.tree t) := by rw [hreach]; exact mem_reachAt_self _ _ _
  constructor
  · intro key
    unfold vget
    rw [get_eq_of_agree hr hr' hG _ hR hag hRr, get_contents hinv, hcont]
    rfl
  · intro req hreq limit
    unfold vscan
    rw [scan_eq_of_agree hr hr' hG _ hR hag hRr req hreq, scan_contents hinv req hreq, hcont]

end Contract
