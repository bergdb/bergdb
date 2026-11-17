/-
The contract package (bergdb 030-08): the theorems over the tree with its
top.

For any history that meets the contract with TREE and the top's clauses
(`MeetsTop`, ShapeStatement.lean):

* it meets the contract with TREE, so the theorems of Theorems.lean and
  TheoremsShape.lean hold for it (`MeetsTop.shape`, `MeetsTop.meets`);
* TP24: Java's search through the skip pointers, at any lookup time, at a
  record's time or between two records, finds the top node made last at or
  before it, and its root pointer is the tree's space root of that time
  (`top_right`);
* so Java's readers, which start from that search, are right at every time
  of the history: every get (`jget_right`) and every scan (`jscan_right`)
  gives what the plain map gives;
* the skip pointers of the abstract model's R4 and its dead top nodes: from
  the super root, every top node can be reached through skip pointers
  (`skip_closure`), and no skip pointer names the super root (`skip_dead`).

These replace `get_right` and `scan_right` as the statements about Java's
reads: those speak of readers that start from the specification's space root
(`Tree.root`, the last one at or before the time), and stay, unchanged, as
the step to these.
-/
import Contract.TheoremsShape
import Contract.Proof.Top

namespace Contract

variable {p : Params} {txs : List (List Op)} {s : Tree} {tp : Top}

/-- A history that meets the contract with TREE and the top meets the
contract with TREE. -/
theorem MeetsTop.shape (h : MeetsTop p txs s tp) : MeetsShape p txs s := by
  induction h with
  | start s tp hs htr _ _ => exact MeetsShape.start s hs htr
  | step txs s tp ops D s' tp' _ hc htr _ _ ih => exact MeetsShape.step txs s ops D s' ih hc htr

/-- And the contract. -/
theorem MeetsTop.meets (h : MeetsTop p txs s tp) : Meets p txs s := h.shape.meets

/-- The tree's space roots are the top's. -/
theorem MeetsTop.roots (h : MeetsTop p txs s tp) : s.roots = rootsOf tp := by
  cases h with
  | start _ _ _ _ _ hr => exact hr
  | step _ _ _ _ _ _ _ _ _ _ _ hr => exact hr

/-- The top of a history is built by the clauses, with root times up to the
history's last. -/
theorem MeetsTop.good (h : MeetsTop p txs s tp) :
    TopGood tp ∧ ∀ zm ∈ tp, zm.2.time ≤ txs.length := by
  induction h with
  | start s tp _ _ hst _ =>
    obtain ⟨z, n, rfl, h0, hsk⟩ := hst
    have hok : skipsOk [] n = true := by simp [skipsOk, hsk, strictUp]
    have hg := TopGood.snoc [] z n TopGood.nil (by simp [Top.node, List.lookup]) (by simp) hok
    refine ⟨by simpa using hg, ?_⟩
    intro zm hzm
    simp only [List.mem_singleton] at hzm
    subst hzm
    simp [h0]
  | step txs s tp ops D s' tp' _ _ _ hts _ ih =>
    obtain ⟨hg, hle⟩ := ih
    simp only [List.length_append, List.length_singleton]
    rcases hts with rfl | ⟨z, n, rfl, hz, hti, hok⟩
    · exact ⟨hg, fun zm hzm => Nat.le_succ_of_le (hle zm hzm)⟩
    · have hlt : ∀ zm ∈ tp, zm.2.time < n.time := by
        intro zm hzm
        rw [hti]
        exact Nat.lt_succ_of_le (hle zm hzm)
      refine ⟨TopGood.snoc tp z n hg hz hlt hok, ?_⟩
      intro zm hzm
      rcases List.mem_append.mp hzm with hzm | hzm
      · exact Nat.le_succ_of_le (hle zm hzm)
      · simp only [List.mem_singleton] at hzm
        subst hzm
        simp [hti]

/-- TP24 for a history that meets the contract with the top: Java's search,
at any lookup time t (between the records t and t + 1 if `mid`), gives the
tree's space root of time t. -/
theorem top_right (h : MeetsTop p txs s tp) (t : Time) (mid : Bool) :
    findRoot tp t mid = (s.at t).root := by
  rw [findRoot_right h.good.1 t mid, root_at_top h.roots t]

/-- TP10 for Java's reader: a get at time t, the latest or an earlier one, at
a record's time or between two records, starting from Java's search through
the top, gives what the plain map after the first t transactions gives. -/
theorem jget_right (h : MeetsTop p txs s tp) (t : Time) (ht : t ≤ txs.length) (mid : Bool)
    (k : Key) : jget s tp t mid k = refGet (refMap (txs.take t)) k := by
  rw [← get_right h.meets t ht k]
  unfold jget get
  rw [top_right h t mid]
  cases (s.at t).root <;> rfl

/-- TP11 for Java's reader: a scan at time t, the latest or an earlier one,
at a record's time or between two records, forward or backward, with or
without a start key and an end key, starting from Java's search through the
top, gives what a scan of the plain map after the first t transactions
gives. -/
theorem jscan_right (h : MeetsTop p txs s tp) (t : Time) (ht : t ≤ txs.length) (mid : Bool)
    (req : ScanReq) (hreq : req.wf = true) (limit : Nat) :
    jscan s tp t mid req limit = refScan (refMap (txs.take t)) req limit := by
  rw [← scan_right h.meets t ht req hreq limit]
  unfold jscan scan
  rw [top_right h t mid]
  cases (s.at t).root <;> rfl

/-! ## The abstract model's top rules: R4 and the dead top nodes -/

/-- Top node y can be reached from top node z through skip pointers. -/
inductive SkipPath (tp : Top) : NodeId → NodeId → Prop where
  | refl (z : NodeId) : SkipPath tp z z
  | step (z : NodeId) (n : TopNode) (q : Nat × NodeId × Time) (y : NodeId) :
      tp.node z = some n → q ∈ n.skips → SkipPath tp q.2.1 y → SkipPath tp z y

theorem pairwise_or {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => by simp at ha
  | c :: r, hp, a, b, ha, hb => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact Or.inl (ha'.trans hb'.symm)
    · subst ha'; exact Or.inr (Or.inl (hp.1 b hb'))
    · subst hb'; exact Or.inr (Or.inr (hp.1 a ha'))
    · exact pairwise_or hp.2 ha' hb'

/-- Two top nodes with one root time are one. -/
theorem TopGood.eq_of_time {tp : Top} (hg : TopGood tp) {a b : NodeId × TopNode} (ha : a ∈ tp)
    (hb : b ∈ tp) (h : a.2.time = b.2.time) : a = b := by
  rcases pairwise_or hg.pairwise ha hb with h1 | h1 | h1
  · exact h1
  · exact absurd h (Nat.ne_of_lt h1)
  · exact absurd h.symm (Nat.ne_of_lt h1)

/-- From a top node, every top node made before it can be reached through
skip pointers: along the lowest ones, each to the top node just before. -/
theorem TopGood.skipPath {tp : Top} (hg : TopGood tp) :
    ∀ (k : Nat) (z : NodeId) (n : TopNode), n.time = k → (z, n) ∈ tp →
      ∀ y ny, (y, ny) ∈ tp → ny.time ≤ n.time → SkipPath tp z y := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro z n hk hm y ny hym hle
    rcases Nat.lt_or_ge ny.time n.time with hlt | hge
    · cases hh : n.skips.head? with
      | none =>
        rw [List.head?_eq_none_iff] at hh
        exact absurd (hg.first hm hh _ hym) (Nat.not_le.mpr hlt)
      | some q =>
        obtain ⟨np, hpm, hpt, hmax⟩ := hg.pred hm hh
        have hqm : q ∈ n.skips := List.mem_of_mem_head? hh
        obtain ⟨np', hpm', hpt', hplt⟩ := hg.skip hm hqm
        have : np' = np := by
          have := (hg.lookup hpm').symm.trans (hg.lookup hpm)
          simpa using this
        subst this
        refine SkipPath.step z n q y (hg.lookup hm) hqm ?_
        exact ih np'.time (hk ▸ hplt) q.2.1 np' rfl hpm' y ny hym (hmax _ hym hlt)
    · have := hg.eq_of_time hm hym (Nat.le_antisymm hge hle)
      simp only [Prod.mk.injEq] at this
      rw [this.1]
      exact SkipPath.refl y

/-- R4 for a history that meets the contract with the top: from the super
root, every top node can be reached through skip pointers. -/
theorem skip_closure (h : MeetsTop p txs s tp) {w : NodeId} {nw : TopNode}
    (hw : tp.getLast? = some (w, nw)) : ∀ zm ∈ tp, SkipPath tp w zm.1 := by
  have hg := h.good.1
  intro zm hzm
  exact hg.skipPath nw.time w nw rfl (List.mem_of_getLast? hw) zm.1 zm.2 hzm
    (hg.last_max hw zm hzm)

/-- The dead top nodes, for a history that meets the contract with the top:
no skip pointer names the super root, the one top node that a reader reaches
from the root; a skip pointer names only an older top node. -/
theorem skip_dead (h : MeetsTop p txs s tp) {w : NodeId} {nw : TopNode}
    (hw : tp.getLast? = some (w, nw)) : ∀ zn ∈ tp, ∀ q ∈ zn.2.skips, q.2.1 ≠ w := by
  have hg := h.good.1
  intro zn hzn q hq heq
  obtain ⟨ny, hym, _, hlt⟩ := hg.skip hzn hq
  rw [heq] at hym
  have : ny = nw := by
    have := (hg.lookup hym).symm.trans (hg.lookup (List.mem_of_getLast? hw))
    simpa using this
  subst this
  exact absurd (Nat.lt_of_lt_of_le hlt (hg.last_max hw zn hzn)) (Nat.lt_irrefl _)

end Contract
