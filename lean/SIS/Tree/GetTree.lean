import SIS.Tree.GetSplit
import SIS.Tree.GetUnder
import SIS.Tree.WriterTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `OpGetOK` (bergdb 024-12, TP10) with the writer's tree as a premise
(`WriterTreeOK`, SIS/Tree/WriterTree.lean): `OpGetTreeOK` is `OpGetOKUnder`
for a state that has the writer's tree, and gives `OpGetOKUnder` with P's tree
before the transaction as a run premise (`opGetOKUnder_of_tree`), from the
writer's tree kept by each operation (`OpTreeOK`).

The rules of the writer read a key's path through every live klong of a node
(`ReachS`), a value's too; the writer's tree follows only links (`TLink`).
With `ValueLinksOK`, a short segment's klong in a leaf of the tree names no key
node, and TREE for key nodes follows from the writer's tree
(`treeK_of_treeOK`), the premise of the time split rule
(`writerWP_put_timeSplit_tree`). -/

/-- A short segment's klong live in a leaf that the tree reaches names no key
node: it names a value. -/
def ValueLinksOK (look : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  ∀ x n, TReach look t r x → look x = some n → n.leaf = true →
    ∀ c z, (c, z) ∈ n.liveAt t → segLen c ≠ 7 → look z = none

/-- A node that the reads reach is in the tree or is no key node. -/
theorem reachS_tReach (look : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hv : ValueLinksOK look t r) :
    ∀ x, ReachS look t r x → TReach look t r x ∨ look x = none := by
  intro x hx
  induction hx with
  | root => exact Or.inl TReach.root
  | step x n c z _ hn hz ih =>
    rcases ih with ih | ih
    · by_cases hl : n.leaf = true ∧ segLen c ≠ 7
      · exact Or.inr (hv x n ih hn hl.1 c z hz hl.2)
      · left
        exact TReach.link ih ⟨n, hn, hz, fun h => Decidable.byContradiction (fun hne => hl ⟨h, hne⟩)⟩
    · rw [hn] at ih; cases ih

/-- TREE for key nodes, over every node that the reads reach, from the
writer's tree. -/
theorem treeK_of_treeOK (look : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hT : TreeOK look t r) (hv : ValueLinksOK look t r) :
    ∀ x xn cc z, ReachS look t r x → look x = some xn → (cc, z) ∈ xn.liveAt t →
      (look z).isSome = true →
      ∀ x' xn' cc', ReachS look t r x' → look x' = some xn' → (cc', z) ∈ xn'.liveAt t →
        x = x' ∧ cc = cc' := by
  have hlink : ∀ x xn cc z, ReachS look t r x → look x = some xn → (cc, z) ∈ xn.liveAt t →
      (look z).isSome = true → TReach look t r x ∧ TLink look t x cc z := by
    intro x xn cc z hx hn hz hs
    have hxT : TReach look t r x := by
      rcases reachS_tReach look t r hv x hx with h | h
      · exact h
      · rw [hn] at h; cases h
    refine ⟨hxT, xn, hn, hz, fun hl => Decidable.byContradiction (fun hne => ?_)⟩
    have h0 := hv x xn hxT hn hl cc z hz hne
    rw [h0] at hs; cases hs
  intro x xn cc z hx hn hz hs x' xn' cc' hx' hn' hz'
  obtain ⟨h1, l1⟩ := hlink x xn cc z hx hn hz hs
  obtain ⟨h2, l2⟩ := hlink x' xn' cc' z hx' hn' hz' hs
  exact hT.oneLink x cc x' cc' z h1 h2 l1 l2

/-- The time split rule (`writerWP_put_timeSplit_key`) with the writer's tree
and `ValueLinksOK` for TREE. -/
theorem writerWP_put_timeSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none ∧ valueOf base (w.next + 2) = none ∧
      knodeOf c.p base (w.next + 2) = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (n.lastVersion c.i).size ≤ c.p.splitAbove ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n → n.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hv : ValueLinksOK (wNode c.p base w) c.i w.top.rootKey)
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z ≠ w.next ∧ z ≠ w.next + 2) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  apply writerWP_put_timeSplit_key c base hvc pre cv h rk w
    (htreeK := treeK_of_treeOK _ _ _ hT hv)
  all_goals assumption

/-- `OpGetOKUnder` for a state that has the writer's tree. -/
def OpGetTreeOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- `OpGetOKUnder` with P's tree before the transaction as a run premise, from
`OpGetTreeOK` and the writer's tree kept by each operation. -/
theorem opGetOKUnder_of_tree (p : Params) (R : Struct BVal → Time → Prop)
    (hg : OpGetTreeOK p R) (ho : OpTreeOK p) :
    OpGetOKUnder p (fun P t => R P t ∧ TreeAt p P t) := by
  intro ts tx hw hR z top hz htop pre op post hsplit r w hpre
  exact hg ts tx hw hR.1 z top hz htop pre op post hsplit r w hpre
    (writerTreeOK_reached p ho ts tx hw z top hz htop hR.2 pre (op :: post) hsplit r w hpre)

/-- `OpGetOKUnder` from `OpGetTreeOK`, the writer's tree kept by each operation,
and the lift (`writerTreeOK_between`). -/
theorem opGetOKUnder_of_tree_lift (p : Params) (R : Struct BVal → Time → Prop)
    (hg : OpGetTreeOK p R) (ho : OpTreeOK p) (hl : CommitLiftOK p) : OpGetOKUnder p R := by
  intro ts tx hw hR z top hz htop pre op post hsplit r w hpre
  exact hg ts tx hw hR z top hz htop pre op post hsplit r w hpre
    (writerTreeOK_between p ho hl ts tx hw z top hz htop pre (op :: post) hsplit r w hpre)

end SIS.Tree
