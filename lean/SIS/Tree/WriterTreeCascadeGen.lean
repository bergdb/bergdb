/-
Cascades of time splits of any depth keep the writer's tree (bergdb 024-22,
`OpTreeOK`). The writer's time split of a node below an inner parent, with
what the parent's `appendKlongs` does left open; the tree before the klong to the
new node is put in the parent, as the tree with the node's klongs put
(`treeOK_up_time`).
-/
import SIS.Tree.WriterTreeDepth

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem wNode_upsert_updN (p : Params) (base : View BVal) (w w' : W) (x : NodeId) (m : KNode)
    (hn : w'.nodes = upsert w.nodes x m) (ht : w'.taken = w.taken) (hx : w.taken.contains x = false) :
    wNode p base w' = updN (wNode p base w) x m := by
  funext z
  unfold wNode updN
  rw [ht, hn, lookup_upsert]
  by_cases hz : z = x
  · subst hz; simp only [hx, Bool.false_eq_true, ↓reduceIte]
  · simp only [hz, ↓reduceIte]

theorem wNode_append_updN (p : Params) (base : View BVal) (w w' : W) (m : KNode)
    (hn : w'.nodes = w.nodes ++ [(w.next, m)]) (ht : w'.taken = w.taken)
    (hfree : w.nodes.lookup w.next = none) (htk : w.taken.contains w.next = false) :
    wNode p base w' = updN (wNode p base w) w.next m := by
  funext z
  unfold wNode updN
  rw [ht, hn]
  by_cases hz : z = w.next
  · subst hz
    simp only [htk, Bool.false_eq_true, ↓reduceIte, List.lookup_append, hfree]
    simp [List.lookup]
  · simp only [hz, ↓reduceIte, List.lookup_append]
    cases h : w.nodes.lookup z with
    | some _ => rfl
    | none =>
      have hb : (z == w.next) = false := by simpa using hz
      simp [List.lookup, hb]

/-- The writer's space split of x, which existed before the transaction, with
klongs ins, below an inner parent q: the halves at the next two ids, then q
gets the klongs to them (`appendKlongs d'`, whatever it does), then x keeps
its klongs before the transaction. -/
theorem writerWP_handleFullWith_space_up (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next),
          ((halves n.leaf c.i (n.lastVersion c.i) ins).2.2, w.next + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (hup _ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      rotate_left 6
      · intro _ w2 h
        simpa only [writerWP_bind, putNode, writerWP_modify] using h
      · intro z
        simp only [lookup_upsert, List.lookup_append]
        by_cases hz2 : z = w.next + 2
        · have hz1 : z ≠ w.next := by omega
          simp [hz2]
        · simp only [hz2, ↓reduceIte]
          by_cases hz1 : z = w.next
          · simp [hz1]
          · simp only [hz1, ↓reduceIte]
            cases h : w.nodes.lookup z with
            | some m => rfl
            | none =>
              have hb1 : (z == w.next) = false := by simpa using hz1
              have hb2 : (z == w.next + 2) = false := by simpa using hz2
              simp [List.lookup, hb1, hb2]
      all_goals rfl)

end SIS.Tree
