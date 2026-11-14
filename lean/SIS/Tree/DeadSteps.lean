/-
The writer's writes keep the dead klongs' bound (bergdb 024-12, pieces for
`QDead` of (4)): a node put in place (`putNode`) or made (`newKey`) at or below
theta keeps every node the writer reads at or below theta (`WDeadN`). With
`writerWP_handleFull_lastDead` and `writerWP_handleFull_rootDead` for a full
node's split and cascade, these are what a delete's steps write: the bitmap
(`writerWP_appendDeleteKlong_dead`) and `mergeParent` put a node only when
`deadOver` lets it through, a merge's new nodes hold none
(`mergeKlongs_deadCount`).
-/
import SIS.Tree.DeadCases

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem wDeadN_updN (p : Params) (N : NodeId → Option KNode) (x : NodeId) (m : KNode)
    (h : WDeadN p N) (hm : p.theta ≠ 0 → m.deadCount ≤ p.theta) : WDeadN p (updN N x m) := by
  intro h0 z n hz
  by_cases hzx : z = x
  · subst hzx
    rw [updN_self] at hz
    cases hz
    exact hm h0
  · rw [updN_ne _ _ _ _ hzx] at hz
    exact h h0 z n hz

/-- A node put in place at or below theta keeps the bound. -/
theorem writerWP_putNode_dead (c : Ctx) (base : View BVal) (x : NodeId) (m : KNode) (w : W)
    (hx : w.taken.contains x = false) (hW : WDeadN c.p (wNode c.p base w))
    (hm : c.p.theta ≠ 0 → m.deadCount ≤ c.p.theta) :
    WriterWP (putNode x m) c w (fun _ w' => WDeadN c.p (wNode c.p base w')) := by
  unfold putNode
  rw [writerWP_modify]
  have hN := wNode_upsert_updN c.p base w { w with nodes := upsert w.nodes x m } x m rfl rfl hx
  show WDeadN c.p (wNode c.p base { w with nodes := upsert w.nodes x m })
  rw [hN]
  exact wDeadN_updN c.p _ x m hW hm

/-- A node put in place that `deadOver` lets through keeps the bound. -/
theorem writerWP_putNode_deadOver (c : Ctx) (base : View BVal) (x : NodeId) (m : KNode) (w : W)
    (hx : w.taken.contains x = false) (hW : WDeadN c.p (wNode c.p base w))
    (hd : deadOver c.p m = false) :
    WriterWP (putNode x m) c w (fun _ w' => WDeadN c.p (wNode c.p base w')) :=
  writerWP_putNode_dead c base x m w hx hW (fun h0 => deadOver_false c.p m hd h0)

/-- A node made at or below theta keeps the bound. -/
theorem writerWP_newKey_dead (c : Ctx) (base : View BVal) (g h : Nat) (leaf : Bool) (ks : List Klong)
    (w : W) (hfree : w.nodes.lookup w.next = none) (htk : w.taken.contains w.next = false)
    (hW : WDeadN c.p (wNode c.p base w))
    (hm : c.p.theta ≠ 0 → (⟨leaf, ks⟩ : KNode).deadCount ≤ c.p.theta) :
    WriterWP (newKey g h leaf ks) c w (fun _ w' => WDeadN c.p (wNode c.p base w')) := by
  have key : ∀ w' : W, w'.nodes = w.nodes ++ [(w.next, (⟨leaf, ks⟩ : KNode))] → w'.taken = w.taken →
      WDeadN c.p (wNode c.p base w') := by
    intro w' h1 h2
    rw [wNode_append_updN c.p base w w' ⟨leaf, ks⟩ h1 h2 hfree htk]
    exact wDeadN_updN c.p _ _ _ hW hm
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  split <;>
  · simp only [writerWP_modify, writerWP_pure, writerWP_bind]
    first
      | exact key _ rfl rfl
      | (simp only [writerWP_modify, writerWP_pure]; exact key _ rfl rfl)

/-- `WDeadN` depends on the overlay's nodes and the taken ids only. -/
theorem wDeadN_of_same (c : Ctx) (base : View BVal) (w w' : W) (hn : w'.nodes = w.nodes)
    (ht : w'.taken = w.taken) (h : WDeadN c.p (wNode c.p base w)) : WDeadN c.p (wNode c.p base w') := by
  have : wNode c.p base w' = wNode c.p base w := by
    funext z; simp only [wNode, hn, ht]
  rw [this]; exact h

/-- The bitmap of a delete (`appendDeleteKlong`) keeps the bound: it puts a node
only when `deadOver` lets it through, and a full node goes to `handleFull`
(`hfull`, the split and its cascade: `writerWP_handleFull_lastDead`,
`writerWP_handleFull_rootDead`). -/
theorem writerWP_appendDeleteKlong_dead (x : NodeId) (depth cv : Nat) (c : Ctx) (base : View BVal)
    (w : W) (n : KNode) (hlk : w.nodes.lookup x = some n) (htk : w.taken.contains x = false)
    (hW : WDeadN c.p (wNode c.p base w))
    (hfull : ∀ (last : KNode) (compact : Bool) (w0 : W), w0.nodes = w.nodes → w0.taken = w.taken →
      WriterWP (handleFull depth x last compact) c w0 (fun _ w' => WDeadN c.p (wNode c.p base w'))) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => WDeadN c.p (wNode c.p base w')) := by
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  repeat' split
  all_goals first
    | exact writerWP_throw _ _ _ _
    | (simp only [writerWP_pure]; exact hW)
    | (simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
       exact writerWP_mono (hfull _ _ _ rfl rfl) (fun _ _ h => h))
    | (simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
       exact writerWP_mono (writerWP_putNode_dead c base x _ _ htk (wDeadN_of_same c base w _ rfl rfl hW)
         (fun h0 => deadOver_false c.p _ (by simp_all) h0)) (fun _ _ h => h))

end SIS.Tree
