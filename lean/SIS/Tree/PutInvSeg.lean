import SIS.Tree.PutInvRoot
import SIS.Tree.WriterTreePutInv
import SIS.Tree.GetSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a put into a segment root that is a leaf below the segment
leaf q of the key's segment before (bergdb 024-12, TP10; the rules of prover
latest's `writerWP_put_segLeaf_inv`): with room, the time split in place, the
time split (q's klong names the new node), the space split into a new segment
root and the space split in place (q's klong names the new root). No inner node
links the segment root, so the order at its leaf needs no bound; q, a leaf
child of an inner node itself, keeps its compare values. -/

/-! ## The rules -/

/-- The segment root L of a key's segment, a key node, is named by a segment
leaf x of the segment before, reachable, and by no other reachable node. -/
theorem segRoot_parent (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 : Nat) (rq L : NodeId)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L) :
    ∃ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ wNode c.p base w x = some xn ∧
      xn.leaf = true ∧ (k1, L) ∈ xn.liveAt c.i := by
  have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre0 _ rq ReachS.root hrq
  obtain ⟨x, xn, hx, hxn, hxl, hs⟩ := getEqR_some_visit _ _ k1 c.p.fuel rq L hL
  have hrx := eqVisits_reach _ _ _ k1 c.p.fuel rq x k1 hrrq hx
  cases hfd : xn.searchEq c.i k1 with
  | none => rw [hfd] at hs; cases hs
  | some fd =>
    rw [hfd] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    have hm := KNode.searchEq_mem xn c.i k1 fd (hI.wf x xn hxn) hfd
    rw [hs] at hm
    exact ⟨x, xn, hrx, hxn, hxl, hm⟩

/-- No reachable inner node links a segment root. -/
theorem segRoot_noInner (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 : Nat) (rq L : NodeId)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L) :
    ∀ q qn k1', ReachS (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      qn.leaf = false → (k1', L) ∈ qn.live → False := by
  intro q qn k1' hq hqn hql hk
  obtain ⟨x, xn, hrx, hxn, hxl, hm⟩ := segRoot_parent c base w hI pre0 k1 rq L hrq hL
  have hk' : (k1', L) ∈ qn.liveAt c.i := by
    rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk
  obtain ⟨he, _⟩ := htree_of_treeOK _ _ _ hI.tree q qn k1' L hq hqn hk' x xn k1 hrx hxn hm
  subst he
  rw [hqn] at hxn; cases hxn
  rw [hxl] at hql; cases hql

theorem segRoot_facts (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true) :
    segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L ∧
    eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] ∧
    (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false) ∧
    ReachS (wNode c.p base w) c.i w.top.rootKey rq := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  · obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hNL, hnl]
  · exact fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      _ _ q.1 q.2 ReachS.root hq)
  · exact segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre0 _ rq ReachS.root hrq

/-- A put into a segment root, a leaf with room, keeps `PutInv`. -/
theorem putInv_put_room_segRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hsegL, hevL, ht, _⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  rw [hkey'] at ht ⊢
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  refine writerWP_mono (writerWP_put_room_after c base hB.coherent (pre0 ++ [k1]) cv h L w hsegL ht
    (fun L' n' hL' hn' _ => by
      rw [hevL] at hL'
      have : L' = L := by simpa using hL'
      subst this; rw [hNL] at hn'; cases hn'; exact hroom)) ?_
  intro _ w' ⟨L', n', hL', hn', hnl', htk, htop, hL'', hother⟩
  rw [hevL] at hL'
  have : L' = L := by simpa using hL'
  subst this
  exact putInvT_room c base w w' hI cv L' n' hn' hnl' htk htop hL'' hother
    (fun q qn k1' hq hqn hql hk => absurd (segRoot_noInner c base w hI pre0 k1 rq L' hrq hL q qn
      k1' hq hqn hql hk) id)

end SIS.Tree
