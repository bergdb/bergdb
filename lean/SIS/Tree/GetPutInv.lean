import SIS.Tree.GetLeafBelow

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The invariant of the writer's state that the put rules take (bergdb 024-12,
TP10; `OpGetOK`): the writer's tree (`TreeOK`, cost's `WriterTreeOK`), the
klongs of every key node well formed and of no later time, the ids below the
next one and the next ones fresh in P, the links of the reachable nodes to ids
below the next one, no reachable node taken back, no key node a value, and the
search tree's order below every reachable inner node (`PutInv`). With it, a put
that splits nothing above the key's leaf changes the reading by itself alone:
into a space whose root is a leaf (`writerWP_put_leafRoot_inv`), or into a
leaf below inner nodes with room for two klongs (`writerWP_put_leafBelow_inv`). -/

/-- The search tree's order at an inner node q: the compare values of q's leaf
child L lie between q's klong k1 to L and q's next klong. -/
def LeafOrderAt (q : KNode) (k1 : Nat) (n : KNode) : Prop :=
  ∀ c' z, (c', z) ∈ n.live → k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ q.live → k1 < c'' → c' < c''

structure PutInv (c : Ctx) (base : View BVal) (w : W) : Prop where
  tree : TreeOK (wNode c.p base w) c.i w.top.rootKey
  wf : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true
  times : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i
  ids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
    (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
    (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next
  fresh : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none
  links : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
    wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next
  untaken : ∀ x, ReachS (wNode c.p base w) c.i w.top.rootKey x → w.taken.contains x = false
  keyNoValue : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none
  order : ∀ q qn L n k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
    wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
    n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n

/-- A node of a descent's visits other than its start is named by a live klong
of a node visited before it. -/
theorem eqVisits_parent (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x L : NodeId), (L, cv) ∈ eqVisits N t cv f x → L ≠ x →
      ∃ q qn c, (q, cv) ∈ eqVisits N t cv f x ∧ N q = some qn ∧ (c, L) ∈ qn.liveAt t := by
  intro f
  induction f with
  | zero => intro x L h; simp [eqVisits] at h
  | succ f ih =>
    intro x L hL hLx
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true] at hL
    rcases hL with hL | hL
    · exact absurd hL hLx
    cases hx : N x with
    | none => rw [hx] at hL; cases hL
    | some n =>
      rw [hx] at hL
      simp only at hL
      split at hL
      · cases hL
      · cases hs : n.searchLte t cv with
        | none => rw [hs] at hL; cases hL
        | some fd =>
          rw [hs] at hL
          by_cases hfy : L = fd.y
          · subst hfy
            exact ⟨x, n, fd.c, by simp [eqVisits], hx, KNode.searchLte_mem n t cv fd hs⟩
          · obtain ⟨q, qn, c, hq, hqn, hlink⟩ := ih fd.y L hL hfy
            refine ⟨q, qn, c, ?_, hqn, hlink⟩
            simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true, hx]
            right
            simp only [show (n.leaf = true) = False from by
              rename_i hnl; simpa using hnl, ↓reduceIte]
            rw [hs]
            exact hq

/-- `writerWP_put_leafRoot` under `PutInv`. -/
theorem writerWP_put_leafRoot_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode) (hI : PutInv c base w) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf [cv] = true)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h)
        else wGet c.p c.i base w key') :=
  writerWP_put_leafRoot c base hvc cv h w n hsa hkey hroot hnl (hI.untaken _ ReachS.root)
    (hI.wf _ _ hroot) (hI.times _ _ hroot) hI.ids (hI.fresh _ (Nat.le_refl _)).1
    (fun key' x _ hkey' h1 h2 _ _ =>
      visits_unique_of_tree _ _ _ _ hI.tree hI.wf cv hkey key' x hkey' h1 h2)
    (fun x xn _ hn => hI.wf x xn hn)
    (fun x xn cc z hx hn hz => ⟨hI.links x xn cc z hx hn hz,
      fun he => hI.tree.rootFree x cc (reachS_tReach _ _ _ x hx) ⟨xn, hn, he ▸ hz⟩⟩)

/-- `writerWP_put_leafBelow` under `PutInv`: a put of a key whose prefix is
there, into a leaf below inner nodes on the key's path with room for two
klongs. -/
theorem writerWP_put_leafBelow_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hI : PutInv c base w)
    (hsa : 1 ≤ c.p.splitAbove) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have hvisR : ∀ x c', (x, c') ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      ReachS (wNode c.p base w) c.i w.top.rootKey x :=
    fun x c' hx => eqVisits_reach _ _ _ cv c.p.fuel rk x c' hrrk hx
  refine writerWP_put_leafBelow c base hvc pre cv h rk w hsa hkey hrk
    (fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      (pre ++ [cv]) _ q.1 q.2 ReachS.root hq))
    hI.ids hI.fresh hinner ?_
    (fun q qn hq hqn hql => by
      obtain ⟨a2, a3, a4⟩ := hparent q qn hq hqn hql
      exact ⟨hI.times q qn hqn, a2, a3, a4⟩)
    ?_
    (fun key' x _ hkey' h1 h2 _ _ =>
      visits_unique_seg_of_tree _ _ _ _ hI.tree hI.wf pre cv rk hkey hrk key' x hkey' h1 h2)
    (fun x xn _ hn => hI.wf x xn hn)
    (fun x xn cc z hx hn hz _ x' xn' cc' hx' hn' hz' =>
      htree_of_treeOK _ _ _ hI.tree x xn cc z hx hn hz x' xn' cc' hx' hn' hz')
    hI.links
  · intro L n hL hn hnl
    refine ⟨hI.wf L n hn, hI.times L n hn, hI.keyNoValue L n hn, ?_⟩
    intro hLr
    -- L is reached by a link from rk's tree: rk is inner, so L ≠ rk
    have hLrk : L ≠ rk := by
      intro he; subst he; rw [hinner n hn] at hnl; cases hnl
    obtain ⟨q, qn, c', hq, hqn, hlink⟩ := eqVisits_parent _ _ cv c.p.fuel rk L hL hLrk
    exact hI.tree.rootFree q c' (reachS_tReach _ _ _ q (hvisR q cv hq)) ⟨qn, hqn, hLr ▸ hlink⟩
  · intro q qn L n k1 hq hqn hql hn hnl hk1
    exact hI.order q qn L n k1 (hvisR q cv hq) hqn hql hn hnl hk1

end SIS.Tree
