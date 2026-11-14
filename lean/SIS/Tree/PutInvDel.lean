import SIS.Tree.PutInvNewSeg
import SIS.Tree.WriterTreePut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the delete rules that change at most one node by shrinking
its live klongs (bergdb 024-12, TP10; prover latest's `writerWP_del_noop_seg`,
`writerWP_del_bitmap_seg`): a delete of a key without a value changes nothing
the state reads (`putInv_del_noop_seg`); a delete by a bitmap in a segment leaf
that keeps a live klong, the merges off, takes live klongs of one node only
(`putInv_del_bitmap_seg`). The parts about the tree after any change that only
takes live klongs of one node: `putInvT_shrink`. -/

/-- A state that reads as w meets the parts about the tree that w meets. -/
theorem putInvT_of_readsAs (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (hr : ReadsAs c.p base w w') : PutInvT c base w' := by
  obtain ⟨hN, htop, htk, _, _⟩ := hr
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hN, htop] at hx
    rw [htk]
    exact hI.untaken x hx
  · intro q qn L n k1 hq hqn hql hn hnl hk
    rw [hN, htop] at hq
    rw [hN] at hqn hn
    exact hI.order q qn L n k1 hq hqn hql hn hnl hk

/-- The parts about the tree after a change of one node x that only takes live
klongs of it, of the same kind. -/
theorem putInvT_shrink (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (x : NodeId) (n n' : KNode) (hn : wNode c.p base w x = some n) (hl : n'.leaf = n.leaf)
    (ht' : ∀ s, Klong.time s ∈ n'.ks → s ≤ c.i)
    (hsub : ∀ c' z, (c', z) ∈ n'.live → (c', z) ∈ n.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hx' : wNode c.p base w' x = some n')
    (hother : ∀ y, y ≠ x → wNode c.p base w' y = wNode c.p base w y) :
    PutInvT c base w' := by
  have hnt := hI.times x n hn
  have hsubAt : ∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z h
    rw [KNode.liveAt_of_times _ c.i ht'] at h
    rw [KNode.liveAt_of_times _ c.i hnt]
    exact hsub c' z h
  have hsub' : ∀ y, ReachS (wNode c.p base w') c.i w'.top.rootKey y →
      ReachS (wNode c.p base w) c.i w.top.rootKey y := by
    rw [htop]
    apply reachS_closed _ _ _ (fun y => ReachS (wNode c.p base w) c.i w.top.rootKey y) ReachS.root
    intro y yn cc z hy hyn hz
    by_cases hyx : y = x
    · subst hyx
      rw [hx'] at hyn; cases hyn
      exact ReachS.step y n cc z hy hn (hsubAt cc z hz)
    · rw [hother y hyx] at hyn
      exact ReachS.step y yn cc z hy hyn hz
  refine ⟨?_, ?_⟩
  · intro y hy; rw [htk]; exact hI.untaken y (hsub' y hy)
  · intro q qn L m k1 hq hqn hql hm hml hk
    have hq' := hsub' q hq
    by_cases hqx : q = x
    · subst hqx
      rw [hx'] at hqn; cases hqn
      have hk' := hsub k1 L hk
      have hql' : n.leaf = false := by rw [← hl]; exact hql
      by_cases hLx : L = q
      · subst hLx; rw [hx'] at hm; cases hm; rw [hql] at hml; cases hml
      rw [hother L hLx] at hm
      have hold := hI.order q n L m k1 hq' hn hql' hm hml hk'
      intro c' z hz
      exact ⟨(hold c' z hz).1, fun c'' z'' hz'' hlt => (hold c' z hz).2 c'' z'' (hsub c'' z'' hz'') hlt⟩
    · rw [hother q hqx] at hqn
      by_cases hLx : L = x
      · subst hLx
        rw [hx'] at hm; cases hm
        have hold := hI.order q qn L n k1 hq' hqn hql hn (by rw [← hl]; exact hml) hk
        exact fun c' z hz => hold c' z (hsub c' z hz)
      · rw [hother L hLx] at hm
        exact hI.order q qn L m k1 hq' hqn hql hm hml hk

/-- A delete of a key without a value keeps `PutInv` (it changes nothing that
the state reads). -/
theorem putInv_del_noop_seg (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hB.coherent (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hB.coherent c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnoop := hleaf L n hvisL hn hnl
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnoopb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by
    rw [hnoop]; simp
  simp only [hnoopb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
  exact putInvT_of_readsAs c base w w3 hI hr03

end SIS.Tree
