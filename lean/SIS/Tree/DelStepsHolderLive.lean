/-
cost's `UpHolderOK` at the upward loop's end from its first part (bergdb
024-12): the times of the cached nodes come from the books (`putInvG_of_book`),
and a chain node taken back is the transaction's (`ChainFateW`, the node's books
at the descent's end, `blank_of_firstTime`). Named stays only that no node not
taken back holds a taken-back node (`UpHolderLiveRunOK`).
-/
import SIS.Tree.DelStepsLive
import SIS.Tree.HeightsUpCascR

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Named input (the take-back's; cost's `UpHolderOK`'s first part, checked on
runs at 2529 loop ends): at the upward loop's end no node not taken back holds,
by a live klong now or before the transaction, a node taken back. -/
def UpHolderLiveRunOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat)
    (w2 : W) (S : KNode),
    PutInv c base w → ReadsAs c.p base w w3 →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) → stop < depth →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    ∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
      ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) → w2.taken.contains z = false

/-- `UpHolderOK` from its first part: the times from the books at the loop's
end, the chain nodes taken back the transaction's by the kinds' books at the
descent's end. -/
theorem upHolderOK_of_live (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (top0 : Top)
    (H : NodeId → Nat → Prop) (w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode)
    (depth stop : Nat) (w2 v : W) (S : KNode)
    (hB : PutBase c base B) (hJ3H : KdHtJ c B top0 KO BK H w3)
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hLE : UpLoopEnd c MB X Nn depth stop w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hbv : PutBook c B top0 v)
    (hA : ∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
      ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) → w2.taken.contains z = false) :
    UpHolderOK c BK X depth stop w2 := by
  refine ⟨hA, ?_, ?_⟩
  · intro y n hy ht s hs
    have hG := putInvG_of_book c base B top0 v hB hbv
    have hwv : wNode c.p base v = wNode c.p base w2 := by
      rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
    have hyn : wNode c.p base w2 y = some n := by
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hy]
    rw [← hwv] at hyn
    exact hG.times y n hyn s hs
  · intro k h1 h2 htk
    have hfw := hLE.2.2.2.2.2.2.2.2.2.2.2.2 k h1 h2
    have hft : (Nn k).firstTime = some c.i := by
      rcases Classical.em ((Nn k).firstTime = some c.i) with h | hne
      · exact h
      · have := (hfw.2 hne).1
        rw [this] at htk
        cases htk
    have hgood := cacheGood_lookup B c w3 hJ3H.1.1.good (X k) (Nn k) (hlkX k h2)
    have hbk : Book BK c w3 := hJ3H.1.2.1
    have hmem : X k ∈ w3.nodes.map (·.1) := by
      obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp (hlkX k h2)
      rw [he]; simp
    rw [hbk.ids] at hmem
    obtain ⟨⟨x', g, h⟩, hq, hx'⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
    simp only at hx'
    subst hx'
    rcases hbk.tag (X k) g h hq with ⟨nd, hnd, hd, hl, _, _⟩ | ⟨hge, _, _⟩
    · exfalso
      have hbl := blank_of_firstTime B c (X k) (Nn k) hB.good.pos hgood (by simp [hft])
      have hb := hbl.1
      simp only [baseKlongs, hnd] at hb
      exact hB.good.nonempty (X k) nd hnd hd hl hb
    · exact hge

/-- `unlink` of a cached node keeps the heights' cache (a step towards the
upward loop keeping it, DelStepsGh.lean). -/
theorem writerWP_unlink_gh (x : NodeId) (c : Ctx) (v : W) (hx : ∃ xn, v.nodes.lookup x = some xn) :
    WriterWP (unlink x) c v (fun _ v' => v'.gh = v.gh) := by
  obtain ⟨xn, hxn⟩ := hx
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x xn c v hxn]
  split
  · simp only [putNode, writerWP_modify]
  · simp only [writerWP_pure]

/-- `takeBack` with the parent cached keeps the heights' cache (a step towards
the upward loop keeping it, DelStepsGh.lean). -/
theorem writerWP_takeBack_gh (x p : NodeId) (k : Nat) (c : Ctx) (v : W)
    (hp : ∃ pn, v.nodes.lookup p = some pn) :
    WriterWP (takeBack x p k) c v (fun _ v' => v'.gh = v.gh) := by
  obtain ⟨pn, hpn⟩ := hp
  unfold takeBack
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c v hpn]
  unfold replacedBy
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  split
  · refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    · unfold retarget takenBack note
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known p pn c v hpn]
      split
      · simp only [putNode, writerWP_modify]
      · simp only [writerWP_pure, writerWP_modify]
  · exact writerWP_throw _ _ _ _

end SIS.Tree
