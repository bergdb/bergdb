import SIS.Tree.TimeSplitMap
import SIS.Tree.WriterKlongOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Distinct compare values for any two physical key klongs. -/
def DifferentKeyCvs (a b : Klong) : Prop :=
  match a, b with
  | .key cv _, .key cv' _ => cv ≠ cv'
  | _, _ => True

/-- With no deletion bits and no repeated physical compare values, the
dead-klong counter is exactly zero. No time or tree premises are needed. -/
theorem KNode.deadCount_zero_of_distinct (n : KNode)
    (hb : n.lastBitmap = []) (hp : n.ks.Pairwise DifferentKeyCvs) : n.deadCount = 0 := by
  unfold KNode.deadCount
  rw [hb]
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro q hq
  rcases q with ⟨k, i⟩
  have hk := List.mem_zipIdx_iff_getElem?.mp hq
  cases k with
  | time t => simp
  | del bits => simp
  | key cv y =>
    intro hdead
    simp only [List.contains_nil, Bool.false_or] at hdead
    obtain ⟨later, hlater, heq⟩ := List.any_eq_true.mp hdead
    have hi := List.getElem?_eq_some_iff.mp hk
    obtain ⟨j, hj, hget⟩ := List.mem_drop_iff_getElem.mp hlater
    have hij : i < i + 1 + j := by omega
    have hrel := hp.rel_getElem_of_lt hi.1 (by omega : i + 1 + j < n.ks.length) hij
    rw [hi.2, hget] at hrel
    cases later with
    | time t => simp at heq
    | del bits => simp at heq
    | key cv' z =>
      change cv ≠ cv' at hrel
      have he : cv' = cv := by simpa only [beq_iff_eq] using heq
      exact hrel he.symm


theorem newKlongs_different (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) :
    (newKlongs t pairs).Pairwise DifferentKeyCvs := by
  apply List.pairwise_cons.mpr
  refine ⟨by intro k hk; trivial, ?_⟩
  have hp : pairs.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp hn
  exact (List.pairwise_map (f := fun q : Nat × NodeId => Klong.key q.1 q.2)).mpr hp

theorem KNode.newKlongs_deadCount (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).deadCount = 0 :=
  KNode.deadCount_zero_of_distinct _ (lastBitmapOf_newKlongs t pairs)
    (newKlongs_different t pairs hn)

/-- Normalization removes every dead physical key, for arbitrary input
klongs and arbitrary supplied deletion bits. -/
theorem KNode.lastVersionGivenDel_deadCount (n : KNode) (t : Time) (bits : List Nat) :
    (n.lastVersionGivenDel t bits).deadCount = 0 := by
  obtain ⟨pairs, hks, horder⟩ := n.lastVersionGivenDel_order t bits
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (horder.imp (by intro a b h; omega))
  change (⟨(n.lastVersionGivenDel t bits).leaf, (n.lastVersionGivenDel t bits).ks⟩ : KNode).deadCount = 0
  rw [hks]
  exact KNode.newKlongs_deadCount _ t pairs hn

theorem KNode.lastVersion_deadCount (n : KNode) (t : Time) :
    (n.lastVersion t).deadCount = 0 := n.lastVersionGivenDel_deadCount t _

/-- Time splitting overwrites existing compare values in place in its
normalized body. Even repeated inserts create no dead physical key. -/
theorem writerWP_replaceOrAdd_deadCount (leaf : Bool) (pairs ins : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd ⟨leaf, newKlongs c.i pairs⟩ ins) c w
      (fun out v => out.deadCount = 0 ∧ v = w) := by
  refine writerWP_mono (writerWP_replaceOrAdd_map leaf pairs ins hn c w) ?_
  rintro out v ⟨_, ⟨more, hks, hnd⟩, _, hv⟩
  refine ⟨?_, hv⟩
  change (⟨out.leaf, out.ks⟩ : KNode).deadCount = 0
  rw [hks]
  exact KNode.newKlongs_deadCount _ _ _ hnd

theorem writerWP_handleFullWith_time_new_deadCount (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat)
    (leaf : Bool) (pairs ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hn : (pairs.map Prod.fst).Nodup)
    (htime : compact = true ∨ (⟨leaf, newKlongs c.i pairs⟩ : KNode).size ≤ c.p.splitAbove) :
    WriterWP (handleFullWith up depth b.id ins ⟨leaf, newKlongs c.i pairs⟩ compact) c w
      (fun _ v => ∃ after, GuardHeld {b with node := after} v ∧ after.deadCount = 0) := by
  have hflag : (!compact && decide ((⟨leaf, newKlongs c.i pairs⟩ : KNode).size > c.p.splitAbove)) = false := by
    rcases htime with hc | hs
    · simp [hc]
    · simp [show ¬ (⟨leaf, newKlongs c.i pairs⟩ : KNode).size > c.p.splitAbove from by omega]
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  refine writerWP_mono (guard_ghOf b b.id c w hw) ?_
  intro gh v hv
  simp only [ht, BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [hflag, Bool.false_eq_true, Bool.not_true, note, ↓reduceIte]
    | kgUse b using (guard_getNode b _)
    | ((with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
       refine writerWP_mono (writerWP_replaceOrAdd_deadCount leaf pairs ins hn c _) ?_
       rintro out state ⟨hdead, heq⟩
       subst state)
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro result state hguard)
    | (exact ⟨_, hguard, hdead⟩)
    | exact writerWP_throw _ _ _ _
    | split

/-- The actual last-version constructor supplies the distinctness premise
of the time/compaction rule without any input-history assumptions. -/
theorem writerWP_handleFullWith_time_normalized_new_deadCount (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat)
    (n : KNode) (bits : List Nat) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (htime : compact = true ∨ (n.lastVersionGivenDel c.i bits).size ≤ c.p.splitAbove) :
    WriterWP (handleFullWith up depth b.id ins (n.lastVersionGivenDel c.i bits) compact) c w
      (fun _ v => ∃ after, GuardHeld {b with node := after} v ∧ after.deadCount = 0) := by
  obtain ⟨pairs, hks, horder⟩ := n.lastVersionGivenDel_order c.i bits
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (horder.imp (by intro a b h; omega))
  have he : n.lastVersionGivenDel c.i bits = ⟨n.leaf, newKlongs c.i pairs⟩ := by
    have hl : (n.lastVersionGivenDel c.i bits).leaf = n.leaf := rfl
    cases ho : n.lastVersionGivenDel c.i bits
    simp_all [newKlongs]
  rw [he] at htime ⊢
  exact writerWP_handleFullWith_time_new_deadCount b up depth n.leaf pairs ins compact c w hw ht hn htime

end SIS.Tree
