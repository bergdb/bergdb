import SIS.Tree.GetCascadeChain
import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit
import SIS.Tree.PutInvRun
import SIS.Tree.WriterTreeCollapseSeg
import SIS.Tree.GetChain
import SIS.Tree.GetSpaceSpace
import SIS.Tree.GetCascadeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a leaf below a cascade of any depth (bergdb 024-12, TP10): the
descent's last m + 1 nodes XX 0 (with room) to XX m (the leaf), each below the
one before by klong KK j; the writer's `appendKlongs` along them
and the leaf's put (`getFromR_leaf_change_seg`). -/

/-! ## The writer's splits of a delete's leaf with the parent's step left open -/

/-- Cost's `writerWP_handleFullWith_space_up` for a delete: nothing to insert and
the last version `last` given. -/
theorem writerWP_handleFullWith_space_up_last (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i last []).1
        else if z = w.next + 2 then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next),
          ((halves n.leaf c.i last []).2.2, w.next + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x []
      last false) c w (fun _ w' => Q w') := by
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
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

/-- The halves of a leaf's last version with nothing put, by the divider r:
the first half's keys are below r, the second half's from r, all of them pairs. -/
theorem halves_nil_links (t : Time) (pairs : List (Nat × NodeId)) (hps : CvSorted pairs)
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r) :
    (halves true t ⟨true, newKlongs t pairs⟩ []).2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).1.live → c < r.1 ∧ (c, z) ∈ pairs) ∧
    (∀ c z, (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).2.1.live →
      r.1 ≤ c ∧ (c, z) ∈ pairs) := by
  rw [halves_leaf_shape t pairs [] r hr]
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  refine ⟨trivial, ?_, ?_⟩
  · intro c z h
    have hm := newKlongs_live_mem true t _ c z h
    exact ⟨halves_left_lt_divider pairs _ hps r hr _ hm, List.mem_of_mem_take hm⟩
  · intro c z h
    have hm := newKlongs_live_mem true t _ c z h
    exact ⟨halves_right_ge_divider pairs _ hps r hr _ hm, List.mem_of_mem_drop hm⟩

/-- The space split in place of a delete's leaf x that the transaction made,
below the inner parent q, with the parent's step left open: x keeps the first
half of the last version `last`, a new node the second, and q gets the second's
klong. -/
theorem writerWP_handleFullWith_spaceInPlace_up_last (d' : Nat) (x q : NodeId) (n qn : KNode)
    (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hxn : x < w.next)
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = x then some (halves n.leaf c.i last []).1
        else if z = w.next then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [((halves n.leaf c.i last []).2.2, w.next)]) c w1
          (fun _ w2 => Q w2)) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x [] last false) c w
      (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hx2 : x ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_modify, writerWP_pure]
        refine writerWP_mono (hup _ ?_ rfl rfl rfl rfl rfl) ?_
        · intro z
          simp only [lookup_upsert, List.lookup_append]
          by_cases hzx : z = x
          · subst hzx
            simp [hx2]
          · by_cases hz1 : z = w.next
            · subst hz1
              simp [hzx]
            · simp only [hzx, hz1, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hz1]; rfl
        · intro _ w2 h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
          exact h

/-- TReach in a lookup whose links are among N's is TReach in N. -/
theorem tReach_of_sublinks (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hsub : ∀ x c y, TLink N' t x c y → TLink N t x c y) :
    ∀ y, TReach N' t r y → TReach N t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | link _ hl ih => exact TReach.link ih (hsub _ _ _ hl)

end SIS.Tree
