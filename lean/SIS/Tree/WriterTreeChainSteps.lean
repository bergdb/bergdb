/-
The writer's splits inside a cascade, with what the parent's `appendKlongs`
does left open (bergdb 024-22, `OpTreeOK`; for the chain of any kind,
`writerWP_appendKlongs_chainG`): a time split below any parent
(`writerWP_handleFullWith_time_up'`), a space split in place below an inner
parent (`_spaceInPlace_up`), a space split below a segment leaf
(`_segSpace_up`).
-/
import SIS.Tree.WriterTreeCascadeGen2
import SIS.Tree.GetRootSplit
import SIS.Tree.GetInPlace
import SIS.Tree.GetSegRoot
import SIS.Tree.GetSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `writerWP_handleFullWith_time_up` for a parent of either kind. -/
theorem writerWP_handleFullWith_time_up' (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true → (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
      (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) →
      ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, l.ks⟩)] → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) compact) c w (fun _ w' => Q w') := by
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl

/-- The writer's space split in place of x, made by the transaction, below an
inner parent q: x keeps the first half, the second at the next id, then q gets
the klong to it (`appendKlongs d'`, whatever it does). -/
theorem writerWP_handleFullWith_spaceInPlace_up (d' : Nat) (x q : NodeId) (n qn : KNode)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hxn : x < w.next)
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = x then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [((halves n.leaf c.i (n.lastVersion c.i) ins).2.2, w.next)]) c w1
          (fun _ w2 => Q w2)) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' => Q w') := by
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
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
          by_cases hz1 : z = w.next
          · subst hz1; simp [Ne.symm hx2]
          · by_cases hzx : z = x
            · subst hzx; simp [hz1]
            · simp only [hz1, hzx, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hz1]; rfl
        · intro _ w2 h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
          exact h

/-- The writer's space split of x, which existed before the transaction, below
a segment leaf q: the halves and a new segment root over them at the next three
ids, then q gets the klong k1 to the new root (`appendKlongs d'`, whatever it
does), then x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_segSpace_up (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else if z = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
          .key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 (w.next + 2)]⟩
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next + 2 + 2)]) c w1 (fun _ w2 =>
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
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    simp only [newKey, fresh, setMadeFor, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        refine (writerWP_klongAt (d' + 1) k1 x c _ ?_ _).mpr ?_
        · exact hpk
        refine writerWP_mono (hup _ ?_ rfl rfl rfl rfl rfl) ?_
        · intro z
          simp only [lookup_upsert, List.lookup_append]
          by_cases h3 : z = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : z = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : z = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup z with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup z) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl
        · intro _ w2 h
          simpa only [Bool.not_false, ↓reduceIte, writerWP_bind, putNode, writerWP_modify] using h

end SIS.Tree
