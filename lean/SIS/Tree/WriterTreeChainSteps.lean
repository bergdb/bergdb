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

/-- The writer's time split of a node that existed before the transaction, with
klongs ins and its last version, below a parent of either kind. -/
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

/-! ## The splits that end a cascade -/

/-- The writer's time split in place of x, made by the transaction, below a
parent q that the writer has: x holds its last version with ins. -/
theorem writerWP_handleFullWith_timeInPlace_term (up : NodeId → List (Nat × NodeId) → M Unit)
    (d' : Nat) (x q : NodeId) (n qn : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hpq : (w.path[d']?).map (·.2) = some q) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up (d' + 1) x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩) := by
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases compact with
    | true =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    | false =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

set_option linter.unusedSimpArgs false in
/-- The writer's time split of the space root x, which existed before the
transaction: the new node at the next id holds the last version with ins and
is the new space root; x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_rootTime_term (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hxn : x < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
        w.next + 2 ≤ w'.next ∧
        ∀ z, w'.nodes.lookup z =
          if z = x then some (n.toPrev (c.i - 1))
          else if z = w.next then some ⟨n.leaf, l.ks⟩ else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hx1 : x ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
    rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst w1
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known x n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
          all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
          show (upsert _ x _).lookup z = _
          rw [lookup_upsert]
          by_cases hzx : z = x
          · simp [hzx]
          · simp only [hzx, ↓reduceIte, List.lookup_append]
            by_cases hzy : z = w.next
            · subst hzy; rw [hny]; simp [List.lookup]
            · simp only [hzy, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hzy]; rfl

set_option linter.unusedSimpArgs false in
/-- The writer's space split of the space root x, which existed before the
transaction: the halves and a new space root over them at the next three ids;
x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_rootSpace_term (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hxn : x < w.next) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) false) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w.next + 2 + 2 + 2 ≤ w'.next ∧
      ∀ z, w'.nodes.lookup z =
        if z = x then some (n.toPrev (c.i - 1))
        else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else if z = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
          .key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 (w.next + 2)]⟩
        else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hx1 : x ≠ w.next := by omega
  have hx2 : x ≠ w.next + 2 := by omega
  have hx3 : x ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known x n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hx1, hx2, hx3, ↓reduceIte, hlk]
          rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
        all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
        simp only [lookup_upsert, List.lookup_append]
        by_cases hzx : z = x
        · subst hzx; simp
        · simp only [hzx, ↓reduceIte]
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

set_option linter.unusedSimpArgs false in
/-- The writer's space split in place of the space root x, made by the
transaction: x keeps the first half, the second at the next id, and a new
space root over them at the id after. -/
theorem writerWP_handleFullWith_rootSpaceInPlace_term (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hxn : x < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) false) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w.next + 2 + 2 ≤ w'.next ∧
      ∀ z, w'.nodes.lookup z =
        if z = x then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else if z = w.next + 2 then some ⟨false, [.time c.i, .key 0 x,
          .key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 w.next]⟩
        else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hx1 : x ≠ w.next := by omega
  have hx2 : x ≠ w.next + 2 := by omega
  simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
            all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
            simp only [lookup_upsert, List.lookup_append]
            by_cases hzx : z = x
            · subst hzx; simp [hx1, hx2]
            · simp only [hzx, ↓reduceIte]
              by_cases h1 : z = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                by_cases h2 : z = w.next + 2
                · subst h2
                  rw [show w.nodes.lookup (w.next + 2) = none from hny]
                  have hb : (w.next + 2 == w.next) = false := by simp
                  simp [List.lookup, hb]
                · simp only [h2, ↓reduceIte]
                  cases h : w.nodes.lookup z with
                  | some m => rfl
                  | none =>
                    show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                      ([(w.next + 2, _)].lookup z)) = none
                    rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl

set_option linter.unusedSimpArgs false in
/-- The writer's space split in place of x, made by the transaction, below a
segment leaf q: x keeps the first half, the second at the next id, a new
segment root over them at the id after, and q's klong of the transaction to x
names the new root in place. -/
theorem writerWP_handleFullWith_segSpaceInPlace_term (d' : Nat) (x q : NodeId) (n qn : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hqx : q ≠ x) (hql : qn.leaf = true) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (hxn : x < w.next) (hqn : q < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' =>
      ∃ j, qn.linkIndex x k1 = some j ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
        w.next + 2 + 2 ≤ w'.next ∧
        ∀ z, w'.nodes.lookup z =
          if z = x then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
          else if z = q then some (qn.repoint j (w.next + 2))
          else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
          else if z = w.next + 2 then some ⟨false, [.time c.i, .key 0 x,
            .key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 w.next]⟩
          else w.nodes.lookup z) := by
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
    have hq1 : q ≠ w.next := by omega
    have hq2 : q ≠ w.next + 2 := by omega
    have hx1 : x ≠ w.next := by omega
    have hx2 : x ≠ w.next + 2 := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
            refine (writerWP_klongAt (d' + 1) k1 x c _ ?_ _).mpr ?_
            · exact hpk
            refine (writerWP_getNode_known q qn c _ ?_ _).mpr ?_
            · simp only [lookup_upsert, List.lookup_append, hq1, hq2, hqx, ↓reduceIte, hlq]
              rfl
            split
            · rename_i j hj
              split
              · simp only [writerWP_bind]
                exact writerWP_throw _ _ _ _
              · simp only [writerWP_bind, writerWP_modify, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, writerWP_pure]
                refine ⟨j, hj, ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
                all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
                simp only [lookup_upsert, List.lookup_append]
                by_cases hzx : z = x
                · subst hzx; simp [hqx.symm, hx1, hx2]
                · simp only [hzx, ↓reduceIte]
                  by_cases hzq : z = q
                  · simp [hzq]
                  · simp only [hzq, ↓reduceIte]
                    by_cases h1 : z = w.next
                    · subst h1; simp
                    · simp only [h1, ↓reduceIte]
                      by_cases h2 : z = w.next + 2
                      · subst h2
                        rw [hny]
                        have hb : (w.next + 2 == w.next) = false := by simp
                        simp [List.lookup, hb]
                      · simp only [h2, ↓reduceIte]
                        cases h : w.nodes.lookup z with
                        | some m => rfl
                        | none =>
                          show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                            ([(w.next + 2, _)].lookup z)) = none
                          rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl
            · exact writerWP_throw _ _ _ _

/-- The writer's time split in place of the space root x, made by the
transaction: x holds its last version with ins. -/
theorem writerWP_handleFullWith_timeInPlace_term0 (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew, parentAt, writerWP_bind, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true]
  cases compact with
  | true =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  | false =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
    refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

end SIS.Tree
