/-
The stop node's split from a state whose stop node has its bitmap (bergdb 025-04,
route (b), step 1): `handleFullWith` on node x reads of x's node only its first
time and its leaf flag, at the start, and its version before the transaction, at
the end; every klong it copies comes from the last version it is given. So every
successful run from the writer's state, x's node m, is a run from the state with
x's node n, to the same result and the same state, when m and n agree in those
three (`handleFull_swap`). The relational walk is root collapse's (`XWP`,
CollapseCommute.lean) until x is written; from there the two states are equal.
-/
import SIS.Tree.CollapseCommute
import SIS.Tree.WriterCacheUnique

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Upsert twice at one id -/

theorem upsert_upsert (ns : List (NodeId × KNode)) (x : NodeId) (a b : KNode) :
    upsert (upsert ns x a) x b = upsert ns x b := by
  cases hx : ns.any (fun q => q.1 == x) with
  | true =>
    rw [upsert_of_any ns x a hx, upsert_of_any _ x b (by rw [any_map_set]; exact hx),
      upsert_of_any ns x b hx, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp]
    by_cases h1 : q.1 = x
    · simp [h1]
    · simp [h1]
  | false =>
    rw [upsert_of_not_any ns x a hx, upsert_of_any _ x b (by simp [List.any_append]),
      upsert_of_not_any ns x b hx, List.map_append]
    have hm : ns.map (fun q => if q.1 == x then (x, b) else q) = ns := by
      conv => rhs; rw [← List.map_id ns]
      apply List.map_congr_left
      intro q hq
      have hne : (q.1 == x) = false := by
        have := List.any_eq_false.mp hx q hq
        simpa using this
      simp [hne]
    rw [hm]
    simp

theorem setX_setX (x : NodeId) (a b : KNode) (w : W) : setX x b (setX x a w) = setX x b w := by
  simp only [setX, upsert_upsert]

theorem lookup_setX_self (x : NodeId) (m : KNode) (w : W) : (setX x m w).nodes.lookup x = some m := by
  simp only [setX, lookup_upsert, ↓reduceIte]

/-- With one overlay entry per id, setting x to the node it has changes nothing. -/
theorem setX_self (x : NodeId) (n : KNode) (w : W) (hU : CacheUnique w)
    (hx : w.nodes.lookup x = some n) : setX x n w = w := by
  have h : upsert w.nodes x n = w.nodes := by
    rw [upsert_of_any _ x n (any_of_lookup _ x n hx)]
    unfold CacheUnique at hU
    generalize w.nodes = ns at hU hx
    induction ns with
    | nil => rfl
    | cons q qs ih =>
      rcases q with ⟨a, b⟩
      simp only [List.map_cons, List.nodup_cons] at hU
      by_cases hax : a = x
      · subst hax
        have hb : b = n := by simpa [List.lookup] using hx
        subst hb
        have hqs : qs.map (fun q => if q.1 == a then (a, b) else q) = qs := by
          conv => rhs; rw [← List.map_id qs]
          apply List.map_congr_left
          intro q hq
          have hne : q.1 ≠ a := fun he => hU.1 (List.mem_map.mpr ⟨q, hq, he⟩)
          simp [hne]
        simp only [List.map_cons, beq_self_eq_true, ↓reduceIte]
        rw [hqs]
      · have hx' : qs.lookup x = some n := by
          have : (List.lookup x ((a, b) :: qs)) = qs.lookup x := by
            simp only [List.lookup, show (x == a) = false from by simpa using Ne.symm hax]
          rw [this] at hx; exact hx
        have hax' : (a == x) = false := by simpa using hax
        simp only [List.map_cons, hax', Bool.false_eq_true, ↓reduceIte]
        rw [ih hU.2 hx']
  cases w
  simp only [setX] at h ⊢
  rw [h]

/-! ## The relation: the same run, to the same state -/

/-- Every successful run of f from u with x's node set to m is a run from u, with
the same result and the same state. -/
def SWP {α : Type} (x : NodeId) (m : KNode) (f : M α) (c : Ctx) (u : W) : Prop :=
  ∀ r w2, f c (setX x m u) = .ok (r, w2) → f c u = .ok (r, w2)

section
variable {x : NodeId} {m nx : KNode}

/-- A step that keeps the walk's relation, then one that ends at the same state. -/
theorem swp_bind_xwp {α β : Type} {f : M α} {g : α → M β} {c : Ctx} {u : W}
    (h : XWP x m f c u (fun a u' => SWP x m (g a) c u')) : SWP x m (f >>= g) c u := by
  intro r w2 h2
  rw [run_bind_ok_iff] at h2 ⊢
  obtain ⟨a, w', h1, h3⟩ := h2
  obtain ⟨u', hu', rfl⟩ := h.1 a w' h1
  exact ⟨a, u', hu', h.2 a u' hu' r w2 h3⟩

theorem swp_ite {α : Type} (b : Prop) [Decidable b] {f g : M α} {c : Ctx} {u : W}
    (h1 : b → SWP x m f c u) (h2 : ¬ b → SWP x m g c u) : SWP x m (if b then f else g) c u := by
  by_cases hb : b
  · simpa [hb] using h1 hb
  · simpa [hb] using h2 hb

theorem swp_throw {α : Type} (e : String) {c : Ctx} {u : W} : SWP x m (throw e : M α) c u := by
  intro r w2 h; cases h

theorem swp_throw_bind {α β : Type} (e : String) (g : α → M β) {c : Ctx} {u : W} :
    SWP x m ((throw e : M α) >>= g) c u := by
  intro r w2 h; cases h

/-- Once x is written, the two states are equal. -/
theorem swp_putNode_bind {β : Type} (v : KNode) (g : Unit → M β) {c : Ctx} {u : W} :
    SWP x m (putNode x v >>= g) c u := by
  intro r w2 h
  rw [run_bind_ok _ _ c _ () _ (run_putNode x v c _)] at h
  rw [run_bind_ok _ _ c _ () _ (run_putNode x v c _)]
  have he : ({ setX x m u with nodes := upsert (setX x m u).nodes x v } : W) =
      { u with nodes := upsert u.nodes x v } := by
    simp only [setX, upsert_upsert]
  rw [he] at h
  exact h

/-- The split's last step for a node of before the transaction: x gets its
version before the transaction, which the two nodes share. -/
theorem swp_final (t : Time) {c : Ctx} {u : W} (hx : u.nodes.lookup x = some nx)
    (hp : m.toPrev t = nx.toPrev t) :
    SWP x m (getNode x >>= fun n => putNode x (n.toPrev t)) c u := by
  intro r w2 h
  rw [run_bind_ok _ _ c _ m _ (run_getNode_some x m c _ (lookup_setX_self x m u))] at h
  rw [run_bind_ok _ _ c _ nx _ (run_getNode_some x nx c _ hx)]
  rw [run_putNode] at h ⊢
  rw [hp] at h
  have he : ({ setX x m u with nodes := upsert (setX x m u).nodes x (nx.toPrev t) } : W) =
      { u with nodes := upsert u.nodes x (nx.toPrev t) } := by
    simp only [setX, upsert_upsert]
  rw [he] at h
  exact h

theorem RJ.lookup {path0 : List (Option Nat × NodeId)} {u : W} (hJ : RJ x nx path0 u) :
    u.nodes.lookup x = some nx := hJ.1

/-- The split's first step: x's node read, m from the writer's state and nx from u;
the rest reads of it only what the two share (`hg`). -/
theorem swp_getNode_bind {β : Type} (g : KNode → M β) {c : Ctx} {u : W}
    (hx : u.nodes.lookup x = some nx) (hg : g m = g nx) (h : SWP x m (g nx) c u) :
    SWP x m (getNode x >>= g) c u := by
  intro r w2 h2
  rw [run_bind_ok _ _ c _ m _ (run_getNode_some x m c _ (lookup_setX_self x m u)), hg] at h2
  rw [run_bind_ok _ _ c _ nx _ (run_getNode_some x nx c _ hx)]
  exact h _ _ h2

variable (path0 : List (Option Nat × NodeId))

/-- The segment and height of x itself: read from `gh`, which the relation does
not change; x's node is read and dropped. -/
theorem xwp_ghOf_x {c : Ctx} {u : W} {post : Nat × Nat → W → Prop} (hJ : RJ x nx path0 u)
    (h : ∀ r u', RJ x nx path0 u' → post r u') : XWP x m (ghOf x) c u post := by
  have h1 : getNode x c u = .ok (nx, u) := run_getNode_some x nx c u hJ.1
  have h2 : getNode x c (setX x m u) = .ok (m, setX x m u) :=
    run_getNode_some x m c _ (lookup_setX_self x m u)
  unfold ghOf
  cases hg : u.gh.lookup x with
  | none =>
    refine xwp_of_noOk ?_ ?_ <;> intro _ _ hh <;> revert hh
    · rw [run_bind_ok _ _ c _ _ _ h1, run_get_bind]; simp only [hg]; intro hh; cases hh
    · rw [run_bind_ok _ _ c _ _ _ h2, run_get_bind]; simp only [setX, hg]; intro hh; cases hh
  | some v =>
    refine xwp_of_run v u ?_ ?_ (h _ _ hJ)
    · rw [run_bind_ok _ _ c _ _ _ h1, run_get_bind]; simp only [hg]; rfl
    · rw [run_bind_ok _ _ c _ _ _ h2, run_get_bind]; simp only [setX, hg]; rfl

end

/-- One step of the walk to the same state. -/
macro "swpStep" : tactic => `(tactic| first
  | (refine swp_ite _ ?_ ?_ <;> intro _)
  | exact swp_throw _
  | exact swp_throw_bind _ _
  | (with_reducible exact swp_putNode_bind _ _)
  | (with_reducible exact swp_final _ (RJ.lookup (by assumption)) (by assumption))
  | (with_reducible refine swp_bind_xwp (xwp_read ?_))
  | (with_reducible refine swp_bind_xwp (xwp_getNode _ _ (by assumption) (by assumption) ?_); intro _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_ghOf_x _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_note _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_spaceSplits _ (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_newKey _ _ _ _ _ (by assumption) ?_); intro _ _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_setMadeFor _ _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_replacedBy _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_putNode _ _ _ (by assumption) (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_newSuperRoot _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_klongAt _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_replaceOrAdd _ _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine swp_bind_xwp (xwp_parentAt_zero _ (by assumption) ?_); intro _ _)
  | (with_reducible refine swp_bind_xwp (xwp_parentAt_succ' _ _ _ _ (by assumption) (by assumption) ?_))
  | (with_reducible exact swp_bind_xwp (xwp_parentAt_none _ _ (by assumption) (by assumption)))
  | (with_reducible refine swp_bind_xwp (xwp_pure _ ?_)))

section
variable {x : NodeId} {m nx : KNode} (path0 : List (Option Nat × NodeId))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- The split of x itself, at depth 0 (the space root). -/
theorem swp_handleFullWith_zero (up : NodeId → List (Nat × NodeId) → M Unit)
    (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool) {c : Ctx} {u : W}
    (hJ : RJ x nx path0 u) (hft : m.firstTime = nx.firstTime) (hleaf : m.leaf = nx.leaf)
    (hprev : nx.firstTime ≠ some c.i → m.toPrev (c.i - 1) = nx.toPrev (c.i - 1)) :
    SWP x m (handleFullWith up 0 x ins last compact) c u := by
  unfold handleFullWith
  simp only []
  refine swp_bind_xwp (xwp_read ?_)
  refine swp_getNode_bind _ hJ.1 (by rw [hft, hleaf]) ?_
  cases hnt : (nx.firstTime == some c.i)
  · have hp : m.toPrev (c.i - 1) = nx.toPrev (c.i - 1) := hprev (by simpa using hnt)
    simp only [hnt, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | swpStep
      | (simp only [Bool.false_eq_true, ↓reduceIte])
      | split)
  · simp only [hnt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | swpStep
      | (simp only [Bool.false_eq_true, ↓reduceIte])
      | split)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- The split of x itself at depth e + 1, its parent q on the key access path not
x, given the walk of `up` at q (the cascade above, which does not read x). -/
theorem swp_handleFullWith_succ (up : NodeId → List (Nat × NodeId) → M Unit) (e : Nat)
    (a : Option Nat) (q : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    {c : Ctx} {u : W} (hJ : RJ x nx path0 u) (hpe : path0[e]? = some (a, q)) (hq : q ≠ x)
    (hup : ∀ more u', RJ x nx path0 u' → XWP x m (up q more) c u' (fun _ v => RJ x nx path0 v))
    (hft : m.firstTime = nx.firstTime) (hleaf : m.leaf = nx.leaf)
    (hprev : nx.firstTime ≠ some c.i → m.toPrev (c.i - 1) = nx.toPrev (c.i - 1)) :
    SWP x m (handleFullWith up (e + 1) x ins last compact) c u := by
  unfold handleFullWith
  simp only []
  refine swp_bind_xwp (xwp_read ?_)
  refine swp_getNode_bind _ hJ.1 (by rw [hft, hleaf]) ?_
  cases hnt : (nx.firstTime == some c.i)
  · have hp : m.toPrev (c.i - 1) = nx.toPrev (c.i - 1) := hprev (by simpa using hnt)
    simp only [hnt, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | swpStep
      | (refine swp_bind_xwp (xwp_mono (hup _ _ (by assumption)) ?_); intro _ _ _)
      | (simp only [Bool.false_eq_true, ↓reduceIte])
      | split)
  · simp only [hnt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | swpStep
      | (refine swp_bind_xwp (xwp_mono (hup _ _ (by assumption)) ?_); intro _ _ _)
      | (simp only [Bool.false_eq_true, ↓reduceIte])
      | split)

/-- The split of x at depth e + 1 with no entry e on the key access path: it fails. -/
theorem swp_handleFullWith_none (up : NodeId → List (Nat × NodeId) → M Unit) (e : Nat)
    (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool) {c : Ctx} {u : W}
    (hJ : RJ x nx path0 u) (hpe : path0[e]? = none) (hft : m.firstTime = nx.firstTime)
    (hleaf : m.leaf = nx.leaf) :
    SWP x m (handleFullWith up (e + 1) x ins last compact) c u := by
  unfold handleFullWith
  simp only []
  refine swp_bind_xwp (xwp_read ?_)
  refine swp_getNode_bind _ hJ.1 (by rw [hft, hleaf]) ?_
  refine swp_bind_xwp (xwp_ghOf_x _ hJ ?_)
  intro _ u' hJ'
  exact swp_bind_xwp (xwp_parentAt_none _ _ hJ' hpe)

end

/-- The split of x reads of x's node only its first time, its leaf flag and its
version before the transaction: every successful run of `handleFull` on x from
the state with x's node set to m is a run from u, where x's node is n, with the
same result and the same state, if m and n agree in those three (the last needed only for a node of before the
transaction). -/
theorem handleFull_swap (x : NodeId) (n m : KNode) (depth : Nat) (last : KNode) (compact : Bool)
    (c : Ctx) (u : W) (hx : u.nodes.lookup x = some n) (hxn : x < u.next)
    (hpath : ∀ i e, i < depth → u.path[i]? = some e → e.2 ≠ x)
    (hft : m.firstTime = n.firstTime) (hleaf : m.leaf = n.leaf)
    (hprev : n.firstTime ≠ some c.i → m.toPrev (c.i - 1) = n.toPrev (c.i - 1)) :
    ∀ r w2, handleFull depth x last compact c (setX x m u) = .ok (r, w2) →
      handleFull depth x last compact c u = .ok (r, w2) := by
  have hJ : RJ x n u.path u := ⟨hx, hxn, rfl⟩
  unfold handleFull
  cases depth with
  | zero => exact swp_handleFullWith_zero u.path _ [] last compact hJ hft hleaf hprev
  | succ d =>
    cases hpe : u.path[d]? with
    | none => exact swp_handleFullWith_none u.path _ d [] last compact hJ hpe hft hleaf
    | some e =>
      rcases e with ⟨a, q⟩
      have hq : q ≠ x := hpath d (a, q) (Nat.lt_succ_self d) hpe
      exact swp_handleFullWith_succ u.path _ d a q [] last compact hJ hpe hq
        (fun more u' hJ' => xwp_appendKlongs u.path d q more c u' hJ' hq
          (fun i e hi he => hpath i e (by omega) he)) hft hleaf hprev

/-- The same at the space root, for any `up` (`writerWP_handleFull_root_j2U` states
the split with `rootUp`). -/
theorem handleFullWith_root_swap (up : NodeId → List (Nat × NodeId) → M Unit) (x : NodeId)
    (n m : KNode) (last : KNode) (compact : Bool)
    (c : Ctx) (u : W) (hx : u.nodes.lookup x = some n) (hxn : x < u.next)
    (hft : m.firstTime = n.firstTime) (hleaf : m.leaf = n.leaf)
    (hprev : n.firstTime ≠ some c.i → m.toPrev (c.i - 1) = n.toPrev (c.i - 1)) :
    ∀ r w2, handleFullWith up 0 x [] last compact c (setX x m u) = .ok (r, w2) →
      handleFullWith up 0 x [] last compact c u = .ok (r, w2) :=
  swp_handleFullWith_zero u.path up [] last compact ⟨hx, hxn, rfl⟩ hft hleaf hprev

/-- The transfer the consumers use: a postcondition of the split from u, whose
node at x is n, holds of the split from the writer's state, whose node at x is m. -/
theorem writerWP_handleFull_swap (x : NodeId) (n m : KNode) (depth : Nat) (last : KNode)
    (compact : Bool) (c : Ctx) (u : W) (post : Unit → W → Prop) (hx : u.nodes.lookup x = some n)
    (hxn : x < u.next) (hpath : ∀ i e, i < depth → u.path[i]? = some e → e.2 ≠ x)
    (hft : m.firstTime = n.firstTime) (hleaf : m.leaf = n.leaf)
    (hprev : n.firstTime ≠ some c.i → m.toPrev (c.i - 1) = n.toPrev (c.i - 1))
    (h : WriterWP (handleFull depth x last compact) c u post) :
    WriterWP (handleFull depth x last compact) c (setX x m u) post := by
  intro r w2 h2
  exact h r w2 (handleFull_swap x n m depth last compact c u hx hxn hpath hft hleaf hprev r w2 h2)

theorem writerWP_handleFullWith_root_swap (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n m : KNode) (last : KNode)
    (compact : Bool) (c : Ctx) (u : W) (post : Unit → W → Prop) (hx : u.nodes.lookup x = some n)
    (hxn : x < u.next) (hft : m.firstTime = n.firstTime) (hleaf : m.leaf = n.leaf)
    (hprev : n.firstTime ≠ some c.i → m.toPrev (c.i - 1) = n.toPrev (c.i - 1))
    (h : WriterWP (handleFullWith up 0 x [] last compact) c u post) :
    WriterWP (handleFullWith up 0 x [] last compact) c (setX x m u) post := by
  intro r w2 h2
  exact h r w2 (handleFullWith_root_swap up x n m last compact c u hx hxn hft hleaf hprev r w2 h2)

end SIS.Tree
