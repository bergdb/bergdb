/-
The contract package (bergdb 030-10): `handleFullWith` when it does a time
split, while a new segment leaf has no klong yet (`CasPreO`,
WriterCascadeDefsO.lean). And: `handleFullWith` never lowers the next id.

`handleFullWith_next`: every step of `handleFullWith` keeps or raises the next
id (`tsoMono`, step by step through all its branches).

`handleFull_time_o` is WriterTimeSplitG.lean's proof with soundness read on
the map with fs set (`ovSet`), where the path's nodes and the nodes the step
makes are not nodes of fs; the books are `PutBooksE`. The new node y is not a
node of fs by the statement's premise on fs's ids: in the parent's case, if
it were one, that premise fails after the step (the next id only grows, also
in `up`, by `hupn`); and a node with no klong yet stays a node of fs
(`PInvO.empties`): the nodes made or changed have klongs.
-/
import Contract.Proof.WriterTimeSplitG
import Contract.Proof.WriterCascadeDefsO

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. The next id never falls -/

/-- A step never lowers the next id. -/
def tsoMono (c : Ctx) {α : Type} (f : SIS.Tree.M α) : Prop :=
  ∀ w : MW, WP f c w (fun _ w' => w.next ≤ w'.next)

theorem tso_bind {c : Ctx} {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β}
    (hf : tsoMono c f) (hg : ∀ a, tsoMono c (g a)) : tsoMono c (f >>= g) := by
  intro w
  rw [wp_bind]
  intro a w1 h1 b w2 h2
  exact Nat.le_trans (hf w a w1 h1) (hg a w1 b w2 h2)

theorem tso_pure {c : Ctx} {α : Type} (a : α) : tsoMono c (pure a) := by
  intro w
  rw [wp_pure]

theorem tso_throw {c : Ctx} {α : Type} (e : String) : tsoMono c (throw e : SIS.Tree.M α) :=
  fun w => wp_throw e c w _

theorem tso_read {c : Ctx} : tsoMono c (read : SIS.Tree.M Ctx) := by
  intro w
  rw [wp_read]

theorem tso_modify {c : Ctx} {f : MW → MW} (hf : ∀ w, w.next ≤ (f w).next) :
    tsoMono c (modify f : SIS.Tree.M Unit) := by
  intro w
  rw [wp_modify]
  exact hf w

theorem tso_ok {c : Ctx} {α : Type} {f : SIS.Tree.M α}
    (h : ∀ w, ∃ a w', f c w = .ok (a, w') ∧ w.next ≤ w'.next) : tsoMono c f := by
  intro w
  obtain ⟨a, w', hr, hn⟩ := h w
  rw [ts_wp_ok hr]
  exact hn

theorem tso_note {c : Ctx} (t : String) : tsoMono c (SIS.Tree.note t) :=
  tso_ok fun w => ⟨_, _, note_eq c w t, Nat.le_refl _⟩

theorem tso_putNode {c : Ctx} (x : NodeId) (n : MNode) : tsoMono c (SIS.Tree.putNode x n) :=
  tso_ok fun w => ⟨_, _, putNode_eq c w x n, Nat.le_refl _⟩

theorem tso_setMadeFor {c : Ctx} (m : NodeId) (o : Option NodeId) :
    tsoMono c (SIS.Tree.setMadeFor m o) := by
  cases o with
  | none => exact tso_ok fun w => ⟨_, _, setMadeFor_none c w m, Nat.le_refl _⟩
  | some o => exact tso_ok fun w => ⟨_, _, setMadeFor_some c w m o, Nat.le_refl _⟩

theorem tso_replacedBy {c : Ctx} (x : NodeId) : tsoMono c (SIS.Tree.replacedBy x) :=
  tso_ok fun w => ⟨_, _, replacedBy_eq c w x, Nat.le_refl _⟩

theorem tso_newKey {c : Ctx} (g h : Nat) (leaf : Bool) (ks : List MKlong) :
    tsoMono c (SIS.Tree.newKey g h leaf ks) :=
  tso_ok fun w => ⟨_, _, newKey_eq c w g h leaf ks, Nat.le_add_right _ 2⟩

theorem tso_newSuperRoot {c : Ctx} (y : NodeId) : tsoMono c (SIS.Tree.newSuperRoot y) := by
  refine tso_ok fun w => ?_
  by_cases hi : c.i = w.top.time
  · exact ⟨_, _, newSuperRoot_inPlace_eq c w y hi, Nat.le_refl _⟩
  · exact ⟨_, _, newSuperRoot_new_eq c w y hi, Nat.le_add_right _ 2⟩

theorem tso_getNode {c : Ctx} (x : NodeId) : tsoMono c (SIS.Tree.getNode x) := by
  intro W
  unfold SIS.Tree.getNode
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
  · rw [wp_bind, wp_read]
    split
    · split
      · exact wp_throw _ _ _ _
      · rw [wp_bind, wp_set, wp_pure]
    · exact wp_throw _ _ _ _

theorem tso_ghOf {c : Ctx} (x : NodeId) : tsoMono c (SIS.Tree.ghOf x) := by
  unfold SIS.Tree.ghOf
  refine tso_bind (tso_getNode x) (fun _ W => ?_)
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
  · exact wp_throw _ _ _ _

theorem tso_pathNode {c : Ctx} (d : Nat) : tsoMono c (SIS.Tree.pathNode d) := by
  intro W
  unfold SIS.Tree.pathNode
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
  · exact wp_throw _ _ _ _

theorem tso_parentAt {c : Ctx} (d : Nat) : tsoMono c (SIS.Tree.parentAt d) := by
  cases d with
  | zero => exact tso_ok fun w => ⟨_, _, parentAt_zero c w, Nat.le_refl _⟩
  | succ e =>
    unfold SIS.Tree.parentAt
    exact tso_bind (tso_pathNode e) (fun _ => tso_pure _)

theorem tso_klongAt {c : Ctx} (d : Nat) : tsoMono c (SIS.Tree.klongAt d) := by
  intro W
  unfold SIS.Tree.klongAt
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
  · exact wp_throw _ _ _ _

theorem tso_foldlM {c : Ctx} {α β : Type} (F : β → α → SIS.Tree.M β)
    (hF : ∀ b a, tsoMono c (F b a)) : ∀ (l : List α) (b : β), tsoMono c (l.foldlM F b)
  | [], b => tso_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact tso_bind (hF b a) (fun b' => tso_foldlM F hF l b')

theorem tso_replaceOrAdd {c : Ctx} (last : MNode) (ins : List (Nat × NodeId)) :
    tsoMono c (SIS.Tree.replaceOrAdd last ins) := by
  unfold SIS.Tree.replaceOrAdd
  refine tso_bind tso_read (fun c' => tso_foldlM _ (fun b a => ?_) _ _)
  obtain ⟨cv, y⟩ := a
  dsimp only
  split
  · exact tso_throw _
  · exact tso_pure _
  · exact tso_pure _

/-- `handleFullWith` never lowers the next id, if `up` does not. -/
theorem handleFullWith_next {c : SIS.Tree.Ctx}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hup : ∀ q ins (w : MW), WP (up q ins) c w (fun _ w' => w.next ≤ w'.next))
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : MNode) (compact : Bool)
    (w : MW) :
    WP (SIS.Tree.handleFullWith up depth x ins last compact) c w
      (fun _ w' => w.next ≤ w'.next) := by
  have hupm : ∀ q ins, tsoMono c (up q ins) := fun q ins w => hup q ins w
  suffices hm : tsoMono c (SIS.Tree.handleFullWith up depth x ins last compact) from hm w
  unfold SIS.Tree.handleFullWith
  dsimp only
  repeat (first
    | with_reducible exact tso_pure _
    | with_reducible exact tso_throw _
    | with_reducible exact tso_read
    | with_reducible exact tso_getNode _
    | with_reducible exact tso_ghOf _
    | with_reducible exact tso_parentAt _
    | with_reducible exact tso_klongAt _
    | with_reducible exact tso_note _
    | with_reducible exact tso_putNode _ _
    | with_reducible exact tso_setMadeFor _ _
    | with_reducible exact tso_replacedBy _
    | with_reducible exact tso_newKey _ _ _ _
    | with_reducible exact tso_newSuperRoot _
    | with_reducible exact tso_replaceOrAdd _ _
    | with_reducible exact hupm _ _
    | with_reducible exact tso_modify (fun _ => Nat.le_refl _)
    | with_reducible refine tso_bind ?_ (fun _ => ?_)
    | split)

/-! ## 2. The map with `fs` set -/

theorem tso_ovSet_not {fs : List (NodeId × Obj)} : ∀ {T : Tree} {z : NodeId},
    z ∉ fs.map (·.1) → (ovSet fs T).obj z = T.obj z := by
  induction fs with
  | nil => intro T z _; rfl
  | cons xo fs ih =>
    intro T z hz
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    show (ovSet fs (T.set xo.1 xo.2)).obj z = T.obj z
    rw [ih hz.2]
    simp [Tree.set, hz.1]

/-- A node of fs, or a node with the same object in T and T', has the same
object in both with fs set. -/
theorem tso_ovSet_eq {fs : List (NodeId × Obj)} : ∀ {T T' : Tree} {z : NodeId},
    (z ∈ fs.map (·.1) ∨ T.obj z = T'.obj z) → (ovSet fs T).obj z = (ovSet fs T').obj z := by
  induction fs with
  | nil =>
    intro T T' z h
    rcases h with h | h
    · simp at h
    · exact h
  | cons xo fs ih =>
    intro T T' z h
    show (ovSet fs (T.set xo.1 xo.2)).obj z = (ovSet fs (T'.set xo.1 xo.2)).obj z
    apply ih
    by_cases e : z = xo.1
    · right
      simp [Tree.set, e]
    · simp only [List.map_cons, List.mem_cons, e, false_or] at h
      rcases h with h | h
      · exact Or.inl h
      · right
        simp [Tree.set, e, h]

theorem tso_ovSet_roots {fs : List (NodeId × Obj)} :
    ∀ {T : Tree}, (ovSet fs T).roots = T.roots := by
  induction fs with
  | nil => intro T; rfl
  | cons xo fs ih =>
    intro T
    show (ovSet fs (T.set xo.1 xo.2)).roots = T.roots
    rw [ih]
    rfl

theorem tso_ovSet_set {fs : List (NodeId × Obj)} {T : Tree} {x : NodeId} {o : Obj}
    (hx : x ∉ fs.map (·.1)) : ovSet fs (T.set x o) = (ovSet fs T).set x o := by
  apply prim_tree_ext
  · intro z
    by_cases e : z = x
    · subst e
      rw [tso_ovSet_not hx]
      simp [Tree.set]
    · rw [tso_ovSet_eq (T' := T) (Or.inr (by simp [Tree.set, e]))]
      simp [Tree.set, e]
  · rw [tso_ovSet_roots]
    show T.roots = (ovSet fs T).roots
    rw [tso_ovSet_roots]

/-- Nodes kept in B where they are in A stay so with fs set. -/
theorem tso_ovSet_some {fs : List (NodeId × Obj)} {A B : Tree}
    (h : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true) :
    ∀ z, ((ovSet fs A).obj z).isSome = true → ((ovSet fs B).obj z).isSome = true := by
  intro z hz
  by_cases e : z ∈ fs.map (·.1)
  · rw [tso_ovSet_eq (T' := A) (Or.inl e)]
    exact hz
  · rw [tso_ovSet_not e] at hz ⊢
    exact h z hz

/-! ## 3. The books that allow a node with no klong yet -/

theorem tso_putBooksE_congr {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w w' : MW}
    (hk : PutBooksE p i base s w) (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals)
    (h3 : w'.taken = w.taken) (h4 : w'.made = w.made) (h5 : w'.top = w.top)
    (h6 : w'.newTop = w.newTop) (h7 : w'.gh = w.gh) (h8 : w'.next = w.next)
    (h9 : w'.outside = w.outside) : PutBooksE p i base s w' := by
  cases w; cases w'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨hk.first, hk.times, hk.levels, hk.ids, hk.taken, hk.overlay, hk.within, hk.timeFirst,
    hk.empty⟩

/-- `PutBooksE` after `newSuperRoot`. -/
theorem tso_putBooksE_afterSuperRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree}
    (y : NodeId) {w : MW} (hk : PutBooksE p i base s w) :
    PutBooksE p i base s (MW.afterSuperRoot w p i y) := by
  obtain ⟨-, -, h1, h2, h3, h4, -, -, h7⟩ := afterSuperRoot_fields w p i y
  have hlev : ∀ x n, w.nodes.lookup x = some n →
      wLevel s (MW.afterSuperRoot w p i y) x = wLevel s w x :=
    fun x n hl => wLevel_afterSuperRoot s p i y (Nat.ne_of_lt (hk.ids.1 x n hl))
  have hmade : ∀ x, x ∈ w.made.map (·.id) →
      x ∈ (MW.afterSuperRoot w p i y).made.map (·.id) := by
    intro x hx
    cases hnt : w.newTop
    · rw [(afterSuperRoot_new hnt p i y).1, List.map_append]
      exact List.mem_append_left _ hx
    · rw [(afterSuperRoot_inPlace hnt p i y).1]
      exact hx
  have hids : ((∀ x n, (MW.afterSuperRoot w p i y).nodes.lookup x = some n →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ x h, (MW.afterSuperRoot w p i y).vals.lookup x = some h →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ m ∈ (MW.afterSuperRoot w p i y).made, m.id < (MW.afterSuperRoot w p i y).next ∧
        base ≤ m.id) ∧
      base ≤ (MW.afterSuperRoot w p i y).next ∧
      ((MW.afterSuperRoot w p i y).newTop = true →
        (MW.afterSuperRoot w p i y).top.id < (MW.afterSuperRoot w p i y).next)) := by
    obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hk.ids
    cases hnt : w.newTop
    · rw [afterSuperRoot_of_false hnt]
      refine ⟨fun x n hl => Nat.lt_add_right 2 (hi1 x n hl),
        fun x h hl => Nat.lt_add_right 2 (hi2 x h hl), fun m hm => ?_, by
          show base ≤ w.next + 2; omega, fun _ => by show w.next < w.next + 2; omega⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨Nat.lt_add_right 2 (hi3 m hm).1, (hi3 m hm).2⟩
      · simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨by show w.next < w.next + 2; omega, hi4⟩
    · rw [afterSuperRoot_of_true hnt]
      exact ⟨hi1, hi2, hi3, hi4, hi5⟩
  refine ⟨?_, ?_, ?_, hids, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h3]
    exact hk.first
  · rw [h1]
    exact hk.times
  · intro x n hl ht
    rw [h1] at hl
    rw [h3] at ht
    obtain ⟨g, h, hg, hG, hH, hL, hleaf⟩ := hk.levels x n hl ht
    exact ⟨g, h, by rw [h4]; exact hg, hG, hH, by rw [hlev x n hl]; exact hL, hleaf⟩
  · rw [h3]
    exact fun x hx => hmade x (hk.taken x hx)
  · rw [h1]
    intro x n hl
    rcases hk.overlay x n hl with h | h
    · exact Or.inl h
    · exact Or.inr (hmade x h)
  · rw [h7]
    exact hk.within
  · rw [h1, h3]
    exact hk.timeFirst
  · rw [h1, h3]
    exact hk.empty

/-- The facts of x, a node from before the transaction, for its cut back. -/
theorem tso_old {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW} {x : NodeId}
    {n : MNode} (hk : PutBooksE p i base s w) (hx : w.nodes.lookup x = some n)
    (hf : ∃ t rest, n.ks = SIS.Tree.Klong.time t :: rest) (hnt : n.firstTime ≠ some i) :
    (n.toPrev (i - 1)).ks.head? = n.ks.head? ∧
      ∀ t, SIS.Tree.Klong.time t ∈ (n.toPrev (i - 1)).ks → t ≤ i := by
  obtain ⟨t0, rest0, hn⟩ := hf
  have ht0 : t0 ≤ i := hk.times x n hx t0 (by rw [hn]; exact List.mem_cons_self)
  have hne : t0 ≠ i := fun e => hnt (by rw [prim_firstTime_of hn, e])
  refine ⟨ts_toPrev_head hn (by omega), fun t htm => hk.times x n hx t (ts_mem_toPrev htm)⟩

theorem tso_ne_of_head {m m' : MNode} (hf : ∃ t rest, m.ks = SIS.Tree.Klong.time t :: rest)
    (hh : m'.ks.head? = m.ks.head?) : m'.ks ≠ [] := by
  obtain ⟨t, rest, hm⟩ := hf
  intro e
  rw [e, hm] at hh
  cases hh

/-- The nodes kept with no klong yet are nodes of fs, after a node is set
to one with klongs. -/
theorem tso_emp_withNode {fs : List (NodeId × Obj)} {W : MW} {x : NodeId} {m : MNode}
    (hE : ∀ y n, W.nodes.lookup y = some n → W.taken.contains y = false → n.ks = [] →
      y ∈ fs.map (·.1)) (hm : m.ks ≠ []) :
    ∀ y n, (W.withNode x m).nodes.lookup y = some n → (W.withNode x m).taken.contains y = false →
      n.ks = [] → y ∈ fs.map (·.1) := by
  intro y n hy ht he
  rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · exact absurd he hm
  · exact hE y n hy ht he

/-- The same after `newKey` with klongs. -/
theorem tso_emp_afterNewKey {fs : List (NodeId × Obj)} {W : MW} {p : MParams} {g h : Nat}
    {leaf : Bool} {ks : List MKlong}
    (hE : ∀ y n, W.nodes.lookup y = some n → W.taken.contains y = false → n.ks = [] →
      y ∈ fs.map (·.1)) (hn : W.nodes.lookup W.next = none) (hks : ks ≠ []) :
    ∀ y n, (W.afterNewKey p g h leaf ks).nodes.lookup y = some n →
      (W.afterNewKey p g h leaf ks).taken.contains y = false → n.ks = [] →
      y ∈ fs.map (·.1) := by
  intro y n hy ht he
  rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · exact absurd he hks
  · exact hE y n hy ht he

/-! ## 4. The lemmas of WriterTimeSplitG.lean with `CasPreO` -/

/-- What `CasPreO` gives of the state w itself, before the klongs are added: x
is kept; the map's root, the frame, the top, BalancedOK, and the nodes kept
with no klong yet are nodes of fs. -/
theorem tso_wfacts {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId} {n : MNode}
    {ins : List (Nat × NodeId)} {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w depth x n ins C) :
    w.taken.contains x = false ∧ (treeOf i s w).root = some w.top.rootKey ∧
      Frame i s (dirtyOf w) (treeOf i s w) ∧ WTopInv i s tp w.top w.newTop ∧
      BalancedAll p (treeOf i s w) ∧
      ∀ y m, w.nodes.lookup y = some m → w.taken.contains y = false → m.ks = [] →
        y ∈ fs.map (·.1) := by
  have htx : w.taken.contains x = false := by
    obtain ⟨c0, hon⟩ := h.on
    obtain ⟨m, -, ht⟩ := h.path.lookup (le_refl _) hon
    exact ht
  have hI := h.hyp
  have hxA : (w.withNode x (addAll i n ins)).nodes.lookup x = some (addAll i n ins) :=
    lookup_upsert_self _ _ _
  have hleaf : n.leaf = (addAll i n ins).leaf := (addAll_leaf i n ins).symm
  refine ⟨htx, hI.root, ?_, hI.top, ?_, ?_⟩
  · have hF := frame_withNode hI.frame hxA htx hleaf (fun n0 hs0 => by
      obtain ⟨-, -, he⟩ := frame_overlay_ext hI.frame hxA htx hs0
      exact ts_ext_back ins (prim_timesBefore (hb.times x n0 hs0)) he)
    rwa [ts_treeOf_back i s h.look htx, ts_dirtyOf_back h.look] at hF
  · have hB := balancedAll_withNode hI.balanced hxA htx hleaf (fun hl c y hy => by
      have hobj := treeOf_obj_overlay i s hxA htx
      obtain ⟨-, -, hk⟩ := hI.balanced x _ hobj
      exact hk (by rw [← hleaf]; exact hl) c y
        ((addAll_key_mem ins n).mpr (Or.inl (ts_key_mem_ksOf hy))))
    rwa [ts_treeOf_back i s h.look htx] at hB
  · intro y m hy ht he
    by_cases e : y = x
    · subst e
      rw [h.look] at hy
      cases hy
      obtain ⟨t, rest, hr⟩ := h.first
      rw [hr] at he
      cases he
    · exact hI.empties y m (by rw [MW.withNode, lookup_upsert_ne _ _ e]; exact hy) ht he

/-- The nodes of the path are reached in a sound tree A that is the map of w
on the path above x, if x is not on the path above its depth. -/
theorem tso_path_reach {i : Time} {s : Tree} {w : MW} {depth : Nat}
    {A : Tree} {lo : Nat} {hi : Option Nat} (hG : Good A w.top.rootKey lo hi)
    (hP : PathOk i s w depth)
    (hA : ∀ d c u, d < depth → w.path[d]? = some (c, u) → A.obj u = (treeOf i s w).obj u) :
    ∀ d, d ≤ depth → ∀ c u, w.path[d]? = some (c, u) →
      u ∈ reachAt A (A.fuel w.top.rootKey) w.top.rootKey
  | 0, _, c, u, hu => by
    rw [hP.root] at hu
    cases hu
    exact tc_self _ _ _
  | d + 1, hd, c, u, hu => by
    obtain ⟨c0', u0, cc, y, nu, e1, e2, e3, e4⟩ := hP.links d (by omega)
    rw [hu] at e2
    cases e2
    have ih := tso_path_reach hG hP hA d (by omega) c0' u0 e1
    rw [← hA d c0' u0 (by omega) e1] at e3
    exact ts_reach_kid hG ih e3 e4

/-- x is not on the path above its depth. -/
theorem tso_off {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId} {n : MNode}
    {ins : List (Nat × NodeId)} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w depth x n ins C) :
    ∀ d c, d < depth → w.path[d]? ≠ some (c, x) := by
  intro d c hd he
  obtain ⟨c0, hon⟩ := h.on
  exact h.nodup d depth c c0 x hd (Nat.le_refl _) he hon

/-- The nodes of the path above x are reached in the "if" tree with fs set. -/
theorem tso_reachP {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId} {n : MNode}
    {ins : List (Nat × NodeId)} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w depth x n ins C) (htx : w.taken.contains x = false) :
    ∀ d, d ≤ depth → ∀ c u, w.path[d]? = some (c, u) →
      u ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
        ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
        w.top.rootKey := by
  refine tso_path_reach (w := w) h.hyp.sound.good h.path (fun d c u hd hu => ?_)
  have hux : u ≠ x := fun e => tso_off h d c hd (e ▸ hu)
  rw [tso_ovSet_not (h.away d c u (Nat.le_of_lt hd) hu), treeOf_withNode i s _ htx]
  simp [Tree.set, hux]

/-- `replaceOrAdd` on x's last version with the klongs (`ts_wp_replace` with
`CasPreO`). -/
theorem tso_wp_replace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)} {compact : Bool}
    (h : CasPreO p i base s tp fs w depth x n ins C)
    (hcase : (compact = true ∧ n.size + ins.length + 1 ≤ p.M) ∨
      (compact = false ∧ (n.lastVersion i).size ≤ p.splitAbove))
    {w0 : MW} {k : MNode → SIS.Tree.M Unit} {post : Unit → MW → Prop}
    (hk : ∀ r : MNode, live (ksOf r) = live (ksOf (addAll i n ins)) →
      klongsWf (ksOf r) = true → r.size ≤ p.M →
      (∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins)) →
      (∃ rest, r.ks = .time i :: rest) → TimesLe r i →
      WP (k r) { p := p, i := i, view := v } w0 post) :
    WP (SIS.Tree.replaceOrAdd (n.lastVersion i) ins >>= k)
      { p := p, i := i, view := v } w0 post := by
  have hlv : ksOf (n.lastVersion i) = Klong.time ({ p := p, i := i, view := v } : Ctx).i ::
      (live (ksOf n)).map (fun cy => Klong.key cy.1 cy.2) := lastVersion_ks i
  obtain ⟨r, hrun, -, hrwf, hrlive, hrf, hrt, -, hrsize, hrkeys⟩ :=
    replaceOrAdd_spec _ w0 (live_sorted _) hlv ins
  rw [ts_wp_bind_ok hrun]
  refine hk r (by rw [hrlive, addAll_live h.wf]) hrwf ?_ ?_ hrf hrt
  · have hlen : (n.lastVersion i).size = (live (ksOf n)).length + 1 := by
      rw [← ksOf_length, hlv]
      simp
    have hins : ins.length ≤ 2 := by rcases h.len with e | e <;> omega
    rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
    · obtain ⟨t0, rest0, hn⟩ := h.first
      have hl := live_length_le (ks := ksOf n) ⟨t0, rest0.map kOf, by simp [ksOf, hn, kOf]⟩
      rw [ksOf_length] at hl
      omega
    · have := hp.splitHi
      omega
  · intro c y hk
    rcases hrkeys c y hk with e | e
    · exact (addAll_key_mem ins n).mpr (Or.inl (ts_live_mem_key e))
    · exact (addAll_key_mem ins n).mpr (Or.inr e)

/-- The state after the time split in place (`tsg_inPlace` with `CasPreO`). -/
theorem tso_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w depth x n ins C)
    (hnt : n.firstTime = some i) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i) (T : List String) :
    CasPostO p i base s tp fs w depth x n ins C ()
      (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) := by
  intro _ _
  obtain ⟨htx, hroot, hF, hT, hB, hE⟩ := tso_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  obtain ⟨c0, hon⟩ := h.on
  have hxfs : x ∉ fs.map (·.1) := h.away depth c0 x (le_refl _) hon
  have hxr := tso_reachP h htx depth (le_refl _) c0 x hon
  have hA : treeOf i s (w.withNode x (addAll i n ins)) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hBt : treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [treeOf_withNode i s (w := { w with trail := T }) _ htx]
    rfl
  have hAx : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [tso_ovSet_not hxfs, hA]; simp [Tree.set]
  have hBx : (ovSet fs (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [tso_ovSet_not hxfs, hBt]; simp [Tree.set]
  have hsame : ∀ z, z ≠ x →
      (ovSet fs (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z hz
    apply tso_ovSet_eq
    right
    rw [hA, hBt]
    simp [Tree.set, hz]
  have hxok := hI.sound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hNode : NodeIs (ovSet fs (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)))
      x (wLevel s w x) n.leaf (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨_, hBx, rfl, rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => ?_⟩⟩
    · show (ksOf r).length ≤ p.M
      rw [ksOf_length]; exact hrs
    · have := hxp c y (hrk c y hk)
      by_cases hy : y = x
      · rw [hy, hBx]; rfl
      · rw [hsame y hy]; exact this
  have hS := Sound.inPlace hI.sound hAx hNode hsame
  have hne : n.ks ≠ [] := by obtain ⟨t, rest, hr⟩ := h.first; rw [hr]; exact List.cons_ne_nil _ _
  have hfirst := h.books.first x n hx htx hne
  have hrne : r.ks ≠ [] := by obtain ⟨rest, hr⟩ := hrf; rw [hr]; exact List.cons_ne_nil _ _
  refine ⟨⟨?_, hS, ?_, hT, ?_, ?_, tso_emp_withNode (W := { w with trail := T }) hE hrne⟩,
    ⟨rfl, ?_, le_refl _, ?_⟩⟩
  · rw [hBt]; exact hroot
  · refine frame_withNode (w := { w with trail := T }) hF hx htx rfl (fun n0 hs0 => ?_)
    exact absurd hnt (hfirst.mp (by rw [hs0]; rfl))
  · refine balancedAll_withNode (w := { w with trail := T }) hB hx htx rfl (fun hl c y hy => ?_)
    exact ts_kids hA hI.balanced hl (hrk c y (ts_key_mem_ksOf hy))
  · refine putBooksE_withNode (w := { w with trail := T })
      (tso_putBooksE_congr h.books rfl rfl rfl rfl rfl rfl rfl rfl rfl) hx htx rfl (Or.inl ?_) ?_
    · obtain ⟨rest, hr⟩ := hrf
      obtain ⟨t0, rest0, hn⟩ := h.first
      rw [prim_firstTime_of hn] at hnt
      cases hnt
      show r.ks.head? = n.ks.head?
      rw [hr, hn]
      rfl
    · intro t ht
      exact hrt t (ts_time_mem_ksOf ht)
  · intro y m hy hny
    have hyx : y ≠ x := fun e => hny depth c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert w.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact hy
  · intro z hz
    left
    unfold reachOfO at hz ⊢
    rw [ts_reach_live hAx hBx hrl rfl hsame] at hz
    exact hz

/-- The time split at the space root of a node from before the transaction
(`ts_root` with `CasPreO`): the new node y is not a node of fs, by the
statement's premise on fs's ids. -/
theorem tso_root {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {fs : List (NodeId × Obj)} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w 0 x n ins C)
    (hnt : n.firstTime ≠ some i) {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPostO p i base s tp fs w 0 x n ins C ()
      (MW.withNode (MW.afterSuperRoot
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } p i w.next)
        x (n.toPrev (i - 1))) := by
  intro _ hfs
  obtain ⟨htx, -, hF, hT, hB, hE⟩ := tso_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  obtain ⟨c0, hon⟩ := h.on
  have hxr : x = w.top.rootKey := by
    rw [h.path.root] at hon
    cases hon
    rfl
  have hxfs : x ∉ fs.map (·.1) := h.away 0 c0 x (le_refl _) hon
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  have hA : treeOf i s (w.withNode x (addAll i n ins)) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hAx : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [tso_ovSet_not hxfs, hA]; simp [Tree.set]
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  let W2 : MW := MW.afterSuperRoot W1 p i w.next
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooksE p i base s W1 :=
    tso_putBooksE_congr (putBooksE_afterNewKey hb h.books hG hH hleaf (Or.inr hrf)
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hrne : r.ks ≠ [] := by obtain ⟨rest, hr⟩ := hrf; rw [hr]; exact List.cons_ne_nil _ _
  have hE1 : ∀ y m, W1.nodes.lookup y = some m → W1.taken.contains y = false → m.ks = [] →
      y ∈ fs.map (·.1) :=
    tso_emp_afterNewKey (p := p) (g := g) (h := hh) (leaf := n.leaf) hE hn0 hrne
  obtain ⟨f1, -, f3, -, f5, -, -, f8, -⟩ := afterSuperRoot_fields W1 p i w.next
  obtain ⟨hobj2, hroot2, -⟩ := treeOf_afterSuperRoot i s p w.next hK1.ids.1
  have hnext2 : w.next + 2 ≤ W2.next := by
    show w.next + 2 ≤ (MW.afterSuperRoot W1 p i w.next).next
    cases hnt1 : W1.newTop
    · rw [(afterSuperRoot_new hnt1 p i w.next).2.1]
      show w.next + 2 ≤ w.next + 2 + 2
      omega
    · rw [(afterSuperRoot_inPlace hnt1 p i w.next).2.1]
      exact Nat.le_refl _
  have hyfs : w.next ∉ fs.map (·.1) := by
    intro hm
    rcases hfs w.next hm with e | e
    · exact Nat.lt_irrefl _ e
    · exact absurd (Nat.le_trans hnext2 e) (by omega)
  have hx2 : W2.nodes.lookup x = some n := by
    rw [f3]; exact prim_lookup_append_some _ hx
  have ht2 : W2.taken.contains x = false := by rw [f5]; exact htx
  have hT3 : treeOf i s (W2.withNode x (n.toPrev (i - 1))) =
      (treeOf i s W2).set x (.key ⟨wLevel s W2 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) :=
    treeOf_withNode i s _ ht2
  have hBobj : ∀ z, (treeOf i s (W2.withNode x (n.toPrev (i - 1)))).obj z =
      if z = x then some (.key ⟨wLevel s W2 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) else
        if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) else
          (treeOf i s w).obj z := by
    intro z
    rw [hT3]
    simp only [Tree.set]
    rw [hobj2, hT1]
    rfl
  -- the rule
  have hxok := hI.sound.nodes x
    (by rw [show (w.withNode x (addAll i n ins)).top.rootKey = x from hxr.symm]
        exact tc_self _ _ _) _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hsome0 : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (W2.withNode x (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    rw [hBobj]
    by_cases e1 : z = x
    · simp [e1]
    · by_cases e2 : z = w.next
      · subst e2
        simp [Ne.symm hxne]
      · simp only [e1, e2, ↓reduceIte]
        rw [hA] at hz
        simpa [Tree.set, e1] using hz
  have hsome := tso_ovSet_some (fs := fs) hsome0
  have hBy : NodeIs (ovSet fs (treeOf i s (W2.withNode x (n.toPrev (i - 1))))) w.next
      (wLevel s w x) n.leaf (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩,
      by rw [tso_ovSet_not hyfs, hBobj]; simp [Ne.symm hxne], hlev.symm,
      rfl, hrl,
      ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hS0 : Sound p.M (some x) (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) x C := by
    have := hI.sound
    rw [show (w.withNode x (addAll i n ins)).top.rootKey = x from hxr.symm] at this
    exact this
  obtain ⟨hSB, -, hreach⟩ := Sound.timeSplitRoot hS0 hAx
    (show (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj w.next = none by
      rw [tso_ovSet_not hyfs]; exact (treeOf_freshE hb hI.books (Nat.le_refl _)).1)
    hBy (by rw [tso_ovSet_not hxfs, hBobj]; simp)
    (fun z e1 e2 => tso_ovSet_eq (Or.inr (by rw [hBobj, hA]; simp [Tree.set, e1, e2])))
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  have hF3 := frame_withNode (ts_frame_superRoot p w.next hF1 hK1.ids.1) hx2 ht2
    (rfl : (n.toPrev (i - 1)).leaf = n.leaf) (ts_toPrev_ext hb hF hx htx)
  have hB1 : BalancedAll p (treeOf i s W1) :=
    balancedAll_afterNewKey g hh n.leaf r.ks hB hs0 hn0 ht0 hm0 hH hleaf (fun hl c y hy => by
      rw [← hlev]
      exact ts_kids hA hI.balanced hl (hrk c y (ts_key_mem_ksOf hy)))
  have hB2 : BalancedAll p (treeOf i s W2) := by
    unfold BalancedAll; rw [hobj2]; exact hB1
  have hB3 := balancedAll_withNode hB2 hx2 ht2 (rfl : (n.toPrev (i - 1)).leaf = n.leaf)
    (fun hl c y hy => by
      obtain ⟨-, -, hk⟩ := hB2 x _ (treeOf_obj_overlay i s hx2 ht2)
      exact hk hl c y (ts_key_mem_ksOf (ts_mem_toPrev hy)))
  obtain ⟨hfst, htimes⟩ := tso_old h.books hx h.first hnt
  have hK3 := putBooksE_withNode (n' := n.toPrev (i - 1)) (tso_putBooksE_afterSuperRoot w.next hK1)
    hx2 ht2 rfl (Or.inl hfst) htimes
  have hE2 : ∀ y m, W2.nodes.lookup y = some m → W2.taken.contains y = false → m.ks = [] →
      y ∈ fs.map (·.1) := by
    rw [f3, f5]; exact hE1
  have hT2 : WTopInv i s tp W2.top W2.newTop :=
    topInv_afterSuperRoot w.next hT hb (by have := hK1.ids.2.2.2.1; exact this)
  refine ⟨⟨?_, ?_, hF3, hT2, hB3, hK3, tso_emp_withNode hE2 (tso_ne_of_head h.first hfst)⟩,
    ⟨f8, ?_, Nat.le_trans (Nat.le_add_right _ 2) hnext2, ?_⟩⟩
  · rw [hT3]
    show (treeOf i s W2).root = some W2.top.rootKey
    rw [hroot2, f1]
  · show Sound p.M none (ovSet fs (treeOf i s (W2.withNode x (n.toPrev (i - 1))))) W2.top.rootKey C
    rw [f1]
    exact hSB
  · intro y m hy hny
    have hyx : y ≠ x := fun e => hny 0 c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert W2.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx, f3]
    exact prim_lookup_append_some _ hy
  · intro z hz
    unfold reachOfO at hz ⊢
    have hz' : z ∈ reachAt (ovSet fs (treeOf i s (W2.withNode x (n.toPrev (i - 1)))))
        ((ovSet fs (treeOf i s (W2.withNode x (n.toPrev (i - 1))))).fuel w.next) w.next := by
      rw [← f1]; exact hz
    rcases hreach z hz' with e | e
    · left
      show z ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
        ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
        w.top.rootKey
      rw [← hxr]
      exact e
    · right
      rw [e]

/-- The time split below the space root of a node from before the
transaction, up to the parent's step (`tsg_parentPre` with `CasPreO`), if the
new node y is not a node of fs. -/
theorem tso_parentPre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {fs : List (NodeId × Obj)} {d : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C) (hyfs : w.next ∉ fs.map (·.1))
    {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    {q : NodeId} {nq : MNode} {c0 : Option Nat} {k1 : Nat} (hq : w.path[d]? = some (c0, q))
    (hqn : w.nodes.lookup q = some nq) (hk1 : w.path[d + 1]? = some (some k1, x))
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPreO p i base s tp fs { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
        d q nq [(k1, w.next)] C ∧
      x ∉ reachOfO i s fs (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])) ∧
      ∀ z ∈ reachOfO i s fs (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])),
        z ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∨ z = w.next := by
  obtain ⟨htx, hroot, hF, hT, hB, hE⟩ := tso_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  -- the parent
  obtain ⟨-, -, htq⟩ := h.path.lookup (Nat.le_succ d) hq
  have hqne : q ≠ w.next := Nat.ne_of_lt (h.books.ids.1 q nq hqn)
  have hoff := tso_off h
  have hqx : q ≠ x := fun e => hoff d c0 (Nat.lt_succ_self d) (e ▸ hq)
  have hxfs : x ∉ fs.map (·.1) := h.away (d + 1) (some k1) x (Nat.le_refl _) hk1
  have hqfs : q ∉ fs.map (·.1) := h.away d c0 q (Nat.le_succ d) hq
  have hk1l : (k1, x) ∈ live (ksOf nq) := by
    obtain ⟨c0', u, c, y, nu, e1, e2, e3, e4⟩ := h.path.links d (Nat.lt_succ_self d)
    rw [hq] at e1
    cases e1
    rw [hk1] at e2
    cases e2
    rw [treeOf_obj_overlay i s hqn htq] at e3
    cases e3
    exact e4
  -- the tree A of the "if" state
  have hA : treeOf i s (w.withNode x (addAll i n ins)) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hAo : ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z =
      (treeOf i s w).obj z := by
    intro z hz; rw [hA]; simp [Tree.set, hz]
  have hAx : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [tso_ovSet_not hxfs, hA]; simp [Tree.set]
  have hAq : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [tso_ovSet_not hqfs, hAo q hqx]; exact treeOf_obj_overlay i s hqn htq
  have hreachP := tso_reachP h htx
  have hqr := hreachP d (Nat.le_succ d) c0 q hq
  have hxr := hreachP (d + 1) (Nat.le_refl _) (some k1) x hk1
  have hxok := hI.sound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hqok := hI.sound.nodes q hqr _ hAq
  simp only [Option.some.injEq, Ne.symm hqx, ite_false] at hqok
  obtain ⟨hqlen, hqwf, hqp⟩ := ts_nodeOk_iff.mp hqok
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooksE p i base s W1 :=
    tso_putBooksE_congr (putBooksE_afterNewKey hb h.books hG hH hleaf (Or.inr hrf)
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hrne : r.ks ≠ [] := by obtain ⟨rest, hr⟩ := hrf; rw [hr]; exact List.cons_ne_nil _ _
  have hE1 : ∀ y m, W1.nodes.lookup y = some m → W1.taken.contains y = false → m.ks = [] →
      y ∈ fs.map (·.1) :=
    tso_emp_afterNewKey (p := p) (g := g) (h := hh) (leaf := n.leaf) hE hn0 hrne
  have hqn1 : W1.nodes.lookup q = some nq := prim_lookup_append_some _ hqn
  have hwq : wLevel s W1 q = wLevel s w q :=
    prim_wLevel_afterNewKey (p := p) (g := g) (h := hh) (leaf := n.leaf) (ks := r.ks) hqne
  have hTq : treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])) =
      (treeOf i s W1).set q (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩) := by
    rw [treeOf_withNode i s (w := W1) _ htq, hwq, addAll_leaf]
  have hBobj : ∀ z, (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj z =
      if z = q then some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩) else
        if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) else
          (treeOf i s w).obj z := by
    intro z
    rw [hTq]
    simp only [Tree.set]
    rw [hT1]
    rfl
  have hsome0 : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj z).isSome = true := by
    intro z hz
    rw [hBobj]
    by_cases e1 : z = q
    · simp [e1]
    · by_cases e2 : z = w.next
      · subst e2
        simp [hqne.symm]
      · simp only [e1, e2, ↓reduceIte]
        by_cases e3 : z = x
        · subst e3
          rw [treeOf_obj_overlay i s hx htx]
          rfl
        · rw [hAo z e3] at hz
          exact hz
  have hsome := tso_ovSet_some (fs := fs) hsome0
  -- the rule
  have hBy : NodeIs (ovSet fs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])))) w.next
      (wLevel s w x) n.leaf (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [tso_ovSet_not hyfs, hBobj]; simp [hqne.symm],
      hlev.symm,
      rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hBq : NodeIs (ovSet fs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])))) q
      (wLevel s w q) nq.leaf (insertCv k1 w.next (live (ksOf nq))) (bnd p.M (some q) q) := by
    refine ⟨⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩,
      by rw [tso_ovSet_not hqfs, hBobj]; simp,
      rfl, rfl, by rw [addAll_live hqwf]; rfl, ts_nodeOk_iff.mpr ⟨?_, addAll_wf hqwf _, ?_⟩⟩
    · show (ksOf (addAll i nq [(k1, w.next)])).length ≤ bnd p.M (some q) q
      rw [ksOf_length]
      have := addAll_size i nq [(k1, w.next)]
      have hql : (ksOf nq).length ≤ p.M := hqlen
      rw [ksOf_length] at hql
      simp only [bnd, ite_true, List.length_singleton] at this ⊢
      omega
    · intro c y hk
      rcases (addAll_key_mem _ nq).mp hk with hk | hk
      · exact hsome y (hqp c y hk)
      · simp only [List.mem_singleton, Prod.mk.injEq] at hk
        rw [hk.2, tso_ovSet_not hyfs, hBobj]
        simp [hqne.symm]
  have hBx : ((ovSet fs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])))).obj x).isSome
      = true := by
    rw [tso_ovSet_not hxfs, hBobj]
    simp only [Ne.symm hqx, hxne, ↓reduceIte]
    rw [treeOf_obj_overlay i s hx htx]
    rfl
  obtain ⟨hSB, hxnot, hreach⟩ := Sound.timeSplit hI.sound hqr hAq hk1l hAx
    (show (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj w.next = none by
      rw [tso_ovSet_not hyfs]; exact (treeOf_freshE hb hI.books (Nat.le_refl _)).1) hBy hBq hBx
    (fun z e1 e2 e3 => tso_ovSet_eq (Or.inr (by rw [hBobj, hAo z e1]; simp [e2, e3])))
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  have hB1 : BalancedAll p (treeOf i s W1) :=
    balancedAll_afterNewKey g hh n.leaf r.ks hB hs0 hn0 ht0 hm0 hH hleaf (fun hl c y hy => by
      rw [← hlev]
      exact ts_kids hA hI.balanced hl (hrk c y (ts_key_mem_ksOf hy)))
  have hnqne : nq.ks ≠ [] := by
    intro e
    have hm := ts_live_mem_key hk1l
    simp [ksOf, e] at hm
  obtain ⟨tq, restq, hnq⟩ := h.books.timeFirst q nq hqn htq hnqne
  obtain ⟨rest', hr'⟩ := addAll_first (i := i) hnq [(k1, w.next)]
  have hane : (addAll i nq [(k1, w.next)]).ks ≠ [] := by rw [hr']; exact List.cons_ne_nil _ _
  refine ⟨⟨hqn1, ⟨c0, hq⟩, ?_, fun e e' c c' u h1 h2 he he' =>
      h.nodup e e' c c' u h1 (Nat.le_succ_of_le h2) he he',
      fun d' c u hd' hu => h.away d' c u (Nat.le_succ_of_le hd') hu, hK1, ⟨tq, restq, hnq⟩,
      hqwf, ?_, Or.inl rfl, ?_,
      ⟨?_, hSB, ?_, hT, ?_, ?_, tso_emp_withNode hE1 hane⟩⟩, hxnot, hreach⟩
  · exact PathOk.congr (pathOk_afterNewKey p g hh n.leaf r.ks (h.path.mono (Nat.le_succ d)) hs0
      hn0 ht0 hm0) rfl rfl rfl rfl rfl
  · have hql : (ksOf nq).length ≤ p.M := hqlen
    rw [ksOf_length] at hql
    exact hql
  · intro a y1 b y2 he
    simp at he
  · exact hroot
  · refine frame_withNode hF1 hqn1 htq (addAll_leaf i nq _) (fun n0 hs => ?_)
    obtain ⟨-, -, he⟩ := frame_overlay_ext hF1 hqn1 htq hs
    exact addAll_ext (prim_timesBefore (hb.times q n0 hs)) he _
  · refine balancedAll_withNode hB1 hqn1 htq (addAll_leaf i nq _) (fun hl c y hy => ?_)
    rw [addAll_leaf] at hl
    rcases (addAll_key_mem _ nq).mp (ts_key_mem_ksOf hy) with hk | hk
    · obtain ⟨-, -, hkk⟩ := hB1 q _ (treeOf_obj_overlay i s hqn1 htq)
      exact hkk hl c y hk
    · simp only [List.mem_singleton, Prod.mk.injEq] at hk
      rw [hk.2, hT1, hwq]
      refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by simp [Tree.set], ?_⟩
      show p.keyLevel g hh + 1 = wLevel s w q
      have hlq : wLevel s w x + 1 = wLevel s w q := by
        obtain ⟨-, -, hkq⟩ := hB q _ (treeOf_obj_overlay i s hqn htq)
        obtain ⟨m, hm, hml⟩ := hkq hl k1 x (ts_live_mem_key hk1l)
        rw [treeOf_obj_overlay i s hx htx] at hm
        cases hm
        exact hml
      rw [← hlev, hlq]
  · refine putBooksE_withNode hK1 hqn1 htq (addAll_leaf i nq _) (Or.inl ?_) ?_
    · rw [hr', hnq]
      rfl
    · intro t ht
      exact addAll_timesLe (ts_timesLe_of (h.books.times q nq hqn)) _ t (ts_time_mem_ksOf ht)


/-- After the parent's step (`tsg_parentPost` with `CasPreO`): x, which that
step leaves as it was and does not reach in the map with fs set, is cut back
to its node of before. -/
theorem tso_parentPost {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {fs : List (NodeId × Obj)} {d : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hnt : n.firstTime ≠ some i) {W1 W1q W3 : MW}
    (hI3 : PInvO p i base s tp fs none C W3) (hcp : CascadePostO i s fs W1 W1q W3 d)
    (hW1n : ∀ y m, w.nodes.lookup y = some m → W1.nodes.lookup y = some m)
    (hW1p : W1.path = w.path) (hW1next : w.next + 2 ≤ W1.next)
    (hxnot : x ∉ reachOfO i s fs W1q)
    (hreach : ∀ z ∈ reachOfO i s fs W1q,
      z ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∨ z = w.next) :
    W3.nodes.lookup x = some n ∧
      CasPostO p i base s tp fs w (d + 1) x n ins C () (W3.withNode x (n.toPrev (i - 1))) := by
  obtain ⟨htx, -⟩ := tso_wfacts hb h
  have hx := h.look
  obtain ⟨c0, hon⟩ := h.on
  have hxnext : x < w.next := h.books.ids.1 x n hx
  have hx3 : W3.nodes.lookup x = some n := hcp.off x n (hW1n x n hx) (fun d' c hd' he => by
    rw [hW1p] at he
    exact tso_off h d' c (Nat.lt_succ_of_le hd') he)
  have hxfs : x ∉ fs.map (·.1) := h.away (d + 1) c0 x (Nat.le_refl _) hon
  have hne : n.ks ≠ [] := by obtain ⟨t, rest, hr⟩ := h.first; rw [hr]; exact List.cons_ne_nil _ _
  have hxs := (h.books.first x n hx htx hne).mpr hnt
  have htx3 : W3.taken.contains x = false := by
    cases e : W3.taken.contains x with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hI3.books.taken x e)
      have hbm := (hI3.books.ids.2.2.1 m hm).2
      rw [hmx] at hbm
      rw [(hb.ids x hbm).1] at hxs
      cases hxs
  refine ⟨hx3, fun _ _ => ?_⟩
  have hT4 : ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1)))) =
      (ovSet fs (treeOf i s W3)).set x (.key ⟨wLevel s W3 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) := by
    rw [treeOf_withNode i s _ htx3, tso_ovSet_set hxfs]
    rfl
  have hT4r : treeOf i s (W3.withNode x (n.toPrev (i - 1))) =
      (treeOf i s W3).set x (.key ⟨wLevel s W3 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) :=
    treeOf_withNode i s _ htx3
  have hx3r : x ∉ reachAt (ovSet fs (treeOf i s W3))
      ((ovSet fs (treeOf i s W3)).fuel W3.top.rootKey) W3.top.rootKey := by
    intro hm
    rcases hcp.reach x hm with e | e
    · exact hxnot e
    · exact absurd (Nat.lt_of_lt_of_le hxnext (Nat.le_trans (Nat.le_add_right _ 2)
        (Nat.le_trans hW1next e))) (Nat.lt_irrefl x)
  have hsame4 : ∀ z, z ≠ x → (ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1))))).obj z =
      (ovSet fs (treeOf i s W3)).obj z := by
    intro z hz; rw [hT4]; simp [Tree.set, hz]
  have ha : ∀ z ∈ reachAt (ovSet fs (treeOf i s W3))
      ((ovSet fs (treeOf i s W3)).fuel W3.top.rootKey) W3.top.rootKey,
      (ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1))))).obj z =
        (ovSet fs (treeOf i s W3)).obj z :=
    fun z hz => hsame4 z (fun e => hx3r (e ▸ hz))
  have hs4 : ∀ z, ((ovSet fs (treeOf i s W3)).obj z).isSome = true →
      ((ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1))))).obj z).isSome = true := by
    intro z hz
    by_cases e : z = x
    · rw [e, hT4]; simp [Tree.set]
    · rw [hsame4 z e]; exact hz
  have hr3 : W3.top.rootKey ≠ x := fun e => hx3r (e ▸ tc_self _ _ _)
  have hR : reachAt (ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1)))))
      ((ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1))))).fuel W3.top.rootKey)
      W3.top.rootKey =
      reachAt (ovSet fs (treeOf i s W3)) ((ovSet fs (treeOf i s W3)).fuel W3.top.rootKey)
        W3.top.rootKey := by
    rw [show (ovSet fs (treeOf i s (W3.withNode x (n.toPrev (i - 1))))).fuel W3.top.rootKey =
      (ovSet fs (treeOf i s W3)).fuel W3.top.rootKey by simp only [Tree.fuel, hsame4 _ hr3]]
    exact reachAt_agree _ _ ha
  obtain ⟨hfst, htimes⟩ := tso_old hI3.books hx3 h.first hnt
  refine ⟨⟨?_, hI3.sound.agree ha hs4, frame_withNode hI3.frame hx3 htx3 rfl
      (ts_toPrev_ext hb hI3.frame hx3 htx3), hI3.top, ?_,
      putBooksE_withNode (n' := n.toPrev (i - 1)) hI3.books hx3 htx3 rfl (Or.inl hfst) htimes,
      tso_emp_withNode hI3.empties (tso_ne_of_head h.first hfst)⟩,
    ⟨hcp.path.trans hW1p, ?_, Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) hcp.next,
      ?_⟩⟩
  · rw [hT4r]; exact hI3.root
  · refine balancedAll_withNode hI3.balanced hx3 htx3 (rfl : (n.toPrev (i - 1)).leaf = n.leaf)
      (fun hl c y hy => ?_)
    obtain ⟨-, -, hk⟩ := hI3.balanced x _ (treeOf_obj_overlay i s hx3 htx3)
    exact hk hl c y (ts_key_mem_ksOf (ts_mem_toPrev hy))
  · intro y m hy hny
    have hyx : y ≠ x := fun e => hny (d + 1) c0 (Nat.le_refl _) (e ▸ hon)
    have := hcp.off y m (hW1n y m hy) (fun d' c hd' he => hny d' c (Nat.le_succ_of_le hd')
      (hW1p ▸ he))
    show (SIS.Tree.upsert W3.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact this
  · intro z hz
    have hz3 : z ∈ reachOfO i s fs W3 := by
      unfold reachOfO at hz ⊢
      rw [← hR]
      exact hz
    rcases hcp.reach z hz3 with e | e
    · rcases hreach z e with e' | e'
      · exact Or.inl e'
      · exact Or.inr (Nat.le_of_eq e'.symm)
    · exact Or.inr (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) e)


/-! ## 5. The statement -/

theorem handleFull_time_o {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {fs : List (NodeId × Obj)}
    {depth : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    {compact : Bool} (h : CasPreO p i base s tp fs w depth x n ins C)
    (hup : ∀ d, depth = d + 1 → UpOkO p i base s tp v fs up d)
    (hupn : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP (up q ins) { p := p, i := i, view := v } w (fun _ w' => w.next ≤ w'.next))
    (hcase : (compact = true ∧ n.size + ins.length + 1 ≤ p.M) ∨
      (compact = false ∧ (n.lastVersion i).size ≤ p.splitAbove)) :
    WP (SIS.Tree.handleFullWith up depth x ins (n.lastVersion i) compact)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w depth x n ins C) := by
  have hx := h.look
  obtain ⟨htx, -, -, hT, -, -⟩ := tso_wfacts hb h
  obtain ⟨g, hh, hg, -⟩ := h.books.levels x n hx htx
  obtain ⟨c0, hon⟩ := h.on
  have hspl : (!compact && decide ((n.lastVersion i).size > p.splitAbove)) = false := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, hle⟩
    · rfl
    · simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
      omega
  unfold SIS.Tree.handleFullWith
  rw [ts_wp_bind_ok (a := ({ p := p, i := i, view := v } : Ctx)) rfl]
  rw [ts_wp_bind_ok (getNode_hit _ hx)]
  rw [ts_wp_bind_ok (ghOf_hit _ hx hg)]
  cases hnt : (n.firstTime == some i)
  · have hnt' : n.firstTime ≠ some i := by simpa using hnt
    cases depth with
    | zero =>
      rw [ts_wp_bind_ok (parentAt_zero _ _)]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [ts_wp_bind_ok rfl]
      refine ts_wp_ite_note (fun T => ?_)
      refine tso_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (newSuperRoot_eq (s := s) (tp := tp) v _ ?_)).mpr ?_
      · exact hT
      refine (ts_wp_bind_ok (getNode_hit (n := n) _ ?_)).mpr ?_
      · rw [(afterSuperRoot_fields _ _ _ _).2.2.1]
        exact prim_lookup_append_some _ hx
      rw [ts_wp_ok (putNode_eq _ _ _ _)]
      exact tso_root hb h hnt' hg hrl hrwf hrs hrk hrf hrt _ _
    | succ d =>
      obtain ⟨c0', u0, k1, x', nu, e1, e2, -⟩ := h.path.links d (Nat.lt_succ_self d)
      rw [hon] at e2
      cases e2
      obtain ⟨nq, hqn, -⟩ := h.path.lookup (Nat.le_succ d) e1
      rw [ts_wp_bind_ok (parentAt_succ _ e1)]
      rw [ts_wp_bind_ok (getNode_hit _ hqn)]
      rw [ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      refine ts_wp_ite_note (fun T => ?_)
      refine tso_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (klongAt_eq (k := k1) (x := x) _ ?_)).mpr ?_
      · exact hon
      rw [wp_bind]
      by_cases hyfs : w.next ∈ fs.map (·.1)
      · refine WP.mono (hupn d rfl u0 [(k1, w.next)] _) (fun _ W3 h3 => ?_)
        intro _ W4 hrun _ hfs4
        have h34 := tso_bind (tso_getNode x) (fun m => tso_putNode x (m.toPrev (i - 1))) W3 () W4
          hrun
        rcases hfs4 w.next hyfs with e | e
        · exact absurd e (Nat.lt_irrefl _)
        · have h14 : w.next + 2 ≤ W4.next := Nat.le_trans h3 h34
          exact absurd (Nat.le_trans h14 e) (by omega)
      obtain ⟨hpre, hxnot, hreach⟩ := tso_parentPre hb h hyfs hg hrl hrwf hrs hrk hrf hrt e1 hqn
        hon ((w.next, x) :: w.madeFor) ("split.time1" :: T')
      refine WP.mono (hup d rfl u0 [(k1, w.next)] _ nq C hpre) (fun _ W3 hpost => ?_)
      by_cases hP3 : W3.outside = [] ∧ ∀ e ∈ fs.map (·.1), e < w.next + 2 ∨ W3.next ≤ e
      · obtain ⟨hI3, hcp⟩ := hpost hP3.1 hP3.2
        obtain ⟨hx3, hfin⟩ := tso_parentPost hb h hnt' hI3 hcp
          (fun y m hy => prim_lookup_append_some _ hy) rfl (Nat.le_refl _) hxnot hreach
        rw [ts_wp_bind_ok (getNode_hit _ hx3), ts_wp_ok (putNode_eq _ _ _ _)]
        exact hfin
      · intro _ W4 hrun hout4 hfs4
        have h34 := tso_bind (tso_getNode x) (fun m => tso_putNode x (m.toPrev (i - 1))) W3 () W4
          hrun
        refine absurd ⟨(ts_getNode_put_outside hrun).symm.trans hout4, fun e he => ?_⟩ hP3
        rcases hfs4 e he with e' | e'
        · exact Or.inl (Nat.lt_of_lt_of_le e' (Nat.le_add_right _ 2))
        · exact Or.inr (Nat.le_trans h34 e')
  · have hnt' : n.firstTime = some i := by simpa using hnt
    cases depth with
    | zero =>
      rw [ts_wp_bind_ok (parentAt_zero _ _), ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine tso_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact tso_inPlace hb h hnt' hrl hrwf hrs hrk hrf hrt _
    | succ d =>
      obtain ⟨c0', u0, -, -, -, e1, -⟩ := h.path.links d (Nat.lt_succ_self d)
      obtain ⟨nq, hqn, -⟩ := h.path.lookup (Nat.le_succ d) e1
      rw [ts_wp_bind_ok (parentAt_succ _ e1), ts_wp_bind_ok (getNode_hit _ hqn),
        ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine tso_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact tso_inPlace hb h hnt' hrl hrwf hrs hrk hrf hrt _

end Contract
