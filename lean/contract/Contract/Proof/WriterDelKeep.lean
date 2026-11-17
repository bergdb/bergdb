/-
The contract package (bergdb 030-16): a delete of a key of one segment whose
segment leaf keeps a live klong, or is the space root, for any parameters that
meet `ParamsOK`: the bitmap in every form (WriterDelBitmap.lean), then the
merges (`afterDelete`), given as `AfterOk`; with the merges off `AfterOk`
holds (`afterOk_off`). The delete keeps `MidP` (`putKv_del1_keep`).

The branches of `Dag.deleteUpward`: a noop (the key is not there); the leaf
keeps a live klong (the bitmap, then the merges); the leaf is the space root
and is emptied (the bitmap; the root is kept empty). The fourth, the upward
unlink of an emptied leaf below the space root, is not here (the premise
`hkeep` excludes it).
-/
import Contract.Proof.WriterDelBitmap

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-- The merges after a delete changed the node of segment g at height 0 on the
key [cv]'s path (`afterDelete [cv] g 0`) keep `PInv` and the keys. -/
def AfterOk (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal)
    (cv : Nat) : Prop :=
  ∀ (g : Nat) (w : MW) (C : List (Key × Nat)), PInv p i base s tp none C w →
    WP (SIS.Tree.afterDelete [cv] g 0) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → PInv p i base s tp none C w')

/-- With the merges off, `afterDelete` changes nothing. -/
theorem afterOk_off {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hmg : p.merges = false) (cv : Nat) : AfterOk p i base s tp v cv := by
  intro g w C hI
  unfold SIS.Tree.afterDelete
  refine wput_read ?_
  dsimp only
  simp only [hmg, Bool.false_eq_true, ↓reduceIte]
  rw [wp_pure]
  exact fun _ => hI

/-! ## No node outside the bounds is taken back

A step of the writer adds a node outside the bounds G and H to `outside`
(`newKey`) and never removes one: so a state with such a node is followed by
states with one. The merges after a delete (`afterDelete`) included. -/

/-- A step of the writer that leaves no node outside the bounds only if there
was none before it. -/
structure WdkGrow {α : Type} (f : SIS.Tree.M α) : Prop where
  out : ∀ c u, WP f c u (fun _ u' => u'.outside = [] → u.outside = [])

theorem wdk_grow_pure {α : Type} (a : α) : WdkGrow (pure a : SIS.Tree.M α) := by
  refine ⟨fun c u => ?_⟩
  rw [wp_pure]
  exact id

theorem wdk_grow_throw {α : Type} (e : String) : WdkGrow (throw e : SIS.Tree.M α) :=
  ⟨fun _ _ => wp_throw _ _ _ _⟩

theorem wdk_grow_bind {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β} (hf : WdkGrow f)
    (hg : ∀ a, WdkGrow (g a)) : WdkGrow (f >>= g) := by
  refine ⟨fun c u => ?_⟩
  rw [wp_bind]
  refine (hf.out c u).mono ?_
  intro a u1 h1
  refine ((hg a).out c u1).mono ?_
  intro _ u2 h2 ho
  exact h1 (h2 ho)

theorem wdk_grow_read : WdkGrow (read : SIS.Tree.M Ctx) := by
  refine ⟨fun c u => ?_⟩
  rw [wp_read]
  exact id

theorem wdk_grow_get : WdkGrow (MonadState.get : SIS.Tree.M MW) := by
  refine ⟨fun c u => ?_⟩
  rw [wp_get]
  exact id

theorem wdk_grow_ite {α : Type} (b : Prop) [Decidable b] {f g : SIS.Tree.M α} (hf : WdkGrow f)
    (hg : WdkGrow g) : WdkGrow (if b then f else g) :=
  ⟨fun c u => wp_ite _ _ _ _ _ _ (fun _ => hf.out c u) (fun _ => hg.out c u)⟩

theorem wdk_grow_modify (F : MW → MW) (hF : ∀ w, (F w).outside = [] → w.outside = []) :
    WdkGrow (modify F : SIS.Tree.M Unit) := by
  refine ⟨fun c u => ?_⟩
  rw [wp_modify]
  exact hF u

/-- A join point of the do notation: its body and the rest each so. -/
theorem wdk_grow_jp {γ α β : Type} {v : γ → SIS.Tree.M α}
    {b : (γ → SIS.Tree.M α) → SIS.Tree.M β}
    (hv : ∀ x, WdkGrow (v x)) (hb : ∀ jp : γ → SIS.Tree.M α, (∀ x, WdkGrow (jp x)) →
      WdkGrow (b jp)) : WdkGrow (have jp := v; b jp) :=
  hb v hv

/-- A join point, or a step given as a value, of two arguments. -/
theorem wdk_grow_jp2 {γ δ α β : Type} {v : γ → δ → SIS.Tree.M α}
    {b : (γ → δ → SIS.Tree.M α) → SIS.Tree.M β} (hv : ∀ x y, WdkGrow (v x y))
    (hb : ∀ jp : γ → δ → SIS.Tree.M α, (∀ x y, WdkGrow (jp x y)) → WdkGrow (b jp)) :
    WdkGrow (have jp := v; b jp) :=
  hb v hv

/-- Any other `have` or `let`: the rest so for every value. -/
theorem wdk_grow_let {γ β : Type} {v : γ} {b : γ → SIS.Tree.M β}
    (hb : ∀ x, WdkGrow (b x)) :
    WdkGrow (have x := v; b x) :=
  hb v

open Lean Elab Tactic Meta in
/-- A join point of the do notation: `wdk_grow_jp` with the join point's value
and body read from the goal; any other `have` or `let` by `wdk_grow_let`. -/
elab "wdk_jp" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``WdkGrow do throwError "wdk_jp: no WdkGrow goal"
  let .letE n t v b _ := tgt.appArg! | throwError "wdk_jp: no join point"
  let vs ← Term.exprToSyntax v
  let bs ← Term.exprToSyntax (Expr.lam n t b .default)
  evalTactic (← `(tactic| first
    | refine wdk_grow_jp (v := $vs) (b := $bs) ?_ ?_
    | refine wdk_grow_jp2 (v := $vs) (b := $bs) ?_ ?_
    | refine wdk_grow_let (v := $vs) (b := $bs) ?_))

open Lean Elab Tactic Meta in
/-- A goal `WdkGrow (f a)` closed by a local `∀ x, WdkGrow (f x)` (a join point's,
or the parent's step). -/
elab "wdk_hyp" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let isGrow ← forallTelescopeReducing ty fun _ concl => pure (concl.isAppOf ``WdkGrow)
    unless isGrow do continue
    let s ← saveState
    try
      let ds ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| with_reducible apply $ds))
      return
    catch _ => s.restore
  throwError "wdk_hyp: no hypothesis"

/-- One step of a proof of `WdkGrow`; extended below by each step proved. -/
syntax "wdk_step" : tactic
macro_rules
  | `(tactic| wdk_step) => `(tactic| first
      | wdk_jp
      | with_reducible exact wdk_grow_pure _
      | with_reducible exact wdk_grow_throw _
      | with_reducible exact wdk_grow_read
      | with_reducible exact wdk_grow_get
      | with_reducible exact wdk_grow_modify _ (fun _ h => h)
      | with_reducible exact wdk_grow_modify _ (fun _ h => by simp at h)
      | with_reducible apply wdk_grow_bind
      | with_reducible apply wdk_grow_ite
      | wdk_hyp
      | (intro _)
      | (dsimp -zeta only)
      | split)

theorem wdk_grow_note (t : String) : WdkGrow (SIS.Tree.note t) :=
  wdk_grow_modify _ (fun _ h => h)

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_note _)

theorem wdk_grow_fresh : WdkGrow SIS.Tree.fresh := by
  refine ⟨fun c u => ?_⟩
  unfold SIS.Tree.fresh
  rw [wp_bind, wp_get, wp_bind, wp_set, wp_pure]
  exact id

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_fresh)

theorem wdk_grow_getNode (x : NodeId) : WdkGrow (SIS.Tree.getNode x) := by
  refine ⟨fun c u => ?_⟩
  unfold SIS.Tree.getNode
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact id
  · refine wput_read ?_
    split
    · refine wp_ite _ _ _ _ _ _ (fun _ => wp_throw _ _ _ _) (fun _ => ?_)
      dsimp only
      rw [wp_bind, wp_set, wp_pure]
      exact id
    · exact wp_throw _ _ _ _

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_getNode _)

theorem wdk_grow_putNode (x : NodeId) (n : MNode) : WdkGrow (SIS.Tree.putNode x n) := by
  unfold SIS.Tree.putNode
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_putNode _ _)

theorem wdk_grow_ghOf (x : NodeId) : WdkGrow (SIS.Tree.ghOf x) := by
  unfold SIS.Tree.ghOf
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_ghOf _)

theorem wdk_grow_newKey (g h : Nat) (leaf : Bool) (ks : List MKlong) :
    WdkGrow (SIS.Tree.newKey g h leaf ks) := by
  unfold SIS.Tree.newKey
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_newKey _ _ _ _)

theorem wdk_grow_setMadeFor (m : NodeId) (o : Option NodeId) :
    WdkGrow (SIS.Tree.setMadeFor m o) := by
  unfold SIS.Tree.setMadeFor
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_setMadeFor _ _)

theorem wdk_grow_replacedBy (x : NodeId) : WdkGrow (SIS.Tree.replacedBy x) := by
  unfold SIS.Tree.replacedBy
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_replacedBy _)

theorem wdk_grow_takenBack (x : NodeId) : WdkGrow (SIS.Tree.takenBack x) := by
  unfold SIS.Tree.takenBack
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_takenBack _)

theorem wdk_grow_pathClear : WdkGrow SIS.Tree.pathClear := by
  unfold SIS.Tree.pathClear
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_pathClear)

theorem wdk_grow_pathAdd (k : Option Nat) (x : NodeId) : WdkGrow (SIS.Tree.pathAdd k x) := by
  unfold SIS.Tree.pathAdd
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_pathAdd _ _)

theorem wdk_grow_pathSize : WdkGrow SIS.Tree.pathSize := by
  unfold SIS.Tree.pathSize
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_pathSize)

theorem wdk_grow_pathNode (d : Nat) : WdkGrow (SIS.Tree.pathNode d) := by
  unfold SIS.Tree.pathNode
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_pathNode _)

theorem wdk_grow_klongAt (d : Nat) : WdkGrow (SIS.Tree.klongAt d) := by
  unfold SIS.Tree.klongAt
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_klongAt _)

theorem wdk_grow_parentAt (d : Nat) : WdkGrow (SIS.Tree.parentAt d) := by
  unfold SIS.Tree.parentAt
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_parentAt _)

theorem wdk_grow_newSuperRoot (y : NodeId) : WdkGrow (SIS.Tree.newSuperRoot y) := by
  refine ⟨fun c u => ?_⟩
  unfold SIS.Tree.newSuperRoot
  refine wput_read ?_
  rw [wp_bind, wp_get]
  refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · rw [wp_bind, wp_set]
    exact ((wdk_grow_note _).out c _).mono (fun _ _ h ho => h ho)
  · refine WdkGrow.out ?_ c u
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_newSuperRoot _)

theorem wdk_grow_findRoot : WdkGrow SIS.Tree.findRoot := by
  unfold SIS.Tree.findRoot
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_findRoot)

theorem wdk_grow_foldlM {α β : Type} (f : β → α → SIS.Tree.M β)
    (hf : ∀ b a, WdkGrow (f b a)) :
    ∀ (l : List α) (b : β), WdkGrow (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact wdk_grow_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact wdk_grow_bind (hf b a) (fun b' => wdk_grow_foldlM f hf l b')

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible apply wdk_grow_foldlM)

theorem wdk_grow_forIn {α β : Type} (f : α → β → SIS.Tree.M (ForInStep β))
    (hf : ∀ a b, WdkGrow (f a b)) : ∀ (l : List α) (b : β), WdkGrow (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact wdk_grow_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine wdk_grow_bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact wdk_grow_pure b'
    | yield b' => exact wdk_grow_forIn f hf l b'

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible apply wdk_grow_forIn)

theorem wdk_grow_addKeys (x : NodeId) (ins : List (Nat × NodeId)) :
    WdkGrow (SIS.Tree.addKeys x ins) := by
  unfold SIS.Tree.addKeys
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_addKeys _ _)

theorem wdk_grow_replaceOrAdd (last : MNode) (ins : List (Nat × NodeId)) :
    WdkGrow (SIS.Tree.replaceOrAdd last ins) := by
  unfold SIS.Tree.replaceOrAdd
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_replaceOrAdd _ _)

theorem wdk_grow_handleFullWith {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hup : ∀ q l, WdkGrow (up q l)) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (last : MNode) (compact : Bool) :
    WdkGrow (SIS.Tree.handleFullWith up depth x ins last compact) := by
  unfold SIS.Tree.handleFullWith
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible apply wdk_grow_handleFullWith)

theorem wdk_grow_appendKlongs :
    ∀ (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)),
      WdkGrow (SIS.Tree.appendKlongs depth x ins) := by
  intro depth
  induction depth with
  | zero =>
    intro x ins
    rw [wput_appendKlongs_eq]
    repeat wdk_step
  | succ d ih =>
    intro x ins
    rw [wput_appendKlongs_eq]
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_appendKlongs _ _ _)

theorem wdk_grow_handleFull (depth : Nat) (x : NodeId) (last : MNode) (compact : Bool) :
    WdkGrow (SIS.Tree.handleFull depth x last compact) := by
  unfold SIS.Tree.handleFull
  refine wdk_grow_handleFullWith ?_ _ _ _ _ _
  intro q l
  cases depth with
  | zero => exact wdk_grow_throw _
  | succ d => exact wdk_grow_appendKlongs d q l

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_handleFull _ _ _ _)

theorem wdk_grow_unlink (x : NodeId) : WdkGrow (SIS.Tree.unlink x) := by
  unfold SIS.Tree.unlink
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_unlink _)

theorem wdk_grow_retarget (q src dst : NodeId) : WdkGrow (SIS.Tree.retarget q src dst) := by
  unfold SIS.Tree.retarget
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_retarget _ _ _)

theorem wdk_grow_descendLte (cv : Nat) : ∀ (f : Nat) (x : NodeId),
    WdkGrow (SIS.Tree.descendLte cv f x) := by
  intro f
  induction f with
  | zero =>
    intro x
    rw [wput_descend_zero]
    exact wdk_grow_throw _
  | succ f ih =>
    intro x
    rw [wput_descend_succ]
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_descendLte _ _ _)

theorem wdk_grow_descendToSegmentRoot (key : Key) (segment : Nat) :
    WdkGrow (SIS.Tree.descendToSegmentRoot key segment) := by
  unfold SIS.Tree.descendToSegmentRoot
  repeat wdk_step

macro_rules
  | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_descendToSegmentRoot _ _)

theorem wdk_grow_takeBackRoot (x : NodeId) (depth only : Nat) :
    WdkGrow (SIS.Tree.takeBackRoot x depth only) := by
  unfold SIS.Tree.takeBackRoot
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_takeBackRoot _ _ _)

theorem wdk_grow_replaceRoot (x : NodeId) (depth only : Nat) :
    WdkGrow (SIS.Tree.replaceRoot x depth only) := by
  unfold SIS.Tree.replaceRoot
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_replaceRoot _ _ _)

theorem wdk_grow_collapseRoot (key : Key) (segment : Nat) : ∀ fuel : Nat,
    WdkGrow (SIS.Tree.collapseRoot key segment fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    rw [SIS.Tree.collapseRoot.eq_1]
    exact wdk_grow_throw _
  | succ f ih =>
    rw [SIS.Tree.collapseRoot.eq_2]
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_collapseRoot _ _ _)

theorem wdk_grow_descendHeight (cv h : Nat) : ∀ (f : Nat) (x : NodeId),
    WdkGrow (SIS.Tree.descendHeight cv h f x) := by
  intro f
  induction f with
  | zero =>
    intro x
    rw [SIS.Tree.descendHeight.eq_1]
    exact wdk_grow_throw _
  | succ f ih =>
    intro x
    rw [SIS.Tree.descendHeight.eq_2]
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_descendHeight _ _ _ _)

theorem wdk_grow_descendToHeight (key : Key) (g h : Nat) :
    WdkGrow (SIS.Tree.descendToHeight key g h) := by
  unfold SIS.Tree.descendToHeight
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_descendToHeight _ _ _)

theorem wdk_grow_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : WdkGrow (SIS.Tree.mergeParent q depth il cL m1 ir cR m2) := by
  unfold SIS.Tree.mergeParent
  repeat wdk_step

macro_rules
  | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_mergeParent _ _ _ _ _ _ _ _)

theorem wdk_grow_sibling (q : NodeId) (pn : MNode) (i : Nat) (inner : Bool) :
    WdkGrow (SIS.Tree.sibling q pn i inner) := by
  unfold SIS.Tree.sibling
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_sibling _ _ _ _)

theorem wdk_grow_merge (x : NodeId) (d : Nat) : WdkGrow (SIS.Tree.merge x d) := by
  unfold SIS.Tree.merge
  repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_merge _ _)

theorem wdk_grow_mergeUp (key : Key) (g : Nat) : ∀ (f h : Nat) (merged : Bool),
    WdkGrow (SIS.Tree.mergeUp key g f h merged) := by
  intro f
  induction f with
  | zero =>
    intro h merged
    rw [SIS.Tree.mergeUp.eq_1]
    exact wdk_grow_throw _
  | succ f ih =>
    intro h merged
    rw [SIS.Tree.mergeUp.eq_2]
    repeat wdk_step

macro_rules | `(tactic| wdk_step) => `(tactic| with_reducible exact wdk_grow_mergeUp _ _ _ _ _)

theorem wdk_grow_afterDelete (key : Key) (g h : Nat) :
    WdkGrow (SIS.Tree.afterDelete key g h) := by
  unfold SIS.Tree.afterDelete
  repeat wdk_step

/-! ## The delete's steps -/

/-- The leaf's `DelVirt`: the state with the segment leaf set to a node V with
the leaf's live klongs but those of cv meets `PInv` with the leaf maybe over its
size and holds the keys with the delete (`Sound.del`), if the leaf keeps a live
klong or is the space root. -/
theorem wdk_fact {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {w : MW} {leaf : NodeId} {nl : MNode} {cv : Nat}
    (hI : PInv p i base s tp none C w) (hlk : w.nodes.lookup leaf = some nl)
    (ht : w.taken.contains leaf = false) (hl : nl.leaf = true)
    (hr : Route (treeOf i s w) w.top.rootKey [cv] leaf [cv]) (hcv : isLong cv = false)
    (hkeep : dropCv cv (live (ksOf nl)) ≠ [] ∨ leaf = w.top.rootKey) :
    DelVirt p i base s tp w leaf nl cv (mapDel [cv] C) := by
  intro n' hleaf hlive hwf hsz hkey hfst htimes hext
  have hAx := treeOf_obj_overlay i s hlk ht
  have hreach := (hr.tc_target hI.sound.good).2
  have hok := hI.sound.nodes leaf hreach _ hAx
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨⟨hlen, -⟩, hptr⟩ := hok
  have hTW : treeOf i s (w.withNode leaf n') =
      (treeOf i s w).set leaf (.key ⟨wLevel s w leaf, n'.leaf, ksOf n'⟩) :=
    treeOf_withNode i s n' ht
  refine ⟨hI.root, ?_, frame_withNode hI.frame hlk ht hleaf hext, hI.top, ?_,
    putBooks_withNode hI.books hlk ht hleaf hfst (timesLe_model htimes)⟩
  · refine (Sound.del (ex' := some leaf) hI.sound hr hAx hl hcv hkeep ?_ ?_).1
    · refine ⟨⟨wLevel s w leaf, n'.leaf, ksOf n'⟩, ?_, rfl, by rw [hleaf]; exact hl, hlive,
        ?_⟩
      · rw [hTW]
        simp [Tree.set]
      · simp only [bnd, ite_true, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true]
        refine ⟨⟨?_, hwf⟩, fun k hk => ?_⟩
        · rw [ksOf_length] at hlen ⊢
          omega
        cases k with
        | key c y =>
          rw [hTW]
          exact wput_set_isSome (hptr _ (hkey c y hk))
        | time t => rfl
        | del b => rfl
    · intro z hz
      rw [hTW]
      simp [Tree.set, hz]
  · refine balancedAll_withNode hI.balanced hlk ht hleaf (fun hl' => ?_)
    rw [hleaf, hl] at hl'
    cases hl'

/-- `putKv` of a delete of the key [cv]: as `wdel_putKv`, for a `deleteUpward`
that keeps `PInv` when it leaves no key node outside the bounds. -/
theorem wdk_putKv {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {done : List Op} {w : MW} {cv : Nat} (hm : MidP p i base s tp done w)
    (hdel : ∀ (leaf : NodeId) (w3 : MW) (nl : MNode),
      PInv p i base s tp none (applyOps done (contents s)) w3 →
      w3.nodes.lookup leaf = some nl → w3.taken.contains leaf = false → nl.leaf = true →
      (∃ c0, w3.path[w3.path.length - 1]? = some (c0, leaf)) →
      PathOk i s w3 (w3.path.length - 1) → PathInner w3 (w3.path.length - 1) →
      Route (treeOf i s w3) w3.top.rootKey [cv] leaf [cv] →
      treeOf i s w3 = treeOf i s w → w3.top = w.top →
      WP (SIS.Tree.deleteUpward leaf (w3.path.length - 1) cv [cv])
        { p := p, i := i, view := v } w3
        (fun _ w4 => w4.outside = [] →
          PInv p i base s tp none (mapDel [cv] (applyOps done (contents s))) w4)) :
    WP (SIS.Tree.putKv (.del [cv])) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → MidP p i base s tp (done ++ [Op.del [cv]]) w') := by
  have hC : applyOps (done ++ [Op.del [cv]]) (contents s) =
      mapDel [cv] (applyOps done (contents s)) := by
    rw [applyOps, List.foldl_append]
    rfl
  simp only [MidP, hC]
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  rw [SIS.Tree.putSegs.eq_2]
  unfold SIS.Tree.setValue
  refine wput_read ?_
  rw [wp_bind]
  refine (wput_descend_root (cv := cv) hs hb (w := { w with path := [(none, w.top.rootKey)] })
    (hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl _).mono ?_
  rintro leaf (w3 : MW) ⟨hT3, htop3, hI3, ⟨nl, hlk3, hl3⟩, hc0, hP3, hin3, hr3⟩
  dsimp only
  obtain ⟨c0, hc0'⟩ := hc0
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0'
  refine wput_ok (pathSize_eq _ _) ?_
  rw [wp_bind]
  refine (hdel leaf w3 nl hI3 hlk3 ht3 hl3 ⟨c0, hc0'⟩ hP3 hin3 hr3 hT3 htop3).mono ?_
  intro noop w4 h4
  split
  · refine wput_ok (f := SIS.Tree.fresh) (a := w4.next) (w' := { w4 with next := w4.next + 2 })
      rfl ?_
    rw [wp_pure]
    exact fun ho => wdel_pinv_next (h4 ho)
  · rw [wp_pure]
    exact h4

/-- `deleteUpward` of the segment leaf that the key [cv] is routed to, at depth
d of the key access path, which keeps a live klong or is the space root: a
noop; the bitmap, then the merges; or the space root emptied and kept. -/
theorem wdk_core {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {C : List (Key × Nat)}
    {cv : Nat} (hcv : isLong cv = false) (hafter : AfterOk p i base s tp v cv)
    (hgrow : ∀ g (u : MW), WP (SIS.Tree.afterDelete [cv] g 0) { p := p, i := i, view := v } u
      (fun _ u' => u'.outside = [] → u.outside = []))
    {w3 : MW} {leaf : NodeId} {nl : MNode} {d : Nat}
    (hI3 : PInv p i base s tp none C w3) (hlk3 : w3.nodes.lookup leaf = some nl)
    (ht3 : w3.taken.contains leaf = false) (hl3 : nl.leaf = true)
    (hon : ∃ c0, w3.path[d]? = some (c0, leaf))
    (hP3 : PathOk i s w3 d) (hin3 : PathInner w3 d)
    (hr3 : Route (treeOf i s w3) w3.top.rootKey [cv] leaf [cv])
    (hkeep : dropCv cv (live (ksOf nl)) ≠ [] ∨ leaf = w3.top.rootKey) :
    WP (SIS.Tree.deleteUpward leaf d cv [cv]) { p := p, i := i, view := v } w3
      (fun _ w4 => w4.outside = [] → PInv p i base s tp none (mapDel [cv] C) w4) := by
  have hAx := treeOf_obj_overlay i s hlk3 ht3
  have hreach := (hr3.tc_target hI3.sound.good).2
  have hok := hI3.sound.nodes leaf hreach _ hAx
  have hok' := hok
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  have hwf0 : klongsWf (ksOf nl) = true := hok'.1.2
  have hsz0 : nl.size ≤ p.M := by rw [← ksOf_length]; exact hok'.1.1
  have hV := wdk_fact hI3 hlk3 ht3 hl3 hr3 hcv hkeep
  unfold SIS.Tree.deleteUpward
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk3) ?_
  dsimp only
  split
  · next hno =>
    rw [wp_pure]
    intro _
    have hsame := delUnion_noop hwf0 hno
    exact ⟨hI3.root, (Sound.del hI3.sound hr3 hAx hl3 hcv hkeep
      ⟨_, hAx, rfl, hl3, hsame.symm, hok⟩ (fun _ _ => rfl)).1, hI3.frame, hI3.top,
      hI3.balanced, hI3.books⟩
  · next hnn =>
    have hno : (delUnion nl cv == nl.lastBitmap) = false := by
      cases h : (delUnion nl cv == nl.lastBitmap)
      · rfl
      · exact absurd h hnn
    split
    · -- the leaf keeps a live klong: the bitmap, then the merges
      obtain ⟨g, h, hgh, -, -, -, hlh⟩ := hI3.books.levels leaf nl hlk3 ht3
      have h0 : h = 0 := by
        rw [hl3] at hlh
        simpa using hlh.symm
      subst h0
      refine wput_ok (ghOf_hit _ hlk3 hgh) ?_
      rw [wp_bind]
      dsimp only
      refine (wdb_spec hp hb hlk3 hon hP3 hin3 hI3.books hwf0 hsz0 hI3.root hI3.frame hI3.top
        hI3.balanced hno hV).mono ?_
      rintro _ w4 ⟨-, h4⟩
      rw [wp_bind]
      by_cases ho4 : w4.outside = []
      · refine (hafter g w4 _ (h4 ho4).1).mono ?_
        intro _ w5 h5
        rw [wp_pure]
        exact h5
      · refine (hgrow g w4).mono ?_
        intro _ w5 h5
        rw [wp_pure]
        exact fun ho5 => absurd (h5 ho5) ho4
    · next hall =>
      -- the leaf is emptied: it is the space root, kept empty
      have hlr : leaf = w3.top.rootKey := by
        refine hkeep.resolve_left (fun hne => hne ?_)
        exact (allKeysIn_iff hwf0 cv).mp (by simpa [delUnion] using hall)
      have hd : d = 0 := by
        by_contra hd
        have := hin3 0 none w3.top.rootKey nl (by omega) hP3.root (by rw [← hlr]; exact hlk3)
        rw [hl3] at this
        cases this
      subst hd
      obtain ⟨c0, hc0⟩ := hon
      rw [wp_bind]
      unfold SIS.Tree.climb
      refine wput_read ?_
      refine wput_ok (pathNode_eq _ hc0) ?_
      refine wput_ok (getNode_hit _ hlk3) ?_
      dsimp only
      refine wp_ite _ _ _ _ _ _ (fun hbad => absurd hbad (by simp [hl3])) (fun _ => ?_)
      rw [wp_pure]
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun hne => absurd rfl hne)
      refine wput_ok (note_eq _ _ _) ?_
      rw [wp_bind]
      have hu := wdb_spec (v := v) (w := { w3 with trail := "up.root-kept-empty" :: w3.trail })
        (depth := 0) hp hb hlk3 ⟨c0, hc0⟩
        (hP3.congr rfl rfl rfl rfl (treeOf_congr i s rfl rfl rfl rfl rfl rfl)) hin3
        (putBooks_congr hI3.books rfl rfl rfl rfl rfl rfl rfl rfl rfl) hwf0 hsz0 hI3.root
        hI3.frame hI3.top hI3.balanced hno
        (wdk_fact (hI3.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) hlk3 ht3 hl3 hr3 hcv hkeep)
      refine hu.mono ?_
      rintro _ w4 ⟨-, h4⟩
      rw [wp_pure]
      exact fun ho => (h4 ho).1

/-! ## The delete -/

/-- A delete of the key [cv] whose segment leaf keeps a live klong or is the space
root keeps `MidP`, given that the merges keep `PInv`. -/
theorem putKv_del1_keep {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) {done : List Op} {w w' : MW} {b : Bool} {cv : Nat}
    (hm : MidP p i base s tp done w) (hcv : isLong cv = false)
    (hafter : AfterOk p i base s tp v cv)
    (hkeep : ∀ leaf nl, Route (treeOf i s w) w.top.rootKey [cv] leaf [cv] →
      (treeOf i s w).obj leaf = some (.key nl) → nl.leaf = true →
      (live nl.ks).filter (fun a => a.1 != cv) ≠ [] ∨ leaf = w.top.rootKey)
    (hrun : SIS.Tree.putKv (.del [cv]) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) :
    MidP p i base s tp (done ++ [Op.del [cv]]) w' := by
  refine wdk_putKv hs hb hm (fun leaf w3 nl hI3 hlk3 ht3 hl3 hc0 hP3 hin3 hr3 hT3 htop3 => ?_)
    b w' hrun hout
  have hAx := treeOf_obj_overlay i s hlk3 ht3
  have hk := hkeep leaf _ (by rw [← hT3, ← htop3]; exact hr3) (by rw [← hT3]; exact hAx) hl3
  refine wdk_core hp hb hcv hafter (fun g u => (wdk_grow_afterDelete _ g 0).out _ u) hI3 hlk3
    ht3 hl3 hc0 hP3 hin3 hr3 ?_
  rcases hk with hk | hk
  · exact Or.inl hk
  · right
    rw [htop3]
    exact hk

/-- With the merges off: the delete of `putKv_del1_keep` keeps `MidP`. -/
theorem putKv_del1_keep_off {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) {done : List Op} {w w' : MW} {b : Bool} {cv : Nat}
    (hm : MidP p i base s tp done w) (hcv : isLong cv = false) (hmg : p.merges = false)
    (hkeep : ∀ leaf nl, Route (treeOf i s w) w.top.rootKey [cv] leaf [cv] →
      (treeOf i s w).obj leaf = some (.key nl) → nl.leaf = true →
      (live nl.ks).filter (fun a => a.1 != cv) ≠ [] ∨ leaf = w.top.rootKey)
    (hrun : SIS.Tree.putKv (.del [cv]) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) :
    MidP p i base s tp (done ++ [Op.del [cv]]) w' :=
  putKv_del1_keep hp hs hb hm hcv (afterOk_off hmg cv) hkeep hrun hout

end Contract
