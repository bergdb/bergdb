/-
The contract package (bergdb 030-10): the put whole. The recursion up the key
access path while a new segment leaf has no klong yet (`appendKlongs_spec_o`,
from the `O` forms of `handleFullWith`); the put that makes new segment
leaves where the segment leaf above is full (`putKv_put_newseg_full`); then
any put of a key as `Keys.toSegments` makes it keeps `MidP` (`putKv_put`), a
transaction of puts meets the writer's contract (`writerMeets_put`), and a
run of such transactions is a history that meets `MeetsTop`
(`runs_meetsTop_put`).
-/
import Contract.Proof.WriterPutSeg
import Contract.Proof.WriterTimeSplitO
import Contract.Proof.WriterSpaceSplitO

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. What every step keeps

Every step of the writer keeps or raises the next id, keeps the nodes taken
back (no step of a put takes a node back), only adds to the nodes made, and
only adds to `outside`. -/

/-- The state w' after a step from w. -/
def WStep (w w' : MW) : Prop :=
  w.next ≤ w'.next ∧ w'.taken = w.taken ∧ (w'.outside = [] → w.outside = []) ∧
    w.made <+: w'.made

theorem WStep.refl (w : MW) : WStep w w :=
  ⟨Nat.le_refl _, rfl, id, List.prefix_refl _⟩

theorem WStep.trans {w1 w2 w3 : MW} (h1 : WStep w1 w2) (h2 : WStep w2 w3) : WStep w1 w3 :=
  ⟨Nat.le_trans h1.1 h2.1, h2.2.1.trans h1.2.1, fun h => h1.2.2.1 (h2.2.2.1 h),
    h1.2.2.2.trans h2.2.2.2⟩

/-- Every result of the step is a `WStep` from where it starts. -/
def StepOk (c : SIS.Tree.Ctx) {α : Type} (f : SIS.Tree.M α) : Prop :=
  ∀ w : MW, WP f c w (fun _ w' => WStep w w')

theorem so_bind {c : SIS.Tree.Ctx} {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β}
    (hf : StepOk c f) (hg : ∀ a, StepOk c (g a)) : StepOk c (f >>= g) := by
  intro w
  rw [wp_bind]
  intro a w1 h1 b w2 h2
  exact (hf w a w1 h1).trans (hg a w1 b w2 h2)

theorem so_pure {c : SIS.Tree.Ctx} {α : Type} (a : α) : StepOk c (pure a) := by
  intro w
  rw [wp_pure]
  exact WStep.refl w

theorem so_throw {c : SIS.Tree.Ctx} {α : Type} (e : String) :
    StepOk c (throw e : SIS.Tree.M α) :=
  fun w => wp_throw e c w _

theorem so_read {c : SIS.Tree.Ctx} : StepOk c (read : SIS.Tree.M SIS.Tree.Ctx) := by
  intro w
  rw [wp_read]
  exact WStep.refl w

theorem so_ok {c : SIS.Tree.Ctx} {α : Type} {f : SIS.Tree.M α}
    (h : ∀ w, ∃ a w', f c w = .ok (a, w') ∧ WStep w w') : StepOk c f := by
  intro w
  obtain ⟨a, w', hr, hn⟩ := h w
  intro r v hv
  rw [hr] at hv
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact hn

theorem so_note {c : SIS.Tree.Ctx} (t : String) : StepOk c (SIS.Tree.note t) :=
  so_ok fun w => ⟨_, _, note_eq c w t, WStep.refl w⟩

theorem so_putNode {c : SIS.Tree.Ctx} (x : NodeId) (n : MNode) :
    StepOk c (SIS.Tree.putNode x n) :=
  so_ok fun w => ⟨_, _, putNode_eq c w x n, WStep.refl w⟩

theorem so_setMadeFor {c : SIS.Tree.Ctx} (m : NodeId) (o : Option NodeId) :
    StepOk c (SIS.Tree.setMadeFor m o) := by
  cases o with
  | none => exact so_ok fun w => ⟨_, _, setMadeFor_none c w m, WStep.refl w⟩
  | some o => exact so_ok fun w => ⟨_, _, setMadeFor_some c w m o, WStep.refl w⟩

theorem so_replacedBy {c : SIS.Tree.Ctx} (x : NodeId) : StepOk c (SIS.Tree.replacedBy x) :=
  so_ok fun w => ⟨_, _, replacedBy_eq c w x, WStep.refl w⟩

theorem so_newKey {c : SIS.Tree.Ctx} (g h : Nat) (leaf : Bool) (ks : List MKlong) :
    StepOk c (SIS.Tree.newKey g h leaf ks) := by
  refine so_ok fun w => ⟨_, _, newKey_eq c w g h leaf ks, Nat.le_add_right _ 2, rfl, ?_,
    List.prefix_append _ _⟩
  intro ho
  simp only [MW.afterNewKey] at ho
  split at ho
  · cases ho
  · exact ho

theorem so_newValue {c : SIS.Tree.Ctx} (h : Nat) : StepOk c (SIS.Tree.newValue h) :=
  so_ok fun w => ⟨_, _, newValue_eq c w h, Nat.le_add_right _ 2, rfl, id,
    List.prefix_append _ _⟩

theorem so_newSuperRoot {c : SIS.Tree.Ctx} (y : NodeId) :
    StepOk c (SIS.Tree.newSuperRoot y) := by
  refine so_ok fun w => ?_
  by_cases hi : c.i = w.top.time
  · exact ⟨_, _, newSuperRoot_inPlace_eq c w y hi, WStep.refl w⟩
  · exact ⟨_, _, newSuperRoot_new_eq c w y hi, Nat.le_add_right _ 2, rfl, id,
      List.prefix_append _ _⟩

theorem so_modify {c : SIS.Tree.Ctx} {f : MW → MW} (hf : ∀ w, WStep w (f w)) :
    StepOk c (modify f : SIS.Tree.M Unit) := by
  intro w
  rw [wp_modify]
  exact hf w

theorem so_getNode {c : SIS.Tree.Ctx} (x : NodeId) : StepOk c (SIS.Tree.getNode x) := by
  intro W
  unfold SIS.Tree.getNode
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact WStep.refl W
  · rw [wp_bind, wp_read]
    split
    · split
      · exact wp_throw _ _ _ _
      · rw [wp_bind, wp_set, wp_pure]
        exact WStep.refl W
    · exact wp_throw _ _ _ _

theorem so_ghOf {c : SIS.Tree.Ctx} (x : NodeId) : StepOk c (SIS.Tree.ghOf x) := by
  unfold SIS.Tree.ghOf
  refine so_bind (so_getNode x) (fun _ W => ?_)
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact WStep.refl W
  · exact wp_throw _ _ _ _

theorem so_pathNode {c : SIS.Tree.Ctx} (d : Nat) : StepOk c (SIS.Tree.pathNode d) := by
  intro W
  unfold SIS.Tree.pathNode
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact WStep.refl W
  · exact wp_throw _ _ _ _

theorem so_parentAt {c : SIS.Tree.Ctx} (d : Nat) : StepOk c (SIS.Tree.parentAt d) := by
  cases d with
  | zero => exact so_ok fun w => ⟨_, _, parentAt_zero c w, WStep.refl w⟩
  | succ e =>
    unfold SIS.Tree.parentAt
    exact so_bind (so_pathNode e) (fun _ => so_pure _)

theorem so_klongAt {c : SIS.Tree.Ctx} (d : Nat) : StepOk c (SIS.Tree.klongAt d) := by
  intro W
  unfold SIS.Tree.klongAt
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact WStep.refl W
  · exact wp_throw _ _ _ _

theorem so_pathAdd {c : SIS.Tree.Ctx} (k : Option Nat) (x : NodeId) :
    StepOk c (SIS.Tree.pathAdd k x) :=
  so_ok fun w => ⟨_, _, pathAdd_eq c w k x, WStep.refl w⟩

theorem so_pathSize {c : SIS.Tree.Ctx} : StepOk c SIS.Tree.pathSize :=
  so_ok fun w => ⟨_, _, pathSize_eq c w, WStep.refl w⟩

theorem so_foldlM {c : SIS.Tree.Ctx} {α β : Type} (F : β → α → SIS.Tree.M β)
    (hF : ∀ b a, StepOk c (F b a)) : ∀ (l : List α) (b : β), StepOk c (l.foldlM F b)
  | [], b => so_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact so_bind (hF b a) (fun b' => so_foldlM F hF l b')

theorem so_replaceOrAdd {c : SIS.Tree.Ctx} (last : MNode) (ins : List (Nat × NodeId)) :
    StepOk c (SIS.Tree.replaceOrAdd last ins) := by
  unfold SIS.Tree.replaceOrAdd
  refine so_bind so_read (fun c' => so_foldlM _ (fun b a => ?_) _ _)
  obtain ⟨cv, y⟩ := a
  dsimp only
  split
  · exact so_throw _
  · exact so_pure _
  · exact so_pure _

/-- `handleFullWith` is a `WStep`, if `up` is. -/
theorem so_handleFullWith {c : SIS.Tree.Ctx}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit} (hup : ∀ q ins, StepOk c (up q ins))
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : MNode) (compact : Bool) :
    StepOk c (SIS.Tree.handleFullWith up depth x ins last compact) := by
  unfold SIS.Tree.handleFullWith
  dsimp only
  repeat (first
    | with_reducible exact so_pure _
    | with_reducible exact so_throw _
    | with_reducible exact so_read
    | with_reducible exact so_getNode _
    | with_reducible exact so_ghOf _
    | with_reducible exact so_parentAt _
    | with_reducible exact so_klongAt _
    | with_reducible exact so_note _
    | with_reducible exact so_putNode _ _
    | with_reducible exact so_setMadeFor _ _
    | with_reducible exact so_replacedBy _
    | with_reducible exact so_newKey _ _ _ _
    | with_reducible exact so_newSuperRoot _
    | with_reducible exact so_replaceOrAdd _ _
    | with_reducible exact hup _ _
    | with_reducible exact so_modify (fun _ => WStep.refl _)
    | with_reducible refine so_bind ?_ (fun _ => ?_)
    | split)

/-- `appendKlongs` is a `WStep`. -/
theorem so_appendKlongs (c : SIS.Tree.Ctx) (d : Nat) :
    ∀ q ins, StepOk c (SIS.Tree.appendKlongs d q ins) := by
  induction d with
  | zero =>
    intro q ins
    rw [show SIS.Tree.appendKlongs 0 q ins = _ from wput_appendKlongs_eq 0 q ins]
    refine so_bind so_read (fun c' => so_bind (so_getNode q) (fun n => ?_))
    dsimp only
    split
    · exact so_handleFullWith (fun _ _ => so_throw _) _ _ _ _ _
    · split
      · exact so_handleFullWith (fun _ _ => so_throw _) _ _ _ _ _
      · unfold SIS.Tree.addKeys
        exact so_bind so_read (fun _ => so_bind (so_getNode q) (fun _ => so_putNode _ _))
  | succ d ih =>
    intro q ins
    rw [show SIS.Tree.appendKlongs (d + 1) q ins = _ from wput_appendKlongs_eq (d + 1) q ins]
    refine so_bind so_read (fun c' => so_bind (so_getNode q) (fun n => ?_))
    dsimp only
    split
    · exact so_handleFullWith (fun q' ins' => ih q' ins') _ _ _ _ _
    · split
      · exact so_handleFullWith (fun q' ins' => ih q' ins') _ _ _ _ _
      · unfold SIS.Tree.addKeys
        exact so_bind so_read (fun _ => so_bind (so_getNode q) (fun _ => so_putNode _ _))

theorem so_descendLte (c : SIS.Tree.Ctx) (cv : Nat) :
    ∀ f x, StepOk c (SIS.Tree.descendLte cv f x)
  | 0, x => by
    rw [wput_descend_zero]
    exact so_throw _
  | f + 1, x => by
    rw [wput_descend_succ]
    refine so_bind so_read (fun c' => so_bind (so_getNode x) (fun n => ?_))
    split
    · exact so_pure _
    · split
      · exact so_throw _
      · exact so_bind (so_pathAdd _ _) (fun _ => so_descendLte c cv f _)

theorem so_setNode (c : SIS.Tree.Ctx) (segRoot cv : Nat) (create : Bool) :
    StepOk c (SIS.Tree.setNode segRoot cv create) := by
  unfold SIS.Tree.setNode
  refine so_bind so_read (fun c' => so_bind (so_descendLte _ _ _ _) (fun cur =>
    so_bind (so_getNode cur) (fun n => ?_)))
  dsimp only
  repeat (first
    | with_reducible exact so_pure _
    | with_reducible exact so_throw _
    | with_reducible exact so_ghOf _
    | with_reducible exact so_note _
    | with_reducible exact so_putNode _ _
    | with_reducible exact so_newKey _ _ _ _
    | with_reducible exact so_pathAdd _ _
    | with_reducible exact so_pathSize
    | with_reducible exact so_appendKlongs _ _ _ _
    | with_reducible refine so_bind ?_ (fun _ => ?_)
    | split)

theorem so_setValue (c : SIS.Tree.Ctx) (segRoot cv : Nat) (key : Key) (h : Nat) :
    StepOk c (SIS.Tree.setValue segRoot cv key (some h)) := by
  unfold SIS.Tree.setValue
  refine so_bind so_read (fun c' => so_bind (so_descendLte _ _ _ _) (fun leaf => ?_))
  dsimp only
  repeat (first
    | with_reducible exact so_pure _
    | with_reducible exact so_throw _
    | with_reducible exact so_getNode _
    | with_reducible exact so_newValue _
    | with_reducible exact so_putNode _ _
    | with_reducible exact so_pathSize
    | with_reducible exact so_appendKlongs _ _ _ _
    | with_reducible refine so_bind ?_ (fun _ => ?_)
    | split)

theorem so_putSegs (c : SIS.Tree.Ctx) (key : Key) (h : Nat) :
    ∀ segs x, StepOk c (SIS.Tree.putSegs key (some h) segs x)
  | [], x => by
    rw [SIS.Tree.putSegs.eq_1]
    exact so_throw _
  | [cv], x => by
    rw [SIS.Tree.putSegs.eq_2]
    exact so_setValue c x cv key h
  | cv :: c2 :: rest, x => by
    rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp)]
    refine so_bind (so_setNode c x cv _) (fun r => ?_)
    cases r with
    | none => exact so_pure _
    | some y => exact so_putSegs c key h (c2 :: rest) y

/-! ## 2. The map with some nodes set -/

theorem wputa_ovSet_not {fs : List (NodeId × Obj)} : ∀ {T : Tree} {z : NodeId},
    z ∉ fs.map (·.1) → (ovSet fs T).obj z = T.obj z := by
  induction fs with
  | nil => intro T z _; rfl
  | cons xo fs ih =>
    intro T z hz
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    show (ovSet fs (T.set xo.1 xo.2)).obj z = T.obj z
    rw [ih hz.2]
    simp [Tree.set, hz.1]

theorem wputa_ovSet_eq {fs : List (NodeId × Obj)} : ∀ {T T' : Tree} {z : NodeId},
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

theorem wputa_ovSet_roots {fs : List (NodeId × Obj)} :
    ∀ {T : Tree}, (ovSet fs T).roots = T.roots := by
  induction fs with
  | nil => intro T; rfl
  | cons xo fs ih =>
    intro T
    show (ovSet fs (T.set xo.1 xo.2)).roots = T.roots
    rw [ih]
    rfl

/-- A node of fs, with ids all distinct, has its object of fs. -/
theorem wputa_ovSet_mem : ∀ {fs : List (NodeId × Obj)} {T : Tree} {z : NodeId} {o : Obj},
    (fs.map (·.1)).Nodup → (z, o) ∈ fs → (ovSet fs T).obj z = some o
  | [], _, _, _, _, h => by simp at h
  | xo :: fs, T, z, o, hnd, h => by
    show (ovSet fs (T.set xo.1 xo.2)).obj z = some o
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | h
    · rw [wputa_ovSet_not hnd.1]
      simp [Tree.set]
    · exact wputa_ovSet_mem hnd.2 h

/-- Two trees equal but at the nodes of fs are equal with fs set. -/
theorem wputa_ovSet_ext {fs : List (NodeId × Obj)} {T T' : Tree}
    (h : ∀ z, z ∉ fs.map (·.1) → T.obj z = T'.obj z) (hr : T.roots = T'.roots) :
    ovSet fs T = ovSet fs T' := by
  apply prim_tree_ext
  · intro z
    by_cases e : z ∈ fs.map (·.1)
    · exact wputa_ovSet_eq (Or.inl e)
    · exact wputa_ovSet_eq (Or.inr (h z e))
  · rw [wputa_ovSet_roots, wputa_ovSet_roots, hr]

/-! ## 3. The recursion up the path while a new segment leaf has no klong yet -/

/-- `PInvO` with x over its size is `PInvO` with no node over it, if x fits
and is no node of fs. -/
theorem wputa_pinvO_fit {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {fs : List (NodeId × Obj)} {C : List (Key × Nat)} {w : MW} {x : NodeId} {n : MNode}
    (hI : PInvO p i base s tp fs (some x) C w) (hx : w.nodes.lookup x = some n)
    (hxf : x ∉ fs.map (·.1)) (hsz : n.size ≤ p.M) : PInvO p i base s tp fs none C w := by
  refine ⟨hI.root, wput_sound_fit hI.sound (fun m hm => ?_), hI.frame, hI.top, hI.balanced,
    hI.books, hI.empties⟩
  rw [wputa_ovSet_not hxf] at hm
  rw [treeOf_obj_overlay i s hx (wput_taken hm)] at hm
  cases hm
  show (ksOf n).length ≤ p.M
  rw [ksOf_length]
  exact hsz

theorem wputa_cascadeO_self {i : Time} {s : Tree} {fs : List (NodeId × Obj)} {w : MW}
    {x : NodeId} {m : MNode} {depth : Nat} (hon : ∃ c0, w.path[depth]? = some (c0, x)) :
    CascadePostO i s fs w (w.withNode x m) (w.withNode x m) depth := by
  refine ⟨rfl, fun y n hy hoff => ?_, Nat.le_refl _, fun z hz => Or.inl hz⟩
  obtain ⟨c0, hc0⟩ := hon
  have hyx : y ≠ x := fun e => hoff depth c0 (Nat.le_refl _) (e ▸ hc0)
  rw [MW.withNode, lookup_upsert_ne _ _ hyx]
  exact hy

/-- One level of `appendKlongs` in the `O` form, given the levels above it. -/
theorem wputa_append_step {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (fs : List (NodeId × Obj)) (depth : Nat)
    (hup : ∀ d, depth = d + 1 →
      UpOkO p i base s tp v fs (fun q ins => SIS.Tree.appendKlongs d q ins) d) :
    UpOkO p i base s tp v fs (fun q ins => SIS.Tree.appendKlongs depth q ins) depth := by
  intro x ins w n C h
  simp only []
  rw [wput_appendKlongs_eq]
  refine wput_read (wput_ok (getNode_hit _ h.look) ?_)
  dsimp only
  have hupn : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP ((match depth with
        | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
        | d + 1 => fun q more => SIS.Tree.appendKlongs d q more :
          NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) q ins) { p := p, i := i, view := v } w
        (fun _ w' => w.next ≤ w'.next) := by
    intro d hd
    subst hd
    exact fun q ins w => (so_appendKlongs _ d q ins w).mono (fun _ _ hs => hs.1)
  split
  · by_cases h2 : (n.lastVersion i).size ≤ p.splitAbove
    · refine handleFull_time_o hp hb h ?_ hupn (Or.inr ⟨rfl, h2⟩)
      intro d hd; subst hd; exact hup d rfl
    · refine handleFull_space_o hp hb hn h ?_ ?_ hupn (by omega)
      · intro d hd; subst hd; exact hup d rfl
      · intro d hd; subst hd; exact wputg_append_outside _ d
  · next h1 =>
    split
    · refine handleFull_time_o hp hb h ?_ hupn (Or.inl ⟨rfl, by omega⟩)
      intro d hd; subst hd; exact hup d rfl
    · unfold SIS.Tree.addKeys
      refine wput_read (wput_ok (getNode_hit _ h.look) ?_)
      intro r w' hr
      rw [putNode_eq] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      show CasPostO p i base s tp fs w depth x n ins C () (w.withNode x (addAll i n ins))
      intro _ _
      have hsz : (addAll i n ins).size ≤ p.M := by
        have := addAll_size i n ins
        omega
      obtain ⟨c0, hc0⟩ := h.on
      exact ⟨wputa_pinvO_fit h.hyp (lookup_upsert_self _ _ _)
        (h.away depth c0 x (Nat.le_refl _) hc0) hsz, wputa_cascadeO_self h.on⟩

/-- `appendKlongs` meets the statement at every depth while the nodes of fs
are away (`UpOkO`). -/
theorem appendKlongs_spec_o {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (fs : List (NodeId × Obj)) :
    ∀ d, UpOkO p i base s tp v fs (fun q ins => SIS.Tree.appendKlongs d q ins) d := by
  intro d
  induction d with
  | zero => exact wputa_append_step hp hb hn fs 0 (fun d h => absurd h (by omega))
  | succ d ih =>
    exact wputa_append_step hp hb hn fs (d + 1) (fun d' h => by
      obtain rfl : d = d' := by omega
      exact ih)

/-! ## 4. The chain of new segment leaves, exactly -/

/-- The new segment leaves and the value that `putSegs` makes from the empty
segment leaf y of segment g for the segments left, with nx the next id: each
leaf with a time klong of i and its one klong, then the value. -/
def chainFs (p : MParams) (i : Time) (h : Nat) :
    NodeId → Nat → Key → NodeId → List (NodeId × Obj)
  | _, _, [], _ => []
  | y, g, c :: rest, nx =>
    (y, .key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩) ::
      match rest with
      | [] => [(nx, .val h)]
      | _ :: _ => chainFs p i h nx (g + 1) rest (nx + 2)

theorem wputa_chainFs_one (p : MParams) (i : Time) (h : Nat) (y : NodeId) (g c : Nat)
    (nx : NodeId) :
    chainFs p i h y g [c] nx = [(y, .key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩),
      (nx, .val h)] := rfl

theorem wputa_chainFs_cons2 (p : MParams) (i : Time) (h : Nat) (y : NodeId) (g c c2 : Nat)
    (rest : Key) (nx : NodeId) :
    chainFs p i h y g (c :: c2 :: rest) nx =
      (y, .key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩) ::
        chainFs p i h nx (g + 1) (c2 :: rest) (nx + 2) := rfl

/-- The ids of the chain: y, then ids at or above nx; all distinct if y < nx. -/
theorem wputa_chainFs_ids (p : MParams) (i : Time) (h : Nat) :
    ∀ (rest : Key) (y : NodeId) (g nx : Nat), y < nx →
      (∀ z ∈ (chainFs p i h y g rest nx).map (·.1), z = y ∨ nx ≤ z) ∧
      ((chainFs p i h y g rest nx).map (·.1)).Nodup
  | [], _, _, _, _ => by simp [chainFs]
  | [c], y, g, nx, hy => by
    simp only [chainFs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_cons, List.nodup_nil, and_true]
    refine ⟨fun z hz => ?_, ⟨Nat.ne_of_lt hy, by simp⟩⟩
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Nat.le_refl _)
  | c :: c2 :: rest, y, g, nx, hy => by
    obtain ⟨h1, h2⟩ := wputa_chainFs_ids p i h (c2 :: rest) nx (g + 1) (nx + 2) (by omega)
    rw [wputa_chainFs_cons2]
    simp only [List.map_cons, List.mem_cons, List.nodup_cons]
    refine ⟨fun z hz => ?_, ⟨fun hm => ?_, h2⟩⟩
    · rcases hz with rfl | hz
      · exact Or.inl rfl
      · rcases h1 z hz with rfl | h
        · exact Or.inr (Nat.le_refl _)
        · exact Or.inr (by omega)
    · rcases h1 y hm with h | h <;> omega

/-- The first id of the chain is y. -/
theorem wputa_chainFs_head (p : MParams) (i : Time) (h : Nat) (y : NodeId) (g : Nat) (c : Nat)
    (rest : Key) (nx : NodeId) : y ∈ (chainFs p i h y g (c :: rest) nx).map (·.1) := by
  cases rest with
  | nil => simp [wputa_chainFs_one]
  | cons c2 r => simp [wputa_chainFs_cons2]

/-- The key nodes of the chain are segment leaves at height 0, above level 0. -/
theorem wputa_chainFs_lev (p : MParams) (i : Time) (h : Nat) :
    ∀ (rest : Key) (y : NodeId) (g nx : Nat) (z : NodeId) (m : KNode),
      (z, Obj.key m) ∈ chainFs p i h y g rest nx →
      0 < m.level ∧ m.leaf = true ∧ p.heightOf m.level = 0
  | [], _, _, _, _, _, hm => by simp [chainFs] at hm
  | [c], y, g, nx, z, m, hm => by
    rw [wputa_chainFs_one] at hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact ⟨keyLevel_pos p g 0, rfl, heightOf_keyLevel p (Nat.zero_le _)⟩
    · rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · cases hm
  | c :: c2 :: rest, y, g, nx, z, m, hm => by
    rw [wputa_chainFs_cons2] at hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact ⟨keyLevel_pos p g 0, rfl, heightOf_keyLevel p (Nat.zero_le _)⟩
    · exact wputa_chainFs_lev p i h (c2 :: rest) nx (g + 1) (nx + 2) z m hm

/-- A map that has the chain's objects has the chain (`NewChain`), if the
levels fall within G and the chain's ids are no nodes of A. -/
theorem wputa_chainFs_newChain {p : MParams} (hp : ParamsOK p) {i : Time} {h : Nat}
    {A B : Tree} :
    ∀ (rest : Key) (y : NodeId) (g nx : Nat), rest ≠ [] → keyWf rest = true →
      g + rest.length ≤ p.G + 1 → y < nx →
      (∀ z ∈ (chainFs p i h y g rest nx).map (·.1), A.obj z = none) →
      (∀ xo ∈ chainFs p i h y g rest nx, B.obj xo.1 = some xo.2) →
      NewChain p.M A B h y (p.keyLevel g 0) rest ((chainFs p i h y g rest nx).map (·.1))
  | [], _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [c], y, g, nx, _, hk, _, hy, hA, hB => by
    have hy' : B.obj y = some (.key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩) :=
      hB (y, .key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩) (by simp [wputa_chainFs_one])
    have hnx : B.obj nx = some (.val h) := hB (nx, .val h) (by simp [wputa_chainFs_one])
    refine NewChain.last y nx _ c (hA y (by simp [wputa_chainFs_one]))
      (hA nx (by simp [wputa_chainFs_one]))
      (Nat.ne_of_lt hy) (wputs_nodeIs_one (i := i) hp hy' (by rw [hnx]; rfl)) (wput_isLong hk)
      hnx
  | c :: c2 :: rest, y, g, nx, _, hk, hg, hy, hA, hB => by
    have hk2 : isLong c = true ∧ keyWf (c2 :: rest) = true := by
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk
    rw [wputa_chainFs_cons2] at hA hB ⊢
    have hy' : B.obj y = some (.key ⟨p.keyLevel g 0, true, [.time i, .key c nx]⟩) :=
      hB _ List.mem_cons_self
    have hids := wputa_chainFs_ids p i h (c2 :: rest) nx (g + 1) (nx + 2) (by omega)
    have hlen : g + (c :: c2 :: rest).length ≤ p.G + 1 := hg
    simp only [List.length_cons] at hlen
    have ih := wputa_chainFs_newChain (i := i) (h := h) (A := A) (B := B) hp (c2 :: rest) nx
      (g + 1) (nx + 2) (by simp) hk2.2 (by simp only [List.length_cons]; omega) (by omega)
      (fun z hz => hA z (List.mem_cons_of_mem _ hz))
      (fun xo hxo => hB xo (List.mem_cons_of_mem _ hxo))
    refine NewChain.step y nx _ _ c (c2 :: rest) _ (hA y List.mem_cons_self) ?_ ?_ hk2.1
      (wputs_keyLevel_lt p (by omega)) ih
    · intro hm
      rcases hids.1 y hm with h1 | h1 <;> omega
    · refine wputs_nodeIs_one (i := i) hp hy' ?_
      obtain ⟨⟨m, hm, -⟩, -⟩ := ih.tr_props
      rw [hm]
      rfl

theorem wputa_wp_and {α : Type} {f : SIS.Tree.M α} {c : SIS.Tree.Ctx} {w : MW}
    {P Q : α → MW → Prop} (hP : WP f c w P) (hQ : WP f c w Q) :
    WP f c w (fun a w' => P a w' ∧ Q a w') :=
  fun a w' h => ⟨hP a w' h, hQ a w' h⟩

/-- The chain of `putSegs` from an empty new segment leaf y, exactly: if no
node is outside G and H at the end, the levels are within G, and the map is
the map before with the chain's objects set. -/
theorem wputa_chain_map {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {A : Tree} {key : Key}
    {h : Nat} :
    ∀ (rest : Key) (w : MW) (y : NodeId) (g : Nat), rest ≠ [] → keyWf rest = true →
      ChainPre p i base s tp A w y g →
      WP (SIS.Tree.putSegs key (some h) rest y) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] → w.outside = [] ∧ g + rest.length ≤ p.G + 1 ∧
          treeOf i s w' = ovSet (chainFs p i h y g rest w.next) (treeOf i s w)) := by
  intro rest
  induction rest with
  | nil => intro w y g hne; exact absurd rfl hne
  | cons c rest' ih =>
    intro w y g _ hk hpre
    have hyn : y < w.next := hpre.ids y _ hpre.look
    have hyv : y ≠ w.next := Nat.ne_of_lt hyn
    have hnv' : w.nodes.lookup w.next = none := by
      cases e : w.nodes.lookup w.next with
      | none => rfl
      | some n => exact absurd (hpre.ids _ n e) (Nat.lt_irrefl _)
    cases rest' with
    | nil =>
      rw [SIS.Tree.putSegs.eq_2]
      refine (wputs_setValue_new hp hpre.look c key h).mono ?_
      rintro r wf rfl ho
      rw [wputs_add_empty] at ho ⊢
      obtain ⟨hW, hty, -, hg⟩ := hpre.cond ho
      obtain ⟨-, -, hnv, hvv, htv, -⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
      have hlvl : wLevel s w y = p.keyLevel g 0 := by
        obtain ⟨g', h', h1, -, -, h4, -⟩ := hW.books.levels y _ hpre.look hty
        rw [hpre.gh] at h1
        cases h1
        exact h4
      have hT4 : treeOf i s (w.afterNewValue h) = (treeOf i s w).set w.next (.val h) :=
        treeOf_afterNewValue i s h hnv hvv htv
      have hTW := treeOf_withNode i s (w := w.afterNewValue h)
        (⟨true, [.time i, .key c w.next]⟩ : MNode) hty
      have hwl : wLevel s (w.afterNewValue h) y = wLevel s w y := prim_wLevel_afterNewValue hyv
      have hnd := (wputa_chainFs_ids p i h [c] y g w.next hyn).2
      refine ⟨ho, by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
      apply prim_tree_ext
      · intro z
        by_cases hzy : z = y
        · rw [hzy, wputa_ovSet_mem (o := .key ⟨p.keyLevel g 0, true, [.time i, .key c w.next]⟩)
            hnd (by simp [wputa_chainFs_one]), hTW]
          simp [Tree.set, hwl, hlvl, ksOf, kOf]
        · by_cases hzv : z = w.next
          · rw [hzv, wputa_ovSet_mem (o := .val h) hnd (by simp [wputa_chainFs_one]), hTW, hT4]
            simp [Tree.set, Ne.symm hyv]
          · rw [wputa_ovSet_not (by simp [wputa_chainFs_one, hzy, hzv]), hTW, hT4]
            simp [Tree.set, hzy, hzv]
      · rw [wputa_ovSet_roots]
        rfl
    | cons c2 rest2 =>
      have hk2 : isLong c = true ∧ keyWf (c2 :: rest2) = true := by
        simp only [keyWf, Bool.and_eq_true] at hk
        exact hk
      rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
      refine (wputs_setNode_new hp hpre.look hpre.gh c).mono ?_
      rintro r w3 ⟨rfl, hw3⟩
      subst w3
      dsimp only
      rw [wputs_add_empty]
      set wN : MW := { w with trail := "segment.new" :: w.trail } with hwN
      set wA : MW := MW.afterNewKey wN p (g + 1) 0 true [] with hwA
      set n1 : MNode := ⟨true, [.time i, .key c w.next]⟩ with hn1
      have hNn : wN.next = w.next := rfl
      have hlkA : wA.nodes.lookup y = some ⟨true, []⟩ := prim_lookup_append_some _ hpre.look
      have hlkA' : wA.nodes.lookup w.next = some ⟨true, []⟩ := prim_lookup_append_self _ _ hnv'
      have hn3 : (wA.withNode y n1).next = w.next + 2 := rfl
      have hout3 : (wA.withNode y n1).outside = if (decide (p.G < g + 1) || decide (p.H < 0))
          then (w.next, g + 1, 0) :: w.outside else w.outside := rfl
      have hcond : (wA.withNode y n1).outside = [] → w.outside = [] ∧ g + 1 ≤ p.G := by
        intro ho3
        rw [hout3] at ho3
        split at ho3
        · cases ho3
        · next hcnd =>
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcnd
          exact ⟨ho3, hcnd.1⟩
      have htimes : ∀ t, SIS.Tree.Klong.time t ∈ n1.ks → t ≤ i := by
        intro t ht
        simp only [hn1, List.mem_cons, SIS.Tree.Klong.time.injEq, List.not_mem_nil, or_false,
          reduceCtorEq] at ht
        omega
      have hpre3 : ChainPre p i base s tp A (wA.withNode y n1) w.next (g + 1) := by
        refine ⟨?_, prim_gh_cons_self _ _ _ _, ?_, ?_, ?_⟩
        · rw [MW.withNode, lookup_upsert_ne _ _ (Ne.symm hyv)]
          exact hlkA'
        · intro x n hx
          rw [hn3]
          rcases prim_lookup_withNode hx with ⟨rfl, -⟩ | ⟨-, hx'⟩
          · omega
          · rcases prim_lookup_afterNewKey (w := wN) hnv' hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
            · omega
            · have := hpre.ids x n hx''
              omega
        · intro z hz
          apply hpre.fresh z (Or.inr ?_)
          rcases hz with rfl | hz
          · exact Nat.le_refl _
          · omega
        · intro ho3
          obtain ⟨ho, hg1⟩ := hcond ho3
          obtain ⟨hW, hty, hemp, -⟩ := hpre.cond ho
          obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
          have hsy : s.obj y = none := hW.books.empty y _ hpre.look hty rfl
          have hWN := hW.trail ("segment.new" :: w.trail)
          have hkA := putBooksE_afterNewKey (w := wN) hb hWN.books hg1 (Nat.zero_le _) rfl
            (Or.inl rfl) (by simp)
          have hFA := frame_afterNewKey (w := wN) p (g + 1) 0 true [] hWN.frame hsv hnv htv hmv
          refine ⟨⟨hW.root, frame_withNode hFA hlkA hty rfl (fun n0 hs0 => by
            rw [hsy] at hs0; cases hs0), hW.top, putBooksE_withNode hkA hlkA hty rfl
            (Or.inr ⟨rfl, _, rfl⟩) htimes⟩, htv, ?_, hg1⟩
          intro x n hx htx he
          rcases prim_lookup_withNode hx with ⟨rfl, rfl⟩ | ⟨hxy, hx'⟩
          · cases he
          · rcases prim_lookup_afterNewKey (w := wN) hnv hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
            · rfl
            · exact absurd (hemp x n hx'' htx he) hxy
      refine (ih (wA.withNode y n1) w.next (g + 1) (by simp) hk2.2 hpre3).mono ?_
      intro r wf hpost ho
      obtain ⟨ho3, hg1, hmap⟩ := hpost ho
      obtain ⟨ho', -⟩ := hcond ho3
      obtain ⟨hW, hty, -, -⟩ := hpre.cond ho'
      obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
      have hTA : treeOf i s wA = (treeOf i s w).set w.next (.key ⟨p.keyLevel (g + 1) 0, true,
          []⟩) := treeOf_afterNewKey (w := wN) i s p (g + 1) 0 true [] hsv hnv htv hmv
      have hT3 : treeOf i s (wA.withNode y n1) =
          (treeOf i s wA).set y (.key ⟨wLevel s wA y, true, ksOf n1⟩) := treeOf_withNode i s n1 hty
      have hwlA : wLevel s wA y = wLevel s w y := prim_wLevel_afterNewKey (w := wN) hyv
      have hlvl : wLevel s w y = p.keyLevel g 0 := by
        obtain ⟨g', h', h1, -, -, h4, -⟩ := hW.books.levels y _ hpre.look hty
        rw [hpre.gh] at h1
        cases h1
        exact h4
      refine ⟨ho', by simp only [List.length_cons] at hg1 ⊢; omega, ?_⟩
      rw [hmap]
      show ovSet _ (treeOf i s (wA.withNode y n1)) =
        ovSet (chainFs p i h w.next (g + 1) (c2 :: rest2) (w.next + 2))
          ((treeOf i s w).set y (.key ⟨p.keyLevel g 0, true, [.time i, .key c w.next]⟩))
      have hhead := wputa_chainFs_head p i h w.next (g + 1) c2 rest2 (w.next + 2)
      apply wputa_ovSet_ext
      · intro z hz
        rw [hT3, hTA]
        by_cases hzy : z = y
        · subst hzy
          simp [Tree.set, hwlA, hlvl, hn1, ksOf, kOf]
        · have hzn : z ≠ w.next := fun e => hz (by rw [e]; exact hhead)
          simp [Tree.set, hzy, hzn]
      · rfl

/-! ## 5. A route with another tail -/

/-- A route to q with cv :: t left is one with cv :: t' left, for the key
with the tail t' in place of t. -/
theorem wputa_route_tail {T : Tree} {u q : NodeId} {k kq : Key} (hr : Route T u k q kq) :
    ∀ (pre : Key) (cv : Nat) (t t' : Key), k = pre ++ cv :: t → kq = cv :: t →
      Route T u (pre ++ cv :: t') q (cv :: t') := by
  induction hr with
  | here q k =>
    intro pre cv t t' hk hkq
    subst hkq
    cases pre with
    | nil => exact Route.here q _
    | cons a pre' =>
      exfalso
      have := congrArg List.length hk
      simp only [List.length_cons, List.length_append] at this
      omega
  | inner u n c y cv0 rest q k' hobj hl hm hle hmax _ ih =>
    intro pre cv t t' hk hkq
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact Route.inner u n c y cv0 t' q (cv0 :: t') hobj hl hm hle hmax
        (ih [] cv0 rest t' rfl hkq)
    | cons a pre' =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact Route.inner u n c y cv0 (pre' ++ cv :: t') q (cv :: t') hobj hl hm hle hmax
        (ih (cv0 :: pre') cv t t' rfl hkq)
  | leaf u n c y rest q k' hobj hl hm hlong hr ih =>
    intro pre cv t t' hk hkq
    cases pre with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      obtain ⟨pre2, he⟩ := wputs_route_suffix hr
      rw [hkq] at he
      have := congrArg List.length he
      simp only [List.length_cons, List.length_append] at this
      omega
    | cons a pre' =>
      simp only [List.cons_append, List.cons.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact Route.leaf u n c y (pre' ++ cv :: t') q (cv :: t') hobj hl hm hlong
        (ih pre' cv t t' rfl hkq)

/-! ## 6. The "if" state of a new segment leaf linked from a full leaf -/

theorem wputa_ovSet_isSome {fs : List (NodeId × Obj)} : ∀ {T : Tree} {z : NodeId},
    (T.obj z).isSome = true → ((ovSet fs T).obj z).isSome = true := by
  induction fs with
  | nil => intro T z h; exact h
  | cons xo fs ih =>
    intro T z h
    exact ih (wput_set_isSome h)

/-- The state after `newKey (g + 1) 0 true []` for the new segment leaf, at the
segment leaf L with its node n, from the state w3 after the descent. -/
abbrev wputaA (p : MParams) (w3 : MW) (g : Nat) : MW :=
  MW.afterNewKey { w3 with trail := "segment.new" :: w3.trail } p (g + 1) 0 true []

/-- The "if" state's map is sound with the chain's objects set: `Sound.putSeg`
with A the map after the descent; and it is BalancedOK, by the nodes reached. -/
theorem wputa_ifSound {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp) {w3 : MW} {L : NodeId}
    {n : MNode} {g cv hval nx : Nat} {key rest : Key}
    (hI3 : PInv p i base s tp none C w3) (hlk3 : w3.nodes.lookup L = some n)
    (ht3 : w3.taken.contains L = false) (hl3 : n.leaf = true)
    (hlv : wLevel s w3 L = p.keyLevel g 0) (hg1 : g + 1 ≤ p.G)
    (hwf : klongsWf (ksOf n) = true) (hsz : n.size ≤ p.M)
    (hr : Route (treeOf i s w3) w3.top.rootKey key L (cv :: rest)) (hcv : isLong cv = true)
    (hno : ∀ y, (cv, y) ∉ live (ksOf n)) (hrne : rest ≠ []) (hkr : keyWf rest = true)
    (hbd : g + 1 + rest.length ≤ p.G + 1) (hnx : w3.next + 2 ≤ nx) :
    Sound p.M (some L)
      (ovSet (chainFs p i hval w3.next (g + 1) rest nx)
        (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next)))))
      w3.top.rootKey (mapPut key hval C) ∧
    Balanced p (ovSet (chainFs p i hval w3.next (g + 1) rest nx)
      (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))))) := by
  obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
  have hLn : L < w3.next := hI3.books.ids.1 L n hlk3
  have hLv : L ≠ w3.next := Nat.ne_of_lt hLn
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  have hTA : treeOf i s (wputaA p w3 g) = (treeOf i s w3).set w3.next
      (.key ⟨p.keyLevel (g + 1) 0, true, []⟩) :=
    treeOf_afterNewKey (w := { w3 with trail := "segment.new" :: w3.trail }) i s p (g + 1) 0
      true [] hsv hnv htv hmv
  have hTW : treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))) =
      (treeOf i s (wputaA p w3 g)).set L (.key ⟨wLevel s (wputaA p w3 g) L,
        (n.add i (.key cv w3.next)).leaf, ksOf (n.add i (.key cv w3.next))⟩) :=
    treeOf_withNode i s _ ht3
  have hwlA : wLevel s (wputaA p w3 g) L = wLevel s w3 L :=
    prim_wLevel_afterNewKey (w := { w3 with trail := "segment.new" :: w3.trail }) hLv
  obtain ⟨hids, hnd⟩ := wputa_chainFs_ids p i hval rest w3.next (g + 1) nx (by omega)
  have hhead : w3.next ∈ (chainFs p i hval w3.next (g + 1) rest nx).map (·.1) := by
    cases rest with
    | nil => exact absurd rfl hrne
    | cons c r => exact wputa_chainFs_head p i hval w3.next (g + 1) c r nx
  have hLf : L ∉ (chainFs p i hval w3.next (g + 1) rest nx).map (·.1) := by
    intro hm
    rcases hids L hm with h1 | h1 <;> omega
  have hreach := (hr.tc_target hI3.sound.good).2
  have hok := hI3.sound.nodes L hreach _ hLm
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨-, hptr⟩ := hok
  have hsameF : ∀ z, z ≠ L → z ∉ (chainFs p i hval w3.next (g + 1) rest nx).map (·.1) →
      (ovSet (chainFs p i hval w3.next (g + 1) rest nx)
        (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))))).obj z =
      (treeOf i s w3).obj z := by
    intro z hzL hzi
    have hzn : z ≠ w3.next := fun e => hzi (e ▸ hhead)
    rw [wputa_ovSet_not hzi, hTW, hTA]
    simp [Tree.set, hzL, hzn]
  have hSP := Sound.putSeg (ex' := some L) hI3.sound hr hLm hl3 hcv hno
    (wputa_chainFs_newChain hp rest w3.next (g + 1) nx hrne hkr hbd (by omega)
      (fun z hz => ?_) (fun xo hxo => wputa_ovSet_mem hnd hxo)) ?_ ?_ hsameF
  · obtain ⟨hS, hRch⟩ := hSP
    refine ⟨hS, ?_⟩
    have hrootB : (ovSet (chainFs p i hval w3.next (g + 1) rest nx)
        (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))))).root =
        some w3.top.rootKey := by
      unfold Tree.root
      rw [wputa_ovSet_roots, hTW, hTA]
      exact hI3.root
    have hBL : (ovSet (chainFs p i hval w3.next (g + 1) rest nx)
        (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))))).obj L =
        some (.key ⟨wLevel s (wputaA p w3 g) L, (n.add i (.key cv w3.next)).leaf,
          ksOf (n.add i (.key cv w3.next))⟩) := by
      rw [wputa_ovSet_not hLf, hTW]
      simp [Tree.set]
    refine Balanced.of_reach (N := L :: (chainFs p i hval w3.next (g + 1) rest nx).map (·.1))
      hI3.balanced (fun z hz => ?_) (fun z _ hz => ?_) (fun y m hm => ?_)
      (fun z hz _ m hm => ?_)
    · rw [reach_of_root hrootB] at hz
      rcases hRch z hz with h1 | h1
      · left
        rw [reach_of_root hI3.root]
        exact h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · simp only [List.mem_cons, not_or] at hz
      exact hsameF z hz.1 hz.2
    · by_cases hyi : y ∈ (chainFs p i hval w3.next (g + 1) rest nx).map (·.1)
      · have hy3 : w3.next ≤ y := by
          rcases hids y hyi with h1 | h1
          · exact Nat.le_of_eq h1.symm
          · omega
        rw [(treeOf_fresh hb hI3.books hy3).1] at hm
        cases hm
      · by_cases hyL : y = L
        · rw [hyL, hLm] at hm
          cases hm
          exact ⟨_, by rw [hyL]; exact hBL, hwlA⟩
        · exact ⟨m, by rw [hsameF y hyL hyi]; exact hm, rfl⟩
    · rcases List.mem_cons.mp hz with hz | hz
      · rw [hz, hBL] at hm
        cases hm
        obtain ⟨h1, h2, -⟩ := hI3.balanced L (by rw [reach_of_root hI3.root]; exact hreach) _
          hLm
        refine ⟨by rw [hwlA]; exact h1, by rw [hwlA, add_leaf]; exact h2, fun hl' => ?_⟩
        change (n.add i (.key cv w3.next)).leaf = false at hl'
        rw [add_leaf, hl3] at hl'
        cases hl'
      · obtain ⟨⟨z', o⟩, ho, he⟩ := List.mem_map.mp hz
        simp only at he
        subst he
        rw [wputa_ovSet_mem hnd ho] at hm
        cases hm
        obtain ⟨h1, h2, h3⟩ := wputa_chainFs_lev p i hval rest w3.next (g + 1) nx _ _ ho
        refine ⟨h1, by simp [h2, h3], fun hl' => ?_⟩
        rw [h2] at hl'
        cases hl'
  · rcases hids z hz with rfl | h1
    · exact hsv ▸ (treeOf_fresh hb hI3.books (Nat.le_refl _)).1
    · exact (treeOf_fresh hb hI3.books (by omega)).1
  · show p.keyLevel (g + 1) 0 < wLevel s w3 L
    rw [hlv]
    exact wputs_keyLevel_lt p hg1
  · refine ⟨⟨wLevel s (wputaA p w3 g) L, (n.add i (.key cv w3.next)).leaf,
      ksOf (n.add i (.key cv w3.next))⟩, ?_, hwlA, by rw [add_leaf]; exact hl3,
      add_key_live hwf cv w3.next, ?_⟩
    · rw [wputa_ovSet_not hLf, hTW]
      simp [Tree.set]
    · simp only [bnd, ite_true, nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨?_, add_key_wf hwf cv w3.next⟩, ?_⟩
      · rw [ksOf_length]
        have := add_size n i (.key cv w3.next)
        omega
      · intro k hk
        cases k with
        | key c y =>
          rcases add_key_mem.mp hk with hk | ⟨rfl, rfl⟩
          · show ((ovSet _ _).obj y).isSome = true
            apply wputa_ovSet_isSome
            rw [hTW, hTA]
            exact wput_set_isSome (wput_set_isSome (hptr _ hk))
          · show ((ovSet _ _).obj w3.next).isSome = true
            apply wputa_ovSet_isSome
            rw [hTW, hTA]
            simp [Tree.set, Ne.symm hLv]
        | time t => rfl
        | del b => rfl

/-- `CasPreO` at the segment leaf L for the klong of the new segment leaf,
given the soundness and BalancedOK of the "if" state with fs set. -/
theorem wputa_ifState {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} (hb : Books i base s tp) {w3 : MW} {L : NodeId} {n : MNode}
    {g cv : Nat} {D : Nat} {c0 : Option Nat} {fs : List (NodeId × Obj)} {C' : List (Key × Nat)}
    (hI3 : PInv p i base s tp none C w3) (hlk3 : w3.nodes.lookup L = some n)
    (ht3 : w3.taken.contains L = false) (hg1 : g + 1 ≤ p.G)
    (hwf : klongsWf (ksOf n) = true) (hsz : n.size ≤ p.M)
    (hP3 : PathOk i s w3 D) (hlev3 : LevDown i s w3 D) (hc0 : w3.path[D]? = some (c0, L))
    (hfs : ∀ e ∈ fs.map (·.1), e = w3.next ∨ w3.next + 2 ≤ e)
    (hchild : w3.next ∈ fs.map (·.1))
    (hsound : Sound p.M (some L) (ovSet fs
      (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next))))) w3.top.rootKey C' ∧
      Balanced p (ovSet fs (treeOf i s ((wputaA p w3 g).withNode L (n.add i (.key cv w3.next)))))) :
    CasPreO p i base s tp fs (wputaA p w3 g) D L n [(cv, w3.next)] C' := by
  obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
  have hkN : PutBooks p i base s { w3 with trail := "segment.new" :: w3.trail } :=
    putBooks_congr hI3.books rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hkA, hempA⟩ := putBooks_afterNewKey_nil (w := { w3 with trail := "segment.new" ::
    w3.trail }) hb hkN hg1 (Nat.zero_le _) rfl
  have hFA := frame_afterNewKey (w := { w3 with trail := "segment.new" :: w3.trail }) p (g + 1)
    0 true [] hI3.frame hsv hnv htv hmv
  have hPA : PathOk i s (wputaA p w3 g) D :=
    pathOk_afterNewKey (w := { w3 with trail := "segment.new" :: w3.trail }) p (g + 1) 0 true []
      (hP3.congr rfl rfl rfl rfl rfl) hsv hnv htv hmv
  have hlkA : (wputaA p w3 g).nodes.lookup L = some n := prim_lookup_append_some _ hlk3
  have hleaf' : (n.add i (.key cv w3.next)).leaf = n.leaf := add_leaf n i _
  obtain ⟨t0, rest0, hr0⟩ := hI3.books.timeFirst L n hlk3 ht3
  obtain ⟨rest1, hr1⟩ := add_first (t := i) (.key cv w3.next) hr0
  refine ⟨hlkA, ⟨c0, hc0⟩, hPA, wputg_nodup (w := w3) hP3 hlev3, ?_, hkA, ⟨t0, rest0, hr0⟩,
    hwf, hsz, Or.inl rfl, fun a y1 b y2 he => by simp at he, ?_⟩
  · intro d c u hd hu hm
    obtain ⟨m, hm', -⟩ := hP3.lookup hd hu
    have := hI3.books.ids.1 u m hm'
    rcases hfs u hm with h1 | h1 <;> omega
  · refine ⟨hI3.root, hsound.1, ?_, hI3.top, hsound.2, ?_, ?_⟩
    · refine frame_withNode hFA hlkA ht3 hleaf' (fun n0 hs0 => ?_)
      obtain ⟨-, -, he⟩ := frame_overlay_ext hI3.frame hlk3 ht3 hs0
      exact add_ext (prim_timesBefore (hb.times L n0 hs0)) he _
    · exact putBooksE_withNode (n' := n.add i (.key cv w3.next)) hkA hlkA ht3 hleaf'
        (Or.inl (by rw [hr1, hr0]; rfl))
        (timesLe_model (add_timesLe (wput_timesLe hI3.books hlk3) _ (fun t' e => by cases e)))
    · intro x m hx htx he
      rcases prim_lookup_withNode hx with ⟨rfl, rfl⟩ | ⟨-, hx'⟩
      · show x ∈ fs.map (·.1)
        exfalso
        have : (n.add i (.key cv w3.next)).ks = [] := he
        rw [hr1] at this
        cases this
      · rw [hempA x m hx' htx he]
        exact hchild

theorem wputa_wLevel_prefix {s : Tree} {w w' : MW} {y : NodeId} {m : SIS.NewNode}
    (hs : s.obj y = none) (hp : w.made <+: w'.made)
    (hf : w.made.find? (fun m => m.id == y) = some m) : wLevel s w' y = m.level := by
  obtain ⟨l, hl⟩ := hp
  simp only [wLevel, hs, ← hl, List.find?_append, hf, Option.some_or]

/-! ## 7. A new segment leaf linked from a full segment leaf -/

/-- `putSegs` from the root x of the tree of the segment cv, which has no
live klong of cv in the segment leaf the key is routed to, and no room in it:
the new segment leaf, its klong given to the full leaf by `appendKlongs` (the
recursion with the chain's nodes set: `appendKlongs_spec_o`), then the chain. -/
theorem wputa_newseg_full {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv : Nat} {rest : Key} {h : Nat} {T : Tree} {nl : KNode} (hp : ParamsOK p)
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hn : SNamed s) (hrne : rest ≠ [])
    (hk : keyWf (cv :: rest) = true) (hleafT : T.obj leaf = some (.key nl))
    (hno : ∀ y, (cv, y) ∉ live nl.ks) (hfull : p.M < nl.ks.length + 2) {w : MW} {depth : Nat}
    {x : NodeId} (hT : treeOf i s w = T)
    (hD : DescInvS p i base s tp C key leaf (cv :: rest) cv rest w depth x) :
    WP (SIS.Tree.putSegs key (some h) (cv :: rest) x) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w') := by
  have hk2 : isLong cv = true ∧ keyWf rest = true := by
    cases rest with
    | nil => exact absurd rfl hrne
    | cons c2 r =>
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk
  rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ hrne, wp_bind]
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  refine (wputs_descend hs hb _ w depth x hD).mono ?_
  rintro L (w3 : MW) ⟨hT3, htop3, hI3, ⟨n, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, ⟨lo, hi, hGL⟩, hr3, hlev3,
    -⟩
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  rcases wputs_route_leaf hr3 hLm hl3 with ⟨hL, -⟩ | ⟨y, -, -, hry⟩
  swap
  · exfalso
    obtain ⟨pre, he⟩ := wputs_route_suffix hry
    have := congrArg List.length he
    simp only [List.length_append, List.length_cons] at this
    omega
  subst hL
  have hnx : nl = ⟨wLevel s w3 L, n.leaf, ksOf n⟩ := by
    have := hLm
    rw [hT3, hT, hleafT] at this
    cases this
    rfl
  subst hnx
  have hwf : klongsWf (ksOf n) = true := wputg_good_wf hGL hLm
  have hfull' : p.M < n.size + 2 := by
    rw [← ksOf_length]
    exact hfull
  have hrT3 : Route (treeOf i s w3) w3.top.rootKey key L (cv :: rest) := by
    rw [hT3, htop3]
    exact hD.full
  have hreach := (hrT3.tc_target hI3.sound.good).2
  have hok := hI3.sound.nodes L hreach _ hLm
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hsz : n.size ≤ p.M := by
    rw [← ksOf_length]
    exact hok.1.1
  refine wput_ok (getNode_hit _ hlk3) ?_
  split
  · next fd hfd =>
    exfalso
    obtain ⟨-, hfm⟩ := searchEq_some hwf (wput_timesLe hI3.books hlk3) hfd
    exact hno fd.y hfm
  · dsimp only
    obtain ⟨g, hh, hgh, -, -, hlv, hlf⟩ := hI3.books.levels L n hlk3 ht3
    have hh0 : hh = 0 := by
      rw [hl3] at hlf
      cases hh with
      | zero => rfl
      | succ k => simp at hlf
    subst hh0
    refine wput_ok (ghOf_hit _ hlk3 hgh) ?_
    dsimp only
    refine wput_ok (note_eq _ _ _) ?_
    refine wput_ok (newKey_eq _ _ _ _ _ _) ?_
    split
    · next hc =>
      exfalso
      omega
    · refine wput_ok (pathSize_eq _ _) ?_
      rw [wp_bind]
      intro u w2 hA
      rw [wp_pure]
      dsimp only
      intro r wf hC hout
      have hstA : WStep (wputaA p w3 g) w2 := so_appendKlongs _ _ L _ (wputaA p w3 g) u w2 hA
      have hstC : WStep w2 wf := so_putSegs _ key h rest _ w2 r wf hC
      have ho2 : w2.outside = [] := hstC.2.2.1 hout
      have hoA : (wputaA p w3 g).outside = [] := hstA.2.2.1 ho2
      have hg1 : g + 1 ≤ p.G := by
        have hoA' : (wputaA p w3 g).outside = if (decide (p.G < g + 1) || decide (p.H < 0))
            then (w3.next, g + 1, 0) :: w3.outside else w3.outside := rfl
        rw [hoA'] at hoA
        split at hoA
        · cases hoA
        · next hcnd =>
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcnd
          exact hcnd.1
      have hnA : w3.next + 2 ≤ w2.next := hstA.1
      obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
      obtain ⟨pre, hpre⟩ := wputs_route_suffix hrT3
      have hfsA : ∀ (hv : Nat) (r' : Key), r' ≠ [] →
          (∀ e ∈ (chainFs p i hv w3.next (g + 1) r' w2.next).map (·.1),
            e = w3.next ∨ w3.next + 2 ≤ e) ∧
          w3.next ∈ (chainFs p i hv w3.next (g + 1) r' w2.next).map (·.1) ∧
          (∀ e ∈ (chainFs p i hv w3.next (g + 1) r' w2.next).map (·.1),
            e < (wputaA p w3 g).next ∨ w2.next ≤ e) := by
        intro hv r' hr'
        obtain ⟨hids, -⟩ := wputa_chainFs_ids p i hv r' w3.next (g + 1) w2.next (by omega)
        refine ⟨fun e he => ?_, ?_, fun e he => ?_⟩
        · rcases hids e he with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by omega)
        · cases r' with
          | nil => exact absurd rfl hr'
          | cons c r => exact wputa_chainFs_head p i hv w3.next (g + 1) c r w2.next
        · rcases hids e he with h1 | h1
          · left
            show e < w3.next + 2
            omega
          · exact Or.inr h1
      -- the recursion with a chain of one node set: the books after it
      obtain ⟨hd1, hd2, hd3⟩ := hfsA 0 [0] (by simp)
      have hsd := wputa_ifSound (hval := 0) (nx := w2.next) hp hb hI3 hlk3 ht3 hl3 hlv hg1 hwf
        hsz (wputa_route_tail hrT3 pre cv rest [0] hpre rfl) hk2.1 hno (by simp) (by decide)
        (by simp only [List.length_cons, List.length_nil]; omega) hnA
      have hcd := wputa_ifState hb hI3 hlk3 ht3 hg1 hwf hsz hP3 hlev3 hc0 hd1 hd2 hsd
      obtain ⟨hPd, hCd⟩ := appendKlongs_spec_o (v := v) hp hb hn _ _ L [(cv, w3.next)] _ n _ hcd
        u w2 hA ho2 hd3
      have hlA : (wputaA p w3 g).nodes.lookup w3.next = some ⟨true, []⟩ :=
        prim_lookup_append_self _ _ hnv
      have hl2 : w2.nodes.lookup w3.next = some ⟨true, []⟩ := by
        refine hCd.off w3.next _ hlA (fun d c hd he => ?_)
        obtain ⟨m, hm, -⟩ := hP3.lookup hd he
        have := hI3.books.ids.1 _ m hm
        omega
      have htk2 : w2.taken.contains w3.next = false := by
        rw [hstA.2.1]
        exact htv
      have hwl2 : wLevel s w2 w3.next = p.keyLevel (g + 1) 0 := by
        refine wputa_wLevel_prefix (m := ⟨w3.next, p.keyLevel (g + 1) 0, false⟩) hsv hstA.2.2.2 ?_
        show (w3.made ++ [(⟨w3.next, p.keyLevel (g + 1) 0, false⟩ : SIS.NewNode)]).find? _ = _
        rw [List.find?_append, List.find?_eq_none.mpr (fun m hm => by simpa using hmv m hm)]
        simp
      obtain ⟨g', h', hgh2, hg', -, hlv2, hlf2⟩ := hPd.books.levels w3.next _ hl2 htk2
      have h'0 : h' = 0 := by
        cases h' with
        | zero => rfl
        | succ k => simp at hlf2
      subst h'0
      have hg'1 : g' = g + 1 := by
        have := congrArg p.segOf (hlv2.symm.trans hwl2)
        rwa [segOf_keyLevel p hg' (Nat.zero_le _), segOf_keyLevel p hg1 (Nat.zero_le _)] at this
      subst hg'1
      have hpre2 : ChainPre p i base s tp (treeOf i s w3) w2 w3.next (g + 1) := by
        refine ⟨hl2, hgh2, hPd.books.ids.1, fun z hz => ?_, fun _ => ⟨⟨hPd.root, hPd.frame,
          hPd.top, hPd.books⟩, htk2, fun x m hx htx he => ?_, hg1⟩⟩
        · rcases hz with rfl | hz
          · exact (treeOf_fresh hb hI3.books (Nat.le_refl _)).1
          · exact (treeOf_fresh hb hI3.books (by omega)).1
        · have hxm := hPd.empties x m hx htx he
          rcases hd1 x hxm with h1 | h1
          · exact h1
          · have := hPd.books.ids.1 x m hx
            obtain ⟨hids, -⟩ := wputa_chainFs_ids p i 0 [0] w3.next (g + 1) w2.next (by omega)
            rcases hids x hxm with h2 | h2
            · exact h2
            · omega
      -- the chain: the map at the end, exactly, and its books
      obtain ⟨-, hbd, hmap⟩ := wputa_chain_map (v := v) hp hb rest w2 w3.next (g + 1) hrne hk2.2
        hpre2 r wf hC hout
      obtain ⟨-, hWf, hnoe, -, -, -, htopf, -⟩ := wputs_chain (v := v) hp hb rest w2 w3.next
        (g + 1) hrne hk2.2 hpre2 r wf hC hout
      -- the recursion with the chain's nodes set
      obtain ⟨hr1, hr2, hr3'⟩ := hfsA h rest hrne
      have hsr := wputa_ifSound (hval := h) (nx := w2.next) hp hb hI3 hlk3 ht3 hl3 hlv hg1 hwf
        hsz hrT3 hk2.1 hno hrne hk2.2 hbd hnA
      have hcr := wputa_ifState hb hI3 hlk3 ht3 hg1 hwf hsz hP3 hlev3 hc0 hr1 hr2 hsr
      obtain ⟨hPr, -⟩ := appendKlongs_spec_o (v := v) hp hb hn _ _ L [(cv, w3.next)] _ n _ hcr
        u w2 hA ho2 hr3'
      refine ⟨hWf.root, ?_, hWf.frame, hWf.top, ?_, hWf.books.toBooks hnoe⟩
      · rw [hmap, htopf]
        exact hPr.sound
      · rw [hmap]
        exact hPr.balanced

/-- `putSegs` along the key's route to the full segment leaf `leaf` with
cv :: rest left, from the root x of the tree of the segment c. -/
theorem wputa_putSegs {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv : Nat} {rest : Key} {h : Nat} {T : Tree} {nl : KNode} (hp : ParamsOK p)
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hn : SNamed s) (hrne : rest ≠ [])
    (hleafT : T.obj leaf = some (.key nl)) (hno : ∀ y, (cv, y) ∉ live nl.ks)
    (hfull : p.M < nl.ks.length + 2) :
    ∀ (tail : Key) (c : Nat) (w : MW) (depth : Nat) (x : NodeId), treeOf i s w = T →
      keyWf (c :: tail) = true → DescInvS p i base s tp C key leaf (cv :: rest) c tail w depth x →
      WP (SIS.Tree.putSegs key (some h) (c :: tail) x) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w') := by
  intro tail
  induction tail with
  | nil =>
    intro c w depth x _ _ hD
    exfalso
    obtain ⟨pre, he⟩ := wputs_route_suffix hD.route
    have := congrArg List.length he
    have hr1 : 0 < rest.length := List.length_pos_iff.mpr hrne
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  | cons c2 tail2 ih =>
    intro c w depth x hT hk hD
    obtain ⟨pre, he⟩ := wputs_route_suffix hD.route
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact wputa_newseg_full hp hs hb hn hrne hk hleafT hno hfull hT hD
    | cons a pre' =>
      have hne : c :: c2 :: tail2 ≠ cv :: rest := by
        intro e
        rw [e] at he
        have := congrArg List.length he
        simp only [List.length_append, List.length_cons] at this
        omega
      have hk2 : keyWf (c2 :: tail2) = true := by
        simp only [keyWf, Bool.and_eq_true] at hk
        exact hk.2
      rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
      refine (wputs_setNode hs hb hD hne).mono ?_
      rintro r w' ⟨y, depth', rfl, hT', hD'⟩
      exact ih c2 w' depth' y (hT'.trans hT) hk2 hD'

/-- A put that makes new segment leaves where the segment leaf that gets the
first new klong is full keeps `MidP`. -/
theorem putKv_put_newseg_full {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) {done : List Op} {w w' : MW} {b : Bool} {key : Key}
    {h : Nat} (hm : MidP p i base s tp done w) (hkey : keyWf key = true)
    (hroute : ∃ leaf cv rest nl, rest ≠ [] ∧
      Route (treeOf i s w) w.top.rootKey key leaf (cv :: rest) ∧
      (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true ∧
      (∀ y, (cv, y) ∉ live nl.ks) ∧ p.M < nl.ks.length + 2)
    (hrun : SIS.Tree.putKv (.put key h) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) : MidP p i base s tp (done ++ [Op.put key h]) w' := by
  suffices hW : WP (SIS.Tree.putKv (.put key h)) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → MidP p i base s tp (done ++ [Op.put key h]) w') from
    hW b w' hrun hout
  have hC : applyOps (done ++ [Op.put key h]) (contents s) =
      mapPut key h (applyOps done (contents s)) := by
    rw [applyOps, List.foldl_append]
    rfl
  simp only [MidP, hC]
  obtain ⟨leaf, cv, rest, nl, hrne, hr, hleafo, hnl, hno, hsize⟩ := hroute
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  cases key with
  | nil => simp [keyWf] at hkey
  | cons c tail =>
    exact wputa_putSegs hp hs hb hn hrne hleafo hno hsize tail c _ 0 _ rfl hkey
      ⟨hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, ⟨none, rfl⟩, rfl,
        fun d hd => absurd hd (Nat.not_lt_zero d), fun d hd => absurd hd (Nat.not_lt_zero d),
        ⟨0, none, hm.sound.good⟩, ⟨nl, hleafo, hnl⟩, hr, hr,
        fun d hd => absurd hd (Nat.not_lt_zero d), by
          show w.top.rootKey ∈ reach (treeOf i s w)
          rw [reach_of_root hm.root]
          exact tc_self _ _ _⟩

/-! ## 8. Any put: the run says which case holds -/

/-- The premise of `putKv_put_newseg_full`: the key is routed to a segment
leaf with two segments or more left, the leaf has no live klong of the first,
and no room for one more. -/
def NewSegFullPre (p : MParams) (i : Time) (s : Tree) (w : MW) (key : Key) : Prop :=
  ∃ leaf cv rest nl, rest ≠ [] ∧ Route (treeOf i s w) w.top.rootKey key leaf (cv :: rest) ∧
    (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true ∧
    (∀ y, (cv, y) ∉ live nl.ks) ∧ p.M < nl.ks.length + 2

/-- The three cases of a put, on the map T0 from the space root r. -/
def PutCases (p : MParams) (T0 : Tree) (r : NodeId) (key : Key) : Prop :=
  (∃ leaf cv nl, Route T0 r key leaf [cv] ∧ T0.obj leaf = some (.key nl) ∧ nl.leaf = true) ∨
  (∃ leaf cv rest nl, rest ≠ [] ∧ Route T0 r key leaf (cv :: rest) ∧
    T0.obj leaf = some (.key nl) ∧ nl.leaf = true ∧
    (∀ y, (cv, y) ∉ live nl.ks) ∧ nl.ks.length + 2 ≤ p.M) ∨
  (∃ leaf cv rest nl, rest ≠ [] ∧ Route T0 r key leaf (cv :: rest) ∧
    T0.obj leaf = some (.key nl) ∧ nl.leaf = true ∧
    (∀ y, (cv, y) ∉ live nl.ks) ∧ p.M < nl.ks.length + 2)

theorem wputa_wp_const {α : Type} {f : SIS.Tree.M α} {c : SIS.Tree.Ctx} {w : MW} {P : Prop}
    (h : P) : WP f c w (fun _ _ => P) :=
  fun _ _ _ => h

/-- On the way down with the segments c :: rest of the key left, from node x:
`PInv`; the map is T0; x is sound; a route of c :: rest from x is a route of
the key from the space root r; x is reached. -/
structure ClsInv (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (T0 : Tree) (r : NodeId) (key : Key) (c : Nat) (rest : Key) (w : MW)
    (x : NodeId) : Prop where
  inv : PInv p i base s tp none C w
  map : treeOf i s w = T0
  good : ∃ lo hi, Good T0 x lo hi
  pre : ∀ q k', Route T0 x (c :: rest) q k' → Route T0 r key q k'
  reached : x ∈ reach T0

/-- The descent keeps `ClsInv` and ends at a segment leaf of the overlay. -/
theorem wputa_cls_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {T0 : Tree} {r : NodeId} {key : Key}
    {c : Nat} {rest : Key} (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (x : NodeId), ClsInv p i base s tp C T0 r key c rest w x →
      WP (SIS.Tree.descendLte c f x) { p := p, i := i, view := v } w
        (fun L w' => ClsInv p i base s tp C T0 r key c rest w' L ∧
          ∃ n, w'.nodes.lookup L = some n ∧ n.leaf = true) := by
  intro f
  induction f with
  | zero =>
    intro w x _
    rw [wput_descend_zero]
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro w x hD
    rw [wput_descend_succ]
    refine wput_read ?_
    obtain ⟨lo, hi, hGx⟩ := hD.good
    obtain ⟨m, hxm⟩ := wput_good_obj hGx
    rw [← hD.map] at hxm
    obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, -, -⟩ :=
      getNode_spec hs hb hD.inv hxm (by rw [hD.map]; exact hD.reached)
    refine wput_ok hget ?_
    have hT1' : treeOf i s w1 = T0 := hT1.trans hD.map
    split
    · next hl =>
      rw [wp_pure]
      exact ⟨⟨hI1, hT1', ⟨lo, hi, hGx⟩, hD.pre, hD.reached⟩, n, hlk1, hl⟩
    · next hl =>
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, hle, hmax⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm hmax
        have hml : m.leaf = false := by
          rw [← hleaf]
          cases e : n.leaf
          · rfl
          · exact absurd e hl
        rw [hD.map] at hxm
        obtain ⟨m', lo', hi', -, -, -, hG'⟩ := hGx.child hxm hm (fun h => by rw [hml] at h; cases h)
        have hyr : fd.y ∈ reach T0 := by
          have h1 := wputg_reach_kid (T := treeOf i s w) hD.inv.sound.good hD.inv.root
            (by rw [hD.map]; exact hD.reached) (by rw [hD.map]; exact hxm) hm
          rwa [hD.map] at h1
        refine wput_ok (pathAdd_eq _ _ _ _) ?_
        refine (ih { w1 with path := w1.path ++ [(some fd.c, fd.y)] } fd.y
          ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, hT1', ⟨lo', hi', hG'⟩,
          fun q k' hr => hD.pre q k' (Route.inner x m fd.c fd.y c rest q k' hxm hml hm hle hmax
            hr), hyr⟩).mono ?_
        exact fun L w' h => h

/-- `putSegs` on the segments c :: rest left from x: in the run, the case of
the put holds of the map T0. -/
theorem wputa_cls_putSegs {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {T0 : Tree} {r : NodeId} {key : Key}
    {h : Nat} (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (rest : Key) (c : Nat) (w : MW) (x : NodeId), keyWf (c :: rest) = true →
      ClsInv p i base s tp C T0 r key c rest w x →
      WP (SIS.Tree.putSegs key (some h) (c :: rest) x) { p := p, i := i, view := v } w
        (fun _ _ => PutCases p T0 r key) := by
  intro rest
  induction rest with
  | nil =>
    intro c w x _ hD
    rw [SIS.Tree.putSegs.eq_2]
    unfold SIS.Tree.setValue
    refine wput_read ?_
    rw [wp_bind]
    refine (wputa_cls_descend hs hb _ w x hD).mono ?_
    rintro L w' ⟨hD', n, hlk, hl⟩
    obtain ⟨lo, hi, hGL⟩ := hD'.good
    obtain ⟨m, hLm⟩ := wput_good_obj hGL
    refine wputa_wp_const (Or.inl ⟨L, c, m, hD'.pre L [c] (Route.here L [c]), hLm, ?_⟩)
    rw [← hD'.map] at hLm
    rw [treeOf_obj_overlay i s hlk (wput_taken hLm)] at hLm
    cases hLm
    exact hl
  | cons c2 rest2 ih =>
    intro c w x hk hD
    have hk2 : isLong c = true ∧ keyWf (c2 :: rest2) = true := by
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk
    rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
    unfold SIS.Tree.setNode
    refine wput_read ?_
    rw [wp_bind]
    refine (wputa_cls_descend hs hb _ w x hD).mono ?_
    rintro L (w' : MW) ⟨hD', n, hlk, hl⟩
    obtain ⟨lo, hi, hGL⟩ := hD'.good
    have hLm := treeOf_obj_overlay i s hlk (by
      obtain ⟨m, hm⟩ := wput_good_obj hGL
      rw [← hD'.map] at hm
      exact wput_taken hm)
    have hLm0 := hLm
    rw [hD'.map] at hLm0
    have hwf : klongsWf (ksOf n) = true := wputg_good_wf hGL hLm0
    refine wput_ok (getNode_hit _ hlk) ?_
    split
    · next fd hfd =>
      obtain ⟨hfc, hfm⟩ := searchEq_some hwf (wput_timesLe hD'.inv.books hlk) hfd
      obtain ⟨m', lo', hi', -, -, -, hG'⟩ := hGL.child hLm0 hfm (fun _ => hk2.1)
      refine wput_ok (pathAdd_eq _ _ _ _) ?_
      rw [wp_pure]
      dsimp only
      have hyr : fd.y ∈ reach T0 := by
        have h1 := wputg_reach_kid (T := treeOf i s w') hD'.inv.sound.good hD'.inv.root
          (by rw [hD'.map]; exact hD'.reached) hLm hfm
        rwa [hD'.map] at h1
      exact ih c2 _ fd.y hk2.2 ⟨hD'.inv.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, hD'.map,
        ⟨lo', hi', hG'⟩, fun q k' hr => hD'.pre q k' (Route.leaf L _ c fd.y (c2 :: rest2) q k'
          hLm0 hl hfm hk2.1 hr), hyr⟩
    · next hfd =>
      have hno := searchEq_none hwf (wput_timesLe hD'.inv.books hlk) hfd
      have hroute := hD'.pre L (c :: c2 :: rest2) (Route.here L _)
      have hcase : PutCases p T0 r key := by
        refine Or.inr ?_
        by_cases hsz : (ksOf n).length + 2 ≤ p.M
        · exact Or.inl ⟨L, c, c2 :: rest2, _, by simp, hroute, hLm0, hl, hno, hsz⟩
        · exact Or.inr ⟨L, c, c2 :: rest2, _, by simp, hroute, hLm0, hl, hno,
            Nat.lt_of_not_le hsz⟩
      exact fun _ _ _ => wputa_wp_const hcase

/-- In a run of `putKv` of a put of a key as `Keys.toSegments` makes it, the
case of the put holds of the state the run starts from. -/
theorem wputa_classify {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {done : List Op} {w w' : MW} {b : Bool} {key : Key} {h : Nat}
    (hm : MidP p i base s tp done w) (hkey : keyWf key = true)
    (hrun : SIS.Tree.putKv (.put key h) { p := p, i := i, view := v } w = .ok (b, w')) :
    RoutedPre i s w key ∨ NewSegPre p i s w key ∨ NewSegFullPre p i s w key := by
  suffices hW : WP (SIS.Tree.putKv (.put key h)) { p := p, i := i, view := v } w
      (fun _ _ => PutCases p (treeOf i s w) w.top.rootKey key) from hW b w' hrun
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  cases key with
  | nil => simp [keyWf] at hkey
  | cons c rest =>
    exact wputa_cls_putSegs hs hb rest c _ _ hkey ⟨hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      rfl, ⟨0, none, hm.sound.good⟩, fun q k' hr => hr, by
        show w.top.rootKey ∈ reach (treeOf i s w)
        rw [reach_of_root hm.root]
        exact tc_self _ _ _⟩

/-- Any put of a key as `Keys.toSegments` makes it keeps `MidP`: the run
follows the key's segments; at each segment leaf the klong of the segment is
found (the walk goes on), or not (new segment leaves, the leaf with room or
full); at the last segment the value's klong is set. -/
theorem putKv_put {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) {done : List Op} {w w' : MW} {b : Bool} {key : Key}
    {h : Nat} (hm : MidP p i base s tp done w) (hkey : keyWf key = true)
    (hrun : SIS.Tree.putKv (.put key h) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) : MidP p i base s tp (done ++ [Op.put key h]) w' := by
  rcases wputa_classify hs hb hm hkey hrun with hr | hr | hr
  · exact putKv_put_routed hp hs hb hn hm hkey hr hrun hout
  · exact putKv_put_newseg hp hs hb hm hkey hr hrun hout
  · exact putKv_put_newseg_full hp hs hb hn hm hkey hr hrun hout

/-! ## 9. A transaction of puts, and a run -/

/-- One transaction of puts: the model's writer meets the writer's contract
(`WriterMeets`' conclusion), from a tree whose key klongs name its nodes
(`SNamed`). -/
def WriterMeetsPut (p : MParams) (ops : List MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId) (t : SIS.Tree.Top)
    (w : MW),
    SNamed s → Before p i base s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
    OpsRun { p := p, i := i, view := v } { next := base, top := t } ops w →
    Contract (cpOf p) i s (ops.map opOf) (dirtyOf w) (treeOf i s w) ∧
      TreeOk ((treeOf i s w).at i) ∧ TopStep i tp (topOf i tp w) ∧
      (treeOf i s w).roots = rootsOf (topOf i tp w) ∧
      invOk (cpOf p) (treeOf i s w) = true ∧ TreeOk (treeOf i s w) ∧
      Balanced p (treeOf i s w) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → timesBefore (i + 1) n.ks = true) ∧
      (∀ r ∈ (treeOf i s w).roots, r.1 < i + 1) ∧
      (∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none) ∧
      (∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
        ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2)

/-- The accepted puts keep `MidP`. -/
theorem wputa_midP_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) :
    ∀ (ops : List MOp) (w w' : MW), OpsRun { p := p, i := i, view := v } w ops w' →
      (∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) →
      ∀ done, MidP p i base s tp done w → MidP p i base s tp (done ++ ops.map opOf) w' := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro _ done hm; simpa using hm
  | cons w w1 w' op ops b hk h1 h2 _ ih =>
    intro hops done hm
    obtain ⟨key, h, rfl⟩ := hops _ List.mem_cons_self
    have hm1 := putKv_put (key := key) hp hs hb hn hm hk h1 h2
    have := ih (fun o ho => hops o (List.mem_cons_of_mem _ ho)) _ hm1
    simpa [opOf] using this

/-- A transaction of puts meets the writer's contract. -/
theorem writerMeets_put {p : MParams} (hp : ParamsOK p) (ops : List MOp)
    (hops : ∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) : WriterMeetsPut p ops := by
  intro i base s tp v z t w hn hbf hs ht hrun
  have hb := hbf.books
  have hm : MidP p i base s tp (ops.map opOf) w := by
    have := wputa_midP_run hp hs hb hn ops _ w hrun hops [] (wput_midP_start hs ht hbf)
    simpa using this
  obtain ⟨hinv, hcont, htree⟩ := (sound_iff (M := p.M)).mpr ⟨_, hm.root, hm.sound⟩
  have hinv' : invOk (cpOf p) (treeOf i s w) = true := hinv
  have hat : (treeOf i s w).at i = treeOf i s w :=
    Tree.at_eq_self (wput_times hm hb) (wput_rootTimes hb)
  have hat0 : s.at (i - 1) = s := by
    apply Tree.at_eq_self
    · intro x n hx t' ht'
      exact Nat.le_sub_one_of_lt (timesBefore_iff.mp (hb.times x n hx) t' ht')
    · intro r hr
      exact Nat.le_sub_one_of_lt (hb.rootTimes r hr)
  refine ⟨⟨?_, hm.frame⟩, by rw [hat]; exact htree, hm.top.step, hm.top.roots, hinv', htree,
    hm.balanced, wput_first hm hb, ?_, ?_, wput_ids hm hb, hm.top.skips hb.skips⟩
  · simp only [contractOk, hat, hat0, hinv', hcont, Bool.true_and, beq_self_eq_true]
  · intro x n hx
    rw [timesBefore_iff]
    intro t' ht'
    exact Nat.lt_succ_of_le (wput_times hm hb x n hx t' ht')
  · intro r hr
    exact Nat.lt_succ_of_le (wput_rootTimes hb r hr)

/-- A run of the model's writer whose transactions are puts, each from a tree
whose key klongs name its nodes: `Runs` with these two premises at each step. -/
inductive RunsPut (p : MParams) : List (List Op) → Tree → Top → Prop where
  | start (s : Tree) (tp : Top) (base : NodeId) :
      Before p 1 base s tp → contents s = [] → TopStart tp → RunsPut p [] s tp
  | step (txs : List (List Op)) (s : Tree) (tp : Top) (ops : List MOp) (base : NodeId)
      (v : View BVal) (z : NodeId) (t : SIS.Tree.Top) (w : MW) :
      RunsPut p txs s tp → SNamed s → (∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) →
      Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
      (∀ x, base ≤ x → s.obj x = none ∧ tp.node x = none) →
      OpsRun { p := p, i := txs.length + 1, view := v } { next := base, top := t } ops w →
      RunsPut p (txs ++ [ops.map opOf]) (treeOf (txs.length + 1) s w)
        (topOf (txs.length + 1) tp w)

/-- Such a run is a run (`Runs`). -/
theorem RunsPut.runs {p : MParams} {txs : List (List Op)} {s : Tree} {tp : Top}
    (h : RunsPut p txs s tp) : Runs p txs s tp := by
  induction h with
  | start s tp base hb hc ht => exact Runs.start s tp base hb hc ht
  | step txs s tp ops base v z t w _ _ _ hs ht hids hrun ih =>
    exact Runs.step txs s tp ops base v z t w ih hs ht hids hrun

/-- A run of the model's writer whose transactions are puts, each from a tree
whose key klongs name its nodes, is a history that meets the writer's
contract, TREE and the top's clauses. -/
theorem runs_meetsTop_put {p : MParams} (hp : ParamsOK p) {txs : List (List Op)} {s : Tree}
    {tp : Top} (h : RunsPut p txs s tp) : MeetsTop (cpOf p) txs s tp := by
  have key : ∀ {txs : List (List Op)} {s : Tree} {tp : Top}, RunsPut p txs s tp →
      MeetsTop (cpOf p) txs s tp ∧ RunInv p txs s tp := by
    intro txs s tp h
    induction h with
    | start s tp base hb hc ht =>
      have hat : s.at 0 = s := by
        apply Tree.at_eq_self
        · intro x n hx t' ht'
          exact Nat.le_of_lt_succ (timesBefore_iff.mp (hb.books.times x n hx) t' ht')
        · intro r hr
          exact Nat.le_of_lt_succ (hb.books.rootTimes r hr)
      refine ⟨MeetsTop.start s tp ⟨by rw [hat]; exact hb.inv, by rw [hat]; exact hc⟩
        (by rw [hat]; exact hb.tree) ht hb.books.roots, ?_⟩
      exact ⟨hb.inv, hb.tree, hb.balanced, hb.books.first, hb.books.times, hb.books.rootTimes,
        hb.books.roots, hb.books.skips⟩
    | step txs s tp ops base v z t w _ hn hops hs ht hids hrun ih =>
      obtain ⟨hmeets, hinv⟩ := ih
      have hbf : Before p (txs.length + 1) base s tp :=
        ⟨hinv.inv, hinv.tree, hinv.balanced,
          ⟨hinv.first, hinv.times, hinv.rootTimes, hids, hinv.roots, hinv.skips⟩⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, hf, h8, h9, _, h11⟩ :=
        writerMeets_put hp ops hops (txs.length + 1) base s tp v z t w hn hbf hs ht hrun
      refine ⟨MeetsTop.step txs s tp (ops.map opOf) (dirtyOf w) _ _ hmeets h1 h2 h3 h4, ?_⟩
      refine ⟨h5, h6, h7, hf, ?_, ?_, h4, h11⟩
      · simpa using h8
      · simpa using h9
  exact (key h).1

end Contract
