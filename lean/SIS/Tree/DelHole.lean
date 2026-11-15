/-
The delete with its `afterDelete` calls as a parameter (bergdb 024-12, section 1):
`deleteUpwardP ad` is the writer's upward delete with `ad` in place of its two
calls of `afterDelete`, and `putKvDP ad` the delete above it. The writer's delete
and the checked copies are instances (`putKvDelChk5_eq`); two instances run alike
from every state when their `ad`s do (`rwp_putKvDP`).
-/
import SIS.Tree.CollapseCommuteTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's `deleteUpward` with `ad` in place of `afterDelete`. -/
def deleteUpwardP (ad : Key → Nat → Nat → M Unit) (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) :
    M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    ad key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBack x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if sn.leaf then
    note "up.stop-at-segment-leaf"
    let _ ← appendDeleteKlong s stop cs
    ad key gs hs
    return false
  if sn.smallestLive != some 0 then
    throw s!"Bug: the upward unlink at {tt}: inner node {s} has no live klong of the empty key"
  if cs != 0 then
    let _ ← appendDeleteKlong s stop cs
  else
    emptyKeyNext s stop
  if c.p.merges then
    let _ ← mergeUp key gs c.p.fuel hs false
  collapseRoot key segment (c.p.fuel)
  return false

/-- `setValueDelChk5` with `deleteUpwardP ad`. -/
def setValueDP (ad : Key → Nat → Nat → M Unit) (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardP ad leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk5` with `setValueDP ad`. -/
def putSegsDP (ad : Key → Nat → Nat → M Unit) (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDP ad segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDP ad key rest next

/-- The delete with `ad` in place of `afterDelete`. -/
def putKvDP (ad : Key → Nat → Nat → M Unit) (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDP ad key key root

theorem deleteUpwardChk5_eq (leaf : NodeId) (depth cv : Nat) (key : Key) :
    deleteUpwardChk5 leaf depth cv key = deleteUpwardP afterDeleteChk leaf depth cv key := rfl

theorem putSegsDelChk5_eq (key : Key) :
    ∀ (segs : List Nat) (r : NodeId), putSegsDelChk5 key segs r = putSegsDP afterDeleteChk key segs r := by
  intro segs
  induction segs with
  | nil => intro r; rfl
  | cons cv rest ih =>
    intro r
    cases rest with
    | nil => rfl
    | cons d rest' =>
      unfold putSegsDelChk5 putSegsDP
      simp only [ih]
      rfl

/-- The checked copy of 2026-11-15 (`putKvDelChk5`) is `putKvDP afterDeleteChk`. -/
theorem putKvDelChk5_eq (key : Key) : putKvDelChk5 key = putKvDP afterDeleteChk key := by
  unfold putKvDelChk5 putKvDP
  simp only [putSegsDelChk5_eq]

/-! ## Two instances run alike when their `ad`s do -/

theorem rwp_ite {β : Type} {b : Prop} [Decidable b] {f1 f2 g1 g2 : M β} {c : Ctx} {w : W}
    (h1 : b → RWP f1 g1 c w) (h2 : ¬ b → RWP f2 g2 c w) :
    RWP (if b then f1 else f2) (if b then g1 else g2) c w := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte]; exact h1 hb
  · simp only [hb, ↓reduceIte]; exact h2 hb

theorem rwp_bind_left {α β : Type} {m1 m2 : M α} {k : α → M β} {c : Ctx} {w : W}
    (h : RWP m1 m2 c w) : RWP (m1 >>= k) (m2 >>= k) c w :=
  rwp_bind2 (fun _ _ => True) h (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)

theorem rwp_deleteUpwardP (a1 a2 : Key → Nat → Nat → M Unit) (c : Ctx)
    (h : ∀ key g h v, RWP (a1 key g h) (a2 key g h) c v)
    (leaf : NodeId) (depth cv : Nat) (key : Key) (w : W) :
    RWP (deleteUpwardP a1 leaf depth cv key) (deleteUpwardP a2 leaf depth cv key) c w := by
  unfold deleteUpwardP
  refine rwp_bind_any (fun c' v => ?_)
  refine rwp_bind_any (fun n v1 => ?_)
  dsimp only
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun _ => ?_)
  refine rwp_ite (fun _ => ?_) (fun _ => ?_)
  · refine rwp_bind_any (fun gh v2 => ?_)
    rcases gh with ⟨g, hh⟩
    refine rwp_bind_any (fun _ v3 => ?_)
    exact rwp_bind_left (h key g hh v3)
  · refine rwp_bind_any (fun stop v2 => ?_)
    refine rwp_ite (fun _ => rwp_refl _ _ _) (fun _ => ?_)
    refine rwp_bind_any (fun _ v3 => ?_)
    refine rwp_bind_any (fun w4 v4 => ?_)
    refine rwp_bind_any (fun seg v5 => ?_)
    refine rwp_bind_any (fun _ v6 => ?_)
    refine rwp_bind_any (fun s v7 => ?_)
    refine rwp_bind_any (fun cs v8 => ?_)
    refine rwp_bind_any (fun sn v9 => ?_)
    refine rwp_bind_any (fun gh v10 => ?_)
    rcases gh with ⟨gs, hs⟩
    dsimp only
    refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
    refine rwp_bind_any (fun _ v11 => ?_)
    refine rwp_bind_any (fun _ v12 => ?_)
    exact rwp_bind_left (h key gs hs v12)

theorem rwp_putSegsDP (a1 a2 : Key → Nat → Nat → M Unit) (c : Ctx)
    (h : ∀ key g h v, RWP (a1 key g h) (a2 key g h) c v) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId) (w : W), RWP (putSegsDP a1 key segs r) (putSegsDP a2 key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro r w; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro r w
    cases rest with
    | nil =>
      unfold putSegsDP setValueDP
      refine rwp_bind_any (fun c' v => ?_)
      refine rwp_bind_any (fun leaf v1 => ?_)
      refine rwp_bind_any (fun sz v2 => ?_)
      exact rwp_bind_left (rwp_deleteUpwardP a1 a2 c h _ _ _ _ _)
    | cons d rest' =>
      unfold putSegsDP
      refine rwp_bind_any (fun res v => ?_)
      cases res with
      | none => exact rwp_refl _ _ _
      | some y => exact ih y v

/-- Two instances of the delete run alike from every state when their `ad`s do. -/
theorem rwp_putKvDP (a1 a2 : Key → Nat → Nat → M Unit) (c : Ctx)
    (h : ∀ key g h v, RWP (a1 key g h) (a2 key g h) c v) (key : Key) (w : W) :
    RWP (putKvDP a1 key) (putKvDP a2 key) c w := by
  unfold putKvDP
  refine rwp_bind_any (fun _ v => ?_)
  refine rwp_bind_any (fun root v1 => ?_)
  exact rwp_putSegsDP a1 a2 c h key key root v1

end SIS.Tree
