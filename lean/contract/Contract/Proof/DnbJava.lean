/-
bergdb 030-29: Java's walk (`DNB.walkAll`, Contract/DirtyBound.lean) as the
path of each key and what it leaves in the records of the nodes it passes.

* `descP`, `keyP`: the walk of one key without the records, the same
  recursion as `descend` and `walkKey`; `descend_eq`, `walkKey_eq`: Java's
  walk is the records reached along that path (`chainW`), then what the key
  does at its end (`endEff`): a put's klong at the leaf of its last segment,
  a put's new segment tree (`addFresh`), or a delete's climb (`markDelete`).
* The records: `Walk.get?` after `modify` and `reach`; `markDelete_eq`: the
  climb along a path whose records name their parents gives each node of the
  path four klongs, `deleteBelow`, and a segment tree's root below a segment
  leaf its height as its collapses (`delStep`).
-/
import Contract.Proof.DnbSpec

namespace Contract.DNB

/-! ## Records by node -/

theorem Walk.get?_some {ws : Walk} {y : NodeId} {w : Walked} (h : ws.get? y = some w) :
    w ∈ ws ∧ w.x = y := by
  unfold Walk.get? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem Walk.get?_eq_none {ws : Walk} {y : NodeId} : ws.get? y = none ↔ y ∉ ws.map (·.x) := by
  unfold Walk.get?
  rw [List.find?_eq_none]
  simp

theorem Walk.get?_of_mem {ws : Walk} {w : Walked} (hw : w ∈ ws) (hnd : (ws.map (·.x)).Nodup) :
    ws.get? w.x = some w := by
  induction ws with
  | nil => cases hw
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold Walk.get? at ih ⊢
    rcases List.mem_cons.mp hw with rfl | hw
    · simp
    · have hne : a.x ≠ w.x := fun he => hnd.1 (he ▸ List.mem_map_of_mem hw)
      have hb : (a.x == w.x) = false := by simpa using hne
      rw [List.find?_cons, hb]
      exact ih hw hnd.2

theorem Walk.get?_modify (ws : Walk) (u y : NodeId) (f : Walked → Walked) (hf : ∀ w, (f w).x = w.x) :
    (ws.modify u f).get? y = if y = u then (ws.get? y).map f else ws.get? y := by
  unfold Walk.modify Walk.get?
  rw [List.find?_map]
  have e : ((fun w : Walked => w.x == y) ∘ (fun w => if w.x == u then f w else w)) =
      (fun w : Walked => w.x == y) := by
    funext w
    simp only [Function.comp_apply]
    split <;> simp [hf]
  rw [e]
  cases h : List.find? (fun w : Walked => w.x == y) ws with
  | none => split <;> rfl
  | some w =>
    have hx : w.x = y := by simpa using List.find?_some h
    simp only [Option.map_some]
    by_cases hyu : y = u
    · subst hyu; simp [hx]
    · have : (w.x == u) = false := by simpa [hx] using hyu
      simp [this, hyu]

theorem Walk.map_x_modify (ws : Walk) (u : NodeId) (f : Walked → Walked) (hf : ∀ w, (f w).x = w.x) :
    (ws.modify u f).map (·.x) = ws.map (·.x) := by
  unfold Walk.modify
  rw [List.map_map]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply]
  split <;> simp [hf]

/-- The record that `Walk.reach` makes. -/
def Walk.newRec (ws : Walk) (x : NodeId) (n : KNode) (up : Option NodeId) : Walked :=
  { x := x, up := up,
    depth := match up with
      | some u => ((ws.get? u).map (·.depth + 1)).getD 0
      | none => 0,
    size := n.ks.length, leaf := n.leaf, klongs := 0, collapses := 0, deleteBelow := false,
    dead := deadCount n.ks, fresh := [], freshLevel := 0 }

theorem Walk.reach_eq (ws : Walk) (x : NodeId) (n : KNode) (up : Option NodeId) :
    ws.reach x n up = if (ws.get? x).isSome then ws else ws ++ [Walk.newRec ws x n up] := by
  unfold Walk.reach Walk.newRec
  rfl

theorem Walk.get?_reach (ws : Walk) (x : NodeId) (n : KNode) (up : Option NodeId) (y : NodeId) :
    (ws.reach x n up).get? y =
      if (ws.get? x).isSome then ws.get? y
      else if y = x then some (Walk.newRec ws x n up) else ws.get? y := by
  rw [Walk.reach_eq]
  by_cases hx : (ws.get? x).isSome
  · simp [hx]
  · simp only [hx, ite_false, Bool.false_eq_true]
    have hn : ws.get? x = none := by simpa using hx
    unfold Walk.get? at hn ⊢
    rw [List.find?_append]
    by_cases hyx : y = x
    · subst hyx
      simp [hn, Walk.newRec]
    · cases h : List.find? (fun w : Walked => w.x == y) ws with
      | some w => simp [hyx]
      | none => simp [hyx, Walk.newRec, Ne.symm hyx]

theorem Walk.nodup_reach {ws : Walk} (hnd : (ws.map (·.x)).Nodup) (x : NodeId) (n : KNode)
    (up : Option NodeId) : ((ws.reach x n up).map (·.x)).Nodup := by
  rw [Walk.reach_eq]
  split
  · exact hnd
  · rename_i hx
    have hn : x ∉ ws.map (·.x) := Walk.get?_eq_none.mp (by simpa using hx)
    rw [List.map_append, List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton, Walk.newRec] at hb
    subst hb
    exact fun h => hn (h ▸ ha)

/-! ## The walk of one key without the records -/

/-- `descend` without the records: the nodes reached after x, and the node it
stops at. -/
def descP (s : Tree) (c : Nat) : Nat → NodeId → List NodeId × NodeId
  | 0, x => ([], x)
  | f + 1, x =>
    match getKey s x with
    | none => ([], x)
    | some n =>
      if n.leaf then ([], x) else
        match searchLte n.ks (.at c) with
        | none => ([], x)
        | some (_, y) =>
          match getKey s y with
          | some _ => (y :: (descP s c f y).1, (descP s c f y).2)
          | none => ([], x)

/-- How a key's walk ends: at the leaf of its last segment (`last`), at a leaf
without the key's next segment (`fresh`), or otherwise (`stop`). -/
inductive WEnd where
  | last
  | fresh
  | stop
  deriving DecidableEq, Repr

/-- `walkKey` without the records: the nodes reached after x, the node it
stops at, the segment there, and how it ends. -/
def keyP (s : Tree) (key : Key) : Nat → Nat → NodeId → List NodeId × NodeId × Nat × WEnd
  | 0, i, x => ([], x, i, .stop)
  | f + 1, i, x =>
    match key[i]? with
    | none => ([], x, i, .stop)
    | some c =>
      if i + 1 = key.length then
        ((descP s c (s.fuel x) x).1, (descP s c (s.fuel x) x).2, i, .last)
      else
        match (getKey s (descP s c (s.fuel x) x).2).bind (fun n => searchEq n.ks c) with
        | none => ((descP s c (s.fuel x) x).1, (descP s c (s.fuel x) x).2, i, .fresh)
        | some y =>
          match getKey s y with
          | some _ => ((descP s c (s.fuel x) x).1 ++ y :: (keyP s key f (i + 1) y).1,
              (keyP s key f (i + 1) y).2)
          | none => ((descP s c (s.fuel x) x).1, (descP s c (s.fuel x) x).2, i, .stop)

/-- The nodes `ys` walked in order, each with the one before it (x for the
first) above it. -/
def chainW (s : Tree) : Walk → NodeId → List NodeId → Walk
  | ws, _, [] => ws
  | ws, x, y :: ys =>
    chainW s (match getKey s y with
      | some n => ws.reach y n (some x)
      | none => ws) y ys

theorem chainW_append (s : Tree) : ∀ (ws : Walk) (x : NodeId) (A B : List NodeId),
    chainW s ws x (A ++ B) = chainW s (chainW s ws x A) (A.getLastD x) B
  | ws, x, [], B => rfl
  | ws, x, a :: A, B => by
    simp only [List.cons_append, chainW]
    rw [chainW_append s _ a A B]
    congr 1
    cases A <;> simp [List.getLastD]

theorem descP_stop (s : Tree) (c : Nat) : ∀ (f : Nat) (x : NodeId),
    (descP s c f x).2 = (descP s c f x).1.getLastD x
  | 0, x => rfl
  | f + 1, x => by
    cases hk : getKey s x with
    | none => simp [descP, hk]
    | some n =>
      by_cases hl : n.leaf = true
      · simp [descP, hk, hl]
      · cases hs : searchLte n.ks (.at c) with
        | none => simp [descP, hk, hl, hs]
        | some cy =>
          obtain ⟨c', y⟩ := cy
          cases hy : getKey s y with
          | none => simp [descP, hk, hl, hs, hy]
          | some ny =>
            simp only [descP, hk, hl, hs, hy, Bool.false_eq_true, ite_false]
            rw [descP_stop s c f y]
            cases (descP s c f y).1 <;> simp [List.getLastD]

/-- **`descend` is the descent without the records**, its nodes walked in
order. -/
theorem descend_eq (s : Tree) (c : Nat) : ∀ (f : Nat) (ws : Walk) (x : NodeId),
    descend s c f ws x = (chainW s ws x (descP s c f x).1, (descP s c f x).2)
  | 0, ws, x => rfl
  | f + 1, ws, x => by
    cases hk : getKey s x with
    | none => simp [descend, descP, hk, chainW]
    | some n =>
      by_cases hl : n.leaf = true
      · simp [descend, descP, hk, hl, chainW]
      · cases hs : searchLte n.ks (.at c) with
        | none => simp [descend, descP, hk, hl, hs, chainW]
        | some cy =>
          obtain ⟨c', y⟩ := cy
          cases hy : getKey s y with
          | none => simp [descend, descP, hk, hl, hs, hy, chainW]
          | some ny =>
            simp only [descend, descP, hk, hl, hs, hy, Bool.false_eq_true, ite_false]
            rw [descend_eq s c f]
            simp only [chainW, hy]

/-- What a key does at the end of its walk, on the records after its walk. -/
def endEff (key : Key) (del : Bool) (ws : Walk) : NodeId × Nat × WEnd → Walk × Option NodeId
  | (z, _, .last) =>
    if del then (markDelete ((((ws.get? z).map (·.depth)).getD 0) + 1) ws (some z) none 0, some z)
    else (ws.modify z (fun w => { w with klongs := w.klongs + 1 }), none)
  | (z, j, .fresh) => if del then (ws, none) else (ws.modify z (Walked.addFresh key j), none)
  | (_, _, .stop) => (ws, none)

/-- **`walkKey` is the walk without the records**: the nodes of the path
walked in order, then what the key does at its end. -/
theorem walkKey_eq (s : Tree) (key : Key) (del : Bool) : ∀ (f i : Nat) (ws : Walk) (x : NodeId),
    walkKey s key del f i ws x =
      endEff key del (chainW s ws x (keyP s key f i x).1) (keyP s key f i x).2
  | 0, i, ws, x => rfl
  | f + 1, i, ws, x => by
    cases hc : key[i]? with
    | none => simp [walkKey, keyP, hc, chainW, endEff]
    | some c =>
      by_cases hl : i + 1 = key.length
      · simp only [walkKey, keyP, hc, hl, ite_true, descend_eq]
        rfl
      · cases hq : (getKey s (descP s c (s.fuel x) x).2).bind (fun n => searchEq n.ks c) with
        | none =>
          simp only [walkKey, keyP, hc, hl, ite_false, descend_eq, hq]
          rfl
        | some y =>
          cases hy : getKey s y with
          | none =>
            simp only [walkKey, keyP, hc, hl, ite_false, descend_eq, hq, hy]
            rfl
          | some ny =>
            simp only [walkKey, keyP, hc, hl, ite_false, descend_eq, hq, hy]
            rw [walkKey_eq s key del f (i + 1), chainW_append, ← descP_stop]
            simp only [chainW, hy]

/-! ## Records that name their parents -/

/-- The tree's facts the records use: each node's parent (`up`) and depth
(`dep`), whether it is a segment leaf (`lf`), and its height (`col`, what a
delete's climb gives a segment tree's root as its collapses). -/
structure TreeFn where
  up : NodeId → Option NodeId
  dep : NodeId → Nat
  lf : NodeId → Bool
  col : NodeId → Nat

/-- The record Java makes for node z when it first reaches it. -/
def initR (s : Tree) (E : TreeFn) (z : NodeId) : Walked :=
  match getKey s z with
  | some n =>
    { x := z, up := E.up z, depth := E.dep z, size := n.ks.length, leaf := n.leaf,
      klongs := 0, collapses := 0, deleteBelow := false, dead := deadCount n.ks, fresh := [],
      freshLevel := 0 }
  | none => default

/-- Every record has its node's parent, depth and kind. -/
def RecOk (E : TreeFn) (ws : Walk) : Prop :=
  ∀ z w, ws.get? z = some w → w.up = E.up z ∧ w.depth = E.dep z ∧ w.leaf = E.lf z

/-- A change of a record that keeps its node, parent, depth and kind. -/
def Keeps (f : Walked → Walked) : Prop :=
  ∀ w, (f w).x = w.x ∧ (f w).up = w.up ∧ (f w).depth = w.depth ∧ (f w).leaf = w.leaf

theorem recOk_modify {E : TreeFn} {ws : Walk} (h : RecOk E ws) (u : NodeId) {f : Walked → Walked}
    (hf : Keeps f) : RecOk E (ws.modify u f) := by
  intro z w hw
  rw [Walk.get?_modify _ _ _ _ (fun w => (hf w).1)] at hw
  split at hw
  · obtain ⟨w0, h0, rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨a, b, c⟩ := h z w0 h0
    exact ⟨(hf w0).2.1.trans a, (hf w0).2.2.1.trans b, (hf w0).2.2.2.trans c⟩
  · exact h z w hw

/-- The facts of a node z of the tree that `initR` and `reach` agree on: a key
node, its kind `lf`. -/
def NodeOk (s : Tree) (E : TreeFn) (z : NodeId) : Prop :=
  ∃ n, getKey s z = some n ∧ E.lf z = n.leaf

theorem initR_x (s : Tree) (E : TreeFn) {z : NodeId} (hz : NodeOk s E z) : (initR s E z).x = z := by
  obtain ⟨n, hn, _⟩ := hz
  simp [initR, hn]

theorem newRec_eq {s : Tree} {E : TreeFn} {ws : Walk} (hws : RecOk E ws) {x y : NodeId} {n : KNode}
    (hn : getKey s y = some n) (hup : E.up y = some x) (hdep : E.dep y = E.dep x + 1)
    (hx : (ws.get? x).isSome) : Walk.newRec ws y n (some x) = initR s E y := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hx
  have hd := (hws x w hw).2.1
  simp [Walk.newRec, initR, hn, hw, hd, hup, hdep]

/-- The path's links: x first, then each node a key node whose parent is the
one before it, one deeper. -/
def Links (s : Tree) (E : TreeFn) : NodeId → List NodeId → Prop
  | _, [] => True
  | x, y :: ys => NodeOk s E y ∧ E.up y = some x ∧ E.dep y = E.dep x + 1 ∧ Links s E y ys

/-- **The nodes of a path walked in order**: a node not yet walked gets its
record (`initR`); the others keep theirs. -/
theorem chainW_get? {s : Tree} {E : TreeFn} : ∀ (ys : List NodeId) (ws : Walk) (x : NodeId),
    RecOk E ws → (ws.map (·.x)).Nodup → (ws.get? x).isSome → Links s E x ys →
      RecOk E (chainW s ws x ys) ∧ ((chainW s ws x ys).map (·.x)).Nodup ∧
      ∀ z, (chainW s ws x ys).get? z =
        if z ∈ ys ∧ ws.get? z = none then some (initR s E z) else ws.get? z
  | [], ws, x, hr, hnd, _, _ => ⟨hr, hnd, fun z => by simp [chainW]⟩
  | y :: ys, ws, x, hr, hnd, hx, hl => by
    obtain ⟨⟨n, hn, hlf⟩, hup, hdep, hl'⟩ := hl
    simp only [chainW, hn]
    have hget : ∀ z, (ws.reach y n (some x)).get? z =
        if z = y ∧ ws.get? z = none then some (initR s E z) else ws.get? z := by
      intro z
      rw [Walk.get?_reach]
      by_cases hy : (ws.get? y).isSome
      · have : ¬ (z = y ∧ ws.get? z = none) := by
          rintro ⟨rfl, h⟩; rw [h] at hy; cases hy
        simp [hy, this]
      · have hy' : ws.get? y = none := by simpa using hy
        simp only [hy, Bool.false_eq_true, ite_false]
        by_cases hzy : z = y
        · subst hzy; simp [hy', newRec_eq hr hn hup hdep hx]
        · simp [hzy]
    have hr1 : RecOk E (ws.reach y n (some x)) := by
      intro z w hw
      rw [hget] at hw
      split at hw
      · rename_i hc
        obtain ⟨rfl, _⟩ := hc
        cases hw
        simp [initR, hn, hlf]
      · exact hr z w hw
    have hnd1 := Walk.nodup_reach hnd y n (some x)
    have hy1 : ((ws.reach y n (some x)).get? y).isSome := by
      rw [hget]
      split
      · rfl
      · rename_i hc
        simp only [true_and] at hc
        exact Option.isSome_iff_ne_none.mpr hc
    obtain ⟨h1, h2, h3⟩ := chainW_get? ys _ y hr1 hnd1 hy1 hl'
    refine ⟨h1, h2, fun z => ?_⟩
    rw [h3, hget]
    by_cases hzy : z = y
    · subst hzy
      by_cases h0 : ws.get? z = none
      · simp [h0]
      · simp [h0]
    · by_cases h0 : ws.get? z = none
      · simp [hzy, h0]
      · simp [hzy, h0]

/-! ## A delete's climb -/

/-- The parent of z is a segment leaf. -/
def TreeFn.pleaf (E : TreeFn) (z : NodeId) : Bool :=
  match E.up z with
  | some u => E.lf u
  | none => false

/-- What a delete that reaches its last segment gives each node of its path:
four klongs, `deleteBelow`, and to a segment tree's root below a segment leaf
its height as its collapses, at least. -/
def delStep (E : TreeFn) (z : NodeId) (w : Walked) : Walked :=
  { w with klongs := w.klongs + 4, deleteBelow := true,
           collapses := if E.pleaf z then max w.collapses (E.col z) else w.collapses }

/-- A segment tree's root's collapses, at least its height. -/
def colStep (E : TreeFn) (z : NodeId) (w : Walked) : Walked :=
  { w with collapses := max w.collapses (E.col z) }

theorem get?_modify_ne {ws : Walk} {u z : NodeId} (f : Walked → Walked) (hf : Keeps f) (h : z ≠ u) :
    (ws.modify u f).get? z = ws.get? z := by
  rw [Walk.get?_modify _ _ _ _ (fun w => (hf w).1)]; simp [h]

theorem get?_modify_eq {ws : Walk} {u : NodeId} (f : Walked → Walked) (hf : Keeps f) :
    (ws.modify u f).get? u = (ws.get? u).map f := by
  rw [Walk.get?_modify _ _ _ _ (fun w => (hf w).1)]; simp

theorem map_x_modify' {ws : Walk} {u : NodeId} (f : Walked → Walked) (hf : Keeps f) :
    (ws.modify u f).map (·.x) = ws.map (·.x) :=
  Walk.map_x_modify _ _ _ (fun w => (hf w).1)

/-- Four klongs and `deleteBelow`. -/
def kdStep (w : Walked) : Walked := { w with klongs := w.klongs + 4, deleteBelow := true }

/-- The collapses at least i. -/
def csStep (i : Nat) (w : Walked) : Walked := { w with collapses := max w.collapses i }

theorem keeps_kd : Keeps kdStep := fun _ => ⟨rfl, rfl, rfl, rfl⟩
theorem keeps_cs (i : Nat) : Keeps (csStep i) := fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem markDelete_unfold (f : Nat) (ws : Walk) (y : NodeId) (w : Walked) (hw : ws.get? y = some w)
    (below : Option NodeId) (inner : Nat) :
    markDelete (f + 1) ws (some y) below inner =
      if w.leaf then
        markDelete f (match below with
          | some b => (ws.modify w.x kdStep).modify b (csStep inner)
          | none => ws.modify w.x kdStep) w.up (some w.x) 0
      else markDelete f (ws.modify w.x kdStep) w.up (some w.x) (inner + 1) := by
  simp only [markDelete, Option.bind_some, hw]
  rfl

theorem map_x_markDelete : ∀ (f : Nat) (ws : Walk) (cur below : Option NodeId) (inner : Nat),
    (markDelete f ws cur below inner).map (·.x) = ws.map (·.x)
  | 0, ws, _, _, _ => rfl
  | f + 1, ws, cur, below, inner => by
    cases hc : cur.bind ws.get? with
    | none => simp [markDelete, hc]
    | some u =>
      obtain ⟨y, rfl, hy⟩ : ∃ y, cur = some y ∧ ws.get? y = some u := by
        cases cur with
        | none => cases hc
        | some y => exact ⟨y, rfl, hc⟩
      rw [markDelete_unfold f ws y u hy]
      split
      · rw [map_x_markDelete]
        cases below with
        | none => exact map_x_modify' _ keeps_kd
        | some b => rw [map_x_modify' _ (keeps_cs _), map_x_modify' _ keeps_kd]
      · rw [map_x_markDelete, map_x_modify' _ keeps_kd]

/-- The climb's nodes: each node's parent is the next, the last has none. -/
def UpChain (E : TreeFn) : List NodeId → Prop
  | [] => True
  | [y] => E.up y = none
  | a :: b :: r => E.up a = some b ∧ UpChain E (b :: r)

theorem upChain_head (E : TreeFn) : ∀ (y : NodeId) (L : List NodeId), UpChain E (y :: L) →
    E.up y = L.head? ∧ UpChain E L
  | _, [], h => ⟨h, trivial⟩
  | _, _ :: _, h => ⟨h.1, h.2⟩

theorem delStep_eq (E : TreeFn) (z : NodeId) (w : Walked) :
    delStep E z w = if E.pleaf z then csStep (E.col z) (kdStep w) else kdStep w := by
  unfold delStep csStep kdStep
  split <;> rfl

theorem delStep_fin (E : TreeFn) (z : NodeId) (P : Prop) [Decidable P] (hP : E.pleaf z = true ↔ P)
    (o : Option Walked) :
    (if P then (o.map kdStep).map (csStep (E.col z)) else o.map kdStep) = o.map (delStep E z) := by
  cases o with
  | none => split <;> rfl
  | some w =>
    simp only [Option.map_some, delStep_eq]
    by_cases hp : P
    · simp [hp, hP.mpr hp]
    · have : E.pleaf z = false := by simpa using (fun h => hp (hP.mp h))
      simp [hp, this]

/-- **The climb**: from the first node of L up through the records' parents,
each node of L once (L ends at the space root), with `below` the node climbed
from and `inner` its height: each node of L gets `delStep`, and `below` its
collapses if the first node of L is a segment leaf. -/
theorem markDelete_eq (E : TreeFn)
    (hcl : ∀ y, E.lf y = true → E.col y = 0)
    (hci : ∀ y b, E.up b = some y → E.lf y = false → E.col y = E.col b + 1) :
    ∀ (L : List NodeId) (ws : Walk) (below : Option NodeId) (inner : Nat),
    L.Nodup → RecOk E ws → (∀ y ∈ L, (ws.get? y).isSome) → UpChain E L →
    (below = none → inner = 0 ∧ ∀ y, L.head? = some y → E.lf y = true) →
    (∀ b, below = some b → b ∉ L ∧ inner = E.col b ∧ ∀ y, L.head? = some y → E.up b = some y) →
    ∀ z, (markDelete L.length ws L.head? below inner).get? z =
      if z ∈ L then (ws.get? z).map (delStep E z)
      else if below = some z ∧ (∃ y, L.head? = some y ∧ E.lf y = true) then
        (ws.get? z).map (csStep (E.col z))
      else ws.get? z
  | [], ws, below, inner, _, _, _, _, _, _, z => by
    simp [markDelete]
  | y :: L, ws, below, inner, hnd, hr, hex, hch, hnone, hsome, z => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hex y List.mem_cons_self)
    obtain ⟨hwup, _, hwlf⟩ := hr y w hw
    have hwx : w.x = y := (Walk.get?_some hw).2
    have hyL : y ∉ L := (List.nodup_cons.mp hnd).1
    obtain ⟨hupy, hch'⟩ := upChain_head E y L hch
    have hupL : w.up = L.head? := hwup.trans hupy
    have hnd' := (List.nodup_cons.mp hnd).2
    simp only [List.length_cons, List.head?_cons]
    rw [markDelete_unfold L.length ws y w hw, hupL, hwx]
    have hr1 : RecOk E (ws.modify y kdStep) := recOk_modify hr _ keeps_kd
    have hex1 : ∀ y' ∈ L, ((ws.modify y kdStep).get? y').isSome := by
      intro y' hy'
      have hne : y' ≠ y := fun h => hyL (h ▸ hy')
      rw [get?_modify_ne _ keeps_kd hne]
      exact hex y' (List.mem_cons_of_mem _ hy')
    have hsome' : ∀ b, some y = some b → b ∉ L ∧ E.col y = E.col b ∧
        ∀ y', L.head? = some y' → E.up b = some y' := by
      intro b hb
      cases hb
      exact ⟨hyL, rfl, fun y' hy' => hupy.trans hy'⟩
    have hpl : E.pleaf y = true ↔ ∃ y', L.head? = some y' ∧ E.lf y' = true := by
      unfold TreeFn.pleaf
      rw [hupy]
      cases L.head? <;> simp
    -- the node below, if any, is not on L
    have hbL : ∀ b, below = some b → b ≠ y ∧ b ∉ L := by
      intro b hb
      have := (hsome b hb).1
      exact ⟨fun h => this (h ▸ List.mem_cons_self), fun h => this (List.mem_cons_of_mem _ h)⟩
    by_cases hleaf : w.leaf = true
    · simp only [hleaf, ite_true]
      have hlf : E.lf y = true := hwlf ▸ hleaf
      have hcol0 : E.col y = 0 := hcl y hlf
      cases hb : below with
      | none =>
        simp only
        have IH := markDelete_eq E hcl hci L (ws.modify y kdStep) (some y) 0 hnd' hr1 hex1 hch'
          (fun h => by cases h) (fun b hb' => by
            obtain ⟨h1, h2, h3⟩ := hsome' b hb'; exact ⟨h1, hcol0 ▸ h2, h3⟩) z
        rw [IH]
        by_cases hzy : z = y
        · subst hzy
          rw [get?_modify_eq _ keeps_kd]
          simp only [hyL, List.mem_cons_self, ite_true, ite_false, true_and]
          exact delStep_fin E z _ hpl _
        · rw [get?_modify_ne _ keeps_kd hzy]
          simp [hzy, Ne.symm hzy]
      | some b =>
        simp only
        obtain ⟨hby, hbL'⟩ := hbL b hb
        have hinner : inner = E.col b := (hsome b hb).2.1
        have hr2 : RecOk E ((ws.modify y kdStep).modify b (csStep inner)) :=
          recOk_modify hr1 _ (keeps_cs _)
        have hex2 : ∀ y' ∈ L, (((ws.modify y kdStep).modify b (csStep inner)).get? y').isSome := by
          intro y' hy'
          have hne : y' ≠ b := fun h => hbL' (h ▸ hy')
          rw [get?_modify_ne _ (keeps_cs _) hne]
          exact hex1 y' hy'
        have IH := markDelete_eq E hcl hci L _ (some y) 0 hnd' hr2 hex2 hch'
          (fun h => by cases h) (fun b hb' => by
            obtain ⟨h1, h2, h3⟩ := hsome' b hb'; exact ⟨h1, hcol0 ▸ h2, h3⟩) z
        rw [IH]
        by_cases hzy : z = y
        · subst hzy
          rw [get?_modify_ne _ (keeps_cs _) (Ne.symm hby), get?_modify_eq _ keeps_kd]
          simp only [hyL, List.mem_cons_self, ite_true, ite_false, true_and]
          exact delStep_fin E z _ hpl _
        · by_cases hzb : z = b
          · subst hzb
            rw [get?_modify_eq _ (keeps_cs _), get?_modify_ne _ keeps_kd hzy, hinner]
            simp [hzy, hbL', hlf, Ne.symm hzy]
          · rw [get?_modify_ne _ (keeps_cs _) hzb, get?_modify_ne _ keeps_kd hzy]
            simp [hzy, Ne.symm hzy, Ne.symm hzb]
    · simp only [hleaf, Bool.false_eq_true, ite_false]
      have hlf : E.lf y = false := by rw [← hwlf]; simpa using hleaf
      obtain ⟨b, hb⟩ : ∃ b, below = some b := by
        cases hb : below with
        | none => exact absurd ((hnone hb).2 y rfl) (by rw [hlf]; decide)
        | some b => exact ⟨b, rfl⟩
      obtain ⟨hbL', hinner, hupb⟩ := hsome b hb
      have hcy : E.col y = inner + 1 := by rw [hinner]; exact hci y b (hupb y rfl) hlf
      have IH := markDelete_eq E hcl hci L (ws.modify y kdStep) (some y) (inner + 1) hnd' hr1 hex1
        hch' (fun h => by cases h) (fun b' hb' => by
          obtain ⟨h1, h2, h3⟩ := hsome' b' hb'; exact ⟨h1, hcy ▸ h2 ▸ rfl, h3⟩) z
      rw [IH]
      by_cases hzy : z = y
      · subst hzy
        rw [get?_modify_eq _ keeps_kd]
        simp only [hyL, List.mem_cons_self, ite_true, ite_false, true_and]
        exact delStep_fin E z _ hpl _
      · rw [get?_modify_ne _ keeps_kd hzy]
        by_cases hzb : z = b
        · subst hzb
          have : z ∉ L := fun h => hbL' (List.mem_cons_of_mem _ h)
          simp [this, hlf, hzy, Ne.symm hzy]
        · simp [hzy, hlf, Ne.symm hzy]

/-! ## The walk of all keys -/

theorem keyP_stop (s : Tree) (key : Key) : ∀ (f i : Nat) (x : NodeId),
    (keyP s key f i x).2.1 = (keyP s key f i x).1.getLastD x
  | 0, i, x => rfl
  | f + 1, i, x => by
    cases hc : key[i]? with
    | none => simp [keyP, hc]
    | some c =>
      by_cases hl : i + 1 = key.length
      · simp only [keyP, hc, hl, ite_true]; exact descP_stop s c _ x
      · cases hq : (getKey s (descP s c (s.fuel x) x).2).bind (fun n => searchEq n.ks c) with
        | none => simp only [keyP, hc, hl, ite_false, hq]; exact descP_stop s c _ x
        | some y =>
          cases hy : getKey s y with
          | none => simp only [keyP, hc, hl, ite_false, hq, hy]; exact descP_stop s c _ x
          | some ny =>
            simp only [keyP, hc, hl, ite_false, hq, hy]
            rw [keyP_stop s key f (i + 1) y]
            simp [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_cons]

/-- A key's path: the space root r and the nodes its walk reaches. -/
def pathOf (s : Tree) (r : NodeId) (key : Key) : List NodeId := r :: (keyP s key (key.length + 1) 0 r).1

/-- Where a key's walk ends: the node, its segment, how. -/
def endOf (s : Tree) (r : NodeId) (key : Key) : NodeId × Nat × WEnd := (keyP s key (key.length + 1) 0 r).2

/-- What a key (a delete if `del`) does to the record of node y of its path,
given where it ends. -/
def effAt (E : TreeFn) (y : NodeId) (key : Key) (del : Bool) : NodeId × Nat × WEnd → Walked → Walked
  | (z, _, .last), w => if del then delStep E y w else if y = z then { w with klongs := w.klongs + 1 } else w
  | (z, j, .fresh), w => if del then w else if y = z then Walked.addFresh key j w else w
  | (_, _, .stop), w => w

/-- One key's change of the record of node y. -/
def stepR (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (w : Walked) (kd : Key × Bool) : Walked :=
  if y ∈ pathOf s r kd.1 then effAt E y kd.1 kd.2 (endOf s r kd.1) w else w

/-- The record of node y after the keys O. -/
def recOf (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (O : List (Key × Bool)) : Walked :=
  O.foldl (stepR s r E y) (initR s E y)

/-- Some key of O passes y. -/
def walkedBy (s : Tree) (r : NodeId) (O : List (Key × Bool)) (y : NodeId) : Bool :=
  O.any (fun kd => decide (y ∈ pathOf s r kd.1))

/-- The records after the keys O: one for each node a key passes, `recOf`. -/
def JI (s : Tree) (r : NodeId) (E : TreeFn) (ws : Walk) (O : List (Key × Bool)) : Prop :=
  (ws.map (·.x)).Nodup ∧ ∀ y, ws.get? y = if walkedBy s r O y then some (recOf s r E y O) else none

/-- What the proof needs of a key's path: its links (each node a key node, its
parent the one before, one deeper), and a walk that reaches its last segment
ends at a segment leaf. -/
structure PathOk (s : Tree) (r : NodeId) (E : TreeFn) (key : Key) : Prop where
  links : Links s E r (keyP s key (key.length + 1) 0 r).1
  leaf : (endOf s r key).2.2 = .last → E.lf (endOf s r key).1 = true

theorem links_dep {s : Tree} {E : TreeFn} : ∀ (x : NodeId) (ys : List NodeId), Links s E x ys →
    (∀ y ∈ ys, E.dep x < E.dep y) ∧ (x :: ys).Nodup ∧ E.dep (ys.getLastD x) = E.dep x + ys.length
  | x, [], _ => ⟨by simp, by simp, by simp⟩
  | x, y :: ys, ⟨_, _, hd, hl⟩ => by
    obtain ⟨h1, h2, h3⟩ := links_dep y ys hl
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · have := h1 z hz; omega
    · refine List.nodup_cons.mpr ⟨?_, h2⟩
      intro hx
      rcases List.mem_cons.mp hx with h | h
      · rw [← h] at hd; omega
      · have := h1 x h; omega
    · have e : (y :: ys).getLastD x = ys.getLastD y := by
        cases ys <;> simp [List.getLastD]
      rw [e, h3]
      simp; omega

theorem links_upChain {s : Tree} {E : TreeFn} : ∀ (x : NodeId) (ys L : List NodeId),
    Links s E x ys → UpChain E (x :: L) → UpChain E (ys.reverse ++ x :: L)
  | x, [], L, _, h => h
  | x, y :: ys, L, ⟨_, hu, _, hl⟩, h => by
    rw [List.reverse_cons, List.append_assoc]
    exact links_upChain y ys (x :: L) hl ⟨hu, h⟩

theorem links_mem {s : Tree} {E : TreeFn} : ∀ (x : NodeId) (ys : List NodeId), Links s E x ys →
    ∀ y ∈ ys, NodeOk s E y
  | _, [], _ => by simp
  | _, y :: ys, ⟨h0, _, _, hl⟩ => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h0
    · exact links_mem y ys hl z hz

theorem keeps_addFresh (key : Key) (i : Nat) : Keeps (Walked.addFresh key i) := by
  intro w
  unfold Walked.addFresh
  dsimp only
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_k1 : Keeps (fun w : Walked => { w with klongs := w.klongs + 1 }) :=
  fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_delStep (E : TreeFn) (z : NodeId) : Keeps (delStep E z) :=
  fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem keeps_effAt (E : TreeFn) (y : NodeId) (key : Key) (del : Bool) (e : NodeId × Nat × WEnd) :
    Keeps (effAt E y key del e) := by
  intro w
  obtain ⟨z, j, e⟩ := e
  cases e with
  | last =>
    simp only [effAt]
    split
    · exact keeps_delStep E y w
    · split
      · exact keeps_k1 w
      · exact ⟨rfl, rfl, rfl, rfl⟩
  | fresh =>
    simp only [effAt]
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · exact keeps_addFresh key j w
      · exact ⟨rfl, rfl, rfl, rfl⟩
  | stop => exact ⟨rfl, rfl, rfl, rfl⟩

theorem recOf_append (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (O : List (Key × Bool))
    (kd : Key × Bool) : recOf s r E y (O ++ [kd]) = stepR s r E y (recOf s r E y O) kd := by
  simp [recOf, List.foldl_append]

theorem recOf_keeps (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (O : List (Key × Bool)) :
    (recOf s r E y O).x = (initR s E y).x ∧ (recOf s r E y O).up = (initR s E y).up ∧
      (recOf s r E y O).depth = (initR s E y).depth ∧ (recOf s r E y O).leaf = (initR s E y).leaf := by
  unfold recOf
  generalize initR s E y = w0
  induction O generalizing w0 with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons kd O ih =>
    rw [List.foldl_cons]
    obtain ⟨a, b, c, d⟩ := ih (stepR s r E y w0 kd)
    have hk : Keeps (fun w => stepR s r E y w kd) := by
      intro w; unfold stepR; split
      · exact keeps_effAt E y kd.1 kd.2 _ w
      · exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨a', b', c', d'⟩ := hk w0
    exact ⟨a.trans a', b.trans b', c.trans c', d.trans d'⟩

theorem initR_fields {s : Tree} {E : TreeFn} {y : NodeId} (hy : NodeOk s E y) :
    (initR s E y).x = y ∧ (initR s E y).up = E.up y ∧ (initR s E y).depth = E.dep y ∧
      (initR s E y).leaf = E.lf y := by
  obtain ⟨n, hn, hl⟩ := hy
  simp [initR, hn, hl]

theorem recOf_not (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) :
    ∀ (O : List (Key × Bool)), walkedBy s r O y = false → recOf s r E y O = initR s E y := by
  intro O hO
  unfold recOf
  suffices h : ∀ (O : List (Key × Bool)) (w : Walked), walkedBy s r O y = false →
      O.foldl (stepR s r E y) w = w from h O _ hO
  intro O
  induction O with
  | nil => intro w _; rfl
  | cons kd O ih =>
    intro w h
    simp only [walkedBy, List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    rw [List.foldl_cons]
    have : stepR s r E y w kd = w := by simp [stepR, h.1]
    rw [this]
    exact ih w h.2

theorem recOk_of_get {s : Tree} {r : NodeId} {E : TreeFn} {ws : Walk} {O : List (Key × Bool)}
    (p : NodeId → Bool) (hget : ∀ y, ws.get? y = if p y then some (recOf s r E y O) else none)
    (hn : ∀ y, p y = true → NodeOk s E y) : RecOk E ws := by
  intro z w hw
  rw [hget] at hw
  split at hw
  · rename_i hz
    cases hw
    obtain ⟨_, b, c, d⟩ := recOf_keeps s r E z O
    obtain ⟨_, b', c', d'⟩ := initR_fields (hn z hz)
    exact ⟨b.trans b', c.trans c', d.trans d'⟩
  · cases hw

theorem walkedBy_append (s : Tree) (r : NodeId) (O : List (Key × Bool)) (kd : Key × Bool)
    (y : NodeId) : walkedBy s r (O ++ [kd]) y = (walkedBy s r O y || decide (y ∈ pathOf s r kd.1)) := by
  simp [walkedBy, List.any_append]

/-- **One key**: from the records after the keys O, the space root walked,
then the key's walk: the records after O and the key. -/
theorem walkKey_JI {s : Tree} {r : NodeId} {rn : KNode} {E : TreeFn}
    (hcl : ∀ y, E.lf y = true → E.col y = 0)
    (hci : ∀ y b, E.up b = some y → E.lf y = false → E.col y = E.col b + 1)
    (hr : getKey s r = some rn) (hrl : E.lf r = rn.leaf) (hru : E.up r = none) (hrd : E.dep r = 0)
    {ws : Walk} {O : List (Key × Bool)} (hJ : JI s r E ws O)
    (hn : ∀ y, walkedBy s r O y = true → NodeOk s E y) (key : Key) (del : Bool)
    (hp : PathOk s r E key) :
    JI s r E (walkKey s key del (key.length + 1) 0 (ws.reach r rn none) r).1 (O ++ [(key, del)]) ∧
      (walkKey s key del (key.length + 1) 0 (ws.reach r rn none) r).2 =
        (if del && (endOf s r key).2.2 == .last then some (endOf s r key).1 else none) := by
  obtain ⟨hnd, hget⟩ := hJ
  have hrok : NodeOk s E r := ⟨rn, hr, hrl⟩
  set P := (keyP s key (key.length + 1) 0 r).1 with hP
  have hpath : pathOf s r key = r :: P := rfl
  have hPok : ∀ y ∈ P, NodeOk s E y := links_mem r P hp.links
  -- the space root walked
  have hnew : Walk.newRec ws r rn none = initR s E r := by
    simp [Walk.newRec, initR, hr, hru, hrd]
  have hget0 : ∀ y, (ws.reach r rn none).get? y =
      if walkedBy s r O y || decide (y = r) then some (recOf s r E y O) else none := by
    intro y
    rw [Walk.get?_reach, hget, hget]
    by_cases hw : walkedBy s r O r
    · simp only [hw, ite_true, Option.isSome_some]
      by_cases hy : y = r
      · subst hy; simp [hw]
      · simp [hy]
    · simp only [hw, Bool.false_eq_true, ite_false, Option.isSome_none]
      by_cases hy : y = r
      · subst hy; simp [hnew, recOf_not s y E y O (by simpa using hw)]
      · simp [hy]
  have hnd0 := Walk.nodup_reach hnd r rn none
  have hR0 : RecOk E (ws.reach r rn none) := recOk_of_get _ hget0 (by
    intro y hy
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
    rcases hy with hy | rfl
    · exact hn y hy
    · exact hrok)
  have hr0 : ((ws.reach r rn none).get? r).isSome := by rw [hget0]; simp
  obtain ⟨hR1, hnd1, hget1⟩ := chainW_get? P _ r hR0 hnd0 hr0 hp.links
  set ws1 := chainW s (ws.reach r rn none) r P with hws1
  have hget1' : ∀ y, ws1.get? y =
      if walkedBy s r O y || decide (y ∈ pathOf s r key) then some (recOf s r E y O) else none := by
    intro y
    rw [hget1, hget0, hpath]
    by_cases hw : walkedBy s r O y
    · simp [hw]
    · by_cases hy : y = r
      · subst hy; simp [hw]
      · by_cases hyP : y ∈ P
        · simp [hw, hy, hyP, recOf_not s r E y O (by simpa using hw)]
        · simp [hw, hy, hyP]
  have hwk := walkKey_eq s key del (key.length + 1) 0 (ws.reach r rn none) r
  rw [hwk]
  have hend : (keyP s key (key.length + 1) 0 r).2 = endOf s r key := rfl
  rw [hend, ← hws1]
  have hstep : ∀ y, recOf s r E y (O ++ [(key, del)]) =
      if y ∈ pathOf s r key then effAt E y key del (endOf s r key) (recOf s r E y O)
      else recOf s r E y O := by
    intro y; rw [recOf_append]; rfl
  have hwb : ∀ y, walkedBy s r (O ++ [(key, del)]) y =
      (walkedBy s r O y || decide (y ∈ pathOf s r key)) := fun y => walkedBy_append s r O _ y
  rcases hE : endOf s r key with ⟨z, j, e⟩
  have hz : z = P.getLastD r := by
    have := keyP_stop s key (key.length + 1) 0 r
    rw [hend, hE] at this; exact this
  have hzP : z ∈ pathOf s r key := by
    rw [hz, hpath]
    cases P using List.reverseRecOn with
    | nil => simp
    | append_singleton L a _ => simp
  cases e with
  | stop =>
    refine ⟨⟨hnd1, fun y => ?_⟩, by simp [endEff]⟩
    simp only [endEff]
    rw [hget1', hwb, hstep, hE]
    split <;> simp [effAt]
  | fresh =>
    cases del with
    | true =>
      refine ⟨⟨hnd1, fun y => ?_⟩, by simp [endEff]⟩
      simp only [endEff, ite_true]
      rw [hget1', hwb, hstep, hE]
      split <;> simp [effAt]
    | false =>
      refine ⟨⟨?_, fun y => ?_⟩, by simp [endEff]⟩
      · simp only [endEff, Bool.false_eq_true, ite_false]
        rw [map_x_modify' _ (keeps_addFresh key j)]; exact hnd1
      simp only [endEff, Bool.false_eq_true, ite_false]
      rw [Walk.get?_modify _ _ _ _ (fun w => (keeps_addFresh key j w).1), hget1', hwb, hstep, hE]
      by_cases hyz : y = z
      · subst hyz; simp [hzP, effAt]
      · simp only [hyz, ite_false]
        split <;> simp [effAt, hyz]
  | last =>
    cases del with
    | false =>
      refine ⟨⟨?_, fun y => ?_⟩, by simp [endEff]⟩
      · simp only [endEff, Bool.false_eq_true, ite_false]
        rw [map_x_modify' _ keeps_k1]; exact hnd1
      simp only [endEff, Bool.false_eq_true, ite_false]
      rw [Walk.get?_modify _ _ _ _ (fun w => (keeps_k1 w).1), hget1', hwb, hstep, hE]
      by_cases hyz : y = z
      · subst hyz; simp [hzP, effAt]
      · simp only [hyz, ite_false]
        split <;> simp [effAt, hyz]
    | true =>
      have hleaf : E.lf z = true := by have := hp.leaf; rw [hE] at this; exact this rfl
      obtain ⟨_, hndP, hdz⟩ := links_dep r P hp.links
      have hdep : (((ws1.get? z).map (·.depth)).getD 0) = P.length := by
        have hzs : (ws1.get? z).isSome := by rw [hget1']; simp [hzP]
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hzs
        rw [hw]
        simp only [Option.map_some, Option.getD_some]
        rw [(hR1 z w hw).2.1, hz, hdz, hrd]; simp
      set L := (pathOf s r key).reverse with hL
      have hLlen : L.length = P.length + 1 := by simp [hL, hpath]
      have hLhead : L.head? = some z := by
        rw [hL, List.head?_reverse, hpath, hz]
        cases P using List.reverseRecOn with
        | nil => simp
        | append_singleton L a _ => rw [← List.cons_append, List.getLast?_append]; simp
      have hLnd : L.Nodup := by rw [hL, List.nodup_reverse, hpath]; exact hndP
      have hLch : UpChain E L := by
        have := links_upChain r P [] hp.links hru
        rw [hL, hpath, List.reverse_cons]; exact this
      have hLex : ∀ y ∈ L, (ws1.get? y).isSome := by
        intro y hy
        rw [hget1']
        have : y ∈ pathOf s r key := by rw [hL, List.mem_reverse] at hy; exact hy
        simp [this]
      have hmd := markDelete_eq E hcl hci L ws1 none 0 hLnd hR1 hLex hLch
        (fun _ => ⟨rfl, fun y hy => by rw [hLhead] at hy; cases hy; exact hleaf⟩)
        (fun b hb => by cases hb)
      refine ⟨⟨?_, fun y => ?_⟩, by simp [endEff]⟩
      · simp only [endEff, ite_true]
        rw [hdep, ← hLlen, ← hLhead, map_x_markDelete]; exact hnd1
      · simp only [endEff, ite_true]
        rw [hdep, ← hLlen, ← hLhead, hmd y, hwb, hstep, hE]
        have hyL : y ∈ L ↔ y ∈ pathOf s r key := by rw [hL, List.mem_reverse]
        by_cases hy : y ∈ pathOf s r key
        · simp only [show y ∈ L from hyL.mpr hy, ite_true]; rw [hget1']; simp [hy, effAt]
        · simp only [show y ∉ L from fun h => hy (hyL.mp h), ite_false]; rw [hget1']; simp [hy]

/-- A delete that reaches its last segment. -/
def delLast (s : Tree) (r : NodeId) (kd : Key × Bool) : Bool :=
  kd.2 && (endOf s r kd.1).2.2 == .last

/-- What the walk of the keys O leaves: the records, whether a delete reached
its last segment, and for each such delete its end's depth and three. -/
def WInv (s : Tree) (r : NodeId) (E : TreeFn) (acc : Walk × Bool × Nat) (O : List (Key × Bool)) :
    Prop :=
  JI s r E acc.1 O ∧ (∀ y, walkedBy s r O y = true → NodeOk s E y) ∧
    acc.2.1 = O.any (delLast s r) ∧
    acc.2.2 = ((O.filter (delLast s r)).map (fun kd => E.dep (endOf s r kd.1).1 + 3)).sum

theorem walkAll_fold {s : Tree} {r : NodeId} {rn : KNode} {E : TreeFn}
    (hcl : ∀ y, E.lf y = true → E.col y = 0)
    (hci : ∀ y b, E.up b = some y → E.lf y = false → E.col y = E.col b + 1)
    (hr : getKey s r = some rn) (hrl : E.lf r = rn.leaf) (hru : E.up r = none) (hrd : E.dep r = 0) :
    ∀ (L O : List (Key × Bool)) (acc : Walk × Bool × Nat), WInv s r E acc O →
      (∀ kd ∈ L, PathOk s r E kd.1) →
      WInv s r E (L.foldl (fun (acc : Walk × Bool × Nat) (kdi : Key × Bool) =>
        let ws := acc.1.reach r rn none
        let res := walkKey s kdi.1 kdi.2 (kdi.1.length + 1) 0 ws r
        match res.2 with
        | some x =>
          (res.1, true, acc.2.2 + ((((res.1.get? x).map (·.depth)).getD 0) + 1 + 2))
        | none => (res.1, acc.2.1, acc.2.2)) acc) (O ++ L)
  | [], O, acc, h, _ => by simpa using h
  | kd :: L, O, acc, h, hL => by
    rw [List.foldl_cons, show O ++ kd :: L = (O ++ [kd]) ++ L by simp]
    apply walkAll_fold hcl hci hr hrl hru hrd L (O ++ [kd]) _ _ (fun k hk => hL k (List.mem_cons_of_mem _ hk))
    obtain ⟨hJ, hn, had, hml⟩ := h
    obtain ⟨key, del⟩ := kd
    have hp := hL (key, del) List.mem_cons_self
    obtain ⟨hJ1, hres⟩ := walkKey_JI hcl hci hr hrl hru hrd hJ hn key del hp
    have hn1 : ∀ y, walkedBy s r (O ++ [(key, del)]) y = true → NodeOk s E y := by
      intro y hy
      rw [walkedBy_append] at hy
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
      rcases hy with hy | hy
      · exact hn y hy
      · simp only [pathOf, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨rn, hr, hrl⟩
        · exact links_mem r _ hp.links y hy
    simp only
    rw [hres]
    by_cases hd : (del && (endOf s r key).2.2 == .last) = true
    · simp only [hd, ite_true]
      set z := (endOf s r key).1
      have hzw : walkedBy s r (O ++ [(key, del)]) z = true := by
        rw [walkedBy_append]
        have : z ∈ pathOf s r key := by
          have hz := keyP_stop s key (key.length + 1) 0 r
          show (endOf s r key).1 ∈ r :: (keyP s key (key.length + 1) 0 r).1
          unfold endOf; rw [hz]
          cases h : (keyP s key (key.length + 1) 0 r).1 using List.reverseRecOn with
          | nil => simp
          | append_singleton L a _ => simp
        simp [this]
      have hdz : (((walkKey s key del (key.length + 1) 0 (acc.1.reach r rn none) r).1.get? z).map
          (·.depth)).getD 0 = E.dep z := by
        rw [hJ1.2 z, hzw]
        simp only [ite_true, Option.map_some, Option.getD_some]
        rw [(recOf_keeps s r E z _).2.2.1, (initR_fields (hn1 z hzw)).2.2.1]
      refine ⟨hJ1, hn1, ?_, ?_⟩
      · simp [List.any_append, delLast, hd]
      · simp only [hdz]
        rw [hml, List.filter_append, List.map_append, List.sum_append]
        simp [delLast, hd, z]
    · have hd' : (del && (endOf s r key).2.2 == .last) = false := by simpa using hd
      simp only [hd', Bool.false_eq_true, ite_false]
      refine ⟨hJ1, hn1, ?_, ?_⟩
      · simp [List.any_append, delLast, hd', had]
      · rw [hml, List.filter_append, List.map_append, List.sum_append]
        simp [delLast, hd']

/-- **The walk of all keys** (`walkAll`): a record `recOf` for each node a
key passes, `anyDelete` if a delete reached its last segment, and
`mergeLevels` the sum over those deletes of their end's depth and three. -/
theorem walkAll_eq {s : Tree} {r : NodeId} {rn : KNode} {E : TreeFn}
    (hcl : ∀ y, E.lf y = true → E.col y = 0)
    (hci : ∀ y b, E.up b = some y → E.lf y = false → E.col y = E.col b + 1)
    (hr : getKey s r = some rn) (hrl : E.lf r = rn.leaf) (hru : E.up r = none) (hrd : E.dep r = 0)
    (kd : List (Key × Bool)) (hk : ∀ k ∈ kd, PathOk s r E k.1) :
    WInv s r E (walkAll s r rn kd) kd := by
  have h0 : WInv s r E ([], false, 0) [] := by
    refine ⟨⟨by simp, fun y => by simp [walkedBy, Walk.get?]⟩, by simp [walkedBy], by simp, by simp⟩
  have := walkAll_fold hcl hci hr hrl hru hrd kd [] _ h0 hk
  rw [List.nil_append] at this
  exact this

end Contract.DNB
