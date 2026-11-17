/-
The contract package (bergdb 030-10): the writer's primitives. What each small
step of the model's writer (`getNode`, `putNode`, `newKey`, `newValue`, the
`madeFor` book, the key access path) gives: its result and the state after
it, as an equation; what the step does to the state's map (`treeOf`); and
that the books, the frame, BalancedOK and the path are kept by a change of
one node of the overlay that meets what each asks of it.
-/
import Contract.Proof.WriterState

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. The steps, as equations -/

theorem getNode_hit (c : Ctx) {w : MW} {x : NodeId} {n : MNode} (h : w.nodes.lookup x = some n) :
    SIS.Tree.getNode x c w = .ok (n, w) := by
  unfold SIS.Tree.getNode
  show (match w.nodes.lookup x with
    | some n => pure n
    | none => _ : SIS.Tree.M MNode) c w = _
  rw [h]; rfl

theorem getNode_miss (c : Ctx) {w : MW} {x : NodeId} {nd : SIS.Node BVal}
    (h : w.nodes.lookup x = none) (hv : c.view x = some nd) (hd : nd.isData = false)
    (hl : nd.level ≤ c.p.keyMax) :
    SIS.Tree.getNode x c w =
      .ok (⟨c.p.heightOf nd.level == 0, SIS.Tree.klongsOf nd.hist⟩,
        { w with nodes := w.nodes ++ [(x, ⟨c.p.heightOf nd.level == 0, SIS.Tree.klongsOf nd.hist⟩)],
                 gh := (x, c.p.segOf nd.level, c.p.heightOf nd.level) :: w.gh }) := by
  have hc : (nd.isData || decide (c.p.keyMax < nd.level)) = false := by
    simp [hd]; omega
  unfold SIS.Tree.getNode
  show (match w.nodes.lookup x with
    | some n => pure n
    | none => _ : SIS.Tree.M MNode) c w = _
  rw [h]
  show (match c.view x with
    | some nd => _
    | none => _ : SIS.Tree.M MNode) c w = _
  rw [hv]
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem putNode_eq (c : Ctx) (w : MW) (x : NodeId) (n : MNode) :
    SIS.Tree.putNode x n c w = .ok ((), w.withNode x n) := rfl

/-- The state after `newKey g h leaf ks`. -/
def MW.afterNewKey (w : MW) (p : MParams) (g h : Nat) (leaf : Bool) (ks : List MKlong) : MW :=
  { w with next := w.next + 2, nodes := w.nodes ++ [(w.next, ⟨leaf, ks⟩)],
           gh := (w.next, g, h) :: w.gh,
           made := w.made ++ [⟨w.next, p.keyLevel g h, false⟩],
           outside := if p.G < g || p.H < h then (w.next, g, h) :: w.outside else w.outside }

theorem prim_read_bind {β : Type} (g : Ctx → SIS.Tree.M β) (c : Ctx) (u : MW) :
    (read >>= g) c u = g c c u := rfl

theorem prim_fresh_bind {β : Type} (g : NodeId → SIS.Tree.M β) (c : Ctx) (u : MW) :
    (SIS.Tree.fresh >>= g) c u = g u.next c { u with next := u.next + 2 } := rfl

theorem newKey_eq (c : Ctx) (w : MW) (g h : Nat) (leaf : Bool) (ks : List MKlong) :
    SIS.Tree.newKey g h leaf ks c w = .ok (w.next, w.afterNewKey c.p g h leaf ks) := by
  unfold SIS.Tree.newKey MW.afterNewKey
  rw [prim_read_bind, prim_fresh_bind]
  split <;> rfl

/-- The state after `newValue h`. -/
def MW.afterNewValue (w : MW) (h : Nat) : MW :=
  { w with next := w.next + 2, vals := w.vals ++ [(w.next, h)],
           made := w.made ++ [⟨w.next, 0, true⟩] }

theorem newValue_eq (c : Ctx) (w : MW) (h : Nat) :
    SIS.Tree.newValue h c w = .ok (w.next, w.afterNewValue h) := rfl

theorem setMadeFor_some (c : Ctx) (w : MW) (m o : NodeId) :
    SIS.Tree.setMadeFor m (some o) c w = .ok ((), { w with madeFor := (m, o) :: w.madeFor }) := rfl

theorem setMadeFor_none (c : Ctx) (w : MW) (m : NodeId) :
    SIS.Tree.setMadeFor m none c w = .ok ((), w) := rfl

theorem replacedBy_eq (c : Ctx) (w : MW) (x : NodeId) :
    SIS.Tree.replacedBy x c w = .ok (w.madeFor.lookup x, w) := rfl

theorem note_eq (c : Ctx) (w : MW) (t : String) :
    SIS.Tree.note t c w = .ok ((), { w with trail := t :: w.trail }) := rfl

theorem pathClear_eq (c : Ctx) (w : MW) :
    SIS.Tree.pathClear c w = .ok ((), { w with path := [] }) := rfl

theorem pathAdd_eq (c : Ctx) (w : MW) (k : Option Nat) (x : NodeId) :
    SIS.Tree.pathAdd k x c w = .ok ((), { w with path := w.path ++ [(k, x)] }) := rfl

theorem pathSize_eq (c : Ctx) (w : MW) : SIS.Tree.pathSize c w = .ok (w.path.length, w) := rfl

theorem pathNode_eq (c : Ctx) {w : MW} {d : Nat} {e : Option Nat × NodeId}
    (h : w.path[d]? = some e) : SIS.Tree.pathNode d c w = .ok (e.2, w) := by
  unfold SIS.Tree.pathNode
  show (match w.path[d]? with
    | some e => pure e.2
    | none => _ : SIS.Tree.M NodeId) c w = _
  rw [h]; rfl

theorem klongAt_eq (c : Ctx) {w : MW} {d : Nat} {k : Nat} {x : NodeId}
    (h : w.path[d]? = some (some k, x)) : SIS.Tree.klongAt d c w = .ok (k, w) := by
  unfold SIS.Tree.klongAt
  show (match w.path[d]? with
    | some (some c, _) => pure c
    | _ => _ : SIS.Tree.M Nat) c w = _
  rw [h]; rfl

theorem parentAt_zero (c : Ctx) (w : MW) : SIS.Tree.parentAt 0 c w = .ok (none, w) := rfl

theorem parentAt_succ (c : Ctx) {w : MW} {d : Nat} {e : Option Nat × NodeId}
    (h : w.path[d]? = some e) : SIS.Tree.parentAt (d + 1) c w = .ok (some e.2, w) := by
  unfold SIS.Tree.parentAt
  show (SIS.Tree.pathNode d >>= fun y => pure (some y) : SIS.Tree.M _) c w = _
  show (SIS.Tree.pathNode d c w).bind _ = _
  rw [pathNode_eq c h]; rfl

theorem ghOf_hit (c : Ctx) {w : MW} {x : NodeId} {n : MNode} {gh : Nat × Nat}
    (h : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some gh) :
    SIS.Tree.ghOf x c w = .ok (gh, w) := by
  unfold SIS.Tree.ghOf
  show (SIS.Tree.getNode x c w).bind _ = _
  rw [getNode_hit c h]
  show (match w.gh.lookup x with
    | some v => pure v
    | none => _ : SIS.Tree.M (Nat × Nat)) c w = _
  rw [hg]; rfl

/-! ## 2. The steps and the state's map -/

/-- The map depends only on these fields of the state. -/
theorem treeOf_congr (i : Time) (s : Tree) {w w' : MW} (h1 : w'.nodes = w.nodes)
    (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken) (h4 : w'.made = w.made)
    (h5 : w'.top = w.top) (h6 : w'.newTop = w.newTop) : treeOf i s w' = treeOf i s w := by
  simp only [treeOf, wLevel, h1, h2, h3, h4, h5, h6]

theorem prim_lookup_cons {β : Type} (y k : NodeId) (m : β) (r : List (NodeId × β)) :
    ((k, m) :: r).lookup y = if y = k then some m else r.lookup y := by
  by_cases h : y = k
  · subst h; simp [List.lookup]
  · have h' : (y == k) = false := by simpa using h
    simp [List.lookup, h, h']

theorem prim_lookup_upd_self (x : NodeId) (n : MNode) : ∀ ns : List (NodeId × MNode),
    (ns.any (fun q => q.1 == x)) = true →
    (ns.map (fun q => if q.1 == x then (x, n) else q)).lookup x = some n
  | [], h => by simp at h
  | (k, m) :: r, h => by
    rw [List.map_cons]
    by_cases hk : k = x
    · simp [hk]
    · have hr : (r.any (fun q => q.1 == x)) = true := by
        simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · exact absurd h hk
        · simpa using h
      have hk' : (k == x) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte, prim_lookup_cons, Ne.symm hk]
      exact prim_lookup_upd_self x n r hr

theorem prim_lookup_upd_ne (x y : NodeId) (n : MNode) (h : y ≠ x) :
    ∀ ns : List (NodeId × MNode),
    (ns.map (fun q => if q.1 == x then (x, n) else q)).lookup y = ns.lookup y
  | [] => rfl
  | (k, m) :: r => by
    rw [List.map_cons]
    by_cases hk : k = x
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, prim_lookup_cons, h, prim_lookup_upd_ne k y n h r]
    · have hk' : (k == x) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte, prim_lookup_cons,
        prim_lookup_upd_ne x y n h r]

theorem prim_lookup_none {β : Type} (x : NodeId) : ∀ ns : List (NodeId × β),
    (ns.any (fun q => q.1 == x)) = false → ns.lookup x = none
  | [], _ => rfl
  | (k, m) :: r, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hk : x ≠ k := by intro e; subst e; simp at h
    simp only [prim_lookup_cons, hk, ↓reduceIte]
    exact prim_lookup_none x r h.2

theorem lookup_upsert_self (ns : List (NodeId × MNode)) (x : NodeId) (n : MNode) :
    (SIS.Tree.upsert ns x n).lookup x = some n := by
  unfold SIS.Tree.upsert
  split
  · exact prim_lookup_upd_self x n ns (by assumption)
  · rename_i h
    rw [List.lookup_append, prim_lookup_none x ns (Bool.eq_false_iff.mpr h), prim_lookup_cons]
    simp

theorem lookup_upsert_ne (ns : List (NodeId × MNode)) {x y : NodeId} (n : MNode) (h : y ≠ x) :
    (SIS.Tree.upsert ns x n).lookup y = ns.lookup y := by
  unfold SIS.Tree.upsert
  split
  · exact prim_lookup_upd_ne x y n h ns
  · rw [List.lookup_append, prim_lookup_cons]
    simp only [h, ↓reduceIte]
    cases ns.lookup y <;> rfl

theorem prim_tree_ext {a b : Tree} (h1 : ∀ y, a.obj y = b.obj y) (h2 : a.roots = b.roots) :
    a = b := by
  cases a; cases b
  simp only [Tree.mk.injEq]
  exact ⟨funext h1, h2⟩

/-- `putNode`: the map with the node set, on its level. -/
theorem treeOf_withNode (i : Time) (s : Tree) {w : MW} {x : NodeId} (n : MNode)
    (ht : w.taken.contains x = false) :
    treeOf i s (w.withNode x n) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf n⟩) := by
  have hl : wLevel s (w.withNode x n) = wLevel s w := rfl
  apply prim_tree_ext
  · intro y
    simp only [treeOf, Tree.set, hl]
    by_cases hy : y = x
    · subst hy
      simp only [MW.withNode, ht, lookup_upsert_self, Bool.false_eq_true, ↓reduceIte, ksOf]
    · simp only [MW.withNode, hy, ↓reduceIte, lookup_upsert_ne _ _ hy]
  · rfl

theorem prim_find_append_ne (l : List SIS.NewNode) (nm : SIS.NewNode) {y : NodeId}
    (h : nm.id ≠ y) : (l ++ [nm]).find? (fun m => m.id == y) = l.find? (fun m => m.id == y) := by
  rw [List.find?_append]
  have : [nm].find? (fun m => m.id == y) = none := by simp [h]
  rw [this]
  cases l.find? (fun m => m.id == y) <;> rfl

theorem prim_lookup_append_ne {β : Type} (l : List (NodeId × β)) {x y : NodeId} (b : β)
    (h : y ≠ x) : (l ++ [(x, b)]).lookup y = l.lookup y := by
  rw [List.lookup_append, prim_lookup_cons]
  simp only [h, ↓reduceIte]
  cases l.lookup y <;> rfl

theorem prim_lookup_append_self {β : Type} (l : List (NodeId × β)) {x : NodeId} (b : β)
    (h : l.lookup x = none) : (l ++ [(x, b)]).lookup x = some b := by
  rw [List.lookup_append, prim_lookup_cons, h]
  simp

/-- `newKey`: the map with the new node, if its id is new. -/
theorem treeOf_afterNewKey (i : Time) (s : Tree) {w : MW} (p : MParams) (g h : Nat) (leaf : Bool)
    (ks : List MKlong) (hs : s.obj w.next = none) (hn : w.nodes.lookup w.next = none)
    (ht : w.taken.contains w.next = false) (hm : ∀ m ∈ w.made, m.id ≠ w.next) :
    treeOf i s (w.afterNewKey p g h leaf ks) =
      (treeOf i s w).set w.next (.key ⟨p.keyLevel g h, leaf, ks.map kOf⟩) := by
  have hf : w.made.find? (fun m => m.id == w.next) = none := by
    rw [List.find?_eq_none]
    intro m hm'
    simpa using hm m hm'
  apply prim_tree_ext
  · intro y
    simp only [treeOf, Tree.set]
    by_cases hy : y = w.next
    · subst hy
      have hl : wLevel s (w.afterNewKey p g h leaf ks) w.next = p.keyLevel g h := by
        simp [wLevel, hs, MW.afterNewKey, List.find?_append, hf]
      simp only [hl]
      simp only [MW.afterNewKey, ht, prim_lookup_append_self _ _ hn, ↓reduceIte,
        Bool.false_eq_true]
    · have hl : wLevel s (w.afterNewKey p g h leaf ks) y = wLevel s w y := by
        simp only [wLevel, MW.afterNewKey,
          prim_find_append_ne w.made ⟨w.next, p.keyLevel g h, false⟩ (Ne.symm hy)]
      simp only [hy, ↓reduceIte, hl]
      simp only [MW.afterNewKey, prim_lookup_append_ne _ _ hy]
  · rfl

/-- `newValue`: the map with the new value, if its id is new. -/
theorem treeOf_afterNewValue (i : Time) (s : Tree) {w : MW} (h : Nat)
    (hn : w.nodes.lookup w.next = none) (hv : w.vals.lookup w.next = none)
    (ht : w.taken.contains w.next = false) :
    treeOf i s (w.afterNewValue h) = (treeOf i s w).set w.next (.val h) := by
  apply prim_tree_ext
  · intro y
    simp only [treeOf, Tree.set]
    by_cases hy : y = w.next
    · subst hy
      simp only [MW.afterNewValue, ht, hn, prim_lookup_append_self _ _ hv, ↓reduceIte,
        Bool.false_eq_true]
    · have hl : wLevel s (w.afterNewValue h) y = wLevel s w y := by
        simp only [wLevel, MW.afterNewValue,
          prim_find_append_ne w.made ⟨w.next, 0, true⟩ (Ne.symm hy)]
      simp only [hy, ↓reduceIte, hl]
      simp only [MW.afterNewValue, prim_lookup_append_ne _ _ hy]
  · rfl

/-- A new id is no node of the map (B6, B9 and the ids of s below the first
id). -/
theorem treeOf_fresh {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (hb : Books i base s tp) (hk : PutBooks p i base s w) {x : NodeId} (hx : w.next ≤ x) :
    (treeOf i s w).obj x = none ∧ s.obj x = none ∧ w.nodes.lookup x = none ∧
      w.vals.lookup x = none ∧ w.taken.contains x = false ∧ ∀ m ∈ w.made, m.id ≠ x := by
  obtain ⟨hn, hv, hm, hbase, -⟩ := hk.ids
  have hs : s.obj x = none := (hb.ids x (Nat.le_trans hbase hx)).1
  have hnx : w.nodes.lookup x = none := by
    cases e : w.nodes.lookup x with
    | none => rfl
    | some n => exact absurd (hn x n e) (Nat.not_lt.mpr hx)
  have hvx : w.vals.lookup x = none := by
    cases e : w.vals.lookup x with
    | none => rfl
    | some h => exact absurd (hv x h e) (Nat.not_lt.mpr hx)
  have hmx : ∀ m ∈ w.made, m.id ≠ x := fun m hm' e => by
    have := (hm m hm').1
    omega
  have htx : w.taken.contains x = false := by
    cases e : w.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm', he⟩ := List.mem_map.mp (hk.taken x e)
      exact absurd he (hmx m hm')
  refine ⟨?_, hs, hnx, hvx, htx, hmx⟩
  simp only [treeOf, htx, hnx, hvx, hs, Bool.false_eq_true, ↓reduceIte]

/-! ## 3. Reading a node of the map -/

theorem prim_lookup_append_some {β : Type} {l : List (NodeId × β)} {y : NodeId} {b : β}
    (l' : List (NodeId × β)) (h : l.lookup y = some b) : (l ++ l').lookup y = some b := by
  rw [List.lookup_append, h]; rfl

/-- A level of a key node, at most the largest, is the level of its segment
and height, which are within G and H. -/
theorem prim_level_gh (p : MParams) {l : Nat} (h0 : 0 < l) (hl : l ≤ p.keyMax) :
    p.segOf l ≤ p.G ∧ p.heightOf l ≤ p.H ∧ p.keyLevel (p.segOf l) (p.heightOf l) = l := by
  unfold SIS.Tree.Params.segOf SIS.Tree.Params.heightOf SIS.Tree.Params.keyLevel
    SIS.Tree.Params.keyMax at *
  have hq : (l - 1) / (p.H + 1) ≤ p.G := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.succ_mul]
    omega
  have hr : (l - 1) % (p.H + 1) < p.H + 1 := Nat.mod_lt _ (by omega)
  have hdm := Nat.div_add_mod' (l - 1) (p.H + 1)
  refine ⟨Nat.sub_le _ _, by omega, ?_⟩
  rw [Nat.sub_sub_self hq]
  omega

theorem prim_firstTime_cons (t : Time) (rest : List MKlong) (leaf : Bool) :
    (⟨leaf, .time t :: rest⟩ : MNode).firstTime = some t := rfl

theorem prim_timesBefore {i : Time} {ks : List Klong} (h : timesBefore i ks = true) :
    ∀ t, Klong.time t ∈ ks → t < i := by
  intro t ht
  have := List.all_eq_true.mp h _ ht
  simpa using this

/-- The frame holds for a larger D. -/
theorem Frame.mono {i : Time} {s s' : Tree} {D D' : List NodeId} (h : Frame i s D s')
    (hD : ∀ x ∈ D, x ∈ D') : Frame i s D' s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x o ho => ?_, fun x n hx hs => hD x (h2 x n hx hs), h3⟩
  obtain ⟨o', ho', he, hu⟩ := h1 x o ho
  exact ⟨o', ho', he, fun hx => hu (fun hd => hx (hD x hd))⟩

/-- `getNode` of a key node of the map: it gives the node (its klongs, its
kind); the state after it is the same, or has the node read into the overlay;
the map is the same, and `PInv` and the path are kept. -/
theorem getNode_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {ex : Option NodeId} {C : List (Key × Nat)} {w : MW}
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hI : PInv p i base s tp ex C w)
    {x : NodeId} {m : KNode} (hx : (treeOf i s w).obj x = some (.key m)) :
    ∃ n w', SIS.Tree.getNode x { p := p, i := i, view := v } w = .ok (n, w') ∧
      ksOf n = m.ks ∧ n.leaf = m.leaf ∧ w'.nodes.lookup x = some n ∧
      treeOf i s w' = treeOf i s w ∧ PInv p i base s tp ex C w' ∧
      (w' = w ∨ (w.nodes.lookup x = none ∧ ∃ gh,
        w' = { w with nodes := w.nodes ++ [(x, n)], gh := (x, gh) :: w.gh })) ∧
      (∀ d, PathOk i s w d → PathOk i s w' d) := by
  have ht : w.taken.contains x = false := by
    cases e : w.taken.contains x
    · rfl
    · have : (treeOf i s w).obj x = none := by simp only [treeOf, e, ↓reduceIte]
      rw [this] at hx; cases hx
  cases hlk : w.nodes.lookup x with
  | some n =>
    have hm : m = ⟨wLevel s w x, n.leaf, ksOf n⟩ := by
      simp only [treeOf, ht, hlk, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Obj.key.injEq] at hx
      rw [← hx]; rfl
    subst hm
    exact ⟨n, w, getNode_hit _ hlk, rfl, rfl, hlk, rfl, hI, Or.inl rfl, fun d h => h⟩
  | none =>
    have hv : w.vals.lookup x = none := by
      cases e : w.vals.lookup x with
      | none => rfl
      | some h => simp [treeOf, hlk, e] at hx
    have hsx : s.obj x = some (.key m) := by
      simpa only [treeOf, ht, hlk, hv, Bool.false_eq_true, ↓reduceIte] using hx
    obtain ⟨nd, hvx, hd, hlev, hkm, hks, hleaf⟩ := hs.key x m hsx
    have hget := getNode_miss { p := p, i := i, view := v } hlk hvx hd (by rw [hlev]; exact hkm)
    let n : MNode := ⟨p.heightOf nd.level == 0, SIS.Tree.klongsOf nd.hist⟩
    have hksn : ksOf n = m.ks := hks
    have hleafn : n.leaf = m.leaf := by
      show (p.heightOf nd.level == 0) = m.leaf
      rw [hleaf, hlev]
    have hlkx : (w.nodes ++ [(x, n)]).lookup x = some n := prim_lookup_append_self _ _ hlk
    let w' : MW := { w with nodes := w.nodes ++ [(x, n)],
                            gh := (x, p.segOf nd.level, p.heightOf nd.level) :: w.gh }
    have hwl : wLevel s w' x = m.level := by simp [wLevel, hsx]
    have hT : treeOf i s w' = treeOf i s w := by
      apply prim_tree_ext
      · intro y
        by_cases hy : y = x
        · subst hy
          rw [hx]
          simp only [treeOf, w', ht, hlkx, Bool.false_eq_true, ↓reduceIte]
          rw [hwl, hleafn]
          show some (Obj.key ⟨m.level, m.leaf, ksOf n⟩) = some (Obj.key m)
          rw [hksn]
        · simp only [treeOf, w', prim_lookup_append_ne _ _ hy]
          rfl
      · rfl
    have hm0 : 0 < m.level := (hI.balanced x m hx).1
    obtain ⟨hg, hh, hkl⟩ := prim_level_gh p hm0 hkm
    have htb := prim_timesBefore (hb.times x m hsx)
    have hntimes : ∀ t, SIS.Tree.Klong.time t ∈ n.ks → t < i := fun t h =>
      htb t (by rw [← hksn]; exact List.mem_map_of_mem (f := kOf) h)
    have hfirst : ∃ t rest, n.ks = .time t :: rest ∧ t < i := by
      obtain ⟨t, rest, hm⟩ := hb.first x m hsx
      cases hk : n.ks with
      | nil =>
        have := hksn
        rw [hm] at this
        simp [ksOf, hk] at this
      | cons k r =>
        have hk0 : kOf k = .time t := by
          have := hksn
          rw [hm] at this
          simp only [ksOf, hk, List.map_cons, List.cons.injEq] at this
          exact this.1
        refine ⟨t, r, by rw [kOf_eq_time hk0], hntimes t ?_⟩
        rw [hk, kOf_eq_time hk0]
        exact List.mem_cons_self
    have hxb : x < base := by
      by_contra hc
      have := (hb.ids x (by omega)).1
      rw [hsx] at this; cases this
    have hk := hI.books
    have hbk : PutBooks p i base s w' := by
      refine ⟨?_, ?_, ?_, ?_, hk.taken, ?_, hk.within, ?_⟩
      · intro y n' hy ht'
        by_cases hyx : y = x
        · subst hyx
          rw [hlkx] at hy; cases hy
          obtain ⟨t, rest, hr, htl⟩ := hfirst
          rw [hsx]
          have : n.firstTime = some t := by
            rw [SIS.Tree.KNode.firstTime, hr]; rfl
          simp only [Option.isSome_some, this, ne_eq, Option.some.injEq, true_iff]
          omega
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          exact hk.first y n' hy ht'
      · intro y n' hy t htm
        by_cases hyx : y = x
        · subst hyx
          rw [hlkx] at hy; cases hy
          exact Nat.le_of_lt (hntimes t htm)
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          exact hk.times y n' hy t htm
      · intro y n' hy ht'
        by_cases hyx : y = x
        · subst hyx
          rw [hlkx] at hy; cases hy
          refine ⟨p.segOf nd.level, p.heightOf nd.level, ?_, ?_, ?_, ?_, rfl⟩
          · show ((y, p.segOf nd.level, p.heightOf nd.level) :: w.gh).lookup y = _
            rw [prim_lookup_cons]; simp
          · rw [hlev]; exact hg
          · rw [hlev]; exact hh
          · rw [hwl, hlev, hkl]
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          obtain ⟨g, h, h1, h2⟩ := hk.levels y n' hy ht'
          refine ⟨g, h, ?_, h2⟩
          show ((x, p.segOf nd.level, p.heightOf nd.level) :: w.gh).lookup y = _
          rw [prim_lookup_cons]
          simp only [hyx, ↓reduceIte, h1]
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hk.ids
        refine ⟨fun y n' hy => ?_, h2, h3, h4, h5⟩
        by_cases hyx : y = x
        · subst hyx; show y < w.next; omega
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          exact h1 y n' hy
      · intro y n' hy
        by_cases hyx : y = x
        · subst hyx; rw [hsx]; exact Or.inl rfl
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          exact hk.overlay y n' hy
      · intro y n' hy ht'
        by_cases hyx : y = x
        · subst hyx
          rw [hlkx] at hy; cases hy
          obtain ⟨t, rest, hr, -⟩ := hfirst
          exact ⟨t, rest, hr⟩
        · rw [prim_lookup_append_ne _ _ hyx] at hy
          exact hk.timeFirst y n' hy ht'
    have hdirty : ∀ y ∈ dirtyOf w, y ∈ dirtyOf w' := by
      intro y hy
      simp only [dirtyOf, w', List.map_append, List.mem_append]
      exact Or.inl hy
    have hPI : PInv p i base s tp ex C w' := by
      refine ⟨?_, ?_, ?_, hI.top, ?_, hbk⟩
      · rw [hT]; exact hI.root
      · rw [hT]; exact hI.sound
      · rw [hT]; exact hI.frame.mono hdirty
      · rw [hT]; exact hI.balanced
    refine ⟨n, w', hget, hksn, hleafn, hlkx, hT, hPI, Or.inr ⟨rfl, _, rfl⟩, ?_⟩
    intro d hP
    refine ⟨hP.root, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨c, u, n', h1, h2, h3⟩ := hP.nodes e he
      exact ⟨c, u, n', h1, prim_lookup_append_some _ h2, h3⟩
    · rw [hT]; exact hP.links e he

/-! ## 4. A change of one node keeps the books

English. What the proofs of the writer's rules need to carry `PInv`'s parts
over a step that changes one node: `putNode` of a node of the overlay
(`MW.withNode`), `newKey` (`MW.afterNewKey`) and `newValue`
(`MW.afterNewValue`). Each lemma has hypotheses about the state w before the
step and a conclusion about the state after it, so that they compose.

* 4.1 The books. `newKey` with no klongs makes a node that breaks B1 and B13
  until a `putNode` gives it its klongs: `PutBooksE` is `PutBooks` with such
  nodes allowed, each no node of s.
* 4.2 The frame, through `Frame.set`.
* 4.3 BalancedOK, through `BalancedAll.set`.
* 4.4 The key access path.
* 4.5 The top, and `PInv` over a step that leaves the map as it is. -/

/-! ### 4.1 The books -/

/-- Node x of the overlay, kept, is in the map with these klongs, on its
level. -/
theorem treeOf_obj_overlay (i : Time) (s : Tree) {w : MW} {x : NodeId} {n : MNode}
    (hx : w.nodes.lookup x = some n) (ht : w.taken.contains x = false) :
    (treeOf i s w).obj x = some (.key ⟨wLevel s w x, n.leaf, ksOf n⟩) := by
  simp only [treeOf, ht, hx, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem prim_firstTime_of {n : MNode} {t : Time} {rest : List MKlong}
    (h : n.ks = .time t :: rest) : n.firstTime = some t := by
  rw [SIS.Tree.KNode.firstTime, h]; rfl

theorem prim_head_time {n n' : MNode} {t : Time} {rest : List MKlong}
    (h : n.ks = .time t :: rest) (hh : n'.ks.head? = n.ks.head?) :
    ∃ rest', n'.ks = .time t :: rest' := by
  rw [h] at hh
  cases e : n'.ks with
  | nil => rw [e] at hh; cases hh
  | cons k r =>
    rw [e] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    exact ⟨r, by rw [hh]⟩

/-- `PutBooks` with nodes that have no klongs yet (`newKey` with no klongs
makes one; a `putNode` gives it its klongs later): B1 and B13 only for a node
with klongs; a node kept without klongs is no node of s. -/
structure PutBooksE (p : MParams) (i : Time) (base : NodeId) (s : Tree) (w : MW) : Prop where
  first : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks ≠ [] →
    ((s.obj x).isSome = true ↔ n.firstTime ≠ some i)
  times : ∀ x n, w.nodes.lookup x = some n → ∀ t, SIS.Tree.Klong.time t ∈ n.ks → t ≤ i
  levels : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∃ g h, w.gh.lookup x = some (g, h) ∧ g ≤ p.G ∧ h ≤ p.H ∧ wLevel s w x = p.keyLevel g h ∧
      n.leaf = (h == 0)
  ids : (∀ x n, w.nodes.lookup x = some n → x < w.next) ∧
    (∀ x h, w.vals.lookup x = some h → x < w.next) ∧
    (∀ m ∈ w.made, m.id < w.next ∧ base ≤ m.id) ∧
    base ≤ w.next ∧ (w.newTop = true → w.top.id < w.next)
  taken : ∀ x, w.taken.contains x = true → x ∈ w.made.map (·.id)
  overlay : ∀ x n, w.nodes.lookup x = some n → (s.obj x).isSome = true ∨ x ∈ w.made.map (·.id)
  within : w.outside = []
  timeFirst : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks ≠ [] →
    ∃ t rest, n.ks = SIS.Tree.Klong.time t :: rest
  empty : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks = [] →
    s.obj x = none

theorem PutBooks.toE {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    (h : PutBooks p i base s w) : PutBooksE p i base s w where
  first x n hx ht _ := h.first x n hx ht
  times := h.times
  levels := h.levels
  ids := h.ids
  taken := h.taken
  overlay := h.overlay
  within := h.within
  timeFirst x n hx ht _ := h.timeFirst x n hx ht
  empty x n hx ht he := by
    obtain ⟨t, rest, hr⟩ := h.timeFirst x n hx ht
    rw [hr] at he; cases he

/-- `PutBooksE` is `PutBooks` when every node kept has klongs. -/
theorem PutBooksE.toBooks {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    (h : PutBooksE p i base s w)
    (hne : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks ≠ []) :
    PutBooks p i base s w where
  first x n hx ht := h.first x n hx ht (hne x n hx ht)
  times := h.times
  levels := h.levels
  ids := h.ids
  taken := h.taken
  overlay := h.overlay
  within := h.within
  timeFirst x n hx ht := h.timeFirst x n hx ht (hne x n hx ht)

/-- `treeOf_fresh` with `PutBooksE`. -/
theorem treeOf_freshE {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (hb : Books i base s tp) (hk : PutBooksE p i base s w) {x : NodeId} (hx : w.next ≤ x) :
    (treeOf i s w).obj x = none ∧ s.obj x = none ∧ w.nodes.lookup x = none ∧
      w.vals.lookup x = none ∧ w.taken.contains x = false ∧ ∀ m ∈ w.made, m.id ≠ x := by
  obtain ⟨hn, hv, hm, hbase, -⟩ := hk.ids
  have hs : s.obj x = none := (hb.ids x (Nat.le_trans hbase hx)).1
  have hnx : w.nodes.lookup x = none := by
    cases e : w.nodes.lookup x with
    | none => rfl
    | some n => exact absurd (hn x n e) (Nat.not_lt.mpr hx)
  have hvx : w.vals.lookup x = none := by
    cases e : w.vals.lookup x with
    | none => rfl
    | some h => exact absurd (hv x h e) (Nat.not_lt.mpr hx)
  have hmx : ∀ m ∈ w.made, m.id ≠ x := fun m hm' e => by
    have := (hm m hm').1
    omega
  have htx : w.taken.contains x = false := by
    cases e : w.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm', he⟩ := List.mem_map.mp (hk.taken x e)
      exact absurd he (hmx m hm')
  refine ⟨?_, hs, hnx, hvx, htx, hmx⟩
  simp only [treeOf, htx, hnx, hvx, hs, Bool.false_eq_true, ↓reduceIte]

theorem prim_lookup_withNode {w : MW} {x y : NodeId} {n n' : MNode}
    (h : (w.withNode x n).nodes.lookup y = some n') :
    (y = x ∧ n' = n) ∨ (y ≠ x ∧ w.nodes.lookup y = some n') := by
  by_cases hy : y = x
  · subst hy
    rw [MW.withNode, lookup_upsert_self] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  · rw [MW.withNode, lookup_upsert_ne _ _ hy] at h
    exact Or.inr ⟨hy, h⟩

/-- `putNode` of node x of the overlay, kept, keeps `PutBooksE` if the new
node n' has the kind of the old node n, no time after i, and either n's first
klong, or klongs that start with a time klong of i where n had none. -/
theorem putBooksE_withNode {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    {x : NodeId} {n n' : MNode} (hk : PutBooksE p i base s w) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hleaf : n'.leaf = n.leaf)
    (hfst : n'.ks.head? = n.ks.head? ∨ (n.ks = [] ∧ ∃ rest, n'.ks = .time i :: rest))
    (htimes : ∀ t, SIS.Tree.Klong.time t ∈ n'.ks → t ≤ i) :
    PutBooksE p i base s (w.withNode x n') := by
  have hwl : wLevel s (w.withNode x n') = wLevel s w := rfl
  refine ⟨?_, ?_, ?_, ?_, hk.taken, ?_, hk.within, ?_, ?_⟩
  · intro y m hy hty hne
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · rcases hfst with hh | ⟨hn0, rest, hr⟩
      · have hn : n.ks ≠ [] := by
          intro e; rw [e] at hh
          cases e' : m.ks with
          | nil => exact hne e'
          | cons _ _ => rw [e'] at hh; cases hh
        obtain ⟨t, rest, hr⟩ := hk.timeFirst y n hx ht hn
        obtain ⟨rest', hr'⟩ := prim_head_time hr hh
        rw [prim_firstTime_of hr']
        rw [← prim_firstTime_of hr]
        exact hk.first y n hx ht hn
      · rw [hk.empty y n hx ht hn0, prim_firstTime_of hr]
        simp
    · exact hk.first y m hy hty hne
  · intro y m hy t htm
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact htimes t htm
    · exact hk.times y m hy t htm
  · intro y m hy hty
    rw [hwl]
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · obtain ⟨g, h, h1, h2, h3, h4, h5⟩ := hk.levels y n hx ht
      exact ⟨g, h, h1, h2, h3, h4, by rw [hleaf, h5]⟩
    · exact hk.levels y m hy hty
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hk.ids
    refine ⟨fun y m hy => ?_, h2, h3, h4, h5⟩
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact h1 y n hx
    · exact h1 y m hy
  · intro y m hy
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact hk.overlay y n hx
    · exact hk.overlay y m hy
  · intro y m hy hty hne
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · rcases hfst with hh | ⟨_, rest, hr⟩
      · have hn : n.ks ≠ [] := by
          intro e; rw [e] at hh
          cases e' : m.ks with
          | nil => exact hne e'
          | cons _ _ => rw [e'] at hh; cases hh
        obtain ⟨t, rest, hr⟩ := hk.timeFirst y n hx ht hn
        obtain ⟨rest', hr'⟩ := prim_head_time hr hh
        exact ⟨t, rest', hr'⟩
      · exact ⟨i, rest, hr⟩
    · exact hk.timeFirst y m hy hty hne
  · intro y m hy hty he
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · rcases hfst with hh | ⟨hn0, rest, hr⟩
      · rw [he] at hh
        have hn0 : n.ks = [] := by
          cases e : n.ks with
          | nil => rfl
          | cons _ _ => rw [e] at hh; cases hh
        exact hk.empty y n hx ht hn0
      · rw [hr] at he; cases he
    · exact hk.empty y m hy hty he

/-- `putNode` of node x of the overlay, kept, keeps `PutBooks` if the new
node n' has the kind of the old node n, n's first klong (a time klong, by
B13) and no time after i. -/
theorem putBooks_withNode {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    {x : NodeId} {n n' : MNode} (hk : PutBooks p i base s w) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hleaf : n'.leaf = n.leaf)
    (hfst : n'.ks.head? = n.ks.head?) (htimes : ∀ t, SIS.Tree.Klong.time t ∈ n'.ks → t ≤ i) :
    PutBooks p i base s (w.withNode x n') := by
  apply (putBooksE_withNode hk.toE hx ht hleaf (Or.inl hfst) htimes).toBooks
  intro y m hy hty
  rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · obtain ⟨t, rest, hr⟩ := hk.timeFirst y n hx ht
    obtain ⟨rest', hr'⟩ := prim_head_time hr hfst
    rw [hr']; exact List.cons_ne_nil _ _
  · obtain ⟨t, rest, hr⟩ := hk.timeFirst y m hy hty
    rw [hr]; exact List.cons_ne_nil _ _

theorem prim_wLevel_afterNewKey {s : Tree} {w : MW} {p : MParams} {g h : Nat} {leaf : Bool}
    {ks : List MKlong} {y : NodeId} (hy : y ≠ w.next) :
    wLevel s (w.afterNewKey p g h leaf ks) y = wLevel s w y := by
  simp only [wLevel, MW.afterNewKey,
    prim_find_append_ne w.made ⟨w.next, p.keyLevel g h, false⟩ (Ne.symm hy)]

theorem prim_wLevel_afterNewValue {s : Tree} {w : MW} {h : Nat} {y : NodeId}
    (hy : y ≠ w.next) : wLevel s (w.afterNewValue h) y = wLevel s w y := by
  simp only [wLevel, MW.afterNewValue, prim_find_append_ne w.made ⟨w.next, 0, true⟩ (Ne.symm hy)]

theorem prim_lookup_afterNewKey {w : MW} {p : MParams} {g h : Nat} {leaf : Bool}
    {ks : List MKlong} {y : NodeId} {n : MNode} (hn : w.nodes.lookup w.next = none)
    (hy : (w.afterNewKey p g h leaf ks).nodes.lookup y = some n) :
    (y = w.next ∧ n = ⟨leaf, ks⟩) ∨ (y ≠ w.next ∧ w.nodes.lookup y = some n) := by
  by_cases e : y = w.next
  · subst e
    rw [MW.afterNewKey, prim_lookup_append_self _ _ hn] at hy
    cases hy
    exact Or.inl ⟨rfl, rfl⟩
  · rw [MW.afterNewKey, prim_lookup_append_ne _ _ e] at hy
    exact Or.inr ⟨e, hy⟩

theorem prim_gh_cons_ne {gh : List (NodeId × Nat × Nat)} {x y : NodeId} (g h : Nat)
    (hy : y ≠ x) : ((x, g, h) :: gh).lookup y = gh.lookup y := by
  rw [prim_lookup_cons]; simp only [hy, ↓reduceIte]

theorem prim_gh_cons_self (gh : List (NodeId × Nat × Nat)) (x g h : Nat) :
    ((x, g, h) :: gh).lookup x = some (g, h) := by
  rw [prim_lookup_cons]; simp

/-- `newKey` keeps `PutBooksE`, for a node within G and H, a segment leaf
exactly at height 0, with no klongs or klongs that start with a time klong of
i, and no time after i. -/
theorem putBooksE_afterNewKey {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {w : MW} {g h : Nat} {leaf : Bool} {ks : List MKlong} (hb : Books i base s tp)
    (hk : PutBooksE p i base s w) (hg : g ≤ p.G) (hh : h ≤ p.H) (hl : leaf = (h == 0))
    (hks : ks = [] ∨ ∃ rest, ks = .time i :: rest)
    (htimes : ∀ t, SIS.Tree.Klong.time t ∈ ks → t ≤ i) :
    PutBooksE p i base s (w.afterNewKey p g h leaf ks) := by
  obtain ⟨-, hs, hn, -, ht, hm⟩ := treeOf_freshE hb hk (Nat.le_refl _)
  have hf : w.made.find? (fun m => m.id == w.next) = none := by
    rw [List.find?_eq_none]
    intro m hm'
    simpa using hm m hm'
  have hwl : wLevel s (w.afterNewKey p g h leaf ks) w.next = p.keyLevel g h := by
    simp [wLevel, hs, MW.afterNewKey, List.find?_append, hf]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk.ids
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m hy hty hne
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · rcases hks with rfl | ⟨rest, rfl⟩
      · exact absurd rfl hne
      · rw [hs, prim_firstTime_cons]; simp
    · exact hk.first y m hy hty hne
  · intro y m hy t htm
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact htimes t htm
    · exact hk.times y m hy t htm
  · intro y m hy hty
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨hyn, hy⟩
    · exact ⟨g, h, prim_gh_cons_self _ _ _ _, hg, hh, hwl, hl⟩
    · obtain ⟨g', h', e1, e2⟩ := hk.levels y m hy hty
      refine ⟨g', h', ?_, e2.1, e2.2.1, ?_, e2.2.2.2⟩
      · show ((w.next, g, h) :: w.gh).lookup y = _
        rw [prim_gh_cons_ne _ _ hyn, e1]
      · rw [prim_wLevel_afterNewKey hyn, e2.2.2.1]
  · refine ⟨fun y m hy => ?_, fun y v hy => ?_, fun m hm' => ?_, ?_, fun hn' => ?_⟩
    · rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
      · show w.next < w.next + 2; omega
      · have := h1 y m hy; show y < w.next + 2; omega
    · have := h2 y v hy; show y < w.next + 2; omega
    · simp only [MW.afterNewKey, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · have := h3 m hm'; exact ⟨by show m.id < w.next + 2; omega, this.2⟩
      · exact ⟨by show w.next < w.next + 2; omega, h4⟩
    · show base ≤ w.next + 2; omega
    · have := h5 hn'; show w.top.id < w.next + 2; omega
  · intro y hy
    have := hk.taken y hy
    simp only [MW.afterNewKey, List.map_append, List.mem_append]
    exact Or.inl this
  · intro y m hy
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · right
      simp [MW.afterNewKey]
    · rcases hk.overlay y m hy with e | e
      · exact Or.inl e
      · right
        simp only [MW.afterNewKey, List.map_append, List.mem_append]
        exact Or.inl e
  · have hc : (decide (p.G < g) || decide (p.H < h)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
      exact ⟨hg, hh⟩
    simp only [MW.afterNewKey, hc, Bool.false_eq_true, ↓reduceIte]
    exact hk.within
  · intro y m hy hty hne
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · rcases hks with rfl | ⟨rest, rfl⟩
      · exact absurd rfl hne
      · exact ⟨i, rest, rfl⟩
    · exact hk.timeFirst y m hy hty hne
  · intro y m hy hty he
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact hs
    · exact hk.empty y m hy hty he

/-- `newKey` keeps `PutBooks`, for a node within G and H, a segment leaf
exactly at height 0, with klongs that start with a time klong of i, and no
time after i. -/
theorem putBooks_afterNewKey {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {w : MW} {g h : Nat} {leaf : Bool} {ks : List MKlong} (hb : Books i base s tp)
    (hk : PutBooks p i base s w) (hg : g ≤ p.G) (hh : h ≤ p.H) (hl : leaf = (h == 0))
    (hks : ∃ rest, ks = .time i :: rest) (htimes : ∀ t, SIS.Tree.Klong.time t ∈ ks → t ≤ i) :
    PutBooks p i base s (w.afterNewKey p g h leaf ks) := by
  have hn := (treeOf_fresh hb hk (Nat.le_refl _)).2.2.1
  apply (putBooksE_afterNewKey hb hk.toE hg hh hl (Or.inr hks) htimes).toBooks
  intro y m hy hty
  rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · obtain ⟨rest, hr⟩ := hks
    show ks ≠ []
    rw [hr]; exact List.cons_ne_nil _ _
  · obtain ⟨t, rest, hr⟩ := hk.timeFirst y m hy hty
    rw [hr]; exact List.cons_ne_nil _ _

/-- `newKey` with no klongs: B1 and B13 fail for the new node only, which is
no node of s: `PutBooksE`, and every other node kept has klongs. -/
theorem putBooks_afterNewKey_nil {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {w : MW} {g h : Nat} {leaf : Bool} (hb : Books i base s tp) (hk : PutBooks p i base s w)
    (hg : g ≤ p.G) (hh : h ≤ p.H) (hl : leaf = (h == 0)) :
    PutBooksE p i base s (w.afterNewKey p g h leaf []) ∧
      ∀ y m, (w.afterNewKey p g h leaf []).nodes.lookup y = some m →
        (w.afterNewKey p g h leaf []).taken.contains y = false → m.ks = [] → y = w.next := by
  have hn := (treeOf_fresh hb hk (Nat.le_refl _)).2.2.1
  refine ⟨putBooksE_afterNewKey hb hk.toE hg hh hl (Or.inl rfl) (by simp), ?_⟩
  intro y m hy hty he
  rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
  · rfl
  · obtain ⟨t, rest, hr⟩ := hk.timeFirst y m hy hty
    rw [hr] at he; cases he

/-- `newValue` keeps `PutBooksE`. -/
theorem putBooksE_afterNewValue {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    (hk : PutBooksE p i base s w) (h : Nat) : PutBooksE p i base s (w.afterNewValue h) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk.ids
  refine ⟨hk.first, hk.times, ?_, ?_, ?_, ?_, hk.within, hk.timeFirst, hk.empty⟩
  · intro y m hy hty
    have hyn : y ≠ w.next := Nat.ne_of_lt (h1 y m hy)
    rw [prim_wLevel_afterNewValue hyn]
    exact hk.levels y m hy hty
  · refine ⟨fun y m hy => ?_, fun y v hy => ?_, fun m hm' => ?_, ?_, fun hn' => ?_⟩
    · have := h1 y m hy; show y < w.next + 2; omega
    · by_cases e : y = w.next
      · subst e; show w.next < w.next + 2; omega
      · rw [MW.afterNewValue, prim_lookup_append_ne _ _ e] at hy
        have := h2 y v hy; show y < w.next + 2; omega
    · simp only [MW.afterNewValue, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · have := h3 m hm'; exact ⟨by show m.id < w.next + 2; omega, this.2⟩
      · exact ⟨by show w.next < w.next + 2; omega, h4⟩
    · show base ≤ w.next + 2; omega
    · have := h5 hn'; show w.top.id < w.next + 2; omega
  · intro y hy
    have := hk.taken y hy
    simp only [MW.afterNewValue, List.map_append, List.mem_append]
    exact Or.inl this
  · intro y m hy
    rcases hk.overlay y m hy with e | e
    · exact Or.inl e
    · right
      simp only [MW.afterNewValue, List.map_append, List.mem_append]
      exact Or.inl e

/-- `newValue` keeps `PutBooks`. -/
theorem putBooks_afterNewValue {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    (hk : PutBooks p i base s w) (h : Nat) : PutBooks p i base s (w.afterNewValue h) := by
  apply (putBooksE_afterNewValue hk.toE h).toBooks
  intro y m hy hty
  obtain ⟨t, rest, hr⟩ := hk.timeFirst y m hy hty
  rw [hr]; exact List.cons_ne_nil _ _

/-! ### 4.2 The frame -/

theorem prim_any_of_lookup {β : Type} {ns : List (NodeId × β)} {x : NodeId} {b : β}
    (h : ns.lookup x = some b) : ns.any (fun q => q.1 == x) = true := by
  cases e : ns.any (fun q => q.1 == x)
  · rw [prim_lookup_none x ns e] at h; cases h
  · rfl

theorem mem_dirtyOf_of_lookup {w : MW} {x : NodeId} {n : MNode}
    (hx : w.nodes.lookup x = some n) : x ∈ dirtyOf w := by
  have := prim_any_of_lookup hx
  simp only [List.any_eq_true, beq_iff_eq] at this
  obtain ⟨q, hq, e⟩ := this
  exact List.mem_map.mpr ⟨q, hq, e⟩

/-- `putNode` of a node of the overlay leaves D as it is. -/
theorem dirtyOf_withNode {w : MW} {x : NodeId} {n n' : MNode}
    (hx : w.nodes.lookup x = some n) : dirtyOf (w.withNode x n') = dirtyOf w := by
  simp only [dirtyOf, MW.withNode, SIS.Tree.upsert, prim_any_of_lookup hx, ↓reduceIte,
    List.map_map]
  congr 1
  funext q
  by_cases e : q.1 = x
  · simp [e]
  · simp [e]

theorem prim_any_false {β : Type} (x : NodeId) : ∀ ns : List (NodeId × β),
    ns.lookup x = none → ns.any (fun q => q.1 == x) = false
  | [], _ => rfl
  | (k, m) :: r, h => by
    rw [prim_lookup_cons] at h
    by_cases e : x = k
    · simp [e] at h
    · simp only [e, ↓reduceIte] at h
      simp only [List.any_cons, prim_any_false x r h, Bool.or_false, beq_eq_false_iff_ne]
      exact Ne.symm e

theorem mem_dirtyOf_withNode {w : MW} {x y : NodeId} {n : MNode} :
    y ∈ dirtyOf (w.withNode x n) ↔ y ∈ dirtyOf w ∨ y = x := by
  cases e : w.nodes.lookup x with
  | some n0 =>
    rw [dirtyOf_withNode e]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact mem_dirtyOf_of_lookup e
  | none =>
    have hany : w.nodes.any (fun q => q.1 == x) = false := prim_any_false x w.nodes e
    simp only [dirtyOf, MW.withNode, SIS.Tree.upsert, hany, Bool.false_eq_true, ↓reduceIte,
      List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton]

theorem dirtyOf_afterNewKey (w : MW) (p : MParams) (g h : Nat) (leaf : Bool)
    (ks : List MKlong) : dirtyOf (w.afterNewKey p g h leaf ks) = dirtyOf w ++ [w.next] := by
  simp [dirtyOf, MW.afterNewKey]

theorem dirtyOf_afterNewValue (w : MW) (h : Nat) : dirtyOf (w.afterNewValue h) = dirtyOf w :=
  rfl

/-- The frame after node x is set to o: x is in D, and o extends the node x of
s, if any. -/
theorem Frame.set {i : Time} {s T : Tree} {D D' : List NodeId} (hF : Frame i s D T)
    (hD : ∀ y ∈ D, y ∈ D') {x : NodeId} (hxD : x ∈ D') {o : Obj}
    (ho : ∀ o0, s.obj x = some o0 → Ext i o0 o) : Frame i s D' (T.set x o) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun y o0 hy => ?_, fun y m hy hs => ?_, h3⟩
  · by_cases e : y = x
    · subst e
      exact ⟨o, by simp [Tree.set], ho o0 hy, fun h => absurd hxD h⟩
    · obtain ⟨o', ho', he, hu⟩ := h1 y o0 hy
      refine ⟨o', by simp [Tree.set, e, ho'], he, fun hy' => hu (fun hd => hy' (hD y hd))⟩
  · by_cases e : y = x
    · subst e; exact hxD
    · simp only [Tree.set, e, ↓reduceIte] at hy
      exact hD y (h2 y m hy hs)

/-- What the frame says of a node of s in the overlay, kept: its level and
kind, and klongs that extend those of s (the premise of `add_ext`). -/
theorem frame_overlay_ext {i : Time} {s : Tree} {w : MW} {x : NodeId} {n : MNode}
    {n0 : KNode} (hF : Frame i s (dirtyOf w) (treeOf i s w)) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hs : s.obj x = some (.key n0)) :
    wLevel s w x = n0.level ∧ n.leaf = n0.leaf ∧
      (ksOf n = n0.ks ∨ ∃ more, ksOf n = n0.ks ++ Klong.time i :: more) := by
  obtain ⟨o', ho', he, -⟩ := hF.1 x _ hs
  rw [treeOf_obj_overlay i s hx ht] at ho'
  cases ho'
  exact he

/-- `putNode` of node x of the overlay, kept, keeps the frame if the new node
has the old one's kind and, for a node of s, klongs that extend those of s:
the same, or those, a time klong of i and more (`add_ext`'s form). -/
theorem frame_withNode {i : Time} {s : Tree} {w : MW} {x : NodeId} {n n' : MNode}
    (hF : Frame i s (dirtyOf w) (treeOf i s w)) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hleaf : n'.leaf = n.leaf)
    (hext : ∀ n0, s.obj x = some (.key n0) →
      ksOf n' = n0.ks ∨ ∃ more, ksOf n' = n0.ks ++ Klong.time i :: more) :
    Frame i s (dirtyOf (w.withNode x n')) (treeOf i s (w.withNode x n')) := by
  rw [treeOf_withNode i s n' ht, dirtyOf_withNode hx]
  refine hF.set (fun y hy => hy) (mem_dirtyOf_of_lookup hx) (fun o0 ho0 => ?_)
  obtain ⟨o', ho', he, -⟩ := hF.1 x o0 ho0
  rw [treeOf_obj_overlay i s hx ht] at ho'
  cases ho'
  cases o0 with
  | val v => exact absurd he (by simp [Ext])
  | key n0 =>
    obtain ⟨e1, e2, -⟩ := he
    exact ⟨e1, by rw [hleaf]; exact e2, hext n0 ho0⟩

/-- `newKey` keeps the frame: the node made is no node of s. -/
theorem frame_afterNewKey {i : Time} {s : Tree} {w : MW} (p : MParams) (g h : Nat)
    (leaf : Bool) (ks : List MKlong) (hF : Frame i s (dirtyOf w) (treeOf i s w))
    (hs : s.obj w.next = none) (hn : w.nodes.lookup w.next = none)
    (ht : w.taken.contains w.next = false) (hm : ∀ m ∈ w.made, m.id ≠ w.next) :
    Frame i s (dirtyOf (w.afterNewKey p g h leaf ks))
      (treeOf i s (w.afterNewKey p g h leaf ks)) := by
  rw [treeOf_afterNewKey i s p g h leaf ks hs hn ht hm, dirtyOf_afterNewKey]
  refine hF.set (fun y hy => List.mem_append_left _ hy) (by simp) (fun o0 ho0 => ?_)
  rw [hs] at ho0; cases ho0

/-- `newValue` keeps the frame: the value made is no node of s. -/
theorem frame_afterNewValue {i : Time} {s : Tree} {w : MW} (h : Nat)
    (hF : Frame i s (dirtyOf w) (treeOf i s w)) (hs : s.obj w.next = none)
    (hn : w.nodes.lookup w.next = none) (hv : w.vals.lookup w.next = none)
    (ht : w.taken.contains w.next = false) :
    Frame i s (dirtyOf (w.afterNewValue h)) (treeOf i s (w.afterNewValue h)) := by
  rw [treeOf_afterNewValue i s h hn hv ht, dirtyOf_afterNewValue]
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun y o0 hy => ?_, fun y m hy hs' => ?_, h3⟩
  · have e : y ≠ w.next := by intro e; rw [e, hs] at hy; cases hy
    obtain ⟨o', ho', he, hu⟩ := h1 y o0 hy
    exact ⟨o', by simp [Tree.set, e, ho'], he, hu⟩
  · have e : y ≠ w.next := by intro e; rw [e] at hy; simp [Tree.set] at hy
    simp only [Tree.set, e, ↓reduceIte] at hy
    exact h2 y m hy hs'

/-! ### 4.3 BalancedOK -/

/-- BalancedOK after node x is set to o: o, if a key node, has a level above
0, is a segment leaf exactly at height 0, and each key klong of it, in an
inner node, names a key node of the tree before, one level below; and if x
was a key node, o is a key node on its level, so that a node that names x
still finds one. -/
theorem BalancedAll.set {p : MParams} {T : Tree} (hB : BalancedAll p T) {x : NodeId} {o : Obj}
    (hkeep : ∀ m0, T.obj x = some (.key m0) → ∃ m, o = .key m ∧ m.level = m0.level)
    (ho : ∀ m, o = .key m → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
      (m.leaf = false → ∀ c y, Klong.key c y ∈ m.ks → ∃ m', T.obj y = some (.key m') ∧
        m'.level + 1 = m.level)) :
    BalancedAll p (T.set x o) := by
  intro y m hy
  by_cases e : y = x
  · subst e
    simp only [Tree.set, ↓reduceIte, Option.some.injEq] at hy
    obtain ⟨h1, h2, h3⟩ := ho m hy
    refine ⟨h1, h2, fun hl c z hz => ?_⟩
    obtain ⟨m', hm', hlev⟩ := h3 hl c z hz
    have hzy : z ≠ y := by
      intro ez; subst ez
      obtain ⟨m'', ho', hl''⟩ := hkeep m' hm'
      rw [hy] at ho'; cases ho'
      omega
    exact ⟨m', by simp [Tree.set, hzy, hm'], hlev⟩
  · simp only [Tree.set, e, ↓reduceIte] at hy
    obtain ⟨h1, h2, h3⟩ := hB y m hy
    refine ⟨h1, h2, fun hl c z hz => ?_⟩
    obtain ⟨m', hm', hlev⟩ := h3 hl c z hz
    by_cases ez : z = x
    · subst ez
      obtain ⟨m'', ho', hl''⟩ := hkeep m' hm'
      exact ⟨m'', by simp [Tree.set, ho'], by omega⟩
    · exact ⟨m', by simp [Tree.set, ez, hm'], hlev⟩

theorem prim_key_mem_ksOf {n : MNode} {c : Nat} {y : NodeId} (h : Klong.key c y ∈ ksOf n) :
    SIS.Tree.Klong.key c y ∈ n.ks := by
  obtain ⟨k, hk, e⟩ := List.mem_map.mp h
  cases k with
  | time t => simp [kOf] at e
  | key c' y' =>
    simp only [kOf, Klong.key.injEq] at e
    rw [← e.1, ← e.2]; exact hk
  | del b => simp [kOf] at e

theorem prim_heightOf_keyLevel (p : MParams) (g : Nat) {h : Nat} (hh : h ≤ p.H) :
    p.heightOf (p.keyLevel g h) = h := by
  unfold SIS.Tree.Params.heightOf SIS.Tree.Params.keyLevel
  rw [show 1 + (p.G - g) * (p.H + 1) + h - 1 = h + (p.G - g) * (p.H + 1) by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hh)]

/-- `putNode` of node x of the overlay, kept, keeps BalancedOK if the new node
has the old one's kind and each key klong of it, in an inner node, names a key
node of the map one level below x's. -/
theorem balancedAll_withNode {p : MParams} {i : Time} {s : Tree} {w : MW} {x : NodeId}
    {n n' : MNode} (hB : BalancedAll p (treeOf i s w)) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hleaf : n'.leaf = n.leaf)
    (hks : n'.leaf = false → ∀ c y, SIS.Tree.Klong.key c y ∈ n'.ks →
      ∃ m', (treeOf i s w).obj y = some (.key m') ∧ m'.level + 1 = wLevel s w x) :
    BalancedAll p (treeOf i s (w.withNode x n')) := by
  rw [treeOf_withNode i s n' ht]
  have hold := treeOf_obj_overlay i s hx ht
  obtain ⟨h1, h2, -⟩ := hB x _ hold
  refine hB.set (fun m0 hm0 => ⟨_, rfl, ?_⟩) (fun m hm => ?_)
  · rw [hold] at hm0; cases hm0; rfl
  · cases hm
    refine ⟨h1, by rw [hleaf]; exact h2, fun hl c y hy => hks hl c y (prim_key_mem_ksOf hy)⟩

/-- `newKey` keeps BalancedOK, for a node at height h at most H, a segment
leaf exactly at height 0, whose key klongs, in an inner node, name key nodes of
the map one level below. -/
theorem balancedAll_afterNewKey {p : MParams} {i : Time} {s : Tree} {w : MW} (g h : Nat)
    (leaf : Bool) (ks : List MKlong) (hB : BalancedAll p (treeOf i s w))
    (hs : s.obj w.next = none) (hn : w.nodes.lookup w.next = none)
    (ht : w.taken.contains w.next = false) (hm : ∀ m ∈ w.made, m.id ≠ w.next)
    (hh : h ≤ p.H) (hl : leaf = (h == 0))
    (hks : leaf = false → ∀ c y, SIS.Tree.Klong.key c y ∈ ks →
      ∃ m', (treeOf i s w).obj y = some (.key m') ∧ m'.level + 1 = p.keyLevel g h) :
    BalancedAll p (treeOf i s (w.afterNewKey p g h leaf ks)) := by
  rw [treeOf_afterNewKey i s p g h leaf ks hs hn ht hm]
  refine hB.set (fun m0 hm0 => ?_) (fun m hm => ?_)
  · exfalso
    simp only [treeOf, ht, hn, Bool.false_eq_true, ↓reduceIte] at hm0
    cases e : w.vals.lookup w.next with
    | none => rw [e, hs] at hm0; cases hm0
    | some v => rw [e] at hm0; cases hm0
  · cases hm
    refine ⟨by show 0 < p.keyLevel g h; unfold SIS.Tree.Params.keyLevel; omega, ?_,
      fun hl' c y hy => ?_⟩
    · show leaf = (p.heightOf (p.keyLevel g h) == 0)
      rw [prim_heightOf_keyLevel p g hh, hl]
    · obtain ⟨k, hk, e⟩ := List.mem_map.mp hy
      cases k with
      | time t => simp [kOf] at e
      | key c' y' =>
        simp only [kOf, Klong.key.injEq] at e
        rw [e.1, e.2] at hk
        exact hks hl' c y hk
      | del b => simp [kOf] at e

/-- `newValue` keeps BalancedOK: the value made is no key node. -/
theorem balancedAll_afterNewValue {p : MParams} {i : Time} {s : Tree} {w : MW} (h : Nat)
    (hB : BalancedAll p (treeOf i s w)) (hs : s.obj w.next = none)
    (hn : w.nodes.lookup w.next = none) (hv : w.vals.lookup w.next = none)
    (ht : w.taken.contains w.next = false) :
    BalancedAll p (treeOf i s (w.afterNewValue h)) := by
  rw [treeOf_afterNewValue i s h hn hv ht]
  refine hB.set (fun m0 hm0 => ?_) (fun m hm => ?_)
  · simp only [treeOf, ht, hn, hv, hs, Bool.false_eq_true, ↓reduceIte] at hm0
    cases hm0
  · cases hm

/-! ### 4.4 The key access path -/

theorem PathOk.mono {i : Time} {s : Tree} {w : MW} {d e : Nat} (h : PathOk i s w d)
    (he : e ≤ d) : PathOk i s w e :=
  ⟨h.root, fun d' hd => h.nodes d' (by omega), fun d' hd => h.links d' (by omega)⟩

/-- A node on the path up to its depth is a node of the overlay. -/
theorem PathOk.lookup {i : Time} {s : Tree} {w : MW} {d e : Nat} (h : PathOk i s w d)
    (he : e ≤ d) {c : Option Nat} {u : NodeId} (hu : w.path[e]? = some (c, u)) :
    ∃ n, w.nodes.lookup u = some n ∧ w.taken.contains u = false := by
  obtain ⟨c', u', n, h1, h2, h3⟩ := h.nodes e he
  rw [hu] at h1
  cases h1
  exact ⟨n, h2, h3⟩

/-- The path depends only on these fields of the state and its map. -/
theorem PathOk.congr {i : Time} {s : Tree} {w w' : MW} {d : Nat} (hP : PathOk i s w d)
    (h1 : w'.path = w.path) (h2 : w'.top = w.top) (h3 : w'.nodes = w.nodes)
    (h4 : w'.taken = w.taken) (h5 : treeOf i s w' = treeOf i s w) : PathOk i s w' d := by
  refine ⟨by rw [h1, h2]; exact hP.root, fun e he => ?_, fun e he => ?_⟩
  · rw [h1, h3, h4]; exact hP.nodes e he
  · rw [h1, h5]; exact hP.links e he

/-- `putNode` of node x, kept, keeps the path if the new node keeps the live
klongs that the path follows from x. -/
theorem pathOk_withNode {i : Time} {s : Tree} {w : MW} {d : Nat} {x : NodeId} {n' : MNode}
    (hP : PathOk i s w d) (ht : w.taken.contains x = false)
    (hlive : ∀ e < d, ∀ c0 c y, w.path[e]? = some (c0, x) → w.path[e + 1]? = some (some c, y) →
      (c, y) ∈ live (ksOf n')) :
    PathOk i s (w.withNode x n') d := by
  refine ⟨hP.root, fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨c, u, n, h1, h2, h3⟩ := hP.nodes e he
    by_cases eu : u = x
    · subst eu
      exact ⟨c, u, n', h1, lookup_upsert_self _ _ _, h3⟩
    · exact ⟨c, u, n, h1, by rw [MW.withNode, lookup_upsert_ne _ _ eu]; exact h2, h3⟩
  · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := hP.links e he
    rw [treeOf_withNode i s n' ht]
    by_cases eu : u = x
    · subst eu
      exact ⟨c0, u, c, y, ⟨wLevel s w u, n'.leaf, ksOf n'⟩, h1, h2, by simp [Tree.set],
        hlive e he c0 c y h1 h2⟩
    · exact ⟨c0, u, c, y, nu, h1, h2, by simp [Tree.set, eu, h3], h4⟩

/-- `putNode` of node x of the overlay, kept, keeps the path if the new node
keeps every live klong of the old one. -/
theorem pathOk_withNode_live {i : Time} {s : Tree} {w : MW} {d : Nat} {x : NodeId}
    {n n' : MNode} (hP : PathOk i s w d) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hsub : ∀ cy ∈ live (ksOf n), cy ∈ live (ksOf n')) :
    PathOk i s (w.withNode x n') d := by
  refine pathOk_withNode hP ht (fun e he c0 c y h1 h2 => hsub _ ?_)
  obtain ⟨c0', u, c', y', nu, h1', h2', h3, h4⟩ := hP.links e he
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [treeOf_obj_overlay i s hx ht] at h3
  cases h3
  exact h4

/-- `newKey` keeps the path. -/
theorem pathOk_afterNewKey {i : Time} {s : Tree} {w : MW} {d : Nat} (p : MParams) (g h : Nat)
    (leaf : Bool) (ks : List MKlong) (hP : PathOk i s w d) (hs : s.obj w.next = none)
    (hn : w.nodes.lookup w.next = none) (ht : w.taken.contains w.next = false)
    (hm : ∀ m ∈ w.made, m.id ≠ w.next) : PathOk i s (w.afterNewKey p g h leaf ks) d := by
  refine ⟨hP.root, fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨c, u, n, h1, h2, h3⟩ := hP.nodes e he
    exact ⟨c, u, n, h1, prim_lookup_append_some _ h2, h3⟩
  · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := hP.links e he
    obtain ⟨n, hu, -⟩ := hP.lookup (Nat.le_of_lt he) h1
    have eu : u ≠ w.next := by intro eu; rw [eu, hn] at hu; cases hu
    rw [treeOf_afterNewKey i s p g h leaf ks hs hn ht hm]
    exact ⟨c0, u, c, y, nu, h1, h2, by simp [Tree.set, eu, h3], h4⟩

/-- `newValue` keeps the path. -/
theorem pathOk_afterNewValue {i : Time} {s : Tree} {w : MW} {d : Nat} (h : Nat)
    (hP : PathOk i s w d) (hn : w.nodes.lookup w.next = none)
    (hv : w.vals.lookup w.next = none) (ht : w.taken.contains w.next = false) :
    PathOk i s (w.afterNewValue h) d := by
  refine ⟨hP.root, hP.nodes, fun e he => ?_⟩
  obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := hP.links e he
  obtain ⟨n, hu, -⟩ := hP.lookup (Nat.le_of_lt he) h1
  have eu : u ≠ w.next := by intro eu; rw [eu, hn] at hu; cases hu
  rw [treeOf_afterNewValue i s h hn hv ht]
  exact ⟨c0, u, c, y, nu, h1, h2, by simp [Tree.set, eu, h3], h4⟩

/-! ### 4.5 The top, and a step that leaves the map -/

/-- `WTopInv` speaks only of the state's super root and whether the writer
made it. -/
theorem topInv_congr {i : Time} {s : Tree} {tp : Top} {w w' : MW}
    (h : WTopInv i s tp w.top w.newTop) (h1 : w'.top = w.top) (h2 : w'.newTop = w.newTop) :
    WTopInv i s tp w'.top w'.newTop := by
  rw [h1, h2]; exact h

/-- `PutBooks` depends only on these fields of the state. -/
theorem putBooks_congr {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w w' : MW}
    (hk : PutBooks p i base s w) (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals)
    (h3 : w'.taken = w.taken) (h4 : w'.made = w.made) (h5 : w'.top = w.top)
    (h6 : w'.newTop = w.newTop) (h7 : w'.gh = w.gh) (h8 : w'.next = w.next)
    (h9 : w'.outside = w.outside) : PutBooks p i base s w' := by
  cases w; cases w'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨hk.first, hk.times, hk.levels, hk.ids, hk.taken, hk.overlay, hk.within, hk.timeFirst⟩

/-- `PInv` after a step that leaves the map as it is, with D as large, the
same super root, and the books. -/
theorem PInv.of_map {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w w' : MW} (hI : PInv p i base s tp ex C w)
    (hT : treeOf i s w' = treeOf i s w) (hD : ∀ y ∈ dirtyOf w, y ∈ dirtyOf w')
    (h5 : w'.top = w.top) (h6 : w'.newTop = w.newTop) (hk : PutBooks p i base s w') :
    PInv p i base s tp ex C w' := by
  refine ⟨?_, ?_, ?_, topInv_congr hI.top h5 h6, ?_, hk⟩
  · rw [hT, h5]; exact hI.root
  · rw [hT, h5]; exact hI.sound
  · rw [hT]; exact hI.frame.mono hD
  · rw [hT]; exact hI.balanced

/-- `PInv` depends only on these fields of the state: `setMadeFor`, `note`
and the steps of the path keep it. -/
theorem PInv.congr {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w w' : MW} (hI : PInv p i base s tp ex C w)
    (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken)
    (h4 : w'.made = w.made) (h5 : w'.top = w.top) (h6 : w'.newTop = w.newTop)
    (h7 : w'.gh = w.gh) (h8 : w'.next = w.next) (h9 : w'.outside = w.outside) :
    PInv p i base s tp ex C w' :=
  hI.of_map (treeOf_congr i s h1 h2 h3 h4 h5 h6) (fun y hy => by simpa [dirtyOf, h1] using hy)
    h5 h6 (putBooks_congr hI.books h1 h2 h3 h4 h5 h6 h7 h8 h9)

end Contract
