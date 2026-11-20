/-
bergdb 030-29: the facts of PE's tree that the proof of `dirtyNodeBound_eq_sb`
uses, from a state PE keeps (`Inv`).

* `at_self_of_inv`: the tree read at t is the tree.
* `rpd`: TREE's walk with each node's parent and depth; with TREE (no node
  reached twice) each node of the tree has one parent and one depth
  (`rpd_unique`), and a live child of a node of the tree is listed with that
  node as its parent, one deeper (`rpd_child`). `treeFn`: the parents,
  depths, kinds and heights that Java's records hold.
* `nxt`: one step of a key's walk (Java's `searchLte` in an inner node,
  `searchEq` in a segment leaf); `keyP_chain`: the walk of a key (`keyP`) is
  the chain of these steps from the space root, each node sound and shaped
  as PE's trees at its segment, its end a segment leaf where the next step
  finds nothing.
-/
import Contract.Proof.DnbCount
import Contract.Proof.DnbRoom

namespace Contract.PE

open DNB

variable {cf : Cfg} {s : Tree}

/-! ## The tree at t -/

/-- The tree of a state PE keeps at t is the tree read at t. -/
theorem at_self_of_inv {t : Time} {tp : Top} {next : NodeId} (hI : Inv cf t s tp next) : s.at t = s := by
  apply tree_at_self
  · intro x n hx u hu
    exact Nat.lt_succ_iff.mp ((hI.sok x n hx).2.2 u hu)
  · intro r hr
    rw [hI.roots] at hr
    simp only [rootsOf, List.mem_map] at hr
    obtain ⟨⟨z, nz⟩, hz, rfl⟩ := hr
    exact hI.top.times z nz hz

/-! ## The walk from a node, its sublists -/

/-- A node a sound node reaches has its walk within the walk of the node. -/
theorem R_sub_of_mem : ∀ (L : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode},
    s.obj x = some (.key n) → n.level ≤ L → Good s x lo hi →
    ∀ y ∈ R s x, (R s y).Sublist (R s x) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x lo hi n hobj hL hg y hy
    have hy' := hy
    rw [R_good hg hobj] at hy'
    rcases List.mem_cons.mp hy' with rfl | hy'
    · exact List.Sublist.refl _
    · obtain ⟨⟨c, z⟩, hcz, hyz⟩ := List.mem_flatMap.mp hy'
      have hsub := R_sub_kid hg hobj hcz
      rcases good_kids hg hobj c z hcz with ⟨m, hm, hlt, lo', hi', hgz⟩ | ⟨v, hv⟩
      · exact (ih m.level (by omega) hm (le_refl _) hgz y hyz).trans hsub
      · have hRz : R s z = [z] := by simp [R, Tree.fuel, hv, reachAt]
        rw [hRz, List.mem_singleton] at hyz
        subst hyz
        exact hsub

/-- The nodes of a key node's walk that are key nodes are sound and shaped as
PE's trees at their height. -/
theorem R_shaped_all : ∀ (L : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} {g : Nat} {n : KNode},
    s.obj x = some (.key n) → n.level ≤ L → Good s x lo hi → Shaped cf s g (htIn cf s x) x →
    ∀ y ∈ R s x, ∀ m, s.obj y = some (.key m) →
      ∃ g' lo' hi', Good s y lo' hi' ∧ Shaped cf s g' (htIn cf s y) y := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x lo hi g n hobj hL hg hsh y hy m hm
    have hy' := hy
    rw [R_good hg hobj] at hy'
    rcases List.mem_cons.mp hy' with rfl | hy'
    · exact ⟨g, lo, hi, hg, hsh⟩
    · obtain ⟨⟨c, z⟩, hcz, hyz⟩ := List.mem_flatMap.mp hy'
      rcases good_kids hg hobj c z hcz with ⟨mz, hmz, hlt, lo', hi', hgz⟩ | ⟨v, hv⟩
      · have hshz : ∃ g', Shaped cf s g' (htIn cf s z) z := by
          cases hl : n.leaf with
          | false => exact ⟨g, shaped_kid_inner hsh hobj hl hcz⟩
          | true =>
            cases hlg : isLong c with
            | false =>
              obtain ⟨v, hv⟩ := good_val hg hobj hl hcz hlg
              rw [hv] at hmz; cases hmz
            | true => exact ⟨g + 1, shaped_kid_leaf hsh hobj hl hcz hlg⟩
        obtain ⟨g', hshz⟩ := hshz
        exact ih mz.level (by omega) hmz (le_refl _) hgz hshz y hyz m hm
      · have hRz : R s z = [z] := by simp [R, Tree.fuel, hv, reachAt]
        rw [hRz, List.mem_singleton] at hyz
        subst hyz
        rw [hv] at hm; cases hm

/-! ## Parents and depths -/

/-- TREE's walk from x with each node's parent and depth. -/
def rpd (s : Tree) : Nat → NodeId → Option NodeId → Nat → List (NodeId × Option NodeId × Nat)
  | 0, x, u, d => [(x, u, d)]
  | f + 1, x, u, d =>
    (x, u, d) :: (match s.obj x with
      | some (.key n) => (live n.ks).flatMap (fun cy => rpd s f cy.2 (some x) (d + 1))
      | _ => [])

theorem rpd_map (s : Tree) : ∀ (f : Nat) (x : NodeId) (u : Option NodeId) (d : Nat),
    (rpd s f x u d).map (·.1) = reachAt s f x
  | 0, x, u, d => rfl
  | f + 1, x, u, d => by
    simp only [rpd, reachAt, List.map_cons]
    congr 1
    cases s.obj x with
    | none => rfl
    | some o =>
      cases o with
      | val v => rfl
      | key n =>
        simp only [List.map_flatMap]
        apply List.flatMap_congr
        intro cy _
        exact rpd_map s f cy.2 _ _

theorem rpd_head (s : Tree) (f : Nat) (x : NodeId) (u : Option NodeId) (d : Nat) :
    (x, u, d) ∈ rpd s f x u d := by
  cases f <;> simp [rpd]

/-- **A live child of a listed node is listed**, with it as its parent, one
deeper (from a sound node with enough fuel). -/
theorem rpd_child : ∀ (f : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} (u : Option NodeId) (d : Nat),
    Good s x lo hi → s.fuel x ≤ f →
    ∀ z uz dz, (z, uz, dz) ∈ rpd s f x u d → ∀ n, s.obj z = some (.key n) →
      ∀ c y, (c, y) ∈ live n.ks → (y, some z, dz + 1) ∈ rpd s f x u d := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro x lo hi u d hg hf z uz dz hz n hn c y hcy
    obtain ⟨nx, hx⟩ := good_obj hg
    have hfx : s.fuel x = nx.level + 1 := by simp [Tree.fuel, hx]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [rpd, hx, List.mem_cons, List.mem_flatMap] at hz ⊢
    rcases hz with h | ⟨⟨c', y'⟩, hcy', hz⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [hx] at hn
      obtain rfl : nx = n := by injection hn with h1; injection h1
      exact Or.inr ⟨(c, y), hcy, rpd_head s f' y _ _⟩
    · right
      refine ⟨(c', y'), hcy', ?_⟩
      rcases good_kids hg hx c' y' hcy' with ⟨m, hm, hlt, lo', hi', hgy⟩ | ⟨v, hv⟩
      · have hfy : s.fuel y' ≤ f' := by simp [Tree.fuel, hm]; omega
        exact ih f' (by omega) (some x) (d + 1) hgy hfy z uz dz hz n hn c y hcy
      · exfalso
        have e : rpd s f' y' (some x) (d + 1) = [(y', some x, d + 1)] := by
          cases f' <;> simp [rpd, hv]
        rw [e, List.mem_singleton, Prod.mk.injEq] at hz
        rw [hz.1, hv] at hn; cases hn

/-- A node listed with a parent is a live child of a listed key node, one
less deep. -/
theorem rpd_parent (s : Tree) : ∀ (f : Nat) (x : NodeId) (u : Option NodeId) (d : Nat) (z y : NodeId)
    (dz : Nat), (z, some y, dz) ∈ rpd s f x u d → (z = x ∧ u = some y ∧ dz = d) ∨
      ∃ uy dy n c, (y, uy, dy) ∈ rpd s f x u d ∧ s.obj y = some (.key n) ∧ (c, z) ∈ live n.ks ∧
        dz = dy + 1
  | 0, x, u, d, z, y, dz, h => by
    simp only [rpd, List.mem_singleton, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1, h.2.1.symm, h.2.2⟩
  | f + 1, x, u, d, z, y, dz, h => by
    simp only [rpd, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      exact Or.inl ⟨h.1, h.2.1.symm, h.2.2⟩
    · right
      cases hx : s.obj x with
      | none => rw [hx] at h; cases h
      | some o =>
        cases o with
        | val v => rw [hx] at h; cases h
        | key n =>
          rw [hx] at h
          obtain ⟨⟨c, w⟩, hcw, hz⟩ := List.mem_flatMap.mp h
          rcases rpd_parent s f w (some x) (d + 1) z y dz hz with ⟨rfl, hu, rfl⟩ | ⟨uy, dy, m, c', h1, h2, h3, h4⟩
          · cases hu
            exact ⟨u, d, n, c, rpd_head s (f + 1) _ u d, hx, hcw, rfl⟩
          · refine ⟨uy, dy, m, c', ?_, h2, h3, h4⟩
            simp only [rpd, List.mem_cons, hx]
            exact Or.inr (List.mem_flatMap.mpr ⟨(c, w), hcw, h1⟩)

/-! ## The tree's context -/

/-- What the proof uses of a state PE keeps: the space root r, sound, shaped
as PE's trees, and TREE. -/
structure TCtx (cf : Cfg) (s : Tree) (r : NodeId) : Prop where
  root : s.root = some r
  good : Good s r 0 none
  shaped : Shaped cf s 0 (htIn cf s r) r
  tree : (reach s).Nodup

theorem tctx_of_inv {t : Time} {tp : Top} {next : NodeId} (hI : Inv cf t s tp next) :
    ∃ r, TCtx cf s r := by
  obtain ⟨r, hr, hsh⟩ := hI.shaped
  exact ⟨r, hr, good_of_invOk hr hI.inv, hsh, hI.tree⟩

/-- TREE's walk from the space root with parents and depths. -/
def RPD (s : Tree) (r : NodeId) : List (NodeId × Option NodeId × Nat) := rpd s (s.fuel r) r none 0

theorem RPD_map {r : NodeId} (T : TCtx cf s r) : (RPD s r).map (·.1) = reach s := by
  rw [RPD, rpd_map, reach_eq_R T.root]; rfl

/-- The parent and depth of node y, if it is a node of the tree. -/
def pdOf (s : Tree) (r : NodeId) (y : NodeId) : Option (Option NodeId × Nat) :=
  ((RPD s r).find? (·.1 == y)).map (·.2)

theorem pdOf_eq {r : NodeId} (T : TCtx cf s r) {y : NodeId} {u : Option NodeId} {d : Nat}
    (h : (y, u, d) ∈ RPD s r) : pdOf s r y = some (u, d) := by
  have hnd : ((RPD s r).map (·.1)).Nodup := by rw [RPD_map T]; exact T.tree
  unfold pdOf
  cases hf : (RPD s r).find? (·.1 == y) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact absurd (hf _ h) (by simp)
  | some a =>
    have ha := List.mem_of_find?_eq_some hf
    have hay : a.1 = y := by simpa using List.find?_some hf
    have := List.inj_on_of_nodup_map hnd ha h hay
    subst this
    rfl

theorem pdOf_mem {r : NodeId} {y : NodeId} {p : Option NodeId × Nat} (h : pdOf s r y = some p) :
    (y, p) ∈ RPD s r := by
  unfold pdOf at h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hay : a.1 = y := by simpa using List.find?_some ha
  have := List.mem_of_find?_eq_some ha
  rw [← hay]
  exact this

/-- Node y is a segment leaf. -/
def lfOf (s : Tree) (y : NodeId) : Bool :=
  match DNB.getKey s y with
  | some n => n.leaf
  | none => false

/-- The parents, depths, kinds and heights of the tree's nodes, as Java's
records hold them. -/
def treeFn (cf : Cfg) (s : Tree) (r : NodeId) : TreeFn where
  up y := match pdOf s r y with
    | some (u, _) => u
    | none => none
  dep y := match pdOf s r y with
    | some (_, d) => d
    | none => 0
  lf y := lfOf s y
  col y := if lfOf s y then 0 else htIn cf s y

theorem treeFn_up_dep {r : NodeId} (T : TCtx cf s r) {y : NodeId} {u : Option NodeId} {d : Nat}
    (h : (y, u, d) ∈ RPD s r) : (treeFn cf s r).up y = u ∧ (treeFn cf s r).dep y = d := by
  simp [treeFn, pdOf_eq T h]

theorem treeFn_root {r : NodeId} (T : TCtx cf s r) :
    (treeFn cf s r).up r = none ∧ (treeFn cf s r).dep r = 0 :=
  treeFn_up_dep T (rpd_head s _ r none 0)

/-- A live child of a listed key node: its parent and depth. -/
theorem treeFn_child {r : NodeId} (T : TCtx cf s r) {x : NodeId} {ux : Option NodeId} {dx : Nat}
    (hx : (x, ux, dx) ∈ RPD s r) {n : KNode} (hn : s.obj x = some (.key n)) {c : Nat} {y : NodeId}
    (hcy : (c, y) ∈ live n.ks) :
    (treeFn cf s r).up y = some x ∧ (treeFn cf s r).dep y = dx + 1 :=
  treeFn_up_dep T (rpd_child (s.fuel r) none 0 T.good (le_refl _) x ux dx hx n hn c y hcy)

theorem lfOf_key {y : NodeId} {n : KNode} (h : s.obj y = some (.key n)) : lfOf s y = n.leaf := by
  simp [lfOf, DNB.getKey, h]

theorem getKey_eq {y : NodeId} {n : KNode} : DNB.getKey s y = some n ↔ s.obj y = some (.key n) := by
  unfold DNB.getKey
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp [h]

/-- An inner node's height is its children's and one. -/
theorem shaped_kid_ht {g e : Nat} {x : NodeId} {n : KNode} (hsh : Shaped cf s g e x)
    (hobj : s.obj x = some (.key n)) (hl : n.leaf = false) {c : Nat} {z : NodeId}
    (hcz : (c, z) ∈ live n.ks) : htIn cf s x = htIn cf s z + 1 := by
  have hx := htIn_of_shaped hsh
  cases hsh with
  | leaf hobj' hleaf _ _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    rw [hl] at hleaf; cases hleaf
  | inner hobj' _ _ _ _ _ hk =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    rw [hx, htIn_of_shaped (hk c z hcz)]

/-- The key nodes of the tree are sound and shaped at their height. -/
theorem tree_shaped {r : NodeId} (T : TCtx cf s r) {y : NodeId} (hy : y ∈ reach s) {m : KNode}
    (hm : s.obj y = some (.key m)) : ∃ g lo hi, Good s y lo hi ∧ Shaped cf s g (htIn cf s y) y := by
  obtain ⟨n, hn⟩ := good_obj T.good
  rw [reach_eq_R T.root] at hy
  exact R_shaped_all n.level hn (le_refl _) T.good T.shaped y hy m hm

/-- **Heights**: a segment leaf's is 0 (`col`), an inner node's its child's and
one, for the tree's nodes. -/
theorem treeFn_hcl {r : NodeId} (y : NodeId) (h : (treeFn cf s r).lf y = true) :
    (treeFn cf s r).col y = 0 := by
  simp only [treeFn] at h ⊢; simp [h]

theorem treeFn_hci {r : NodeId} (T : TCtx cf s r) (y b : NodeId) (hu : (treeFn cf s r).up b = some y)
    (hl : (treeFn cf s r).lf y = false) : (treeFn cf s r).col y = (treeFn cf s r).col b + 1 := by
  have hp : ∃ d, pdOf s r b = some (some y, d) := by
    simp only [treeFn] at hu
    cases h : pdOf s r b with
    | none => rw [h] at hu; cases hu
    | some p => rw [h] at hu; exact ⟨p.2, by rw [← hu]⟩
  obtain ⟨d, hd⟩ := hp
  have hmem := pdOf_mem hd
  rcases rpd_parent s _ r none 0 b y d hmem with ⟨_, hc, _⟩ | ⟨uy, dy, n, c, h1, h2, h3, _⟩
  · cases hc
  · have hyr : y ∈ reach s := by rw [← RPD_map T]; exact List.mem_map_of_mem h1
    obtain ⟨g, lo, hi, _, hsh⟩ := tree_shaped T hyr h2
    have hnl : n.leaf = false := by
      have : lfOf s y = false := hl
      rwa [lfOf_key h2] at this
    have hbs := shaped_kid_inner hsh h2 hnl h3
    have hht := shaped_kid_ht hsh h2 hnl h3
    simp only [treeFn, lfOf_key h2, hnl, Bool.false_eq_true, ite_false]
    rw [hht]
    obtain ⟨mb, hmb, _, hlb, _, _⟩ := shaped_obj hbs
    rw [lfOf_key hmb]
    by_cases hb : mb.leaf = true
    · simp only [hb, ite_true]
      have : htIn cf s b = 0 := by
        have := htIn_of_shaped hbs
        rw [hb] at hlb
        have : htIn cf s b == 0 := hlb.symm
        simpa using this
      rw [this]
    · simp [hb]

/-! ## One step of a key's walk -/

/-- One step of key `key`'s walk from node p.1 at segment p.2: in an inner
node the child `searchLte` finds, in a segment leaf before the key's last
segment the next segment's root `searchEq` finds; none at a value, at the
leaf of the key's last segment, or where the search finds no key node. -/
def nxt (s : Tree) (key : Key) (p : NodeId × Nat) : Option (NodeId × Nat) :=
  match DNB.getKey s p.1 with
  | none => none
  | some n =>
    if n.leaf then
      if p.2 + 1 < key.length then
        match searchEq n.ks (key[p.2]?.getD 0) with
        | some y => if (DNB.getKey s y).isSome then some (y, p.2 + 1) else none
        | none => none
      else none
    else
      match searchLte n.ks (.at (key[p.2]?.getD 0)) with
      | some (_, y) => if (DNB.getKey s y).isSome then some (y, p.2) else none
      | none => none

/-- Each node of the list the step from the one before. -/
def NChain (s : Tree) (key : Key) : List (NodeId × Nat) → Prop
  | [] => True
  | [_] => True
  | a :: b :: L => nxt s key a = some b ∧ NChain s key (b :: L)

theorem nchain_append (s : Tree) (key : Key) : ∀ (A B : List (NodeId × Nat)), NChain s key A →
    NChain s key B → (∀ a b, A.getLast? = some a → B.head? = some b → nxt s key a = some b) →
    NChain s key (A ++ B)
  | [], B, _, hB, _ => hB
  | [a], [], _, _, _ => trivial
  | [a], b :: B, _, hB, h => ⟨h a b rfl rfl, hB⟩
  | a :: a' :: A, B, hA, hB, h => by
    refine ⟨hA.1, ?_⟩
    exact nchain_append s key (a' :: A) B hA.2 hB (fun x y hx hy => h x y (by
      rw [List.getLast?_cons_cons]; exact hx) hy)

/-- A node of a key's walk: sound, shaped as PE's trees at its segment. -/
def NodeP (cf : Cfg) (s : Tree) (p : NodeId × Nat) : Prop :=
  ∃ lo hi, Good s p.1 lo hi ∧ Shaped cf s p.2 (htIn cf s p.1) p.1

theorem good_wf {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) : klongsWf n.ks = true := by
  cases hg with
  | mk _ _ _ n' hobj' hwf _ _ _ _ _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    exact hwf

theorem searchLte_mem {ks : List Klong} {p : Pos} {c : Nat} {y : NodeId}
    (h : searchLte ks p = some (c, y)) : (c, y) ∈ live ks := by
  rw [searchLte_spec] at h
  exact (List.mem_filter.mp (List.mem_of_getLast? h)).1

/-- **A step goes to a live child**, sound and shaped at its segment: the same
in an inner node, the next in a segment leaf. -/
theorem nxt_some {key : Key} {x : NodeId} {g : Nat} (hp : NodeP cf s (x, g)) {y : NodeId} {g' : Nat}
    (h : nxt s key (x, g) = some (y, g')) :
    ∃ n c, s.obj x = some (.key n) ∧ (c, y) ∈ live n.ks ∧ NodeP cf s (y, g') ∧
      (n.leaf = false → g' = g ∧ searchLte n.ks (.at (key[g]?.getD 0)) = some (c, y)) ∧
      (n.leaf = true → g' = g + 1 ∧ g + 1 < key.length ∧ searchEq n.ks (key[g]?.getD 0) = some y) := by
  obtain ⟨lo, hi, hg, hsh⟩ := hp
  obtain ⟨n, hn⟩ := good_obj hg
  have hk : DNB.getKey s x = some n := getKey_eq.mpr hn
  unfold nxt at h
  simp only [hk] at h
  by_cases hl : n.leaf = true
  · simp only [hl, ite_true] at h
    by_cases hlt : g + 1 < key.length
    · simp only [hlt, ite_true] at h
      cases hq : searchEq n.ks (key[g]?.getD 0) with
      | none => rw [hq] at h; cases h
      | some z =>
        rw [hq] at h
        simp only at h
        split at h
        · rename_i hz
          cases h
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hz
          rw [getKey_eq] at hm
          have hlk : (live n.ks).lookup (key[g]?.getD 0) = some y := by
            rw [← searchEq_spec n.ks (good_wf hg hn)]; exact hq
          have hmem : ((key[g]?.getD 0), y) ∈ live n.ks := (lookup_iff_mem (live_sorted n.ks) _ _).mp hlk
          have hlong : isLong (key[g]?.getD 0) = true := by
            by_contra hc
            obtain ⟨v, hv⟩ := good_val hg hn hl hmem (by simpa using hc)
            rw [hv] at hm; cases hm
          rcases good_kids hg hn _ y hmem with ⟨m', hm', _, lo', hi', hgy⟩ | ⟨v, hv⟩
          · refine ⟨n, _, hn, hmem, ⟨lo', hi', hgy, shaped_kid_leaf hsh hn hl hmem hlong⟩, ?_, ?_⟩
            · intro h'; rw [hl] at h'; cases h'
            · intro _; exact ⟨rfl, hlt, hq⟩
          · rw [hv] at hm; cases hm
        · cases h
    · simp only [hlt, ite_false] at h; cases h
  · simp only [hl, Bool.false_eq_true, ite_false] at h
    cases hq : searchLte n.ks (.at (key[g]?.getD 0)) with
    | none => rw [hq] at h; cases h
    | some cz =>
      obtain ⟨c, z⟩ := cz
      rw [hq] at h
      simp only at h
      split at h
      · rename_i hz
        cases h
        have hmem := searchLte_mem hq
        have hl' : n.leaf = false := by simpa using hl
        rcases good_kids hg hn c y hmem with ⟨m', hm', _, lo', hi', hgy⟩ | ⟨v, hv⟩
        · refine ⟨n, c, hn, hmem, ⟨lo', hi', hgy, shaped_kid_inner hsh hn hl' hmem⟩, ?_, ?_⟩
          · intro _; exact ⟨rfl, hq⟩
          · intro h'; rw [hl'] at h'; cases h'
        · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hz
          rw [getKey_eq, hv] at hm; cases hm
      · cases h

theorem shaped_head {g e : Nat} {x : NodeId} {n : KNode} (hsh : Shaped cf s g e x)
    (hn : s.obj x = some (.key n)) (hl : n.leaf = false) : (live n.ks).head?.map (·.1) = some 0 := by
  cases hsh with
  | leaf hobj' hleaf _ _ _ =>
    rw [hn] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    rw [hl] at hleaf; cases hleaf
  | inner hobj' _ _ _ _ hh _ =>
    rw [hn] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    exact hh

/-- An inner node of a key's walk always has a next step, at the same segment. -/
theorem nxt_inner {key : Key} {x : NodeId} {g : Nat} (hp : NodeP cf s (x, g)) {n : KNode}
    (hn : s.obj x = some (.key n)) (hl : n.leaf = false) : ∃ y, nxt s key (x, g) = some (y, g) := by
  obtain ⟨lo, hi, hg, hsh⟩ := hp
  have hk : DNB.getKey s x = some n := getKey_eq.mpr hn
  have hhead : (live n.ks).head?.map (·.1) = some 0 := shaped_head hsh hn hl
  obtain ⟨e0, hne⟩ : ∃ e0, (live n.ks).head? = some e0 := by
    cases h : (live n.ks).head? with
    | none => rw [h] at hhead; cases hhead
    | some e0 => exact ⟨e0, rfl⟩
  have he0 : e0.1 = 0 := by rw [hne] at hhead; simpa using hhead
  have hfne : ((live n.ks).filter (fun cy => !(Pos.at (key[g]?.getD 0)).below cy.1)) ≠ [] := by
    intro h
    have hm : e0 ∈ (live n.ks).filter (fun cy => !(Pos.at (key[g]?.getD 0)).below cy.1) := by
      rw [List.mem_filter]
      refine ⟨List.mem_of_head? hne, ?_⟩
      simp [Pos.below, he0]
    rw [h] at hm; cases hm
  obtain ⟨cy, hcy⟩ : ∃ cy, searchLte n.ks (.at (key[g]?.getD 0)) = some cy := by
    rw [searchLte_spec]
    cases h : ((live n.ks).filter (fun cy => !(Pos.at (key[g]?.getD 0)).below cy.1)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hfne
    | some cy => exact ⟨cy, rfl⟩
  obtain ⟨c, y⟩ := cy
  have hmem := searchLte_mem hcy
  obtain ⟨m, hm, _, _⟩ := good_kids hg hn c y hmem |>.resolve_right (by
    rintro ⟨v, hv⟩
    cases hg with
    | mk _ _ _ n' hobj' _ _ _ _ hkey _ _ =>
      rw [hn] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      obtain ⟨m, hm, _⟩ := hkey c y hmem (fun h => by rw [hl] at h; cases h)
      rw [hv] at hm; cases hm)
  refine ⟨y, ?_⟩
  unfold nxt
  simp only [hk, hl, Bool.false_eq_true, ite_false, hcy, getKey_eq.mpr hm, Option.isSome_some, ite_true]

theorem nodeP_key {x : NodeId} {g : Nat} (hp : NodeP cf s (x, g)) : ∃ n, s.obj x = some (.key n) := by
  obtain ⟨lo, hi, hg, _⟩ := hp
  exact good_obj hg

/-- **The descent**: `descP` from x in segment i's tree is the chain of steps
to a segment leaf, each node sound and shaped. -/
theorem descP_chain {key : Key} {i c : Nat} (hc : key[i]? = some c) :
    ∀ (f : Nat) (x : NodeId), NodeP cf s (x, i) → s.fuel x ≤ f →
      NChain s key ((x, i) :: (descP s c f x).1.map (·, i)) ∧
      (∀ p ∈ (x, i) :: (descP s c f x).1.map (·, i), NodeP cf s p) ∧
      lfOf s (descP s c f x).2 = true
  | 0, x, hp, hf => by
    obtain ⟨n, hn⟩ := nodeP_key hp
    simp [Tree.fuel, hn] at hf
  | f + 1, x, hp, hf => by
    obtain ⟨n, hn⟩ := nodeP_key hp
    have hk : DNB.getKey s x = some n := getKey_eq.mpr hn
    by_cases hl : n.leaf = true
    · have hd : descP s c (f + 1) x = ([], x) := by simp [descP, hk, hl]
      rw [hd]
      refine ⟨trivial, ?_, by rw [lfOf_key hn, hl]⟩
      intro p hp'
      simp only [List.map_nil, List.mem_singleton] at hp'
      rw [hp']; exact hp
    · have hl' : n.leaf = false := by simpa using hl
      obtain ⟨y, hy⟩ := nxt_inner (key := key) hp hn hl'
      obtain ⟨n', c', hn', hmem, hpy, hin, _⟩ := nxt_some hp hy
      rw [hn] at hn'
      obtain rfl : n = n' := by injection hn' with h1; injection h1
      obtain ⟨_, hsl⟩ := hin hl'
      rw [hc, Option.getD_some] at hsl
      obtain ⟨ny, hny⟩ := nodeP_key hpy
      have hd : descP s c (f + 1) x = (y :: (descP s c f y).1, (descP s c f y).2) := by
        simp [descP, hk, hl', hsl, getKey_eq.mpr hny]
      have hfy : s.fuel y ≤ f := by
        obtain ⟨lo, hi, hg, _⟩ := hp
        rcases good_kids hg hn c' y hmem with ⟨m, hm, hlt, _⟩ | ⟨v, hv⟩
        · simp [Tree.fuel, hn] at hf; simp [Tree.fuel, hm]; omega
        · rw [hv] at hny; cases hny
      obtain ⟨h1, h2, h3⟩ := descP_chain hc f y hpy hfy
      rw [hd]
      refine ⟨⟨hy, h1⟩, ?_, h3⟩
      intro p hp'
      simp only [List.map_cons, List.mem_cons] at hp'
      rcases hp' with rfl | hp'
      · exact hp
      · exact h2 p (by simp only [List.mem_cons]; exact hp')

/-- How a key's walk that stops at p ends. -/
def kindOf (s : Tree) (key : Key) (p : NodeId × Nat) : WEnd :=
  if p.2 + 1 = key.length then .last else
    match (DNB.getKey s p.1).bind (fun n => searchEq n.ks (key[p.2]?.getD 0)) with
    | none => .fresh
    | some _ => .stop

/-- **A key's walk** (`keyP`) from x at segment i is a chain of steps (from
x, each node sound and shaped at its segment) to a segment leaf where no step
goes on; it ends as `kindOf` says. -/
theorem keyP_chain {key : Key} : ∀ (f i : Nat) (x : NodeId), NodeP cf s (x, i) → i < key.length →
    key.length ≤ f + i →
    ∃ L : List (NodeId × Nat), L.head? = some (x, i) ∧ L.map (·.1) = x :: (keyP s key f i x).1 ∧
      NChain s key L ∧ L.getLast? = some ((keyP s key f i x).2.1, (keyP s key f i x).2.2.1) ∧
      nxt s key ((keyP s key f i x).2.1, (keyP s key f i x).2.2.1) = none ∧
      (∀ p ∈ L, NodeP cf s p) ∧ lfOf s (keyP s key f i x).2.1 = true ∧
      (keyP s key f i x).2.2.2 = kindOf s key ((keyP s key f i x).2.1, (keyP s key f i x).2.2.1)
  | 0, i, x, _, hi, hf => by omega
  | f + 1, i, x, hp, hi, hf => by
    obtain ⟨c, hc⟩ : ∃ c, key[i]? = some c := ⟨key[i], List.getElem?_eq_getElem hi⟩
    obtain ⟨h1, h2, h3⟩ := descP_chain hc (s.fuel x) x hp (le_refl _)
    set d := descP s c (s.fuel x) x with hd
    have hstop : d.2 = d.1.getLastD x := descP_stop s c _ x
    set Ld := (x, i) :: d.1.map (·, i) with hLd
    have hLdl : Ld.getLast? = some (d.2, i) := by
      rw [hLd, hstop]
      cases h : d.1 using List.reverseRecOn with
      | nil => simp
      | append_singleton L a _ =>
        rw [List.map_append, ← List.cons_append, List.getLast?_append]; simp
    have hLdm : Ld.map (·.1) = x :: d.1 := by
      simp only [hLd, List.map_cons, List.map_map]
      congr 1
      conv_rhs => rw [← List.map_id d.1]
      rfl
    have hpd : NodeP cf s (d.2, i) := h2 _ (List.mem_of_getLast? hLdl)
    obtain ⟨nl, hnl⟩ := nodeP_key hpd
    have hkl : DNB.getKey s d.2 = some nl := getKey_eq.mpr hnl
    have hll : nl.leaf = true := by rw [← lfOf_key hnl]; exact h3
    have hci : key[i]?.getD 0 = c := by rw [hc]; rfl
    by_cases hlast : i + 1 = key.length
    · have hk : keyP s key (f + 1) i x = (d.1, d.2, i, .last) := by
        simp only [keyP, hc, hlast, ite_true, hd]
      rw [hk]
      refine ⟨Ld, rfl, hLdm, h1, hLdl, ?_, h2, h3, ?_⟩
      · simp [nxt, hkl, hll, hlast]
      · simp [kindOf, hlast]
    · cases hq : (DNB.getKey s d.2).bind (fun n => searchEq n.ks c) with
      | none =>
        have hk : keyP s key (f + 1) i x = (d.1, d.2, i, .fresh) := by
          simp only [keyP, hc, hlast, ite_false]; rw [← hd, hq]
        rw [hk]
        have hq' : searchEq nl.ks c = none := by simpa [hkl] using hq
        refine ⟨Ld, rfl, hLdm, h1, hLdl, ?_, h2, h3, ?_⟩
        · simp [nxt, hkl, hll, hci, hq']
        · simp [kindOf, hlast, hkl, hci, hq']
      | some y =>
        have hq' : searchEq nl.ks c = some y := by simpa [hkl] using hq
        cases hy : DNB.getKey s y with
        | none =>
          have hk : keyP s key (f + 1) i x = (d.1, d.2, i, .stop) := by
            simp only [keyP, hc, hlast, ite_false]; rw [← hd, hq]; simp [hy]
          rw [hk]
          refine ⟨Ld, rfl, hLdm, h1, hLdl, ?_, h2, h3, ?_⟩
          · simp [nxt, hkl, hll, hci, hq', hy]
          · simp [kindOf, hlast, hkl, hci, hq']
        | some ny =>
          have hk : keyP s key (f + 1) i x =
              (d.1 ++ y :: (keyP s key f (i + 1) y).1, (keyP s key f (i + 1) y).2) := by
            simp only [keyP, hc, hlast, ite_false]; rw [← hd, hq]; simp [hy]
          rw [hk]
          have hlt : i + 1 < key.length := by omega
          have hnx : nxt s key (d.2, i) = some (y, i + 1) := by
            simp [nxt, hkl, hll, hlt, hci, hq', hy]
          obtain ⟨_, _, _, _, hpy, _, _⟩ := nxt_some hpd hnx
          obtain ⟨L', hh', hm', hc', hl', hn', hp'', hlf', hk'⟩ :=
            keyP_chain f (i + 1) y hpy hlt (by omega)
          refine ⟨Ld ++ L', by simp [hLd], ?_, ?_, ?_, hn', ?_, hlf', hk'⟩
          · rw [List.map_append, hLdm, hm']; simp
          · exact nchain_append s key Ld L' h1 hc' (fun a b ha hb => by
              rw [hLdl] at ha; rw [hh'] at hb; cases ha; cases hb; exact hnx)
          · rw [List.getLast?_append, hl']; simp
          · intro p hp'
            rcases List.mem_append.mp hp' with hp' | hp'
            · exact h2 p hp'
            · exact hp'' p hp'

/-! ## The paths of the keys -/

theorem keyWf_ne : ∀ {k : Key}, keyWf k = true → k ≠ []
  | [], h => by simp [keyWf] at h
  | _ :: _, _ => by simp

/-- A key's path from the space root: the chain of steps from (r, 0). -/
structure KeyPath (cf : Cfg) (s : Tree) (r : NodeId) (key : Key) (L : List (NodeId × Nat)) : Prop where
  head : L.head? = some (r, 0)
  map : L.map (·.1) = pathOf s r key
  chain : NChain s key L
  last : L.getLast? = some ((endOf s r key).1, (endOf s r key).2.1)
  stop : nxt s key ((endOf s r key).1, (endOf s r key).2.1) = none
  nodes : ∀ p ∈ L, NodeP cf s p
  leaf : lfOf s (endOf s r key).1 = true
  kind : (endOf s r key).2.2 = kindOf s key ((endOf s r key).1, (endOf s r key).2.1)

theorem keyPath_of {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    ∃ L, KeyPath cf s r key L := by
  have hpos : 0 < key.length := List.length_pos_iff.mpr (keyWf_ne hwf)
  obtain ⟨L, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    keyP_chain (cf := cf) (key := key) (key.length + 1) 0 r ⟨0, none, T.good, T.shaped⟩ hpos (by omega)
  exact ⟨L, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- The links of a chain from a listed node. -/
theorem links_of_chain {r : NodeId} (T : TCtx cf s r) {key : Key} :
    ∀ (L : List (NodeId × Nat)) (x : NodeId) (g : Nat) (ux : Option NodeId) (dx : Nat),
    NChain s key ((x, g) :: L) → (∀ p ∈ (x, g) :: L, NodeP cf s p) → (x, ux, dx) ∈ RPD s r →
    Links s (treeFn cf s r) x (L.map (·.1))
  | [], _, _, _, _, _, _, _ => trivial
  | (y, g') :: L, x, g, ux, dx, hch, hn, hx => by
    obtain ⟨n, c, hxn, hcy, hpy, _, _⟩ := nxt_some (hn (x, g) List.mem_cons_self) hch.1
    obtain ⟨hu, hd⟩ := treeFn_child T hx hxn hcy
    obtain ⟨m, hm⟩ := nodeP_key hpy
    have hy : (y, some x, dx + 1) ∈ RPD s r :=
      rpd_child (s.fuel r) none 0 T.good (le_refl _) x ux dx hx n hxn c y hcy
    refine ⟨⟨m, getKey_eq.mpr hm, lfOf_key hm⟩, hu, ?_, ?_⟩
    · rw [hd, (treeFn_up_dep T hx).2]
    · exact links_of_chain T L y g' (some x) (dx + 1) hch.2
        (fun p hp => hn p (List.mem_cons_of_mem _ hp)) hy

/-- **Every key's path is as Java's records need** (`PathOk`). -/
theorem pathOk_of {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    PathOk s r (treeFn cf s r) key := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  refine ⟨?_, fun _ => hL.leaf⟩
  obtain ⟨p, L', rfl⟩ : ∃ p L', L = p :: L' := by
    cases h : L with
    | nil => have := hL.head; rw [h] at this; cases this
    | cons p L' => exact ⟨p, L', rfl⟩
  have hp : p = (r, 0) := by have := hL.head; simpa using this
  subst hp
  have hm := hL.map
  simp only [List.map_cons, pathOf, List.cons.injEq, true_and] at hm
  rw [← hm]
  exact links_of_chain T L' r 0 none 0 hL.chain hL.nodes (rpd_head s _ r none 0)

/-! ## The segment of a node -/

/-- The segment of a key node, from its level. -/
def segY (cf : Cfg) (s : Tree) (y : NodeId) : Nat :=
  match s.obj y with
  | some (.key n) => cf.segOf n.level
  | _ => 0

theorem segY_of_shaped {g h : Nat} {y : NodeId} (hsh : Shaped cf s g h y) : segY cf s y = g := by
  obtain ⟨n, hobj, hlev, _, hg, hH⟩ := shaped_obj hsh
  simp only [segY, hobj, hlev, Cfg.segOf, Cfg.lev]
  have e : 1 + (cf.G - g) * (cf.H + 1) + h - 1 = h + (cf.G - g) * (cf.H + 1) := by omega
  rw [e, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (by omega)]
  omega

/-! ## Chains -/

theorem nchain_next (s : Tree) (key : Key) : ∀ (L : List (NodeId × Nat)) (a b l : NodeId × Nat),
    NChain s key L → a ∈ L → nxt s key a = some b → L.getLast? = some l → nxt s key l = none → b ∈ L
  | [], _, _, _, _, ha, _, _, _ => by cases ha
  | [c], a, b, l, _, ha, hab, hl, hn => by
    simp only [List.mem_singleton] at ha
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst ha; subst hl
    rw [hn] at hab; cases hab
  | c :: d :: L, a, b, l, hch, ha, hab, hl, hn => by
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hch.1] at hab; cases hab; exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (nchain_next s key (d :: L) a b l hch.2 ha hab
        (by rw [List.getLast?_cons_cons] at hl; exact hl) hn)

theorem nchain_pred (s : Tree) (key : Key) : ∀ (L : List (NodeId × Nat)) (b : NodeId × Nat),
    NChain s key L → b ∈ L → L.head? ≠ some b → ∃ a ∈ L, nxt s key a = some b
  | [], _, _, hb, _ => by cases hb
  | [c], b, _, hb, hh => by
    simp only [List.mem_singleton] at hb; subst hb; simp at hh
  | c :: d :: L, b, hch, hb, hh => by
    rcases List.mem_cons.mp hb with rfl | hb
    · simp at hh
    · by_cases hbd : b = d
      · subst hbd; exact ⟨c, List.mem_cons_self, hch.1⟩
      · obtain ⟨a, ha, hab⟩ := nchain_pred s key (d :: L) b hch.2 hb (by simpa using Ne.symm hbd)
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- A chain's nodes are distinct (their depths increase). -/
theorem keyPath_nodup {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true)
    {L : List (NodeId × Nat)} (hL : KeyPath cf s r key L) : (L.map (·.1)).Nodup := by
  rw [hL.map]
  exact (links_dep r _ (pathOk_of T hwf).links).2.1

/-- **The pair of a node on a key's path**: its segment is `segY`. -/
theorem keyPath_seg {r : NodeId} {key : Key} {L : List (NodeId × Nat)} (hL : KeyPath cf s r key L) {y : NodeId} (hy : y ∈ pathOf s r key) :
    (y, segY cf s y) ∈ L := by
  rw [← hL.map] at hy
  obtain ⟨⟨y', g⟩, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨_, _, _, hsh⟩ := hL.nodes _ hp
  rw [segY_of_shaped hsh]
  exact hp

/-- The nodes of the tree on the path are in the walk with parents. -/
theorem path_rpd {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    (hy : y ∈ pathOf s r key) : ∃ uy dy, (y, uy, dy) ∈ RPD s r := by
  have hl := (pathOk_of T hwf).links
  simp only [pathOf, List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact ⟨none, 0, rpd_head s _ y none 0⟩
  · -- a node of the path has a parent listed, so it is listed
    obtain ⟨u, hu, h1, h2⟩ := links_up _ _ hl y hy
    simp only [treeFn] at h1
    cases hp : pdOf s r y with
    | none => rw [hp] at h1; cases h1
    | some p => exact ⟨p.1, p.2, pdOf_mem hp⟩

/-- **The next node of a path**: for a key that passes y (key node n, at its
segment g), a live child z of y is on the path exactly if the step from
(y, g) goes to z. -/
theorem path_child {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true)
    {y : NodeId} (hy : y ∈ pathOf s r key) {n : KNode} (hn : s.obj y = some (.key n)) {c : Nat}
    {z : NodeId} (hcz : (c, z) ∈ live n.ks) :
    z ∈ pathOf s r key ↔ ∃ g', nxt s key (y, segY cf s y) = some (z, g') := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  have hyL := keyPath_seg hL hy
  obtain ⟨uy, dy, hyr⟩ := path_rpd T hwf hy
  have hzu : (treeFn cf s r).up z = some y := (treeFn_child T hyr hn hcz).1
  constructor
  · intro hz
    rw [← hL.map] at hz
    obtain ⟨⟨z', g'⟩, hzp, rfl⟩ := List.mem_map.mp hz
    have hne : L.head? ≠ some (z', g') := by
      rw [hL.head]
      intro h
      cases h
      rw [(treeFn_root T).1] at hzu; cases hzu
    obtain ⟨⟨x, gx⟩, hxL, hxz⟩ := nchain_pred s key L _ hL.chain hzp hne
    obtain ⟨nx, cx, hxn, hcx, _, _, _⟩ := nxt_some (hL.nodes _ hxL) hxz
    have hxr : x ∈ pathOf s r key := by rw [← hL.map]; exact List.mem_map_of_mem hxL
    obtain ⟨ux, dx, hxr'⟩ := path_rpd T hwf hxr
    have hzx := (treeFn_child T hxr' hxn hcx).1
    rw [hzu] at hzx
    cases hzx
    have hseg : gx = segY cf s y := by
      obtain ⟨_, _, _, hsh⟩ := hL.nodes _ hxL
      exact (segY_of_shaped hsh).symm
    subst hseg
    exact ⟨g', hxz⟩
  · rintro ⟨g', h⟩
    rw [← hL.map]
    exact List.mem_map_of_mem (nchain_next s key L _ _ _ hL.chain hyL h hL.last hL.stop)

/-- **The end of a path**: a key that passes y ends there exactly if no step
goes on from (y, g). -/
theorem path_end {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true)
    {y : NodeId} (hy : y ∈ pathOf s r key) :
    (endOf s r key).1 = y ↔ nxt s key (y, segY cf s y) = none := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  have hyL := keyPath_seg hL hy
  have hnd := keyPath_nodup T hwf hL
  have hlast := List.mem_of_getLast? hL.last
  constructor
  · intro h
    have := List.inj_on_of_nodup_map hnd hlast hyL (by simp [h])
    rw [← this]
    exact hL.stop
  · intro h
    -- the last pair: if it were not (y, g), the step from (y, g) would go on
    by_contra hne
    obtain ⟨l, hl⟩ : ∃ l, L.getLast? = some l := ⟨_, hL.last⟩
    -- (y, g) is not last, so its successor exists in the chain
    have key_lemma : ∀ (M : List (NodeId × Nat)) (a : NodeId × Nat), NChain s key M → a ∈ M →
        M.getLast? ≠ some a → (nxt s key a).isSome := by
      intro M
      induction M with
      | nil => intro a _ ha; cases ha
      | cons c M ih =>
        intro a hch ha hla
        cases M with
        | nil =>
          simp only [List.mem_singleton] at ha; subst ha
          simp at hla
        | cons d M' =>
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hch.1]; rfl
          · exact ih a hch.2 ha (by rw [List.getLast?_cons_cons] at hla; exact hla)
    have := key_lemma L _ hL.chain hyL (by
      rw [hL.last]
      intro he
      apply hne
      have h1 := Option.some.inj he
      exact (Prod.mk.inj h1).1)
    rw [h] at this; cases this

end Contract.PE
