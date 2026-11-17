/-
The contract package (bergdb 030-10): `handleFullWith` when it does a time
split (Java's `Dag.timeSplit` and `timeSplitInPlace`): the full node x is
replaced by its last version with the klongs set, a new node y that the
parent's klong then names, or that becomes the space root; a node that the
transaction made becomes its last version in place. Also a node that is full
by its dead klongs only (`compact`).

The proof: from `CasPre`, the state w itself (x without the klongs) has the
frame and BalancedOK (section 3; the frame's form of x is read back from that
of x with the klongs added); the key access path goes down one level at each
step, so x is not above its own depth, and its nodes are reached in the "if"
tree A (section 4). Then the three cases, each by a rule of TreeRules.lean
with A and the tree B after the step: in place (`Sound.inPlace`); at the space
root (`Sound.timeSplitRoot`, `newSuperRoot`); below it (`Sound.timeSplit`
gives `CasPre` for the parent, and after the parent's step x, left as it was
and not reached, is cut back to its node of before, `toPrev`).
-/
import Contract.Proof.WriterCascadeDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. Helpers -/

theorem ts_wp_bind_ok {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β} {c : Ctx}
    {w w' : MW} {a : α} {post : β → MW → Prop} (h : f c w = .ok (a, w')) :
    WP (f >>= g) c w post ↔ WP (g a) c w' post := by
  rw [wp_bind]
  constructor
  · intro hw
    exact hw a w' h
  · intro hw r v hr
    rw [h] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hw

theorem ts_wp_ok {α : Type} {f : SIS.Tree.M α} {c : Ctx} {w w' : MW} {a : α}
    {post : α → MW → Prop} (h : f c w = .ok (a, w')) : WP f c w post ↔ post a w' := by
  constructor
  · intro hw
    exact hw a w' h
  · intro hp r v hr
    rw [h] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact hp

theorem ts_liveWith_mem (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases ts_liveWith_mem del r _ a h with h1 | ⟨i', h1⟩
    · cases k with
      | time t => exact Or.inl h1
      | del b => exact Or.inl h1
      | key c y =>
        simp only at h1
        split at h1
        · exact Or.inl h1
        · rcases mem_insertCv h1 with h2 | h2
          · right
            refine ⟨i, ?_⟩
            rw [h2]
            exact List.mem_cons_self
          · exact Or.inl h2
    · exact Or.inr ⟨i', List.mem_cons_of_mem _ h1⟩

/-- A live klong is a key klong of the node. -/
theorem ts_live_mem_key {ks : List Klong} {c : Nat} {y : NodeId} (h : (c, y) ∈ live ks) :
    Klong.key c y ∈ ks := by
  unfold live liveWith at h
  rcases ts_liveWith_mem (lastBitmap ks) ks.zipIdx [] (c, y) h with h1 | ⟨i, h1⟩
  · simp at h1
  · obtain ⟨hlt, heq⟩ := List.mem_zipIdx' h1
    have h2 : Klong.key c y = ks[i] := heq
    rw [h2]
    exact List.getElem_mem hlt

theorem ts_nodeOk_iff {b : Nat} {T : Tree} {m : KNode} :
    nodeOk ⟨b⟩ T m = true ↔ m.ks.length ≤ b ∧ klongsWf m.ks = true ∧
      ∀ c y, Klong.key c y ∈ m.ks → (T.obj y).isSome = true := by
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun c y hk => h3 _ hk⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun k hk => ?_⟩
    cases k with
    | key c y => exact h3 c y hk
    | _ => rfl

theorem ts_key_mem_ksOf {n : MNode} {c : Nat} {y : NodeId} (h : SIS.Tree.Klong.key c y ∈ n.ks) :
    Klong.key c y ∈ ksOf n :=
  List.mem_map_of_mem (f := kOf) h

theorem ts_time_mem_ksOf {n : MNode} {t : Time} (h : SIS.Tree.Klong.time t ∈ n.ks) :
    Klong.time t ∈ ksOf n :=
  List.mem_map_of_mem (f := kOf) h

/-- A live child of a node reached is reached. -/
theorem ts_reach_kid {T : Tree} {r u y : NodeId} {lo : Nat} {hi : Option Nat} (hG : Good T r lo hi)
    (hu : u ∈ reachAt T (T.fuel r) r) {m : KNode} (hm : T.obj u = some (.key m)) {c : Nat}
    (hc : (c, y) ∈ live m.ks) : y ∈ reachAt T (T.fuel r) r :=
  hG.tr_closed hu (tc_kid hm hc (tc_self T m.level y))

/-- Two trees that differ only at node x, a key node in both with the same
live klongs, reach the same nodes. -/
theorem ts_reachAt_live {A B : Tree} {x : NodeId} {na nb : KNode}
    (hAx : A.obj x = some (.key na)) (hBx : B.obj x = some (.key nb))
    (hl : live nb.ks = live na.ks) (hsame : ∀ z, z ≠ x → B.obj z = A.obj z) :
    ∀ f u, reachAt B f u = reachAt A f u
  | 0, _ => rfl
  | f + 1, u => by
    have ih := ts_reachAt_live hAx hBx hl hsame f
    by_cases hu : u = x
    · subst hu
      rw [tc_key hAx, tc_key hBx, hl]
      simp only [ih]
    · have ho : B.obj u = A.obj u := hsame u hu
      simp only [reachAt, ho, ih]

/-! ## 2. The klongs of a node before klongs were added -/

theorem ts_addAll_late {i : Time} : ∀ (ins : List (Nat × NodeId)) (n : MNode),
    (∃ lt, n.lastTime = some lt ∧ i ≤ lt) →
    ∃ E, ksOf (addAll i n ins) = ksOf n ++ E ∧ ∀ t, Klong.time t ∉ E
  | [], n, _ => ⟨[], by simp [addAll_nil], by simp⟩
  | cy :: ins, n, ⟨lt, hl, hle⟩ => by
    rw [addAll_cons]
    obtain ⟨E, hE, hno⟩ := ts_addAll_late ins _ (add_lastTime n i cy.1 cy.2)
    rcases ksOf_add n i (.key cy.1 cy.2) with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd (h lt hl) (Nat.not_lt.mpr hle)
    · refine ⟨kOf (.key cy.1 cy.2) :: E, by rw [hE, h]; simp, fun t ht => ?_⟩
      rcases List.mem_cons.mp ht with ht | ht
      · simp [kOf] at ht
      · exact hno t ht

theorem ts_addAll_split (i : Time) (ins : List (Nat × NodeId)) (n : MNode) :
    ∃ E, ksOf (addAll i n ins) = ksOf n ++ E ∧
      ((∃ E', E = Klong.time i :: E') ∨
        ((∀ t, Klong.time t ∉ E) ∧ (E = [] ∨ ∃ lt, n.lastTime = some lt ∧ i ≤ lt))) := by
  cases ins with
  | nil => exact ⟨[], by simp [addAll_nil], Or.inr ⟨by simp, Or.inl rfl⟩⟩
  | cons cy ins =>
    rw [addAll_cons]
    obtain ⟨E, hE, hno⟩ := ts_addAll_late (i := i) ins _ (add_lastTime n i cy.1 cy.2)
    rcases ksOf_add n i (.key cy.1 cy.2) with ⟨h, _⟩ | ⟨h, lt, hl, hle⟩
    · exact ⟨Klong.time i :: kOf (.key cy.1 cy.2) :: E, by rw [hE, h]; simp, Or.inl ⟨_, rfl⟩⟩
    · refine ⟨kOf (.key cy.1 cy.2) :: E, by rw [hE, h]; simp, Or.inr ⟨fun t ht => ?_,
        Or.inr ⟨lt, hl, hle⟩⟩⟩
      rcases List.mem_cons.mp ht with ht | ht
      · simp [kOf] at ht
      · exact hno t ht

/-- The frame's form (`add_ext`'s) of a node, from that of the node with key
klongs added at time i. -/
theorem ts_ext_back {n : MNode} {i : Time} {ks0 : List Klong} (ins : List (Nat × NodeId))
    (h0 : ∀ t, Klong.time t ∈ ks0 → t < i)
    (h : ksOf (addAll i n ins) = ks0 ∨
      ∃ more, ksOf (addAll i n ins) = ks0 ++ Klong.time i :: more) :
    ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more := by
  have hni : Klong.time i ∉ ks0 := fun hm => Nat.lt_irrefl _ (h0 i hm)
  obtain ⟨E, hE, hcase⟩ := ts_addAll_split i ins n
  rw [hE] at h
  rcases hcase with ⟨E', rfl⟩ | ⟨hno, hE0⟩
  · rcases h with h | ⟨more, h⟩
    · exact absurd (h ▸ List.mem_append_right _ List.mem_cons_self) hni
    · rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
      · cases a' with
        | nil => exact Or.inl (by simpa using h1.symm)
        | cons k a'' =>
          simp only [List.cons_append, List.cons.injEq] at h2
          exact absurd (h1 ▸ List.mem_append_right _ (h2.1 ▸ List.mem_cons_self)) hni
      · cases c' with
        | nil => exact Or.inl (by simpa using h1)
        | cons k c'' =>
          simp only [List.cons_append, List.cons.injEq] at h2
          exact Or.inr ⟨c'', by rw [h1, ← h2.1]⟩
  · rcases h with h | ⟨more, h⟩
    · rcases hE0 with rfl | ⟨lt, hl, hle⟩
      · exact Or.inl (by simpa using h)
      · have hm : Klong.time lt ∈ ksOf n := lastT_mem (by rw [lastT_ksOf]; exact hl)
        have hm0 : Klong.time lt ∈ ks0 := by rw [← h]; exact List.mem_append_left _ hm
        exact absurd (h0 lt hm0) (Nat.not_lt.mpr hle)
    · rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
      · exact absurd (h2 ▸ List.mem_append_right _ List.mem_cons_self) (hno i)
      · cases c' with
        | nil =>
          rw [List.nil_append] at h2
          exact absurd (by rw [← h2]; exact List.mem_cons_self) (hno i)
        | cons k c'' =>
          simp only [List.cons_append, List.cons.injEq] at h2
          exact Or.inr ⟨c'', by rw [h1, ← h2.1]⟩

/-- Two trees that differ only at node x, a key node in both on one level with
the same live klongs: the walk from any node, with its fuel, is the same. -/
theorem ts_reach_live {A B : Tree} {x : NodeId} {na nb : KNode}
    (hAx : A.obj x = some (.key na)) (hBx : B.obj x = some (.key nb))
    (hl : live nb.ks = live na.ks) (hlev : nb.level = na.level)
    (hsame : ∀ z, z ≠ x → B.obj z = A.obj z) (u : NodeId) :
    reachAt B (B.fuel u) u = reachAt A (A.fuel u) u := by
  have hf : B.fuel u = A.fuel u := by
    by_cases hu : u = x
    · subst hu
      simp [Tree.fuel, hAx, hBx, hlev]
    · simp only [Tree.fuel, hsame u hu]
  rw [hf]
  exact ts_reachAt_live hAx hBx hl hsame _ u

/-! ## 3. The state before the klongs were added -/

theorem ts_treeOf_back (i : Time) (s : Tree) {w : MW} {x : NodeId} {n a : MNode}
    (hx : w.nodes.lookup x = some n) (ht : w.taken.contains x = false) :
    treeOf i s ((w.withNode x a).withNode x n) = treeOf i s w := by
  rw [treeOf_withNode i s n (w := w.withNode x a) ht, treeOf_withNode i s a ht]
  apply prim_tree_ext
  · intro y
    simp only [Tree.set]
    by_cases hy : y = x
    · subst hy
      rw [treeOf_obj_overlay i s hx ht]
      simp only [ite_true]
      rfl
    · simp [hy]
  · rfl

theorem ts_dirtyOf_back {w : MW} {x : NodeId} {n a : MNode} (hx : w.nodes.lookup x = some n) :
    dirtyOf ((w.withNode x a).withNode x n) = dirtyOf w := by
  rw [dirtyOf_withNode (n := a) (lookup_upsert_self _ _ _), dirtyOf_withNode hx]

/-- What `CasPre` gives of the state w itself, before the klongs are added: x
is kept; the map's root, the frame and the top. -/
theorem ts_wfacts {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {depth : Nat} {x : NodeId} {n : MNode} {ins : List (Nat × NodeId)} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPre p i base s tp w depth x n ins C) :
    w.taken.contains x = false ∧ (treeOf i s w).root = some w.top.rootKey ∧
      Frame i s (dirtyOf w) (treeOf i s w) ∧ WTopInv i s tp w.top w.newTop := by
  have htx : w.taken.contains x = false := by
    obtain ⟨c0, hon⟩ := h.on
    obtain ⟨m, -, ht⟩ := h.path.lookup (le_refl _) hon
    exact ht
  have hI := h.hyp
  have hxA : (w.withNode x (addAll i n ins)).nodes.lookup x = some (addAll i n ins) :=
    lookup_upsert_self _ _ _
  have hleaf : n.leaf = (addAll i n ins).leaf := (addAll_leaf i n ins).symm
  refine ⟨htx, ?_, ?_, hI.top⟩
  · exact hI.root
  · have hF := frame_withNode hI.frame hxA htx hleaf (fun n0 hs0 => by
      obtain ⟨-, -, he⟩ := frame_overlay_ext hI.frame hxA htx hs0
      exact ts_ext_back ins (prim_timesBefore (hb.times x n0 hs0)) he)
    rwa [ts_treeOf_back i s h.look htx, ts_dirtyOf_back h.look] at hF

/-- BalancedOK, in B, of a node y with the level, the kind and the live klongs
of node x of A, reached in A: each live klong names a node of A one level
below, a key node of B on the same level (`hlev`). -/
theorem ts_bal_copy {p : MParams} {A B : Tree} {x y : NodeId} {nx ny : KNode}
    (hA : Balanced p A) (hxr : x ∈ reach A) (hAx : A.obj x = some (.key nx))
    (hBy : B.obj y = some (.key ny)) (hlv : ny.level = nx.level) (hlf : ny.leaf = nx.leaf)
    (hl : live ny.ks = live nx.ks)
    (hlev : ∀ z m, A.obj z = some (.key m) → ∃ m', B.obj z = some (.key m') ∧
      m'.level = m.level) :
    ∀ m, B.obj y = some (.key m) → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
      (m.leaf = false → ∀ c y', (c, y') ∈ live m.ks → ∃ m', B.obj y' = some (.key m') ∧
        m'.level + 1 = m.level) := by
  intro m hm
  rw [hBy] at hm
  cases hm
  obtain ⟨h1, h2, h3⟩ := hA x hxr nx hAx
  refine ⟨by rw [hlv]; exact h1, by rw [hlv, hlf]; exact h2, fun hlf' c y' hc => ?_⟩
  rw [hl] at hc
  obtain ⟨m0, hm0, e0⟩ := h3 (by rw [← hlf]; exact hlf') c y' hc
  obtain ⟨m', hm', e'⟩ := hlev y' m0 hm0
  exact ⟨m', hm', by rw [e', e0, hlv]⟩

/-- BalancedOK, in B, of the parent q: its node of A, reached in A, with the
klong (k1, y) set, y a key node of B one level below q. -/
theorem ts_bal_set1 {p : MParams} {A B : Tree} {q y : NodeId} {nq nb : KNode} {k1 : Nat}
    (hA : Balanced p A) (hqr : q ∈ reach A) (hAq : A.obj q = some (.key nq))
    (hBq : B.obj q = some (.key nb)) (hlv : nb.level = nq.level) (hlf : nb.leaf = nq.leaf)
    (hl : live nb.ks = insertCv k1 y (live nq.ks))
    (hy : nq.leaf = false → ∃ m', B.obj y = some (.key m') ∧ m'.level + 1 = nq.level)
    (hlev : ∀ z m, A.obj z = some (.key m) → ∃ m', B.obj z = some (.key m') ∧
      m'.level = m.level) :
    ∀ m, B.obj q = some (.key m) → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
      (m.leaf = false → ∀ c y', (c, y') ∈ live m.ks → ∃ m', B.obj y' = some (.key m') ∧
        m'.level + 1 = m.level) := by
  intro m hm
  rw [hBq] at hm
  cases hm
  obtain ⟨h1, h2, h3⟩ := hA q hqr nq hAq
  refine ⟨by rw [hlv]; exact h1, by rw [hlv, hlf]; exact h2, fun hlf' c y' hc => ?_⟩
  have hl' : nq.leaf = false := by rw [← hlf]; exact hlf'
  rw [hl] at hc
  rcases mem_insertCv hc with e | e
  · simp only [Prod.mk.injEq] at e
    rw [e.2]
    obtain ⟨m', h1', h2'⟩ := hy hl'
    exact ⟨m', h1', by rw [h2', hlv]⟩
  · obtain ⟨m0, hm0, e0⟩ := h3 hl' c y' e
    obtain ⟨m', hm', e'⟩ := hlev y' m0 hm0
    exact ⟨m', hm', by rw [e', e0, hlv]⟩

/-! ## 4. The key access path -/

/-- x is not on the path above its depth (`CasPre.nodup`). -/
theorem ts_off {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {depth : Nat} {x : NodeId} {n : MNode} {ins : List (Nat × NodeId)} {C : List (Key × Nat)}
    (h : CasPre p i base s tp w depth x n ins C) :
    ∀ d c, d < depth → w.path[d]? ≠ some (c, x) := by
  intro d c hd he
  obtain ⟨c0, hon⟩ := h.on
  exact h.nodup d depth c c0 x hd (Nat.le_refl _) he hon

/-- The nodes of the path are reached in a sound tree A that is the map of w
but at x, if x is not on the path above its depth. -/
theorem ts_path_reach {i : Time} {s : Tree} {w : MW} {depth : Nat} {x : NodeId}
    {A : Tree} {lo : Nat} {hi : Option Nat} (hG : Good A w.top.rootKey lo hi)
    (hP : PathOk i s w depth) (hoff : ∀ d c, d < depth → w.path[d]? ≠ some (c, x))
    (hA : ∀ z, z ≠ x → A.obj z = (treeOf i s w).obj z) :
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
    have ih := ts_path_reach hG hP hoff hA d (by omega) c0' u0 e1
    have hne : u0 ≠ x := fun e => hoff d c0' (by omega) (e ▸ e1)
    rw [← hA u0 hne] at e3
    exact ts_reach_kid hG ih e3 e4

/-! ## 5. A node that the transaction made: in place -/

/-- The state after the time split in place: x is the node r, with x's
kind, whose live klongs are those of x with the klongs added. -/
theorem ts_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {depth : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} (h : CasPre p i base s tp w depth x n ins C)
    (hnt : n.firstTime = some i) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    (hxr : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    (T : List String) :
    CasPost p i base s tp w depth x n ins C ()
      (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) := by
  intro _
  obtain ⟨htx, hroot, hF, hT⟩ := ts_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  have hA : treeOf i s (w.withNode x (addAll i n ins)) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hBt : treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [treeOf_withNode i s (w := { w with trail := T }) _ htx]
    rfl
  have hAx : (treeOf i s (w.withNode x (addAll i n ins))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [hA]; simp [Tree.set]
  have hBx : (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [hBt]; simp [Tree.set]
  have hsame : ∀ z, z ≠ x →
      (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z hz
    rw [hA, hBt]
    simp [Tree.set, hz]
  have hxok := hI.sound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hNode : NodeIs (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)) x
      (wLevel s w x) n.leaf (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨_, hBx, rfl, rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => ?_⟩⟩
    · show (ksOf r).length ≤ p.M
      rw [ksOf_length]; exact hrs
    · have := hxp c y (hrk c y hk)
      by_cases hy : y = x
      · rw [hy, hBx]; rfl
      · rw [hsame y hy]; exact this
  have hS := Sound.inPlace hI.sound hAx hNode hsame
  have hfirst := h.books.first x n hx htx
  refine ⟨⟨?_, hS, ?_, hT, ?_, ?_⟩, ⟨rfl, ?_, le_refl _, ?_⟩⟩
  · rw [hBt]; exact hroot
  · refine frame_withNode (w := { w with trail := T }) hF hx htx rfl (fun n0 hs0 => ?_)
    exact absurd hnt (hfirst.mp (by rw [hs0]; rfl))
  · have hRA := reach_of_root hI.root
    have hRB : reach (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)) =
        reach (treeOf i s (w.withNode x (addAll i n ins))) := by
      rw [reach_of_root (show (treeOf i s (MW.withNode { w with trail := T } x
        ⟨n.leaf, r.ks⟩)).root = some w.top.rootKey by rw [hBt]; exact hroot), hRA]
      exact ts_reach_live hAx hBx hrl rfl hsame _
    have hlk : ∀ z m, (treeOf i s (w.withNode x (addAll i n ins))).obj z = some (.key m) →
        ∃ m', (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)).obj z =
          some (.key m') ∧ m'.level = m.level := by
      intro z m hm
      by_cases e : z = x
      · subst e
        rw [hAx] at hm
        cases hm
        exact ⟨_, hBx, rfl⟩
      · exact ⟨m, by rw [hsame z e]; exact hm, rfl⟩
    refine Balanced.of_reach hI.balanced (N := [x]) (fun z hz => Or.inl (hRB ▸ hz))
      (fun z _ hz => hsame z (by simpa using hz)) hlk (fun z hz _ m hm => ?_)
    simp only [List.mem_singleton] at hz
    subst hz
    exact ts_bal_copy hI.balanced (by rw [hRA]; exact hxr) hAx hBx rfl rfl hrl hlk m hm
  · refine putBooks_withNode (w := { w with trail := T })
      (putBooks_congr h.books rfl rfl rfl rfl rfl rfl rfl rfl rfl) hx htx rfl ?_ ?_
    · obtain ⟨rest, hr⟩ := hrf
      obtain ⟨t0, rest0, hn⟩ := h.books.timeFirst x n hx htx
      rw [prim_firstTime_of hn] at hnt
      cases hnt
      show r.ks.head? = n.ks.head?
      rw [hr, hn]
      rfl
    · intro t ht
      exact hrt t (ts_time_mem_ksOf ht)
  · intro y m hy hny
    have hyx : y ≠ x := by
      intro e
      obtain ⟨c0, hon⟩ := h.on
      exact hny depth c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert w.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact hy
  · intro z hz
    left
    unfold reachOf at hz ⊢
    rw [ts_reach_live hAx hBx hrl rfl hsame] at hz
    exact hz

/-! ## 6. A node from before the transaction at the space root -/

theorem ts_mem_toPrev {n : MNode} {t : Time} {k : MKlong} (h : k ∈ (n.toPrev t).ks) : k ∈ n.ks :=
  (List.takeWhile_sublist _).subset h

theorem ts_toPrev_head {n : MNode} {t t0 : Time} {rest : List MKlong}
    (hn : n.ks = .time t0 :: rest) (ht : t0 ≤ t) : (n.toPrev t).ks.head? = n.ks.head? := by
  show (SIS.Tree.prefixAt n.ks t).head? = n.ks.head?
  rw [hn]
  simp [SIS.Tree.prefixAt, ht]

/-- The facts of x, a node from before the transaction, for its cut back. -/
theorem ts_old {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW} {x : NodeId}
    {n : MNode} (hk : PutBooks p i base s w) (hx : w.nodes.lookup x = some n)
    (ht : w.taken.contains x = false) (hnt : n.firstTime ≠ some i) :
    (n.toPrev (i - 1)).ks.head? = n.ks.head? ∧
      ∀ t, SIS.Tree.Klong.time t ∈ (n.toPrev (i - 1)).ks → t ≤ i := by
  obtain ⟨t0, rest0, hn⟩ := hk.timeFirst x n hx ht
  have ht0 : t0 ≤ i := hk.times x n hx t0 (by rw [hn]; exact List.mem_cons_self)
  have hne : t0 ≠ i := fun e => hnt (by rw [prim_firstTime_of hn, e])
  refine ⟨ts_toPrev_head hn (by omega), fun t htm => hk.times x n hx t (ts_mem_toPrev htm)⟩

/-- The frame's form of x cut back: its node of s. -/
theorem ts_toPrev_ext {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW} {x : NodeId}
    {n : MNode} (hb : Books i base s tp) (hF : Frame i s (dirtyOf w) (treeOf i s w))
    (hx : w.nodes.lookup x = some n) (ht : w.taken.contains x = false) (n0 : KNode)
    (hs : s.obj x = some (.key n0)) :
    ksOf (n.toPrev (i - 1)) = n0.ks ∨
      ∃ more, ksOf (n.toPrev (i - 1)) = n0.ks ++ Klong.time i :: more := by
  obtain ⟨-, -, he⟩ := frame_overlay_ext hF hx ht hs
  exact Or.inl (toPrev_ext (prim_timesBefore (hb.times x n0 hs)) (hb.first x n0 hs) he)

/-- The frame after `newSuperRoot`. -/
theorem ts_frame_superRoot {i : Time} {s : Tree} {W : MW} (p : MParams) (y : NodeId)
    (hF : Frame i s (dirtyOf W) (treeOf i s W))
    (hn : ∀ x n, W.nodes.lookup x = some n → x < W.next) :
    Frame i s (dirtyOf (MW.afterSuperRoot W p i y)) (treeOf i s (MW.afterSuperRoot W p i y)) := by
  obtain ⟨hobj, -, hdirty⟩ := treeOf_afterSuperRoot i s p y hn
  rw [hdirty]
  obtain ⟨h1, h2, -⟩ := hF
  refine ⟨fun x o ho => ?_, fun x n hx hs => ?_,
    ⟨[(i, y)], treeOf_afterSuperRoot_roots i s p y W, by simp⟩⟩
  · rw [hobj]; exact h1 x o ho
  · rw [hobj] at hx; exact h2 x n hx hs

/-- The time split at the space root of a node from before the transaction: a
new node y, with the live klongs of x with the klongs added, becomes the space
root; then x is cut back to its node of before. -/
theorem ts_root {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} (h : CasPre p i base s tp w 0 x n ins C)
    (hnt : n.firstTime ≠ some i) {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPost p i base s tp w 0 x n ins C ()
      (MW.withNode (MW.afterSuperRoot
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } p i w.next)
        x (n.toPrev (i - 1))) := by
  intro _
  obtain ⟨htx, -, hF, hT⟩ := ts_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  have hxr : x = w.top.rootKey := by
    obtain ⟨c0, hon⟩ := h.on
    rw [h.path.root] at hon
    cases hon
    rfl
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  have hA : treeOf i s (w.withNode x (addAll i n ins)) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hAx : (treeOf i s (w.withNode x (addAll i n ins))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [hA]; simp [Tree.set]
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  let W2 : MW := MW.afterSuperRoot W1 p i w.next
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooks p i base s W1 :=
    putBooks_congr (putBooks_afterNewKey hb h.books hG hH hleaf hrf
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨f1, -, f3, -, f5, -, -, f8, -⟩ := afterSuperRoot_fields W1 p i w.next
  obtain ⟨hobj2, hroot2, -⟩ := treeOf_afterSuperRoot i s p w.next hK1.ids.1
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
  have hsome : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
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
  have hBy : NodeIs (treeOf i s (W2.withNode x (n.toPrev (i - 1)))) w.next (wLevel s w x) n.leaf
      (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [hBobj]; simp [Ne.symm hxne], hlev.symm,
      rfl, hrl,
      ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hS0 : Sound p.M (some x) (treeOf i s (w.withNode x (addAll i n ins))) x C := by
    have := hI.sound
    rw [show (w.withNode x (addAll i n ins)).top.rootKey = x from hxr.symm] at this
    exact this
  obtain ⟨hSB, hxnotB, hreach⟩ := Sound.timeSplitRoot hS0 hAx
    (show (treeOf i s (w.withNode x (addAll i n ins))).obj w.next = none from
      (treeOf_fresh hb hI.books (Nat.le_refl _)).1) hBy (by rw [hBobj]; simp)
    (fun z e1 e2 => by rw [hBobj, hA]; simp [Tree.set, e1, e2])
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  have hF2 := ts_frame_superRoot p w.next hF1 hK1.ids.1
  have hF3 := frame_withNode hF2 hx2 ht2
    (rfl : (n.toPrev (i - 1)).leaf = n.leaf) (ts_toPrev_ext hb hF hx htx)
  have hwx : wLevel s W2 x = wLevel s w x := by
    rw [show wLevel s W2 x = wLevel s W1 x from
      wLevel_afterSuperRoot s p i w.next (x := x)
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.books.ids.1 x n hx) (Nat.le_add_right _ 2)))]
    exact prim_wLevel_afterNewKey (p := p) (g := g) (h := hh) (leaf := n.leaf) (ks := r.ks) hxne
  have hroot3 : (treeOf i s (W2.withNode x (n.toPrev (i - 1)))).root = some w.next := by
    rw [hT3]
    show (treeOf i s W2).root = some w.next
    exact hroot2
  have hRA : reach (treeOf i s (w.withNode x (addAll i n ins))) =
      reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel x) x := by
    rw [reach_of_root hI.root,
      show (w.withNode x (addAll i n ins)).top.rootKey = x from hxr.symm]
  have hlk : ∀ z m, (treeOf i s (w.withNode x (addAll i n ins))).obj z = some (.key m) →
      ∃ m', (treeOf i s (W2.withNode x (n.toPrev (i - 1)))).obj z = some (.key m') ∧
        m'.level = m.level := by
    intro z m hm
    rw [hBobj]
    by_cases e1 : z = x
    · rw [e1] at hm ⊢
      rw [hAx] at hm
      cases hm
      exact ⟨⟨wLevel s W2 x, n.leaf, ksOf (n.toPrev (i - 1))⟩, by simp, hwx⟩
    · by_cases e2 : z = w.next
      · subst e2
        rw [show (treeOf i s (w.withNode x (addAll i n ins))).obj w.next = none from
          (treeOf_fresh hb hI.books (Nat.le_refl _)).1] at hm
        cases hm
      · rw [hA] at hm
        simp only [Tree.set, e1, ↓reduceIte] at hm
        exact ⟨m, by simp [e1, e2, hm], rfl⟩
  have hB3 : Balanced p (treeOf i s (W2.withNode x (n.toPrev (i - 1)))) := by
    refine Balanced.of_reach hI.balanced (N := [w.next, x]) (fun z hz => ?_) (fun z _ hz => ?_)
      hlk (fun z hz hzB m hm => ?_)
    · rw [reach_of_root hroot3] at hz
      rcases hreach z hz with e | e
      · left; rw [hRA]; exact e
      · right; simp [e]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hBobj, hA]
      simp [Tree.set, hz.1, hz.2]
    · rw [reach_of_root hroot3] at hzB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ts_bal_copy (ny := ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) hI.balanced
          (by rw [hRA]; exact tc_self _ _ _) hAx (by rw [hBobj]; simp [Ne.symm hxne]) hlev.symm
          rfl hrl hlk m hm
      · exact absurd hzB hxnotB
  obtain ⟨hfst, htimes⟩ := ts_old h.books hx htx hnt
  have hK3 := putBooks_withNode (n' := n.toPrev (i - 1)) (putBooks_afterSuperRoot w.next hK1) hx2
    ht2 rfl hfst htimes
  have hT2 : WTopInv i s tp W2.top W2.newTop :=
    topInv_afterSuperRoot w.next hT hb (by have := hK1.ids.2.2.2.1; exact this)
  refine ⟨⟨?_, ?_, hF3, hT2, hB3, hK3⟩, ⟨f8, ?_, ?_, ?_⟩⟩
  · show (treeOf i s (W2.withNode x (n.toPrev (i - 1)))).root = some W2.top.rootKey
    rw [hroot3, f1]
  · show Sound p.M none (treeOf i s (W2.withNode x (n.toPrev (i - 1)))) W2.top.rootKey C
    rw [f1]
    exact hSB
  · intro y m hy hny
    have hyx : y ≠ x := by
      intro e
      obtain ⟨c0, hon⟩ := h.on
      exact hny 0 c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert W2.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx, f3]
    exact prim_lookup_append_some _ hy
  · show w.next ≤ W2.next
    cases hnt1 : W1.newTop
    · rw [(afterSuperRoot_new hnt1 p i w.next).2.1]
      show w.next ≤ w.next + 2 + 2
      omega
    · rw [(afterSuperRoot_inPlace hnt1 p i w.next).2.1]
      show w.next ≤ w.next + 2
      omega
  · intro z hz
    unfold reachOf at hz ⊢
    have hz' : z ∈ reachAt (treeOf i s (W2.withNode x (n.toPrev (i - 1))))
        ((treeOf i s (W2.withNode x (n.toPrev (i - 1)))).fuel w.next) w.next := by
      rw [← f1]; exact hz
    rcases hreach z hz' with e | e
    · left
      show z ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey
      rw [← hxr]
      exact e
    · right
      rw [e]

/-! ## 7. A node from before the transaction below the space root -/

theorem ts_timesLe_of {m : MNode} {i : Time} (h : ∀ t, SIS.Tree.Klong.time t ∈ m.ks → t ≤ i) :
    TimesLe m i := by
  intro t ht
  obtain ⟨k, hk, e⟩ := List.mem_map.mp ht
  rw [kOf_eq_time e] at hk
  exact h t hk

/-- The time split below the space root of a node from before the
transaction, up to the parent's step: the state after the new node y is made
meets `CasPre` for the parent q with y's klong, from the rule `Sound.timeSplit`;
and the nodes that the parent's "if" state reaches. -/
theorem ts_parentPre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} (h : CasPre p i base s tp w (d + 1) x n ins C)
    {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf (addAll i n ins))) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf (addAll i n ins))
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    {q : NodeId} {nq : MNode} {c0 : Option Nat} {k1 : Nat} (hq : w.path[d]? = some (c0, q))
    (hqn : w.nodes.lookup q = some nq) (hk1 : w.path[d + 1]? = some (some k1, x))
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPre p i base s tp { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } d q
        nq [(k1, w.next)] C ∧
      x ∉ reachOf i s (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])) ∧
      ∀ z ∈ reachOf i s (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])),
        z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ z = w.next := by
  obtain ⟨htx, hroot, hF, hT⟩ := ts_wfacts hb h
  have hI := h.hyp
  have hx := h.look
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  -- the parent
  obtain ⟨-, -, htq⟩ := h.path.lookup (Nat.le_succ d) hq
  have hqne : q ≠ w.next := Nat.ne_of_lt (h.books.ids.1 q nq hqn)
  have hqx : q ≠ x := fun e => ts_off h d c0 (Nat.lt_succ_self d) (e ▸ hq)
  have hinq : nq.leaf = false := h.inner d c0 q nq (Nat.lt_succ_self d) hq hqn
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
  have hAx : (treeOf i s (w.withNode x (addAll i n ins))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [hA]; simp [Tree.set]
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAo q hqx]; exact treeOf_obj_overlay i s hqn htq
  have hreachP := ts_path_reach (w := w) hI.sound.good h.path (ts_off h) hAo
  have hRA := reach_of_root hI.root
  have hqr := hreachP d (Nat.le_succ d) c0 q hq
  have hxr := hreachP (d + 1) (Nat.le_refl _) (some k1) x hk1
  have hxok := hI.sound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hlq : wLevel s w x + 1 = wLevel s w q := by
    obtain ⟨-, -, hkq⟩ := hI.balanced q (by rw [hRA]; exact hqr) _ hAq
    obtain ⟨m, hm, hml⟩ := hkq hinq k1 x hk1l
    rw [hAx] at hm
    cases hm
    exact hml
  have hqok := hI.sound.nodes q hqr _ hAq
  simp only [Option.some.injEq, Ne.symm hqx, ite_false] at hqok
  obtain ⟨hqlen, hqwf, hqp⟩ := ts_nodeOk_iff.mp hqok
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooks p i base s W1 :=
    putBooks_congr (putBooks_afterNewKey hb h.books hG hH hleaf hrf
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
  have hsome : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
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
  -- the rule
  have hBy : NodeIs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))) w.next
      (wLevel s w x) n.leaf (live (ksOf (addAll i n ins))) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [hBobj]; simp [hqne.symm], hlev.symm,
      rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hBq : NodeIs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))) q
      (wLevel s w q) nq.leaf (insertCv k1 w.next (live (ksOf nq))) (bnd p.M (some q) q) := by
    refine ⟨⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩, by rw [hBobj]; simp,
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
        rw [hk.2, hBobj]
        simp [hqne.symm]
  have hBx : ((treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj x).isSome = true := by
    rw [hBobj]
    simp only [Ne.symm hqx, hxne, ↓reduceIte]
    rw [treeOf_obj_overlay i s hx htx]
    rfl
  have hRB : reach (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))) =
      reachAt (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])))
        ((treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).fuel w.top.rootKey)
        w.top.rootKey := reach_of_root hroot
  obtain ⟨hSB, hxnot, hreach⟩ := Sound.timeSplit hI.sound hqr hAq hk1l hAx
    (show (treeOf i s (w.withNode x (addAll i n ins))).obj w.next = none from
      (treeOf_fresh hb hI.books (Nat.le_refl _)).1) hBy hBq hBx
    (fun z e1 e2 e3 => by rw [hBobj, hAo z e1]; simp [e2, e3])
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  obtain ⟨tq, restq, hnq⟩ := h.books.timeFirst q nq hqn htq
  refine ⟨⟨hqn1, ⟨c0, hq⟩, ?_, fun e e' c c' u h1 h2 he he' =>
      h.nodup e e' c c' u h1 (Nat.le_succ_of_le h2) he he', ?_, hK1, hqwf, ?_, Or.inl rfl, ?_,
      ⟨?_, hSB, ?_, hT, ?_, ?_⟩⟩, hxnot, hreach⟩
  · exact PathOk.congr (pathOk_afterNewKey p g hh n.leaf r.ks (h.path.mono (Nat.le_succ d)) hs0
      hn0 ht0 hm0) rfl rfl rfl rfl rfl
  · intro d' c u m hd' hu hm
    obtain ⟨m', hm', -⟩ := h.path.lookup (by omega : d' ≤ d + 1) hu
    have : W1.nodes.lookup u = some m' := prim_lookup_append_some _ hm'
    rw [hm] at this
    cases this
    exact h.inner d' c u m (by omega) hu hm'
  · have hql : (ksOf nq).length ≤ p.M := hqlen
    rw [ksOf_length] at hql
    exact hql
  · intro a y1 b y2 he
    simp at he
  · exact hroot
  · refine frame_withNode hF1 hqn1 htq (addAll_leaf i nq _) (fun n0 hs => ?_)
    obtain ⟨-, -, he⟩ := frame_overlay_ext hF1 hqn1 htq hs
    exact addAll_ext (prim_timesBefore (hb.times q n0 hs)) he _
  · have hlk : ∀ z m, (treeOf i s (w.withNode x (addAll i n ins))).obj z = some (.key m) →
        ∃ m', (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj z =
          some (.key m') ∧ m'.level = m.level := by
      intro z m hm
      rw [hBobj]
      by_cases e1 : z = q
      · rw [e1] at hm ⊢
        rw [hAq] at hm
        cases hm
        exact ⟨⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩, by simp, rfl⟩
      · by_cases e2 : z = w.next
        · subst e2
          rw [show (treeOf i s (w.withNode x (addAll i n ins))).obj w.next = none from
            (treeOf_fresh hb hI.books (Nat.le_refl _)).1] at hm
          cases hm
        · simp only [e1, e2, ↓reduceIte]
          by_cases e3 : z = x
          · subst e3
            rw [hAx] at hm
            cases hm
            exact ⟨_, treeOf_obj_overlay i s hx htx, rfl⟩
          · rw [hAo z e3] at hm
            exact ⟨m, hm, rfl⟩
    refine Balanced.of_reach hI.balanced (N := [x, w.next, q]) (fun z hz => ?_)
      (fun z _ hz => ?_) hlk (fun z hz hzB m hm => ?_)
    · rw [hRB] at hz
      rcases hreach z hz with e | e
      · left; rw [hRA]; exact e
      · right; simp [e]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [hBobj, hAo z hz.1]
      simp [hz.2.1, hz.2.2]
    · rw [hRB] at hzB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with e | e | e
      · rw [e] at hzB
        exact absurd hzB hxnot
      · rw [e] at hm
        exact ts_bal_copy (ny := ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) hI.balanced
          (by rw [hRA]; exact hxr) hAx (by rw [hBobj]; simp [hqne.symm]) hlev.symm rfl hrl hlk m hm
      · rw [e] at hm
        refine ts_bal_set1 (k1 := k1) (y := w.next)
          (nb := ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩) hI.balanced
          (by rw [hRA]; exact hqr) hAq (by rw [hBobj]; simp) rfl rfl ?_ (fun _ => ?_) hlk m hm
        · show live (ksOf (addAll i nq [(k1, w.next)])) = insertCv k1 w.next (live (ksOf nq))
          rw [addAll_live hqwf]
          rfl
        · refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [hBobj]; simp [hqne.symm], ?_⟩
          show p.keyLevel g hh + 1 = wLevel s w q
          rw [← hlev, hlq]
  · refine putBooks_withNode hK1 hqn1 htq (addAll_leaf i nq _) ?_ ?_
    · obtain ⟨rest', hr'⟩ := addAll_first (i := i) hnq [(k1, w.next)]
      rw [hr', hnq]
      rfl
    · intro t ht
      exact addAll_timesLe (ts_timesLe_of (h.books.times q nq hqn)) _ t (ts_time_mem_ksOf ht)

/-- After the parent's step: x, which that step leaves as it was and does not
reach, is cut back to its node of before (`toPrev`): the frame holds again. -/
theorem ts_parentPost {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {d : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPre p i base s tp w (d + 1) x n ins C)
    (hnt : n.firstTime ≠ some i) {W1 W1q W3 : MW}
    (hI3 : PInv p i base s tp none C W3) (hcp : CascadePost i s W1 W1q W3 d)
    (hW1n : ∀ y m, w.nodes.lookup y = some m → W1.nodes.lookup y = some m)
    (hW1p : W1.path = w.path) (hW1next : w.next + 2 ≤ W1.next)
    (hxnot : x ∉ reachOf i s W1q)
    (hreach : ∀ z ∈ reachOf i s W1q, z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ z = w.next) :
    W3.nodes.lookup x = some n ∧
      CasPost p i base s tp w (d + 1) x n ins C () (W3.withNode x (n.toPrev (i - 1))) := by
  obtain ⟨htx, -⟩ := ts_wfacts hb h
  have hx := h.look
  obtain ⟨c0, hon⟩ := h.on
  have hxnext : x < w.next := h.books.ids.1 x n hx
  have hx3 : W3.nodes.lookup x = some n := hcp.off x n (hW1n x n hx) (fun d' c hd' he => by
    rw [hW1p] at he
    exact ts_off h d' c (Nat.lt_succ_of_le hd') he)
  have hxs := (h.books.first x n hx htx).mpr hnt
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
  refine ⟨hx3, fun _ => ?_⟩
  have hT4 : treeOf i s (W3.withNode x (n.toPrev (i - 1))) =
      (treeOf i s W3).set x (.key ⟨wLevel s W3 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) :=
    treeOf_withNode i s _ htx3
  have hx3r : x ∉ reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey := by
    intro hm
    rcases hcp.reach x hm with e | e
    · exact hxnot e
    · exact absurd (Nat.lt_of_lt_of_le hxnext (Nat.le_trans (Nat.le_add_right _ 2)
        (Nat.le_trans hW1next e))) (Nat.lt_irrefl x)
  have hsame4 : ∀ z, z ≠ x → (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s W3).obj z := by
    intro z hz; rw [hT4]; simp [Tree.set, hz]
  have ha : ∀ z ∈ reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey,
      (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z = (treeOf i s W3).obj z :=
    fun z hz => hsame4 z (fun e => hx3r (e ▸ hz))
  have hs4 : ∀ z, ((treeOf i s W3).obj z).isSome = true →
      ((treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    by_cases e : z = x
    · rw [e, hT4]; simp [Tree.set]
    · rw [hsame4 z e]; exact hz
  have hr3 : W3.top.rootKey ≠ x := fun e => hx3r (e ▸ tc_self _ _ _)
  have hR : reachAt (treeOf i s (W3.withNode x (n.toPrev (i - 1))))
      ((treeOf i s (W3.withNode x (n.toPrev (i - 1)))).fuel W3.top.rootKey) W3.top.rootKey =
      reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey := by
    rw [show (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).fuel W3.top.rootKey =
      (treeOf i s W3).fuel W3.top.rootKey by simp only [Tree.fuel, hsame4 _ hr3]]
    exact reachAt_agree _ _ ha
  obtain ⟨hfst, htimes⟩ := ts_old hI3.books hx3 htx3 hnt
  refine ⟨⟨?_, hI3.sound.agree ha hs4, frame_withNode hI3.frame hx3 htx3 rfl
      (ts_toPrev_ext hb hI3.frame hx3 htx3), hI3.top, ?_,
      putBooks_withNode (n' := n.toPrev (i - 1)) hI3.books hx3 htx3 rfl hfst htimes⟩,
    ⟨hcp.path.trans hW1p, ?_, Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) hcp.next,
      ?_⟩⟩
  · rw [hT4]; exact hI3.root
  · have hR3 := reach_of_root hI3.root
    have hR4 : reach (treeOf i s (W3.withNode x (n.toPrev (i - 1)))) = reach (treeOf i s W3) := by
      rw [reach_of_root (show (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).root =
        some W3.top.rootKey by rw [hT4]; exact hI3.root), hR3]
      exact hR
    refine Balanced.of_reach hI3.balanced (N := [x]) (fun z hz => Or.inl (hR4 ▸ hz))
      (fun z _ hz => hsame4 z (by simpa using hz)) (fun z m hm => ?_) (fun z hz hzB m hm => ?_)
    · by_cases e : z = x
      · rw [e] at hm ⊢
        rw [treeOf_obj_overlay i s hx3 htx3] at hm
        cases hm
        exact ⟨⟨wLevel s W3 x, n.leaf, ksOf (n.toPrev (i - 1))⟩, by rw [hT4]; simp [Tree.set], rfl⟩
      · exact ⟨m, by rw [hsame4 z e]; exact hm, rfl⟩
    · simp only [List.mem_singleton] at hz
      subst hz
      rw [hR4, hR3] at hzB
      exact absurd hzB hx3r
  · intro y m hy hny
    have hyx : y ≠ x := fun e => hny (d + 1) c0 (Nat.le_refl _) (e ▸ hon)
    have := hcp.off y m (hW1n y m hy) (fun d' c hd' he => hny d' c (Nat.le_succ_of_le hd')
      (hW1p ▸ he))
    show (SIS.Tree.upsert W3.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact this
  · intro z hz
    have hz3 : z ∈ reachOf i s W3 := by
      unfold reachOf at hz ⊢
      rw [← hR]
      exact hz
    rcases hcp.reach z hz3 with e | e
    · rcases hreach z e with e' | e'
      · exact Or.inl e'
      · exact Or.inr (Nat.le_of_eq e'.symm)
    · exact Or.inr (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) e)

/-! ## 8. The steps of `handleFullWith` -/

/-- A note in one branch of an `if`: the rest runs from the state with some
trail either way. -/
theorem ts_wp_ite_note {b : Bool} {t : String} {K : SIS.Tree.M Unit} {c : Ctx} {w0 : MW}
    {post : Unit → MW → Prop} (h : ∀ T, WP K c { w0 with trail := T } post) :
    WP (if b = true then (SIS.Tree.note t >>= fun _ => K) else K) c w0 post := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h w0.trail
  · simp only [↓reduceIte]
    rw [ts_wp_bind_ok (note_eq c w0 t)]
    exact h _

/-- `replaceOrAdd` on x's last version with the klongs: no error, the same
state, and a node r with the live klongs of x with the klongs added, well
formed, within the node size, that starts with a time klong of i and has no
time after i; its key klongs are those of x with the klongs added. -/
theorem ts_wp_replace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)} {compact : Bool}
    (h : CasPre p i base s tp w depth x n ins C)
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
  obtain ⟨htx, -⟩ := ts_wfacts hb h
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
    · obtain ⟨t0, rest0, hn⟩ := h.books.timeFirst x n h.look htx
      have hl := live_length_le (ks := ksOf n) ⟨t0, rest0.map kOf, by simp [ksOf, hn, kOf]⟩
      rw [ksOf_length] at hl
      omega
    · have := hp.splitHi
      omega
  · intro c y hk
    rcases hrkeys c y hk with e | e
    · exact (addAll_key_mem ins n).mpr (Or.inl (ts_live_mem_key e))
    · exact (addAll_key_mem ins n).mpr (Or.inr e)

/-- `getNode` leaves the nodes outside the bounds as they are. -/
theorem ts_getNode_outside {x : NodeId} {c : Ctx} {W W' : MW} {m : MNode}
    (h : SIS.Tree.getNode x c W = .ok (m, W')) : W'.outside = W.outside := by
  have hw : WP (SIS.Tree.getNode x) c W (fun _ W' => W'.outside = W.outside) := by
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
  exact hw m W' h

theorem ts_getNode_put_outside {x : NodeId} {f : MNode → MNode} {c : Ctx} {W W' : MW} {a : Unit}
    (h : (SIS.Tree.getNode x >>= fun m => SIS.Tree.putNode x (f m)) c W = .ok (a, W')) :
    W'.outside = W.outside := by
  have hw : WP (SIS.Tree.getNode x >>= fun m => SIS.Tree.putNode x (f m)) c W
      (fun _ W' => W'.outside = W.outside) := by
    rw [wp_bind]
    intro m W'' h1
    rw [ts_wp_ok (putNode_eq _ _ _ _)]
    show W''.outside = W.outside
    exact ts_getNode_outside h1
  exact hw a W' h

/-! ## 9. The statement -/

theorem handleFull_time {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit} {compact : Bool}
    (h : CasPre p i base s tp w depth x n ins C)
    (hup : ∀ d, depth = d + 1 → UpOk p i base s tp v up d)
    (hcase : (compact = true ∧ n.size + ins.length + 1 ≤ p.M) ∨
      (compact = false ∧ (n.lastVersion i).size ≤ p.splitAbove)) :
    WP (SIS.Tree.handleFullWith up depth x ins (n.lastVersion i) compact)
      { p := p, i := i, view := v } w (CasPost p i base s tp w depth x n ins C) := by
  have hx := h.look
  obtain ⟨htx, -, -, hT⟩ := ts_wfacts hb h
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
      refine ts_wp_replace hp hb h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (newSuperRoot_eq (s := s) (tp := tp) v _ ?_)).mpr ?_
      · exact hT
      refine (ts_wp_bind_ok (getNode_hit (n := n) _ ?_)).mpr ?_
      · rw [(afterSuperRoot_fields _ _ _ _).2.2.1]
        exact prim_lookup_append_some _ hx
      rw [ts_wp_ok (putNode_eq _ _ _ _)]
      exact ts_root hb h hnt' hg hrl hrwf hrs hrk hrf hrt _ _
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
      refine ts_wp_replace hp hb h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (klongAt_eq (k := k1) (x := x) _ ?_)).mpr ?_
      · exact hon
      rw [wp_bind]
      obtain ⟨hpre, hxnot, hreach⟩ := ts_parentPre hb h hg hrl hrwf hrs hrk hrf hrt e1 hqn hon
        ((w.next, x) :: w.madeFor) ("split.time1" :: T')
      refine WP.mono (hup d rfl u0 [(k1, w.next)] _ nq C hpre) (fun _ W3 hpost => ?_)
      by_cases hout : W3.outside = []
      · obtain ⟨hI3, hcp⟩ := hpost hout
        obtain ⟨hx3, hfin⟩ := ts_parentPost hb h hnt' hI3 hcp
          (fun y m hy => prim_lookup_append_some _ hy) rfl (Nat.le_refl _) hxnot hreach
        rw [ts_wp_bind_ok (getNode_hit _ hx3), ts_wp_ok (putNode_eq _ _ _ _)]
        exact hfin
      · intro _ W4 hrun hout4
        exact absurd ((ts_getNode_put_outside hrun).symm.trans hout4) hout
  · have hnt' : n.firstTime = some i := by simpa using hnt
    have hAo : ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z =
        (treeOf i s w).obj z := by
      intro z hz
      rw [treeOf_withNode i s _ htx]
      simp [Tree.set, hz]
    have hxr := ts_path_reach (w := w) h.hyp.sound.good h.path (ts_off h) hAo depth
      (Nat.le_refl _) c0 x hon
    cases depth with
    | zero =>
      rw [ts_wp_bind_ok (parentAt_zero _ _), ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine ts_wp_replace hp hb h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact ts_inPlace hb h hnt' hrl hrwf hrs hrk hrf hrt hxr _
    | succ d =>
      obtain ⟨c0', u0, -, -, -, e1, -⟩ := h.path.links d (Nat.lt_succ_self d)
      obtain ⟨nq, hqn, -⟩ := h.path.lookup (Nat.le_succ d) e1
      rw [ts_wp_bind_ok (parentAt_succ _ e1), ts_wp_bind_ok (getNode_hit _ hqn),
        ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine ts_wp_replace hp hb h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact ts_inPlace hb h hnt' hrl hrwf hrs hrk hrf hrt hxr _

end Contract
