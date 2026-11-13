/-
What the writer's tree gives the reads (bergdb 024-12, TP10, `OpGetOK`): in a
tree a node is reached through the same number of links of segment leaves on
every path (`tPath_unique`); so a node that the search of a key of one segment visits in
the space root's tree is visited by no other key (`visits_unique_of_tree`): the
premise `huniq` of `writerWP_put_room` (`GetFrame.lean`), which TP7's invariant
lacks (`sharedSegment_changes_other_key`). And the tree is `GetSplit.lean`'s
TREE premise (`htree_of_treeOK`).
-/
import SIS.Tree.WriterTree
import SIS.Tree.GetSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem mem_of_lookup_nodup {β : Type} (l : List (Nat × β)) (a : Nat) (b : β)
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  obtain ⟨l1, l2, hl, _⟩ := List.lookup_eq_some_iff.mp h
  rw [hl]; simp

theorem lookup_of_mem_nodup {β : Type} (l : List (Nat × β)) (hn : (l.map Prod.fst).Nodup)
    (a : Nat) (b : β) (h : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => cases h
  | cons q l ih =>
    rcases q with ⟨a', b'⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with hm | hm
    · simp only [Prod.mk.injEq] at hm
      rcases hm with ⟨h1, h2⟩
      subst h1; subst h2
      simp
    · have hne : a ≠ a' := by
        intro he
        apply hn.1
        rw [← he]
        exact List.mem_map.mpr ⟨(a, b), hm, rfl⟩
      have hb : (a == a') = false := by simpa using hne
      simp only [List.lookup_cons, hb]
      exact ih hn.2 hm

/-- The key of one segment: its compare value is no long segment's. -/
theorem keyWf_single_segLen (cv : Nat) (h : keyWf [cv] = true) : segLen cv ≠ 7 := by
  simp only [keyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2


/-- Reached from r through k links of segment leaves (to the next segment's
tree) and any number of inner links. -/
inductive TPath (L : NodeId → Option KNode) (t : Time) (r : NodeId) : NodeId → Nat → Prop
  | root : TPath L t r r 0
  | inner {x : NodeId} {c : Nat} {y : NodeId} {k : Nat} {n : KNode} :
      TPath L t r x k → L x = some n → n.leaf = false → TLink L t x c y → TPath L t r y k
  | seg {x : NodeId} {c : Nat} {y : NodeId} {k : Nat} {n : KNode} :
      TPath L t r x k → L x = some n → n.leaf = true → TLink L t x c y → TPath L t r y (k + 1)

theorem tPath_reach (L : NodeId → Option KNode) (t : Time) (r x : NodeId) (k : Nat)
    (h : TPath L t r x k) : TReach L t r x := by
  induction h with
  | root => exact TReach.root
  | inner _ _ _ hl ih => exact TReach.link ih hl
  | seg _ _ _ hl ih => exact TReach.link ih hl

/-- In a tree, every path to a node passes the same number of segment links. -/
theorem tPath_unique (L : NodeId → Option KNode) (t : Time) (r : NodeId) (ht : TreeOK L t r)
    (x : NodeId) (k1 : Nat) (h1 : TPath L t r x k1) : ∀ k2, TPath L t r x k2 → k1 = k2 := by
  induction h1 with
  | root =>
    intro k2 h2
    cases h2 with
    | root => rfl
    | inner hp _ _ hl => exact absurd hl (ht.rootFree _ _ (tPath_reach L t r _ _ hp))
    | seg hp _ _ hl => exact absurd hl (ht.rootFree _ _ (tPath_reach L t r _ _ hp))
  | @inner x c y k n hp hn hleaf hl ih =>
    intro k2 h2
    cases h2 with
    | root => exact absurd hl (ht.rootFree x c (tPath_reach L t r x k hp))
    | @inner x' c' _ _ n' hp' hn' _ hl' =>
      have := (ht.oneLink x c x' c' _ (tPath_reach L t r x k hp)
        (tPath_reach L t r x' _ hp') hl hl').1
      subst this
      exact ih _ hp'
    | @seg x' c' _ k' n' hp' hn' hleaf' hl' =>
      have := (ht.oneLink x c x' c' _ (tPath_reach L t r x k hp)
        (tPath_reach L t r x' k' hp') hl hl').1
      subst this
      rw [hn] at hn'
      simp only [Option.some.injEq] at hn'
      subst hn'
      rw [hleaf] at hleaf'
      cases hleaf'
  | @seg x c y k n hp hn hleaf hl ih =>
    intro k2 h2
    cases h2 with
    | root => exact absurd hl (ht.rootFree x c (tPath_reach L t r x k hp))
    | @inner x' c' _ _ n' hp' hn' hleaf' hl' =>
      have := (ht.oneLink x c x' c' _ (tPath_reach L t r x k hp)
        (tPath_reach L t r x' _ hp') hl hl').1
      subst this
      rw [hn] at hn'
      simp only [Option.some.injEq] at hn'
      subst hn'
      rw [hleaf] at hleaf'
      cases hleaf'
    | @seg x' c' _ k' n' hp' hn' _ hl' =>
      have := (ht.oneLink x c x' c' _ (tPath_reach L t r x k hp)
        (tPath_reach L t r x' k' hp') hl hl').1
      subst this
      rw [ih k' hp']

/-- The search of a compare value through one segment tree visits nodes
through inner links: no segment link more. -/
theorem eqVisits_tPath (L : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat) :
    ∀ f y k, TPath L t r y k → ∀ x c, (x, c) ∈ eqVisits L t cv f y → TPath L t r x k ∧ c = cv := by
  intro f
  induction f with
  | zero => intro y k _ x c hm; simp [eqVisits] at hm
  | succ f ih =>
    intro y k hy x c hm
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨hy, rfl⟩
    · cases hn : L y with
      | none => rw [hn] at hm; cases hm
      | some n =>
        rw [hn] at hm
        simp only at hm
        cases hl : n.leaf with
        | true => rw [hl] at hm; cases hm
        | false =>
          rw [hl] at hm
          simp only [Bool.false_eq_true, ↓reduceIte] at hm
          cases hs : n.searchLte t cv with
          | none => rw [hs] at hm; cases hm
          | some fd =>
            rw [hs] at hm
            simp only at hm
            have hlive : (fd.c, fd.y) ∈ n.liveAt t :=
              mem_of_lookup_nodup _ fd.c fd.y (n.searchLte_liveAt_lookup t cv fd hs)
            have hlink : TLink L t y fd.c fd.y := ⟨n, hn, hlive⟩
            exact ih fd.y k (TPath.inner hy hn hl hlink) x c hm

/-- The search of a compare value through one segment tree, if it finds a
pointer, ends at a segment leaf of the tree that is visited. -/
theorem getEqR_leaf (L : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat)
    (hwf : ∀ x n, L x = some n → klongsWf n.ks = true) :
    ∀ f y k z, TPath L t r y k → getEqR L t cv f y = some z →
      ∃ x n, TPath L t r x k ∧ L x = some n ∧ n.leaf = true ∧ (cv, z) ∈ n.liveAt t := by
  intro f
  induction f with
  | zero => intro y k z _ h; simp [getEqR] at h
  | succ f ih =>
    intro y k z hy h
    simp only [getEqR] at h
    cases hn : L y with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      cases hl : n.leaf with
      | true =>
        rw [hl] at h
        simp only [↓reduceIte] at h
        have hs := searchEqSpec n t cv (hwf y n hn)
        rw [h] at hs
        exact ⟨y, n, hy, hn, hl, mem_of_lookup_nodup _ cv z hs.symm⟩
      | false =>
        rw [hl] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hs : n.searchLte t cv with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          simp only at h
          have hlive : (fd.c, fd.y) ∈ n.liveAt t :=
            mem_of_lookup_nodup _ fd.c fd.y (n.searchLte_liveAt_lookup t cv fd hs)
          have hlink : TLink L t y fd.c fd.y := ⟨n, hn, hlive⟩
          exact ih fd.y k z (TPath.inner hy hn hl hlink) h

/-- The reading of a key visits its first segment's tree through no segment
link, and every later one through at least one. -/
theorem fromVisits_tPath (L : NodeId → Option KNode) (t : Time) (r : NodeId) (fuel : Nat)
    (hwf : ∀ x n, L x = some n → klongsWf n.ks = true) :
    ∀ key y k, keyWf key = true → TPath L t r y k → ∀ x c, (x, c) ∈ fromVisits L t fuel key y →
      (TPath L t r x k ∧ some c = key.head?) ∨ ∃ k', k < k' ∧ TPath L t r x k' := by
  intro key
  induction key with
  | nil => intro y k _ _ x c hm; simp [fromVisits] at hm
  | cons c1 rest ih =>
    intro y k hkey hy x c hm
    cases rest with
    | nil =>
      simp only [fromVisits] at hm
      obtain ⟨hx, hc⟩ := eqVisits_tPath L t r c1 fuel y k hy x c hm
      exact Or.inl ⟨hx, by rw [hc]; rfl⟩
    | cons c2 rest =>
      obtain ⟨_, _, hlen, hrest⟩ := (keyWf_cons_cons c1 c2 rest).mp hkey
      simp only [fromVisits, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨hx, hc⟩ := eqVisits_tPath L t r c1 fuel y k hy x c hm
        exact Or.inl ⟨hx, by rw [hc]; rfl⟩
      · cases hg : getEqR L t c1 fuel y with
        | none => rw [hg] at hm; cases hm
        | some z =>
          rw [hg] at hm
          simp only at hm
          obtain ⟨lx, ln, hlp, hln, hll, hlive⟩ := getEqR_leaf L t r c1 hwf fuel y k z hy hg
          have hlink : TLink L t lx c1 z := ⟨ln, hln, hlive⟩
          have hz : TPath L t r z (k + 1) := TPath.seg hlp hln hll hlink
          rcases ih z (k + 1) hrest hz x c hm with ⟨hx, _⟩ | ⟨k', hk', hx⟩
          · exact Or.inr ⟨k + 1, Nat.lt_succ_self k, hx⟩
          · exact Or.inr ⟨k', by omega, hx⟩

/-- In the writer's tree, a node that the search of a key of one segment, cv,
visits in the space root's tree is visited by the reading of no other key with
cv: `writerWP_put_room`'s `huniq`, from the tree and well-formed klongs. -/
theorem visits_unique_of_tree (L : NodeId → Option KNode) (t : Time) (r : NodeId) (fuel : Nat)
    (ht : TreeOK L t r) (hwf : ∀ x n, L x = some n → klongsWf n.ks = true)
    (cv : Nat) (hcv : keyWf [cv] = true) (key' : Key) (x : NodeId) (hkey' : keyWf key' = true)
    (h1 : (x, cv) ∈ fromVisits L t fuel key' r) (h2 : (x, cv) ∈ eqVisits L t cv fuel r) :
    key' = [cv] := by
  obtain ⟨hx0, _⟩ := eqVisits_tPath L t r cv fuel r 0 TPath.root x cv h2
  rcases fromVisits_tPath L t r fuel hwf key' r 0 hkey' TPath.root x cv h1 with
    ⟨_, hhead⟩ | ⟨k', hk', hx'⟩
  · cases key' with
    | nil => cases hhead
    | cons c1 rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      cases rest with
      | nil => rw [hhead]
      | cons c2 rest =>
        obtain ⟨_, _, hlen, _⟩ := (keyWf_cons_cons c1 c2 rest).mp hkey'
        rw [hhead] at hcv
        exact absurd hlen (keyWf_single_segLen c1 hcv)
  · have := tPath_unique L t r ht x 0 hx0 k' hx'
    omega

/-- The reads' reach (`GetSplit.lean`) is the tree's. -/
theorem reachS_tReach (L : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (h : ReachS L t r x) : TReach L t r x := by
  induction h with
  | root => exact TReach.root
  | step x n c z _ hn hc ih => exact TReach.link ih ⟨n, hn, hc⟩

/-- The tree is the TREE premise of `GetSplit.lean`'s lemmas (`htree`): of the
nodes reached, one live klong names a node at most. -/
theorem htree_of_treeOK (L : NodeId → Option KNode) (t : Time) (r : NodeId) (ht : TreeOK L t r) :
    ∀ x xn cc z, ReachS L t r x → L x = some xn → (cc, z) ∈ xn.liveAt t →
      ∀ x' xn' cc', ReachS L t r x' → L x' = some xn' → (cc', z) ∈ xn'.liveAt t →
        x = x' ∧ cc = cc' := by
  intro x xn cc z hx hxn hc x' xn' cc' hx' hxn' hc'
  exact ht.oneLink x cc x' cc' z (reachS_tReach L t r x hx) (reachS_tReach L t r x' hx')
    ⟨xn, hxn, hc⟩ ⟨xn', hxn', hc'⟩

end SIS.Tree
