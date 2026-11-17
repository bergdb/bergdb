/-
The contract package (bergdb 030-10): the writer's rules for a put, as
statements about two trees. `Sound M ex T r C` says that the tree T from the
space root r meets the invariants, TREE, and holds the keys C; the node `ex`,
if any, may hold three klongs more than the node size M (a node with klongs
added that has not been split yet).

Each rule: the tree A is sound with the node x over its size; the tree B is A
with x replaced as the writer's rule does it (`NodeIs` says what a node of B
is: its level, its kind, its live klongs, and that it meets the rules of one
node within a size); then B is sound, with the parent over its size, or with
no node over it. The rules also say which nodes are reached in B: those of A,
and the nodes made; a node replaced is not.

* `Sound.agree`: a change of nodes that are not reached.
* `Sound.inPlace`: x replaced by a node with its live klongs (a time split in
  place; a node with room).
* `Sound.put`: a klong of a value added to the segment leaf that the key is
  routed to: the tree holds the keys with the put applied.
* `Sound.timeSplit`, `Sound.timeSplitRoot`: x replaced by a new node y with
  its live klongs; the parent's klong names y, or y is the space root.
* `Sound.spaceSplit`, `Sound.spaceSplitRoot`: x replaced by two nodes with
  the halves of its live klongs (the first one new, or x itself); the parent
  gets the second one's klong, or a new root names both.
-/
import Contract.Proof.Sound

namespace Contract

/-- The contract's invariants, the contents and TREE, as `Sound`. -/
theorem sound_iff {M : Nat} {T : Tree} {C : List (Key × Nat)} :
    (invOk ⟨M⟩ T = true ∧ contents T = C ∧ TreeOk T) ↔
      ∃ r, T.root = some r ∧ Sound M none T r C := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨r, n, hr, ho, hne, hG, hn⟩ := (invOk_iff (p := ⟨M⟩)).mp h1
    have hreach : reach T = reachAt T (T.fuel r) r := by simp [reach, hr]
    refine ⟨r, hr, ⟨⟨n, ho, hne⟩, hG, ?_, ?_, ?_⟩⟩
    · intro z hz m hm
      simpa using hn z (hreach ▸ hz) m hm
    · rw [← h2]
      simp [contents, hr, L]
    · unfold TreeOk at h3
      rwa [hreach] at h3
  · rintro ⟨r, hr, hS⟩
    have hreach : reach T = reachAt T (T.fuel r) r := by simp [reach, hr]
    obtain ⟨n, ho, hne⟩ := hS.key
    refine ⟨(invOk_iff (p := ⟨M⟩)).mpr ⟨r, n, hr, ho, hne, hS.good, ?_⟩, ?_, ?_⟩
    · intro z hz m hm
      simpa using hS.nodes z (hreach ▸ hz) m hm
    · rw [← hS.holds]
      simp [contents, hr, L]
    · unfold TreeOk
      rw [hreach]
      exact hS.tree

/-! ## Helpers: nodes, reaching -/

theorem tr_nodeOk {A B : Tree} {b b' : Nat} {m : KNode} (h : nodeOk ⟨b⟩ A m = true)
    (hb : b ≤ b') (hs : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true) :
    nodeOk ⟨b'⟩ B m = true := by
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  refine ⟨⟨by omega, h.1.2⟩, ?_⟩
  intro k hk
  have := h.2 k hk
  cases k with
  | key c y => exact hs y this
  | _ => rfl

/-- Every node reached from a sound node exists. -/
theorem Good.tr_exists {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi) :
    ∀ f, ∀ z ∈ reachAt s f u, (s.obj z).isSome = true := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro f z hz
    cases f with
    | zero =>
      simp only [reachAt, List.mem_singleton] at hz
      simp [hz, hobj]
    | succ f =>
      rcases tc_mem_succ.mp hz with rfl | ⟨n', ho, ⟨c, y⟩, hm, hz⟩
      · simp [hobj]
      · rw [hobj] at ho
        cases ho
        by_cases hk : n.leaf = true → isLong c = true
        · cases hl : n.leaf with
          | true => exact ihseg hl c y hm (hk hl) f z hz
          | false =>
            obtain ⟨pre, post, he⟩ := List.append_of_mem hm
            exact ihkid hl pre c y post he f z hz
        · simp only [Classical.not_imp, Bool.not_eq_true] at hk
          obtain ⟨v, hv⟩ := hval hk.1 c y hm hk.2
          rw [tc_val hv, List.mem_singleton] at hz
          simp [hz, hv]

/-- A key node reached from a sound node is sound for some range. -/
theorem Good.tr_reach_good {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat}
    (h : Good s u lo hi) : ∀ f, ∀ z ∈ reachAt s f u, ∀ m, s.obj z = some (.key m) →
      ∃ lo' hi', Good s z lo' hi' := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    intro f z hz m hm
    cases f with
    | zero =>
      simp only [reachAt, List.mem_singleton] at hz
      exact ⟨lo, hi, hz ▸ hG⟩
    | succ f =>
      rcases tc_mem_succ.mp hz with rfl | ⟨n', ho, ⟨c, y⟩, hm', hz⟩
      · exact ⟨lo, hi, hG⟩
      · rw [hobj] at ho
        cases ho
        by_cases hk : n.leaf = true → isLong c = true
        · cases hl : n.leaf with
          | true => exact ihseg hl c y hm' (hk hl) f z hz m hm
          | false =>
            obtain ⟨pre, post, he⟩ := List.append_of_mem hm'
            exact ihkid hl pre c y post he f z hz m hm
        · simp only [Classical.not_imp, Bool.not_eq_true] at hk
          obtain ⟨v, hv⟩ := hval hk.1 c y hm' hk.2
          rw [tc_val hv, List.mem_singleton] at hz
          rw [hz, hv] at hm
          cases hm

/-- What a node reached from a sound node reaches is reached from it. -/
theorem Good.tr_closed {s : Tree} {r q z : NodeId} {lo : Nat} {hi : Option Nat}
    (h : Good s r lo hi) (hq : q ∈ reachAt s (s.fuel r) r) {g : Nat} (hz : z ∈ reachAt s g q) :
    z ∈ reachAt s (s.fuel r) r := by
  have h1 := tc_trans g (s.fuel r) r q hq hz
  rwa [h.reachAt_eq (s.fuel r + g) (by omega)] at h1

/-- TREE below a node reached. -/
theorem Good.tr_nodup {s : Tree} {r q : NodeId} {lo : Nat} {hi : Option Nat}
    (h : Good s r lo hi) (hT : (reachAt s (s.fuel r) r).Nodup) (hq : q ∈ reachAt s (s.fuel r) r) :
    (reachAt s (s.fuel q) q).Nodup := by
  cases ho : s.obj q with
  | none => simp [Tree.fuel, ho, reachAt]
  | some o =>
    cases o with
    | val v => simp [Tree.fuel, ho, reachAt]
    | key m =>
      obtain ⟨P, S, hA, _⟩ := tc_reach_split (A := s) (B := s) (q := q)
        (fun n hn => ⟨n, hn, le_refl _, id⟩) (fun _ _ h => h) ⟨m, ho⟩ h hT hq (fun _ _ _ => rfl)
      rw [hA] at hT
      exact (List.nodup_append.mp (List.nodup_append.mp hT).1).2.1

theorem Sound.agree {M : Nat} {ex : Option NodeId} {A B : Tree} {r : NodeId}
    {C : List (Key × Nat)} (h : Sound M ex A r C)
    (ha : ∀ z ∈ reachAt A (A.fuel r) r, B.obj z = A.obj z)
    (hs : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true) : Sound M ex B r C := by
  have hr : B.obj r = A.obj r := ha r (tc_self _ _ _)
  have hf : B.fuel r = A.fuel r := by simp [Tree.fuel, hr]
  have hR : reachAt B (B.fuel r) r = reachAt A (A.fuel r) r := by
    rw [hf]
    exact reachAt_agree _ _ ha
  obtain ⟨n, ho, hne⟩ := h.key
  refine ⟨⟨n, hr.trans ho, hne⟩, h.good.agree ha, ?_, ?_, ?_⟩
  · intro z hz m hm
    rw [hR] at hz
    rw [ha z hz] at hm
    exact tr_nodeOk (h.nodes z hz m hm) (le_refl _) hs
  · rw [← h.holds]
    exact L_agree ha
  · rw [hR]
    exact h.tree

/-- A tree that is sound with `ex` is sound with none over its size, if `ex`
is not reached. -/
theorem Sound.tr_drop {M : Nat} {ex : Option NodeId} {T : Tree} {r : NodeId}
    {C : List (Key × Nat)} (h : Sound M ex T r C)
    (hx : ∀ z ∈ reachAt T (T.fuel r) r, ex ≠ some z) : Sound M none T r C := by
  refine ⟨h.key, h.good, ?_, h.holds, h.tree⟩
  intro z hz m hm
  have := h.nodes z hz m hm
  simpa [hx z hz] using this

/-! ## A node by its live klongs -/

/-- What `Good` asks of the live klong (c, y) of a key node of level `lev` and
kind `leaf` with the range [lo, hi); H is the bound of the child in an inner
node. -/
def KidOk (s : Tree) (lev : Nat) (leaf : Bool) (lo : Nat) (hi : Option Nat) (c : Nat)
    (y : NodeId) (H : Option Nat) : Prop :=
  belowHi c hi = true ∧ (leaf = true → lo ≤ c) ∧
    (leaf = true → isLong c = false → ∃ v, s.obj y = some (.val v)) ∧
    ((leaf = true → isLong c = true) → ∃ m, s.obj y = some (.key m) ∧ m.level < lev ∧
      live m.ks ≠ [] ∧ Good s y (if leaf then 0 else max lo c) (if leaf then none else H))

/-- The live klongs, each with the bound of its child. -/
def bounds : List (Nat × NodeId) → Option Nat → List (Nat × NodeId × Option Nat)
  | [], _ => []
  | (c, y) :: r, hi => (c, y, nextHi r hi) :: bounds r hi

theorem bounds_append (l1 l2 : List (Nat × NodeId)) (hi : Option Nat) :
    bounds (l1 ++ l2) hi = bounds l1 (nextHi l2 hi) ++ bounds l2 hi := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih =>
    obtain ⟨c, y⟩ := a
    have h : nextHi (l1 ++ l2) hi = nextHi l1 (nextHi l2 hi) := by cases l1 <;> rfl
    simp [bounds, ih, h]

theorem bounds_mem {l pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId} (hi : Option Nat)
    (he : l = pre ++ (c, y) :: post) : (c, y, nextHi post hi) ∈ bounds l hi := by
  subst he
  rw [bounds_append]
  simp [bounds]

theorem bounds_split {hi : Option Nat} {t : Nat × NodeId × Option Nat} :
    ∀ {l : List (Nat × NodeId)}, t ∈ bounds l hi →
      ∃ pre post, l = pre ++ (t.1, t.2.1) :: post ∧ t.2.2 = nextHi post hi
  | [], h => by simp [bounds] at h
  | (c, y) :: r, h => by
    simp only [bounds, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], r, rfl, rfl⟩
    · obtain ⟨pre, post, h1, h2⟩ := bounds_split h
      exact ⟨(c, y) :: pre, post, by rw [h1]; rfl, h2⟩

theorem bounds_mem_live {hi : Option Nat} {t : Nat × NodeId × Option Nat}
    {l : List (Nat × NodeId)} (h : t ∈ bounds l hi) : (t.1, t.2.1) ∈ l := by
  obtain ⟨pre, post, h1, _⟩ := bounds_split h
  rw [h1]
  simp

/-- `Good` gives what it asks of each live klong. -/
theorem Good.tr_kids {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) :
    ∀ t ∈ bounds (live n.ks) hi, KidOk s n.level n.leaf lo hi t.1 t.2.1 t.2.2 := by
  cases h with
  | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    rintro ⟨c, y, H⟩ ht
    obtain ⟨pre, post, he, hH⟩ := bounds_split ht
    simp only at he hH
    have hm : (c, y) ∈ live n.ks := by rw [he]; simp
    refine ⟨hhi c y hm, fun hl => hlo hl c y hm, fun hl hs => hval hl c y hm hs, ?_⟩
    intro hk
    obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm hk
    refine ⟨m, hm1, hm2, hm3, ?_⟩
    cases hl : n.leaf with
    | true => simpa using hseg hl c y hm (hk hl)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [hH]
      exact hkid hl pre c y post he

/-- And what each live klong asks gives `Good`. -/
theorem tr_good_of {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode}
    (hobj : s.obj u = some (.key n)) (hwf : klongsWf n.ks = true)
    (hk : ∀ t ∈ bounds (live n.ks) hi, KidOk s n.level n.leaf lo hi t.1 t.2.1 t.2.2) :
    Good s u lo hi := by
  have hk' : ∀ c y, (c, y) ∈ live n.ks → ∃ H, KidOk s n.level n.leaf lo hi c y H := by
    intro c y hm
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    exact ⟨_, hk _ (bounds_mem hi he)⟩
  refine Good.mk u lo hi n hobj hwf ?_ ?_ ?_ ?_ ?_ ?_
  · intro c y hm
    obtain ⟨H, h⟩ := hk' c y hm
    exact h.1
  · intro hl c y hm
    obtain ⟨H, h⟩ := hk' c y hm
    exact h.2.1 hl
  · intro hl c y hm hs
    obtain ⟨H, h⟩ := hk' c y hm
    exact h.2.2.1 hl hs
  · intro c y hm hl
    obtain ⟨H, h⟩ := hk' c y hm
    obtain ⟨m, hm1, hm2, hm3, _⟩ := h.2.2.2 hl
    exact ⟨m, hm1, hm2, hm3⟩
  · intro hl c y hm hs
    obtain ⟨H, h⟩ := hk' c y hm
    obtain ⟨m, _, _, _, hg⟩ := h.2.2.2 (fun _ => hs)
    simpa [hl] using hg
  · intro hl pre c y post he
    obtain ⟨m, _, _, _, hg⟩ := (hk _ (bounds_mem hi he)).2.2.2 (by simp [hl])
    simpa [hl] using hg

/-- A live klong whose child's subtree is unchanged, moved to another node or
range. -/
theorem KidOk.tr_move {A B : Tree} {lev : Nat} {leaf : Bool} {lo lo' : Nat}
    {hi hi' H H' : Option Nat} {c c' : Nat} {y : NodeId} (h : KidOk A lev leaf lo hi c y H)
    (ha : ∀ z ∈ reachAt A (A.fuel y) y, B.obj z = A.obj z) (hb : belowHi c' hi' = true)
    (hl : leaf = true → c' = c ∧ lo' ≤ c) (hk : leaf = false → max lo' c' = max lo c ∧ H' = H) :
    KidOk B lev leaf lo' hi' c' y H' := by
  obtain ⟨_, _, h3, h4⟩ := h
  have hy : B.obj y = A.obj y := ha y (tc_self _ _ _)
  refine ⟨hb, fun hl' => (hl hl').1 ▸ (hl hl').2, ?_, ?_⟩
  · intro hl' hs
    rw [(hl hl').1] at hs
    rw [hy]
    exact h3 hl' hs
  · intro hk'
    have hk'' : leaf = true → isLong c = true := by
      intro hl'
      have := hk' hl'
      rwa [(hl hl').1] at this
    obtain ⟨m, hm1, hm2, hm3, hg⟩ := h4 hk''
    refine ⟨m, hy ▸ hm1, hm2, hm3, ?_⟩
    cases hlf : leaf with
    | true =>
      simp only [hlf, ite_true] at hg ⊢
      exact hg.agree ha
    | false =>
      simp only [hlf, Bool.false_eq_true, ite_false] at hg ⊢
      obtain ⟨e1, e2⟩ := hk hlf
      rw [e1, e2]
      exact hg.agree ha

/-- The children of a sound node do not reach it: B may change it. -/
theorem Good.tr_kids_agree {A B : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A x lo hi) {nx : KNode} (hAx : A.obj x = some (.key nx))
    (ha : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live nx.ks) : ∀ z ∈ reachAt A (A.fuel y) y, B.obj z = A.obj z := by
  intro z hz
  rw [← hG.tc_kid_eq hAx hm] at hz
  refine ha z ?_ (fun h => hG.not_below hAx hm nx.level (h ▸ hz))
  rw [show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx]]
  exact tc_kid hAx hm hz

theorem tr_klongList_long {s s' : Tree} {leaf : Bool} {sub sub' : NodeId → List (Key × Nat)}
    {c : Nat} {x y : NodeId} (h1 : leaf = true → isLong c = true) (h2 : sub' y = sub x) :
    klongList s' leaf sub' c y = klongList s leaf sub c x := by
  unfold klongList
  cases leaf with
  | false => simp [h2]
  | true => simp [h1 rfl, h2]

/-- A copy: node y of B has the level, the kind and the live klongs of node x
of A, and B agrees with A below x. Then y is sound for every range x is, holds
what x holds, and reaches y and what x reaches below itself. -/
theorem tr_copy {A B : Tree} {x y : NodeId} {lo : Nat} {hi : Option Nat} (hG : Good A x lo hi)
    {nx : KNode} (hAx : A.obj x = some (.key nx)) {b : Nat}
    (hBy : NodeIs B y nx.level nx.leaf (live nx.ks) b)
    (ha : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z) :
    Good B y lo hi ∧ L B y = L A x ∧
      reachAt B (B.fuel y) y = y :: (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) := by
  obtain ⟨ny, hy1, hy2, hy3, hy4, hy5⟩ := hBy
  have hwf : klongsWf ny.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hy5
    exact hy5.1.2
  have hka := fun c z (hm : (c, z) ∈ live nx.ks) => hG.tr_kids_agree hAx ha hm
  have hGB : Good B y lo hi := by
    refine tr_good_of hy1 hwf ?_
    rw [hy2, hy3, hy4]
    intro t ht
    exact (hG.tr_kids hAx t ht).tr_move (hka _ _ (bounds_mem_live ht)) (hG.tr_kids hAx t ht).1
      (fun _ => ⟨rfl, (hG.tr_kids hAx t ht).2.1 ‹_›⟩) (fun _ => ⟨rfl, rfl⟩)
  refine ⟨hGB, ?_, ?_⟩
  · rw [hGB.L_eq hy1, hG.L_eq hAx, hy4, hy3]
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact tc_klongList (hka c z hm z (tc_self _ _ _)) (L_agree (hka c z hm))
  · rw [show B.fuel y = nx.level + 1 by simp [Tree.fuel, hy1, hy2], tc_key hy1, hy4]
    congr 1
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hG.tc_kid_eq hAx hm] at hz'
    exact hka c z hm z' hz'

theorem Sound.inPlace {M : Nat} {A B : Tree} {r x : NodeId} {C : List (Key × Nat)} {nx : KNode}
    (h : Sound M (some x) A r C) (hAx : A.obj x = some (.key nx))
    (hBx : NodeIs B x nx.level nx.leaf (live nx.ks) M)
    (hsame : ∀ z, z ≠ x → B.obj z = A.obj z) : Sound M none B r C := by
  obtain ⟨nb, hb1, hb2, hb3, hb4, hb5⟩ := id hBx
  have hs : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx, hb1]
    · rw [hsame z hzx]
      exact hz
  by_cases hx : x ∈ reachAt A (A.fuel r) r
  · obtain ⟨lo, hi, hg⟩ := h.good.tr_reach_good _ x hx nx hAx
    have hcopy := fun lo hi (hg : Good A x lo hi) => tr_copy hg hAx hBx (fun z _ hz => hsame z hz)
    have hk : KeepsKind A B x := by
      intro n hn
      rw [hAx] at hn
      cases hn
      exact ⟨nb, hb1, by omega, by rw [hb4]; exact id⟩
    have ha : Agree A B r x := fun z _ hz => hsame z (fun h => hz (h ▸ tc_self _ _ _))
    have hloc : ∀ lo' hi', Good A x lo' hi' → Good B x lo' hi' :=
      fun lo' hi' hg => (hcopy lo' hi' hg).1
    have hqk : ∃ n, A.obj x = some (.key n) := ⟨nx, hAx⟩
    have hRx : reachAt B (B.fuel x) x = reachAt A (A.fuel x) x := by
      rw [(hcopy lo hi hg).2.2, show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx]
    obtain ⟨hTB, hmem⟩ := ctx_reach h.good h.tree hx ha hk hloc hqk
      (hRx ▸ h.good.tr_nodup h.tree hx) (fun z hz => Or.inl (hRx ▸ hz))
    refine ⟨?_, Good.ctx h.good h.tree hx ha hk hloc hqk, ?_, ?_, hTB⟩
    · obtain ⟨n, ho, hne⟩ := h.key
      by_cases hrx : r = x
      · rw [hrx] at ho ⊢
        rw [hAx] at ho
        cases ho
        exact ⟨nb, hb1, by rw [hb3, hb4]; exact hne⟩
      · exact ⟨n, (hsame r hrx).trans ho, hne⟩
    · intro z hz m hm
      by_cases hzx : z = x
      · rw [hzx, hb1] at hm
        cases hm
        simpa using hb5
      · have hzA : z ∈ reachAt A (A.fuel r) r := by
          rcases hmem z hz with ⟨h1, _⟩ | h1
          · exact h1
          · rw [hRx] at h1
            exact h.good.tr_closed hx h1
        rw [hsame z hzx] at hm
        have := h.nodes z hzA m hm
        simp only [Option.some.injEq, Ne.symm hzx, ite_false] at this
        simpa using tr_nodeOk this (le_refl _) hs
    · rw [ctx_L h.good h.tree hx ha hk hloc hqk (hcopy lo hi hg).2.1]
      exact h.holds
  · have ha : ∀ z ∈ reachAt A (A.fuel r) r, B.obj z = A.obj z :=
      fun z hz => hsame z (fun h => hx (h ▸ hz))
    have hR : reachAt B (B.fuel r) r = reachAt A (A.fuel r) r := by
      rw [show B.fuel r = A.fuel r by simp [Tree.fuel, ha r (tc_self _ _ _)]]
      exact reachAt_agree _ _ ha
    refine (h.agree ha hs).tr_drop ?_
    intro z hz hzx
    cases hzx
    rw [hR] at hz
    exact hx hz

/-! ## Along a route: the local step asked only for ranges that hold the key -/

/-- The range [lo, hi) holds the key's first segment. -/
def KeyIn (k : Key) (lo : Nat) (hi : Option Nat) : Prop :=
  ∀ c rest, k = c :: rest → lo ≤ c ∧ belowHi c hi = true

theorem Good.tr_wf {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) : klongsWf n.ks = true := by
  cases h with
  | mk _ _ _ n' hobj' hwf =>
    rw [hobj] at hobj'
    cases hobj'
    exact hwf

theorem Good.tr_kid {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) (hl : n.leaf = false)
    {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post) : Good s y (max lo c) (nextHi post hi) := by
  obtain ⟨_, _, _, _, hg⟩ := (h.tr_kids hobj _ (bounds_mem hi he)).2.2.2 (by simp [hl])
  simpa [hl] using hg

theorem Good.tr_seg {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) (hl : n.leaf = true) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) (hlong : isLong c = true) : Good s y 0 none := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem hm
  obtain ⟨_, _, _, _, hg⟩ := (h.tr_kids hobj _ (bounds_mem hi he)).2.2.2 (fun _ => hlong)
  simpa [hl] using hg

/-- An inner step of a route keeps the key's first segment in the range. -/
theorem tr_keyIn_kid {n : KNode} {lo : Nat} {hi : Option Nat} {c cv : Nat} {rest : Key}
    {pre post : List (Nat × NodeId)} {y : NodeId} (hK : KeyIn (cv :: rest) lo hi) (hc : c ≤ cv)
    (hlast : ∀ c' y', (c', y') ∈ live n.ks → c' ≤ cv → c' ≤ c)
    (he : live n.ks = pre ++ (c, y) :: post) : KeyIn (cv :: rest) (max lo c) (nextHi post hi) := by
  intro c0 r0 h0
  injection h0 with h1 _
  subst h1
  obtain ⟨hlo, hhi⟩ := hK _ _ rfl
  refine ⟨max_le hlo hc, ?_⟩
  cases post with
  | nil => exact hhi
  | cons b post =>
    obtain ⟨_, hpost, _⟩ := live_split he
    have hb : (b.1, b.2) ∈ live n.ks := by rw [he]; simp
    have h1 : c < b.1 := hpost b (by simp)
    simp only [nextHi, belowHi, decide_eq_true_eq]
    by_contra hcon
    have := hlast b.1 b.2 hb (by omega)
    omega

theorem KidOk.tr_up {A B : Tree} {lev : Nat} {leaf : Bool} {lo : Nat} {hi H : Option Nat}
    {c : Nat} {y : NodeId} (h : KidOk A lev leaf lo hi c y H)
    (hlong : leaf = true → isLong c = true) (hk : KeepsKind A B y)
    (hy : Good A y (if leaf then 0 else max lo c) (if leaf then none else H) →
      Good B y (if leaf then 0 else max lo c) (if leaf then none else H)) :
    KidOk B lev leaf lo hi c y H := by
  obtain ⟨h1, h2, _, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro hl hs
    rw [hlong hl] at hs
    cases hs
  intro _
  obtain ⟨m, hm1, hm2, hm3, hg⟩ := h4 hlong
  obtain ⟨m', hm1', hm2', hm3'⟩ := hk m hm1
  exact ⟨m', hm1', by omega, hm3' hm3, hy hg⟩

/-- One step up: u is sound in B if the child y that reaches q is, for the
ranges u gives it. -/
theorem tr_good_up {A B : Tree} {u q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A u lo hi) {n : KNode} (hobj : A.obj u = some (.key n))
    (hT : (reachAt A (A.fuel u) u).Nodup) (ha : Agree A B u q)
    (hqk : ∃ m, A.obj q = some (.key m)) (hk : KeepsKind A B q)
    {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post) (hqy : q ∈ reachAt A n.level y)
    (hy : ∀ pre' post', live n.ks = pre' ++ (c, y) :: post' →
      Good A y (if n.leaf then 0 else max lo c) (if n.leaf then none else nextHi post' hi) →
      Good B y (if n.leaf then 0 else max lo c) (if n.leaf then none else nextHi post' hi)) :
    Good B u lo hi := by
  obtain ⟨hBu, hside, hBy, hlong, _, _, _⟩ := hG.tc_step hobj hT ha hqk he hqy
  have hKK : KeepsKind A B y := by
    by_cases hyq : y = q
    · rw [hyq]
      exact hk
    · intro m hm
      exact ⟨m, (hBy hyq).trans hm, le_refl _, id⟩
  have hside' : ∀ c' y', (c', y') ∈ pre ++ post →
      ∀ z ∈ reachAt A (A.fuel y') y', B.obj z = A.obj z := by
    intro c' y' h z hz
    have hm' : (c', y') ∈ live n.ks := by
      rw [he]
      rcases List.mem_append.mp h with h | h <;> simp [h]
    rw [← hG.tc_kid_eq hobj hm'] at hz
    exact hside c' y' h z hz
  refine tr_good_of (hBu.trans hobj) (hG.tr_wf hobj) ?_
  rintro ⟨c', y', H⟩ ht
  have hA := hG.tr_kids hobj _ ht
  have hmem := bounds_mem_live ht
  simp only at hmem hA ⊢
  rw [he] at hmem
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with h1 | h1 | h1
  · exact hA.tr_move (hside' _ _ (List.mem_append_left _ h1)) hA.1 (fun hl => ⟨rfl, hA.2.1 hl⟩)
      (fun _ => ⟨rfl, rfl⟩)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    obtain ⟨pre', post', he', hH⟩ := bounds_split ht
    simp only at he' hH
    rw [hH] at hA ⊢
    exact hA.tr_up hlong hKK (hy pre' post' he')
  · exact hA.tr_move (hside' _ _ (List.mem_append_right _ h1)) hA.1 (fun hl => ⟨rfl, hA.2.1 hl⟩)
      (fun _ => ⟨rfl, rfl⟩)

/-- Along a route, r is sound in B if q is for the ranges that hold the key
left at q. -/
theorem tr_route_good {A B : Tree} {q : NodeId} (hk : KeepsKind A B q) {k' : Key}
    (hloc : ∀ lo' hi', Good A q lo' hi' → KeyIn k' lo' hi' → Good B q lo' hi')
    {u : NodeId} {k : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi → KeyIn k lo hi →
      (reachAt A (A.fuel u) u).Nodup → Agree A B u q → Good B u lo hi := by
  induction hr with
  | here q k => intro lo hi hG hK _ _; exact hloc lo hi hG hK
  | inner u n c y cv rest q k' hobj hl hm hc hlast hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (by simp [hl])
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨_, _, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hgq.obj he hqy
    refine tr_good_up hG hobj hT ha hgq.obj hk he hqy ?_
    intro pre' post' he' hgy
    simp only [hl, Bool.false_eq_true, ite_false] at hgy ⊢
    exact ih hk hloc hgy (tr_keyIn_kid hK hc hlast he') hTy hay
  | leaf u n c y rest q k' hobj hl hm hlong hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨_, _, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hgq.obj he hqy
    refine tr_good_up hG hobj hT ha hgq.obj hk he hqy ?_
    intro pre' post' _ hgy
    simp only [hl, ite_true] at hgy ⊢
    exact ih hk hloc hgy (fun _ _ _ => ⟨Nat.zero_le _, rfl⟩) hTy hay

/-- Along a route, the node reached holds the key left, in a range that holds
it. -/
theorem Route.tr_target {A : Tree} {u q : NodeId} {k k' : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi → KeyIn k lo hi →
      ∃ lo' hi', Good A q lo' hi' ∧ KeyIn k' lo' hi' := by
  induction hr with
  | here q k => intro lo hi hG hK; exact ⟨lo, hi, hG, hK⟩
  | inner u n c y cv rest q k' hobj hl hm hc hlast _ ih =>
    intro lo hi hG hK
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    exact ih (hG.tr_kid hobj hl he) (tr_keyIn_kid hK hc hlast he)
  | leaf u n c y rest q k' hobj hl hm hlong _ ih =>
    intro lo hi hG _
    exact ih (hG.tr_seg hobj hl hm hlong) (fun _ _ _ => ⟨Nat.zero_le _, rfl⟩)

/-- Along a route, r holds the keys with the change F if q does. -/
theorem tr_route_L {A B : Tree} {q : NodeId} (hk : KeepsKind A B q) {k' : Key}
    (hloc : ∀ lo' hi', Good A q lo' hi' → KeyIn k' lo' hi' → Good B q lo' hi')
    {F : Key → List (Key × Nat) → List (Key × Nat)} (hF : LocalTo F)
    (hL : L B q = F k' (L A q)) {u : NodeId} {k : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi → KeyIn k lo hi →
      (reachAt A (A.fuel u) u).Nodup → Agree A B u q → L B u = F k (L A u) := by
  induction hr with
  | here q k => intro _ _ _ _ _ _; exact hL
  | inner u n c y cv rest q k' hobj hl hm hc hlast hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (by simp [hl])
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    have hqk := hgq.obj
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hGB := tr_route_good hk hloc
      (Route.inner u n c y cv rest q k' hobj hl hm hc hlast hry) hG hK hT ha
    obtain ⟨h1, h2⟩ := tc_L_split hG hGB hobj hBu he hside
    have hmB : klongList B n.leaf (L B) c y = L B y := by simp [klongList, hl]
    have hmA : klongList A n.leaf (L A) c y = L A y := by simp [klongList, hl]
    rw [h1, h2, hmB, hmA,
      ih hk hloc hL (hG.tr_kid hobj hl he) (tr_keyIn_kid hK hc hlast he) hTy hay]
    have hflat : ∀ l : List (Nat × NodeId),
        l.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2) =
          l.flatMap (fun cy => L A cy.2) := by
      intro l
      apply List.flatMap_congr
      intro cy _
      simp [klongList, hl]
    rw [hflat pre, hflat post]
    obtain ⟨_, hpost, _⟩ := live_split he
    have hmid := hF.mid (cv :: rest) (pre.flatMap (fun cy => L A cy.2)) (L A y)
      (post.flatMap (fun cy => L A cy.2)) ?_ ?_
    · simp only [List.append_assoc] at hmid
      rw [hmid]
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, y0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      obtain ⟨d, r', rfl, hd⟩ := hG.tc_kid_upper hobj hl he h0 k0 v0 hkv
      exact cons_lt_cons_of_lt (by omega) _ _
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, y2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hm2 : (c2, y2) ∈ live n.ks := by rw [he]; simp [h2]
      have hc2 : c < c2 := hpost (c2, y2) h2
      have hcv : cv < c2 := by
        by_contra hcon
        have := hlast c2 y2 hm2 (by omega)
        omega
      obtain ⟨d, r', rfl, hd⟩ := hG.kid_lower hobj hl hm2 k2 v2 hkv
      exact cons_lt_cons_of_lt (by omega) _ _
  | leaf u n c y rest q k' hobj hl hm hlong hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    have hqk := hgq.obj
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hGB := tr_route_good hk hloc (Route.leaf u n c y rest q k' hobj hl hm hlong hry)
      hG hK hT ha
    obtain ⟨h1, h2⟩ := tc_L_split hG hGB hobj hBu he hside
    have hmB : klongList B n.leaf (L B) c y = (L B y).map (fun kv => (c :: kv.1, kv.2)) := by
      simp [klongList, hl, hlong]
    have hmA : klongList A n.leaf (L A) c y = (L A y).map (fun kv => (c :: kv.1, kv.2)) := by
      simp [klongList, hl, hlong]
    rw [h1, h2, hmB, hmA,
      ih hk hloc hL (hG.tr_seg hobj hl hm hlong) (fun _ _ _ => ⟨Nat.zero_le _, rfl⟩) hTy hay,
      ← hF.seg c rest (L A y)]
    obtain ⟨hpre, hpost, _⟩ := live_split he
    have hmid := hF.mid (c :: rest)
      (pre.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2))
      ((L A y).map (fun kv => (c :: kv.1, kv.2)))
      (post.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2)) ?_ ?_
    · simp only [List.append_assoc] at hmid
      rw [hmid]
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, y0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      have hc0 : c0 < c := hpre (c0, y0) h0
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc0 _ _
      · exact cons_lt_cons_of_lt hc0 _ _
      · rw [hl] at hl'
        cases hl'
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, y2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hc2 : c < c2 := hpost (c2, y2) h2
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc2 _ _
      · exact cons_lt_cons_of_lt hc2 _ _
      · rw [hl] at hl'
        cases hl'

/-- One step up of the split of what is reached around q. -/
theorem tr_split_step {A B : Tree} {u q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A u lo hi) {n : KNode} (hobj : A.obj u = some (.key n))
    (hT : (reachAt A (A.fuel u) u).Nodup) (ha : Agree A B u q)
    (hqk : ∃ m, A.obj q = some (.key m)) (hk : KeepsKind A B q)
    {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post) (hqy : q ∈ reachAt A n.level y)
    {lo' : Nat} {hi' : Option Nat} (hGBy : Good B y lo' hi')
    (hIH : ∃ P S, reachAt A (A.fuel y) y = P ++ reachAt A (A.fuel q) q ++ S ∧
      reachAt B (B.fuel y) y = P ++ reachAt B (B.fuel q) q ++ S) :
    ∃ P S, reachAt A (A.fuel u) u = P ++ reachAt A (A.fuel q) q ++ S ∧
      reachAt B (B.fuel u) u = P ++ reachAt B (B.fuel q) q ++ S := by
  have hfuel : A.fuel u = n.level + 1 := by simp [Tree.fuel, hobj]
  have hm : (c, y) ∈ live n.ks := by rw [he]; simp
  obtain ⟨hBu, hside, hBy, hlong, _, _, _⟩ := hG.tc_step hobj hT ha hqk he hqy
  have hBfuel : B.fuel u = n.level + 1 := by simp [Tree.fuel, hBu, hobj]
  obtain ⟨P, S, hPA, hPB⟩ := hIH
  obtain ⟨m, _, _, hm1, hm2, _, _⟩ := hG.child hobj hm hlong
  have hBfy : B.fuel y ≤ n.level := by
    by_cases hyq : y = q
    · rw [hyq] at hm1 ⊢
      obtain ⟨n'', h1, h2, _⟩ := hk m hm1
      simp only [Tree.fuel, h1]
      omega
    · simp only [Tree.fuel, hBy hyq, hm1]
      omega
  have hyB : reachAt B n.level y = reachAt B (B.fuel y) y := hGBy.reachAt_eq n.level hBfy
  have hyA : reachAt A n.level y = reachAt A (A.fuel y) y := hG.tc_kid_eq hobj hm
  have hsB : ∀ l : List (Nat × NodeId), (∀ cy ∈ l, cy ∈ pre ++ post) →
      l.flatMap (fun cy => reachAt B n.level cy.2) =
        l.flatMap (fun cy => reachAt A n.level cy.2) := by
    intro l hl'
    apply List.flatMap_congr
    rintro ⟨c', y'⟩ h
    exact reachAt_agree n.level y' (hside c' y' (hl' _ h))
  refine ⟨u :: pre.flatMap (fun cy => reachAt A n.level cy.2) ++ P,
    S ++ post.flatMap (fun cy => reachAt A n.level cy.2), ?_, ?_⟩
  · rw [hfuel, tc_key hobj, he, List.flatMap_append, List.flatMap_cons, hyA, hPA]
    simp
  · rw [hBfuel, tc_key (hBu.trans hobj), he, List.flatMap_append, List.flatMap_cons, hyB, hPB,
      hsB pre (fun cy h => List.mem_append_left _ h),
      hsB post (fun cy h => List.mem_append_right _ h)]
    simp

/-- Along a route, what is reached from u in A and in B: the same before and
after what is reached from q. -/
theorem tr_route_split {A B : Tree} {q : NodeId} (hk : KeepsKind A B q) {k' : Key}
    (hloc : ∀ lo' hi', Good A q lo' hi' → KeyIn k' lo' hi' → Good B q lo' hi')
    {u : NodeId} {k : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi → KeyIn k lo hi →
      (reachAt A (A.fuel u) u).Nodup → Agree A B u q →
      ∃ P S, reachAt A (A.fuel u) u = P ++ reachAt A (A.fuel q) q ++ S ∧
        reachAt B (B.fuel u) u = P ++ reachAt B (B.fuel q) q ++ S := by
  induction hr with
  | here q k => intro _ _ _ _ _ _; exact ⟨[], [], by simp, by simp⟩
  | inner u n c y cv rest q k' hobj hl hm hc hlast hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (by simp [hl])
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨_, _, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hgq.obj he hqy
    have hgy := hG.tr_kid hobj hl he
    have hKy := tr_keyIn_kid hK hc hlast he
    exact tr_split_step hG hobj hT ha hgq.obj hk he hqy
      (tr_route_good hk hloc hry hgy hKy hTy hay) (ih hk hloc hgy hKy hTy hay)
  | leaf u n c y rest q k' hobj hl hm hlong hry ih =>
    intro lo hi hG hK hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨_, _, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hgq.obj he hqy
    have hgy := hG.tr_seg hobj hl hm hlong
    have hKy : KeyIn rest 0 none := fun _ _ _ => ⟨Nat.zero_le _, rfl⟩
    exact tr_split_step hG hobj hT ha hgq.obj hk he hqy
      (tr_route_good hk hloc hry hgy hKy hTy hay) (ih hk hloc hgy hKy hTy hay)

/-- TREE in B from the split around q. -/
theorem tr_split_concl {A B : Tree} {r q : NodeId} {P S : List NodeId}
    (hA : reachAt A (A.fuel r) r = P ++ reachAt A (A.fuel q) q ++ S)
    (hB : reachAt B (B.fuel r) r = P ++ reachAt B (B.fuel q) q ++ S)
    (hT : (reachAt A (A.fuel r) r).Nodup) (hR : (reachAt B (B.fuel q) q).Nodup)
    (hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r) :
    (reachAt B (B.fuel r) r).Nodup ∧
      ∀ z ∈ reachAt B (B.fuel r) r,
        (z ∈ reachAt A (A.fuel r) r ∧ z ∉ reachAt A (A.fuel q) q) ∨ z ∈ reachAt B (B.fuel q) q := by
  have hp : ∀ X : List NodeId, (P ++ X ++ S).Perm (P ++ S ++ X) := fun X => by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := X) (l₂ := S)).append_left P
  rw [hA] at hT hnew
  rw [hB, hA]
  have hT' := (hp _).nodup_iff.mp hT
  rw [List.nodup_append] at hT'
  constructor
  · rw [(hp _).nodup_iff, List.nodup_append]
    refine ⟨hT'.1, hR, ?_⟩
    intro a ha b hb hab
    subst hab
    rcases hnew a hb with h | h
    · exact hT'.2.2 a ha a h rfl
    · apply h
      simp only [List.mem_append] at ha ⊢
      tauto
  · intro z hz
    simp only [List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl ⟨by simp [hz], fun h => hT'.2.2 z (by simp [hz]) z h rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨by simp [hz], fun h => hT'.2.2 z (by simp [hz]) z h rfl⟩

/-! ## A put -/

theorem tr_nodup_swap {α : Type} {a b : α} {P O S : List α} (h : (a :: (P ++ (O ++ S))).Nodup)
    (hb : b ∉ a :: (P ++ (O ++ S))) : (a :: (P ++ b :: S)).Nodup := by
  have h1 : (a :: (P ++ S)).Nodup := h.sublist
    (List.Sublist.cons_cons a ((List.Sublist.refl P).append (List.sublist_append_right O S)))
  have h2 : b ∉ a :: (P ++ S) := fun hm => hb (by simp at hm ⊢; tauto)
  rw [List.nodup_cons] at h1 ⊢
  rw [List.nodup_middle, List.nodup_cons]
  simp only [List.mem_cons, List.mem_append, not_or] at h1 h2 ⊢
  exact ⟨⟨h1.1.1, fun e => h2.1 e.symm, h1.1.2⟩, ⟨h2.2.1, h2.2.2⟩, h1.2⟩

/-- Where `insertCv` puts the pair in a list in order: between the pairs below
and above its compare value, in place of the pair of that compare value if
there is one. -/
theorem tr_insertCv (c : Nat) (y : NodeId) :
    ∀ {l : List (Nat × NodeId)}, l.Pairwise CvLt →
      ∃ pre old post, l = pre ++ old ++ post ∧ (old = [] ∨ ∃ y0, old = [(c, y0)]) ∧
        insertCv c y l = pre ++ (c, y) :: post ∧ (∀ a ∈ pre, a.1 < c) ∧ (∀ b ∈ post, c < b.1)
  | [], _ => ⟨[], [], [], rfl, Or.inl rfl, rfl, by simp, by simp⟩
  | (c', y') :: r, h => by
    rw [List.pairwise_cons] at h
    unfold insertCv
    split
    · rename_i hlt
      refine ⟨[], [], (c', y') :: r, rfl, Or.inl rfl, rfl, by simp, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hlt
      · exact lt_trans hlt (h.1 b hb)
    · split
      · rename_i heq
        subst heq
        exact ⟨[], [(c, y')], r, rfl, Or.inr ⟨y', rfl⟩, rfl, by simp, fun b hb => h.1 b hb⟩
      · rename_i hnlt hne
        obtain ⟨pre, old, post, h1, h2, h3, h4, h5⟩ := tr_insertCv c y h.2
        refine ⟨(c', y') :: pre, old, post, by rw [h1]; rfl, h2, by rw [h3]; rfl, ?_, h5⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · show c' < c
          omega
        · exact h4 a ha

theorem tr_mapPut_old {s : Tree} {sub : NodeId → List (Key × Nat)} {cv hval : Nat}
    (hcv : isLong cv = false) {old : List (Nat × NodeId)}
    (hold : old = [] ∨ ∃ y0, old = [(cv, y0)]) :
    mapPut [cv] hval (old.flatMap (fun cy => klongList s true sub cy.1 cy.2)) = [([cv], hval)] := by
  rcases hold with rfl | ⟨y0, rfl⟩
  · rfl
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, klongList, hcv, ite_true,
      Bool.false_eq_true, ite_false]
    split <;> simp [mapPut, keyLt]

theorem Sound.put {M : Nat} {A B : Tree} {r x v : NodeId} {C : List (Key × Nat)} {nx : KNode}
    {k : Key} {cv hval : Nat} (h : Sound M none A r C) (hr : Route A r k x [cv])
    (hAx : A.obj x = some (.key nx)) (hleaf : nx.leaf = true) (hcv : isLong cv = false)
    (hv : A.obj v = none) (hBv : B.obj v = some (.val hval))
    (hBx : NodeIs B x nx.level true (insertCv cv v (live nx.ks)) (M + 3))
    (hsame : ∀ z, z ≠ x → z ≠ v → B.obj z = A.obj z) :
    Sound M (some x) B r (mapPut k hval C) ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = v := by
  obtain ⟨nb, hb1, hb2, hb3, hb4, hb5⟩ := hBx
  have hG := h.good
  have hK0 : KeyIn k 0 none := fun _ _ _ => ⟨Nat.zero_le _, rfl⟩
  have hxr := (hr.tc_target hG).2
  obtain ⟨lox, hix, hgx, hKx⟩ := hr.tr_target hG hK0
  have hvA : v ∉ reachAt A (A.fuel r) r := by
    intro hv'
    have := hG.tr_exists _ v hv'
    simp [hv] at this
  have hvx : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ v :=
    fun z hz hzv => hvA (hzv ▸ hG.tr_closed hxr hz)
  have hxA : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z :=
    fun z hz hzx => hsame z hzx (hvx z hz)
  have hka := fun c z (hm : (c, z) ∈ live nx.ks) => hgx.tr_kids_agree hAx hxA hm
  obtain ⟨pre, old, post, hlv, hold, hins, hpre, hpost⟩ := tr_insertCv cv v (live_sorted nx.ks)
  rw [hins] at hb4
  have hmpre : ∀ a ∈ pre, a ∈ live nx.ks := fun a ha => by rw [hlv]; simp [ha]
  have hmpost : ∀ a ∈ post, a ∈ live nx.ks := fun a ha => by rw [hlv]; simp [ha]
  have hwf : klongsWf nb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hb5
    exact hb5.1.2
  have hloc : ∀ lo' hi', Good A x lo' hi' → KeyIn [cv] lo' hi' → Good B x lo' hi' := by
    intro lo' hi' hg hK
    obtain ⟨hK1, hK2⟩ := hK cv [] rfl
    have hold' : ∀ t : Nat × NodeId × Option Nat, (t.1, t.2.1) ∈ live nx.ks →
        KidOk B nx.level true lo' hi' t.1 t.2.1 t.2.2 := by
      rintro ⟨c, z, H⟩ hm
      obtain ⟨p1, p2, he⟩ := List.append_of_mem hm
      have hA := hg.tr_kids hAx _ (bounds_mem hi' he)
      rw [hleaf] at hA
      exact hA.tr_move (hka _ _ hm) hA.1 (fun _ => ⟨rfl, hA.2.1 rfl⟩) (fun h => by cases h)
    refine tr_good_of hb1 hwf ?_
    rw [hb4, hb2, hb3, bounds_append]
    intro t ht
    simp only [bounds, List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · exact hold' t (hmpre _ (bounds_mem_live ht))
    · refine ⟨hK2, fun _ => hK1, fun _ _ => ⟨hval, hBv⟩, fun hk => ?_⟩
      have := hk rfl
      rw [hcv] at this
      cases this
    · exact hold' t (hmpost _ (bounds_mem_live ht))
  have hk : KeepsKind A B x := by
    intro n hn
    rw [hAx] at hn
    cases hn
    exact ⟨nb, hb1, by omega, fun _ => by rw [hb4]; simp⟩
  have ha : Agree A B r x :=
    fun z hz hzx => hsame z (fun h => hzx (h ▸ tc_self _ _ _)) (fun h => hvA (h ▸ hz))
  have hGB := tr_route_good hk hloc hr hG hK0 h.tree ha
  have hgBx := hloc lox hix hgx hKx
  -- what x holds
  have hL : L B x = mapPut [cv] hval (L A x) := by
    rw [hgBx.L_eq hb1, hgx.L_eq hAx, hb4, hb3, hlv, hleaf]
    simp only [List.flatMap_append, List.flatMap_cons]
    have hE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ live nx.ks) →
        l.flatMap (fun cy => klongList B true (L B) cy.1 cy.2) =
          l.flatMap (fun cy => klongList A true (L A) cy.1 cy.2) := by
      intro l hl
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hka c z (hl _ hm) z (tc_self _ _ _)) (L_agree (hka c z (hl _ hm)))
    have hv' : klongList B true (L B) cv v = [([cv], hval)] := by simp [klongList, hcv, hBv]
    rw [hE pre hmpre, hE post hmpost, hv']
    have hmid := (mapPut_local hval).mid [cv]
      (pre.flatMap (fun cy => klongList A true (L A) cy.1 cy.2))
      (old.flatMap (fun cy => klongList A true (L A) cy.1 cy.2))
      (post.flatMap (fun cy => klongList A true (L A) cy.1 cy.2)) ?_ ?_
    · simp only [List.append_assoc] at hmid ⊢
      rw [hmid, tr_mapPut_old hcv hold]
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, z0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      have hc0 : c0 < cv := hpre (c0, z0) h0
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc0 _ _
      · exact cons_lt_cons_of_lt hc0 _ _
      · cases hl'
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, z2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hc2 : cv < c2 := hpost (c2, z2) h2
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc2 _ _
      · exact cons_lt_cons_of_lt hc2 _ _
      · cases hl'
  -- what x reaches
  have hRE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ live nx.ks) →
      l.flatMap (fun cy => reachAt B nx.level cy.2) =
        l.flatMap (fun cy => reachAt A nx.level cy.2) := by
    intro l hl
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hgx.tc_kid_eq hAx (hl _ hm)] at hz'
    exact hka c z (hl _ hm) z' hz'
  have hRB : reachAt B (B.fuel x) x = x :: (pre.flatMap (fun cy => reachAt A nx.level cy.2) ++
      v :: post.flatMap (fun cy => reachAt A nx.level cy.2)) := by
    rw [show B.fuel x = nx.level + 1 by simp [Tree.fuel, hb1, hb2], tc_key hb1, hb4,
      List.flatMap_append, List.flatMap_cons, hRE pre hmpre, hRE post hmpost, tc_val hBv]
    rfl
  have hRA : reachAt A (A.fuel x) x = x :: (pre.flatMap (fun cy => reachAt A nx.level cy.2) ++
      (old.flatMap (fun cy => reachAt A nx.level cy.2) ++
        post.flatMap (fun cy => reachAt A nx.level cy.2))) := by
    rw [show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx, hlv,
      List.flatMap_append, List.flatMap_append, List.append_assoc]
  have hTx := hG.tr_nodup h.tree hxr
  have hR : (reachAt B (B.fuel x) x).Nodup := by
    rw [hRB]
    rw [hRA] at hTx
    refine tr_nodup_swap hTx (fun hm => ?_)
    rw [← hRA] at hm
    exact hvx v hm rfl
  have hxmem : ∀ z ∈ reachAt B (B.fuel x) x, z ∈ reachAt A (A.fuel x) x ∨ z = v := by
    intro z hz
    rw [hRB] at hz
    rw [hRA]
    simp only [List.mem_cons, List.mem_append] at hz ⊢
    tauto
  have hnew : ∀ z ∈ reachAt B (B.fuel x) x,
      z ∈ reachAt A (A.fuel x) x ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hxmem z hz with h' | rfl
    · exact Or.inl h'
    · exact Or.inr hvA
  obtain ⟨P, S, hPA, hPB⟩ := tr_route_split hk hloc hr hG hK0 h.tree ha
  obtain ⟨hTB, hmemB⟩ := tr_split_concl hPA hPB h.tree hR hnew
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = v := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hxmem z h1 with h2 | h2
      · exact Or.inl (hG.tr_closed hxr h2)
      · exact Or.inr h2
  have hs : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx, hb1]
    · by_cases hzv : z = v
      · rw [hzv, hv] at hz
        cases hz
      · rw [hsame z hzx hzv]
        exact hz
  refine ⟨⟨?_, hGB, ?_, ?_, hTB⟩, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrx : r = x
    · rw [hrx] at ho ⊢
      exact ⟨nb, hb1, Or.inl hb3⟩
    · have hrv : r ≠ v := by
        intro hrv
        rw [hrv, hv] at ho
        cases ho
      exact ⟨n, (hsame r hrx hrv).trans ho, hne⟩
  · intro z hz m hm
    by_cases hzx : z = x
    · rw [hzx, hb1] at hm
      cases hm
      simpa [hzx] using hb5
    · rcases hmem z hz with hzA | rfl
      · have hzv : z ≠ v := fun h' => hvA (h' ▸ hzA)
        rw [hsame z hzx hzv] at hm
        have := h.nodes z hzA m hm
        simp only [reduceCtorEq, ite_false] at this
        exact tr_nodeOk this (by split <;> omega) hs
      · rw [hBv] at hm
        cases hm
  · rw [tr_route_L hk hloc (mapPut_local hval) hL hr hG hK0 h.tree ha, h.holds]

/-! ## Splits -/

/-- An old node reached in A, unchanged in B, meets the size M in B. -/
theorem Sound.tr_old {M : Nat} {ex : Option NodeId} {A B : Tree} {r : NodeId}
    {C : List (Key × Nat)} (h : Sound M ex A r C)
    (hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true) {z : NodeId}
    (hz : z ∈ reachAt A (A.fuel r) r) (hex : ex ≠ some z) (hBz : B.obj z = A.obj z) {m : KNode}
    (hm : B.obj z = some (.key m)) {b : Nat} (hb : M ≤ b) : nodeOk ⟨b⟩ B m = true := by
  rw [hBz] at hm
  have := h.nodes z hz m hm
  simp only [hex, ↓reduceIte] at this
  exact tr_nodeOk this hb hs

theorem tr_nodup_replace {α : Type} {a b : α} {P S : List α} (h : (P ++ a :: S).Nodup)
    (hb : b ∉ P ++ S) : (P ++ b :: S).Nodup := by
  rw [List.nodup_middle, List.nodup_cons] at h ⊢
  exact ⟨hb, h.2⟩

theorem tr_insertCv_replace {c : Nat} {x y : NodeId} :
    ∀ {pre : List (Nat × NodeId)} (post : List (Nat × NodeId)), (∀ a ∈ pre, a.1 < c) →
      insertCv c y (pre ++ (c, x) :: post) = pre ++ (c, y) :: post
  | [], post, _ => by simp [insertCv]
  | a :: pre, post, h => by
    have h1 := h a List.mem_cons_self
    obtain ⟨a1, a2⟩ := a
    simp only at h1
    simp only [List.cons_append, insertCv, show ¬ c < a1 by omega, show c ≠ a1 by omega,
      ite_false]
    rw [tr_insertCv_replace post (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem tr_insertCv_insert {c : Nat} {y : NodeId} {post : List (Nat × NodeId)}
    (hpost : ∀ b ∈ post, c < b.1) :
    ∀ {pre : List (Nat × NodeId)}, (∀ a ∈ pre, a.1 < c) →
      insertCv c y (pre ++ post) = pre ++ (c, y) :: post
  | [], _ => by
    cases post with
    | nil => rfl
    | cons b post =>
      obtain ⟨b1, b2⟩ := b
      have : c < b1 := hpost (b1, b2) List.mem_cons_self
      simp [insertCv, this]
  | a :: pre, h => by
    have h1 := h a List.mem_cons_self
    obtain ⟨a1, a2⟩ := a
    simp only at h1
    simp only [List.cons_append, insertCv, show ¬ c < a1 by omega, show c ≠ a1 by omega,
      ite_false]
    rw [tr_insertCv_insert hpost (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The other children of q: what they reach is not q, nor reached from x,
and exists. -/
theorem Good.tr_side {A : Tree} {q x : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A q lo hi) {nq : KNode} (hAq : A.obj q = some (.key nq))
    (hT : (reachAt A (A.fuel q) q).Nodup) {pre post : List (Nat × NodeId)} {k1 : Nat}
    (he : live nq.ks = pre ++ (k1, x) :: post) {c : Nat} {z z' : NodeId}
    (hb : (c, z) ∈ pre ++ post) (hz : z' ∈ reachAt A nq.level z) :
    z' ≠ q ∧ z' ∉ reachAt A nq.level x ∧ (A.obj z').isSome = true := by
  have hm : (c, z) ∈ live nq.ks := by
    rw [he]
    rcases List.mem_append.mp hb with h | h <;> simp [h]
  have hfuel : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hRA := tc_key hAq nq.level
  rw [← hfuel] at hRA
  have hT' := (List.nodup_cons.mp (hRA ▸ hT)).2
  refine ⟨fun e => hG.not_below hAq hm nq.level (e ▸ hz), fun hx => ?_, ?_⟩
  · exact tc_nodup_mid (g := fun cy => reachAt A nq.level cy.2) hT' he hb hz hx
  · refine hG.tr_exists (A.fuel q) z' ?_
    rw [hfuel]
    exact tc_kid hAq hm hz

theorem Sound.timeSplit {M : Nat} {ex' : Option NodeId} {A B : Tree} {r q x y : NodeId}
    {C : List (Key × Nat)} {nq nx : KNode} {k1 : Nat}
    (h : Sound M (some x) A r C) (hq : q ∈ reachAt A (A.fuel r) r)
    (hAq : A.obj q = some (.key nq)) (hk1 : (k1, x) ∈ live nq.ks)
    (hAx : A.obj x = some (.key nx)) (hy : A.obj y = none)
    (hBy : NodeIs B y nx.level nx.leaf (live nx.ks) M)
    (hBq : NodeIs B q nq.level nq.leaf (insertCv k1 y (live nq.ks)) (bnd M ex' q))
    (hBx : (B.obj x).isSome = true)
    (hsame : ∀ z, z ≠ x → z ≠ y → z ≠ q → B.obj z = A.obj z) :
    Sound M ex' B r C ∧ x ∉ reachAt B (B.fuel r) r ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = y := by
  obtain ⟨nqb, hq1, hq2, hq3, hq4, hq5⟩ := hBq
  obtain ⟨ny, hy1, hy2, hy3, hy4, hy5⟩ := id hBy
  have hG := h.good
  obtain ⟨loq, hiq, hgq⟩ := hG.tr_reach_good _ q hq nq hAq
  have hTq := hG.tr_nodup h.tree hq
  have hyA : y ∉ reachAt A (A.fuel r) r := by
    intro hy'
    have := hG.tr_exists _ y hy'
    simp [hy] at this
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, _, _⟩ := live_split he
  have hxk : (nq.leaf = true → isLong k1 = true) ∧ nx.level < nq.level := by
    rcases hgq.kind hAq hk1 with ⟨_, _, v, hv⟩ | ⟨hk', m, _, _, hm1, hm2, _, _⟩
    · rw [hAx] at hv
      cases hv
    · rw [hAx] at hm1
      cases hm1
      exact ⟨hk', hm2⟩
  have hqx : q ≠ x := by
    intro e
    rw [e, hAx] at hAq
    cases hAq
    omega
  have hfq : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hxq : x ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hk1 (tc_self _ _ _)
  have hxr : x ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hxq
  obtain ⟨lox, hix, hgx⟩ := hG.tr_reach_good _ x hxr nx hAx
  have hqnx : ∀ f, q ∉ reachAt A f x := fun f => hgq.tc_no_cycle hxq (Ne.symm hqx) f
  have hax : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z :=
    fun z hz hzx => hsame z hzx (fun e => hyA (e ▸ hG.tr_closed hxr hz)) (fun e => hqnx _ (e ▸ hz))
  have hcopy := fun lo hi (hg : Good A x lo hi) => tr_copy hg hAx hBy hax
  have hmpp : ∀ a ∈ pre ++ post, a ∈ live nq.ks := by
    intro a h'
    rw [he]
    rcases List.mem_append.mp h' with h' | h' <;> simp [h']
  have hside : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A nq.level z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    obtain ⟨h1, h2, h3⟩ := hgq.tr_side hAq hTq he hb hz'
    refine hsame z' (fun e => h2 (e ▸ tc_self _ _ _)) (fun e => ?_) h1
    rw [e, hy] at h3
    cases h3
  have hside' : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A (A.fuel z) z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    rw [← hgq.tc_kid_eq hAq (hmpp _ hb)] at hz'
    exact hside c' z hb z' hz'
  have hlvB : live nqb.ks = pre ++ (k1, y) :: post := by
    rw [hq4, he]
    exact tr_insertCv_replace post hpre
  have hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi' := by
    intro lo' hi' hg
    have hwf : klongsWf nqb.ks = true := by
      simp only [nodeOk, Bool.and_eq_true] at hq5
      exact hq5.1.2
    have hA := hg.tr_kids hAq
    rw [he, bounds_append] at hA
    refine tr_good_of hq1 hwf ?_
    rw [hlvB, hq2, hq3, bounds_append]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hA' := hA t (List.mem_append_left _ ht)
      exact hA'.tr_move (hside' _ _ (List.mem_append_left _ (bounds_mem_live ht))) hA'.1
        (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun _ => ⟨rfl, rfl⟩)
    · simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | ht
      · obtain ⟨a1, a2, a3, a4⟩ := hA _ (List.mem_append_right _ List.mem_cons_self)
        refine ⟨a1, a2, fun hl hs => ?_, fun hk => ?_⟩
        · obtain ⟨v, hv⟩ := a3 hl hs
          rw [hAx] at hv
          cases hv
        · obtain ⟨m, hm1, hm2, hm3, hgm⟩ := a4 hk
          rw [hAx] at hm1
          cases hm1
          exact ⟨ny, hy1, by omega, by rw [hy4]; exact hm3, (hcopy _ _ hgm).1⟩
      · have hA' := hA t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
        exact hA'.tr_move (hside' _ _ (List.mem_append_right _ (bounds_mem_live ht))) hA'.1
          (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun _ => ⟨rfl, rfl⟩)
  have hgqB := hloc loq hiq hgq
  have hL : L B q = L A q := by
    rw [hgqB.L_eq hq1, hgq.L_eq hAq, hlvB, he, hq3]
    simp only [List.flatMap_append, List.flatMap_cons]
    have hE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
        l.flatMap (fun cy => klongList B nq.leaf (L B) cy.1 cy.2) =
          l.flatMap (fun cy => klongList A nq.leaf (L A) cy.1 cy.2) := by
      intro l hl
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hside c z (hl _ hm) z (tc_self _ _ _))
        (L_agree (hside' c z (hl _ hm)))
    rw [hE pre (fun a h' => List.mem_append_left _ h'),
      hE post (fun a h' => List.mem_append_right _ h'),
      tr_klongList_long hxk.1 (hcopy lox hix hgx).2.1]
  have hRE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
      l.flatMap (fun cy => reachAt B nq.level cy.2) =
        l.flatMap (fun cy => reachAt A nq.level cy.2) := by
    intro l hl
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact reachAt_agree _ _ (hside c z (hl _ hm))
  have hyB : reachAt B nq.level y =
      y :: (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [(hcopy lox hix hgx).1.reachAt_eq nq.level (by simp [Tree.fuel, hy1, hy2]; omega)]
    exact (hcopy lox hix hgx).2.2
  have hxA : reachAt A nq.level x =
      x :: (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [hgq.tc_kid_eq hAq hk1, show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx]
  have hRqA : reachAt A (A.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      x :: ((live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) ++
        post.flatMap (fun cy => reachAt A nq.level cy.2)) := by
    rw [hfq, tc_key hAq, he, List.flatMap_append, List.flatMap_cons, hxA]
    simp
  have hRqB : reachAt B (B.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      y :: ((live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) ++
        post.flatMap (fun cy => reachAt A nq.level cy.2)) := by
    rw [show B.fuel q = nq.level + 1 by simp [Tree.fuel, hq1, hq2], tc_key hq1, hlvB,
      List.flatMap_append, List.flatMap_cons, hyB, hRE pre (fun a h' => List.mem_append_left _ h'),
      hRE post (fun a h' => List.mem_append_right _ h')]
    simp
  have hqA : ∀ z, z ∈ reachAt A (A.fuel q) q → z ∈ reachAt A (A.fuel r) r :=
    fun z hz => hG.tr_closed hq hz
  have hR : (reachAt B (B.fuel q) q).Nodup := by
    rw [hRqB]
    have hT' := hTq
    rw [hRqA] at hT'
    refine tr_nodup_replace hT' (fun hm => hyA (hqA y ?_))
    rw [hRqA]
    simp only [List.mem_append, List.mem_cons] at hm ⊢
    tauto
  have hmemq : ∀ z ∈ reachAt B (B.fuel q) q, z ∈ reachAt A (A.fuel q) q ∨ z = y := by
    intro z hz
    rw [hRqB] at hz
    rw [hRqA]
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    tauto
  have hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hmemq z hz with h' | rfl
    · exact Or.inl h'
    · exact Or.inr hyA
  have ha : Agree A B r q := fun z hz hzq => hsame z (fun e => hzq (e ▸ hxq))
    (fun e => hyA (e ▸ hz)) (fun e => hzq (e ▸ tc_self _ _ _))
  have hk : KeepsKind A B q := by
    intro n hn
    rw [hAq] at hn
    cases hn
    exact ⟨nqb, hq1, by omega, fun _ => by rw [hlvB]; simp⟩
  have hqk : ∃ n, A.obj q = some (.key n) := ⟨nq, hAq⟩
  obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hq ha hk hloc hqk hR hnew
  have hxB : x ∉ reachAt B (B.fuel r) r := by
    intro hx
    rcases hmemB x hx with ⟨_, h2⟩ | h2
    · exact h2 hxq
    · have hT' := hTq
      rw [hRqA, List.nodup_middle, List.nodup_cons] at hT'
      rw [hRqB] at h2
      rcases List.mem_append.mp h2 with h2 | h2
      · exact hT'.1 (List.mem_append_left _ h2)
      · rcases List.mem_cons.mp h2 with h2 | h2
        · rw [h2, hy] at hAx
          cases hAx
        · exact hT'.1 (List.mem_append_right _ h2)
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = y := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hmemq z h1 with h2 | h2
      · exact Or.inl (hqA z h2)
      · exact Or.inr h2
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwx : w = x
    · rw [hwx]
      exact hBx
    by_cases hwy : w = y
    · rw [hwy, hy] at hw
      cases hw
    by_cases hwq : w = q
    · simp [hwq, hq1]
    rw [hsame w hwx hwy hwq]
    exact hw
  refine ⟨⟨?_, Good.ctx hG h.tree hq ha hk hloc hqk, ?_, ?_, hTB⟩, hxB, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrq : r = q
    · rw [hrq]
      exact ⟨nqb, hq1, Or.inr (by rw [hlvB]; simp)⟩
    · have hrx : r ≠ x := fun e => hqnx _ (e ▸ hq)
      have hry : r ≠ y := by
        intro e
        rw [e, hy] at ho
        cases ho
      exact ⟨n, (hsame r hrx hry hrq).trans ho, hne⟩
  · intro z hz m hm
    by_cases hzq : z = q
    · rw [hzq, hq1] at hm
      cases hm
      rw [hzq]
      exact hq5
    by_cases hzy : z = y
    · rw [hzy, hy1] at hm
      cases hm
      exact tr_nodeOk hy5 (by split <;> omega) (fun _ h' => h')
    have hzx : z ≠ x := fun e => hxB (e ▸ hz)
    have hzA : z ∈ reachAt A (A.fuel r) r := by
      rcases hmem z hz with h' | h'
      · exact h'
      · exact absurd h' hzy
    exact h.tr_old hs hzA (fun e => hzx (Option.some.inj e).symm) (hsame z hzx hzy hzq) hm
      (by split <;> omega)
  · rw [ctx_L hG h.tree hq ha hk hloc hqk hL]
    exact h.holds

theorem Sound.timeSplitRoot {M : Nat} {A B : Tree} {r y : NodeId} {C : List (Key × Nat)}
    {nx : KNode} (h : Sound M (some r) A r C) (hAx : A.obj r = some (.key nx))
    (hy : A.obj y = none) (hBy : NodeIs B y nx.level nx.leaf (live nx.ks) M)
    (hBx : (B.obj r).isSome = true) (hsame : ∀ z, z ≠ r → z ≠ y → B.obj z = A.obj z) :
    Sound M none B y C ∧ r ∉ reachAt B (B.fuel y) y ∧
      ∀ z ∈ reachAt B (B.fuel y) y, z ∈ reachAt A (A.fuel r) r ∨ z = y := by
  obtain ⟨ny, hy1, hy2, hy3, hy4, hy5⟩ := id hBy
  have hG := h.good
  have hyA : y ∉ reachAt A (A.fuel r) r := by
    intro hy'
    have := hG.tr_exists _ y hy'
    simp [hy] at this
  have ha : ∀ z ∈ reachAt A (A.fuel r) r, z ≠ r → B.obj z = A.obj z :=
    fun z hz hzr => hsame z hzr (fun e => hyA (e ▸ hz))
  obtain ⟨hGB, hLB, hRB⟩ := tr_copy hG hAx hBy ha
  have hRA : reachAt A (A.fuel r) r =
      r :: (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [show A.fuel r = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx]
  have hT := h.tree
  rw [hRA, List.nodup_cons] at hT
  have hyT : y ∉ (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) :=
    fun hm => hyA (by rw [hRA]; exact List.mem_cons_of_mem _ hm)
  have hry : r ≠ y := by
    intro e
    rw [e, hy] at hAx
    cases hAx
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwr : w = r
    · rw [hwr]
      exact hBx
    by_cases hwy : w = y
    · rw [hwy, hy] at hw
      cases hw
    rw [hsame w hwr hwy]
    exact hw
  refine ⟨⟨?_, hGB, ?_, by rw [hLB]; exact h.holds, ?_⟩, ?_, ?_⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    rw [hAx] at ho
    cases ho
    exact ⟨ny, hy1, by rw [hy3, hy4]; exact hne⟩
  · intro z hz m hm
    rw [hRB] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · rw [hy1] at hm
      cases hm
      simpa using hy5
    · have hzr : z ≠ r := fun e => hT.1 (e ▸ hz)
      have hzy : z ≠ y := fun e => hyT (e ▸ hz)
      have hzA : z ∈ reachAt A (A.fuel r) r := by
        rw [hRA]
        exact List.mem_cons_of_mem _ hz
      have := h.tr_old hs hzA (fun e => hzr (Option.some.inj e).symm) (hsame z hzr hzy) hm
        (le_refl M)
      simpa using this
  · rw [hRB, List.nodup_cons]
    exact ⟨hyT, hT.2⟩
  · rw [hRB]
    intro hm
    rcases List.mem_cons.mp hm with e | hm
    · exact hry e
    · exact hT.1 hm
  · intro z hz
    rw [hRB] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inr rfl
    · left
      rw [hRA]
      exact List.mem_cons_of_mem _ hz

theorem tr_belowHi_le {d c : Nat} {hi : Option Nat} (h : d ≤ c) (hc : belowHi c hi = true) :
    belowHi d hi = true := by
  cases hi with
  | none => rfl
  | some b =>
    simp only [belowHi, decide_eq_true_eq] at hc ⊢
    omega

theorem Good.tr_hi {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) : belowHi c hi = true := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem hm
  exact (h.tr_kids hobj _ (bounds_mem hi he)).1

/-- A space split: two nodes with the two halves of x's live klongs, the
second half's first klong with compare value 0 in an inner node. -/
theorem tr_split {A B : Tree} {x first second : NodeId} {lo : Nat} {H : Option Nat}
    (hG : Good A x lo H) {nx : KNode} (hAx : A.obj x = some (.key nx))
    {l1 rest : List (Nat × NodeId)} {sc : Nat} {y0 : NodeId}
    (hsplit : live nx.ks = l1 ++ (sc, y0) :: rest) {b1 b2 : Nat}
    (hBf : NodeIs B first nx.level nx.leaf l1 b1)
    (hBs : NodeIs B second nx.level nx.leaf
      (if nx.leaf then (sc, y0) :: rest else (0, y0) :: rest) b2)
    (ha : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z) :
    Good B first lo (some sc) ∧ Good B second (max lo sc) H ∧
      L B first ++ L B second = L A x ∧
      reachAt B (B.fuel first) first = first :: l1.flatMap (fun cy => reachAt A nx.level cy.2) ∧
      reachAt B (B.fuel second) second =
        second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := hBf
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := hBs
  have hka := fun c z (hm : (c, z) ∈ live nx.ks) => hG.tr_kids_agree hAx ha hm
  obtain ⟨hl1lt, hrestgt, _⟩ := live_split hsplit
  have hm1 : ∀ a ∈ l1, a ∈ live nx.ks := fun a h => by rw [hsplit]; simp [h]
  have hmr : ∀ a ∈ rest, a ∈ live nx.ks := fun a h => by rw [hsplit]; simp [h]
  have hm0 : (sc, y0) ∈ live nx.ks := by rw [hsplit]; simp
  have hRE : ∀ c z, (c, z) ∈ live nx.ks → reachAt B nx.level z = reachAt A nx.level z := by
    intro c z hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hG.tc_kid_eq hAx hm] at hz'
    exact hka c z hm z' hz'
  have hKE : ∀ c z, (c, z) ∈ live nx.ks →
      klongList B nx.leaf (L B) c z = klongList A nx.leaf (L A) c z :=
    fun c z hm => tc_klongList (hka c z hm z (tc_self _ _ _)) (L_agree (hka c z hm))
  have hA := hG.tr_kids hAx
  rw [hsplit, bounds_append] at hA
  have hwf1 : klongsWf nf.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hf5
    exact hf5.1.2
  have hwf2 : klongsWf ns.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hs5
    exact hs5.1.2
  have hGf : Good B first lo (some sc) := by
    refine tr_good_of hf1 hwf1 ?_
    rw [hf4, hf2, hf3]
    intro t ht
    have hA' := hA t (List.mem_append_left _ ht)
    have hlt : t.1 < sc := hl1lt _ (bounds_mem_live ht)
    exact hA'.tr_move (hka _ _ (hm1 _ (bounds_mem_live ht))) (by simp [belowHi, hlt])
      (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun _ => ⟨rfl, rfl⟩)
  have hGs : Good B second (max lo sc) H := by
    refine tr_good_of hs1 hwf2 ?_
    rw [hs2, hs3]
    cases hlf : nx.leaf with
    | true =>
      rw [hs4, hlf]
      simp only [ite_true]
      intro t ht
      have hA' := hA t (List.mem_append_right _ ht)
      rw [hlf] at hA'
      have hmem := bounds_mem_live ht
      have hge : sc ≤ t.1 := by
        rcases List.mem_cons.mp hmem with h' | h'
        · rw [← (Prod.mk.inj h').1]
        · exact le_of_lt (hrestgt _ h')
      have hm' : (t.1, t.2.1) ∈ live nx.ks := by
        rcases List.mem_cons.mp hmem with h' | h'
        · rw [h']
          exact hm0
        · exact hmr _ h'
      exact hA'.tr_move (hka _ _ hm') hA'.1 (fun _ => ⟨rfl, max_le (hA'.2.1 rfl) hge⟩)
        (fun h' => by cases h')
    | false =>
      rw [hs4, hlf]
      simp only [Bool.false_eq_true, ite_false]
      intro t ht
      simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hA' := hA (sc, y0, nextHi rest H) (List.mem_append_right _ (by simp [bounds]))
        rw [hlf] at hA'
        exact hA'.tr_move (hka sc y0 hm0) (tr_belowHi_le (Nat.zero_le _) hA'.1)
          (fun h' => by cases h') (fun _ => ⟨by omega, rfl⟩)
      · have hA' := hA t (List.mem_append_right _ (by simp [bounds, ht]))
        rw [hlf] at hA'
        have hgt : sc < t.1 := hrestgt _ (bounds_mem_live ht)
        exact hA'.tr_move (hka _ _ (hmr _ (bounds_mem_live ht))) hA'.1 (fun h' => by cases h')
          (fun _ => ⟨by omega, rfl⟩)
  refine ⟨hGf, hGs, ?_, ?_, ?_⟩
  · rw [hGf.L_eq hf1, hGs.L_eq hs1, hG.L_eq hAx, hf4, hf3, hs3, hsplit, List.flatMap_append]
    congr 1
    · apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact hKE c z (hm1 _ hm)
    · rw [hs4]
      cases hlf : nx.leaf with
      | true =>
        simp only [ite_true]
        apply List.flatMap_congr
        rintro ⟨c, z⟩ hm
        rw [← hlf]
        rcases List.mem_cons.mp hm with h' | h'
        · rw [h']
          exact hKE _ _ hm0
        · exact hKE c z (hmr _ h')
      | false =>
        simp only [Bool.false_eq_true, ite_false, List.flatMap_cons]
        congr 1
        · simp only [klongList, Bool.false_eq_true, ite_false]
          exact L_agree (hka sc y0 hm0)
        · apply List.flatMap_congr
          rintro ⟨c, z⟩ hm
          rw [← hlf]
          exact hKE c z (hmr _ hm)
  · rw [show B.fuel first = nx.level + 1 by simp [Tree.fuel, hf1, hf2], tc_key hf1, hf4]
    congr 1
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact hRE c z (hm1 _ hm)
  · rw [show B.fuel second = nx.level + 1 by simp [Tree.fuel, hs1, hs2], tc_key hs1, hs4]
    congr 1
    cases nx.leaf with
    | true =>
      simp only [ite_true]
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      rcases List.mem_cons.mp hm with h' | h'
      · rw [h']
        exact hRE _ _ hm0
      · exact hRE c z (hmr _ h')
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.flatMap_cons]
      rw [hRE _ _ hm0]
      congr 1
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact hRE c z (hmr _ hm)

/-- The split klong of a sound node is above the node's lower bound: in a leaf
by the range, in an inner node because the klong before it holds a key. -/
theorem Good.tr_split_lo {s : Tree} {x : NodeId} {lo : Nat} {H : Option Nat}
    (hG : Good s x lo H) {nx : KNode} (hAx : s.obj x = some (.key nx))
    {l1 rest : List (Nat × NodeId)} {sc : Nat} {y0 : NodeId}
    (hsplit : live nx.ks = l1 ++ (sc, y0) :: rest) (hl1 : l1 ≠ []) : lo < sc := by
  rcases List.eq_nil_or_concat' l1 with h | ⟨l0, ⟨c0, z0⟩, rfl⟩
  · exact absurd h hl1
  have he : live nx.ks = l0 ++ (c0, z0) :: ((sc, y0) :: rest) := by rw [hsplit]; simp
  obtain ⟨_, hpost, _⟩ := live_split he
  have hc0 : c0 < sc := hpost (sc, y0) List.mem_cons_self
  have hm : (c0, z0) ∈ live nx.ks := by rw [he]; simp
  have hk := hG.tr_kids hAx _ (bounds_mem H he)
  cases hlf : nx.leaf with
  | true =>
    have := hk.2.1 hlf
    omega
  | false =>
    obtain ⟨m, hm1, _, hm3, hg⟩ := hk.2.2.2 (by simp [hlf])
    simp only [hlf, Bool.false_eq_true, ite_false, nextHi] at hg
    obtain ⟨⟨k, v⟩, hkv⟩ := List.exists_mem_of_ne_nil _ (hg.nonempty m hm1 hm3)
    obtain ⟨d, r, _, hd1, hd2⟩ := hg.range k v hkv
    simp only [belowHi, decide_eq_true_eq] at hd2
    omega

theorem tr_lt_post {post : List (Nat × NodeId)} {d : Nat} {hi : Option Nat}
    (hp : post.Pairwise CvLt) (h : belowHi d (nextHi post hi) = true) : ∀ b ∈ post, d < b.1 := by
  cases post with
  | nil => simp
  | cons a r =>
    simp only [nextHi, belowHi, decide_eq_true_eq] at h
    rw [List.pairwise_cons] at hp
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h
    · exact lt_trans h (hp.1 b hb)

theorem tr_ne_of_obj {s : Tree} {a b : NodeId} {n : KNode} (ha : s.obj a = some (.key n))
    (hb : s.obj b = none) : a ≠ b := by
  intro e
  rw [e, hb] at ha
  cases ha

theorem tr_mem_mid {α : Type} {z a : α} {P S : List α} (h : z ∈ P ++ S) : z ∈ P ++ a :: S := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem tr_mem_swap {α : Type} {z a b : α} {P S : List α} (h : z ∈ P ++ b :: S) :
    z = b ∨ z ∈ P ++ a :: S := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem tr_mem_two {α : Type} {z a b : α} {P R1 S : List α} (h : z ∈ P ++ a :: (R1 ++ b :: S)) :
    z = a ∨ z = b ∨ z ∈ P ++ (R1 ++ S) := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem tr_nodup_insert2 {α : Type} {a b : α} {P R1 S : List α} (h : (P ++ a :: (R1 ++ S)).Nodup)
    (hb : b ∉ P ++ a :: (R1 ++ S)) : (P ++ a :: (R1 ++ b :: S)).Nodup := by
  have e1 : P ++ a :: (R1 ++ b :: S) = (P ++ a :: R1) ++ b :: S := by simp
  have e2 : P ++ a :: (R1 ++ S) = (P ++ a :: R1) ++ S := by simp
  rw [e1, List.nodup_middle, List.nodup_cons, ← e2]
  exact ⟨hb, h⟩

theorem Sound.spaceSplit {M : Nat} {ex' : Option NodeId} {A B : Tree}
    {r q x first second : NodeId} {C : List (Key × Nat)} {nq nx : KNode} {k1 sc : Nat}
    {y0 : NodeId} {l1 rest : List (Nat × NodeId)}
    (h : Sound M (some x) A r C) (hq : q ∈ reachAt A (A.fuel r) r)
    (hAq : A.obj q = some (.key nq)) (hql : nq.leaf = false) (hk1 : (k1, x) ∈ live nq.ks)
    (hAx : A.obj x = some (.key nx)) (hsplit : live nx.ks = l1 ++ (sc, y0) :: rest)
    (hl1 : l1 ≠ []) (hfirst : first = x ∨ A.obj first = none) (hsecond : A.obj second = none)
    (hne : first ≠ second) (hBf : NodeIs B first nx.level nx.leaf l1 M)
    (hBs : NodeIs B second nx.level nx.leaf
      (if nx.leaf then (sc, y0) :: rest else (0, y0) :: rest) M)
    (hBq : NodeIs B q nq.level false (insertCv sc second (insertCv k1 first (live nq.ks)))
      (bnd M ex' q))
    (hBx : (B.obj x).isSome = true)
    (hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ q → B.obj z = A.obj z) :
    Sound M ex' B r C ∧ (first ≠ x → x ∉ reachAt B (B.fuel r) r) ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = first ∨ z = second := by
  obtain ⟨nqb, hq1, hq2, hq3, hq4, hq5⟩ := hBq
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := id hBf
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := id hBs
  have hG := h.good
  obtain ⟨loq, hiq, hgq⟩ := hG.tr_reach_good _ q hq nq hAq
  have hTq := hG.tr_nodup h.tree hq
  have hnotA : ∀ z, A.obj z = none → z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hz] at this
  have hsA := hnotA second hsecond
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, _, hpp⟩ := live_split he
  have hxk : nx.level < nq.level := by
    obtain ⟨m, _, _, hm1, hm2, _, _⟩ := hgq.child hAq hk1 (by simp [hql])
    rw [hAx] at hm1
    cases hm1
    exact hm2
  have hqx : q ≠ x := by
    intro e
    rw [e, hAx] at hAq
    cases hAq
    omega
  have hfq : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hxq : x ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hk1 (tc_self _ _ _)
  have hxr : x ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hxq
  have hqnx : ∀ f, q ∉ reachAt A f x := fun f => hgq.tc_no_cycle hxq (Ne.symm hqx) f
  have hqA : ∀ z, z ∈ reachAt A (A.fuel q) q → z ∈ reachAt A (A.fuel r) r :=
    fun z hz => hG.tr_closed hq hz
  have hax : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z := by
    intro z hz hzx
    have hzr := hG.tr_closed hxr hz
    refine hsame z hzx (fun e => ?_) (fun e => hsA (e ▸ hzr)) (fun e => hqnx _ (e ▸ hz))
    rcases hfirst with e' | e'
    · exact hzx (e.trans e')
    · exact hnotA first e' (e ▸ hzr)
  have hmpp : ∀ a ∈ pre ++ post, a ∈ live nq.ks := by
    intro a h'
    rw [he]
    rcases List.mem_append.mp h' with h' | h' <;> simp [h']
  have hside : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A nq.level z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    obtain ⟨h1, h2, h3⟩ := hgq.tr_side hAq hTq he hb hz'
    have hz'x : z' ≠ x := fun e => h2 (e ▸ tc_self _ _ _)
    refine hsame z' hz'x (fun e => ?_) (fun e => ?_) h1
    · rcases hfirst with e' | e'
      · exact hz'x (e.trans e')
      · rw [e, e'] at h3
        cases h3
    · rw [e, hsecond] at h3
      cases h3
  have hside' : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A (A.fuel z) z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    rw [← hgq.tc_kid_eq hAq (hmpp _ hb)] at hz'
    exact hside c' z hb z' hz'
  have hm0 : (sc, y0) ∈ live nx.ks := by rw [hsplit]; simp
  have hgxq := hgq.tr_kid hAq hql he
  have hk1sc : k1 < sc := by
    have := hgxq.tr_split_lo hAx hsplit hl1
    omega
  have hscpost : ∀ b ∈ post, sc < b.1 := tr_lt_post hpp (hgxq.tr_hi hAx hm0)
  have hlvB : live nqb.ks = pre ++ (k1, first) :: (sc, second) :: post := by
    rw [hq4, he, tr_insertCv_replace post hpre]
    have := tr_insertCv_insert (c := sc) (y := second) hscpost (pre := pre ++ [(k1, first)])
      (by
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact lt_trans (hpre a ha) hk1sc
        · exact hk1sc)
    simpa using this
  have hwf : klongsWf nqb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hq5
    exact hq5.1.2
  have hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi' := by
    intro lo' hi' hg
    have hgx' := hg.tr_kid hAq hql he
    obtain ⟨hGf, hGs, _, _, _⟩ := tr_split hgx' hAx hsplit hBf hBs hax
    have hlo' : max (max lo' k1) sc = max lo' sc := by omega
    rw [hlo'] at hGs
    have hA := hg.tr_kids hAq
    rw [he, bounds_append] at hA
    refine tr_good_of hq1 hwf ?_
    rw [hlvB, hq2, hq3, bounds_append]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hA' := hA t (List.mem_append_left _ ht)
      rw [hql] at hA'
      exact hA'.tr_move (hside' _ _ (List.mem_append_left _ (bounds_mem_live ht))) hA'.1
        (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
    · simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · have hA' := hA _ (List.mem_append_right _ List.mem_cons_self)
        refine ⟨hA'.1, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
        exact ⟨nf, hf1, by omega, by rw [hf4]; exact hl1, by simpa [nextHi] using hGf⟩
      · have hh : ∀ b ∈ post, belowHi b.1 hi' = true :=
          fun b hb => hg.tr_hi hAq (hmpp _ (List.mem_append_right _ hb))
        have hsc := (below_nextHi hpp hh (hgx'.tr_hi hAx hm0)).1
        refine ⟨hsc, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
        exact ⟨ns, hs1, by omega, by rw [hs4]; split <;> simp, by simpa using hGs⟩
      · have hA' := hA t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
        rw [hql] at hA'
        exact hA'.tr_move (hside' _ _ (List.mem_append_right _ (bounds_mem_live ht))) hA'.1
          (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
  have hgqB := hloc loq hiq hgq
  obtain ⟨hGf0, hGs0, hLfs, hRf, hRs⟩ := tr_split hgxq hAx hsplit hBf hBs hax
  have hL : L B q = L A q := by
    rw [hgqB.L_eq hq1, hgq.L_eq hAq, hlvB, he, hq3, hql]
    have hE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
        l.flatMap (fun cy => klongList B false (L B) cy.1 cy.2) =
          l.flatMap (fun cy => klongList A false (L A) cy.1 cy.2) := by
      intro l hl
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hside c z (hl _ hm) z (tc_self _ _ _))
        (L_agree (hside' c z (hl _ hm)))
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hE pre (fun a h' => List.mem_append_left _ h'),
      hE post (fun a h' => List.mem_append_right _ h')]
    simp only [klongList, Bool.false_eq_true, ite_false]
    rw [← hLfs]
    simp
  have hRE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
      l.flatMap (fun cy => reachAt B nq.level cy.2) =
        l.flatMap (fun cy => reachAt A nq.level cy.2) := by
    intro l hl
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact reachAt_agree _ _ (hside c z (hl _ hm))
  have hfB : reachAt B nq.level first =
      first :: l1.flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [hGf0.reachAt_eq nq.level (by simp [Tree.fuel, hf1, hf2]; omega)]
    exact hRf
  have hsB : reachAt B nq.level second =
      second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [hGs0.reachAt_eq nq.level (by simp [Tree.fuel, hs1, hs2]; omega)]
    exact hRs
  have hxA : reachAt A nq.level x = x :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
      ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2)) := by
    rw [hgq.tc_kid_eq hAq hk1, show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx,
      hsplit, List.flatMap_append]
  have hRqA : reachAt A (A.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      x :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [hfq, tc_key hAq, he, List.flatMap_append, List.flatMap_cons, hxA]
    simp
  have hRqB : reachAt B (B.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      first :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        second :: (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [show B.fuel q = nq.level + 1 by simp [Tree.fuel, hq1, hq2], tc_key hq1, hlvB,
      List.flatMap_append, List.flatMap_cons, List.flatMap_cons, hfB, hsB,
      hRE pre (fun a h' => List.mem_append_left _ h'),
      hRE post (fun a h' => List.mem_append_right _ h')]
    simp
  have hTq' := hTq
  rw [hRqA] at hTq'
  have hA1 : ((q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      first :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2)))).Nodup := by
    rcases hfirst with e | e
    · rw [e]
      exact hTq'
    · refine tr_nodup_replace hTq' (fun hm => hnotA first e (hqA first ?_))
      rw [hRqA]
      exact tr_mem_mid hm
  have hR : (reachAt B (B.fuel q) q).Nodup := by
    rw [hRqB]
    refine tr_nodup_insert2 hA1 (fun hm => ?_)
    rcases tr_mem_swap (a := x) hm with e | e
    · exact hne e.symm
    · exact hsA (hqA _ (by rw [hRqA]; exact e))
  have hmemq : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z = first ∨ z = second := by
    intro z hz
    rw [hRqB] at hz
    rcases tr_mem_two hz with e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · left
      rw [hRqA]
      exact tr_mem_mid e
  have hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hmemq z hz with h' | rfl | rfl
    · exact Or.inl h'
    · rcases hfirst with e | e
      · rw [e]
        exact Or.inl hxq
      · exact Or.inr (hnotA _ e)
    · exact Or.inr hsA
  have ha : Agree A B r q := by
    intro z hz hzq
    have hzx : z ≠ x := fun e => hzq (e ▸ hxq)
    refine hsame z hzx (fun e => ?_) (fun e => hsA (e ▸ hz)) (fun e => hzq (e ▸ tc_self _ _ _))
    rcases hfirst with e' | e'
    · exact hzx (e.trans e')
    · exact hnotA first e' (e ▸ hz)
  have hk : KeepsKind A B q := by
    intro n hn
    rw [hAq] at hn
    cases hn
    exact ⟨nqb, hq1, by omega, fun _ => by rw [hlvB]; simp⟩
  have hqk : ∃ n, A.obj q = some (.key n) := ⟨nq, hAq⟩
  obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hq ha hk hloc hqk hR hnew
  have hxB : first ≠ x → x ∉ reachAt B (B.fuel r) r := by
    intro hfx hx
    rcases hmemB x hx with ⟨_, h2⟩ | h2
    · exact h2 hxq
    · have hxs : x ≠ second := tr_ne_of_obj hAx hsecond
      have hT2 := hTq'
      rw [List.nodup_middle, List.nodup_cons] at hT2
      rw [hRqB] at h2
      rcases tr_mem_two h2 with e | e | e
      · exact hfx e.symm
      · exact hxs e
      · exact hT2.1 e
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r,
      z ∈ reachAt A (A.fuel r) r ∨ z = first ∨ z = second := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hmemq z h1 with h2 | h2 | h2
      · exact Or.inl (hqA z h2)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwx : w = x
    · rw [hwx]
      exact hBx
    by_cases hwf : w = first
    · simp [hwf, hf1]
    by_cases hws : w = second
    · rw [hws, hsecond] at hw
      cases hw
    by_cases hwq : w = q
    · simp [hwq, hq1]
    rw [hsame w hwx hwf hws hwq]
    exact hw
  refine ⟨⟨?_, Good.ctx hG h.tree hq ha hk hloc hqk, ?_, ?_, hTB⟩, hxB, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrq : r = q
    · rw [hrq]
      exact ⟨nqb, hq1, Or.inr (by rw [hlvB]; simp)⟩
    · have hrx : r ≠ x := fun e => hqnx _ (e ▸ hq)
      have hrf : r ≠ first := by
        intro e
        rcases hfirst with e' | e'
        · exact hrx (e.trans e')
        · exact tr_ne_of_obj ho e' e
      have hrs : r ≠ second := tr_ne_of_obj ho hsecond
      exact ⟨n, (hsame r hrx hrf hrs hrq).trans ho, hne⟩
  · intro z hz m hm
    by_cases hzq : z = q
    · rw [hzq, hq1] at hm
      cases hm
      rw [hzq]
      exact hq5
    by_cases hzf : z = first
    · rw [hzf, hf1] at hm
      cases hm
      exact tr_nodeOk hf5 (by split <;> omega) (fun _ h' => h')
    by_cases hzs : z = second
    · rw [hzs, hs1] at hm
      cases hm
      exact tr_nodeOk hs5 (by split <;> omega) (fun _ h' => h')
    have hzx : z ≠ x := by
      intro e
      rcases hfirst with e' | e'
      · exact hzf (e.trans e'.symm)
      · have hfx : first ≠ x := fun e'' => tr_ne_of_obj hAx e' e''.symm
        exact hxB hfx (e ▸ hz)
    have hzA : z ∈ reachAt A (A.fuel r) r := by
      rcases hmem z hz with h' | h' | h'
      · exact h'
      · exact absurd h' hzf
      · exact absurd h' hzs
    exact h.tr_old hs hzA (fun e => hzx (Option.some.inj e).symm) (hsame z hzx hzf hzs hzq) hm
      (by split <;> omega)
  · rw [ctx_L hG h.tree hq ha hk hloc hqk hL]
    exact h.holds

theorem Sound.spaceSplitRoot {M : Nat} {A B : Tree} {r first second r' : NodeId}
    {C : List (Key × Nat)} {nx : KNode} {sc : Nat} {y0 : NodeId} {l1 rest : List (Nat × NodeId)}
    (h : Sound M (some r) A r C) (hAx : A.obj r = some (.key nx))
    (hsplit : live nx.ks = l1 ++ (sc, y0) :: rest) (hl1 : l1 ≠ [])
    (hfirst : first = r ∨ A.obj first = none) (hsecond : A.obj second = none)
    (hne : first ≠ second) (hr' : A.obj r' = none) (hne' : r' ≠ first ∧ r' ≠ second)
    (hBf : NodeIs B first nx.level nx.leaf l1 M)
    (hBs : NodeIs B second nx.level nx.leaf
      (if nx.leaf then (sc, y0) :: rest else (0, y0) :: rest) M)
    (hBr : NodeIs B r' (nx.level + 1) false [(0, first), (sc, second)] M)
    (hBx : (B.obj r).isSome = true)
    (hsame : ∀ z, z ≠ r → z ≠ first → z ≠ second → z ≠ r' → B.obj z = A.obj z) :
    Sound M none B r' C ∧ (first ≠ r → r ∉ reachAt B (B.fuel r') r') ∧
      ∀ z ∈ reachAt B (B.fuel r') r',
        z ∈ reachAt A (A.fuel r) r ∨ z = first ∨ z = second ∨ z = r' := by
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := id hBf
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := id hBs
  obtain ⟨nr, hr1, hr2, hr3, hr4, hr5⟩ := hBr
  have hG := h.good
  have hnotA : ∀ z, A.obj z = none → z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hz] at this
  have hsA := hnotA second hsecond
  have hr'A := hnotA r' hr'
  have ha : ∀ z ∈ reachAt A (A.fuel r) r, z ≠ r → B.obj z = A.obj z := by
    intro z hz hzr
    refine hsame z hzr (fun e => ?_) (fun e => hsA (e ▸ hz)) (fun e => hr'A (e ▸ hz))
    rcases hfirst with e' | e'
    · exact hzr (e.trans e')
    · exact hnotA first e' (e ▸ hz)
  obtain ⟨hGf, hGs, hLfs, hRf, hRs⟩ := tr_split hG hAx hsplit hBf hBs ha
  have hRA : reachAt A (A.fuel r) r = r :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
      ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2)) := by
    rw [show A.fuel r = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx, hsplit,
      List.flatMap_append]
  have hRf' : reachAt B (nx.level + 1) first =
      first :: l1.flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [← hRf, show B.fuel first = nx.level + 1 by simp [Tree.fuel, hf1, hf2]]
  have hRs' : reachAt B (nx.level + 1) second =
      second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [← hRs, show B.fuel second = nx.level + 1 by simp [Tree.fuel, hs1, hs2]]
  have hRB : reachAt B (B.fuel r') r' =
      r' :: ((first :: l1.flatMap (fun cy => reachAt A nx.level cy.2)) ++
        (second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2))) := by
    rw [show B.fuel r' = nx.level + 1 + 1 by simp [Tree.fuel, hr1, hr2], tc_key hr1, hr4]
    simp [hRf', hRs']
  have hp : List.Perm (r' :: ((first :: l1.flatMap (fun cy => reachAt A nx.level cy.2)) ++
      (second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2))))
      (r' :: first :: second :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2))) :=
    (List.perm_middle.cons first).cons r'
  have hT := h.tree
  rw [hRA, List.nodup_cons] at hT
  have hinA : ∀ z, z ∈ l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
      ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) →
      z ∈ reachAt A (A.fuel r) r := fun z hz => by rw [hRA]; exact List.mem_cons_of_mem _ hz
  have hfR : first ∉ l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
      ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rcases hfirst with e | e
    · rw [e]
      exact hT.1
    · exact fun hm => hnotA first e (hinA _ hm)
  have hTB : (reachAt B (B.fuel r') r').Nodup := by
    rw [hRB, hp.nodup_iff]
    simp only [List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨hne'.1, hne'.2, fun hm => hr'A (hinA _ hm)⟩, ⟨hne, hfR⟩,
      fun hm => hsA (hinA _ hm), hT.2⟩
  have hmem : ∀ z ∈ reachAt B (B.fuel r') r', z = r' ∨ z = first ∨ z = second ∨
      z ∈ l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
    intro z hz
    rw [hRB, hp.mem_iff] at hz
    simp only [List.mem_cons] at hz
    tauto
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwr : w = r
    · rw [hwr]
      exact hBx
    by_cases hwf : w = first
    · simp [hwf, hf1]
    by_cases hws : w = second
    · rw [hws, hsecond] at hw
      cases hw
    by_cases hwr' : w = r'
    · rw [hwr', hr'] at hw
      cases hw
    rw [hsame w hwr hwf hws hwr']
    exact hw
  have hwf : klongsWf nr.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hr5
    exact hr5.1.2
  have hGB : Good B r' 0 none := by
    refine tr_good_of hr1 hwf ?_
    rw [hr4, hr2, hr3]
    intro t ht
    simp only [bounds, nextHi, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨rfl, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
      exact ⟨nf, hf1, by omega, by rw [hf4]; exact hl1, by simpa using hGf⟩
    · refine ⟨rfl, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
      refine ⟨ns, hs1, by omega, by rw [hs4]; split <;> simp, by simpa using hGs⟩
  refine ⟨⟨⟨nr, hr1, Or.inr (by rw [hr4]; simp)⟩, hGB, ?_, ?_, hTB⟩, ?_, ?_⟩
  · intro z hz m hm
    rcases hmem z hz with rfl | rfl | rfl | hzR
    · rw [hr1] at hm
      cases hm
      simpa using hr5
    · rw [hf1] at hm
      cases hm
      simpa using hf5
    · rw [hs1] at hm
      cases hm
      simpa using hs5
    · have hzr : z ≠ r := fun e => hT.1 (e ▸ hzR)
      have hzf : z ≠ first := fun e => hfR (e ▸ hzR)
      have hzs : z ≠ second := fun e => hsA (e ▸ hinA _ hzR)
      have hzr' : z ≠ r' := fun e => hr'A (e ▸ hinA _ hzR)
      have := h.tr_old hs (hinA _ hzR) (fun e => hzr (Option.some.inj e).symm)
        (hsame z hzr hzf hzs hzr') hm (le_refl M)
      simpa using this
  · rw [hGB.L_eq hr1, hr4, hr3]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, klongList,
      Bool.false_eq_true, ite_false]
    rw [hLfs]
    exact h.holds
  · intro hfr hm
    have hrr' : r ≠ r' := by
      intro e
      have h1 : A.obj r' = some (.key nx) := e ▸ hAx
      simp [hr'] at h1
    have hrs : r ≠ second := by
      intro e
      have h1 : A.obj second = some (.key nx) := e ▸ hAx
      simp [hsecond] at h1
    rcases hmem r hm with e | e | e | hrR
    · exact hrr' e
    · exact hfr e.symm
    · exact hrs e
    · exact hT.1 hrR
  · intro z hz
    rcases hmem z hz with e | e | e | hzR
    · exact Or.inr (Or.inr (Or.inr e))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inl (hinA _ hzR)

end Contract
