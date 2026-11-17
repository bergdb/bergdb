/-
The contract package (bergdb 030-04): earlier times. From the frame, clause 3
of the contract: the tree after a transaction, read at an earlier time, has
every node of the tree before it, read at that time, unchanged; so the
invariants and the contents at the earlier time are what they were.
-/
import Mathlib.Tactic
import Contract.Statement

namespace Contract

/-- Klongs added after a time klong of a later time are not seen at t. -/
theorem prefixAt_ext (ks more : List Klong) (i t : Time) (h : t < i) :
    prefixAt (ks ++ Klong.time i :: more) t = prefixAt ks t := by
  induction ks with
  | nil => simp [prefixAt, List.takeWhile, Nat.not_le.mpr h]
  | cons a r ih =>
    unfold prefixAt at ih ⊢
    simp only [List.cons_append, List.takeWhile_cons]
    split <;> simp [ih]

/-- A node extended at time i is, at an earlier time, the node it was. -/
theorem Ext.at_eq {i t : Time} {o o' : Obj} (h : Ext i o o') (ht : t < i) :
    o'.at t = o.at t := by
  cases o with
  | val v =>
    cases o' with
    | val v' => simp only [Ext] at h; simp [Obj.at, h]
    | key n' => simp [Ext] at h
  | key n =>
    cases o' with
    | val v' => simp [Ext] at h
    | key n' =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [Obj.at, Obj.key.injEq, KNode.mk.injEq]
      refine ⟨h1, h2, ?_⟩
      rcases h3 with h3 | ⟨more, h3⟩
      · rw [h3]
      · rw [h3, prefixAt_ext _ _ _ _ ht]

/-- One tree holds every node of another, unchanged, and has its space roots. -/
def Sub (s s' : Tree) : Prop :=
  (∀ x o, s.obj x = some o → s'.obj x = some o) ∧ s'.roots = s.roots

/-- The frame: the tree after, at an earlier time, holds the tree before at
that time. -/
theorem Frame.sub {i : Time} {s s' : Tree} {D : List NodeId} (h : Frame i s D s')
    {t : Time} (ht : t < i) : Sub (s.at t) (s'.at t) := by
  obtain ⟨h1, _, new, h3, h4⟩ := h
  constructor
  · intro x o hx
    simp only [Tree.at, Option.map_eq_some_iff] at hx ⊢
    obtain ⟨o0, hx0, rfl⟩ := hx
    obtain ⟨o0', hx', hext, _⟩ := h1 x o0 hx0
    exact ⟨o0', hx', hext.at_eq ht⟩
  · simp only [Tree.at, h3, List.filter_append]
    have : new.filter (fun r => decide (r.1 ≤ t)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      have h5 : r.1 = i := h4 r hr
      simp only [decide_eq_true_eq, h5]
      exact Nat.not_le.mpr ht
    simp [this]

variable {p : Params} {s s' : Tree}

theorem nodeOk_sub (hs : Sub s s') {n : KNode} (h : nodeOk p s n = true) :
    nodeOk p s' n = true := by
  simp only [nodeOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  intro k hk
  have := h.2 k hk
  cases k with
  | key c y =>
    simp only [Option.isSome_iff_exists] at this ⊢
    obtain ⟨o, ho⟩ := this
    exact ⟨o, hs.1 y o ho⟩
  | _ => rfl

theorem kidOk_sub (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub sub' : NodeId → Nat → Option Nat → Bool}
    (hsub : ∀ y lo hi, sub y lo hi = true → sub' y lo hi = true)
    {c : Nat} {y : NodeId} {rest : List (Nat × NodeId)}
    (h : kidOk s n lo hi sub c y rest = true) : kidOk s' n lo hi sub' c y rest = true := by
  unfold kidOk at h ⊢
  cases ho : s.obj y with
  | none => simp [ho] at h
  | some o =>
    rw [hs.1 y o ho]
    rw [ho] at h
    cases o with
    | val v => simpa using h
    | key m =>
      by_cases hleaf : n.leaf = true <;> by_cases hlong : isLong c = true <;>
        simp [hleaf, hlong] at h ⊢
      · exact ⟨h.1, h.2.1, h.2.2.1, hsub _ _ _ h.2.2.2⟩
      · exact ⟨h.1, h.2.1, hsub _ _ _ h.2.2⟩
      · exact ⟨h.1, h.2.1, hsub _ _ _ h.2.2⟩

theorem kidsOk_sub (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub sub' : NodeId → Nat → Option Nat → Bool}
    (hsub : ∀ y lo hi, sub y lo hi = true → sub' y lo hi = true) :
    ∀ l : List (Nat × NodeId), kidsOk s n lo hi sub l = true → kidsOk s' n lo hi sub' l = true
  | [], _ => rfl
  | (c, y) :: rest, h => by
    simp only [kidsOk, Bool.and_eq_true] at h ⊢
    exact ⟨kidOk_sub hs hsub h.1, kidsOk_sub hs hsub rest h.2⟩

/-- The walk of the larger tree finds no fault either. -/
theorem walk_sub (hs : Sub s s') : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    walk p s f x lo hi = true → walk p s' f x lo hi = true
  | 0, _, _, _, h => by simp [walk] at h
  | f + 1, x, lo, hi, h => by
    unfold walk at h ⊢
    cases ho : s.obj x with
    | none => simp [ho] at h
    | some o =>
      rw [hs.1 x o ho]
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨nodeOk_sub hs h.1, kidsOk_sub hs (fun y lo hi => walk_sub hs f y lo hi) _ h.2⟩

theorem klongList_sub (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub : NodeId → Nat → Option Nat → Bool} {l l' : NodeId → List (Key × Nat)}
    (hl : ∀ y lo hi, sub y lo hi = true → l' y = l y)
    {c : Nat} {y : NodeId} {rest : List (Nat × NodeId)}
    (h : kidOk s n lo hi sub c y rest = true) :
    klongList s' n.leaf l' c y = klongList s n.leaf l c y := by
  unfold kidOk at h
  unfold klongList
  cases ho : s.obj y with
  | none => simp [ho] at h
  | some o =>
    rw [hs.1 y o ho]
    rw [ho] at h
    cases o with
    | val v =>
      by_cases hleaf : n.leaf = true <;> by_cases hlong : isLong c = true <;>
        simp [hleaf, hlong] at h ⊢
    | key m =>
      by_cases hleaf : n.leaf = true <;> by_cases hlong : isLong c = true <;>
        simp [hleaf, hlong] at h ⊢
      · rw [hl _ _ _ h.2.2.2]
      · rw [hl _ _ _ h.2.2]
      · rw [hl _ _ _ h.2.2]

theorem flatMap_sub (hs : Sub s s') {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub : NodeId → Nat → Option Nat → Bool} {l l' : NodeId → List (Key × Nat)}
    (hl : ∀ y lo hi, sub y lo hi = true → l' y = l y) :
    ∀ cs : List (Nat × NodeId), kidsOk s n lo hi sub cs = true →
      cs.flatMap (fun cy => klongList s' n.leaf l' cy.1 cy.2) =
        cs.flatMap (fun cy => klongList s n.leaf l cy.1 cy.2)
  | [], _ => rfl
  | (c, y) :: rest, h => by
    simp only [kidsOk, Bool.and_eq_true] at h
    simp only [List.flatMap_cons]
    rw [klongList_sub hs hl h.1, flatMap_sub hs hl rest h.2]

/-- The larger tree holds, below a sound node, what the smaller one holds. -/
theorem listAt_sub (hs : Sub s s') : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    walk p s f x lo hi = true → listAt s' f x = listAt s f x
  | 0, _, _, _, h => by simp [walk] at h
  | f + 1, x, lo, hi, h => by
    unfold walk at h
    unfold listAt
    cases ho : s.obj x with
    | none => simp [ho] at h
    | some o =>
      rw [hs.1 x o ho]
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        exact flatMap_sub hs (fun y lo hi hw => listAt_sub hs f y lo hi hw) _ h.2

/-- The invariants carry over to a tree that holds the sound one. -/
theorem invOk_sub (hs : Sub s s') (h : invOk p s = true) : invOk p s' = true := by
  unfold invOk Tree.root at h ⊢
  rw [hs.2]
  cases hr : s.roots.getLast?.map (·.2) with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h ⊢
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [hs.1 r o ho]
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, walk_sub hs _ _ _ _ h.2⟩

/-- And so do the contents. -/
theorem contents_sub (hs : Sub s s') (h : invOk p s = true) : contents s' = contents s := by
  unfold invOk Tree.root at h
  unfold contents Tree.root Tree.fuel
  rw [hs.2]
  cases hr : s.roots.getLast?.map (·.2) with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h ⊢
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [hs.1 r o ho]
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h ⊢
        exact listAt_sub hs _ _ _ _ h.2

/-- Earlier times: after a transaction that meets the frame, the tree at an
earlier time meets the invariants it met, and has the contents it had. -/
theorem Frame.earlier {i : Time} {s s' : Tree} {D : List NodeId} (h : Frame i s D s')
    {t : Time} (ht : t < i) (hi : invOk p (s.at t) = true) :
    invOk p (s'.at t) = true ∧ contents (s'.at t) = contents (s.at t) :=
  ⟨invOk_sub (h.sub ht) hi, contents_sub (h.sub ht) hi⟩

end Contract
