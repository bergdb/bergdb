/-
The contract package (bergdb 030-04): the chain of a scan. What a chain has
before it, at it and after it (`restD`, `atOf`): for a chain that is a path
from the space root, the three make up what the tree holds (`Path.split`).
`Chain.next` gives the first of what is after the chain, in the scan's
direction, and leaves a chain with the rest after it (`nextGo_spec`); so the
loop of a scan gives what is after its first chain (`scanGo_spec`).
-/
import Contract.Proof.Good
import Contract.Proof.Lex

namespace Contract

variable {s : Tree}

/-! ## In the scan's direction -/

/-- A list in the scan's direction. -/
def dir {α : Type} (fwd : Bool) (l : List α) : List α := if fwd then l else l.reverse

/-- A key and value with key segments put in front. -/
def pre (segs : List Nat) (kv : Key × Nat) : Key × Nat := (segs ++ kv.1, kv.2)

/-- What the live klongs cs of key node n hold, below the key segments
`segs`, in key order. -/
def ent (s : Tree) (segs : List Nat) (n : KNode) (cs : List (Nat × NodeId)) : List (Key × Nat) :=
  cs.flatMap (fun cy => (klongList s n.leaf (L s) cy.1 cy.2).map (pre segs))

/-- What the live klongs cs hold, each klong's keys in the scan's direction. -/
def entD (s : Tree) (fwd : Bool) (segs : List Nat) (n : KNode) (cs : List (Nat × NodeId)) :
    List (Key × Nat) :=
  cs.flatMap (fun cy => dir fwd ((klongList s n.leaf (L s) cy.1 cy.2).map (pre segs)))

/-- The live klongs still to visit from position p, in the scan's direction:
those after p, or with `incl` those at or after p. -/
def pend (fwd incl : Bool) (n : KNode) (p : Pos) : List (Nat × NodeId) :=
  if fwd then (live n.ks).filter (fun cy => if incl then !p.above cy.1 else p.below cy.1)
  else ((live n.ks).filter (fun cy => if incl then !p.below cy.1 else p.above cy.1)).reverse

theorem entD_dir (fwd : Bool) (segs : List Nat) (n : KNode) (cs : List (Nat × NodeId)) :
    entD s fwd segs n (dir fwd cs) = dir fwd (ent s segs n cs) := by
  cases fwd with
  | true => rfl
  | false =>
    simp only [entD, ent, dir, Bool.false_eq_true, ite_false]
    rw [List.reverse_flatMap]
    rfl

theorem entD_cons (fwd : Bool) (segs : List Nat) (n : KNode) (c : Nat) (y : NodeId)
    (cs : List (Nat × NodeId)) :
    entD s fwd segs n ((c, y) :: cs) =
      dir fwd ((klongList s n.leaf (L s) c y).map (pre segs)) ++ entD s fwd segs n cs := by
  simp [entD]

theorem ent_append (segs : List Nat) (n : KNode) (a b : List (Nat × NodeId)) :
    ent s segs n (a ++ b) = ent s segs n a ++ ent s segs n b := by
  simp [ent]

/-! ## The live klongs around a position -/

/-- The live klongs in order: those below a position, the one at it, those
above it. -/
theorem sorted_split3 {l : List (Nat × NodeId)} (hs : l.Pairwise CvLt) (p : Pos) :
    l = l.filter (fun cy => p.above cy.1) ++ l.filter (fun cy => p.is cy.1) ++
      l.filter (fun cy => p.below cy.1) := by
  cases p with
  | lo => simp [Pos.above, Pos.is, Pos.below]
  | hi => simp [Pos.above, Pos.is, Pos.below]
  | «at» d =>
    induction l with
    | nil => simp
    | cons a r ih =>
      rw [List.pairwise_cons] at hs
      have ih := ih hs.2
      simp only [Pos.above, Pos.is, Pos.below, List.filter_cons] at ih ⊢
      rcases lt_trichotomy a.1 d with h | h | h
      · have h1 : ¬ d < a.1 := by omega
        have h2 : ¬ a.1 = d := by omega
        simp only [h, h1, h2, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
          beq_iff_eq, List.cons_append]
        rw [← ih]
      · have hr : ∀ b ∈ r, d < b.1 := fun b hb => by have := hs.1 b hb; unfold CvLt at this; omega
        have e1 : r.filter (fun cy => decide (cy.1 < d)) = [] := by
          rw [List.filter_eq_nil_iff]; intro b hb; have := hr b hb; simp; omega
        have e2 : r.filter (fun cy => cy.1 == d) = [] := by
          rw [List.filter_eq_nil_iff]; intro b hb; have := hr b hb; simp; omega
        have e3 : r.filter (fun cy => decide (d < cy.1)) = r := by
          rw [List.filter_eq_self]; intro b hb; have := hr b hb; simp; omega
        simp [h, e1, e2, e3]
      · have hr : ∀ b ∈ r, d < b.1 := fun b hb => by have := hs.1 b hb; unfold CvLt at this; omega
        have e1 : r.filter (fun cy => decide (cy.1 < d)) = [] := by
          rw [List.filter_eq_nil_iff]; intro b hb; have := hr b hb; simp; omega
        have e2 : r.filter (fun cy => cy.1 == d) = [] := by
          rw [List.filter_eq_nil_iff]; intro b hb; have := hr b hb; simp; omega
        have e3 : r.filter (fun cy => decide (d < cy.1)) = r := by
          rw [List.filter_eq_self]; intro b hb; have := hr b hb; simp; omega
        have h1 : ¬ a.1 < d := by omega
        have h2 : ¬ a.1 = d := by omega
        simp [h, h1, h2, e1, e2, e3]

/-- The live klongs around one of them. -/
theorem live_split3 {ks : List Klong} {pre' post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live ks = pre' ++ (c, y) :: post) :
    (live ks).filter (fun cy => (Pos.at c).above cy.1) = pre' ∧
    (live ks).filter (fun cy => (Pos.at c).is cy.1) = [(c, y)] ∧
    (live ks).filter (fun cy => (Pos.at c).below cy.1) = post := by
  obtain ⟨h1, h2, _⟩ := live_split he
  rw [he]
  simp only [List.filter_append, List.filter_cons, Pos.above, Pos.is, Pos.below]
  have e1 : pre'.filter (fun cy => decide (cy.1 < c)) = pre' := by
    rw [List.filter_eq_self]; intro b hb; have := h1 b hb; simp; omega
  have e2 : pre'.filter (fun cy => cy.1 == c) = [] := by
    rw [List.filter_eq_nil_iff]; intro b hb; have := h1 b hb; simp; omega
  have e3 : pre'.filter (fun cy => decide (c < cy.1)) = [] := by
    rw [List.filter_eq_nil_iff]; intro b hb; have := h1 b hb; simp; omega
  have e4 : post.filter (fun cy => decide (cy.1 < c)) = [] := by
    rw [List.filter_eq_nil_iff]; intro b hb; have := h2 b hb; simp; omega
  have e5 : post.filter (fun cy => cy.1 == c) = [] := by
    rw [List.filter_eq_nil_iff]; intro b hb; have := h2 b hb; simp; omega
  have e6 : post.filter (fun cy => decide (c < cy.1)) = post := by
    rw [List.filter_eq_self]; intro b hb; have := h2 b hb; simp; omega
  simp [e1, e2, e3, e4, e5, e6]

theorem filter_filter_imp {α : Type} {l : List α} {r q : α → Bool}
    (h : ∀ a ∈ l, r a = true → q a = true) : (l.filter q).filter r = l.filter r := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro a ha
  cases hr : r a with
  | false => simp
  | true => simp [h a ha hr]

/-- The search of `next` gives the first klong still to visit. -/
theorem nextSearch_pend (fwd incl : Bool) (n : KNode) (p : Pos) :
    nextSearch fwd incl n.ks p = (pend fwd incl n p).head? := by
  unfold nextSearch pend
  cases fwd <;> cases incl <;>
    simp [searchGte_spec, searchLte_spec, searchGt_spec, searchLt_spec, List.head?_reverse]

/-- After the first klong to visit, the klongs after its position are left. -/
theorem pend_tail {fwd incl : Bool} {n : KNode} {p : Pos} {c : Nat} {y : NodeId}
    {cs : List (Nat × NodeId)} (h : pend fwd incl n p = (c, y) :: cs) :
    pend fwd false n (.at c) = cs := by
  have hs := live_sorted n.ks
  cases fwd with
  | true =>
    simp only [pend, ite_true, Bool.false_eq_true, ite_false] at h ⊢
    have hsf := hs.filter (fun cy => if incl = true then !p.above cy.1 else p.below cy.1)
    rw [h, List.pairwise_cons] at hsf
    have hq : (if incl = true then !p.above c else p.below c) = true := by
      have : (c, y) ∈ (live n.ks).filter
          (fun cy => if incl = true then !p.above cy.1 else p.below cy.1) := by rw [h]; simp
      exact (List.mem_filter.mp this).2
    rw [← filter_filter_imp (q := fun cy => if incl = true then !p.above cy.1 else p.below cy.1), h]
    · rw [List.filter_cons]
      have e1 : (Pos.at c).below c = false := by simp [Pos.below]
      simp only [e1, Bool.false_eq_true, ite_false]
      rw [List.filter_eq_self]
      intro b hb
      have := hsf.1 b hb
      simp only [Pos.below, decide_eq_true_eq]
      exact this
    · intro a _ ha
      simp only [Pos.below, decide_eq_true_eq] at ha
      cases incl with
      | true =>
        simp only [ite_true, Bool.not_eq_true'] at hq ⊢
        rw [← Bool.not_eq_true, Pos.above_iff] at hq ⊢
        intro h1
        exact hq (lt_trans (Pos.at_lt_at.mpr ha) h1)
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hq ⊢
        rw [Pos.below_iff] at hq ⊢
        exact lt_trans hq (Pos.at_lt_at.mpr ha)
  | false =>
    simp only [pend, Bool.false_eq_true, ite_false] at h ⊢
    have h' : (live n.ks).filter (fun cy => if incl = true then !p.below cy.1 else p.above cy.1) =
        cs.reverse ++ [(c, y)] := by
      rw [← List.reverse_reverse (List.filter _ _), h]; simp
    have hsf := hs.filter (fun cy => if incl = true then !p.below cy.1 else p.above cy.1)
    rw [h', List.pairwise_append] at hsf
    have hq : (if incl = true then !p.below c else p.above c) = true := by
      have : (c, y) ∈ (live n.ks).filter
          (fun cy => if incl = true then !p.below cy.1 else p.above cy.1) := by rw [h']; simp
      exact (List.mem_filter.mp this).2
    rw [← filter_filter_imp (q := fun cy => if incl = true then !p.below cy.1 else p.above cy.1), h']
    · rw [List.filter_append, List.filter_cons]
      have e1 : (Pos.at c).above c = false := by simp [Pos.above]
      simp only [e1, Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil]
      have e2 : cs.reverse.filter (fun cy => (Pos.at c).above cy.1) = cs.reverse := by
        rw [List.filter_eq_self]
        intro b hb
        have := hsf.2.2 b hb (c, y) (by simp)
        simp only [Pos.above, decide_eq_true_eq]
        exact this
      rw [e2, List.reverse_reverse]
    · intro a _ ha
      simp only [Pos.above, decide_eq_true_eq] at ha
      cases incl with
      | true =>
        simp only [ite_true, Bool.not_eq_true'] at hq ⊢
        rw [← Bool.not_eq_true, Pos.below_iff] at hq ⊢
        intro h1
        exact hq (lt_trans h1 (Pos.at_lt_at.mpr ha))
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hq ⊢
        rw [Pos.above_iff] at hq ⊢
        exact lt_trans (Pos.at_lt_at.mpr ha) hq

/-- From the scan's first position in a node, every live klong is to visit. -/
theorem pend_start (fwd : Bool) (n : KNode) :
    pend fwd false n (if fwd then .lo else .hi) = dir fwd (live n.ks) := by
  cases fwd <;> simp [pend, dir, Pos.below, Pos.above]

/-- A klong still to visit is a live klong. -/
theorem mem_pend {fwd incl : Bool} {n : KNode} {p : Pos} {a : Nat × NodeId}
    (h : a ∈ pend fwd incl n p) : a ∈ live n.ks := by
  cases fwd <;> simp [pend] at h <;> exact h.1

/-! ## What is before a chain, at it and after it -/

/-- What is after a chain in the scan's direction (`fwd`), or before it
(backward): in each link's node, the klongs after the link's position, then
what is after the links above. The links are the last one first, as
`Chain.links`. -/
def restD (s : Tree) (fwd : Bool) : List (NodeId × Pos) → List Nat → List (Key × Nat)
  | [], _ => []
  | (x, p) :: above, segs =>
    match s.obj x with
    | some (.key n) =>
      entD s fwd segs n (pend fwd false n p) ++ restD s fwd above (segsUp s above segs)
    | _ => []

/-- `restD`, with the klong at the last link's position too if `incl`. -/
def restX (s : Tree) (fwd incl : Bool) (links : List (NodeId × Pos)) (segs : List Nat) :
    List (Key × Nat) :=
  match links with
  | [] => []
  | (x, p) :: above =>
    match s.obj x with
    | some (.key n) =>
      entD s fwd segs n (pend fwd incl n p) ++ restD s fwd above (segsUp s above segs)
    | _ => []

theorem restX_false (fwd : Bool) (links : List (NodeId × Pos)) (segs : List Nat) :
    restX s fwd false links segs = restD s fwd links segs := by
  cases links with
  | nil => rfl
  | cons a above => obtain ⟨x, p⟩ := a; rfl

/-- What the klong at the last link's position holds. -/
def atOf (s : Tree) (links : List (NodeId × Pos)) (segs : List Nat) : List (Key × Nat) :=
  match links with
  | [] => []
  | (x, p) :: _ =>
    match s.obj x with
    | some (.key n) => ent s segs n ((live n.ks).filter (fun cy => p.is cy.1))
    | _ => []

/-- A chain that is a path from the space root r: each link's position is
the klong that names the node of the link below it; the key segments are
those of the segment leaves passed. -/
inductive Path (s : Tree) (r : NodeId) : List (NodeId × Pos) → List Nat → Prop where
  | root (p : Pos) : Path s r [(r, p)] []
  | push {x : NodeId} {c : Nat} {y : NodeId} {p : Pos} {above : List (NodeId × Pos)}
      {segs : List Nat} {n m : KNode} :
      Path s r ((x, .at c) :: above) segs → s.obj x = some (.key n) → (c, y) ∈ live n.ks →
      s.obj y = some (.key m) →
      Path s r ((y, p) :: (x, .at c) :: above) (if n.leaf then segs ++ [c] else segs)

theorem Path.setPos {r x : NodeId} {p : Pos} {above : List (NodeId × Pos)} {segs : List Nat}
    (h : Path s r ((x, p) :: above) segs) (p' : Pos) : Path s r ((x, p') :: above) segs := by
  cases h with
  | root => exact Path.root p'
  | push h1 h2 h3 h4 => exact Path.push h1 h2 h3 h4

theorem Good.obj {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∃ n, s.obj x = some (.key n) := by
  cases h with
  | mk _ _ _ n hobj => exact ⟨n, hobj⟩

/-- What a live klong of a sound node names: a value, in a segment leaf for a
short segment; else a sound key node of a lower level, with a live klong. -/
theorem Good.kind {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) {c : Nat} {y : NodeId} (hm : (c, y) ∈ live n.ks) :
    (n.leaf = true ∧ isLong c = false ∧ ∃ v, s.obj y = some (.val v)) ∨
    ((n.leaf = true → isLong c = true) ∧ ∃ m lo' hi', s.obj y = some (.key m) ∧
      m.level < n.level ∧ live m.ks ≠ [] ∧ Good s y lo' hi') := by
  by_cases hk : n.leaf = true → isLong c = true
  · exact Or.inr ⟨hk, h.child hobj hm hk⟩
  · simp only [Classical.not_imp, Bool.not_eq_true] at hk
    cases h with
    | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      exact Or.inl ⟨hk.1, hk.2, hval hk.1 c y hm hk.2⟩

theorem Path.good {r : NodeId} (hG : Good s r 0 none) {links : List (NodeId × Pos)}
    {segs : List Nat} (h : Path s r links segs) :
    ∀ x p above, links = (x, p) :: above → ∃ lo hi, Good s x lo hi := by
  induction h with
  | root p =>
    intro x p' above he
    injection he with h1 _
    injection h1 with h1 _
    subst h1
    exact ⟨0, none, hG⟩
  | push h1 h2 h3 h4 ih =>
    intro x' p' above' he
    injection he with he1 _
    injection he1 with he1 _
    subst he1
    obtain ⟨lo, hi, hg⟩ := ih _ _ _ rfl
    rcases hg.kind h2 h3 with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', _, _, _, hg'⟩
    · rw [h4] at hv; simp at hv
    · exact ⟨lo', hi', hg'⟩

/-- A path is no longer than the root's fuel allows, with the level of its
last node. -/
theorem Path.level {r : NodeId} (hG : Good s r 0 none) {links : List (NodeId × Pos)}
    {segs : List Nat} (h : Path s r links segs) :
    ∀ x p above, links = (x, p) :: above → ∀ n, s.obj x = some (.key n) →
      links.length + n.level ≤ s.fuel r := by
  induction h with
  | root p =>
    intro x p' above he n hn
    injection he with h1 _
    injection h1 with h1 _
    subst h1
    simp [Tree.fuel, hn]
    omega
  | @push x c y p above segs n m h1 h2 h3 h4 ih =>
    intro x' p' above' he n' hn'
    injection he with he1 _
    injection he1 with he1 _
    subst he1
    have h5 := ih _ _ _ rfl n h2
    obtain ⟨lo, hi, hg⟩ := h1.good hG _ _ _ rfl
    rcases hg.kind h2 h3 with ⟨_, _, v, hv⟩ | ⟨_, m', lo', hi', hm', hlt, _, _⟩
    · rw [h4] at hv; simp at hv
    · rw [hn'] at hm'
      obtain rfl : n' = m' := by injection hm' with h6; injection h6
      simp only [List.length_cons] at h5 ⊢
      omega

theorem segsUp_push {x : NodeId} {n : KNode} (h : s.obj x = some (.key n)) (q : Pos)
    (above : List (NodeId × Pos)) (segs : List Nat) (c : Nat) :
    segsUp s ((x, q) :: above) (if n.leaf then segs ++ [c] else segs) = segs := by
  simp only [segsUp, h]
  cases n.leaf <;> simp

/-- A path without its last link is a path, or nothing. -/
theorem Path.pop {r x : NodeId} {p : Pos} {above : List (NodeId × Pos)} {segs : List Nat}
    (h : Path s r ((x, p) :: above) segs) : above = [] ∨ Path s r above (segsUp s above segs) := by
  cases h with
  | root => exact Or.inl rfl
  | push h1 h2 h3 h4 =>
    right
    rw [segsUp_push h2]
    exact h1

theorem entD_true (segs : List Nat) (n : KNode) (cs : List (Nat × NodeId)) :
    entD s true segs n cs = ent s segs n cs := rfl

theorem entD_false_reverse (segs : List Nat) (n : KNode) (cs : List (Nat × NodeId)) :
    (entD s false segs n cs.reverse).reverse = ent s segs n cs := by
  have := entD_dir (s := s) false segs n cs
  simp only [dir, Bool.false_eq_true, ite_false] at this
  rw [this, List.reverse_reverse]

/-- What the live klongs of a sound node hold is what the node holds. -/
theorem Good.ent_live {y : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s y lo hi) {m : KNode}
    (hobj : s.obj y = some (.key m)) (segs : List Nat) :
    ent s segs m (live m.ks) = (L s y).map (pre segs) := by
  rw [h.L_eq hobj, List.map_flatMap]
  rfl

/-- What the klong of a key node below holds: what that node holds, below
the key segments that the klong leaves. -/
theorem klong_child {n m : KNode} {c : Nat} {y : NodeId} (_hy : s.obj y = some (.key m))
    (hk : n.leaf = true → isLong c = true) (segs : List Nat) :
    (klongList s n.leaf (L s) c y).map (pre segs) =
      (L s y).map (pre (if n.leaf then segs ++ [c] else segs)) := by
  unfold klongList
  cases hl : n.leaf with
  | false => simp
  | true =>
    simp only [hk hl, ite_true, List.map_map]
    apply List.map_congr_left
    intro kv _
    simp [pre]

/-- For a chain that is a path, what the tree holds is what is before the
chain, what is at it, and what is after it. -/
theorem Path.split {r : NodeId} (hG : Good s r 0 none) {links : List (NodeId × Pos)}
    {segs : List Nat} (h : Path s r links segs) :
    L s r = (restD s false links segs).reverse ++ atOf s links segs ++
      restD s true links segs := by
  have hnode : ∀ (y : NodeId) (m : KNode) (lo : Nat) (hi : Option Nat), Good s y lo hi →
      s.obj y = some (.key m) → ∀ (sg : List Nat) (p : Pos),
      (L s y).map (pre sg) =
        (entD s false sg m (pend false false m p)).reverse ++
          ent s sg m ((live m.ks).filter (fun cy => p.is cy.1)) ++
          entD s true sg m (pend true false m p) := by
    intro y m lo hi hg hy sg p
    rw [← hg.ent_live hy sg]
    conv_lhs => rw [sorted_split3 (live_sorted m.ks) p]
    simp only [ent_append, pend, Bool.false_eq_true, ite_false, ite_true, entD_false_reverse,
      entD_true]
  induction h with
  | root p =>
    obtain ⟨n, hn⟩ := hG.obj
    have := hnode r n 0 none hG hn [] p
    simp only [restD, atOf, hn, List.append_nil]
    rw [← this]
    have hid : pre ([] : List Nat) = id := by funext kv; simp [pre]
    rw [hid, List.map_id]
  | @push x c y p above segs n m h1 h2 h3 h4 ih =>
    obtain ⟨lo, hi, hg⟩ := h1.good hG _ _ _ rfl
    rcases hg.kind h2 h3 with ⟨_, _, v, hv⟩ | ⟨hk, m', lo', hi', hm', _, _, hg'⟩
    · rw [h4] at hv; simp at hv
    · have hat : atOf s ((x, Pos.at c) :: above) segs =
          (L s y).map (pre (if n.leaf then segs ++ [c] else segs)) := by
        obtain ⟨pre', post, he⟩ := List.append_of_mem h3
        simp only [atOf, h2, (live_split3 he).2.1, ent, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        exact klong_child h4 hk segs
      rw [hnode y m lo' hi' hg' h4 _ p] at hat
      rw [ih, hat]
      simp only [restD, atOf, h4, segsUp_push h2, List.reverse_append, List.append_assoc]

/-! ## The end of a scan's range -/

/-- A key is within the scan's end. -/
def inEnd (req : ScanReq) (k : Key) : Bool :=
  match req.endKey with
  | none => true
  | some e => if req.endInclusive then !keyLt e k else keyLt k e

theorem past_eq (req : ScanReq) (segs : List Nat) (c : Nat) :
    past req segs c = !inEnd req (segs ++ [c]) := by
  unfold past inEnd pastEnd
  cases req.endKey with
  | none => rfl
  | some e =>
    cases req.endInclusive with
    | true => simp
    | false =>
      simp only [Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, keyLt_iff, beq_iff_eq, Bool.not_eq_true', keyLt_false_iff]
      rw [le_iff_lt_or_eq]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr h.symm

theorem inEnd_false_of_le {req : ScanReq} {k k' : Key} (h : inEnd req k = false) (hle : k ≤ k') :
    inEnd req k' = false := by
  unfold inEnd at h ⊢
  cases he : req.endKey with
  | none => simp [he] at h
  | some e =>
    simp only [he] at h ⊢
    cases hi : req.endInclusive with
    | true =>
      simp only [hi, ite_true, Bool.not_eq_false'] at h ⊢
      rw [keyLt_iff] at h ⊢
      exact lt_of_lt_of_le h hle
    | false =>
      simp only [hi, Bool.false_eq_true, ite_false] at h ⊢
      rw [keyLt_false_iff] at h ⊢
      exact le_trans h hle

/-- The klongs at or above a position: the one at it, then those above it. -/
theorem pend_incl_fwd (n : KNode) (p : Pos) :
    pend true true n p = (live n.ks).filter (fun cy => p.is cy.1) ++ pend true false n p := by
  simp only [pend, ite_true, Bool.false_eq_true, ite_false]
  have h3 := sorted_split3 (live_sorted n.ks) p
  have e1 : ((live n.ks).filter (fun cy => p.above cy.1)).filter (fun cy => !p.above cy.1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp [(List.mem_filter.mp ha).2]
  have e2 : ((live n.ks).filter (fun cy => p.is cy.1)).filter (fun cy => !p.above cy.1) =
      (live n.ks).filter (fun cy => p.is cy.1) := by
    rw [List.filter_eq_self]
    intro a ha
    have := (Pos.is_iff p a.1).mp (List.mem_filter.mp ha).2
    rw [Bool.not_eq_true', ← Bool.not_eq_true, Pos.above_iff, this]
    exact lt_irrefl _
  have e3 : ((live n.ks).filter (fun cy => p.below cy.1)).filter (fun cy => !p.above cy.1) =
      (live n.ks).filter (fun cy => p.below cy.1) := by
    rw [List.filter_eq_self]
    intro a ha
    have := (Pos.below_iff p a.1).mp (List.mem_filter.mp ha).2
    rw [Bool.not_eq_true', ← Bool.not_eq_true, Pos.above_iff]
    exact not_lt_of_gt this
  conv_lhs => rw [h3]
  rw [List.filter_append, List.filter_append, e1, e2, e3, List.nil_append]

/-- In an inner node, a key below the child of the klong with compare value
c starts at or above c. -/
theorem Good.kid_lower {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) (hl : n.leaf = false) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) :
    ∀ k v, (k, v) ∈ L s y → ∃ d r', k = d :: r' ∧ c ≤ d := by
  cases h with
  | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    obtain ⟨pre', post, he⟩ := List.append_of_mem hm
    intro k v hkv
    obtain ⟨d, r', hd, hd1, _⟩ := (hkid hl pre' c y post he).range k v hkv
    exact ⟨d, r', hd, le_trans (le_max_right _ _) hd1⟩

/-- Forward, every key from the klong found on is at or after the key
segments passed and the klong's compare value (`Chain.isPastEnd`'s reason). -/
theorem lower_bound {r : NodeId} (hG : Good s r 0 none) {x : NodeId} {p : Pos}
    {above : List (NodeId × Pos)} {segs : List Nat} {n : KNode}
    (hpath : Path s r ((x, p) :: above) segs) (hobj : s.obj x = some (.key n)) {incl : Bool}
    {c : Nat} {y : NodeId} {cs : List (Nat × NodeId)} (hp : pend true incl n p = (c, y) :: cs) :
    ∀ kv ∈ entD s true segs n (pend true incl n p) ++ restD s true above (segsUp s above segs),
      segs ++ [c] ≤ kv.1 := by
  obtain ⟨lo, hi, hgx⟩ := hpath.good hG _ _ _ rfl
  have hm : (c, y) ∈ live n.ks := mem_pend (by rw [hp]; simp)
  -- what is left is the end of what the tree holds, so it is in order
  have hsuf : ∃ B, L s r = B ++ (entD s true segs n (pend true incl n p) ++
      restD s true above (segsUp s above segs)) := by
    have hsp := hpath.split hG
    simp only [restD, atOf, hobj] at hsp
    cases incl with
    | false => exact ⟨_, by rw [hsp]⟩
    | true =>
      refine ⟨(entD s false segs n (pend false false n p) ++
        restD s false above (segsUp s above segs)).reverse, ?_⟩
      rw [hsp, pend_incl_fwd]
      simp only [entD_true, ent_append, List.append_assoc]
  obtain ⟨B, hB⟩ := hsuf
  have hsorted : (entD s true segs n (pend true incl n p) ++
      restD s true above (segsUp s above segs)).Pairwise KvLt := by
    have := hG.sorted
    rw [hB, List.pairwise_append] at this
    exact this.2.1
  rw [hp, entD_cons] at hsorted ⊢
  simp only [dir, ite_true, List.append_assoc] at hsorted ⊢
  -- the keys of the klong found
  have hE : ∀ kv ∈ (klongList s n.leaf (L s) c y).map (pre segs), segs ++ [c] ≤ kv.1 := by
    intro kv hkv
    obtain ⟨⟨k, v⟩, hk0, rfl⟩ := List.mem_map.mp hkv
    simp only [pre]
    rw [append_le_append_iff]
    rcases mem_klongList.mp hk0 with ⟨_, _, k', rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl, hkv⟩
    · exact singleton_le_cons c k'
    · exact le_refl _
    · obtain ⟨d, r', rfl, hd⟩ := hgx.kid_lower hobj hl hm k v hkv
      rcases lt_or_eq_of_le hd with h | h
      · exact le_of_lt (cons_lt_cons_of_lt h _ _)
      · subst h; exact singleton_le_cons c r'
  have hne : (klongList s n.leaf (L s) c y).map (pre segs) ≠ [] := by
    rcases hgx.kind hobj hm with ⟨hl, hlong, v, hv⟩ | ⟨hk, m, lo', hi', hy, _, hne, hgy⟩
    · simp [klongList, hl, hlong, hv]
    · rw [klong_child hy hk]
      simp only [ne_eq, List.map_eq_nil_iff]
      exact hgy.nonempty m hy hne
  intro kv hkv
  rcases List.mem_append.mp hkv with h | h
  · exact hE kv h
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    rw [List.pairwise_append] at hsorted
    exact le_of_lt (lt_of_le_of_lt (hE a ha) (hsorted.2.2 a ha kv h))

/-! ## `Chain.next` -/

/-- `Chain.next` on a chain that is a path, with fuel enough to climb the
chain and to descend, or to descend from a node just entered: it ends only
if no key within the scan's end is left; else it gives the first key left
and a chain with the rest after it. -/
theorem nextGo_spec {r : NodeId} (hG : Good s r 0 none) (req : ScanReq)
    (hend : req.endKey ≠ none → req.forward = true) :
    ∀ (f : Nat) (ch : Chain), (ch.links = [] ∨ Path s r ch.links ch.segs) →
      (ch.links.length + s.fuel r + 1 ≤ f ∨
        (ch.first = false ∧ ∃ y above m,
          ch.links = (y, if req.forward then Pos.lo else Pos.hi) :: above ∧
          s.obj y = some (.key m) ∧ live m.ks ≠ [] ∧ m.level + 1 ≤ f)) →
      ∀ res ch', nextGo s req f ch = (res, ch') →
        (res = none → ∀ kv ∈ restX s req.forward (ch.first && req.inclusive && ch.eqMatch)
          ch.links ch.segs, inEnd req kv.1 = false) ∧
        (∀ kv, res = some kv →
          restX s req.forward (ch.first && req.inclusive && ch.eqMatch) ch.links ch.segs =
            kv :: restD s req.forward ch'.links ch'.segs ∧
          inEnd req kv.1 = true ∧ Path s r ch'.links ch'.segs ∧ ch'.first = false) := by
  intro f
  induction f with
  | zero =>
    intro ch _ hf
    rcases hf with hf | ⟨_, y, above, m, _, _, _, hf⟩
    · omega
    · omega
  | succ f ih =>
    intro ch hp hf res ch' hn
    obtain ⟨links, segs, first, eqm⟩ := ch
    simp only at hp hf ⊢
    cases links with
    | nil =>
      simp only [nextGo] at hn
      injection hn with h1 h2
      subst h1
      exact ⟨fun _ kv hkv => by simp [restX] at hkv, fun kv h => by simp at h⟩
    | cons a above =>
      obtain ⟨x, p⟩ := a
      have hpath : Path s r ((x, p) :: above) segs := by
        rcases hp with h | h
        · simp at h
        · exact h
      obtain ⟨lo, hi, hgx⟩ := hpath.good hG _ _ _ rfl
      obtain ⟨n, hobj⟩ := hgx.obj
      simp only [nextGo, hobj] at hn
      rw [nextSearch_pend] at hn
      have hrx : restX s req.forward (first && req.inclusive && eqm) ((x, p) :: above) segs =
          entD s req.forward segs n (pend req.forward (first && req.inclusive && eqm) n p) ++
            restD s req.forward above (segsUp s above segs) := by
        simp [restX, hobj]
      rw [hrx]
      cases hpd : pend req.forward (first && req.inclusive && eqm) n p with
      | nil =>
        rw [hpd] at hn
        simp only [List.head?_nil] at hn
        have hp1 : above = [] ∨ Path s r above (segsUp s above segs) := hpath.pop
        have hf1 : above.length + s.fuel r + 1 ≤ f ∨
            ((false : Bool) = false ∧ ∃ y above' m,
              above = (y, if req.forward then Pos.lo else Pos.hi) :: above' ∧
              s.obj y = some (.key m) ∧ live m.ks ≠ [] ∧ m.level + 1 ≤ f) := by
          left
          rcases hf with hf | ⟨hfirst, y, above', m, hl, hy, hne, _⟩
          · simp only [List.length_cons] at hf; omega
          · exfalso
            injection hl with h1 h2
            injection h1 with h1 h3
            subst h1 h3
            rw [hobj] at hy
            obtain rfl : n = m := by injection hy with h6; injection h6
            simp only [hfirst, Bool.false_and] at hpd
            rw [pend_start] at hpd
            cases hfw : req.forward <;> simp [dir, hfw] at hpd <;> exact hne hpd
        have := ih _ hp1 hf1 res ch' hn
        simp only [Bool.false_and, restX_false] at this
        simpa [entD] using this
      | cons a cs =>
        obtain ⟨c, y⟩ := a
        rw [hpd] at hn
        simp only [List.head?_cons] at hn
        have hm : (c, y) ∈ live n.ks := mem_pend (by rw [hpd]; simp)
        rw [past_eq] at hn
        by_cases hin : inEnd req (segs ++ [c]) = true
        · simp only [hin, Bool.not_true, Bool.false_eq_true, ite_false] at hn
          rcases hgx.kind hobj hm with ⟨hl, hlong, v, hv⟩ | ⟨hk, m, lo', hi', hy, hlt, hne, hgy⟩
          · simp only [hv] at hn
            injection hn with h1 h2
            subst h1 h2
            refine ⟨fun h => by simp at h, ?_⟩
            intro kv hkv
            injection hkv with hkv
            subst hkv
            refine ⟨?_, hin, hpath.setPos _, rfl⟩
            have hkl : klongList s n.leaf (L s) c y = [([c], v)] := by
              simp [klongList, hl, hlong, hv]
            have hd : ∀ a : Key × Nat, dir req.forward [a] = [a] := by
              intro a; cases req.forward <;> rfl
            simp only [entD_cons, restD, hobj, pend_tail hpd, hkl, List.map_cons, List.map_nil,
              hd, pre, List.cons_append, List.nil_append]
          · simp only [hy] at hn
            have hp2 : Path s r ((y, if req.forward then Pos.lo else Pos.hi) :: (x, Pos.at c) ::
                above) (if n.leaf then segs ++ [c] else segs) :=
              Path.push (hpath.setPos _) hobj hm hy
            have hlv := hpath.level hG _ _ _ rfl n hobj
            have hf2 : ((y, if req.forward then Pos.lo else Pos.hi) :: (x, Pos.at c) ::
                above).length + s.fuel r + 1 ≤ f ∨
                ((false : Bool) = false ∧ ∃ y' above' m',
                  ((y, if req.forward then Pos.lo else Pos.hi) :: (x, Pos.at c) :: above) =
                    (y', if req.forward then Pos.lo else Pos.hi) :: above' ∧
                  s.obj y' = some (.key m') ∧ live m'.ks ≠ [] ∧ m'.level + 1 ≤ f) := by
              refine Or.inr ⟨rfl, y, _, m, rfl, hy, hne, ?_⟩
              rcases hf with hf | ⟨_, y', above', m', hl', hy', _, hf⟩
              · simp only [List.length_cons] at hf hlv; omega
              · injection hl' with h1 _
                injection h1 with h1 _
                subst h1
                rw [hobj] at hy'
                obtain rfl : n = m' := by injection hy' with h6; injection h6
                omega
            have := ih _ (Or.inr hp2) hf2 res ch' hn
            simp only [Bool.false_and, restX_false] at this
            have heq : entD s req.forward segs n ((c, y) :: cs) ++
                restD s req.forward above (segsUp s above segs) =
                restD s req.forward ((y, if req.forward then Pos.lo else Pos.hi) ::
                  (x, Pos.at c) :: above) (if n.leaf then segs ++ [c] else segs) := by
              simp only [restD, hy, hobj, segsUp_push hobj, pend_start, entD_dir, entD_cons,
                pend_tail hpd, List.append_assoc]
              rw [hgy.ent_live hy, klong_child hy hk]
            rw [heq]
            exact this
        · simp only [Bool.not_eq_true] at hin
          simp only [hin, Bool.not_false, ite_true] at hn
          injection hn with h1 h2
          subst h1
          refine ⟨fun _ => ?_, fun kv h => by simp at h⟩
          have hfw : req.forward = true := hend (by intro h0; simp [inEnd, h0] at hin)
          intro kv hkv
          rw [hfw] at hkv hpd
          rw [← hpd] at hkv
          exact inEnd_false_of_le hin (lower_bound hG hpath hobj hpd kv hkv)

/-- The loop of a scan gives what is left after its chain, within the scan's
end, the first `limit`. -/
theorem scanGo_spec {r : NodeId} (hG : Good s r 0 none) (req : ScanReq)
    (hend : req.endKey ≠ none → req.forward = true) (nf : Nat) (hnf : 2 * s.fuel r + 1 ≤ nf) :
    ∀ (limit : Nat) (ch : Chain), (ch.links = [] ∨ Path s r ch.links ch.segs) →
      scanGo s req nf limit ch =
        ((restX s req.forward (ch.first && req.inclusive && ch.eqMatch) ch.links ch.segs).filter
          (fun kv => inEnd req kv.1)).take limit := by
  intro limit
  induction limit with
  | zero => intro ch _; simp [scanGo]
  | succ limit ih =>
    intro ch hp
    have hfuel : ch.links.length + s.fuel r + 1 ≤ nf := by
      rcases hp with h | h
      · rw [h]; simp only [List.length_nil]; omega
      · cases hl : ch.links with
        | nil => simp only [List.length_nil]; omega
        | cons a above =>
          obtain ⟨x, p⟩ := a
          rw [hl] at h
          obtain ⟨lo, hi, hgx⟩ := h.good hG _ _ _ rfl
          obtain ⟨n, hobj⟩ := hgx.obj
          have := h.level hG _ _ _ rfl n hobj
          omega
    unfold scanGo
    cases hn : nextGo s req nf ch with
    | mk res ch' =>
      obtain ⟨h1, h2⟩ := nextGo_spec hG req hend nf ch hp (Or.inl hfuel) res ch' hn
      cases res with
      | none =>
        simp only
        have : (restX s req.forward (ch.first && req.inclusive && ch.eqMatch) ch.links
            ch.segs).filter (fun kv => inEnd req kv.1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro kv hkv
          simp [h1 rfl kv hkv]
        rw [this]
        rfl
      | some kv =>
        obtain ⟨h3, h4, h5, h6⟩ := h2 kv rfl
        simp only
        rw [h3, List.filter_cons, h4, ih ch' (Or.inr h5), h6]
        simp only [ite_true, Bool.false_and, restX_false, List.take_succ_cons]

end Contract
