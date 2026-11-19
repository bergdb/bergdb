/-
bergdb 026-24 (copied for 030-21), phase 3, a step beyond the two lemmas: the proof's part 1 for
the keys (026-23, 1.2: "plan and settle keep the keys (the concatenation of
the lists is the old one with the operations applied)"), through the whole
recursion of plan, for keys of one segment, on an abstract tree of lists.

A node of height h is a list of entries (`Node h`): a segment leaf (h = 0)
holds (compare value, value); an inner node (compare value, child), each
child a node of height h - 1. A key of several segments is the same
recursion once more for each segment's tree; not done here.

PE's plan is stated as a relation (`Plan`), so that what is proved holds for
every choice PE makes (M1's neighbour, h and c, how many parts): a leaf gets
the operations applied; an inner node's operations are divided among its
children by its live list (`Routed`), each child with operations is
planned, and the children are settled by any sequence of `Settle`'s steps
(drop an empty child, join two neighbours, cut a list into pieces), where a
child's own list may be settled again one level down (`Sett.down`: a join
of two inner nodes rebalanced at its boundary); then the first entry gets
the empty key.

Proved (`Plan.keys`): the contents of the planned node are the old
contents with the operations applied, if the old node holds its keys in its
children's ranges (`Holds`).
-/
import Contract.Proof.PeSettle

namespace PeProof.Abs

open PeProof Contract.PE

/-- What a node of height h holds in an entry: a value (h = 0), or a child of
height h - 1 (its entries). -/
def Elem : Nat → Type
  | 0 => Nat
  | h + 1 => List (Nat × Elem h)

/-- A node of height h: its entries. -/
abbrev Node (h : Nat) := List (Nat × Elem h)

/-- The entries of a node of height h + 1 are children of height h. -/
def kids {h : Nat} (es : Node (h + 1)) : List (Nat × Node h) := es

def ofKids {h : Nat} (ks : List (Nat × Node h)) : Node (h + 1) := ks

/-! ## The plain map -/

/-- An operation at a compare value: a put of a value, or a delete. -/
inductive Op where
  | put (c v : Nat)
  | del (c : Nat)
  deriving DecidableEq, Repr

def Op.cv : Op → Nat
  | .put c _ => c
  | .del c => c

/-- A put in the plain map, in compare order. -/
def mput (c v : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(c, v)]
  | (c', v') :: r => if c < c' then (c, v) :: (c', v') :: r
    else if c = c' then (c, v) :: r else (c', v') :: mput c v r

def applyOp (m : List (Nat × Nat)) : Op → List (Nat × Nat)
  | .put c v => mput c v m
  | .del c => m.filter (fun e => e.1 != c)

/-- The operations applied to the plain map, in their order. -/
def applyOps (ops : List Op) (m : List (Nat × Nat)) : List (Nat × Nat) := ops.foldl applyOp m

/-! ## Contents -/

/-- What a node of height h holds: its leaves' entries, in order. -/
def content : (h : Nat) → Node h → List (Nat × Nat)
  | 0, es => es
  | h + 1, es => (kids es).flatMap (fun e => content h e.2)

/-- A node holds its keys in its children's ranges (the old tree, for the
routing): a leaf's entries in strictly increasing order and in [lo, hi); an
inner node has a child, and its k-th child holds its keys in [lo, c1) for the
first, [ck, ck+1) for the others, ck+1 the next child's compare value, or hi
for the last, the bounds increasing. -/
def HoldsKids {β : Type} (H : Nat → Option Nat → β → Prop) (lo : Nat) (hi : Option Nat) :
    List (Nat × β) → Prop
  | [] => False
  | [(_, x)] => H lo hi x
  | (_, x) :: (c', y) :: r => lo ≤ c' ∧ Below c' hi ∧ H lo (some c') x ∧ HoldsKids H c' hi ((c', y) :: r)

def Holds : (h : Nat) → Nat → Option Nat → Node h → Prop
  | 0, lo, hi, es => (es : List (Nat × Nat)).Pairwise CvLtA ∧ ∀ e ∈ (es : List (Nat × Nat)), lo ≤ e.1 ∧ Below e.1 hi
  | h + 1, lo, hi, es => HoldsKids (Holds h) lo hi (kids es)

/-! ## Plan, as a relation -/

/-- The operations of each child, by the node's live list: the first child
every operation below the second compare value, each other child those from
its compare value to the next one's (`Pe.plan`'s division). -/
def route {β : Type} : List (Nat × β) → List Op → List (List Op)
  | [], _ => []
  | [_], ops => [ops]
  | _ :: (c', y) :: r, ops =>
    ops.filter (fun o => decide (o.cv < c')) :: route ((c', y) :: r) (ops.filter (fun o => decide (c' ≤ o.cv)))

/-- The children, each with its operations: unchanged if it has none, else
planned by P. -/
inductive Routed {β : Type} (P : β → List Op → β → Prop) :
    List (Nat × β) → List (List Op) → List (Nat × β) → Prop
  | nil : Routed P [] [] []
  | keep (c : Nat) (x : β) (ks : List (Nat × β)) (os : List (List Op)) (ks' : List (Nat × β)) :
      Routed P ks os ks' → Routed P ((c, x) :: ks) ([] :: os) ((c, x) :: ks')
  | plan (c : Nat) (x : β) (o : List Op) (x' : β) (ks : List (Nat × β)) (os : List (List Op))
      (ks' : List (Nat × β)) :
      P x o x' → Routed P ks os ks' → Routed P ((c, x) :: ks) (o :: os) ((c, x') :: ks')

/-- Settle of a parent's children of height h: `Settle`'s steps, and a child's
own list settled again one level down. -/
inductive Sett : (h : Nat) → List (Nat × Node h) → List (Nat × Node h) → Prop
  | refl (h : Nat) (ks : List (Nat × Node h)) : Sett h ks ks
  | step (h : Nat) (ks ks' ks'' : List (Nat × Node h)) :
      Step (h != 0) ks ks' → Sett h ks' ks'' → Sett h ks ks''
  | down (h : Nat) (pre post : List (Nat × Node (h + 1))) (c : Nat) (J J' : Node (h + 1))
      (ks'' : List (Nat × Node (h + 1))) :
      Sett h (kids J) (kids J') → Sett (h + 1) (pre ++ (c, J') :: post) ks'' →
      Sett (h + 1) (pre ++ (c, J) :: post) ks''

/-- PE's plan of a node of height h with the operations ops (in the node's
range): the planned node es'. Settle leaves no empty child (`rebalance` drops
them first; a join or a cut makes none). -/
def Plan : (h : Nat) → Node h → List Op → Node h → Prop
  | 0, es, ops, es' => es' = applyOps ops es
  | h + 1, es, ops, es' => ∃ ks' ks'', Routed (Plan h) (kids es) (route (kids es) ops) ks' ∧
      Sett h ks' ks'' ∧ (∀ e ∈ ks'', e.2 ≠ []) ∧ kids es' = renameHead 0 ks''

/-! ## Settle keeps the contents -/

/-- What a list of children of height h holds. -/
def kidsContent (h : Nat) (ks : List (Nat × Node h)) : List (Nat × Nat) :=
  ks.flatMap (fun e => content h e.2)

theorem renameHead_flatMap {β γ : Type} (c : Nat) (g : β → List γ) (l : List (Nat × β)) :
    (renameHead c l).flatMap (fun e => g e.2) = l.flatMap (fun e => g e.2) := by
  cases l with
  | nil => rfl
  | cons a r => obtain ⟨_, _⟩ := a; rfl

theorem eff_flatMap {β γ : Type} (inner : Bool) (g : β → List γ) (e : Nat × List (Nat × β)) :
    (eff inner e).flatMap (fun x => g x.2) = e.2.flatMap (fun x => g x.2) := by
  unfold eff
  split
  · exact renameHead_flatMap _ _ _
  · rfl

/-- What leaves hold, from the child level read as one list. -/
theorem kidsContent_zero (ks : List (Nat × Node 0)) : kidsContent 0 ks = flat false ks := by
  unfold kidsContent flat
  congr 1

/-- What inner children hold, from the child level read as one list. -/
theorem kidsContent_succ (h' : Nat) (ks : List (Nat × Node (h' + 1))) :
    kidsContent (h' + 1) ks = (flat true ks).flatMap (fun e => content h' e.2) := by
  unfold kidsContent flat
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro e _
  show List.flatMap (fun x => content h' x.2) (e.2 : List (Nat × Node h')) =
    List.flatMap (fun x => content h' x.2) (renameHead e.1 (e.2 : List (Nat × Node h')))
  exact (renameHead_flatMap e.1 (fun x => content h' x) _).symm

theorem Step.kidsContent {h : Nat} {ks ks' : List (Nat × Node h)} (hs : Step (h != 0) ks ks') :
    kidsContent h ks' = kidsContent h ks := by
  cases h with
  | zero =>
    have hs' : Step false ks ks' := hs
    rw [kidsContent_zero, kidsContent_zero]; exact hs'.flat_eq
  | succ h' =>
    have hs' : Step true ks ks' := hs
    rw [kidsContent_succ, kidsContent_succ, hs'.flat_eq]

theorem kidsContent_append (h : Nat) (a b : List (Nat × Node h)) :
    kidsContent h (a ++ b) = kidsContent h a ++ kidsContent h b := by
  simp [kidsContent]

theorem kidsContent_cons (h : Nat) (e : Nat × Node h) (b : List (Nat × Node h)) :
    kidsContent h (e :: b) = content h e.2 ++ kidsContent h b := by
  simp [kidsContent]

/-- **Settle keeps the keys**, through every level it touches. -/
theorem Sett.kidsContent {h : Nat} {ks ks' : List (Nat × Node h)} (hs : Sett h ks ks') :
    kidsContent h ks' = kidsContent h ks := by
  induction hs with
  | refl => rfl
  | step h ks ks' ks'' h1 _ ih => rw [ih, Step.kidsContent h1]
  | down h pre post c J J' ks'' h1 _ ih1 ih2 =>
    rw [ih2, kidsContent_append, kidsContent_append, kidsContent_cons, kidsContent_cons]
    have : content (h + 1) J' = content (h + 1) J := ih1
    rw [this]

/-! ## The plain map split at a bound -/

theorem mem_mput {c v : Nat} {e : Nat × Nat} : ∀ {m : List (Nat × Nat)},
    e ∈ mput c v m → e = (c, v) ∨ e ∈ m
  | [], h => by simp [mput] at h; exact Or.inl h
  | (c', v') :: r, h => by
    unfold mput at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
    · split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases mem_mput h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem mput_append_left {c v b : Nat} (hc : c < b) {m2 : List (Nat × Nat)}
    (h2 : ∀ e ∈ m2, b ≤ e.1) : ∀ m1 : List (Nat × Nat), mput c v (m1 ++ m2) = mput c v m1 ++ m2
  | [] => by
    cases m2 with
    | nil => rfl
    | cons a r =>
      have := h2 a List.mem_cons_self
      simp only [List.nil_append, mput, List.singleton_append]
      rw [ite_eq_left (by omega)]
  | (c1, v1) :: r1 => by
    simp only [List.cons_append, mput]
    split
    · rfl
    · split
      · rfl
      · rw [mput_append_left hc h2 r1]; rfl

theorem mput_append_right {c v b : Nat} (hc : b ≤ c) {m2 : List (Nat × Nat)} :
    ∀ m1 : List (Nat × Nat), (∀ e ∈ m1, e.1 < b) → mput c v (m1 ++ m2) = m1 ++ mput c v m2
  | [], _ => rfl
  | (c1, v1) :: r1, h1 => by
    have := h1 (c1, v1) List.mem_cons_self
    simp only at this
    simp only [List.cons_append, mput]
    rw [ite_eq_right (by omega), ite_eq_right (by omega),
      mput_append_right hc r1 (fun e he => h1 e (List.mem_cons_of_mem _ he))]

/-- The operations applied to two parts of the map split at b: each part gets
the operations on its side. -/
theorem applyOps_split (b : Nat) : ∀ (ops : List Op) (m1 m2 : List (Nat × Nat)),
    (∀ e ∈ m1, e.1 < b) → (∀ e ∈ m2, b ≤ e.1) →
    applyOps ops (m1 ++ m2) =
      applyOps (ops.filter (fun o => decide (o.cv < b))) m1 ++
        applyOps (ops.filter (fun o => decide (b ≤ o.cv))) m2
  | [], _, _, _, _ => rfl
  | o :: ops, m1, m2, h1, h2 => by
    by_cases ho : o.cv < b
    · have hf1 : (o :: ops).filter (fun o => decide (o.cv < b)) =
          o :: ops.filter (fun o => decide (o.cv < b)) := by simp [ho]
      have hf2 : (o :: ops).filter (fun o => decide (b ≤ o.cv)) =
          ops.filter (fun o => decide (b ≤ o.cv)) := by
        rw [List.filter_cons]; simp only [decide_eq_true_eq]; rw [ite_eq_right (by omega)]
      rw [hf1, hf2]
      simp only [applyOps, List.foldl_cons]
      have e1 : applyOp (m1 ++ m2) o = applyOp m1 o ++ m2 := by
        cases o with
        | put c v => exact mput_append_left ho h2 m1
        | del c => simp [applyOp, List.filter_append]; intro a b' hab hb'; have := h2 _ hab; simp [Op.cv] at ho; omega
      rw [e1]
      refine applyOps_split b ops _ m2 ?_ h2
      intro e he
      cases o with
      | put c v =>
        rcases mem_mput he with rfl | he
        · exact ho
        · exact h1 e he
      | del c => exact h1 e (List.mem_of_mem_filter he)
    · have hf1 : (o :: ops).filter (fun o => decide (o.cv < b)) =
          ops.filter (fun o => decide (o.cv < b)) := by simp [ho]
      have hf2 : (o :: ops).filter (fun o => decide (b ≤ o.cv)) =
          o :: ops.filter (fun o => decide (b ≤ o.cv)) := by
        rw [List.filter_cons]; simp only [decide_eq_true_eq]; rw [ite_eq_left (by omega)]
      rw [hf1, hf2]
      simp only [applyOps, List.foldl_cons]
      have e1 : applyOp (m1 ++ m2) o = m1 ++ applyOp m2 o := by
        cases o with
        | put c v => exact mput_append_right (by simp [Op.cv] at ho; omega) m1 h1
        | del c =>
          simp only [applyOp, List.filter_append]
          congr 1
          rw [List.filter_eq_self]
          intro a ha
          have := h1 a ha
          simp [Op.cv] at ho
          simp; omega
      rw [e1]
      refine applyOps_split b ops m1 _ h1 ?_
      intro e he
      cases o with
      | put c v =>
        rcases mem_mput he with rfl | he
        · simp [Op.cv] at ho; simpa using ho
        · exact h2 e he
      | del c => exact h2 e (List.mem_of_mem_filter he)

/-! ## The old node's keys are in its range -/

theorem holdsKids_bounds {β : Type} {H : Nat → Option Nat → β → Prop} {C : β → List (Nat × Nat)}
    (hH : ∀ lo hi x, H lo hi x → ∀ e ∈ C x, lo ≤ e.1 ∧ Below e.1 hi) :
    ∀ (ks : List (Nat × β)) (lo : Nat) (hi : Option Nat), HoldsKids H lo hi ks →
      ∀ e ∈ ks.flatMap (fun k => C k.2), lo ≤ e.1 ∧ Below e.1 hi
  | [], _, _, h => absurd h (by simp [HoldsKids])
  | [(_, x)], lo, hi, h => by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact hH lo hi x h
  | (_, x) :: (c', y) :: r, lo, hi, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro e he
    rw [List.flatMap_cons, List.mem_append] at he
    rcases he with he | he
    · have := hH lo (some c') x h3 e he
      exact ⟨this.1, below_trans (by simpa [Below] using this.2) h2⟩
    · have := holdsKids_bounds hH ((c', y) :: r) c' hi h4 e he
      exact ⟨le_trans h1 this.1, this.2⟩

theorem holds_bounds : ∀ (h : Nat) (lo : Nat) (hi : Option Nat) (x : Node h), Holds h lo hi x →
    ∀ e ∈ content h x, lo ≤ e.1 ∧ Below e.1 hi
  | 0, lo, hi, x, hx => fun e he => hx.2 e he
  | h + 1, lo, hi, x, hx => by
    simp only [content]
    exact holdsKids_bounds (C := content h) (fun lo hi x hx => holds_bounds h lo hi x hx)
      (kids x) lo hi hx

/-! ## Plan keeps the keys -/

theorem applyOps_nil (m : List (Nat × Nat)) : applyOps [] m = m := rfl

/-- The children routed and planned hold the old children's keys with the
operations applied. -/
theorem routed_content {h : Nat}
    (IH : ∀ (lo : Nat) (hi : Option Nat) (x : Node h) (o : List Op) (x' : Node h), Plan h x o x' →
      Holds h lo hi x → (∀ op ∈ o, lo ≤ op.cv ∧ Below op.cv hi) →
      content h x' = applyOps o (content h x)) :
    ∀ (ks : List (Nat × Node h)) (lo : Nat) (hi : Option Nat) (ops : List Op)
      (ks' : List (Nat × Node h)), HoldsKids (Holds h) lo hi ks →
      (∀ op ∈ ops, lo ≤ op.cv ∧ Below op.cv hi) → Routed (Plan h) ks (route ks ops) ks' →
      kidsContent h ks' = applyOps ops (kidsContent h ks)
  | [], _, _, _, _, hk, _, _ => absurd hk (by simp [HoldsKids])
  | [(c, x)], lo, hi, ops, ks', hk, hops, hr => by
    simp only [route] at hr
    cases hr with
    | keep _ _ _ _ _ hr' =>
      cases hr'
      rfl
    | plan _ _ _ x' _ _ _ hp hr' =>
      cases hr'
      simp only [kidsContent, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact IH lo hi x ops x' hp hk hops
  | (c, x) :: (c', y) :: r, lo, hi, ops, ks', hk, hops, hr => by
    obtain ⟨h1, h2, h3, h4⟩ := hk
    simp only [route] at hr
    have hbx := holds_bounds h lo (some c') x h3
    have hbr := holdsKids_bounds (C := content h) (fun lo hi x hx => holds_bounds h lo hi x hx)
      ((c', y) :: r) c' hi h4
    have hsplit := applyOps_split c' ops (content h x) (kidsContent h ((c', y) :: r))
      (fun e he => by simpa [Below] using (hbx e he).2) (fun e he => (hbr e he).1)
    have hops1 : ∀ op ∈ ops.filter (fun o => decide (o.cv < c')),
        lo ≤ op.cv ∧ Below op.cv (some c') := by
      intro op hop
      rw [List.mem_filter] at hop
      exact ⟨(hops op hop.1).1, by simpa [Below] using hop.2⟩
    have hops2 : ∀ op ∈ ops.filter (fun o => decide (c' ≤ o.cv)),
        c' ≤ op.cv ∧ Below op.cv hi := by
      intro op hop
      rw [List.mem_filter] at hop
      exact ⟨by simpa using hop.2, (hops op hop.1).2⟩
    rw [kidsContent_cons, hsplit]
    generalize ho1 : ops.filter (fun o => decide (o.cv < c')) = o1 at hr hops1
    cases hr with
    | keep _ _ _ _ ks'' hr' =>
      rw [kidsContent_cons, routed_content IH ((c', y) :: r) c' hi _ ks'' h4 hops2 hr']
      rfl
    | plan _ _ _ x' _ _ ks'' hp hr' =>
      rw [kidsContent_cons, routed_content IH ((c', y) :: r) c' hi _ ks'' h4 hops2 hr',
        IH lo (some c') x _ x' hp h3 hops1]

/-- **Plan keeps the keys**: the planned node holds the old node's keys with
the operations applied. -/
theorem Plan.keys : ∀ (h : Nat) (lo : Nat) (hi : Option Nat) (es : Node h) (ops : List Op)
    (es' : Node h), Plan h es ops es' → Holds h lo hi es →
    (∀ op ∈ ops, lo ≤ op.cv ∧ Below op.cv hi) → content h es' = applyOps ops (content h es)
  | 0, _, _, es, ops, es', hp, _, _ => by
    simp only [Plan] at hp
    subst hp
    rfl
  | h + 1, lo, hi, es, ops, es', hp, hh, hops => by
    obtain ⟨ks', ks'', hr, hs, _, he⟩ := hp
    have e1 : content (h + 1) es' = kidsContent h ks'' := by
      show kidsContent h (kids es') = _
      rw [he]
      exact renameHead_flatMap 0 (fun x => content h x) ks''
    rw [e1, hs.kidsContent]
    exact routed_content (fun lo hi x o x' hp hx ho => Plan.keys h lo hi x o x' hp hx ho)
      (kids es) lo hi ops ks' hh hops hr

end PeProof.Abs
