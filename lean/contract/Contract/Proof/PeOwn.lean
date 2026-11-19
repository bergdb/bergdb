/-
bergdb 030-21: the plan's side of the writes and of TREE. Each old node the
program's virtual tree uses is used at most once: the old nodes a planned
node uses above its leaves' payloads (`Ui`: its base, every node reached from
an untouched child), and for each payload of a planned leaf the nodes reached
from the old entry of its compare value (`oldPart`), are together, as a
multiset, among the nodes reached from the old node planned (`R`).

* `plan_own`: plan meets `EOk`; the bound (`Ui` and the payloads' old parts
  are a sub-multiset of `R s x`); each payload is an entry of the planned
  node; a payload of a compare value that no operation touched is the old
  entry. Premises: `Cfg.Ok`, the run, `Shaped` and `Good` of x (no Nodup of
  `R s x` is needed: the bound is a sub-multiset).
* `settle_own`: the root settled alone keeps `EOk`, any bound of what it
  uses, and its payloads (some of the root's, each an entry of the root as
  emit writes it); `settle_root_own` with `Root` (030-21's `settle_root`)
  at the same height.
* `plan_new_own`: a new segment tree (no old root): `EOk`, no old node used,
  every payload touched.

The accounting (`cost`): a visited node is its planned node's base; an
untouched child keeps its walk; a join drops the opened node's own id and
keeps its children (an opened leaf's entries become payloads whose old entry
is themselves); a leaf's payloads of distinct compare values take distinct
old entries; a payload of a planned child is looked up in the child's part of
the old leaf level (`planKids_own`: the program routes by the old node's
compare values, and the old tree's leaf level lies in its ranges,
`view_content`).
-/
import Contract.Proof.PeEmitSpec

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Lists -/

theorem subperm_flatMap {α β : Type} {l1 l2 : List α} (f : α → List β) (h : l1.Subperm l2) :
    (l1.flatMap f).Subperm (l2.flatMap f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.flatMap f, hp.flatMap_right f, hs.flatMap f⟩

theorem flatMap_append_perm {α β : Type} (f g : α → List β) :
    ∀ (L : List α), (L.flatMap (fun x => f x ++ g x)).Perm (L.flatMap f ++ L.flatMap g)
  | [] => List.Perm.refl _
  | x :: L => by
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact ((flatMap_append_perm f g L).append_left _).trans (List.perm_append_comm_assoc _ _ _)

theorem lookup_none_of {α : Type} {c : Nat} :
    ∀ {L : List (Nat × α)}, (∀ e ∈ L, e.1 ≠ c) → L.lookup c = none
  | [], _ => rfl
  | (a, w) :: r, h => by
    rw [lookup_cons', ite_eq_right (by have := h (a, w) List.mem_cons_self; simp at this; omega)]
    exact lookup_none_of (fun e he => h e (List.mem_cons_of_mem _ he))

theorem lookup_append_left' {α : Type} {c : Nat} {A B : List (Nat × α)} (hB : ∀ e ∈ B, e.1 ≠ c) :
    (A ++ B).lookup c = A.lookup c := by
  rw [List.lookup_append, lookup_none_of hB]
  cases A.lookup c <;> rfl

theorem lookup_append_right' {α : Type} {c : Nat} {A B : List (Nat × α)} (hA : ∀ e ∈ A, e.1 ≠ c) :
    (A ++ B).lookup c = B.lookup c := by
  rw [List.lookup_append, lookup_none_of hA]
  rfl

/-- In a list in order, an entry is what its compare value looks up. -/
theorem lookup_of_mem {α : Type} {p : Nat × α} :
    ∀ {L : List (Nat × α)}, L.Pairwise CvLtA → p ∈ L → L.lookup p.1 = some p.2
  | [], _, h => by simp at h
  | (a, w) :: r, hs, h => by
    rw [List.pairwise_cons] at hs
    rw [lookup_cons']
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := hs.1 p h
      simp only [CvLtA] at this
      rw [ite_eq_right (by omega)]
      exact lookup_of_mem hs.2 h

/-! ## What a virtual node uses -/

/-- The old nodes a virtual node uses: `Ui`, and the old part of each of its
payloads (in E, the old leaf level's entries). -/
def cost (s : Tree) (E : List (Nat × NodeId)) (w : VN) : List NodeId :=
  Ui s w ++ (pays w).flatMap (oldPart s E)

/-- `cost` of a list of entries. -/
def costL (s : Tree) (E : List (Nat × NodeId)) (es : List (Nat × VN)) : List NodeId :=
  es.flatMap (fun e => cost s E e.2)

/-- Every untouched node of a virtual node, but a planned leaf's payloads,
holds entries of E (the old leaf level). -/
inductive OldIn (s : Tree) (E : List (Nat × NodeId)) : Nat → VN → Prop where
  | old {h : Nat} {y : NodeId} : (∀ p ∈ content h (view h s y), p ∈ E) → OldIn s E h (.old y)
  | leaf {b : Option NodeId} {g h' : Nat} {j : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {d : Dec} : OldIn s E 0 (.node b g h' j es F d)
  | inner {h : Nat} {b : Option NodeId} {g h' : Nat} {j : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {d : Dec} :
      (∀ e ∈ es, OldIn s E h e.2) → OldIn s E (h + 1) (.node b g h' j es F d)

/-- Every payload of a virtual node is of a compare value touched (T), or an
entry of E. -/
def PaysIn (T : List Nat) (E : List (Nat × NodeId)) (w : VN) : Prop :=
  ∀ p ∈ pays w, p.1 ∈ T ∨ p ∈ E

/-- The entries of a list, for the induction: each one's untouched nodes in
E, its payloads touched or in E, and EOk. -/
def OwnL (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (T : List Nat) (E : List (Nat × NodeId))
    (es : List (Nat × VN)) : Prop :=
  ∀ e ∈ es, OldIn s E h e.2 ∧ PaysIn T E e.2 ∧ EOk cf i s g h e.2

theorem OldIn.mono {E E' : List (Nat × NodeId)} (hE : ∀ p ∈ E, p ∈ E') {h : Nat} {w : VN}
    (hw : OldIn s E h w) : OldIn s E' h w := by
  induction hw with
  | old hy => exact OldIn.old (fun p hp => hE p (hy p hp))
  | leaf => exact OldIn.leaf
  | inner _ ih => exact OldIn.inner (fun e he => ih e he)

theorem PaysIn.mono {T T' : List Nat} {E E' : List (Nat × NodeId)} (hT : ∀ c ∈ T, c ∈ T')
    (hE : ∀ p ∈ E, p ∈ E') {w : VN} (hw : PaysIn T E w) : PaysIn T' E' w := by
  intro p hp
  rcases hw p hp with h | h
  · exact Or.inl (hT _ h)
  · exact Or.inr (hE _ h)

theorem cost_congr {E E' : List (Nat × NodeId)} {w : VN}
    (h : ∀ p ∈ pays w, E.lookup p.1 = E'.lookup p.1) : cost s E w = cost s E' w := by
  unfold cost
  congr 1
  apply List.flatMap_congr
  intro p hp
  unfold oldPart
  rw [h p hp]

theorem costL_eq (E : List (Nat × NodeId)) (es : List (Nat × VN)) :
    costL s E es = es.flatMap (fun e => cost s E e.2) := rfl

theorem costL_append (E : List (Nat × NodeId)) (A B : List (Nat × VN)) :
    costL s E (A ++ B) = costL s E A ++ costL s E B := by
  simp [costL]

theorem costL_renameHead (E : List (Nat × NodeId)) (c : Nat) (es : List (Nat × VN)) :
    costL s E (renameHead c es) = costL s E es := renameHead_flatMap_snd c _ es

theorem cost_old (E : List (Nat × NodeId)) (y : NodeId) : cost s E (.old y) = R s y := by
  simp [cost, Ui, pays]

/-- An inner node uses its base and what its children use. -/
theorem cost_inner (E : List (Nat × NodeId)) (b : Option NodeId) (g h : Nat) (j : Bool)
    (es : List (Nat × VN)) (F : List (Nat × Option NodeId)) (d : Dec) :
    (cost s E (.node b g (h + 1) j es F d)).Perm (b.toList ++ costL s E es) := by
  unfold cost costL
  rw [Ui_node, pays_node]
  simp only [Nat.add_one_ne_zero, ite_false, List.append_assoc, List.flatMap_assoc]
  refine List.Perm.append_left _ ?_
  exact (flatMap_append_perm (fun e => Ui s e.2) (fun e => (pays e.2).flatMap (oldPart s E)) es).symm

/-- A leaf uses its base and its payloads' old parts. -/
theorem cost_leaf (E : List (Nat × NodeId)) (b : Option NodeId) (g : Nat) (j : Bool)
    (es : List (Nat × VN)) (F : List (Nat × Option NodeId)) (d : Dec) :
    cost s E (.node b g 0 j es F d) =
      b.toList ++ (es.map (fun e => (e.1, e.2.oid))).flatMap (oldPart s E) := by
  unfold cost
  rw [Ui_node, pays_node]
  simp

/-! ## The old tree: its leaf level in order, its walks -/

theorem below_of_bh {c : Nat} {hi : Option Nat} (h : belowHi c hi = true) : Below c hi := by
  cases hi with
  | none => trivial
  | some b => simpa [belowHi, Below] using h

/-- The children's leaf levels, each in its range, make a list in order. -/
theorem kids_content {C : NodeId → List (Nat × NodeId)} {lo : Nat} {hi : Option Nat} :
    ∀ (L : List (Nat × NodeId)), L.Pairwise CvLtA → (∀ e ∈ L, Below e.1 hi) →
      (∀ pre c z post, L = pre ++ (c, z) :: post →
        (C z).Pairwise CvLtA ∧ ∀ e ∈ C z, max lo c ≤ e.1 ∧ Below e.1 (nextHi post hi)) →
      (L.flatMap (fun cy => C cy.2)).Pairwise CvLtA ∧
        ∀ e ∈ L.flatMap (fun cy => C cy.2), lo ≤ e.1 ∧ Below e.1 hi ∧
          ∀ c z, L.head? = some (c, z) → c ≤ e.1
  | [], _, _, _ => by simp
  | (c, z) :: rest, hs, hb, hk => by
    rw [List.pairwise_cons] at hs
    obtain ⟨k1, k2⟩ := hk [] c z rest rfl
    obtain ⟨r1, r2⟩ := kids_content rest hs.2 (fun e he => hb e (List.mem_cons_of_mem _ he))
      (fun pre c' z' post he => hk ((c, z) :: pre) c' z' post (by rw [he]; rfl))
    have hnx : ∀ e ∈ C z, Below e.1 hi := by
      intro e he
      have := (k2 e he).2
      cases rest with
      | nil => exact this
      | cons q r =>
        exact below_trans (by simpa [nextHi, Below] using this) (hb q (by simp))
    simp only [List.flatMap_cons]
    refine ⟨List.pairwise_append.mpr ⟨k1, r1, fun a ha b hb' => ?_⟩, fun e he => ?_⟩
    · cases rest with
      | nil => simp at hb'
      | cons q r =>
        have h1 := (k2 a ha).2
        have h2 := (r2 b hb').2.2 q.1 q.2 rfl
        simp only [nextHi, Below] at h1
        show a.1 < b.1
        omega
    · rcases List.mem_append.mp he with he | he
      · refine ⟨by have := (k2 e he).1; omega, hnx e he, fun c' z' h0 => ?_⟩
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, rfl⟩ := h0
        have := (k2 e he).1; omega
      · refine ⟨(r2 e he).1, (r2 e he).2.1, fun c' z' h0 => ?_⟩
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, rfl⟩ := h0
        cases rest with
        | nil => simp at he
        | cons q r =>
          have h1 := hs.1 q List.mem_cons_self
          have h2 := (r2 e he).2.2 q.1 q.2 rfl
          simp only [CvLtA] at h1
          omega

/-- **The old leaf level is in order**: what a sound node shaped as PE's
trees holds at its leaf level is in strictly increasing order of compare
values, within its range. -/
theorem view_content : ∀ (h : Nat) {g : Nat} {y : NodeId} {lo : Nat} {hi : Option Nat},
    Good s y lo hi → Shaped cf s g h y →
    (content h (view h s y)).Pairwise CvLtA ∧ ∀ e ∈ content h (view h s y), lo ≤ e.1 ∧ Below e.1 hi
  | 0, g, y, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, _, hleaf, _, _⟩ := shaped_obj hsh
    simp only [beq_self_eq_true] at hleaf
    cases hg with
    | mk _ _ _ n' hobj' _ hhi hlo _ _ _ _ =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      show (view 0 s y).Pairwise CvLtA ∧ ∀ e ∈ view 0 s y, lo ≤ e.1 ∧ Below e.1 hi
      rw [view_zero hobj]
      exact ⟨live_sorted n.ks, fun e he => ⟨hlo hleaf e.1 e.2 he, below_of_bh (hhi e.1 e.2 he)⟩⟩
  | h + 1, g, y, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, _, hleaf, _, _⟩ := shaped_obj hsh
    have hleaf' : n.leaf = false := by simpa using hleaf
    have hkids : ∀ c z, (c, z) ∈ live n.ks → Shaped cf s g h z := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hk =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hk
    cases hg with
    | mk _ _ _ n' hobj' _ hhi _ _ _ _ hkid =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      have hc : content (h + 1) (view (h + 1) s y) =
          (live n.ks).flatMap (fun cy => content h (view h s cy.2)) := by
        show kidsContent h (kids (view (h + 1) s y)) = _
        rw [view_succ hobj]
        simp only [kidsContent, List.flatMap_map]
      rw [hc]
      obtain ⟨a1, a2⟩ := kids_content (C := fun z => content h (view h s z)) (lo := lo) (live n.ks)
        (live_sorted n.ks) (fun e he => below_of_bh (hhi e.1 e.2 he))
        (fun pre c z post he => by
          have hm : (c, z) ∈ live n.ks := by rw [he]; simp
          exact view_content h (hkid hleaf' pre c z post he) (hkids c z hm))
      exact ⟨a1, fun e he => ⟨(a2 e he).1, (a2 e he).2.1⟩⟩

/-- The walk from a sound key node: the node, then its children's walks. -/
theorem R_good {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) : R s x = x :: (live n.ks).flatMap (fun cy => R s cy.2) := by
  have hfu : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  unfold R
  rw [hfu, reachAt_key hobj]
  congr 1
  apply List.flatMap_congr
  intro ⟨c, w⟩ hw
  rcases good_kids hg hobj c w hw with ⟨m, hm, hlt, lo', hi', hg'⟩ | ⟨v, hv⟩
  · have hfw : s.fuel w = m.level + 1 := by simp [Tree.fuel, hm]
    show reachAt s n.level w = reachAt s (s.fuel w) w
    exact reach_stable n.level hg' (by omega)
  · simp only
    rw [reachAt_val hv, reachAt_val hv]

/-- The walk from an inner node shaped as PE's trees: the node, then its
children's walks (their levels are one below). -/
theorem R_shaped {g h : Nat} {y : NodeId} (hsh : Shaped cf s g (h + 1) y) {n : KNode}
    (hobj : s.obj y = some (.key n)) : R s y = y :: (live n.ks).flatMap (fun cy => R s cy.2) := by
  obtain ⟨n', hobj', hlev, _, _, _⟩ := shaped_obj hsh
  rw [hobj] at hobj'
  obtain rfl : n = n' := by injection hobj' with h1; injection h1
  have hkids : ∀ c z, (c, z) ∈ live n.ks → Shaped cf s g h z := by
    cases hsh with
    | inner hobj' _ _ _ _ _ hk =>
      rw [hobj] at hobj'
      obtain rfl : n = _ := by injection hobj' with h1; injection h1
      exact hk
  have hfu : s.fuel y = n.level + 1 := by simp [Tree.fuel, hobj]
  unfold R
  rw [hfu, reachAt_key hobj]
  congr 1
  apply List.flatMap_congr
  intro ⟨c, w⟩ hw
  obtain ⟨m, hm, hmlev, _⟩ := shaped_obj (hkids c w hw)
  have hfw : s.fuel w = n.level := by
    simp only [Tree.fuel, hm, hmlev, hlev, Cfg.lev_succ]
  simp only
  rw [hfw]

/-- A leaf's payloads of distinct compare values take distinct old entries:
their old parts are among the old entries' walks. -/
theorem leaf_oldPart {es live : List (Nat × NodeId)} (hes : es.Pairwise CvLtA) :
    (es.flatMap (oldPart s live)).Subperm (live.flatMap (fun cy => R s cy.2)) := by
  let f : Nat × NodeId → Option (Nat × NodeId) := fun p => (live.lookup p.1).map (fun y0 => (p.1, y0))
  have e1 : ∀ L : List (Nat × NodeId), L.flatMap (oldPart s live) =
      (L.filterMap f).flatMap (fun q => R s q.2) := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih =>
      rw [List.flatMap_cons, List.filterMap_cons, ih]
      unfold oldPart
      simp only [f]
      cases live.lookup p.1 <;> simp
  rw [e1]
  apply subperm_flatMap
  apply List.subperm_of_subset
  · have hpw : (es.filterMap f).Pairwise CvLtA := by
      refine List.Pairwise.filterMap f (fun a a' haa b hb b' hb' => ?_) hes
      simp only [f, Option.map_eq_some_iff] at hb hb'
      obtain ⟨_, _, rfl⟩ := hb
      obtain ⟨_, _, rfl⟩ := hb'
      exact haa
    exact hpw.imp (fun {a b} h hab => by subst hab; exact absurd h (lt_irrefl _))
  · intro q hq
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hq
    simp only [f, Option.map_eq_some_iff] at hp
    obtain ⟨y0, hy0, rfl⟩ := hp
    exact lookup_mem hy0

/-! ## A virtual node made: EOk -/

theorem mkNode_eok {b : Option NodeId} {g h : Nat} {j : Bool} {es0 : List (Nat × VN)} {v : VN}
    (hm : mkNode cf i s b g h j es0 = some v) (hb : ∀ x, b = some x → Shaped cf s g h x)
    (hk : ∀ e ∈ es0, h ≠ 0 → EOk cf i s g (h - 1) e.2) :
    EOk cf i s g h v ∧ ∃ F dec, v = .node b g h j (if h == 0 then es0 else renameHead 0 es0) F dec := by
  have hk' : ∀ e ∈ (if h == 0 then es0 else renameHead 0 es0), h ≠ 0 → EOk cf i s g (h - 1) e.2 := by
    intro e he hh
    have h0 : (h == 0) = false := by simp [hh]
    simp only [h0, Bool.false_eq_true, ite_false] at he
    obtain ⟨e', he', h2⟩ := renameHead_mem he
    rw [← h2]; exact hk e' he' hh
  unfold mkNode at hm
  cases b with
  | some x =>
    simp only at hm
    split at hm
    · rename_i n hn
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨EOk.node (by simp [hn]) hb (by simp) hk', _, _, rfl⟩
    · cases hm
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · rename_i hgh
      simp only [Option.some.injEq] at hm
      subst hm
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hgh
      exact ⟨EOk.node (by simp) (by simp) (fun _ => hgh) hk', _, _, rfl⟩

/-! ## Rebalance keeps the accounting -/

theorem content_view_succ {h : Nat} {y : NodeId} {n : KNode} (hobj : s.obj y = some (.key n)) :
    content (h + 1) (view (h + 1) s y) = (live n.ks).flatMap (fun cy => content h (view h s cy.2)) := by
  show kidsContent h (kids (view (h + 1) s y)) = _
  rw [view_succ hobj]
  simp only [kidsContent, List.flatMap_map]

theorem openEs_old {y : NodeId} {esW : List (Nat × VN)} (ho : openEs s (.old y) = some esW) :
    ∃ n, s.obj y = some (.key n) ∧ esW = (live n.ks).map (fun q => (q.1, VN.old q.2)) := by
  simp only [openEs] at ho
  cases hgk : getKey s y with
  | none => rw [hgk] at ho; cases ho
  | some n =>
    rw [hgk] at ho
    simp only [Option.some.injEq] at ho
    exact ⟨n, getKey_obj hgk, ho.symm⟩

/-- A leaf opened for a join: its entries, as payloads, use no more than it. -/
theorem open_leaf_own {g : Nat} {T : List Nat} {E : List (Nat × NodeId)} (hE : E.Pairwise CvLtA)
    {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g 0 w) (hO : OldIn s E 0 w) (hP : PaysIn T E w)
    (ho : openEs s w = some esW) :
    ((esW.map (fun e => (e.1, e.2.oid))).flatMap (oldPart s E)).Subperm (cost s E w) ∧
      ∀ p ∈ esW.map (fun e => (e.1, e.2.oid)), p.1 ∈ T ∨ p ∈ E := by
  cases w with
  | old y =>
    obtain ⟨n, hobj, rfl⟩ := openEs_old ho
    have hid : ((live n.ks).map (fun q => (q.1, VN.old q.2))).map (fun e => (e.1, e.2.oid)) = live n.ks := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (live n.ks)]
      apply List.map_congr_left
      intro q _
      rfl
    rw [hid]
    have hin : ∀ p ∈ live n.ks, p ∈ E := by
      cases hO with
      | old hy =>
        intro p hp
        apply hy p
        show p ∈ view 0 s y
        rw [view_zero hobj]; exact hp
    refine ⟨?_, fun p hp => Or.inr (hin p hp)⟩
    obtain ⟨lo, hi, hg⟩ : ∃ lo hi, Good s y lo hi := by cases hw with | old _ hg _ => exact hg
    rw [cost_old, R_good hg hobj]
    have : (live n.ks).flatMap (oldPart s E) = (live n.ks).flatMap (fun cy => R s cy.2) := by
      apply List.flatMap_congr
      intro q hq
      unfold oldPart
      rw [lookup_of_mem hE (hin q hq)]
    rw [this]
    exact (List.sublist_cons_self _ _).subperm
  | node b g' h' j es F d =>
    have hh : h' = 0 := by cases hw; rfl
    subst hh
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    refine ⟨?_, fun p hp => hP p (by rw [pays_node]; simpa using hp)⟩
    rw [cost_leaf]
    exact (List.sublist_append_right _ _).subperm

/-- An inner node opened for a join: its entries use no more than it, and
keep the accounting one height down. -/
theorem open_inner_own {g h : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g (h + 1) w) (hO : OldIn s E (h + 1) w)
    (hP : PaysIn T E w) (hE : EOk cf i s g (h + 1) w) (ho : openEs s w = some esW) :
    (costL s E esW).Subperm (cost s E w) ∧ OwnL cf i s g h T E esW := by
  cases w with
  | old y =>
    obtain ⟨n, hobj, rfl⟩ := openEs_old ho
    obtain ⟨_, hkids⟩ := old_kids hobj (by cases hw with | old hsh _ _ => exact hsh)
      (by cases hw with | old _ hg _ => exact hg)
    have hin : ∀ p ∈ content (h + 1) (view (h + 1) s y), p ∈ E := by
      cases hO with
      | old hy => exact hy
    refine ⟨?_, fun e he => ?_⟩
    · obtain ⟨lo, hi, hg⟩ : ∃ lo hi, Good s y lo hi := by cases hw with | old _ hg _ => exact hg
      rw [cost_old, R_good hg hobj]
      have : costL s E ((live n.ks).map (fun q => (q.1, VN.old q.2))) =
          (live n.ks).flatMap (fun cy => R s cy.2) := by
        simp only [costL, List.flatMap_map, cost_old]
      rw [this]
      exact (List.sublist_cons_self _ _).subperm
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      refine ⟨OldIn.old (fun p hp => hin p ?_), fun p hp => by simp [pays] at hp, ?_⟩
      · rw [content_view_succ hobj, List.mem_flatMap]
        exact ⟨q, hq, hp⟩
      · exact EOk.old (by cases hkids q.1 q.2 hq with | old hsh _ _ => exact hsh)
  | node b g' h' j es F d =>
    have hh : h' = h + 1 := by cases hw; rfl
    subst hh
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    refine ⟨((List.sublist_append_right _ _).subperm).trans (cost_inner E b g' h j es F d).symm.subperm,
      fun e he => ⟨?_, ?_, ?_⟩⟩
    · cases hO with
      | inner hk => exact hk e he
    · intro p hp
      exact hP p (by rw [pays_node]; simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap]; exact ⟨e, he, hp⟩)
    · cases hE with
      | node _ _ _ hk => exact hk e he (by omega)

theorem split_costL {E : List (Nat × NodeId)} {es : List (Nat × VN)} {il : Nat} {l r : Nat × VN}
    (hl : es[il]? = some l) (hr : es[il + 1]? = some r) (v : VN)
    (hv : (cost s E v).Subperm (cost s E l.2 ++ cost s E r.2)) :
    (costL s E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))).Subperm (costL s E es) := by
  have hsplit := split_at2 hl hr
  conv_rhs => rw [hsplit]
  simp only [costL_append]
  simp only [costL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine (List.subperm_append_left _).mpr ?_
  rw [← List.append_assoc]
  exact (hv.append (List.Subperm.refl _))

theorem split_own {g h : Nat} {T : List Nat} {E : List (Nat × NodeId)} {es : List (Nat × VN)}
    {il : Nat} (l : Nat × VN) (v : VN)
    (hown : OwnL cf i s g h T E es) (hv : OldIn s E h v ∧ PaysIn T E v ∧ EOk cf i s g h v) :
    OwnL cf i s g h T E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)) := by
  intro e he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with (he | rfl) | he
  · exact hown e (List.mem_of_mem_take he)
  · exact hv
  · exact hown e (List.mem_of_mem_drop he)

/-- One join at the leaf level keeps the accounting. -/
theorem join_own_zero {g : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    (hE : E.Pairwise CvLtA) {es : List (Nat × VN)} {il : Nat} {l r : Nat × VN}
    {esL esR : List (Nat × VN)} {v : VN} (hl : es[il]? = some l) (hr : es[il + 1]? = some r)
    (hoL : openEs s l.2 = some esL) (hoR : openEs s r.2 = some esR)
    (hm : mkNode cf i s none g 0 true (esL ++ esR) = some v) (hes : KOk cf s g 0 es)
    (hown : OwnL cf i s g 0 T E es) :
    OwnL cf i s g 0 T E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)) ∧
      (costL s E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))).Subperm (costL s E es) := by
  have hsplit := split_at2 hl hr
  have hlm : l ∈ es := by rw [hsplit]; simp
  have hrm : r ∈ es := by rw [hsplit]; simp
  obtain ⟨a1, a2⟩ := open_leaf_own hE (hes l hlm).1 (hown l hlm).1 (hown l hlm).2.1 hoL
  obtain ⟨b1, b2⟩ := open_leaf_own hE (hes r hrm).1 (hown r hrm).1 (hown r hrm).2.1 hoR
  obtain ⟨hev, F, dec, rfl⟩ := mkNode_eok hm (by simp) (by simp)
  simp only [beq_self_eq_true, ite_true] at hev ⊢
  refine ⟨split_own l _ hown ⟨OldIn.leaf, ?_, hev⟩, split_costL hl hr _ ?_⟩
  · intro p hp
    rw [pays_node] at hp
    simp only [ite_true, List.map_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact a2 p hp
    · exact b2 p hp
  · rw [cost_leaf]
    simp only [Option.toList_none, List.nil_append, List.map_append, List.flatMap_append]
    exact a1.append b1

/-- One join of two inner nodes, rebalanced one level down, keeps the
accounting. -/
theorem join_own_succ {g h : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    {es : List (Nat × VN)} {il : Nat} {l r : Nat × VN}
    {esL esR J' : List (Nat × VN)} {v : VN} (hl : es[il]? = some l) (hr : es[il + 1]? = some r)
    (hoL : openEs s l.2 = some esL) (hoR : openEs s r.2 = some esR)
    (hdown : OwnL cf i s g h T E (esL ++ renameHead r.1 esR) →
      OwnL cf i s g h T E J' ∧ (costL s E J').Subperm (costL s E (esL ++ renameHead r.1 esR)))
    (hm : mkNode cf i s none g (h + 1) true J' = some v) (hes : KOk cf s g (h + 1) es)
    (hown : OwnL cf i s g (h + 1) T E es) :
    OwnL cf i s g (h + 1) T E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)) ∧
      (costL s E (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))).Subperm (costL s E es) := by
  have hsplit := split_at2 hl hr
  have hlm : l ∈ es := by rw [hsplit]; simp
  have hrm : r ∈ es := by rw [hsplit]; simp
  obtain ⟨a1, a2⟩ := open_inner_own (hes l hlm).1 (hown l hlm).1 (hown l hlm).2.1 (hown l hlm).2.2 hoL
  obtain ⟨b1, b2⟩ := open_inner_own (hes r hrm).1 (hown r hrm).1 (hown r hrm).2.1 (hown r hrm).2.2 hoR
  have hJ : OwnL cf i s g h T E (esL ++ renameHead r.1 esR) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact a2 e he
    · obtain ⟨e', he', h2⟩ := renameHead_mem he
      rw [← h2]; exact b2 e' he'
  obtain ⟨d1, d2⟩ := hdown hJ
  obtain ⟨hev, F, dec, rfl⟩ := mkNode_eok hm (by simp) (fun e he _ => (d1 e he).2.2)
  simp only [show (h + 1 == 0) = false by simp, Bool.false_eq_true, ite_false] at hev ⊢
  refine ⟨split_own l _ hown ⟨OldIn.inner (fun e he => ?_), fun p hp => ?_, hev⟩,
    split_costL hl hr _ ?_⟩
  · obtain ⟨e', he', h2⟩ := renameHead_mem he
    rw [← h2]; exact (d1 e' he').1
  · rw [pays_node] at hp
    simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap] at hp
    obtain ⟨e, he, hp⟩ := hp
    obtain ⟨e', he', h2⟩ := renameHead_mem he
    rw [← h2] at hp
    exact (d1 e' he').2.1 p hp
  · refine (cost_inner E none g h true _ F dec).subperm.trans ?_
    simp only [Option.toList_none, List.nil_append, costL_renameHead]
    refine d2.trans ?_
    rw [costL_append, costL_renameHead]
    exact a1.append b1

theorem joinAt_own_zero {g : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    (hE : E.Pairwise CvLtA) {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g 0 down es ix = some es')
    (hes : KOk cf s g 0 es) (hown : OwnL cf i s g 0 T E es) :
    OwnL cf i s g 0 T E es' ∧ (costL s E es').Subperm (costL s E es) := by
  unfold joinAt at hj
  simp only at hj
  split at hj
  · rename_i l r hl hr
    split at hj
    · rename_i esL esR hoL hoR
      simp only [beq_self_eq_true, ite_true] at hj
      cases hm : mkNode cf i s none g 0 true (esL ++ esR) with
      | none => rw [hm] at hj; cases hj
      | some v =>
        rw [hm] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        exact join_own_zero hE hl hr hoL hoR hm hes hown
    · cases hj
  · cases hj

theorem joinAt_own_succ {g h : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hdown : ∀ J J', down J = some J' → KOk cf s g h J → OwnL cf i s g h T E J →
      OwnL cf i s g h T E J' ∧ (costL s E J').Subperm (costL s E J))
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g (h + 1) down es ix = some es')
    (hes : KOk cf s g (h + 1) es) (hown : OwnL cf i s g (h + 1) T E es) :
    OwnL cf i s g (h + 1) T E es' ∧ (costL s E es').Subperm (costL s E es) := by
  unfold joinAt at hj
  simp only at hj
  split at hj
  · rename_i l r hl hr
    split at hj
    · rename_i esL esR hoL hoR
      simp only [show (h + 1 == 0) = false by simp, Bool.false_eq_true, ite_false] at hj
      cases hd : down (esL ++ renameHead r.1 esR) with
      | none => rw [hd] at hj; cases hj
      | some J' =>
        rw [hd] at hj
        simp only at hj
        cases hm : mkNode cf i s none g (h + 1) true J' with
        | none => rw [hm] at hj; cases hj
        | some v =>
          rw [hm] at hj
          simp only [Option.some.injEq] at hj
          subst hj
          have hsplit := split_at2 hl hr
          have hlm : l ∈ es := by rw [hsplit]; simp
          have hrm : r ∈ es := by rw [hsplit]; simp
          have hJk : KOk cf s g h (esL ++ renameHead r.1 esR) := by
            obtain ⟨hL1, _, _⟩ := openEs_succ (hes l hlm).1 hoL
            obtain ⟨hR1, _, _⟩ := openEs_succ (hes r hrm).1 hoR
            intro e he
            rcases List.mem_append.mp he with he | he
            · exact hL1 e he
            · obtain ⟨e', he', h2⟩ := renameHead_mem he
              rw [← h2]; exact hR1 e' he'
          exact join_own_succ hl hr hoL hoR (hdown _ _ hd hJk) hm hes hown
    · cases hj
  · cases hj

/-- The loop of joins keeps the accounting. -/
theorem joinLoop_own {g h : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hjoin : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
        es'.head?.map (·.1) = es.head?.map (·.1))
    (hjo : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      OwnL cf i s g h T E es → OwnL cf i s g h T E es' ∧ (costL s E es').Subperm (costL s E es)) :
    ∀ (n : Nat) (es es' : List (Nat × VN)), joinLoop cf i s g h down n es = some es' →
      KOk cf s g h es → OwnL cf i s g h T E es →
      OwnL cf i s g h T E es' ∧ (costL s E es').Subperm (costL s E es)
  | 0, es, es', hl, _, ho => by
    simp only [joinLoop, Option.some.injEq] at hl
    subst hl
    exact ⟨ho, List.Subperm.refl _⟩
  | n + 1, es, es', hl, hk, ho => by
    simp only [joinLoop] at hl
    split at hl
    · simp only [Option.some.injEq] at hl; subst hl; exact ⟨ho, List.Subperm.refl _⟩
    · split at hl
      · simp only [Option.some.injEq] at hl; subst hl; exact ⟨ho, List.Subperm.refl _⟩
      · rename_i ix _
        cases hj : joinAt cf i s g h down es ix with
        | none => rw [hj] at hl; cases hl
        | some es1 =>
          rw [hj] at hl
          simp only at hl
          obtain ⟨_, a2, _⟩ := hjoin es ix es1 hj hk
          obtain ⟨b1, b2⟩ := hjo es ix es1 hj hk ho
          obtain ⟨c1, c2⟩ := joinLoop_own hjoin hjo n es1 es' hl a2 b1
          exact ⟨c1, c2.trans b2⟩

/-- **Rebalance keeps the accounting**: the children rebalanced use no more
old nodes than before, and keep their untouched nodes in E, their payloads
touched or in E, and EOk. -/
theorem rebalance_own (hcf : cf.Ok) {g : Nat} {T : List Nat} {E : List (Nat × NodeId)}
    (hE : E.Pairwise CvLtA) : ∀ (f h : Nat) (es0 es2 : List (Nat × VN)),
    rebalance cf i s f g h es0 = some es2 → (∀ e ∈ es0, VOk cf s g h e.2) →
    OwnL cf i s g h T E es0 →
    OwnL cf i s g h T E es2 ∧ (costL s E es2).Subperm (costL s E es0)
  | 0, _, _, _, hr, _, _ => by simp [rebalance] at hr
  | f + 1, h, es0, es2, hr, hk, ho => by
    unfold rebalance at hr
    simp only at hr
    have hk1 : KOk cf s g h (es0.filter (fun e => !e.2.isEmpty)) := by
      intro e he
      rw [List.mem_filter] at he
      exact ⟨hk e he.1, by simpa using he.2⟩
    have ho1 : OwnL cf i s g h T E (es0.filter (fun e => !e.2.isEmpty)) :=
      fun e he => ho e (List.mem_of_mem_filter he)
    have hc1 : (costL s E (es0.filter (fun e => !e.2.isEmpty))).Subperm (costL s E es0) :=
      ((List.filter_sublist).flatMap _).subperm
    split at hr
    · simp only [Option.some.injEq] at hr
      subst hr
      exact ⟨ho1, hc1⟩
    · have hjoin : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es →
          Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
            es'.head?.map (·.1) = es.head?.map (·.1) := by
        intro es ix es' hj hes
        cases h with
        | zero => exact joinAt_zero hcf hj hes
        | succ h' =>
          refine joinAt_succ hcf (fun J J' hd hJ => ?_) hj hes
          obtain ⟨a1, a2, a3⟩ := rebalance_spec hcf f h' J J' hd (fun e he => (hJ e he).1)
          exact ⟨a1, a2, a3 (fun e he => (hJ e he).2)⟩
      have hjo : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es → OwnL cf i s g h T E es →
          OwnL cf i s g h T E es' ∧ (costL s E es').Subperm (costL s E es) := by
        intro es ix es' hj hes hown
        cases h with
        | zero => exact joinAt_own_zero hE hj hes hown
        | succ h' =>
          exact joinAt_own_succ (fun J J' hd hJk hJo =>
            rebalance_own hcf hE f h' J J' hd (fun e he => (hJk e he).1) hJo) hj hes hown
      obtain ⟨b1, b2⟩ := joinLoop_own hjoin hjo _ _ _ hr hk1 ho1
      exact ⟨b1, b2.trans hc1⟩

/-! ## Plan keeps the accounting -/

/-- What `plan` gives at fuel f, for the induction: relative to the old leaf
level E of the node planned, its untouched nodes in E, its payloads touched or
in E, EOk, and the old nodes it uses among those reached from the node. -/
def PlanOwnOk (cf : Cfg) (i : Time) (s : Tree) (f : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Contract.Op) (acc : Acc) (v : VN) (acc' : Acc)
    (lo : Nat) (hi : Option Nat),
    plan cf i s f x g h ops acc = some (v, acc') → Shaped cf s g h x → Good s x lo hi →
    OldIn s (content h (view h s x)) h v ∧ PaysIn (touched g ops) (content h (view h s x)) v ∧
      EOk cf i s g h v ∧ (cost s (content h (view h s x)) v).Subperm (R s x)

theorem touched_sub {g : Nat} {o ops : List Contract.Op} (h : ∀ op ∈ o, op ∈ ops) :
    ∀ c ∈ touched g o, c ∈ touched g ops := by
  intro c hc
  obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc
  exact mem_touched.mpr ⟨op, h op hop, rfl⟩

/-- The children planned keep the accounting, relative to the node's old
leaf level (each child's, concatenated): an untouched child uses its walk, a
planned one what its plan uses. -/
theorem planKids_own {g h : Nat} : ∀ (F : Nat) (lv : List (Nat × NodeId)) (ops : List Contract.Op)
    (acc : Acc) (es : List (Nat × VN)) (acc' : Acc) (lo : Nat) (hi : Option Nat),
    (∀ f' < F, PlanOwnOk cf i s f') → lv ≠ [] →
    planKids cf i s F g (h + 1) lv (Contract.PE.route (segAt g) lv ops) acc = some (es, acc') →
    lv.Pairwise CvLtA → (∀ e ∈ lv, Below e.1 hi) →
    (∀ pre c y post, lv = pre ++ (c, y) :: post →
      Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h y) →
    OwnL cf i s g h (touched g ops) (lv.flatMap (fun cy => content h (view h s cy.2))) es ∧
      (costL s (lv.flatMap (fun cy => content h (view h s cy.2))) es).Subperm
        (lv.flatMap (fun cy => R s cy.2))
  | 0, _, _, _, _, _, _, _, _, _, hp, _, _, _ => by simp [planKids] at hp
  | _, [], _, _, _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | F + 1, [(c, y)], ops, acc, es, acc', lo, hi, IH, _, hp, _, _, hpos => by
    obtain ⟨hg, hsh⟩ := hpos [] c y [] rfl
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [Contract.PE.route, planKids, Nat.add_sub_cancel] at hp
    split at hp
    · cases hp2 : planKids cf i s F g (h + 1) [] [] acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, _⟩ := hp
        have := planKids_nil _ _ _ _ _ _ _ hp2
        subst this
        refine ⟨fun e he => ?_, ?_⟩
        · simp only [List.mem_singleton] at he
          subst he
          exact ⟨OldIn.old (fun p hp => hp), fun p hp => by simp [pays] at hp, EOk.old hsh⟩
        · simpa [costL, cost_old] using List.Subperm.refl (R s y)
    · cases hp1 : plan cf i s F y g h ops acc with
      | none => rw [hp1] at hp; cases hp
      | some q =>
        rw [hp1] at hp
        obtain ⟨v, acc1⟩ := q
        simp only at hp
        cases hp2 : planKids cf i s F g (h + 1) [] [] acc1 with
        | none => rw [hp2] at hp; cases hp
        | some q =>
          rw [hp2] at hp
          obtain ⟨es2, acc2⟩ := q
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, _⟩ := hp
          have := planKids_nil _ _ _ _ _ _ _ hp2
          subst this
          obtain ⟨a1, a2, a3, a4⟩ := IH F (by omega) y g h ops acc v acc1 _ _ hp1 hsh hg
          refine ⟨fun e he => ?_, ?_⟩
          · simp only [List.mem_singleton] at he
            subst he
            exact ⟨a1, a2, a3⟩
          · simpa [costL] using a4
  | F + 1, (c, y) :: (c', y') :: r, ops, acc, es, acc', lo, hi, IH, _, hp, hs, hb, hpos => by
    obtain ⟨hg, hsh⟩ := hpos [] c y ((c', y') :: r) rfl
    have IH' : ∀ f' < F, PlanOwnOk cf i s f' := fun f' h => IH f' (by omega)
    have hs' := List.pairwise_cons.mp hs
    -- the old leaf level: the first child's below c', the others' from c'
    have hEy : ∀ e ∈ content h (view h s y), e.1 < c' := by
      intro e he
      have := ((view_content h hg hsh).2 e he).2
      simpa [nextHi, Below] using this
    have hpos' : ∀ pre c y post, (c', y') :: r = pre ++ (c, y) :: post →
        Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h y :=
      fun pre c0 y0 post he => hpos ((c, y) :: pre) c0 y0 post (by rw [he]; rfl)
    have hErest : ∀ e ∈ ((c', y') :: r).flatMap (fun cy => content h (view h s cy.2)), c' ≤ e.1 := by
      have := kids_content (C := fun z => content h (view h s z)) (lo := lo) (hi := hi)
        ((c', y') :: r) hs'.2 (fun e he => hb e (List.mem_cons_of_mem _ he))
        (fun pre c0 y0 post he => by
          obtain ⟨g1, s1⟩ := hpos' pre c0 y0 post he
          exact view_content h g1 s1)
      intro e he
      exact (this.2 e he).2.2 c' y' rfl
    simp only [List.flatMap_cons] at hErest ⊢
    generalize hER : List.flatMap (fun cy => content h (view h s cy.2)) r = ER at hErest ⊢
    simp only [Contract.PE.route] at hp
    simp only [planKids, Nat.add_sub_cancel] at hp
    generalize ho1 : ops.filter (fun o => decide (segAt g o < c')) = o1 at hp
    generalize ho2 : ops.filter (fun o => decide (c' ≤ segAt g o)) = o2 at hp
    have ht1 : ∀ c0 ∈ touched g o1, c0 < c' := by
      intro c0 hc0
      obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc0
      rw [← ho1] at hop
      simpa using (List.mem_filter.mp hop).2
    have ht2 : ∀ c0 ∈ touched g o2, c' ≤ c0 := by
      intro c0 hc0
      obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc0
      rw [← ho2] at hop
      simpa using (List.mem_filter.mp hop).2
    have hs1 : ∀ op ∈ o1, op ∈ ops := fun op h => by rw [← ho1] at h; exact List.mem_of_mem_filter h
    have hs2 : ∀ op ∈ o2, op ∈ ops := fun op h => by rw [← ho2] at h; exact List.mem_of_mem_filter h
    -- the rest of the children, from the rest's leaf level to the whole one
    have hrest : ∀ es2 acc1 acc2, planKids cf i s F g (h + 1) ((c', y') :: r)
        (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc1 = some (es2, acc2) →
        OwnL cf i s g h (touched g ops) (content h (view h s y) ++
          (content h (view h s y') ++ ER)) es2 ∧
        (costL s (content h (view h s y) ++ (content h (view h s y') ++ ER)) es2).Subperm
          (R s y' ++ r.flatMap (fun cy => R s cy.2)) := by
      intro es2 acc1 acc2 hp2
      obtain ⟨b1, b2⟩ := planKids_own F ((c', y') :: r) o2 acc1 es2 acc2 lo hi IH' (by simp) hp2
        hs'.2 (fun e he => hb e (List.mem_cons_of_mem _ he)) hpos'
      simp only [List.flatMap_cons] at b1 b2
      rw [hER] at b1 b2
      refine ⟨fun e he => ?_, ?_⟩
      · obtain ⟨o1', o2', o3'⟩ := b1 e he
        exact ⟨o1'.mono (fun p hp => List.mem_append_right _ hp),
          o2'.mono (touched_sub hs2) (fun p hp => List.mem_append_right _ hp), o3'⟩
      · have : costL s (content h (view h s y) ++ (content h (view h s y') ++ ER)) es2 =
            costL s (content h (view h s y') ++ ER) es2 := by
          apply List.flatMap_congr
          intro e he
          apply cost_congr
          intro p hp
          have hp' : c' ≤ p.1 := by
            rcases (b1 e he).2.1 p hp with h1 | h1
            · exact ht2 _ h1
            · exact hErest p h1
          exact lookup_append_right' (fun q hq => by have := hEy q hq; omega)
        rw [this]
        simpa using b2
    split at hp
    · rename_i hops
      cases hp2 : planKids cf i s F g (h + 1) ((c', y') :: r)
          (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, _⟩ := hp
        obtain ⟨b1, b2⟩ := hrest es2 acc acc2 hp2
        refine ⟨fun e he => ?_, ?_⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact ⟨OldIn.old (fun p hp => List.mem_append_left _ hp), fun p hp => by simp [pays] at hp,
              EOk.old hsh⟩
          · exact b1 e he
        · simp only [costL, List.flatMap_cons, cost_old] at b2 ⊢
          exact (List.Subperm.refl _).append (by simpa [costL] using b2)
    · cases hp1 : plan cf i s F y g h o1 acc with
      | none => rw [hp1] at hp; cases hp
      | some q =>
        rw [hp1] at hp
        obtain ⟨v, acc1⟩ := q
        simp only at hp
        cases hp2 : planKids cf i s F g (h + 1) ((c', y') :: r)
            (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc1 with
        | none => rw [hp2] at hp; cases hp
        | some q =>
          rw [hp2] at hp
          obtain ⟨es2, acc2⟩ := q
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, _⟩ := hp
          obtain ⟨a1, a2, a3, a4⟩ := IH F (by omega) y g h o1 acc v acc1 _ _ hp1 hsh hg
          obtain ⟨b1, b2⟩ := hrest es2 acc1 acc2 hp2
          refine ⟨fun e he => ?_, ?_⟩
          · rcases List.mem_cons.mp he with rfl | he
            · exact ⟨a1.mono (fun p hp => List.mem_append_left _ hp),
                a2.mono (touched_sub hs1) (fun p hp => List.mem_append_left _ hp), a3⟩
            · exact b1 e he
          · have hc : cost s (content h (view h s y) ++ (content h (view h s y') ++ ER)) v =
                cost s (content h (view h s y)) v := by
              apply cost_congr
              intro p hp
              have hp' : p.1 < c' := by
                rcases a2 p hp with h1 | h1
                · exact ht1 _ h1
                · exact hEy p h1
              refine lookup_append_left' (fun q hq => ?_)
              rcases List.mem_append.mp hq with hq | hq
              · have := hErest q (List.mem_append_left _ hq); omega
              · have := hErest q (List.mem_append_right _ hq); omega
            simp only [costL, List.flatMap_cons] at b2 ⊢
            rw [hc]
            exact a4.append (by simpa [costL] using b2)

theorem plan_own_ok (hcf : cf.Ok) : ∀ f, PlanOwnOk cf i s f := by
  intro f
  refine Nat.strong_induction_on f ?_
  intro f IH x g h ops acc v acc' lo hi hp hsh hg
  have hE := (view_content h hg hsh).1
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
    have hp0 := hp
    unfold plan at hp
    cases hgk : getKey s x with
    | none => rw [hgk] at hp; cases hp
    | some n =>
      rw [hgk] at hp
      simp only at hp
      have hobj := getKey_obj hgk
      split at hp
      · -- a segment leaf
        rename_i hh
        have hh0 : h = 0 := by simpa using hh
        subst hh0
        cases ha : applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc with
        | none => rw [ha] at hp; cases hp
        | some q =>
          rw [ha] at hp
          obtain ⟨es, acc1⟩ := q
          simp only at hp
          cases hm : mkNode cf i s (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
          | none => rw [hm] at hp; cases hp
          | some w =>
            rw [hm] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, _⟩ := hp
            obtain ⟨hev, F, dec, rfl⟩ := mkNode_eok hm (fun x' hx => by cases hx; exact hsh) (by simp)
            simp only [beq_self_eq_true, ite_true] at hev ⊢
            obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc1 ha (live_sorted n.ks)
            have hid : (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es := by
              rw [List.map_map]
              conv_rhs => rw [← List.map_id es]
              apply List.map_congr_left
              intro e _
              rfl
            have hE0 : content 0 (view 0 s x) = live n.ks := view_zero hobj
            rw [hE0]
            refine ⟨OldIn.leaf, fun p hp => ?_, hev, ?_⟩
            · rw [pays_node] at hp
              simp only [ite_true, hid] at hp
              by_cases ht : p.1 ∈ touched g ops
              · exact Or.inl ht
              · right
                have h1 := lookup_of_mem hs1 hp
                rw [hs2 p.1 ht] at h1
                exact lookup_mem h1
            · rw [cost_leaf, hid, R_good hg hobj]
              exact (List.subperm_cons x).mpr (leaf_oldPart hs1)
      · -- an inner node
        rename_i hh
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by simp at hh; omega⟩
        simp only [Nat.add_sub_cancel] at hp
        cases hpk : planKids cf i s f g (h' + 1) (live n.ks)
            (Contract.PE.route (segAt g) (live n.ks) ops) acc with
        | none => rw [hpk] at hp; cases hp
        | some q =>
          rw [hpk] at hp
          obtain ⟨es, acc1⟩ := q
          simp only at hp
          cases hr : rebalance cf i s (f + 1) g h' es with
          | none => rw [hr] at hp; cases hp
          | some es2 =>
            rw [hr] at hp
            simp only at hp
            cases hm : mkNode cf i s (some x) g (h' + 1) false es2 with
            | none => rw [hm] at hp; cases hp
            | some w =>
              rw [hm] at hp
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, _⟩ := hp
              obtain ⟨hhead, hkids⟩ := old_kids hobj hsh ⟨lo, hi, hg⟩
              have hne : live n.ks ≠ [] := by
                intro h0; rw [h0] at hhead; cases hhead
              have hleaf : n.leaf = false := by
                obtain ⟨n', hobj', _, hl, _, _⟩ := shaped_obj hsh
                rw [hobj] at hobj'
                obtain rfl : n = n' := by injection hobj' with h1; injection h1
                simpa using hl
              have hpos : ∀ pre c y post, live n.ks = pre ++ (c, y) :: post →
                  Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h' y := by
                intro pre c y post he
                cases hg with
                | mk _ _ _ n' hobj' _ _ _ _ _ _ hkid =>
                  rw [hobj] at hobj'
                  obtain rfl : n = n' := by injection hobj' with h1; injection h1
                  refine ⟨hkid hleaf pre c y post he, ?_⟩
                  have := hkids c y (by rw [he]; simp)
                  cases this with
                  | old hsh' _ _ => exact hsh'
              have hbelow : ∀ e ∈ live n.ks, Below e.1 hi := by
                cases hg with
                | mk _ _ _ n' hobj' _ hhi _ _ _ _ _ =>
                  rw [hobj] at hobj'
                  obtain rfl : n = n' := by injection hobj' with h1; injection h1
                  exact fun e he => below_of_bh (hhi e.1 e.2 he)
              obtain ⟨k1, k2⟩ := planKids_own f (live n.ks) ops acc es acc1 lo hi
                (fun f' h => IH f' (by omega)) hne hpk (live_sorted n.ks) hbelow hpos
              obtain ⟨_, _, _, hvk⟩ := planKids_spec f (live n.ks) ops acc es acc1
                (fun f' _ => plan_ok hcf f') hne hpk hkids
              rw [← content_view_succ hobj] at k1 k2
              obtain ⟨r1, r2⟩ := rebalance_own hcf hE (f + 1) h' es es2 hr hvk k1
              obtain ⟨hev, F, dec, rfl⟩ := mkNode_eok hm (fun x' hx => by cases hx; exact hsh)
                (fun e he _ => (r1 e he).2.2)
              simp only [show (h' + 1 == 0) = false by simp, Bool.false_eq_true, ite_false] at hev ⊢
              refine ⟨OldIn.inner (fun e he => ?_), fun p hp => ?_, hev, ?_⟩
              · obtain ⟨e', he', h2⟩ := renameHead_mem he
                rw [← h2]; exact (r1 e' he').1
              · rw [pays_node] at hp
                simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap] at hp
                obtain ⟨e, he, hp⟩ := hp
                obtain ⟨e', he', h2⟩ := renameHead_mem he
                rw [← h2] at hp
                exact (r1 e' he').2.1 p hp
              · refine (cost_inner _ (some x) g h' false _ F dec).subperm.trans ?_
                rw [costL_renameHead, R_good hg hobj]
                exact (List.subperm_cons x).mpr (r2.trans k2)

/-- A planned virtual node's payloads are entries of it, read before any
cut. -/
theorem pays_absV : ∀ (h : Nat) {g : Nat} {w : VN}, EOk cf i s g h w →
    ∀ p ∈ pays w, p ∈ content h (absV s h w)
  | 0, g, w, hw => by
    cases hw with
    | old _ => intro p hp; simp [pays] at hp
    | @node _ b join es F dec _ _ _ _ =>
      intro p hp
      rw [pays_node] at hp
      simp only [ite_true] at hp
      show p ∈ es.map (fun e => (e.1, e.2.oid))
      exact hp
  | h + 1, g, w, hw => by
    cases hw with
    | old _ => intro p hp; simp [pays] at hp
    | @node _ b join es F dec _ _ _ hk =>
      intro p hp
      rw [pays_node] at hp
      simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap] at hp
      obtain ⟨e, he, hp⟩ := hp
      show p ∈ kidsContent h (absK s h es)
      simp only [kidsContent, absK, List.flatMap_map, List.mem_flatMap]
      exact ⟨e, he, pays_absV h (hk e he (by omega)) p hp⟩

/-- **Plan's side of the writes and of TREE**: if `plan` gives v for key node
x of segment g at height h, shaped as PE's trees and sound (`Good`), then v
meets `EOk`; the old nodes v uses (`Ui`) and the old parts of its payloads
(`oldPart`, of x's old leaf level) are, as a multiset, among the nodes reached
from x (`R s x`); each payload is an entry of v read before any cut; and a
payload of a compare value that no operation touched is x's old entry. -/
theorem plan_own (hcf : cf.Ok) {f : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op}
    {acc : Acc} {v : VN} {acc' : Acc} {lo : Nat} {hi : Option Nat}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) (hsh : Shaped cf s g h x)
    (hg : Good s x lo hi) :
    EOk cf i s g h v ∧
      (Ui s v ++ (pays v).flatMap (oldPart s (content h (view h s x)))).Subperm (R s x) ∧
      (∀ p ∈ pays v, p ∈ content h (absV s h v)) ∧
      (∀ p ∈ pays v, p.1 ∉ touched g ops → (content h (view h s x)).lookup p.1 = some p.2) := by
  obtain ⟨_, a2, a3, a4⟩ := plan_own_ok hcf f x g h ops acc v acc' lo hi hp hsh hg
  refine ⟨a3, a4, pays_absV h a3, fun p hp ht => ?_⟩
  rcases a2 p hp with h1 | h1
  · exact absurd h1 ht
  · exact lookup_of_mem (view_content h hg hsh).1 h1

/-! ## The root settled alone keeps the accounting -/

theorem content_append : ∀ (h : Nat) (A B : Node h), content h (A ++ B) = content h A ++ content h B
  | 0, _, _ => rfl
  | h + 1, A, B => by
    show (kids (A ++ B)).flatMap _ = (kids A).flatMap _ ++ (kids B).flatMap _
    exact List.flatMap_append

theorem content_flatten (h : Nat) : ∀ (Ps : List (Node h)), content h Ps.flatten = Ps.flatMap (content h)
  | [] => by cases h <;> rfl
  | P :: Ps => by
    rw [List.flatten_cons, content_append, content_flatten h Ps, List.flatMap_cons]

theorem content_piece (h : Nat) (Q : Node h) :
    content h (if (h != 0) then renameHead 0 Q else Q) = content h Q := by
  cases h with
  | zero => rfl
  | succ h =>
    simp only [Nat.add_one_ne_zero, bne_iff_ne, ne_eq, not_false_eq_true, ite_true]
    exact renameHead_flatMap 0 (fun x => content h x) Q

theorem kidsContent_cutEnts (h c : Nat) (Ps : List (Node h)) :
    kidsContent h (cutEnts (h != 0) c Ps) = Ps.flatMap (content h) := by
  cases Ps with
  | nil => rfl
  | cons P Qs =>
    simp only [cutEnts, kidsContent, List.flatMap_cons, List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro Q _
    exact content_piece h Q

/-- A child as emit writes it, cut into its parts, holds what it holds. -/
theorem kidsContent_finEnts {h : Nat} (c : Nat) (w : VN) (fv : Node h) :
    kidsContent h (finEnts c w fv) = content h fv := by
  by_cases hcut : ∃ base g' h' join es F k, w = .node base g' h' join es F (.parts k) ∧ 2 ≤ k
  · obtain ⟨base, g', h', join, es, F, k, rfl, hk⟩ := hcut
    rw [finEnts_cut c hk fv, kidsContent_cutEnts, ← content_flatten,
      cutList_flatten fv _ (partSizes_sum (by omega) join)]
  · rw [finEnts_one c w fv (fun base g' h' join es F k hw' => by
      by_contra hk; exact hcut ⟨base, g', h', join, es, F, k, hw', by omega⟩)]
    simp [kidsContent]

/-- A planned virtual node's payloads are entries of it as emit writes it. -/
theorem pays_fin : ∀ (h : Nat) {g : Nat} {w : VN}, EOk cf i s g h w →
    ∀ p ∈ pays w, p ∈ content h (fin s h w)
  | 0, g, w, hw => pays_absV 0 hw
  | h + 1, g, w, hw => by
    cases hw with
    | old _ => intro p hp; simp [pays] at hp
    | @node _ b join es F dec _ _ _ hk =>
      intro p hp
      rw [pays_node] at hp
      simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap] at hp
      obtain ⟨e, he, hp⟩ := hp
      show p ∈ kidsContent h (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))))
      rw [show kidsContent h (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2)))) =
          kidsContent h (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))) from
          renameHead_flatMap 0 (fun x => content h x) _]
      simp only [kidsContent, List.flatMap_assoc]
      rw [List.mem_flatMap]
      refine ⟨e, he, ?_⟩
      have := kidsContent_finEnts (h := h) e.1 e.2 (fin s h e.2)
      unfold kidsContent at this
      rw [this]
      exact pays_fin h (hk e he (by omega)) p hp

/-- **Settle keeps the accounting**: if `settleRoot` gives v' for a root v
that meets `EOk` at height h, and what v uses (`Ui`, and P of each payload)
is among B, then v' meets `EOk` at some height h', what it uses is among B,
its payloads are some of v's, and each is an entry of v' as emit writes it. -/
theorem settle_own : ∀ (f g : Nat) (space : Bool) (h : Nat) (v v' : VN)
    (P : Nat × NodeId → List NodeId) (B : List NodeId),
    EOk cf i s g h v → (Ui s v ++ (pays v).flatMap P).Subperm B →
    settleRoot cf i s f g v space = some (some v') →
    ∃ h', EOk cf i s g h' v' ∧ (Ui s v' ++ (pays v').flatMap P).Subperm B ∧
      (∀ p ∈ pays v', p ∈ pays v) ∧ (∀ p ∈ pays v', p ∈ content h' (fin s h' v'))
  | 0, _, _, _, _, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, g, space, h, v, v', P, B, hv, hB, hs => by
    have hdone : ∃ h', EOk cf i s g h' v ∧ (Ui s v ++ (pays v).flatMap P).Subperm B ∧
        (∀ p ∈ pays v, p ∈ pays v) ∧ (∀ p ∈ pays v, p ∈ content h' (fin s h' v)) :=
      ⟨h, hv, hB, fun _ h => h, pays_fin h hv⟩
    unfold settleRoot at hs
    cases v with
    | old y =>
      have hsh : Shaped cf s g h y := by cases hv with | old hsh => exact hsh
      simp only at hs
      cases hgk : getKey s y with
      | none => rw [hgk] at hs; cases hs
      | some n =>
        rw [hgk] at hs
        simp only at hs
        have hobj := getKey_obj hgk
        split at hs
        · rename_i c z hl
          split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · rename_i hleaf
            cases hsh with
            | leaf hobj' hleaf' _ _ _ =>
              rw [hobj] at hobj'
              obtain rfl : n = _ := by injection hobj' with h1; injection h1
              exact absurd hleaf' hleaf
            | @inner _ h'' _ n' hobj' a1 a2 a3 a4 a5 hkids =>
              rw [hobj] at hobj'
              obtain rfl : n = n' := by injection hobj' with h1; injection h1
              have hz : Shaped cf s g h'' z := hkids c z (by rw [hl]; simp)
              have hR : R s y = y :: R s z := by
                rw [R_shaped (Shaped.inner hobj a1 a2 a3 a4 a5 hkids) hobj, hl]
                simp
              refine settle_own f g space h'' (.old z) v' P B (EOk.old hz) ?_ hs
              simp only [Ui, pays, List.flatMap_nil, List.append_nil] at hB ⊢
              rw [hR] at hB
              exact (List.sublist_cons_self _ _).subperm.trans hB
        · simp only [Option.some.injEq] at hs; subst hs; exact hdone
    | node base g' hv' join es F dec =>
      have hgh : g' = g ∧ hv' = h := by cases hv; exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := hgh
      simp only at hs
      split at hs
      · split at hs
        · cases hs
        · split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · cases hm : mkNode cf i s none g' 0 false [] with
            | none => rw [hm] at hs; cases hs
            | some w =>
              rw [hm] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              subst hs
              obtain ⟨hew, F2, dec2, rfl⟩ := mkNode_eok hm (by simp) (by simp)
              refine ⟨0, hew, ?_, fun p hp => by simp [pays] at hp, pays_fin 0 hew⟩
              simp [Ui, pays]
      · split at hs
        · rename_i hF hone
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hone
          obtain ⟨hh, _⟩ := hone
          obtain ⟨h'', rfl⟩ : ∃ h'', hv' = h'' + 1 := ⟨hv' - 1, by omega⟩
          split at hs
          · rename_i c ch
            have hch : EOk cf i s g' h'' ch := by
              cases hv with
              | node _ _ _ hk => exact hk (c, ch) (by simp) (by omega)
            have hB' : (Ui s ch ++ (pays ch).flatMap P).Subperm B := by
              refine List.Subperm.trans ?_ hB
              rw [Ui_node, pays_node]
              simp only [Nat.add_one_ne_zero, ite_false, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]
              exact (List.sublist_append_right _ _).subperm
            obtain ⟨h', a1, a2, a3, a4⟩ := settle_own f g' space h'' ch v' P B hch hB' hs
            refine ⟨h', a1, a2, fun p hp => ?_, a4⟩
            rw [pays_node]
            simp only [Nat.add_one_ne_zero, ite_false, List.flatMap_cons, List.flatMap_nil,
              List.append_nil]
            exact a3 p hp
          · cases hs
        · split at hs
          · rename_i k
            split at hs
            · cases hm : mkNode cf i s none g' (hv' + 1) false [(0, .node base g' hv' join es F (.parts k))] with
              | none => rw [hm] at hs; cases hs
              | some r =>
                rw [hm] at hs
                simp only at hs
                obtain ⟨her, F2, dec2, rfl⟩ := mkNode_eok hm (by simp)
                  (by intro e he _; simp at he; subst he; exact hv)
                have hUi : Ui s (VN.node none g' (hv' + 1) false
                    (if hv' + 1 == 0 then [(0, VN.node base g' hv' join es F (Dec.parts k))]
                      else renameHead 0 [(0, VN.node base g' hv' join es F (Dec.parts k))]) F2 dec2) =
                    Ui s (VN.node base g' hv' join es F (Dec.parts k)) := by
                  rw [Ui_node]; simp [renameHead]
                have hpays : pays (VN.node none g' (hv' + 1) false
                    (if hv' + 1 == 0 then [(0, VN.node base g' hv' join es F (Dec.parts k))]
                      else renameHead 0 [(0, VN.node base g' hv' join es F (Dec.parts k))]) F2 dec2) =
                    pays (VN.node base g' hv' join es F (Dec.parts k)) := by
                  rw [pays_node]; simp [renameHead]
                obtain ⟨h', a1, a2, a3, a4⟩ := settle_own f g' space (hv' + 1) _ v' P B her
                  (by rw [hUi, hpays]; exact hB) hs
                exact ⟨h', a1, a2, fun p hp => by rw [← hpays]; exact a3 p hp, a4⟩
            · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone

/-- A new segment tree (`planTree` with no old root): EOk, it uses no old
node, every payload is of a compare value touched, and each is an entry of
it. -/
theorem plan_new_own {f g : Nat} {ops : List Contract.Op} {acc : Acc}
    {es : List (Nat × NodeId)} {acc' : Acc} {v : VN}
    (ha : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc'))
    (hm : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    EOk cf i s g 0 v ∧ Ui s v = [] ∧ (pays v).flatMap (oldPart s []) = [] ∧
      (∀ p ∈ pays v, p.1 ∈ touched g ops) ∧ (∀ p ∈ pays v, p ∈ content 0 (absV s 0 v)) := by
  obtain ⟨hev, F, dec, rfl⟩ := mkNode_eok hm (by simp) (by simp)
  obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc' ha List.Pairwise.nil
  have hid : (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    apply List.map_congr_left
    intro e _
    rfl
  refine ⟨hev, by simp [Ui], ?_, fun p hp => ?_, pays_absV 0 hev⟩
  · apply List.flatMap_eq_nil_iff.mpr
    intro p _
    rfl
  · rw [pays_node] at hp
    simp only [beq_self_eq_true, ite_true, hid] at hp
    by_contra ht
    have h1 := lookup_of_mem hs1 hp
    rw [hs2 p.1 ht] at h1
    cases h1

/-- The height of a root is determined by what it is. -/
theorem RootOk.ht_eq {g h1 h2 : Nat} {w : VN} (h1w : RootOk cf s g h1 w)
    (h2w : EOk cf i s g h2 w) : h1 = h2 := by
  cases w with
  | old y =>
    have hs1 : Shaped cf s g h1 y := by
      rcases h1w with ⟨y', hy, hsh⟩ | hv
      · cases hy; exact hsh
      · cases hv with | old hsh _ _ => exact hsh
    have hs2 : Shaped cf s g h2 y := by cases h2w with | old hsh => exact hsh
    obtain ⟨n1, o1, l1, _⟩ := shaped_obj hs1
    obtain ⟨n2, o2, l2, _⟩ := shaped_obj hs2
    rw [o1] at o2
    obtain rfl : n1 = n2 := by injection o2 with h; injection h
    rw [l1] at l2
    simp only [Cfg.lev] at l2
    omega
  | node b g' h' j es F d =>
    have e1 : h' = h1 := by
      rcases h1w with ⟨y', hy, _⟩ | hv
      · cases hy
      · exact (VOk.ht hv).1
    have e2 : h' = h2 := by cases h2w; rfl
    omega

/-- Settle, both sides: the root settles (`Root`) into v' as emit writes it,
at a height h' where v' meets `RootOk` and `EOk`, uses no more than v, and
whose payloads are some of v's, each an entry of v'. -/
theorem settle_root_own (hcf : cf.Ok) {f g : Nat} {space : Bool} {h : Nat} {v v' : VN}
    {P : Nat × NodeId → List NodeId} {B : List NodeId}
    (hr : RootOk cf s g h v) (hv : EOk cf i s g h v) (hB : (Ui s v ++ (pays v).flatMap P).Subperm B)
    (hs : settleRoot cf i s f g v space = some (some v')) :
    ∃ h', Root h (absV s h v) h' (fin s h' v') ∧ RootOk cf s g h' v' ∧ EOk cf i s g h' v' ∧
      (Ui s v' ++ (pays v').flatMap P).Subperm B ∧ (∀ p ∈ pays v', p ∈ pays v) ∧
      (∀ p ∈ pays v', p ∈ content h' (fin s h' v')) := by
  obtain ⟨h1, a1, a2⟩ := settle_root hcf f g space h v v' hr hs
  obtain ⟨h2, b1, b2, b3, b4⟩ := settle_own f g space h v v' P B hv hB hs
  obtain rfl := a2.ht_eq b1
  exact ⟨h1, a1, a2, b1, b2, b3, b4⟩

end Contract.PE
