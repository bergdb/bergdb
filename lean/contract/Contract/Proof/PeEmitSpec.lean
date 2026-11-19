/-
bergdb 030-21: emit realizes the planned tree. PE's emit (Contract/PeWriter.lean:
`emit`, `emitKids`, `newParts`) writes each planned virtual node once, after its
children, by its decision: `same` (the base kept), `append` (the base gets
`emitKs`), `parts k` (its final list cut into k new nodes with fresh ids).

`emit_spec` and `emit_spec_w`, by induction on the height (`emit_main`; a
node's children by `kids_spec`, its decision by `step_same`, `step_append`,
`step_parts`):

* the writes W: each node once; a fresh id of the run or an old node the
  virtual node uses (`Ui`: an appended base); every klong written has a time at
  most i; a written old node keeps its klongs and gets klongs after a time
  klong of i (the contract's frame), and is a key node of the segment shaped
  as PE's trees (`emit_spec_w`);
* in any tree T that has the writes, leaves every other used old node as it
  was, keeps every node of s, and whose leaves' payloads are nodes of T: each
  entry emit gives holds its planned piece (`Holds`: its level, `nodeOk`, its
  live klongs; the pieces are `finEnts` of `fin`), the nodes reached from the
  entries are, as a multiset, among the used old nodes, the payloads' bounds
  and the fresh ids of the run (for TREE), and every node written meets the
  rules of one node and has a klong (`emit_spec_w`).

The premises are facts of the tree before s (its key nodes meet `nodeOk`, have
a klong and times before i; the ids from `acc.next` are no nodes of s), of the
run (`VOk`, `EOk`: the program's virtual node; its used old nodes distinct;
its planned tree in order, `InOrd`, which 026-24's `WF` gives: `wfe_inord`),
and of T. Three changes against the statement first asked for (030-21), each
needed, as the program runs:

* the order premise `InOrd h (fin s h v)`: emit writes a node from its list as
  it is, and a node's live klongs are in compare order, so an unordered plan
  would not be held (`newKs_live`, `emitKs_live` need the order);
* the first entry's compare value: emit gives a leaf's first part its own first
  compare value (`newParts`, `headCv`), which `emitKids` then replaces by the
  parent's (`renameHead`); so the compare values are those of the pieces after
  `renameHead 0` (a new leaf of entries 40 and 48, one part: emit gives
  [(40, z)], `finEnts` [(0, _)]);
* the payloads' walks with any fuel from a leaf's level: a leaf's walk gives
  its payloads the leaf's fuel (`lev g 0`), not their own (`R`), and a walk in
  T with more fuel than a payload's own may reach more if T's levels do not go
  down below it. The conclusion is given for every fuel from the entries'
  level on, so that a next segment's tree (`lev_next`), an old payload
  (`payload_old`) and a value (`payload_val`) give the premise.
-/
import Contract.Proof.PeInst
import Contract.Proof.PeEmit

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

/-- omega through the alias `NodeId` of Nat. -/
macro "nomega" : tactic => `(tactic| ((try unfold NodeId at *) <;> omega))

/-! ## Lists -/

theorem flatMap_subperm {α β : Type} {f g : α → List β} :
    ∀ (L : List α), (∀ x ∈ L, (f x).Subperm (g x)) → (L.flatMap f).Subperm (L.flatMap g)
  | [], _ => List.nil_subperm
  | x :: L, h => by
    simp only [List.flatMap_cons]
    exact (h x List.mem_cons_self).append
      (flatMap_subperm L (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem renameHead_flatMap_snd {α β : Type} (c : Nat) (f : α → List β) (l : List (Nat × α)) :
    (renameHead c l).flatMap (fun e => f e.2) = l.flatMap (fun e => f e.2) := by
  cases l <;> rfl

theorem renameHead_map_snd {α : Type} (c : Nat) (l : List (Nat × α)) :
    (renameHead c l).map (·.2) = l.map (·.2) := by
  cases l <;> rfl

theorem mem_renameHead_snd {α : Type} {c : Nat} {l : List (Nat × α)} {e : Nat × α}
    (he : e ∈ renameHead c l) : e.2 ∈ l.map (·.2) := by
  obtain ⟨e', he', h2⟩ := renameHead_mem he
  rw [← h2]; exact List.mem_map_of_mem he'

theorem forall₂_renameHead {α β : Type} {R : Nat × α → Nat × β → Prop} (c : Nat)
    (hR : ∀ a b, R a b → R (c, a.2) (c, b.2)) {l : List (Nat × α)} {l' : List (Nat × β)}
    (h : List.Forall₂ R l l') : List.Forall₂ R (renameHead c l) (renameHead c l') := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons h1 h2 => exact List.Forall₂.cons (hR _ _ h1) h2

theorem forall₂_flatMap {α β γ δ : Type} {R : γ → δ → Prop} {S : α → β → Prop}
    {f : α → List γ} {g : β → List δ} (hfg : ∀ a b, S a b → List.Forall₂ R (f a) (g b)) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ S l l' →
      List.Forall₂ R (l.flatMap f) (l'.flatMap g)
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons h1 h2 => by
    simp only [List.flatMap_cons]
    exact List.rel_append (hfg _ _ h1) (forall₂_flatMap hfg h2)

theorem forall₂_cutList {α β : Type} {R : α → β → Prop} :
    ∀ (sz : List Nat) {l : List α} {l' : List β}, List.Forall₂ R l l' →
      List.Forall₂ (List.Forall₂ R) (cutList l sz) (cutList l' sz)
  | [], _, _, _ => List.Forall₂.nil
  | n :: sz, _, _, h => List.Forall₂.cons (List.forall₂_take n h)
      (forall₂_cutList sz (List.forall₂_drop n h))

theorem forall₂_map_fst {α β : Type} {R : Nat × α → Nat × β → Prop}
    (hR : ∀ a b, R a b → a.1 = b.1) : ∀ {l : List (Nat × α)} {l' : List (Nat × β)},
    List.Forall₂ R l l' → l.map (·.1) = l'.map (·.1)
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h1 h2 => by
    simp only [List.map_cons, hR _ _ h1, forall₂_map_fst hR h2]

theorem cutList_map {α β : Type} (f : α → β) :
    ∀ (sz : List Nat) (l : List α), (cutList l sz).map (List.map f) = cutList (l.map f) sz
  | [], _ => rfl
  | n :: sz, l => by
    simp only [cutList, List.map_cons, List.map_take, List.map_drop, cutList_map f sz]

theorem headCv_eq {α β : Type} {P : List (Nat × α)} {Q : List (Nat × β)}
    (h : P.map (·.1) = Q.map (·.1)) : headCv P = headCv Q := by
  cases P with
  | nil => cases Q with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a P => cases Q with
    | nil => simp at h
    | cons b Q =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [headCv, h.1]

/-- The parts of two lists with the same compare values have the same first
compare values. -/
theorem cutList_headCv {α β : Type} {l : List (Nat × α)} {l' : List (Nat × β)}
    (h : l.map (·.1) = l'.map (·.1)) (sz : List Nat) :
    (cutList l sz).map headCv = (cutList l' sz).map headCv := by
  have h1 : (cutList l sz).map headCv = ((cutList l sz).map (List.map (·.1))).map
      (fun P => headCv (P.map (fun c => (c, ())))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro P _
    apply headCv_eq
    simp
  have h2 : (cutList l' sz).map headCv = ((cutList l' sz).map (List.map (·.1))).map
      (fun P => headCv (P.map (fun c => (c, ())))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro P _
    apply headCv_eq
    simp
  rw [h1, h2, cutList_map, cutList_map, h]

theorem partSizes_one (n : Nat) (j : Bool) : partSizes n 1 j = [n] := by
  cases j <;> simp [partSizes, Nat.mod_one]

theorem cutList_one {α : Type} (l : List α) : cutList l [l.length] = [l] := by
  simp [cutList]

/-! ## Multisets for the nodes reached -/

theorem subperm_iff_le {α : Type} {l l' : List α} : l.Subperm l' ↔ (l : Multiset α) ≤ l' :=
  Multiset.coe_le.symm

/-! ## The definitions of the statement -/

/-- An abstract node in order at every level: its entries in strictly
increasing order of compare values, and so each child's (026-24's `WF`
without the ranges). -/
def InOrd : (h : Nat) → Node h → Prop
  | 0, x => (x : List (Nat × Nat)).Pairwise CvLtA
  | h + 1, x => (kids x).Pairwise CvLtA ∧ ∀ e ∈ kids x, InOrd h e.2

/-- Entries that emit gives, (compare value, id), and planned abstract
entries: the same compare values, and each id holds its entry's node in T. -/
def HoldsE (cf : Cfg) (T : Tree) (g h : Nat) (E : List (Nat × NodeId))
    (A : List (Nat × Node h)) : Prop :=
  List.Forall₂ (fun e a => e.1 = a.1 ∧ Holds cf T g h e.2 a.2) E A

/-- A node's live list P holds the abstract node Q of height h: a leaf's is
Q; an inner node's entries hold Q's children. -/
def RelH (cf : Cfg) (T : Tree) (g : Nat) : (h : Nat) → List (Nat × NodeId) → Node h → Prop
  | 0, P, Q => P = Q
  | h + 1, P, Q => HoldsE cf T g h P (kids Q)

/-- Entries that emit gives and the planned entries (`ents`: an id, or none
for a new node): the same compare values; a planned id is the id given, a new
node's id is no node of s. -/
def MatchF (s : Tree) (E : List (Nat × NodeId)) (P : List (Nat × Option NodeId)) : Prop :=
  List.Forall₂ (fun e p => e.1 = p.1 ∧ (p.2 = some e.2 ∨ (p.2 = none ∧ s.obj e.2 = none))) E P

/-- What a run of emit from acc to acc' writes, W (newest first): each node
once; a fresh id of the run or an old node of U; every time klong at most i;
an old node keeps its klongs and gets klongs after a time klong of i. -/
structure WOk (i : Time) (s : Tree) (U : List NodeId) (acc acc' : Acc)
    (W : List (NodeId × Obj)) : Prop where
  ws : acc'.ws = W ++ acc.ws
  next : acc.next ≤ acc'.next
  nodup : (W.map (·.1)).Nodup
  ids : ∀ w ∈ W.map (·.1), (acc.next ≤ w ∧ w < acc'.next) ∨ w ∈ U
  times : ∀ p ∈ W, ∃ n, p.2 = .key n ∧ ∀ t, Klong.time t ∈ n.ks → t ≤ i
  frame : ∀ p ∈ W, ∀ n, s.obj p.1 = some (.key n) →
    ∃ more, p.2 = .key { n with ks := n.ks ++ Klong.time i :: more }

/-- A tree T after the writes W: it has them; every other node of U is as in
s; every node of s is a node of T; every payload p of the leaves is a node of
T, and the nodes reached from it with the fuel of a leaf of segment g, or
more, are among PB p. -/
structure TPre (cf : Cfg) (s T : Tree) (g : Nat) (W : List (NodeId × Obj)) (U : List NodeId)
    (Py : List (Nat × NodeId)) (PB : Nat × NodeId → List NodeId) : Prop where
  ws : ∀ p ∈ W, T.obj p.1 = some p.2
  keep : ∀ z ∈ U, z ∉ W.map (·.1) → T.obj z = s.obj z
  exist : ∀ z, s.obj z ≠ none → T.obj z ≠ none
  pays : ∀ p ∈ Py, T.obj p.2 ≠ none ∧ ∀ f, cf.lev g 0 ≤ f → (reachAt T f p.2).Subperm (PB p)

/-- The old nodes that W writes are key nodes of segment g shaped as PE's trees
(an appended base, `EOk`). -/
def WSh (cf : Cfg) (s : Tree) (g : Nat) (W : List (NodeId × Obj)) : Prop :=
  ∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n h', o = .key n ∧ Shaped cf s g h' p.1

/-- Every key node that W writes meets the rules of one node in T and has a
klong. -/
def WNode (cf : Cfg) (T : Tree) (W : List (NodeId × Obj)) : Prop :=
  ∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []

theorem WSh.nil {g : Nat} : WSh cf s g [] := by
  intro _ hp; cases hp

theorem WSh.append {g : Nat} {W1 W2 : List (NodeId × Obj)} (h1 : WSh cf s g W1)
    (h2 : WSh cf s g W2) : WSh cf s g (W1 ++ W2) :=
  fun p hp => (List.mem_append.mp hp).elim (h1 p) (h2 p)

theorem WNode.nil {T : Tree} : WNode cf T [] := by
  intro _ hp; cases hp

theorem WNode.append {T : Tree} {W1 W2 : List (NodeId × Obj)} (h1 : WNode cf T W1)
    (h2 : WNode cf T W2) : WNode cf T (W1 ++ W2) :=
  fun p hp => (List.mem_append.mp hp).elim (h1 p) (h2 p)

/-! ## One node -/

theorem liveWith_mem' (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases liveWith_mem' del r _ a h with h1 | ⟨i', h1⟩
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
theorem live_mem_key' {ks : List Klong} {c : Nat} {y : NodeId} (h : (c, y) ∈ live ks) :
    Klong.key c y ∈ ks := by
  unfold live liveWith at h
  rcases liveWith_mem' (lastBitmap ks) ks.zipIdx [] (c, y) h with h1 | ⟨i, h1⟩
  · simp at h1
  · obtain ⟨hlt, heq⟩ := List.mem_zipIdx' h1
    have h2 : Klong.key c y = ks[i] := heq
    rw [h2]
    exact List.getElem_mem hlt

theorem nodeOk_iff {p : Params} {T : Tree} {n : KNode} :
    nodeOk p T n = true ↔ n.ks.length ≤ p.M ∧ klongsWf n.ks = true ∧
      ∀ c y, Klong.key c y ∈ n.ks → T.obj y ≠ none := by
  unfold nodeOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun c y hk => ?_⟩
    have := h3 _ hk
    simpa [Option.isSome_iff_ne_none] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun k hk => ?_⟩
    cases k with
    | key c y => simpa [Option.isSome_iff_ne_none] using h3 c y hk
    | time t => rfl
    | del b => rfl

theorem nodeOk_transfer {p : Params} {T : Tree} {n : KNode} (h : nodeOk p s n = true)
    (hex : ∀ z, s.obj z ≠ none → T.obj z ≠ none) : nodeOk p T n = true := by
  rw [nodeOk_iff] at h ⊢
  exact ⟨h.1, h.2.1, fun c y hk => hex y (h.2.2 c y hk)⟩

theorem holds_of_rel {T : Tree} {g h : Nat} {x : NodeId} {n : KNode} {Q : Node h}
    (hobj : T.obj x = some (.key n)) (hleaf : n.leaf = (h == 0)) (hlev : n.level = cf.lev g h)
    (hg : g ≤ cf.G) (hh : h ≤ cf.H) (hok : nodeOk cf.params T n = true)
    (hr : RelH cf T g h (live n.ks) Q) : Holds cf T g h x Q := by
  cases h with
  | zero => exact Holds.leaf hobj (by simpa using hleaf) hlev hg hok hr
  | succ h =>
    exact Holds.inner hobj (by simpa using hleaf) hlev hg hh hok
      (forall₂_map_fst (fun _ _ h => h.1) hr)
      (fun p hp => ((List.forall₂_iff_zip.mp hr).2 hp).2)

theorem Holds.obj {T : Tree} {g h : Nat} {x : NodeId} {Q : Node h} (hx : Holds cf T g h x Q) :
    ∃ n, T.obj x = some (.key n) ∧ n.level = cf.lev g h := by
  cases hx with
  | leaf hobj _ hlev _ _ _ => exact ⟨_, hobj, hlev⟩
  | inner hobj _ hlev _ _ _ _ _ => exact ⟨_, hobj, hlev⟩

/-! ## The nodes reached -/

theorem reachAt_key {T : Tree} {x : NodeId} {n : KNode} (h : T.obj x = some (.key n)) (f : Nat) :
    reachAt T (f + 1) x = x :: (live n.ks).flatMap (fun cy => reachAt T f cy.2) := by
  simp only [reachAt, h]

theorem reachAt_val {T : Tree} {x : NodeId} {v : Nat} (h : T.obj x = some (.val v)) :
    ∀ f, reachAt T f x = [x]
  | 0 => rfl
  | f + 1 => by simp only [reachAt, h]

/-- A walk that meets only nodes that T has as s has them is the same in T. -/
theorem reachAt_agree {T : Tree} : ∀ (f : Nat) (y : NodeId),
    (∀ z ∈ reachAt s f y, T.obj z = s.obj z) → reachAt T f y = reachAt s f y
  | 0, _, _ => rfl
  | f + 1, y, h => by
    have hy : T.obj y = s.obj y := h y (by simp [reachAt])
    simp only [reachAt, hy]
    cases ho : s.obj y with
    | none => rfl
    | some o =>
      cases o with
      | val v => rfl
      | key n =>
        simp only [List.cons.injEq, true_and]
        apply List.flatMap_congr
        intro cy hcy
        apply reachAt_agree f cy.2
        intro z hz
        apply h z
        simp only [reachAt, ho, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨cy, hcy, hz⟩

/-- The children of a sound node: key nodes of lower levels, sound, or values. -/
theorem good_kids {y : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi) {n : KNode}
    (hobj : s.obj y = some (.key n)) : ∀ c z, (c, z) ∈ live n.ks →
      (∃ m, s.obj z = some (.key m) ∧ m.level < n.level ∧ ∃ lo' hi', Good s z lo' hi') ∨
        (∃ v, s.obj z = some (.val v)) := by
  cases hg with
  | mk _ _ _ n' hobj' _ _ _ hval hkey hseg hkid =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    intro c z hm
    by_cases hl : n.leaf = true
    · by_cases hlong : isLong c = true
      · obtain ⟨m, h1, h2, _⟩ := hkey c z hm (fun _ => hlong)
        exact Or.inl ⟨m, h1, h2, 0, none, hseg hl c z hm hlong⟩
      · exact Or.inr (hval hl c z hm (by simpa using hlong))
    · obtain ⟨m, h1, h2, _⟩ := hkey c z hm (fun h => absurd h hl)
      obtain ⟨pre, post, he⟩ := List.append_of_mem hm
      exact Or.inl ⟨m, h1, h2, _, _, hkid (by simpa using hl) pre c z post he⟩

theorem good_obj {y : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi) :
    ∃ n, s.obj y = some (.key n) := by
  cases hg with
  | mk _ _ _ n hobj _ _ _ _ _ _ _ => exact ⟨n, hobj⟩

/-- Every node a sound node reaches is a node of s. -/
theorem reach_exists : ∀ (f : Nat) {y : NodeId} {lo : Nat} {hi : Option Nat}, Good s y lo hi →
    ∀ z ∈ reachAt s f y, s.obj z ≠ none
  | 0, y, _, _, hg, z, hz => by
    obtain ⟨n, hn⟩ := good_obj hg
    simp only [reachAt, List.mem_singleton] at hz
    subst hz; simp [hn]
  | f + 1, y, _, _, hg, z, hz => by
    obtain ⟨n, hn⟩ := good_obj hg
    rw [reachAt_key hn, List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨⟨c, w⟩, hw, hz⟩
    · simp [hn]
    · rcases good_kids hg hn c w hw with ⟨m, _, _, lo', hi', hg'⟩ | ⟨v, hv⟩
      · exact reach_exists f hg' z hz
      · rw [reachAt_val hv, List.mem_singleton] at hz
        subst hz; simp [hv]

/-- The walk from a sound node does not depend on more fuel than its own. -/
theorem reach_stable : ∀ (f : Nat) {y : NodeId} {lo : Nat} {hi : Option Nat}, Good s y lo hi →
    s.fuel y ≤ f → reachAt s f y = reachAt s (s.fuel y) y := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro y lo hi hg hf
    obtain ⟨n, hn⟩ := good_obj hg
    have hfu : s.fuel y = n.level + 1 := by simp [Tree.fuel, hn]
    rw [hfu] at hf ⊢
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [reachAt_key hn, reachAt_key hn]
    simp only [List.cons.injEq, true_and]
    apply List.flatMap_congr
    intro ⟨c, w⟩ hw
    rcases good_kids hg hn c w hw with ⟨m, hm, hlt, lo', hi', hg'⟩ | ⟨v, hv⟩
    · have hfw : s.fuel w = m.level + 1 := by simp [Tree.fuel, hm]
      rw [ih f' (by omega) hg' (by omega), ih n.level (by omega) hg' (by omega)]
    · rw [reachAt_val hv, reachAt_val hv]

/-! ## The old tree -/

/-- The facts of the tree before that emit needs: every key node meets the
rules of one node, has a klong, and has times before i. -/
def SOk (cf : Cfg) (i : Time) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) →
    nodeOk cf.params s n = true ∧ n.ks ≠ [] ∧ ∀ t, Klong.time t ∈ n.ks → t < i

theorem mem_reachAt_self' (T : Tree) (f : Nat) (x : NodeId) : x ∈ reachAt T f x := by
  cases f <;> simp [reachAt]

theorem UiL_eq (es : List (Nat × VN)) : UiL s es = es.flatMap (fun e => Ui s e.2) := by
  induction es with
  | nil => simp [UiL]
  | cons e r ih => obtain ⟨c, v⟩ := e; simp [UiL, ih]

theorem paysL_eq (es : List (Nat × VN)) : paysL es = es.flatMap (fun e => pays e.2) := by
  induction es with
  | nil => simp [paysL]
  | cons e r ih => obtain ⟨c, v⟩ := e; simp [paysL, ih]

theorem Ui_node (b : Option NodeId) (g h : Nat) (join : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec) :
    Ui s (.node b g h join es F dec) = b.toList ++ (if h = 0 then [] else es.flatMap (fun e => Ui s e.2)) := by
  simp [Ui, UiL_eq]

theorem pays_node (b : Option NodeId) (g h : Nat) (join : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec) :
    pays (.node b g h join es F dec) =
      (if h = 0 then es.map (fun e => (e.1, e.2.oid)) else es.flatMap (fun e => pays e.2)) := by
  simp [pays, paysL_eq]

theorem Cfg.lev_succ (cf : Cfg) (g h : Nat) : cf.lev g (h + 1) = cf.lev g h + 1 := by
  simp only [Cfg.lev]; omega

theorem shaped_obj {g h : Nat} {y : NodeId} (hsh : Shaped cf s g h y) :
    ∃ n, s.obj y = some (.key n) ∧ n.level = cf.lev g h ∧ n.leaf = (h == 0) ∧ g ≤ cf.G ∧ h ≤ cf.H := by
  cases hsh with
  | leaf hobj hleaf hlev hg _ => exact ⟨_, hobj, hlev, by simpa using hleaf, hg, Nat.zero_le _⟩
  | inner hobj hleaf hlev hg hh _ _ => exact ⟨_, hobj, hlev, by simpa using hleaf, hg, by omega⟩

/-- **An untouched node holds what it held**: a node shaped as PE's trees, all
of whose nodes reached are in T as in s, holds its view in T. -/
theorem holds_kept (hs : SOk cf i s) {T : Tree} (hex : ∀ z, s.obj z ≠ none → T.obj z ≠ none) :
    ∀ (h : Nat) {g : Nat} {y : NodeId}, Shaped cf s g h y → (∀ z ∈ R s y, T.obj z = s.obj z) →
      Holds cf T g h y (view h s y) := by
  intro h
  induction h with
  | zero =>
    intro g y hsh hag
    obtain ⟨n, hobj, hlev, hleaf, hg, hh⟩ := shaped_obj hsh
    have hT : T.obj y = some (.key n) := by rw [hag y (mem_reachAt_self' _ _ _), hobj]
    exact holds_of_rel hT hleaf hlev hg hh (nodeOk_transfer (hs y n hobj).1 hex) (view_zero hobj).symm
  | succ h ih =>
    intro g y hsh hag
    obtain ⟨n, hobj, hlev, hleaf, hg, hh⟩ := shaped_obj hsh
    have hT : T.obj y = some (.key n) := by rw [hag y (mem_reachAt_self' _ _ _), hobj]
    refine holds_of_rel hT hleaf hlev hg hh (nodeOk_transfer (hs y n hobj).1 hex) ?_
    show HoldsE cf T g h (live n.ks) (kids (view (h + 1) s y))
    rw [view_succ hobj]
    unfold HoldsE
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro cy hcy
    refine ⟨rfl, ?_⟩
    have hk : Shaped cf s g h cy.2 := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hkids =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hkids cy.1 cy.2 hcy
    obtain ⟨m, hm, hmlev, _⟩ := shaped_obj hk
    apply ih hk
    intro z hz
    apply hag z
    have hRy : R s y = reachAt s (cf.lev g h + 1 + 1) y := by
      simp [R, Tree.fuel, hobj, hlev, Cfg.lev_succ]
    have hRc : R s cy.2 = reachAt s (cf.lev g h + 1) cy.2 := by
      simp [R, Tree.fuel, hm, hmlev]
    rw [hRy, reachAt_key hobj, List.mem_cons, List.mem_flatMap]
    rw [hRc] at hz
    exact Or.inr ⟨cy, hcy, hz⟩

/-- The nodes an untouched node reaches are nodes of s. -/
theorem ui_exists : ∀ (h : Nat) {g : Nat} {v : VN}, VOk cf s g h v → EOk cf i s g h v →
    ∀ z ∈ Ui s v, s.obj z ≠ none := by
  intro h
  induction h with
  | zero =>
    intro g v hv he z hz
    cases hv with
    | old hsh hg _ => exact reach_exists _ hg.choose_spec.choose_spec z hz
    | leaf _ _ _ =>
      cases he with
      | node _ hb _ _ =>
        rw [Ui_node] at hz
        simp only [ite_true, List.append_nil, Option.mem_toList] at hz
        obtain ⟨n, hn, _⟩ := shaped_obj (hb z hz)
        simp [hn]
  | succ h ih =>
    intro g v hv he z hz
    cases hv with
    | old hsh hg _ => exact reach_exists _ hg.choose_spec.choose_spec z hz
    | inner hk _ _ _ _ =>
      cases he with
      | node _ hb _ hke =>
        rw [Ui_node] at hz
        simp only [Nat.add_one_ne_zero, ite_false, List.mem_append, Option.mem_toList,
          List.mem_flatMap] at hz
        rcases hz with hz | ⟨e, he', hz⟩
        · obtain ⟨n, hn, _⟩ := shaped_obj (hb z hz)
          simp [hn]
        · exact ih (hk e he') (hke e he' (by omega)) z hz

/-! ## The decision -/

theorem dec_same {n : KNode} {join : Bool} {F : List (Nat × Option NodeId)}
    (h : decideNode cf i (some n) join F = .same) : (live n.ks).map (fun q => (q.1, some q.2)) = F := by
  unfold decideNode at h
  simp only at h
  split at h
  · rename_i hc; simpa using hc
  · split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h

theorem dec_append {n : KNode} {join : Bool} {F : List (Nat × Option NodeId)}
    (h : decideNode cf i (some n) join F = .append) :
    n.ks.length + (appendKsO i n.ks F).length ≤ cf.M := by
  unfold decideNode at h
  simp only at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- Parts of at most B entries, if B parts of k hold n. -/
theorem partSizes_le {n k B : Nat} (hk : 0 < k) (hn : n ≤ k * B) (j : Bool) :
    ∀ x ∈ partSizes n k j, x ≤ B := by
  intro x hx
  simp only [partSizes, List.mem_map, List.mem_range] at hx
  obtain ⟨jj, hjj, rfl⟩ := hx
  have hdm := Nat.div_add_mod n k
  generalize n / k = q at hdm ⊢
  generalize n % k = r at hdm ⊢
  have hle : k * q ≤ k * B := by omega
  have hqB : q ≤ B := Nat.le_of_mul_le_mul_left hle hk
  have hlt : 0 < r → q < B := by
    intro hr
    have : k * q < k * B := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  cases j <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> split <;> omega

theorem nParts_cover {cap n : Nat} (hc : 1 ≤ cap) :
    (n ≤ cap ∧ nParts cap n = 1) ∨ (cap < n ∧ 2 ≤ nParts cap n ∧ n ≤ nParts cap n * cap) := by
  unfold nParts
  have hm : max cap 1 = cap := by omega
  simp only [hm]
  split
  · exact Or.inl ⟨by assumption, rfl⟩
  · rename_i hn
    right
    have hdm := Nat.div_add_mod (n + cap - 1) cap
    have hmod := Nat.mod_lt (n + cap - 1) (show 0 < cap by omega)
    generalize (n + cap - 1) / cap = q at hdm ⊢
    generalize (n + cap - 1) % cap = r at hdm hmod
    refine ⟨by omega, ?_, ?_⟩
    · by_contra hq
      have : q ≤ 1 := by omega
      have : cap * q ≤ cap * 1 := Nat.mul_le_mul_left cap this
      omega
    · rw [Nat.mul_comm]; omega

/-- Every part that a decision `parts k` cuts fits a node, with its time klong:
k is at least 1, and each part's size is at most M - 1. -/
theorem dec_parts (hcf : cf.Ok) {base : Option KNode} {join : Bool} {F : List (Nat × Option NodeId)}
    {k : Nat} (h : decideNode cf i base join F = .parts k) :
    1 ≤ k ∧ ∀ x ∈ partSizes F.length k join, x + 1 ≤ cf.M := by
  have hcut : ∀ n, 1 ≤ cutParts cf n ∧ ∀ x ∈ partSizes n (cutParts cf n) join, x + 1 ≤ cf.M := by
    intro n
    have := hcf.hM; have := hcf.capM; have := hcf.cap1
    unfold cutParts
    split
    · rename_i hn
      refine ⟨le_refl _, fun x hx => ?_⟩
      rw [partSizes_one, List.mem_singleton] at hx
      omega
    · rename_i hn
      refine ⟨by omega, fun x hx => ?_⟩
      have : n ≤ max 2 (nParts cf.cap n) * cf.cap := by
        rcases nParts_cover (n := n) hcf.cap1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
        · have : 2 * cf.cap ≤ max 2 (nParts cf.cap n) * cf.cap :=
            Nat.mul_le_mul_right _ (le_max_left _ _)
          omega
        · have : nParts cf.cap n * cf.cap ≤ max 2 (nParts cf.cap n) * cf.cap :=
            Nat.mul_le_mul_right _ (le_max_right _ _)
          omega
      have := partSizes_le (by omega) this join x hx
      omega
  have hpk : ∀ n, Dec.parts n = Dec.parts k → n = k := fun n h => by injection h
  cases base with
  | none =>
    unfold decideNode at h
    simp only at h
    have := hpk _ h
    subst this
    cases join
    · exact hcut _
    · simp only [ite_true]
      have := hcf.cM
      rcases nParts_cover (n := F.length) hcf.c1 with ⟨h1, h2⟩ | ⟨_, h2, h3⟩
      · rw [h2]
        refine ⟨le_refl _, fun x hx => ?_⟩
        rw [partSizes_one, List.mem_singleton] at hx
        omega
      · refine ⟨by omega, fun x hx => ?_⟩
        have := partSizes_le (by omega) h3 true x hx
        omega
  | some n =>
    unfold decideNode at h
    simp only at h
    split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · have := hpk _ h; subst this
            rename_i hF
            refine ⟨le_refl _, fun x hx => ?_⟩
            rw [partSizes_one, List.mem_singleton] at hx
            omega
          · have := hpk _ h; subst this; exact hcut _
        · cases h
      · have := hpk _ h; subst this; exact hcut _

theorem MatchF.cvs {E : List (Nat × NodeId)} {P : List (Nat × Option NodeId)} (h : MatchF s E P) :
    E.map (·.1) = P.map (·.1) :=
  forall₂_map_fst (fun _ _ h => h.1) h

theorem MatchF.length {E : List (Nat × NodeId)} {P : List (Nat × Option NodeId)} (h : MatchF s E P) :
    E.length = P.length := List.Forall₂.length_eq h

theorem removedCvs_congr {β γ : Type} (lb : List (Nat × NodeId)) {F : List (Nat × β)}
    {F' : List (Nat × γ)} (h : F.map (·.1) = F'.map (·.1)) : removedCvs lb F = removedCvs lb F' := by
  unfold removedCvs
  have : ∀ c, (F.any (fun e => e.1 == c)) = (F'.any (fun e => e.1 == c)) := by
    intro c
    have h1 : F.any (fun e => e.1 == c) = (F.map (·.1)).any (· == c) := by rw [List.any_map]; rfl
    have h2 : F'.any (fun e => e.1 == c) = (F'.map (·.1)).any (· == c) := by rw [List.any_map]; rfl
    rw [h1, h2, h]
  simp only [this]

theorem filter_length_congr {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (l.filter p).length = (l'.filter q).length
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons (a := a) (b := b) h1 h2 => by
    simp only [List.filter_cons, hpq a b h1]
    split <;> simp [filter_length_congr hpq h2]

/-- emit's klongs for the real final list are as many as the decision counted
(`appendKsO`: a new node's id 0, never a live pointer's). -/
theorem emitKs_length_eq {ks : List Klong} {F' : List (Nat × NodeId)} {F : List (Nat × Option NodeId)}
    (hm : MatchF s F' F) (hlive : ∀ c y, (c, y) ∈ live ks → s.obj y ≠ none) :
    (emitKs i ks F').length = (appendKsO i ks F).length := by
  unfold emitKs appendKsO
  rw [List.length_append, List.length_append, removedCvs_congr (live ks) hm.cvs]
  congr 1
  unfold keysOf addedOf
  rw [List.length_map, List.length_map]
  apply filter_length_congr _ hm
  rintro ⟨c, y⟩ ⟨c', o⟩ ⟨h1, h2⟩
  simp only at h1 h2
  subst h1
  rcases h2 with rfl | ⟨rfl, hy⟩
  · rfl
  · simp only [isAdded, bne_iff_ne, ne_eq]
    intro hl
    exact hlive c y (lookup_mem hl) hy

theorem emitKs_times {ks : List Klong} {F : List (Nat × NodeId)} {t : Time}
    (h : Klong.time t ∈ emitKs i ks F) : t = i := by
  unfold emitKs emitHead keysOf at h
  split at h <;> simp at h <;> omega

theorem newKs_times {F : List (Nat × NodeId)} {t : Time} (h : Klong.time t ∈ newKs i F) : t = i := by
  unfold newKs keysOf at h
  simp at h; omega

/-! ## New nodes -/

/-- The list a new part is written with: an inner part starts with the empty key. -/
def rnH {α : Type} (h : Nat) (P : List (Nat × α)) : List (Nat × α) :=
  if h == 0 then P else renameHead 0 P

/-- The node that `newParts` writes for part P. -/
def npObj (cf : Cfg) (i : Time) (g h : Nat) (P : List (Nat × NodeId)) : Obj :=
  .key ⟨cf.lev g h, h == 0, newKs i (rnH h P)⟩

/-- The entries `newParts` gives for parts Ps from the id a. -/
def npE : Nat → List (List (Nat × NodeId)) → List (Nat × NodeId)
  | _, [] => []
  | a, P :: Ps => (headCv P, a) :: npE (a + 1) Ps

/-- The nodes `newParts` writes, oldest first. -/
def npW (cf : Cfg) (i : Time) (g h : Nat) : Nat → List (List (Nat × NodeId)) → List (NodeId × Obj)
  | _, [] => []
  | a, P :: Ps => (a, npObj cf i g h P) :: npW cf i g h (a + 1) Ps

theorem newParts_eq {g h : Nat} : ∀ (Ps : List (List (Nat × NodeId))) (acc : Acc),
    (newParts cf i g h Ps acc).1 = npE acc.next Ps ∧
    (newParts cf i g h Ps acc).2.ws = (npW cf i g h acc.next Ps).reverse ++ acc.ws ∧
    (newParts cf i g h Ps acc).2.next = acc.next + Ps.length
  | [], acc => by simp [newParts, npE, npW]
  | P :: Ps, acc => by
    obtain ⟨h1, h2, h3⟩ := newParts_eq (g := g) (h := h) Ps
      ((acc.fresh.2).write acc.fresh.1 (.key ⟨cf.lev g h, h == 0, newKs i (if h == 0 then P else renameHead 0 P)⟩))
    simp only [Acc.fresh, Acc.write] at h1 h2 h3
    simp only [newParts]
    refine ⟨?_, ?_, ?_⟩
    · simp only [h1, npE, Acc.fresh, Acc.write]
    · simp only [h2, npW, Acc.fresh, Acc.write, List.reverse_cons, List.append_assoc,
        List.singleton_append, npObj, rnH]
    · simp only [h3, Acc.fresh, Acc.write, List.length_cons]
      nomega

theorem npW_ids {g h : Nat} : ∀ (a : Nat) (Ps : List (List (Nat × NodeId))),
    (npW cf i g h a Ps).map (·.1) = List.range' a Ps.length
  | _, [] => rfl
  | a, P :: Ps => by simp [npW, npW_ids (a + 1) Ps, List.range'_succ]

theorem npE_ids : ∀ (a : Nat) (Ps : List (List (Nat × NodeId))),
    (npE a Ps).map (·.2) = List.range' a Ps.length
  | _, [] => rfl
  | a, P :: Ps => by simp [npE, npE_ids (a + 1) Ps, List.range'_succ]

theorem npE_cvs : ∀ (a : Nat) (Ps : List (List (Nat × NodeId))),
    (npE a Ps).map (·.1) = Ps.map headCv
  | _, [] => rfl
  | a, P :: Ps => by simp [npE, npE_cvs (a + 1) Ps]

theorem mem_npW {g h : Nat} : ∀ {a : Nat} {Ps : List (List (Nat × NodeId))} {p : NodeId × Obj},
    p ∈ npW cf i g h a Ps → a ≤ p.1 ∧ ∃ P ∈ Ps, p.2 = npObj cf i g h P
  | _, [], _, hp => by simp [npW] at hp
  | a, P :: Ps, p, hp => by
    simp only [npW, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_refl _, P, List.mem_cons_self, rfl⟩
    · obtain ⟨h1, Q, hQ, h2⟩ := mem_npW hp
      exact ⟨by omega, Q, List.mem_cons_of_mem _ hQ, h2⟩

/-- The entries of new parts against any list related part by part. -/
theorem npE_forall₂ {g h : Nat} {β : Type} {S : List (Nat × NodeId) → β → Prop}
    {R : Nat × NodeId → β → Prop} :
    ∀ {Ps : List (List (Nat × NodeId))} {Qs : List β} (a : Nat), List.Forall₂ S Ps Qs →
      (∀ P Q a', S P Q → (a', npObj cf i g h P) ∈ npW cf i g h a Ps → R (headCv P, a') Q) →
      List.Forall₂ R (npE a Ps) Qs
  | _, _, _, List.Forall₂.nil, _ => List.Forall₂.nil
  | _, _, a, List.Forall₂.cons (a := P) (b := Q) h1 h2, hR => by
    refine List.Forall₂.cons (hR P Q a h1 (by simp [npW])) ?_
    exact npE_forall₂ (a + 1) h2 (fun P' Q' a' hS hm => hR P' Q' a' hS (by
      simp only [npW, List.mem_cons]; exact Or.inr hm))

theorem forall₂_mem {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → List.Forall₂ (fun a b => R a b ∧ a ∈ l ∧ b ∈ l') l l'
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons h1 h2 =>
    List.Forall₂.cons ⟨h1, List.mem_cons_self, List.mem_cons_self⟩
      ((forall₂_mem h2).imp (fun _ _ h => ⟨h.1, List.mem_cons_of_mem _ h.2.1,
        List.mem_cons_of_mem _ h.2.2⟩))

/-! ## The statement of one virtual node, and of its children -/

/-- What emit of the virtual node v of segment g at height h, from acc to
acc', giving E, does: it writes W (`WOk`, the old nodes those v uses, shaped
at segment g: `WSh`); the entries it gives are the planned ones (`MatchF`
against `ents`), with the compare values of the pieces of the planned node as
emit writes it (`finEnts`, `fin`); and in a tree T after the writes (`TPre`)
each entry holds its piece, the nodes reached from them with the fuel of a
node of height h, or more, are among the old nodes v uses, the payloads'
bounds and the fresh ids of the run, and every node written meets the rules
of one node (`WNode`). -/
def ESpec (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (v : VN) (acc : Acc)
    (E : List (Nat × NodeId)) (acc' : Acc) : Prop :=
  ∃ W, WOk i s (Ui s v) acc acc' W ∧ WSh cf s g W ∧ MatchF s (renameHead 0 E) (ents 0 v) ∧
    (renameHead 0 E).map (·.1) = (finEnts 0 v (fin s h v)).map (·.1) ∧
    ∀ T PB, TPre cf s T g W (Ui s v) (pays v) PB →
      HoldsE cf T g h (renameHead 0 E) (finEnts 0 v (fin s h v)) ∧
      (∀ f, cf.lev g h + 1 ≤ f → (E.flatMap (fun e => reachAt T f e.2)).Subperm
        (Ui s v ++ (pays v).flatMap PB ++ List.range' acc.next (acc'.next - acc.next))) ∧
      WNode cf T W

/-- What emit of a planned node's children did, from acc to acc1, writing W
(its old nodes shaped at segment g): its real final list F' (with each child's
ids) is the planned final list F, has the compare values of the node as emit
writes it, and in a tree after the writes holds it (`RelH`), names nodes of T,
and reaches, with the fuel of a child or more, among the old nodes U the
children use, the payloads' bounds and the fresh ids; there the nodes written
meet the rules of one node. -/
structure CRes (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (v : VN) (U : List NodeId)
    (acc acc1 : Acc) (W : List (NodeId × Obj)) (F' : List (Nat × NodeId))
    (F : List (Nat × Option NodeId)) : Prop where
  w : WOk i s U acc acc1 W
  sh : WSh cf s g W
  m : MatchF s F' F
  cv : F'.map (·.1) = (fin s h v).map (·.1)
  t : ∀ T PB, TPre cf s T g W U (pays v) PB →
    RelH cf T g h F' (fin s h v) ∧ (∀ e ∈ F', T.obj e.2 ≠ none) ∧
    (∀ f, cf.lev g h ≤ f → (F'.flatMap (fun e => reachAt T f e.2)).Subperm
      (U ++ (pays v).flatMap PB ++ List.range' acc.next (acc1.next - acc.next))) ∧
    WNode cf T W

theorem tpre_sub {T : Tree} {g : Nat} {W1 W2 : List (NodeId × Obj)} {U1 U2 : List NodeId}
    {Py1 Py2 : List (Nat × NodeId)} {PB : Nat × NodeId → List NodeId}
    (h : TPre cf s T g W1 U1 Py1 PB) (hW : ∀ p ∈ W2, p ∈ W1) (hU : ∀ z ∈ U2, z ∈ U1)
    (hPy : ∀ p ∈ Py2, p ∈ Py1) (hk : ∀ z ∈ U2, z ∉ W2.map (·.1) → z ∉ W1.map (·.1)) :
    TPre cf s T g W2 U2 Py2 PB :=
  ⟨fun p hp => h.ws p (hW p hp), fun z hz hn => h.keep z (hU z hz) (hk z hz hn), h.exist,
    fun p hp => h.pays p (hPy p hp)⟩

/-- An id that is a node of s, and not one of U', is not written by a run
whose ids are fresh or of U'. -/
theorem not_mem_ws {a : Acc} {b : Nat} {Wi U' : List NodeId}
    (hfresh : ∀ x, a.next ≤ x → s.obj x = none) (hW : ∀ w ∈ Wi, (a.next ≤ w ∧ w < b) ∨ w ∈ U')
    {z : NodeId} (hz : s.obj z ≠ none) (hzU : z ∉ U') : z ∉ Wi := by
  intro hm
  rcases hW z hm with ⟨h1, _⟩ | h1
  · exact hz (hfresh z h1)
  · exact hzU h1

theorem WOk.mono {U U' : List NodeId} {a a' : Acc} {W : List (NodeId × Obj)}
    (h : WOk i s U a a' W) (hU : ∀ z ∈ U, z ∈ U') : WOk i s U' a a' W :=
  ⟨h.ws, h.next, h.nodup, fun w hw => (h.ids w hw).imp_right (hU w), h.times, h.frame⟩

/-- Two runs one after the other. -/
theorem WOk.append {U1 U2 : List NodeId} {a0 a1 a2 : Acc} {W1 W2 : List (NodeId × Obj)}
    (hfresh : ∀ x, a0.next ≤ x → s.obj x = none) (h1 : WOk i s U1 a0 a1 W1)
    (h2 : WOk i s U2 a1 a2 W2) (hnd : (U1 ++ U2).Nodup) (hex : ∀ z ∈ U1 ++ U2, s.obj z ≠ none) :
    WOk i s (U1 ++ U2) a0 a2 (W2 ++ W1) := by
  have hn1 := h1.next
  have hn2 := h2.next
  refine ⟨by rw [h2.ws, h1.ws, List.append_assoc], by nomega, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨h2.nodup, h1.nodup, ?_⟩
    intro w hw w' hw' hww
    subst hww
    rw [List.nodup_append] at hnd
    rcases h2.ids w hw with ⟨r1, r2⟩ | u2 <;> rcases h1.ids w hw' with ⟨q1, q2⟩ | u1
    · nomega
    · exact hex w (List.mem_append_left _ u1) (hfresh w (by nomega))
    · exact hex w (List.mem_append_right _ u2) (hfresh w (by nomega))
    · exact hnd.2.2 w u1 w u2 rfl
  · intro w hw
    rw [List.map_append, List.mem_append] at hw
    rcases hw with hw | hw
    · rcases h2.ids w hw with ⟨r1, r2⟩ | u2
      · left; constructor <;> nomega
      · exact Or.inr (List.mem_append_right _ u2)
    · rcases h1.ids w hw with ⟨r1, r2⟩ | u1
      · left; constructor <;> nomega
      · exact Or.inr (List.mem_append_left _ u1)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h2.times p hp
    · exact h1.times p hp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h2.frame p hp
    · exact h1.frame p hp

/-! ## An untouched node -/

theorem fin_old' (h : Nat) (y : NodeId) : fin s h (.old y) = view h s y := by
  rw [fin_old, absV_old]

/-- emit of an untouched node writes nothing and gives the node. -/
theorem old_spec (hs : SOk cf i s) {g h : Nat} {y : NodeId} {acc : Acc}
    (hv : VOk cf s g h (.old y)) : ESpec cf i s g h (.old y) acc [(0, y)] acc := by
  cases hv with
  | old hsh hg _ =>
  obtain ⟨lo, hi, hg⟩ := hg
  obtain ⟨n, hobj, hlev, _⟩ := shaped_obj hsh
  refine ⟨[], ⟨by simp, le_refl _, by simp, by simp, by simp, by simp⟩, WSh.nil,
    List.Forall₂.cons ⟨rfl, Or.inl rfl⟩ List.Forall₂.nil, rfl, ?_⟩
  intro T PB hT
  have hag : ∀ z ∈ R s y, T.obj z = s.obj z := fun z hz => hT.keep z hz (by simp)
  refine ⟨List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil, ?_, WNode.nil⟩
  · show Holds cf T g h y (fin s h (.old y))
    rw [fin_old']
    exact holds_kept hs hT.exist h hsh hag
  · intro f hf
    have hfu : s.fuel y = cf.lev g h + 1 := by simp [Tree.fuel, hobj, hlev]
    have hst : reachAt s f y = R s y := by
      rw [reach_stable f hg (by omega)]; rfl
    have hT' : reachAt T f y = R s y := by
      rw [reachAt_agree f y (fun z hz => hag z (hst ▸ hz)), hst]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hT', Nat.sub_self,
      List.range'_zero]
    show (R s y).Subperm (Ui s (.old y) ++ (pays (.old y)).flatMap PB)
    simp only [Ui, pays, List.flatMap_nil, List.append_nil]
    exact List.Subperm.refl _

/-! ## A planned node, by its decision -/

/-- The facts of a planned node that each decision's step uses: its children
use the old nodes U (its base apart), all nodes of s, all distinct. -/
structure NH (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (b : Option NodeId) (join : Bool)
    (es : List (Nat × VN)) (F : List (Nat × Option NodeId)) (dec : Dec) (U : List NodeId)
    (acc : Acc) : Prop where
  v : VOk cf s g h (.node b g h join es F dec)
  e : EOk cf i s g h (.node b g h join es F dec)
  ui : Ui s (.node b g h join es F dec) = b.toList ++ U
  nd : (b.toList ++ U).Nodup
  ex : ∀ z ∈ U, s.obj z ≠ none
  fresh : ∀ x, acc.next ≤ x → s.obj x = none
  ord : ∀ e ∈ finEnts 0 (.node b g h join es F dec) (fin s h (.node b g h join es F dec)), InOrd h e.2

theorem matchF_some {F' : List (Nat × NodeId)} : ∀ {L : List (Nat × NodeId)},
    MatchF s F' (L.map (fun q => (q.1, some q.2))) → F' = L
  | [], h => by cases h; rfl
  | q :: L, h => by
    cases h with
    | cons h1 h2 =>
      rename_i e F''
      obtain ⟨c1, c2⟩ := h1
      have := matchF_some h2
      subst this
      obtain ⟨a, y⟩ := e
      obtain ⟨c, z⟩ := q
      simp only at c1 c2
      rcases c2 with c2 | ⟨c2, _⟩
      · simp only [Option.some.injEq] at c2; subst c1 c2; rfl
      · cases c2

theorem inord_cvs : ∀ {h : Nat} {Q : Node h}, InOrd h Q → (Q.map (·.1)).Pairwise (· < ·)
  | 0, _, hq => List.pairwise_map.mpr hq
  | _ + 1, _, hq => List.pairwise_map.mpr hq.1

theorem sorted_of_cvs {β : Type} {P : List (Nat × NodeId)} {Q : List (Nat × β)}
    (h : P.map (·.1) = Q.map (·.1)) (hq : (Q.map (·.1)).Pairwise (· < ·)) : P.Pairwise CvLt := by
  rw [← h] at hq
  have := List.pairwise_map.mp hq
  exact this

theorem RelH.cvs {T : Tree} {g : Nat} : ∀ {h : Nat} {P : List (Nat × NodeId)} {Q : Node h},
    RelH cf T g h P Q → P.map (·.1) = Q.map (·.1)
  | 0, _, _, hr => congrArg (List.map Prod.fst) hr
  | _ + 1, _, _, hr => forall₂_map_fst (fun _ _ h => h.1) hr

theorem sub_cons {x : NodeId} {X U PBs r : List NodeId} (h : X.Subperm (U ++ PBs ++ r)) :
    (x :: X).Subperm ([x] ++ U ++ PBs ++ r) := by
  have : [x] ++ U ++ PBs ++ r = x :: (U ++ PBs ++ r) := by simp
  rw [this]; exact (List.subperm_cons x).mpr h

theorem shaped_getKey {g h : Nat} {x : NodeId} (hsh : Shaped cf s g h x) :
    ∃ n, s.obj x = some (.key n) ∧ getKey s x = some n ∧ n.level = cf.lev g h ∧
      n.leaf = (h == 0) ∧ g ≤ cf.G ∧ h ≤ cf.H := by
  obtain ⟨n, hobj, h1, h2, h3, h4⟩ := shaped_obj hsh
  exact ⟨n, hobj, by simp [getKey, hobj], h1, h2, h3, h4⟩

/-- **`same`**: the base kept; it holds the planned node, as its live list
is the real final list. -/
theorem step_same (hs : SOk cf i s) {g h : Nat} {x : NodeId} {join : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {U : List NodeId} {acc acc1 : Acc} {W0 : List (NodeId × Obj)}
    {F' : List (Nat × NodeId)} (hn : NH cf i s g h (some x) join es F .same U acc)
    (hc : CRes cf i s g h (.node (some x) g h join es F .same) U acc acc1 W0 F' F) :
    ESpec cf i s g h (.node (some x) g h join es F .same) acc [(0, x)] acc1 := by
  have hev := hn.e
  cases hev with
  | node hdec hb _ _ =>
  obtain ⟨n, hobj, hgk, hlev, hleaf, hg, hh⟩ := shaped_getKey (hb x rfl)
  simp only [Option.bind_some, hgk] at hdec
  have hF' : F' = live n.ks := matchF_some ((dec_same hdec.symm) ▸ hc.m)
  have hxU : x ∉ U := by
    have := hn.nd; simp only [Option.toList_some, List.singleton_append, List.nodup_cons] at this
    exact this.1
  have hxW : x ∉ W0.map (·.1) := not_mem_ws hn.fresh hc.w.ids (by simp [hobj]) hxU
  refine ⟨W0, hc.w.mono (fun z hz => by rw [hn.ui]; simp [hz]), hc.sh,
    List.Forall₂.cons ⟨rfl, Or.inl rfl⟩ List.Forall₂.nil, rfl, ?_⟩
  intro T PB hT
  have hTk : TPre cf s T g W0 U (pays (.node (some x) g h join es F .same)) PB :=
    tpre_sub hT (fun p hp => hp) (fun z hz => by rw [hn.ui]; simp [hz]) (fun p hp => hp)
      (fun z _ hn' => hn')
  obtain ⟨hrel, _, hreach, hwn⟩ := hc.t T PB hTk
  have hTx : T.obj x = some (.key n) := by
    rw [hT.keep x (by rw [hn.ui]; simp) hxW, hobj]
  refine ⟨List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil, ?_, hwn⟩
  · exact holds_of_rel hTx hleaf hlev hg hh (nodeOk_transfer (hs x n hobj).1 hT.exist)
      (hF' ▸ hrel)
  · intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, reachAt_key hTx, ← hF']
    rw [hn.ui]
    exact sub_cons (hreach f' (by omega))

/-- **`append`**: the base gets emit's klongs (026-24's lemma of emit). -/
theorem step_append (hs : SOk cf i s) {g h : Nat} {x : NodeId} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {U : List NodeId} {acc acc1 : Acc}
    {W0 : List (NodeId × Obj)} {F' : List (Nat × NodeId)} {n : KNode}
    (hn : NH cf i s g h (some x) join es F .append U acc)
    (hc : CRes cf i s g h (.node (some x) g h join es F .append) U acc acc1 W0 F' F)
    (hgk : getKey s x = some n) :
    ESpec cf i s g h (.node (some x) g h join es F .append) acc [(0, x)]
      (acc1.write x (.key { n with ks := n.ks ++ emitKs i n.ks F' })) := by
  have hev := hn.e
  cases hev with
  | node hdec hb _ _ =>
  obtain ⟨n', hobj, hgk', hlev, hleaf, hg, hh⟩ := shaped_getKey (hb x rfl)
  rw [hgk] at hgk'
  obtain rfl : n = n' := by injection hgk'
  simp only [Option.bind_some, hgk] at hdec
  obtain ⟨hok, hne, hti⟩ := hs x n hobj
  have hok' := nodeOk_iff.mp hok
  have hxU : x ∉ U := by
    have := hn.nd; simp only [Option.toList_some, List.singleton_append, List.nodup_cons] at this
    exact this.1
  have hxW : x ∉ W0.map (·.1) := not_mem_ws hn.fresh hc.w.ids (by simp [hobj]) hxU
  -- the real final list is in order
  have hsort : F'.Pairwise CvLt := by
    have := hn.ord (0, fin s h (.node (some x) g h join es F .append)) (by simp [finEnts])
    exact sorted_of_cvs hc.cv (inord_cvs this)
  set nobj : Obj := .key { n with ks := n.ks ++ emitKs i n.ks F' } with hnobj
  have hw := hc.w
  refine ⟨(x, nobj) :: W0, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    List.Forall₂.cons ⟨rfl, Or.inl rfl⟩ List.Forall₂.nil, rfl, ?_⟩
  · simp [Acc.write, hw.ws]
  · simpa [Acc.write] using hw.next
  · simp only [List.map_cons, List.nodup_cons]; exact ⟨hxW, hw.nodup⟩
  · intro w hw'
    simp only [List.map_cons, List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · right; rw [hn.ui]; simp
    · rcases hw.ids w hw' with h1 | h1
      · left; simpa [Acc.write] using h1
      · right; rw [hn.ui]; simp [h1]
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨_, rfl, fun t ht => ?_⟩
      rcases List.mem_append.mp ht with ht | ht
      · exact Nat.le_of_lt (hti t ht)
      · exact Nat.le_of_eq (emitKs_times ht)
    · exact hw.times p hp
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · intro n' hn'
      rw [hobj] at hn'
      obtain rfl : n = n' := by injection hn' with h1; injection h1
      obtain ⟨more, hm⟩ := emitKs_ext i n.ks F'
      exact ⟨more, by rw [hnobj, hm]⟩
    · exact hw.frame p hp
  · intro p hp o ho
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨n, h, (Option.some.inj (hobj.symm.trans ho)).symm, hb x rfl⟩
    · exact hc.sh p hp o ho
  · intro T PB hT
    have hTk : TPre cf s T g W0 U (pays (.node (some x) g h join es F .append)) PB :=
      tpre_sub hT (fun p hp => List.mem_cons_of_mem _ hp) (fun z hz => by rw [hn.ui]; simp [hz])
        (fun p hp => hp) (fun z hz hn' => by
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun h => hxU (h ▸ hz), hn'⟩)
    obtain ⟨hrel, hptr, hreach, hwn⟩ := hc.t T PB hTk
    have hTx : T.obj x = some nobj := hT.ws (x, nobj) List.mem_cons_self
    have hlive : live (n.ks ++ emitKs i n.ks F') = F' := emitKs_live hok'.2.1 i hsort
    have hlen : (n.ks ++ emitKs i n.ks F').length ≤ cf.M := by
      rw [List.length_append, emitKs_length_eq hc.m (fun c y hy => hok'.2.2 c y (live_mem_key' hy))]
      exact dec_append hdec.symm
    have hok2 : nodeOk cf.params T { n with ks := n.ks ++ emitKs i n.ks F' } = true := by
      rw [nodeOk_iff]
      refine ⟨hlen, emitKs_wf hok'.2.1 hne hti F', fun c y hk => ?_⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact hT.exist y (hok'.2.2 c y hk)
      · exact hptr (c, y) (emitKs_ptrs hk)
    refine ⟨List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil, ?_, ?_⟩
    · exact holds_of_rel hTx hleaf hlev hg hh hok2 (by rw [hlive]; exact hrel)
    · intro f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, reachAt_key hTx, hlive]
      rw [hn.ui, show (acc1.write x nobj).next = acc1.next from rfl]
      exact sub_cons (hreach f' (by omega))
    · intro p hp m hm
      rcases List.mem_cons.mp hp with rfl | hp
      · have hm' : nobj = .key m := hm
        rw [hnobj, Obj.key.injEq] at hm'
        subst hm'
        exact ⟨hok2, by simp [hne]⟩
      · exact hwn p hp m hm

/-! ## The parts -/

theorem renameHead_take {α : Type} (c : Nat) : ∀ (n : Nat) (l : List (Nat × α)),
    renameHead c (l.take n) = (renameHead c l).take n
  | 0, l => by simp [renameHead]
  | n + 1, [] => rfl
  | n + 1, _ :: _ => rfl

theorem renameHead_cvs {α β : Type} (c : Nat) {l : List (Nat × α)} {l' : List (Nat × β)}
    (h : l.map (·.1) = l'.map (·.1)) : (renameHead c l).map (·.1) = (renameHead c l').map (·.1) := by
  cases l with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a l => cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [renameHead, h.2]

theorem rnH_cvs {α β : Type} (h : Nat) {l : List (Nat × α)} {l' : List (Nat × β)}
    (hl : l.map (·.1) = l'.map (·.1)) : (rnH h l).map (·.1) = (rnH h l').map (·.1) := by
  unfold rnH; split
  · exact hl
  · exact renameHead_cvs 0 hl

theorem rnH_snd {α : Type} (h : Nat) (l : List (Nat × α)) : (rnH h l).map (·.2) = l.map (·.2) := by
  unfold rnH; split
  · rfl
  · exact renameHead_map_snd 0 l

theorem rnH_flatMap_snd {α β : Type} (h : Nat) (f : α → List β) (l : List (Nat × α)) :
    (rnH h l).flatMap (fun e => f e.2) = l.flatMap (fun e => f e.2) := by
  unfold rnH; split
  · rfl
  · exact renameHead_flatMap_snd 0 f l

theorem rnH_length {α : Type} (h : Nat) (l : List (Nat × α)) : (rnH h l).length = l.length := by
  unfold rnH; split
  · rfl
  · exact renameHead_length 0 l

theorem rnH_take {α : Type} {h : Nat} {l : List (Nat × α)} (hl : rnH h l = l) (n : Nat) :
    rnH h (l.take n) = l.take n := by
  unfold rnH at hl ⊢
  split
  · rfl
  · rename_i hh
    have hl' : renameHead 0 l = l := by simpa [hh] using hl
    rw [renameHead_take, hl']

/-- A planned node as emit writes it: an inner one starts with the empty key. -/
theorem fin_rnH (h : Nat) (b : Option NodeId) (g' h' : Nat) (join : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec) :
    rnH h (fin s h (.node b g' h' join es F dec)) = fin s h (.node b g' h' join es F dec) := by
  cases h with
  | zero => rfl
  | succ h =>
    exact renameHead_renameHead 0 0 _

theorem ents_parts {b : Option NodeId} {g' h' : Nat} {join : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {k : Nat} (hk : 1 ≤ k) :
    ents 0 (.node b g' h' join es F (.parts k)) =
      renameHead 0 ((cutList F (partSizes F.length k join)).map
        (fun P => (headCv P, (none : Option NodeId)))) := by
  simp only [ents]
  split
  · rename_i hk2
    unfold partEnts
    have hl : (cutList F (partSizes F.length k join)).length = k := by
      rw [cutList_length, partSizes_length]
    split
    · rename_i h0; rw [h0] at hl; simp at hl; omega
    · rename_i P rest h0; rw [h0]; rfl
  · have : k = 1 := by omega
    subst this
    rw [partSizes_one, cutList_one]; rfl

theorem finEnts_parts {h : Nat} {b : Option NodeId} {g' h' : Nat} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {k : Nat} (hk : 1 ≤ k) (fv : Node h)
    (hfv : rnH h fv = fv) :
    finEnts 0 (.node b g' h' join es F (.parts k)) fv =
      renameHead 0 ((cutList fv (partSizes fv.length k join)).map (fun Q => (headCv Q, rnH h Q))) := by
  by_cases hk2 : 2 ≤ k
  · rw [finEnts_cut 0 hk2 fv]
    have hl : (cutList fv (partSizes fv.length k join)).length = k := by
      rw [cutList_length, partSizes_length]
    obtain ⟨s1, sr, hsz⟩ : ∃ s1 sr, partSizes fv.length k join = s1 :: sr := by
      cases hc : partSizes fv.length k join with
      | nil => rw [hc] at hl; simp [cutList] at hl; omega
      | cons s1 sr => exact ⟨s1, sr, rfl⟩
    rw [hsz]
    simp only [cutList, cutEnts, List.map_cons, renameHead, rnH_take hfv]
    congr 1
    apply List.map_congr_left
    intro Q _
    cases h
    · simp [rnH]
    · simp [rnH]; rfl
  · have : k = 1 := by omega
    subst this
    simp only [finEnts, show ¬ (2 ≤ 1) by omega, ite_false]
    rw [partSizes_one, cutList_one]
    simp [renameHead, hfv]

theorem relH_cut {T : Tree} {g : Nat} : ∀ {h : Nat} {P : List (Nat × NodeId)} {Q : Node h}
    (sz : List Nat), RelH cf T g h P Q →
      List.Forall₂ (RelH cf T g h) (cutList P sz) (cutList Q sz)
  | 0, P, Q, sz, hr => by
    have : P = Q := hr
    subst this
    exact List.forall₂_same.mpr (fun _ _ => rfl)
  | _ + 1, _, _, sz, hr => forall₂_cutList sz hr

theorem relH_rnH {T : Tree} {g : Nat} : ∀ {h : Nat} {P : List (Nat × NodeId)} {Q : Node h},
    RelH cf T g h P Q → RelH cf T g h (rnH h P) (rnH h Q)
  | 0, _, _, hr => hr
  | _ + 1, _, _, hr => forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩) hr

theorem forall₂_exists {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, List.Forall₂.nil, _, ha => by simp at ha
  | _, _, List.Forall₂.cons h1 h2, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists h2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_of_cvs {α β : Type} : ∀ {l : List (Nat × α)} {l' : List (Nat × β)},
    l.map (·.1) = l'.map (·.1) → List.Forall₂ (fun a b => a.1 = b.1) l l'
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact List.Forall₂.cons h.1 (forall₂_of_cvs h.2)

theorem mem_of_mem_cutList {α : Type} {l : List α} {sz : List Nat} (hs : sz.sum = l.length)
    {P : List α} (hP : P ∈ cutList l sz) {e : α} (he : e ∈ P) : e ∈ l := by
  have := cutList_flatten l sz hs
  rw [← this]
  exact List.mem_flatten.mpr ⟨P, hP, he⟩

/-- The nodes reached from new parts: their ids, and what their entries reach. -/
theorem npE_reach {T : Tree} {g h f : Nat} :
    ∀ (a : Nat) (Ps : List (List (Nat × NodeId))),
      (∀ p ∈ npW cf i g h a Ps, T.obj p.1 = some p.2) →
      (∀ P ∈ Ps, live (newKs i (rnH h P)) = rnH h P) →
      ((npE a Ps).flatMap (fun e => reachAt T (f + 1) e.2)).Perm
        (List.range' a Ps.length ++ Ps.flatten.flatMap (fun e => reachAt T f e.2))
  | _, [], _, _ => List.Perm.refl _
  | a, P :: Ps, hw, hl => by
    have ih := npE_reach (f := f) (a + 1) Ps (fun p hp => hw p (by simp only [npW, List.mem_cons]; exact Or.inr hp))
      (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ))
    have hTa : T.obj a = some (npObj cf i g h P) := hw (a, npObj cf i g h P) (by simp [npW])
    simp only [npE, List.flatMap_cons, npObj] at hTa ⊢
    rw [reachAt_key hTa, hl P List.mem_cons_self, rnH_flatMap_snd, List.length_cons,
      List.range'_succ, List.flatten_cons, List.flatMap_append]
    simp only [List.cons_append]
    refine List.Perm.cons _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    exact List.perm_append_comm_assoc _ _ _

theorem sub_parts {Z X B U PBs r1 : List NodeId} (hX : X.Subperm (U ++ PBs ++ r1)) :
    (Z ++ X).Subperm (B ++ U ++ PBs ++ (r1 ++ Z)) := by
  rw [subperm_iff_le] at hX ⊢
  simp only [← Multiset.coe_add] at hX ⊢
  calc (Z : Multiset NodeId) + X ≤ Z + (U + PBs + r1) := add_le_add_right hX _
    _ ≤ B + U + PBs + (r1 + Z) := by
      have : (B : Multiset NodeId) + U + PBs + (r1 + Z) = B + (Z + (U + PBs + r1)) := by abel
      rw [this]; exact Multiset.le_add_left _ _

/-- **`parts k`**: the real final list cut into k new nodes with fresh ids
(026-24's `cut_spec`; each part fits a node by the decision and `Cfg.Ok`). -/
theorem step_parts (hcf : cf.Ok) {g h : Nat} {b : Option NodeId} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {k : Nat} {U : List NodeId}
    {acc acc1 : Acc} {W0 : List (NodeId × Obj)} {F' : List (Nat × NodeId)}
    (hn : NH cf i s g h b join es F (.parts k) U acc)
    (hc : CRes cf i s g h (.node b g h join es F (.parts k)) U acc acc1 W0 F' F) :
    ESpec cf i s g h (.node b g h join es F (.parts k)) acc
      (newParts cf i g h (cutList F' (partSizes F'.length k join)) acc1).1
      (newParts cf i g h (cutList F' (partSizes F'.length k join)) acc1).2 := by
  have hev := hn.e
  cases hev with
  | node hdec hb hnone _ =>
  obtain ⟨hk1, hfit⟩ := dec_parts hcf hdec.symm
  have hgh : g ≤ cf.G ∧ h ≤ cf.H := by
    cases b with
    | none => exact hnone rfl
    | some x =>
      obtain ⟨_, _, _, _, h3, h4⟩ := shaped_obj (hb x rfl)
      exact ⟨h3, h4⟩
  have hlen : F'.length = F.length := hc.m.length
  have hflen : (fin s h (.node b g h join es F (.parts k))).length = F'.length := by
    have := congrArg List.length hc.cv; simp only [List.length_map] at this; exact this.symm
  have hsum : (partSizes F'.length k join).sum = F'.length := partSizes_sum (by omega) join
  have hPsl : (cutList F' (partSizes F'.length k join)).length = k := by
    rw [cutList_length, partSizes_length]
  have hflat : (cutList F' (partSizes F'.length k join)).flatten = F' := cutList_flatten F' _ hsum
  have hfin : finEnts 0 (.node b g h join es F (.parts k)) (fin s h (.node b g h join es F (.parts k))) =
      renameHead 0 ((cutList (fin s h (.node b g h join es F (.parts k))) (partSizes F'.length k join)).map
        (fun Q => (headCv Q, rnH h Q))) := by
    rw [finEnts_parts hk1 _ (fin_rnH h b g h join es F _), hflen]
  obtain ⟨hE, hws, hnext⟩ := newParts_eq (cf := cf) (i := i) (g := g) (h := h)
    (cutList F' (partSizes F'.length k join)) acc1
  have hw := hc.w
  have hn1 := hw.next
  have hfr : ∀ p ∈ npW cf i g h acc1.next (cutList F' (partSizes F'.length k join)),
      s.obj p.1 = none := fun p hp => hn.fresh p.1 (by have := (mem_npW hp).1; nomega)
  refine ⟨(npW cf i g h acc1.next (cutList F' (partSizes F'.length k join))).reverse ++ W0,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hws, hw.ws, List.append_assoc]
  · rw [hnext]; nomega
  · rw [List.map_append, List.nodup_append, List.map_reverse, npW_ids]
    refine ⟨List.nodup_reverse.mpr (List.nodup_range' _), hw.nodup, ?_⟩
    intro w hw1 w' hw2 hww
    subst hww
    rw [List.mem_reverse, List.mem_range'] at hw1
    obtain ⟨j, _, rfl⟩ := hw1
    rcases hw.ids _ hw2 with ⟨_, h2⟩ | h2
    · nomega
    · exact hn.ex _ h2 (hn.fresh _ (by nomega))
  · intro w hw'
    rw [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse, npW_ids,
      List.mem_range'] at hw'
    rcases hw' with ⟨j, hj, rfl⟩ | hw'
    · left; rw [hnext, hPsl]; constructor <;> nomega
    · rcases hw.ids w hw' with ⟨h1, h2⟩ | h2
      · left; rw [hnext]; constructor <;> nomega
      · right; rw [hn.ui]; simp [h2]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨_, P, _, hP⟩ := mem_npW (List.mem_reverse.mp hp)
      exact ⟨⟨cf.lev g h, h == 0, newKs i (rnH h P)⟩, hP, fun t ht => Nat.le_of_eq (newKs_times ht)⟩
    · exact hw.times p hp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · intro n hn'
      rw [hfr p (List.mem_reverse.mp hp)] at hn'; cases hn'
    · exact hw.frame p hp
  · intro p hp o ho
    rcases List.mem_append.mp hp with hp | hp
    · rw [hfr p (List.mem_reverse.mp hp)] at ho; cases ho
    · exact hc.sh p hp o ho
  · -- the entries are the planned ones
    rw [hE, ents_parts hk1]
    unfold MatchF
    apply forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩)
    rw [List.forall₂_map_right_iff, ← hlen]
    have hS : List.Forall₂ (fun (P : List (Nat × NodeId)) (Q : List (Nat × Option NodeId)) =>
        P.map (·.1) = Q.map (·.1)) (cutList F' (partSizes F'.length k join))
        (cutList F (partSizes F'.length k join)) :=
      (forall₂_cutList _ (hc.m.imp (fun _ _ h => h.1))).imp
        (fun _ _ h => forall₂_map_fst (fun _ _ h => h) h)
    refine npE_forall₂ (cf := cf) (i := i) (g := g) (h := h) acc1.next hS ?_
    intro P Q a' hPQ hm
    exact ⟨headCv_eq hPQ, Or.inr ⟨rfl, hn.fresh a' (by have := (mem_npW hm).1; nomega)⟩⟩
  · -- their compare values
    rw [hE, hfin]
    apply renameHead_cvs
    rw [npE_cvs]
    simp only [List.map_map, Function.comp_def]
    exact cutList_headCv hc.cv _
  · intro T PB hT
    have hTk : TPre cf s T g W0 U (pays (.node b g h join es F (.parts k))) PB :=
      tpre_sub hT (fun p hp => List.mem_append_right _ hp) (fun z hz => by rw [hn.ui]; simp [hz])
        (fun p hp => hp) (fun z hz hn' => by
          rw [List.map_append, List.mem_append, not_or]
          refine ⟨fun hm => ?_, hn'⟩
          rw [List.map_reverse, List.mem_reverse, npW_ids, List.mem_range'] at hm
          obtain ⟨j, _, rfl⟩ := hm
          exact hn.ex _ hz (hn.fresh _ (by nomega)))
    obtain ⟨hrel, hptr, hreach, hwn⟩ := hc.t T PB hTk
    have hTw : ∀ p ∈ npW cf i g h acc1.next (cutList F' (partSizes F'.length k join)),
        T.obj p.1 = some p.2 := fun p hp =>
      hT.ws p (List.mem_append_left _ (List.mem_reverse.mpr hp))
    have hcvPQ : List.Forall₂ (fun (P : List (Nat × NodeId)) (Q : Node h) => P.map (·.1) = Q.map (·.1))
        (cutList F' (partSizes F'.length k join))
        (cutList (fin s h (.node b g h join es F (.parts k))) (partSizes F'.length k join)) :=
      (forall₂_cutList _ (forall₂_of_cvs hc.cv)).imp (fun _ _ h => forall₂_map_fst (fun _ _ h => h) h)
    have hordQ : ∀ Q ∈ cutList (fin s h (.node b g h join es F (.parts k))) (partSizes F'.length k join),
        InOrd h (rnH h Q) := by
      intro Q hQ
      have hm : rnH h Q ∈ (finEnts 0 (.node b g h join es F (.parts k))
          (fin s h (.node b g h join es F (.parts k)))).map (·.2) := by
        rw [hfin, renameHead_map_snd, List.map_map]
        exact List.mem_map.mpr ⟨Q, hQ, rfl⟩
      obtain ⟨e, he, he2⟩ := List.mem_map.mp hm
      exact he2 ▸ hn.ord e he
    have hsortP : ∀ P ∈ cutList F' (partSizes F'.length k join), (rnH h P).Pairwise CvLt := by
      intro P hP
      obtain ⟨Q, hQ, hPQ⟩ := forall₂_exists hcvPQ P hP
      exact sorted_of_cvs (rnH_cvs h hPQ) (inord_cvs (hordQ Q hQ))
    have hliveP : ∀ P ∈ cutList F' (partSizes F'.length k join), live (newKs i (rnH h P)) = rnH h P :=
      fun P hP => newKs_live i (hsortP P hP)
    have hfitP : ∀ P ∈ cutList F' (partSizes F'.length k join), P.length + 1 ≤ cf.M := by
      intro P hP
      have := cutList_length_le F' _ (cf.M - 1) (fun x hx => by
        have := hfit x (by rw [← hlen]; exact hx); omega) P hP
      have := hcf.hM; omega
    have hptrP : ∀ P ∈ cutList F' (partSizes F'.length k join), ∀ e ∈ P, T.obj e.2 ≠ none :=
      fun P hP e he => hptr e (mem_of_mem_cutList hsum hP he)
    have hokP : ∀ P ∈ cutList F' (partSizes F'.length k join),
        nodeOk cf.params T ⟨cf.lev g h, h == 0, newKs i (rnH h P)⟩ = true := by
      intro P hP
      rw [nodeOk_iff]
      refine ⟨?_, newKs_wf i _, fun c y hk => ?_⟩
      · show (newKs i (rnH h P)).length ≤ cf.M
        rw [newKs_length, rnH_length]; exact hfitP P hP
      · have hy := newKs_ptrs hk
        have : y ∈ P.map (·.2) := by rw [← rnH_snd h P]; exact List.mem_map.mpr ⟨_, hy, rfl⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp this
        exact hptrP P hP e he
    refine ⟨?_, ?_, ?_⟩
    · rw [hE, hfin]
      unfold HoldsE
      apply forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩)
      rw [List.forall₂_map_right_iff]
      refine npE_forall₂ (cf := cf) (i := i) (g := g) (h := h) acc1.next (forall₂_mem (relH_cut _ hrel)) ?_
      rintro P Q a' ⟨hr, hP, _⟩ hm
      refine ⟨headCv_eq (RelH.cvs hr), ?_⟩
      have hTa : T.obj a' = some (npObj cf i g h P) := hTw _ hm
      exact holds_of_rel hTa rfl rfl hgh.1 hgh.2 (hokP P hP) (by
        show RelH cf T g h (live (newKs i (rnH h P))) _
        rw [hliveP P hP]; exact relH_rnH hr)
    · intro f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [hE, hnext, hPsl]
      refine (npE_reach acc1.next _ hTw hliveP).subperm_right.mpr ?_
      rw [hflat, hPsl, hn.ui]
      have hr : List.range' acc.next (acc1.next + k - acc.next) =
          List.range' acc.next (acc1.next - acc.next) ++ List.range' acc1.next k := by
        have e1 : acc1.next + k - acc.next = (acc1.next - acc.next) + k := by nomega
        have e2 : acc.next + 1 * (acc1.next - acc.next) = acc1.next := by nomega
        rw [e1, ← List.range'_append, e2]
      rw [hr]
      exact sub_parts (hreach f' (by omega))
    · intro p hp m hm
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨_, P, hP, hP2⟩ := mem_npW (List.mem_reverse.mp hp)
        rw [hP2, npObj, Obj.key.injEq] at hm
        subst hm
        exact ⟨hokP P hP, by simp [newKs]⟩
      · exact hwn p hp m hm

/-! ## Emit of a planned node: its children, then its decision -/

/-- emit of a planned node after its children, by its decision, on its real
final list F (as `emit`). -/
def emitAfter (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (join : Bool) (dec : Dec)
    (b : Option NodeId) (F : List (Nat × NodeId)) (acc : Acc) :
    Option (List (Nat × NodeId) × Acc) :=
  match dec, b with
  | .same, some b => some ([(0, b)], acc)
  | .append, some b =>
    match getKey s b with
    | some n => some ([(0, b)], acc.write b (.key { n with ks := n.ks ++ emitKs i n.ks F }))
    | none => none
  | .parts k, _ => some (newParts cf i g h (cutList F (partSizes F.length k join)) acc)
  | _, none => none

theorem emit_node (b : Option NodeId) (g h : Nat) (join : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec) (acc : Acc) :
    emit cf i s (.node b g h join es F dec) acc =
      (emitKids cf i s es acc).bind (fun r =>
        emitAfter cf i s g h join dec b (if h == 0 then r.1 else renameHead 0 r.1) r.2) := by
  rw [emit.eq_2]
  cases emitKids cf i s es acc with
  | none => rfl
  | some r => obtain ⟨F0, acc1⟩ := r; rfl

/-- A planned node's decision: each case its step. -/
theorem node_dispatch (hcf : cf.Ok) (hs : SOk cf i s) {g h : Nat} {b : Option NodeId}
    {join : Bool} {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    {U : List NodeId} {acc acc1 acc' : Acc} {W0 : List (NodeId × Obj)} {F' E : List (Nat × NodeId)}
    (hn : NH cf i s g h b join es F dec U acc)
    (hc : CRes cf i s g h (.node b g h join es F dec) U acc acc1 W0 F' F)
    (he : emitAfter cf i s g h join dec b F' acc1 = some (E, acc')) :
    ESpec cf i s g h (.node b g h join es F dec) acc E acc' := by
  cases dec with
  | same =>
    cases b with
    | none => simp [emitAfter] at he
    | some x =>
      simp only [emitAfter, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact step_same hs hn hc
  | append =>
    cases b with
    | none => simp [emitAfter] at he
    | some x =>
      simp only [emitAfter] at he
      cases hgk : getKey s x with
      | none => rw [hgk] at he; cases he
      | some n =>
        rw [hgk] at he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact step_append hs hn hc hgk
  | parts k =>
    simp only [emitAfter, Option.some.injEq] at he
    have h1 : (newParts cf i g h (cutList F' (partSizes F'.length k join)) acc1).1 = E := by rw [he]
    have h2 : (newParts cf i g h (cutList F' (partSizes F'.length k join)) acc1).2 = acc' := by rw [he]
    rw [← h1, ← h2]
    exact step_parts hcf hn hc

/-! ## The children of a leaf: payloads -/

theorem emitKids_old {acc : Acc} : ∀ (es : List (Nat × VN)), (∀ e ∈ es, ∃ y, e.2 = .old y) →
    emitKids cf i s es acc = some (es.map (fun e => (e.1, e.2.oid)), acc)
  | [], _ => by rw [emitKids.eq_1]; rfl
  | (c, w) :: rest, h => by
    obtain ⟨y, hy⟩ := h (c, w) List.mem_cons_self
    simp only at hy
    subst hy
    rw [emitKids.eq_2, emit.eq_1]
    simp only
    rw [emitKids_old rest (fun e he => h e (List.mem_cons_of_mem _ he))]
    rfl

/-- The children of a planned leaf: its payloads, nothing written. -/
theorem leaf_cres {g : Nat} {b : Option NodeId} {join : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} {acc : Acc}
    (hold : ∀ e ∈ es, ∃ y, e.2 = .old y) (hF : F = es.flatMap (fun e => ents e.1 e.2)) :
    CRes cf i s g 0 (.node b g 0 join es F dec) [] acc acc [] (es.map (fun e => (e.1, e.2.oid))) F := by
  have hpays : pays (.node b g 0 join es F dec) = es.map (fun e => (e.1, e.2.oid)) := by
    rw [pays_node]; rfl
  refine ⟨⟨by simp, le_refl _, by simp, by simp, by simp, by simp⟩, WSh.nil, ?_, rfl, ?_⟩
  · rw [hF]
    unfold MatchF
    have : ∀ e ∈ es, ents e.1 e.2 = [(e.1, some e.2.oid)] := by
      intro e he
      obtain ⟨y, hy⟩ := hold e he
      rw [hy]; rfl
    have h2 : es.flatMap (fun e => ents e.1 e.2) = es.map (fun e => (e.1, some e.2.oid)) := by
      rw [List.flatMap_congr this]
      clear this hF hold hpays
      induction es with
      | nil => rfl
      | cons e r ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl
    rw [h2, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro e _
    exact ⟨rfl, Or.inl rfl⟩
  · intro T PB hT
    refine ⟨rfl, fun e he => (hT.pays e (hpays ▸ he)).1, fun f hf => ?_, WNode.nil⟩
    simp only [List.nil_append, Nat.sub_self, List.range'_zero, List.append_nil]
    rw [hpays]
    exact flatMap_subperm _ (fun p hp => (hT.pays p (hpays ▸ hp)).2 f hf)

/-! ## The children of an inner node -/

theorem finEnts_rename {h : Nat} (c : Nat) (v : VN) (fv : Node h) :
    finEnts c v fv = renameHead c (finEnts 0 v fv) := by
  cases v with
  | old y => rfl
  | node b g' h' join es F dec =>
    cases dec with
    | parts k =>
      simp only [finEnts]
      split
      · cases cutList fv (partSizes fv.length k join) with
        | nil => rfl
        | cons Q Qs => rfl
      · rfl
    | same => rfl
    | append => rfl

theorem ents_rename (c : Nat) (v : VN) : ents c v = renameHead c (ents 0 v) := by
  cases v with
  | old y => rfl
  | node b g' h' join es F dec =>
    cases dec with
    | parts k =>
      simp only [ents]
      split
      · unfold partEnts
        split <;> rfl
      · rfl
    | same => cases b <;> rfl
    | append => cases b <;> rfl

theorem mem_snd_of_rename {α : Type} {c : Nat} {l : List (Nat × α)} {e : Nat × α} (he : e ∈ l) :
    ∃ e' ∈ renameHead c l, e'.2 = e.2 := by
  have : e.2 ∈ (renameHead c l).map (·.2) := by
    rw [renameHead_map_snd]; exact List.mem_map_of_mem he
  obtain ⟨e', he', h2⟩ := List.mem_map.mp this
  exact ⟨e', he', h2⟩

theorem sub_two {X1 X2 U1 U2 P1 P2 r1 r2 : List NodeId} (h1 : X1.Subperm (U1 ++ P1 ++ r1))
    (h2 : X2.Subperm (U2 ++ P2 ++ r2)) :
    (X1 ++ X2).Subperm (U1 ++ U2 ++ (P1 ++ P2) ++ (r1 ++ r2)) := by
  rw [subperm_iff_le] at h1 h2 ⊢
  simp only [← Multiset.coe_add] at h1 h2 ⊢
  calc (X1 : Multiset NodeId) + X2 ≤ (U1 + P1 + r1) + (U2 + P2 + r2) := add_le_add h1 h2
    _ = U1 + U2 + (P1 + P2) + (r1 + r2) := by abel

/-- **emit of the children of an inner node**, one height down, from the
statement for each child. -/
theorem kids_spec (hcf : cf.Ok) (hs : SOk cf i s) {g h : Nat}
    (ih : ∀ {v : VN} {acc : Acc} {E : List (Nat × NodeId)} {acc' : Acc},
      VOk cf s g h v → EOk cf i s g h v → (Ui s v).Nodup → (∀ x, acc.next ≤ x → s.obj x = none) →
      (∀ e ∈ finEnts 0 v (fin s h v), InOrd h e.2) → emit cf i s v acc = some (E, acc') →
      ESpec cf i s g h v acc E acc') :
    ∀ (es : List (Nat × VN)) {acc : Acc} {F0 : List (Nat × NodeId)} {acc1 : Acc},
      (∀ e ∈ es, VOk cf s g h e.2) → (∀ e ∈ es, EOk cf i s g h e.2) →
      (es.flatMap (fun e => Ui s e.2)).Nodup → (∀ x, acc.next ≤ x → s.obj x = none) →
      (∀ e ∈ es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2)), InOrd h e.2) →
      emitKids cf i s es acc = some (F0, acc1) →
      ∃ W, WOk i s (es.flatMap (fun e => Ui s e.2)) acc acc1 W ∧ WSh cf s g W ∧
        MatchF s F0 (es.flatMap (fun e => ents e.1 e.2)) ∧
        F0.map (·.1) = (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))).map (·.1) ∧
        ∀ T PB, TPre cf s T g W (es.flatMap (fun e => Ui s e.2)) (es.flatMap (fun e => pays e.2)) PB →
          HoldsE cf T g h F0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))) ∧
          (∀ f, cf.lev g h + 1 ≤ f → (F0.flatMap (fun e => reachAt T f e.2)).Subperm
            (es.flatMap (fun e => Ui s e.2) ++ (es.flatMap (fun e => pays e.2)).flatMap PB ++
              List.range' acc.next (acc1.next - acc.next))) ∧
          WNode cf T W
  | [], acc, F0, acc1, _, _, _, _, _, he => by
    rw [emitKids.eq_1] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨[], ⟨by simp, le_refl _, by simp, by simp, by simp, by simp⟩, WSh.nil,
      List.Forall₂.nil, rfl, ?_⟩
    intro T PB _
    exact ⟨List.Forall₂.nil, fun f _ => List.nil_subperm, WNode.nil⟩
  | (c, w) :: rest, acc, F0, acc1, hv, he', hnd, hfresh, hord, he => by
    rw [emitKids.eq_2] at he
    cases hw : emit cf i s w acc with
    | none => rw [hw] at he; cases he
    | some r =>
    obtain ⟨E, accA⟩ := r
    rw [hw] at he
    simp only at he
    cases hr : emitKids cf i s rest accA with
    | none => rw [hr] at he; cases he
    | some r' =>
    obtain ⟨F, accB⟩ := r'
    rw [hr] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.flatMap_cons] at hnd hord ⊢
    have hvw : VOk cf s g h w := hv (c, w) List.mem_cons_self
    have hew : EOk cf i s g h w := he' (c, w) List.mem_cons_self
    have hnd' := hnd
    rw [List.nodup_append] at hnd'
    obtain ⟨W1, hW1, hsh1, hm1, hcv1, ht1⟩ := ih hvw hew hnd'.1 hfresh (by
      intro e he
      obtain ⟨e', he', h2⟩ := mem_snd_of_rename (c := c) he
      rw [← finEnts_rename] at he'
      exact h2 ▸ hord e' (List.mem_append_left _ he')) hw
    have hfA : ∀ x, accA.next ≤ x → s.obj x = none := fun x hx =>
      hfresh x (by have := hW1.next; nomega)
    obtain ⟨W2, hW2, hsh2, hm2, hcv2, ht2⟩ := kids_spec hcf hs ih rest
      (fun e he => hv e (List.mem_cons_of_mem _ he)) (fun e he => he' e (List.mem_cons_of_mem _ he))
      hnd'.2.1 hfA (fun e he => hord e (List.mem_append_right _ he)) hr
    have hex1 : ∀ z ∈ Ui s w, s.obj z ≠ none := ui_exists h hvw hew
    have hex2 : ∀ z ∈ rest.flatMap (fun e => Ui s e.2), s.obj z ≠ none := by
      intro z hz
      obtain ⟨e, he, hz⟩ := List.mem_flatMap.mp hz
      exact ui_exists h (hv e (List.mem_cons_of_mem _ he)) (he' e (List.mem_cons_of_mem _ he)) z hz
    have hdisj : ∀ z ∈ Ui s w, z ∉ rest.flatMap (fun e => Ui s e.2) :=
      fun z hz hz' => hnd'.2.2 z hz z hz' rfl
    refine ⟨W2 ++ W1, WOk.append hfresh hW1 hW2 hnd (fun z hz => by
        rcases List.mem_append.mp hz with hz | hz
        · exact hex1 z hz
        · exact hex2 z hz), hsh2.append hsh1, ?_, ?_, ?_⟩
    · unfold MatchF
      refine List.rel_append ?_ hm2
      rw [ents_rename c w, ← renameHead_renameHead c 0 E]
      exact forall₂_renameHead c (fun _ _ h => ⟨rfl, h.2⟩) hm1
    · rw [List.map_append, List.map_append, hcv2, finEnts_rename c w, ← renameHead_renameHead c 0 E]
      congr 1
      exact renameHead_cvs c hcv1
    · intro T PB hT
      have hT1 : TPre cf s T g W1 (Ui s w) (pays w) PB :=
        tpre_sub hT (fun p hp => List.mem_append_right _ hp) (fun z hz => List.mem_append_left _ hz)
          (fun p hp => List.mem_append_left _ hp) (fun z hz hn => by
            rw [List.map_append, List.mem_append, not_or]
            exact ⟨not_mem_ws hfA hW2.ids (hex1 z hz) (hdisj z hz), hn⟩)
      have hT2 : TPre cf s T g W2 (rest.flatMap (fun e => Ui s e.2))
          (rest.flatMap (fun e => pays e.2)) PB :=
        tpre_sub hT (fun p hp => List.mem_append_left _ hp) (fun z hz => List.mem_append_right _ hz)
          (fun p hp => List.mem_append_right _ hp) (fun z hz hn => by
            rw [List.map_append, List.mem_append, not_or]
            exact ⟨hn, not_mem_ws hfresh hW1.ids (hex2 z hz) (fun h => hdisj z h hz)⟩)
      obtain ⟨hh1, hr1, hwn1⟩ := ht1 T PB hT1
      obtain ⟨hh2, hr2, hwn2⟩ := ht2 T PB hT2
      refine ⟨?_, fun f hf => ?_, hwn2.append hwn1⟩
      · unfold HoldsE at hh1 hh2 ⊢
        refine List.rel_append ?_ hh2
        rw [finEnts_rename c w, ← renameHead_renameHead c 0 E]
        exact forall₂_renameHead c (fun _ _ h => ⟨rfl, h.2⟩) hh1
      · rw [List.flatMap_append, renameHead_flatMap_snd, List.flatMap_append]
        have hr : List.range' acc.next (accB.next - acc.next) =
            List.range' acc.next (accA.next - acc.next) ++ List.range' accA.next (accB.next - accA.next) := by
          have h1 := hW1.next
          have h2 := hW2.next
          have e1 : accB.next - acc.next = (accA.next - acc.next) + (accB.next - accA.next) := by nomega
          have e2 : acc.next + 1 * (accA.next - acc.next) = accA.next := by nomega
          rw [e1, ← List.range'_append, e2]
        rw [hr]
        exact sub_two (hr1 f hf) (hr2 f hf)

/-! ## The induction -/

theorem decParts_pos (hcf : cf.Ok) {g h : Nat} {b : Option NodeId} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {k : Nat}
    (he : EOk cf i s g h (.node b g h join es F (.parts k))) : 1 ≤ k := by
  cases he with
  | node hdec _ _ _ => exact (dec_parts hcf hdec.symm).1

/-- The pieces of an inner node in order: so are its written children. -/
theorem pieces_kids (hcf : cf.Ok) {g h : Nat} {b : Option NodeId} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    (he : EOk cf i s g (h + 1) (.node b g (h + 1) join es F dec))
    (hord : ∀ e ∈ finEnts 0 (.node b g (h + 1) join es F dec)
      (fin s (h + 1) (.node b g (h + 1) join es F dec)), InOrd (h + 1) e.2) :
    ∀ e ∈ kids (fin s (h + 1) (.node b g (h + 1) join es F dec)), InOrd h e.2 := by
  intro e he'
  cases dec with
  | same => exact (hord (0, fin s (h + 1) (.node b g (h + 1) join es F .same))
      (by simp [finEnts])).2 e he'
  | append => exact (hord (0, fin s (h + 1) (.node b g (h + 1) join es F .append))
      (by simp [finEnts])).2 e he'
  | parts k =>
    have hk := decParts_pos hcf he
    have hfin := finEnts_parts (b := b) (g' := g) (h' := h + 1) (join := join) (es := es) (F := F) hk
      (fin s (h + 1) (.node b g (h + 1) join es F (.parts k))) (fin_rnH (h + 1) b g (h + 1) join es F _)
    have hfl := cutList_flatten (fin s (h + 1) (.node b g (h + 1) join es F (.parts k)))
      (partSizes (fin s (h + 1) (.node b g (h + 1) join es F (.parts k))).length k join)
      (partSizes_sum (by omega) join)
    have he2 : e ∈ (cutList (fin s (h + 1) (.node b g (h + 1) join es F (.parts k)))
        (partSizes (fin s (h + 1) (.node b g (h + 1) join es F (.parts k))).length k join)).flatten := by
      rw [hfl]; exact he'
    obtain ⟨Q, hQ, heQ⟩ := List.mem_flatten.mp he2
    obtain ⟨e', he', h2⟩ := mem_snd_of_rename (c := 0) (List.mem_map_of_mem (f := fun Q => (headCv Q, rnH (h + 1) Q)) hQ)
    rw [← hfin] at he'
    have hQo : InOrd (h + 1) (rnH (h + 1) Q) := by
      have := hord e' he'
      rw [h2] at this
      exact this
    obtain ⟨x, hx, hx2⟩ := mem_snd_of_rename (c := 0) heQ
    rw [← hx2]
    exact hQo.2 x hx

/-- **emit realizes the planned node**, by induction on the height. -/
theorem emit_main (hcf : cf.Ok) (hs : SOk cf i s) {g : Nat} : ∀ (h : Nat) {v : VN} {acc : Acc}
    {E : List (Nat × NodeId)} {acc' : Acc},
    VOk cf s g h v → EOk cf i s g h v → (Ui s v).Nodup → (∀ x, acc.next ≤ x → s.obj x = none) →
    (∀ e ∈ finEnts 0 v (fin s h v), InOrd h e.2) → emit cf i s v acc = some (E, acc') →
    ESpec cf i s g h v acc E acc'
  | 0, v, acc, E, acc', hv, he, hnd, hfresh, hord, hem => by
    cases v with
    | old y =>
      rw [emit.eq_1] at hem
      simp only [Option.some.injEq, Prod.mk.injEq] at hem
      obtain ⟨rfl, rfl⟩ := hem
      exact old_spec hs hv
    | node b g' h' join es F dec =>
      obtain ⟨rfl, rfl⟩ := hv.ht
      have hv' := hv
      cases hv with
      | leaf hold hF _ =>
      rw [emit_node, emitKids_old es hold] at hem
      simp only [Option.bind_some, beq_self_eq_true, ite_true] at hem
      have hn : NH cf i s g' 0 b join es F dec [] acc :=
        ⟨hv', he, by rw [Ui_node]; simp, by rw [Ui_node] at hnd; simpa using hnd, by simp,
          hfresh, hord⟩
      exact node_dispatch hcf hs hn (leaf_cres hold hF) hem
  | h + 1, v, acc, E, acc', hv, he, hnd, hfresh, hord, hem => by
    cases v with
    | old y =>
      rw [emit.eq_1] at hem
      simp only [Option.some.injEq, Prod.mk.injEq] at hem
      obtain ⟨rfl, rfl⟩ := hem
      exact old_spec hs hv
    | node b g' h' join es F dec =>
      obtain ⟨rfl, rfl⟩ := hv.ht
      have hv' := hv
      have he' := he
      cases hv with
      | inner hk _ _ hF _ =>
      rw [emit_node] at hem
      cases hkr : emitKids cf i s es acc with
      | none => rw [hkr] at hem; cases hem
      | some r =>
      obtain ⟨F0, acc1⟩ := r
      rw [hkr] at hem
      simp only [Option.bind_some, Nat.add_one_ne_zero, beq_iff_eq, ite_false] at hem
      cases he with
      | node _ _ _ hke =>
      have hUi : Ui s (.node b g' (h + 1) join es F dec) =
          b.toList ++ es.flatMap (fun e => Ui s e.2) := by rw [Ui_node]; simp
      have hpays : pays (.node b g' (h + 1) join es F dec) = es.flatMap (fun e => pays e.2) := by
        rw [pays_node]; simp
      have hnd' : (b.toList ++ es.flatMap (fun e => Ui s e.2)).Nodup := hUi ▸ hnd
      have hordk := pieces_kids hcf he' hord
      have hordc : ∀ e ∈ es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2)), InOrd h e.2 := by
        intro e hm
        obtain ⟨e', hm', h2⟩ := mem_snd_of_rename (c := 0) hm
        exact h2 ▸ hordk e' hm'
      have hex : ∀ z ∈ es.flatMap (fun e => Ui s e.2), s.obj z ≠ none := by
        intro z hz
        obtain ⟨e, hm, hz⟩ := List.mem_flatMap.mp hz
        exact ui_exists h (hk e hm) (hke e hm (by omega)) z hz
      obtain ⟨W0, hW0, hsh0, hm0, hcv0, ht0⟩ := kids_spec hcf hs
        (fun hv he hnd hf ho hem => emit_main hcf hs h hv he hnd hf ho hem) es hk
        (fun e hm => hke e hm (by omega)) (List.nodup_append.mp hnd').2.1 hfresh hordc hkr
      have hc : CRes cf i s g' (h + 1) (.node b g' (h + 1) join es F dec)
          (es.flatMap (fun e => Ui s e.2)) acc acc1 W0 (renameHead 0 F0) F := by
        refine ⟨hW0, hsh0, ?_, renameHead_cvs 0 hcv0, ?_⟩
        · rw [hF]
          exact forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩) hm0
        · intro T PB hT
          rw [hpays] at hT
          obtain ⟨hh, hr, hwn⟩ := ht0 T PB hT
          refine ⟨forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩) hh, fun e hm => ?_, fun f hf => ?_,
            hwn⟩
          · obtain ⟨e', hm', h2⟩ := renameHead_mem hm
            obtain ⟨a, _, hrel⟩ := forall₂_exists hh e' hm'
            obtain ⟨n, hn, _⟩ := hrel.2.obj
            rw [← h2, hn]; simp
          · rw [renameHead_flatMap_snd, hpays]
            exact hr f (by rw [Cfg.lev_succ] at hf; omega)
      have hn : NH cf i s g' (h + 1) b join es F dec (es.flatMap (fun e => Ui s e.2)) acc :=
        ⟨hv', he', hUi, hnd', hex, hfresh, hord⟩
      exact node_dispatch hcf hs hn hc hem

/-! ## The order of the planned tree -/

theorem inord_sublist : ∀ {h : Nat} {Q Q' : Node h}, Q'.Sublist Q → InOrd h Q → InOrd h Q'
  | 0, _, _, hs, hq => List.Pairwise.sublist hs hq
  | _ + 1, _, _, hs, hq => ⟨List.Pairwise.sublist hs hq.1, fun e he => hq.2 e (hs.subset he)⟩

theorem renameHead_pairwise {β : Type} {l : List (Nat × β)} (h : l.Pairwise CvLtA) :
    (renameHead 0 l).Pairwise CvLtA := by
  cases l with
  | nil => exact h
  | cons a l =>
    rw [List.pairwise_cons] at h
    show ((0, a.2) :: l).Pairwise CvLtA
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, h.2⟩
    have := h.1 b hb
    simp only [CvLtA] at this ⊢
    omega

theorem inord_rnH : ∀ {h : Nat} {Q : Node h}, InOrd h Q → InOrd h (rnH h Q)
  | 0, _, hq => hq
  | h + 1, Q, hq => by
    show InOrd (h + 1) (renameHead 0 Q)
    exact ⟨renameHead_pairwise (β := Node h) hq.1, fun e he => by
      obtain ⟨e', he', h2⟩ := renameHead_mem (l := (kids Q : List (Nat × Node h))) he
      rw [← h2]; exact hq.2 e' he'⟩

theorem cutList_sublist {α : Type} : ∀ (l : List α) (sz : List Nat), ∀ Q ∈ cutList l sz, Q.Sublist l
  | _, [], _, hQ => by simp [cutList] at hQ
  | l, n :: sz, Q, hQ => by
    simp only [cutList, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact List.take_sublist _ _
    · exact (cutList_sublist (l.drop n) sz Q hQ).trans (List.drop_sublist _ _)

/-- A planned node in order: so is each piece its parent gets. -/
theorem pieces_of_inord (hcf : cf.Ok) {g h : Nat} {v : VN} (he : EOk cf i s g h v)
    (hord : InOrd h (fin s h v)) : ∀ e ∈ finEnts 0 v (fin s h v), InOrd h e.2 := by
  intro e hm
  cases v with
  | old y => simp only [finEnts, List.mem_singleton] at hm; subst hm; exact hord
  | node b g' h' join es F dec =>
    cases dec with
    | same => simp only [finEnts, List.mem_singleton] at hm; subst hm; exact hord
    | append => simp only [finEnts, List.mem_singleton] at hm; subst hm; exact hord
    | parts k =>
      have hk : 1 ≤ k := by
        cases he with
        | node hdec _ _ _ => exact (dec_parts hcf hdec.symm).1
      rw [finEnts_parts hk _ (fin_rnH h b g' h' join es F _)] at hm
      obtain ⟨e', hm', h2⟩ := renameHead_mem hm
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hm'
      rw [← h2]
      exact inord_rnH (inord_sublist (cutList_sublist _ _ Q hQ) hord)

theorem kidsWF_each {β : Type} {W : Nat → Option Nat → β → Prop} :
    ∀ {lo : Nat} {hi : Option Nat} {l : List (Nat × β)}, KidsWF W lo hi l →
      ∀ e ∈ l, ∃ lo' hi', W lo' hi' e.2
  | _, _, [], _, _, he => by simp at he
  | lo, hi, (c, x) :: rest, hk, e, he => by
    obtain ⟨h1, h2⟩ := hk
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, h1⟩
    · exact kidsWF_each h2 e he

/-- 026-24's order (`WF`, what `Root.wf` gives) is in order. -/
theorem wf_inord : ∀ {h : Nat} {lo : Nat} {hi : Option Nat} {x : Node h}, WF h lo hi x → InOrd h x
  | 0, _, _, _, hw => hw.2.1
  | _ + 1, _, _, _, hw => ⟨hw.2.1, fun e he => by
      obtain ⟨lo', hi', hw'⟩ := kidsWF_each hw.2.2.2 e he
      exact wf_inord hw'⟩

theorem wfe_inord {h : Nat} {lo : Nat} {hi : Option Nat} {x : Node h} (hw : WFE h lo hi x) :
    InOrd h x := by
  rcases hw with rfl | hw
  · cases h with
    | zero => exact List.Pairwise.nil
    | succ h => exact ⟨List.Pairwise.nil, fun e he => by cases he⟩
  · exact wf_inord hw

/-! ## The statement -/

theorem zip_renameHead {β : Type} {P : NodeId → β → Prop} (c : Nat) :
    ∀ {l : List (Nat × NodeId)} {X : List β}, (∀ p ∈ (renameHead c l).zip X, P p.1.2 p.2) →
      ∀ p ∈ l.zip X, P p.1.2 p.2
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | a :: l, x :: X, h, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h ((c, a.2), x) (by simp [renameHead])
    · exact h p (by simp [renameHead, hp])

/-- **emit realizes the planned tree, and the nodes it writes** (bergdb
030-21): `emit_spec` below, and two more facts of the writes W. Every old node
emit writes is a key node of segment g shaped as PE's trees (an appended base:
`EOk`); in T, every key node written meets the rules of one node and has a
klong (a time klong of i first: `emitHead`, `newKs`). -/
theorem emit_spec_w (hcf : cf.Ok) {i : Time} {s : Tree} {g h : Nat} {v : VN} {acc acc' : Acc}
    {E : List (Nat × NodeId)}
    (hv : VOk cf s g h v) (ho : EOk cf i s g h v)
    (hs : ∀ x n, s.obj x = some (.key n) →
      nodeOk cf.params s n = true ∧ n.ks ≠ [] ∧ ∀ t, Klong.time t ∈ n.ks → t < i)
    (hfresh : ∀ x, acc.next ≤ x → s.obj x = none)
    (hU : (Ui s v).Nodup)
    (hord : InOrd h (fin s h v))
    (he : emit cf i s v acc = some (E, acc')) :
    ∃ W, acc'.ws = W ++ acc.ws ∧ acc.next ≤ acc'.next ∧ (W.map (·.1)).Nodup ∧
      (∀ w ∈ W.map (·.1), (acc.next ≤ w ∧ w < acc'.next) ∨ w ∈ Ui s v) ∧
      (∀ p ∈ W, ∃ n, p.2 = .key n ∧ ∀ t, Klong.time t ∈ n.ks → t ≤ i) ∧
      (∀ p ∈ W, ∀ n, s.obj p.1 = some (.key n) →
        ∃ more, p.2 = .key { n with ks := n.ks ++ Klong.time i :: more }) ∧
      (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n h', o = .key n ∧ Shaped cf s g h' p.1) ∧
      ∀ (T : Tree) (PB : Nat × NodeId → List NodeId),
        (∀ p ∈ W, T.obj p.1 = some p.2) →
        (∀ z ∈ Ui s v, z ∉ W.map (·.1) → T.obj z = s.obj z) →
        (∀ z, s.obj z ≠ none → T.obj z ≠ none) →
        (∀ p ∈ pays v, T.obj p.2 ≠ none ∧
          ∀ f, cf.lev g 0 ≤ f → (reachAt T f p.2).Subperm (PB p)) →
        (renameHead 0 E).map (·.1) = (finEnts 0 v (fin s h v)).map (·.1) ∧
        (∀ p ∈ E.zip (finEnts 0 v (fin s h v)), Holds cf T g h p.1.2 p.2.2) ∧
        (E.flatMap (fun e => R T e.2)).Subperm
          (Ui s v ++ (pays v).flatMap PB ++ List.range' acc.next (acc'.next - acc.next)) ∧
        (∀ f, cf.lev g h + 1 ≤ f → (E.flatMap (fun e => reachAt T f e.2)).Subperm
          (Ui s v ++ (pays v).flatMap PB ++ List.range' acc.next (acc'.next - acc.next))) ∧
        (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) := by
  obtain ⟨W, hW, hsh, _, hcv, ht⟩ := emit_main hcf hs h hv ho hU hfresh (pieces_of_inord hcf ho hord) he
  refine ⟨W, hW.ws, hW.next, hW.nodup, hW.ids, hW.times, hW.frame, hsh, ?_⟩
  intro T PB h1 h2 h3 h4
  obtain ⟨hh, hr, hwn⟩ := ht T PB ⟨h1, h2, h3, h4⟩
  have hhz : ∀ p ∈ (renameHead 0 E).zip (finEnts 0 v (fin s h v)), Holds cf T g h p.1.2 p.2.2 :=
    fun p hp => ((List.forall₂_iff_zip.mp hh).2 hp).2
  have hhE := zip_renameHead (P := fun x (a : Nat × Node h) => Holds cf T g h x a.2) 0 hhz
  have hfuel : ∀ e ∈ E, R T e.2 = reachAt T (cf.lev g h + 1) e.2 := by
    intro e hm
    have hlen : E.length = (finEnts 0 v (fin s h v)).length := by
      rw [← renameHead_length 0 E]; exact List.Forall₂.length_eq hh
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    have hp : (E[j], (finEnts 0 v (fin s h v))[j]'(hlen ▸ hj)) ∈ E.zip (finEnts 0 v (fin s h v)) := by
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp [hj, ← hlen], by simp⟩
    obtain ⟨n, hn, hlev⟩ := (hhE _ hp).obj
    simp [R, Tree.fuel, hn, hlev]
  refine ⟨hcv, hhE, ?_, hr, hwn⟩
  rw [List.flatMap_congr hfuel]
  exact hr _ (le_refl _)

/-- **emit realizes the planned tree** (bergdb 030-21). For a virtual node v
of segment g at height h that the program made (`VOk`, `EOk`), whose old nodes
are distinct (`Ui`), whose planned tree as emit writes it is in order
(`InOrd`, from 026-24's `WF`: `wfe_inord`), in a tree s whose key nodes meet
the rules of one node, have a klong and times before i, from an `Acc` whose
next ids are no nodes of s: emit writes W, each node once, a fresh id of the
run or an old node v uses; every klong written has a time at most i; a written
old node keeps its klongs and gets klongs after a time klong of i. In a tree
T that has the writes, keeps every other old node v uses, keeps every node of
s, and whose leaves' payloads are nodes whose walks with a leaf's fuel or more
are among PB: the entries emit gives are the planned pieces (the compare
values, the first one's apart: emit gives a leaf's first part its own first
compare value, the parent puts its own), each holds its piece (`Holds`), and
the nodes reached from them (with the fuel of their level, `R`, or more) are,
as a multiset, among the old nodes v uses, the payloads' bounds and the fresh
ids of the run. -/
theorem emit_spec (hcf : cf.Ok) {i : Time} {s : Tree} {g h : Nat} {v : VN} {acc acc' : Acc}
    {E : List (Nat × NodeId)}
    (hv : VOk cf s g h v) (ho : EOk cf i s g h v)
    (hs : ∀ x n, s.obj x = some (.key n) →
      nodeOk cf.params s n = true ∧ n.ks ≠ [] ∧ ∀ t, Klong.time t ∈ n.ks → t < i)
    (hfresh : ∀ x, acc.next ≤ x → s.obj x = none)
    (hU : (Ui s v).Nodup)
    (hord : InOrd h (fin s h v))
    (he : emit cf i s v acc = some (E, acc')) :
    ∃ W, acc'.ws = W ++ acc.ws ∧ acc.next ≤ acc'.next ∧ (W.map (·.1)).Nodup ∧
      (∀ w ∈ W.map (·.1), (acc.next ≤ w ∧ w < acc'.next) ∨ w ∈ Ui s v) ∧
      (∀ p ∈ W, ∃ n, p.2 = .key n ∧ ∀ t, Klong.time t ∈ n.ks → t ≤ i) ∧
      (∀ p ∈ W, ∀ n, s.obj p.1 = some (.key n) →
        ∃ more, p.2 = .key { n with ks := n.ks ++ Klong.time i :: more }) ∧
      ∀ (T : Tree) (PB : Nat × NodeId → List NodeId),
        (∀ p ∈ W, T.obj p.1 = some p.2) →
        (∀ z ∈ Ui s v, z ∉ W.map (·.1) → T.obj z = s.obj z) →
        (∀ z, s.obj z ≠ none → T.obj z ≠ none) →
        (∀ p ∈ pays v, T.obj p.2 ≠ none ∧
          ∀ f, cf.lev g 0 ≤ f → (reachAt T f p.2).Subperm (PB p)) →
        (renameHead 0 E).map (·.1) = (finEnts 0 v (fin s h v)).map (·.1) ∧
        (∀ p ∈ E.zip (finEnts 0 v (fin s h v)), Holds cf T g h p.1.2 p.2.2) ∧
        (E.flatMap (fun e => R T e.2)).Subperm
          (Ui s v ++ (pays v).flatMap PB ++ List.range' acc.next (acc'.next - acc.next)) ∧
        ∀ f, cf.lev g h + 1 ≤ f → (E.flatMap (fun e => reachAt T f e.2)).Subperm
          (Ui s v ++ (pays v).flatMap PB ++ List.range' acc.next (acc'.next - acc.next)) := by
  obtain ⟨W, h1, h2, h3, h4, h5, h6, _, ht⟩ := emit_spec_w hcf hv ho hs hfresh hU hord he
  refine ⟨W, h1, h2, h3, h4, h5, h6, fun T PB t1 t2 t3 t4 => ?_⟩
  obtain ⟨c1, c2, c3, c4, _⟩ := ht T PB t1 t2 t3 t4
  exact ⟨c1, c2, c3, c4⟩

/-! ## The payloads' premise, for the caller -/

/-- A value as a payload: its walk is itself, with any fuel. -/
theorem payload_val {T : Tree} {y : NodeId} {v : Nat} (hy : T.obj y = some (.val v)) (f : Nat) :
    (reachAt T f y).Subperm [y] := by
  rw [reachAt_val hy f]

/-- An untouched sound node of s as a payload (an old next segment's root),
all of whose nodes reached are in T as in s: with its fuel or more, its walk
in T is its walk in s. -/
theorem payload_old {T : Tree} {y : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hag : ∀ z ∈ R s y, T.obj z = s.obj z) (f : Nat) (hf : s.fuel y ≤ f) :
    reachAt T f y = R s y := by
  have hst : reachAt s f y = R s y := by rw [reach_stable f hg hf]; rfl
  rw [reachAt_agree f y (fun z hz => hag z (hst ▸ hz)), hst]

/-- A next segment's root, at any height within H, has a lower level than a
segment leaf: `emit_spec` for segment g + 1 gives the premise for segment g's
payloads. -/
theorem lev_next (cf : Cfg) {g h' : Nat} (hg : g + 1 ≤ cf.G) (hh : h' ≤ cf.H) :
    cf.lev (g + 1) h' + 1 ≤ cf.lev g 0 := by
  simp only [Cfg.lev]
  have : cf.G - g = (cf.G - (g + 1)) + 1 := by omega
  rw [this, Nat.add_mul, Nat.one_mul]
  omega

end Contract.PE
