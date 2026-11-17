/-
The contract package (bergdb 030-07): what the model reaches is what the tree
reaches. After every transaction of a bridged history (`BInv`), the nodes
reachable in the model's structure at the latest time are the root, the top
node of the link, and the nodes that the tree reaches from its space root
through live klongs (`reach`, bergdb 030-08): `mem_reach_model` and
`model_reach_cases`.
-/
import Mathlib.Tactic
import SIS.Proof.Reach
import Contract.Proof.BridgeInv

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

/-! ## The tree at the latest time -/

theorem prefixAt_self : ∀ {ks : List Klong} {j : Nat},
    (∀ t : Nat, Klong.time t ∈ ks → t ≤ j) → prefixAt ks j = ks
  | [], _, _ => rfl
  | k :: r, j, h => by
    have ih := prefixAt_self (ks := r) (j := j) (fun t ht => h t (List.mem_cons_of_mem _ ht))
    unfold prefixAt at ih ⊢
    cases k with
    | time t =>
      have := h t List.mem_cons_self
      simp [this, ih]
    | key c y => simp [ih]
    | del b => simp [ih]

/-- With every time up to j, the tree at time j is the tree. -/
theorem Timely.at_eq {j : Nat} {s : Tree} (h : Timely j s) : s.at j = s := by
  obtain ⟨obj, roots⟩ := s
  simp only [Tree.at, Tree.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext x
    cases ho : obj x with
    | none => rfl
    | some o =>
      cases o with
      | val v => rfl
      | key n =>
        simp only [Option.map_some, Obj.at, Option.some.injEq, Obj.key.injEq]
        rw [prefixAt_self (h.1 x n ho)]
  · rw [List.filter_eq_self]
    intro r hr
    simpa using h.2 r hr

/-! ## Live klongs are key klongs -/

theorem liveWith_mem (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases liveWith_mem del r _ a h with h1 | ⟨i', h1⟩
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
theorem live_mem_key {ks : List Klong} {c : Nat} {y : NodeId} (h : (c, y) ∈ live ks) :
    Klong.key c y ∈ ks := by
  unfold live liveWith at h
  rcases liveWith_mem (lastBitmap ks) ks.zipIdx [] (c, y) h with h1 | ⟨i, h1⟩
  · simp at h1
  · obtain ⟨hlt, heq⟩ := List.mem_zipIdx' h1
    have h2 : Klong.key c y = ks[i] := heq
    rw [h2]
    exact List.getElem_mem hlt

/-! ## The walk of the tree -/

theorem mem_reachAt_self (s : Tree) (f : Nat) (x : NodeId) : x ∈ reachAt s f x := by
  cases f <;> simp [reachAt]

/-- The walk goes on through a live klong of a key node that it reaches, when
the fuel is above the level of the node it starts from. -/
theorem reachAt_closed {s : Tree} (hl : LevOK s) : ∀ (f : Nat) (x0 : NodeId) (o0 : Obj),
    s.obj x0 = some o0 → lvl o0 < f → ∀ z n c y, z ∈ reachAt s f x0 → s.obj z = some (.key n) →
    (c, y) ∈ live n.ks → y ∈ reachAt s f x0
  | 0, _, _, _, hf, _, _, _, _, _, _, _ => by omega
  | f + 1, x0, o0, h0, hf, z, n, c, y, hz, hn, hy => by
    simp only [reachAt, List.mem_cons] at hz ⊢
    rcases hz with rfl | hz
    · right
      rw [hn]
      exact List.mem_flatMap.mpr ⟨(c, y), hy, mem_reachAt_self s f y⟩
    · right
      cases o0 with
      | val v => rw [h0] at hz; simp at hz
      | key n0 =>
        rw [h0] at hz ⊢
        simp only [List.mem_flatMap] at hz ⊢
        obtain ⟨⟨c0, w⟩, hw, hzw⟩ := hz
        obtain ⟨ow, how, hlt⟩ := hl x0 n0 h0 c0 w (live_mem_key hw)
        have hf' : lvl ow < f := by simp only [lvl] at hf; omega
        exact ⟨(c0, w), hw, reachAt_closed hl f w ow how hf' z n c y hzw hn hy⟩

/-- Every node that the walk reaches is a node of the tree. -/
theorem reachAt_obj {s : Tree} (hl : LevOK s) : ∀ (f : Nat) (x0 : NodeId),
    (s.obj x0).isSome = true → ∀ z, z ∈ reachAt s f x0 → (s.obj z).isSome = true
  | 0, x0, h0, z, hz => by
    simp only [reachAt, List.mem_singleton] at hz
    rw [hz]; exact h0
  | f + 1, x0, h0, z, hz => by
    simp only [reachAt, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h0
    · cases ho : s.obj x0 with
      | none => rw [ho] at hz; simp at hz
      | some o =>
        cases o with
        | val v => rw [ho] at hz; simp at hz
        | key n0 =>
          rw [ho] at hz
          simp only [List.mem_flatMap] at hz
          obtain ⟨⟨c0, w⟩, hw, hzw⟩ := hz
          obtain ⟨ow, how, _⟩ := hl x0 n0 ho c0 w (live_mem_key hw)
          exact reachAt_obj hl f w (by rw [how]; rfl) z hzw

/-! ## The model's structure, at a node of the tree -/

section Model

variable {h : BHist} {j : Nat}

theorem spec_live (h : BHist) : h.spec.live = blive := rfl
theorem spec_ptrs (h : BHist) : h.spec.ptrs = bptrs := rfl

/-- A key node of the tree, in the model at the latest time: its live children
are the pointees of its live klongs. -/
theorem BInv.key_live (hi : BInv h j) {x : NodeId} {n : KNode}
    (hx : (h.tree j).obj x = some (.key n)) :
    (h.P j).get? x = some { level := n.level, isData := false, hist := entriesOf n.ks } ∧
    ∀ y, y ∈ h.spec.live ((entriesOf n.ks).upTo j) ↔ ∃ c, (c, y) ∈ live n.ks := by
  refine ⟨hi.rep x _ hx, ?_⟩
  intro y
  have hup : (entriesOf n.ks).upTo j = entriesOf n.ks := by
    apply SIS.upTo_of_forall
    intro e he
    rcases entriesFrom_time_mem n.ks [] 0 [] e he with h1 | h1
    · omega
    · exact hi.timely.1 x n hx e.time h1
  rw [hup, spec_live]
  exact mem_blive_entriesOf n.ks (hi.wf x n hx).1 (hi.wf x n hx).2 y

/-- A node of the tree is a node of the model with the tree's level. -/
theorem BInv.node_of (hi : BInv h j) {x : NodeId} {o : Obj} (hx : (h.tree j).obj x = some o) :
    ∃ N, (h.P j).get? x = some N ∧ N.level = lvl o := by
  have := hi.rep x o hx
  cases o with
  | key n => exact ⟨_, this, rfl⟩
  | val v =>
    obtain ⟨t, _, ht⟩ := this
    exact ⟨_, ht, rfl⟩

/-- A value of the tree has no live child in the model. -/
theorem BInv.val_live (hi : BInv h j) {x : NodeId} {v : Nat}
    (hx : (h.tree j).obj x = some (.val v)) {N : Node BVal} (hN : (h.P j).get? x = some N)
    (t : Nat) (y : NodeId) : y ∉ h.spec.live (N.hist.upTo t) := by
  obtain ⟨t0, _, ht0⟩ := hi.rep x _ hx
  rw [hN] at ht0
  injection ht0 with ht0
  subst ht0
  intro hy
  rw [spec_live] at hy
  obtain ⟨e, he, hp⟩ := SIS.Check.blive_sub _ y hy
  have he' := (SIS.mem_upTo.mp he).1
  simp only [List.mem_singleton] at he'
  subst he'
  simp [bptrs] at hp

/-- The model reaches what the walk of the tree reaches from a node that the
model reaches. -/
theorem BInv.reach_walk (hi : BInv h j) : ∀ (f : Nat) (x : NodeId),
    Reach h.spec (h.P j) j x → ∀ z, z ∈ reachAt (h.tree j) f x → Reach h.spec (h.P j) j z
  | 0, x, hx, z, hz => by
    simp only [reachAt, List.mem_singleton] at hz
    rw [hz]; exact hx
  | f + 1, x, hx, z, hz => by
    simp only [reachAt, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · cases ho : (h.tree j).obj x with
      | none => rw [ho] at hz; simp at hz
      | some o =>
        cases o with
        | val v => rw [ho] at hz; simp at hz
        | key n =>
          rw [ho] at hz
          simp only [List.mem_flatMap] at hz
          obtain ⟨⟨c, y⟩, hy, hzy⟩ := hz
          obtain ⟨hP, hlive⟩ := hi.key_live ho
          obtain ⟨oy, hoy, hlt⟩ := hi.lev x n ho c y (live_mem_key hy)
          obtain ⟨M, hM, hMl⟩ := hi.node_of hoy
          have hry : Reach h.spec (h.P j) j y :=
            Reach.child hx hP ((hlive y).mpr ⟨c, hy⟩) hM (by rw [hMl]; exact hlt)
          exact hi.reach_walk f y hry z hzy

/-- The model reaches every node that the tree reaches. -/
theorem BInv.mem_reach_model (hi : BInv h j) {x : NodeId} (hx : x ∈ reach (h.tree j)) :
    SIS.reachable h.spec (h.P j) j x = true := by
  rw [SIS.reachable_iff]
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, _, _⟩ := hi.link
  have hr0 : Reach h.spec (h.P j) j SIS.root := Reach.root n0 h0
  have hrz : Reach h.spec (h.P j) j z :=
    Reach.child hr0 h0 (by rw [hl0]; exact List.mem_singleton_self z) hz hlz
  obtain ⟨M, hM, hMl⟩ := hi.node_of hy
  have hry : Reach h.spec (h.P j) j y :=
    Reach.child hrz hz (by rw [hly]; exact List.mem_singleton_self y) hM (by rw [hMl]; exact hny)
  unfold reach at hx
  rw [hroot] at hx
  exact hi.reach_walk _ y hry x hx

/-- What the model reaches, with the link's nodes named: the root, the top
node z, or a node that the tree reaches. -/
theorem BInv.reach3 (hi : BInv h j) {n0 nz : Node BVal} {z y : NodeId} {n : KNode}
    (h0 : (h.P j).get? SIS.root = some n0) (hl0 : h.spec.live (n0.hist.upTo j) = [z])
    (hz : (h.P j).get? z = some nz) (hly : h.spec.live (nz.hist.upTo j) = [y])
    (hroot : (h.tree j).root = some y) (hy : (h.tree j).obj y = some (.key n)) {x : NodeId}
    (hx : Reach h.spec (h.P j) j x) : x = SIS.root ∨ x = z ∨ x ∈ reach (h.tree j) := by
  induction hx with
  | root _ _ => exact Or.inl rfl
  | @child x y' N M hrx hN hy' hM hlt ih =>
    rcases ih with rfl | rfl | hin
    · rw [h0] at hN
      injection hN with hN
      subst hN
      rw [hl0] at hy'
      exact Or.inr (Or.inl (List.mem_singleton.mp hy'))
    · rw [hz] at hN
      injection hN with hN
      subst hN
      rw [hly] at hy'
      right; right
      rw [List.mem_singleton.mp hy']
      unfold reach
      rw [hroot]
      exact mem_reachAt_self _ _ _
    · right; right
      have hfuel : lvl (.key n) < (h.tree j).fuel y := by
        simp [Tree.fuel, hy, lvl]
      have hin' := hin
      unfold reach at hin' ⊢
      rw [hroot] at hin' ⊢
      have hsome := reachAt_obj hi.lev _ y (by rw [hy]; rfl) x hin'
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
      cases o with
      | val v => exact absurd hy' (hi.val_live ho hN j y')
      | key nx =>
        obtain ⟨hP, hlive⟩ := hi.key_live ho
        rw [hP] at hN
        injection hN with hN
        subst hN
        obtain ⟨c, hc⟩ := (hlive y').mp hy'
        exact reachAt_closed hi.lev _ y _ hy hfuel x nx c y' hin' ho hc

/-- What the model reaches: the root, a node that is no node of the tree (the
top node of the link), or a node that the tree reaches. -/
theorem BInv.model_reach_cases (hi : BInv h j) {x : NodeId}
    (hx : SIS.reachable h.spec (h.P j) j x = true) :
    x = SIS.root ∨ (h.tree j).obj x = none ∨ x ∈ reach (h.tree j) := by
  rw [SIS.reachable_iff] at hx
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  rcases hi.reach3 h0 hl0 hz hly hroot hy hx with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl (by rw [h1]; exact hsz))
  · exact Or.inr (Or.inr h1)

/-- Every node that the tree reaches is a node of the tree. -/
theorem BInv.reach_obj (hi : BInv h j) {x : NodeId} (hx : x ∈ reach (h.tree j)) :
    ((h.tree j).obj x).isSome = true := by
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  unfold reach at hx
  rw [hroot] at hx
  exact reachAt_obj hi.lev _ y (by rw [hy]; rfl) x hx

end Model

end Contract
