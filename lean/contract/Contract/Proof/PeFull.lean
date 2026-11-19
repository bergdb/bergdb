/-
bergdb 030-21, part 2: PE's histories meet `MeetsFull` (BridgeTop.lean), so
that the bridge's theorems (BridgeFull.lean: recovery, restarts, eviction,
cuts; 030-14 and 030-17: the reads after them) hold for PE.

This file: the ids a transaction writes (`pe_ids`); the top's clause TB
(`topChangeOk`) for PE's change (`pe_topLocal`, then with the model's
levels, `pe_topChange_hist`); the start (`StartB`, `topStartOk`); and the
whole statement (`pe_meetsFull`), from `pe_step` (the contract, TREE, the
top's step), `pe_bridge` (the bridge's computed clauses and N's rest),
`pe_touch_hist` (the touch) and `pe_adopt_hist` (A6', A-COPY, from `Prov`).
-/
import Contract.Proof.PeAdopt
import Contract.RecoverTheorems

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys
open SIS (Changes NewNode Struct)
open SIS.Check (BVal)

variable {cf : Cfg}

/-! ## The ids a transaction writes -/

/-- The ids a transaction of PE writes: each fresh one is from `next` on and
below the next id after it; if the top grew, the new top node's id is from
`next` on, written by none, and no node of the tree before. -/
theorem pe_ids (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hw : peTx cf i s tp next ops = some o) :
    next ≤ o.next ∧
    (∀ x ∈ o.ws.map (·.1), s.obj x = none → next ≤ x ∧ x < o.next) ∧
    (o.top = tp ∨ ∃ z n', o.top = tp ++ [(z, n')] ∧ next ≤ z ∧ z ∉ o.ws.map (·.1) ∧
      s.obj z = none) := by
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
  obtain ⟨r0, hr0, hsh0⟩ := hI.shaped
  have hrr : r0 = r := by rw [hr] at hr0; exact (Option.some.inj hr0).symm
  subst hrr
  have hobj : s.obj r0 = some (.key n) := getKey_obj hn
  have hht : htIn cf s r0 = cf.htOf n.level := by simp [htIn, hobj]
  have hpre : SegPre cf i s 0 (some r0) (dropNoops cf ops) ⟨[], next⟩ :=
    { sok := hsok
      fresh := hI.fresh
      ops := fun op hop => by
        have h1 : keyOk cf op.key = true := List.all_eq_true.mp hok op hop
        exact ⟨h1, key_ne_nil h1⟩
      root := fun r1 h => by
        cases h
        exact ⟨hsh0, hgood, hnd⟩ }
  obtain ⟨W, hWok, _, _⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  have hws : acc2.ws = W := by simpa using hWok.ws
  have hwn : next ≤ acc2.next := by simpa using hWok.next
  have hRex : ∀ z ∈ R s r0, s.obj z ≠ none := reach_exists _ hgood
  have hids : ∀ x ∈ W.map (·.1), s.obj x = none → next ≤ x ∧ x < acc2.next := by
    intro x hx hsx
    rcases hWok.ids x hx with h | h
    · simpa using h
    · exact absurd hsx (hRex x h)
  rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · refine ⟨hwn, fun x hx hsx => hids x (by simpa [hws] using hx) hsx, Or.inl rfl⟩
  · refine ⟨Nat.le_trans hwn (Nat.le_succ _), fun x hx hsx => ?_, Or.inr ⟨acc2.next, _, rfl, hwn, ?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hids x (by simpa [hws] using hx) hsx
      exact ⟨h1, Nat.lt_succ_of_lt h2⟩
    · intro hz
      have hz' : acc2.next ∈ W.map (·.1) := by simpa [hws] using hz
      by_cases hs : s.obj acc2.next = none
      · exact absurd (hids _ hz' hs).2 (Nat.lt_irrefl _)
      · exact hs (hI.fresh _ hwn)
    · exact hI.fresh _ hwn

/-! ## Small facts -/

theorem inv_at {t : Time} {s : Tree} {tp : Top} {nx : NodeId} (h : Inv cf t s tp nx) : s.at t = s := by
  apply tree_at_self
  · intro x n hx u hu
    exact Nat.le_of_lt_succ ((h.sok x n hx).2.2 u hu)
  · rw [h.roots]; exact roots_times h.top

theorem lookup_isSome_of_mem {W : List (NodeId × Obj)} {x : NodeId} (hx : x ∈ W.map (·.1)) :
    (W.lookup x).isSome = true := by
  induction W with
  | nil => simp at hx
  | cons a rest ih =>
    obtain ⟨k, b⟩ := a
    by_cases hk : x = k
    · subst hk; simp [List.lookup]
    · have hne : (x == k) = false := by simpa using hk
      simp only [List.lookup, hne]
      simp only [List.map_cons, List.mem_cons] at hx
      exact ih (hx.resolve_left hk)

theorem tree_obj_written {s : Tree} {o : Out} {x : NodeId} (hx : x ∈ o.ws.map (·.1)) :
    ((o.tree s).obj x).isSome = true := by
  have := lookup_isSome_of_mem hx
  simp only [Out.tree, applyWs]
  cases h : o.ws.lookup x with
  | none => rw [h] at this; cases this
  | some ob => simp

theorem tree_obj_not_written {s : Tree} {o : Out} {x : NodeId} (hx : x ∉ o.ws.map (·.1)) :
    (o.tree s).obj x = s.obj x := by
  simp [Out.tree, applyWs, lookup_none_of_not_mem hx]

theorem lev_le_keyMax {g h : Nat} (_hg : g ≤ cf.G) (hh : h ≤ cf.H) : cf.lev g h ≤ cf.keyMax := by
  simp only [Cfg.lev, Cfg.keyMax]
  have : (cf.G - g) * (cf.H + 1) ≤ cf.G * (cf.H + 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

/-- Every key node that a walk from a sound shaped node reaches is on a key
level. -/
theorem shaped_reach_level {T : Tree} : ∀ (f : Nat) {g h : Nat} {x : NodeId} {lo : Nat}
    {hi : Option Nat}, Shaped cf T g h x → Good T x lo hi →
    ∀ z ∈ reachAt T f x, ∀ m, T.obj z = some (.key m) → m.level ≤ cf.keyMax
  | 0, g, h, x, lo, hi, hsh, _, z, hz, m, hm => by
    simp only [reachAt, List.mem_singleton] at hz
    subst hz
    obtain ⟨n, hobj, hlev, _, hg, hh⟩ := shaped_obj hsh
    rw [hobj] at hm; cases hm
    rw [hlev]; exact lev_le_keyMax hg hh
  | f + 1, g, h, x, lo, hi, hsh, hgd, z, hz, m, hm => by
    obtain ⟨n, hobj, hlev, _, hg, hh⟩ := shaped_obj hsh
    simp only [reachAt, hobj, List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨cy, hcy, hz⟩
    · rw [hobj] at hm; cases hm
      rw [hlev]; exact lev_le_keyMax hg hh
    · cases hgd with
      | mk _ _ _ n' hobj' _ _ _ hval _ hseg hkid =>
        rw [hobj] at hobj'; cases hobj'
        cases hsh with
        | leaf hobj2 hleaf _ _ hk =>
          rw [hobj] at hobj2; cases hobj2
          cases hl : isLong cy.1 with
          | true =>
            exact shaped_reach_level f (hk cy.1 cy.2 hcy hl) (hseg hleaf cy.1 cy.2 hcy hl) z hz m hm
          | false =>
            obtain ⟨v, hv⟩ := hval hleaf cy.1 cy.2 hcy hl
            cases f with
            | zero =>
              simp only [reachAt, List.mem_singleton] at hz
              subst hz; rw [hv] at hm; cases hm
            | succ f =>
              simp only [reachAt, hv, List.mem_cons, List.not_mem_nil, or_false] at hz
              subst hz; rw [hv] at hm; cases hm
        | inner hobj2 hleaf _ _ _ _ hk =>
          rw [hobj] at hobj2; cases hobj2
          obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
          exact shaped_reach_level f (hk cy.1 cy.2 hcy) (hkid hleaf pre cy.1 cy.2 post he) z hz m hm

/-! ## PE's change: its parts -/

theorem filter_pair_self {z : NodeId} (L : List BVal) :
    ((L.map (fun v => (z, v))).filter (fun a => a.1 == z)).map (·.2) = L := by
  induction L with
  | nil => rfl
  | cons v r ih => simp [ih]

theorem filter_pair_other {z w : NodeId} (hzw : z ≠ w) (L : List BVal) :
    (L.map (fun v => (z, v))).filter (fun a => a.1 == w) = [] := by
  induction L with
  | nil => rfl
  | cons v r ih => simp [ih, hzw]

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {x : α} {y : β}, l.lookup x = some y → (x, y) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, b) :: rest, x, y, h => by
    by_cases hk : x = k
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hne : (x == k) = false := by simpa using hk
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem newTopOf_same {tp : Top} {o : Out} (h : o.top = tp) : newTopOf tp o = none := by
  simp [newTopOf, h]

theorem newTopOf_snoc {tp : Top} {o : Out} {z : NodeId} {n : TopNode} (h : o.top = tp ++ [(z, n)]) :
    newTopOf tp o = some (z, n) := by
  simp [newTopOf, h]

theorem mem_peChange_new {s : Tree} {tp : Top} {o : Out} {nn : NewNode}
    (h : nn ∈ (peChange cf s tp o).new) :
    (nn.id ∈ o.ws.map (·.1) ∧ s.obj nn.id = none ∧ nn.level = lvlOf (o.tree s) nn.id) ∨
    (∃ z n, newTopOf tp o = some (z, n) ∧ nn = ⟨z, cf.topBase + tp.length, false⟩) := by
  simp only [peChange, List.mem_append, List.mem_map, List.mem_filter, List.mem_reverse,
    Option.isNone_iff_eq_none] at h
  rcases h with ⟨x, ⟨hx, hsx⟩, rfl⟩ | h
  · exact Or.inl ⟨by simpa using hx, hsx, rfl⟩
  · right
    cases ht : newTopOf tp o with
    | none => rw [ht] at h; simp at h
    | some zn =>
      obtain ⟨z, n⟩ := zn
      rw [ht] at h
      simp only [List.mem_singleton] at h
      exact ⟨z, n, rfl, h⟩

theorem mem_peChange_adds {s : Tree} {tp : Top} {o : Out} {a : NodeId × BVal}
    (h : a ∈ (peChange cf s tp o).adds) :
    a.1 ∈ o.ws.map (·.1) ∨ (∃ z n, newTopOf tp o = some (z, n) ∧ (a.1 = 0 ∨ a.1 = z)) := by
  simp only [peChange, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_map] at h
  rcases h with ⟨x, hx, v, _, rfl⟩ | h
  · exact Or.inl (List.mem_map.mpr hx)
  · right
    cases ht : newTopOf tp o with
    | none => rw [ht] at h; simp at h
    | some zn =>
      obtain ⟨z, n⟩ := zn
      rw [ht] at h
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨v, _, rfl⟩
      · exact ⟨z, n, rfl, Or.inl rfl⟩
      · exact ⟨z, n, rfl, Or.inr rfl⟩

/-! ## The top's clause TB, without the model's levels -/

/-- What TB asks of PE's change that does not read the model's levels: the
nodes made are no root and no top node, and a node of the tree after is on
a key level; no top node made, every node made and every entry added is the
tree's; a top node z made, it is the one node made that is no node of the
tree, on the level of its ordinal, with its root and skip pointers as
entries, and the root's entry for it. -/
theorem pe_topLocal (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s) (hn1 : 1 ≤ next)
    (hkeys : (ops.map Op.key).Nodup) (hw : peTx cf i s tp next ops = some o) :
    (∀ nn ∈ (peChange cf s tp o).new, nn.id ≠ 0 ∧ tp.node nn.id = none ∧
      ((o.tree s).obj nn.id = none ∨ nn.level < cf.topBase)) ∧
    (o.top = tp → (∀ nn ∈ (peChange cf s tp o).new, ((o.tree s).obj nn.id).isSome = true) ∧
      ∀ a ∈ (peChange cf s tp o).adds, ((o.tree s).obj a.1).isSome = true) ∧
    (∀ z n, o.top = tp ++ [(z, n)] →
      (peChange cf s tp o).new.filter (fun nn => ((o.tree s).obj nn.id).isNone) =
        [⟨z, cf.topBase + tp.length, false⟩] ∧
      ((peChange cf s tp o).adds.filter (fun a => a.1 == z)).map (·.2) = topVals n ∧
      ((peChange cf s tp o).adds.filter (fun a => a.1 == 0)).map (·.2) = [BVal.top z] ∧
      ∀ a ∈ (peChange cf s tp o).adds, ((o.tree s).obj a.1).isSome = true ∨ a.1 = z ∨ a.1 = 0) := by
  obtain ⟨hnx, hfr, htop⟩ := pe_ids hcf hi hI hw
  obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf hi hI hw
  obtain ⟨hbr, _, _⟩ := pe_bridge hcf hi hI hB hkeys hw
  set T := o.tree s with hT
  have hTat : T.at i = T := inv_at hI2
  -- made nodes are reached, and so on key levels
  have hmade : ∀ nn ∈ (peChange cf s tp o).new, (T.obj nn.id).isNone = true ∨ nn.id ∈ reach T := by
    have := hbr
    simp only [bridgeOk, Bool.and_eq_true] at this
    have hm := this.1.2
    simp only [madeOk, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, hTat] at hm
    exact hm
  obtain ⟨rT, hrT, hshT⟩ := hI2.shaped
  have hgT : Good T rT 0 none := good_of_invOk hrT hI2.inv
  have hlevT : ∀ z ∈ reach T, ∀ m, T.obj z = some (.key m) → m.level ≤ cf.keyMax := by
    intro z hz m hm
    rw [reach_eq_R hrT] at hz
    exact shaped_reach_level _ hshT hgT z hz m hm
  have htopB : cf.keyMax < cf.topBase := by simp [Cfg.topBase]
  -- ids
  have hwr0 : ∀ x ∈ o.ws.map (·.1), x ≠ 0 := by
    intro x hx h0
    subst h0
    by_cases hs : s.obj 0 = none
    · have := (hfr 0 hx hs).1; omega
    · exact hs hB.zero
  have htpnode : ∀ x, next ≤ x → tp.node x = none := by
    intro x hx
    unfold Top.node
    cases hl : tp.lookup x with
    | none => rfl
    | some n =>
      exfalso
      have hm : (x, n) ∈ tp := mem_of_lookup hl
      have := hI.top.ids x n hm
      tomega
  refine ⟨fun nn hnn => ?_, fun hsame => ?_, fun z n hsnoc => ?_⟩
  · rcases mem_peChange_new hnn with ⟨hx, hsx, hlv⟩ | ⟨z, n, hz, rfl⟩
    · refine ⟨hwr0 _ hx, htpnode _ (hfr _ hx hsx).1, ?_⟩
      have hsome := tree_obj_written (s := s) hx
      rcases hmade nn hnn with h | h
      · rw [← hT] at hsome; simp_all
      · right
        rw [hlv]
        cases hob : T.obj nn.id with
        | none => rw [← hT, hob] at hsome; cases hsome
        | some ob =>
          cases ob with
          | val v => simp only [lvlOf, ← hT, hob, lvl]; omega
          | key m =>
            simp only [lvlOf, ← hT, hob, lvl]
            have := hlevT nn.id h m hob
            omega
    · rcases htop with h | ⟨z', n', h, hz1, hz2, hz3⟩
      · rw [newTopOf_same h] at hz; cases hz
      · rw [newTopOf_snoc h] at hz
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hz)
        refine ⟨by simp; omega, htpnode _ hz1, Or.inl ?_⟩
        show T.obj z' = none
        rw [hT, tree_obj_not_written hz2, hz3]
  · refine ⟨fun nn hnn => ?_, fun a ha => ?_⟩
    · rcases mem_peChange_new hnn with ⟨hx, _, _⟩ | ⟨z, n, hz, _⟩
      · exact tree_obj_written hx
      · rw [newTopOf_same hsame] at hz; cases hz
    · rcases mem_peChange_adds ha with hx | ⟨z, n, hz, _⟩
      · exact tree_obj_written hx
      · rw [newTopOf_same hsame] at hz; cases hz
  · have hnt := newTopOf_snoc hsnoc
    rcases htop with h | ⟨z', n', h, hz1, hz2, hz3⟩
    · rw [h] at hsnoc
      have := congrArg List.length hsnoc
      simp at this
    · rw [h] at hsnoc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.append_inj_right' hsnoc rfl |> List.singleton_inj.mp)
      have hz0 : z' ≠ 0 := by omega
      have hTz : T.obj z' = none := by rw [hT, tree_obj_not_written hz2, hz3]
      have hxz : ∀ x ∈ o.ws.map (·.1), x ≠ z' := fun x hx h => hz2 (h ▸ hx)
      refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
      · simp only [peChange, hnt, List.filter_append, List.filter_map]
        rw [List.filter_eq_nil_iff.mpr]
        · simp [hTz]
        · intro x hx
          simp only [List.mem_filter, List.mem_reverse, Option.isNone_iff_eq_none] at hx
          have hsm := tree_obj_written (s := s) hx.1
          simp only [Function.comp, Option.isNone_iff_eq_none]
          intro h2
          rw [← hT, h2] at hsm
          cases hsm
      · have hw0 : ∀ a ∈ (o.ws.map (·.1)).reverse.flatMap
            (fun x => (newVals s T x).map (fun v => (x, v))), (a.1 == z') = false := by
          intro a ha
          simp only [List.mem_flatMap, List.mem_reverse, List.mem_map] at ha
          obtain ⟨x, hx, v, _, rfl⟩ := ha
          simpa using hxz x (List.mem_map.mpr hx)
        simp only [peChange, hnt, List.filter_append, List.map_append]
        rw [List.filter_eq_nil_iff.mpr (fun a ha => by simp [hw0 a ha])]
        have h0z : (0 == z') = false := by simpa using hz0.symm
        simp only [List.filter_cons, h0z, List.map_nil, List.nil_append]
        exact filter_pair_self _
      · have hw0 : ∀ a ∈ (o.ws.map (·.1)).reverse.flatMap
            (fun x => (newVals s T x).map (fun v => (x, v))), (a.1 == 0) = false := by
          intro a ha
          simp only [List.mem_flatMap, List.mem_reverse, List.mem_map] at ha
          obtain ⟨x, hx, v, _, rfl⟩ := ha
          simpa using hwr0 x (List.mem_map.mpr hx)
        simp only [peChange, hnt, List.filter_append, List.map_append]
        rw [List.filter_eq_nil_iff.mpr (fun a ha => by simp [hw0 a ha])]
        simp only [List.filter_cons, beq_self_eq_true, ite_true, List.map_cons]
        rw [filter_pair_other hz0]
        rfl
      · rcases mem_peChange_adds ha with hx | ⟨z, n, hz, h0⟩
        · exact Or.inl (tree_obj_written hx)
        · rw [hnt] at hz
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hz)
          rcases h0 with h0 | h0
          · exact Or.inr (Or.inr h0)
          · exact Or.inr (Or.inl h0)

/-! ## A run's transactions, one by one -/

/-- The top before the j-th transaction (from 0) of a run from the top tp
with the list L (`peRun`). -/
def topL (tp : Top) (L : List (BTx × Top)) : Nat → Top
  | 0 => tp
  | j + 1 => ((L[j]?).map (·.2)).getD tp

theorem topL_cons (tp : Top) (x : BTx × Top) (L : List (BTx × Top)) :
    ∀ j, j ≤ L.length → topL tp (x :: L) (j + 1) = topL x.2 L j
  | 0, _ => rfl
  | j + 1, hj => by
    have hj' : j < L.length := by omega
    simp [topL, List.getElem?_eq_getElem hj']

/-- What one transaction of a run gives, for MeetsFull: the contract, TREE,
the top's step and its roots, and TB's facts of the change that do not read
the model's levels. -/
structure StepF (cf : Cfg) (i : Time) (a b : Tree) (tx : BTx) (tpa tpb : Top) : Prop where
  contract : Contract cf.params i a tx.ops tx.D b
  tree : Contract.TreeOk (b.at i)
  topStep : TopStep i tpa tpb
  roots : b.roots = rootsOf tpb
  newOk : ∀ nn ∈ tx.c.new, nn.id ≠ 0 ∧ tpa.node nn.id = none ∧ (b.obj nn.id = none ∨ nn.level < cf.topBase)
  same : tpb = tpa → (∀ nn ∈ tx.c.new, (b.obj nn.id).isSome = true) ∧
    ∀ e ∈ tx.c.adds, (b.obj e.1).isSome = true
  grow : ∀ z n, tpb = tpa ++ [(z, n)] →
    tx.c.new.filter (fun nn => (b.obj nn.id).isNone) = [⟨z, cf.topBase + tpa.length, false⟩] ∧
    (tx.c.adds.filter (fun e => e.1 == z)).map (·.2) = topVals n ∧
    (tx.c.adds.filter (fun e => e.1 == 0)).map (·.2) = [BVal.top z] ∧
    ∀ e ∈ tx.c.adds, (b.obj e.1).isSome = true ∨ e.1 = z ∨ e.1 = 0
  ids : ∀ zn ∈ tpb, zn.1 ≠ 0

/-- **Every transaction of a run of PE** gives `StepF`: from a state PE keeps at
time t, with `InvB`, a next id of at least 1 and top ids not 0, for
transactions each of distinct keys. -/
theorem pe_full_run (hcf : cf.Ok) (c0' : Changes BVal) :
    ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId) (t : Time)
      (L : List (BTx × Top)), Inv cf t s tp nx → InvB cf s → 1 ≤ nx → (∀ zn ∈ tp, zn.1 ≠ 0) →
      (∀ ops ∈ txs, (ops.map Op.key).Nodup) → peRun cf s tp nx t txs = some L →
      ∀ j (hj : j < L.length),
        StepF cf (t + j + 1) ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
          ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1 (topL tp L j) (topL tp L (j + 1))
  | [], s, tp, nx, t, L, _, _, _, _, _, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj
    simp at hj
  | ops :: rest, s, tp, nx, t, L, hI, hB, hn1, hz, hk, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o hw
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      have hI' : Inv cf (t + 1 - 1) s tp nx := by simpa using hI
      have hko : (ops.map Op.key).Nodup := hk ops List.mem_cons_self
      obtain ⟨_, _, hB'⟩ := pe_bridge hcf (Nat.succ_pos t) hI' hB hko hw
      obtain ⟨hc, htr, hts, hro, hI2⟩ := pe_step hcf (Nat.succ_pos t) hI' hw
      obtain ⟨hnx, _, htop⟩ := pe_ids hcf (Nat.succ_pos t) hI' hw
      obtain ⟨h1, h2, h3⟩ := pe_topLocal hcf (Nat.succ_pos t) hI' hB hn1 hko hw
      have hz' : ∀ zn ∈ o.top, zn.1 ≠ 0 := by
        rcases htop with h | ⟨z, n', h, hzn, _, _⟩
        · rw [h]; exact hz
        · rw [h]
          intro zn hzn'
          rcases List.mem_append.mp hzn' with hzn' | hzn'
          · exact hz zn hzn'
          · simp at hzn'; rw [hzn']; simp; tomega
      have ih := pe_full_run hcf c0' rest (o.tree s) o.top o.next (t + 1) L' (by simpa using hI2)
        hB' (by omega) hz' (fun ops' h' => hk ops' (List.mem_cons_of_mem _ h')) hrest
      intro j hj
      cases j with
      | zero =>
        exact { contract := hc, tree := htr, topStep := hts, roots := hro, newOk := h1, same := h2,
                grow := h3, ids := hz' }
      | succ j =>
        have hj' : j < L'.length := by simpa using hj
        have e1 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1)) j
          (by simp; omega)
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        have t1 := topL_cons tp (⟨ops, o.D, o.tree s, peChange cf s tp o⟩, o.top) L' j (by omega)
        have t2 := topL_cons tp (⟨ops, o.D, o.tree s, peChange cf s tp o⟩, o.top) L' (j + 1)
          (by omega)
        simp only [List.map_cons] at e1 e2 ⊢
        rw [e1, e2, t1, t2, show t + (j + 1) + 1 = t + 1 + j + 1 by omega]
        exact ih j hj'

/-! ## The model's levels -/

theorem lookup_map_level (P : Struct BVal) (i : Time) (x : NodeId) (v : BVal) (y : NodeId) :
    ((P.addEntry i x v).get? y).map (·.level) = (P.get? y).map (·.level) := by
  unfold SIS.Struct.addEntry SIS.Struct.get?
  induction P with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨k, n⟩ := a
    by_cases hk : y = k
    · subst hk
      by_cases hx : y = x
      · subst hx; simp [List.lookup]
      · simp [List.lookup, hx]
    · have hne : (y == k) = false := by simpa using hk
      by_cases hx : k = x
      · subst hx
        simp only [List.map_cons, ite_true, List.lookup, hne]
        exact ih
      · simp only [List.map_cons, hx, ite_false, List.lookup, hne]
        exact ih

theorem levelIn_eq_map (P : Struct BVal) (y : NodeId) :
    levelIn P y = ((P.get? y).map (·.level)).getD 0 := by
  unfold levelIn; cases P.get? y <;> rfl

theorem levelIn_addEntry (P : Struct BVal) (i : Time) (x : NodeId) (v : BVal) (y : NodeId) :
    levelIn (P.addEntry i x v) y = levelIn P y := by
  rw [levelIn_eq_map, levelIn_eq_map, lookup_map_level]

theorem isSome_addEntry (P : Struct BVal) (i : Time) (x : NodeId) (v : BVal) (y : NodeId) :
    ((P.addEntry i x v).get? y).isSome = (P.get? y).isSome := by
  have := lookup_map_level P i x v y
  cases h1 : (P.addEntry i x v).get? y <;> cases h2 : P.get? y <;> simp_all

theorem levelIn_foldl (adds : List (NodeId × BVal)) (i : Time) :
    ∀ (P : Struct BVal) (y : NodeId),
      levelIn (adds.foldl (fun P a => P.addEntry i a.1 a.2) P) y = levelIn P y ∧
      ((adds.foldl (fun P a => P.addEntry i a.1 a.2) P).get? y).isSome = (P.get? y).isSome := by
  induction adds with
  | nil => intro P y; exact ⟨rfl, rfl⟩
  | cons a rest ih =>
    intro P y
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (P.addEntry i a.1 a.2) y
    exact ⟨h1.trans (levelIn_addEntry _ _ _ _ _), h2.trans (isSome_addEntry _ _ _ _ _)⟩

/-- The level of node y after a change: as before if it was a node; else the
level of a node made with id y, or 0. -/
theorem levelIn_apply (P : Struct BVal) (i : Time) (c : Changes BVal) (y : NodeId) :
    ((P.get? y).isSome = true → levelIn (P.apply i c) y = levelIn P y) ∧
    ((P.get? y).isSome = false → levelIn (P.apply i c) y = 0 ∨
      ∃ nn ∈ c.new, nn.id = y ∧ levelIn (P.apply i c) y = nn.level) ∧
    ((P.get? y).isSome = true → ((P.apply i c).get? y).isSome = true) := by
  unfold SIS.Struct.apply
  simp only
  obtain ⟨hl, hs⟩ := levelIn_foldl c.adds i
    (P ++ c.new.map (fun n => (n.id, ({ level := n.level, isData := n.isData, hist := [] } : SIS.Node BVal)))) y
  rw [hl, hs]
  unfold levelIn SIS.Struct.get?
  rw [List.lookup_append]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · cases hP : P.lookup y with
    | none => rw [hP] at h; cases h
    | some n => simp
  · cases hP : P.lookup y with
    | some n => rw [hP] at h; cases h
    | none =>
      simp only [Option.none_or]
      clear hl hs hP h
      induction c.new with
      | nil => left; rfl
      | cons nn rest ih =>
        by_cases hy : y = nn.id
        · right
          refine ⟨nn, List.mem_cons_self, hy.symm, ?_⟩
          subst hy
          simp
        · have hne : (y == nn.id) = false := by simpa using hy
          simp only [List.map_cons, List.lookup, hne]
          rcases ih with h | ⟨m, hm, h1, h2⟩
          · left; exact h
          · right; exact ⟨m, List.mem_cons_of_mem _ hm, h1, h2⟩
  · cases hP : P.lookup y with
    | none => rw [hP] at h; cases h
    | some n => simp

/-! ## PE's history -/

theorem peHist_eq {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hh : peHist cf txs = some (h, top)) :
    ∃ L, peRun cf (startTree cf) startTop startNext 0 txs = some L ∧
      h = ⟨startTree cf, c0 cf, L.map (·.1)⟩ ∧ ∀ j, top j = topL startTop L j := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    refine ⟨L, rfl, rfl, fun j => ?_⟩
    cases j <;> rfl

/-- Every transaction of PE's history from the empty tree gives `StepF`. -/
theorem pe_steps (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length),
      StepF cf (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j] (top j) (top (j + 1)) := by
  obtain ⟨L, hr, rfl, htop⟩ := peHist_eq hh
  intro j hj
  have hj' : j < L.length := by simpa using hj
  obtain ⟨h0, _, _⟩ := start_inv hcf
  have := pe_full_run hcf (c0 cf) txs _ _ _ 0 L h0 (invB_start hcf) (by decide)
    (by intro zn hzn; simp [startTop] at hzn; rw [hzn]; decide) hk hr j hj'
  rw [htop, htop]
  simpa using this

/-- The model's levels along PE's history: the root on the root's level; every
other node below the level of the next top node. -/
theorem pe_levels (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j, j ≤ h.txs.length → ((h.P j).get? 0).isSome = true ∧ levelIn (h.P j) 0 = cf.rootLevel ∧
      ∀ x, x ≠ 0 → levelIn (h.P j) x < cf.topBase + (top j).length := by
  have hst := pe_steps hcf hk hh
  obtain ⟨L, _, hhL, htop⟩ := peHist_eq hh
  have hlt : cf.lev 0 0 < cf.topBase := by
    have := lev_le_keyMax (cf := cf) (g := 0) (h := 0) (Nat.zero_le _) (Nat.zero_le _)
    simp only [Cfg.topBase]; omega
  intro j
  induction j with
  | zero =>
    intro _
    rw [htop 0]
    subst hhL
    have hP0 : (⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).P 0 = SIS.Struct.apply [] 0 (c0 cf) := rfl
    rw [hP0]
    refine ⟨by simp [SIS.Struct.apply, c0, SIS.Struct.addEntry, SIS.Struct.get?],
      by simp [SIS.Struct.apply, c0, SIS.Struct.addEntry, SIS.Struct.get?, levelIn], ?_⟩
    intro x hx
    have := (levelIn_apply [] 0 (c0 cf) x).2.1 (by simp [SIS.Struct.get?, List.lookup])
    simp only [topL, startTop, List.length_singleton]
    rcases this with h0 | ⟨nn, hnn, hid, hlv⟩
    · rw [h0]; simp [Cfg.topBase]
    · rw [hlv]
      simp only [c0, List.mem_cons, List.not_mem_nil, or_false] at hnn
      rcases hnn with rfl | rfl | rfl
      · exact absurd hid.symm hx
      · simp only; omega
      · simp only; omega
  | succ j ih =>
    intro hj
    have hjl : j < h.txs.length := by omega
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    have hPs : h.P (j + 1) = (h.P j).apply (j + 1) h.txs[j].c := by
      simp [BHist.P, List.getElem?_eq_getElem hjl]
    have hS := hst j hjl
    have hlen : (top j).length ≤ (top (j + 1)).length := by
      rcases hS.topStep with h1 | ⟨z, n, h1, _⟩
      · rw [h1]
      · rw [h1]; simp
    rw [hPs]
    obtain ⟨a1, a2, a3⟩ := levelIn_apply (h.P j) (j + 1) h.txs[j].c 0
    refine ⟨a3 i1, by rw [a1 i1, i2], fun x hx => ?_⟩
    obtain ⟨b1, b2, _⟩ := levelIn_apply (h.P j) (j + 1) h.txs[j].c x
    cases hsx : ((h.P j).get? x).isSome with
    | true => rw [b1 hsx]; exact Nat.lt_of_lt_of_le (i3 x hx) (by omega)
    | false =>
      rcases b2 hsx with h0 | ⟨nn, hnn, hid, hlv⟩
      · rw [h0]; simp [Cfg.topBase]
      · rw [hlv]
        rcases (hS.newOk nn hnn).2.2 with hb | hb
        · rcases hS.topStep with h1 | ⟨z, n, h1, _⟩
          · have := (hS.same h1).1 nn hnn
            rw [hb] at this; cases this
          · have hf := (hS.grow z n h1).1
            have hm : nn ∈ h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
              simp [hnn, hb]
            rw [hf] at hm
            simp only [List.mem_singleton] at hm
            rw [hm, h1]
            simp
        · omega

/-! ## TB with the model's levels -/

theorem peRun_length (cf : Cfg) : ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId)
    (t : Time) (L : List (BTx × Top)), peRun cf s tp nx t txs = some L → L.length = txs.length
  | [], _, _, _, _, L, hr => by
    simp only [peRun, Option.some.injEq] at hr; subst hr; rfl
  | ops :: rest, s, tp, nx, t, L, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o _
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      simp [peRun_length cf rest _ _ _ _ L' hrest]

/-- The history's top nodes' level is the start top node's, if it is at most
2^62. -/
theorem peHist_topLevel_eq (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)} {h : BHist}
    {top : Nat → Top} (hh : peHist cf txs = some (h, top)) : h.topLevel = cf.topBase := by
  obtain ⟨L, _, rfl, _⟩ := peHist_eq hh
  simp [BHist.topLevel, BHist.spec, SIS.Check.bspec, BHist.p0, SIS.Check.topLevelOf,
    SIS.Struct.apply, c0, SIS.Struct.addEntry]
  omega

/-- **TB for PE's history**: every transaction's change meets the top's
clause TB with the model's levels, for histories of fewer than 2^48 - 1
transactions (the top nodes stay below the root's level) whose start top
node's level is at most 2^62. -/
theorem pe_topChange_hist (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length),
      topChangeOk h.topLevel (h.P j) (h.tree (j + 1)) (top j) (top (j + 1)) h.txs[j].c = true := by
  have hst := pe_steps hcf hk hh
  have hlv := pe_levels hcf hk hh
  rw [peHist_topLevel_eq hcap hh]
  obtain ⟨L, hr, hhL, htop⟩ := peHist_eq hh
  -- the tops' lengths
  have hlenTop : ∀ j, j ≤ h.txs.length → (top j).length ≤ j + 1 := by
    intro j
    induction j with
    | zero => intro _; rw [htop 0]; simp [topL, startTop]
    | succ j ih =>
      intro hj
      have := ih (by omega)
      rcases (hst j (by omega)).topStep with h1 | ⟨z, n, h1, _⟩ <;> rw [h1] <;> simp <;> omega
  have hlenH : h.txs.length = txs.length := by
    subst hhL
    have := peRun_length cf txs _ _ _ 0 L hr
    simpa using this
  intro j hj
  have hS := hst j hj
  obtain ⟨_, i2, i3⟩ := hlv j (by omega)
  unfold topChangeOk
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun nn hnn => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hS.newOk nn hnn
    simp only [bne_iff_ne, ne_eq, SIS.root, h2, Option.isNone_none, Bool.or_eq_true,
      Option.isNone_iff_eq_none, decide_eq_true_eq]
    exact ⟨⟨h1, trivial⟩, h3⟩
  · rcases hS.topStep with h1 | ⟨z, n, h1, _⟩
    · rw [h1]
      simp only [beq_self_eq_true, ite_true, Bool.and_eq_true, List.all_eq_true]
      exact (hS.same h1)
    · have hne : (top (j + 1) == top j) = false := by
        rw [h1]; simp
      rw [hne]
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨g1, g2, g3, g4⟩ := hS.grow z n h1
      rw [h1, List.getLast?_append, g1]
      simp only [List.getLast?_singleton, Option.some_or]
      have htl : (top j).length < 2 ^ 48 := by
        have := hlenTop j (by omega); omega
      have g3' : (List.filter (fun a => a.1 == SIS.root) h.txs[j].c.adds).map (·.2) = [BVal.top z] :=
        g3
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨beq_self_eq_true z, fun zm hzm => ?_⟩, ?_⟩, beq_iff_eq.mpr g2⟩,
        beq_iff_eq.mpr g3'⟩, fun e he => ?_⟩
      · have hz0 : zm.1 ≠ 0 := by
          cases j with
          | zero => rw [htop 0] at hzm; simp [topL, startTop] at hzm; rw [hzm]; decide
          | succ j' => exact (hst j' (by omega)).ids zm hzm
        exact i3 zm.1 hz0
      · rw [show SIS.root = 0 from rfl, i2]; simp only [Cfg.rootLevel, Cfg.topBase]; omega
      · simp only [Bool.or_eq_true, beq_iff_eq]
        rcases g4 e he with h' | h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

/-! ## The start, and the whole statement -/

/-- **The start is Java's primordial structure** (`StartB`), with its top
(`topStartOk`), if the top nodes' level is at most 2^62. -/
theorem pe_start (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hh : peHist cf txs = some (h, top)) : StartB h ∧ topStartOk h.c0 (top 0) h.s0 = true := by
  obtain ⟨L, _, rfl, htop⟩ := peHist_eq hh
  rw [htop 0]
  have hlt : cf.lev 0 0 < cf.topBase := by
    have := lev_le_keyMax (cf := cf) (g := 0) (h := 0) (Nat.zero_le _) (Nat.zero_le _)
    simp only [Cfg.topBase]; omega
  have hlz : cf.topBase < cf.rootLevel := by
    simp only [Cfg.rootLevel, Cfg.topBase]
    have : 1 ≤ 2 ^ 48 - 1 := Nat.le_sub_of_add_le (Nat.one_add_le_iff.mpr (Nat.one_lt_two_pow (by decide)))
    omega
  refine ⟨⟨1, 2, cf.lev 0 0, cf.topBase, cf.rootLevel, Nat.one_ne_zero, Nat.succ_ne_zero 1,
    by norm_num, by simp [Cfg.lev], hlt, hlz, hcap, rfl, rfl, rfl,
    fun x hx => startTree_obj_ne hx, rfl⟩, ?_⟩
  simp [topStartOk, c0, topL, startTop, startTree, rootsOf]

/-- **Every history PE writes meets `MeetsFull`, given `Prov`**: from the
empty tree, for parameters with `Cfg.Ok` whose top nodes' level is at most
2^62, for fewer than 2^48 - 1 transactions each of distinct keys, PE's
history with its record in the model's words (`peHist`) meets every clause
of `MeetsFull`, if each transaction meets `Prov` (PeAdopt.lean: an old node
that a written node names by a live klong was before a live child of it or of
an old node reached and not written). -/
theorem pe_meetsFull_of_prov (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hP : ∀ j (hj : j < h.txs.length), Prov (h.tree j) (h.tree (j + 1)) h.txs[j].D) :
    MeetsFull cf.params h top := by
  have hst := pe_steps hcf hk hh
  have hbr := pe_bridge_hist_full hcf hk hh
  have htb := pe_topChange_hist hcf hcap hlen hk hh
  have hto := pe_touch_hist hh
  obtain ⟨had, hco, _⟩ := pe_adopt_hist hcf hk hh hP
  obtain ⟨hsB, hsT⟩ := pe_start hcap hh
  refine { start := hsB, startTop := hsT, step := fun j hj => ?_, tree := fun j hj => ?_,
           adopt := fun j hj => had j hj }
  · have hS := hst j hj
    exact ⟨hS.contract, (hbr j hj).1, (hbr j hj).2, hS.topStep, hS.roots, htb j hj, hto j hj,
      hco j hj⟩
  · cases j with
    | zero =>
      obtain ⟨L, _, rfl, _⟩ := peHist_eq hh
      obtain ⟨h0, _, _⟩ := start_inv hcf
      show Contract.TreeOk ((startTree cf).at 0)
      rw [inv_at_zero h0]; exact h0.tree
    | succ j => exact (hst j (by omega)).tree

/-! ## K-LEVEL: each key node's kind from its level -/

/-- Every key node that a walk from a sound shaped node reaches has the kind
of its level. -/
theorem shaped_reach_kind {T : Tree} : ∀ (f : Nat) {g h : Nat} {x : NodeId} {lo : Nat}
    {hi : Option Nat}, Shaped cf T g h x → Good T x lo hi →
    ∀ z ∈ reachAt T f x, ∀ m, T.obj z = some (.key m) → m.leaf = peKind cf m.level
  | 0, g, h, x, lo, hi, hsh, _, z, hz, m, hm => by
    simp only [reachAt, List.mem_singleton] at hz
    subst hz
    obtain ⟨n, hobj, hlev, hleaf, _, hh⟩ := shaped_obj hsh
    rw [hobj] at hm; cases hm
    rw [hleaf, peKind, hlev, htOf_lev cf hh]
  | f + 1, g, h, x, lo, hi, hsh, hgd, z, hz, m, hm => by
    obtain ⟨n, hobj, hlev, hleaf, _, hh⟩ := shaped_obj hsh
    simp only [reachAt, hobj, List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨cy, hcy, hz⟩
    · rw [hobj] at hm; cases hm
      rw [hleaf, peKind, hlev, htOf_lev cf hh]
    · cases hgd with
      | mk _ _ _ n' hobj' _ _ _ hval _ hseg hkid =>
        rw [hobj] at hobj'; cases hobj'
        cases hsh with
        | leaf hobj2 hleaf2 _ _ hk =>
          rw [hobj] at hobj2; cases hobj2
          cases hl : isLong cy.1 with
          | true =>
            exact shaped_reach_kind f (hk cy.1 cy.2 hcy hl) (hseg hleaf2 cy.1 cy.2 hcy hl) z hz m hm
          | false =>
            obtain ⟨v, hv⟩ := hval hleaf2 cy.1 cy.2 hcy hl
            cases f with
            | zero =>
              simp only [reachAt, List.mem_singleton] at hz
              subst hz; rw [hv] at hm; cases hm
            | succ f =>
              simp only [reachAt, hv, List.mem_cons, List.not_mem_nil, or_false] at hz
              subst hz; rw [hv] at hm; cases hm
        | inner hobj2 hleaf2 _ _ _ _ hk =>
          rw [hobj] at hobj2; cases hobj2
          obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
          exact shaped_reach_kind f (hk cy.1 cy.2 hcy) (hkid hleaf2 pre cy.1 cy.2 post he) z hz m hm

/-- Every node a transaction of PE writes is reached in the tree after, for
operations of distinct keys. -/
theorem pe_written_reached (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top}
    {next : NodeId} {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next)
    (hkeys : (ops.map Op.key).Nodup) (hw : peTx cf i s tp next ops = some o) :
    ∀ x ∈ o.ws.map (·.1), x ∈ reach (o.tree s) := by
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf hi hI hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
  obtain ⟨r0, hr0, hsh0⟩ := hI.shaped
  have hrr : r0 = r := by rw [hr] at hr0; exact (Option.some.inj hr0).symm
  subst hrr
  have hobj : s.obj r0 = some (.key n) := getKey_obj hn
  have hht : htIn cf s r0 = cf.htOf n.level := by simp [htIn, hobj]
  have hok' : ∀ op ∈ dropNoops cf ops, keyOk cf op.key = true ∧ 0 < op.key.length := by
    intro op hop
    have h1 : keyOk cf op.key = true := List.all_eq_true.mp hok op hop
    exact ⟨h1, key_ne_nil h1⟩
  have hpre : SegPre cf i s 0 (some r0) (dropNoops cf ops) ⟨[], next⟩ :=
    { sok := hsok, fresh := hI.fresh, ops := hok',
      root := fun r1 h => by cases h; exact ⟨hsh0, hgood, hnd⟩ }
  have hsub : (dropNoops cf ops).Sublist ops := List.filter_sublist
  have hkd : ((dropNoops cf ops).map Op.key).Nodup := (hsub.map Op.key).nodup hkeys
  obtain ⟨W, hWok, _, _⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  obtain ⟨W', hW', hrch⟩ := seg_space_rch hcf hpre hkd (hht ▸ hp) hsr he
  have hws : acc2.ws = W := by simpa using hWok.ws
  have hWW : W' = W := by rw [← hws]; simpa using hW'.symm
  subst hWW
  have hows : o.ws = W' := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hws
  set T := o.tree s with hTdef
  have hafter : After s T W' (R s r0) := by
    have := applyWs_after (s := s) (roots := o.roots) (U := R s r0) hWok.nodup
    have hTobj : T.obj = (applyWs s W' o.roots).obj := by simp [hTdef, Out.tree, hows]
    exact ⟨fun p hp => by rw [hTobj]; exact this.ws p hp,
      fun z hz hz' => by rw [hTobj]; exact this.keep z hz hz',
      fun z hz => by rw [hTobj]; exact this.exist z hz⟩
  have hTroot : T.root = some r' := by
    rcases hout with ⟨heq, rfl⟩ | ⟨_, rfl⟩
    · show s.root = some r'
      rw [hr, heq]
    · show (s.roots ++ [(i, r')]).getLast?.map (·.2) = some r'
      simp
  obtain ⟨rT, hrT, hshT⟩ := hI2.shaped
  have hrTr : rT = r' := by rw [hTroot] at hrT; exact (Option.some.inj hrT).symm
  subst hrTr
  have hgT : Good T rT 0 none := good_of_invOk hTroot hI2.inv
  intro x hx
  rw [reach_eq_R hTroot]
  exact rch_reachAt hgT hshT (hrch T hafter x (by rw [← hows]; exact hx)) _ (le_refl _)

/-- K-LEVEL at every transaction of a run of PE. -/
theorem pe_kinds_run (hcf : cf.Ok) (c0' : Changes BVal) :
    ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId) (t : Time)
      (L : List (BTx × Top)), Inv cf t s tp nx →
      (∀ ops ∈ txs, (ops.map Op.key).Nodup) → peRun cf s tp nx t txs = some L →
      ∀ j (hj : j < L.length),
        kindsOk (peKind cf) ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.D = true
  | [], s, tp, nx, t, L, _, _, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj
    simp at hj
  | ops :: rest, s, tp, nx, t, L, hI, hk, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o hw
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      have hI' : Inv cf (t + 1 - 1) s tp nx := by simpa using hI
      have hko : (ops.map Op.key).Nodup := hk ops List.mem_cons_self
      obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf (Nat.succ_pos t) hI' hw
      have hwr := pe_written_reached hcf (Nat.succ_pos t) hI' hko hw
      have ih := pe_kinds_run hcf c0' rest (o.tree s) o.top o.next (t + 1) L' (by simpa using hI2)
        (fun ops' h' => hk ops' (List.mem_cons_of_mem _ h')) hrest
      intro j hj
      cases j with
      | zero =>
        show kindsOk (peKind cf) (o.tree s) o.D = true
        obtain ⟨rT, hrT, hshT⟩ := hI2.shaped
        have hgT : Good (o.tree s) rT 0 none := good_of_invOk hrT hI2.inv
        simp only [kindsOk, List.all_eq_true]
        intro x hx
        cases hob : (o.tree s).obj x with
        | none => rfl
        | some ob =>
          cases ob with
          | val v => rfl
          | key m =>
            have hxr := hwr x (by simpa [Out.D] using hx)
            rw [reach_eq_R hrT] at hxr
            simp [shaped_reach_kind _ hshT hgT x hxr m hob]
      | succ j =>
        have hj' : j < L'.length := by simpa using hj
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        simp only [List.map_cons] at e2 ⊢
        rw [e2]
        exact ih j hj'

/-- **K-LEVEL for PE's history**: every key node of the start, and every key
node written by a transaction, has the kind of its level (`peKind`), for
transactions of distinct keys. -/
theorem pe_kinds (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    KindsOK (peKind cf) h := by
  obtain ⟨L, hr, rfl, _⟩ := peHist_eq hh
  refine ⟨fun x n hx => ?_, fun j hj => ?_⟩
  · by_cases h1 : x = 1
    · subst h1
      rw [startTree_obj1] at hx; cases hx
      simp [peKind, Cfg.htOf, Cfg.lev]
    · rw [startTree_obj_ne h1] at hx; cases hx
  · obtain ⟨h0, _, _⟩ := start_inv hcf
    have hj' : j < L.length := by simpa using hj
    simpa using pe_kinds_run hcf (c0 cf) txs _ _ _ 0 L h0 hk hr j hj'

/-! ## For the read theorems -/

/-- **PE's history meets `MeetsFull` and K-LEVEL, given `Prov`**: what the
bridge's theorems (BridgeFull.lean) and the reads after a crash, restarts,
eviction and cuts (RecoverTheorems.lean, 030-14, 030-17) ask of a history. -/
theorem pe_full_of_prov (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hP : ∀ j (hj : j < h.txs.length), Prov (h.tree j) (h.tree (j + 1)) h.txs[j].D) :
    MeetsFull cf.params h top ∧ KindsOK (peKind cf) h :=
  ⟨pe_meetsFull_of_prov hcf hcap hlen hk hh hP, pe_kinds hcf hk hh⟩

/-- **Reads after a crash, for PE** (an instance of `crash_reads`): after a
crash that keeps the first k + 1 records of PE's history, startup gives a
structure whose reader at every time t up to k answers every get and scan
as the plain map after the first t transactions. -/
theorem pe_crash_reads_of_prov (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hP : ∀ j (hj : j < h.txs.length), Prov (h.tree j) (h.tree (j + 1)) h.txs[j].D)
    (al : SIS.Algo BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k t : Nat}
    (hkl : k ≤ h.txs.length) (htk : t ≤ k) :
    let V := SIS.view h.spec (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P t
    ReadsRight V (kindOf (peKind cf) V) (h.txs.map (·.ops)) t := by
  obtain ⟨hm, hkd⟩ := pe_full_of_prov hcf hcap hlen hk hh hP
  have hM : 1 ≤ cf.params.M := by
    show 1 ≤ cf.M
    have := hcf.h1; have := hcf.hM; omega
  exact crash_reads hm hM hkd al hst hkl htk

end Contract.PE
