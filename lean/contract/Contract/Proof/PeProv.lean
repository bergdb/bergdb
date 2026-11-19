/-
bergdb 030-21, part 2: PE's provenance (`Prov`, PeAdopt.lean) proved for its
transaction (`pe_prov`) and its history (`pe_prov_hist`), so A6' and A-COPY
hold for PE with no premise of provenance (`pe_adopt_copy`,
`pe_adopt_hist_full`; PeFullProved.lean: `pe_full`, `pe_crash_reads`).

* Emit (`emit_prov`): the old nodes emit writes are bases of planned nodes
  decided `append`; every key klong a node written gets names a fresh id of
  the run or a kept child (`kidIds`: an untouched node, a base decided `same`
  or `append`) of a planned node that is the node's own (its base) or cut
  into parts; the entries emit gives are fresh or the node's kept id.
* Rebalance (`rebalance_step`, from `joinAt_step_zero`, `joinAt_step_succ`,
  `joinLoop_step`): with `KidsProv` (every old kept child of a planned node
  is a live child before of the node's base, of a consumed node in C, or
  meets Rp), the nodes opened by joins join C, and no node of C is an old
  node the children use (`Ui`); no kept child and no old node used is new.
* Plan (`plan_prov`, `planKids_prov`): the plan of x keeps `KidsProv` with C
  among the nodes reached from x and none in its `Ui`, given that
  `applyGroups`'s old entries are live children before of the leaf or have a
  parent below segment g (`AGProv`, `ag_prov`, from the runs' provenance).
* The root settled (`settle_prov`): collapsed roots join C; the new root's
  kept id is the planned root's, a live child before of a node of C, or meets
  Rp.
* The runs (`RunProv`, `d_ag'`, `f_old'`, `f_new'`): a run's writes and
  result, with the next segment's tree by the induction over the fuel
  (`fp_all`); each run's writes are the only ones on its old part
  (`runs_prov`, from PeSeg's `e_runs_W`).
* A segment's step (`seg_prov_some`, `seg_prov_none`): a key klong of a node
  emit writes names a fresh id or a kept child y of a planned node u; y is a
  live child before of u's base (u's own node, or a base cut into parts, not
  decided `append` elsewhere: the bases are distinct in `Ui`), of a consumed
  node (in no `Ui`, so not written by emit), or of a node below segment g
  (a payload a run gave: `e_run_res`, `e_out_res`; the run does not write it,
  `RunProv`, and no other run touches it). Levels separate emit's writes (of
  segment g) from the runs' (below it); an old leaf entry's parent is a leaf
  of segment g (`content_parent`, TREE before: `ro_one_parent`).
* The transaction (`pe_prov`): `Prov` from the writes' forms (`WForm`): a live
  child after of a node written was a live child before of it, or is named by
  a klong it got (`newKlongs`).
-/
import Contract.Proof.PeAdopt

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys
open SIS (Changes NewNode)
open SIS.Check (BVal)

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Planned nodes and their kept children -/

/-- The id a parent's entry for a child keeps: an untouched node's, or a
base kept (decided `same` or `append`); none for a node cut into parts or a
new one. -/
def kidId : VN → Option NodeId
  | .old y => some y
  | .node (some b) _ _ _ _ _ dec =>
    match dec with
    | .parts _ => none
    | _ => some b
  | .node none _ _ _ _ _ _ => none

/-- The kept ids of a list of entries. -/
def kidIds (es : List (Nat × VN)) : List NodeId := es.filterMap (fun e => kidId e.2)

/-- A decision to cut into parts. -/
def isParts : Dec → Bool
  | .parts _ => true
  | _ => false

mutual

/-- The planned nodes of a virtual node: base, decision, entries. -/
def nodesOf : VN → List (Option NodeId × Dec × List (Nat × VN))
  | .old _ => []
  | .node b _ _ _ es _ dec => (b, dec, es) :: nodesL es

/-- `nodesOf` of a list of entries. -/
def nodesL : List (Nat × VN) → List (Option NodeId × Dec × List (Nat × VN))
  | [] => []
  | (_, v) :: r => nodesOf v ++ nodesL r

end

/-- The klongs a node written got: all of a new node's, those after the old
klongs of an old one. -/
def newKlongs (s : Tree) (p : NodeId × Obj) : List Klong :=
  match p.2, s.obj p.1 with
  | .key m, some (.key n) => m.ks.drop n.ks.length
  | .key m, _ => m.ks
  | .val _, _ => []

/-- A key klong of the node p written names a fresh id of the run, or a kept
child of a planned node among N that is p's base or cut into parts. -/
def NamesOk (N : List (Option NodeId × Dec × List (Nat × VN))) (a a' : Nat) (p : NodeId)
    (y : NodeId) : Prop :=
  (a ≤ y ∧ y < a') ∨ ∃ u ∈ N, y ∈ kidIds u.2.2 ∧ (u.1 = some p ∨ isParts u.2.1 = true)

/-- What emit of a planned node (N its planned nodes) did, from acc to acc',
giving E: its writes W; an old node written is a base decided `append`; a
key klong written names as `NamesOk`; an entry given is fresh, or the kept
id K. -/
def EProv (s : Tree) (N : List (Option NodeId × Dec × List (Nat × VN))) (K : NodeId → Prop)
    (acc : Acc) (E : List (Nat × NodeId)) (acc' : Acc) : Prop :=
  ∃ W, acc'.ws = W ++ acc.ws ∧ acc.next ≤ acc'.next ∧
    (∀ p ∈ W, (acc.next ≤ p.1 ∧ p.1 < acc'.next) ∨ ∃ u ∈ N, u.1 = some p.1 ∧ u.2.1 = .append) ∧
    (∀ p ∈ W, ∀ c y, Klong.key c y ∈ newKlongs s p → NamesOk N acc.next acc'.next p.1 y) ∧
    (∀ e ∈ E, (acc.next ≤ e.2 ∧ e.2 < acc'.next) ∨ K e.2)

theorem NamesOk.mono {N N' : List (Option NodeId × Dec × List (Nat × VN))} {a a' b b' p y : Nat}
    (h : NamesOk N a a' p y) (hN : ∀ u ∈ N, u ∈ N') (hb : b ≤ a) (hb' : a' ≤ b') :
    NamesOk N' b b' p y := by
  rcases h with ⟨h1, h2⟩ | ⟨u, hu, h1, h2⟩
  · exact Or.inl ⟨by tomega, by tomega⟩
  · exact Or.inr ⟨u, hN u hu, h1, h2⟩

theorem mem_kidIds {es : List (Nat × VN)} {e : Nat × VN} {y : NodeId} (he : e ∈ es)
    (hk : kidId e.2 = some y) : y ∈ kidIds es :=
  List.mem_filterMap.mpr ⟨e, he, hk⟩

/-- The klongs of a new node: all its klongs. -/
theorem newKlongs_fresh {p : NodeId × Obj} {l : Nat} {b : Bool} {ks : List Klong}
    (hs : s.obj p.1 = none) (hp : p.2 = .key ⟨l, b, ks⟩) : newKlongs s p = ks := by
  unfold newKlongs
  rw [hp, hs]

/-- The klongs an old node got: those appended. -/
theorem newKlongs_old {p : NodeId × Obj} {n : KNode} {more : List Klong}
    (hs : s.obj p.1 = some (.key n)) (hp : p.2 = .key { n with ks := n.ks ++ more }) :
    newKlongs s p = more := by
  unfold newKlongs
  rw [hp, hs]
  simp

theorem mem_rnH_snd {α : Type} {h : Nat} {l : List (Nat × α)} {e : Nat × α} (he : e ∈ rnH h l) :
    e.2 ∈ l.map (·.2) := by
  unfold rnH at he
  split at he
  · exact List.mem_map_of_mem he
  · exact mem_renameHead_snd he

theorem mem_cutList {α : Type} : ∀ {l : List α} {sz : List Nat} {P : List α} {x : α},
    P ∈ cutList l sz → x ∈ P → x ∈ l
  | _, [], _, _, hP, _ => by simp [cutList] at hP
  | l, n :: sz, P, x, hP, hx => by
    simp only [cutList, List.mem_cons] at hP
    rcases hP with rfl | hP
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (mem_cutList hP hx)

mutual

/-- **Emit's provenance**, for a planned node. -/
theorem emit_prov :
    ∀ (v : VN) {acc : Acc} {E : List (Nat × NodeId)} {acc' : Acc},
    (∀ x, acc.next ≤ x → s.obj x = none) → emit cf i s v acc = some (E, acc') →
    EProv s (nodesOf v) (fun y => kidId v = some y) acc E acc'
  | .old y, acc, E, acc', _, hem => by
    rw [emit.eq_1] at hem
    simp only [Option.some.injEq, Prod.mk.injEq] at hem
    obtain ⟨rfl, rfl⟩ := hem
    refine ⟨[], by simp, le_refl _, by simp, by simp, ?_⟩
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact Or.inr rfl
  | .node b g h join es F dec, acc, E, acc', hf, hem => by
    rw [emit_node] at hem
    cases hkr : emitKids cf i s es acc with
    | none => rw [hkr] at hem; cases hem
    | some r =>
    obtain ⟨F0, acc1⟩ := r
    rw [hkr] at hem
    simp only [Option.bind_some] at hem
    obtain ⟨W0, hW0, hn0, hw0, hk0, he0⟩ := emitKids_prov es hf hkr
    have hN : ∀ u ∈ nodesL es, u ∈ nodesOf (.node b g h join es F dec) := by
      intro u hu
      simp only [nodesOf, List.mem_cons]
      exact Or.inr hu
    have hself : (b, dec, es) ∈ nodesOf (.node b g h join es F dec) := by
      simp [nodesOf]
    -- the final list's ids: fresh or kept children
    have hF : ∀ e ∈ (if h == 0 then F0 else renameHead 0 F0),
        (acc.next ≤ e.2 ∧ e.2 < acc1.next) ∨ e.2 ∈ kidIds es := by
      intro e he
      have h2 : e.2 ∈ F0.map (·.2) := mem_rnH_snd (h := h) he
      obtain ⟨e', he', h3⟩ := List.mem_map.mp h2
      rw [← h3]
      exact he0 e' he'
    unfold emitAfter at hem
    split at hem
    · -- same
      simp only [Option.some.injEq, Prod.mk.injEq] at hem
      obtain ⟨rfl, rfl⟩ := hem
      refine ⟨W0, hW0, hn0, fun p hp => (hw0 p hp).imp_right (fun ⟨u, hu, h1⟩ => ⟨u, hN u hu, h1⟩),
        fun p hp c y hk => (hk0 p hp c y hk).mono hN (le_refl _) (le_refl _), ?_⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact Or.inr rfl
    · -- append
      rename_i bb
      split at hem
      · rename_i n hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hem
        obtain ⟨rfl, rfl⟩ := hem
        refine ⟨(bb, .key { n with ks := n.ks ++ emitKs i n.ks (if h == 0 then F0 else renameHead 0 F0) })
          :: W0, by simp [Acc.write, hW0], hn0, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr ⟨_, hself, rfl, rfl⟩
          · exact (hw0 p hp).imp_right (fun ⟨u, hu, h1⟩ => ⟨u, hN u hu, h1⟩)
        · intro p hp c y hk
          rcases List.mem_cons.mp hp with rfl | hp
          · rw [newKlongs_old (getKey_obj hn) rfl] at hk
            have hcy := emitKs_ptrs hk
            rcases hF _ hcy with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨_, hself, h1, Or.inl rfl⟩
          · exact (hk0 p hp c y hk).mono hN (le_refl _) (le_refl _)
        · intro e he
          simp only [List.mem_singleton] at he
          subst he
          exact Or.inr rfl
      · cases hem
    · -- parts
      rename_i k
      obtain ⟨h1, h2, h3⟩ := newParts_eq (cf := cf) (i := i) (g := g) (h := h)
        (cutList (if h == 0 then F0 else renameHead 0 F0)
          (partSizes (if h == 0 then F0 else renameHead 0 F0).length k join)) acc1
      rw [Option.some.injEq] at hem
      have hE := congrArg Prod.fst hem
      have hA := congrArg Prod.snd hem
      simp only at hE hA
      subst hE hA
      set Ps := cutList (if h == 0 then F0 else renameHead 0 F0)
          (partSizes (if h == 0 then F0 else renameHead 0 F0).length k join) with hPs
      have hnext : acc1.next ≤ (newParts cf i g h Ps acc1).2.next := by rw [h3]; tomega
      refine ⟨(npW cf i g h acc1.next Ps).reverse ++ W0, by rw [h2, hW0, List.append_assoc],
        le_trans hn0 hnext, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨ha, _⟩ := mem_npW (List.mem_reverse.mp hp)
          left
          have : p.1 ∈ (npW cf i g h acc1.next Ps).map (·.1) :=
            List.mem_map_of_mem (List.mem_reverse.mp hp)
          rw [npW_ids, List.mem_range'_1] at this
          rw [h3]
          tomega
        · rcases hw0 p hp with h4 | ⟨u, hu, h4⟩
          · left; tomega
          · exact Or.inr ⟨u, hN u hu, h4⟩
      · intro p hp c y hk
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨ha, P, hP, hob⟩ := mem_npW (List.mem_reverse.mp hp)
          have hsp : s.obj p.1 = none := hf p.1 (by tomega)
          rw [newKlongs_fresh hsp hob] at hk
          simp only [newKs, keysOf, List.mem_cons, List.mem_map] at hk
          rcases hk with hk | ⟨e, he, hk⟩
          · cases hk
          · injection hk with hk1 hk2
            subst hk1 hk2
            have he1 : e.2 ∈ P.map (·.2) := mem_rnH_snd (h := h) he
            obtain ⟨e', he', h5⟩ := List.mem_map.mp he1
            rw [← h5]
            rcases hF e' (mem_cutList hP he') with h6 | h6
            · left; tomega
            · exact Or.inr ⟨_, hself, h6, Or.inr rfl⟩
        · exact (hk0 p hp c y hk).mono hN (le_refl _) (by tomega)
      · intro e he
        rw [h1] at he
        have : e.2 ∈ (npE acc1.next Ps).map (·.2) := List.mem_map_of_mem he
        rw [npE_ids, List.mem_range'_1] at this
        left
        rw [h3]
        tomega
    · cases hem

/-- **Emit's provenance**, for a list of entries. -/
theorem emitKids_prov :
    ∀ (es : List (Nat × VN)) {acc : Acc} {F : List (Nat × NodeId)} {acc' : Acc},
    (∀ x, acc.next ≤ x → s.obj x = none) → emitKids cf i s es acc = some (F, acc') →
    EProv s (nodesL es) (fun y => y ∈ kidIds es) acc F acc'
  | [], acc, F, acc', _, hem => by
    rw [emitKids.eq_1] at hem
    simp only [Option.some.injEq, Prod.mk.injEq] at hem
    obtain ⟨rfl, rfl⟩ := hem
    exact ⟨[], by simp, le_refl _, by simp, by simp, by simp⟩
  | (c, v) :: rest, acc, F, acc', hf, hem => by
    rw [emitKids.eq_2] at hem
    cases h1 : emit cf i s v acc with
    | none => rw [h1] at hem; cases hem
    | some r =>
    obtain ⟨E1, acc1⟩ := r
    rw [h1] at hem
    simp only at hem
    cases h2 : emitKids cf i s rest acc1 with
    | none => rw [h2] at hem; cases hem
    | some r2 =>
    obtain ⟨F2, acc2⟩ := r2
    rw [h2] at hem
    simp only [Option.some.injEq, Prod.mk.injEq] at hem
    obtain ⟨rfl, rfl⟩ := hem
    obtain ⟨W1, hW1, hn1, hw1, hk1, he1⟩ := emit_prov v hf h1
    have hf1 : ∀ x, acc1.next ≤ x → s.obj x = none := fun x hx => hf x (by tomega)
    obtain ⟨W2, hW2, hn2, hw2, hk2, he2⟩ := emitKids_prov rest hf1 h2
    have hN1 : ∀ u ∈ nodesOf v, u ∈ nodesL ((c, v) :: rest) := by
      intro u hu; simp only [nodesL, List.mem_append]; exact Or.inl hu
    have hN2 : ∀ u ∈ nodesL rest, u ∈ nodesL ((c, v) :: rest) := by
      intro u hu; simp only [nodesL, List.mem_append]; exact Or.inr hu
    refine ⟨W2 ++ W1, by rw [hW2, hW1, List.append_assoc], by tomega, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases hw2 p hp with h3 | ⟨u, hu, h3⟩
        · left; tomega
        · exact Or.inr ⟨u, hN2 u hu, h3⟩
      · rcases hw1 p hp with h3 | ⟨u, hu, h3⟩
        · left; tomega
        · exact Or.inr ⟨u, hN1 u hu, h3⟩
    · intro p hp c' y hk
      rcases List.mem_append.mp hp with hp | hp
      · exact (hk2 p hp c' y hk).mono hN2 (by tomega) (le_refl _)
      · exact (hk1 p hp c' y hk).mono hN1 (le_refl _) (by tomega)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨e', he', h3⟩ := renameHead_mem he
        rw [← h3]
        rcases he1 e' he' with h4 | h4
        · left; tomega
        · right
          exact mem_kidIds (List.mem_cons_self) h4
      · rcases he2 e he with h4 | h4
        · left; tomega
        · right
          exact List.mem_filterMap.mpr (by
            obtain ⟨e', he', h5⟩ := List.mem_filterMap.mp h4
            exact ⟨e', List.mem_cons_of_mem _ he', h5⟩)

end

/-! ## The plan's provenance: rebalance -/

/-- The kept children of the planned nodes N: every old one is a live child
before of its node's base, of a node of C (consumed by the plan), or meets
R (a next segment's run gave it). -/
def KidsProv (s : Tree) (C : List NodeId) (R : NodeId → Prop)
    (N : List (Option NodeId × Dec × List (Nat × VN))) : Prop :=
  ∀ u ∈ N, ∀ y ∈ kidIds u.2.2, s.obj y ≠ none →
    (∃ x, u.1 = some x ∧ kidOf s x y = true) ∨ (∃ q ∈ C, kidOf s q y = true) ∨ R y

theorem KidsProv.mono {C C' : List NodeId} {R : NodeId → Prop}
    {N N' : List (Option NodeId × Dec × List (Nat × VN))} (h : KidsProv s C R N)
    (hC : ∀ q ∈ C, q ∈ C') (hN : ∀ u ∈ N', u ∈ N) : KidsProv s C' R N' := by
  intro u hu y hy hs
  rcases h u (hN u hu) y hy hs with h1 | ⟨q, hq, h1⟩ | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨q, hC q hq, h1⟩)
  · exact Or.inr (Or.inr h1)

theorem nodesL_eq : ∀ (es : List (Nat × VN)), nodesL es = es.flatMap (fun e => nodesOf e.2)
  | [] => rfl
  | (c, v) :: r => by simp [nodesL, nodesL_eq r]

theorem nodesL_append (A B : List (Nat × VN)) : nodesL (A ++ B) = nodesL A ++ nodesL B := by
  simp [nodesL_eq]

theorem nodesL_renameHead (c : Nat) (es : List (Nat × VN)) : nodesL (renameHead c es) = nodesL es := by
  cases es with
  | nil => rfl
  | cons e r => obtain ⟨a, w⟩ := e; rfl

theorem kidIds_append (A B : List (Nat × VN)) : kidIds (A ++ B) = kidIds A ++ kidIds B := by
  simp [kidIds]

theorem kidIds_cons (e : Nat × VN) (es : List (Nat × VN)) :
    kidIds (e :: es) = (kidId e.2).toList ++ kidIds es := by
  simp only [kidIds, List.filterMap_cons]
  cases kidId e.2 <;> simp

theorem kidIds_renameHead (c : Nat) (es : List (Nat × VN)) : kidIds (renameHead c es) = kidIds es := by
  cases es with
  | nil => rfl
  | cons e r => obtain ⟨a, w⟩ := e; rfl

theorem mem_nodesL {es : List (Nat × VN)} {e : Nat × VN} (he : e ∈ es)
    {u : Option NodeId × Dec × List (Nat × VN)} (hu : u ∈ nodesOf e.2) : u ∈ nodesL es := by
  rw [nodesL_eq]
  exact List.mem_flatMap.mpr ⟨e, he, hu⟩

/-- What the children of a planned node keep for the provenance: their old
nodes used distinct, their kept children's provenance, and C none of their
old nodes. -/
def RB (s : Tree) (C : List NodeId) (R : NodeId → Prop) (es : List (Nat × VN)) : Prop :=
  (UiL s es).Nodup ∧ KidsProv s C R (nodesL es) ∧ ∀ q ∈ C, q ∉ UiL s es

/-- A step of rebalance from es to es': C grows by old nodes es used, to one
that es' keeps; no kept child is new, no old node used is new. -/
def Step (s : Tree) (C : List NodeId) (R : NodeId → Prop) (es es' : List (Nat × VN)) : Prop :=
  ∃ C', (∀ q ∈ C, q ∈ C') ∧ (∀ q ∈ C', q ∈ C ∨ q ∈ UiL s es) ∧ RB s C' R es' ∧
    (∀ y ∈ kidIds es', y ∈ kidIds es) ∧ (∀ z ∈ UiL s es', z ∈ UiL s es)

theorem Step.refl {C : List NodeId} {R : NodeId → Prop} {es : List (Nat × VN)} (h : RB s C R es) :
    Step s C R es es :=
  ⟨C, fun _ h => h, fun _ h => Or.inl h, h, fun _ h => h, fun _ h => h⟩

theorem Step.trans {C : List NodeId} {R : NodeId → Prop} {es es1 es2 : List (Nat × VN)}
    (h1 : Step s C R es es1) (h2 : ∀ C1, RB s C1 R es1 → Step s C1 R es1 es2) :
    Step s C R es es2 := by
  obtain ⟨C1, a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨C2, b1, b2, b3, b4, b5⟩ := h2 C1 a3
  refine ⟨C2, fun q hq => b1 q (a1 q hq), fun q hq => ?_, b3, fun y hy => a4 y (b4 y hy),
    fun z hz => a5 z (b5 z hz)⟩
  rcases b2 q hq with h | h
  · exact a2 q h
  · exact Or.inr (a5 q h)

/-- The id that a child opened for a join gives up. -/
def openId : VN → Option NodeId
  | .old y => some y
  | .node b _ _ _ _ _ _ => b

theorem openId_mem_Ui {w : VN} {q : NodeId} (h : openId w = some q) : q ∈ Ui s w := by
  cases w with
  | old y =>
    simp only [openId, Option.some.injEq] at h
    subst h
    exact mem_reachAt_self' _ _ _
  | node b g h' j es F d =>
    simp only [openId] at h
    subst h
    rw [Ui_node]
    simp

/-- The entries of a child opened for a join: their kept children are live
children before of the child's own id, or as the child's planned nodes had
them; their planned nodes are the child's. -/
theorem openEs_prov {C : List NodeId} {R : NodeId → Prop} {w : VN} {esW : List (Nat × VN)}
    (ho : openEs s w = some esW) (hP : KidsProv s C R (nodesOf w)) :
    (∀ y ∈ kidIds esW, s.obj y ≠ none → (∃ q, openId w = some q ∧ kidOf s q y = true) ∨
      (∃ q ∈ C, kidOf s q y = true) ∨ R y) ∧ (∀ u ∈ nodesL esW, u ∈ nodesOf w) := by
  cases w with
  | old y =>
    obtain ⟨n, hobj, rfl⟩ := openEs_old ho
    refine ⟨fun z hz _ => ?_, fun u hu => ?_⟩
    · obtain ⟨e, he, hk⟩ := List.mem_filterMap.mp hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      simp only [kidId, Option.some.injEq] at hk
      subst hk
      exact Or.inl ⟨y, rfl, kidOf_iff.mpr ⟨n, q.1, hobj, hq⟩⟩
    · rw [nodesL_eq] at hu
      obtain ⟨e, he, hu⟩ := List.mem_flatMap.mp hu
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      simp [nodesOf] at hu
  | node b g h j es F d =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    have hself : (b, d, es) ∈ nodesOf (.node b g h j es F d) := by simp [nodesOf]
    refine ⟨fun y hy hs => ?_, fun u hu => by simp only [nodesOf, List.mem_cons]; exact Or.inr hu⟩
    rcases hP _ hself y hy hs with ⟨x, hx, h1⟩ | h1 | h1
    · exact Or.inl ⟨x, hx, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

/-- An inner child opened: its entries' old nodes are distinct and miss its
own id. -/
theorem open_ui_split {g h : Nat} {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g (h + 1) w)
    (ho : openEs s w = some esW) (hnd : (Ui s w).Nodup) :
    (UiL s esW).Nodup ∧ ∀ q, openId w = some q → q ∉ UiL s esW := by
  cases hw with
  | @old _ y hsh hg hne =>
    obtain ⟨n, hobj, rfl⟩ := openEs_old ho
    obtain ⟨lo, hi, hg⟩ := hg
    have hR := R_good hg hobj
    have hU : UiL s ((live n.ks).map (fun q => (q.1, VN.old q.2))) =
        (live n.ks).flatMap (fun cy => R s cy.2) := by
      simp [UiL_eq, List.flatMap_map, Ui]
    have hnd' : (R s y).Nodup := hnd
    rw [hR] at hnd'
    rw [hU]
    refine ⟨(List.nodup_cons.mp hnd').2, fun q hq => ?_⟩
    simp only [openId, Option.some.injEq] at hq
    subst hq
    exact (List.nodup_cons.mp hnd').1
  | inner _ _ _ _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    rename_i b _ _ _ _
    rw [Ui_node] at hnd
    simp only [Nat.add_one_ne_zero, ite_false] at hnd
    rw [← UiL_eq] at hnd
    refine ⟨(List.nodup_append.mp hnd).2.1, fun q hq => ?_⟩
    simp only [openId] at hq
    subst hq
    intro hm
    exact (List.nodup_append.mp hnd).2.2 q (by simp) q hm rfl

/-- A join's split: replacing two neighbours l, r by v is a step, given what
v keeps. -/
theorem step_split {C C' : List NodeId} {R : NodeId → Prop} {es A B : List (Nat × VN)}
    {l r : Nat × VN} {c : Nat} {v : VN} (hes : es = A ++ l :: r :: B) (hrb : RB s C R es)
    (hC1 : ∀ q ∈ C, q ∈ C') (hC2 : ∀ q ∈ C', q ∈ C ∨ q ∈ Ui s l.2 ∨ q ∈ Ui s r.2)
    (hvUi : ∀ z ∈ Ui s v, z ∈ Ui s l.2 ∨ z ∈ Ui s r.2) (hvnd : (Ui s v).Nodup)
    (hvC : ∀ q ∈ C', q ∉ Ui s v) (hvkid : kidId v = none) (hvP : KidsProv s C' R (nodesOf v)) :
    Step s C R es (A ++ (c, v) :: B) := by
  obtain ⟨hnd, hkp, hcu⟩ := hrb
  subst hes
  have hU : UiL s (A ++ l :: r :: B) = UiL s A ++ (Ui s l.2 ++ (Ui s r.2 ++ UiL s B)) := by
    simp [UiL_eq]
  have hU' : UiL s (A ++ (c, v) :: B) = UiL s A ++ (Ui s v ++ UiL s B) := by
    simp [UiL_eq]
  rw [hU] at hnd hcu
  -- disjointness from the nodup list
  have dA : ∀ z ∈ Ui s l.2 ++ Ui s r.2, z ∉ UiL s A ++ UiL s B := by
    intro z hz hz'
    rcases List.mem_append.mp hz' with hz' | hz'
    · exact (List.nodup_append.mp hnd).2.2 z hz' z (by simp at hz ⊢; tauto) rfl
    · have h2 := (List.nodup_append.mp hnd).2.1
      rcases List.mem_append.mp hz with hz | hz
      · exact (List.nodup_append.mp h2).2.2 z hz z (by simp [hz']) rfl
      · have h3 := (List.nodup_append.mp h2).2.1
        exact (List.nodup_append.mp h3).2.2 z hz z hz' rfl
  have hndA := (List.nodup_append.mp hnd).1
  have hndB := (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).2.1).2.1
  have hAB : ∀ z ∈ UiL s A, z ∉ UiL s B := by
    intro z hz hz'
    exact (List.nodup_append.mp hnd).2.2 z hz z (by simp [hz']) rfl
  refine ⟨C', hC1, fun q hq => ?_, ⟨?_, ?_, ?_⟩, fun y hy => ?_, fun z hz => ?_⟩
  · rcases hC2 q hq with h | h | h
    · exact Or.inl h
    · right; rw [hU]; simp [h]
    · right; rw [hU]; simp [h]
  · -- nodup
    rw [hU']
    refine List.nodup_append.mpr ⟨hndA, List.nodup_append.mpr ⟨hvnd, hndB, ?_⟩, ?_⟩
    · intro z hz z' hz' he
      subst he
      exact dA z (by rcases hvUi z hz with h | h <;> simp [h]) (List.mem_append_right _ hz')
    · intro z hz z' hz' he
      subst he
      rcases List.mem_append.mp hz' with hz' | hz'
      · exact dA z (by rcases hvUi z hz' with h | h <;> simp [h]) (List.mem_append_left _ hz)
      · exact hAB z hz hz'
  · -- provenance
    intro u hu
    rw [nodesL_append] at hu
    simp only [nodesL, List.mem_append] at hu
    rcases hu with hu | hu | hu
    · exact hkp.mono hC1 (fun u h => by rw [nodesL_append]; exact List.mem_append_left _ h) u hu
    · exact hvP u hu
    · exact hkp.mono hC1 (fun u h => by
        rw [nodesL_append]; simp only [nodesL, List.mem_append]; exact Or.inr (Or.inr (Or.inr h))) u hu
  · -- C' misses the old nodes used
    intro q hq hm
    rw [hU'] at hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases hC2 q hq with h | h | h
      · exact hcu q h (List.mem_append_left _ hm)
      · exact dA q (by simp [h]) (List.mem_append_left _ hm)
      · exact dA q (by simp [h]) (List.mem_append_left _ hm)
    · rcases List.mem_append.mp hm with hm | hm
      · exact hvC q hq hm
      · rcases hC2 q hq with h | h | h
        · exact hcu q h (by simp [hm])
        · exact dA q (by simp [h]) (List.mem_append_right _ hm)
        · exact dA q (by simp [h]) (List.mem_append_right _ hm)
  · -- kept children
    rw [kidIds_append, kidIds_cons, hvkid] at hy
    rw [kidIds_append, kidIds_cons, kidIds_cons]
    simp only [Option.toList_none, List.nil_append, List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inr hy))
  · rw [hU]
    rw [hU'] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ hz
    · rcases List.mem_append.mp hz with hz | hz
      · rcases hvUi z hz with h | h <;> simp [h]
      · simp [hz]

theorem nodesL_le {es : List (Nat × VN)} {e : Nat × VN} (he : e ∈ es) :
    ∀ u ∈ nodesOf e.2, u ∈ nodesL es := fun _ hu => mem_nodesL he hu

theorem ui_le {es : List (Nat × VN)} {e : Nat × VN} (he : e ∈ es) :
    ∀ z ∈ Ui s e.2, z ∈ UiL s es := by
  intro z hz
  rw [UiL_eq]
  exact List.mem_flatMap.mpr ⟨e, he, hz⟩

/-- The kept children of the entries of two children opened. -/
theorem open2_kids {C : List NodeId} {R : NodeId → Prop} {l r : Nat × VN} {esL esR : List (Nat × VN)}
    (hoL : openEs s l.2 = some esL) (hoR : openEs s r.2 = some esR)
    (hPL : KidsProv s C R (nodesOf l.2)) (hPR : KidsProv s C R (nodesOf r.2))
    (C' : List NodeId) (hC : ∀ q ∈ C, q ∈ C') (hl : ∀ q, openId l.2 = some q → q ∈ C')
    (hr : ∀ q, openId r.2 = some q → q ∈ C') :
    ∀ y ∈ kidIds esL ++ kidIds esR, s.obj y ≠ none → (∃ q ∈ C', kidOf s q y = true) ∨ R y := by
  intro y hy hs
  rcases List.mem_append.mp hy with hy | hy
  · rcases (openEs_prov hoL hPL).1 y hy hs with ⟨q, hq, h1⟩ | ⟨q, hq, h1⟩ | h1
    · exact Or.inl ⟨q, hl q hq, h1⟩
    · exact Or.inl ⟨q, hC q hq, h1⟩
    · exact Or.inr h1
  · rcases (openEs_prov hoR hPR).1 y hy hs with ⟨q, hq, h1⟩ | ⟨q, hq, h1⟩ | h1
    · exact Or.inl ⟨q, hr q hq, h1⟩
    · exact Or.inl ⟨q, hC q hq, h1⟩
    · exact Or.inr h1

/-- A join at the leaf level is a step. -/
theorem joinAt_step_zero {g : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g 0 down es ix = some es')
    {C : List NodeId} {R : NodeId → Prop} (hrb : RB s C R es) : Step s C R es es' := by
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
        obtain ⟨F, dec, rfl⟩ := mkNode_form hm
        have hsplit := split_at2 hl hr
        have hlm : l ∈ es := by rw [hsplit]; simp
        have hrm : r ∈ es := by rw [hsplit]; simp
        have hPL := hrb.2.1.mono (fun q h => h) (nodesL_le hlm)
        have hPR := hrb.2.1.mono (fun q h => h) (nodesL_le hrm)
        simp only [beq_self_eq_true, ite_true]
        rw [List.append_assoc, List.singleton_append]
        let C' := C ++ (openId l.2).toList ++ (openId r.2).toList
        refine step_split (C' := C') hsplit hrb (fun q h => by simp [C', h]) ?_ ?_ ?_ ?_ rfl ?_
        · intro q hq
          simp only [C', List.mem_append, Option.mem_toList] at hq
          rcases hq with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (openId_mem_Ui h))
          · exact Or.inr (Or.inr (openId_mem_Ui h))
        · intro z hz; rw [Ui_node] at hz; simp at hz
        · rw [Ui_node]; simp
        · intro q _ hz; rw [Ui_node] at hz; simp at hz
        · intro u hu y hy hs
          simp only [nodesOf, List.mem_cons] at hu
          rcases hu with rfl | hu
          · simp only at hy
            rw [kidIds_append] at hy
            rcases open2_kids hoL hoR hPL hPR C' (fun q h => by simp [C', h])
              (fun q h => by simp [C', h]) (fun q h => by simp [C', h]) y hy hs with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rw [nodesL_append] at hu
            rcases List.mem_append.mp hu with hu | hu
            · exact (hPL.mono (fun q h => by simp [C', h]) (openEs_prov hoL hPL).2) u hu y hy hs
            · exact (hPR.mono (fun q h => by simp [C', h]) (openEs_prov hoR hPR).2) u hu y hy hs
    · cases hj
  · cases hj

theorem uiL_split {es A B : List (Nat × VN)} {l r : Nat × VN} (h : es = A ++ l :: r :: B) :
    UiL s es = UiL s A ++ (Ui s l.2 ++ (Ui s r.2 ++ UiL s B)) := by
  subst h
  simp [UiL_eq]

/-- A join of two inner nodes, rebalanced one level down, is a step. -/
theorem joinAt_step_succ {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {R : NodeId → Prop}
    (hdown : ∀ J J', down J = some J' → KOk cf s g h J → ∀ C, RB s C R J → Step s C R J J')
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g (h + 1) down es ix = some es')
    (hes : KOk cf s g (h + 1) es) {C : List NodeId} (hrb : RB s C R es) : Step s C R es es' := by
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
          obtain ⟨F, dec, rfl⟩ := mkNode_form hm
          simp only [show (h + 1 == 0) = false by simp, Bool.false_eq_true, ite_false]
          rw [List.append_assoc, List.singleton_append]
          have hsplit := split_at2 hl hr
          have hlm : l ∈ es := by rw [hsplit]; simp
          have hrm : r ∈ es := by rw [hsplit]; simp
          have hPL := hrb.2.1.mono (fun q h => h) (nodesL_le hlm)
          have hPR := hrb.2.1.mono (fun q h => h) (nodesL_le hrm)
          -- the old nodes of l and r: distinct, each list nodup
          have hU := uiL_split (s := s) hsplit
          have hnd := hrb.1
          rw [hU] at hnd
          have hndL : (Ui s l.2).Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
          have hndR : (Ui s r.2).Nodup :=
            (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).2.1).1
          have hLR : ∀ z ∈ Ui s l.2, z ∉ Ui s r.2 := by
            intro z hz hz'
            exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).2.2 z hz z (by simp [hz']) rfl
          obtain ⟨sL1, sL2⟩ := open_ui_split (hes l hlm).1 hoL hndL
          obtain ⟨sR1, sR2⟩ := open_ui_split (hes r hrm).1 hoR hndR
          have uL := open_ui (hes l hlm).1 hoL
          have uR := open_ui (hes r hrm).1 hoR
          let C1 := C ++ (openId l.2).toList ++ (openId r.2).toList
          have hC1 : ∀ q ∈ C1, q ∈ C ∨ q ∈ Ui s l.2 ∨ q ∈ Ui s r.2 := by
            intro q hq
            simp only [C1, List.mem_append, Option.mem_toList] at hq
            rcases hq with (h1 | h1) | h1
            · exact Or.inl h1
            · exact Or.inr (Or.inl (openId_mem_Ui h1))
            · exact Or.inr (Or.inr (openId_mem_Ui h1))
          have hUJ : UiL s (esL ++ renameHead r.1 esR) = UiL s esL ++ UiL s esR := by
            rw [UiL_append, UiL_renameHead]
          have hJsub : ∀ z ∈ UiL s (esL ++ renameHead r.1 esR), z ∈ Ui s l.2 ∨ z ∈ Ui s r.2 := by
            intro z hz
            rw [hUJ] at hz
            rcases List.mem_append.mp hz with hz | hz
            · exact Or.inl (uL z hz)
            · exact Or.inr (uR z hz)
          have hJk : KOk cf s g h (esL ++ renameHead r.1 esR) := by
            obtain ⟨hL1, _, _⟩ := openEs_succ (hes l hlm).1 hoL
            obtain ⟨hR1, _, _⟩ := openEs_succ (hes r hrm).1 hoR
            intro e he
            rcases List.mem_append.mp he with he | he
            · exact hL1 e he
            · obtain ⟨e', he', h2⟩ := renameHead_mem he
              rw [← h2]; exact hR1 e' he'
          have hrbJ : RB s C1 R (esL ++ renameHead r.1 esR) := by
            refine ⟨?_, ?_, ?_⟩
            · rw [hUJ]
              refine List.nodup_append.mpr ⟨sL1, sR1, fun a ha b hb hab => ?_⟩
              subst hab
              exact hLR a (uL a ha) (uR a hb)
            · intro u hu
              rw [nodesL_append, nodesL_renameHead] at hu
              rcases List.mem_append.mp hu with hu | hu
              · exact (hPL.mono (fun q h => by simp [C1, h]) (openEs_prov hoL hPL).2) u hu
              · exact (hPR.mono (fun q h => by simp [C1, h]) (openEs_prov hoR hPR).2) u hu
            · intro q hq hm
              rw [hUJ] at hm
              simp only [C1, List.mem_append, Option.mem_toList] at hq
              rcases hq with (hq | hq) | hq
              · have h2 := hrb.2.2 q hq
                rw [hU] at h2
                rcases List.mem_append.mp hm with hm | hm
                · exact h2 (by simp [uL q hm])
                · exact h2 (by simp [uR q hm])
              · rcases List.mem_append.mp hm with hm | hm
                · exact sL2 q hq hm
                · exact hLR q (openId_mem_Ui hq) (uR q hm)
              · rcases List.mem_append.mp hm with hm | hm
                · exact hLR q (uL q hm) (openId_mem_Ui hq)
                · exact sR2 q hq hm
          obtain ⟨C2, d1, d2, d3, d4, d5⟩ := hdown _ _ hd hJk C1 hrbJ
          refine step_split (C' := C2) hsplit hrb (fun q h => d1 q (by simp [C1, h])) ?_ ?_ ?_ ?_ rfl ?_
          · intro q hq
            rcases d2 q hq with h1 | h1
            · exact hC1 q h1
            · exact Or.inr (hJsub q h1)
          · intro z hz
            rw [Ui_node] at hz
            simp only [Option.toList_none, List.nil_append, Nat.add_one_ne_zero, ite_false] at hz
            rw [← UiL_eq, UiL_renameHead] at hz
            exact hJsub z (d5 z hz)
          · rw [Ui_node]
            simp only [Option.toList_none, List.nil_append, Nat.add_one_ne_zero, ite_false]
            rw [← UiL_eq, UiL_renameHead]
            exact d3.1
          · intro q hq hz
            rw [Ui_node] at hz
            simp only [Option.toList_none, List.nil_append, Nat.add_one_ne_zero, ite_false] at hz
            rw [← UiL_eq, UiL_renameHead] at hz
            exact d3.2.2 q hq hz
          · intro u hu y hy hs
            simp only [nodesOf, List.mem_cons] at hu
            rcases hu with rfl | hu
            · simp only at hy
              rw [kidIds_renameHead] at hy
              have hy2 := d4 y hy
              rw [kidIds_append, kidIds_renameHead] at hy2
              rcases open2_kids hoL hoR hPL hPR C2 (fun q h => d1 q (by simp [C1, h]))
                (fun q h => d1 q (by simp [C1, h])) (fun q h => d1 q (by simp [C1, h])) y hy2 hs with
                h1 | h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr h1)
            · rw [nodesL_renameHead] at hu
              exact d3.2.1 u hu y hy hs
    · cases hj
  · cases hj

/-- The loop of joins is a step. -/
theorem joinLoop_step {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {R : NodeId → Prop}
    (hjoin : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      KOk cf s g h es')
    (hjs : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      ∀ C, RB s C R es → Step s C R es es') :
    ∀ (n : Nat) (es es' : List (Nat × VN)), joinLoop cf i s g h down n es = some es' →
      KOk cf s g h es → ∀ C, RB s C R es → Step s C R es es'
  | 0, es, es', hl, _, C, hrb => by
    simp only [joinLoop, Option.some.injEq] at hl
    subst hl
    exact Step.refl hrb
  | n + 1, es, es', hl, hk, C, hrb => by
    simp only [joinLoop] at hl
    split at hl
    · simp only [Option.some.injEq] at hl; subst hl; exact Step.refl hrb
    · split at hl
      · simp only [Option.some.injEq] at hl; subst hl; exact Step.refl hrb
      · rename_i ix _
        cases hj : joinAt cf i s g h down es ix with
        | none => rw [hj] at hl; cases hl
        | some es1 =>
          rw [hj] at hl
          simp only at hl
          exact (hjs es ix es1 hj hk C hrb).trans (fun C1 h1 =>
            joinLoop_step hjoin hjs n es1 es' hl (hjoin es ix es1 hj hk) C1 h1)

/-- **Rebalance is a step**: the children rebalanced keep the provenance of
their kept children, with the nodes opened added to C, none of them an old
node they use. -/
theorem rebalance_step (hcf : cf.Ok) {g : Nat} {R : NodeId → Prop} :
    ∀ (f h : Nat) (es0 es2 : List (Nat × VN)), rebalance cf i s f g h es0 = some es2 →
    (∀ e ∈ es0, VOk cf s g h e.2) → ∀ C, RB s C R es0 → Step s C R es0 es2
  | 0, _, _, _, hr, _, _, _ => by simp [rebalance] at hr
  | f + 1, h, es0, es2, hr, hk, C, hrb => by
    unfold rebalance at hr
    simp only at hr
    have hk1 : KOk cf s g h (es0.filter (fun e => !e.2.isEmpty)) := by
      intro e he
      rw [List.mem_filter] at he
      exact ⟨hk e he.1, by simpa using he.2⟩
    have hsub : (es0.filter (fun e => !e.2.isEmpty)).Sublist es0 := List.filter_sublist
    have hstep1 : Step s C R es0 (es0.filter (fun e => !e.2.isEmpty)) := by
      have hUs : (UiL s (es0.filter (fun e => !e.2.isEmpty))).Sublist (UiL s es0) := by
        rw [UiL_eq, UiL_eq]; exact hsub.flatMap _
      refine ⟨C, fun q h => h, fun q h => Or.inl h, ⟨hUs.nodup hrb.1, ?_, ?_⟩, ?_, ?_⟩
      · intro u hu
        rw [nodesL_eq] at hu
        exact hrb.2.1 u (by rw [nodesL_eq]; exact (hsub.flatMap _).subset hu)
      · intro q hq hm; exact hrb.2.2 q hq (hUs.subset hm)
      · intro y hy
        exact (hsub.filterMap _).subset hy
      · intro z hz; exact hUs.subset hz
    split at hr
    · simp only [Option.some.injEq] at hr
      subst hr
      exact hstep1
    · have hjoin : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es → KOk cf s g h es' := by
        intro es ix es' hj hes
        cases h with
        | zero => exact (joinAt_zero hcf hj hes).2.1
        | succ h' =>
          refine (joinAt_succ hcf (fun J J' hd hJ => ?_) hj hes).2.1
          obtain ⟨a1, a2, a3⟩ := rebalance_spec hcf f h' J J' hd (fun e he => (hJ e he).1)
          exact ⟨a1, a2, a3 (fun e he => (hJ e he).2)⟩
      have hjs : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es → ∀ C, RB s C R es → Step s C R es es' := by
        intro es ix es' hj hes C hrb
        cases h with
        | zero => exact joinAt_step_zero hj hrb
        | succ h' =>
          exact joinAt_step_succ (fun J J' hd hJk C' hJ =>
            rebalance_step hcf f h' J J' hd (fun e he => (hJk e he).1) C' hJ) hj hes hrb
      exact hstep1.trans (fun C1 h1 => joinLoop_step hjoin hjs _ _ _ hr hk1 C1 h1)

/-! ## The plan's provenance: plan -/

/-- What `applyGroups` gives a segment leaf x, for the provenance: every old
id of its entries is a live child before of x, or meets Rp. -/
def AGProv (cf : Cfg) (i : Time) (s : Tree) (Xs : List NodeId) (Rp : Nat → NodeId → Prop)
    (f : Nat) : Prop :=
  ∀ (x : NodeId) (n : KNode) (g : Nat) (lo : Nat) (hi : Option Nat) (ops : List Contract.Op)
    (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc), s.obj x = some (.key n) →
    Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup → (∀ z ∈ R s x, z ∈ Xs) →
    (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    (∀ z, acc.next ≤ z → s.obj z = none) →
    applyGroups cf i s f g (live n.ks) (touched g ops) ops acc = some (es, acc') →
    ∀ e ∈ es, s.obj e.2 ≠ none → kidOf s x e.2 = true ∨ Rp g e.2

/-- The plan's provenance at fuel f: the kept children of every planned node
of the plan of x are live children before of the node's base, of a node of C,
or meet Rp; C is of the nodes reached from x and none an old node the plan
uses. -/
def PlanProvOk (cf : Cfg) (i : Time) (s : Tree) (Xs : List NodeId) (Rp : Nat → NodeId → Prop)
    (f : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Contract.Op) (acc : Acc) (v : VN) (acc' : Acc)
    (lo : Nat) (hi : Option Nat),
    plan cf i s f x g h ops acc = some (v, acc') → Shaped cf s g h x → Good s x lo hi →
    (R s x).Nodup → (∀ z ∈ R s x, z ∈ Xs) → (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    (∀ z, acc.next ≤ z → s.obj z = none) →
    ∃ C, KidsProv s C (Rp g) (nodesOf v) ∧ (∀ q ∈ C, q ∉ Ui s v) ∧ (∀ q ∈ C, q ∈ R s x)

/-- A plan's next id does not go down. -/
theorem plan_next (hcf : cf.Ok) (hs : SOk cf i s) {f : Nat} {x : NodeId} {g h : Nat}
    {ops : List Contract.Op} {acc acc' : Acc} {v : VN} {lo : Nat} {hi : Option Nat}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) (hsh : Shaped cf s g h x)
    (hg : Good s x lo hi) (hnd : (R s x).Nodup)
    (hq : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length)
    (hfr : ∀ z, acc.next ≤ z → s.obj z = none) : acc.next ≤ acc'.next := by
  obtain ⟨_, runs, _, _, _, hch, _⟩ := plan_runs hcf (fun grp y0 r => RunOk cf i s g grp y0 r)
    (fun op => keyOk cf op.key = true ∧ g < op.key.length) (f_hAG hcf (f_all hcf f) hs)
    x h ops acc v acc' lo hi hp hsh hg hnd hq hfr
  exact chain_next hch

theorem route_mem {β : Type} {cv : Contract.Op → Nat} : ∀ (lv : List (Nat × β))
    (ops : List Contract.Op), ∀ o ∈ Contract.PE.route cv lv ops, ∀ op ∈ o, op ∈ ops
  | [], _, o, ho, _, _ => by simp [Contract.PE.route] at ho
  | [_], ops, o, ho, op, hop => by
    simp only [Contract.PE.route, List.mem_singleton] at ho
    subst ho; exact hop
  | _ :: (c', y) :: r, ops, o, ho, op, hop => by
    simp only [Contract.PE.route, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact (List.mem_filter.mp hop).1
    · exact (List.mem_filter.mp (route_mem ((c', y) :: r) _ o ho op hop)).1

/-- The plan of x is a planned node with base x. -/
theorem plan_form {f : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op} {acc acc' : Acc}
    {v : VN} (hp : plan cf i s f x g h ops acc = some (v, acc')) :
    ∃ g' h' j es F dec, v = .node (some x) g' h' j es F dec := by
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
    unfold plan at hp
    split at hp
    · cases hp
    · split at hp
      · split at hp
        · cases hp
        · split at hp
          · rename_i w hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, _⟩ := hp
            obtain ⟨F, dec, rfl⟩ := mkNode_form hm
            exact ⟨_, _, _, _, _, _, rfl⟩
          · cases hp
      · dsimp only at hp
        split at hp
        · cases hp
        · split at hp
          · cases hp
          · split at hp
            · rename_i w hm
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, _⟩ := hp
              obtain ⟨F, dec, rfl⟩ := mkNode_form hm
              exact ⟨_, _, _, _, _, _, rfl⟩
            · cases hp

theorem kidId_plan {f : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op} {acc acc' : Acc}
    {v : VN} (hp : plan cf i s f x g h ops acc = some (v, acc')) {y : NodeId}
    (hy : kidId v = some y) : y = x := by
  obtain ⟨g', h', j, es, F, dec, rfl⟩ := plan_form hp
  simp only [kidId] at hy
  split at hy
  · cases hy
  · exact (Option.some.inj hy).symm

/-- The children planned keep the provenance. -/
theorem planKids_prov (hcf : cf.Ok) (hs : SOk cf i s) {Xs : List NodeId}
    {Rp : Nat → NodeId → Prop} {g h : Nat} :
    ∀ (F : Nat) (lv : List (Nat × NodeId))
    (os : List (List Contract.Op)) (acc : Acc) (es : List (Nat × VN)) (acc' : Acc),
    (∀ f' < F, PlanProvOk cf i s Xs Rp f') → (∀ e ∈ lv, Shaped cf s g h e.2 ∧ ∃ lo hi, Good s e.2 lo hi) →
    (lv.flatMap (fun e => R s e.2)).Nodup → (∀ z ∈ lv.flatMap (fun e => R s e.2), z ∈ Xs) →
    (∀ o ∈ os, ∀ op ∈ o, keyOk cf op.key = true ∧ g < op.key.length) →
    (∀ z, acc.next ≤ z → s.obj z = none) →
    planKids cf i s F g (h + 1) lv os acc = some (es, acc') →
    ∃ C, RB s C (Rp g) es ∧ (∀ q ∈ C, q ∈ lv.flatMap (fun e => R s e.2)) ∧
      (∀ z ∈ UiL s es, z ∈ lv.flatMap (fun e => R s e.2)) ∧ (∀ y ∈ kidIds es, ∃ c, (c, y) ∈ lv)
  | 0, _, _, _, _, _, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | F + 1, [], _, acc, es, acc', _, _, _, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, _⟩ := hp
    exact ⟨[], ⟨by simp [UiL], by intro u hu; simp [nodesL] at hu, by simp⟩, by simp, by simp [UiL],
      by simp [kidIds]⟩
  | F + 1, (c, y) :: rest, [], acc, es, acc', _, _, _, _, _, _, hp => by simp [planKids] at hp
  | F + 1, (c, y) :: rest, o :: os, acc, es, acc', IH, hlv, hnd, hXs, hos, hfr, hp => by
    simp only [planKids] at hp
    have hnd' : (R s y ++ rest.flatMap (fun e => R s e.2)).Nodup := by simpa using hnd
    have hdis : ∀ z ∈ R s y, z ∉ rest.flatMap (fun e => R s e.2) := by
      intro z hz hz'
      exact (List.nodup_append.mp hnd').2.2 z hz z hz' rfl
    obtain ⟨hsh, lo, hi, hg⟩ := hlv (c, y) List.mem_cons_self
    have hlv' : ∀ e ∈ rest, Shaped cf s g h e.2 ∧ ∃ lo hi, Good s e.2 lo hi :=
      fun e he => hlv e (List.mem_cons_of_mem _ he)
    have IH' : ∀ f' < F, PlanProvOk cf i s Xs Rp f' := fun f' hf => IH f' (by omega)
    have hXy : ∀ z ∈ R s y, z ∈ Xs := fun z hz => hXs z (by simp [hz])
    have hXr : ∀ z ∈ rest.flatMap (fun e => R s e.2), z ∈ Xs := fun z hz => hXs z (by
      simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hz)
    -- the child: its old nodes, its consumed nodes, its kept id
    have child : ∀ (w : VN) (Cw : List NodeId) es2 acc2, (Ui s w).Nodup →
        (∀ z ∈ Ui s w, z ∈ R s y) → KidsProv s Cw (Rp g) (nodesOf w) → (∀ q ∈ Cw, q ∉ Ui s w) →
        (∀ q ∈ Cw, q ∈ R s y) → (∀ z, kidId w = some z → z = y) →
        (∀ z, acc2.next ≤ z → s.obj z = none) →
        planKids cf i s F g (h + 1) rest os acc2 = some (es2, acc') →
        ∃ C, RB s C (Rp g) ((c, w) :: es2) ∧ (∀ q ∈ C, q ∈ ((c, y) :: rest).flatMap (fun e => R s e.2)) ∧
          (∀ z ∈ UiL s ((c, w) :: es2), z ∈ ((c, y) :: rest).flatMap (fun e => R s e.2)) ∧
          (∀ z ∈ kidIds ((c, w) :: es2), ∃ c', (c', z) ∈ (c, y) :: rest) := by
      intro w Cw es2 acc2 hwnd hwR hwP hwC hwC2 hwk hfr2 hp2
      obtain ⟨C2, ⟨r1, r2, r3⟩, r4, r5, r6⟩ := planKids_prov hcf hs F rest os acc2 es2 acc' IH' hlv'
        (List.nodup_append.mp hnd').2.1 hXr (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho')) hfr2 hp2
      have hU : UiL s ((c, w) :: es2) = Ui s w ++ UiL s es2 := by simp [UiL_eq]
      refine ⟨Cw ++ C2, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hU]
        refine List.nodup_append.mpr ⟨hwnd, r1, fun a ha b hb hab => ?_⟩
        subst hab
        exact hdis a (hwR a ha) (r5 a hb)
      · intro u hu
        simp only [nodesL, List.mem_append] at hu
        rcases hu with hu | hu
        · exact (hwP.mono (fun q h => List.mem_append_left _ h) (fun u h => h)) u hu
        · exact (r2.mono (fun q h => List.mem_append_right _ h) (fun u h => h)) u hu
      · intro q hq hm
        rw [hU] at hm
        rcases List.mem_append.mp hq with hq | hq
        · rcases List.mem_append.mp hm with hm | hm
          · exact hwC q hq hm
          · exact hdis q (hwC2 q hq) (r5 q hm)
        · rcases List.mem_append.mp hm with hm | hm
          · exact hdis q (hwR q hm) (r4 q hq)
          · exact r3 q hq hm
      · intro q hq
        simp only [List.flatMap_cons, List.mem_append]
        rcases List.mem_append.mp hq with hq | hq
        · exact Or.inl (hwC2 q hq)
        · exact Or.inr (r4 q hq)
      · intro z hz
        rw [hU] at hz
        simp only [List.flatMap_cons, List.mem_append]
        rcases List.mem_append.mp hz with hz | hz
        · exact Or.inl (hwR z hz)
        · exact Or.inr (r5 z hz)
      · intro z hz
        rw [kidIds_cons] at hz
        rcases List.mem_append.mp hz with hz | hz
        · rw [hwk z (Option.mem_toList.mp hz)]
          exact ⟨c, List.mem_cons_self⟩
        · obtain ⟨c', hc'⟩ := r6 z hz
          exact ⟨c', List.mem_cons_of_mem _ hc'⟩
    have hRy : (R s y).Nodup := (List.nodup_append.mp hnd').1
    split at hp
    · cases hp2 : planKids cf i s F g (h + 1) rest os acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact child (.old y) [] es2 acc hRy (fun z hz => hz) (by intro u hu; simp [nodesOf] at hu)
          (by simp) (by simp) (fun z hz => by simp [kidId] at hz; exact hz.symm) hfr hp2
    · cases hp1 : plan cf i s F y g (h + 1 - 1) o acc with
      | none => rw [hp1] at hp; cases hp
      | some q =>
        rw [hp1] at hp
        obtain ⟨w, acc1⟩ := q
        simp only at hp
        cases hp2 : planKids cf i s F g (h + 1) rest os acc1 with
        | none => rw [hp2] at hp; cases hp
        | some q =>
          rw [hp2] at hp
          obtain ⟨es2, acc2⟩ := q
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simp only [Nat.add_sub_cancel] at hp1
          have hoq := hos o List.mem_cons_self
          obtain ⟨Cw, hwP, hwC, hwC2⟩ := IH F (by omega) y g h o acc w acc1 lo hi hp1 hsh hg hRy
            hXy hoq hfr
          obtain ⟨_, hown, _, _⟩ := plan_own hcf hp1 hsh hg
          have hsub : (Ui s w).Subperm (R s y) := (List.sublist_append_left _ _).subperm.trans hown
          have hn1 := plan_next hcf hs hp1 hsh hg hRy hoq hfr
          exact child w Cw es2 acc1 (e_subperm_nodup hsub hRy) (fun z hz => hsub.subset hz) hwP hwC
            hwC2 (fun z hz => kidId_plan hp1 hz) (fun z hz => hfr z (by tomega)) hp2

/-- **The plan's provenance**, given that of `applyGroups`. -/
theorem plan_prov (hcf : cf.Ok) (hs : SOk cf i s) {Xs : List NodeId} {Rp : Nat → NodeId → Prop}
    {FF : Nat} (hAG : ∀ f < FF, AGProv cf i s Xs Rp f) : ∀ f, f ≤ FF → PlanProvOk cf i s Xs Rp f := by
  intro f
  refine Nat.strong_induction_on f ?_
  intro f IH hfF x g h ops acc v acc' lo hi hp hsh hg hnd hXs hq hfr
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
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
            obtain ⟨F, dec, rfl⟩ := mkNode_form hm
            simp only [beq_self_eq_true, ite_true]
            refine ⟨[], fun u hu y hy hs => ?_, by simp, by simp⟩
            simp only [nodesOf, List.mem_cons] at hu
            rcases hu with rfl | hu
            · simp only [kidIds, List.filterMap_map, List.mem_filterMap, Function.comp_def,
                kidId, Option.some.injEq] at hy
              obtain ⟨e, he, rfl⟩ := hy
              rcases hAG f (by omega) x n g lo hi ops acc es acc1 hobj hsh hg hnd hXs hq hfr ha e he hs
                with h1 | h1
              · exact Or.inl ⟨x, rfl, h1⟩
              · exact Or.inr (Or.inr h1)
            · rw [nodesL_eq] at hu
              obtain ⟨e, he, hu⟩ := List.mem_flatMap.mp hu
              obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
              simp [nodesOf] at hu
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
              have hRx := R_good hg hobj
              have hnd' := hnd
              rw [hRx] at hnd'
              obtain ⟨hxn, hndk⟩ := List.nodup_cons.mp hnd'
              have hlv : ∀ e ∈ live n.ks, Shaped cf s g h' e.2 ∧ ∃ lo hi, Good s e.2 lo hi := by
                intro e he
                cases hkids e.1 e.2 he with
                | old hsh' hg' _ => exact ⟨hsh', hg'⟩
              obtain ⟨C0, hrb, hC0, hU0, hk0⟩ := planKids_prov hcf hs f (live n.ks) _ acc es acc1
                (fun f' h => IH f' (by omega) (by omega)) hlv hndk
                (fun z hz => hXs z (by rw [hRx]; exact List.mem_cons_of_mem _ hz))
                (fun o ho op hop => hq op (route_mem _ _ o ho op hop)) hfr hpk
              obtain ⟨_, _, _, hvk⟩ := planKids_spec f (live n.ks) ops acc es acc1
                (fun f' _ => plan_ok hcf f') hne hpk hkids
              obtain ⟨C1, d1, d2, ⟨e1, e2, e3⟩, d4, d5⟩ :=
                rebalance_step (R := Rp g) hcf (f + 1) h' es es2 hr hvk C0 hrb
              obtain ⟨F, dec, rfl⟩ := mkNode_form hm
              simp only [show (h' + 1 == 0) = false by simp, Bool.false_eq_true, ite_false]
              have hC1 : ∀ q ∈ C1, q ∈ (live n.ks).flatMap (fun e => R s e.2) := by
                intro q hq
                rcases d2 q hq with h1 | h1
                · exact hC0 q h1
                · exact hU0 q h1
              refine ⟨C1, fun u hu y hy hs => ?_, fun q hq hm => ?_, fun q hq => ?_⟩
              · simp only [nodesOf, List.mem_cons] at hu
                rcases hu with rfl | hu
                · simp only at hy
                  rw [kidIds_renameHead] at hy
                  obtain ⟨c, hc⟩ := hk0 y (d4 y hy)
                  exact Or.inl ⟨x, rfl, kidOf_iff.mpr ⟨n, c, hobj, hc⟩⟩
                · rw [nodesL_renameHead] at hu
                  exact e2 u hu y hy hs
              · rw [Ui_node] at hm
                simp only [Option.toList_some, Nat.add_one_ne_zero, ite_false, List.singleton_append,
                  List.mem_cons] at hm
                rcases hm with rfl | hm
                · exact hxn (hC1 _ hq)
                · rw [← UiL_eq, UiL_renameHead] at hm
                  exact e3 q hq hm
              · rw [hRx]
                exact List.mem_cons_of_mem _ (hC1 q hq)

/-! ## The plan's provenance: the root settled -/

/-- A planned tree for the provenance: its kept children's provenance, its
old nodes distinct, C none of them. -/
def SP (s : Tree) (C : List NodeId) (Rp : NodeId → Prop) (v : VN) : Prop :=
  KidsProv s C Rp (nodesOf v) ∧ (Ui s v).Nodup ∧ ∀ q ∈ C, q ∉ Ui s v

/-- What the root settled keeps: C grows by the collapsed roots; the root's
kept id is the planned root's, or a live child before of a node of C, or
meets Rp. -/
def SettleOk (s : Tree) (C : List NodeId) (Rp : NodeId → Prop) (v v' : VN) : Prop :=
  ∃ C', (∀ q ∈ C, q ∈ C') ∧ (∀ q ∈ C', q ∈ C ∨ q ∈ Ui s v) ∧ SP s C' Rp v' ∧
    (∀ z ∈ Ui s v', z ∈ Ui s v) ∧
    (∀ y, kidId v' = some y → s.obj y ≠ none →
      kidId v = some y ∨ (∃ q ∈ C', kidOf s q y = true) ∨ Rp y)

theorem SettleOk.refl {C : List NodeId} {Rp : NodeId → Prop} {v : VN} (h : SP s C Rp v) :
    SettleOk s C Rp v v :=
  ⟨C, fun _ h => h, fun _ h => Or.inl h, h, fun _ h => h, fun _ h _ => Or.inl h⟩

/-- **The root settled keeps the provenance.** -/
theorem settle_prov {Rp : NodeId → Prop} : ∀ (f g : Nat) (space : Bool) (h : Nat) (v v' : VN),
    EOk cf i s g h v → settleRoot cf i s f g v space = some (some v') →
    ∀ C, SP s C Rp v → SettleOk s C Rp v v'
  | 0, _, _, _, _, _, _, hs, _, _ => by simp [settleRoot] at hs
  | f + 1, g, space, h, v, v', hv, hs, C, hsp => by
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
          · simp only [Option.some.injEq] at hs; subst hs; exact SettleOk.refl hsp
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
              obtain ⟨_, hnd, hC⟩ := hsp
              have hnd' : (R s y).Nodup := hnd
              rw [hR] at hnd'
              have hsp' : SP s (C ++ [y]) Rp (.old z) := by
                refine ⟨fun u hu => by simp [nodesOf] at hu, (List.nodup_cons.mp hnd').2, ?_⟩
                intro q hq hm
                rcases List.mem_append.mp hq with hq | hq
                · exact hC q hq (show q ∈ R s y by rw [hR]; exact List.mem_cons_of_mem _ hm)
                · simp only [List.mem_singleton] at hq
                  subst hq
                  exact (List.nodup_cons.mp hnd').1 hm
              obtain ⟨C2, b1, b2, b3, b4, b5⟩ := settle_prov f g space h'' (.old z) v' (EOk.old hz) hs
                (C ++ [y]) hsp'
              have hUy : ∀ w ∈ Ui s (.old z), w ∈ Ui s (.old y) := by
                intro w hw
                show w ∈ R s y
                rw [hR]; exact List.mem_cons_of_mem _ hw
              refine ⟨C2, fun q hq => b1 q (List.mem_append_left _ hq), fun q hq => ?_, b3,
                fun w hw => hUy w (b4 w hw), fun y' hy' hsy' => ?_⟩
              · rcases b2 q hq with h1 | h1
                · rcases List.mem_append.mp h1 with h1 | h1
                  · exact Or.inl h1
                  · simp only [List.mem_singleton] at h1
                    subst h1
                    right; show q ∈ R s q; rw [hR]; exact List.mem_cons_self
                · exact Or.inr (hUy q h1)
              · rcases b5 y' hy' hsy' with h1 | h1 | h1
                · simp only [kidId, Option.some.injEq] at h1
                  subst h1
                  exact Or.inr (Or.inl ⟨y, b1 y (by simp), kidOf_iff.mpr ⟨n, c, hobj, by rw [hl]; simp⟩⟩)
                · exact Or.inr (Or.inl h1)
                · exact Or.inr (Or.inr h1)
        · simp only [Option.some.injEq] at hs; subst hs; exact SettleOk.refl hsp
    | node base g' hv' join es F dec =>
      have hgh : g' = g ∧ hv' = h := by cases hv; exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := hgh
      simp only at hs
      split at hs
      · split at hs
        · cases hs
        · split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact SettleOk.refl hsp
          · cases hm : mkNode cf i s none g' 0 false [] with
            | none => rw [hm] at hs; cases hs
            | some w =>
              rw [hm] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              subst hs
              obtain ⟨F2, dec2, rfl⟩ := mkNode_form hm
              refine ⟨C, fun _ h => h, fun _ h => Or.inl h, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
              · intro u hu y hy
                simp [nodesOf, nodesL] at hu
                subst hu
                simp [kidIds] at hy
              · rw [Ui_node]; simp
              · intro q _ hm; rw [Ui_node] at hm; simp at hm
              · intro z hz; rw [Ui_node] at hz; simp at hz
              · intro y hy; simp [kidId] at hy
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
            obtain ⟨hkp, hnd, hC⟩ := hsp
            have hU : Ui s (.node base g' (h'' + 1) join [(c, ch)] F dec) = base.toList ++ Ui s ch := by
              rw [Ui_node]; simp
            rw [hU] at hnd hC
            have hsp' : SP s (C ++ base.toList) Rp ch := by
              refine ⟨hkp.mono (fun q h => List.mem_append_left _ h) (fun u hu => by
                simp only [nodesOf, nodesL, List.append_nil, List.mem_cons]; exact Or.inr hu),
                (List.nodup_append.mp hnd).2.1, fun q hq hm => ?_⟩
              rcases List.mem_append.mp hq with hq | hq
              · exact hC q hq (List.mem_append_right _ hm)
              · exact (List.nodup_append.mp hnd).2.2 q hq q hm rfl
            obtain ⟨C2, b1, b2, b3, b4, b5⟩ := settle_prov f g' space h'' ch v' hch hs _ hsp'
            refine ⟨C2, fun q hq => b1 q (List.mem_append_left _ hq), fun q hq => ?_, b3,
              fun z hz => by rw [hU]; exact List.mem_append_right _ (b4 z hz), fun y hy hsy => ?_⟩
            · rcases b2 q hq with h1 | h1
              · rcases List.mem_append.mp h1 with h1 | h1
                · exact Or.inl h1
                · right; rw [hU]; exact List.mem_append_left _ h1
              · right; rw [hU]; exact List.mem_append_right _ h1
            · rcases b5 y hy hsy with h1 | h1 | h1
              · -- the child's kept id: a kept child of the node collapsed
                have hyk : y ∈ kidIds [(c, ch)] := by rw [kidIds_cons]; simp [h1]
                rcases hkp (base, dec, [(c, ch)]) (by simp [nodesOf]) y hyk hsy with
                  ⟨x, hx, h2⟩ | ⟨q, hq, h2⟩ | h2
                · right; left
                  exact ⟨x, b1 x (List.mem_append_right _ (by simpa using hx)), h2⟩
                · right; left; exact ⟨q, b1 q (List.mem_append_left _ hq), h2⟩
                · right; right; exact h2
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr h1)
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
                have hsp' : SP s C Rp (VN.node none g' (hv' + 1) false
                    (if hv' + 1 == 0 then [(0, VN.node base g' hv' join es F (Dec.parts k))]
                      else renameHead 0 [(0, VN.node base g' hv' join es F (Dec.parts k))]) F2 dec2) := by
                  obtain ⟨hkp, hnd, hC⟩ := hsp
                  refine ⟨fun u hu y hy hs' => ?_, by rw [hUi]; exact hnd, by rw [hUi]; exact hC⟩
                  simp only [show (hv' + 1 == 0) = false by simp, Bool.false_eq_true, ite_false,
                    renameHead, nodesOf, nodesL, List.append_nil, List.mem_cons] at hu
                  rcases hu with rfl | hu
                  · cases base <;> simp [kidIds, kidId] at hy
                  · exact hkp u (by simp only [nodesOf]; exact List.mem_cons.mpr hu) y hy hs'
                obtain ⟨C2, b1, b2, b3, b4, b5⟩ := settle_prov f g' space (hv' + 1) _ v' her hs C hsp'
                refine ⟨C2, b1, fun q hq => ?_, b3, fun z hz => by rw [← hUi]; exact b4 z hz,
                  fun y hy hsy => ?_⟩
                · rcases b2 q hq with h1 | h1
                  · exact Or.inl h1
                  · right; rw [← hUi]; exact h1
                · rcases b5 y hy hsy with h1 | h1 | h1
                  · simp [kidId] at h1
                  · exact Or.inr (Or.inl h1)
                  · exact Or.inr (Or.inr h1)
            · simp only [Option.some.injEq] at hs; subst hs; exact SettleOk.refl hsp
          · simp only [Option.some.injEq] at hs; subst hs; exact SettleOk.refl hsp

/-! ## The segments: a run's provenance -/

/-- A segment's provenance, for its writes W and its result res, from the old
root `root`: every key klong a node of W gets names a live child before of it,
or of an old node of the segment's tree that W does not write; the result is
the old root, or a live child before of such a node. -/
def SegProvW (s : Tree) (root : Option NodeId) (W : List (NodeId × Obj)) (res : Option NodeId) :
    Prop :=
  (∀ p ∈ W, ∀ c y, Klong.key c y ∈ newKlongs s p → s.obj y ≠ none →
    (∃ n c', s.obj p.1 = some (.key n) ∧ (c', y) ∈ live n.ks) ∨
    ∃ q ∈ Ro s root, q ∉ W.map (·.1) ∧ kidOf s q y = true) ∧
  (∀ y, res = some y → s.obj y ≠ none → root = some y ∨
    ∃ q ∈ Ro s root, q ∉ W.map (·.1) ∧ kidOf s q y = true)

/-- A run's provenance: its writes and result, from its old entry y0. -/
def RunProv (s : Tree) (y0 : Option NodeId) (r : Run) : Prop :=
  ∃ W, r.a'.ws = W ++ r.a.ws ∧ SegProvW s y0 W r.res

/-- `planTree`'s provenance at every fuel below F. -/
def TreeProvIH (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ f < F, ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
    (acc' : Acc), SegPre cf i s g root ops acc → planTree cf i s f root g ops acc = some (res, acc') →
    ∃ W, acc'.ws = W ++ acc.ws ∧ SegProvW s root W res

theorem newKlongs_val {p : NodeId × Obj} {v : Nat} (h : p.2 = .val v) : newKlongs s p = [] := by
  unfold newKlongs; rw [h]

/-- A short compare value's run: values only, and a result that is a value
written or none. -/
theorem run_short_prov {c : Nat} {grp : List Op} {y0 : Option NodeId}
    {es0 es1 : List (Nat × NodeId)} {acc acc1 : Acc}
    (F : List (Nat × NodeId) × Acc → Op → List (Nat × NodeId) × Acc)
    (hq : grp.foldl F (es0, acc) = (es1, acc1))
    (hFp : ∀ q k hv, F q (.put k hv) =
      (setEntry c q.2.next q.1, q.2.fresh.2.write q.2.next (.val hv)))
    (hFd : ∀ q k, F q (.del k) = (removeEntry c q.1, q.2))
    (hfresh : ∀ z, acc.next ≤ z → s.obj z = none) (hne : grp ≠ []) :
    RunProv s y0 ⟨c, es1.lookup c, acc, acc1⟩ := by
  obtain ⟨W, h1, _, _, h4, _, h6, h7⟩ := d_fold c F hFp hFd es0 acc grp
  rw [hq] at h1 h4 h6 h7
  simp only at h1 h4 h6 h7
  refine ⟨W, h1, fun p hp c' y hk _ => ?_, fun y hy hs => ?_⟩
  · obtain ⟨v, hv⟩ := (h4 p hp).2
    rw [newKlongs_val hv] at hk
    cases hk
  · exfalso
    obtain ⟨lop, hlop⟩ : ∃ lop, grp.getLast? = some lop := by
      cases hl : grp.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
      | some lop => exact ⟨lop, rfl⟩
    simp only at hy
    cases lop with
    | put k hv =>
      obtain ⟨y', hy', hyW⟩ := h6 k hv hlop
      rw [hy'] at hy
      obtain rfl : y' = y := Option.some.inj hy
      exact hs (hfresh _ (h4 _ hyW).1.1)
    | del k =>
      rw [h7 k hlop] at hy
      cases hy

/-- A long compare value's run: the next segment's tree, by `TreeProvIH`. -/
theorem run_long_prov {f g c : Nat} {ops : List Op} {y0 : Option NodeId}
    {acc acc1 : Acc} {res : Option NodeId}
    (hIP : TreeProvIH cf i s (f + 1)) (hs : SOk cf i s)
    (hfresh : ∀ z, acc.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) (hc : isLong c = true)
    (hroot : ∀ y, y0 = some y →
      Shaped cf s (g + 1) (htIn cf s y) y ∧ Good s y 0 none ∧ (R s y).Nodup)
    (hp : planTree cf i s f y0 (g + 1) (ops.filter (fun op => segAt g op == c)) acc =
      some (res, acc1)) :
    RunProv s y0 ⟨c, res, acc, acc1⟩ := by
  have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
    have := (hops op hop).1
    simp only [keyOk, Bool.and_eq_true] at this
    exact this.1
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
  have hpre : SegPre cf i s (g + 1) y0 (ops.filter (fun op => segAt g op == c)) acc := by
    refine ⟨hs, hfresh, fun op hop => ⟨(hops op (mem_grp hop).1).1, ?_⟩, hroot⟩
    obtain ⟨hm1, hm2⟩ := mem_grp hop
    have he := endsAt_of_keyWf (hw op hm1) (hg op hm1)
    rw [hm2, hc] at he
    have := hg op hm1
    simp only [endsAt, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at he
    omega
  exact hIP f (Nat.lt_succ_self f) y0 (g + 1) _ acc res acc1 hpre hp

/-- `d_ag` (PeSeg.lean) with each run's provenance. -/
theorem d_ag' : ∀ (f g : Nat) (es0 : List (Nat × NodeId)) (cvs : List Nat)
    (ops : List Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    TreeIH cf i s f → TreeProvIH cf i s f → SOk cf i s → (∀ z, acc.next ≤ z → s.obj z = none) →
    (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    cvs.Nodup → (∀ c ∈ cvs, ∃ op ∈ ops, segAt g op = c) →
    (∀ c ∈ cvs, ∀ y0, es0.lookup c = some y0 → isLong c = true →
      Shaped cf s (g + 1) (htIn cf s y0) y0 ∧ Good s y0 0 none ∧ (R s y0).Nodup) →
    applyGroups cf i s f g es0 cvs ops acc = some (es, acc') →
    (∀ c, c ∉ cvs → es.lookup c = es0.lookup c) ∧
    ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cvs ∧
      ∀ r ∈ runs, (RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
        (es0.lookup r.c) r ∧ RunProv s (es0.lookup r.c) r) ∧ es.lookup r.c = r.res
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [applyGroups] at h
  | f + 1, g, es0, [], ops, acc, es, acc', _, _, _, _, _, _, _, _, h => by
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => rfl, [], rfl, rfl, by simp⟩
  | f + 1, g, es0, cv :: cvs, ops, acc, es, acc', hIH, hIP, hs, hfresh, hops, hnd, hne, hroot, h => by
    have hIH' : TreeIH cf i s f := fun f' hf' => hIH f' (by omega)
    have hIP' : TreeProvIH cf i s f := fun f' hf' => hIP f' (by omega)
    rw [List.nodup_cons] at hnd
    have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
      have := (hops op hop).1
      simp only [keyOk, Bool.and_eq_true] at this
      exact this.1
    have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
    have fin : ∀ (es1 : List (Nat × NodeId)) (acc1 : Acc) (res : Option NodeId),
        RunOk cf i s g (ops.filter (fun op => segAt g op == cv)) (es0.lookup cv)
          ⟨cv, res, acc, acc1⟩ → RunProv s (es0.lookup cv) ⟨cv, res, acc, acc1⟩ →
        acc.next ≤ acc1.next → (∀ a, a ≠ cv → es1.lookup a = es0.lookup a) →
        es1.lookup cv = res → applyGroups cf i s f g es1 cvs ops acc1 = some (es, acc') →
        (∀ c, c ∉ cv :: cvs → es.lookup c = es0.lookup c) ∧
        ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cv :: cvs ∧
          ∀ r ∈ runs, (RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
            (es0.lookup r.c) r ∧ RunProv s (es0.lookup r.c) r) ∧ es.lookup r.c = r.res := by
      intro es1 acc1 res hrun hrp hnext hlk hres h2
      obtain ⟨hout, runs, hch, hmap, hruns⟩ := d_ag' f g es1 cvs ops acc1 es acc' hIH' hIP' hs
        (fun z hz => hfresh z (by nomega)) hops hnd.2
        (fun c hc => hne c (List.mem_cons_of_mem _ hc))
        (fun c hc y0 hy0 hl => hroot c (List.mem_cons_of_mem _ hc) y0
          (by rw [← hlk c (fun h => hnd.1 (h ▸ hc))]; exact hy0) hl) h2
      refine ⟨fun a ha => ?_, ⟨cv, res, acc, acc1⟩ :: runs, ⟨rfl, hnext, hch⟩,
        by simp [hmap], ?_⟩
      · simp only [List.mem_cons, not_or] at ha
        rw [hout a ha.2, hlk a ha.1]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨⟨hrun, hrp⟩, by rw [hout cv hnd.1]; exact hres⟩
        · have hrc : r.c ∈ cvs := hmap ▸ List.mem_map_of_mem hr
          have hne' : r.c ≠ cv := fun h => hnd.1 (h ▸ hrc)
          obtain ⟨⟨a1, a0⟩, a2⟩ := hruns r hr
          rw [hlk r.c hne'] at a1 a0
          exact ⟨⟨a1, a0⟩, a2⟩
    unfold applyGroups at h
    simp only at h
    generalize hq : List.foldl _ (es0, acc) _ = q at h
    obtain ⟨es1, acc1⟩ := q
    simp only at h
    cases hcl : isLong cv with
    | false =>
      rw [(grp_short hw hg hcl).1] at hq
      obtain ⟨hrun, hnext, hlk⟩ := d_run_short (y0 := es0.lookup cv) _ hq
        (by intro q k hv; rfl) (by intro q k; rfl) hfresh hops (hne cv List.mem_cons_self) hcl
      have hrp := run_short_prov (y0 := es0.lookup cv) _ hq (by intro q k hv; rfl)
        (by intro q k; rfl) hfresh (by
          obtain ⟨op0, hop0, hc0⟩ := hne cv List.mem_cons_self
          intro h0
          have : op0 ∈ ops.filter (fun op => segAt g op == cv) :=
            List.mem_filter.mpr ⟨hop0, by simp [hc0]⟩
          rw [h0] at this
          simp at this)
      split at h
      · exact fin es1 acc1 _ hrun hrp hnext hlk rfl h
      · rename_i hsub
        exfalso
        apply hsub
        rw [(grp_short hw hg hcl).2]
        rfl
    | true =>
      rw [(grp_long hw hg hcl).1, List.foldl_nil, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      split at h
      · rename_i hsub
        exfalso
        rw [(grp_long hw hg hcl).2, List.isEmpty_iff] at hsub
        obtain ⟨op0, hop0, hc0⟩ := hne cv List.mem_cons_self
        have : op0 ∈ ops.filter (fun op => segAt g op == cv) :=
          List.mem_filter.mpr ⟨hop0, by simp [hc0]⟩
        rw [hsub] at this
        simp at this
      · split at h
        · cases h
        · rename_i y acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          have hrp := run_long_prov hIP hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 (some y) hrun hrp hnext
            (fun a ha => by rw [setEntry_lookup, ite_eq_right ha])
            (by rw [setEntry_lookup, ite_eq_left rfl]) h
        · rename_i acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          have hrp := run_long_prov hIP hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 none hrun hrp hnext
            (fun a ha => by rw [removeEntry_lookup, ite_eq_right ha])
            (by rw [removeEntry_lookup, ite_eq_left rfl]) h


/-- `f_hAG` (PeSeg.lean) with each run's provenance. -/
theorem f_hAG' (_hcf : cf.Ok) {f g : Nat} (IH : TreeIH cf i s f) (IP : TreeProvIH cf i s f)
    (hs : SOk cf i s) :
    ∀ f' < f, ∀ (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat)
      (ops : List Contract.Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
      s.obj x = some (.key n) → Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup →
      (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
      (∀ z, acc.next ≤ z → s.obj z = none) →
      applyGroups cf i s f' g (live n.ks) (touched g ops) ops acc = some (es, acc') →
      ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = touched g ops ∧
        ∀ r ∈ runs, (fun grp y0 r => RunOk cf i s g grp y0 r ∧ RunProv s y0 r)
          (ops.filter (fun op => segAt g op == r.c)) ((live n.ks).lookup r.c) r ∧
          es.lookup r.c = r.res := by
  intro f' hf' x n lo hi ops acc es acc' hobj hsh hg hnd hq hfr hap
  obtain ⟨_, runs, hch, hmap, hr⟩ := d_ag' f' g (live n.ks) (touched g ops) ops acc es acc'
    (f_ih_mono IH (by omega)) (fun f'' h => IP f'' (by omega)) hs hfr hq (nodup_touched g ops)
    (fun c hc => mem_touched.mp hc)
    (fun c _ y0 hy hl => f_long hobj hsh hg hnd c y0 (Contract.PE.lookup_mem hy) hl) hap
  exact ⟨runs, hch, hmap, hr⟩

/-- A node whose parent before is below segment g (a next segment's node). -/
def RpG (cf : Cfg) (s : Tree) (Xs : List NodeId) (g : Nat) (y : NodeId) : Prop :=
  ∃ q n, q ∈ Xs ∧ s.obj q = some (.key n) ∧ n.level < cf.lev g 0 ∧ kidOf s q y = true

/-- **applyGroups's provenance**: an old id of a leaf's entries after is a
live child before of the leaf, or a next segment's run moved it (its parent
before is below segment g). -/
theorem ag_prov (hcf : cf.Ok) (hs : SOk cf i s) {f : Nat} (hIH : TreeIH cf i s f)
    (hIP : TreeProvIH cf i s f) (Xs : List NodeId) : ∀ f' < f, AGProv cf i s Xs (RpG cf s Xs) f' := by
  intro f' hf' x n g lo hi ops acc es acc' hobj hsh hg hnd hXs hq hfr hap e he hse
  obtain ⟨runs, _, hmap, hr⟩ := f_hAG' hcf hIH hIP hs f' hf' x n lo hi ops acc es acc' hobj hsh hg
    hnd hq hfr hap
  obtain ⟨hsorted, hout⟩ := applyGroups_spec f' g _ _ ops acc es acc' hap (live_sorted n.ks)
  have hlk : es.lookup e.1 = some e.2 := lookup_of_mem hsorted he
  by_cases ht : e.1 ∈ touched g ops
  · rw [← hmap] at ht
    obtain ⟨r, hr', hrc⟩ := List.mem_map.mp ht
    obtain ⟨⟨_, W, _, _, hb⟩, hres⟩ := hr r hr'
    rw [hrc, hlk] at hres
    rcases hb e.2 hres.symm hse with h1 | ⟨q, hq', _, hk⟩
    · left
      exact kidOf_iff.mpr ⟨n, r.c, hobj, Contract.PE.lookup_mem h1⟩
    · right
      cases hy0 : (live n.ks).lookup r.c with
      | none => rw [hy0] at hq'; simp [Ro] at hq'
      | some y0 =>
        rw [hy0] at hq'
        obtain ⟨nq, cq, hobjq, _⟩ := kidOf_iff.mp hk
        have hE0 : content 0 (view 0 s x) = live n.ks := view_zero hobj
        have hm : (r.c, y0) ∈ content 0 (view 0 s x) := by
          rw [hE0]; exact Contract.PE.lookup_mem hy0
        have hqx : q ∈ R s x :=
          List.mem_of_mem_tail ((content_walks 0 hsh hg).subset
            (List.mem_flatMap.mpr ⟨_, hm, hq'⟩))
        exact ⟨q, nq, hXs q hqx, hobjq, walk_below 0 hsh hg _ hm q hq' nq hobjq, hk⟩
  · left
    rw [hout e.1 ht] at hlk
    exact kidOf_iff.mpr ⟨n, e.1, hobj, Contract.PE.lookup_mem hlk⟩

/-! ## The segments: facts of the final plan -/

/-- The bases of the planned nodes. -/
def basesOf (v : VN) : List NodeId := (nodesOf v).filterMap (·.1)

theorem basesOf_node (b : Option NodeId) (g h : Nat) (j : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec) :
    basesOf (.node b g h j es F dec) = b.toList ++ es.flatMap (fun e => basesOf e.2) := by
  simp only [basesOf, nodesOf, List.filterMap_cons, nodesL_eq, List.filterMap_flatMap]
  cases b <;> simp

/-- The bases of the planned nodes are old nodes they use, each once. -/
theorem basesOf_sub {g : Nat} : ∀ (h : Nat) {v : VN}, VOk cf s g h v → (basesOf v).Subperm (Ui s v)
  | _, .old y, _ => by simp [basesOf, nodesOf]
  | 0, .node b g' h' j es F dec, hv => by
    cases hv with
    | leaf hold _ _ =>
      rw [basesOf_node, Ui_node]
      have : es.flatMap (fun e => basesOf e.2) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro e he
        obtain ⟨y, hy⟩ := hold e he
        rw [hy]; rfl
      simp [this]
      exact List.Subperm.refl _
  | h + 1, .node b g' h' j es F dec, hv => by
    cases hv with
    | inner hk _ _ _ _ =>
      rw [basesOf_node, Ui_node]
      simp only [Nat.add_one_ne_zero, ite_false]
      exact (List.Subperm.refl _).append (flatMap_subperm es (fun e he => basesOf_sub h (hk e he)))

/-- The bases of the planned nodes are shaped at segment g. -/
theorem bases_shaped {g : Nat} : ∀ (h : Nat) {v : VN}, VOk cf s g h v → EOk cf i s g h v →
    ∀ b ∈ basesOf v, ∃ h', Shaped cf s g h' b
  | _, .old y, _, _ => by simp [basesOf, nodesOf]
  | 0, .node b g' h' j es F dec, hv, he => by
    cases hv with
    | leaf hold _ _ =>
      cases he with
      | node _ hb _ _ =>
        intro x hx
        rw [basesOf_node] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨0, hb x (Option.mem_toList.mp hx)⟩
        · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
          obtain ⟨y, hy⟩ := hold e he
          rw [hy] at hx; simp [basesOf, nodesOf] at hx
  | h + 1, .node b g' h' j es F dec, hv, he => by
    cases hv with
    | inner hk _ _ _ _ =>
      cases he with
      | node _ hb _ hke =>
        intro x hx
        rw [basesOf_node] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨h + 1, hb x (Option.mem_toList.mp hx)⟩
        · obtain ⟨e, hm, hx⟩ := List.mem_flatMap.mp hx
          exact bases_shaped h (hk e hm) (hke e hm (by omega)) x hx

theorem mem_basesOf {v : VN} {u : Option NodeId × Dec × List (Nat × VN)} (hu : u ∈ nodesOf v)
    {b : NodeId} (hb : u.1 = some b) : b ∈ basesOf v :=
  List.mem_filterMap.mpr ⟨u, hu, hb⟩

/-- Two planned nodes with one base are one. -/
theorem nodes_base_unique {v : VN} (hnd : (basesOf v).Nodup)
    {u u' : Option NodeId × Dec × List (Nat × VN)} (hu : u ∈ nodesOf v) (hu' : u' ∈ nodesOf v)
    {b : NodeId} (hb : u.1 = some b) (hb' : u'.1 = some b) : u = u' := by
  unfold basesOf at hnd
  generalize nodesOf v = l at hnd hu hu'
  induction l with
  | nil => simp at hu
  | cons a l ih =>
    rw [List.filterMap_cons] at hnd
    have hnd' : (l.filterMap (·.1)).Nodup := by
      cases ha : a.1 with
      | none => rw [ha] at hnd; exact hnd
      | some x => rw [ha] at hnd; exact (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp hu with h1 | h1
    · rcases List.mem_cons.mp hu' with h2 | h2
      · rw [h1, h2]
      · exfalso
        subst h1
        rw [hb] at hnd
        exact (List.nodup_cons.mp hnd).1 (List.mem_filterMap.mpr ⟨u', h2, hb'⟩)
    · rcases List.mem_cons.mp hu' with h2 | h2
      · exfalso
        subst h2
        rw [hb'] at hnd
        exact (List.nodup_cons.mp hnd).1 (List.mem_filterMap.mpr ⟨u, h1, hb⟩)
      · exact ih hnd' h1 h2

/-- The kept children of planned nodes: of segment g (an inner node's), or
payloads. -/
theorem kids_shaped_or_pay {g : Nat} : ∀ (h : Nat) {v : VN}, VOk cf s g h v → EOk cf i s g h v →
    ∀ u ∈ nodesOf v, ∀ y ∈ kidIds u.2.2, (∃ h', Shaped cf s g h' y) ∨ ∃ c, (c, y) ∈ pays v
  | _, .old y, _, _ => by simp [nodesOf]
  | 0, .node b g' h' j es F dec, hv, he => by
    cases hv with
    | leaf hold _ _ =>
      intro u hu y hy
      simp only [nodesOf, List.mem_cons] at hu
      rcases hu with rfl | hu
      · right
        obtain ⟨e, he', hk⟩ := List.mem_filterMap.mp hy
        obtain ⟨z, hz⟩ := hold e he'
        rw [hz] at hk
        simp only [kidId, Option.some.injEq] at hk
        subst hk
        refine ⟨e.1, ?_⟩
        rw [pays_node]
        simp only [ite_true, List.mem_map]
        exact ⟨e, he', by rw [hz]; rfl⟩
      · exfalso
        rw [nodesL_eq] at hu
        obtain ⟨e, he', hu⟩ := List.mem_flatMap.mp hu
        obtain ⟨z, hz⟩ := hold e he'
        rw [hz] at hu; simp [nodesOf] at hu
  | h + 1, .node b g' h' j es F dec, hv, he => by
    cases hv with
    | inner hk _ _ _ _ =>
      cases he with
      | node _ _ _ hke =>
        intro u hu y hy
        simp only [nodesOf, List.mem_cons] at hu
        rcases hu with rfl | hu
        · left
          obtain ⟨e, he', hkk⟩ := List.mem_filterMap.mp hy
          have hee := hke e he' (by omega)
          cases hw : e.2 with
          | old z =>
            rw [hw] at hkk hee
            simp only [kidId, Option.some.injEq] at hkk
            subst hkk
            cases hee with | old hsh => exact ⟨h, hsh⟩
          | node bb gg hh jj ee FF dd =>
            rw [hw] at hkk hee
            cases bb with
            | none => simp [kidId] at hkk
            | some bb =>
              have hby : bb = y := by
                simp only [kidId] at hkk; split at hkk
                · cases hkk
                · exact Option.some.inj hkk
              subst hby
              cases hee with | node _ hb _ _ => exact ⟨h, hb bb rfl⟩
        · rw [nodesL_eq] at hu
          obtain ⟨e, he', hu⟩ := List.mem_flatMap.mp hu
          rcases kids_shaped_or_pay h (hk e he') (hke e he' (by omega)) u hu y hy with h1 | ⟨c, hc⟩
          · exact Or.inl h1
          · right
            refine ⟨c, ?_⟩
            rw [pays_node]
            simp only [Nat.add_one_ne_zero, ite_false, List.mem_flatMap]
            exact ⟨e, he', hc⟩

/-- The kept id of a planned root: of segment g. -/
theorem kidId_shaped {g h : Nat} {v : VN} (he : EOk cf i s g h v) {y : NodeId}
    (hy : kidId v = some y) : ∃ h', Shaped cf s g h' y := by
  cases v with
  | old z =>
    simp only [kidId, Option.some.injEq] at hy
    subst hy
    cases he with | old hsh => exact ⟨h, hsh⟩
  | node b g' h' j es F dec =>
    cases b with
    | none => simp [kidId] at hy
    | some bb =>
      have : bb = y := by
        simp only [kidId] at hy; split at hy
        · cases hy
        · exact Option.some.inj hy
      subst this
      cases he with | node _ hb _ _ => exact ⟨h, hb bb rfl⟩

/-- An entry of a segment tree's old leaf level is a live child before of one
of its leaves. -/
theorem content_parent : ∀ (h : Nat) {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Shaped cf s g h x → Good s x lo hi → ∀ e ∈ content h (view h s x),
    ∃ l n, l ∈ R s x ∧ s.obj l = some (.key n) ∧ n.level = cf.lev g 0 ∧ e ∈ live n.ks
  | 0, g, x, lo, hi, hsh, hg => by
    obtain ⟨n0, hobj, _, hlev, _, _⟩ := hsh.inv_leaf
    intro e he
    have he' : e ∈ live n0.ks := by
      have : e ∈ view 0 s x := he
      rwa [view_zero hobj] at this
    exact ⟨x, n0, mem_reachAt_self' _ _ _, hobj, hlev, he'⟩
  | h + 1, g, x, lo, hi, hsh, hg => by
    obtain ⟨n0, hobj, hleaf, _, _, _, _, hk⟩ := hsh.inv_inner
    intro e he
    rw [content_view_succ hobj, List.mem_flatMap] at he
    obtain ⟨⟨c, y⟩, hcy, he⟩ := he
    obtain ⟨m, lo', hi', _, _, _, hg'⟩ := hg.child hobj hcy (by simp [hleaf])
    obtain ⟨l, n, hl, h1, h2, h3⟩ := content_parent h (hk c y hcy) hg' e he
    refine ⟨l, n, ?_, h1, h2, h3⟩
    rw [R_shaped hsh hobj]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(c, y), hcy, hl⟩)

/-- `f_old` (PeSeg.lean) with each run's provenance. -/
theorem f_old' (hcf : cf.Ok) {f g h : Nat} {r : NodeId} {ops : List Contract.Op} {acc acc1 : Acc}
    {v : VN} (IH : TreeIH cf i s f) (IP : TreeProvIH cf i s f) (hpre : SegPre cf i s g (some r) ops acc)
    (hsh : Shaped cf s g h r) (hg : Good s r 0 none) (hnd : (R s r).Nodup)
    (hp : plan cf i s f r g h ops acc = some (v, acc1)) :
    ∃ runs, OldSeg cf s g (some r) (content h (view h s r)) ∧
      PlanSeg cf i s g (some r) (content h (view h s r)) ops h v runs acc acc1 ∧
      ∀ rr ∈ runs, RunProv s ((content h (view h s r)).lookup rr.c) rr := by
  obtain ⟨sops, runs, hplan, hcv, hvok, hch, hperm, hsops, hrun, hout⟩ :=
    plan_runs hcf (fun grp y0 r => RunOk cf i s g grp y0 r ∧ RunProv s y0 r)
      (fun op => keyOk cf op.key = true ∧ g < op.key.length)
      (f_hAG' hcf IH IP hpre.sok) r h ops acc v acc1 0 none hp hsh hg hnd hpre.ops hpre.fresh
  obtain ⟨heok, hown, _, hunt⟩ := plan_own hcf hp hsh hg
  have hwfe := (view_wfe h hg hsh).1
  have hopsB : ∀ op ∈ sops, 0 ≤ op.cv ∧ Below op.cv none :=
    fun _ _ => ⟨Nat.zero_le _, trivial⟩
  refine ⟨runs, ?_, ?_, fun rr hrr => (hrun rr hrr).2⟩
  · exact
      { sorted := view_sorted h hg hsh
        pay := view_pay h hg hsh
        nodup := hnd
        walks := ((content_walks h hsh hg).trans (List.tail_sublist _)).subperm
        exist := fun z hz => reach_exists _ hg z hz
        below := walk_below h hsh hg
        keys := view_L_pays h hg hsh }
  · exact
      { vok := hvok
        eok := heok
        sops := ⟨sops, Plan.keys h 0 none _ _ _ hplan (f_holds h hsh hg) hopsB, hcv, hsops⟩
        wfe := Plan.wf h 0 none _ _ _ hplan hwfe hopsB
        own := hown
        untouched := hunt
        chain := hch
        perm := hperm
        run := fun rr hrr => (hrun rr hrr).1
        outUi := hout }

/-- A virtual node's final list and decision (for a planned node). -/
def VN.F' : VN → List (Nat × Option NodeId)
  | .old _ => []
  | .node _ _ _ _ _ F _ => F

def VN.dec' : VN → Dec
  | .old _ => .same
  | .node _ _ _ _ _ _ d => d

/-- `f_new` (PeSeg.lean) with each run's provenance. -/
theorem f_new' (hcf : cf.Ok) {f g : Nat} {ops : List Contract.Op} {acc acc1 : Acc} {v : VN}
    {es : List (Nat × NodeId)} (IH : TreeIH cf i s f) (IP : TreeProvIH cf i s f) (hpre : SegPre cf i s g none ops acc)
    (hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc1))
    (hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    ∃ runs, OldSeg cf s g none [] ∧ PlanSeg cf i s g none [] ops 0 v runs acc acc1 ∧
      (∀ rr ∈ runs, RunProv s (([] : List (Nat × NodeId)).lookup rr.c) rr) ∧
      v = .node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) v.F' v.dec' := by
  obtain ⟨_, runs, hch, hmap, hrun⟩ := d_ag' f g [] (touched g ops) ops acc es acc1 IH IP
    hpre.sok hpre.fresh hpre.ops (nodup_touched g ops) (fun c hc => mem_touched.mp hc)
    (by intro c _ y0 h; simp at h) hag
  obtain ⟨heok, hui, hpo, htch, _⟩ := plan_new_own hag hmk
  obtain ⟨⟨F, dec, rfl⟩, hvok⟩ := mkNode_leaf hcf hmk (by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨a, _, rfl⟩ := he
    exact ⟨_, rfl⟩)
  obtain ⟨hsorted, hlk⟩ := applyGroups_spec f g [] _ ops acc es acc1 hag List.Pairwise.nil
  have habs : absV s 0 (.node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) F dec) = es := by
    show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    apply List.map_congr_left
    intro e _
    rfl
  refine ⟨runs, ?_, ?_, fun rr hrr => (hrun rr hrr).1.2, rfl⟩
  · exact
      { sorted := List.Pairwise.nil
        pay := by simp
        nodup := List.nodup_nil
        walks := by simp [Ro]
        exist := by simp [Ro]
        below := by simp
        keys := rfl }
  · refine
      { vok := hvok
        eok := heok
        sops := ⟨finalOps (touched g ops) es, ?_, finalOps_cv _ _, ?_⟩
        wfe := ?_
        own := ?_
        untouched := fun p hp ht => absurd (htch p hp) ht
        chain := hch
        perm := by rw [hmap]
        run := fun r hr => (hrun r hr).1.1
        outUi := ?_ }
    · show absV s 0 _ = _
      rw [habs]
      exact (applyOps_finalOps (touched g ops) [] es List.Pairwise.nil hsorted
        (fun c hc => hlk c hc)).symm
    · intro o ho
      simp only [finalOps, List.mem_map] at ho
      obtain ⟨c, hc, rfl⟩ := ho
      rw [← hmap] at hc
      simp only [List.mem_map] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      refine ⟨r, hr, ?_, ?_⟩
      · split <;> rfl
      · rw [(hrun r hr).2]
        cases r.res <;> rfl
    · rw [habs]
      by_cases he : es = []
      · exact Or.inl he
      · exact Or.inr ⟨he, hsorted, fun e _ => ⟨Nat.zero_le _, trivial⟩⟩
    · rw [hui, hpo]
      exact List.nil_subperm
    · intro r _ y0 hy0
      simp at hy0


/-! ## The segments: a segment's step -/

/-- The runs' writes: their key klongs' provenance, and a node of a run's old
part that the run does not write is written by no run. -/
theorem runs_prov {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)} {ops : List Op}
    {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hrp : ∀ r ∈ runs, RunProv s (E.lookup r.c) r) :
    ∃ Wr, acc1.ws = Wr ++ acc0.ws ∧
      (∀ p ∈ Wr, ∀ n, s.obj p.1 = some (.key n) → n.level < cf.lev g 0) ∧
      (∀ p ∈ Wr, ∀ c y, Klong.key c y ∈ newKlongs s p → s.obj y ≠ none →
        (∃ n c', s.obj p.1 = some (.key n) ∧ (c', y) ∈ live n.ks) ∨
        ∃ q n, q ∈ Ro s root ∧ s.obj q = some (.key n) ∧ n.level < cf.lev g 0 ∧
          q ∉ Wr.map (·.1) ∧ kidOf s q y = true) ∧
      (∀ r ∈ runs, ∀ y, r.res = some y → s.obj y ≠ none → E.lookup r.c = some y ∨
        ∃ q n, q ∈ Ro s root ∧ s.obj q = some (.key n) ∧ n.level < cf.lev g 0 ∧
          q ∉ Wr.map (·.1) ∧ kidOf s q y = true) := by
  obtain ⟨Wr, hWr, hWrun, hWmem⟩ := e_runs_W hfresh ho hp
  have hEex : ∀ e ∈ E, ∀ z ∈ R s e.2, z ∈ Ro s root := fun e he z hz =>
    ho.walks.subset (List.mem_flatMap.mpr ⟨e, he, hz⟩)
  -- a run's witness: in the old tree, below segment g, written by no run
  have wit : ∀ r ∈ runs, ∀ Wk, WOkV i s (Ro s (E.lookup r.c)) r.a r.a' Wk →
      ∀ q y, q ∈ Ro s (E.lookup r.c) → q ∉ Wk.map (·.1) → kidOf s q y = true →
      ∃ q n, q ∈ Ro s root ∧ s.obj q = some (.key n) ∧ n.level < cf.lev g 0 ∧
        q ∉ Wr.map (·.1) ∧ kidOf s q y = true := by
    intro r hr Wk hWk q y hq hqW hk
    cases hl : E.lookup r.c with
    | none => rw [hl] at hq; simp [Ro] at hq
    | some y0 =>
      rw [hl] at hq
      have hE := Contract.PE.lookup_mem hl
      obtain ⟨n, c', hobj, _⟩ := kidOf_iff.mp hk
      refine ⟨q, n, hEex _ hE q hq, hobj, ho.below _ hE q hq n hobj, fun hm => ?_, hk⟩
      obtain ⟨p, hpW, hpq⟩ := List.mem_map.mp hm
      obtain ⟨Wk', hWk', _, _, hown⟩ := hWrun r hr
      have hpk : p ∈ Wk' := hown p hpW (by rw [hpq, hl]; exact hq)
      rw [e_wokv_unique hWk' hWk] at hpk
      exact hqW (List.mem_map.mpr ⟨p, hpk, hpq⟩)
  refine ⟨Wr, hWr.ws, fun p hp n hpn => ?_, fun p hpW c y hk hsy => ?_, fun r hr y hy hsy => ?_⟩
  · rcases hWr.ids p.1 (List.mem_map_of_mem hp) with ⟨hlo, _⟩ | hU
    · rw [hfresh _ hlo] at hpn; cases hpn
    · obtain ⟨r, _, hzr⟩ := List.mem_flatMap.mp hU
      cases hl : E.lookup r.c with
      | none => rw [hl] at hzr; simp [Ro] at hzr
      | some y0 =>
        rw [hl] at hzr
        exact ho.below _ (Contract.PE.lookup_mem hl) _ hzr n hpn
  · obtain ⟨r, hr, Wk, hWk, _, _, _, hpk⟩ := hWmem p hpW
    obtain ⟨W', hW', ha, _⟩ := hrp r hr
    have hWW : W' = Wk := List.append_cancel_right (hW'.symm.trans hWk.ws)
    subst hWW
    rcases ha p hpk c y hk hsy with h1 | ⟨q, hq, hqW, hkq⟩
    · exact Or.inl h1
    · exact Or.inr (wit r hr W' hWk q y hq hqW hkq)
  · obtain ⟨Wk, hWk, _, _, _⟩ := hWrun r hr
    obtain ⟨W', hW', _, hb⟩ := hrp r hr
    have hWW : W' = Wk := List.append_cancel_right (hW'.symm.trans hWk.ws)
    subst hWW
    rcases hb y hy hsy with h1 | ⟨q, hq, hqW, hkq⟩
    · exact Or.inl h1
    · exact Or.inr (wit r hr W' hWk q y hq hqW hkq)

/-- TREE in an old segment tree: two key nodes of it with one live child are
one. -/
theorem ro_one_parent (hlev : LevOK s) {root : Option NodeId} (hnd : (Ro s root).Nodup)
    {x1 x2 y : NodeId} (h1 : x1 ∈ Ro s root) (h2 : x2 ∈ Ro s root) (k1 : kidOf s x1 y = true)
    (k2 : kidOf s x2 y = true) : x1 = x2 := by
  cases root with
  | none => simp [Ro] at h1
  | some r =>
    simp only [Ro, R] at h1 h2 hnd
    obtain ⟨n1, c1, hn1, hc1⟩ := kidOf_iff.mp k1
    obtain ⟨n2, c2, hn2, hc2⟩ := kidOf_iff.mp k2
    cases hr : s.obj r with
    | none =>
      have : s.fuel r = 0 := by simp [Tree.fuel, hr]
      rw [this] at h1 h2
      simp [reachAt] at h1 h2
      rw [h1, h2]
    | some o =>
      cases o with
      | val v =>
        have : s.fuel r = 0 := by simp [Tree.fuel, hr]
        rw [this] at h1 h2
        simp [reachAt] at h1 h2
        rw [h1, h2]
      | key nr =>
        have hf : s.fuel r = nr.level + 1 := by simp [Tree.fuel, hr]
        rw [hf] at h1 h2 hnd
        exact reachAt_one_parent hlev (nr.level + 1) r (.key nr) hr (by simp [lvl]) hnd x1 x2 n1 n2
          c1 c2 y h1 h2 hn1 hn2 hc1 hc2

theorem lev_le (cf : Cfg) (g h : Nat) : cf.lev g 0 ≤ cf.lev g h := by
  unfold Cfg.lev; omega

/-- **A segment's step with a new root**: from the plan's provenance, the
runs' and emit's. -/
theorem seg_prov_some (hcf : cf.Ok) {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v v' : VN} {runs : List Run} {acc0 acc1 acc2 : Acc} {space : Bool}
    {c0 y : NodeId} (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none) (hlev : LevOK s)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hrp : ∀ r ∈ runs, RunProv s (E.lookup r.c) r)
    (hEp : ∀ e ∈ E, ∃ l n, l ∈ Ro s root ∧ s.obj l = some (.key n) ∧ n.level = cf.lev g 0 ∧
      e ∈ live n.ks)
    (hKP : ∃ C, KidsProv s C (RpG cf s (Ro s root) g) (nodesOf v) ∧ (∀ q ∈ C, q ∉ Ui s v) ∧
      (∀ q ∈ C, q ∈ Ro s root))
    (hkid : ∀ y, kidId v = some y → s.obj y ≠ none → root = some y)
    (hset : settleRoot cf i s f g v space = some (some v'))
    (he : emit cf i s v' acc1 = some ([(c0, y)], acc2)) :
    ∃ W, acc2.ws = W ++ acc0.ws ∧ SegProvW s root W (some y) := by
  obtain ⟨Wr, hWr, hWrdeep, hWra, hWrb⟩ := runs_prov hfresh ho hp hrp
  have h01 : acc0.next ≤ acc1.next := chain_next hp.chain
  have hE's : (content h (absV s h v)).Pairwise CvLtA := e_content_sorted hp.wfe
  have hPs : (pays v).Pairwise CvLtA := hE's.sublist (pays_sublist h hp.vok)
  obtain ⟨h', hroot, hrok', heok', hB', hpv', _⟩ :=
    settle_root_own hcf (Or.inr hp.vok) hp.eok (e_hB hp hPs) hset
  have hvok' : VOk cf s g h' v' := settle_vok hcf hp.vok hset hrok'
  have hBnd := e_B_nodup ho hfresh (acc1.next - acc0.next)
  have hUnd' : (Ui s v').Nodup :=
    e_subperm_nodup ((List.sublist_append_left _ _).subperm.trans hB') hBnd
  have hUiR : ∀ z ∈ Ui s v, z ∈ Ro s root := fun z hz => hp.own.subset (List.mem_append_left _ hz)
  have hUnd : (Ui s v).Nodup :=
    e_subperm_nodup ((List.sublist_append_left _ _).subperm.trans hp.own) ho.nodup
  obtain ⟨C, hkp, hCU, hCR⟩ := hKP
  obtain ⟨C', b1, b2, ⟨kp', _, cu'⟩, b4, b5⟩ := settle_prov f g space h v v' hp.eok hset C
    ⟨hkp, hUnd, hCU⟩
  have hC'R : ∀ q ∈ C', q ∈ Ro s root := by
    intro q hq
    rcases b2 q hq with h1 | h1
    · exact hCR q h1
    · exact hUiR q h1
  have hfresh1 : ∀ x, acc1.next ≤ x → s.obj x = none := fun x hx => hfresh x (le_trans h01 hx)
  obtain ⟨We, hWe, _, hwe, hke, hEe⟩ := emit_prov v' hfresh1 he
  have hbnd : (basesOf v').Nodup := e_subperm_nodup (basesOf_sub h' hvok') hUnd'
  -- emit's old writes: bases decided append, of segment g
  have hWesg : ∀ p ∈ We, ∀ n, s.obj p.1 = some (.key n) → cf.lev g 0 ≤ n.level := by
    intro p hp n hpn
    rcases hwe p hp with ⟨hlo, _⟩ | ⟨u, hu, hb, _⟩
    · rw [hfresh1 _ hlo] at hpn; cases hpn
    · obtain ⟨h'', hsh⟩ := bases_shaped h' hvok' heok' _ (mem_basesOf hu hb)
      obtain ⟨n', hn', hl', _⟩ := shaped_obj hsh
      rw [hpn] at hn'
      obtain rfl : n = n' := by injection hn' with h1; injection h1
      rw [hl']; exact lev_le cf g h''
  have hWeUi : ∀ p ∈ We, s.obj p.1 ≠ none → p.1 ∈ Ui s v' := by
    intro p hp hsp
    rcases hwe p hp with ⟨hlo, _⟩ | ⟨u, hu, hb, _⟩
    · exact absurd (hfresh1 _ hlo) hsp
    · exact (basesOf_sub h' hvok').subset (mem_basesOf hu hb)
  -- a node of segment g or above is written by no run
  have notWr : ∀ q n, s.obj q = some (.key n) → cf.lev g 0 ≤ n.level → q ∉ Wr.map (·.1) := by
    intro q n hq hl hm
    obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp hm
    have := hWrdeep p hpW n hq
    omega
  -- a node below segment g is written by no emit
  have notWe : ∀ q n, s.obj q = some (.key n) → n.level < cf.lev g 0 → q ∉ We.map (·.1) := by
    intro q n hq hl hm
    obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp hm
    have := hWesg p hpW n hq
    omega
  -- the deep case: an old kept child whose parent is below segment g
  have deep : ∀ u ∈ nodesOf v', ∀ yy ∈ kidIds u.2.2, s.obj yy ≠ none →
      ∀ q n, q ∈ Ro s root → s.obj q = some (.key n) → n.level < cf.lev g 0 → kidOf s q yy = true →
      ∃ q', q' ∈ Ro s root ∧ q' ∉ (We ++ Wr).map (·.1) ∧ kidOf s q' yy = true := by
    intro u hu yy hyy hsy q n hqR hq hql hk
    have hEcontra : ∀ c, (c, yy) ∈ E → False := by
      intro c hc
      obtain ⟨l, nl, hlR, hl, hll, hlc⟩ := hEp _ hc
      have := ro_one_parent hlev ho.nodup hlR hqR (kidOf_iff.mpr ⟨nl, c, hl, hlc⟩) hk
      subst this
      rw [hl] at hq
      obtain rfl : nl = n := by injection hq with h1; injection h1
      omega
    rcases kids_shaped_or_pay h' hvok' heok' u hu yy hyy with ⟨h'', hsh⟩ | ⟨c, hc⟩
    · exfalso
      obtain ⟨ny, hny, hly, _⟩ := shaped_obj hsh
      obtain ⟨n', c', hq', hc'⟩ := kidOf_iff.mp hk
      rw [hq] at hq'
      obtain rfl : n = n' := by injection hq' with h1; injection h1
      obtain ⟨oy, hoy, hlt⟩ := hlev q n hq c' yy (live_mem_key hc')
      rw [hny] at hoy
      obtain rfl : oy = .key ny := (Option.some.inj hoy).symm
      have := lev_le cf g h''
      simp only [lvl] at hlt
      omega
    · have hcv : (c, yy) ∈ content h (absV s h v) := pays_absV h hp.eok _ (hpv' _ hc)
      have hlk := lookup_of_mem hE's hcv
      simp only at hlk
      by_cases ht : c ∈ touched g ops
      · obtain ⟨r, hr, hrc⟩ := e_run_of_touched hp ht
        have hres := e_run_res hp hr
        rw [hrc, hlk] at hres
        rcases hWrb r hr yy hres.symm hsy with h1 | ⟨q', n', hq'R, hq', hq'l, hq'W, hk'⟩
        · exact absurd (Contract.PE.lookup_mem (hrc ▸ h1)) (hEcontra c)
        · refine ⟨q', hq'R, fun hm => ?_, hk'⟩
          rw [List.map_append] at hm
          rcases List.mem_append.mp hm with hm | hm
          · exact notWe q' n' hq' hq'l hm
          · exact hq'W hm
      · have := e_out_res hp ht
        rw [hlk] at this
        exact absurd (Contract.PE.lookup_mem this.symm) (hEcontra c)
  refine ⟨We ++ Wr, by rw [hWe, hWr, List.append_assoc], fun p hpW c yy hk hsy => ?_,
    fun yy hyy hsy => ?_⟩
  · rcases List.mem_append.mp hpW with hpW | hpW
    · -- a node emit writes
      rcases hke p hpW c yy hk with ⟨hlo, _⟩ | ⟨u, hu, hyu, hpu⟩
      · exact absurd (hfresh1 _ hlo) hsy
      · rcases kp' u hu yy hyu hsy with ⟨x, hx, hkx⟩ | ⟨q, hq, hkq⟩ | ⟨q, n, hqR, hq, hql, hkq⟩
        · rcases hpu with hpu | hpu
          · rw [hx] at hpu
            obtain rfl : x = p.1 := Option.some.inj hpu
            obtain ⟨n, c', hn, hc'⟩ := kidOf_iff.mp hkx
            exact Or.inl ⟨n, c', hn, hc'⟩
          · -- a base cut into parts: neither emit nor a run writes it
            right
            have hxb : x ∈ basesOf v' := mem_basesOf hu hx
            obtain ⟨h'', hsh⟩ := bases_shaped h' hvok' heok' x hxb
            obtain ⟨nx, hnx, hlx, _⟩ := shaped_obj hsh
            refine ⟨x, hUiR x (b4 x ((basesOf_sub h' hvok').subset hxb)), fun hm => ?_, hkx⟩
            rw [List.map_append] at hm
            rcases List.mem_append.mp hm with hm | hm
            · obtain ⟨p', hp', hpx⟩ := List.mem_map.mp hm
              rcases hwe p' hp' with ⟨hlo, _⟩ | ⟨u', hu', hb', hap⟩
              · rw [hpx] at hlo; rw [hfresh1 _ hlo] at hnx; cases hnx
              · rw [hpx] at hb'
                have := nodes_base_unique hbnd hu hu' hx hb'
                subst this
                rw [hap] at hpu
                cases hpu
            · exact notWr x nx hnx (by rw [hlx]; exact lev_le cf g h'') hm
        · -- a consumed node
          obtain ⟨nq, cq, hnq, _⟩ := kidOf_iff.mp hkq
          by_cases hql : cf.lev g 0 ≤ nq.level
          · right
            refine ⟨q, hC'R q hq, fun hm => ?_, hkq⟩
            rw [List.map_append] at hm
            rcases List.mem_append.mp hm with hm | hm
            · obtain ⟨p', hp', hpx⟩ := List.mem_map.mp hm
              have := hWeUi p' hp' (by rw [hpx, hnq]; simp)
              rw [hpx] at this
              exact cu' q hq this
            · exact notWr q nq hnq hql hm
          · obtain ⟨q', h1, h2, h3⟩ := deep u hu yy hyu hsy q nq (hC'R q hq) hnq (by omega) hkq
            exact Or.inr ⟨q', h1, h2, h3⟩
        · obtain ⟨q', h1, h2, h3⟩ := deep u hu yy hyu hsy q n hqR hq hql hkq
          exact Or.inr ⟨q', h1, h2, h3⟩
    · -- a node a run writes
      rcases hWra p hpW c yy hk hsy with h1 | ⟨q, n, hqR, hq, hql, hqW, hkq⟩
      · exact Or.inl h1
      · right
        refine ⟨q, hqR, fun hm => ?_, hkq⟩
        rw [List.map_append] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact notWe q n hq hql hm
        · exact hqW hm
  · -- the new root
    simp only [Option.some.injEq] at hyy
    subst hyy
    rcases hEe (c0, y) (by simp) with ⟨hlo, _⟩ | hk
    · exact absurd (hfresh1 _ hlo) hsy
    · obtain ⟨h'', hsh⟩ := kidId_shaped heok' hk
      obtain ⟨ny, hny, hly, _⟩ := shaped_obj hsh
      have hyl := lev_le cf g h''
      rcases b5 y hk hsy with h1 | ⟨q, hq, hkq⟩ | ⟨q, n, _, hq, hql, hkq⟩
      · exact Or.inl (hkid y h1 hsy)
      · right
        obtain ⟨nq, cq, hnq, hcq⟩ := kidOf_iff.mp hkq
        obtain ⟨oy, hoy, hlt⟩ := hlev q nq hnq cq y (live_mem_key hcq)
        rw [hny] at hoy
        obtain rfl : oy = .key ny := (Option.some.inj hoy).symm
        simp only [lvl] at hlt
        refine ⟨q, hC'R q hq, fun hm => ?_, hkq⟩
        rw [List.map_append] at hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨p', hp', hpx⟩ := List.mem_map.mp hm
          have := hWeUi p' hp' (by rw [hpx, hnq]; simp)
          rw [hpx] at this
          exact cu' q hq this
        · exact notWr q nq hnq (by omega) hm
      · exfalso
        obtain ⟨n', cq, hq', hcq⟩ := kidOf_iff.mp hkq
        rw [hq] at hq'
        obtain rfl : n = n' := by injection hq' with h1; injection h1
        obtain ⟨oy, hoy, hlt⟩ := hlev q n hq cq y (live_mem_key hcq)
        rw [hny] at hoy
        obtain rfl : oy = .key ny := (Option.some.inj hoy).symm
        simp only [lvl] at hlt
        omega

/-- **A segment's step with no tree after**: the runs' writes only. -/
theorem seg_prov_none {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hrp : ∀ r ∈ runs, RunProv s (E.lookup r.c) r) :
    ∃ W, acc1.ws = W ++ acc0.ws ∧ SegProvW s root W none := by
  obtain ⟨Wr, hWr, _, hWra, _⟩ := runs_prov hfresh ho hp hrp
  refine ⟨Wr, hWr, fun p hpW c y hk hsy => ?_, fun y hy => by cases hy⟩
  rcases hWra p hpW c y hk hsy with h1 | ⟨q, _, hqR, _, _, hqW, hkq⟩
  · exact Or.inl h1
  · exact Or.inr ⟨q, hqR, hqW, hkq⟩

/-- One step of the induction: `planTree` at fuel f + 1 from `TreeIH` and
`TreeProvIH` at f. -/
theorem fp_step (hcf : cf.Ok) (hlev : LevOK s) {f : Nat} (IH : TreeIH cf i s f)
    (IP : TreeProvIH cf i s f) :
    ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
    (acc' : Acc), SegPre cf i s g root ops acc →
    planTree cf i s (f + 1) root g ops acc = some (res, acc') →
    ∃ W, acc'.ws = W ++ acc.ws ∧ SegProvW s root W res := by
  intro root g ops acc res acc' hpre hpt
  -- the tail: settled, emitted
  have tail : ∀ {h : Nat} {E : List (Nat × NodeId)} {v : VN} {runs : List Run} {acc1 : Acc},
      OldSeg cf s g root E → PlanSeg cf i s g root E ops h v runs acc acc1 →
      (∀ r ∈ runs, RunProv s (E.lookup r.c) r) →
      (∀ e ∈ E, ∃ l n, l ∈ Ro s root ∧ s.obj l = some (.key n) ∧ n.level = cf.lev g 0 ∧
        e ∈ live n.ks) →
      (∃ C, KidsProv s C (RpG cf s (Ro s root) g) (nodesOf v) ∧ (∀ q ∈ C, q ∉ Ui s v) ∧
        (∀ q ∈ C, q ∈ Ro s root)) →
      (∀ y, kidId v = some y → s.obj y ≠ none → root = some y) →
      (match settleRoot cf i s f g v false with
        | none => none
        | some none => some (none, acc1)
        | some (some v) =>
          match emit cf i s v acc1 with
          | some ([(_, y)], acc) => some (some y, acc)
          | _ => none) = some (res, acc') →
      ∃ W, acc'.ws = W ++ acc.ws ∧ SegProvW s root W res := by
    intro h E v runs acc1 ho hp hrp hEp hKP hkid ht
    split at ht
    · cases ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact seg_prov_none hpre.fresh ho hp hrp
    · rename_i v' hset
      split at ht
      · rename_i c0 y acc2 he
        simp only [Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact seg_prov_some hcf hpre.fresh hlev ho hp hrp hEp hKP hkid hset he
      · cases ht
  unfold planTree at hpt
  cases root with
  | some r =>
    cases hgk : getKey s r with
    | none => simp [hgk] at hpt
    | some n =>
      cases hplan : plan cf i s f r g (cf.htOf n.level) ops acc with
      | none => simp [hgk, hplan] at hpt
      | some p =>
        obtain ⟨v, acc1⟩ := p
        simp only [hgk, hplan] at hpt
        obtain ⟨hsh, hg, hnd⟩ := hpre.root r rfl
        have hht : htIn cf s r = cf.htOf n.level := by
          unfold htIn; rw [getKey_obj hgk]
        rw [hht] at hsh
        obtain ⟨runs, ho, hp, hrp⟩ := f_old' hcf IH IP hpre hsh hg hnd hplan
        refine tail ho hp hrp ?_ ?_ ?_ hpt
        · intro e he
          obtain ⟨l, n', hl, h1, h2, h3⟩ := content_parent _ hsh hg e he
          exact ⟨l, n', hl, h1, h2, h3⟩
        · obtain ⟨C, a1, a2, a3⟩ := plan_prov hcf hpre.sok (Xs := R s r)
            (Rp := RpG cf s (R s r)) (FF := f) (ag_prov hcf hpre.sok IH IP (R s r)) f (le_refl f)
            r g _ ops acc v acc1 0 none hplan hsh hg hnd (fun z hz => hz) hpre.ops hpre.fresh
          exact ⟨C, a1, a2, a3⟩
        · intro y hy _
          rw [kidId_plan hplan hy]
  | none =>
    cases hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc with
    | none => simp [hag] at hpt
    | some p =>
      obtain ⟨es, acc1⟩ := p
      cases hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
      | none => simp [hag, hmk] at hpt
      | some v =>
        simp only [hag, hmk, Option.map_some] at hpt
        obtain ⟨runs, ho, hp, hrp, hv⟩ := f_new' hcf IH IP hpre hag hmk
        obtain ⟨hsorted, hlk0⟩ := applyGroups_spec f g [] _ ops acc es acc1 hag List.Pairwise.nil
        -- no kept child of the new tree is an old node
        have hnew : ∀ e ∈ es, s.obj e.2 = none := by
          intro e he
          by_contra hse
          have hlk := lookup_of_mem hsorted he
          by_cases ht : e.1 ∈ touched g ops
          · obtain ⟨r, hr, hrc⟩ := e_run_of_touched hp ht
            have hres := e_run_res hp hr
            have habs : content 0 (absV s 0 v) = es := by
              rw [hv]
              show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
              rw [List.map_map]
              conv_rhs => rw [← List.map_id es]
              apply List.map_congr_left
              intro e _
              rfl
            rw [habs, hrc, hlk] at hres
            obtain ⟨W', _, _, hb⟩ := hrp r hr
            rcases hb e.2 hres.symm hse with h1 | ⟨q, hq, _⟩
            · simp at h1
            · simp [Ro] at hq
          · have := hlk0 e.1 ht
            rw [hlk] at this
            simp at this
        refine tail ho hp hrp (by simp) ⟨[], fun u hu y hy hs => ?_, by simp, by simp⟩ ?_ hpt
        · exfalso
          rw [hv] at hu
          simp only [nodesOf, List.mem_cons] at hu
          rcases hu with rfl | hu
          · obtain ⟨e, he, hk⟩ := List.mem_filterMap.mp hy
            obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
            simp only [kidId, Option.some.injEq] at hk
            subst hk
            exact hs (hnew e' he')
          · rw [nodesL_eq] at hu
            obtain ⟨e, he, hu⟩ := List.mem_flatMap.mp hu
            obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
            simp [nodesOf] at hu
        · intro y hy
          rw [hv] at hy
          simp [kidId] at hy

/-- `planTree`'s provenance at every fuel. -/
theorem fp_all (hcf : cf.Ok) (hlev : LevOK s) : ∀ F, TreeProvIH cf i s F := by
  intro F
  induction F with
  | zero => intro f hf; omega
  | succ F IH =>
    intro f hf root g ops acc res acc' hpre hpt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hlt | rfl
    · exact IH f hlt root g ops acc res acc' hpre hpt
    · cases f with
      | zero => simp [planTree] at hpt
      | succ f =>
        exact fp_step hcf hlev (f_all hcf f) (fun f' hf' => IH f' (by omega)) root g ops acc res
          acc' hpre hpt

/-! ## The transaction -/

/-- **PE's transaction has its provenance** (`Prov`): from a state PE keeps at
i - 1 with `InvB`. -/
theorem pe_prov (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s)
    (hw : peTx cf i s tp next ops = some o) : Prov s (o.tree s) o.D := by
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hlev : LevOK s := fun x m hx => ptrsLow_iff.mp (hB.low x m hx)
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by
    have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
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
  have hsh : Shaped cf s 0 (cf.htOf n.level) r0 := hht ▸ hsh0
  obtain ⟨runs, ho, hps, hrp⟩ := f_old' hcf (f_all hcf fuel) (fp_all hcf hlev fuel) hpre hsh hgood hnd
    hp
  obtain ⟨C, a1, a2, a3⟩ := plan_prov hcf hsok (Xs := R s r0) (Rp := RpG cf s (R s r0))
    (FF := fuel) (ag_prov hcf hsok (f_all hcf fuel) (fp_all hcf hlev fuel) (R s r0)) fuel
    (le_refl _) r0 0 _ _ _ v acc1 0 none hp hsh hgood hnd (fun z hz => hz) hpre.ops hpre.fresh
  obtain ⟨W, hW, hSP, _⟩ := seg_prov_some hcf hpre.fresh hlev ho hps hrp
    (fun e he => by
      obtain ⟨l, n', hl, h1, h2, h3⟩ := content_parent _ hsh hgood e he
      exact ⟨l, n', hl, h1, h2, h3⟩)
    ⟨C, a1, a2, a3⟩ (fun y hy _ => by rw [kidId_plan hp hy]) hsr he
  have hWs : acc2.ws = W := by simpa using hW
  obtain ⟨W2, hW2, hform⟩ := seg_space_form hcf hpre (hht ▸ hp) hsr he
  have hW2W : W2 = W := by rw [← hWs, hW2]; simp
  rw [hW2W] at hform
  obtain ⟨W3, hWok, _, _⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  have hW3W : W3 = W := by rw [← hWs, hWok.ws]; simp
  rw [hW3W] at hWok
  have hows : o.ws = W := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hWs
  have hreach : reach s = R s r0 := reach_eq_R hr
  intro p hpD m hTp c y hy hsy
  have hpW : p ∈ W.map (·.1) := by rw [← hows]; exact hpD
  obtain ⟨⟨p', ob⟩, hpm, hpp⟩ := List.mem_map.mp hpW
  simp only at hpp
  subst hpp
  have hTob : (o.tree s).obj p' = some ob := by
    show (applyWs s o.ws o.roots).obj p' = some ob
    rw [hows]
    exact applyWs_obj_of_mem hWok.nodup hpm
  rw [hTp] at hTob
  obtain rfl : ob = .key m := (Option.some.inj hTob).symm
  have conv : ∀ (h1 : Klong.key c y ∈ newKlongs s (p', Obj.key m)),
      (∃ n c', s.obj p' = some (.key n) ∧ (c', y) ∈ live n.ks) ∨
      ∃ q ∈ reach s, q ∉ o.D ∧ ∃ n c', s.obj q = some (.key n) ∧ (c', y) ∈ live n.ks := by
    intro h1
    rcases hSP (p', .key m) hpm c y h1 hsy with h2 | ⟨q, hq, hqW, hkq⟩
    · exact Or.inl h2
    · right
      refine ⟨q, by rw [hreach]; exact hq, by rw [Out.D, hows]; exact hqW, kidOf_iff.mp hkq⟩
  rcases hform _ hpm with ⟨hs0, ⟨v0, hv0⟩ | ⟨l, b, F, hk, hlive⟩⟩ | ⟨n0, F, hs0, hob, hlive, _⟩
  · simp at hv0
  · simp only at hs0 hk
    injection hk with hk
    subst hk
    simp only at hy
    rw [hlive] at hy
    apply conv
    rw [newKlongs_fresh hs0 rfl]
    simp only [newKs, keysOf, List.mem_cons, List.mem_map]
    exact Or.inr ⟨(c, y), hy, rfl⟩
  · simp only at hs0 hob hlive
    injection hob with hob
    subst hob
    simp only at hy
    rw [hlive] at hy
    by_cases hlk : (live n0.ks).lookup c = some y
    · exact Or.inl ⟨n0, c, hs0, Contract.PE.lookup_mem hlk⟩
    · apply conv
      rw [newKlongs_old hs0 rfl]
      simp only [emitKs, List.mem_append]
      right
      simp only [keysOf, addedOf, List.mem_map, List.mem_filter]
      exact ⟨(c, y), ⟨hy, by simpa using hlk⟩, rfl⟩

/-- **PE's transaction meets A-COPY and A6' and keeps `InvA`** (030-21 part
2): from a state PE keeps at i - 1 (`Inv`) with `InvB` and `InvA`, for
operations of distinct keys. -/
theorem pe_adopt_copy (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s) (hA : InvA cf s)
    (hkeys : (ops.map Op.key).Nodup) (hw : peTx cf i s tp next ops = some o) :
    copyOk i s (o.tree s) tp (peChange cf s tp o) = true ∧
      adoptOk ((o.tree s).at i) = true ∧ InvA cf (o.tree s) :=
  pe_adopt_copy_of_prov hcf hi hI hB hA hkeys (pe_prov hcf hi hI hB hw) hw

/-- Every transaction of a run of PE has its provenance. -/
theorem pe_prov_run (hcf : cf.Ok) (c0' : Changes BVal) :
    ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId) (t : Time)
      (L : List (BTx × Top)), Inv cf t s tp nx → InvB cf s →
      (∀ ops ∈ txs, (ops.map Op.key).Nodup) → peRun cf s tp nx t txs = some L →
      ∀ j (hj : j < L.length), Prov ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
        ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.D
  | [], s, tp, nx, t, L, _, _, _, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj
    simp at hj
  | ops :: rest, s, tp, nx, t, L, hI, hB, hk, hr => by
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
      have hP0 := pe_prov hcf (Nat.succ_pos t) hI' hB hw
      obtain ⟨_, _, hB'⟩ := pe_bridge hcf (Nat.succ_pos t) hI' hB hko hw
      obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf (Nat.succ_pos t) hI' hw
      have ih := pe_prov_run hcf c0' rest (o.tree s) o.top o.next (t + 1) L' (by simpa using hI2)
        hB' (fun ops' h' => hk ops' (List.mem_cons_of_mem _ h')) hrest
      intro j hj
      cases j with
      | zero => exact hP0
      | succ j =>
        have hj' : j < L'.length := by simpa using hj
        have h1 := ih j hj'
        have e1 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1)) j
          (by simp; omega)
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        simp only [List.map_cons] at e1 e2 ⊢
        rw [e1, e2]
        simpa using h1

/-- **Every transaction of PE's history from the empty tree has its
provenance**, for transactions each of distinct keys. -/
theorem pe_prov_hist (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length), Prov (h.tree j) (h.tree (j + 1)) h.txs[j].D := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq] at hh
    have hh1 := congrArg Prod.fst hh
    simp only at hh1
    subst hh1
    obtain ⟨h0, _, _⟩ := start_inv hcf
    intro j hj
    have hj' : j < L.length := by simpa using hj
    have := pe_prov_run hcf (c0 cf) txs _ _ _ 0 L h0 (invB_start hcf) hk hr j hj'
    simpa using this

/-- **A6' and A-COPY for PE's history from the empty tree** (030-21 part 2):
for transactions each of distinct keys, `MeetsFull.adopt` at every time, the
touch rules and A-COPY of `MeetsFull.step` at every transaction, with the
history's own tops; and every tree of it meets `InvA`. -/
theorem pe_adopt_hist_full (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    (∀ j, j ≤ h.txs.length → adoptOk ((h.tree j).at j) = true) ∧
    (∀ j (hj : j < h.txs.length),
      touchOk ((h.tree j).at j) (top j) h.txs[j].c.touch = true ∧
      copyOk (j + 1) (h.tree j) (h.tree (j + 1)) (top j) h.txs[j].c = true) ∧
    ∀ j, j ≤ h.txs.length → InvA cf (h.tree j) := by
  obtain ⟨a1, a2, a3⟩ := pe_adopt_hist hcf hk hh (pe_prov_hist hcf hk hh)
  exact ⟨a1, fun j hj => ⟨pe_touch_hist hh j hj, a2 j hj⟩, a3⟩

end Contract.PE
