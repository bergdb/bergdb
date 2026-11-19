/-
bergdb 030-21: plan with its runs. The plan of a segment's tree from an old
node, as 026-24's `Plan` (as `plan_inst`), with what each compare value's run
of `applyGroups` at the leaves did: the runs one after the other (`Chain`),
one for each compare value touched; each abstract operation is its run's
result (`opOf`); each run meets P with its group of operations and the old
entry of its compare value (the old leaf level's); and the nodes reached from
that old entry are none of the old nodes the planned node uses (`Ui`).

* `runs_ok`: the induction on the fuel, as `plan_ok` (PeInst.lean): a leaf's
  runs are its `applyGroups` call's; an inner node's are its planned
  children's, one after the other (`planKids_runs`, as `planKids_spec`).
* `content_R`: an entry of a node's old leaf level walks within the node's
  walk; the children's walks are disjoint (`R s x` has no duplicates).
* `rebalance_ui`: rebalance only drops old nodes used (a joined node has no
  base; an opened child gives its children's walks, `open_ui`).
-/
import Contract.Proof.PeOwn

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

/-- One compare value's run of `applyGroups`: its compare value, the entry it
ends with (none: no entry), and the Acc before and after it. -/
structure Run where
  c : Nat
  res : Option NodeId
  a : Acc
  a' : Acc

/-- Runs one after the other from a to a', the next id growing in each. -/
def Chain : Acc → List Run → Acc → Prop
  | a, [], a' => a = a'
  | a, r :: rs, a' => r.a = a ∧ r.a.next ≤ r.a'.next ∧ Chain r.a' rs a'

/-- The abstract operation of a run's result. -/
def opOf (c : Nat) : Option NodeId → Abs.Op
  | some y => .put c y
  | none => .del c

/-! ## Runs one after the other -/

theorem chain_append {a b c : Acc} : ∀ {rs1 rs2 : List Run}, Chain a rs1 b → Chain b rs2 c →
    Chain a (rs1 ++ rs2) c
  | [], _, h1, h2 => by
    simp only [Chain] at h1
    subst h1
    simpa using h2
  | r :: rs1, rs2, h1, h2 => by
    obtain ⟨e1, e2, e3⟩ := h1
    exact ⟨e1, e2, chain_append e3 h2⟩

/-- The next id grows along runs. -/
theorem chain_next : ∀ {a a' : Acc} {rs : List Run}, Chain a rs a' → a.next ≤ a'.next
  | _, _, [], h => by simp only [Chain] at h; subst h; exact le_rfl
  | _, _, r :: rs, h => by
    obtain ⟨e1, e2, e3⟩ := h
    have := chain_next e3
    rw [← e1]
    exact le_trans e2 this

/-! ## The old tree's walks -/

/-- An entry of the old leaf level of a sound node shaped as PE's trees: the
nodes reached from it are reached from the node. -/
theorem content_R : ∀ (h : Nat) {g : Nat} {y : NodeId} {lo : Nat} {hi : Option Nat},
    Good s y lo hi → Shaped cf s g h y → ∀ p ∈ content h (view h s y), ∀ z ∈ R s p.2, z ∈ R s y
  | 0, g, y, lo, hi, hg, hsh => by
    intro p hp z hz
    obtain ⟨n, hobj, _, _, _, _⟩ := shaped_obj hsh
    have hp' : p ∈ live n.ks := by
      have : content 0 (view 0 s y) = live n.ks := view_zero hobj
      rw [this] at hp; exact hp
    rw [R_good hg hobj, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨p, hp', hz⟩
  | h + 1, g, y, lo, hi, hg, hsh => by
    intro p hp z hz
    obtain ⟨n, hobj, _, hleaf, _, _⟩ := shaped_obj hsh
    have hleaf' : n.leaf = false := by simpa using hleaf
    have hkids : ∀ c z, (c, z) ∈ live n.ks → Shaped cf s g h z := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hk =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hk
    rw [content_view_succ hobj, List.mem_flatMap] at hp
    obtain ⟨cy, hcy, hp⟩ := hp
    obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
    have hgc : Good s cy.2 (max lo cy.1) (nextHi post hi) := by
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ _ _ _ hkid =>
        rw [hobj] at hobj'
        obtain rfl : n = n' := by injection hobj' with h1; injection h1
        exact hkid hleaf' pre cy.1 cy.2 post he
    have := content_R h hgc (hkids cy.1 cy.2 hcy) p hp z hz
    rw [R_good hg hobj, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨cy, hcy, this⟩

/-- An entry of the children's old leaf levels: the nodes reached from it are
reached from one of the children. -/
theorem content_R_kids {g h : Nat} {lo : Nat} {hi : Option Nat} {lv : List (Nat × NodeId)}
    (hpos : ∀ pre c y post, lv = pre ++ (c, y) :: post →
      Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h y) :
    ∀ p ∈ lv.flatMap (fun cy => content h (view h s cy.2)), ∀ z ∈ R s p.2,
      z ∈ lv.flatMap (fun cy => R s cy.2) := by
  intro p hp z hz
  obtain ⟨cy, hcy, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
  obtain ⟨hg, hsh⟩ := hpos pre cy.1 cy.2 post he
  exact List.mem_flatMap.mpr ⟨cy, hcy, content_R h hg hsh p hp z hz⟩

/-! ## Rebalance only drops old nodes used -/

/-- An inner child opened for a join: its entries use no old node it does
not use. -/
theorem open_ui {g h : Nat} {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g (h + 1) w)
    (ho : openEs s w = some esW) : ∀ z ∈ UiL s esW, z ∈ Ui s w := by
  intro z hz
  rw [UiL_eq] at hz
  cases hw with
  | @old _ y hsh hg hne =>
    obtain ⟨n, hobj, rfl⟩ := openEs_old ho
    show z ∈ R s y
    rw [R_shaped hsh hobj, List.mem_cons]
    right
    simpa [List.flatMap_map, Ui] using hz
  | inner _ _ _ _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    rw [Ui_node]
    simp only [Nat.add_one_ne_zero, ite_false, List.mem_append]
    exact Or.inr hz

/-- The virtual node that `mkNode` makes. -/
theorem mkNode_form {b : Option NodeId} {g h : Nat} {j : Bool} {es0 : List (Nat × VN)} {v : VN}
    (hm : mkNode cf i s b g h j es0 = some v) :
    ∃ F dec, v = .node b g h j (if h == 0 then es0 else renameHead 0 es0) F dec := by
  unfold mkNode at hm
  cases b with
  | some x =>
    simp only at hm
    split at hm
    · simp only [Option.some.injEq] at hm
      exact ⟨_, _, hm.symm⟩
    · cases hm
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · simp only [Option.some.injEq] at hm
      exact ⟨_, _, hm.symm⟩

theorem UiL_append (A B : List (Nat × VN)) : UiL s (A ++ B) = UiL s A ++ UiL s B := by
  simp [UiL_eq]

theorem UiL_renameHead (c : Nat) (es : List (Nat × VN)) : UiL s (renameHead c es) = UiL s es := by
  cases es with
  | nil => rfl
  | cons e r => obtain ⟨a, w⟩ := e; rfl

theorem split_ui {es : List (Nat × VN)} {il : Nat} {l r : Nat × VN}
    (hl : es[il]? = some l) (hr : es[il + 1]? = some r) (v : VN)
    (hv : ∀ z ∈ Ui s v, z ∈ Ui s l.2 ∨ z ∈ Ui s r.2) :
    ∀ z ∈ UiL s (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)), z ∈ UiL s es := by
  have hsplit := split_at2 hl hr
  intro z hz
  rw [congrArg (UiL s) hsplit]
  simp only [UiL_eq, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.mem_append,
    List.append_nil] at hz ⊢
  rcases hz with (hz | hz) | hz
  · exact Or.inl hz
  · rcases hv z hz with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr hz))

theorem joinAt_ui_zero {g : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g 0 down es ix = some es') :
    ∀ z ∈ UiL s es', z ∈ UiL s es := by
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
        refine split_ui hl hr _ (fun z hz => ?_)
        rw [Ui_node] at hz
        simp at hz
    · cases hj
  · cases hj

theorem joinAt_ui_succ {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hdown : ∀ J J', down J = some J' → KOk cf s g h J → ∀ z ∈ UiL s J', z ∈ UiL s J)
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g (h + 1) down es ix = some es')
    (hes : KOk cf s g (h + 1) es) : ∀ z ∈ UiL s es', z ∈ UiL s es := by
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
          obtain ⟨F, dec, rfl⟩ := mkNode_form hm
          refine split_ui hl hr _ (fun z hz => ?_)
          rw [Ui_node] at hz
          simp only [Option.toList_none, List.nil_append, Nat.add_one_ne_zero, ite_false,
            show (h + 1 == 0) = false by simp, Bool.false_eq_true] at hz
          rw [← UiL_eq, UiL_renameHead] at hz
          have hz2 := hdown _ _ hd hJk z hz
          rw [UiL_append, UiL_renameHead, List.mem_append] at hz2
          rcases hz2 with hz2 | hz2
          · exact Or.inl (open_ui (hes l hlm).1 hoL z hz2)
          · exact Or.inr (open_ui (hes r hrm).1 hoR z hz2)
    · cases hj
  · cases hj

/-- The loop of joins only drops old nodes used. -/
theorem joinLoop_ui {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hjoin : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
        es'.head?.map (·.1) = es.head?.map (·.1))
    (hju : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      ∀ z ∈ UiL s es', z ∈ UiL s es) :
    ∀ (n : Nat) (es es' : List (Nat × VN)), joinLoop cf i s g h down n es = some es' →
      KOk cf s g h es → ∀ z ∈ UiL s es', z ∈ UiL s es
  | 0, es, es', hl, _ => by
    simp only [joinLoop, Option.some.injEq] at hl
    subst hl
    exact fun z hz => hz
  | n + 1, es, es', hl, hk => by
    simp only [joinLoop] at hl
    split at hl
    · simp only [Option.some.injEq] at hl; subst hl; exact fun z hz => hz
    · split at hl
      · simp only [Option.some.injEq] at hl; subst hl; exact fun z hz => hz
      · rename_i ix _
        cases hj : joinAt cf i s g h down es ix with
        | none => rw [hj] at hl; cases hl
        | some es1 =>
          rw [hj] at hl
          simp only at hl
          obtain ⟨_, a2, _⟩ := hjoin es ix es1 hj hk
          exact fun z hz => hju es ix es1 hj hk z (joinLoop_ui hjoin hju n es1 es' hl a2 z hz)

/-- **Rebalance only drops old nodes used**: every old node the children
rebalanced use (`UiL`) is one that the children before used (a joined node
has no base, and an opened child gives its children's walks). -/
theorem rebalance_ui (hcf : cf.Ok) {g : Nat} : ∀ (f h : Nat) (es0 es2 : List (Nat × VN)),
    rebalance cf i s f g h es0 = some es2 → (∀ e ∈ es0, VOk cf s g h e.2) →
    ∀ z ∈ UiL s es2, z ∈ UiL s es0
  | 0, _, _, _, hr, _ => by simp [rebalance] at hr
  | f + 1, h, es0, es2, hr, hk => by
    unfold rebalance at hr
    simp only at hr
    have hk1 : KOk cf s g h (es0.filter (fun e => !e.2.isEmpty)) := by
      intro e he
      rw [List.mem_filter] at he
      exact ⟨hk e he.1, by simpa using he.2⟩
    have hc1 : ∀ z ∈ UiL s (es0.filter (fun e => !e.2.isEmpty)), z ∈ UiL s es0 := by
      intro z hz
      rw [UiL_eq] at hz ⊢
      exact ((List.filter_sublist).flatMap _).subset hz
    split at hr
    · simp only [Option.some.injEq] at hr
      subst hr
      exact hc1
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
      have hju : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es → ∀ z ∈ UiL s es', z ∈ UiL s es := by
        intro es ix es' hj hes
        cases h with
        | zero => exact joinAt_ui_zero hj
        | succ h' =>
          exact joinAt_ui_succ (fun J J' hd hJk =>
            rebalance_ui hcf f h' J J' hd (fun e he => (hJk e he).1)) hj hes
      exact fun z hz => hc1 z (joinLoop_ui hjoin hju _ _ _ hr hk1 z hz)

/-! ## The induction -/

/-- The leaf's premise at fuel f': `applyGroups` gives its runs. -/
def AGOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (P : List Contract.Op → Option NodeId → Run → Prop)
    (Q : Contract.Op → Prop) (f' : Nat) : Prop :=
  ∀ (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat)
    (ops : List Contract.Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    s.obj x = some (.key n) → Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup →
    (∀ op ∈ ops, Q op) → (∀ z, acc.next ≤ z → s.obj z = none) →
    applyGroups cf i s f' g (live n.ks) (touched g ops) ops acc = some (es, acc') →
    ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = touched g ops ∧
      ∀ r ∈ runs, P (ops.filter (fun op => segAt g op == r.c)) ((live n.ks).lookup r.c) r ∧
        es.lookup r.c = r.res

/-- What `plan` gives at fuel F, for the induction (`plan_runs`'s
conclusion). -/
def RunsOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (P : List Contract.Op → Option NodeId → Run → Prop)
    (Q : Contract.Op → Prop) (F : Nat) : Prop :=
  ∀ (x : NodeId) (h : Nat) (ops : List Contract.Op) (acc : Acc) (v : VN) (acc' : Acc)
    (lo : Nat) (hi : Option Nat),
    plan cf i s F x g h ops acc = some (v, acc') → Shaped cf s g h x → Good s x lo hi →
    (R s x).Nodup → (∀ op ∈ ops, Q op) → (∀ z, acc.next ≤ z → s.obj z = none) →
    ∃ (sops : List Abs.Op) (runs : List Run), Plan h (view h s x) sops (absV s h v) ∧
      sops.map Abs.Op.cv = touched g ops ∧ VOk cf s g h v ∧ Chain acc runs acc' ∧
      (runs.map (·.c)).Perm (touched g ops) ∧
      (∀ o ∈ sops, ∃ r ∈ runs, r.c = o.cv ∧ o = opOf r.c r.res) ∧
      (∀ r ∈ runs, P (ops.filter (fun op => segAt g op == r.c))
        ((content h (view h s x)).lookup r.c) r) ∧
      (∀ r ∈ runs, ∀ y0, (content h (view h s x)).lookup r.c = some y0 →
        ∀ z ∈ R s y0, z ∉ Ui s v)

theorem planKids_nil' {f g h : Nat} {os : List (List Contract.Op)} {acc : Acc}
    {es : List (Nat × VN)} {acc' : Acc} (hp : planKids cf i s f g h [] os acc = some (es, acc')) :
    es = [] ∧ acc' = acc := by
  cases f with
  | zero => simp [planKids] at hp
  | succ f =>
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩

/-- The operations of a compare value in a range: those of the range's
operations. -/
theorem filter_range {g c : Nat} {q : Nat → Bool} (hq : q c = true) (ops : List Contract.Op) :
    (ops.filter (fun o => q (segAt g o))).filter (fun op => segAt g op == c) =
      ops.filter (fun op => segAt g op == c) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro op _
  by_cases h : segAt g op = c
  · simp [h, hq]
  · simp [h]

/-- **The children planned with their runs**: `planKids_spec` with the runs
of the planned children one after the other, each meeting P with its group
and its old entry in the children's old leaf levels, and walking from its old
entry into none of the old nodes the children use. -/
theorem planKids_runs (hcf : cf.Ok) {g h : Nat} {P : List Contract.Op → Option NodeId → Run → Prop}
    {Q : Contract.Op → Prop} : ∀ (F : Nat) (lv : List (Nat × NodeId)) (ops : List Contract.Op)
    (acc : Acc) (es : List (Nat × VN)) (acc' : Acc) (lo : Nat) (hi : Option Nat),
    (∀ f' < F, RunsOk cf i s g P Q f') → lv ≠ [] →
    planKids cf i s F g (h + 1) lv (Contract.PE.route (segAt g) lv ops) acc = some (es, acc') →
    (∀ c y, (c, y) ∈ lv → VOk cf s g h (.old y)) →
    lv.Pairwise CvLtA → (∀ e ∈ lv, Below e.1 hi) →
    (∀ pre c y post, lv = pre ++ (c, y) :: post →
      Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h y) →
    (lv.flatMap (fun cy => R s cy.2)).Nodup → (∀ op ∈ ops, Q op) →
    (∀ z, acc.next ≤ z → s.obj z = none) →
    ∃ (sops : List Abs.Op) (runs : List Run),
      Routed (Plan h) (lv.map (fun cy => (cy.1, view h s cy.2)))
        (PeProof.Abs.route (lv.map (fun cy => (cy.1, view h s cy.2))) sops) (absK s h es) ∧
      sops.map Abs.Op.cv = touched g ops ∧ (∀ e ∈ es, VOk cf s g h e.2) ∧
      Chain acc runs acc' ∧ (runs.map (·.c)).Perm (touched g ops) ∧
      (∀ o ∈ sops, ∃ r ∈ runs, r.c = o.cv ∧ o = opOf r.c r.res) ∧
      (∀ r ∈ runs, P (ops.filter (fun op => segAt g op == r.c))
        ((lv.flatMap (fun cy => content h (view h s cy.2))).lookup r.c) r) ∧
      (∀ r ∈ runs, ∀ y0, (lv.flatMap (fun cy => content h (view h s cy.2))).lookup r.c = some y0 →
        ∀ z ∈ R s y0, z ∉ UiL s es) ∧
      (∀ z ∈ UiL s es, z ∈ lv.flatMap (fun cy => R s cy.2))
  | 0, _, _, _, _, _, _, _, _, _, hp, _, _, _, _, _, _, _ => by simp [planKids] at hp
  | _, [], _, _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _ => absurd rfl hne
  | F + 1, [(c, y)], ops, acc, es, acc', lo, hi, IH, _, hp, hk, _, _, hpos, hnd, hQ, hfr => by
    have hy := hk c y (by simp)
    obtain ⟨hg, hsh⟩ := hpos [] c y [] rfl
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hnd ⊢
    simp only [Contract.PE.route, planKids, Nat.add_sub_cancel] at hp
    split at hp
    · rename_i hops
      cases hp2 : planKids cf i s F g (h + 1) [] [] acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨rfl, rfl⟩ := planKids_nil' hp2
        have hops' : ops = [] := List.isEmpty_iff.mp hops
        subst hops'
        refine ⟨[], [], ?_, rfl, ?_, rfl, by simp [touched_nil], by simp, by simp, by simp, ?_⟩
        · simp only [List.map_cons, List.map_nil, PeProof.Abs.route, absK, absV_old]
          exact Routed.keep c _ [] [] [] Routed.nil
        · intro e he; simp at he; subst he; exact hy
        · intro z hz; simpa [UiL, Ui] using hz
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
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨rfl, hacc⟩ := planKids_nil' hp2
          subst acc2
          obtain ⟨sops, runs, hpl, hcv, hv, hch, hperm, hop, hP, hU⟩ :=
            IH F (by omega) y h ops acc v acc1 _ _ hp1 hsh hg hnd hQ hfr
          have hown := (plan_own hcf hp1 hsh hg).2.1.subset
          refine ⟨sops, runs, ?_, hcv, ?_, hch, hperm, hop, hP, ?_, ?_⟩
          · simp only [List.map_cons, List.map_nil, PeProof.Abs.route, absK]
            exact Routed.plan c _ sops _ [] [] [] hpl Routed.nil
          · intro e he; simp at he; subst he; exact hv
          · intro r hr y0 hy0 z hz; simpa [UiL] using hU r hr y0 hy0 z hz
          · intro z hz
            simp only [UiL, List.append_nil] at hz
            exact hown (List.mem_append_left _ hz)
  | F + 1, (c, y) :: (c', y') :: r, ops, acc, es, acc', lo, hi, IH, _, hp, hk, hs, hb, hpos, hnd,
      hQ, hfr => by
    have hy := hk c y (by simp)
    obtain ⟨hg, hsh⟩ := hpos [] c y ((c', y') :: r) rfl
    have hk' : ∀ c y, (c, y) ∈ (c', y') :: r → VOk cf s g h (.old y) :=
      fun c y h => hk c y (List.mem_cons_of_mem _ h)
    have IH' : ∀ f' < F, RunsOk cf i s g P Q f' := fun f' h => IH f' (by omega)
    have hs' := List.pairwise_cons.mp hs
    have hpos' : ∀ pre c y post, (c', y') :: r = pre ++ (c, y) :: post →
        Good s y (max lo c) (nextHi post hi) ∧ Shaped cf s g h y :=
      fun pre c0 y0 post he => hpos ((c, y) :: pre) c0 y0 post (by rw [he]; rfl)
    have hb' : ∀ e ∈ (c', y') :: r, Below e.1 hi := fun e he => hb e (List.mem_cons_of_mem _ he)
    -- the old leaf level: the first child's below c', the others' from c'
    have hEy : ∀ e ∈ content h (view h s y), e.1 < c' := by
      intro e he
      have := ((view_content h hg hsh).2 e he).2
      simpa [nextHi, Below] using this
    have hErest : ∀ e ∈ ((c', y') :: r).flatMap (fun cy => content h (view h s cy.2)), c' ≤ e.1 := by
      have := kids_content (C := fun z => content h (view h s z)) (lo := lo) (hi := hi)
        ((c', y') :: r) hs'.2 hb'
        (fun pre c0 y0 post he => by
          obtain ⟨g1, s1⟩ := hpos' pre c0 y0 post he
          exact view_content h g1 s1)
      intro e he
      exact (this.2 e he).2.2 c' y' rfl
    have hRrest := content_R_kids hpos'
    have hRy := content_R h hg hsh
    have eE : ((c, y) :: (c', y') :: r).flatMap (fun cy => content h (view h s cy.2)) =
        content h (view h s y) ++ ((c', y') :: r).flatMap (fun cy => content h (view h s cy.2)) :=
      List.flatMap_cons
    have eR : ((c, y) :: (c', y') :: r).flatMap (fun cy => R s cy.2) =
        R s y ++ ((c', y') :: r).flatMap (fun cy => R s cy.2) := List.flatMap_cons
    rw [eR] at hnd
    rw [eE, eR]
    have hnd1 : (R s y).Nodup := (List.nodup_append.mp hnd).1
    have hnd2 := (List.nodup_append.mp hnd).2.1
    have hdis : ∀ z ∈ R s y, z ∉ ((c', y') :: r).flatMap (fun cy => R s cy.2) :=
      fun z hz hz' => (List.nodup_append.mp hnd).2.2 z hz z hz' rfl
    set ER := ((c', y') :: r).flatMap (fun cy => content h (view h s cy.2)) with hER
    have ht1 := touched_filter g (fun c => decide (c < c')) ops
    have ht2 := touched_filter g (fun c => decide (c' ≤ c)) ops
    have hf1 : ∀ c0, c0 < c' → (ops.filter (fun o => decide (segAt g o < c'))).filter
        (fun op => segAt g op == c0) = ops.filter (fun op => segAt g op == c0) :=
      fun c0 hc0 => filter_range (q := fun c => decide (c < c')) (by simpa using hc0) ops
    have hf2 : ∀ c0, c' ≤ c0 → (ops.filter (fun o => decide (c' ≤ segAt g o))).filter
        (fun op => segAt g op == c0) = ops.filter (fun op => segAt g op == c0) :=
      fun c0 hc0 => filter_range (q := fun c => decide (c' ≤ c)) (by simpa using hc0) ops
    simp only [Contract.PE.route] at hp
    simp only [planKids, Nat.add_sub_cancel] at hp
    generalize ho1 : ops.filter (fun o => decide (segAt g o < c')) = o1 at hp ht1 hf1
    generalize ho2 : ops.filter (fun o => decide (c' ≤ segAt g o)) = o2 at hp ht2 hf2
    have ht1' : ∀ c0 ∈ touched g o1, c0 < c' := by
      intro c0 hc0
      obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc0
      rw [← ho1] at hop
      simpa using (List.mem_filter.mp hop).2
    have ht2' : ∀ c0 ∈ touched g o2, c' ≤ c0 := by
      intro c0 hc0
      obtain ⟨op, hop, rfl⟩ := mem_touched.mp hc0
      rw [← ho2] at hop
      simpa using (List.mem_filter.mp hop).2
    have hQ1 : ∀ op ∈ o1, Q op := fun op h => by rw [← ho1] at h; exact hQ op (List.mem_of_mem_filter h)
    have hQ2 : ∀ op ∈ o2, Q op := fun op h => by rw [← ho2] at h; exact hQ op (List.mem_of_mem_filter h)
    split at hp
    · rename_i hops
      have ho1' : o1 = [] := List.isEmpty_iff.mp hops
      subst ho1'
      have ho2' : o2 = ops := by
        rw [← ho2]
        apply List.filter_eq_self.mpr
        intro op hop
        have := List.filter_eq_nil_iff.mp ho1 op hop
        simp at this ⊢
        omega
      subst ho2'
      cases hp2 : planKids cf i s F g (h + 1) ((c', y') :: r)
          (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨sops, runs, hr, hcv, hv, hch, hperm, hop, hP, hU, hUs⟩ := planKids_runs hcf F
          ((c', y') :: r) o2 acc es2 acc2 lo hi IH' (by simp) hp2 hk' hs'.2 hb' hpos' hnd2 hQ2 hfr
        have hrge : ∀ r0 ∈ runs, c' ≤ r0.c := fun r0 hr0 =>
          ht2' _ (hperm.subset (List.mem_map_of_mem hr0))
        have hlk : ∀ r0 ∈ runs, (content h (view h s y) ++ ER).lookup r0.c = ER.lookup r0.c :=
          fun r0 hr0 => lookup_append_right' (fun q hq => by
            have := hEy q hq; have := hrge r0 hr0; omega)
        have hge : ∀ o ∈ sops, c' ≤ o.cv := by
          intro o ho
          have hm : o.cv ∈ touched g o2 := by rw [← hcv]; exact List.mem_map_of_mem ho
          exact ht2' _ hm
        refine ⟨sops, runs, ?_, hcv, ?_, hch, hperm, hop, ?_, ?_, ?_⟩
        · simp only [List.map_cons, PeProof.Abs.route, absK, absV_old] at hr ⊢
          rw [List.filter_eq_nil_iff.mpr (fun o ho => by have := hge o ho; simp; omega),
            List.filter_eq_self.mpr (fun o ho => by have := hge o ho; simpa using this)]
          exact Routed.keep c _ _ _ _ hr
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hy
          · exact hv e he
        · intro r0 hr0; rw [hlk r0 hr0]; exact hP r0 hr0
        · intro r0 hr0 y0 hy0 z hz hzU
          rw [hlk r0 hr0] at hy0
          have hz' := hRrest _ (lookup_mem hy0) z hz
          simp only [UiL, Ui, List.mem_append] at hzU
          rcases hzU with hzU | hzU
          · exact hdis z hzU hz'
          · exact hU r0 hr0 y0 hy0 z hz hzU
        · intro z hz
          simp only [UiL, Ui, List.mem_append] at hz ⊢
          rcases hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (hUs z hz)
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
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨sops1, runs1, hpl, hcv1, hv1, hch1, hperm1, hop1, hP1, hU1⟩ :=
            IH F (by omega) y h o1 acc v acc1 _ _ hp1 hsh hg hnd1 hQ1 hfr
          have hfr1 : ∀ z, acc1.next ≤ z → s.obj z = none :=
            fun z hz => hfr z (le_trans (chain_next hch1) hz)
          obtain ⟨sops, runs2, hr, hcv, hv, hch2, hperm2, hop2, hP2, hU2, hUs2⟩ := planKids_runs hcf F
            ((c', y') :: r) o2 acc1 es2 acc2 lo hi IH' (by simp) hp2 hk' hs'.2 hb' hpos' hnd2 hQ2 hfr1
          obtain ⟨S, hS1, hS2, hS3⟩ := interleave c' (touched g ops) sops1 sops
            (by rw [hcv1, ht1]) (by rw [hcv, ht2])
          have hown := (plan_own hcf hp1 hsh hg).2.1.subset
          have hr1 : ∀ r0 ∈ runs1, r0.c < c' := fun r0 hr0 =>
            ht1' _ (hperm1.subset (List.mem_map_of_mem hr0))
          have hr2 : ∀ r0 ∈ runs2, c' ≤ r0.c := fun r0 hr0 =>
            ht2' _ (hperm2.subset (List.mem_map_of_mem hr0))
          have hlk1 : ∀ r0 ∈ runs1, (content h (view h s y) ++ ER).lookup r0.c =
              (content h (view h s y)).lookup r0.c :=
            fun r0 hr0 => lookup_append_left' (fun q hq => by
              have := hErest q hq; have := hr1 r0 hr0; omega)
          have hlk2 : ∀ r0 ∈ runs2, (content h (view h s y) ++ ER).lookup r0.c = ER.lookup r0.c :=
            fun r0 hr0 => lookup_append_right' (fun q hq => by
              have := hEy q hq; have := hr2 r0 hr0; omega)
          refine ⟨S, runs1 ++ runs2, ?_, hS1, ?_, chain_append hch1 hch2, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [List.map_cons, PeProof.Abs.route, absK] at hr ⊢
            rw [hS2, hS3]
            exact Routed.plan c _ sops1 _ _ _ _ hpl hr
          · intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · exact hv1
            · exact hv e he
          · rw [List.map_append]
            refine (hperm1.append hperm2).trans ?_
            rw [ht1, ht2]
            have e2 : (touched g ops).filter (fun c => decide (c' ≤ c)) =
                (touched g ops).filter (fun c => !decide (c < c')) :=
              List.filter_congr (fun c _ => by by_cases hc : c < c' <;> simp [hc]; omega)
            rw [e2]
            exact List.filter_append_perm _ _
          · intro o ho
            by_cases hc : o.cv < c'
            · have : o ∈ sops1 := by
                rw [← hS2]; exact List.mem_filter.mpr ⟨ho, by simpa using hc⟩
              obtain ⟨r0, hr0, h1, h2⟩ := hop1 o this
              exact ⟨r0, List.mem_append_left _ hr0, h1, h2⟩
            · have : o ∈ sops := by
                rw [← hS3]; exact List.mem_filter.mpr ⟨ho, by simp; omega⟩
              obtain ⟨r0, hr0, h1, h2⟩ := hop2 o this
              exact ⟨r0, List.mem_append_right _ hr0, h1, h2⟩
          · intro r0 hr0
            rcases List.mem_append.mp hr0 with hr0 | hr0
            · rw [hlk1 r0 hr0, ← hf1 r0.c (hr1 r0 hr0)]; exact hP1 r0 hr0
            · rw [hlk2 r0 hr0, ← hf2 r0.c (hr2 r0 hr0)]; exact hP2 r0 hr0
          · intro r0 hr0 y0 hy0 z hz hzU
            simp only [UiL, List.mem_append] at hzU
            rcases List.mem_append.mp hr0 with hr0 | hr0
            · rw [hlk1 r0 hr0] at hy0
              have hzy := hRy _ (lookup_mem hy0) z hz
              rcases hzU with hzU | hzU
              · exact hU1 r0 hr0 y0 hy0 z hz hzU
              · exact hdis z hzy (hUs2 z hzU)
            · rw [hlk2 r0 hr0] at hy0
              have hz' := hRrest _ (lookup_mem hy0) z hz
              rcases hzU with hzU | hzU
              · exact hdis z (hown (List.mem_append_left _ hzU)) hz'
              · exact hU2 r0 hr0 y0 hy0 z hz hzU
          · intro z hz
            simp only [UiL, List.mem_append] at hz ⊢
            rcases hz with hz | hz
            · exact Or.inl (hown (List.mem_append_left _ hz))
            · exact Or.inr (hUs2 z hz)

/-- `plan` with its runs, by induction on the fuel. -/
theorem runs_ok (hcf : cf.Ok) {g : Nat} {P : List Contract.Op → Option NodeId → Run → Prop}
    {Q : Contract.Op → Prop} : ∀ F, (∀ f' < F, AGOk cf i s g P Q f') → RunsOk cf i s g P Q F := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F IH =>
  intro hAG x h ops acc v acc' lo hi hp hsh hg hnd hQ hfr
  cases F with
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
      · -- a segment leaf: the operations applied, one run per compare value
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
            obtain ⟨rfl, rfl⟩ := hp
            obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_leaf hcf hm (by
              intro e he
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
              exact ⟨q.2, rfl⟩)
            have hsorted : (live n.ks).Pairwise CvLtA := live_sorted n.ks
            obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc1 ha hsorted
            obtain ⟨runs, hch, hrc, hrs⟩ :=
              hAG f (by omega) x n lo hi ops acc es acc1 hobj hsh hg hnd hQ hfr ha
            have hE0 : content 0 (view 0 s x) = live n.ks := view_zero hobj
            refine ⟨finalOps (touched g ops) es, runs, ?_, by rw [finalOps_cv], hv, hch,
              by rw [hrc], ?_, ?_, ?_⟩
            · have habs : absV s 0 (VN.node (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2)))
                  F dec) = es := by
                show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
                rw [List.map_map]
                conv_rhs => rw [← List.map_id es]
                apply List.map_congr_left
                intro e _
                rfl
              show absV s 0 _ = Abs.applyOps (finalOps (touched g ops) es) (view 0 s x)
              rw [view_zero hobj, habs]
              exact (applyOps_finalOps _ _ _ hsorted hs1 hs2).symm
            · intro o ho
              unfold finalOps at ho
              obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp ho
              rw [← hrc] at hc0
              obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hc0
              refine ⟨r0, hr0, ?_, ?_⟩
              · split <;> rfl
              · rw [(hrs r0 hr0).2]
                cases r0.res <;> rfl
            · intro r0 hr0
              rw [hE0]
              exact (hrs r0 hr0).1
            · intro r0 hr0 y0 hy0 z hz hzU
              rw [hE0] at hy0
              rw [Ui_node] at hzU
              simp only [Option.toList_some, ite_true, List.append_nil, List.mem_singleton] at hzU
              subst hzU
              rw [R_good hg hobj] at hnd
              exact (List.nodup_cons.mp hnd).1 (List.mem_flatMap.mpr ⟨_, lookup_mem hy0, hz⟩)
      · -- an inner node: the children planned with their runs, rebalanced
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
              obtain ⟨rfl, rfl⟩ := hp
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
              have hRx := R_good hg hobj
              have hnd' : ((live n.ks).flatMap (fun cy => R s cy.2)).Nodup := by
                rw [hRx] at hnd; exact (List.nodup_cons.mp hnd).2
              have IHr : ∀ f' < f, RunsOk cf i s g P Q f' :=
                fun f' hf' => IH f' (by omega) (fun f'' h'' => hAG f'' (by omega))
              obtain ⟨sops, runs, hrt, hcv, hvk, hch, hperm, hop, hP, hU, _⟩ :=
                planKids_runs hcf f (live n.ks) ops acc es acc1 lo hi IHr hne hpk hkids
                  (live_sorted n.ks) hbelow hpos hnd' hQ hfr
              obtain ⟨hs, hk2, _⟩ := rebalance_spec hcf (f + 1) h' es es2 hr hvk
              have hui := rebalance_ui hcf (f + 1) h' es es2 hr hvk
              obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_inner hcf hm (fun e he => (hk2 e he).1)
                (fun e he => (hk2 e he).2)
              refine ⟨sops, runs, ?_, hcv, hv, hch, hperm, hop, ?_, ?_⟩
              · show ∃ ks' ks'', Routed (Plan h') (kids (view (h' + 1) s x))
                    (PeProof.Abs.route (kids (view (h' + 1) s x)) sops) ks' ∧ Sett h' ks' ks'' ∧
                    (∀ e ∈ ks'', e.2 ≠ []) ∧ kids (absV s (h' + 1) _) = renameHead 0 ks''
                rw [view_succ hobj]
                refine ⟨absK s h' es, absK s h' es2, hrt, hs, ?_, ?_⟩
                · intro e he
                  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
                  exact absV_ne (hk2 e' he').1 (hk2 e' he').2
                · show absK s h' (renameHead 0 es2) = _
                  exact absK_renameHead _ _ _
              · intro r0 hr0
                rw [content_view_succ hobj]
                exact hP r0 hr0
              · intro r0 hr0 y0 hy0 z hz hzU
                rw [content_view_succ hobj] at hy0
                rw [Ui_node] at hzU
                simp only [Option.toList_some, Nat.add_one_ne_zero, ite_false, List.singleton_append,
                  List.mem_cons] at hzU
                rw [← UiL_eq, UiL_renameHead] at hzU
                rcases hzU with hzx | hzU
                · have := content_R_kids hpos _ (lookup_mem hy0) z hz
                  rw [hRx] at hnd
                  rw [hzx] at this
                  exact (List.nodup_cons.mp hnd).1 this
                · exact hU r0 hr0 y0 hy0 z hz (hui z hzU)

/-- **Plan with its runs.** If every `applyGroups` at a lower fuel gives its
runs (one per compare value touched, in order, each meeting P and giving the
entry the leaf ends with), then `plan` gives an instance of `Plan` whose
operations are its runs' results, and runs that meet P with the old entries
of the node's leaf level, whose old walks are none of the old nodes the
planned node uses. -/
theorem plan_runs (hcf : cf.Ok) {g : Nat} (P : List Contract.Op → Option NodeId → Run → Prop)
    (Q : Contract.Op → Prop) {F : Nat}
    (hAG : ∀ f' < F, ∀ (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat)
      (ops : List Contract.Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
      s.obj x = some (.key n) → Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup →
      (∀ op ∈ ops, Q op) → (∀ z, acc.next ≤ z → s.obj z = none) →
      applyGroups cf i s f' g (live n.ks) (touched g ops) ops acc = some (es, acc') →
      ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = touched g ops ∧
        ∀ r ∈ runs, P (ops.filter (fun op => segAt g op == r.c)) ((live n.ks).lookup r.c) r ∧
          es.lookup r.c = r.res) :
    ∀ (x : NodeId) (h : Nat) (ops : List Contract.Op) (acc : Acc) (v : VN) (acc' : Acc)
      (lo : Nat) (hi : Option Nat),
      plan cf i s F x g h ops acc = some (v, acc') → Shaped cf s g h x → Good s x lo hi →
      (R s x).Nodup → (∀ op ∈ ops, Q op) → (∀ z, acc.next ≤ z → s.obj z = none) →
      ∃ (sops : List Abs.Op) (runs : List Run), Plan h (view h s x) sops (absV s h v) ∧
        sops.map Abs.Op.cv = touched g ops ∧ VOk cf s g h v ∧ Chain acc runs acc' ∧
        (runs.map (·.c)).Perm (touched g ops) ∧
        (∀ o ∈ sops, ∃ r ∈ runs, r.c = o.cv ∧ o = opOf r.c r.res) ∧
        (∀ r ∈ runs, P (ops.filter (fun op => segAt g op == r.c))
          ((content h (view h s x)).lookup r.c) r) ∧
        (∀ r ∈ runs, ∀ y0, (content h (view h s x)).lookup r.c = some y0 →
          ∀ z ∈ R s y0, z ∉ Ui s v) :=
  runs_ok hcf F hAG

end Contract.PE
