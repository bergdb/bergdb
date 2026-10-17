/-
Proofs about the physical layer, part 12: one transaction of the rerun keeps
the invariant, from K to K + 1 (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysApply

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section StepMem

variable {sp : Spec V T} {db : DB V T} {K : Nat}

/-- The new nodes' fold: the memory's other parts. -/
theorem foldl_addNew_parts (N : List NewNode) : ∀ (m : Mem V),
    (N.foldl addNew m).s = m.s ∧ (N.foldl addNew m).root = m.root := by
  induction N with
  | nil => intro m; exact ⟨rfl, rfl⟩
  | cons nn N ih => intro m; simp only [List.foldl_cons]; exact ih _

theorem foldl_addNew_fresh (N : List NewNode) : ∀ (m : Mem V), (∀ h, m.next ≤ h → m.obj? h = none) →
    ∀ h, (N.foldl addNew m).next ≤ h → (N.foldl addNew m).obj? h = none := by
  induction N with
  | nil => intro m hfr h hh; exact hfr h hh
  | cons nn N ih =>
    intro m hfr h hh
    simp only [List.foldl_cons] at hh ⊢
    apply ih _ _ h hh
    intro h' hh'
    rw [addNew_next] at hh'
    rw [addNew_obj]
    simp only [show h' ≠ m.next by omega, ↓reduceIte]
    exact hfr h' (by omega)

theorem foldl_addNew_nodup (N : List NewNode) : ∀ (m : Mem V), (∀ h, m.next ≤ h → m.obj? h = none) →
    (m.objs.map (·.1)).Nodup → ((N.foldl addNew m).objs.map (·.1)).Nodup := by
  induction N with
  | nil => intro m _ hnd; exact hnd
  | cons nn N ih =>
    intro m hfr hnd
    simp only [List.foldl_cons]
    apply ih
    · intro h' hh'
      rw [addNew_next] at hh'
      rw [addNew_obj]
      simp only [show h' ≠ m.next by omega, ↓reduceIte]
      exact hfr h' (by omega)
    · unfold addNew
      rw [Mem.setTable_objs]
      exact nodup_addObj_keys m _ hnd hfr

end StepMem

section Step

variable {sp : Spec V T} {al : Algo V T} {db dbK : DB V T} {tr : T} {K k : Nat}

/-- An old node, in the final state: its history up to K is the one after
T(K), up to K + 1 that with the entries of T(K + 1). -/
theorem step_final_old (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1))
    {x : NodeId} {nK : Node V} (hnK : dbK.P.get? x = some nK) :
    ∃ n, db.P.get? x = some n ∧ n.hist.upTo K = nK.hist ∧
      n.hist.upTo (K + 1) = nK.hist ++ addsFor (parts sp al dbK tr).c (K + 1) x ∧
      n.level = nK.level ∧ n.isData = nK.isData := by
  obtain ⟨n, hn, hl, hd, hh⟩ := hkK.grow x nK hnK
  have hnJ := step_P_old sp al dbK tr hkK.inv.len hnK
  rw [← step_P] at hnJ
  obtain ⟨n', hn', -, -, hh'⟩ := hkJ.grow x _ hnJ
  rw [hn, Option.some.injEq] at hn'
  subst hn'
  refine ⟨n, hn, by rw [hh, upTo_of_forall _ _ (hkK.inv.times x nK hnK)], ?_, hl, hd⟩
  rw [hh']
  exact upTo_of_forall _ _ (hkJ.inv.times x _ hnJ)

/-- A new node, in the final state: its history up to K + 1 is the entries of
T(K + 1). -/
theorem step_final_new (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1))
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {nn : NewNode}
    (hnn : nn ∈ (parts sp al dbK tr).c.new) :
    ∃ n, db.P.get? nn.id = some n ∧ n.hist.upTo (K + 1) = addsFor (parts sp al dbK tr).c (K + 1) nn.id ∧
      n.level = nn.level ∧ n.isData = nn.isData := by
  have hfr := hstep.fresh nn hnn
  have hnJ := step_P_new sp al dbK tr hkK.inv.len hfr
  cases hnew : newNodeOf (parts sp al dbK tr).c nn.id with
  | none => have := newNodeOf_isSome hnn; rw [hnew] at this; cases this
  | some m0 =>
    obtain ⟨nn', hnn', hid, hm0⟩ := newNodeOf_some hnew
    have : nn' = nn := eq_of_map_nodup hstep.distinct hnn' hnn hid
    subst this
    rw [hnew] at hnJ
    simp only [Option.map_some] at hnJ
    rw [← step_P] at hnJ
    obtain ⟨n, hn, hl, hd, hh⟩ := hkJ.grow nn'.id _ hnJ
    refine ⟨n, hn, ?_, by rw [hl, hm0], by rw [hd, hm0]⟩
    rw [hh, upTo_of_forall _ _ (hkJ.inv.times nn'.id _ hnJ), hm0]
    simp

end Step

section Main

variable {sp : Spec V T} {al : Algo V T} {db dbK : DB V T} {tr : T} {K k : Nat}

/-- The memory after the new nodes, and after the adds: what it holds. -/
structure ApplyFacts (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (mA : Mem V) : Prop where
  table : ∀ y, (mA.applyChange sp P j c).tableOf y = (c.new.foldl addNew mA).tableOf y
  obj : ∀ h, (mA.applyChange sp P j c).obj? h = ((c.new.foldl addNew mA).obj? h).map
    (updAll sp P j (c.new.foldl addNew mA)
      (c.adds.filter (fun a => (c.new.foldl addNew mA).canonicalOf a.1 == some h)))
  next : (mA.applyChange sp P j c).next = mA.next + c.new.length
  s : (mA.applyChange sp P j c).s = mA.s
  root : (mA.applyChange sp P j c).root = mA.root
  nodup : (mA.objs.map (·.1)).Nodup → (∀ h, mA.next ≤ h → mA.obj? h = none) →
    ((mA.applyChange sp P j c).objs.map (·.1)).Nodup

theorem applyFacts (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (mA : Mem V) :
    ApplyFacts sp P j c mA := by
  have h := adds_fold (sp := sp) (P := P) (j := j) (c.new.foldl addNew mA) c.adds [] (c.new.foldl addNew mA) rfl rfl rfl rfl
    (by intro h; cases (c.new.foldl addNew mA).obj? h <;> rfl)
  rw [← applyChange_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨p1, p2⟩ := foldl_addNew_parts c.new mA
  refine ⟨fun y => by unfold Mem.tableOf; rw [h1], fun h => by rw [h5 h]; rfl,
    by rw [h2, foldl_addNew_next], by rw [h3, p1], by rw [h4, p2], fun hnd hfr => ?_⟩
  exact h6 (foldl_addNew_nodup c.new mA hfr hnd)

theorem applyChange_canonicalOf (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (mA : Mem V) (y : NodeId) :
    (mA.applyChange sp P j c).canonicalOf y = (c.new.foldl addNew mA).canonicalOf y := by
  have hf := applyFacts sp P j c mA
  unfold Mem.canonicalOf
  rw [hf.table]
  cases (c.new.foldl addNew mA).tableOf y with
  | none => rfl
  | some h =>
    simp only
    rw [hf.obj h]
    cases (c.new.foldl addNew mA).obj? h with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      rw [(updAll_core sp P j _ _ o).2.2.2.2.1]

theorem addNew_canonicalOf_old (mA : Mem V) (N : List NewNode)
    (hfr : ∀ h, mA.next ≤ h → mA.obj? h = none)
    (htbl : ∀ y h, mA.tableOf y = some h → (mA.obj? h).isSome) {y : NodeId}
    (hy : y ∉ N.map (·.id)) : (N.foldl addNew mA).canonicalOf y = mA.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [foldl_addNew_table_old N mA y hy]
  cases ht : mA.tableOf y with
  | none => rfl
  | some h =>
    simp only
    have hlt : h < mA.next := by
      apply Nat.lt_of_not_le
      intro hle
      have := htbl y h ht
      rw [hfr h hle] at this; cases this
    rw [foldl_addNew_old N mA h hlt]

theorem addNew_canonicalOf_new (mA : Mem V) (N : List NewNode) (hnd : (N.map (·.id)).Nodup)
    {nn : NewNode} (hnn : nn ∈ N) :
    ∃ h, mA.next ≤ h ∧ (N.foldl addNew mA).canonicalOf nn.id = some h ∧
      (N.foldl addNew mA).obj? h = some (newObj nn) := by
  obtain ⟨h, hle, ht, ho⟩ := foldl_addNew_new N hnd mA nn hnn
  exact ⟨h, hle, ((N.foldl addNew mA).canonicalOf_eq_some nn.id h).mpr ⟨ht, _, ho, rfl⟩, ho⟩

end Main

/-! ### The memory after the change, compared with before -/

section After

variable {sp : Spec V T} {db : DB V T} {K : Nat} {P : Struct V} {j : Time} {c : Changes V}
  {mA : Mem V}

/-- Every object of the memory before is in the memory after, at the same
handle: a canonical one with the change's entries for its node, the others
as they were. -/
theorem after_old (hm : MemInv sp db K mA) (_hnd : (c.new.map (·.id)).Nodup) {h : Nat} {o : Obj V}
    (ho : mA.obj? h = some o) :
    (mA.applyChange sp P j c).obj? h = some (updAll sp P j (c.new.foldl addNew mA)
      (c.adds.filter (fun a => (c.new.foldl addNew mA).canonicalOf a.1 == some h)) o) := by
  rw [(applyFacts sp P j c mA).obj h, foldl_addNew_old c.new mA h (lt_next_of_obj? hm.fresh ho), ho]
  rfl

theorem after_obj (hm : MemInv sp db K mA) (hnd : (c.new.map (·.id)).Nodup) {h : Nat} {o : Obj V}
    (ho : (mA.applyChange sp P j c).obj? h = some o) :
    (∃ o0, mA.obj? h = some o0 ∧ o = updAll sp P j (c.new.foldl addNew mA)
      (c.adds.filter (fun a => (c.new.foldl addNew mA).canonicalOf a.1 == some h)) o0) ∨
    (mA.next ≤ h ∧ ∃ nn ∈ c.new, o = updAll sp P j (c.new.foldl addNew mA)
      (c.adds.filter (fun a => (c.new.foldl addNew mA).canonicalOf a.1 == some h)) (newObj nn) ∧
      (c.new.foldl addNew mA).tableOf nn.id = some h) := by
  rw [(applyFacts sp P j c mA).obj h] at ho
  cases h1 : (c.new.foldl addNew mA).obj? h with
  | none => rw [h1] at ho; cases ho
  | some o1 =>
    rw [h1] at ho
    simp only [Option.map_some, Option.some.injEq] at ho
    rcases foldl_addNew_obj c.new hnd mA hm.fresh h o1 h1 with ⟨hlt, h2⟩ | ⟨hle, nn, hnn, hon, ht⟩
    · left; exact ⟨o1, h2, ho.symm⟩
    · right; rw [hon] at ho; exact ⟨hle, nn, hnn, ho.symm, ht⟩

theorem after_table_old {y : NodeId} (hy : y ∉ c.new.map (·.id)) :
    (mA.applyChange sp P j c).tableOf y = mA.tableOf y := by
  rw [(applyFacts sp P j c mA).table, foldl_addNew_table_old c.new mA y hy]

theorem after_canon_old (hm : MemInv sp db K mA) {y : NodeId} (hy : y ∉ c.new.map (·.id)) :
    (mA.applyChange sp P j c).canonicalOf y = mA.canonicalOf y := by
  rw [applyChange_canonicalOf, addNew_canonicalOf_old mA c.new hm.fresh
    (fun y h ht => by obtain ⟨o, ho, -⟩ := hm.tbl y h ht; simp [ho]) hy]

theorem after_canon_new (hnd : (c.new.map (·.id)).Nodup) {nn : NewNode} (hnn : nn ∈ c.new) :
    ∃ h, mA.next ≤ h ∧ (mA.applyChange sp P j c).canonicalOf nn.id = some h ∧
      (c.new.foldl addNew mA).obj? h = some (newObj nn) := by
  obtain ⟨h, hle, hc, ho⟩ := addNew_canonicalOf_new mA c.new hnd hnn
  exact ⟨h, hle, by rw [applyChange_canonicalOf]; exact hc, ho⟩

/-- A node's canonical object after the new nodes: the adds for it are the
node's. -/
theorem adds_filter_node (hm : MemInv sp db K mA) (hnd : (c.new.map (·.id)).Nodup) {x : NodeId} {h : Nat}
    (hx : (c.new.foldl addNew mA).canonicalOf x = some h) :
    c.adds.filter (fun a => (c.new.foldl addNew mA).canonicalOf a.1 == some h) =
      c.adds.filter (fun a => a.1 == x) := by
  apply List.filter_congr
  intro a _
  -- two nodes with the same canonical object are the same
  have hnode : ∀ z, (c.new.foldl addNew mA).canonicalOf z = some h → ∃ o,
      (c.new.foldl addNew mA).obj? h = some o ∧ o.node = z := by
    intro z hz
    obtain ⟨ht, o, ho, -⟩ := ((c.new.foldl addNew mA).canonicalOf_eq_some z h).mp hz
    refine ⟨o, ho, ?_⟩
    rcases foldl_addNew_obj c.new hnd mA hm.fresh h o ho with ⟨hlt, h2⟩ | ⟨hle, nn, hnn, hon, ht'⟩
    · by_cases hzn : z ∈ c.new.map (·.id)
      · exfalso
        obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hzn
        obtain ⟨h', hle', ht', -⟩ := foldl_addNew_new c.new hnd mA nn hnn
        rw [hid, ht, Option.some.injEq] at ht'
        omega
      · rw [foldl_addNew_table_old c.new mA z hzn] at ht
        obtain ⟨o', ho', hn'⟩ := hm.tbl z h ht
        rw [h2, Option.some.injEq] at ho'
        rw [ho', hn']
    · rw [hon]
      -- the table maps nn.id and z to h
      by_cases hz : z = nn.id
      · rw [hz]; rfl
      · exfalso
        by_cases hzn : z ∈ c.new.map (·.id)
        · obtain ⟨nn2, hnn2, hid2⟩ := List.mem_map.mp hzn
          obtain ⟨h2, -, ht2, ho2⟩ := foldl_addNew_new c.new hnd mA nn2 hnn2
          rw [hid2, ht, Option.some.injEq] at ht2
          subst ht2
          rw [ho, Option.some.injEq] at ho2
          rw [hon] at ho2
          have : nn.id = nn2.id := by
            have := congrArg Obj.node ho2; simpa [newObj] using this
          rw [hid2] at this
          exact hz this.symm
        · rw [foldl_addNew_table_old c.new mA z hzn] at ht
          obtain ⟨o', ho', -⟩ := hm.tbl z h ht
          have := lt_next_of_obj? hm.fresh ho'
          omega
  obtain ⟨o, ho, hon⟩ := hnode x hx
  cases hc : (c.new.foldl addNew mA).canonicalOf a.1 == some h
  · simp only [Bool.false_eq, beq_eq_false_iff_ne, ne_eq]
    intro hax
    rw [hax] at hc
    simp [hx] at hc
  · simp only [beq_iff_eq] at hc
    obtain ⟨o', ho', hon'⟩ := hnode a.1 hc
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    simp [← hon', hon]

end After

/-! ### Transfer from before the change (time K) to after it (time K + 1) -/

section Transfer

variable {sp : Spec V T} {al : Algo V T} {db dbK : DB V T} {tr : T} {K k : Nat} {mA : Mem V}

/-- A node of the memory before is not new. -/
theorem MemInv.not_new (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {h : Nat} {o : Obj V}
    (ho : mA.obj? h = some o) : o.node ∉ (parts sp al dbK tr).c.new.map (·.id) := by
  intro hn
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hn
  obtain ⟨t, ht, hr⟩ := hm.born h o ho
  rw [hkK.reachable_eq hls ht] at hr
  have := Reach.isSome ((reachable_iff _ _ _ _).mp hr)
  rw [← hid, hstep.fresh nn hnn] at this
  cases this

/-- A node with a canonical object before is not new. -/
theorem MemInv.canon_not_new (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {y : NodeId}
    (hy : mA.canonicalOf y ≠ none) : y ∉ (parts sp al dbK tr).c.new.map (·.id) := by
  cases hc : mA.canonicalOf y with
  | none => exact absurd hc hy
  | some h =>
    obtain ⟨ht, o, ho, -⟩ := (mA.canonicalOf_eq_some y h).mp hc
    obtain ⟨o', ho', hn⟩ := hm.tbl y h ht
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    rw [← hn]
    exact hm.not_new hkK hls hstep ho

/-- An object that is not canonical before is unchanged after. -/
theorem MemInv.after_snap (hm : MemInv sp db K mA) (hnd : ((parts sp al dbK tr).c.new.map (·.id)).Nodup)
    {h : Nat} {o : Obj V} (ho : mA.obj? h = some o) (hc : o.canonical = false) (P : Struct V) (j : Time) :
    (mA.applyChange sp P j (parts sp al dbK tr).c).obj? h = some o := by
  rw [after_old hm hnd ho]
  congr
  have : (parts sp al dbK tr).c.adds.filter
      (fun a => ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf a.1 == some h) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _ ha
    simp only [beq_iff_eq] at ha
    obtain ⟨-, o', ho', hc'⟩ := ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf_eq_some a.1 h |>.mp ha
    rw [foldl_addNew_old _ mA h (lt_next_of_obj? hm.fresh ho), ho, Option.some.injEq] at ho'
    subst ho'
    rw [hc] at hc'; cases hc'
  rw [this]
  rfl

/-- A node that T(K + 1) does not change has the same history up to K + 1 as
up to K. -/
theorem histAt_unchanged (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1))
    {y : NodeId} {nK : Node V} (hnK : dbK.P.get? y = some nK)
    (hch : changed (parts sp al dbK tr).c y = false) : histAt db.P y (K + 1) = histAt db.P y K := by
  obtain ⟨n, hn, h1, h2, -, -⟩ := step_final_old (al := al) (tr := tr) hkK hkJ hnK
  have hadds : addsFor (parts sp al dbK tr).c (K + 1) y = [] := by
    simp only [addsFor, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
    intro a ha hay
    have : changed (parts sp al dbK tr).c y = true := by
      simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inr ⟨a, ha, hay⟩
    rw [hch] at this; cases this
  unfold histAt
  rw [hn]
  simp only [Option.map_some, Option.getD_some]
  rw [h1, h2, hadds, List.append_nil]

/-- A changed node, not new, has a canonical object before the change (it is on
a path). -/
theorem changed_canon (hkK : KCtx sp db dbK K) (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    {y : NodeId} {nK : Node V} (hnK : dbK.P.get? y = some nK)
    (hch : changed (parts sp al dbK tr).c y = true) : mA.canonicalOf y ≠ none := by
  apply hpath
  apply step_changed_path sp al dbK tr hkK.inv hstep hnK hch
  -- reachable at K + 1: A2 for an added entry, A3 for a new node
  simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hch
  rcases hch with ⟨nn, hnn, hid⟩ | ⟨a, ha, hay⟩
  · have := hstep.fresh nn hnn; rw [hid, hnK] at this; cases this
  · rw [← hay]; exact hstep.current a ha

theorem MemInv.snapOK_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K)
    (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    {h : Nat} {o : Obj V} (ho : mA.obj? h = some o) (hc : o.canonical = false) {w : Version V}
    (hs : SnapOK db mA K h o w) :
    SnapOK db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) (K + 1) h o w := by
  obtain ⟨r, a1, a2, a3, a4, a5⟩ := hs
  refine ⟨r, a1, a2, a3, a4, ?_⟩
  have hnn := hm.not_new hkK hls hstep ho
  rcases a5 with ⟨b1, b2⟩ | ⟨b1, b2, b3, b4⟩
  · exact Or.inl ⟨b1, fun e he => by have := b2 e he; omega⟩
  · right
    refine ⟨b1, b2, by rw [after_table_old hnn]; exact b3, ?_⟩
    -- the node is not changed: else its canonical object would be the table's object
    obtain ⟨t, ht, hr⟩ := hm.born h o ho
    rw [hkK.reachable_eq hls ht] at hr
    obtain ⟨nK, hnK⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
    cases hch : changed (parts sp al dbK tr).c o.node
    · rw [histAt_unchanged hkK hkJ hnK hch]; exact b4
    · exfalso
      have hcan := changed_canon hkK hstep hpath hnK hch
      cases hcc : mA.canonicalOf o.node with
      | none => exact hcan hcc
      | some hc' =>
        obtain ⟨ht', o', ho', hc''⟩ := (mA.canonicalOf_eq_some o.node hc').mp hcc
        rw [b3, Option.some.injEq] at ht'
        subst ht'
        rw [ho, Option.some.injEq] at ho'
        subst ho'
        rw [hc] at hc''; cases hc''

/-- Every object of the memory before is in the memory after, with the same
node, level, kind, flag and record; a non-canonical one is unchanged. -/
theorem MemInv.after_keep (hm : MemInv sp db K mA)
    (hnd : ((parts sp al dbK tr).c.new.map (·.id)).Nodup) {h : Nat} {o : Obj V}
    (ho : mA.obj? h = some o) (P : Struct V) (j : Time) :
    ∃ o', (mA.applyChange sp P j (parts sp al dbK tr).c).obj? h = some o' ∧ o'.node = o.node ∧
      o'.level = o.level ∧ o'.isData = o.isData ∧ o'.canonical = o.canonical ∧ o'.pos = o.pos ∧
      (o.canonical = false → o' = o) := by
  cases hc : o.canonical
  · exact ⟨o, hm.after_snap (al := al) (tr := tr) hnd ho hc P j, rfl, rfl, rfl, by rw [hc], rfl, fun _ => rfl⟩
  · obtain ⟨a1, a2, a3, -, a5, a6⟩ := updAll_core sp P j ((parts sp al dbK tr).c.new.foldl addNew mA)
      ((parts sp al dbK tr).c.adds.filter
        (fun a => ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf a.1 == some h)) o
    exact ⟨_, after_old hm hnd ho, a1, a2, a3, by rw [a5, hc], a6, fun h => by cases h⟩

theorem MemInv.readable_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K)
    (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    {t : Time} {h : Nat} {z : NodeId} (hr : Readable sp db mA K t h z) :
    Readable sp db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) (K + 1) t h z := by
  obtain ⟨o, ho, hz, hc⟩ := hr
  obtain ⟨o', ho', e1, -, -, e4, -, e6⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
  refine ⟨o', ho', by rw [e1, hz], ?_⟩
  cases hcan : o.canonical
  · rcases hc with hc | ⟨w, hw, hg⟩
    · rw [hc] at hcan; cases hcan
    · rw [e6 hcan]
      exact Or.inr ⟨w, hm.snapOK_after hkK hkJ hls hstep hpath ho hcan hw, hg⟩
  · exact Or.inl (by rw [e4, hcan])

theorem MemInv.canon_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {z : NodeId}
    (hz : mA.canonicalOf z ≠ none) :
    (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf z ≠ none := by
  rw [after_canon_old hm (hm.canon_not_new hkK hls hstep hz)]; exact hz

theorem MemInv.slotGood_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K)
    (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    {t : Time} {z : NodeId} {sl : Slot} (hg : SlotGood sp db mA K t z sl) :
    SlotGood sp db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) (K + 1) t z sl := by
  cases sl with
  | mem h' => exact hm.readable_after hkK hkJ hls hstep hpath hg
  | stream r =>
    rcases hg with hg | hg
    · exact Or.inl (hm.canon_after hkK hls hstep hg)
    · exact Or.inr hg

theorem MemInv.slotFresh_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    {z : NodeId} {sl : Slot} (hf : SlotFresh db mA z sl) :
    SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) z sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho, hc⟩ := hf
    obtain ⟨o', ho', -, -, e3, e4, e5, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
    exact ⟨o', ho', by rw [e4, e3, e5]; exact hc⟩
  | stream r =>
    rcases hf with hf | hf
    · exact Or.inl (hm.canon_after hkK hls hstep hf)
    · exact Or.inr hf

theorem MemInv.atLeast_after (hm : MemInv sp db K mA)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    {z : NodeId} {h' : Nat} {r' : Option Nat} (ha : AtLeast mA z h' r') :
    AtLeast (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) z h' r' := by
  obtain ⟨o, ho, hz, hc⟩ := ha
  obtain ⟨o', ho', e1, -, e3, e4, e5, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
  exact ⟨o', ho', by rw [e1, hz], by rw [e4, e3, e5]; exact hc⟩

theorem MemInv.memSlotOK_after (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    {z : NodeId} {h' : Nat} (hms : MemSlotOK mA z h') :
    MemSlotOK (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) z h' := by
  obtain ⟨o, ho, hz, hc⟩ := hms
  obtain ⟨o', ho', e1, -, -, e4, e5, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
  have hzn : z ∉ (parts sp al dbK tr).c.new.map (·.id) := by rw [← hz]; exact hm.not_new hkK hls hstep ho
  refine ⟨o', ho', by rw [e1, hz], ?_⟩
  rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp, hp0, hlt⟩
  · left; rw [after_table_old hzn]; exact hc
  · right
    obtain ⟨o0', ho0', -, -, -, -, f5, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho0 dbK.P (K + 1)
    exact ⟨by rw [e4, hcan], h0, o0', p, p0, by rw [after_table_old hzn]; exact ht, ho0',
      by rw [e5, hp], by rw [f5, hp0], hlt⟩

/-- A node that step 7 puts back passed the still-dirty test. -/
theorem fold_test_mem (al : Algo V T) (S : Stream V T) (P : Struct V) (i : Time) (x : NodeId) :
    ∀ (l : List NodeId) (D : Dirty) (L : List NodeId),
      x ∈ (l.foldl (fun (acc : Dirty × List NodeId) x =>
        if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L)).2 →
      x ∈ L ∨ ∃ D', al.stillDirty S P D' i x = true := by
  intro l
  induction l with
  | nil => intro D L h; exact Or.inl h
  | cons y l ih =>
    intro D L h
    simp only [List.foldl_cons] at h
    split at h
    · rename_i hy
      rcases ih _ _ h with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · rw [List.mem_singleton] at h2; subst h2; exact Or.inr ⟨D, hy⟩
      · exact Or.inr h1
    · exact ih D L h

/-- With BergDB's test, a node that step 7 puts back has a pointee. -/
theorem step_r7_pointee (hj : al.stillDirty = javaTest sp) (hinv : Inv sp dbK K) {x : NodeId}
    (hx : x ∈ (parts sp al dbK tr).r7.2) :
    ∃ n, (parts sp al dbK tr).P.get? x = some n ∧ pointees sp n.hist ≠ [] := by
  have ht : x ∈ (parts sp al dbK tr).taken := (step_r7_shape sp al dbK tr hinv.len).2.subset hx
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (isSome_of_isIndex (step_taken_index sp al dbK tr hinv ht))
  rw [parts_r7] at hx
  unfold stillDirtyOf at hx
  rcases fold_test_mem al _ _ _ x _ _ [] hx with h | ⟨D', hD'⟩
  · cases h
  · rw [hj] at hD'
    unfold javaTest at hD'
    rw [hn] at hD'
    refine ⟨n, hn, ?_⟩
    intro hnil
    simp only [hnil] at hD'
    cases hD'

/-- Record K + 1 of the final stream is the step's record. -/
theorem step_record (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) :
    db.S[K + 1]? = some (parts sp al dbK tr).R := by
  have h1 := hkJ.pre
  rw [step_S] at h1
  unfold Snew at h1
  have h2 : (dbK.S ++ [(parts sp al dbK tr).R])[K + 1]? = some (parts sp al dbK tr).R := by
    rw [List.getElem?_append_right (Nat.le_of_eq hkK.inv.len)]
    simp [hkK.inv.len]
  rw [h1, List.getElem?_take] at h2
  simpa using h2

/-- The nodes that have canonical objects after the change, at K + 1. -/
theorem MemInv.cover_after (hm : MemInv sp db K mA) (hctx : PCtx sp db k) (hkK : KCtx sp db dbK K)
    (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hsp : SpecOK sp) (hj : al.stillDirty = javaTest sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none) :
    Cover db (K + 1) (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) := by
  have hls : LiveSub sp := hsp.liveSub
  have hc0 := hm.cover
  -- a node with an entry at K + 1 has a canonical object after
  have hnewent : ∀ x n e, db.P.get? x = some n → e ∈ n.hist → e.time = K + 1 →
      (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf x ≠ none := by
    intro x n e hn he het
    have hr := hctx.inv.er x n hn e he
    rw [het, hkJ.reachable_eq hls (Nat.le_refl _)] at hr
    obtain ⟨nJ, hnJ⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
    cases hnK : dbK.P.get? x with
    | some nK =>
      obtain ⟨n', hn', -, h2, -, -⟩ := step_final_old (al := al) (tr := tr) hkK hkJ hnK
      rw [hn, Option.some.injEq] at hn'
      subst hn'
      have hch : changed (parts sp al dbK tr).c x = true := by
        have he' : e ∈ n.hist.upTo (K + 1) := mem_upTo.mpr ⟨he, by omega⟩
        rw [h2] at he'
        rcases List.mem_append.mp he' with h3 | h3
        · have := hkK.inv.times x nK hnK e h3; omega
        · obtain ⟨-, hm'⟩ := mem_addsFor.mp h3
          simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
          exact Or.inr ⟨(x, e.val), hm', rfl⟩
      exact hm.canon_after hkK hls hstep (changed_canon hkK hstep hpath hnK hch)
    | none =>
      rw [step_P] at hnJ
      rw [step_P_new sp al dbK tr hkK.inv.len hnK] at hnJ
      cases hnew : newNodeOf (parts sp al dbK tr).c x with
      | none => rw [hnew] at hnJ; cases hnJ
      | some m0 =>
        obtain ⟨nn, hnn, hid, -⟩ := newNodeOf_some hnew
        obtain ⟨h1, -, hc1, -⟩ := after_canon_new (sp := sp) (P := dbK.P) (j := K + 1) (mA := mA)
          hstep.distinct hnn
        rw [← hid, hc1]; simp
  refine ⟨by have := hm.sK; omega, hm.canon_after hkK hls hstep hc0.rootC, ?_,
    fun x w a b c' => hm.canon_after hkK hls hstep (hm.coverSec x w a b c'), ?_⟩
  · intro d R x hd1 hd2 hR hx
    rcases Nat.lt_or_ge d (K + 1) with hlt | hge
    · exact hm.canon_after hkK hls hstep (hm.coverGd d R x hd1 (by omega) hR hx)
    · have hd : d = K + 1 := by omega
      subst hd
      rw [step_record hkK hkJ, Option.some.injEq] at hR
      subst hR
      rw [parts_R] at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · -- marked: new, or on a path; touched: on a path
        obtain ⟨-, -, -, -, hmk | htx⟩ := (step_gd3_marked sp al dbK tr hsp hkK.inv hstep x).mp hx
        rotate_left
        · exact hm.canon_after hkK hls hstep (hpath x (step_touched_path sp al dbK tr hstep htx))
        by_cases hxn : x ∈ (parts sp al dbK tr).c.new.map (·.id)
        · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hxn
          obtain ⟨h1, -, hc1, -⟩ := after_canon_new (sp := sp) (P := dbK.P) (j := K + 1) (mA := mA)
            hstep.distinct hnn
          rw [← hid, hc1]; simp
        · have hmk' : marked sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (parts sp al dbK tr).c (K + 1) x = true := by
            rw [← parts_P' sp al dbK tr hkK.inv.len]; exact hmk
          exact hm.canon_after hkK hls hstep
            (hpath x (step_marked_path sp al dbK tr hsp hkK.inv hstep hmk' hxn))
      · -- put back: it has an entry, up to s, in (s, K], or at K + 1
        obtain ⟨nJ, hnJ, hptr⟩ := step_r7_pointee hj hkK.inv hx
        obtain ⟨y, hy⟩ : ∃ y, y ∈ pointees sp nJ.hist := by
          cases hp : pointees sp nJ.hist with
          | nil => exact absurd hp hptr
          | cons y _ => exact ⟨y, List.mem_cons_self⟩
        obtain ⟨e, he, -⟩ := (mem_pointees sp _ y).mp hy
        obtain ⟨n, hn, -, -, hh⟩ := hkJ.grow x nJ (by rw [step_P]; exact hnJ)
        have heJ : e ∈ n.hist := by
          have : e ∈ nJ.hist.upTo (K + 1) := mem_upTo.mpr ⟨he, hkJ.inv.times x nJ (by rw [step_P]; exact hnJ) e he⟩
          rw [← hh] at this
          exact (mem_upTo.mp this).1
        have hetK := hkJ.inv.times x nJ (by rw [step_P]; exact hnJ) e he
        rcases Nat.lt_or_ge (lastSp db.S) e.time with hes | hes
        · rcases Nat.lt_or_ge e.time (K + 1) with heK | heK
          · exact hm.canon_after hkK hls hstep (hm.coverNew x n e hn heJ hes (by omega))
          · exact hnewent x n e hn heJ (by omega)
        · -- a section version of x with an entry up to s
          have ht : x ∈ (parts sp al dbK tr).taken := (step_r7_shape sp al dbK tr hkK.inv.len).2.subset hx
          obtain ⟨w, hw, hwx⟩ := (step_written_iff sp al dbK tr hkK.inv hstep x).mpr (Or.inr ht)
          have hwK1 : db.S.versionAt (K + 1) x = some w := by
            unfold Stream.versionAt
            rw [step_record hkK hkJ]
            simp only
            rw [parts_R]
            exact find?_node_of_mem (step_vs_nodup sp al dbK tr hkK.inv hstep) hw hwx
          cases hnw : newest db.S (lastSp db.S) x with
          | none =>
            have := (newest_eq_none_iff db.S (lastSp db.S) x).mp hnw (K + 1) (by have := hm.sK; omega)
            rw [hwK1] at this; cases this
          | some w' =>
            obtain ⟨r2, hr2s, hw2, -⟩ := newest_ge hnw hwK1
            obtain ⟨-, -, n2, hn2, hwh2, -, hwd2⟩ := hctx.inv.version_node hw2
            rw [hn, Option.some.injEq] at hn2
            subst hn2
            apply hm.canon_after hkK hls hstep
            apply hm.coverSec x w' hnw
            · rw [hwd2]
              have := step_taken_index sp al dbK tr hkK.inv ht
              simp only [isIndex, hnJ] at this
              obtain ⟨-, -, hd', -⟩ := hkJ.grow x nJ (by rw [step_P]; exact hnJ)
              cases hdd : n.isData
              · rfl
              · exfalso
                obtain ⟨n'', hn'', -, hd'', -⟩ := hkJ.grow x nJ (by rw [step_P]; exact hnJ)
                rw [hn, Option.some.injEq] at hn''
                subst hn''
                rw [hd''] at hdd
                rw [hdd] at this
                cases this
            · rw [hwh2, upTo_upTo _ hr2s]
              intro hnil
              have : e ∈ n.hist.upTo (lastSp db.S) := mem_upTo.mpr ⟨heJ, hes⟩
              rw [hnil] at this
              cases this
  · intro x n e hn he hes heK
    rcases Nat.lt_or_ge e.time (K + 1) with hlt | hge
    · exact hm.canon_after hkK hls hstep (hm.coverNew x n e hn he hes (by omega))
    · exact hnewent x n e hn he (by omega)

/-- A non-canonical object after the change was there before. -/
theorem MemInv.after_noncanon (hm : MemInv sp db K mA)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {h : Nat} {o : Obj V}
    (ho : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).obj? h = some o)
    (hc : o.canonical = false) : mA.obj? h = some o := by
  rcases after_obj hm hstep.distinct ho with ⟨o0, ho0, he⟩ | ⟨-, nn, -, he, -⟩
  · obtain ⟨o0', ho0', -, -, -, e4, -, e6⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho0 dbK.P (K + 1)
    rw [ho, Option.some.injEq] at ho0'
    subst ho0'
    have hc0 : o0.canonical = false := by rw [← e4, hc]
    rw [e6 hc0]; exact ho0
  · exfalso
    have key : ∀ L, (updAll sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) L
        (newObj nn)).canonical = true := fun L => by
      rw [(updAll_core sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) L (newObj nn)).2.2.2.2.1]
      rfl
    rw [he, key] at hc
    cases hc

/-- The record of an object after the change holds a version of its node. -/
theorem MemInv.after_pos (hm : MemInv sp db K mA)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {h : Nat} {o : Obj V}
    (ho : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).obj? h = some o) {p : Nat}
    (hp : o.pos = some p) : (db.S.versionAt p o.node).isSome := by
  rcases after_obj hm hstep.distinct ho with ⟨o0, ho0, he⟩ | ⟨-, nn, -, he, -⟩
  · obtain ⟨a1, -, -, -, a5, a6⟩ := updAll_core sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA)
      ((parts sp al dbK tr).c.adds.filter
        (fun a => ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf a.1 == some h)) o0
    rw [he] at hp ⊢
    rw [a1]
    rw [a6] at hp
    cases hc0 : o0.canonical
    · obtain ⟨w, hw, -⟩ := hm.snap h o0 ho0 hc0
      obtain ⟨r, hr, hv, -⟩ := hw
      rw [hp, Option.some.injEq] at hr
      subst hr
      simp [hv]
    · obtain ⟨-, -, c3, -⟩ := hm.canon h o0 ho0 hc0
      exact c3 p hp
  · exfalso
    have key : ∀ L, (updAll sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) L
        (newObj nn)).pos = none := fun L => by
      rw [(updAll_core sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) L (newObj nn)).2.2.2.2.2]
      rfl
    rw [he, key] at hp
    cases hp

/-- A fresh slot after the change is good at every time up to K + 1 at which
its node is reachable. -/
theorem MemInv.fresh_good_after (hm : MemInv sp db K mA) (hctx : PCtx sp db k)
    (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    (hcov : Cover db (K + 1) (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c))
    {t : Time} (ht : t ≤ K + 1) {y : NodeId} (hr : reachable sp db.P t y = true) {sl : Slot}
    (hf : SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y sl)
    (hms : ∀ h', sl = Slot.mem h' → MemSlotOK (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y h') :
    SlotGood sp db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) (K + 1) t y sl := by
  cases sl with
  | stream r =>
    rcases hf with hf | ⟨n, r', w, hn, hd, hr', hw⟩ | ⟨hf, hsome⟩
    · exact Or.inl hf
    · exact Or.inr ⟨r', w, hr', hw, hctx.good_dataVer hn hd hw t⟩
    · cases hc : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf y with
      | some _ => left; simp [hc]
      | none =>
        right
        obtain ⟨v, hv, hg⟩ := hcov.mg hkJ hctx hc ht hr
        rw [hv] at hf
        exact ⟨v.recNo, v, hf, hctx.inv.lv_at hv, hg⟩
  | mem h' =>
    obtain ⟨o', ho', hc'⟩ := hf
    obtain ⟨o'', ho'', hn'', htab⟩ := hms h' rfl
    rw [ho', Option.some.injEq] at ho''
    subst ho''
    refine ⟨o', ho', hn'', ?_⟩
    cases hcan : o'.canonical
    · right
      have ho0 := hm.after_noncanon (al := al) (tr := tr) hstep ho' hcan
      obtain ⟨w, hw, -⟩ := hm.snap h' o' ho0 hcan
      refine ⟨w, hm.snapOK_after hkK hkJ hls hstep hpath ho0 hcan hw, fun _ => ?_⟩
      obtain ⟨r1, hp1, hv1, -, hd1, -⟩ := hw
      rw [hn''] at hv1
      rcases hc' with hc' | hc' | hc'
      · rw [hcan] at hc'; cases hc'
      · obtain ⟨-, -, n1, hn1, -, -, hd1'⟩ := hctx.inv.version_node hv1
        exact hctx.good_dataVer hn1 (by rw [← hd1', ← hd1, hc']) hv1 t
      · -- y's latest version; the slot names the table's object, so y has no canonical object
        cases hlv : db.S.lv y with
        | none => rw [hlv, hp1] at hc'; cases hc'
        | some v =>
          rw [hlv, hp1] at hc'
          simp only [Option.map_some, Option.some.injEq] at hc'
          have hnc : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf y = none := by
            rcases htab with htab | ⟨-, h0, o0, p, p0, ht0, ho0', hp, hp0, hlt⟩
            · exact canonicalOf_none_of_table htab ho' hcan
            · exfalso
              rw [hp1, Option.some.injEq] at hp
              subst hp
              have hpos0 := hm.after_pos (al := al) (tr := tr) hstep ho0' hp0
              -- the table's object for y is an object of y
              have hn0 : o0.node = y := by
                rcases after_obj hm hstep.distinct ho0' with ⟨o1, ho1, he1⟩ | ⟨hle1, nn, hnn, he1, ht1⟩
                · have hyn : y ∉ (parts sp al dbK tr).c.new.map (·.id) := by
                    rw [← hn'']; exact hm.not_new hkK hls hstep ho0
                  rw [after_table_old hyn] at ht0
                  obtain ⟨o2, ho2, hn2⟩ := hm.tbl y h0 ht0
                  rw [ho1, Option.some.injEq] at ho2
                  subst ho2
                  rw [he1, (updAll_core sp dbK.P (K + 1) _ _ o1).1, hn2]
                · exfalso
                  have hyn : y ∉ (parts sp al dbK tr).c.new.map (·.id) := by
                    rw [← hn'']; exact hm.not_new hkK hls hstep ho0
                  rw [after_table_old hyn] at ht0
                  obtain ⟨o2, ho2, -⟩ := hm.tbl y h0 ht0
                  have := lt_next_of_obj? hm.fresh ho2
                  omega
              rw [hn0] at hpos0
              obtain ⟨u0, hu0⟩ := Option.isSome_iff_exists.mp hpos0
              obtain ⟨v', hv', hle'⟩ := hctx.inv.le_lv hu0
              rw [hlv, Option.some.injEq] at hv'
              subst hv'
              omega
          obtain ⟨v', hv', hg⟩ := hcov.mg hkJ hctx hnc ht hr
          rw [hlv, Option.some.injEq] at hv'
          subst hv'
          have := hctx.inv.lv_at hlv
          rw [← hc', hv1, Option.some.injEq] at this
          rw [this]; exact hg
    · exact Or.inl rfl

/-! ### The slots of new pointers, after the change -/

theorem mem_of_lookup {β : Type} : ∀ (l : List (Nat × β)) (a : Nat) (b : β),
    List.lookup a l = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro a b h; cases h
  | cons q l ih =>
    intro a b h
    obtain ⟨c, x⟩ := q
    rw [lookup_cons_eq] at h
    split at h
    · rename_i hac; subst hac; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih a b h)

theorem lookup_of_mem {β : Type} : ∀ (l : List (Nat × β)), (l.map (·.1)).Nodup →
    ∀ (p : Nat × β), p ∈ l → List.lookup p.1 l = some p.2 := by
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons q l ih =>
    intro hnd p hp
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨c, x⟩ := q
    rw [lookup_cons_eq]
    rcases List.mem_cons.mp hp with h | h
    · subst h; simp
    · have : p.1 ≠ c := by
        intro he
        apply hnd.1
        simp only
        rw [← he]
        exact List.mem_map.mpr ⟨p, h, rfl⟩
      simp only [this, ↓reduceIte]
      exact ih hnd.2 p h

theorem mem_objs_of_obj? {m : Mem V} {h : Nat} {o : Obj V} (ho : m.obj? h = some o) : (h, o) ∈ m.objs :=
  mem_of_lookup m.objs h o ho

theorem obj?_of_mem_objs {m : Mem V} (hnd : (m.objs.map (·.1)).Nodup) {p : Nat × Obj V}
    (hp : p ∈ m.objs) : m.obj? p.1 = some p.2 :=
  lookup_of_mem m.objs hnd p hp

/-- A source of a copied slot is an object of the memory before the change. -/
theorem MemInv.src_old (hm : MemInv sp db K mA) (hnd : ((parts sp al dbK tr).c.new.map (·.id)).Nodup)
    {y : NodeId} {p : Nat × Obj V} (hp : p ∈ ((parts sp al dbK tr).c.new.foldl addNew mA).objs)
    (hsl : (p.2.slot? y).isSome) : mA.obj? p.1 = some p.2 := by
  have hnd1 := foldl_addNew_nodup (parts sp al dbK tr).c.new mA hm.fresh hm.nodup
  have ho := obj?_of_mem_objs hnd1 hp
  rcases foldl_addNew_obj _ hnd mA hm.fresh p.1 p.2 ho with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
  · exact h2
  · exfalso; rw [hon] at hsl; simp [newObj, Obj.slot?] at hsl

/-- The slot that NS1 gives is fresh after the change. -/
theorem MemInv.NS1_fresh (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {y : NodeId} {sl : Slot}
    (hns : NS1 sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) y = some sl) :
    SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y sl := by
  unfold NS1 at hns
  cases hc : ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf y with
  | some hc' =>
    rw [hc] at hns
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at hns
    subst hns
    have hcR : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf y = some hc' := by
      rw [applyChange_canonicalOf]; exact hc
    obtain ⟨-, o, ho, hco⟩ := ((mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf_eq_some y hc').mp hcR
    exact ⟨o, ho, Or.inl hco⟩
  | none =>
    rw [hc] at hns
    simp only [Option.map_none, Option.none_or] at hns
    unfold srcSlot at hns
    cases hf : ((parts sp al dbK tr).c.new.foldl addNew mA).objs.find? (srcOK sp dbK.P (K + 1) y) with
    | none => rw [hf] at hns; cases hns
    | some p =>
      rw [hf] at hns
      simp only [Option.bind_some] at hns
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      unfold srcOK at hpp
      simp only [Bool.and_eq_true] at hpp
      obtain ⟨⟨⟨hcan, hsl⟩, hrp⟩, hlive⟩ := hpp
      have hpo := hm.src_old (al := al) (tr := tr) hstep.distinct hpm hsl
      obtain ⟨-, ⟨n, hn, hh, -, -⟩, -, -, c5⟩ := hm.canon p.1 p.2 hpo hcan
      have hK1 : K + 1 - 1 = K := by omega
      rw [hK1] at hrp hlive
      have hrK : reachable sp db.P K p.2.node = true := by rw [hkK.reachable_eq hls (Nat.le_refl _)]; exact hrp
      split at hlive
      · rename_i nP hnP
        obtain ⟨n', hn', -, -, hh'⟩ := hkK.grow p.2.node nP hnP
        rw [hn, Option.some.injEq] at hn'
        subst hn'
        have hy : y ∈ sp.live p.2.hist := by
          rw [hh, hh', upTo_of_forall _ _ (hkK.inv.times _ nP hnP)]
          rw [upTo_of_forall _ _ (hkK.inv.times _ nP hnP)] at hlive
          exact List.contains_iff_mem.mp hlive
        obtain ⟨sl', hsl', hfr⟩ := c5 hrK y hy
        rw [hsl', Option.some.injEq] at hns
        subst hns
        exact hm.slotFresh_after hkK hls hstep hfr
      · cases hlive

/-- The node table after the change names objects of its nodes. -/
theorem MemInv.after_tbl (hm : MemInv sp db K mA)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {y : NodeId} {h : Nat}
    (ht : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).tableOf y = some h) :
    ∃ o, (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).obj? h = some o ∧ o.node = y := by
  by_cases hyn : y ∈ (parts sp al dbK tr).c.new.map (·.id)
  · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hyn
    obtain ⟨h1, -, ht1, ho1⟩ := foldl_addNew_new _ hstep.distinct mA nn hnn
    rw [(applyFacts sp dbK.P (K + 1) _ mA).table, ← hid, ht1, Option.some.injEq] at ht
    subst ht
    rw [(applyFacts sp dbK.P (K + 1) _ mA).obj h1, ho1]
    refine ⟨_, rfl, ?_⟩
    rw [(updAll_core sp dbK.P (K + 1) _ _ (newObj nn)).1, ← hid]
    rfl
  · rw [after_table_old hyn] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
    obtain ⟨o', ho', e1, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
    exact ⟨o', ho', by rw [e1, hn]⟩

/-- A node that adoption allows to be a new live child has an NS1 slot: it is
new (canonical), or a live child at K of a node on a path (a source). -/
theorem MemInv.NS1_some (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    {y : NodeId}
    (hy : y ∈ (parts sp al dbK tr).c.new.map (·.id) ∨ ∃ z nz, dbK.P.get? z = some nz ∧
      reachable sp dbK.P K z = true ∧
      (changed (parts sp al dbK tr).c z = true ∨
        reachable sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (K + 1) z = false) ∧
      y ∈ sp.live (nz.hist.upTo K)) :
    (NS1 sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) y).isSome := by
  unfold NS1
  cases hc : ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf y with
  | some _ => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    rcases hy with hy | ⟨z, nz, hnz, hrz, htz, hyz⟩
    · exfalso
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨h1, -, hc1, -⟩ := addNew_canonicalOf_new mA _ hstep.distinct hnn
      rw [hid, hc] at hc1; cases hc1
    · -- z is on a path: its canonical object is a source
      have hzp : z ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1) := by
        apply pathOf_mem (by simpa using hrz) hnz
        apply List.any_eq_true.mpr
        refine ⟨z, self_mem_reachFrom sp _ _ z nz, ?_⟩
        rcases htz with htz | htz
        · simp [htz]
        · simp [hrz, htz]
      cases hcz : mA.canonicalOf z with
      | none => exact absurd hcz (hpath z hzp)
      | some hz =>
        obtain ⟨htz', oz, hoz, hcanz⟩ := (mA.canonicalOf_eq_some z hz).mp hcz
        obtain ⟨oz', hoz', hnodez⟩ := hm.tbl z hz htz'
        rw [hoz, Option.some.injEq] at hoz'
        subst hoz'
        obtain ⟨-, ⟨n, hn, hh, -, -⟩, -, -, c5⟩ := hm.canon hz oz hoz hcanz
        obtain ⟨n', hn', -, -, hh'⟩ := hkK.grow z nz hnz
        rw [hnodez] at hn
        rw [hn, Option.some.injEq] at hn'
        subst hn'
        have hzK : reachable sp db.P K oz.node = true := by
          rw [hnodez, hkK.reachable_eq hls (Nat.le_refl _)]; exact hrz
        have hyz' : y ∈ sp.live oz.hist := by
          rw [hh, hh']; exact hyz
        obtain ⟨sl, hsl, -⟩ := c5 hzK y hyz'
        have hsrc : srcOK sp dbK.P (K + 1) y (hz, oz) = true := by
          unfold srcOK
          simp only [Bool.and_eq_true, show K + 1 - 1 = K by omega]
          refine ⟨⟨⟨hcanz, by rw [hsl]; rfl⟩, by rw [hnodez]; exact hrz⟩, ?_⟩
          rw [hnodez, hnz]
          simp only
          rw [upTo_of_forall _ _ (hkK.inv.times z nz hnz)] at hyz
          rw [upTo_of_forall _ _ (hkK.inv.times z nz hnz)]
          exact List.contains_iff_mem.mpr hyz
        have hmem : (hz, oz) ∈ ((parts sp al dbK tr).c.new.foldl addNew mA).objs := by
          apply mem_objs_of_obj?
          rw [foldl_addNew_old _ mA hz (lt_next_of_obj? hm.fresh hoz)]
          exact hoz
        unfold srcSlot
        cases hf : ((parts sp al dbK tr).c.new.foldl addNew mA).objs.find? (srcOK sp dbK.P (K + 1) y) with
        | none =>
          rw [List.find?_eq_none] at hf
          exact absurd hsrc (hf _ hmem)
        | some p =>
          simp only [Option.bind_some]
          have hpp := List.find?_some hf
          unfold srcOK at hpp
          simp only [Bool.and_eq_true] at hpp
          exact hpp.1.1.2

/-- A memory slot that a new pointer gets names the table's object, or an older
one. -/
theorem MemInv.combo_memSlot (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {o : Obj V} {y : NodeId} {h' : Nat}
    (ho : (∃ h0, mA.obj? h0 = some o) ∨ o.slots = [])
    (hcb : combo sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) o y = some (Slot.mem h')) :
    MemSlotOK (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y h' := by
  -- a slot of an object of the memory before
  have hold : ∀ h0 o0, mA.obj? h0 = some o0 → o0.slot? y = some (Slot.mem h') →
      MemSlotOK (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y h' :=
    fun h0 o0 ho0 hsl => hm.memSlotOK_after hkK hls hstep (hm.memSlot h0 o0 y h' ho0 hsl)
  unfold combo NS1 at hcb
  cases hc : ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf y with
  | some hc' =>
    rw [hc] at hcb
    simp only [Option.map_some, Option.some_or, Option.some.injEq, Slot.mem.injEq] at hcb
    subst hcb
    have hcR : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf y = some hc' := by
      rw [applyChange_canonicalOf]; exact hc
    obtain ⟨ht, -, -, -⟩ := ((mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).canonicalOf_eq_some y hc').mp hcR
    obtain ⟨o', ho', hn'⟩ := hm.after_tbl hstep ht
    exact ⟨o', ho', hn', Or.inl ht⟩
  | none =>
    rw [hc] at hcb
    simp only [Option.map_none, Option.none_or] at hcb
    unfold srcSlot at hcb
    cases hf : ((parts sp al dbK tr).c.new.foldl addNew mA).objs.find? (srcOK sp dbK.P (K + 1) y) with
    | some p =>
      rw [hf] at hcb
      simp only [Option.bind_some] at hcb
      have hpp := List.find?_some hf
      unfold srcOK at hpp
      simp only [Bool.and_eq_true] at hpp
      have hpm := List.mem_of_find?_eq_some hf
      obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hpp.1.1.2
      rw [hsl] at hcb
      simp only [Option.some_or, Option.some.injEq] at hcb
      rw [hcb] at hsl
      exact hold p.1 p.2 (hm.src_old (al := al) (tr := tr) hstep.distinct hpm (by rw [hsl]; rfl)) hsl
    | none =>
      rw [hf] at hcb
      simp only [Option.bind_none, Option.none_or] at hcb
      cases hos : o.slot? y with
      | some sl =>
        rw [hos] at hcb
        simp only [Option.some_or] at hcb
        rw [hcb] at hos
        rcases ho with ⟨h0, ho0⟩ | ho
        · exact hold h0 o ho0 hos
        · exfalso; unfold Obj.slot? at hos; rw [ho] at hos; cases hos
      | none =>
        rw [hos] at hcb
        simp only [Option.none_or] at hcb
        unfold anySlot at hcb
        cases ha : ((parts sp al dbK tr).c.new.foldl addNew mA).objs.find?
            (fun p => p.2.canonical && (p.2.slot? y).isSome) with
        | none => rw [ha] at hcb; cases hcb
        | some q =>
          rw [ha] at hcb
          simp only [Option.bind_some] at hcb
          have hqm := List.mem_of_find?_eq_some ha
          have hqp := List.find?_some ha
          simp only [Bool.and_eq_true] at hqp
          exact hold q.1 q.2 (hm.src_old (al := al) (tr := tr) hstep.distinct hqm hqp.2) hcb

/-- Every memory slot after the change names the table's object, or an older one. -/
theorem MemInv.memSlot_after_all (hm : MemInv sp db K mA) (hkK : KCtx sp db dbK K) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c) {h : Nat} {o : Obj V} {y : NodeId} {h' : Nat}
    (ho : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).obj? h = some o)
    (hsl : o.slot? y = some (Slot.mem h')) :
    MemSlotOK (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y h' := by
  rcases after_obj hm hstep.distinct ho with ⟨o0, ho0, he⟩ | ⟨-, nn, -, he, -⟩
  · rw [he, updAll_slot] at hsl
    split at hsl
    · exact hm.combo_memSlot hkK hls hstep (Or.inl ⟨h, ho0⟩) hsl
    · exact hm.memSlotOK_after hkK hls hstep (hm.memSlot h o0 y h' ho0 hsl)
  · rw [he, updAll_slot] at hsl
    split at hsl
    · exact hm.combo_memSlot hkK hls hstep (Or.inr rfl) hsl
    · simp [newObj, Obj.slot?] at hsl

/-- A canonical object after the change: what CanonOK asks at K + 1. -/
theorem MemInv.canon_after_ok (hm : MemInv sp db K mA) (hctx : PCtx sp db k)
    (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hls : LiveSub sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hph : PhysStep sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none)
    (hcov : Cover db (K + 1) (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c))
    {h : Nat} {o : Obj V} (ho : (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c).obj? h = some o)
    (hc : o.canonical = true) :
    CanonOK sp db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) (K + 1) h o := by
  -- the slot of a new pointer that adoption allows is fresh
  have hnew_fresh : ∀ (o0 : Obj V) (y : NodeId),
      (y ∈ (parts sp al dbK tr).c.new.map (·.id) ∨ ∃ z nz, dbK.P.get? z = some nz ∧
        reachable sp dbK.P K z = true ∧
        (changed (parts sp al dbK tr).c z = true ∨
          reachable sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (K + 1) z = false) ∧
        y ∈ sp.live (nz.hist.upTo K)) →
      ∃ sl, combo sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) o0 y = some sl ∧
        SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y sl := by
    intro o0 y hy
    obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (hm.NS1_some hkK hls hstep hpath hy)
    refine ⟨s1, by unfold combo; rw [hs1]; rfl, hm.NS1_fresh hkK hls hstep hs1⟩
  -- adoption for a new live child of x at K + 1
  have hadopt : ∀ x nJ, (parts sp al dbK tr).P.get? x = some nJ →
      reachable sp db.P (K + 1) x = true → ∀ y ∈ sp.live (nJ.hist.upTo (K + 1)),
      (∀ n0, dbK.P.get? x = some n0 → y ∉ sp.live (n0.hist.upTo K)) →
      y ∈ (parts sp al dbK tr).c.new.map (·.id) ∨ ∃ z nz, dbK.P.get? z = some nz ∧
        reachable sp dbK.P K z = true ∧
        (changed (parts sp al dbK tr).c z = true ∨
          reachable sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (K + 1) z = false) ∧
        y ∈ sp.live (nz.hist.upTo K) := by
    intro x nJ hnJ hr y hy hny
    by_cases hyn : y ∈ (parts sp al dbK tr).c.new.map (·.id)
    · exact Or.inl hyn
    · right
      have hrJ : reachable sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (K + 1) x = true := by
        rw [← parts_P' sp al dbK tr hkK.inv.len, ← step_P, ← hkJ.reachable_eq hls (Nat.le_refl _)]
        exact hr
      have hnJ' : (dbK.P.apply (K + 1) (parts sp al dbK tr).c).get? x = some nJ := by
        rw [← parts_P' sp al dbK tr hkK.inv.len]; exact hnJ
      obtain ⟨z, nz, hnz, hrz, htz, hyz⟩ := hph.adopt x nJ hrJ hnJ' y hy hny hyn
      exact ⟨z, nz, hnz, by simpa using hrz, htz, hyz⟩
  rcases after_obj hm hstep.distinct ho with ⟨o0, ho0, he⟩ | ⟨-, nn, hnn, he, ht1⟩
  · -- an object of the memory before
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := updAll_core sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA)
      ((parts sp al dbK tr).c.adds.filter
        (fun a => ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf a.1 == some h)) o0
    rw [← he] at a1 a2 a3 a4 a5 a6
    have hc0 : o0.canonical = true := by rw [← a5, hc]
    obtain ⟨c1, ⟨n, hn, hh, hl, hd⟩, c3, c4, c5⟩ := hm.canon h o0 ho0 hc0
    have hxn := hm.not_new hkK hls hstep ho0
    have hcx : mA.canonicalOf o0.node = some h := (mA.canonicalOf_eq_some _ h).mpr ⟨c1, o0, ho0, hc0⟩
    have hcx1 : ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf o0.node = some h := by
      rw [addNew_canonicalOf_old mA _ hm.fresh
        (fun y h ht => by obtain ⟨o, ho, -⟩ := hm.tbl y h ht; simp [ho]) hxn]
      exact hcx
    have hA := adds_filter_node hm hstep.distinct hcx1
    rw [hA] at a4
    -- the node before and after
    obtain ⟨t0, ht0, hr0⟩ := hm.born h o0 ho0
    rw [hkK.reachable_eq hls ht0] at hr0
    obtain ⟨nK, hnK⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr0))
    obtain ⟨n', hn', hK, hK1, -, -⟩ := step_final_old (al := al) (tr := tr) hkK hkJ hnK
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hoh : o.hist = n.hist.upTo (K + 1) := by
      rw [a4, hK1, hh, hK]; rfl
    have hslot : ∀ y, o.slot? y = if y ∈ ((parts sp al dbK tr).c.adds.filter (fun a => a.1 == o0.node)).flatMap
        (fun a => sp.ptrs a.2) then combo sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) o0 y
        else o0.slot? y := by
      intro y; rw [he, updAll_slot, hA]
    have hnJ := step_P_old sp al dbK tr hkK.inv.len hnK
    -- fresh at K + 1
    have hfresh : reachable sp db.P (K + 1) o.node = true → ∀ y ∈ sp.live o.hist,
        ∃ sl, o.slot? y = some sl ∧
          SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y sl := by
      intro hr y hy
      rw [a1] at hr
      have hrK : reachable sp db.P K o0.node = true := by
        have hrJ : reachable sp (dbK.P.apply (K + 1) (parts sp al dbK tr).c) (K + 1) o0.node = true := by
          rw [← parts_P' sp al dbK tr hkK.inv.len, ← step_P, ← hkJ.reachable_eq hls (Nat.le_refl _)]
          exact hr
        rcases hstep.noRes _ hrJ with h1 | h1
        · rw [hkK.reachable_eq hls (Nat.le_refl _)]; simpa using h1
        · exact absurd h1 hxn
      have hyJ : y ∈ sp.live ({ nK with hist := nK.hist ++ addsFor (parts sp al dbK tr).c (K + 1) o0.node }.hist.upTo (K + 1)) := by
        simp only
        rw [← hK1, upTo_upTo _ (Nat.le_refl _), ← hoh]
        exact hy
      by_cases hyo : y ∈ sp.live o0.hist
      · obtain ⟨sl0, hsl0, hf0⟩ := c5 hrK y hyo
        rw [hslot]
        split
        · unfold combo
          rw [hsl0]
          cases hns : NS1 sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) y with
          | some s1 => exact ⟨s1, rfl, hm.NS1_fresh hkK hls hstep hns⟩
          | none => exact ⟨sl0, rfl, hm.slotFresh_after hkK hls hstep hf0⟩
        · exact ⟨sl0, hsl0, hm.slotFresh_after hkK hls hstep hf0⟩
      · -- a new live child: a pointee of a new entry, from a node of a path or new
        have hny : ∀ n0, dbK.P.get? o0.node = some n0 → y ∉ sp.live (n0.hist.upTo K) := by
          intro n0 hn0
          rw [hnK, Option.some.injEq] at hn0
          subst hn0
          rw [upTo_of_forall _ _ (hkK.inv.times _ _ hnK), ← hK, ← hh]
          exact hyo
        rcases hph.liveNew o0.node _ (by rw [← parts_P' sp al dbK tr hkK.inv.len]; exact hnJ) y hyJ with
          ⟨n0, hn0, hy0⟩ | ⟨a, ha, hax, hya⟩
        · exact absurd hy0 (hny n0 hn0)
        · obtain ⟨sl, hcb, hfr⟩ := hnew_fresh o0 y (hadopt o0.node _ hnJ hr y hyJ hny)
          refine ⟨sl, ?_, hfr⟩
          rw [hslot]
          have : y ∈ ((parts sp al dbK tr).c.adds.filter (fun a => a.1 == o0.node)).flatMap
              (fun a => sp.ptrs a.2) :=
            List.mem_flatMap.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hax]⟩, hya⟩
          simp only [this, ↓reduceIte]
          exact hcb
    refine ⟨by rw [a1, after_table_old hxn]; exact c1, ⟨n, by rw [a1]; exact hn, hoh, by rw [a2, hl],
      by rw [a3, hd]⟩, fun p hp => by rw [a1]; exact c3 p (by rw [← a6]; exact hp), ?_, hfresh⟩
    intro t ht hr y hy
    by_cases htK : t ≤ K
    · -- the entries of K + 1 are not seen at t
      have hyo : y ∈ sp.live (o0.hist.upTo t) := by
        have : o.hist.upTo t = o0.hist.upTo t := by
          rw [a4, upTo_append]
          have : (addsFor (parts sp al dbK tr).c (K + 1) o0.node).upTo t = [] := by
            apply upTo_eq_nil
            intro e he
            rw [(mem_addsFor.mp he).1]
            omega
          rw [show ((parts sp al dbK tr).c.adds.filter (fun a => a.1 == o0.node)).map
            (fun a => (⟨K + 1, a.2⟩ : Entry V)) = addsFor (parts sp al dbK tr).c (K + 1) o0.node from rfl,
            this, List.append_nil]
        rw [← this]; exact hy
      obtain ⟨sl0, hsl0, hg0⟩ := c4 t htK (by rw [← a1]; exact hr) y hyo
      rw [hslot]
      split
      · unfold combo
        rw [hsl0]
        cases hns : NS1 sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA) y with
        | some s1 =>
          refine ⟨s1, rfl, hm.fresh_good_after hctx hkK hkJ hls hstep hpath hcov (by omega) ?_
            (hm.NS1_fresh hkK hls hstep hns) ?_⟩
          · rw [reachable_iff] at hr ⊢
            obtain ⟨e, he, hye⟩ := hls _ _ hyo
            have he' : e ∈ n.hist := by rw [hh] at he; exact (mem_upTo.mp (mem_upTo.mp he).1).1
            obtain ⟨ny, hny, hlt⟩ := hctx.inv.ptrs o0.node n hn e he' y hye
            exact Reach.child (by rw [← a1]; exact hr) hn (by
              rw [hh, upTo_upTo _ htK] at hyo; exact hyo) hny hlt
          · intro h' hs
            subst hs
            exact hm.combo_memSlot hkK hls hstep (Or.inl ⟨h, ho0⟩) (by unfold combo; rw [hns]; rfl)
        | none => exact ⟨sl0, rfl, hm.slotGood_after hkK hkJ hls hstep hpath hg0⟩
      · exact ⟨sl0, hsl0, hm.slotGood_after hkK hkJ hls hstep hpath hg0⟩
    · have ht1 : t = K + 1 := by omega
      subst ht1
      have hy' : y ∈ sp.live o.hist := by
        have hoK : o.hist.upTo (K + 1) = o.hist :=
          upTo_of_forall _ _ (fun e he => by rw [hoh] at he; exact (mem_upTo.mp he).2)
        rw [hoK] at hy
        exact hy
      obtain ⟨sl, hsl, hfr⟩ := hfresh hr y hy'
      refine ⟨sl, hsl, hm.fresh_good_after hctx hkK hkJ hls hstep hpath hcov (Nat.le_refl _) ?_ hfr ?_⟩
      · rw [reachable_iff] at hr ⊢
        obtain ⟨e, he, hye⟩ := hls _ _ hy'
        rw [hoh] at he
        obtain ⟨ny, hny, hlt⟩ := hctx.inv.ptrs o.node n (by rw [a1]; exact hn) e (mem_upTo.mp he).1 y hye
        exact Reach.child hr (by rw [a1]; exact hn) (by rw [← hoh]; exact hy') hny hlt
      · intro h' hs; subst hs
        exact hm.memSlot_after_all hkK hls hstep ho hsl
  · -- a new node
    obtain ⟨a1, a2, a3, a4, -, a6⟩ := updAll_core sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA)
      ((parts sp al dbK tr).c.adds.filter
        (fun a => ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf a.1 == some h)) (newObj nn)
    rw [← he] at a1 a2 a3 a4 a6
    obtain ⟨h2, -, ht2, ho2⟩ := foldl_addNew_new _ hstep.distinct mA nn hnn
    rw [ht1, Option.some.injEq] at ht2
    subst ht2
    have hcx1 : ((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf nn.id = some h :=
      (((parts sp al dbK tr).c.new.foldl addNew mA).canonicalOf_eq_some nn.id h).mpr ⟨ht1, _, ho2, rfl⟩
    have hA := adds_filter_node hm hstep.distinct hcx1
    rw [hA] at a4
    obtain ⟨n, hn, hn1, hl, hd⟩ := step_final_new (al := al) (tr := tr) hkK hkJ hstep hnn
    have hoh : o.hist = n.hist.upTo (K + 1) := by rw [a4, hn1]; rfl
    have hnode : o.node = nn.id := a1
    have hslot : ∀ y, o.slot? y = if y ∈ ((parts sp al dbK tr).c.adds.filter (fun a => a.1 == nn.id)).flatMap
        (fun a => sp.ptrs a.2) then combo sp dbK.P (K + 1) ((parts sp al dbK tr).c.new.foldl addNew mA)
          (newObj nn) y else (newObj (V := V) nn).slot? y := by
      intro y; rw [he, updAll_slot, hA]
    have hfr0 := hstep.fresh nn hnn
    have hnJ := step_P_new sp al dbK tr hkK.inv.len hfr0
    have hnJ' : (parts sp al dbK tr).P.get? nn.id =
        some (Node.mk nn.level nn.isData (addsFor (parts sp al dbK tr).c (K + 1) nn.id)) := by
      rw [hnJ]
      cases hnew : newNodeOf (parts sp al dbK tr).c nn.id with
      | none => have := newNodeOf_isSome hnn; rw [hnew] at this; cases this
      | some m0 =>
        obtain ⟨nn', hnn', hid, hm0⟩ := newNodeOf_some hnew
        have : nn' = nn := eq_of_map_nodup hstep.distinct hnn' hnn hid
        subst this
        rw [hm0]; simp
    have hfresh : reachable sp db.P (K + 1) o.node = true → ∀ y ∈ sp.live o.hist,
        ∃ sl, o.slot? y = some sl ∧
          SlotFresh db (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) y sl := by
      intro hr y hy
      rw [hnode] at hr
      have hyJ : y ∈ sp.live ((Node.mk nn.level nn.isData
          (addsFor (parts sp al dbK tr).c (K + 1) nn.id) : Node V).hist.upTo (K + 1)) := by
        simp only
        rw [← hn1, upTo_upTo _ (Nat.le_refl _), ← hoh]
        exact hy
      have hny : ∀ n0, dbK.P.get? nn.id = some n0 → y ∉ sp.live (n0.hist.upTo K) := by
        intro n0 hn0; rw [hfr0] at hn0; cases hn0
      rcases hph.liveNew nn.id _ (by rw [← parts_P' sp al dbK tr hkK.inv.len]; exact hnJ') y hyJ with
        ⟨n0, hn0, -⟩ | ⟨a, ha, hax, hya⟩
      · rw [hfr0] at hn0; cases hn0
      · obtain ⟨sl, hcb, hfr⟩ := hnew_fresh (newObj nn) y (hadopt nn.id _ hnJ' hr y hyJ hny)
        refine ⟨sl, ?_, hfr⟩
        rw [hslot]
        have : y ∈ ((parts sp al dbK tr).c.adds.filter (fun a => a.1 == nn.id)).flatMap
            (fun a => sp.ptrs a.2) :=
          List.mem_flatMap.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hax]⟩, hya⟩
        simp only [this, ↓reduceIte]
        exact hcb
    refine ⟨by rw [hnode, (applyFacts sp dbK.P (K + 1) _ mA).table]; exact ht1,
      ⟨n, by rw [hnode]; exact hn, hoh, by rw [a2, hl]; rfl, by rw [a3, hd]; rfl⟩,
      fun p hp => (by rw [a6] at hp; cases hp), ?_, hfresh⟩
    intro t ht hr y hy
    by_cases htK : t ≤ K
    · exfalso
      have : o.hist.upTo t = [] := by
        rw [hoh, upTo_upTo _ (by omega), ← upTo_upTo _ htK]
        have : n.hist.upTo K = [] := by
          rw [← upTo_upTo _ (Nat.le_succ K), hn1]
          apply upTo_eq_nil
          intro e he
          rw [(mem_addsFor.mp he).1]
          omega
        rw [this]; rfl
      rw [this, live_nil hls] at hy
      cases hy
    · have ht1' : t = K + 1 := by omega
      subst ht1'
      have hy' : y ∈ sp.live o.hist := by
        have hoK : o.hist.upTo (K + 1) = o.hist :=
          upTo_of_forall _ _ (fun e he => by rw [hoh] at he; exact (mem_upTo.mp he).2)
        rw [hoK] at hy
        exact hy
      obtain ⟨sl, hsl, hfr⟩ := hfresh hr y hy'
      refine ⟨sl, hsl, hm.fresh_good_after hctx hkK hkJ hls hstep hpath hcov (Nat.le_refl _) ?_ hfr ?_⟩
      · rw [reachable_iff] at hr ⊢
        obtain ⟨e, he, hye⟩ := hls _ _ hy'
        rw [hoh] at he
        obtain ⟨ny, hny, hlt⟩ := hctx.inv.ptrs o.node n (by rw [hnode]; exact hn) e (mem_upTo.mp he).1 y hye
        exact Reach.child hr (by rw [hnode]; exact hn) (by rw [← hoh]; exact hy') hny hlt
      · intro h' hs; subst hs
        exact hm.memSlot_after_all hkK hls hstep ho hsl

/-- The change of transaction K + 1 applied to the canonical objects keeps the
invariant, from K to K + 1, once the writer has reached the nodes of the paths. -/
theorem MemInv.applyChange_ok (hm : MemInv sp db K mA) (hctx : PCtx sp db k)
    (hkK : KCtx sp db dbK K) (hkJ : KCtx sp db (step sp al dbK tr) (K + 1)) (hsp : SpecOK sp)
    (hj : al.stillDirty = javaTest sp)
    (hstep : StepOK sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hph : PhysStep sp dbK.P (K + 1) (parts sp al dbK tr).c)
    (hpath : ∀ x ∈ pathOf sp dbK.P (parts sp al dbK tr).c (K + 1), mA.canonicalOf x ≠ none) :
    MemInv sp db (K + 1) (mA.applyChange sp dbK.P (K + 1) (parts sp al dbK tr).c) := by
  have hls : LiveSub sp := hsp.liveSub
  have hf := applyFacts sp dbK.P (K + 1) (parts sp al dbK tr).c mA
  have hcov := hm.cover_after hctx hkK hkJ hsp hj hstep hpath
  have hrootn : SIS.root ∉ (parts sp al dbK tr).c.new.map (·.id) := by
    intro hr
    obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hr
    have := hstep.fresh nn hnn
    rw [hid] at this
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hkK.inv.rootIn
    rw [hn0] at this; cases this
  refine ⟨by rw [hf.s]; exact hm.sEq, hcov.sK, ?_, hf.nodup hm.nodup hm.fresh, ?_, ?_, ?_, ?_, ?_, ?_,
    hcov.coverGd, hcov.coverSec, hcov.coverNew⟩
  · -- fresh handles
    intro h hh
    rw [hf.next] at hh
    rw [hf.obj h, foldl_addNew_fresh _ mA hm.fresh h (by rw [foldl_addNew_next]; exact hh)]
    rfl
  · -- the root
    obtain ⟨ht, o, ho, hc, hn⟩ := hm.root
    obtain ⟨o', ho', e1, -, -, e4, -, -⟩ := hm.after_keep (al := al) (tr := tr) hstep.distinct ho dbK.P (K + 1)
    rw [hf.root]
    exact ⟨by rw [after_table_old hrootn]; exact ht, o', ho', by rw [e4, hc], by rw [e1, hn]⟩
  · -- the table
    intro y h ht
    exact hm.after_tbl hstep ht
  · -- born
    intro h o ho
    rcases after_obj hm hstep.distinct ho with ⟨o0, ho0, he⟩ | ⟨-, nn, hnn, he, -⟩
    · obtain ⟨t, ht, hr⟩ := hm.born h o0 ho0
      refine ⟨t, by omega, ?_⟩
      rw [he, (updAll_core sp dbK.P (K + 1) _ _ o0).1]
      exact hr
    · refine ⟨K + 1, Nat.le_refl _, ?_⟩
      rw [he, (updAll_core sp dbK.P (K + 1) _ _ (newObj nn)).1]
      have := hstep.newReachable nn hnn
      rw [← parts_P' sp al dbK tr hkK.inv.len, ← step_P, ← hkJ.reachable_eq hls (Nat.le_refl _)] at this
      exact this
  · -- canonical objects
    intro h o ho hc
    exact hm.canon_after_ok hctx hkK hkJ hls hstep hph hpath hcov ho hc
  · -- snapshots
    intro h o ho hc
    have ho0 := hm.after_noncanon (al := al) (tr := tr) hstep ho hc
    obtain ⟨w, hw, hss1, hss2⟩ := hm.snap h o ho0 hc
    refine ⟨w, hm.snapOK_after hkK hkJ hls hstep hpath ho0 hc hw, hss1, ?_⟩
    intro y sl hsl
    rcases hss2 y sl hsl with h2 | ⟨h', h2, h3⟩
    · exact Or.inl h2
    · exact Or.inr ⟨h', h2, hm.atLeast_after hstep h3⟩
  · -- memory slots
    intro h o y h' ho hsl
    exact hm.memSlot_after_all hkK hls hstep ho hsl

/-- The nodes of gd(K + 1) all have canonical objects after the change, so
`canonicalNode` changes nothing. -/
theorem canonicalNode_noop (sp : Spec V T) (S : Stream V T) (m : Mem V) (x : NodeId)
    (hx : m.canonicalOf x ≠ none) : m.canonicalNode sp S x = m := by
  unfold Mem.canonicalNode
  cases hc : m.canonicalOf x with
  | none => exact absurd hc hx
  | some _ => rfl

theorem foldl_canonicalNode_noop (sp : Spec V T) (S : Stream V T) (m : Mem V) (L : List NodeId)
    (hL : ∀ x ∈ L, m.canonicalOf x ≠ none) : L.foldl (Mem.canonicalNode sp S) m = m := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.foldl_cons]
    rw [canonicalNode_noop sp S m x (hL x List.mem_cons_self)]
    exact ih (fun y hy => hL y (List.mem_cons_of_mem x hy))

end Transfer

end SIS
