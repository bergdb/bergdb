/-
The contract package (bergdb 030-07): the touch, A6' and A-COPY in the
contract's words (BridgeTop.lean: `touchOk`, `adoptOk`, `copyOk`) give the
model's (`TouchOK`, `adoptAt`, `CopyStep`), for the model's structure of a
history with the contract's top. So a history that meets every clause in the
contract's words (`MeetsFull`) meets `MeetsBridge` and `MeetsEvict`
(`MeetsFull.meetsBridge`, `MeetsFull.meetsEvict`).
-/
import Mathlib.Tactic
import SIS.Proof.Mark
import Contract.Proof.BridgeTop

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

/-! ## Key klongs and pointers -/

/-- A key klong has its key entry. -/
theorem entriesFrom_key : ∀ (r pre : List Klong) (t : Nat) (b : List Nat) (c : Nat) (y : NodeId),
    Klong.key c y ∈ r → ∃ t', (⟨t', BVal.key c y⟩ : Entry BVal) ∈ entriesFrom pre t b r
  | [], _, _, _, _, _, h => by simp at h
  | k :: r, pre, t, b, c, y, h => by
    cases k with
    | time t' =>
      have h1 : Klong.key c y ∈ r := by simpa using h
      obtain ⟨t'', ht⟩ := entriesFrom_key r _ t' b c y h1
      exact ⟨t'', by simpa [entriesFrom] using ht⟩
    | key c' y' =>
      rcases List.mem_cons.mp h with h1 | h1
      · injection h1 with h2 h3
        subst h2 h3
        exact ⟨t, by simp [entriesFrom]⟩
      · obtain ⟨t'', ht⟩ := entriesFrom_key r _ t b c y h1
        exact ⟨t'', by simp only [entriesFrom]; exact List.mem_cons_of_mem _ ht⟩
    | del bits =>
      have h1 : Klong.key c y ∈ r := by simpa using h
      obtain ⟨t'', ht⟩ := entriesFrom_key r _ t bits c y h1
      exact ⟨t'', by simp only [entriesFrom]; exact List.mem_cons_of_mem _ ht⟩

/-- The model's pointees of a key node: the pointees of its key klongs, live
or dead. -/
theorem mem_pointees_entries (h : BHist) (ks : List Klong) (y : NodeId) :
    y ∈ SIS.pointees h.spec (entriesOf ks) ↔ ∃ c, Klong.key c y ∈ ks := by
  simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hy⟩
    exact entriesFrom_ptr ks [] 0 [] e he y hy
  · rintro ⟨c, hc⟩
    obtain ⟨t, ht⟩ := entriesFrom_key ks [] 0 [] c y hc
    exact ⟨_, ht, by simp [BHist.spec, bspec, bptrs]⟩

/-- An entry value that a node of the tree got is a key entry, a delete entry
or a value's. -/
theorem newVals_kind {s s' : Tree} {x : NodeId} {v : BVal} (hv : v ∈ newVals s s' x) :
    (∃ c y, v = .key c y) ∨ (∃ cs, v = .del cs) ∨ ∃ d, v = .data d := by
  unfold newVals at hv
  cases ho : s'.obj x with
  | none => rw [ho] at hv; simp at hv
  | some o =>
    rw [ho] at hv
    cases o with
    | val d =>
      simp only at hv
      split at hv
      · simp at hv
      · exact Or.inr (Or.inr ⟨d, by simpa using hv⟩)
    | key n' =>
      simp only [List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv
      rcases entriesFrom_kind n'.ks [] 0 [] e (List.mem_of_mem_drop he) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)

section Words

variable {p : Params} {h : BHist} {top : Nat → Top} {j : Nat}

/-! ## The walks -/

/-- What the model reaches: the root, the super root, or a node that the tree
reaches. -/
theorem TopInv.reach_cases (ti : TopInv h top j) (hi : BInv h j) {zl : NodeId} {nl : TopNode}
    (hl : (top j).getLast? = some (zl, nl)) {x : NodeId} (hx : Reach h.spec (h.P j) j x) :
    x = SIS.root ∨ x = zl ∨ x ∈ reach (h.tree j) := by
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  have hzz : z = zl := by
    have h1 := ti.rootNode
    rw [h0] at h1
    injection h1 with h1
    rw [h1] at hl0
    have h2 := (ti.reach_last hl).2.2.1
    rw [hl0] at h2
    simpa using h2
  rw [← hzz]
  exact hi.reach3 h0 hl0 hz hly hroot hy hx

/-- Below a node of the tree, the model reaches what the walk reaches. -/
theorem BInv.walk_reachFrom (hi : BInv h j) : ∀ (f : Nat) (x : NodeId) (N : Node BVal),
    (h.P j).get? x = some N → ∀ z, z ∈ reachAt (h.tree j) f x →
    z ∈ SIS.reachFrom h.spec (h.P j) j x N
  | 0, x, N, _, z, hz => by
    simp only [reachAt, List.mem_singleton] at hz
    rw [hz]
    exact SIS.self_mem_reachFrom _ _ _ _ _
  | f + 1, x, N, hN, z, hz => by
    simp only [reachAt, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact SIS.self_mem_reachFrom _ _ _ _ _
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
          rw [hP] at hN
          injection hN with hN
          subst hN
          obtain ⟨oy, hoy, hlt⟩ := hi.lev x n ho c y (live_mem_key hy)
          obtain ⟨M, hM, hMl⟩ := hi.node_of hoy
          have ih := hi.walk_reachFrom f y M hM z hzy
          exact SIS.reachFrom_child_sub h.spec ((hlive y).mpr ⟨c, hy⟩) hM
            (by rw [hMl]; exact hlt) z ih

/-- And the walk reaches what the model reaches below a node of the tree. -/
theorem BInv.reachFrom_walk (hi : BInv h j) : ∀ (k f : Nat) (x : NodeId) (o : Obj)
    (N : Node BVal), N.level < k → (h.tree j).obj x = some o → lvl o < f →
    (h.P j).get? x = some N → ∀ z, z ∈ SIS.reachFrom h.spec (h.P j) j x N →
    z ∈ reachAt (h.tree j) f x
  | 0, _, _, _, _, hk, _, _, _, _, _ => by omega
  | k + 1, f, x, o, N, hk, ho, hf, hN, z, hz => by
    rw [SIS.reachFrom_eq] at hz
    simp only [List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨y, hy, hz⟩
    · exact mem_reachAt_self _ _ _
    · cases o with
      | val v => exact absurd hy (hi.val_live ho hN j y)
      | key n =>
        obtain ⟨hP, hlive⟩ := hi.key_live ho
        rw [hP] at hN
        injection hN with hN
        subst hN
        obtain ⟨c, hc⟩ := (hlive y).mp hy
        obtain ⟨oy, hoy, hlt⟩ := hi.lev x n ho c y (live_mem_key hc)
        obtain ⟨M, hM, hMl⟩ := hi.node_of hoy
        rw [hM] at hz
        have hlt' : M.level < n.level := by rw [hMl]; exact hlt
        simp only [hlt', ite_true] at hz
        cases f with
        | zero => omega
        | succ f =>
          have hf' : n.level < f + 1 := hf
          have ih := hi.reachFrom_walk k f y oy M (by simp only at hk; omega) hoy (by omega) hM z hz
          simp only [reachAt, List.mem_cons, ho]
          right
          exact List.mem_flatMap.mpr ⟨(c, y), hc, ih⟩

/-! ## A6' -/

/-- A top node that is not the super root is not reachable. -/
theorem TopInv.unreach (ti : TopInv h top j) (hi : BInv h j) {zl : NodeId} {nl : TopNode}
    (hl : (top j).getLast? = some (zl, nl)) {zm : NodeId × TopNode} (hzm : zm ∈ top j)
    (hne : zm.1 ≠ zl) : SIS.reachable h.spec (h.P j) j zm.1 = false := by
  cases hr : SIS.reachable h.spec (h.P j) j zm.1 with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, _, _, hnr, hno, _⟩ := ti.topNode zm hzm
    rcases ti.reach_cases hi hl ((SIS.reachable_iff _ _ _ _).mp hr) with h1 | h1 | h1
    · exact hnr h1
    · exact hne h1
    · have := hi.reach_obj h1
      rw [hno] at this
      cases this

/-- A6' in the contract's words gives the model's A6'. -/
theorem adopt_of (hi : BInv h j) (ti : TopInv h top j) (ha : adoptOk (h.tree j) = true) :
    SIS.adoptAt h.spec (h.P j) j := by
  obtain ⟨zl, nl, hl, hml, hroot⟩ := ti.last
  obtain ⟨hr0, hrz, hl0, hly⟩ := ti.reach_last hl
  intro x N hx hN y hy hnl
  rw [SIS.reachable_iff] at hx
  rcases ti.reach_cases hi hl hx with rfl | rfl | hin
  · -- the root: its other pointees are older top nodes
    rw [ti.rootNode] at hN
    injection hN with hN
    subst hN
    simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap] at hy
    obtain ⟨e, he, hye⟩ := hy
    unfold rootHist at he
    obtain ⟨zm, hzm, rfl⟩ := List.mem_map.mp he
    have hyz : y = zm.1 := by simpa [BHist.spec, bspec, bptrs] using hye
    subst hyz
    right; left
    apply ti.unreach hi hl hzm
    intro heq
    apply hnl
    show zm.1 ∈ h.spec.live (History.upTo (rootHist (top j)) j)
    rw [hl0, heq]
    exact List.mem_singleton_self _
  · -- the super root: its other pointees are older top nodes
    obtain ⟨hN', _⟩ := ti.topNode _ hml
    rw [hN'] at hN
    injection hN with hN
    subst hN
    simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap] at hy
    obtain ⟨e, he, hye⟩ := hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    rcases mem_ptrs_topVals hv hye with h2 | ⟨q, hq, h2⟩
    · exfalso
      apply hnl
      show y ∈ h.spec.live (History.upTo ((topVals nl).map (fun v => (⟨nl.time, v⟩ : Entry BVal))) j)
      rw [hly, h2]
      exact List.mem_singleton_self _
    · right; left
      subst h2
      obtain ⟨ny, hym, _, hlt⟩ := ti.good.skip hml hq
      apply ti.unreach hi hl hym
      intro heq
      have hny : ny = nl := by
        have h4 := ti.good.lookup hym
        simp only at heq
        rw [heq, ti.good.lookup hml] at h4
        injection h4 with h4
        exact h4.symm
      rw [hny] at hlt
      exact Nat.lt_irrefl _ hlt
  · -- a node of the tree
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hi.reach_obj hin)
    cases o with
    | val v =>
      obtain ⟨t0, _, ht0⟩ := hi.rep x _ ho
      rw [hN] at ht0
      injection ht0 with ht0
      subst ht0
      simp [SIS.pointees, BHist.spec, bspec, bptrs] at hy
    | key n =>
      obtain ⟨hP, hlive⟩ := hi.key_live ho
      rw [hP] at hN
      injection hN with hN
      subst hN
      obtain ⟨c, hc⟩ := (mem_pointees_entries h n.ks y).mp hy
      obtain ⟨oy, hoy, _⟩ := hi.lev x n ho c y hc
      simp only [adoptOk, List.all_eq_true] at ha
      have h1 := ha x hin
      rw [ho] at h1
      simp only [List.all_eq_true] at h1
      have h2 := h1 _ hc
      simp only [Bool.or_eq_true] at h2
      rcases h2 with ((h3 | h3) | h3) | h3
      · exfalso
        apply hnl
        apply (hlive y).mpr
        have h4 : y ∈ (live n.ks).map (·.2) := by simpa using h3
        obtain ⟨cy, hcy, rfl⟩ := List.mem_map.mp h4
        exact ⟨cy.1, hcy⟩
      · left
        rw [hoy] at h3
        cases oy with
        | key m => simp at h3
        | val v =>
          obtain ⟨t0, _, ht0⟩ := hi.rep y _ hoy
          exact ⟨_, ht0, rfl⟩
      · right; left
        cases hr : SIS.reachable h.spec (h.P j) j y with
        | false => rfl
        | true =>
          exfalso
          rcases ti.reach_cases hi hl ((SIS.reachable_iff _ _ _ _).mp hr) with h4 | h4 | h4
          · rw [h4, ti.s0] at hoy; cases hoy
          · rw [h4, (ti.topNode _ hml).2.2.2.2.1] at hoy; cases hoy
          · simp [h4] at h3
      · right; right
        exact hi.walk_reachFrom _ x _ hP y (by simpa using h3)

/-! ## The touch -/

/-- The touch rules in the contract's words give the model's. -/
theorem touch_of (hi : BInv h j) (ti : TopInv h top j) {c : Changes BVal}
    (ht : touchOk (h.tree j) (top j) c.touch = true) : TouchOK h.spec (h.P j) (j + 1) c := by
  obtain ⟨zl, nl, hl, hml, hroot⟩ := ti.last
  obtain ⟨hr0, hrz, hl0, hly⟩ := ti.reach_last hl
  have hsr : superRoot (top j) = some zl := by simp [superRoot, hl]
  simp only [touchOk, hsr, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.some.injEq] at ht
  obtain ⟨h1, h2⟩ := ht
  have kind : ∀ x ∈ c.touch, x = zl ∨
      ∃ n, (h.tree j).obj x = some (.key n) ∧ x ∈ reach (h.tree j) := by
    intro x hx
    rcases h1 x hx with h3 | h3
    · exact Or.inl h3.symm
    · right
      cases ho : (h.tree j).obj x with
      | none => rw [ho] at h3; simp at h3
      | some o =>
        cases o with
        | val v => rw [ho] at h3; simp at h3
        | key n => exact ⟨n, rfl, by rw [ho] at h3; simpa using h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases kind x hx with rfl | ⟨n, hn, _⟩
    · simp [SIS.isIndex, (ti.topNode _ hml).1]
    · have := hi.rep x _ hn
      simp only at this
      simp [SIS.isIndex, this]
  · intro x hx
    simp only [Nat.add_sub_cancel]
    rcases kind x hx with rfl | ⟨n, _, hin⟩
    · exact (SIS.reachable_iff _ _ _ _).mpr hrz
    · exact hi.mem_reach_model hin
  · intro x hx q nq hq hnq hsub
    simp only [Nat.add_sub_cancel] at hq hsub
    rcases h2 with h2 | h2
    · rw [List.isEmpty_iff] at h2
      rw [h2] at hx
      simp at hx
    · obtain ⟨hz, hall⟩ := h2
      rcases ti.reach_cases hi hl ((SIS.reachable_iff _ _ _ _).mp hq) with h3 | h3 | h3
      · exact Or.inr h3
      · left
        rw [h3]
        simpa using hz
      · rcases hall q h3 with h4 | h4
        · left; simpa using h4
        · exfalso
          obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hi.reach_obj h3)
          cases o with
          | val v =>
            have hxq : x = q := by
              rw [SIS.reachFrom_eq] at hsub
              simp only [List.mem_cons, List.mem_flatMap] at hsub
              rcases hsub with h5 | ⟨y', hy', _⟩
              · exact h5
              · exact absurd hy' (hi.val_live ho hnq j y')
            rcases kind x hx with h5 | ⟨n, hn, _⟩
            · rw [← hxq, h5, (ti.topNode _ hml).2.2.2.2.1] at ho; cases ho
            · rw [hxq, ho] at hn; cases hn
          | key n =>
            rw [ho] at h4
            simp only [List.all_eq_true] at h4
            have h5 := h4 x hx
            have hfuel : lvl (.key n) < (h.tree j).fuel q := by simp [Tree.fuel, ho, lvl]
            have h6 := hi.reachFrom_walk (nq.level + 1) _ q _ nq (Nat.lt_succ_self _) ho hfuel hnq
              x hsub
            simp [h6] at h5

/-! ## A-COPY -/

/-- A node reachable before the transaction that it changes, touches or leaves
unreachable is a node of the writer's paths. -/
theorem mem_pathOf_self {sp : Spec BVal Nat} {P : Struct BVal} {c : Changes BVal} {i : Nat}
    {x : NodeId} {N : Node BVal} (hr : SIS.reachable sp P i x = true) (hN : P.get? x = some N)
    (ht : (SIS.changed c x || c.touch.contains x ||
      (SIS.reachable sp P i x && !SIS.reachable sp (P.apply (i + 1) c) (i + 1) x)) = true) :
    x ∈ SIS.pathOf sp P c (i + 1) := by
  unfold SIS.pathOf
  simp only [List.mem_filter, List.mem_eraseDups, Nat.add_sub_cancel]
  refine ⟨by simpa [SIS.reachable] using hr, ?_⟩
  rw [hN]
  exact List.any_eq_true.mpr ⟨x, SIS.self_mem_reachFrom _ _ _ _ _, ht⟩

variable {hj : j < h.txs.length}

/-- A-COPY in the contract's words gives the model's A-COPY. -/
theorem copy_of (hi : BInv h j) (ti : TopInv h top j) (hi' : BInv h (j + 1))
    (ti' : TopInv h top (j + 1)) (tf : TreeFacts p h j hj)
    {nt : Option (NodeId × TopNode × Nat)} (hnt : NonTree h top j hj nt)
    (hc : copyOk (j + 1) (h.tree j) (h.tree (j + 1)) (top j) h.txs[j].c = true) :
    SIS.CopyStep h.spec (h.P j) (j + 1) h.txs[j].c := by
  obtain ⟨zl, nl, hl, hml, hroot⟩ := ti.last
  obtain ⟨hr0, hrz, hl0, hly⟩ := ti.reach_last hl
  have hP' := h.P_succ hj
  unfold copyOk at hc
  simp only [Nat.add_sub_cancel] at hc
  rw [hi.timely.at_eq, hi'.timely.at_eq, List.all_eq_true] at hc
  -- A node of the tree's part of the writer's paths is a node of the model's.
  have inPath : ∀ x, x ∈ (reach (h.tree j)).filter (fun x =>
      h.txs[j].c.adds.any (fun a => a.1 == x) || h.txs[j].c.touch.contains x ||
        !(reach (h.tree (j + 1))).contains x) →
      x ∈ SIS.pathOf h.spec (h.P j) h.txs[j].c (j + 1) ∧ x ≠ SIS.root ∧
      ((h.tree j).obj x).isSome = true := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
    have hr := hi.mem_reach_model hx1
    have hsome := hi.reach_obj hx1
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨N, hN, _⟩ := hi.node_of ho
    have hne : x ≠ SIS.root := by
      rintro rfl
      rw [ti.s0] at ho; cases ho
    refine ⟨mem_pathOf_self hr hN ?_, hne, hsome⟩
    simp only [Bool.or_eq_true] at hx2 ⊢
    rcases hx2 with (h1 | h1) | h1
    · left; left
      unfold SIS.changed
      rw [Bool.or_eq_true]
      exact Or.inr h1
    · left; right; exact h1
    · right
      rw [Bool.and_eq_true]
      refine ⟨hr, ?_⟩
      cases hr' : SIS.reachable h.spec ((h.P j).apply (j + 1) h.txs[j].c) (j + 1) x with
      | false => rfl
      | true =>
        exfalso
        rw [← hP'] at hr'
        obtain ⟨o', ho', _⟩ := tf.contract.2.1 x o ho
        rcases hi'.model_reach_cases hr' with h2 | h2 | h2
        · exact hne h2
        · rw [h2] at ho'; cases ho'
        · simp [h2] at h1
  -- An entry of a node of the tree is a key entry, a delete entry or a value's.
  have treeAdd : ∀ a ∈ h.txs[j].c.adds, ((h.tree (j + 1)).obj a.1).isSome = true →
      (∃ c y, a.2 = .key c y) ∨ (∃ cs, a.2 = .del cs) ∨ ∃ d, a.2 = .data d :=
    fun a ha hs => newVals_kind (tf.add_mem ha hs)
  -- An entry of a node that is no node of the tree: the top node made, or the root.
  have topAdd : ∀ a ∈ h.txs[j].c.adds, (h.tree (j + 1)).obj a.1 = none →
      ∃ z n lv, nt = some (z, n, lv) ∧
        ((a.1 = z ∧ a.2 ∈ topVals n) ∨ (a.1 = SIS.root ∧ a.2 = .top z)) := by
    intro a ha hno
    obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha hno
    have hm := hnt.made z n lv hnt'
    refine ⟨z, n, lv, hnt', ?_⟩
    rcases hcase with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rw [← hm.2.2.2.2.2.1]
      exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using h1⟩, rfl⟩
    · right
      refine ⟨h1, ?_⟩
      have : a.2 ∈ [BVal.top z] := by
        rw [← hm.2.2.2.2.2.2]
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using h1⟩, rfl⟩
      simpa using this
  -- The top node made is made by the change.
  have topNew : ∀ z n lv, nt = some (z, n, lv) → z ∈ h.txs[j].c.new.map (·.id) := by
    intro z n lv hnt'
    have hmem : (⟨z, lv, false⟩ : NewNode) ∈ h.txs[j].c.new.filter
        (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
      rw [hnt.news, hnt']; exact List.mem_singleton_self _
    exact List.mem_map.mpr ⟨_, (List.mem_filter.mp hmem).1, rfl⟩
  -- If a top node is made, the super root before is a node of the writer's paths: it is
  -- no longer reachable.
  have oldTopPath : ∀ z n lv, nt = some (z, n, lv) →
      zl ∈ SIS.pathOf h.spec (h.P j) h.txs[j].c (j + 1) := by
    intro z n lv hnt'
    obtain ⟨hNl, _, _, _, _, _⟩ := ti.topNode _ hml
    have hlast' : (top (j + 1)).getLast? = some (z, n) := by
      rw [hnt.tops, hnt']; simp [ntTops]
    have hzl : zl ≠ z := by
      rintro rfl
      have := (hnt.made _ n lv hnt').2.2.1
      rw [ti.good.lookup hml] at this
      cases this
    have hml' : (zl, nl) ∈ top (j + 1) := by
      rw [hnt.tops]; exact List.mem_append_left _ hml
    have hunreach := ti'.unreach hi' hlast' hml' hzl
    apply mem_pathOf_self ((SIS.reachable_iff _ _ _ _).mpr hrz) hNl
    rw [← hP', hunreach, (SIS.reachable_iff _ _ _ _).mpr hrz]
    simp
  -- A pointer that the clause allows for a key entry or a root pointer.
  have named : ∀ y, y ∉ h.txs[j].c.new.map (·.id) →
      (h.txs[j].c.new.any (fun nn => nn.id == y) ||
        ((reach (h.tree j)).filter (fun x => h.txs[j].c.adds.any (fun a => a.1 == x) ||
          h.txs[j].c.touch.contains x || !(reach (h.tree (j + 1))).contains x)).contains y ||
        ((reach (h.tree j)).filter (fun x => h.txs[j].c.adds.any (fun a => a.1 == x) ||
          h.txs[j].c.touch.contains x || !(reach (h.tree (j + 1))).contains x)).any
            (fun z => namesKey (h.tree j) z y) ||
        (h.txs[j].c.adds.any (fun a => match a.2 with
            | .top _ => true
            | _ => false) &&
          match (top j).getLast? with
          | some (_, nw) => nw.root == y
          | none => false)) = true →
      y ∈ SIS.pathOf h.spec (h.P j) h.txs[j].c (j + 1) ∨
      ∃ z ∈ SIS.pathOf h.spec (h.P j) h.txs[j].c (j + 1), ∃ nz, (h.P j).get? z = some nz ∧
        y ∈ SIS.pointees h.spec nz.hist ∧ (SIS.written h.spec z = true ∨
          y ∈ h.spec.live (nz.hist.upTo (j + 1 - 1))) := by
    intro y hnew hn
    simp only [Bool.or_eq_true] at hn
    rcases hn with ((h1 | h1) | h1) | h1
    rotate_left 3
    · -- the space root before, the root pointer of the super root that is replaced
      right
      rw [Bool.and_eq_true, hl] at h1
      obtain ⟨hmade, hroot'⟩ := h1
      obtain ⟨a, ha, hav⟩ := List.any_eq_true.mp hmade
      have hno : (h.tree (j + 1)).obj a.1 = none := by
        cases ho : (h.tree (j + 1)).obj a.1 with
        | none => rfl
        | some o =>
          exfalso
          rcases treeAdd a ha (by rw [ho]; rfl) with ⟨c', y', hv⟩ | ⟨cs, hv⟩ | ⟨d, hv⟩ <;>
            rw [hv] at hav <;> simp at hav
      obtain ⟨z, n, lv, hnt', _⟩ := topAdd a ha hno
      obtain ⟨hNl, _, _, hnel, _, _⟩ := ti.topNode _ hml
      refine ⟨zl, oldTopPath z n lv hnt', _, hNl, ?_, Or.inl (by simp [SIS.written, hnel])⟩
      simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap]
      refine ⟨⟨nl.time, .rootKey nl.root⟩, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨.rootKey nl.root, List.mem_cons_self, rfl⟩
      · have : nl.root = y := by simpa using hroot'
        rw [← this]
        simp [BHist.spec, bspec, bptrs]
    · exfalso
      obtain ⟨nn, hnn, hid⟩ := List.any_eq_true.mp h1
      exact hnew (List.mem_map.mpr ⟨nn, hnn, by simpa using hid⟩)
    · left
      exact (inPath y (by simpa using h1)).1
    · right
      obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h1
      obtain ⟨hzp, hzne, _⟩ := inPath z hz
      unfold namesKey at hzy
      cases ho : (h.tree j).obj z with
      | none => rw [ho] at hzy; simp at hzy
      | some o =>
        cases o with
        | val v => rw [ho] at hzy; simp at hzy
        | key n =>
          rw [ho] at hzy
          obtain ⟨k, hk, hky⟩ := List.any_eq_true.mp hzy
          cases k with
          | time t => simp at hky
          | del b => simp at hky
          | key c' y' =>
            have hy' : y' = y := by simpa using hky
            subst hy'
            have hN := hi.rep z _ ho
            simp only at hN
            exact ⟨z, hzp, _, hN, (mem_pointees_entries h n.ks y').mpr ⟨c', hk⟩,
              Or.inl (by simp [SIS.written, hzne])⟩
  intro a ha y hy hnew
  have hall := hc a ha
  cases ho' : (h.tree (j + 1)).obj a.1 with
  | some o' =>
    rcases treeAdd a ha (by rw [ho']; rfl) with ⟨c', y', hv⟩ | ⟨cs, hv⟩ | ⟨d, hv⟩
    · rw [hv] at hy hall
      have hyy : y = y' := by simpa [BHist.spec, bspec, bptrs] using hy
      rw [hyy] at hnew ⊢
      exact named y' hnew hall
    · rw [hv] at hy
      simp [BHist.spec, bspec, bptrs] at hy
    · rw [hv] at hy
      simp [BHist.spec, bspec, bptrs] at hy
  | none =>
    obtain ⟨z, n, lv, hnt', hcase⟩ := topAdd a ha ho'
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [topVals, List.mem_cons, List.mem_map] at h2
      rcases h2 with h2 | ⟨q, hq, h2⟩
      · -- the root pointer
        rw [h2] at hy hall
        have hyy : y = n.root := by simpa [BHist.spec, bspec, bptrs] using hy
        rw [hyy] at hnew ⊢
        exact named n.root hnew hall
      · -- a skip pointer
        rw [← h2] at hy hall
        have hyy : y = q.2.1 := by simpa [BHist.spec, bspec, bptrs] using hy
        rw [hl] at hall
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hall
        obtain ⟨hNl, _, _, hnel, _, _⟩ := ti.topNode _ hml
        have hpath := oldTopPath z n lv hnt'
        rcases hall with h3 | ⟨q', hq', h3⟩
        · left
          rw [hyy, h3]
          exact hpath
        · right
          refine ⟨zl, hpath, _, hNl, ?_, Or.inl (by simp [SIS.written, hnel])⟩
          simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap]
          refine ⟨⟨nl.time, .skip q'.1 q'.2.1⟩, ?_, ?_⟩
          · apply List.mem_map.mpr
            exact ⟨.skip q'.1 q'.2.1, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q', hq', rfl⟩), rfl⟩
          · rw [hyy, ← (by simpa using h3 : q'.2.1 = q.2.1)]
            simp [BHist.spec, bspec, bptrs]
    · -- the root's entry names the top node made
      exfalso
      rw [h2] at hy
      have hyy : y = z := by simpa [BHist.spec, bspec, bptrs] using hy
      rw [hyy] at hnew
      exact hnew (topNew z n lv hnt')

end Words

/-! ## A history in the contract's words -/

section Hist

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- A history that meets every clause in the contract's words meets
`MeetsBridgeTop`, with the touch in the model's words; and with it, after
every transaction, the invariants, and A-COPY for the transaction. -/
theorem MeetsFull.inv (hm : MeetsFull p h top) : ∀ j, j ≤ h.txs.length →
    BInv h j ∧ TopInv h top j
  | 0, _ => by
    obtain ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, hnone,
      hroots⟩ := hm.start
    obtain ⟨r', z', lr', lz', l0', f⟩ := hm.start.facts
    have hadds' : h.c0.adds = [(0, .top z'), (z', .rootKey r')] := by
      have hp0 := p0_eq hr hz hzr hnew hadds
      have hp0' := f.p0
      rw [hp0] at hp0'
      simp only [List.cons.injEq, Prod.mk.injEq, Node.mk.injEq, and_true, true_and] at hp0'
      obtain ⟨⟨_, h1⟩, ⟨h2, _⟩, h3, _⟩ := hp0'
      simp only [Entry.mk.injEq, BVal.top.injEq, true_and] at h1
      rw [hadds, h1, h2]
    exact ⟨f.binv, topInv_start f hadds' hm.startTop⟩
  | j + 1, hj => by
    obtain ⟨hi, ti⟩ := hm.inv j (Nat.le_of_succ_le hj)
    obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := hm.step j hj
    obtain ⟨_, ti', hi', _, _⟩ := top_step (hj := hj) hi ti h1 h2 h3 h4 h5 h6
    exact ⟨hi', ti'⟩

/-- A history that meets every clause in the contract's words meets the
contract and the bridge's clauses with the top (`MeetsBridgeTop`). -/
theorem MeetsFull.meetsBridgeTop (hm : MeetsFull p h top) : MeetsBridgeTop p h top where
  start := hm.start
  startTop := hm.startTop
  step := by
    intro j hj
    obtain ⟨hi, ti⟩ := hm.inv j (Nat.le_of_lt hj)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hm.step j hj
    rw [hi.timely.at_eq] at h7
    exact ⟨h1, h2, h3, h4, h5, h6, touch_of hi ti h7⟩

/-- So it meets `MeetsBridge`. -/
theorem MeetsFull.meetsBridge (hm : MeetsFull p h top) : MeetsBridge p h :=
  hm.meetsBridgeTop.meetsBridge

/-- And what eviction needs besides (`MeetsEvict`): the model's A6' and A-COPY
are proved from the clauses in the contract's words. -/
theorem MeetsFull.meetsEvict (hm : MeetsFull p h top) : MeetsEvict h where
  tree := hm.tree
  adopt := by
    intro j hj
    obtain ⟨hi, ti⟩ := hm.inv j hj
    have ha := hm.adopt j hj
    rw [hi.timely.at_eq] at ha
    exact adopt_of hi ti ha
  copy := by
    intro j hj
    obtain ⟨hi, ti⟩ := hm.inv j (Nat.le_of_lt hj)
    obtain ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ := hm.step j hj
    obtain ⟨_, ti', hi', tf, nt, hnt⟩ := top_step (hj := hj) hi ti h1 h2 h3 h4 h5 h6
    exact copy_of hi ti hi' ti' tf hnt h8

end Hist

end Contract
