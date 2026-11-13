import SIS.Tree.GetWriter
import SIS.Tree.DataEntries

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `CommitGetOK` (bergdb 024-12, TP10) from the lift of the writer's key
nodes alone (`CommitLiftOK`): the structure after the transaction has, as its
key nodes, those the writer's last state reads, and the nodes the transaction
took back are its own. The super root and the values are proved here. -/

/-! ## What the writer keeps of its super root and values -/

/-- The writer's super root and values, against its first super root top0:
top0 is not of the transaction's time; without a new super root the writer's
is top0; a new one is an allocation above the key levels; every value made is
an allocation of a data node. -/
def CommitInv (top0 : Top) (c : Ctx) (w : W) : Prop :=
  top0.time ≠ c.i ∧ (w.newTop = false → w.top = top0) ∧
  (w.newTop = true → ∃ m ∈ w.made, m.id = w.top.id ∧ m.isData = false ∧ c.p.keyMax < m.level) ∧
  (∀ q ∈ w.vals, (⟨q.1, 0, true⟩ : NewNode) ∈ w.made) ∧
  (w.vals.map (·.1)).Nodup ∧ ∀ q ∈ w.vals, q.1 < w.next

theorem commitInv_grow (top0 : Top) (c : Ctx) (w w' : W)
    (hw : CommitInv top0 c w) (hnew : w'.newTop = w.newTop) (htop : w'.top = w.top)
    (hmade : ∀ m ∈ w.made, m ∈ w'.made) (hvals : w'.vals = w.vals) (hnext : w.next ≤ w'.next) :
    CommitInv top0 c w' := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hw
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    rw [hnew] at hn
    rw [htop]
    exact h1 hn
  · intro ht
    rw [hnew] at ht
    obtain ⟨m, hm, he⟩ := h2 ht
    rw [htop]
    exact ⟨m, hmade m hm, he⟩
  · intro q hq
    rw [hvals] at hq
    exact hmade _ (h3 q hq)
  · rw [hvals]; exact h4
  · intro q hq
    rw [hvals] at hq
    exact Nat.lt_of_lt_of_le (h5 q hq) hnext

@[instance_reducible]
def commitInvariant (top0 : Top) : WriterStateInvariant where
  pred := CommitInv top0
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact hw
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode, writerWP_modify]
    exact hw
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    · exact commitInv_grow top0 c w _ hw rfl rfl (fun m hm => List.mem_append_left _ hm) rfl
        (Nat.le_add_right _ _)
    · exact commitInv_grow top0 c w _ hw rfl rfl (fun m hm => List.mem_append_left _ hm) rfl
        (Nat.le_add_right _ _)
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hw
    unfold CommitInv
    refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
    · intro ht
      obtain ⟨m, hm, he⟩ := h2 ht
      exact ⟨m, List.mem_append_left _ hm, he⟩
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact List.mem_append_left _ (h3 q hq)
      · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · simp only [List.map_append, List.map_cons, List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨h4, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      have := h5 q hq
      omega
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · have := h5 q hq; dsimp only; omega
      · dsimp only; omega
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    exact commitInv_grow top0 c w _ hw rfl rfl (fun m hm => hm) rfl (Nat.le_add_right _ _)
  trace := by
    intro s c w hw
    simp only [note, writerWP_modify]
    exact hw
  provenance := by
    intro x old c w hw
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact hw
    · simpa only [writerWP_pure] using hw
  take := by
    intro x c w hw
    simp only [takenBack, writerWP_modify]
    exact hw
  clear := by
    intro c w hw
    simp only [pathClear, writerWP_modify]
    exact hw
  path := by
    intro cv x c w hw
    simp only [pathAdd, writerWP_modify]
    exact hw
  top := by
    intro x c w hw
    have hw' := hw
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hw
    unfold newSuperRoot note fresh
    wpSimplify
    split
    · rename_i htime
      wpSimplify
      have hnt : w.newTop = true := by
        cases hn : w.newTop with
        | true => rfl
        | false =>
          have := h1 hn
          rw [this] at htime
          exact absurd (by simpa using htime : c.i = top0.time).symm h0
      unfold CommitInv
      refine ⟨h0, fun h => by simp_all, fun _ => h2 hnt, h3, h4, h5⟩
    · wpSimplify
      unfold CommitInv
      refine ⟨h0, ?_, ?_, ?_, h4, ?_⟩
      · intro h
        simp at h
      · intro _
        refine ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl, rfl, ?_⟩
        simp only [Params.topLevel]
        omega
      · intro q hq
        exact List.mem_append_left _ (h3 q hq)
      · intro q hq
        have := h5 q hq
        dsimp only
        omega
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-! ## The writer's last state -/

theorem topOf_time (p : Params) (v : View BVal) (z : NodeId) (top : Top)
    (h : topOf p v z = .ok top) : ∃ nd, v z = some nd ∧ ∃ e ∈ nd.hist, e.time = top.time := by
  unfold topOf at h
  cases hz : v z with
  | none => rw [hz] at h; cases h
  | some nd =>
    rw [hz] at h
    simp only at h
    refine ⟨nd, rfl, ?_⟩
    split at h
    · rename_i t y hf
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some hf
      refine ⟨e, he, ?_⟩
      cases hv : e.val <;> simp [hv] at hfe
      exact hfe.1
    · cases h

/-- The writer's last state keeps its super root and values (`CommitInv`). -/
theorem commitInv_of_runOps (p : Params) (ts : List Tx) (tx : Tx) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w)) :
    ∃ z top0, lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z ∧
      topOf p (ctxOf p ts).view z = .ok top0 ∧ CommitInv top0 (ctxOf p ts) w := by
  obtain ⟨z, top0, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  refine ⟨z, top0, hz, htop, ?_⟩
  have ht : top0.time ≠ ts.length + 1 := by
    obtain ⟨nd, hv, e, he, het⟩ := topOf_time p _ z top0 htop
    simp only [rootless] at hv
    split at hv
    · cases hv
    · obtain ⟨nd0, _, hnd⟩ := view_some p _ _ _ _ hv
      subst hnd
      have := (List.mem_filter.mp he).2
      simp only [decide_eq_true_eq] at this
      omega
  letI := commitInvariant top0
  exact state_ops tx.ops (ctxOf p ts) (wInit tx top0) (by
    change CommitInv top0 (ctxOf p ts) (wInit tx top0)
    refine ⟨ht, fun _ => rfl, fun h => by simp [wInit] at h, by simp [wInit], by simp [wInit],
      by simp [wInit]⟩) noops w hops

theorem treeRun_root (p : Params) (ts : List Tx) :
    ∃ nd, (treeRun p ts).get? root = some nd ∧ nd.level = p.rootLevel ∧ nd.isData = false := by
  have hf : ∀ (qs : List (Tx × Nat)) (P : Struct BVal),
      (∃ nd, P.get? root = some nd ∧ nd.level = p.rootLevel ∧ nd.isData = false) →
      ∃ nd, (qs.foldl (fun P (q : Tx × Nat) =>
          P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) P).get? root = some nd ∧
        nd.level = p.rootLevel ∧ nd.isData = false := by
    intro qs
    induction qs with
    | nil => intro P h; exact h
    | cons q qs ih =>
      intro P ⟨nd, hnd, hl, hd⟩
      apply ih
      exact ⟨_, get?_apply_of_get? hnd, hl, hd⟩
  exact hf _ _ ⟨_, rfl, rfl, rfl⟩

theorem nodup_map_inj {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup)
    (a b : α) (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (he ▸ List.mem_map_of_mem hb') h.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (he.symm ▸ List.mem_map_of_mem ha') h.1
      · exact ih h.2 ha' hb'

theorem findSome_of_all {α β : Type} (f : α → Option β) (l : List α) (b : β)
    (hex : ∃ a ∈ l, f a = some b) (hall : ∀ a ∈ l, f a = none ∨ f a = some b) :
    l.findSome? f = some b := by
  induction l with
  | nil => obtain ⟨a, ha, _⟩ := hex; cases ha
  | cons x l ih =>
    rw [List.findSome?_cons]
    rcases hall x List.mem_cons_self with hx | hx
    · rw [hx]
      simp only
      apply ih
      · obtain ⟨a, ha, hfa⟩ := hex
        rcases List.mem_cons.mp ha with rfl | ha'
        · rw [hx] at hfa; cases hfa
        · exact ⟨a, ha', hfa⟩
      · exact fun a ha => hall a (List.mem_cons_of_mem x ha)
    · rw [hx]

theorem getLast_append_const {α : Type} (l A : List α) (E : α) (hne : A ≠ [])
    (hall : ∀ a ∈ A, a = E) : (l ++ A).getLast? = some E := by
  rw [List.getLast?_append]
  cases hA : A.getLast? with
  | none => simp [List.getLast?_eq_none_iff] at hA; exact absurd hA hne
  | some a =>
    simp only [Option.some_or]
    rw [hall a (List.mem_of_getLast? hA)]

/-! ## The changes of the writer's last state -/

theorem mem_changesOf_adds (i : Time) (w : W) (x : NodeId) (val : BVal)
    (h : (x, val) ∈ (changesOf i w).adds) :
    (∃ q ∈ w.nodes, w.taken.contains q.1 = false ∧ q.1 = x) ∨
      (∃ h, (x, h) ∈ w.vals ∧ val = .data h) ∨
      (w.newTop = true ∧ ((x = root ∧ val = .top w.top.id) ∨
        (x = w.top.id ∧ (val = .rootKey w.top.rootKey ∨ ∃ j z, val = .skip j z)))) := by
  unfold changesOf at h
  simp only at h
  have h' := (List.mergeSort_perm _ _).mem_iff.mp h
  rcases List.mem_append.mp h' with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · left
      obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp h2
      obtain ⟨e, _, he⟩ := List.mem_map.mp hm
      obtain ⟨hqn, hqt⟩ := List.mem_filter.mp hq
      refine ⟨q, hqn, by simpa using hqt, ?_⟩
      exact (Prod.mk.inj he).1
    · right; left
      obtain ⟨q, hq, he⟩ := List.mem_map.mp h2
      obtain ⟨hx1, hx2⟩ := Prod.mk.inj he
      subst hx1
      exact ⟨q.2, hq, hx2.symm⟩
  · right; right
    split at h1
    · rename_i hnt
      refine ⟨hnt, ?_⟩
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_map] at h1
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨q, _, h3⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h3.1.symm, Or.inr ⟨q.1, q.2, h3.2.symm⟩⟩
    · cases h1

theorem val_mem_changesOf_adds (i : Time) (w : W) (y h : Nat) (hy : (y, h) ∈ w.vals) :
    (y, BVal.data h) ∈ (changesOf i w).adds := by
  unfold changesOf
  apply (List.mergeSort_perm _ _).mem_iff.mpr
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨(y, h), hy, rfl⟩

theorem top_mem_changesOf_adds (i : Time) (w : W) (hnt : w.newTop = true) :
    (root, BVal.top w.top.id) ∈ (changesOf i w).adds ∧
      (w.top.id, BVal.rootKey w.top.rootKey) ∈ (changesOf i w).adds := by
  unfold changesOf
  simp only [hnt, ↓reduceIte]
  constructor <;> apply (List.mergeSort_perm _ _).mem_iff.mpr <;> apply List.mem_append_right <;> simp

theorem newNodeOf_changesOf_some (i : Time) (w : W) (x : NodeId) (nd : Node BVal)
    (h : newNodeOf (changesOf i w) x = some nd) :
    ∃ m ∈ w.made, m.id = x ∧ w.taken.contains x = false ∧
      nd = { level := m.level, isData := m.isData, hist := [] } := by
  have hm := mem_of_get? h
  obtain ⟨m, hm, he⟩ := List.mem_map.mp hm
  have hm' : m ∈ w.made.filter (fun n => !w.taken.contains n.id) :=
    (List.mergeSort_perm _ _).mem_iff.mp hm
  obtain ⟨hmade, ht⟩ := List.mem_filter.mp hm'
  obtain ⟨h1, h2⟩ := Prod.mk.inj he
  subst h1
  exact ⟨m, hmade, rfl, by simpa using ht, h2.symm⟩

theorem newNodeOf_changesOf_none (i : Time) (w : W) (x : NodeId)
    (h : ∀ m ∈ w.made, m.id = x → w.taken.contains x = true) :
    newNodeOf (changesOf i w) x = none := by
  cases hn : newNodeOf (changesOf i w) x with
  | none => rfl
  | some nd =>
    obtain ⟨m, hm, hid, ht, _⟩ := newNodeOf_changesOf_some i w x nd hn
    rw [h m hm hid] at ht
    cases ht

theorem newNodeOf_changesOf_made (base : NodeId) (i : Time) (w : W) (hw : AllocatedIds base w)
    (m : NewNode) (hm : m ∈ w.made) (ht : w.taken.contains m.id = false) :
    newNodeOf (changesOf i w) m.id = some { level := m.level, isData := m.isData, hist := [] } := by
  cases hn : newNodeOf (changesOf i w) m.id with
  | none =>
    unfold newNodeOf Struct.get? at hn
    have hall := List.lookup_eq_none_iff.mp hn
    have hmem : (m.id, ({ level := m.level, isData := m.isData, hist := [] } : Node BVal)) ∈
        (changesOf i w).new.map (fun n => (n.id, ({ level := n.level, isData := n.isData, hist := [] } : Node BVal))) := by
      apply List.mem_map.mpr
      refine ⟨m, ?_, rfl⟩
      apply (List.mergeSort_perm _ _).mem_iff.mpr
      exact List.mem_filter.mpr ⟨hm, by simpa using ht⟩
    have := hall _ hmem
    simp at this
  | some nd =>
    obtain ⟨m', hm', hid, _, hnd⟩ := newNodeOf_changesOf_some i w m.id nd hn
    have heq := nodup_map_inj (·.id) w.made hw.2.1 m' m hm' hm hid
    subst heq
    rw [hnd]

/-! ## The lift -/

/-- The lift of the writer's key nodes, for TP7 and TP10 alike: after a
transaction within reach, the structure's key nodes are those that the
writer's last state reads (its own copies, P's for the others, none for a
node it took back); the transaction took back only nodes of its own ids; and
not the super root it made. Not proved. -/
def CommitLiftOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x, knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = wNode p (viewOf (treeRun p ts)) w x) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

theorem treeRun_snoc_changes (p : Params) (ts : List Tx) (tx : Tx) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w)) :
    treeRun p (ts ++ [tx]) = (treeRun p ts).apply (ts.length + 1) (changesOf (ts.length + 1) w) := by
  rw [treeRun_snoc]
  unfold exec exec?
  rw [hrun]
  rfl

theorem get?_none_of_ge (P : Struct BVal) (base x : NodeId) (hbase : ∀ q ∈ P, q.1 < base)
    (hx : base ≤ x) : P.get? x = none := by
  cases h : P.get? x with
  | none => rfl
  | some nd =>
    have := hbase _ (get?_mem P x nd h)
    simp only at this
    omega

theorem rootLevel_gt (p : Params) : p.keyMax < p.rootLevel := by
  unfold Params.rootLevel
  omega

/-- `CommitGetOK` from the lift of the writer's key nodes: the super root and
the values of the structure after the transaction are the writer's. -/
theorem commitGetOK_of_lift (p : Params) (hl : CommitLiftOK p) : CommitGetOK p := by
  intro ts tx hw noops w hrun key _
  obtain ⟨hK, htaken, htopt⟩ := hl ts tx hw noops w hrun
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  have hdata : MadeData w := execW_madeData p tx _ _ noops w hrun
  obtain ⟨z, top0, hz, htop, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, hnf, hnt, hvm, hvn, _⟩ := hinv
  have hroot0 := rootAt_of_writerTop p ts z top0 hz htop
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hK ⊢
  generalize hP : treeRun p ts = P at hK hbase hroot0 ⊢
  generalize hi : ts.length + 1 = i at hK ⊢
  have hroot := treeRun_root p ts
  rw [hP] at hroot
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have hbase0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
  -- Key adds only for the writer's own nodes, which the lift reads.
  have noKey : ∀ x, knodeOf p (viewOf (P.apply i (changesOf i w))) x = none →
      w.taken.contains x = false → ∀ q ∈ w.nodes, q.1 ≠ x := by
    intro x hx ht q hq hqx
    rw [hK x] at hx
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte] at hx
    cases hl : w.nodes.lookup x with
    | none =>
      have := List.lookup_eq_none_iff.mp hl q hq
      simp [hqx] at this
    | some n => rw [hl] at hx; cases hx
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  -- The values.
  have hV : valueOf (viewOf (P.apply i (changesOf i w))) = wValue (viewOf P) w := by
    funext y
    by_cases hty : w.taken.contains y = true
    · have hPy := get?_none_of_ge P tx.base y hbase (htaken y (by simpa using hty))
      have hNy := newNodeOf_changesOf_none i w y (fun m _ hid => by rw [← hid] at hty ⊢; exact hty)
      have hty2 : y ∈ w.taken := by simpa using hty
      simp [valueOf, viewOf, get?_apply, hPy, hNy, wValue, hty2]
    · have hty' : w.taken.contains y = false := by simpa using hty
      cases hv : w.vals.lookup y with
      | some h =>
        obtain ⟨l1, l2, hvl, _⟩ := List.lookup_eq_some_iff.mp hv
        have hmem : (y, h) ∈ w.vals := by rw [hvl]; simp
        have hmade := hvm (y, h) hmem
        have hge : tx.base ≤ y := madeGe _ hmade
        have hPy := get?_none_of_ge P tx.base y hbase hge
        have hNy := newNodeOf_changesOf_made tx.base i w halloc _ hmade hty'
        have hk : knodeOf p (viewOf (P.apply i (changesOf i w))) y = none := by
          simp [knodeOf, viewOf, get?_apply, hPy, hNy]
        have hadds : ∀ e ∈ addsFor (changesOf i w) i y, e.val = .data h := by
          intro e he
          obtain ⟨_, hm⟩ := mem_addsFor.mp he
          rcases mem_changesOf_adds i w y e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', hv'⟩ |
              ⟨hnt', hr⟩
          · exact absurd hqy (noKey y hk hty' q hq)
          · have := nodup_map_inj (·.1) w.vals hvn _ _ hh' hmem rfl
            cases this
            exact hv'
          · rcases hr with ⟨hyr, _⟩ | ⟨hyt, _⟩
            · rw [hyr] at hge; simp only [root] at hge; omega
            · obtain ⟨m, hm, hmid, hmd, _⟩ := hnt hnt'
              have := nodup_map_inj (·.id) w.made halloc.2.1 m _ hm hmade (by simp [hmid, hyt])
              rw [this] at hmd
              cases hmd
        have hex : (⟨i, .data h⟩ : Entry BVal) ∈ addsFor (changesOf i w) i y :=
          mem_addsFor.mpr ⟨rfl, val_mem_changesOf_adds i w y h hmem⟩
        simp only [valueOf, viewOf, get?_apply, hPy, hNy, Option.none_or, Option.map_some,
          ↓reduceIte, List.nil_append, wValue, hty', hv, Bool.false_eq_true]
        apply findSome_of_all
        · exact ⟨_, hex, rfl⟩
        · intro e he
          right
          rw [hadds e he]
      | none =>
        cases hPy : P.get? y with
        | some nd =>
          simp only [valueOf, viewOf, get?_apply_of_get? hPy, wValue, hty', hv, hPy,
            Bool.false_eq_true, ↓reduceIte]
          cases hd : nd.isData with
          | false => rfl
          | true =>
            obtain ⟨e, he, h0, hed⟩ := treeRun_dataEntriesOK p ts y nd (by rw [hP]; exact hPy) hd
            simp only [↓reduceIte, List.findSome?_append]
            have hs : (nd.hist.findSome? (fun e => match e.val with
                | .data h => some h
                | _ => none)).isSome = true := by
              apply List.findSome?_isSome_iff.mpr
              exact ⟨e, he, by simp [hed]⟩
            cases hf : nd.hist.findSome? (fun e => match e.val with
                | .data h => some h
                | _ => none) with
            | none => rw [hf] at hs; cases hs
            | some h1 => rfl
        | none =>
          cases hNy : newNodeOf (changesOf i w) y with
          | none => simp [valueOf, viewOf, get?_apply, hPy, hNy, wValue, hty', hv]
          | some nd =>
            obtain ⟨m, hm, hid, _, hnd⟩ := newNodeOf_changesOf_some i w y nd hNy
            cases hmd : m.isData with
            | false =>
              simp [valueOf, viewOf, get?_apply, hPy, hNy, hnd, hmd, wValue, hty', hv]
            | true =>
              obtain ⟨h, hh⟩ := hdata m hm hmd
              rw [hid] at hh
              have := List.lookup_eq_none_iff.mp hv _ hh
              simp at this
  -- The super root.
  have hR : rootAt (viewOf (P.apply i (changesOf i w))) i = some w.top.rootKey := by
    have hrt : w.taken.contains root = false := by
      cases h : w.taken.contains root with
      | false => rfl
      | true =>
        have := htaken root (by simpa using h)
        simp only [root] at this
        omega
    have hkr : knodeOf p (viewOf (P.apply i (changesOf i w))) root = none := by
      have := rootLevel_gt p
      simp [knodeOf, viewOf, get?_apply_of_get? hndr, hlr, hdr, this]
    have noKeyRoot := noKey root hkr hrt
    have hradds : ∀ e ∈ addsFor (changesOf i w) i root,
        w.newTop = true ∧ e = ⟨i, .top w.top.id⟩ := by
      intro e he
      obtain ⟨het, hm⟩ := mem_addsFor.mp he
      rcases mem_changesOf_adds i w root e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
          ⟨hnt', hr⟩
      · exact absurd hqy (noKeyRoot q hq)
      · have := madeGe _ (hvm _ hh')
        simp only [root] at this
        omega
      · rcases hr with ⟨_, hval⟩ | ⟨hyt, _⟩
        · refine ⟨hnt', ?_⟩
          cases e
          simp only at het hval
          rw [het, hval]
        · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
          have := madeGe m hm
          rw [hmid, ← hyt] at this
          simp only [root] at this
          omega
    cases hnew : w.newTop with
    | true =>
      obtain ⟨m, hm, hmid, hmd, hml⟩ := hnt hnew
      have htt := htopt hnew
      have hge : tx.base ≤ w.top.id := hmid ▸ madeGe m hm
      have hPt := get?_none_of_ge P tx.base _ hbase hge
      have hNt := newNodeOf_changesOf_made tx.base i w halloc m hm (by rw [hmid]; exact htt)
      rw [hmid] at hNt
      have hkt : knodeOf p (viewOf (P.apply i (changesOf i w))) w.top.id = none := by
        have hml' : p.keyMax < m.level := hml
        simp [knodeOf, viewOf, get?_apply, hPt, hNt, hml']
      have noKeyTop := noKey _ hkt htt
      have hmems := top_mem_changesOf_adds i w hnew
      unfold rootAt topAt rootKeyOf viewOf
      rw [get?_apply_of_get? hndr]
      simp only
      rw [upTo_append]
      have hA : (addsFor (changesOf i w) i root).upTo i = addsFor (changesOf i w) i root :=
        List.filter_eq_self.mpr (fun e he => by
          rw [(mem_addsFor.mp he).1]; simp)
      rw [hA, getLast_append_const (ndr.hist.upTo i) (addsFor (changesOf i w) i root)
        ⟨i, .top w.top.id⟩
        (List.ne_nil_of_mem (a := (⟨i, .top w.top.id⟩ : Entry BVal)) (mem_addsFor.mpr ⟨rfl, hmems.1⟩))
        (fun e he => (hradds e he).2)]
      simp only [Option.bind_some]
      rw [get?_apply, hPt, hNt]
      simp only [Option.none_or, Option.map_some, Option.bind_some, List.nil_append]
      apply findSome_of_all
      · exact ⟨⟨i, .rootKey w.top.rootKey⟩, mem_addsFor.mpr ⟨rfl, hmems.2⟩, rfl⟩
      · intro e he
        obtain ⟨_, hm'⟩ := mem_addsFor.mp he
        rcases mem_changesOf_adds i w w.top.id e.val hm' with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
            ⟨_, hr⟩
        · exact absurd hqy (noKeyTop q hq)
        · have := nodup_map_inj (·.id) w.made halloc.2.1 m _ hm (hvm _ hh') (by simp [hmid])
          rw [this] at hmd
          cases hmd
        · rcases hr with ⟨hyr, _⟩ | ⟨_, hv | ⟨j, z', hv⟩⟩
          · simp only [root] at hyr; omega
          · right; rw [hv]
          · left; rw [hv]
    | false =>
      have htw := hnf hnew
      have hA : addsFor (changesOf i w) i root = [] :=
        List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
          have := (hradds e he).1
          rw [hnew] at this
          cases this)
      have hshift := topAt_succ_of_timesLE P ts.length (by rw [← hP]; exact treeRun_timesLE p ts)
      rw [htw]
      unfold rootAt at hroot0 ⊢
      have htopEq : topAt (viewOf (P.apply i (changesOf i w))) i = topAt (viewOf P) ts.length := by
        rw [← hshift, hi]
        unfold topAt viewOf
        rw [get?_apply_of_get? hndr, hA, List.append_nil, hndr]
      rw [htopEq]
      cases hzt : topAt (viewOf P) ts.length with
      | none => rw [hzt] at hroot0; cases hroot0
      | some z' =>
        rw [hzt] at hroot0
        simp only [Option.bind_some] at hroot0 ⊢
        exact rootKeyOf_apply_some P i (changesOf i w) z' _ hroot0
  -- The get.
  unfold get runGet wGet
  rw [hR, hP]
  simp only [Option.bind_some]
  rw [getFrom_eq_getFromR, hV, show knodeOf p (viewOf (P.apply i (changesOf i w))) =
    wNode p (viewOf P) w from funext hK, hi]

/-- TP10's step for one transaction from the writer's refinement of the map
and the lift of its key nodes. -/
theorem txGetOK_of_op_lift (p : Params) (ho : OpGetOK p) (hl : CommitLiftOK p) : TxGetOK p :=
  txGetOK_of_op_commit p ho (commitGetOK_of_lift p hl)

/-- TP10 from TP7, the writer's refinement of the map and the lift of its key
nodes. -/
theorem getOK_of_op_lift (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : CommitLiftOK p) : GetOK p :=
  getOK_of_op_commit p hinv ho (commitGetOK_of_lift p hl)

/-- TP11 from TP7, the writer's refinement of the map and the lift of its key
nodes. -/
theorem scanOK_of_op_lift (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : CommitLiftOK p) : ScanOK p :=
  scanOK_of_op_commit p hinv ho (commitGetOK_of_lift p hl)

end SIS.Tree
