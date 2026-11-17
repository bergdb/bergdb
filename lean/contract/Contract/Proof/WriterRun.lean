/-
The contract package (bergdb 030-10): from one operation to one transaction.
If every operation of a transaction keeps `Mid` (`OpStep`), the model's
writer meets the writer's contract for the transaction (`WriterMeets`):
`Mid` holds at the start, each accepted operation keeps it, and at the end it
gives the contract, TREE, the top's clauses and what the next transaction
starts from.
-/
import Contract.Proof.WriterWP
import Contract.Proof.Frame

namespace Contract

open SIS (View)
open SIS.Check (BVal)

theorem Ext.refl (i : Time) : ∀ o : Obj, Ext i o o
  | .val _ => rfl
  | .key _ => ⟨rfl, rfl, Or.inl rfl⟩

theorem timesBefore_iff {i : Time} {ks : List Klong} :
    timesBefore i ks = true ↔ ∀ t, Klong.time t ∈ ks → t < i := by
  unfold timesBefore
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    simpa using h _ ht
  · intro h k hk
    cases k with
    | time t => simpa using h t hk
    | key c y => rfl
    | del b => rfl

theorem prefixAt_all {ks : List Klong} {t : Time} (h : ∀ t', Klong.time t' ∈ ks → t' ≤ t) :
    prefixAt ks t = ks := by
  unfold prefixAt
  induction ks with
  | nil => rfl
  | cons k r ih =>
    have ih' := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    cases k with
    | time t' =>
      have := h t' (by simp)
      simp only [List.takeWhile_cons, this, decide_true, ite_true, ih']
    | key c y => simp only [List.takeWhile_cons, ite_true, ih']
    | del b => simp only [List.takeWhile_cons, ite_true, ih']

/-- A tree with no time after t is the tree at t. -/
theorem Tree.at_eq_self {s : Tree} {t : Time}
    (hk : ∀ x n, s.obj x = some (.key n) → ∀ t', Klong.time t' ∈ n.ks → t' ≤ t)
    (hr : ∀ r ∈ s.roots, r.1 ≤ t) : s.at t = s := by
  unfold Tree.at
  have h1 : (fun x => (s.obj x).map (Obj.at t)) = s.obj := by
    funext x
    cases ho : s.obj x with
    | none => rfl
    | some o =>
      cases o with
      | val h => rfl
      | key n => simp [Obj.at, prefixAt_all (hk x n ho)]
  have h2 : s.roots.filter (fun r => decide (r.1 ≤ t)) = s.roots := by
    rw [List.filter_eq_self]
    intro r hr'
    simpa using hr r hr'
  rw [h1, h2]

theorem mem_map_kOf_time {ks : List MKlong} {t : Time} :
    Klong.time t ∈ ks.map kOf ↔ SIS.Tree.Klong.time t ∈ ks := by
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, he⟩
    cases k with
    | time t' => simp only [kOf, Klong.time.injEq] at he; subst he; exact hk
    | key c y => simp [kOf] at he
    | del b => simp [kOf] at he
  · intro h
    exact ⟨_, h, rfl⟩

/-- The tree of the writer's first state is the tree before. -/
theorem treeOf_start (i : Time) (s : Tree) (base : NodeId) (t : SIS.Tree.Top) :
    treeOf i s { next := base, top := t } = s := by
  simp [treeOf]

theorem topOf_start (i : Time) (tp : Top) (base : NodeId) (t : SIS.Tree.Top) :
    topOf i tp { next := base, top := t } = tp := by
  simp [topOf]

/-- J5 gives the top's clauses. -/
theorem WTopInv.step {i : Time} {s : Tree} {tp : Top} {w : MW}
    (h : WTopInv i s tp w.top w.newTop) : TopStep i tp (topOf i tp w) := by
  unfold topOf
  cases hn : w.newTop with
  | false => exact Or.inl rfl
  | true =>
    obtain ⟨h1, h2, h3⟩ := h.2.2 hn
    exact Or.inr ⟨_, _, rfl, h2, rfl, h3⟩

/-- J5 gives that the space roots are the top's. -/
theorem WTopInv.roots {i : Time} {s : Tree} {tp : Top} {w : MW}
    (h : WTopInv i s tp w.top w.newTop) : (treeOf i s w).roots = rootsOf (topOf i tp w) := by
  unfold topOf treeOf
  cases hn : w.newTop with
  | false => simpa using h.1
  | true => simp [rootsOf, h.1]

/-- The skip pointers of the last top node name top nodes and cache their
times, after the transaction too. -/
theorem WTopInv.skips {i : Time} {s : Tree} {tp : Top} {w : MW}
    (h : WTopInv i s tp w.top w.newTop)
    (hb : ∀ z zn, tp.getLast? = some (z, zn) → ∀ q ∈ zn.skips,
      (tp.node q.2.1).map (·.time) = some q.2.2) :
    ∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
      ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2 := by
  unfold topOf
  cases hn : w.newTop with
  | false => simpa using hb
  | true =>
    obtain ⟨_, _, h3⟩ := h.2.2 hn
    intro z zn hl q hq
    simp only [ite_true, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨_, rfl⟩ := hl
    simp only [skipsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h3
    have h4 := h3.1.2 q hq
    simp only [Top.node] at h4 ⊢
    cases hlk : List.lookup q.2.1 tp with
    | none => simp [hlk] at h4
    | some n => simp [List.lookup_append, hlk] at h4 ⊢; exact h4

/-- `Mid` holds at the start of a transaction. -/
theorem mid_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {t : SIS.Tree.Top} (hs : Shows p v z s tp)
    (ht : SIS.Tree.topOf p v z = .ok t) (hb : Before p i base s tp) :
    Mid p i base s tp [] { next := base, top := t } := by
  have h0 := treeOf_start i s base t
  have htop : WTopInv i s tp t false := by
    obtain ⟨t', zn, h1, h2, h3, h4, _, h6, h7⟩ := hs.top
    rw [ht] at h1
    obtain rfl : t = t' := by injection h1
    refine ⟨hb.books.roots, fun _ => ⟨?_, zn, by rw [h3]; exact h2, h6, h7,
      hb.books.skips z zn h2⟩, fun h => by cases h⟩
    rw [h4]
    apply hb.books.rootTimes (zn.time, zn.root)
    rw [hb.books.roots]
    exact List.mem_map.mpr ⟨(z, zn), List.mem_of_getLast? h2, rfl⟩
  refine ⟨by rw [h0]; exact hb.inv, by rw [h0]; rfl, ?_, by rw [h0]; exact hb.tree, htop,
    by rw [h0]; exact hb.balanced, ?_⟩
  · rw [h0]
    refine ⟨fun x o hx => ⟨o, hx, Ext.refl i o, fun _ => rfl⟩, ?_, [], by simp, by simp⟩
    intro x n hx hn
    rw [hn] at hx
    cases hx
  · constructor <;> simp

/-- The times of the map of a state with `Mid` are at most i. -/
theorem Mid.times {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {done : List Op} {w : MW} (hm : Mid p i base s tp done w) (hb : Books i base s tp) :
    ∀ x n, (treeOf i s w).obj x = some (.key n) → ∀ t, Klong.time t ∈ n.ks → t ≤ i := by
  intro x n hx t ht
  simp only [treeOf] at hx
  split at hx
  · cases hx
  · split at hx
    · next m hl =>
      simp only [Option.some.injEq, Obj.key.injEq] at hx
      subst hx
      exact hm.books.times x m hl t (mem_map_kOf_time.mp ht)
    · split at hx
      · cases hx
      · exact Nat.le_of_lt (timesBefore_iff.mp (hb.times x n hx) t ht)

/-- Every key node of the map of a state with `Mid` starts with a time klong. -/
theorem Mid.first {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {done : List Op} {w : MW} (hm : Mid p i base s tp done w) (hb : Books i base s tp) :
    ∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest := by
  intro x n hx
  simp only [treeOf] at hx
  split at hx
  · cases hx
  · next htk =>
    split at hx
    · next m hl =>
      simp only [Option.some.injEq, Obj.key.injEq] at hx
      subst hx
      obtain ⟨t, rest, he⟩ := hm.books.timeFirst x m hl (by simpa using htk)
      exact ⟨t, rest.map kOf, by simp [he, kOf]⟩
    · split at hx
      · cases hx
      · exact hb.first x n hx

theorem Mid.rootTimes {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {done : List Op} {w : MW} (_hm : Mid p i base s tp done w) (hb : Books i base s tp) :
    ∀ r ∈ (treeOf i s w).roots, r.1 ≤ i := by
  intro r hr
  simp only [treeOf] at hr
  split at hr
  · rcases List.mem_append.mp hr with h | h
    · exact Nat.le_of_lt (hb.rootTimes r h)
    · simp only [List.mem_singleton] at h
      subst h
      exact Nat.le_refl _
  · exact Nat.le_of_lt (hb.rootTimes r hr)

/-- The ids at or above the next id are no nodes of the map. -/
theorem Mid.ids {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {done : List Op} {w : MW} (hm : Mid p i base s tp done w) (hb : Books i base s tp) :
    ∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none := by
  intro x hx
  obtain ⟨h1, h2, _, h4, h5⟩ := hm.books.ids
  have hbx : base ≤ x := Nat.le_trans h4 hx
  constructor
  · simp only [treeOf]
    split
    · rfl
    · split
      · next m hl => exact absurd (h1 x m hl) (Nat.not_lt.mpr hx)
      · split
        · next v hl => exact absurd (h2 x v hl) (Nat.not_lt.mpr hx)
        · exact (hb.ids x hbx).1
  · simp only [topOf]
    split
    · next hn =>
      have hne : (x == w.top.id) = false := by
        have := h5 hn
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [Top.node, List.lookup_append, List.lookup_cons, List.lookup_nil, hne]
      have := (hb.ids x hbx).2
      simp only [Top.node] at this
      rw [this]
      rfl
    · exact (hb.ids x hbx).2

/-- The accepted operations keep `Mid`, if each operation does. -/
theorem mid_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (ops : List MOp) (w w' : MW), OpsRun { p := p, i := i, view := v } w ops w' →
      (∀ op ∈ ops, OpStep p op) → ∀ done, Mid p i base s tp done w →
      Mid p i base s tp (done ++ ops.map opOf) w' := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro _ done hm; simpa using hm
  | cons w w1 w' op ops b hk h1 h2 _ ih =>
    intro hop done hm
    have hm1 := hop op (by simp) i base s tp v z done w w1 b hs hb hm hk h1 h2
    have := ih (fun o ho => hop o (by simp [ho])) (done ++ [opOf op]) hm1
    simpa using this

/-- If every operation keeps `Mid`, the model's writer meets the writer's
contract for the transaction. -/
theorem writerMeets_of_opStep (p : MParams) (ops : List MOp) (hop : ∀ op ∈ ops, OpStep p op) :
    WriterMeets p ops := by
  intro i base s tp v z t w hbf hs ht hrun
  have hb := hbf.books
  have hm : Mid p i base s tp (ops.map opOf) w := by
    have := mid_run hs hb ops _ w hrun hop [] (mid_start hs ht hbf)
    simpa using this
  have hat : (treeOf i s w).at i = treeOf i s w :=
    Tree.at_eq_self (hm.times hb) (hm.rootTimes hb)
  have hat0 : s.at (i - 1) = s := by
    apply Tree.at_eq_self
    · intro x n hx t' ht'
      exact Nat.le_sub_one_of_lt (timesBefore_iff.mp (hb.times x n hx) t' ht')
    · intro r hr
      exact Nat.le_sub_one_of_lt (hb.rootTimes r hr)
  refine ⟨⟨?_, hm.frame⟩, by rw [hat]; exact hm.tree, hm.top.step, hm.top.roots, hm.inv, hm.tree,
    hm.balanced, hm.first hb, ?_, ?_, hm.ids hb, hm.top.skips hb.skips⟩
  · simp only [contractOk, hat, hat0, hm.inv, hm.contents, Bool.true_and, beq_self_eq_true]
  · intro x n hx
    rw [timesBefore_iff]
    intro t' ht'
    exact Nat.lt_succ_of_le (hm.times hb x n hx t' ht')
  · intro r hr
    exact Nat.lt_succ_of_le (hm.rootTimes hb r hr)

/-- What a run keeps for the next transaction. -/
structure RunInv (p : MParams) (txs : List (List Op)) (s : Tree) (tp : Top) : Prop where
  inv : invOk (cpOf p) s = true
  tree : TreeOk s
  balanced : Balanced p s
  first : ∀ x n, s.obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest
  times : ∀ x n, s.obj x = some (.key n) → timesBefore (txs.length + 1) n.ks = true
  rootTimes : ∀ r ∈ s.roots, r.1 < txs.length + 1
  roots : s.roots = rootsOf tp
  skips : ∀ z zn, tp.getLast? = some (z, zn) → ∀ q ∈ zn.skips,
    (tp.node q.2.1).map (·.time) = some q.2.2

/-- If the model's writer meets the contract for every transaction, a run of
the writer is a history that meets the writer's contract, TREE and the top's
clauses. -/
theorem runs_meetsTop {p : MParams} (hW : ∀ ops, WriterMeets p ops) :
    ∀ {txs : List (List Op)} {s : Tree} {tp : Top}, Runs p txs s tp →
      MeetsTop (cpOf p) txs s tp ∧ RunInv p txs s tp := by
  intro txs s tp h
  induction h with
  | start s tp base hb hc ht =>
    have hat : s.at 0 = s := by
      apply Tree.at_eq_self
      · intro x n hx t' ht'
        exact Nat.le_of_lt_succ (timesBefore_iff.mp (hb.books.times x n hx) t' ht')
      · intro r hr
        exact Nat.le_of_lt_succ (hb.books.rootTimes r hr)
    refine ⟨MeetsTop.start s tp ⟨by rw [hat]; exact hb.inv, by rw [hat]; exact hc⟩
      (by rw [hat]; exact hb.tree) ht hb.books.roots, ?_⟩
    exact ⟨hb.inv, hb.tree, hb.balanced, hb.books.first, hb.books.times, hb.books.rootTimes,
      hb.books.roots, hb.books.skips⟩
  | step txs s tp ops base v z t w _ hs ht hids hrun ih =>
    obtain ⟨hmeets, hinv⟩ := ih
    have hbf : Before p (txs.length + 1) base s tp :=
      ⟨hinv.inv, hinv.tree, hinv.balanced,
        ⟨hinv.first, hinv.times, hinv.rootTimes, hids, hinv.roots, hinv.skips⟩⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, hf, h8, h9, _, h11⟩ :=
      hW ops (txs.length + 1) base s tp v z t w hbf hs ht hrun
    refine ⟨MeetsTop.step txs s tp (ops.map opOf) (dirtyOf w) _ _ hmeets h1 h2 h3 h4, ?_⟩
    refine ⟨h5, h6, h7, hf, ?_, ?_, h4, h11⟩
    · simpa using h8
    · simpa using h9

/-- If every operation keeps `Mid`, a run of the model's writer is a history
that meets the writer's contract, TREE and the top's clauses: the premise of
the theorems on reads (`top_right`, `jget_right`, `jscan_right`). -/
theorem runs_meetsTop_of_opStep {p : MParams} (hop : ∀ op, OpStep p op)
    {txs : List (List Op)} {s : Tree} {tp : Top} (h : Runs p txs s tp) :
    MeetsTop (cpOf p) txs s tp :=
  (runs_meetsTop (fun ops => writerMeets_of_opStep p ops (fun op _ => hop op)) h).1

end Contract
