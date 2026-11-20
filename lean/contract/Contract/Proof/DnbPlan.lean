/-
bergdb 030-29: PE's plan of a transaction of puts against Java's count, node by
node: the induction over plan's fuel (`plan_tree_puts`). For a node x of the
tree before with the operations whose walks pass it, planned into the virtual
node v: the key nodes written below it and v's own (`vcost v`), and for a
tree's root the new roots above it, are at most Java's count of x
(`sbPlan`); PE cuts or replaces x only where Java has x overflow, into at
most Java's parts; v holds at least x's live entries. For a segment's tree:
what it writes is at most Java's count of its root, and its root changes only
where Java gives the leaf above a klong for it.

The tree's fill rules (`Filled`: RootsOK, FillOK) are premises: with them no
child of a transaction of puts is small, so no node is joined.
-/
import Contract.Proof.DnbKids
import Contract.Proof.DnbRoom

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- Java's new roots above a tree's root that overflows. -/
def rootT (b : Nat) (r : SR) (isRoot : Bool) : Nat :=
  if isRoot = true ∧ r.ov ≠ 0 then max r.ov (rootsAbove b r.parts) else 0

/-- Puts of well-formed keys of more than g segments. -/
def PutsAt (g : Nat) (ops : List Op) : Prop :=
  ∀ op ∈ ops, opDel op = false ∧ keyWf op.key = true ∧ g < op.key.length

/-- What the induction says of a node x planned into v, against Java's count r. -/
structure PlanSpec (b : Nat) (s : Tree) (g h : Nat) (x : NodeId) (isRoot : Bool) (v : VN)
    (acc acc' : Acc) (r : SR) : Prop where
  shape : ∃ n es Fl dec, DNB.getKey s x = some n ∧ v = .node (some x) g h false es Fl dec ∧
    (∀ k, dec = .parts k → 0 < r.ov ∧ k ≤ r.parts) ∧ (live n.ks).length ≤ Fl.length ∧ Fl ≠ []
  kw : kw acc' + vcost v + rootT b r isRoot ≤ kw acc + r.cnt
  nd : r.nd = 0
  up : r.up = if r.ov = 0 then 0 else if isRoot = true then r.ov + 1 else r.parts
  parts : r.ov ≠ 0 → r.ov + 1 ≤ r.parts

theorem PlanSpec.child {b g h : Nat} {x : NodeId} {v : VN} {acc acc' : Acc} {r : SR}
    (p : PlanSpec b s g h x false v acc acc' r) : ChildSpec b s g h x v acc acc' r := by
  refine ⟨p.shape, ?_, p.nd, by rw [p.up]; simp, p.parts⟩
  have := p.kw
  simp only [rootT, Bool.false_eq_true, false_and, ↓reduceIte] at this
  omega

/-- The tree's key nodes meet the rules of one node: well-formed klongs, at
most b of them. -/
def KsOk (b : Nat) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → klongsWf n.ks = true ∧ n.ks.length ≤ b

/-- plan at fuel F meets `PlanSpec`. -/
def PlanP (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
    (fs : Nat), Shaped cf s g h x → (∃ lo hi, Good s x lo hi) → Filled cf s isRoot x →
    PutsAt g ops → ops ≠ [] → s.fuel x ≤ fs →
    plan cf i s F x g h ops acc = some (v, acc') →
    PlanSpec b s g h x isRoot v acc acc' (sbPlan b s fs x g ops isRoot)

/-- planTree from a root y at fuel F: its writes against Java's count of y,
and its new root, y itself unless Java gives the leaf above a klong. -/
def TreeP (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (y : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId) (acc' : Acc)
    (fs : Nat), Shaped cf s g (htIn cf s y) y → (∃ lo hi, Good s y lo hi) → Filled cf s true y →
    PutsAt g ops → ops ≠ [] → s.fuel y ≤ fs →
    planTree cf i s F (some y) g ops acc = some (res, acc') →
    kw acc' ≤ kw acc + (sbPlan b s fs y g ops true).cnt ∧ (sbPlan b s fs y g ops true).nd = 0 ∧
      ∃ y', res = some y' ∧ (y' = y ∨ 1 ≤ (sbPlan b s fs y g ops true).up)

theorem renameHead_of_head {α : Type} {c : Nat} {l : List (Nat × α)} (h : l.head?.map (·.1) = some c) :
    renameHead c l = l := by
  cases l with
  | nil => simp at h
  | cons a r => simp at h; simp [renameHead, ← h]

theorem dcost_le {dec : Dec} {r : SR} (h : ∀ k, dec = .parts k → 0 < r.ov ∧ k ≤ r.parts) :
    dcost dec ≤ 1 + r.parts := by
  cases dec with
  | same => simp [dcost]
  | append => simp [dcost]
  | parts k => have := (h k rfl).2; simp [dcost]; omega

theorem filled_key {isRoot : Bool} {x : NodeId} {n : KNode} (hF : Filled cf s isRoot x)
    (hobj : s.obj x = some (.key n)) :
    (n.leaf = false → isRoot = true → 2 ≤ (live n.ks).length) ∧
    (2 ≤ cf.m → isRoot = false → cf.m ≤ (live n.ks).length) ∧
    (∀ c y, (c, y) ∈ live n.ks → n.leaf = true → isLong c = true → Filled cf s true y) ∧
    (∀ c y, (c, y) ∈ live n.ks → n.leaf = false → Filled cf s false y) := by
  cases hF with
  | key hobj' h1 h2 h3 h4 =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h; injection h
    exact ⟨h1, h2, h3, h4⟩
  | other hn => exact absurd hobj (hn n)

theorem good_key {x : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode} (hg : Good s x lo hi)
    (hobj : s.obj x = some (.key n)) :
    klongsWf n.ks = true ∧
    (∀ c y, (c, y) ∈ live n.ks → (n.leaf = true → isLong c = true) →
      ∃ m, s.obj y = some (.key m) ∧ m.level < n.level ∧ live m.ks ≠ []) := by
  cases hg with
  | mk _ _ _ n' hobj' hwf _ _ _ hkey _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h; injection h
    exact ⟨hwf, hkey⟩

theorem lookup_live {n : KNode} {c : Nat} {y : NodeId} (h : (c, y) ∈ live n.ks) :
    (live n.ks).lookup c = some y :=
  lookup_of_mem_sorted (live_sorted n.ks) h

/-- emit of a node kept or appended to gives its base. -/
theorem emit_base {y : NodeId} {g h : Nat} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} (hd : ∀ k, dec ≠ .parts k) {acc acc' : Acc}
    {E : List (Nat × NodeId)} (he : emit cf i s (.node (some y) g h j es F dec) acc = some (E, acc')) :
    E = [(0, y)] := by
  rw [emit.eq_2] at he
  cases hk : emitKids cf i s es acc with
  | none => rw [hk] at he; cases he
  | some q =>
    obtain ⟨F0, acc1⟩ := q
    rw [hk] at he
    cases dec with
    | same =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact he.1.symm
    | append =>
      simp only at he
      cases hg : getKey s y with
      | none => rw [hg] at he; cases he
      | some n =>
        rw [hg] at he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        exact he.1.symm
    | parts k => exact absurd rfl (hd k)

/-- **A segment's tree from its root**, given plan at a lower fuel. -/
theorem dnb_tree_step {b G H F : Nat} (hb : 8 ≤ b) (IH : PlanP b (Cfg.java b G H) i s F) :
    TreeP b (Cfg.java b G H) i s (F + 1) := by
  intro y g ops acc res acc' fs hsh hgood hfill hops hne hfs hpt
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s y = some n := hgk
  rw [planTree.eq_def] at hpt
  simp only at hpt
  rw [hgk] at hpt
  simp only at hpt
  rw [show (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s y by simp [htIn, hobj]] at hpt
  cases hpl : plan (Cfg.java b G H) i s F y g (htIn (Cfg.java b G H) s y) ops acc with
  | none => rw [hpl] at hpt; cases hpt
  | some q =>
    obtain ⟨v, acc1⟩ := q
    rw [hpl] at hpt
    simp only at hpt
    have hp := IH y g _ ops acc v acc1 true fs hsh hgood hfill hops hne hfs hpl
    obtain ⟨n', es, Fl, dec, hgk', rfl, hdec, hlen, hFne⟩ := hp.shape
    rw [hgkD] at hgk'
    obtain rfl : n = n' := by injection hgk'
    have hF1 : htIn (Cfg.java b G H) s y ≠ 0 → Fl.length ≠ 1 := by
      intro h0
      have hl : n.leaf = false := by rw [hleaf]; simpa using h0
      have := (filled_key hfill hobj).1 hl rfl
      omega
    split at hpt
    · cases hpt
    · rename_i hset
      obtain ⟨v', hv, _⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _ hFne hF1 hset
      cases hv
    · rename_i v1 hset
      obtain ⟨v', hv, hv', hsame⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _
        hFne hF1 hset
      cases hv
      split at hpt
      · rename_i c y' acc2 hem
        simp only [Option.some.injEq, Prod.mk.injEq] at hpt
        obtain ⟨rfl, rfl⟩ := hpt
        have hkw := emit_kw v1 acc1 _ acc2 hem
        have hk := hp.kw
        have hra : raOf b dec ≤ rootT b (sbPlan b s fs y g ops true) true := by
          cases dec with
          | parts k =>
            obtain ⟨hov, hkp⟩ := hdec k rfl
            simp only [raOf, rootT, true_and, Nat.pos_iff_ne_zero.mp hov, ne_eq, not_false_eq_true,
              ↓reduceIte]
            split
            · exact le_max_of_le_right (rootsAbove_mono hb hkp)
            · exact Nat.zero_le _
          | same => simp [raOf]
          | append => simp [raOf]
        refine ⟨by omega, hp.nd, y', rfl, ?_⟩
        by_cases hov : (sbPlan b s fs y g ops true).ov = 0
        · left
          have hnp : ∀ k, dec ≠ .parts k := by
            intro k hk'; have := (hdec k hk').1; omega
          rw [hsame (fun k _ => hnp k)] at hem
          have := emit_base hnp hem
          simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
          exact this.2
        · right; rw [hp.up]; simp [hov]
      · cases hpt

theorem len_le_of_lookup {lb es : List (Nat × NodeId)} (hlb : lb.Pairwise CvLtA)
    (h : ∀ q ∈ lb, ∃ y, es.lookup q.1 = some y) : lb.length ≤ es.length := by
  have hnd : (lb.map (·.1)).Nodup := by
    rw [List.Nodup, List.pairwise_map]; exact hlb.imp (fun h => Nat.ne_of_lt h)
  have hsub : lb.map (·.1) ⊆ es.map (·.1) := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    obtain ⟨y, hy⟩ := h q hq
    exact List.mem_map.mpr ⟨(q.1, y), lookup_mem hy, rfl⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

theorem flatMap_ents_old (es : List (Nat × NodeId)) :
    (es.map (fun e => (e.1, VN.old e.2))).flatMap (fun e => ents e.1 e.2) =
      es.map (fun e => (e.1, some e.2)) := by
  induction es with
  | nil => rfl
  | cons e r ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem le_foldl_max_len : ∀ (keys : List Key) (m : Nat) (k : Key), k ∈ keys →
    k.length ≤ keys.foldl (fun m (k : Key) => max m k.length) m
  | [], _, _, h => by simp at h
  | k' :: r, m, k, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have : ∀ (l : List Key) (a : Nat), a ≤ l.foldl (fun m (k : Key) => max m k.length) a := by
        intro l; induction l with
        | nil => intro a; exact le_rfl
        | cons x l ih => intro a; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih _)
      exact le_trans (le_max_right _ _) (this r _)
    · exact le_foldl_max_len r _ k h

/-- A group of puts: Java's klongs, count and deletes of it. -/
theorem sbGroup_puts {b g : Nat} {lv : List (Nat × NodeId)} {ops : List Op} {cv : Nat}
    {child : NodeId → List Op → SR} (hputs : ∀ op ∈ ops, opDel op = false)
    (hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op)) :
    let r := sbGroup b g lv (grpOf g ops cv) child cv
    r.2.2 = (if subsOf g ops cv = [] then 0 else match lv.lookup cv with
      | some y => (child y (subsOf g ops cv)).nd
      | none => 0) ∧
    r.2.1 = (if subsOf g ops cv = [] then 0 else match lv.lookup cv with
      | some y => (child y (subsOf g ops cv)).cnt
      | none => ftbOf b (opKeys (subsOf g ops cv)) (g + 1)) ∧
    (subsOf g ops cv = [] → r.1 = (grpOf g ops cv).length) ∧
    (subsOf g ops cv ≠ [] → r.1 = match lv.lookup cv with
      | some y => (child y (subsOf g ops cv)).up
      | none => 1) := by
  intro r
  have hD : ((grpOf g ops cv).filter (fun op => endsAt g op && opDel op)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro op hop
    have := hputs op (List.mem_of_mem_filter hop)
    simp [this]
  have hsubP : (subsOf g ops cv).filter (fun op => !opDel op) = subsOf g ops cv := by
    rw [List.filter_eq_self]; intro op hop
    have := hputs op (List.mem_of_mem_filter (List.mem_of_mem_filter hop))
    simp [this]
  by_cases hs : subsOf g ops cv = []
  · have hP : ((grpOf g ops cv).filter (fun op => endsAt g op && !opDel op)).length =
        (grpOf g ops cv).length := by
      congr 1
      rw [List.filter_eq_self]
      intro op hop
      have h1 := hputs op (List.mem_of_mem_filter hop)
      have h2 : op ∉ subsOf g ops cv := by rw [hs]; simp
      unfold subsOf at h2
      simp only [List.mem_filter, not_and, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
      have := h2 hop
      simp [h1]; simpa using this
    have hse : ((grpOf g ops cv).filter (fun op => !endsAt g op)).isEmpty = true := by
      show (subsOf g ops cv).isEmpty = true
      rw [hs]; rfl
    simp only [r, sbGroup, hse, ↓reduceIte, hs, hD, hP]
    simp
  · have hL := subs_no_end hend hs
    have hP : ((grpOf g ops cv).filter (fun op => endsAt g op && !opDel op)).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro op hop he
      have : op ∈ (grpOf g ops cv).filter (endsAt g) := by
        rw [List.mem_filter]; simp only [Bool.and_eq_true] at he; exact ⟨hop, he.1⟩
      rw [hL] at this; simp at this
    have hse : ((grpOf g ops cv).filter (fun op => !endsAt g op)).isEmpty = false := by
      show (subsOf g ops cv).isEmpty = false
      cases h : subsOf g ops cv with
      | nil => exact absurd h hs
      | cons _ _ => rfl
    have hsubs : (grpOf g ops cv).filter (fun op => !endsAt g op) = subsOf g ops cv := rfl
    have hspe : ((subsOf g ops cv).filter (fun op => !opDel op)).isEmpty = false := by
      rw [hsubP]
      cases h : subsOf g ops cv with
      | nil => exact absurd h hs
      | cons _ _ => rfl
    simp only [r, sbGroup, ↓reduceIte, hs, hD, hP, hsubs]
    cases hl : lv.lookup cv with
    | some y => simp [hs]
    | none => simp [hs, hsubP]

theorem sbNode_cnt (b : Nat) (n : KNode) (isRoot : Bool) (K nd ci below : Nat) :
    (sbNode b n isRoot K nd ci below).cnt =
      1 + 4 * nd + below + (sbNode b n isRoot K nd ci below).parts +
        rootT b (sbNode b n isRoot K nd ci below) isRoot := rfl

theorem sbNode_facts (b : Nat) (n : KNode) (isRoot : Bool) (K ci below : Nat) :
    let r := sbNode b n isRoot K 0 ci below
    r.nd = 0 ∧ r.up = (if r.ov = 0 then 0 else if isRoot = true then r.ov + 1 else r.parts) ∧
      (r.ov ≠ 0 → r.ov + 1 ≤ r.parts) ∧
      r.ov = overflowsD b K n.ks.length false (some (deadCount n.ks)) ∧
      r.parts = (if r.ov = 0 then 0 else max (r.ov + 1) (cutPartsBound b (n.ks.length + K))) := by
  intro r
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · simp only [r, sbNode]; simp
  · intro h; simp only [r, sbNode] at h ⊢; rw [ite_eq_right h]; exact le_max_left _ _

/-- Java's count of puts has no deletes. -/
theorem sb_nd_puts (b : Nat) (s : Tree) : ∀ (fs : Nat) (x : NodeId) (g : Nat) (ops : List Op) (isRoot : Bool),
    (∀ op ∈ ops, opDel op = false) → (sbPlan b s fs x g ops isRoot).nd = 0
  | 0, _, _, _, _, _ => rfl
  | fs + 1, x, g, ops, isRoot, hputs => by
    rw [sbPlan.eq_def]
    simp only
    split
    · rfl
    · rename_i n _
      split
      · simp only [sbNode]
        rw [List.sum_eq_zero_iff]
        intro t ht
        simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
        obtain ⟨cv, _, rfl⟩ := ht
        unfold sbGroup
        have hD : ((ops.filter (fun op => segAt g op == cv)).filter
            (fun op => endsAt g op && opDel op)).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro op hop
          simp [hputs op (List.mem_of_mem_filter hop)]
        simp only [hD]
        split
        · rfl
        · split
          · rename_i y _
            simp only [zero_add]
            exact sb_nd_puts b s fs y (g + 1) _ true (fun op hop =>
              hputs op (List.mem_of_mem_filter (List.mem_of_mem_filter hop)))
          · split <;> rfl
      · simp only [sbNode]
        rw [List.sum_eq_zero_iff]
        intro t ht
        simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
        obtain ⟨e, he, rfl⟩ := ht
        rw [List.mem_filter] at he
        have hsub : e.2.Sublist ops := by
          have := List.of_mem_zip he.1
          exact route_sub (segAt g) _ ops e.2 this.2
        exact sb_nd_puts b s fs e.1.2 g e.2 false (fun op hop => hputs op (hsub.subset hop))

/-- **A segment leaf**, given the next segments' trees at lower fuels. -/
theorem leaf_step {b G H F : Nat} (hb : 8 ≤ b)
    (IHt : ∀ f < F, TreeP b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g 0 x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → PutsAt g ops → ops ≠ [] → s.fuel x ≤ fs →
      plan (Cfg.java b G H) i s (F + 1) x g 0 ops acc = some (v, acc') →
      PlanSpec b s g 0 x isRoot v acc acc' (sbPlan b s fs x g ops isRoot) := by
  intro x g ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hpl
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s x = some n := hgk
  simp only [beq_self_eq_true] at hleaf
  obtain ⟨lo, hi, hg⟩ := hgood
  obtain ⟨hwf, hkey⟩ := good_key hg hobj
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
  have hend : ∀ op ∈ ops, endsAt g op = !isLong (segAt g op) :=
    fun op hop => endsAt_isLong (hops op hop).2.1 (hops op hop).2.2
  set lv := live n.ks with hlv
  set child : NodeId → List Op → SR := fun y subs => sbPlan b s fs' y (g + 1) subs true
  -- plan's leaf
  rw [plan.eq_def] at hpl
  simp only at hpl
  rw [hgk] at hpl
  simp only [beq_self_eq_true, ↓reduceIte] at hpl
  cases hag : applyGroups (Cfg.java b G H) i s F g lv (List.map (segAt g) ops).eraseDups ops acc with
  | none => rw [hag] at hpl; cases hpl
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hag] at hpl
    simp only at hpl
    unfold mkNode at hpl
    simp only [beq_self_eq_true, ↓reduceIte] at hpl
    rw [hgk] at hpl
    simp only [Option.some.injEq, Prod.mk.injEq] at hpl
    obtain ⟨rfl, rfl⟩ := hpl
    rw [flatMap_ents_old]
    -- the groups
    have hT : ∀ f, f < F → ∀ cv acc0 res acc1', subsOf g ops cv ≠ [] →
        planTree (Cfg.java b G H) i s f (lv.lookup cv) (g + 1) (subsOf g ops cv) acc0 =
          some (res, acc1') →
        kw acc1' ≤ kw acc0 + (sbGroup b g lv (grpOf g ops cv) child cv).2.1 ∧
          ∃ y, res = some y ∧ (lv.lookup cv = some y ∨ 1 ≤ (sbGroup b g lv (grpOf g ops cv) child cv).1) := by
      intro f hf cv acc0 res acc1' hsne hpt
      obtain ⟨_, hB, _, hK⟩ := sbGroup_puts (b := b) (lv := lv) (cv := cv) (child := child)
        (fun op hop => (hops op hop).1) hend
      rw [ite_eq_right hsne] at hB
      have hK' := hK hsne
      obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hsne
      have hop' := hop
      unfold subsOf grpOf at hop'
      simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hop'
      have hlong : isLong cv = true := by
        have := hend op hop'.1.1
        rw [hop'.2, hop'.1.2] at this
        simpa using this.symm
      have hsops : PutsAt (g + 1) (subsOf g ops cv) := by
        intro o ho
        have ho' := ho
        unfold subsOf grpOf at ho'
        simp only [List.mem_filter, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at ho'
        obtain ⟨h1, h2, h3⟩ := hops o ho'.1.1
        refine ⟨h1, h2, ?_⟩
        have := ho'.2; simp only [endsAt, beq_eq_false_iff_ne] at this; omega
      cases hl : lv.lookup cv with
      | some y =>
        rw [hl] at hpt hB hK'
        have hmem : (cv, y) ∈ lv := lookup_mem hl
        obtain ⟨m, hm, hmlev, _⟩ := hkey cv y hmem (fun _ => hlong)
        have hsh' := shaped_kid_leaf hsh hobj (by simpa using hleaf) hmem hlong
        have hgood' : ∃ lo hi, Good s y lo hi := by
          rcases good_kids hg hobj cv y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
          · exact ⟨lo', hi', hg'⟩
          · rw [hm] at hv'; cases hv'
        have hfill' := (filled_key hfill hobj).2.2.1 cv y hmem (by simpa using hleaf) hlong
        have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
        obtain ⟨t1, _, y', hy', hor⟩ := IHt f hf y (g + 1) _ acc0 res acc1' fs' hsh' hgood' hfill'
          hsops hsne hfy hpt
        refine ⟨by rw [hB]; exact t1, y', hy', ?_⟩
        rcases hor with rfl | hor
        · exact Or.inl rfl
        · right; rw [hK']; exact hor
      | none =>
        rw [hl] at hpt hB hK'
        have hfr : FreshOps (g + 1) ((opKeys (subsOf g ops cv)).foldl (fun m (k : Key) => max m k.length) 0 + 1)
            (subsOf g ops cv) := by
          intro o ho
          obtain ⟨h1, h2, h3⟩ := hsops o ho
          refine ⟨h1, h2, h3, ?_⟩
          have := le_foldl_max_len (opKeys (subsOf g ops cv)) 0 o.key (List.mem_map_of_mem ho)
          omega
        obtain ⟨t1, y', hy'⟩ := fresh_le (i := i) (s := s) (G := G) (H := H) hb _ f (g + 1) _ acc0 res acc1'
          hfr hsne hpt
        refine ⟨by rw [hB]; exact t1, y', hy', Or.inr (by rw [hK'])⟩
    obtain ⟨a1, a2, a3, a4⟩ := ag_loop (cf := Cfg.java b G H) (i := i) (s := s) (es0 := lv)
      (fun op hop => (hops op hop).1) hend
      (fun cv => (sbGroup b g lv (grpOf g ops cv) child cv).2.1)
      (fun cv y => lv.lookup cv = some y ∨ 1 ≤ (sbGroup b g lv (grpOf g ops cv) child cv).1) F hT
      (touched g ops) F lv acc es acc1 le_rfl (nodup_touched g ops) (fun _ _ => rfl) (live_sorted n.ks)
      (fun cv hcv => by
        obtain ⟨op, hop, rfl⟩ := mem_touched.mp hcv
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hop, by simp⟩)) hag
    -- the leaf's list
    have hon : ∀ cv ∈ touched g ops, ∃ y, es.lookup cv = some y ∧
        (lv.lookup cv = some y ∨ 1 ≤ (sbGroup b g lv (grpOf g ops cv) child cv).1) := by
      intro cv hcv
      obtain ⟨y, hy, hor⟩ := a4 cv hcv
      refine ⟨y, hy, ?_⟩
      rcases hor with hs | hq
      · right
        obtain ⟨_, _, hK, _⟩ := sbGroup_puts (b := b) (lv := lv) (cv := cv) (child := child)
          (fun op hop => (hops op hop).1) hend
        rw [hK hs]
        obtain ⟨op, hop, rfl⟩ := mem_touched.mp hcv
        exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hop, by simp⟩)
      · exact hq
    obtain ⟨l1, l2, l3, l4⟩ := leaf_counts (fun cv => (sbGroup b g lv (grpOf g ops cv) child cv).1)
      (live_sorted n.ks) a2 (nodup_touched g ops) a3 hon
    -- Java's count of the leaf
    set SG := fun cv => sbGroup b g lv (grpOf g ops cv) child cv with hSG
    have hsb : sbPlan b s (fs' + 1) x g ops isRoot = sbNode b n isRoot
        (4 * ((touched g ops).map (fun cv => (SG cv).2.2)).sum +
          ((touched g ops).map (fun cv => (SG cv).1)).sum)
        ((touched g ops).map (fun cv => (SG cv).2.2)).sum 0
        ((touched g ops).map (fun cv => (SG cv).2.1)).sum := by
      rw [sbPlan.eq_def]
      simp only [hgkD, hleaf, ↓reduceIte, List.map_map]
      rfl
    have hnd0 : ((touched g ops).map (fun cv => (SG cv).2.2)).sum = 0 := by
      have := sb_nd_puts b s (fs' + 1) x g ops isRoot (fun op hop => (hops op hop).1)
      rw [hsb] at this
      exact this
    rw [hsb, hnd0]
    set K := ((touched g ops).map (fun cv => (SG cv).1)).sum with hK
    set below := ((touched g ops).map (fun cv => (SG cv).2.1)).sum with hbelow
    rw [show 4 * 0 + K = K by omega]
    obtain ⟨f1, f2, f3, f4, f5⟩ := sbNode_facts b n isRoot K 0 below
    have hlvl : lv.length ≤ n.ks.length := live_length_le n.ks
    have hlvl' : (live n.ks).length ≤ n.ks.length := live_length_le n.ks
    have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false (es.map (fun e => (e.1, some e.2))) =
        .parts k → 0 < (sbNode b n isRoot K 0 0 below).ov ∧ k ≤ (sbNode b n isRoot K 0 0 below).parts := by
      intro k hk
      obtain ⟨d1, d2⟩ := dec_parts_ov (F := es.map (fun e => (e.1, some e.2))) (K := K)
        (merged := false) hwf (by omega) (fun h0 => l4 (by omega)) (by simp only [List.length_map] at l3 ⊢; omega) hk
      rw [f4]
      refine ⟨d1, ?_⟩
      rw [f5, f4, ite_eq_right (by omega)]
      exact d2
    have hall : ∀ q ∈ lv, ∃ y, es.lookup q.1 = some y := by
      intro q hq
      by_cases hc : q.1 ∈ touched g ops
      · obtain ⟨y, hy, _⟩ := hon q.1 hc; exact ⟨y, hy⟩
      · exact ⟨q.2, by rw [a3 q.1 hc]; exact lookup_live hq⟩
    have hesne : es ≠ [] := by
      obtain ⟨op, hop⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨y, hy, _⟩ := hon (segAt g op) (mem_touched.mpr ⟨op, hop, rfl⟩)
      intro h0; rw [h0] at hy; cases hy
    refine ⟨⟨n, _, _, _, hgkD, rfl, hdec, ?_, ?_⟩, ?_, f1, f2, f3⟩
    · rw [List.length_map]; exact len_le_of_lookup (live_sorted n.ks) hall
    · intro h0; exact hesne (List.map_eq_nil_iff.mp h0)
    · have hc := dcost_le hdec
      have hcnt := sbNode_cnt b n isRoot K 0 0 below
      simp only [vcost, vcostL_old, add_zero]
      have hsum : ((touched g ops).map (fun cv => if subsOf g ops cv = [] then 0 else (SG cv).2.1)).sum
          = below := by
        rw [hbelow]
        congr 1
        apply List.map_congr_left
        intro cv _
        obtain ⟨_, hB, _, _⟩ := sbGroup_puts (b := b) (lv := lv) (cv := cv) (child := child)
          (fun op hop => (hops op hop).1) hend
        split
        · rename_i hs; simp only [SG]; rw [hB, ite_eq_left hs]
        · rfl
      rw [hsum] at a1
      omega

theorem shaped_inner {g h : Nat} {x : NodeId} {n : KNode} (hsh : Shaped cf s g (h + 1) x)
    (hobj : s.obj x = some (.key n)) :
    (live n.ks).head?.map (·.1) = some 0 ∧ ∀ c y, (c, y) ∈ live n.ks → Shaped cf s g h y := by
  cases hsh with
  | inner hobj' _ _ _ _ hhead hkids =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    exact ⟨hhead, hkids⟩

/-- Java's counts of an inner node's children with operations. -/
def kidsRs (b : Nat) (s : Tree) (fs g : Nat) (lv : List (Nat × NodeId)) (ops : List Op) : List SR :=
  ((lv.zip (route (segAt g) lv ops)).filter (fun e => !e.2.isEmpty)).map
    (fun e => sbPlan b s fs e.1.2 g e.2 false)

/-- **An inner node**, given plan at lower fuels. -/
theorem inner_step {b G H F : Nat}
    (IHp : ∀ f < F, PlanP b (Cfg.java b G H) i s f) :
    ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
      (fs : Nat), Shaped (Cfg.java b G H) s g (h + 1) x → (∃ lo hi, Good s x lo hi) →
      Filled (Cfg.java b G H) s isRoot x → PutsAt g ops → ops ≠ [] → s.fuel x ≤ fs →
      plan (Cfg.java b G H) i s (F + 1) x g (h + 1) ops acc = some (v, acc') →
      PlanSpec b s g (h + 1) x isRoot v acc acc' (sbPlan b s fs x g ops isRoot) := by
  intro x g h ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hpl
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s x = some n := hgk
  have hleaf' : n.leaf = false := by simpa using hleaf
  obtain ⟨hhead, hkids⟩ := shaped_inner hsh hobj
  obtain ⟨lo, hi, hg⟩ := hgood
  obtain ⟨hwf, hkey⟩ := good_key hg hobj
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  obtain ⟨fs', rfl⟩ : ∃ fs', fs = fs' + 1 := ⟨fs - 1, by omega⟩
  have hlvne : (live n.ks) ≠ [] := by intro h0; rw [h0] at hhead; simp at hhead
  rw [plan.eq_def] at hpl
  simp only at hpl
  rw [hgk] at hpl
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel] at hpl
  cases hk : planKids (Cfg.java b G H) i s F g (h + 1) (live n.ks) (route (segAt g) (live n.ks) ops) acc with
  | none => rw [hk] at hpl; cases hpl
  | some q =>
    obtain ⟨es, acc1⟩ := q
    rw [hk] at hpl
    simp only at hpl
    have hout := kids_puts (PutsAt g) (F0 := F) (fs := fs') (lvAll := live n.ks)
      (fun f hf c y o acc0 w acc2 hmem hone hP hp => by
        obtain ⟨m, hm, hmlev, _⟩ := hkey c y hmem (by simp [hleaf'])
        have hgood' : ∃ lo hi, Good s y lo hi := by
          rcases good_kids hg hobj c y hmem with ⟨m', hm', _, lo', hi', hg'⟩ | ⟨v', hv'⟩
          · exact ⟨lo', hi', hg'⟩
          · rw [hm] at hv'; cases hv'
        have hfy : s.fuel y ≤ fs' := by simp [Tree.fuel, hm]; omega
        exact (IHp f hf y g h o acc0 w acc2 false fs' (hkids c y hmem) hgood'
          ((filled_key hfill hobj).2.2.2 c y hmem hleaf') hP hone hfy hp).child)
      (fun c y hmem n' hgk' hm2 => by
        have hobj' : s.obj y = some (.key n') := by
          unfold DNB.getKey at hgk'; split at hgk' <;> simp_all
        exact (filled_key ((filled_key hfill hobj).2.2.2 c y hmem hleaf') hobj').2.1 hm2 rfl)
      (fun c y hmem => lookup_live hmem)
      (live n.ks) (route (segAt g) (live n.ks) ops) F acc es acc1 (fun _ h => h)
      (fun o ho op hop => hops op ((route_sub (segAt g) (live n.ks) ops o ho).subset hop)) le_rfl hk
    cases hrb : rebalance (Cfg.java b G H) i s (F + 1) g h es with
    | none => rw [hrb] at hpl; cases hpl
    | some es2 =>
      rw [hrb] at hpl
      simp only at hpl
      have hes2 : es2 = es := rebalance_id hout.small hrb
      subst hes2
      have hesh : es2.head?.map (·.1) = some 0 := by
        rw [← hhead]
        have := congrArg List.head? hout.cvs
        rw [List.head?_map, List.head?_map] at this
        rw [this]
      have hFh : (es2.flatMap (fun e => ents e.1 e.2)).head?.map (·.1) = some 0 := by
        rw [hout.head, hhead]
      unfold mkNode at hpl
      simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, renameHead_of_head hesh] at hpl
      rw [hgk, renameHead_of_head hFh] at hpl
      simp only [Option.some.injEq, Prod.mk.injEq] at hpl
      obtain ⟨rfl, rfl⟩ := hpl
      have hsb : sbPlan b s (fs' + 1) x g ops isRoot = sbNode b n isRoot
          (4 * ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum +
            ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum)
          ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum
          (if ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum = 0 then 0
            else 1 + (((kidsRs b s fs' g (live n.ks) ops).filter (fun r => 0 < r.nd)).map (·.ci)).foldl
              max 0)
          ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum := by
        rw [sbPlan.eq_def]
        simp only [hgkD, hleaf', Bool.false_eq_true, ↓reduceIte]
        rfl
      have hnd : ((kidsRs b s fs' g (live n.ks) ops).map (·.nd)).sum = 0 := hout.nd
      have hA0 : ((es2.flatMap (fun e => ents e.1 e.2)).filter (isAdded (live n.ks))).length ≤
          ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum := hout.added
      have hkw0 : kw acc1 + vcostL es2 ≤ kw acc + ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum :=
        hout.kw
      rw [hsb, hnd]
      simp only [Nat.mul_zero, zero_add, ↓reduceIte]
      generalize ((kidsRs b s fs' g (live n.ks) ops).map (·.up)).sum = K at hA0 ⊢
      generalize ((kidsRs b s fs' g (live n.ks) ops).map (·.cnt)).sum = below at hkw0 ⊢
      obtain ⟨f1, f2, f3, f4, f5⟩ := sbNode_facts b n isRoot K 0 below
      have hlvl : (live n.ks).length ≤ n.ks.length := live_length_le n.ks
      have hR : (removedCvs (live n.ks) (es2.flatMap (fun e => ents e.1 e.2))).length = 0 := by
        unfold removedCvs
        rw [List.length_map, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro q hq
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
        exact hout.keep q hq
      have hA := hA0
      have hL := hout.len
      have hdec : ∀ k, decideNode (Cfg.java b G H) i (some n) false (es2.flatMap (fun e => ents e.1 e.2)) =
          .parts k → 0 < (sbNode b n isRoot K 0 0 below).ov ∧
            k ≤ (sbNode b n isRoot K 0 0 below).parts := by
        intro k hkd
        obtain ⟨d1, d2⟩ := dec_parts_ov (F := es2.flatMap (fun e => ents e.1 e.2)) (K := K)
          (merged := false) hwf (by omega) (fun h0 => (hout.same (by omega)).symm) (by omega) hkd
        rw [f4]
        refine ⟨d1, ?_⟩
        rw [f5, f4, ite_eq_right (by omega)]
        exact d2
      refine ⟨⟨n, _, _, _, hgkD, rfl, hdec, ?_, ?_⟩, ?_, f1, f2, f3⟩
      · have := flatMap_ents_length_ge es2
        have h2 : es2.length = (live n.ks).length := by
          have := congrArg List.length hout.cvs; simpa using this
        omega
      · intro h0
        have := flatMap_ents_nil h0
        subst this
        have := hout.cvs
        simp at this
        exact hlvne this
      · have hc := dcost_le hdec
        have hcnt := sbNode_cnt b n isRoot K 0 0 below
        have hkw := hkw0
        simp only [vcost]
        omega

/-- **PE's plan of puts against Java's count**, at every fuel. -/
theorem plan_tree_puts {b G H : Nat} (hb : 8 ≤ b) :
    ∀ F, PlanP b (Cfg.java b G H) i s F ∧ TreeP b (Cfg.java b G H) i s F := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F IH =>
    cases F with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro x g h ops acc v acc' isRoot fs _ _ _ _ _ _ hp; simp [plan] at hp
      · intro y g ops acc res acc' fs _ _ _ _ _ _ hp; simp [planTree] at hp
    | succ F =>
      refine ⟨?_, dnb_tree_step hb (IH F (by omega)).1⟩
      intro x g h ops acc v acc' isRoot fs hsh hgood hfill hops hne hfs hp
      cases h with
      | zero =>
        exact leaf_step hb (fun f hf => (IH f (by omega)).2) x g ops acc v acc' isRoot fs hsh hgood
          hfill hops hne hfs hp
      | succ h =>
        exact inner_step (fun f hf => (IH f (by omega)).1) x g h ops acc v acc' isRoot fs hsh hgood
          hfill hops hne hfs hp

end Contract.PE
