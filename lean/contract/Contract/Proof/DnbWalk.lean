/-
bergdb 030-29: Java's count is the structural count. `DNB.dirtyNodeBound`
(Contract/DirtyBound.lean, Java's `Dag.dirtyNodeBound` restated) computes
`sbTop` (Contract/Proof/DnbSpec.lean) on every tree of a state PE keeps, for
every transaction whose keys the tree can hold:

  `dirtyNodeBound_eq_sb`: from `Inv cf t s tp next` and `keyOk cf op.key`
  for each operation, `DNB.dirtyNodeBound b s t (DNB.opsKd ops) = sbTop b s ops`,
  at every node size b (with any parameters cf: `cf.Ok` is not needed).

The proof joins the two halves:

* Java's side (DnbJava.lean, DnbCount.lean, `dnb_formula`): the walk leaves
  one record for each node a key's path passes (`recOf`); the fold deepest
  first counts, for each, the number of walked nodes, its terms with its
  klongs `Kf`, and four times `mergeLevels` after a delete.
* `sbPlan`'s side (DnbSb.lean, `sb_main`): at each walked node with the
  operations that pass it, `sbPlan` is its own terms (Java's record) and its
  walked children's.

Here: `sbPlan`'s count summed over the walked nodes (`tree_cnt`), each node's
klongs from its children as Java's records give them (the records whose
parent it is are its walked children, by TREE), and the deletes' terms: four
on every node of a delete's path and eight at its end are four times its
end's depth and three (`ml_eq`).

Neither `cf.Ok` nor the fill rules are needed.
-/
import Contract.Proof.DnbSb

namespace Contract.PE

open DNB

variable {cf : Cfg} {s : Tree}

/-! ## The walked nodes -/

/-- The walked nodes, in TREE's order. -/
def Lw (s : Tree) (r : NodeId) (ops : List Op) : List NodeId := (reach s).filter (wkd s r ops)

theorem walked_reach {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} (hw : wkd s r ops y = true) : y ∈ reach s := by
  obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, y ∈ pathOf s r op.key := by simpa [wkd] using hw
  obtain ⟨_, _, _, _, _, _, hyr, _, _⟩ := walked_facts T (hops op hop) hpo
  rw [← RPD_map T]
  exact List.mem_map_of_mem hyr

theorem Lw_mem {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    (y : NodeId) : y ∈ Lw s r ops ↔ wkd s r ops y = true := by
  unfold Lw
  rw [List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨walked_reach T hops h, h⟩⟩

theorem Lw_nodup {r : NodeId} (T : TCtx cf s r) (ops : List Op) : (Lw s r ops).Nodup :=
  T.tree.filter _

/-- A walked node below x: x is walked (the path to it passes x). -/
theorem desc_path {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    ∀ (L : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode},
    s.obj x = some (.key n) → n.level ≤ L → Good s x lo hi → x ∈ reach s →
    ∀ z ∈ R s x, z ∈ pathOf s r key → x ∈ pathOf s r key := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x lo hi n hn hL hg hx z hz hzp
    have hz' := hz
    rw [R_good hg hn] at hz'
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact hzp
    · obtain ⟨⟨c, w⟩, hcw, hzw⟩ := List.mem_flatMap.mp hz'
      obtain ⟨ux, dx, hxr⟩ : ∃ ux dx, (x, ux, dx) ∈ RPD s r := by
        rw [← RPD_map T] at hx
        obtain ⟨⟨x', ux, dx⟩, h1, h2⟩ := List.mem_map.mp hx
        simp only at h2; subst h2
        exact ⟨ux, dx, h1⟩
      rcases good_kids hg hn c w hcw with ⟨m, hm, hlt, lo', hi', hgw⟩ | ⟨v, hv⟩
      · have hwr : w ∈ reach s := by
          obtain ⟨nr, hnr⟩ := good_obj T.good
          have hxR : x ∈ R s r := by rw [← reach_eq_R T.root]; exact hx
          have hsub := R_sub_of_mem nr.level hnr (le_refl _) T.good x hxR
          rw [reach_eq_R T.root]
          exact hsub.subset ((R_sub_kid hg hn hcw).subset (R_head s w))
        have hw := ih m.level (by omega) hm (le_refl _) hgw hwr z hzw hzp
        exact path_parent T hwf hxr hn hcw hw
      · have hRw : R s w = [w] := by simp [R, Tree.fuel, hv, reachAt]
        rw [hRw, List.mem_singleton] at hzw
        subst hzw
        obtain ⟨_, _, _, _, _, hm, _, _, _⟩ := walked_facts T hwf hzp
        rw [hv] at hm; cases hm

theorem sum_flatMap_nat {α β : Type} (l : List α) (f : α → List β) (g : β → Nat) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem filter_flatMap_eq {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.filter_append, ih]

/-- What `sbPlan` counts at a walked node itself. -/
def locY (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : Nat :=
  1 + 4 * (R0 b cf s r ops y).nd + 8 * endDel cf s r ops y + termY b cf s r ops y (R0 b cf s r ops y).K

/-- **`sbPlan`'s count is the sum over the walked nodes below**. -/
theorem tree_cnt (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true) :
    ∀ (L : Nat) (y : NodeId) (n : KNode), s.obj y = some (.key n) → n.level ≤ L →
      wkd s r ops y = true →
      (R0 b cf s r ops y).cnt = (((R s y).filter (wkd s r ops)).map (locY b cf s r ops)).sum := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro y n hn hL hw
    have hsb := sb_main b T hops n.level y n hn (le_refl _) hw
    obtain ⟨op0, hop0, hp0⟩ : ∃ op ∈ ops, y ∈ pathOf s r op.key := by simpa [wkd] using hw
    obtain ⟨n', _, _, lo, hi, hn', _, hg, _⟩ := walked_facts T (hops op0 hop0) hp0
    rw [hn] at hn'
    obtain rfl : n = n' := by injection hn' with h1; injection h1
    have hyr : y ∈ reach s := walked_reach T hops hw
    rw [R_good hg hn, List.filter_cons_of_pos hw, List.map_cons, List.sum_cons, filter_flatMap_eq,
      sum_flatMap_nat, hsb.cnt]
    have hwch : wch s r ops y = (live n.ks).filter (fun e => wkd s r ops e.2) := by simp [wch, hn]
    rw [hwch, sum_filter_zero (live n.ks) (fun e => wkd s r ops e.2)
      (fun e => (((R s e.2).filter (wkd s r ops)).map (locY b cf s r ops)).sum) (by
        intro e he hne
        have : (R s e.2).filter (wkd s r ops) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz hzw
          obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, z ∈ pathOf s r op.key := by simpa [wkd] using hzw
          rcases good_kids hg hn e.1 e.2 he with ⟨m, hm, _, lo', hi', hge⟩ | ⟨v, hv⟩
          · have her : e.2 ∈ reach s := by
              obtain ⟨nr, hnr⟩ := good_obj T.good
              have hyR : y ∈ R s r := by rw [← reach_eq_R T.root]; exact hyr
              have hsub := R_sub_of_mem nr.level hnr (le_refl _) T.good y hyR
              rw [reach_eq_R T.root]
              exact hsub.subset ((R_sub_kid hg hn he).subset (R_head s e.2))
            have := desc_path T (hops op hop) m.level hm (le_refl _) hge her z hz hpo
            have hw' : wkd s r ops e.2 = true := by
              simp only [wkd, List.any_eq_true, decide_eq_true_eq]; exact ⟨op, hop, this⟩
            rw [hw'] at hne; cases hne
          · have hRw : R s e.2 = [e.2] := by simp [R, Tree.fuel, hv, reachAt]
            rw [hRw, List.mem_singleton] at hz
            subst hz
            rw [hzw] at hne; cases hne
        simp [this])]
    have hrest : ((((live n.ks).filter (fun e => wkd s r ops e.2)).map
        (fun e => (R0 b cf s r ops e.2).cnt))).sum =
        ((((live n.ks).filter (fun e => wkd s r ops e.2)).map
        (fun e => (((R s e.2).filter (wkd s r ops)).map (locY b cf s r ops)).sum))).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      obtain ⟨he1, he2⟩ := List.mem_filter.mp he
      obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, e.2 ∈ pathOf s r op.key := by simpa [wkd] using he2
      obtain ⟨m, _, _, _, _, hm, _, _, _⟩ := walked_facts T (hops op hop) hpo
      have hlt : m.level < n.level := by
        rcases good_kids hg hn e.1 e.2 he1 with ⟨m', hm', hlt, _⟩ | ⟨v, hv⟩
        · rw [hm] at hm'
          obtain rfl : m = m' := by injection hm' with h1; injection h1
          exact hlt
        · rw [hm] at hv; cases hv
      exact ih m.level (by omega) e.2 m hm (le_refl _) he2
    rw [← hrest]
    unfold locY
    ring

/-! ## A node's children, as Java's records name them -/

/-- **The records whose parent is y are y's walked children** (TREE: each
node of the tree has one parent). -/
theorem kids_sum {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} (hw : wkd s r ops y = true) (G : NodeId → Nat) :
    ((Lw s r ops).map (fun c => if (treeFn cf s r).up c = some y then G c else 0)).sum =
      ((wch s r ops y).map (fun e => G e.2)).sum := by
  obtain ⟨op0, hop0, hp0⟩ : ∃ op ∈ ops, y ∈ pathOf s r op.key := by simpa [wkd] using hw
  obtain ⟨n, uy, dy, _, _, hn, hyr, _, _⟩ := walked_facts T (hops op0 hop0) hp0
  have hyreach : y ∈ reach s := walked_reach T hops hw
  have hwch : wch s r ops y = (live n.ks).filter (fun e => wkd s r ops e.2) := by simp [wch, hn]
  rw [sum_filter_zero (Lw s r ops) (fun c => decide ((treeFn cf s r).up c = some y)) _ (by
    intro c _ h
    simp only [decide_eq_false_iff_not] at h
    simp [h])]
  have hm : ((Lw s r ops).filter (fun c => decide ((treeFn cf s r).up c = some y))).map
      (fun c => if (treeFn cf s r).up c = some y then G c else 0) =
      ((Lw s r ops).filter (fun c => decide ((treeFn cf s r).up c = some y))).map G := by
    apply List.map_congr_left
    intro c hc
    have := (List.mem_filter.mp hc).2
    simp only [decide_eq_true_eq] at this
    simp [this]
  rw [hm]
  have hnd2 : ((wch s r ops y).map (·.2)).Nodup := by
    rw [hwch]
    exact (live_nodup T hyreach hn).sublist (List.filter_sublist.map _)
  rw [sum_perm_nodup ((Lw_nodup T ops).filter _) hnd2 (by
    intro c
    rw [List.mem_filter, Lw_mem T hops, List.mem_map]
    constructor
    · rintro ⟨hcw, hcu⟩
      simp only [decide_eq_true_eq] at hcu
      have hp : ∃ d, pdOf s r c = some (some y, d) := by
        simp only [treeFn] at hcu
        cases h : pdOf s r c with
        | none => rw [h] at hcu; cases hcu
        | some p => rw [h] at hcu; exact ⟨p.2, by rw [← hcu]⟩
      obtain ⟨d, hd⟩ := hp
      rcases rpd_parent s _ r none 0 c y d (pdOf_mem hd) with ⟨_, hc, _⟩ | ⟨uy', dy', n', c', h1, h2, h3, _⟩
      · cases hc
      · rw [hn] at h2
        obtain rfl : n = n' := by injection h2 with h; injection h
        refine ⟨(c', c), ?_, rfl⟩
        rw [hwch]
        exact List.mem_filter.mpr ⟨h3, hcw⟩
    · rintro ⟨e, he, rfl⟩
      rw [hwch] at he
      obtain ⟨he1, he2⟩ := List.mem_filter.mp he
      refine ⟨he2, ?_⟩
      simp [(treeFn_child T hyr hn he1).1]) G]
  rw [List.map_map]
  rfl

/-! ## The deletes' terms -/

theorem swap_count {α β : Type} (L : List α) (l : List β) (R : α → β → Bool) :
    (L.map (fun z => (l.filter (R z)).length)).sum = (l.map (fun a => (L.filter (fun z => R z a)).length)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : ∀ z, ((a :: l).filter (R z)).length = (if R z a then 1 else 0) + (l.filter (R z)).length := by
      intro z
      rw [List.filter_cons]
      cases R z a <;> simp [Nat.add_comm]
    simp only [e, List.sum_map_add, sum_filter_one, ih, List.map_cons, List.sum_cons]

theorem len_filter_eq_one {L : List NodeId} (hnd : L.Nodup) {e : NodeId} (he : e ∈ L) :
    (L.filter (fun z => decide (z = e))).length = 1 := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    rw [List.filter_cons]
    rcases List.mem_cons.mp he with hea | he
    · have : L.filter (fun z => decide (z = e)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz
        simp only [decide_eq_true_eq]
        intro h
        rw [h, hea] at hz
        exact hnd.1 hz
      simp only [hea, decide_true, ite_true, List.length_cons, Nat.add_eq_right]
      rw [← hea, this]; rfl
    · have hae : a ≠ e := fun h => hnd.1 (h ▸ he)
      simp [hae, ih hnd.2 he]

/-- A key's path has its end's depth and one nodes. -/
theorem path_len {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    (pathOf s r key).length = (treeFn cf s r).dep (endOf s r key).1 + 1 := by
  have hl := (pathOk_of T hwf).links
  obtain ⟨_, _, hdz⟩ := links_dep r _ hl
  have hend : (endOf s r key).1 = (keyP s key (key.length + 1) 0 r).1.getLastD r := keyP_stop s key _ 0 r
  rw [hend, hdz, (treeFn_root T).2]
  simp [pathOf]

theorem path_nodup {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    (pathOf s r key).Nodup :=
  (links_dep r _ (pathOk_of T hwf).links).2.1

theorem endDel_eq (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) :
    endDel cf s r ops y = (ops.filter (fun op => lfOf s y && decide (y ∈ pathOf s r op.key) &&
      endsAt (segY cf s y) op && opDel op)).length := by
  unfold endDel
  cases h : lfOf s y
  · simp
  · simp only [ite_true, Bool.true_and, filter_oy]
    congr 1
    apply List.filter_congr
    intro op _
    rw [Bool.and_assoc]

/-- **The deletes' terms**: four on every node of each delete's path that
reaches its last segment and eight at its end, summed over the walked nodes,
are four times the sum of the ends' depths and three. -/
theorem ml_eq (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true) :
    ((Lw s r ops).map (fun z => 4 * (R0 b cf s r ops z).nd + 8 * endDel cf s r ops z)).sum =
      4 * ((ops.filter (dlo s r)).map (fun op => (treeFn cf s r).dep (endOf s r op.key).1 + 3)).sum := by
  have hnd : ∀ z ∈ Lw s r ops, (R0 b cf s r ops z).nd =
      (ops.filter (fun op => decide (z ∈ pathOf s r op.key) && dlo s r op)).length := by
    intro z hz
    have hw := (Lw_mem T hops z).mp hz
    obtain ⟨op0, hop0, hp0⟩ : ∃ op ∈ ops, z ∈ pathOf s r op.key := by simpa [wkd] using hw
    obtain ⟨n, _, _, _, _, hn, _, _, _⟩ := walked_facts T (hops op0 hop0) hp0
    rw [(sb_main b T hops n.level z n hn (le_refl _) hw).nd, filter_oy]
  rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
  have h1 : ((Lw s r ops).map (fun z => (R0 b cf s r ops z).nd)).sum =
      ((ops.filter (dlo s r)).map (fun op => (treeFn cf s r).dep (endOf s r op.key).1 + 1)).sum := by
    rw [List.map_congr_left hnd, swap_count]
    rw [sum_filter_zero ops (dlo s r) _ (by intro op _ h; simp [h])]
    congr 1
    apply List.map_congr_left
    intro op hop
    obtain ⟨hop1, hd⟩ := List.mem_filter.mp hop
    have hwf := hops op hop1
    simp only [hd, Bool.and_true]
    rw [← path_len T hwf]
    apply List.Perm.length_eq
    apply (List.perm_ext_iff_of_nodup ((Lw_nodup T ops).filter _) (path_nodup T hwf)).mpr
    intro z
    rw [List.mem_filter, Lw_mem T hops, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      simp only [wkd, List.any_eq_true, decide_eq_true_eq]
      exact ⟨op, hop1, h⟩
  have h2 : ((Lw s r ops).map (fun z => endDel cf s r ops z)).sum = (ops.filter (dlo s r)).length := by
    simp only [endDel_eq]
    rw [swap_count, ← sum_filter_one]
    congr 1
    apply List.map_congr_left
    intro op hop
    have hwf := hops op hop
    have hfeq : (Lw s r ops).filter (fun z => lfOf s z && decide (z ∈ pathOf s r op.key) &&
        endsAt (segY cf s z) op && opDel op) =
        (Lw s r ops).filter (fun z => decide (z = (endOf s r op.key).1) && dlo s r op) := by
      apply List.filter_congr
      intro z hz
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨⟨hlf, hzp⟩, he⟩, hd⟩
        obtain ⟨_, _, _, _, _, hn, _, _, _⟩ := walked_facts T hwf hzp
        rw [lfOf_key hn] at hlf
        obtain ⟨hez, hk⟩ := (endsAt_iff T hwf hzp hn hlf).mpr he
        refine ⟨hez.symm, ?_⟩
        simp [dlo, kindOp, hd, hk]
      · rintro ⟨rfl, hd⟩
        simp only [dlo, kindOp, Bool.and_eq_true, beq_iff_eq] at hd
        have hzp := end_mem T hwf
        obtain ⟨L, hL⟩ := keyPath_of T hwf
        have hlf := hL.leaf
        obtain ⟨_, _, _, _, _, hn, _, _, _⟩ := walked_facts T hwf hzp
        rw [lfOf_key hn] at hlf
        refine ⟨⟨⟨by rw [lfOf_key hn]; exact hlf, hzp⟩, ?_⟩, hd.1⟩
        exact (endsAt_iff T hwf hzp hn hlf).mp ⟨rfl, hd.2⟩
    rw [hfeq]
    cases hd : dlo s r op
    · simp
    · simp only [Bool.and_true, ite_true]
      apply len_filter_eq_one (Lw_nodup T ops)
      rw [Lw_mem T hops]
      simp only [wkd, List.any_eq_true, decide_eq_true_eq]
      exact ⟨op, hop, end_mem T hwf⟩
  rw [h1, h2]
  have hc : ∀ (l : List Op) (f : Op → Nat) (c : Nat), (l.map (fun a => f a + c)).sum = (l.map f).sum + c * l.length := by
    intro l f c
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring
  have e3 := hc (ops.filter (dlo s r)) (fun op => (treeFn cf s r).dep (endOf s r op.key).1) 3
  have e1 := hc (ops.filter (dlo s r)) (fun op => (treeFn cf s r).dep (endOf s r op.key).1) 1
  rw [e3, e1]
  ring

/-! ## Java's count is the structural count -/

theorem walkedBy_kd (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) :
    walkedBy s r (ops.map kdOf) y = wkd s r ops y := by
  simp only [walkedBy, wkd, List.any_map]
  rfl

theorem delLast_kd (s : Tree) (r : NodeId) (op : Op) : delLast s r (kdOf op) = dlo s r op := rfl

theorem keyOk_wf {cf : Cfg} {k : Key} (h : keyOk cf k = true) : keyWf k = true := by
  simp only [keyOk, Bool.and_eq_true] at h; exact h.1

/-- **Java's count is the structural count** (bergdb 030-29): on the tree of a
state PE keeps, for operations whose keys the tree can hold, `dirtyNodeBound`
(Java's `Dag.dirtyNodeBound` restated) is `sbTop`, at every node size b. -/
theorem dirtyNodeBound_eq_sb {cf : Cfg} {t : Time} {s : Tree} {tp : Top} {next : NodeId} {ops : List Op}
    (b : Nat) (hI : Inv cf t s tp next) (hops : ∀ op ∈ ops, keyOk cf op.key = true) :
    DNB.dirtyNodeBound b s t (DNB.opsKd ops) = sbTop b s ops := by
  obtain ⟨r, T⟩ := tctx_of_inv hI
  have hs := at_self_of_inv hI
  have hwf : ∀ op ∈ ops, keyWf op.key = true := fun op hop => keyOk_wf (hops op hop)
  obtain ⟨rn, hrn⟩ := good_obj T.good
  set E := treeFn cf s r with hE
  have hk : ∀ k ∈ ops.map kdOf, PathOk s r E k.1 := by
    intro k hk
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hk
    exact pathOk_of T (hwf op hop)
  have hLm : ∀ y, y ∈ Lw s r ops ↔ walkedBy s r (ops.map kdOf) y = true := by
    intro y; rw [walkedBy_kd]; exact Lw_mem T hwf y
  set Kf : NodeId → Nat := fun y => (R0 b cf s r ops y).K with hKf
  -- the collapses of the children: none without a delete that reaches its last segment
  have hcol0 : (ops.map kdOf).any (delLast s r) = false → ∀ c, (recY cf s r ops c).collapses = 0 := by
    intro hany c
    by_cases hc : ∃ n, s.obj c = some (.key n)
    · obtain ⟨n, hn⟩ := hc
      have hri := recOf_RI s r (treeFn cf s r) c n (getKey_eq.mpr hn) (ops.map kdOf)
      show (recOf s r (treeFn cf s r) c (ops.map kdOf)).collapses = 0
      rw [hri.col]
      have : (ops.map kdOf).any (dlP s r c) = false := by
        rw [List.any_eq_false] at hany ⊢
        intro k hk h
        apply hany k hk
        simp only [dlP, Bool.and_eq_true] at h
        simp [delLast, h.1.2, h.2]
      simp [this]
    · have : recOf s r (treeFn cf s r) c (ops.map kdOf) = initR s (treeFn cf s r) c :=
        recOf_not s r _ c _ (by
          rw [walkedBy_kd]
          by_contra hw
          simp only [Bool.not_eq_false] at hw
          obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, c ∈ pathOf s r op.key := by simpa [wkd] using hw
          obtain ⟨n, _, _, _, _, hn, _, _, _⟩ := walked_facts T (hwf op hop) hpo
          exact hc ⟨n, hn⟩)
      show (recOf s r (treeFn cf s r) c (ops.map kdOf)).collapses = 0
      rw [this]
      unfold initR
      split
      · rfl
      · rfl
  have hK : ∀ y ∈ Lw s r ops, (recOf s r E y (ops.map kdOf)).klongs +
      (if (ops.map kdOf).any (delLast s r) then
        ((Lw s r ops).map (fun c => if E.up c = some y then (recOf s r E c (ops.map kdOf)).collapses else 0)).sum
        else 0) +
      ((Lw s r ops).map (fun c => if E.up c = some y then
        (let w := recOf s r E c (ops.map kdOf)
         if ovOf b w (Kf c) = 0 then 0 else if E.upIn c then partsOf b w (Kf c) else ovOf b w (Kf c) + 1)
        else 0)).sum = Kf y := by
    intro y hy
    have hw := (Lw_mem T hwf y).mp hy
    obtain ⟨op0, hop0, hp0⟩ : ∃ op ∈ ops, y ∈ pathOf s r op.key := by simpa [wkd] using hw
    obtain ⟨n, _, _, _, _, hn, _, _, _⟩ := walked_facts T (hwf op0 hop0) hp0
    have hsb := sb_main b T hwf n.level y n hn (le_refl _) hw
    have hcs := kids_sum T hwf hw (fun c => (recY cf s r ops c).collapses)
    have hcb := kids_sum T hwf hw (fun c => contribY b cf s r ops c (Kf c))
    have hite : (if (ops.map kdOf).any (delLast s r) then
        ((Lw s r ops).map (fun c => if E.up c = some y then (recOf s r E c (ops.map kdOf)).collapses else 0)).sum
        else 0) = ((wch s r ops y).map (fun e => (recY cf s r ops e.2).collapses)).sum := by
      rw [← hcs]
      split
      · rfl
      · rename_i hany
        have := hcol0 (by simpa using hany)
        symm
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        simp [this c]
    rw [hite]
    show (recY cf s r ops y).klongs + _ + _ = (R0 b cf s r ops y).K
    rw [hsb.K, List.sum_map_add]
    have : ((Lw s r ops).map (fun c => if E.up c = some y then
        (let w := recOf s r E c (ops.map kdOf)
         if ovOf b w (Kf c) = 0 then 0 else if E.upIn c then partsOf b w (Kf c) else ovOf b w (Kf c) + 1)
        else 0)).sum = ((wch s r ops y).map (fun e => contribY b cf s r ops e.2 (R0 b cf s r ops e.2).K)).sum :=
      hcb
    rw [this]
    ring
  have hJ := dnb_formula b hs T.root (getKey_eq.mpr hrn) (treeFn_hcl (cf := cf) (s := s) (r := r))
    (treeFn_hci T) (lfOf_key hrn) (treeFn_root T).1 (treeFn_root T).2 (ops.map kdOf) hk (Lw s r ops)
    (Lw_nodup T ops) hLm Kf hK
  rw [opsKd_eq, hJ]
  -- the structural count
  unfold sbTop
  rw [T.root]
  simp only
  by_cases hne : ops.isEmpty = true
  · have hops0 : ops = [] := List.isEmpty_iff.mp hne
    subst hops0
    have hL0 : Lw s r [] = [] := by simp [Lw, wkd]
    simp [hL0]
  · simp only [hne, Bool.false_eq_true, ite_false]
    obtain ⟨op0, hop0⟩ : ∃ op, op ∈ ops := by
      cases ops with
      | nil => simp at hne
      | cons op _ => exact ⟨op, List.mem_cons_self⟩
    have hrw : wkd s r ops r = true := by
      simp only [wkd, List.any_eq_true, decide_eq_true_eq]
      exact ⟨op0, hop0, by simp [pathOf]⟩
    have hsegr : segY cf s r = 0 := segY_of_shaped T.shaped
    have hOr : Oy s r ops r = ops := by
      unfold Oy; apply List.filter_eq_self.mpr; intro op _; simp [pathOf]
    have hiRr : iRoot cf s r r = true := by
      simp [iRoot, TreeFn.upIn, (treeFn_root T).1]
    have hR0r : sbPlan b s (s.fuel r) r 0 ops true = R0 b cf s r ops r := by
      simp only [R0, hsegr, hOr, hiRr]
    rw [hR0r, tree_cnt b T hwf rn.level r rn hrn (le_refl _) hrw, ← reach_eq_R T.root]
    -- the walked nodes' own counts
    have hloc : ((Lw s r ops).map (locY b cf s r ops)).sum = (Lw s r ops).length +
        ((Lw s r ops).map (fun z => 4 * (R0 b cf s r ops z).nd + 8 * endDel cf s r ops z)).sum +
        ((Lw s r ops).map (fun z => termY b cf s r ops z (R0 b cf s r ops z).K)).sum := by
      unfold locY
      have hc : ∀ (l : List NodeId) , (l.map (fun z => 1 + 4 * (R0 b cf s r ops z).nd + 8 * endDel cf s r ops z +
          termY b cf s r ops z (R0 b cf s r ops z).K)).sum = l.length +
          (l.map (fun z => 4 * (R0 b cf s r ops z).nd + 8 * endDel cf s r ops z)).sum +
          (l.map (fun z => termY b cf s r ops z (R0 b cf s r ops z).K)).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring
      exact hc _
    show _ = (((reach s).filter (wkd s r ops)).map (locY b cf s r ops)).sum
    rw [show (reach s).filter (wkd s r ops) = Lw s r ops from rfl, hloc, ml_eq b T hwf]
    have hml : ((List.filter (delLast s r) (ops.map kdOf)).map (fun k => E.dep (endOf s r k.1).1 + 3)).sum =
        ((ops.filter (dlo s r)).map (fun op => (treeFn cf s r).dep (endOf s r op.key).1 + 3)).sum := by
      rw [List.filter_map, List.map_map]
      rfl
    rw [hml]
    have hterm : ((Lw s r ops).map (fun y => let w := recOf s r E y (ops.map kdOf)
        freshSum b w + (if ovOf b w (Kf y) = 0 then 0 else partsOf b w (Kf y) +
          (if E.upIn y then 0 else max (ovOf b w (Kf y)) (rootsAbove b (partsOf b w (Kf y))))))).sum =
        ((Lw s r ops).map (fun z => termY b cf s r ops z (R0 b cf s r ops z).K)).sum := rfl
    rw [hterm]
    split
    · ring
    · rename_i hany
      have : ops.filter (dlo s r) = [] := by
        rw [List.filter_eq_nil_iff]
        intro op hop h
        apply hany
        rw [List.any_map]
        exact List.any_eq_true.mpr ⟨op, hop, h⟩
      rw [this]
      simp

end Contract.PE
