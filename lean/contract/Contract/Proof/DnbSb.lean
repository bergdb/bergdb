/-
bergdb 030-29: `sbPlan` (Contract/Proof/DnbSpec.lean) node by node: at a
walked node with the operations that pass it, its count is its own terms
(Java's record of it, DnbRec.lean) and its walked children's.

* Lists: `sum_part` (each element counted once among the values it may
  map to), `route_spec` (PE's `route` is `searchLte` on a live list whose
  first compare value is at most every operation's).
* The operations of a node (`Oy`): those whose path passes it; at an
  inner node a child's are those `searchLte` sends to it, at a segment leaf
  a next segment's root's those whose segment is its compare value and that
  go on (`oy_inner`, `oy_leaf`); where they end (`end_inner`, `end_leaf`).
* `sb_inner`, `sb_leaf`: `sbPlan` at a walked inner node, at a walked
  segment leaf, as `sbNode` of its walked children's counts.
* `sb_main` (`SBP`): at every walked node, by induction on its level, with
  any fuel from the node's own: its deletes that reach their last segment
  (`nd`), its collapses (its height, `ci`), its klongs (Java's record's and
  what its walked children give it, `K`), its count (`cnt`) and what it gives
  its parent (`up`).
-/
import Contract.Proof.DnbRec

namespace Contract.PE

open DNB

variable {cf : Cfg} {s : Tree}

/-! ## Lists -/

theorem sum_ite_one {β : Type} [DecidableEq β] : ∀ (D : List β), D.Nodup → ∀ x ∈ D,
    (D.map (fun v => if x = v then 1 else 0)).sum = 1
  | [], _, x, hx => by cases hx
  | d :: D, hnd, x, hx => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have : (D.map (fun v => if x = v then 1 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
        have : x ≠ v := fun h => hnd.1 (h ▸ hv)
        simp [this]
      simp [this]
    · have hxd : x ≠ d := fun h => hnd.1 (h ▸ hx)
      simp [hxd, sum_ite_one D hnd.2 x hx]

/-- **Each element counted once** among the values it may map to. -/
theorem sum_part {α β : Type} [DecidableEq β] (D : List β) (hD : D.Nodup) (h : α → β) (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → h a ∈ D) →
    (D.map (fun v => (l.filter (fun a => p a && decide (h a = v))).length)).sum = (l.filter p).length
  | [], _ => by simp
  | a :: l, hc => by
    have ih := sum_part D hD h p l (fun a' ha' => hc a' (List.mem_cons_of_mem _ ha'))
    have e : ∀ v, ((a :: l).filter (fun a => p a && decide (h a = v))).length =
        (if p a = true ∧ h a = v then 1 else 0) + (l.filter (fun a => p a && decide (h a = v))).length := by
      intro v
      rw [List.filter_cons]
      by_cases hp : p a = true <;> by_cases hv : h a = v <;> simp [hp, hv, Nat.add_comm]
    simp only [e]
    rw [List.sum_map_add, ih, List.filter_cons]
    by_cases hp : p a = true
    · simp only [hp, true_and, ite_true, List.length_cons]
      rw [sum_ite_one D hD (h a) (hc a List.mem_cons_self hp)]
      omega
    · simp [hp]

/-- The last entry of a live list at or below c (Java's `searchLte`). -/
def selE (lv : List (Nat × NodeId)) (c : Nat) : Option (Nat × NodeId) :=
  (lv.filter (fun e => decide (e.1 ≤ c))).getLast?

theorem searchLte_sel (ks : List Klong) (c : Nat) : searchLte ks (.at c) = selE (live ks) c := by
  rw [searchLte_spec, selE]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Pos.below]
  by_cases h : e.1 ≤ c
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

theorem selE_cons (e : Nat × NodeId) (l : List (Nat × NodeId)) (c : Nat) :
    selE (e :: l) c = match selE l c with
      | some x => some x
      | none => if e.1 ≤ c then some e else none := by
  unfold selE
  rw [List.filter_cons]
  cases h : (l.filter (fun e => decide (e.1 ≤ c))).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at h
    rw [h]
    by_cases he : e.1 ≤ c <;> simp [he]
  | some x =>
    simp only
    by_cases he : e.1 ≤ c
    · simp only [he, decide_true, ite_true]
      rw [List.getLast?_cons, h]; rfl
    · simp [he, h]

theorem selE_mem {lv : List (Nat × NodeId)} {c : Nat} {e : Nat × NodeId} (h : selE lv c = some e) :
    e ∈ lv ∧ e.1 ≤ c := by
  have := List.mem_of_getLast? h
  rw [List.mem_filter] at this
  exact ⟨this.1, by simpa using this.2⟩

/-- **PE's `route` is `searchLte`**: on a live list in increasing order whose
first compare value is at most every operation's, each child gets the
operations whose last entry at or below their compare value is its own. -/
theorem route_spec {α : Type} (cv : α → Nat) : ∀ (lv : List (Nat × NodeId)) (ops : List α),
    lv.Pairwise (fun a b => a.1 < b.1) → (∀ e, lv.head? = some e → ∀ o ∈ ops, e.1 ≤ cv o) →
    route cv lv ops = lv.map (fun e => ops.filter (fun o => decide (selE lv (cv o) = some e)))
  | [], _, _, _ => rfl
  | [e], ops, _, hh => by
    simp only [route, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    symm
    apply List.filter_eq_self.mpr
    intro o ho
    have := hh e rfl o ho
    simp [selE, this]
  | e :: e' :: r, ops, hs, hh => by
    simp only [route, List.map_cons]
    have hs' := List.pairwise_cons.mp hs
    have hee' : e.1 < e'.1 := hs'.1 e' List.mem_cons_self
    have hgt : ∀ x ∈ e' :: r, e.1 < x.1 := fun x hx => hs'.1 x hx
    have ih := route_spec cv (e' :: r) (ops.filter (fun o => decide (e'.1 ≤ cv o))) hs'.2 (by
      intro x hx o ho
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      simpa using (List.mem_filter.mp ho).2)
    rw [ih]
    -- the selection in e :: e' :: r
    have hsel : ∀ o ∈ ops, selE (e :: e' :: r) (cv o) =
        if cv o < e'.1 then some e else selE (e' :: r) (cv o) := by
      intro o ho
      have he0 := hh e rfl o ho
      rw [selE_cons]
      by_cases hlt : cv o < e'.1
      · have : selE (e' :: r) (cv o) = none := by
          unfold selE
          rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
          intro x hx
          have : e'.1 ≤ x.1 := by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_refl _
            · exact le_of_lt ((List.pairwise_cons.mp hs'.2).1 x hx)
          simp only [decide_eq_true_eq]; omega
        simp [this, he0, hlt]
      · have : ∃ x, selE (e' :: r) (cv o) = some x := by
          unfold selE
          cases h : ((e' :: r).filter (fun e => decide (e.1 ≤ cv o))).getLast? with
          | some x => exact ⟨x, rfl⟩
          | none =>
            rw [List.getLast?_eq_none_iff] at h
            have : e' ∈ (e' :: r).filter (fun e => decide (e.1 ≤ cv o)) := by
              simp only [List.mem_filter, List.mem_cons_self, true_and, decide_eq_true_eq]; omega
            rw [h] at this; cases this
        obtain ⟨x, hx⟩ := this
        simp [hx, hlt]
    congr 1
    · apply List.filter_congr
      intro o ho
      rw [hsel o ho]
      by_cases hlt : cv o < e'.1
      · simp [hlt]
      · simp only [hlt, ite_false, decide_false]
        symm
        simp only [decide_eq_false_iff_not]
        intro h
        have := (selE_mem h).1
        have := hgt e this
        omega
    · change _ = List.map (fun x => ops.filter (fun o => decide (selE (e :: e' :: r) (cv o) = some x)))
        (e' :: r)
      apply List.map_congr_left
      intro x hx
      rw [List.filter_filter]
      apply List.filter_congr
      intro o ho
      rw [hsel o ho]
      by_cases hlt : cv o < e'.1
      · have hxe : x ≠ e := fun h => by have := hgt x hx; rw [h] at this; omega
        simp [hlt, Ne.symm hxe]
      · simp only [hlt, ite_false]
        have : e'.1 ≤ cv o := by omega
        simp [this]

/-! ## Live children of the tree's nodes -/

/-- **The live children of a node of the tree are distinct** (TREE). -/
theorem live_nodup {r : NodeId} (T : TCtx cf s r) {y : NodeId} (hy : y ∈ reach s) {n : KNode}
    (hn : s.obj y = some (.key n)) : ((live n.ks).map (·.2)).Nodup := by
  obtain ⟨g, lo, hi, hg, _⟩ := tree_shaped T hy hn
  obtain ⟨nr, hnr⟩ := good_obj T.good
  have hyR : y ∈ R s r := by rw [← reach_eq_R T.root]; exact hy
  have hsub := R_sub_of_mem nr.level hnr (le_refl _) T.good y hyR
  have hnd : (R s y).Nodup := hsub.nodup (by rw [← reach_eq_R T.root]; exact T.tree)
  rw [R_good hg hn] at hnd
  have h2 := (List.nodup_cons.mp hnd).2
  unfold List.Nodup at h2
  rw [List.pairwise_flatMap] at h2
  unfold List.Nodup
  rw [List.pairwise_map]
  apply h2.2.imp
  intro a b hab heq
  exact hab a.2 (R_head s a.2) b.2 (R_head s b.2) heq

/-- A live child of a node of the tree on a key's path: its parent is on it. -/
theorem path_parent {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) {c : Nat} {z : NodeId} (hcz : (c, z) ∈ live n.ks)
    (hz : z ∈ pathOf s r key) : y ∈ pathOf s r key := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  have hzu : (treeFn cf s r).up z = some y := (treeFn_child T hyr hn hcz).1
  rw [← hL.map] at hz ⊢
  obtain ⟨⟨z', g'⟩, hzp, rfl⟩ := List.mem_map.mp hz
  have hne : L.head? ≠ some (z', g') := by
    rw [hL.head]
    intro h
    cases h
    rw [(treeFn_root T).1] at hzu; cases hzu
  obtain ⟨⟨x, gx⟩, hxL, hxz⟩ := nchain_pred s key L _ hL.chain hzp hne
  obtain ⟨nx, cx, hxn, hcx, _, _, _⟩ := nxt_some (hL.nodes _ hxL) hxz
  have hxr : x ∈ pathOf s r key := by rw [← hL.map]; exact List.mem_map_of_mem hxL
  obtain ⟨ux, dx, hxr'⟩ := path_rpd T hwf hxr
  have hzx := (treeFn_child T hxr' hxn hcx).1
  rw [hzu] at hzx
  cases hzx
  exact List.mem_map_of_mem hxL

theorem nxt_seg {key : Key} {x y : NodeId} {g g' : Nat} (h : nxt s key (x, g) = some (y, g')) :
    g' = g ∨ (g' = g + 1 ∧ g + 1 < key.length) := by
  unfold nxt at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hlt
        split at h
        · split at h
          · cases h; exact Or.inr ⟨rfl, hlt⟩
          · cases h
        · cases h
      · cases h
    · split at h
      · split at h
        · cases h; exact Or.inl rfl
        · cases h
      · cases h

theorem nchain_all {key : Key} (P : NodeId × Nat → Prop)
    (hP : ∀ x y, P x → nxt s key x = some y → P y) :
    ∀ (L : List (NodeId × Nat)) (a : NodeId × Nat), NChain s key (a :: L) → P a → ∀ q ∈ a :: L, P q
  | [], a, _, ha, q, hq => by simp only [List.mem_singleton] at hq; subst hq; exact ha
  | b :: L, a, hch, ha, q, hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ha
    · exact nchain_all P hP L b hch.2 (hP a b ha hch.1) q hq

/-- The segments of a key's path are below its length. -/
theorem keyPath_seg_lt {r : NodeId} {key : Key} (hwf : keyWf key = true) {L : List (NodeId × Nat)}
    (hL : KeyPath cf s r key L) : ∀ q ∈ L, q.2 < key.length := by
  obtain ⟨a, L', rfl⟩ : ∃ a L', L = a :: L' := by
    cases h : L with
    | nil => have := hL.head; rw [h] at this; cases this
    | cons a L' => exact ⟨a, L', rfl⟩
  have ha : a = (r, 0) := by have := hL.head; simpa using this
  subst ha
  apply nchain_all (fun q => q.2 < key.length) _ L' (r, 0) hL.chain
  · exact List.length_pos_iff.mpr (keyWf_ne hwf)
  · rintro ⟨x, gx⟩ ⟨y, gy⟩ hx hxy
    rcases nxt_seg hxy with h | ⟨h, h'⟩
    · simp only at hx ⊢; omega
    · simp only at hx ⊢; omega

theorem keyWf_long : ∀ {k : Key}, keyWf k = true → ∀ j, j + 1 < k.length → isLong (k[j]?.getD 0) = true
  | [], _, j, hj => by simp at hj
  | [c], _, j, hj => by simp at hj
  | c :: d :: rest, h, j, hj => by
    simp only [keyWf, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := keyWf_long h.2 j (by simp at hj ⊢; omega)
      simpa using this

/-! ## The operations of a node -/

/-- The operations whose path passes y. -/
def Oy (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : List Op :=
  ops.filter (fun op => decide (y ∈ pathOf s r op.key))

/-- Some operation's path passes y. -/
def wkd (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : Bool :=
  ops.any (fun op => decide (y ∈ pathOf s r op.key))

theorem oy_ne {r : NodeId} {ops : List Op} {y : NodeId} : Oy s r ops y ≠ [] ↔ wkd s r ops y = true := by
  simp [Oy, wkd, List.filter_eq_nil_iff]

/-- A walked node's facts: a key node of the tree, sound and shaped at its
segment `segY`. -/
theorem walked_facts {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    (hy : y ∈ pathOf s r key) : ∃ n uy dy lo hi, s.obj y = some (.key n) ∧ (y, uy, dy) ∈ RPD s r ∧
      Good s y lo hi ∧ Shaped cf s (segY cf s y) (htIn cf s y) y := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  have hyL := keyPath_seg hL hy
  obtain ⟨lo, hi, hg, hsh⟩ := hL.nodes _ hyL
  obtain ⟨n, hn⟩ := good_obj hg
  obtain ⟨uy, dy, hyr⟩ := path_rpd T hwf hy
  exact ⟨n, uy, dy, lo, hi, hn, hyr, hg, hsh⟩

/-- **A child of an inner node**: an operation passes it exactly if it passes
the node and `searchLte` there sends it to it. -/
theorem oy_inner {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode} (hn : s.obj y = some (.key n))
    (hl : n.leaf = false) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hsh : Shaped cf s (segY cf s y) (htIn cf s y) y) {e : Nat × NodeId} (he : e ∈ live n.ks) :
    e.2 ∈ pathOf s r key ↔ y ∈ pathOf s r key ∧ selE (live n.ks) (key[segY cf s y]?.getD 0) = some e := by
  have hyreach : y ∈ reach s := by rw [← RPD_map T]; exact List.mem_map_of_mem hyr
  constructor
  · intro hz
    have hy := path_parent T hwf hyr hn he hz
    refine ⟨hy, ?_⟩
    obtain ⟨g', hnx⟩ := (path_child T hwf hy hn he).mp hz
    obtain ⟨n', c', hn', hmem, _, hin, _⟩ := nxt_some ⟨lo, hi, hg, hsh⟩ hnx
    rw [hn] at hn'
    obtain rfl : n = n' := by injection hn' with h1; injection h1
    obtain ⟨_, hsl⟩ := hin hl
    have hsl' : selE (live n.ks) (key[segY cf s y]?.getD 0) = some (c', e.2) := by
      rw [← searchLte_sel]; exact hsl
    rw [hsl']
    have hnd := live_nodup T hyreach hn
    have := List.inj_on_of_nodup_map hnd hmem he rfl
    rw [this]
  · rintro ⟨hy, hsel⟩
    apply (path_child T hwf hy hn he).mpr
    have hm := (selE_mem hsel).1
    obtain ⟨m, hm', _⟩ : ∃ m, s.obj e.2 = some (.key m) ∧ True := by
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ _ hkey _ _ =>
        rw [hn] at hobj'
        obtain rfl : n = n' := by injection hobj' with h1; injection h1
        obtain ⟨m, hm', _⟩ := hkey e.1 e.2 he (fun h => by rw [hl] at h; cases h)
        exact ⟨m, hm', trivial⟩
    refine ⟨segY cf s y, ?_⟩
    unfold nxt
    simp only [getKey_eq.mpr hn, hl, Bool.false_eq_true, ite_false, searchLte_sel, hsel,
      getKey_eq.mpr hm', Option.isSome_some, ite_true]

/-- **A next segment's root below a segment leaf**: an operation passes it
exactly if it passes the leaf, goes on past the leaf's segment, and its
compare value there names it. -/
theorem oy_leaf {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode} (hn : s.obj y = some (.key n))
    (hl : n.leaf = true) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    {c : Nat} {z : NodeId} (hcz : (c, z) ∈ live n.ks) :
    z ∈ pathOf s r key ↔ y ∈ pathOf s r key ∧ segY cf s y + 1 < key.length ∧
      key[segY cf s y]?.getD 0 = c := by
  have hyreach : y ∈ reach s := by rw [← RPD_map T]; exact List.mem_map_of_mem hyr
  have hwfk := good_wf hg hn
  constructor
  · intro hz
    have hy := path_parent T hwf hyr hn hcz hz
    obtain ⟨g', hnx⟩ := (path_child T hwf hy hn hcz).mp hz
    unfold nxt at hnx
    simp only [getKey_eq.mpr hn, hl, ite_true] at hnx
    split at hnx
    · rename_i hlt
      split at hnx
      · rename_i z' hq
        split at hnx
        · cases hnx
          rw [searchEq_spec n.ks hwfk] at hq
          have hm := (lookup_iff_mem (live_sorted n.ks) _ _).mp hq
          -- two entries with the node z: the same compare value
          have hnd := live_nodup T hyreach hn
          have := List.inj_on_of_nodup_map hnd hm hcz rfl
          refine ⟨hy, hlt, ?_⟩
          have := congrArg Prod.fst this
          exact this
        · cases hnx
      · cases hnx
    · cases hnx
  · rintro ⟨hy, hlt, hc⟩
    apply (path_child T hwf hy hn hcz).mpr
    refine ⟨segY cf s y + 1, ?_⟩
    have hq : searchEq n.ks (key[segY cf s y]?.getD 0) = some z := by
      rw [searchEq_spec n.ks hwfk, hc]
      exact (lookup_iff_mem (live_sorted n.ks) _ _).mpr hcz
    have hlong : isLong c = true := by rw [← hc]; exact keyWf_long hwf _ hlt
    obtain ⟨m, hm, _⟩ : ∃ m, s.obj z = some (.key m) ∧ True := by
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ _ hkey _ _ =>
        rw [hn] at hobj'
        obtain rfl : n = n' := by injection hobj' with h1; injection h1
        obtain ⟨m, hm', _⟩ := hkey c z hcz (fun _ => hlong)
        exact ⟨m, hm', trivial⟩
    unfold nxt
    simp only [getKey_eq.mpr hn, hl, ite_true, hlt, hq, getKey_eq.mpr hm, Option.isSome_some]

/-! ## Where a key's walk ends -/

theorem end_seg {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    (endOf s r key).2.1 = segY cf s (endOf s r key).1 := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  obtain ⟨_, _, _, hsh⟩ := hL.nodes _ (List.mem_of_getLast? hL.last)
  exact (segY_of_shaped hsh).symm

theorem end_mem {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) :
    (endOf s r key).1 ∈ pathOf s r key := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  rw [← hL.map]
  exact List.mem_map_of_mem (List.mem_of_getLast? hL.last)

/-- No walk ends at an inner node. -/
theorem end_inner {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    (hy : y ∈ pathOf s r key) {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = false) :
    (endOf s r key).1 ≠ y := by
  intro he
  obtain ⟨n', uy, dy, lo, hi, hn', _, hg, hsh⟩ := walked_facts T hwf hy
  obtain ⟨z, hz⟩ := nxt_inner (key := key) (g := segY cf s y) ⟨lo, hi, hg, hsh⟩ hn hl
  have h2 := (path_end T hwf hy).mp he
  rw [hz] at h2
  cases h2

/-- **The end at a segment leaf** of segment g: a walk that passes it ends
there exactly if the key ends at g or the leaf lacks its next segment; it
ends `last` in the first case, `fresh` in the second. -/
theorem end_leaf {r : NodeId} (T : TCtx cf s r) {key : Key} (hwf : keyWf key = true) {y : NodeId}
    (hy : y ∈ pathOf s r key) {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    ((endOf s r key).1 = y ↔
      (key.length = segY cf s y + 1 ∨ (live n.ks).lookup (key[segY cf s y]?.getD 0) = none)) ∧
    ((endOf s r key).1 = y → (endOf s r key).2.1 = segY cf s y ∧
      (endOf s r key).2.2 = (if key.length = segY cf s y + 1 then .last else .fresh)) := by
  obtain ⟨L, hL⟩ := keyPath_of T hwf
  obtain ⟨n', uy, dy, lo, hi, hn', _, hg, hsh⟩ := walked_facts T hwf hy
  rw [hn] at hn'
  obtain rfl : n = n' := by injection hn' with h1; injection h1
  have hwfk := good_wf hg hn
  have hlt : segY cf s y < key.length := keyPath_seg_lt hwf hL _ (keyPath_seg hL hy)
  -- the step from (y, g)
  have hnx : nxt s key (y, segY cf s y) = none ↔
      (key.length = segY cf s y + 1 ∨ (live n.ks).lookup (key[segY cf s y]?.getD 0) = none) := by
    unfold nxt
    simp only [getKey_eq.mpr hn, hl, ite_true]
    by_cases h1 : segY cf s y + 1 < key.length
    · simp only [h1, ite_true]
      have hne : key.length ≠ segY cf s y + 1 := by omega
      rw [searchEq_spec n.ks hwfk]
      cases hq : (live n.ks).lookup (key[segY cf s y]?.getD 0) with
      | none => simp [hne]
      | some z =>
        simp only [hne, false_or, reduceCtorEq, iff_false]
        -- a long compare value names a key node
        have hm := (lookup_iff_mem (live_sorted n.ks) _ _).mp hq
        have hlong := keyWf_long hwf _ h1
        cases hg with
        | mk _ _ _ n' hobj' _ _ _ _ hkey _ _ =>
          rw [hn] at hobj'
          obtain rfl : n = n' := by injection hobj' with h1; injection h1
          obtain ⟨m, hm', _⟩ := hkey _ z hm (fun _ => hlong)
          simp [getKey_eq.mpr hm']
    · have : key.length = segY cf s y + 1 := by omega
      simp [this]
  refine ⟨(path_end T hwf hy).trans hnx, ?_⟩
  intro he
  have hseg : (endOf s r key).2.1 = segY cf s y := by rw [end_seg T hwf, he]
  refine ⟨hseg, ?_⟩
  rw [hL.kind, he, hseg]
  unfold kindOf
  simp only
  by_cases h1 : key.length = segY cf s y + 1
  · simp [h1]
  · have h2 : ¬ (segY cf s y + 1 = key.length) := by omega
    simp only [h2, ite_false, h1]
    have := (hnx.mp ((path_end T hwf hy).mp he)).resolve_left h1
    rw [getKey_eq.mpr hn]
    simp only [Option.bind_some, searchEq_spec n.ks hwfk, this]

/-! ## Java's keys from the operations -/

/-- Java's key of an operation, and whether it is a delete. -/
def kdOf (op : Op) : Key × Bool := (op.key, opDel op)

theorem opsKd_eq (ops : List Op) : opsKd ops = ops.map kdOf := by
  unfold opsKd
  apply List.map_congr_left
  intro op _
  cases op <;> rfl

theorem len_filter_kd (ops : List Op) (P : Key × Bool → Bool) :
    ((ops.map kdOf).filter P).length = (ops.filter (fun op => P (kdOf op))).length := by
  rw [List.filter_map, List.length_map]; rfl

theorem any_kd (ops : List Op) (P : Key × Bool → Bool) :
    (ops.map kdOf).any P = ops.any (fun op => P (kdOf op)) := by
  rw [List.any_map]; rfl

/-- The kind of an operation's end. -/
def kindOp (s : Tree) (r : NodeId) (op : Op) : WEnd := (endOf s r op.key).2.2

/-- A delete that reaches its last segment. -/
def dlo (s : Tree) (r : NodeId) (op : Op) : Bool := opDel op && kindOp s r op == .last

theorem filter_oy (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) (P : Op → Bool) :
    (Oy s r ops y).filter P = ops.filter (fun op => decide (y ∈ pathOf s r op.key) && P op) := by
  rw [Oy, List.filter_filter]
  apply List.filter_congr
  intro op _
  rw [Bool.and_comm]

theorem len_dlP (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) :
    ((ops.map kdOf).filter (dlP s r y)).length = ((Oy s r ops y).filter (dlo s r)).length := by
  rw [len_filter_kd, filter_oy]
  congr 1
  apply List.filter_congr
  intro op _
  unfold dlP passK dlo kindOp kdOf
  simp only
  rw [Bool.and_assoc]

/-! ## `sbPlan` at a walked node -/

/-- y is a segment tree's root (`sbPlan`'s `isRoot`): the space root, or a
node whose parent is a segment leaf. -/
def iRoot (cf : Cfg) (s : Tree) (r y : NodeId) : Bool := !(treeFn cf s r).upIn y

/-- `sbPlan` at y with the operations that pass it, with the fuel of y. -/
def R0 (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : SR :=
  sbPlan b s (s.fuel y) y (segY cf s y) (Oy s r ops y) (iRoot cf s r y)

/-- The walked children of y: its live entries whose node a path passes. -/
def wch (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : List (Nat × NodeId) :=
  match s.obj y with
  | some (.key n) => (live n.ks).filter (fun e => wkd s r ops e.2)
  | _ => []

theorem zip_map_self {α β : Type} (F : α → β) : ∀ (l : List α), l.zip (l.map F) = l.map (fun e => (e, F e))
  | [] => rfl
  | a :: l => by simp [zip_map_self F l]

theorem fuel_kid {y : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi) {n : KNode}
    (hn : s.obj y = some (.key n)) {c : Nat} {z : NodeId} (hcz : (c, z) ∈ live n.ks) {m : KNode}
    (hm : s.obj z = some (.key m)) {f : Nat} (hf : s.fuel y ≤ f + 1) : s.fuel z ≤ f := by
  rcases good_kids hg hn c z hcz with ⟨m', hm', hlt, _⟩ | ⟨v, hv⟩
  · rw [hm] at hm'
    obtain rfl : m = m' := by injection hm' with h1; injection h1
    simp [Tree.fuel, hn] at hf; simp [Tree.fuel, hm]; omega
  · rw [hm] at hv; cases hv

/-- The operations of a child of an inner node: those `searchLte` sends to it. -/
theorem oy_inner_eq {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = false) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hsh : Shaped cf s (segY cf s y) (htIn cf s y) y) {e : Nat × NodeId} (he : e ∈ live n.ks) :
    (Oy s r ops y).filter (fun op => decide (selE (live n.ks) (segAt (segY cf s y) op) = some e)) =
      Oy s r ops e.2 := by
  rw [filter_oy, Oy]
  apply List.filter_congr
  intro op hop
  have := oy_inner T (hops op hop) hyr hn hl hg hsh he
  simp only [segAt] at this ⊢
  by_cases h1 : e.2 ∈ pathOf s r op.key
  · simp [h1, this.mp h1]
  · simp only [h1, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases h2 : y ∈ pathOf s r op.key
    · exact Or.inr (decide_eq_false (fun h3 => h1 (this.mpr ⟨h2, h3⟩)))
    · exact Or.inl h2

/-- **`sbPlan` at a walked inner node**: `sbNode` of its walked children's
counts (given them for each walked child, with any fuel from the child's). -/
theorem sb_inner (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = false) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hsh : Shaped cf s (segY cf s y) (htIn cf s y) y)
    (hIH : ∀ e ∈ live n.ks, wkd s r ops e.2 = true → ∀ f', s.fuel e.2 ≤ f' →
      sbPlan b s f' e.2 (segY cf s e.2) (Oy s r ops e.2) (iRoot cf s r e.2) = R0 b cf s r ops e.2)
    (iR : Bool) (f : Nat) (hf : s.fuel y ≤ f) :
    sbPlan b s f y (segY cf s y) (Oy s r ops y) iR =
      let rs := (wch s r ops y).map (fun e => R0 b cf s r ops e.2)
      let nd := (rs.map (·.nd)).sum
      let ci := if nd = 0 then 0 else 1 + ((rs.filter (fun r => 0 < r.nd)).map (·.ci)).foldl max 0
      sbNode b n iR (4 * nd + (rs.map (·.up)).sum) nd ci (rs.map (·.cnt)).sum := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [Tree.fuel, hn] at hf; omega⟩
  have hk : DNB.getKey s y = some n := getKey_eq.mpr hn
  have hroute : route (segAt (segY cf s y)) (live n.ks) (Oy s r ops y) =
      (live n.ks).map (fun e => Oy s r ops e.2) := by
    rw [route_spec (segAt (segY cf s y)) (live n.ks) (Oy s r ops y) (live_sorted n.ks) (by
      intro e he op _
      have := shaped_head hsh hn hl
      rw [he] at this
      simp only [Option.map_some, Option.some.injEq] at this
      omega)]
    apply List.map_congr_left
    intro e he
    exact oy_inner_eq T hops hyr hn hl hg hsh he
  have hrs : (((live n.ks).zip (route (segAt (segY cf s y)) (live n.ks) (Oy s r ops y))).filter
      (fun e => !e.2.isEmpty)).map (fun e => sbPlan b s f' e.1.2 (segY cf s y) e.2 false) =
      (wch s r ops y).map (fun e => R0 b cf s r ops e.2) := by
    rw [hroute, zip_map_self, List.filter_map, List.map_map]
    simp only [wch, hn]
    have hfeq : (live n.ks).filter ((fun e : (Nat × NodeId) × List Op => !e.2.isEmpty) ∘
        (fun e => (e, Oy s r ops e.2))) = (live n.ks).filter (fun e => wkd s r ops e.2) := by
      apply List.filter_congr
      intro e _
      simp only [Function.comp_apply]
      by_cases h : wkd s r ops e.2 = true
      · have := oy_ne.mpr h
        rw [h]
        cases h' : Oy s r ops e.2 with
        | nil => exact absurd h' this
        | cons a l => rfl
      · have : Oy s r ops e.2 = [] := by
          by_contra hc; exact h (oy_ne.mp hc)
        rw [this]
        simpa using h
    rw [hfeq]
    apply List.map_congr_left
    intro e he
    obtain ⟨he1, he2⟩ := List.mem_filter.mp he
    simp only [Function.comp_apply]
    obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, e.2 ∈ pathOf s r op.key := by
      simpa [wkd] using he2
    obtain ⟨m, _, _, _, _, hm, _, _, hshm⟩ := walked_facts T (hops op hop) hpo
    have hseg : segY cf s e.2 = segY cf s y := segY_of_shaped (shaped_kid_inner hsh hn hl he1)
    have hir : iRoot cf s r e.2 = false := by
      have hu := (treeFn_child T hyr hn he1).1
      simp only [iRoot, TreeFn.upIn, hu]
      simp [treeFn, lfOf_key hn, hl]
    have := hIH e he1 he2 f' (fuel_kid hg hn he1 hm (by simpa using hf))
    rw [hseg, hir] at this
    exact this
  simp only [sbPlan, hk, hl, Bool.false_eq_true, ite_false]
  rw [hrs]

/-- The operations a segment leaf sends on to the next segment's root z named
by compare value cv: those with segment cv that go on, the operations of z. -/
theorem subs_eq {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = true) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    {cv : Nat} {z : NodeId} (hz : (live n.ks).lookup cv = some z) :
    ((Oy s r ops y).filter (fun op => segAt (segY cf s y) op == cv)).filter
      (fun op => !endsAt (segY cf s y) op) = Oy s r ops z := by
  have hcz : (cv, z) ∈ live n.ks := (lookup_iff_mem (live_sorted n.ks) _ _).mp hz
  rw [List.filter_filter, filter_oy, Oy]
  apply List.filter_congr
  intro op hop
  have hwf := hops op hop
  have := oy_leaf T hwf hyr hn hl hg hcz
  by_cases hy : y ∈ pathOf s r op.key
  · obtain ⟨L, hL⟩ := keyPath_of T hwf
    have hlt : segY cf s y < op.key.length := keyPath_seg_lt hwf hL _ (keyPath_seg hL hy)
    have e1 : (!endsAt (segY cf s y) op) = decide (segY cf s y + 1 < op.key.length) := by
      unfold endsAt
      by_cases h : segY cf s y + 1 < op.key.length
      · have : op.key.length ≠ segY cf s y + 1 := by omega
        simp [h, this]
      · have : op.key.length = segY cf s y + 1 := by omega
        simp [this]
    rw [e1]
    simp only [segAt, hy, decide_true, Bool.true_and]
    by_cases hz' : z ∈ pathOf s r op.key
    · obtain ⟨_, h2, h3⟩ := this.mp hz'
      simp [hz', h2, h3]
    · simp only [hz', decide_false]
      by_cases h2 : segY cf s y + 1 < op.key.length
      · by_cases h3 : op.key[segY cf s y]?.getD 0 = cv
        · exact absurd (this.mpr ⟨hy, h2, h3⟩) hz'
        · simp [h3]
      · simp [h2]
  · have hz' : z ∉ pathOf s r op.key := fun h => hy (this.mp h).1
    simp [hy, hz']

/-- What a segment leaf's group of compare value cv gives from the next
segment's root it names, if a path passes it. -/
def chf (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (lv : List (Nat × NodeId))
    (φ : SR → Nat) (cv : Nat) : Nat :=
  match lv.lookup cv with
  | some z => if wkd s r ops z then φ (R0 b cf s r ops z) else 0
  | none => 0

/-- **`sbPlan` at a walked segment leaf**: `sbNode` of its groups, each the
puts and deletes that end there, the next segment's root's counts, or a
new segment tree. -/
theorem sb_leaf (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = true) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hsh : Shaped cf s (segY cf s y) (htIn cf s y) y)
    (hIH : ∀ e ∈ live n.ks, wkd s r ops e.2 = true → ∀ f', s.fuel e.2 ≤ f' →
      sbPlan b s f' e.2 (segY cf s e.2) (Oy s r ops e.2) (iRoot cf s r e.2) = R0 b cf s r ops e.2)
    (iR : Bool) (f : Nat) (hf : s.fuel y ≤ f) :
    sbPlan b s f y (segY cf s y) (Oy s r ops y) iR =
      let g := segY cf s y
      let O := Oy s r ops y
      let lv := live n.ks
      let rs := (touched g O).map (fun cv =>
        let grp := O.filter (fun op => segAt g op == cv)
        let subP := (grp.filter (fun op => !endsAt g op)).filter (fun op => !opDel op)
        let eP := (grp.filter (fun op => endsAt g op && !opDel op)).length
        let eD := (grp.filter (fun op => endsAt g op && opDel op)).length
        let fr := (lv.lookup cv).isNone && !subP.isEmpty
        (eP + (chf b cf s r ops lv (·.up) cv + if fr then 1 else 0),
          8 * eD + (chf b cf s r ops lv (·.cnt) cv + if fr then ftbOf b (opKeys subP) (g + 1) else 0),
          eD + chf b cf s r ops lv (·.nd) cv))
      let nd := (rs.map (·.2.2)).sum
      sbNode b n iR (4 * nd + (rs.map (·.1)).sum) nd 0 (rs.map (·.2.1)).sum := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [Tree.fuel, hn] at hf; omega⟩
  have hk : DNB.getKey s y = some n := getKey_eq.mpr hn
  have hgrp : ∀ cv ∈ touched (segY cf s y) (Oy s r ops y),
      sbGroup b (segY cf s y) (live n.ks) ((Oy s r ops y).filter (fun op => segAt (segY cf s y) op == cv))
        (fun z subs => sbPlan b s f' z (segY cf s y + 1) subs true) cv =
      (let grp := (Oy s r ops y).filter (fun op => segAt (segY cf s y) op == cv)
       let subP := (grp.filter (fun op => !endsAt (segY cf s y) op)).filter (fun op => !opDel op)
       let eP := (grp.filter (fun op => endsAt (segY cf s y) op && !opDel op)).length
       let eD := (grp.filter (fun op => endsAt (segY cf s y) op && opDel op)).length
       let fr := ((live n.ks).lookup cv).isNone && !subP.isEmpty
       (eP + (chf b cf s r ops (live n.ks) (·.up) cv + if fr then 1 else 0),
         8 * eD + (chf b cf s r ops (live n.ks) (·.cnt) cv +
           if fr then ftbOf b (opKeys subP) (segY cf s y + 1) else 0),
         eD + chf b cf s r ops (live n.ks) (·.nd) cv)) := by
    intro cv _
    simp only [sbGroup]
    set grp := (Oy s r ops y).filter (fun op => segAt (segY cf s y) op == cv) with hgrp'
    set subs := grp.filter (fun op => !endsAt (segY cf s y) op) with hsubs
    cases hlk : (live n.ks).lookup cv with
    | none =>
      have hc : ∀ φ, chf b cf s r ops (live n.ks) φ cv = 0 := by intro φ; simp [chf, hlk]
      simp only [hc, Nat.zero_add, Option.isNone_none, Bool.true_and]
      by_cases hs : subs.isEmpty = true
      · have hsp : (subs.filter (fun op => !opDel op)).isEmpty = true := by
          rw [List.isEmpty_iff] at hs ⊢; rw [hs]; rfl
        simp [hs, hsp]
      · simp only [hs, Bool.false_eq_true, ite_false]
        by_cases hsp : (subs.filter (fun op => !opDel op)).isEmpty = true
        · simp [hsp]
        · simp [hsp]
    | some z =>
      have hsz : subs = Oy s r ops z := subs_eq T hops hyr hn hl hg hlk
      have hfr : ∀ x : Nat, (if ((some z : Option NodeId).isNone && !(subs.filter (fun op => !opDel op)).isEmpty)
          then x else 0) = 0 := by intro x; simp
      by_cases hs : subs.isEmpty = true
      · have hw : wkd s r ops z = false := by
          cases h : wkd s r ops z
          · rfl
          · exfalso
            have := oy_ne.mpr h
            rw [← hsz] at this
            exact this (List.isEmpty_iff.mp hs)
        simp [hs, chf, hlk, hw]
      · have hw : wkd s r ops z = true := by
          apply oy_ne.mp
          rw [← hsz]
          intro h; rw [h] at hs; exact hs rfl
        have hcz : (cv, z) ∈ live n.ks := (lookup_iff_mem (live_sorted n.ks) _ _).mp hlk
        obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, z ∈ pathOf s r op.key := by simpa [wkd] using hw
        obtain ⟨m, _, _, _, _, hm, _, _, _⟩ := walked_facts T (hops op hop) hpo
        have hlong : isLong cv = true := by
          by_contra hc
          obtain ⟨v, hv⟩ := good_val hg hn hl hcz (by simpa using hc)
          rw [hv] at hm; cases hm
        have hseg : segY cf s z = segY cf s y + 1 := segY_of_shaped (shaped_kid_leaf hsh hn hl hcz hlong)
        have hir : iRoot cf s r z = true := by
          have hu := (treeFn_child T hyr hn hcz).1
          simp only [iRoot, TreeFn.upIn, hu]
          simp [treeFn, lfOf_key hn, hl]
        have hsb : sbPlan b s f' z (segY cf s y + 1) subs true = R0 b cf s r ops z := by
          have := hIH (cv, z) hcz hw f' (fuel_kid hg hn hcz hm (by simpa using hf))
          rw [hseg, hir] at this
          rw [hsz]; exact this
        simp only [hs, Bool.false_eq_true, ite_false, hsb, chf, hlk, hw, ite_true, Option.isNone_some,
          Bool.false_and, Nat.add_zero]
  simp only [sbPlan, hk, hl, ite_true]
  rw [List.map_congr_left hgrp]

/-! ## Sums over a node's operations and children -/

theorem sum_filter_zero {α : Type} (l : List α) (p : α → Bool) (f : α → Nat)
    (h : ∀ a ∈ l, p a = false → f a = 0) : (l.map f).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    rw [List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, ih']
    · have : p a = false := by simpa using hp
      simp [this, ih', h a List.mem_cons_self this]

theorem len_filter_split {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter (fun a => p a && q a)).length + (l.filter (fun a => p a && !q a)).length =
      (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp <;> omega

theorem sum_filter_one {α : Type} (l : List α) (p : α → Bool) :
    (l.map (fun a => if p a then 1 else 0)).sum = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.filter_cons]; cases h : p a <;> simp [h, ih]; omega

theorem sum_perm_nodup {α : Type} {l₁ l₂ : List α} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hm : ∀ a, a ∈ l₁ ↔ a ∈ l₂) (f : α → Nat) : (l₁.map f).sum = (l₂.map f).sum :=
  List.Perm.sum_nat (((List.perm_ext_iff_of_nodup h1 h2).mpr hm).map f)

theorem live_cv_nodup (ks : List Klong) : ((live ks).map (·.1)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact (live_sorted ks).imp (fun h => Nat.ne_of_lt h)

theorem live_nodup' (ks : List Klong) : (live ks).Nodup :=
  (live_cv_nodup ks).of_map _

theorem live_lookup_of_mem {ks : List Klong} {e : Nat × NodeId} (he : e ∈ live ks) :
    (live ks).lookup e.1 = some e.2 :=
  (lookup_iff_mem (live_sorted ks) _ _).mpr he

/-- **The operations of an inner node among its walked children**: each goes
to one. -/
theorem part_inner {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = false) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (hsh : Shaped cf s (segY cf s y) (htIn cf s y) y) (P : Op → Bool) :
    ((wch s r ops y).map (fun e => ((Oy s r ops e.2).filter P).length)).sum =
      ((Oy s r ops y).filter P).length := by
  simp only [wch, hn]
  rw [← sum_filter_zero (live n.ks) (fun e => wkd s r ops e.2) _ (by
    intro e _ he
    have : Oy s r ops e.2 = [] := by by_contra hc; rw [oy_ne.mp hc] at he; cases he
    simp [this])]
  have hhead := shaped_head hsh hn hl
  set g := segY cf s y
  have hsome : ∀ op : Op, ∃ e, selE (live n.ks) (segAt g op) = some e := by
    intro op
    obtain ⟨e0, he0⟩ : ∃ e0, (live n.ks).head? = some e0 := by
      cases h : (live n.ks).head? with
      | none => rw [h] at hhead; cases hhead
      | some e0 => exact ⟨e0, rfl⟩
    have h0 : e0.1 = 0 := by rw [he0] at hhead; simpa using hhead
    unfold selE
    cases h : ((live n.ks).filter (fun e => decide (e.1 ≤ segAt g op))).getLast? with
    | some e => exact ⟨e, rfl⟩
    | none =>
      rw [List.getLast?_eq_none_iff] at h
      have : e0 ∈ (live n.ks).filter (fun e => decide (e.1 ≤ segAt g op)) := by
        simp [List.mem_of_head? he0, h0]
      rw [h] at this; cases this
  let hsel : Op → Nat × NodeId := fun op => (selE (live n.ks) (segAt g op)).getD (0, 0)
  have hsel_eq : ∀ op e, (selE (live n.ks) (segAt g op) = some e) ↔ hsel op = e := by
    intro op e
    obtain ⟨e', he'⟩ := hsome op
    show selE (live n.ks) (segAt g op) = some e ↔ (selE (live n.ks) (segAt g op)).getD (0, 0) = e
    rw [he']; simp
  have := sum_part (live n.ks) (live_nodup' n.ks) hsel P (Oy s r ops y) (by
    intro op _ _
    obtain ⟨e', he'⟩ := hsome op
    have : hsel op = e' := by
      show (selE (live n.ks) (segAt g op)).getD (0, 0) = e'
      rw [he']; rfl
    rw [this]; exact (selE_mem he').1)
  rw [← this]
  congr 1
  apply List.map_congr_left
  intro e he
  rw [← oy_inner_eq T hops hyr hn hl hg hsh he, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro op _
  have := hsel_eq op e
  by_cases hp : P op = true
  · simp only [hp, Bool.true_and]; exact decide_eq_decide.mpr this
  · simp [hp]

/-- **The operations of a segment leaf among its walked children**: each that
goes on and whose compare value the leaf has goes to one. -/
theorem part_leaf {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = true) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (P : Op → Bool) :
    ((wch s r ops y).map (fun e => ((Oy s r ops e.2).filter P).length)).sum =
      ((Oy s r ops y).filter (fun op => P op && !endsAt (segY cf s y) op &&
        ((live n.ks).lookup (segAt (segY cf s y) op)).isSome)).length := by
  simp only [wch, hn]
  rw [← sum_filter_zero (live n.ks) (fun e => wkd s r ops e.2) _ (by
    intro e _ he
    have : Oy s r ops e.2 = [] := by by_contra hc; rw [oy_ne.mp hc] at he; cases he
    simp [this])]
  have := sum_part ((live n.ks).map (·.1)) (live_cv_nodup n.ks) (segAt (segY cf s y))
    (fun op => P op && !endsAt (segY cf s y) op && ((live n.ks).lookup (segAt (segY cf s y) op)).isSome) (Oy s r ops y) (by
      intro op _ hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hp.2
      exact List.mem_map.mpr ⟨_, (lookup_iff_mem (live_sorted n.ks) _ _).mp hz, rfl⟩)
  rw [← this, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_apply]
  rw [← subs_eq T hops hyr hn hl hg (live_lookup_of_mem he), List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro op _
  by_cases h1 : segAt (segY cf s y) op = e.1
  · have h2 : ((live n.ks).lookup (segAt (segY cf s y) op)).isSome = true := by
      rw [h1, live_lookup_of_mem he]; rfl
    rw [h2]
    cases hP : P op <;> cases hE : endsAt (segY cf s y) op <;> simp [h1]
  · cases hP : P op <;> cases hE : endsAt (segY cf s y) op <;> simp [h1]

/-- **The children's sum over a segment leaf's groups** is the sum over its
walked children. -/
theorem sum_chf (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {uy : Option NodeId} {dy : Nat} (hyr : (y, uy, dy) ∈ RPD s r) {n : KNode}
    (hn : s.obj y = some (.key n)) (hl : n.leaf = true) {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi)
    (φ : SR → Nat) :
    ((touched (segY cf s y) (Oy s r ops y)).map (chf b cf s r ops (live n.ks) φ)).sum =
      ((wch s r ops y).map (fun e => φ (R0 b cf s r ops e.2))).sum := by
  set g := segY cf s y
  let Q : Nat → Bool := fun cv => match (live n.ks).lookup cv with
    | some z => wkd s r ops z
    | none => false
  rw [sum_filter_zero _ Q _ (by
    intro cv _ hq
    simp only [chf]
    split
    · rename_i z hz
      have : wkd s r ops z = false := by simpa [Q, hz] using hq
      simp [this]
    · rfl)]
  have hwch : wch s r ops y = (live n.ks).filter (fun e => wkd s r ops e.2) := by simp [wch, hn]
  have hnd1 : ((touched g (Oy s r ops y)).filter Q).Nodup := (nodup_touched _ _).filter _
  have hnd2 : ((wch s r ops y).map (·.1)).Nodup := by
    rw [hwch]
    exact (live_cv_nodup n.ks).sublist (List.filter_sublist.map _)
  rw [sum_perm_nodup hnd1 hnd2 (by
    intro cv
    rw [List.mem_filter, mem_touched, hwch, List.mem_map]
    constructor
    · rintro ⟨_, hq⟩
      simp only [Q] at hq
      split at hq
      · rename_i z hz
        exact ⟨(cv, z), List.mem_filter.mpr ⟨(lookup_iff_mem (live_sorted n.ks) _ _).mp hz, hq⟩, rfl⟩
      · cases hq
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he1, he2⟩ := List.mem_filter.mp he
      refine ⟨?_, by simp [Q, live_lookup_of_mem he1, he2]⟩
      obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, e.2 ∈ pathOf s r op.key := by simpa [wkd] using he2
      obtain ⟨hy, _, hc⟩ := (oy_leaf T (hops op hop) hyr hn hl hg he1).mp hpo
      exact ⟨op, List.mem_filter.mpr ⟨hop, by simpa using hy⟩, hc⟩)]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have he' := List.mem_filter.mp (hwch ▸ he)
  simp [chf, live_lookup_of_mem he'.1, he'.2]

/-- At a segment leaf y of segment g, for an operation that passes it: it
ends there `last` exactly if its key ends at g. -/
theorem endsAt_iff {r : NodeId} (T : TCtx cf s r) {op : Op} (hwf : keyWf op.key = true) {y : NodeId}
    (hy : y ∈ pathOf s r op.key) {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    ((endOf s r op.key).1 = y ∧ (endOf s r op.key).2.2 = .last) ↔ endsAt (segY cf s y) op = true := by
  obtain ⟨h1, h2⟩ := end_leaf T hwf hy hn hl
  unfold endsAt
  constructor
  · rintro ⟨he, hk⟩
    rw [(h2 he).2] at hk
    by_contra hc
    have : op.key.length ≠ segY cf s y + 1 := by simpa using hc
    simp [this] at hk
  · intro h
    have hlen : op.key.length = segY cf s y + 1 := by simpa using h
    have he := h1.mpr (Or.inl hlen)
    exact ⟨he, by rw [(h2 he).2]; simp [hlen]⟩

/-- At a segment leaf y of segment g, for an operation that passes it: it
ends there `fresh` exactly if it goes on and the leaf lacks its compare value. -/
theorem fresh_iff {r : NodeId} (T : TCtx cf s r) {op : Op} (hwf : keyWf op.key = true) {y : NodeId}
    (hy : y ∈ pathOf s r op.key) {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    ((endOf s r op.key).1 = y ∧ (endOf s r op.key).2.2 = .fresh) ↔
      (endsAt (segY cf s y) op = false ∧ (live n.ks).lookup (segAt (segY cf s y) op) = none) := by
  obtain ⟨h1, h2⟩ := end_leaf T hwf hy hn hl
  unfold endsAt segAt
  constructor
  · rintro ⟨he, hk⟩
    rw [(h2 he).2] at hk
    have hlen : op.key.length ≠ segY cf s y + 1 := by
      intro h; simp [h] at hk
    exact ⟨by simpa using hlen, (h1.mp he).resolve_left hlen⟩
  · rintro ⟨hne, hlk⟩
    have hlen : op.key.length ≠ segY cf s y + 1 := by simpa using hne
    have he := h1.mpr (Or.inr hlk)
    exact ⟨he, by rw [(h2 he).2]; simp [hlen]⟩

/-! ## Java's record of a node from the operations -/

/-- Java's record of y after the transaction's keys. -/
def recY (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : Walked :=
  recOf s r (treeFn cf s r) y (ops.map kdOf)

theorem pe_char {r : NodeId} (T : TCtx cf s r) {op : Op} (hwf : keyWf op.key = true) {y : NodeId}
    {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    peP s r y (kdOf op) = true ↔
      (y ∈ pathOf s r op.key ∧ opDel op = false ∧ endsAt (segY cf s y) op = true) := by
  unfold peP passK kdOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hy, hd⟩, hk⟩, he⟩
    exact ⟨hy, hd, (endsAt_iff T hwf hy hn hl).mp ⟨he, hk⟩⟩
  · rintro ⟨hy, hd, he⟩
    obtain ⟨h1, h2⟩ := (endsAt_iff T hwf hy hn hl).mpr he
    exact ⟨⟨⟨hy, hd⟩, h2⟩, h1⟩

theorem pf_char {r : NodeId} (T : TCtx cf s r) {op : Op} (hwf : keyWf op.key = true) {y : NodeId}
    {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    pfP s r y (kdOf op) = true ↔
      (y ∈ pathOf s r op.key ∧ opDel op = false ∧ endsAt (segY cf s y) op = false ∧
        (live n.ks).lookup (segAt (segY cf s y) op) = none) := by
  unfold pfP passK kdOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨hy, hd⟩, hk⟩, he⟩
    obtain ⟨h1, h2⟩ := (fresh_iff T hwf hy hn hl).mp ⟨he, hk⟩
    exact ⟨hy, hd, h1, h2⟩
  · rintro ⟨hy, hd, he, hlk⟩
    obtain ⟨h1, h2⟩ := (fresh_iff T hwf hy hn hl).mpr ⟨he, hlk⟩
    exact ⟨⟨⟨hy, hd⟩, h2⟩, h1⟩

theorem cvF_eq {r : NodeId} (T : TCtx cf s r) {op : Op} (hwf : keyWf op.key = true) {y : NodeId}
    (he : (endOf s r op.key).1 = y) : cvF s r (kdOf op) = segAt (segY cf s y) op := by
  simp only [cvF, kdOf, segAt]
  rw [end_seg T hwf, he]

/-- The group of compare value cv of a segment leaf's operations has a new
segment tree (`sbGroup`'s third case). -/
def frG (s : Tree) (r : NodeId) (ops : List Op) (g : Nat) (lv : List (Nat × NodeId)) (y : NodeId)
    (cv : Nat) : Bool :=
  (lv.lookup cv).isNone && !((((Oy s r ops y).filter (fun op => segAt g op == cv)).filter
    (fun op => !endsAt g op)).filter (fun op => !opDel op)).isEmpty

theorem frG_mem {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) (cv : Nat) :
    (cv ∈ touched (segY cf s y) (Oy s r ops y) ∧ frG s r ops (segY cf s y) (live n.ks) y cv = true) ↔
      ∃ k ∈ ops.map kdOf, pfP s r y k = true ∧ cvF s r k = cv := by
  constructor
  · rintro ⟨_, hfr⟩
    simp only [frG, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
      List.isEmpty_eq_false_iff_exists_mem] at hfr
    obtain ⟨hlk, op, hop⟩ := hfr
    simp only [List.mem_filter, Oy, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hop
    obtain ⟨⟨⟨⟨hop, hy⟩, hc⟩, he⟩, hd⟩ := hop
    have hwf := hops op hop
    refine ⟨kdOf op, List.mem_map_of_mem hop, (pf_char T hwf hn hl).mpr ⟨hy, hd, he, by rw [hc]; exact hlk⟩, ?_⟩
    have hpf := (pf_char T hwf hn hl).mpr ⟨hy, hd, he, by rw [hc]; exact hlk⟩
    have hend : (endOf s r op.key).1 = y := by
      unfold pfP at hpf; simp [passK, kdOf] at hpf; exact hpf.2
    rw [cvF_eq T hwf hend, hc]
  · rintro ⟨k, hk, hpf, hcv⟩
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hk
    have hwf := hops op hop
    obtain ⟨hy, hd, he, hlk⟩ := (pf_char T hwf hn hl).mp hpf
    have hend : (endOf s r op.key).1 = y := by
      unfold pfP at hpf; simp [passK, kdOf] at hpf; exact hpf.2
    rw [cvF_eq T hwf hend] at hcv
    subst hcv
    refine ⟨mem_touched.mpr ⟨op, List.mem_filter.mpr ⟨hop, by simpa using hy⟩, rfl⟩, ?_⟩
    simp only [frG, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
      List.isEmpty_eq_false_iff_exists_mem]
    refine ⟨hlk, op, ?_⟩
    simp [Oy, hop, hy, he, hd]

/-- **The new segment trees' klongs**: one for each group with a new tree. -/
theorem fresh_len {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    ((touched (segY cf s y) (Oy s r ops y)).map
      (fun cv => if frG s r ops (segY cf s y) (live n.ks) y cv then 1 else 0)).sum =
      (recY cf s r ops y).fresh.length := by
  rw [sum_filter_one]
  have hri := recOf_RI s r (treeFn cf s r) y n (getKey_eq.mpr hn) (ops.map kdOf)
  obtain ⟨hnd, hmem, _, _⟩ := hri.fresh
  rw [show (recY cf s r ops y).fresh.length = ((recY cf s r ops y).fresh.map
    (fun q : Nat × List Key => q.1)).length from (List.length_map _).symm]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup ((nodup_touched _ _).filter _) hnd).mpr
  intro cv
  rw [List.mem_filter, frG_mem T hops hn hl cv]
  exact (hmem cv).symm

/-- **The new segment trees' count**: `freshTreeBound` of each group with a
new tree. -/
theorem fresh_sum (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = true) :
    ((touched (segY cf s y) (Oy s r ops y)).map (fun cv =>
      if frG s r ops (segY cf s y) (live n.ks) y cv then
        ftbOf b (opKeys ((((Oy s r ops y).filter (fun op => segAt (segY cf s y) op == cv)).filter
          (fun op => !endsAt (segY cf s y) op)).filter (fun op => !opDel op))) (segY cf s y + 1)
      else 0)).sum = freshSum b (recY cf s r ops y) := by
  have hri := recOf_RI s r (treeFn cf s r) y n (getKey_eq.mpr hn) (ops.map kdOf)
  obtain ⟨hnd, hmem, hq, hfl⟩ := hri.fresh
  unfold recY
  set w := recOf s r (treeFn cf s r) y (ops.map kdOf) with hw
  set g := segY cf s y
  let Tf : Nat → Nat := fun cv => ftbOf b (opKeys ((((Oy s r ops y).filter (fun op => segAt g op == cv)).filter
    (fun op => !endsAt g op)).filter (fun op => !opDel op))) (g + 1)
  rw [sum_filter_zero _ (frG s r ops g (live n.ks) y) _ (by intro cv _ h; simp [h])]
  have hmap : ((touched g (Oy s r ops y)).filter (frG s r ops g (live n.ks) y)).map
      (fun cv => if frG s r ops g (live n.ks) y cv then Tf cv else 0) =
      ((touched g (Oy s r ops y)).filter (frG s r ops g (live n.ks) y)).map Tf := by
    apply List.map_congr_left
    intro cv hcv
    simp [(List.mem_filter.mp hcv).2]
  rw [hmap]
  rw [sum_perm_nodup ((nodup_touched _ _).filter _) hnd (by
    intro cv
    rw [List.mem_filter, frG_mem T hops hn hl cv]
    exact (hmem cv).symm) Tf]
  unfold freshSum
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hqm
  simp only [Function.comp_apply]
  -- the fresh level is the leaf's segment
  have hlev : w.freshLevel = g := by
    obtain ⟨k, hk, hpf, hfl'⟩ := hfl (List.ne_nil_of_mem hqm)
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hk
    have hend : (endOf s r op.key).1 = y := by
      unfold pfP at hpf; simp [passK, kdOf] at hpf; exact hpf.2
    rw [hfl']
    simp only [kdOf]
    rw [end_seg T (hops op hop), hend]
  -- the keys of the group
  have hq1 : ∃ k ∈ ops.map kdOf, pfP s r y k = true ∧ cvF s r k = q.1 :=
    (hmem q.1).mp (List.mem_map_of_mem hqm)
  have hlk : (live n.ks).lookup q.1 = none := by
    obtain ⟨k, hk, hpf, hcv⟩ := hq1
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hy, hd, he, hl'⟩ := (pf_char T (hops op hop) hn hl).mp hpf
    have hend : (endOf s r op.key).1 = y := by
      unfold pfP at hpf; simp [passK, kdOf] at hpf; exact hpf.2
    rw [cvF_eq T (hops op hop) hend] at hcv
    rw [← hcv]; exact hl'
  have hkeys : q.2 = opKeys ((((Oy s r ops y).filter (fun op => segAt g op == q.1)).filter
      (fun op => !endsAt g op)).filter (fun op => !opDel op)) := by
    rw [hq q hqm]
    simp only [opKeys, List.filter_map, List.map_map, List.filter_filter, filter_oy]
    have hfun : ((fun x : Key × Bool => x.1) ∘ kdOf) = Op.key := by funext op; rfl
    rw [hfun]
    congr 1
    apply List.filter_congr
    intro op hop
    have hwf := hops op hop
    simp only [Function.comp_apply]
    by_cases hpf : pfP s r y (kdOf op) = true
    · obtain ⟨hy, hd, he, hl'⟩ := (pf_char T hwf hn hl).mp hpf
      have hend : (endOf s r op.key).1 = y := by
        unfold pfP at hpf; simp [passK, kdOf] at hpf; exact hpf.2
      rw [cvF_eq T hwf hend]
      have he' : endsAt g op = false := he
      simp [hpf, hy, hd, he']
      exact Iff.rfl
    · simp only [hpf, Bool.and_false]
      symm
      apply Bool.eq_false_iff.mpr
      intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hc
      apply hpf
      refine (pf_char T hwf hn hl).mpr ⟨?_, ?_, ?_, ?_⟩
      · tauto
      · tauto
      · tauto
      · have hc1 : segAt g op = q.1 := by tauto
        show (live n.ks).lookup (segAt g op) = none
        rw [hc1]; exact hlk
  rw [hlev, hkeys]
  rfl

/-! ## The count node by node -/

/-- What y with K klongs gives its parent's klongs (Java's `countNode`). -/
def contribY (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) (K : Nat) : Nat :=
  let w := recY cf s r ops y
  if ovOf b w K = 0 then 0 else if (treeFn cf s r).upIn y then partsOf b w K else ovOf b w K + 1

/-- What Java's fold counts for y with K klongs. -/
def termY (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) (K : Nat) : Nat :=
  let w := recY cf s r ops y
  freshSum b w + (if ovOf b w K = 0 then 0 else partsOf b w K +
    (if (treeFn cf s r).upIn y then 0 else max (ovOf b w K) (rootsAbove b (partsOf b w K))))

/-- The deletes that end at segment leaf y. -/
def endDel (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : Nat :=
  if lfOf s y then ((Oy s r ops y).filter (fun op => endsAt (segY cf s y) op && opDel op)).length else 0

theorem sbNode_vals (b : Nat) (n : KNode) (iR : Bool) (K nd ci below : Nat) (w : Walked)
    (hsz : w.size = n.ks.length) (hdd : w.dead = deadCount n.ks) (hdb : w.deleteBelow = decide (0 < nd)) :
    (sbNode b n iR K nd ci below).K = K ∧ (sbNode b n iR K nd ci below).nd = nd ∧
    (sbNode b n iR K nd ci below).ci = ci ∧
    (sbNode b n iR K nd ci below).cnt = 1 + 4 * nd + below + (if ovOf b w K = 0 then 0 else
      partsOf b w K + (if iR then max (ovOf b w K) (rootsAbove b (partsOf b w K)) else 0)) ∧
    (sbNode b n iR K nd ci below).up = (if iR = true ∧ 0 < nd then ci else 0) +
      (if ovOf b w K = 0 then 0 else if iR then ovOf b w K + 1 else partsOf b w K) := by
  have hov : overflowsD b K n.ks.length (decide (0 < nd)) (some (deadCount n.ks)) = ovOf b w K := by
    simp [ovOf, hsz, hdd, hdb]
  have hpt : ∀ v, max (v + 1) (cutPartsBound b (n.ks.length + K)) = max (v + 1) (cutPartsBound b (w.size + K)) := by
    intro v; rw [hsz]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp only [sbNode, hov]
    by_cases h0 : ovOf b w K = 0
    · simp [h0]
    · simp only [h0, ite_false, partsOf, hpt]
      cases iR
      · simp only [Bool.false_eq_true, false_and, ite_false]; omega
      · simp only [ne_eq, h0, not_false_eq_true, and_self, ite_true]; omega
  · simp only [sbNode, hov]
    by_cases h0 : ovOf b w K = 0
    · simp [h0]
    · simp only [h0, ite_false, partsOf, hpt]

theorem foldl_max_const : ∀ (l : List Nat) (v a : Nat), (∀ x ∈ l, x = v) → a ≤ v → l ≠ [] →
    l.foldl max a = v
  | [], _, _, _, _, h => absurd rfl h
  | [x], v, a, hx, ha, _ => by simp [hx x (by simp)]; omega
  | x :: y :: l, v, a, hx, ha, _ => by
    rw [List.foldl_cons]
    apply foldl_max_const (y :: l) v (max a x) (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      (by have := hx x List.mem_cons_self; omega) (by simp)

/-- What the proof of `sbPlan` at y gives. -/
structure SBP (b : Nat) (cf : Cfg) (s : Tree) (r : NodeId) (ops : List Op) (y : NodeId) : Prop where
  fuel : ∀ f, s.fuel y ≤ f →
    sbPlan b s f y (segY cf s y) (Oy s r ops y) (iRoot cf s r y) = R0 b cf s r ops y
  nd : (R0 b cf s r ops y).nd = ((Oy s r ops y).filter (dlo s r)).length
  ci : (R0 b cf s r ops y).ci = (if (R0 b cf s r ops y).nd = 0 then 0 else (treeFn cf s r).col y)
  K : (R0 b cf s r ops y).K = (recY cf s r ops y).klongs +
    ((wch s r ops y).map (fun e => (recY cf s r ops e.2).collapses +
      contribY b cf s r ops e.2 (R0 b cf s r ops e.2).K)).sum
  cnt : (R0 b cf s r ops y).cnt = 1 + 4 * (R0 b cf s r ops y).nd + 8 * endDel cf s r ops y +
    termY b cf s r ops y (R0 b cf s r ops y).K + ((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).cnt)).sum
  up : (treeFn cf s r).up y ≠ none →
    (R0 b cf s r ops y).up = (recY cf s r ops y).collapses + contribY b cf s r ops y (R0 b cf s r ops y).K

theorem any_eq_len {α : Type} (l : List α) (p : α → Bool) : l.any p = decide (0 < (l.filter p).length) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.any_cons, List.filter_cons, ih]; cases p a <;> simp

/-- No walk ends at an inner node: neither a put's klong nor a new segment
tree there. -/
theorem inner_noend {r : NodeId} (T : TCtx cf s r) {ops : List Op} (hops : ∀ op ∈ ops, keyWf op.key = true)
    {y : NodeId} {n : KNode} (hn : s.obj y = some (.key n)) (hl : n.leaf = false) :
    ∀ k ∈ ops.map kdOf, peP s r y k = false ∧ pfP s r y k = false := by
  intro k hk
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hk
  constructor
  · by_contra h
    simp only [Bool.not_eq_false] at h
    unfold peP at h
    simp only [passK, kdOf, Bool.and_eq_true, beq_iff_eq] at h
    exact end_inner T (hops op hop) (of_decide_eq_true h.1.1.1) hn hl h.2
  · by_contra h
    simp only [Bool.not_eq_false] at h
    unfold pfP at h
    simp only [passK, kdOf, Bool.and_eq_true, beq_iff_eq] at h
    exact end_inner T (hops op hop) (of_decide_eq_true h.1.1.1) hn hl h.2

/-- The groups of a segment leaf's operations by compare value: each
operation in one. -/
theorem grp_sum (g : Nat) (O : List Op) (q : Op → Bool) :
    ((touched g O).map (fun cv => ((O.filter (fun op => segAt g op == cv)).filter q).length)).sum =
      (O.filter q).length := by
  rw [← sum_part (touched g O) (nodup_touched g O) (segAt g) q O (by
    intro op hop _
    exact mem_touched.mpr ⟨op, hop, rfl⟩)]
  congr 1
  apply List.map_congr_left
  intro cv _
  rw [List.filter_filter]
  congr 1

/-- **`sbPlan` node by node** (`SBP`): at every walked node, by induction on
its level. -/
theorem sb_main (b : Nat) {r : NodeId} (T : TCtx cf s r) {ops : List Op}
    (hops : ∀ op ∈ ops, keyWf op.key = true) :
    ∀ (L : Nat) (y : NodeId) (n : KNode), s.obj y = some (.key n) → n.level ≤ L →
      wkd s r ops y = true → SBP b cf s r ops y := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro y n hn hL hw
  obtain ⟨op0, hop0, hp0⟩ : ∃ op ∈ ops, y ∈ pathOf s r op.key := by simpa [wkd] using hw
  obtain ⟨n', uy, dy, lo, hi, hn', hyr, hg, hsh⟩ := walked_facts T (hops op0 hop0) hp0
  rw [hn] at hn'
  obtain rfl : n = n' := by injection hn' with h1; injection h1
  have hch : ∀ e ∈ live n.ks, wkd s r ops e.2 = true → SBP b cf s r ops e.2 := by
    intro e he hwe
    obtain ⟨op, hop, hpo⟩ : ∃ op ∈ ops, e.2 ∈ pathOf s r op.key := by simpa [wkd] using hwe
    obtain ⟨m, _, _, _, _, hm, _, _, _⟩ := walked_facts T (hops op hop) hpo
    have hlt : m.level < n.level := by
      rcases good_kids hg hn e.1 e.2 he with ⟨m', hm', hlt, _⟩ | ⟨v, hv⟩
      · rw [hm] at hm'
        obtain rfl : m = m' := by injection hm' with h1; injection h1
        exact hlt
      · rw [hm] at hv; cases hv
    exact ih m.level (by omega) e.2 m hm (le_refl _) hwe
  have hIHf : ∀ e ∈ live n.ks, wkd s r ops e.2 = true → ∀ f', s.fuel e.2 ≤ f' →
      sbPlan b s f' e.2 (segY cf s e.2) (Oy s r ops e.2) (iRoot cf s r e.2) = R0 b cf s r ops e.2 :=
    fun e he hwe => (hch e he hwe).fuel
  have hwch : wch s r ops y = (live n.ks).filter (fun e => wkd s r ops e.2) := by simp [wch, hn]
  have hwchm : ∀ e ∈ wch s r ops y, e ∈ live n.ks ∧ wkd s r ops e.2 = true := by
    intro e he; rw [hwch] at he; exact List.mem_filter.mp he
  have hupc : ∀ e ∈ wch s r ops y, (treeFn cf s r).up e.2 ≠ none := by
    intro e he
    rw [(treeFn_child T hyr hn (hwchm e he).1).1]; simp
  have hri := recOf_RI s r (treeFn cf s r) y n (getKey_eq.mpr hn) (ops.map kdOf)
  have hdl : ((ops.map kdOf).filter (dlP s r y)).length = ((Oy s r ops y).filter (dlo s r)).length :=
    len_dlP s r ops y
  have hdb : (recY cf s r ops y).deleteBelow = decide (0 < ((Oy s r ops y).filter (dlo s r)).length) := by
    show (recOf s r (treeFn cf s r) y (ops.map kdOf)).deleteBelow = _
    rw [hri.del, any_eq_len, hdl]
  have hcol : (recY cf s r ops y).collapses =
      (if decide (0 < ((Oy s r ops y).filter (dlo s r)).length) && (treeFn cf s r).pleaf y then
        (treeFn cf s r).col y else 0) := by
    show (recOf s r (treeFn cf s r) y (ops.map kdOf)).collapses = _
    rw [hri.col, any_eq_len, hdl]
  -- the root flag: a segment tree's root exactly when its parent is a segment leaf
  have hiR : ∀ u, (treeFn cf s r).up y = some u → iRoot cf s r y = (treeFn cf s r).pleaf y := by
    intro u hu
    simp only [iRoot, TreeFn.upIn, TreeFn.pleaf, hu, Bool.not_not]
  -- the children's parts of the klongs
  have hupsum : ((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).up)).sum =
      ((wch s r ops y).map (fun e => (recY cf s r ops e.2).collapses +
        contribY b cf s r ops e.2 (R0 b cf s r ops e.2).K)).sum := by
    congr 1
    apply List.map_congr_left
    intro e he
    exact (hch e (hwchm e he).1 (hwchm e he).2).up (hupc e he)
  have hfuel_eq : ∀ (E : Nat → SR), (∀ f, s.fuel y ≤ f →
      sbPlan b s f y (segY cf s y) (Oy s r ops y) (iRoot cf s r y) = E f) →
      (∀ f, E f = E (s.fuel y)) →
      ∀ f, s.fuel y ≤ f → sbPlan b s f y (segY cf s y) (Oy s r ops y) (iRoot cf s r y) =
        R0 b cf s r ops y := by
    intro E hE hc f hf
    rw [hE f hf, hc f, ← hE _ (le_refl _)]
    rfl
  -- the root flag and the parent
  have hupIn : (treeFn cf s r).upIn y = !iRoot cf s r y := by simp [iRoot]
  cases hl : n.leaf with
  | false =>
    set rs := (wch s r ops y).map (fun e => R0 b cf s r ops e.2) with hrs
    have hnd : (rs.map (·.nd)).sum = ((Oy s r ops y).filter (dlo s r)).length := by
      rw [hrs, List.map_map, ← part_inner T hops hyr hn hl hg hsh (dlo s r)]
      congr 1; apply List.map_congr_left; intro e he
      exact (hch e (hwchm e he).1 (hwchm e he).2).nd
    have hunf := fun f hf => sb_inner b T hops hyr hn hl hg hsh hIHf (iRoot cf s r y) f hf
    simp only [← hrs] at hunf
    set nd := (rs.map (·.nd)).sum with hndd
    set ci := (if nd = 0 then 0 else 1 + ((rs.filter (fun r => 0 < r.nd)).map (·.ci)).foldl max 0)
      with hci
    have hR0 : R0 b cf s r ops y = sbNode b n (iRoot cf s r y) (4 * nd + (rs.map (·.up)).sum) nd ci
        (rs.map (·.cnt)).sum := hunf _ (le_refl _)
    obtain ⟨vK, vnd, vci, vcnt, vup⟩ := sbNode_vals b n (iRoot cf s r y) (4 * nd + (rs.map (·.up)).sum)
      nd ci (rs.map (·.cnt)).sum (recY cf s r ops y) hri.size hri.dead (by rw [hdb, hnd])
    -- no walk ends at y
    have hne := inner_noend T hops hn hl
    have hfr : (recY cf s r ops y).fresh = [] := by
      by_contra hc
      obtain ⟨k, hk, hpf, _⟩ := hri.fresh.2.2.2 hc
      rw [(hne k hk).2] at hpf; cases hpf
    have hpe : ((ops.map kdOf).filter (peP s r y)).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro k hk; simp [(hne k hk).1]
    have hkl : (recY cf s r ops y).klongs = 4 * nd := by
      show (recOf s r (treeFn cf s r) y (ops.map kdOf)).klongs = _
      rw [hri.klongs, hpe, hdl, ← hnd]
      have : (recOf s r (treeFn cf s r) y (ops.map kdOf)).fresh = [] := hfr
      rw [this]; simp
    -- the collapses below: the height of y
    have hciv : ci = (if nd = 0 then 0 else (treeFn cf s r).col y) := by
      rw [hci]
      by_cases h0 : nd = 0
      · simp [h0]
      · simp only [h0, ite_false]
        -- every child with a delete has y's height less one
        obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ live n.ks := by
          obtain ⟨x, hx⟩ : ∃ x, x ∈ rs := by
            cases h : rs with
            | nil => rw [hndd, h] at h0; simp at h0
            | cons x _ => exact ⟨x, List.mem_cons_self⟩
          rw [hrs] at hx
          obtain ⟨e, he, _⟩ := List.mem_map.mp hx
          exact ⟨e, (hwchm e he).1⟩
        have hcy : (treeFn cf s r).col y = htIn cf s y := by simp [treeFn, lfOf_key hn, hl]
        have hval : ∀ x ∈ (rs.filter (fun r => 0 < r.nd)).map (·.ci), x = htIn cf s y - 1 := by
          intro x hx
          obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hR1, hR2⟩ := List.mem_filter.mp hR
          rw [hrs] at hR1
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hR1
          obtain ⟨he1, he2⟩ := hwchm e he
          have hsb := hch e he1 he2
          have hnd0 : (R0 b cf s r ops e.2).nd ≠ 0 := Nat.pos_iff_ne_zero.mp (by simpa using hR2)
          rw [hsb.ci]
          simp only [hnd0, ite_false]
          have hht := shaped_kid_ht hsh hn hl he1
          have hshe := shaped_kid_inner hsh hn hl he1
          obtain ⟨m, hm, _, hml, _, _⟩ := shaped_obj hshe
          simp only [treeFn, lfOf_key hm]
          by_cases hlm : m.leaf = true
          · have : htIn cf s e.2 = 0 := by
              rw [hlm] at hml
              have := hml.symm
              simpa using this
            simp [hlm]; omega
          · simp [hlm]; omega
        have hnem : (rs.filter (fun r => 0 < r.nd)).map (·.ci) ≠ [] := by
          intro hnil
          apply h0
          rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hnil
          rw [hndd]
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hx
          have := hnil R hR
          simpa using this
        rw [foldl_max_const _ (htIn cf s y - 1) 0 hval (Nat.zero_le _) hnem, hcy]
        have := shaped_kid_ht hsh hn hl (c := e0.1) (z := e0.2) he0
        omega
    have hfresh0 : freshSum b (recY cf s r ops y) = 0 := by simp [freshSum, hfr]
    have hend0 : endDel cf s r ops y = 0 := by simp [endDel, lfOf_key hn, hl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      rw [hunf f hf]
      exact hR0.symm
    · rw [hR0, vnd, hnd]
    · rw [hR0, vci, vnd, hciv]
    · rw [hR0, vK, hkl, hrs, List.map_map, ← hupsum]
      rfl
    · have htm : ∀ K, termY b cf s r ops y K = (if ovOf b (recY cf s r ops y) K = 0 then 0 else
          partsOf b (recY cf s r ops y) K + (if iRoot cf s r y then
            max (ovOf b (recY cf s r ops y) K) (rootsAbove b (partsOf b (recY cf s r ops y) K)) else 0)) := by
        intro K
        simp only [termY, hfresh0, hupIn, Nat.zero_add]
        cases iRoot cf s r y <;> simp
      have hcs : (rs.map (·.cnt)).sum = ((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).cnt)).sum := by
        rw [hrs, List.map_map]; rfl
      rw [hR0, vcnt, vnd, vK, hend0, htm, hcs]
      ring
    · intro hne'
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne'
      rw [hR0, vup, vK, hciv, hcol, hiR u hu]
      simp only [contribY, hupIn, hiR u hu, ← hnd]
      by_cases h0 : nd = 0
      · cases (treeFn cf s r).pleaf y <;> simp [h0]
      · have : 0 < nd := Nat.pos_of_ne_zero h0
        cases (treeFn cf s r).pleaf y <;> simp [h0, this]
  | true =>
    set g := segY cf s y with hgdef
    set O := Oy s r ops y with hO
    let F : Nat → Nat × Nat × Nat := fun cv =>
      (((O.filter (fun op => segAt g op == cv)).filter (fun op => endsAt g op && !opDel op)).length +
        (chf b cf s r ops (live n.ks) (·.up) cv + if frG s r ops g (live n.ks) y cv then 1 else 0),
       8 * ((O.filter (fun op => segAt g op == cv)).filter (fun op => endsAt g op && opDel op)).length +
        (chf b cf s r ops (live n.ks) (·.cnt) cv + if frG s r ops g (live n.ks) y cv then
          ftbOf b (opKeys (((O.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op)).filter
            (fun op => !opDel op))) (g + 1) else 0),
       ((O.filter (fun op => segAt g op == cv)).filter (fun op => endsAt g op && opDel op)).length +
        chf b cf s r ops (live n.ks) (·.nd) cv)
    have hunf : ∀ f, s.fuel y ≤ f → sbPlan b s f y g O (iRoot cf s r y) =
        sbNode b n (iRoot cf s r y) (4 * (((touched g O).map F).map (·.2.2)).sum +
          (((touched g O).map F).map (·.1)).sum) (((touched g O).map F).map (·.2.2)).sum 0
          (((touched g O).map F).map (·.2.1)).sum :=
      fun f hf => sb_leaf b T hops hyr hn hl hg hsh hIHf (iRoot cf s r y) f hf
    have hR0 := hunf _ (le_refl _)
    change R0 b cf s r ops y = _ at hR0
    -- the sums
    have hSeD : (((touched g O).map F).map (·.2.2)).sum =
        (O.filter (fun op => endsAt g op && opDel op)).length +
        ((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).nd)).sum := by
      rw [List.map_map]
      simp only [Function.comp_def, F]
      rw [List.sum_map_add, grp_sum, sum_chf b T hops hyr hn hl hg]
    have hS1 : (((touched g O).map F).map (·.1)).sum =
        (O.filter (fun op => endsAt g op && !opDel op)).length +
        (((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).up)).sum + (recY cf s r ops y).fresh.length) := by
      rw [List.map_map]
      simp only [Function.comp_def, F]
      rw [List.sum_map_add, List.sum_map_add, grp_sum, sum_chf b T hops hyr hn hl hg, fresh_len T hops hn hl]
    have hS21 : (((touched g O).map F).map (·.2.1)).sum =
        8 * (O.filter (fun op => endsAt g op && opDel op)).length +
        (((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).cnt)).sum + freshSum b (recY cf s r ops y)) := by
      rw [List.map_map]
      simp only [Function.comp_def, F]
      rw [List.sum_map_add, List.sum_map_add, List.sum_map_mul_left, grp_sum,
        sum_chf b T hops hyr hn hl hg, fresh_sum b T hops hn hl]
    -- the operations of y, one by one
    have hOm : ∀ op ∈ O, op ∈ ops ∧ y ∈ pathOf s r op.key := by
      intro op hop
      simp only [hO, Oy, List.mem_filter, decide_eq_true_eq] at hop
      exact hop
    have hdlo_end : (O.filter (fun op => endsAt g op && opDel op)).length =
        (O.filter (fun op => dlo s r op && endsAt g op)).length := by
      congr 1
      apply List.filter_congr
      intro op hop
      obtain ⟨hop1, hy⟩ := hOm op hop
      cases he : endsAt g op
      · simp
      · obtain ⟨_, hk⟩ := (endsAt_iff T (hops op hop1) hy hn hl).mpr he
        simp [dlo, kindOp, hk]
    have hdlo_cont : (O.filter (fun op => dlo s r op && !endsAt g op &&
        ((live n.ks).lookup (segAt g op)).isSome)).length =
        (O.filter (fun op => dlo s r op && !endsAt g op)).length := by
      congr 1
      apply List.filter_congr
      intro op hop
      obtain ⟨hop1, hy⟩ := hOm op hop
      cases hd : dlo s r op
      · simp
      · cases he : endsAt g op
        · simp only [Bool.not_false, Bool.true_and, Bool.and_true]
          cases hlk : (live n.ks).lookup (segAt g op) with
          | some z => rfl
          | none =>
            exfalso
            obtain ⟨_, hk⟩ := (fresh_iff T (hops op hop1) hy hn hl).mpr ⟨he, hlk⟩
            simp [dlo, kindOp, hk] at hd
        · simp
    have hnd : (((touched g O).map F).map (·.2.2)).sum = (O.filter (dlo s r)).length := by
      rw [hSeD]
      have : ((wch s r ops y).map (fun e => (R0 b cf s r ops e.2).nd)).sum =
          ((wch s r ops y).map (fun e => ((Oy s r ops e.2).filter (dlo s r)).length)).sum := by
        congr 1; apply List.map_congr_left; intro e he
        exact (hch e (hwchm e he).1 (hwchm e he).2).nd
      rw [this, part_leaf T hops hyr hn hl hg (dlo s r), ← hO, hdlo_cont, hdlo_end]
      exact len_filter_split O (dlo s r) (endsAt g)
    set nd := (((touched g O).map F).map (·.2.2)).sum with hndd
    obtain ⟨vK, vnd, vci, vcnt, vup⟩ := sbNode_vals b n (iRoot cf s r y)
      (4 * nd + (((touched g O).map F).map (·.1)).sum) nd 0 (((touched g O).map F).map (·.2.1)).sum
      (recY cf s r ops y) hri.size hri.dead (by rw [hdb, hnd])
    have hpe : ((ops.map kdOf).filter (peP s r y)).length =
        (O.filter (fun op => endsAt g op && !opDel op)).length := by
      rw [len_filter_kd, hO, filter_oy]
      congr 1
      apply List.filter_congr
      intro op hop
      have := pe_char T (hops op hop) hn hl (y := y)
      by_cases hy : y ∈ pathOf s r op.key
      · cases hd : opDel op <;> cases he : endsAt g op <;> simp_all
      · have : peP s r y (kdOf op) = false := by simp [peP, passK, kdOf, hy]
        simp [this, hy]
    have hkl : (recY cf s r ops y).klongs = (O.filter (fun op => endsAt g op && !opDel op)).length +
        4 * nd + (recY cf s r ops y).fresh.length := by
      show (recOf s r (treeFn cf s r) y (ops.map kdOf)).klongs = _
      rw [hri.klongs, hpe, hdl, hnd]
      rfl
    have hcol0 : (treeFn cf s r).col y = 0 := by simp [treeFn, lfOf_key hn, hl]
    have hend : endDel cf s r ops y = (O.filter (fun op => endsAt g op && opDel op)).length := by
      simp [endDel, lfOf_key hn, hl, hO, hgdef]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      rw [hunf f hf]
      exact hR0.symm
    · rw [hR0, vnd, hnd]
    · rw [hR0, vci, vnd, hcol0]; simp
    · rw [hR0, vK, hS1, hkl, ← hupsum]
      ring
    · have htm : ∀ K, termY b cf s r ops y K = freshSum b (recY cf s r ops y) +
          (if ovOf b (recY cf s r ops y) K = 0 then 0 else
          partsOf b (recY cf s r ops y) K + (if iRoot cf s r y then
            max (ovOf b (recY cf s r ops y) K) (rootsAbove b (partsOf b (recY cf s r ops y) K)) else 0)) := by
        intro K
        simp only [termY, hupIn]
        cases iRoot cf s r y <;> simp
      rw [hR0, vcnt, vnd, vK, hend, htm, hS21]
      ring
    · intro hne'
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne'
      rw [hR0, vup, vK, hcol, hiR u hu, hcol0]
      simp only [contribY, hupIn, hiR u hu]
      cases (treeFn cf s r).pleaf y <;> simp

end Contract.PE
