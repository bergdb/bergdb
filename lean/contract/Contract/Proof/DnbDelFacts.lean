/-
bergdb 030-36: facts for the delete case of the proof that Java's dirty-node
bound bounds PE.

Package A, the parameters and PE's decisions:

* `java_params`: at Java's parameters (`Cfg.java b G H`) from node size 8,
  2 ≤ m ≤ c, M ≤ 2c, 1 ≤ cap ≤ c, h = c, and merges are on.
* `nParts_pos`, `nParts_add_le`, `nParts_two`: a list cut into parts of at
  most c entries has one part at least; a times more entries, a ≤ c, give
  one part more at most; at most 2c entries give two parts at most.
* `decide_facts`: PE's decision for a node of the tree before with base n
  and final list F (`decideNode`): a cut gives one part or more; a change
  writes one node or more; the parts of F cut by c are at most the nodes
  written and two, and at most the new entries its parent gets
  (`noneCount`) and two; a list of fewer than m entries gives its parent one
  entry; the parent gets at most one entry that is not new.
* `joined_facts`: a joined list's node (no base) is k = `nParts c |F|`
  new nodes, the parent's k entries all new.

Package B, rebalance's exit:

* `joinAt_length`: a join makes the list one shorter.
* `joinLoop_exit`, `rebalance_exit`: with merges on, rebalance ends with
  fewer than two children or none changed and small (`findSmall` none).
* `findSmall_none`: then every changed child has m entries or more.
-/
import Contract.Proof.DnbKids

namespace Contract.PE

open DNB

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## A. The parameters and PE's decisions -/

/-- The entries a parent gets for its child (c, w) that are new (no pointer). -/
def noneCount (c : Nat) (w : VN) : Nat := ((ents c w).filter (fun e => e.2.isNone)).length

/-- **Java's parameters** from node size 8. -/
theorem java_params {b G H : Nat} (hb : 8 ≤ b) :
    2 ≤ (Cfg.java b G H).m ∧ (Cfg.java b G H).m ≤ (Cfg.java b G H).c ∧
    (Cfg.java b G H).M ≤ 2 * (Cfg.java b G H).c ∧ (Cfg.java b G H).cap ≤ (Cfg.java b G H).c ∧
    (Cfg.java b G H).h = (Cfg.java b G H).c ∧ 1 ≤ (Cfg.java b G H).cap ∧
    (Cfg.java b G H).merges = true := by
  have h8 : ¬ b < 8 := by omega
  simp only [Cfg.java, Cfg.merges, DNB.minFill, DNB.mergeCap, DNB.cutSize, DNB.splitAbove, h8,
    ite_false]
  refine ⟨le_max_left _ _, ?_, ?_, ?_, trivial, ?_, ?_⟩
  · rw [Nat.max_le]; constructor <;> omega
  · omega
  · omega
  · omega
  · simp

theorem nParts_of_pos {c : Nat} (hc : 1 ≤ c) (n : Nat) :
    nParts c n = if n ≤ c then 1 else (n + c - 1) / c := by
  unfold nParts
  rw [Nat.max_eq_left hc]

theorem nParts_pos (c n : Nat) : 1 ≤ nParts c n := by
  unfold nParts
  simp only
  generalize hcap : max c 1 = cap
  have h1 : 1 ≤ cap := by rw [← hcap]; exact le_max_right _ _
  split
  · exact le_refl 1
  · rename_i h
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

theorem nParts_add_le {c a n : Nat} (hc : 1 ≤ c) (ha : a ≤ c) : nParts c (a + n) ≤ nParts c n + 1 := by
  rw [nParts_of_pos hc, nParts_of_pos hc]
  split
  · omega
  · rename_i h1
    split
    · rename_i h2
      have : (a + n + c - 1) / c < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    · rename_i h2
      have e : (n + c - 1) / c + 1 = (n + c - 1 + c) / c := (Nat.add_div_right _ (by omega)).symm
      rw [e]
      exact Nat.div_le_div_right (by omega)

theorem nParts_two {c n : Nat} (hc : 1 ≤ c) (h : n ≤ 2 * c) : nParts c n ≤ 2 := by
  rw [nParts_of_pos hc]
  split
  · omega
  · have : (n + c - 1) / c < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega

/-- Smaller parts, more of them: the parts by c are at most the parts by cap
for cap ≤ c. -/
theorem nParts_cap_anti {c cap n : Nat} (h1 : 1 ≤ cap) (hle : cap ≤ c) : nParts c n ≤ nParts cap n := by
  rw [nParts_of_pos (le_trans h1 hle), nParts_of_pos h1]
  split
  · exact nParts_of_pos h1 n ▸ nParts_pos cap n
  · rename_i hn
    have hn' : ¬ n ≤ cap := by omega
    simp only [hn', ite_false]
    generalize hk : (n + cap - 1) / cap = k
    have hlt : n + cap - 1 < cap * (k + 1) := by
      rw [← hk]; exact Nat.lt_mul_div_succ _ (by omega)
    have hmul : cap * k ≤ c * k := Nat.mul_le_mul_right _ hle
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have e1 : cap * (k + 1) = cap * k + cap := by ring
    have e2 : (k + 1) * c = c * k + c := by ring
    rw [e1] at hlt
    rw [e2]
    omega

/-- PE's cut of a list that does not fit its base: at least its parts by c,
at Java's parameters. -/
theorem nParts_c_le_cutParts {b G H : Nat} (hb : 8 ≤ b) (n : Nat) :
    nParts (Cfg.java b G H).c n ≤ cutParts (Cfg.java b G H) n := by
  obtain ⟨_, _, _, hcap, hh, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  unfold cutParts
  split
  · rename_i h
    have h' : n ≤ (Cfg.java b G H).c := by rw [← hh]; exact h
    simp [nParts_of_pos hc1, h']
  · exact le_trans (nParts_cap_anti hcap1 hcap) (le_max_right _ _)

theorem cutParts_one_le (cf : Cfg) (n : Nat) : 1 ≤ cutParts cf n := by
  unfold cutParts
  split
  · exact le_refl 1
  · exact le_trans (by omega) (le_max_left _ _)

/-- A virtual node of k ≥ 1 parts gives its parent k entries, all new. -/
theorem ents_parts_none {c : Nat} {bs : Option NodeId} {g h : Nat} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {k : Nat} (hk : 1 ≤ k) :
    (ents c (.node bs g h j es F (.parts k))).length = k ∧
      noneCount c (.node bs g h j es F (.parts k)) = k := by
  by_cases h2 : 2 ≤ k
  · have hl := ents_parts_length (c := c) (b := bs) (g := g) (h := h) (j := j) (es := es) (F := F) h2
    refine ⟨hl, ?_⟩
    unfold noneCount
    rw [List.filter_eq_self.mpr, hl]
    intro e he
    simp only [ents, h2, ite_true] at he
    simp [partEnts_none c F k j e he]
  · have hk1 : k = 1 := by omega
    subst hk1
    simp [noneCount, ents]

/-- A virtual node with a base that it keeps (`same` or `append`) gives its
parent one entry, its base. -/
theorem ents_keep_base {c : Nat} {y : NodeId} {g h : Nat} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} (hd : dec = .same ∨ dec = .append) :
    (ents c (.node (some y) g h j es F dec)).length = 1 ∧ noneCount c (.node (some y) g h j es F dec) = 0 := by
  rcases hd with rfl | rfl <;> simp [noneCount, ents]

/-- The four cases of PE's decision for a node with a base. -/
theorem decideNode_java_cases {b G H : Nat} {i : Time} {n : KNode} {F : List (Nat × Option NodeId)}
    (hks : n.ks.length ≤ b)
    (hlen : F.length ≤ (live n.ks).length + (F.filter (isAdded (live n.ks))).length) :
    (decideNode (Cfg.java b G H) i (some n) false F = .same ∧ F.length ≤ b) ∨
    (decideNode (Cfg.java b G H) i (some n) false F = .append ∧ F.length + 1 ≤ b) ∨
    (decideNode (Cfg.java b G H) i (some n) false F = .parts 1 ∧ F.length + 1 ≤ b) ∨
    decideNode (Cfg.java b G H) i (some n) false F = .parts (cutParts (Cfg.java b G H) F.length) := by
  have hlv := live_length_le n.ks
  unfold decideNode
  simp only
  split
  · rename_i heq
    left
    refine ⟨rfl, ?_⟩
    have := beq_iff_eq.mp heq
    rw [← this, List.length_map]
    omega
  · split
    · rename_i hfit
      have hM : (Cfg.java b G H).M = b := rfl
      have hak := appendKsO_length i n.ks F
      have hF : F.length + 1 ≤ b := by
        have : 1 + (F.filter (isAdded (live n.ks))).length ≤ (appendKsO i n.ks F).length := by
          rw [hak]; split <;> omega
        omega
      split
      · split
        · right; right; left; exact ⟨rfl, hF⟩
        · right; right; right; rfl
      · right; left; exact ⟨rfl, hF⟩
    · right; right; right; rfl

/-- The facts of a decision in one of `decideNode_java_cases`' four cases. -/
theorem decide_facts_of {b G H g h : Nat} (hb : 8 ≤ b) {y : NodeId} {c : Nat}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} (dec : Dec)
    (hcase : (dec = .same ∧ F.length ≤ b) ∨ (dec = .append ∧ F.length + 1 ≤ b) ∨
      (dec = .parts 1 ∧ F.length + 1 ≤ b) ∨ dec = .parts (cutParts (Cfg.java b G H) F.length)) :
    (∀ k, dec = .parts k → 1 ≤ k) ∧ (dec ≠ .same → 1 ≤ dcost dec) ∧
    nParts (Cfg.java b G H).c F.length ≤ dcost dec + 2 ∧
    nParts (Cfg.java b G H).c F.length ≤ noneCount c (VN.node (some y) g h false es F dec) + 2 ∧
    (F.length < (Cfg.java b G H).m → (ents c (VN.node (some y) g h false es F dec)).length = 1) ∧
    (ents c (VN.node (some y) g h false es F dec)).length ≤
      1 + noneCount c (VN.node (some y) g h false es F dec) := by
  obtain ⟨_, hmc, hM2, hcap, hh, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  have hMb : (Cfg.java b G H).M = b := rfl
  have hsmall : F.length ≤ b → nParts (Cfg.java b G H).c F.length ≤ 2 :=
    fun h => nParts_two hc1 (by omega)
  rcases hcase with ⟨rfl, hF⟩ | ⟨rfl, hF⟩ | ⟨rfl, hF⟩ | rfl
  · have hk := ents_keep_base (c := c) (y := y) (g := g) (h := h) (j := false) (es := es) (F := F)
      (dec := .same) (Or.inl rfl)
    refine ⟨fun k hk' => (by cases hk'), fun h => absurd rfl h, ?_, ?_, fun _ => hk.1, ?_⟩
    · simp only [dcost]; have := hsmall hF; omega
    · rw [hk.2]; have := hsmall hF; omega
    · rw [hk.1, hk.2]
  · have hk := ents_keep_base (c := c) (y := y) (g := g) (h := h) (j := false) (es := es) (F := F)
      (dec := .append) (Or.inr rfl)
    refine ⟨fun k hk' => (by cases hk'), fun _ => le_refl _, ?_, ?_, fun _ => hk.1, ?_⟩
    · simp only [dcost]; have := hsmall (by omega); omega
    · rw [hk.2]; have := hsmall (by omega); omega
    · rw [hk.1, hk.2]
  · have hk := ents_parts_none (c := c) (bs := some y) (g := g) (h := h) (j := false) (es := es)
      (F := F) (k := 1) (le_refl _)
    refine ⟨fun k hk' => (by cases hk'; exact le_refl _), fun _ => le_refl _, ?_, ?_, fun _ => hk.1, ?_⟩
    · simp only [dcost]; have := hsmall (by omega); omega
    · rw [hk.2]; have := hsmall (by omega); omega
    · rw [hk.1, hk.2]; omega
  · have hpos := cutParts_one_le (Cfg.java b G H) F.length
    have hk := ents_parts_none (c := c) (bs := some y) (g := g) (h := h) (j := false) (es := es)
      (F := F) hpos
    have hle := nParts_c_le_cutParts (G := G) (H := H) hb F.length
    refine ⟨fun k hk' => (by cases hk'; exact hpos), fun _ => hpos, ?_, ?_, ?_, ?_⟩
    · simp only [dcost]; omega
    · rw [hk.2]; omega
    · intro hlt
      rw [hk.1]
      unfold cutParts
      have h' : F.length ≤ (Cfg.java b G H).h := by rw [hh]; omega
      simp [h']
    · rw [hk.1, hk.2]; omega

/-- **PE's decision for a node of the tree before** (base n, final list F),
at Java's parameters from node size 8. -/
theorem decide_facts {b G H g h : Nat} (hb : 8 ≤ b) {i : Time} {n : KNode} {y : NodeId} {c : Nat}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} (hks : n.ks.length ≤ b)
    (hlen : F.length ≤ (live n.ks).length + (F.filter (isAdded (live n.ks))).length) :
    let dec := decideNode (Cfg.java b G H) i (some n) false F
    let w := VN.node (some y) g h false es F dec
    (∀ k, dec = .parts k → 1 ≤ k) ∧ (dec ≠ .same → 1 ≤ dcost dec) ∧
    nParts (Cfg.java b G H).c F.length ≤ dcost dec + 2 ∧
    nParts (Cfg.java b G H).c F.length ≤ noneCount c w + 2 ∧
    (F.length < (Cfg.java b G H).m → (ents c w).length = 1) ∧
    (ents c w).length ≤ 1 + noneCount c w :=
  decide_facts_of hb _ (decideNode_java_cases hks hlen)

/-- **A joined list's node**: k = `nParts c |F|` new nodes, the parent's k
entries all new. -/
theorem joined_facts {b G H g h c : Nat} {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} :
    let k := nParts (Cfg.java b G H).c F.length
    let w := VN.node none g h true es F (.parts k)
    1 ≤ k ∧ dcost (.parts k) = k ∧ noneCount c w = k ∧ (ents c w).length = k := by
  intro k w
  have hk : 1 ≤ k := nParts_pos _ _
  have := ents_parts_none (c := c) (bs := none) (g := g) (h := h) (j := true) (es := es) (F := F) hk
  exact ⟨hk, rfl, this.2, this.1⟩

/-! ## B. Rebalance's exit -/

theorem joinAtIl_length {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} {il : Nat} (hj : joinAtIl cf i s g h down es il = some es') :
    es'.length + 1 = es.length := by
  unfold joinAtIl at hj
  split at hj
  · rename_i l r hl hr
    have hlt : il + 1 < es.length := (List.getElem?_eq_some_iff.mp hr).1
    split at hj
    · dsimp only at hj
      split at hj
      · split at hj
        · cases hj
          simp only [List.length_append, List.length_take, List.length_cons, List.length_nil,
            List.length_drop]
          omega
        · cases hj
      · cases hj
    · cases hj
  · cases hj

/-- **A join makes the list one shorter.** -/
theorem joinAt_length {cf : Cfg} {i : Time} {s : Tree} {g h : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} {es es' : List (Nat × VN)} {ix : Nat}
    (hj : joinAt cf i s g h down es ix = some es') : es'.length + 1 = es.length := by
  rw [joinAt_eq] at hj
  exact joinAtIl_length hj

/-- **The loop of joins ends** with fewer than two children, or none changed
and small, given fuel for one join each child. -/
theorem joinLoop_exit {cf : Cfg} {i : Time} {s : Tree} {g h : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} :
    ∀ (n : Nat) (es es' : List (Nat × VN)), es.length ≤ n →
      joinLoop cf i s g h down n es = some es' → es'.length < 2 ∨ findSmall cf es' = none
  | 0, es, es', hn, hj => by
    simp only [joinLoop, Option.some.injEq] at hj
    subst hj
    left; omega
  | n + 1, es, es', hn, hj => by
    unfold joinLoop at hj
    split at hj
    · rename_i h2
      cases hj
      exact Or.inl h2
    · cases hf : findSmall cf es with
      | none =>
        rw [hf] at hj
        cases hj
        exact Or.inr hf
      | some ix =>
        rw [hf] at hj
        simp only at hj
        split at hj
        · rename_i es'' hjo
          have := joinAt_length hjo
          exact joinLoop_exit n es'' es' (by omega) hj
        · cases hj

/-- **Rebalance's exit**: with merges on, rebalance ends with fewer than two
children, or no changed child with fewer than m entries. -/
theorem rebalance_exit {cf : Cfg} {i : Time} {s : Tree} {f g h : Nat} {es es2 : List (Nat × VN)}
    (hr : rebalance cf i s f g h es = some es2) (hm : cf.merges = true) :
    es2.length < 2 ∨ findSmall cf es2 = none := by
  cases f with
  | zero => simp [rebalance] at hr
  | succ f =>
    simp only [rebalance, hm, Bool.not_true, Bool.false_eq_true, ite_false] at hr
    exact joinLoop_exit _ _ _ (Nat.le_succ _) hr

/-- **No small changed child**: then every changed child has m entries or
more. -/
theorem findSmall_none {cf : Cfg} {es : List (Nat × VN)} (h : findSmall cf es = none) :
    ∀ e ∈ es, e.2.changed = true → cf.m ≤ e.2.size := by
  intro e he hc
  unfold findSmall at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  obtain ⟨j, hj⟩ := List.getElem_of_mem he
  have hz : (e, j) ∈ es.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getElem?_eq_getElem hj.1, hj.2]
  have := h _ hz
  simp only [hc, Bool.true_and, decide_eq_true_eq] at this
  omega

end Contract.PE
