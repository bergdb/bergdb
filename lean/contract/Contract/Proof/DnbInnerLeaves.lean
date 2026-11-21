/-
bergdb 030-37: the leaf estimates needed when two inner nodes are joined.
The number of parent entries grows by at most one in a leaf join. Two
already rebalanced lists of leaves require at most one further leaf join.
-/
import Contract.Proof.DnbLeafRebalance

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem entries_append (A B : List (Nat × VN)) : entries (A ++ B) = entries A ++ entries B :=
  List.flatMap_append

theorem nParts_mono {c a n : Nat} (hc : 1 ≤ c) (ha : a ≤ n) :
    nParts c a ≤ nParts c n := by
  have hn := nParts_pos c n
  rw [nParts_of_pos hc] at hn
  rw [nParts_of_pos hc, nParts_of_pos hc]
  split
  · exact hn
  · split
    · omega
    · exact Nat.div_le_div_right (by omega)

/-- A leaf's parts by the join capacity exceed its current parent entries
by at most one. This includes an untouched neighbour. -/
theorem JoinLeaf.parts_le_ents {b G H : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : JoinLeaf b G H i s v) (c : Nat) :
    nParts (Cfg.java b G H).c (cntOf s v) ≤ (ents c v).length + 1 := by
  obtain ⟨_, _, hM, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  change b ≤ 2 * (Cfg.java b G H).c at hM
  cases hv with
  | @old y n hk hks _ =>
    have hl := live_length_le n.ks
    have hn := nParts_two hc (n := (live n.ks).length) (by omega)
    simpa [cntOf, hk, ents] using hn
  | @planned y g n es hks _ hlen _ =>
    change nParts (Cfg.java b G H).c (entries es).length ≤
      (ents c (.node (some y) g 0 false es (entries es)
        (decideNode (Cfg.java b G H) i (some n) false (entries es)))).length + 1
    change (entries es).length ≤ (live n.ks).length +
      ((entries es).filter (isAdded (live n.ks))).length at hlen
    rcases decideNode_java_cases (G := G) (H := H) (i := i) hks hlen with
      ⟨hd, hn⟩ | ⟨hd, hn⟩ | ⟨hd, hn⟩ | hd
    · have h2 := nParts_two hc (n := (entries es).length) (by omega)
      simpa only [cntOf, VN.size, hd, ents, List.length_singleton] using h2
    · have h2 := nParts_two hc (n := (entries es).length) (by omega)
      simpa only [cntOf, VN.size, hd, ents, List.length_singleton] using h2
    · have h2 := nParts_two hc (n := (entries es).length) (by omega)
      simpa only [cntOf, VN.size, hd, ents, Nat.not_ofNat_le_one, ↓reduceIte,
        List.length_singleton] using h2
    · have hle := nParts_c_le_cutParts (G := G) (H := H) hb (entries es).length
      have he := (ents_parts_none (c := c) (bs := some y) (g := g) (h := 0)
        (j := false) (es := es) (F := entries es)
        (cutParts_one_le (Cfg.java b G H) (entries es).length)).1
      rw [hd, he]
      omega
  | @joined g es _ =>
    change nParts (Cfg.java b G H).c (entries es).length ≤
      (ents c (.node none g 0 true es (entries es)
        (.parts (nParts (Cfg.java b G H).c (entries es).length)))).length + 1
    have he := (joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := c)
      (es := es) (F := entries es)).2.2.2
    rw [he]
    omega

theorem JoinLeaf.small_ents {b G H : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : JoinLeaf b G H i s v) (c : Nat)
    (hs : smallLeaf (Cfg.java b G H) v = true) : (ents c v).length = 1 := by
  have hn := hv.small.mp hs
  cases hv with
  | old hk _ hf => simp [cntOf, hk] at hn; omega
  | @planned y g n es hks _ hlen _ =>
    exact (decide_facts (G := G) (H := H) (i := i) (g := g) (h := 0) (y := y)
      (c := c) (es := es) hb hks hlen).2.2.2.2.1 hn
  | @joined g es _ =>
    change (ents c (.node none g 0 true es (entries es)
      (.parts (nParts (Cfg.java b G H).c (entries es).length)))).length = 1
    obtain ⟨_, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
    have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
    have he := (joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := c)
      (es := es) (F := entries es)).2.2.2
    rw [he, nParts_of_pos hc, ite_eq_left (by change (entries es).length < _ at hn; omega)]

theorem leaf_join_entries_growth {b G H : Nat} (hb : 8 ≤ b) {g cL cR : Nat}
    {l r v : VN} {L R : List (Nat × VN)}
    (hl : JoinLeaf b G H i s l) (hr : JoinLeaf b G H i s r)
    (hoL : openEs s l = some L) (hoR : openEs s r = some R)
    (hs : smallLeaf (Cfg.java b G H) l = true ∨ smallLeaf (Cfg.java b G H) r = true)
    (hm : mkNode (Cfg.java b G H) i s none g 0 true (L ++ R) = some v) :
    (ents cL v).length ≤ (ents cL l).length + (ents cR r).length + 1 := by
  obtain ⟨L', hL, _, hnL⟩ := hl.open
  obtain ⟨R', hR, _, hnR⟩ := hr.open
  rw [hoL] at hL; cases hL
  rw [hoR] at hR; cases hR
  have hlen : (entries (L ++ R)).length = cntOf s l + cntOf s r := by
    simp only [entries, List.flatMap_append, List.length_append, hnL, hnR]
  unfold mkNode at hm
  simp only [beq_self_eq_true, ↓reduceIte] at hm
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    simp only [decideNode, ↓reduceIte]
    change (ents cL (.node none g 0 true (L ++ R) (entries (L ++ R))
      (.parts (nParts (Cfg.java b G H).c (entries (L ++ R)).length)))).length ≤ _
    rw [(joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := cL)
      (es := L ++ R) (F := entries (L ++ R))).2.2.2, hlen]
    obtain ⟨_, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
    have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
    rcases hs with hs | hs
    · have hsm := hl.small.mp hs
      have he := hl.small_ents hb cL hs
      have hparts := hr.parts_le_ents hb cR
      have hsum := nParts_add_le hc (n := cntOf s r) (a := cntOf s l) (by omega)
      omega
    · have hsm := hr.small.mp hs
      have he := hr.small_ents hb cR hs
      have hparts := hl.parts_le_ents hb cL
      have hsum := nParts_add_le hc (n := cntOf s l) (a := cntOf s r) (by omega)
      rw [Nat.add_comm (cntOf s r)] at hsum
      omega

theorem JoinLeaf.cnt_pos {b G H : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : JoinLeaf b G H i s v) (hne : v.isEmpty = false) : 0 < cntOf s v := by
  cases hv with
  | old hk _ hf =>
    have hm := (java_params (G := G) (H := H) hb).1
    simp only [cntOf, hk]
    omega
  | planned => simpa only [VN.isEmpty, List.isEmpty_eq_false_iff, List.length_pos_iff_ne_nil,
      cntOf, VN.size] using hne
  | joined => simpa only [VN.isEmpty, List.isEmpty_eq_false_iff, List.length_pos_iff_ne_nil,
      cntOf, VN.size] using hne

theorem joinAt_leaf_extra {b G H : Nat} (hb : 8 ≤ b) {g ix : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} {es es' : List (Nat × VN)}
    (hsmall : findSmall (Cfg.java b G H) es = some ix)
    (hes : ∀ e ∈ es, JoinLeaf b G H i s e.2)
    (hne : ∀ e ∈ es, e.2.isEmpty = false)
    (hj : joinAt (Cfg.java b G H) i s g 0 down es ix = some es') :
    (entries es').length ≤ (entries es).length + 1 ∧
      (∀ e ∈ es', e.2.isEmpty = false) := by
  obtain ⟨x, hx, hxs⟩ := findSmall_get hsmall
  have hil : (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) = ix ∨
      (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) + 1 = ix := by
    by_cases h0 : ix = 0
    · subst h0; simp [useLeftOf, hx]
    · split <;> omega
  rw [joinAt_eq] at hj
  generalize hi : (if useLeftOf (Cfg.java b G H) s es ix then ix - 1 else ix) = il at hj hil
  unfold joinAtIl at hj
  split at hj
  · rename_i l r hl hr
    have hls := hes l (List.mem_of_getElem? hl)
    have hrs := hes r (List.mem_of_getElem? hr)
    have hs : smallLeaf (Cfg.java b G H) l.2 = true ∨ smallLeaf (Cfg.java b G H) r.2 = true := by
      rcases hil with rfl | hh
      · rw [hx] at hl; cases hl; exact Or.inl hxs
      · rw [hh, hx] at hr; cases hr; exact Or.inr hxs
    split at hj
    · rename_i L R hoL hoR
      simp only [beq_self_eq_true, ↓reduceIte] at hj
      cases hm : mkNode (Cfg.java b G H) i s none g 0 true (L ++ R) with
      | none => rw [hm] at hj; cases hj
      | some v =>
        rw [hm] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        have hg := leaf_join_entries_growth hb hls hrs hoL hoR hs hm (cL := l.1) (cR := r.1)
        have hvne : v.isEmpty = false := by
          obtain ⟨L', hL, _, hnL⟩ := hls.open
          rw [hoL] at hL; cases hL
          have hpos := hls.cnt_pos hb (hne l (List.mem_of_getElem? hl))
          have hlen : 0 < (entries (L ++ R)).length := by
            simp only [entries, List.flatMap_append, List.length_append]
            omega
          unfold mkNode at hm
          simp only [beq_self_eq_true, ↓reduceIte] at hm
          split at hm
          · cases hm
          · cases hm
            simpa only [entries, VN.isEmpty, List.isEmpty_eq_false_iff,
              List.length_pos_iff_ne_nil] using hlen
        constructor
        · conv_rhs => rw [split_at2 hl hr]
          simp only [entries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.length_append]
          omega
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with (he | rfl) | he
          · exact hne e (List.mem_of_mem_take he)
          · exact hvne
          · exact hne e (List.mem_of_mem_drop he)
    · cases hj
  · cases hj

theorem joinLoop_leaf_extra {b G H : Nat} (hb : 8 ≤ b) {g : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} :
    ∀ (n : Nat) (es es' : List (Nat × VN)),
      (∀ e ∈ es, JoinLeaf b G H i s e.2) → (∀ e ∈ es, e.2.isEmpty = false) →
      joinLoop (Cfg.java b G H) i s g 0 down n es = some es' →
      (entries es').length + es'.length ≤ (entries es).length + es.length ∧
      (es'.length = es.length → es' = es) ∧ (∀ e ∈ es', e.2.isEmpty = false)
  | 0, es, es', hes, hne, hj => by
    simp only [joinLoop, Option.some.injEq] at hj
    subst hj
    exact ⟨le_refl _, fun _ => rfl, hne⟩
  | n + 1, es, es', hes, hne, hj => by
    rw [joinLoop] at hj
    split at hj
    · cases hj; exact ⟨le_refl _, fun _ => rfl, hne⟩
    · cases hs : findSmall (Cfg.java b G H) es with
      | none => rw [hs] at hj; cases hj; exact ⟨le_refl _, fun _ => rfl, hne⟩
      | some ix =>
        rw [hs] at hj
        simp only at hj
        cases hstep : joinAt (Cfg.java b G H) i s g 0 down es ix with
        | none => rw [hstep] at hj; cases hj
        | some es1 =>
          rw [hstep] at hj
          obtain ⟨h1, _, _, h4, _, _, _, _⟩ := joinAt_leaf_account hb hs hes hstep
          obtain ⟨hlen, hne1⟩ := joinAt_leaf_extra hb hs hes hne hstep
          obtain ⟨k1, _, _, _, klen, _, _, _, _⟩ := joinLoop_leaf_account hb n es1 es' h1 hj
          obtain ⟨ih, heq, hne'⟩ := joinLoop_leaf_extra hb n es1 es' h1 hne1 hj
          exact ⟨by omega, fun he => by omega, hne'⟩

def LeafReady (b G H : Nat) (i : Time) (s : Tree) (es : List (Nat × VN)) : Prop :=
  (∀ e ∈ es, JoinLeaf b G H i s e.2) ∧ (∀ e ∈ es, e.2.isEmpty = false) ∧
    (es.length < 2 ∨ findSmall (Cfg.java b G H) es = none)

theorem leafReady_small {b G H : Nat} (hb : 8 ≤ b) {es : List (Nat × VN)}
    (hr : LeafReady b G H i s es) :
    smallLeaves (Cfg.java b G H) es ≤ 1 ∧
      (0 < smallLeaves (Cfg.java b G H) es → es.length = 1 ∧ (entries es).length = 1) := by
  rcases hr.2.2 with hlen | hfind
  · have hle := List.length_filter_le (p := fun e : Nat × VN => smallLeaf (Cfg.java b G H) e.2) (l := es)
    change smallLeaves (Cfg.java b G H) es ≤ es.length at hle
    refine ⟨by omega, fun hp => ?_⟩
    have h1 : es.length = 1 := by omega
    obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp h1
    have hs : smallLeaf (Cfg.java b G H) e.2 = true := by
      simpa [smallLeaves] using hp
    have he := (hr.1 e List.mem_cons_self).small_ents hb e.1 hs
    exact ⟨rfl, by simpa [entries] using he⟩
  · have hzero : smallLeaves (Cfg.java b G H) es = 0 := by
      unfold smallLeaves
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro e he hs
      have hsmall := findSmall_none hfind e he
      simp only [smallLeaf, Bool.and_eq_true, decide_eq_true_eq] at hs
      have := hsmall hs.1
      omega
    exact ⟨by omega, fun hp => by omega⟩

theorem leafReady_rename {b G H : Nat} {es : List (Nat × VN)}
    (hr : LeafReady b G H i s es) (c : Nat) : LeafReady b G H i s (renameHead c es) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', heq⟩ := renameHead_mem he
    rw [← heq]; exact hr.1 e' he'
  · intro e he
    obtain ⟨e', he', heq⟩ := renameHead_mem he
    rw [← heq]; exact hr.2.1 e' he'
  · rcases hr.2.2 with hh | hh
    · left; rw [renameHead_length]; exact hh
    · right
      cases es with
      | nil => exact hh
      | cons e es =>
        unfold findSmall at hh ⊢
        simp only [renameHead, List.zipIdx_cons, List.find?_cons] at hh ⊢
        cases hp : e.2.changed && decide (e.2.size < (Cfg.java b G H).m) <;> simp_all
        exact hh

theorem smallLeaves_rename (cf : Cfg) (c : Nat) (es : List (Nat × VN)) :
    smallLeaves cf (renameHead c es) = smallLeaves cf es := by
  cases es with
  | nil => rfl
  | cons e es => simp only [renameHead, smallLeaves_cons]

/-- Joining two inner nodes exposes two lists that have already finished
their own leaf rebalances. Their union needs at most one further leaf join.
No restriction on the leaf sizes, split counts or neighbour choices is used. -/
theorem rebalance_leaf_pair {b G H : Nat} (hb : 8 ≤ b) {f g : Nat}
    {A B es2 : List (Nat × VN)}
    (hA : LeafReady b G H i s A) (hB : LeafReady b G H i s B)
    (hr : rebalance (Cfg.java b G H) i s f g 0 (A ++ B) = some es2) :
    ∃ j, j ≤ 1 ∧ LeafReady b G H i s es2 ∧
      vcostL es2 ≤ vcostL A + vcostL B + 2 * j ∧
      (entries es2).length ≤ (entries A).length + (entries B).length + j ∧
      smallLeaves (Cfg.java b G H) es2 + j ≤
        smallLeaves (Cfg.java b G H) A + smallLeaves (Cfg.java b G H) B ∧
      (j = 0 → es2 = A ++ B) := by
  have hm := (java_params (G := G) (H := H) hb).2.2.2.2.2.2
  cases f with
  | zero => simp [rebalance] at hr
  | succ f =>
    have hAB : ∀ e ∈ A ++ B, JoinLeaf b G H i s e.2 := by
      intro e he
      exact (List.mem_append.mp he).elim (hA.1 e) (hB.1 e)
    have hne : ∀ e ∈ A ++ B, e.2.isEmpty = false := by
      intro e he
      exact (List.mem_append.mp he).elim (hA.2.1 e) (hB.2.1 e)
    have hkeep : kept (A ++ B) = A ++ B := filter_head hne
    have hr' := hr
    change (if !(Cfg.java b G H).merges then some (kept (A ++ B)) else
      joinLoop (Cfg.java b G H) i s g 0 (fun J => rebalance (Cfg.java b G H) i s f g (0 - 1) J)
        ((kept (A ++ B)).length + 1) (kept (A ++ B))) = some es2 at hr'
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hkeep] at hr'
    obtain ⟨j, hv, hc, _, hlen, hs, _, hhead, _⟩ := joinLoop_leaf_account hb _ _ _ hAB hr'
    obtain ⟨hgrow, heq, hne2⟩ := joinLoop_leaf_extra hb _ _ _ hAB hne hr'
    have hAs := leafReady_small hb hA
    have hBs := leafReady_small hb hB
    rw [smallLeaves_append] at hs
    have hj : j ≤ 1 := by
      by_cases ha : 0 < smallLeaves (Cfg.java b G H) A
      · by_cases hb' : 0 < smallLeaves (Cfg.java b G H) B
        · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (hAs.2 ha).1
          obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (hBs.2 hb').1
          cases es2 with
          | nil => simp at hhead
          | cons e es2 => simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
        · omega
      · omega
    refine ⟨j, hj, ⟨hv, hne2, rebalance_exit hr hm⟩, ?_, ?_, hs, ?_⟩
    · rw [vcostL_append] at hc; exact hc
    · simp only [entries, List.flatMap_append, List.length_append] at hgrow hlen ⊢
      omega
    · intro hj0
      apply heq
      omega

end Contract.PE
