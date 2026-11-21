/-
bergdb 030-37: virtual-node fill conditions before emit. A rebalance may
leave a single small child, which its parent's join or root collapse
must resolve. The conditions record that exception explicitly.
-/
import Contract.Proof.DnbFillParts
import Contract.Proof.DnbLeafJoins

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- Fill conditions within one segment of a virtual tree. Leaf payloads
are ids; the fill of the next-segment trees they name is separate. -/
inductive VFill (cf : Cfg) (i : Time) (s : Tree) (g : Nat) : Bool → Nat → VN → Prop where
  | old {isRoot : Bool} {h y : Nat} : Shaped cf s g h y → Filled cf s isRoot y →
      VFill cf i s g isRoot h (.old y)
  | leaf {isRoot : Bool} {base : Option NodeId} {join : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {d : Dec} :
      (∀ e ∈ es, ∃ y, e.2 = .old y) → F = entries es →
      d = decideNode cf i (base.bind (getKey s)) join F →
      (isRoot = false → d = .same → cf.m ≤ F.length) →
      VFill cf i s g isRoot 0 (.node base g 0 join es F d)
  | inner {isRoot : Bool} {h : Nat} {base : Option NodeId} {join : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {d : Dec} :
      (∀ e ∈ es, VFill cf i s g false h e.2) → (∀ e ∈ es, e.2.isEmpty = false) →
      (es.length < 2 ∨ findSmall cf es = none) → F = renameHead 0 (entries es) →
      d = decideNode cf i (base.bind (getKey s)) join F →
      (isRoot = false → d = .same → cf.m ≤ F.length) →
      VFill cf i s g isRoot (h + 1) (.node base g (h + 1) join es F d)

theorem findSmall_none_rename {es : List (Nat × VN)} (hf : findSmall cf es = none) (c : Nat) :
    findSmall cf (renameHead c es) = none := by
  cases es with
  | nil => exact hf
  | cons e es =>
    unfold findSmall at hf ⊢
    simp only [renameHead, List.zipIdx_cons, List.find?_cons] at hf ⊢
    cases hp : e.2.changed && decide (e.2.size < cf.m) <;> simp_all
    exact hf

theorem findSmall_none_old (lv : List (Nat × NodeId)) :
    findSmall cf (lv.map (fun q => (q.1, VN.old q.2))) = none := by
  unfold findSmall
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro p hp
  have he := List.mem_of_getElem? (mem_zipIdx_get hp).2
  obtain ⟨q, _, hq⟩ := List.mem_map.mp he
  have hv : p.1.2 = VN.old q.2 := congrArg Prod.snd hq.symm
  simp [hv, VN.changed]

theorem VFill.small {g h : Nat} {v : VN} (hm : 2 ≤ cf.m)
    (hv : VFill cf i s g false h v) :
    smallLeaf cf v = true ↔ cntOf s v < cf.m := by
  cases hv with
  | old hs hf =>
    obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hs
    have hmin := (filled_key hf ho).2.1 hm rfl
    simp [smallLeaf, VN.changed, cntOf, hk]
    omega
  | @leaf _ base j es F d _ _ _ hfull =>
    change ((d != .same) && decide (F.length < cf.m)) = true ↔ F.length < cf.m
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨fun he => by have := hfull rfl he; omega, h⟩⟩
  | @inner _ h base j es F d _ _ _ _ _ hfull =>
    change ((d != .same) && decide (F.length < cf.m)) = true ↔ F.length < cf.m
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨fun he => by have := hfull rfl he; omega, h⟩⟩

theorem VFill.cnt_pos {g h : Nat} {v : VN} (hm : 2 ≤ cf.m)
    (hv : VFill cf i s g false h v) (hne : v.isEmpty = false) : 0 < cntOf s v := by
  cases hv with
  | old hs hf =>
    obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hs
    have hmin := (filled_key hf ho).2.1 hm rfl
    simp only [cntOf, hk]
    omega
  | leaf => simpa only [VN.isEmpty, List.isEmpty_eq_false_iff, List.length_pos_iff_ne_nil,
      cntOf, VN.size] using hne
  | inner => simpa only [VN.isEmpty, List.isEmpty_eq_false_iff, List.length_pos_iff_ne_nil,
      cntOf, VN.size] using hne

theorem VFill.open_leaf {g : Nat} {isRoot : Bool} {v : VN}
    (hv : VFill cf i s g isRoot 0 v) :
    ∃ es, openEs s v = some es ∧ (∀ e ∈ es, ∃ y, e.2 = .old y) ∧
      (entries es).length = cntOf s v := by
  cases hv with
  | old hs _ =>
    obtain ⟨n, _, hk, _, _, _, _⟩ := shaped_getKey hs
    refine ⟨(live n.ks).map (fun q => (q.1, VN.old q.2)), by simp [openEs, hk], ?_, ?_⟩
    · intro e he
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      exact ⟨q.2, rfl⟩
    · simp [entries, cntOf, hk, List.flatMap_map, ents]
  | leaf hp hF _ _ => exact ⟨_, rfl, hp, by simpa only [cntOf, VN.size] using congrArg List.length hF.symm⟩

theorem VFill.open_inner {g h : Nat} {isRoot : Bool} {v : VN}
    (hv : VFill cf i s g isRoot (h + 1) v) :
    ∃ es, openEs s v = some es ∧
      (∀ e ∈ es, VFill cf i s g false h e.2) ∧ (∀ e ∈ es, e.2.isEmpty = false) ∧
      (es.length < 2 ∨ findSmall cf es = none) ∧ (entries es).length = cntOf s v := by
  cases hv with
  | old hs hf =>
    obtain ⟨n, ho, hk, _, hl, _, _⟩ := shaped_getKey hs
    have hleaf : n.leaf = false := by simpa using hl
    have hkids := (shaped_inner hs ho).2
    refine ⟨(live n.ks).map (fun q => (q.1, VN.old q.2)), by simp [openEs, hk], ?_, ?_,
      Or.inr (findSmall_none_old _), ?_⟩
    · intro e he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      exact VFill.old (hkids q.1 q.2 hq) ((filled_key hf ho).2.2.2 q.1 q.2 hq hleaf)
    · intro e he
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      rfl
    · simp [entries, cntOf, hk, List.flatMap_map, ents]
  | inner hc hn he hF _ _ =>
    exact ⟨_, rfl, hc, hn, he, by simp only [cntOf, VN.size, hF, renameHead_length]⟩

theorem decideNode_same_min {base : Option KNode} {j : Bool} {F : List (Nat × Option NodeId)}
    (hf : ∀ n, base = some n → cf.m ≤ (live n.ks).length)
    (hd : decideNode cf i base j F = .same) : cf.m ≤ F.length := by
  cases base with
  | none => simp [decideNode] at hd
  | some n =>
    have he := dec_same hd
    have hlen := congrArg List.length he
    rw [List.length_map] at hlen
    have := hf n rfl
    omega

theorem decideNode_small_parts_one {base : Option KNode} {j : Bool}
    {F : List (Nat × Option NodeId)} {k : Nat}
    (hh : cf.m ≤ cf.h) (hc : cf.m ≤ cf.c) (hc1 : 1 ≤ cf.c)
    (hn : F.length < cf.m) (hd : decideNode cf i base j F = .parts k) : k = 1 := by
  have hcut : cutParts cf F.length = 1 := by simp [cutParts, show F.length ≤ cf.h by omega]
  have hjoin : nParts cf.c F.length = 1 := by
    rw [nParts_of_pos hc1, ite_eq_left (by omega)]
  cases base with
  | none => cases j <;> simpa [decideNode, hcut, hjoin] using hd.symm
  | some n =>
    unfold decideNode at hd
    simp only [hcut] at hd
    split at hd
    · cases hd
    · split at hd
      · split at hd
        · split at hd <;> cases hd <;> rfl
        · cases hd
      · cases hd; rfl

theorem VFill.small_ents {b G H g h cv : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : VFill (Cfg.java b G H) i s g false h v)
    (hs : smallLeaf (Cfg.java b G H) v = true) : (ents cv v).length = 1 := by
  obtain ⟨hm2, hmc, _, hcap, hh, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := by omega
  have hmh : (Cfg.java b G H).m ≤ (Cfg.java b G H).h := by omega
  have hsz := (hv.small hm2).mp hs
  cases hv with
  | old hshape hfilled =>
    obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hshape
    have hmin := (filled_key hfilled ho).2.1 hm2 rfl
    simp [cntOf, hk] at hsz
    omega
  | @leaf root base j es F d _ _ hd _ =>
    cases d with
    | same => cases base <;> rfl
    | append => cases base <;> rfl
    | parts k =>
      have hk := decideNode_small_parts_one hmh hmc hc1 hsz hd.symm
      subst k
      simp [ents]
  | @inner root ht base j es F d _ _ _ _ hd _ =>
    cases d with
    | same => cases base <;> rfl
    | append => cases base <;> rfl
    | parts k =>
      have hk := decideNode_small_parts_one hmh hmc hc1 hsz hd.symm
      subst k
      simp [ents]

theorem VFill.open_ne {g h : Nat} {isRoot : Bool} {v : VN} {es : List (Nat × VN)}
    (hv : VFill cf i s g isRoot h v) (ho : openEs s v = some es) (hne : es ≠ []) :
    v.isEmpty = false := by
  cases hv with
  | old => rfl
  | @leaf _ base j es0 F d _ hF _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    have hneF : entries es0 ≠ [] := fun he => hne (flatMap_ents_nil he)
    simpa only [VN.isEmpty, hF, List.isEmpty_eq_false_iff] using hneF
  | @inner _ h base j es0 F d _ _ _ hF _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    have hneF : entries es0 ≠ [] := fun he => hne (flatMap_ents_nil he)
    simpa only [VN.isEmpty, hF, List.isEmpty_eq_false_iff] using renameHead_ne 0 hneF

theorem mkNode_vfill_leaf {g : Nat} {base : Option NodeId} {j isRoot : Bool}
    {es : List (Nat × VN)} {v : VN}
    (hp : ∀ e ∈ es, ∃ y, e.2 = .old y)
    (hf : ∀ n, base.bind (getKey s) = some n → isRoot = false → cf.m ≤ (live n.ks).length)
    (hm : mkNode cf i s base g 0 j es = some v) : VFill cf i s g isRoot 0 v := by
  unfold mkNode at hm
  simp only [beq_self_eq_true, ↓reduceIte] at hm
  cases base with
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · cases hm
      exact VFill.leaf hp rfl rfl (fun _ hs => by simp [decideNode] at hs)
  | some y =>
    simp only at hm
    cases hk : getKey s y with
    | none => rw [hk] at hm; cases hm
    | some n =>
      rw [hk] at hm
      cases hm
      refine VFill.leaf hp rfl (by simp [hk]) ?_
      intro hr hs
      exact decideNode_same_min (fun n' hn => by
        cases hn; exact hf n (by simp [hk]) hr) hs

theorem mkNode_vfill_inner {g h : Nat} {base : Option NodeId} {j isRoot : Bool}
    {es : List (Nat × VN)} {v : VN}
    (hc : ∀ e ∈ es, VFill cf i s g false h e.2)
    (hne : ∀ e ∈ es, e.2.isEmpty = false)
    (he : es.length < 2 ∨ findSmall cf es = none)
    (hf : ∀ n, base.bind (getKey s) = some n → isRoot = false → cf.m ≤ (live n.ks).length)
    (hm : mkNode cf i s base g (h + 1) j es = some v) : VFill cf i s g isRoot (h + 1) v := by
  have hc' : ∀ e ∈ renameHead 0 es, VFill cf i s g false h e.2 := by
    intro e hem
    obtain ⟨e', he', h2⟩ := renameHead_mem hem
    rw [← h2]; exact hc e' he'
  have hn' : ∀ e ∈ renameHead 0 es, e.2.isEmpty = false := by
    intro e hem
    obtain ⟨e', he', h2⟩ := renameHead_mem hem
    rw [← h2]; exact hne e' he'
  have he' : (renameHead 0 es).length < 2 ∨ findSmall cf (renameHead 0 es) = none := by
    rcases he with he | he
    · left; simpa only [renameHead_length] using he
    · exact Or.inr (findSmall_none_rename he 0)
  unfold mkNode at hm
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at hm
  cases base with
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · cases hm
      exact VFill.inner hc' hn' he' rfl rfl (fun _ hs => by simp [decideNode] at hs)
  | some y =>
    simp only at hm
    cases hk : getKey s y with
    | none => rw [hk] at hm; cases hm
    | some n =>
      rw [hk] at hm
      cases hm
      refine VFill.inner hc' hn' he' rfl (by simp [hk]) ?_
      intro hr hs
      exact decideNode_same_min (fun n' hn => by
        cases hn; exact hf n (by simp [hk]) hr) hs

end Contract.PE
