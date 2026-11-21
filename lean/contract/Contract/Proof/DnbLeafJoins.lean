/-
bergdb 030-37: accounting for the complete loop of joins of segment leaves.
Untouched neighbours, planned leaves and leaves already joined are included.
The potential is the number of changed small children: each join consumes
at least one, since concatenating leaf lists cannot make a large leaf small.
-/
import Contract.Proof.DnbDelJoin
import Contract.Proof.DnbDelEntries

namespace Contract.PE

open DNB PeProof

/-- The three forms of a leaf that the join loop can encounter. -/
inductive JoinLeaf (b G H : Nat) (i : Time) (s : Tree) : VN → Prop where
  | old {y : NodeId} {n : KNode} : getKey s y = some n → n.ks.length ≤ b →
      (Cfg.java b G H).m ≤ (live n.ks).length → JoinLeaf b G H i s (.old y)
  | planned {y g : Nat} {n : KNode} {es : List (Nat × VN)} :
      n.ks.length ≤ b → (∀ e ∈ es, ∃ z, e.2 = .old z) →
      (es.flatMap (fun e => ents e.1 e.2)).length ≤ (live n.ks).length +
        ((es.flatMap (fun e => ents e.1 e.2)).filter (isAdded (live n.ks))).length →
      (decideNode (Cfg.java b G H) i (some n) false (es.flatMap (fun e => ents e.1 e.2)) = .same →
        (Cfg.java b G H).m ≤ (es.flatMap (fun e => ents e.1 e.2)).length) →
      JoinLeaf b G H i s (.node (some y) g 0 false es (es.flatMap (fun e => ents e.1 e.2))
        (decideNode (Cfg.java b G H) i (some n) false (es.flatMap (fun e => ents e.1 e.2))))
  | joined {g : Nat} {es : List (Nat × VN)} :
      (∀ e ∈ es, ∃ z, e.2 = .old z) →
      JoinLeaf b G H i s (.node none g 0 true es (es.flatMap (fun e => ents e.1 e.2))
        (.parts (nParts (Cfg.java b G H).c (es.flatMap (fun e => ents e.1 e.2)).length)))

def smallLeaf (cf : Cfg) (v : VN) : Bool := v.changed && decide (v.size < cf.m)

def smallLeaves (cf : Cfg) (es : List (Nat × VN)) : Nat :=
  (es.filter (fun e => smallLeaf cf e.2)).length

def newEntries (es : List (Nat × VN)) : Nat :=
  ((entries es).filter (fun e => e.2.isNone)).length

def addedEntries (lb : List (Nat × NodeId)) (es : List (Nat × VN)) : Nat :=
  ((entries es).filter (isAdded lb)).length

theorem smallLeaves_cons (cf : Cfg) (a : Nat × VN) (es : List (Nat × VN)) :
    smallLeaves cf (a :: es) = (if smallLeaf cf a.2 then 1 else 0) + smallLeaves cf es := by
  simp only [smallLeaves, List.filter_cons]
  split
  · simp only [List.length_cons]; omega
  · simp

theorem smallLeaves_nil (cf : Cfg) : smallLeaves cf [] = 0 := rfl

theorem vcostL_append (A B : List (Nat × VN)) : vcostL (A ++ B) = vcostL A + vcostL B := by
  induction A with
  | nil => simp [vcostL]
  | cons a A ih => simp only [List.cons_append, vcostL, ih]; omega

theorem smallLeaves_append (cf : Cfg) (A B : List (Nat × VN)) :
    smallLeaves cf (A ++ B) = smallLeaves cf A + smallLeaves cf B := by
  simp [smallLeaves, List.filter_append]

theorem newEntries_append (A B : List (Nat × VN)) :
    newEntries (A ++ B) = newEntries A + newEntries B := by
  simp [newEntries, entries, List.flatMap_append, List.filter_append]

theorem newEntries_cons (a : Nat × VN) (A : List (Nat × VN)) :
    newEntries (a :: A) = noneCount a.1 a.2 + newEntries A := by
  simp [newEntries, entries, noneCount, List.filter_append]

theorem addedEntries_append (lb : List (Nat × NodeId)) (A B : List (Nat × VN)) :
    addedEntries lb (A ++ B) = addedEntries lb A + addedEntries lb B := by
  simp [addedEntries, entries, List.flatMap_append, List.filter_append]

theorem addedEntries_cons (lb : List (Nat × NodeId)) (a : Nat × VN) (A : List (Nat × VN)) :
    addedEntries lb (a :: A) = ((ents a.1 a.2).filter (isAdded lb)).length + addedEntries lb A := by
  simp [addedEntries, entries, List.filter_append]

theorem noneCount_le_added (lb : List (Nat × NodeId)) (c : Nat) (v : VN) :
    noneCount c v ≤ ((ents c v).filter (isAdded lb)).length := by
  unfold noneCount
  generalize ents c v = L
  induction L with
  | nil => simp
  | cons e L ih =>
    cases he : e.2 with
    | none => simp [isAdded, he]; omega
    | some y =>
      simp only [List.filter_cons, he, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      split
      · simp_all; omega
      · simp_all

theorem mkNode_none_added {cf : Cfg} {i : Time} {s : Tree} {g : Nat}
    {es : List (Nat × VN)} {v : VN} (hm : mkNode cf i s none g 0 true es = some v)
    (lb : List (Nat × NodeId)) (c : Nat) :
    ((ents c v).filter (isAdded lb)).length = noneCount c v := by
  unfold mkNode at hm
  simp only [beq_self_eq_true, ↓reduceIte] at hm
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    simp only [decideNode, ↓reduceIte]
    let F := es.flatMap (fun e => ents e.1 e.2)
    let k := nParts cf.c F.length
    have ha : ∀ e ∈ ents c (VN.node none g 0 true es F (.parts k)), e.2 = none := by
      simp only [ents]
      split
      · exact partEnts_none _ _ _ _
      · simp
    unfold noneCount
    have heq : (ents c (VN.node none g 0 true es F (.parts k))).filter (isAdded lb) =
        (ents c (VN.node none g 0 true es F (.parts k))).filter (fun e => e.2.isNone) := by
      apply List.filter_congr
      intro e he
      simp [isAdded, ha e he]
    exact congrArg List.length heq

/-- Opening a leaf exposes payloads only, and its live count is their length. -/
theorem JoinLeaf.open {b G H : Nat} {i : Time} {s : Tree} {v : VN}
    (hv : JoinLeaf b G H i s v) :
    ∃ es, openEs s v = some es ∧ (∀ e ∈ es, ∃ z, e.2 = .old z) ∧
      (es.flatMap (fun e => ents e.1 e.2)).length = cntOf s v := by
  cases hv with
  | @old y n hk _ _ =>
    refine ⟨(live n.ks).map (fun q => (q.1, VN.old q.2)), by simp [openEs, hk], ?_, ?_⟩
    · intro e he
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
      exact ⟨q.2, rfl⟩
    · simp [cntOf, hk, List.flatMap_map, ents]
  | planned _ hp _ _ => exact ⟨_, rfl, hp, rfl⟩
  | joined hp => exact ⟨_, rfl, hp, rfl⟩

/-- A leaf smaller than m is a changed planned node; untouched nodes have
the old fill rule. -/
theorem JoinLeaf.small {b G H : Nat} {i : Time} {s : Tree} {v : VN}
    (hv : JoinLeaf b G H i s v) :
    smallLeaf (Cfg.java b G H) v = true ↔ cntOf s v < (Cfg.java b G H).m := by
  cases hv with
  | old hk _ hf => simp [smallLeaf, VN.changed, cntOf, hk]; omega
  | @planned y g n es _ _ _ hf =>
    change ((decideNode (Cfg.java b G H) i (some n) false
      (es.flatMap (fun e => ents e.1 e.2)) != .same) &&
      decide ((es.flatMap (fun e => ents e.1 e.2)).length < (Cfg.java b G H).m)) = true ↔
        (es.flatMap (fun e => ents e.1 e.2)).length < (Cfg.java b G H).m
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨fun he => by have := hf he; omega, h⟩⟩
  | joined _ => simp [smallLeaf, VN.changed, VN.size, cntOf]

/-- A leaf's parts by c are covered by its decision and two spare nodes,
also when the neighbour is untouched. -/
theorem JoinLeaf.cost {b G H : Nat} (hb : 8 ≤ b) {i : Time} {s : Tree} {v : VN}
    (hv : JoinLeaf b G H i s v) (cv : Nat) :
    nParts (Cfg.java b G H).c (cntOf s v) ≤ vcost v + 2 ∧
      nParts (Cfg.java b G H).c (cntOf s v) ≤ noneCount cv v + 2 ∧
      (smallLeaf (Cfg.java b G H) v = true → 1 ≤ vcost v) := by
  obtain ⟨_, _, hM, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  cases hv with
  | @old y n hk hks _ =>
    have hlen := live_length_le n.ks
    have ht := nParts_two hc (n := (live n.ks).length) (by
      change b ≤ 2 * (Cfg.java b G H).c at hM; omega)
    simpa [cntOf, hk, vcost, noneCount, ents, smallLeaf, VN.changed] using ht
  | @planned y g n es hks hp hlen hf =>
    have hd := decide_facts (G := G) (H := H) (i := i) (g := g) (h := 0) (y := y) (c := cv)
      (es := es) hb hks hlen
    have hz := vcostL_payloads hp
    refine ⟨?_, hd.2.2.2.1, ?_⟩
    · simpa only [cntOf, VN.size, vcost, hz, Nat.add_zero] using hd.2.2.1
    · intro hs
      have hne : decideNode (Cfg.java b G H) i (some n) false
          (es.flatMap (fun e => ents e.1 e.2)) ≠ .same := by
        simp only [smallLeaf, Bool.and_eq_true] at hs
        exact bne_iff_ne.mp hs.1
      simpa only [vcost, hz, Nat.add_zero] using hd.2.1 hne
  | @joined g es hp =>
    have hz := vcostL_payloads hp
    have hj := joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := cv)
      (es := es) (F := es.flatMap (fun e => ents e.1 e.2))
    simp only [cntOf, VN.size, vcost, dcost, hz, Nat.add_zero]
    exact ⟨by omega, by rw [hj.2.2.1]; omega, fun _ => nParts_pos _ _⟩

/-- One leaf join, including an untouched neighbour or a previously joined
group. Its result can be small only when both inputs were small. -/
theorem leaf_join_pair {b G H : Nat} (hb : 8 ≤ b) {i : Time} {s : Tree}
    {g cL cR : Nat} {l r v : VN} {esL esR : List (Nat × VN)}
    (hl : JoinLeaf b G H i s l) (hr : JoinLeaf b G H i s r)
    (hoL : openEs s l = some esL) (hoR : openEs s r = some esR)
    (hs : smallLeaf (Cfg.java b G H) l = true ∨ smallLeaf (Cfg.java b G H) r = true)
    (hm : mkNode (Cfg.java b G H) i s none g 0 true (esL ++ esR) = some v) :
    JoinLeaf b G H i s v ∧
      vcost v ≤ vcost l + vcost r + 2 ∧
      noneCount cL v ≤ noneCount cL l + noneCount cR r + 3 ∧
      (smallLeaf (Cfg.java b G H) v = true →
        smallLeaf (Cfg.java b G H) l = true ∧ smallLeaf (Cfg.java b G H) r = true) := by
  obtain ⟨L, hL, hpL, hnL⟩ := hl.open
  obtain ⟨R, hR, hpR, hnR⟩ := hr.open
  rw [hoL] at hL; cases hL
  rw [hoR] at hR; cases hR
  have hp : ∀ e ∈ esL ++ esR, ∃ z, e.2 = .old z := by
    intro e he
    exact (List.mem_append.mp he).elim (hpL e) (hpR e)
  have hlen : ((esL ++ esR).flatMap (fun e => ents e.1 e.2)).length = cntOf s l + cntOf s r := by
    rw [List.flatMap_append, List.length_append, hnL, hnR]
  unfold mkNode at hm
  simp only [beq_self_eq_true, ↓reduceIte] at hm
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    simp only [decideNode, ↓reduceIte]
    refine ⟨JoinLeaf.joined hp, ?_, ?_, ?_⟩
    · have hz := vcostL_payloads hp
      simp only [vcost, dcost, hz, Nat.add_zero, hlen]
      have hcl := hl.cost hb cL
      have hcr := hr.cost hb cR
      obtain ⟨_, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
      have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
      rcases hs with hs | hs
      · have hn := hl.small.mp hs
        have ha := nParts_add_le hc (n := cntOf s r) (a := cntOf s l) (by omega)
        have := hcl.2.2 hs
        omega
      · have hn := hr.small.mp hs
        have ha := nParts_add_le hc (n := cntOf s l) (a := cntOf s r) (by omega)
        rw [Nat.add_comm (cntOf s r)] at ha
        have := hcr.2.2 hs
        omega
    · rw [(joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := cL)
        (es := esL ++ esR) (F := (esL ++ esR).flatMap (fun e => ents e.1 e.2))).2.2.1, hlen]
      have hcl := (hl.cost hb cL).2.1
      have hcr := (hr.cost hb cR).2.1
      obtain ⟨_, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
      have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
      rcases hs with hs | hs
      · have hn := hl.small.mp hs
        have ha := nParts_add_le hc (n := cntOf s r) (a := cntOf s l) (by omega)
        omega
      · have hn := hr.small.mp hs
        have ha := nParts_add_le hc (n := cntOf s l) (a := cntOf s r) (by omega)
        rw [Nat.add_comm (cntOf s r)] at ha
        omega
    · intro hsmall
      have hn : cntOf s l + cntOf s r < (Cfg.java b G H).m := by
        change ((_ != Dec.same) && decide (((esL ++ esR).flatMap
          (fun e => ents e.1 e.2)).length < (Cfg.java b G H).m)) = true at hsmall
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsmall
        rw [hlen] at hsmall
        exact hsmall.2
      exact ⟨hl.small.mpr (by omega), hr.small.mpr (by omega)⟩

/-- The child selected by the actual loop is changed and small. -/
theorem findSmall_get {cf : Cfg} {es : List (Nat × VN)} {ix : Nat}
    (h : findSmall cf es = some ix) :
    ∃ e, es[ix]? = some e ∧ smallLeaf cf e.2 = true := by
  unfold findSmall at h
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  obtain rfl : p.2 = ix := he
  have hm := List.mem_of_find?_eq_some hp
  have hget := mem_zipIdx_get hm
  exact ⟨p.1, hget.2, by simpa only [smallLeaf] using List.find?_some hp⟩

/-- One loop step consumes at least one small child, including when the
selected child is on the right of the pair chosen by M1. -/
theorem joinAt_leaf_account {b G H : Nat} (hb : 8 ≤ b) {i : Time} {s : Tree} {g ix : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} {es es' : List (Nat × VN)}
    (hsmall : findSmall (Cfg.java b G H) es = some ix)
    (hes : ∀ e ∈ es, JoinLeaf b G H i s e.2)
    (hj : joinAt (Cfg.java b G H) i s g 0 down es ix = some es') :
    (∀ e ∈ es', JoinLeaf b G H i s e.2) ∧
      vcostL es' ≤ vcostL es + 2 ∧ newEntries es' ≤ newEntries es + 3 ∧
      es'.length + 1 = es.length ∧
      smallLeaves (Cfg.java b G H) es' + 1 ≤ smallLeaves (Cfg.java b G H) es ∧
      (es'.map (·.1)).Sublist (es.map (·.1)) ∧
      es'.head?.map (·.1) = es.head?.map (·.1) ∧
      ∀ lb, addedEntries lb es' ≤ addedEntries lb es + 3 := by
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
    · rename_i esL esR hoL hoR
      simp only [beq_self_eq_true, ↓reduceIte] at hj
      cases hm : mkNode (Cfg.java b G H) i s none g 0 true (esL ++ esR) with
      | none => rw [hm] at hj; cases hj
      | some v =>
        rw [hm] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        obtain ⟨hv, hw, hn, hp⟩ := leaf_join_pair hb hls hrs hoL hoR hs hm (cL := l.1) (cR := r.1)
        have hsplit := split_at2 hl hr
        have hpot : (if smallLeaf (Cfg.java b G H) v then 1 else 0) + 1 ≤
            (if smallLeaf (Cfg.java b G H) l.2 then 1 else 0) +
              (if smallLeaf (Cfg.java b G H) r.2 then 1 else 0) := by
          cases h1 : smallLeaf (Cfg.java b G H) l.2 <;>
            cases h2 : smallLeaf (Cfg.java b G H) r.2 <;>
            cases h3 : smallLeaf (Cfg.java b G H) v <;> simp [h1, h2, h3] at hs hp ⊢
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with (he | rfl) | he
          · exact hes e (List.mem_of_mem_take he)
          · exact hv
          · exact hes e (List.mem_of_mem_drop he)
        · conv_rhs => rw [hsplit, vcostL_append]
          simp only [vcostL_append, vcostL, Nat.add_zero]
          omega
        · conv_rhs => rw [hsplit, newEntries_append]
          simp only [newEntries_append, newEntries_cons]
          have h0 : newEntries [] = 0 := rfl
          rw [h0]
          omega
        · have hlt := (List.getElem?_eq_some_iff.mp hr).1
          simp only [List.length_append, List.length_take, List.length_cons, List.length_nil,
            List.length_drop]
          omega
        · conv_rhs => rw [hsplit, smallLeaves_append]
          simp only [smallLeaves_append, smallLeaves_cons, smallLeaves_nil]
          omega
        · conv_rhs => rw [hsplit]
          simp only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append]
          exact List.Sublist.append (.refl _) (.cons_cons _ (.cons _ (.refl _)))
        · conv_rhs => rw [hsplit]
          simp only [List.append_assoc, List.singleton_append]
          exact head_fst_eq _ _ _ _ _ _
        · intro lb
          have hnl := noneCount_le_added lb l.1 l.2
          have hnr := noneCount_le_added lb r.1 r.2
          have hnnew := mkNode_none_added hm lb l.1
          conv_rhs => rw [hsplit, addedEntries_append]
          simp only [addedEntries_append, addedEntries_cons]
          have h0 : addedEntries lb [] = 0 := rfl
          rw [h0, hnnew]
          omega
    · cases hj
  · cases hj

/-- Complete accounting for any number of leaf joins in the actual loop.
The witness j is the number of joins; it is at most the initial number of
small changed leaves. The statement permits every fuel, so it also bounds
an interrupted prefix of the loop. -/
theorem joinLoop_leaf_account {b G H : Nat} (hb : 8 ≤ b) {i : Time} {s : Tree} {g : Nat}
    {down : List (Nat × VN) → Option (List (Nat × VN))} :
    ∀ (n : Nat) (es es' : List (Nat × VN)),
      (∀ e ∈ es, JoinLeaf b G H i s e.2) →
      joinLoop (Cfg.java b G H) i s g 0 down n es = some es' →
      ∃ j, (∀ e ∈ es', JoinLeaf b G H i s e.2) ∧
        vcostL es' ≤ vcostL es + 2 * j ∧ newEntries es' ≤ newEntries es + 3 * j ∧
        es'.length + j = es.length ∧
        smallLeaves (Cfg.java b G H) es' + j ≤ smallLeaves (Cfg.java b G H) es ∧
        (es'.map (·.1)).Sublist (es.map (·.1)) ∧
        es'.head?.map (·.1) = es.head?.map (·.1) ∧
        ∀ lb, addedEntries lb es' ≤ addedEntries lb es + 3 * j
  | 0, es, es', hes, hj => by
    simp only [joinLoop, Option.some.injEq] at hj
    subst hj
    exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
  | n + 1, es, es', hes, hj => by
    rw [joinLoop] at hj
    split at hj
    · cases hj
      exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
    · cases hs : findSmall (Cfg.java b G H) es with
      | none =>
        rw [hs] at hj; cases hj
        exact ⟨0, hes, by omega, by omega, by omega, by omega, .refl _, rfl, fun _ => by omega⟩
      | some ix =>
        rw [hs] at hj
        simp only at hj
        cases hstep : joinAt (Cfg.java b G H) i s g 0 down es ix with
        | none => rw [hstep] at hj; cases hj
        | some es1 =>
          rw [hstep] at hj
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := joinAt_leaf_account hb hs hes hstep
          obtain ⟨j, k1, k2, k3, k4, k5, k6, k7, k8⟩ := joinLoop_leaf_account hb n es1 es' h1 hj
          exact ⟨j + 1, k1, by omega, by omega, by omega, by omega, k6.trans h6, k7.trans h7,
            fun lb => by have := h8 lb; have := k8 lb; omega⟩

end Contract.PE
