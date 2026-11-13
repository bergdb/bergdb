/-
The merge under a parent with room keeps the take-back's (B) and (C) together
(bergdb 024-12, TP4; `J2N`, TakeDeadCollapse.lean): `writerWP_merge_made_j2`.
The parent's klongs after are its own or name the new nodes
(`key_mem_mergeParentNode`), with its klongs before t and first time kept
(`mergeParentNode_facts`); a merged node the transaction made is retargeted away
from the parent's klongs of the transaction (`writerWP_mergeCleanup_K`, `RetOK`),
and the parent's klongs before its last time klong are klongs before t, which
name old nodes (`key_before_last_time`); the new nodes hold live klongs of
distinct compare values only (`newKlongs_lastLive`). At node-map level:
`deadLive_mergeParent` and `j2rest_merge`.
-/
import SIS.Tree.TakeDeadCollapse
import SIS.Tree.TakeInvMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem key_mem_set (ks : List Klong) (j : Nat) (k : Klong) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ ks.set j k) : Klong.key c y ∈ ks ∨ k = Klong.key c y := by
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact Or.inl h
  · exact Or.inr h.symm

theorem key_mem_add (n : KNode) (t : Time) (k : Klong) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (n.add t k).ks) : Klong.key c y ∈ n.ks ∨ k = Klong.key c y := by
  unfold KNode.add at h
  split at h
  · split at h
    · simp only [List.mem_append, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
  · simp only [List.mem_append, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false,
      false_or] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm

theorem key_mem_repoint (n : KNode) (j : Nat) (z : NodeId) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (n.repoint j z).ks) : Klong.key c y ∈ n.ks ∨ y = z := by
  unfold KNode.repoint at h
  split at h
  · rename_i c0 y0 _
    simp only [KNode.setAt] at h
    rcases key_mem_set n.ks j (.key c0 z) c y h with h | h
    · exact Or.inl h
    · simp only [Klong.key.injEq] at h
      exact Or.inr h.2.symm
  · exact Or.inl h

theorem key_mem_n1 (pn : KNode) (tt : Time) (b1 b2 : Bool) (u : List Nat) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (if b1 = true then pn else if b2 = true then pn.setAt (pn.size - 1) (.del u)
      else pn.add tt (.del u)).ks) : Klong.key c y ∈ pn.ks := by
  split at h
  · exact h
  · split at h
    · rcases key_mem_set pn.ks _ _ c y h with h | h
      · exact h
      · cases h
    · rcases key_mem_add pn tt _ c y h with h | h
      · exact h
      · cases h

theorem key_mem_n2 (n1 : KNode) (tt : Time) (b : Bool) (il cL : Nat) (m1 : NodeId) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (if b = true then n1.repoint il m1 else n1.add tt (.key cL m1)).ks) :
    Klong.key c y ∈ n1.ks ∨ y = m1 := by
  split at h
  · exact key_mem_repoint n1 il m1 c y h
  · rcases key_mem_add n1 tt _ c y h with h | h
    · exact Or.inl h
    · simp only [Klong.key.injEq] at h
      exact Or.inr h.2.symm

theorem key_mem_mpNode (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks) :
    Klong.key c y ∈ pn.ks ∨ y = m1 ∨ ∃ g, m2 = some (y, g) := by
  unfold mpNode at h
  cases m2 with
  | none =>
    simp only at h
    rcases key_mem_n2 _ tt lip il cL m1 c y h with h | h
    · exact Or.inl (key_mem_n1 pn tt _ htd _ c y h)
    · exact Or.inr (Or.inl h)
  | some yg =>
    obtain ⟨y2, g2⟩ := yg
    simp only at h
    cases rip with
    | true =>
      simp only [↓reduceIte] at h
      rcases key_mem_repoint _ ir y2 c y h with h | h
      · rcases key_mem_n2 _ tt lip il cL m1 c y h with h | h
        · exact Or.inl (key_mem_n1 pn tt _ htd _ c y h)
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨g2, by rw [h]⟩)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases key_mem_add _ tt _ c y h with h | h
      · rcases key_mem_n2 _ tt lip il cL m1 c y h with h | h
        · exact Or.inl (key_mem_n1 pn tt _ htd _ c y h)
        · exact Or.inr (Or.inl h)
      · simp only [Klong.key.injEq] at h
        exact Or.inr (Or.inr ⟨g2, by rw [h.2]⟩)

/-- A key klong of the merge's parent after names what the parent named, or a new
node. -/
theorem key_mem_mergeParentNode (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (mergeParentNode pn tt il cL m1 ir cR m2).ks) :
    Klong.key c y ∈ pn.ks ∨ y = m1 ∨ ∃ g, m2 = some (y, g) := by
  rw [mergeParentNode_eq] at h
  exact key_mem_mpNode pn tt il cL m1 ir cR m2 _ _ _ c y h

/-! ## Klongs before time t -/

/-- Two klong lists that agree up to a time klong of t > 0 have the same klongs
before t. -/
theorem prefixAt_agree (ks ks' : List Klong) (t : Time) (ti : Nat) (hpos : 0 < t)
    (hti : ks[ti]? = some (.time t)) (hag : ∀ i, i ≤ ti → ks'[i]? = ks[i]?) :
    prefixAt ks' (t - 1) = prefixAt ks (t - 1) := by
  unfold prefixAt
  induction ks generalizing ks' ti with
  | nil => simp at hti
  | cons k ks ih =>
    cases ks' with
    | nil => have := hag 0 (Nat.zero_le _); simp at this
    | cons k' ks' =>
      have h0 := hag 0 (Nat.zero_le _)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      cases ti with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hti
        subst hti
        simp [show ¬ (t ≤ t - 1) by omega]
      | succ ti =>
        simp only [List.getElem?_cons_succ] at hti
        have hrest : ∀ i, i ≤ ti → ks'[i]? = ks[i]? := fun i hi => by
          have := hag (i + 1) (by omega)
          simpa using this
        cases k' with
        | time u =>
          by_cases hu : u ≤ t - 1
          · simp only [List.takeWhile_cons, hu, decide_true, ↓reduceIte]
            rw [ih ks' ti hti hrest]
          · simp [hu]
        | key c y =>
          simp only [List.takeWhile_cons, ↓reduceIte]
          rw [ih ks' ti hti hrest]
        | del b =>
          simp only [List.takeWhile_cons, ↓reduceIte]
          rw [ih ks' ti hti hrest]

theorem KNode.add_ks_time (n : KNode) (t : Time) (k : Klong) (hlt : ∀ u, n.lastTime = some u → u < t) :
    (n.add t k).ks = n.ks ++ [.time t, k] := by
  unfold KNode.add
  split
  · rename_i lt hl
    simp only [hlt lt hl, ↓reduceIte]
  · rfl

/-- Every step of `mpNode` keeps the klongs up to a time klong of tt at ti when
what it sets in place lies after ti. -/
theorem mpNode_agree_at (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) (ti : Nat)
    (hk : pn.ks[ti]? = some (.time tt)) (htdh : htd = true → ti < pn.size - 1)
    (hlip : lip = true → ti < il) (hrip : rip = true → ti < ir) :
    ∀ i, i ≤ ti → (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks[i]? = pn.ks[i]? := by
  have htil : ti < pn.ks.length := (List.getElem?_eq_some_iff.mp hk).1
  have hset : ∀ (n : KNode) (j : Nat) (k : Klong), ti < j →
      (∀ i, i ≤ ti → n.ks[i]? = pn.ks[i]?) → ∀ i, i ≤ ti → (n.setAt j k).ks[i]? = pn.ks[i]? := by
    intro n j k hj hn i hi
    simp only [KNode.setAt]
    rw [List.getElem?_set_ne (by omega)]
    exact hn i hi
  have hrep : ∀ (n : KNode) (j : Nat) (z : NodeId), ti < j →
      (∀ i, i ≤ ti → n.ks[i]? = pn.ks[i]?) → ∀ i, i ≤ ti → (n.repoint j z).ks[i]? = pn.ks[i]? := by
    intro n j z hj hn i hi
    unfold KNode.repoint
    split
    · exact hset n j _ hj hn i hi
    · exact hn i hi
  have hadd : ∀ (n : KNode) (k : Klong), ti < n.ks.length →
      (∀ i, i ≤ ti → n.ks[i]? = pn.ks[i]?) → ∀ i, i ≤ ti → (n.add tt k).ks[i]? = pn.ks[i]? := by
    intro n k hl hn i hi
    rcases KNode.add_ks n tt k with h | h <;> rw [h, List.getElem?_append_left (by omega)] <;>
      exact hn i hi
  have hlen : ∀ (n : KNode) (k : Klong), ti < n.ks.length → ti < (n.add tt k).ks.length := by
    intro n k hl
    rcases KNode.add_ks n tt k with h | h <;> rw [h] <;> simp <;> omega
  have hlenr : ∀ (n : KNode) (j : Nat) (z : NodeId), ti < n.ks.length → ti < (n.repoint j z).ks.length := by
    intro n j z hl
    unfold KNode.repoint
    split
    · simp only [KNode.setAt, List.length_set]; exact hl
    · exact hl
  have h0 : ∀ i, i ≤ ti → pn.ks[i]? = pn.ks[i]? := fun _ _ => rfl
  have h1 : ∀ (dr : Bool) (u : List Nat),
      ti < (if !dr then pn else if htd then pn.setAt (pn.size - 1) (.del u)
        else pn.add tt (.del u)).ks.length ∧
      ∀ i, i ≤ ti → (if !dr then pn else if htd then pn.setAt (pn.size - 1) (.del u)
        else pn.add tt (.del u)).ks[i]? = pn.ks[i]? := by
    intro dr u
    cases dr with
    | false => exact ⟨htil, h0⟩
    | true =>
      cases htd with
      | true =>
        have := htdh rfl
        simp only [KNode.size] at this
        refine ⟨?_, hset pn _ _ (by simp only [KNode.size]; omega) h0⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, KNode.setAt, List.length_set]
        exact htil
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hlen pn _ htil, hadd pn _ htil h0⟩
  have h2 : ∀ n1 : KNode, ti < n1.ks.length → (∀ i, i ≤ ti → n1.ks[i]? = pn.ks[i]?) →
      ti < (if lip then n1.repoint il m1 else n1.add tt (.key cL m1)).ks.length ∧
      ∀ i, i ≤ ti → (if lip then n1.repoint il m1 else n1.add tt (.key cL m1)).ks[i]? = pn.ks[i]? := by
    intro n1 hl1 ha1
    cases lip with
    | true => exact ⟨hlenr n1 il m1 hl1, hrep n1 il m1 (hlip rfl) ha1⟩
    | false => exact ⟨hlen n1 _ hl1, hadd n1 _ hl1 ha1⟩
  unfold mpNode
  rcases m2 with _ | ⟨y, g⟩
  · obtain ⟨hl1, ha1⟩ := h1 true (bitsUnion pn.lastBitmap (pn.bitsOf cR))
    exact (h2 _ hl1 ha1).2
  · obtain ⟨hl1, ha1⟩ := h1 (g != cR) (if (g != cR) then bitsUnion pn.lastBitmap (pn.bitsOf cR)
      else pn.lastBitmap)
    obtain ⟨hl2, ha2⟩ := h2 _ hl1 ha1
    cases rip with
    | true => exact hrep _ ir y (hrip rfl) ha2
    | false => exact hadd _ _ hl2 ha2

/-- `mpNode` with nothing set in place under a parent whose times are before tt
appends a time klong of tt and more. -/
theorem mpNode_ext_new (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hlt : ∀ u, pn.lastTime = some u → u < tt) :
    ∃ more, (mpNode pn tt il cL m1 ir cR m2 false false false).ks = pn.ks ++ more ∧
      more.head? = some (.time tt) := by
  have hext : ∀ (n : KNode) (k : Klong), (∃ more, n.ks = pn.ks ++ more ∧ more.head? = some (.time tt)) →
      ∃ more, (n.add tt k).ks = pn.ks ++ more ∧ more.head? = some (.time tt) := by
    intro n k ⟨more, hm, hh⟩
    cases more with
    | nil => simp at hh
    | cons a more =>
      rcases KNode.add_ks n tt k with h | h
      · exact ⟨a :: more ++ [.time tt, k], by rw [h, hm]; simp, hh⟩
      · exact ⟨a :: more ++ [k], by rw [h, hm]; simp, hh⟩
  have hfirst : ∀ k, ∃ more, (pn.add tt k).ks = pn.ks ++ more ∧ more.head? = some (.time tt) :=
    fun k => ⟨[.time tt, k], KNode.add_ks_time pn tt k hlt, rfl⟩
  have hfin : ∃ more, (mpNode pn tt il cL m1 ir cR m2 false false false).ks = pn.ks ++ more ∧
      more.head? = some (.time tt) := by
    have h2 : ∀ (dr : Bool) (u : List Nat), ∃ more,
        ((if !dr then pn else pn.add tt (.del u)).add tt (.key cL m1)).ks = pn.ks ++ more ∧
          more.head? = some (.time tt) := by
      intro dr u
      cases dr with
      | false => exact hfirst _
      | true => exact hext _ _ (hfirst _)
    unfold mpNode
    rcases m2 with _ | ⟨y, g⟩
    · exact h2 true _
    · exact hext _ _ (h2 (g != cR) _)
  exact hfin

/-- Two nodes that agree up to a time klong have the same first time. -/
theorem KNode.firstTime_agree (n n' : KNode) (ti : Nat) (u : Time) (hti : n.ks[ti]? = some (.time u))
    (hag : ∀ i, i ≤ ti → n'.ks[i]? = n.ks[i]?) : n'.firstTime = n.firstTime := by
  unfold KNode.firstTime
  generalize n.ks = ks at hti hag
  generalize n'.ks = ks' at hag
  induction ks generalizing ks' ti with
  | nil => simp at hti
  | cons k ks ih =>
    cases ks' with
    | nil => have := hag 0 (Nat.zero_le _); simp at this
    | cons k' ks' =>
      have h0 := hag 0 (Nat.zero_le _)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      cases ti with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hti
        subst hti
        simp
      | succ ti =>
        simp only [List.getElem?_cons_succ] at hti
        have hrest : ∀ i, i ≤ ti → ks'[i]? = ks[i]? := fun i hi => by
          have := hag (i + 1) (by omega)
          simpa using this
        simp only [List.findSome?_cons]
        rw [ih ti hti ks' hrest]

/-- `mpNode` agreeing with the parent up to its time klong of tt: it keeps the
klongs before tt and its first time, and has a time klong of tt. -/
theorem mpNode_facts_at (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) (ti : Nat) (hpos : 0 < tt)
    (hk : pn.ks[ti]? = some (.time tt)) (htdh : htd = true → ti < pn.size - 1)
    (hlip : lip = true → ti < il) (hrip : rip = true → ti < ir) :
    prefixAt (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks (tt - 1) = prefixAt pn.ks (tt - 1) ∧
    (∀ s, pn.firstTime = some s → (mpNode pn tt il cL m1 ir cR m2 htd lip rip).firstTime = some s) ∧
    Klong.time tt ∈ (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks := by
  have hag := mpNode_agree_at pn tt il cL m1 ir cR m2 htd lip rip ti hk htdh hlip hrip
  refine ⟨prefixAt_agree pn.ks _ tt ti hpos hk hag, fun s hs => ?_, ?_⟩
  · rw [KNode.firstTime_agree pn _ ti tt hk hag]; exact hs
  · exact List.mem_of_getElem? (by rw [hag ti (Nat.le_refl _)]; exact hk)

theorem mpNode_facts_new (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hpos : 0 < tt) (hlt : ∀ u, pn.lastTime = some u → u < tt) :
    prefixAt (mpNode pn tt il cL m1 ir cR m2 false false false).ks (tt - 1) = prefixAt pn.ks (tt - 1) ∧
    (∀ s, pn.firstTime = some s →
      (mpNode pn tt il cL m1 ir cR m2 false false false).firstTime = some s) ∧
    Klong.time tt ∈ (mpNode pn tt il cL m1 ir cR m2 false false false).ks := by
  obtain ⟨more, hm, hh⟩ := mpNode_ext_new pn tt il cL m1 ir cR m2 hlt
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · rw [hm]
    exact prefixAt_append_stop pn.ks more (tt - 1) tt (by omega) (Or.inr hh)
  · unfold KNode.firstTime at hs ⊢
    rw [hm, List.findSome?_append, hs]
    rfl
  · rw [hm]
    cases more with
    | nil => simp at hh
    | cons a more =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp

/-- The merge's parent after keeps the klongs before t and its first time, and
has a time klong of t. -/
theorem mergeParentNode_facts (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hpos : 0 < tt) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ tt) :
    prefixAt (mergeParentNode pn tt il cL m1 ir cR m2).ks (tt - 1) = prefixAt pn.ks (tt - 1) ∧
    (∀ s, pn.firstTime = some s → (mergeParentNode pn tt il cL m1 ir cR m2).firstTime = some s) ∧
    Klong.time tt ∈ (mergeParentNode pn tt il cL m1 ir cR m2).ks := by
  rw [mergeParentNode_eq]
  by_cases hof : pn.lastTime = some tt
  · obtain ⟨ti, hti, hk⟩ := KNode.lastTime_anchor pn tt hof
    have htil : ti < pn.ks.length := (List.getElem?_eq_some_iff.mp hk).1
    apply mpNode_facts_at pn tt il cL m1 ir cR m2 _ _ _ ti hpos hk
    · intro h
      simp only [Bool.and_eq_true] at h
      obtain ⟨h, -⟩ := h
      split at h
      · rename_i old hl
        simp only [KNode.size]
        have hne : ti ≠ pn.ks.length - 1 := by
          intro he
          rw [List.getLast?_eq_getElem?, ← he, hk] at hl
          cases hl
        omega
      · cases h
    · intro h
      simp only [hti, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    · intro h
      simp only [hti, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
  · have hb : (pn.lastTime == some tt) = false := by simpa using hof
    simp only [hb, Bool.and_false, Bool.false_and]
    apply mpNode_facts_new pn tt il cL m1 ir cR m2 hpos
    intro u hu
    obtain ⟨m, -, hm⟩ := KNode.lastTime_anchor pn u hu
    have := hpt u (List.mem_of_getElem? hm)
    have hne : u ≠ tt := fun he => hof (by rw [hu, he])
    omega

/-! ## Retarget -/

theorem retargetKlongs_get (ks : List Klong) (ti : Nat) (src dst : NodeId) (j : Nat) :
    (retargetKlongs ks ti src dst)[j]? = ks[j]?.map (fun k => retargetStep ti src dst (k, j)) := by
  rw [retargetKlongs_eq, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  congr 1
  funext k
  simp

theorem retargetKlongs_le (ks : List Klong) (ti : Nat) (src dst : NodeId) (j : Nat) (hj : j ≤ ti) :
    (retargetKlongs ks ti src dst)[j]? = ks[j]? := by
  rw [retargetKlongs_get]
  cases h : ks[j]? with
  | none => rfl
  | some k =>
    simp only [Option.map_some, Option.some.injEq]
    cases k with
    | key cv y =>
      simp only [retargetStep]
      have : decide (ti < j) = false := by simp; omega
      simp [this]
    | time u => rfl
    | del b => rfl

theorem retargetKlongs_key (ks : List Klong) (ti : Nat) (src dst : NodeId) (j cv : Nat) (y : NodeId)
    (h : (retargetKlongs ks ti src dst)[j]? = some (.key cv y)) :
    y = dst ∨ (ks[j]? = some (.key cv y) ∧ (ti < j → y ≠ src)) := by
  rw [retargetKlongs_get] at h
  cases hk : ks[j]? with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    simp only [Option.map_some, Option.some.injEq] at h
    cases k with
    | key c z =>
      simp only [retargetStep] at h
      split at h
      · rename_i hc
        cases h
        exact Or.inl rfl
      · rename_i hc
        cases h
        refine Or.inr ⟨rfl, fun hj he => hc ?_⟩
        simp [hj, he]
    | time u => simp [retargetStep] at h
    | del b => simp [retargetStep] at h

theorem lastTimeIndex_fold_shape (l : List Klong) (s : Nat) (acc : Option Nat) :
    ((l.map klongShape).zipIdx s).foldl (fun t (q : Klong × Nat) => match q.1 with
      | .time _ => some q.2
      | _ => t) acc =
    (l.zipIdx s).foldl (fun t (q : Klong × Nat) => match q.1 with
      | .time _ => some q.2
      | _ => t) acc := by
  induction l generalizing s acc with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.foldl_cons]
    cases a <;> exact ih _ _

theorem KNode.lastTimeIndex_shapeOf (n : KNode) : n.shapeOf.lastTimeIndex = n.lastTimeIndex := by
  unfold KNode.lastTimeIndex KNode.shapeOf
  exact lastTimeIndex_fold_shape n.ks 0 none

theorem KNode.lastTimeIndex_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    a.lastTimeIndex = b.lastTimeIndex := by
  rw [← KNode.lastTimeIndex_shapeOf a, h, KNode.lastTimeIndex_shapeOf]

/-- A klong before the last time klong t of a well formed list is a klong
before t. -/
theorem takeWhile_length_ge {α : Type} (p : α → Bool) (l : List α) (n : Nat) (hn : n ≤ l.length)
    (h : ∀ i a, i < n → l[i]? = some a → p a = true) : n ≤ (l.takeWhile p).length := by
  induction l generalizing n with
  | nil => simp at hn; omega
  | cons a l ih =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      have ha := h 0 a (by omega) rfl
      simp only [List.takeWhile_cons, ha, ↓reduceIte, List.length_cons]
      have := ih n (by simp at hn; omega) (fun i b hi hb => h (i + 1) b (by omega) (by simpa using hb))
      omega

theorem key_before_last_time (ks : List Klong) (t : Time) (ti : Nat) (hw : klongsWf ks = true)
    (hti : ks[ti]? = some (.time t)) (j : Nat) (hj : j < ti) (k : Klong) (hk : ks[j]? = some k) :
    k ∈ prefixAt ks (t - 1) := by
  have htil : ti < ks.length := (List.getElem?_eq_some_iff.mp hti).1
  apply mem_prefixAt_of_lt ks (t - 1) j k _ hk
  unfold prefixAt
  have := takeWhile_length_ge (fun k => match k with
    | .time x => decide (x ≤ t - 1)
    | _ => true) ks ti (by omega) (fun i a hi ha => by
    cases a with
    | time u =>
      have := klongsWf_times_increase ks hw i ti u t hi ha hti
      simp only [decide_eq_true_eq]; omega
    | key c y => rfl
    | del b => rfl)
  exact Nat.lt_of_lt_of_le hj this

/-! ## The new nodes -/

theorem newKlongs_prefix (t : Time) (l : List (Nat × NodeId)) (hpos : 0 < t) :
    prefixAt (newKlongs t l) (t - 1) = [] := by
  unfold prefixAt newKlongs
  simp only [List.takeWhile_cons]
  have : decide (t ≤ t - 1) = false := by simp; omega
  simp [this]

theorem newKlongs_firstTime (b : Bool) (t : Time) (l : List (Nat × NodeId)) :
    (⟨b, newKlongs t l⟩ : KNode).firstTime = some t := by
  simp [KNode.firstTime, newKlongs]

theorem key_mem_newKlongs (t : Time) (l : List (Nat × NodeId)) (cv : Nat) (y : NodeId)
    (h : Klong.key cv y ∈ newKlongs t l) : (cv, y) ∈ l := by
  simp only [newKlongs, List.mem_cons, reduceCtorEq, false_or, List.mem_map] at h
  obtain ⟨⟨a, b⟩, hm, he⟩ := h
  simp only [Klong.key.injEq] at he
  rw [← he.1, ← he.2]; exact hm

theorem newKlongs_lastBitmap (b : Bool) (t : Time) (l : List (Nat × NodeId)) :
    (⟨b, newKlongs t l⟩ : KNode).lastBitmap = [] := by
  unfold KNode.lastBitmap
  apply lastBitmapOf_append_nodel [] _ ?_ |>.trans rfl
  intro bs hm
  simp at hm

theorem newKlongs_lastLive (t : Time) (l : List (Nat × NodeId)) (hnd : (l.map Prod.fst).Nodup)
    (i cv : Nat) (y : NodeId) (hi : (newKlongs t l)[i]? = some (.key cv y)) :
    LastLive (newKlongs t l) [] i cv := by
  refine ⟨⟨y, hi⟩, List.not_mem_nil, fun j y' hij hj => ?_⟩
  exfalso
  have hget : ∀ (k : Nat) (c : Nat) (z : NodeId), (newKlongs t l)[k]? = some (.key c z) →
      ∃ k', k = k' + 1 ∧ (l.map Prod.fst)[k']? = some c := by
    intro k c z hk
    cases k with
    | zero => simp [newKlongs] at hk
    | succ k' =>
      refine ⟨k', rfl, ?_⟩
      simp only [newKlongs, List.getElem?_cons_succ, List.getElem?_map] at hk
      rw [List.getElem?_map]
      cases hl : l[k']? with
      | none => rw [hl] at hk; cases hk
      | some q =>
        rw [hl] at hk
        simp only [Option.map_some, Option.some.injEq, Klong.key.injEq] at hk
        simp [hk.1]
  obtain ⟨i', rfl, hi'⟩ := hget i cv y hi
  obtain ⟨j', rfl, hj'⟩ := hget j cv y' hj
  have hlen : i' < (l.map Prod.fst).length := (List.getElem?_eq_some_iff.mp hi').1
  have := (List.Nodup.getElem?_inj hlen hnd).mp (hi'.trans hj'.symm)
  omega

/-! ## (C) and the node facts after the merge, at node-map level -/

/-- (C) at the merge's parent after: every klong of it to a node at or above B
that is no value comes with a live klong. The parent's klongs are its own, its
klongs to the new nodes, and its klongs to a merged node the transaction made,
retargeted unless they come before the transaction's time klong, which they
cannot, since those name old nodes. -/
theorem deadLive_mergeParent (pn pn7 pn8 : KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (l r m1 : NodeId) (m2 : Option NodeId) (cL cR : Nat) (lMade rMade : Bool)
    (hDp : ∀ (i : Nat) (cv : Nat) (y : NodeId), pn.ks[i]? = some (Klong.key cv y) → B ≤ y → y ∉ vals → ∃ c, (c, y) ∈ pn.liveAt t)
    (hOp : ∀ cv y, Klong.key cv y ∈ prefixAt pn.ks (t - 1) → y < B)
    (hpL : (cL, l) ∈ pn.liveAt t) (hpR : (cR, r) ∈ pn.liveAt t)
    (hlM : B ≤ l → lMade = true) (hrM : B ≤ r → rMade = true)
    (hkey7 : ∀ cv y, Klong.key cv y ∈ pn7.ks → Klong.key cv y ∈ pn.ks ∨ y = m1 ∨ m2 = some y)
    (hpre7 : prefixAt pn7.ks (t - 1) = prefixAt pn.ks (t - 1)) (hwf7 : klongsWf pn7.ks = true)
    (hti7 : ∀ ti, pn7.lastTimeIndex = some ti → pn7.ks[ti]? = some (.time t))
    (hkeep : ∀ c z, (c, z) ∈ pn.liveAt t → c ≠ cL → c ≠ cR → (c, z) ∈ pn8.liveAt t)
    (hnew1 : ∃ c, (c, m1) ∈ pn8.liveAt t) (hnew2 : ∀ y, m2 = some y → ∃ c, (c, y) ∈ pn8.liveAt t)
    (hret : ∀ (j : Nat) (cv : Nat) (y : NodeId), pn8.ks[j]? = some (Klong.key cv y) → y = m1 ∨ (pn7.ks[j]? = some (Klong.key cv y) ∧
      ((y = l ∧ lMade = true) ∨ (y = r ∧ rMade = true) →
        ∃ ti, pn7.lastTimeIndex = some ti ∧ j ≤ ti))) :
    ∀ (i : Nat) (cv : Nat) (y : NodeId), pn8.ks[i]? = some (Klong.key cv y) → B ≤ y → y ∉ vals → ∃ c, (c, y) ∈ pn8.liveAt t := by
  intro i cv y hi hB hv
  -- a klong of pn7 at index i to a made merged node lies before the time klong
  have hold : ∀ ti, pn7.lastTimeIndex = some ti → i ≤ ti → pn7.ks[i]? = some (Klong.key cv y) → False := by
    intro ti hti hle h7
    have hk := hti7 ti hti
    have hne : i ≠ ti := fun he => by rw [he, hk] at h7; cases h7
    have hm := key_before_last_time pn7.ks t ti hwf7 hk i (by omega) _ h7
    rw [hpre7] at hm
    have := hOp cv y hm
    omega
  rcases hret i cv y hi with he | ⟨h7, hmade⟩
  · rw [he]; exact hnew1
  · rcases hkey7 cv y (List.mem_of_getElem? h7) with hpk | he | h2
    · obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hpk
      obtain ⟨c, hc⟩ := hDp i0 cv y hi0 hB hv
      by_cases hcl : c = cL
      · rw [hcl] at hc
        have hyl := KNode.liveAt_fun pn t cL l y hpL hc
        rw [← hyl] at hB
        obtain ⟨ti, hti, hle⟩ := hmade (Or.inl ⟨hyl.symm, hlM hB⟩)
        exact (hold ti hti hle h7).elim
      · by_cases hcr : c = cR
        · rw [hcr] at hc
          have hyr := KNode.liveAt_fun pn t cR r y hpR hc
          rw [← hyr] at hB
          obtain ⟨ti, hti, hle⟩ := hmade (Or.inr ⟨hyr.symm, hrM hB⟩)
          exact (hold ti hti hle h7).elim
        · exact ⟨c, hkeep c y hc hcl hcr⟩
    · rw [he]; exact hnew1
    · exact hnew2 y h2

/-- The node a merged node becomes when it is unlinked. -/
abbrev unlinkedNode (n : KNode) (t : Time) : KNode :=
  if n.lastTime == some t then n.toPrev (t - 1) else n

/-- (C) and the node facts after a merge, at node-map level: the parent p
changed with the same klongs before t and first time, (C) at it given; the new
nodes ms at or above B, no values, with live klongs of distinct compare values
only; a merged node the transaction made taken back, another unlinked; the
other nodes as before. -/
theorem j2rest_merge (N N' : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (p l r : NodeId) (ms : List NodeId) (pn ln rn pn8 : KNode) (lMade rMade : Bool) (hpos : 0 < t)
    (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B) (hS : OldStartN N t B)
    (hM : MadeStartN N t B) (hV : ValsNoNodeN N vals)
    (hpn : N p = some pn) (hN'p : N' p = some pn8) (hp8leaf : pn8.leaf = false)
    (hp8pre : prefixAt pn8.ks (t - 1) = prefixAt pn.ks (t - 1))
    (hp8ft : ∀ s, pn.firstTime = some s → pn8.firstTime = some s)
    (hp8D : ∀ (i : Nat) (cv : Nat) (y : NodeId), pn8.ks[i]? = some (Klong.key cv y) → B ≤ y → y ∉ vals → ∃ c, (c, y) ∈ pn8.liveAt t)
    (hms : ∀ m ∈ ms, B ≤ m ∧ m ∉ vals ∧
      ∃ b kl, N' m = some ⟨b, newKlongs t kl⟩ ∧ (kl.map Prod.fst).Nodup)
    (hln : N l = some ln) (hrn : N r = some rn)
    (hlM : lMade = (ln.firstTime == some t)) (hrM : rMade = (rn.firstTime == some t))
    (hfl : lMade = true → N' l = none) (hfl' : lMade = false → N' l = some (unlinkedNode ln t))
    (hfr : rMade = true → N' r = none) (hfr' : rMade = false → N' r = some (unlinkedNode rn t))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ r → y ∉ ms → N' y = N y) :
    DeadLiveN N' t B vals ∧ OldBelowN N' t B ∧ OldStartN N' t B ∧ MadeStartN N' t B ∧
      ValsNoNodeN N' vals := by
  -- the merged nodes after
  have hmerged : ∀ (x : NodeId) (xn : KNode) (xM : Bool), N x = some xn →
      xM = (xn.firstTime == some t) → (xM = true → N' x = none) →
      (xM = false → N' x = some (unlinkedNode xn t)) →
      ∀ xn', N' x = some xn' → x < B ∧ xn' = unlinkedNode xn t := by
    intro x xn xM hx hxM h1 h2 xn' hx'
    cases xM with
    | true => rw [h1 rfl] at hx'; cases hx'
    | false =>
      rw [h2 rfl] at hx'
      cases hx'
      refine ⟨lt_of_firstTime_ne N t B hM x xn hx ?_, rfl⟩
      intro hf
      rw [hf] at hxM
      simp at hxM
  have hfl2 := hmerged l ln lMade hln hlM hfl hfl'
  have hfr2 := hmerged r rn rMade hrn hrM hfr hfr'
  -- the facts of a node unlinked
  have hunl : ∀ (x : NodeId) (xn : KNode), N x = some xn → x < B →
      (DeadLiveN (fun z => if z = x then some (unlinkedNode xn t) else N z) t B vals) := by
    intro x xn hx hxB q qn hq i cv y hi hB hv
    by_cases hqx : q = x
    · simp only [hqx, ↓reduceIte, Option.some.injEq] at hq
      subst hq
      unfold unlinkedNode at hi
      split at hi
      · have hm : Klong.key cv y ∈ prefixAt xn.ks (t - 1) := List.mem_of_getElem? hi
        have := hO x xn hx cv y hm
        omega
      · have := hD x xn hx i cv y hi hB hv
        unfold unlinkedNode
        rename_i hne
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact this
    · simp only [hqx, ↓reduceIte] at hq
      exact hD q qn hq i cv y hi hB hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (C)
    intro q qn hq i cv y hi hB hv
    by_cases hqp : q = p
    · rw [hqp, hN'p] at hq; cases hq
      exact ⟨hp8D i cv y hi hB hv, fun h => by rw [hp8leaf] at h; cases h⟩
    · by_cases hql : q = l
      · rw [hql] at hq
        obtain ⟨hlB, he⟩ := hfl2 qn hq
        subst he
        exact hunl l ln hln hlB l _ (by simp) i cv y hi hB hv
      · by_cases hqr : q = r
        · rw [hqr] at hq
          obtain ⟨hrB, he⟩ := hfr2 qn hq
          subst he
          exact hunl r rn hrn hrB r _ (by simp) i cv y hi hB hv
        · by_cases hqm : q ∈ ms
          · obtain ⟨_, _, b, kl, hm, hnd⟩ := hms q hqm
            rw [hm] at hq; cases hq
            have hkl : (cv, y) ∈ kl := key_mem_newKlongs t kl cv y (List.mem_of_getElem? hi)
            refine ⟨⟨cv, (mrg_newKlongs_liveAt_iff b t kl hnd cv y).mpr hkl⟩, fun _ => ?_⟩
            rw [newKlongs_lastBitmap]
            exact newKlongs_lastLive t kl hnd i cv y hi
          · rw [hother q hqp hql hqr hqm] at hq
            exact hD q qn hq i cv y hi hB hv
  · -- klongs before t
    intro q qn hq cv y hk
    by_cases hqp : q = p
    · rw [hqp, hN'p] at hq; cases hq
      rw [hp8pre] at hk; exact hO p pn hpn cv y hk
    · by_cases hql : q = l
      · rw [hql] at hq
        obtain ⟨_, he⟩ := hfl2 qn hq
        subst he
        rw [(unlinked_facts ln t hpos).1] at hk
        exact hO l ln hln cv y hk
      · by_cases hqr : q = r
        · rw [hqr] at hq
          obtain ⟨_, he⟩ := hfr2 qn hq
          subst he
          rw [(unlinked_facts rn t hpos).1] at hk
          exact hO r rn hrn cv y hk
        · by_cases hqm : q ∈ ms
          · obtain ⟨_, _, b, kl, hm, _⟩ := hms q hqm
            rw [hm] at hq; cases hq
            simp only [newKlongs_prefix t kl hpos, List.not_mem_nil] at hk
          · rw [hother q hqp hql hqr hqm] at hq
            exact hO q qn hq cv y hk
  · -- old nodes start before t
    intro q qn hq hqB
    by_cases hqp : q = p
    · rw [hqp, hN'p] at hq; cases hq
      obtain ⟨s, hs, hf⟩ := hS p pn hpn (by rw [← hqp]; exact hqB)
      exact ⟨s, hs, hp8ft s hf⟩
    · by_cases hql : q = l
      · rw [hql] at hq hqB
        obtain ⟨_, he⟩ := hfl2 qn hq
        subst he
        obtain ⟨s, hs, hf⟩ := hS l ln hln hqB
        exact ⟨s, hs, (unlinked_facts ln t hpos).2 s hs hf⟩
      · by_cases hqr : q = r
        · rw [hqr] at hq hqB
          obtain ⟨_, he⟩ := hfr2 qn hq
          subst he
          obtain ⟨s, hs, hf⟩ := hS r rn hrn hqB
          exact ⟨s, hs, (unlinked_facts rn t hpos).2 s hs hf⟩
        · by_cases hqm : q ∈ ms
          · have := (hms q hqm).1; omega
          · rw [hother q hqp hql hqr hqm] at hq
            exact hS q qn hq hqB
  · -- new nodes start at t
    intro q qn hq hqB
    by_cases hqp : q = p
    · rw [hqp, hN'p] at hq; cases hq
      exact hp8ft t (hM p pn hpn (by rw [← hqp]; exact hqB))
    · by_cases hql : q = l
      · rw [hql] at hq hqB
        have := (hfl2 qn hq).1; omega
      · by_cases hqr : q = r
        · rw [hqr] at hq hqB
          have := (hfr2 qn hq).1; omega
        · by_cases hqm : q ∈ ms
          · obtain ⟨_, _, b, kl, hm, _⟩ := hms q hqm
            rw [hm] at hq; cases hq
            exact newKlongs_firstTime b t kl
          · rw [hother q hqp hql hqr hqm] at hq
            exact hM q qn hq hqB
  · -- no value is a node
    intro y hy
    by_cases hyp : y = p
    · rw [hyp] at hy; rw [hV p hy] at hpn; cases hpn
    · by_cases hyl : y = l
      · rw [hyl] at hy; rw [hV l hy] at hln; cases hln
      · by_cases hyr : y = r
        · rw [hyr] at hy; rw [hV r hy] at hrn; cases hrn
        · by_cases hym : y ∈ ms
          · exact absurd hy (hms y hym).2.1
          · rw [hother y hyp hyl hyr hym]; exact hV y hy

/-! ## The merge's parent: well formed, of time t, of its kind -/

theorem mergeParentNode_wf (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hw : klongsWf pn.ks = true) (hcR : cR ∈ pn.live.map Prod.fst) :
    klongsWf (mergeParentNode pn tt il cL m1 ir cR m2).ks = true := by
  unfold mergeParentNode
  exact KNode.merge_writes_wf pn tt il cL m1 ir cR m2 _ _ hw (pn.delete_bitmap_changes_of_live cR hcR)

theorem mpNode_leaf (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) :
    (mpNode pn tt il cL m1 ir cR m2 htd lip rip).leaf = pn.leaf := by
  have hadd : ∀ (n : KNode) (t : Time) (k : Klong), (n.add t k).leaf = n.leaf := by
    intro n t k; unfold KNode.add; split
    · split <;> rfl
    · rfl
  have hrep : ∀ (n : KNode) (j : Nat) (y : NodeId), (n.repoint j y).leaf = n.leaf := by
    intro n j y; unfold KNode.repoint; split <;> rfl
  have h1 : ∀ (dr : Bool) (u : List Nat), (if !dr then pn else if htd then pn.setAt (pn.size - 1) (.del u)
      else pn.add tt (.del u)).leaf = pn.leaf := by
    intro dr u
    cases dr <;> cases htd <;> simp [hadd, KNode.setAt]
  have h2 : ∀ n1 : KNode, n1.leaf = pn.leaf →
      (if lip then n1.repoint il m1 else n1.add tt (.key cL m1)).leaf = pn.leaf := by
    intro n1 hn1
    cases lip <;> simp [hadd, hrep, hn1]
  unfold mpNode
  rcases m2 with _ | ⟨y, g⟩
  · exact h2 _ (h1 _ _)
  · have := h2 _ (h1 (g != cR) (if (g != cR) then bitsUnion pn.lastBitmap (pn.bitsOf cR)
      else pn.lastBitmap))
    cases rip with
    | true => simp only [↓reduceIte]; rw [hrep]; exact this
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [hadd]; exact this

theorem mergeParentNode_leaf (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : (mergeParentNode pn tt il cL m1 ir cR m2).leaf = pn.leaf := by
  rw [mergeParentNode_eq]; exact mpNode_leaf _ _ _ _ _ _ _ _ _ _ _

/-- The merge's parent after is well formed, its last time t at its last time
klong. -/
theorem mergeParentNode_last (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hpos : 0 < tt) (hw : klongsWf pn.ks = true)
    (hcR : cR ∈ pn.live.map Prod.fst) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ tt) :
    klongsWf (mergeParentNode pn tt il cL m1 ir cR m2).ks = true ∧
    (mergeParentNode pn tt il cL m1 ir cR m2).lastTime = some tt ∧
    ∃ ti, (mergeParentNode pn tt il cL m1 ir cR m2).lastTimeIndex = some ti ∧
      (mergeParentNode pn tt il cL m1 ir cR m2).ks[ti]? = some (.time tt) := by
  have hwf := mergeParentNode_wf pn tt il cL m1 ir cR m2 hw hcR
  have hmem := (mergeParentNode_facts pn tt il cL m1 ir cR m2 hpos hpt).2.2
  have htimes : ∀ s, Klong.time s ∈ (mergeParentNode pn tt il cL m1 ir cR m2).ks → s ≤ tt := by
    rw [mergeParentNode_eq]
    exact mpNode_times pn tt il cL m1 ir cR m2 _ _ _ (htd_last pn _) hpt
  have hlt := KNode.lastTime_of_mem_max _ tt hwf hmem htimes
  exact ⟨hwf, hlt, KNode.lastTime_anchor _ tt hlt⟩

/-! ## The merge's last loop with the parent's klongs -/

/-- n' is n with some klongs of the transaction (after ti) pointed to dst, those
to a node meeting S among them. -/
def RetOK (n n' : KNode) (ti : Nat) (dst : NodeId) (S : NodeId → Prop) : Prop :=
  n'.leaf = n.leaf ∧ n'.lastTime = n.lastTime ∧ n'.lastTimeIndex = n.lastTimeIndex ∧
    (∀ j, j ≤ ti → n'.ks[j]? = n.ks[j]?) ∧
    (∀ (j : Nat) (cv : Nat) (y : NodeId), n'.ks[j]? = some (Klong.key cv y) →
      y = dst ∨ (n.ks[j]? = some (Klong.key cv y) ∧ (S y → j ≤ ti)))

theorem retOK_refl (n : KNode) (ti : Nat) (dst : NodeId) : RetOK n n ti dst (fun _ => False) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ h => Or.inr ⟨h, fun h => h.elim⟩⟩

theorem retOK_trans (n n1 n2 : KNode) (ti : Nat) (dst : NodeId) (S1 S2 : NodeId → Prop)
    (h1 : RetOK n n1 ti dst S1) (h2 : RetOK n1 n2 ti dst S2) :
    RetOK n n2 ti dst (fun y => S1 y ∨ S2 y) := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun j hj => (d2 j hj).trans (d1 j hj), ?_⟩
  intro j cv y hj
  rcases e2 j cv y hj with h | ⟨h, hS2⟩
  · exact Or.inl h
  · rcases e1 j cv y h with h' | ⟨h', hS1⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h', fun hS => hS.elim hS1 hS2⟩

theorem retOK_retarget (n : KNode) (ti : Nat) (src dst : NodeId) :
    RetOK n { n with ks := retargetKlongs n.ks ti src dst } ti dst (fun y => y = src) := by
  have hsh := KNode.retarget_shapeOf n ti src dst
  refine ⟨rfl, KNode.lastTime_of_shapeOf hsh, KNode.lastTimeIndex_of_shapeOf hsh,
    fun j hj => retargetKlongs_le n.ks ti src dst j hj, ?_⟩
  intro j cv y hj
  rcases retargetKlongs_key n.ks ti src dst j cv y hj with h | ⟨h, hne⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, fun hy => ?_⟩
    rcases Nat.lt_or_ge ti j with hlt | hge
    · exact absurd hy (hne hlt)
    · exact hge

theorem retOK_mono (n n' : KNode) (ti : Nat) (dst : NodeId) (S S' : NodeId → Prop)
    (h : RetOK n n' ti dst S) (hS : ∀ y, S' y → S y) : RetOK n n' ti dst S' := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a, b, c, d, fun j cv y hj => ?_⟩
  rcases e j cv y hj with h | ⟨h, hS'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, fun hy => hS' (hS y hy)⟩

/-- One step of the merge's last loop with the parent's klongs: q.1 taken back
and its klongs of the transaction in p retargeted to m1, or unlinked. -/
theorem writerWP_mergeCleanup_stepK (p m1 : NodeId) (c : Ctx) (q : NodeId × Bool) (w : W)
    (pn qn : KNode) (ti : Nat) (hp : w.nodes.lookup p = some pn) (hq : w.nodes.lookup q.1 = some qn)
    (hqp : q.1 ≠ p) (hlt : pn.lastTime = some c.i) (hti : pn.lastTimeIndex = some ti) :
    WriterWP ((if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) : M (ForInStep PUnit)) c w (fun s w' =>
      s = ForInStep.yield PUnit.unit ∧ w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
      (∀ y, y ≠ q.1 → w'.taken.contains y = w.taken.contains y) ∧
      (q.2 = true → w'.taken.contains q.1 = true) ∧
      (q.2 = false → w'.taken.contains q.1 = w.taken.contains q.1) ∧
      (∀ y, y ≠ p → y ≠ q.1 → w'.nodes.lookup y = w.nodes.lookup y) ∧
      (q.2 = false → w'.nodes.lookup q.1 = some (unlinkedNode qn c.i)) ∧
      ∃ pn', w'.nodes.lookup p = some pn' ∧
        RetOK pn pn' ti m1 (fun y => y = q.1 ∧ q.2 = true)) := by
  split
  · rename_i hq2
    simp only [writerWP_bind]
    unfold retarget
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hp]
    simp only [hlt, beq_self_eq_true, ↓reduceIte, hti, Option.getD_some]
    unfold putNode
    refine (writerWP_modify _ c w _).mpr ?_
    refine (writerWP_takenBack_iff _ c _ _).mpr ?_
    refine (writerWP_note_iff _ c _ _).mpr ?_
    refine (writerWP_pure _ c _ _).mpr ?_
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy; simp [hy]
    · intro _; simp
    · intro h; rw [hq2] at h; cases h
    · intro y hyp _
      show (upsert w.nodes p _).lookup y = _
      rw [lookup_upsert]; simp [hyp]
    · intro h; rw [hq2] at h; cases h
    · refine ⟨_, ?_, retOK_mono _ _ _ _ _ _ (retOK_retarget pn ti q.1 m1) (fun y hy => hy.1)⟩
      show (upsert w.nodes p _).lookup p = _
      rw [lookup_upsert]; simp only [↓reduceIte]
      rfl
  · rename_i hq2
    simp only [writerWP_bind]
    unfold unlink
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known q.1 qn c w hq]
    have hR : RetOK pn pn ti m1 (fun y => y = q.1 ∧ q.2 = true) :=
      retOK_mono _ _ _ _ _ _ (retOK_refl pn ti m1) (fun y hy => absurd hy.2 hq2)
    split
    · rename_i h
      simp only [putNode, writerWP_modify, writerWP_pure]
      refine ⟨by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial,
        by first | rfl | trivial, fun _ _ => by first | rfl | trivial, fun h => absurd h hq2,
        fun _ => by first | rfl | trivial, fun y _ hyq => ?_, fun _ => ?_, ⟨pn, ?_, hR⟩⟩
      · simp only [lookup_upsert, hyq, ↓reduceIte]
      · simp only [lookup_upsert, ↓reduceIte]
      · simp only [lookup_upsert, Ne.symm hqp, ↓reduceIte]; exact hp
    · rename_i h
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial,
        by first | rfl | trivial, fun _ _ => by first | rfl | trivial, fun h => absurd h hq2,
        fun _ => by first | rfl | trivial, fun y _ _ => by first | rfl | trivial, fun _ => ?_, ⟨pn, hp, hR⟩⟩
      exact hq

/-- The merge's last loop with the parent's klongs: each merged node taken back
(the parent's klongs of the transaction to it retargeted to m1) or unlinked. -/
theorem writerWP_mergeCleanup_K (p m1 : NodeId) (c : Ctx) (l r : NodeId) (bl br : Bool)
    (pn ln rn : KNode) (ti : Nat) (w : W) (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p)
    (hp : w.nodes.lookup p = some pn) (hl : w.nodes.lookup l = some ln)
    (hr : w.nodes.lookup r = some rn) (hlt : pn.lastTime = some c.i)
    (hti : pn.lastTimeIndex = some ti) :
    WriterWP (forIn [(l, bl), (r, br)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w (fun _ w' =>
      w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
      (∀ y, y ≠ l → y ≠ r → w'.taken.contains y = w.taken.contains y) ∧
      (bl = true → w'.taken.contains l = true) ∧ (br = true → w'.taken.contains r = true) ∧
      (bl = false → w'.taken.contains l = w.taken.contains l) ∧
      (br = false → w'.taken.contains r = w.taken.contains r) ∧
      (∀ y, y ≠ p → y ≠ l → y ≠ r → w'.nodes.lookup y = w.nodes.lookup y) ∧
      (bl = false → w'.nodes.lookup l = some (unlinkedNode ln c.i)) ∧
      (br = false → w'.nodes.lookup r = some (unlinkedNode rn c.i)) ∧
      ∃ pn', w'.nodes.lookup p = some pn' ∧
        RetOK pn pn' ti m1 (fun y => (y = l ∧ bl = true) ∨ (y = r ∧ br = true))) := by
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_stepK p m1 c (l, bl) w pn ln ti hp hl hlp hlt hti) ?_
  rintro s w1 ⟨hs, h1top, h1next, h1v, h1t, h1tl, h1tk, h1n, h1ul, pn1, h1p, hR1⟩
  subst hs
  simp only
  have hlt1 : pn1.lastTime = some c.i := by rw [hR1.2.1]; exact hlt
  have hti1 : pn1.lastTimeIndex = some ti := by rw [hR1.2.2.1]; exact hti
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_stepK p m1 c (r, br) w1 pn1 rn ti h1p
    (by rw [h1n r hrp (Ne.symm hlr)]; exact hr) hrp hlt1 hti1) ?_
  rintro s w2 ⟨hs, h2top, h2next, h2v, h2t, h2tl, h2tk, h2n, h2ul, pn2, h2p, hR2⟩
  subst hs
  simp only [List.forIn_nil, writerWP_pure]
  refine ⟨h2top.trans h1top, h2next.trans h1next, h2v.trans h1v, fun y hyl hyr => ?_,
    fun h => ?_, h2tl, fun h => ?_, fun h => ?_, fun y hyp hyl hyr => ?_, fun h => ?_, h2ul, pn2, h2p,
    retOK_mono _ _ _ _ _ _ (retOK_trans _ _ _ _ _ _ _ hR1 hR2) (fun y hy => hy)⟩
  · rw [h2t y hyr, h1t y hyl]
  · rw [h2t l hlr]; exact h1tl h
  · rw [h2t l hlr]; exact h1tk h
  · rw [h2tk h, h1t r (Ne.symm hlr)]
  · rw [h2n y hyp hyr, h1n y hyp hyl]
  · rw [h2n l hlp hlr]; exact h1ul h

theorem wNode_none_of (p : Params) (base : View BVal) (w : W) (x : NodeId)
    (h : w.taken.contains x = true) : wNode p base w x = none := by
  simp only [wNode, h, ↓reduceIte]

theorem wNode_some_of (p : Params) (base : View BVal) (w : W) (x : NodeId) (n : KNode)
    (ht : w.taken.contains x = false) (hl : w.nodes.lookup x = some n) : wNode p base w x = some n := by
  simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]

/-! ## The writer's merge under a parent with room keeps (B) and (C) -/

set_option maxHeartbeats 1600000 in
/-- The merge's tail keeps the take-back's (B) and (C) together (`TakeJ2`),
whether the transaction made the two nodes merged or not: each taken back or
unlinked; the premises those of `writerWP_mergeTail_made_take`, with `J2N`
before, the fresh nodes at or above B and above the values. -/
theorem writerWP_mergeTail_made_j2 (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (B : NodeId) (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hclt : cL < cR) (hcap : 1 ≤ c.p.mergeMax)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hwfN : ∀ y yn, N y = some yn → klongsWf yn.ks = true) (hpos : 0 < c.i)
    (hJ : J2N N c.i root B (w3.vals.map (·.1))) (hBnx : B ≤ nx)
    (hvnx : ∀ y ∈ w3.vals.map (·.1), y < nx)
    (h3l : w3.nodes.lookup l = some ln) (h3r : w3.nodes.lookup r = some rn) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => TakeJ2 c base B w') := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hcRl : cR ∈ pn.live.map Prod.fst := by
    have h := hpR
    rw [KNode.liveAt_of_times pn c.i hpt] at h
    exact List.mem_map.mpr ⟨_, h, rfl⟩
  have hlT3 : w3.taken.contains l = false := by
    have := hN3 ▸ hln
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hrT3 : w3.taken.contains r = false := by
    have := hN3 ▸ hrn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hndE : ((mergeList (!xn.leaf) cR ln.live rn.live).map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hsortE.imp (by intro a b hab; omega))
  have hll' : ln.leaf = !(!xn.leaf) := by rw [hll]; simp
  have hrl' : rn.leaf = !(!xn.leaf) := by rw [hrl]; simp
  have hm1notR : ¬ TReach N c.i root nx := not_reach_fresh N c.i root nx hT (hfree nx (Nat.le_refl _)).1
    (hfreshT nx (Nat.le_refl _))
  obtain ⟨hparOne, hparTwo⟩ := mrg_parent_liveAt pn c.i il cL nx ir cR l r hpwf hpt hL hLL hR hRL hc
  have hadjR : ∀ q ∈ pn.liveAt c.i, cL < q.1 → cR ≤ q.1 :=
    fun q hq hlt => (hadj q.1 q.2 hq).resolve_left (by omega)
  have hhead : (!xn.leaf) = true → ∃ y, rn.live.head? = some (0, y) := by
    intro h
    obtain ⟨y0, tl, he⟩ := hrhead h
    exact ⟨y0, by rw [he]; rfl⟩
  simp only [writerWP_bind, writerWP_modify]
  obtain ⟨xn3, hx3⟩ : ∃ n, w3.nodes.lookup x = some n := by
    rcases hxlr with h | h
    · rw [h]; exact ⟨ln, h3l⟩
    · rw [h]; exact ⟨rn, h3r⟩
  have hlr : l ≠ r := fun h => by
    have := (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩ ⟨pn, hpn, hpR⟩).2
    omega
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_ghOf_cached x xn3 c _ (by exact hx3) (fun _ w' => w'.nodes.lookup x = some xn3)
      (fun _ => by exact hx3))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, h4x⟩
  have hcl' : ∀ (b1 b2 : Bool) y, y ≠ l → y ≠ r → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
    intro b1 b2 y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ (b1 b2 : Bool), ∀ q ∈ [(l, b1), (r, b2)], (q : NodeId × Bool).1 ≠ p := by
    intro b1 b2 q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
    intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
    intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
    -- the ids
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
    have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
      intro z hz
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := h3src z (by rw [h']; rfl); omega
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, lookup_append_single_self]
      rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6x : w6.nodes.lookup x = w3.nodes.lookup x := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; omega), h4x, hx3]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
    have hpT : w3.taken.contains p = false := by
      have := hN3 ▸ hpn
      unfold wNode at this
      split at this
      · cases this
      · rename_i h; simpa using h
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
    have hhtd := htd_last pn
    -- the parent after
    have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
        ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
        (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
      intro m2 cc z hm
      rw [KNode.liveAt_of_times _ c.i (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
    rw [hw4m1] at hw6m1
    have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
        (first, second) := hmk
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
      intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlr' : ∀ (b1 b2 : Bool) (q : NodeId × Bool), q ∈ [(l, b1), (r, b2)] → q.1 = l ∨ q.1 = r := by
      intro b1 b2 q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    -- the parent after, into one node
    have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro cc z hm
      have hlk := hpliveAt none cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      simp only at hlk
      by_cases h1 : cc = cL
      · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inl ⟨h1, hlk.symm⟩
      · by_cases h2 : cc = cR
        · simp [h2, Ne.symm hc] at hlk
        · simp only [h1, h2, ↓reduceIte] at hlk
          right
          refine ⟨?_, h1, h2⟩
          rw [KNode.liveAt_of_times pn c.i hpt]
          exact mem_of_lookup_nodup _ cc z hlk
    -- the parent after, into two nodes
    have hchar2 : ∀ (m2 : NodeId) (g2 : Nat) cc z,
        (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR (some (m2, g2))).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ (cc = g2 ∧ z = m2) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro m2 g2 cc z hm
      have hlk := hpliveAt (some (m2, g2)) cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m2, g2)) _ _ _ l r
        hpwf hL hLL hR hRL hc ?htd ?hrip cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      case hrip =>
        intro h y g heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simp at h
        exact h.1.1
      simp only at hlk
      by_cases h0 : cc = g2
      · simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inr (Or.inl ⟨h0, hlk.symm⟩)
      · by_cases h1 : cc = cL
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨rfl, hlk.symm⟩
        · by_cases h2 : cc = cR
          · subst h2
            simp [h0, h1] at hlk
          · simp only [h0, h1, h2, ↓reduceIte] at hlk
            right; right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact mem_of_lookup_nodup _ cc z hlk
    -- neither merged node is named live by the parent after
    have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
      intro z hz cc hm h1 h2
      rcases hz with hz | hz
      · rw [hz] at hm
        exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hm⟩ hlink_l).2
      · rw [hz] at hm
        exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hm⟩ hlink_r).2
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
        (hdead _ _ _ _ _ _)) ?_
      intro _ w7 ⟨h7n, h7t, h7top, _, h7v, _, _, _⟩
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      obtain ⟨hwf7, hlt7, ti7, hti7, hk7⟩ := mergeParentNode_last pn c.i il cL m1 ir cR none hpos hpwf
        hcRl hpt
      have hfacts7 := mergeParentNode_facts pn c.i il cL m1 ir cR none hpos hpt
      have h7lr : ∀ y, (y = l ∨ y = r) → w7.nodes.lookup y = w3.nodes.lookup y := by
        intro y hy
        have hyp : y ≠ p := by
          rcases hy with h | h
          · rw [h]; exact Ne.symm hpl
          · rw [h]; exact Ne.symm hpr
        have hym : y ≠ m1 := by rcases hy with h | h <;> rw [h] <;> omega
        rw [h7n, lookup_upsert]
        simp only [hyp, ↓reduceIte]
        by_cases hyx' : y = x
        · rw [hyx']; exact h6x
        · exact h6old y hyx' hym
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_keep p m1 c.i c _ w7 _ (hne' _ _) hlk7
        (fun q hq c' hm => by
          rcases hchar1 c' q.1 hm with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2))
        (writerWP_mergeCleanup_K p m1 c l r _ _ _ ln rn ti7 w7 hlr (Ne.symm hpl) (Ne.symm hpr) hlk7
          (by rw [h7lr l (Or.inl rfl)]; exact h3l) (by rw [h7lr r (Or.inr rfl)]; exact h3r) hlt7 hti7)) ?_
      intro _ w8 ⟨⟨h8top, _, h8t, h8l, pn8, h8p, h8leaf, h8sub⟩, _, _, h8v, _, h8tl, h8tr, h8tkl, h8tkr, _,
        h8ul, h8ur, pn8', h8p', hR8⟩
      have hpn8 : pn8' = pn8 := by rw [h8p] at h8p'; exact (Option.some.inj h8p').symm
      rw [hpn8] at hR8
      have h8fl : w8.taken.contains l = true ∨ w8.nodes.lookup l = some (unlinkedNode ln c.i) := by
        first | exact Or.inl (h8tl rfl) | exact Or.inr (h8ul rfl)
      have h8fr : w8.taken.contains r = true ∨ w8.nodes.lookup r = some (unlinkedNode rn c.i) := by
        first | exact Or.inl (h8tr rfl) | exact Or.inr (h8ur rfl)
      try simp only [writerWP_pure]
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' _ _ y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' _ _ y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      have hN8m1 : wNode c.p base w8 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      have hN8p : wNode c.p base w8 p = some pn8 := by
        simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      have hndF : (first.map Prod.fst).Nodup := by rw [hfirst]; exact hndE
      have hother8 : ∀ y, y ≠ p → y ≠ l → y ≠ r → y ∉ [m1] → wNode c.p base w8 y = N y := by
        intro y hyp hyl hyr hym
        have hym' : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_singleton_self _)
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym']
      have hkeep8 : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → (cc, z) ∈ pn8.liveAt c.i :=
        fun cc z hm hc1 hc2 => (h8sub cc z).mpr ((hparOne cc z).mpr (Or.inr ⟨hm, hc1, hc2⟩))
      have hnew8 : ∃ cc, (cc, m1) ∈ pn8.liveAt c.i :=
        ⟨cL, (h8sub cL m1).mpr ((hparOne cL m1).mpr (Or.inl ⟨rfl, rfl⟩))⟩
      have hag8 := hR8.2.2.2.1
      have hp8D := deadLive_mergeParent pn (mergeParentNode pn c.i il cL m1 ir cR none) pn8 c.i B
        (w3.vals.map (·.1)) l r m1 none cL cR (ln.firstTime == some c.i) (rn.firstTime == some c.i)
        (fun i cv y hi hB hv => (hD p pn hpn i cv y hi hB hv).1) (hO p pn hpn) hpL hpR
        (fun hB => by rw [hM l ln hln hB]; simp) (fun hB => by rw [hM r rn hrn hB]; simp)
        (fun cv y hk => by
          rcases key_mem_mergeParentNode pn c.i il cL m1 ir cR none cv y hk with h | h | ⟨g, hg⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · cases hg)
        hfacts7.1 hwf7 (fun ti h => by rw [hti7] at h; cases h; exact hk7) hkeep8 hnew8
        (fun y h => by cases h)
        (fun j cv y hj => by
          rcases hR8.2.2.2.2 j cv y hj with h | ⟨h, hS'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, fun hy => ⟨ti7, hti7, hS' (by rw [hLM, hRM] at hy; exact hy)⟩⟩)
      have hrest := j2rest_merge N (wNode c.p base w8) c.i B (w3.vals.map (·.1)) p l r [m1] pn ln rn
        pn8 (ln.firstTime == some c.i) (rn.firstTime == some c.i) hpos hD hO hS hM hV hpn hN8p
        (by rw [hR8.1, mergeParentNode_leaf]; exact hpleaf)
        (by rw [prefixAt_agree _ pn8.ks c.i ti7 hpos hk7 hag8]; exact hfacts7.1)
        (fun s hs => by rw [KNode.firstTime_agree _ pn8 ti7 c.i hk7 hag8]; exact hfacts7.2.1 s hs)
        hp8D
        (fun m hm => by
          simp only [List.mem_singleton] at hm
          rw [hm]
          refine ⟨by omega, fun h => ?_, _, first, hN8m1, hndF⟩
          have := hvnx m1 h; omega)
        hln hrn rfl rfl
        (fun h => by rw [hLM] at h; exact wNode_none_of _ _ _ _ (h8tl h))
        (fun h => by
          rw [hLM] at h
          exact wNode_some_of _ _ _ _ _ (by rw [h8tkl h, h7t, h6taken]; exact hlT3) (h8ul h))
        (fun h => by rw [hRM] at h; exact wNode_none_of _ _ _ _ (h8tr h))
        (fun h => by
          rw [hRM] at h
          exact wNode_some_of _ _ _ _ _ (by rw [h8tkr h, h7t, h6taken]; exact hrT3) (h8ur h))
        hother8
      unfold TakeJ2
      rw [h8top, h7top, h6top', h8v, h7v, h6v, h5v, h4v]
      refine ⟨?_, hrest⟩
      refine ttReachedN_merge N (wNode c.p base w8) c.i root p l r [m1] pn ln rn pn8 cL cR hT hp hpn
        hpL hpR hln hrn
        (by intro m hm; simp only [List.mem_singleton] at hm; rw [hm]; exact hm1N) hN8p
        hkeep8 (fun m hm => by simp only [List.mem_singleton] at hm; rw [hm]; exact hnew8)
        ?_ hother8 ?_ hTt
      · intro cc z hz
        have hzs : z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
          rw [mergeList_map_snd, List.mem_append]
          rcases hz with h | h
          · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
          · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp hzs
        simp only at hqz
        rw [← hqz]
        refine ⟨m1, List.mem_singleton_self _, _, c', hN8m1, ?_⟩
        rw [mrg_newKlongs_liveAt_iff _ c.i first hndF, hfirst]
        exact hq
      · intro y yn hy hyn
        rcases hy with hy | hy <;> rw [hy] at hyn
        · rcases h8fl with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hlt8 : w8.taken.contains l = false := by
              cases hc : w8.taken.contains l with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hlt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
        · rcases h8fr with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hrt8 : w8.taken.contains r = false := by
              cases hc : w8.taken.contains r with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hrt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
      simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, h7v, _, _⟩
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
      subst hm2'
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, _, h8v, _⟩
      try simp only [writerWP_pure]
      have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
          hlk4 _ (by omega)]
        exact hnone3 _ (by omega)
      have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
          ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
        intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]
        exact hw6p
      refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
        w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
      intro _ w9 ⟨h9n, h9t, h9top, _, h9v, _, _, _⟩
      have hlk9 : w9.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
      obtain ⟨hwf9, hlt9, ti9, hti9, hk9⟩ := mergeParentNode_last pn c.i il cL m1 ir cR (some (m1 + 2, g2))
        hpos hpwf hcRl hpt
      have hfacts9 := mergeParentNode_facts pn c.i il cL m1 ir cR (some (m1 + 2, g2)) hpos hpt
      have h9lr : ∀ y, (y = l ∨ y = r) → w9.nodes.lookup y = w3.nodes.lookup y := by
        intro y hy
        have hyp : y ≠ p := by
          rcases hy with h | h
          · rw [h]; exact Ne.symm hpl
          · rw [h]; exact Ne.symm hpr
        have hym : y ≠ m1 := by rcases hy with h | h <;> rw [h] <;> omega
        have hym2 : y ≠ m1 + 2 := by rcases hy with h | h <;> rw [h] <;> omega
        rw [h9n, lookup_upsert]
        simp only [hyp, ↓reduceIte]
        rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
        by_cases hyx' : y = x
        · rw [hyx']; exact h6x
        · exact h6old y hyx' hym
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_keep p m1 c.i c _ w9 _ (hne' _ _) hlk9
        (fun q hq c' hm => by
          rcases hchar2 (m1 + 2) g2 c' q.1 hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h <;> omega
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2))
        (writerWP_mergeCleanup_K p m1 c l r _ _ _ ln rn ti9 w9 hlr (Ne.symm hpl) (Ne.symm hpr) hlk9
          (by rw [h9lr l (Or.inl rfl)]; exact h3l) (by rw [h9lr r (Or.inr rfl)]; exact h3r) hlt9 hti9)) ?_
      intro _ w10 ⟨⟨h10top, _, h10t, h10l, pn10, h10p, h10leaf, h10sub⟩, _, _, h10v, _, h10tl, h10tr, h10tkl,
        h10tkr, _, h10ul, h10ur, pn10', h10p', hR10⟩
      have hpn10 : pn10' = pn10 := by rw [h10p] at h10p'; exact (Option.some.inj h10p').symm
      rw [hpn10] at hR10
      have h10fl : w10.taken.contains l = true ∨ w10.nodes.lookup l = some (unlinkedNode ln c.i) := by
        first | exact Or.inl (h10tl rfl) | exact Or.inr (h10ul rfl)
      have h10fr : w10.taken.contains r = true ∨ w10.nodes.lookup r = some (unlinkedNode rn c.i) := by
        first | exact Or.inl (h10tr rfl) | exact Or.inr (h10ur rfl)
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElen : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
          ((!xn.leaf) = false → cL ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
        exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
      have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
          ((!xn.leaf) = false → cR ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrrange _ _ hq'
      obtain ⟨hgL, hg0, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hgU : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → g2 < k := by
        intro k z hk hkc
        apply hgU0 k hkc
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrup k z hk hkc _ _ hq'
      have hnd1 : (first.map Prod.fst).Nodup := by
        rw [hE1]
        exact List.pairwise_map.mpr ((hsortE.sublist (List.take_sublist _ _)).imp
          (by intro a b hab; omega))
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hnd2 : (ks2.map Prod.fst).Nodup := by
        rw [hE2]
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp (R := fun a b : Nat × NodeId => a.1 < b.1)
          (by intro a b hab; omega)
        generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hsortD
        | true =>
          simp only [↓reduceIte]
          apply renameHead_sorted 0 _ hsortD
          intro q hq
          cases hd : (mergeList true cR ln.live rn.live).drop
              (((mergeList true cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hq; simp at hq
          | cons a tl =>
            rw [hd] at hq hgs hsortD
            simp only [List.head?_cons, Option.some.injEq] at hgs
            subst hgs
            simp only [List.tail_cons] at hq
            have := (List.pairwise_cons.mp hsortD).1 q hq
            simp at this; omega
      have hTD : List.Pairwise (fun a b : Nat × NodeId => a.1 < b.1)
          ((mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) ++ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) := by
        rw [List.take_append_drop]; exact hsortE
      have hTDlt := (List.pairwise_append.mp hTD).2.2
      have hgD : (g2, yg) ∈ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := List.mem_of_head? hgs
      have hN10m1 : wNode c.p base w10 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), h8l,
          lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hN10m2 : wNode c.p base w10 (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        simp only [wNode, h10tc (m1 + 2) (by omega) (by omega), hm2T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' _ (by omega) (by omega) (by omega), h8l, lookup_append_single_self _ _ _ hw6m2]
      have hN10p : wNode c.p base w10 p = some pn10 := by
        simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      have hkeep10 : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → (cc, z) ∈ pn10.liveAt c.i := by
        intro cc z hm hc1 hc2
        have hcg : cc ≠ g2 := by
          rcases hadj cc z hm with h | h
          · omega
          · have := hgU cc z hm (by omega); omega
        exact (h10sub cc z).mpr ((hparTwo (m1 + 2) g2 cc z).mpr (Or.inr (Or.inr ⟨hcg, hc1, hc2, hm⟩)))
      have hnew10a : ∃ cc, (cc, m1) ∈ pn10.liveAt c.i := ⟨cL, (h10sub cL m1).mpr
            ((hparTwo (m1 + 2) g2 cL m1).mpr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)))⟩
      have hnew10b : ∃ cc, (cc, m1 + 2) ∈ pn10.liveAt c.i :=
        ⟨g2, (h10sub g2 (m1 + 2)).mpr ((hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩))⟩
      have hother10 : ∀ y, y ≠ p → y ≠ l → y ≠ r → y ∉ [m1, m1 + 2] → wNode c.p base w10 y = N y := by
        intro y hyp hyl hyr hym
        have hym1 : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_cons_self)
        have hym2 : y ≠ m1 + 2 := fun h => hym (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym1]
      have hag10 := hR10.2.2.2.1
      have hp10D := deadLive_mergeParent pn (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))
        pn10 c.i B (w3.vals.map (·.1)) l r m1 (some (m1 + 2)) cL cR (ln.firstTime == some c.i)
        (rn.firstTime == some c.i)
        (fun i cv y hi hB hv => (hD p pn hpn i cv y hi hB hv).1) (hO p pn hpn) hpL hpR
        (fun hB => by rw [hM l ln hln hB]; simp) (fun hB => by rw [hM r rn hrn hB]; simp)
        (fun cv y hk => by
          rcases key_mem_mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)) cv y hk with
            h | h | ⟨g, hg⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · simp only [Option.some.injEq, Prod.mk.injEq] at hg
            exact Or.inr (Or.inr (by rw [hg.1])))
        hfacts9.1 hwf9 (fun ti h => by rw [hti9] at h; cases h; exact hk9) hkeep10 hnew10a
        (fun y h => by simp only [Option.some.injEq] at h; rw [← h]; exact hnew10b)
        (fun j cv y hj => by
          rcases hR10.2.2.2.2 j cv y hj with h | ⟨h, hS'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, fun hy => ⟨ti9, hti9, hS' (by rw [hLM, hRM] at hy; exact hy)⟩⟩)
      have hrest := j2rest_merge N (wNode c.p base w10) c.i B (w3.vals.map (·.1)) p l r [m1, m1 + 2] pn
        ln rn pn10 (ln.firstTime == some c.i) (rn.firstTime == some c.i) hpos hD hO hS hM hV hpn hN10p
        (by rw [hR10.1, mergeParentNode_leaf]; exact hpleaf)
        (by rw [prefixAt_agree _ pn10.ks c.i ti9 hpos hk9 hag10]; exact hfacts9.1)
        (fun s hs => by rw [KNode.firstTime_agree _ pn10 ti9 c.i hk9 hag10]; exact hfacts9.2.1 s hs)
        hp10D
        (fun m hm => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hm | hm <;> rw [hm]
          · refine ⟨by omega, fun h => ?_, _, first, hN10m1, hnd1⟩
            have := hvnx m1 h; omega
          · refine ⟨by omega, fun h => ?_, _, ks2, hN10m2, hnd2⟩
            have := hvnx (m1 + 2) h; omega)
        hln hrn rfl rfl
        (fun h => by rw [hLM] at h; exact wNode_none_of _ _ _ _ (h10tl h))
        (fun h => by
          rw [hLM] at h
          exact wNode_some_of _ _ _ _ _ (by rw [h10tkl h, h9t, h8t, h7t, h6taken]; exact hlT3) (h10ul h))
        (fun h => by rw [hRM] at h; exact wNode_none_of _ _ _ _ (h10tr h))
        (fun h => by
          rw [hRM] at h
          exact wNode_some_of _ _ _ _ _ (by rw [h10tkr h, h9t, h8t, h7t, h6taken]; exact hrT3) (h10ur h))
        hother10
      unfold TakeJ2
      rw [h10top, h9top, h8top, h7top, h6top', h10v, h9v, h8v, h7v, h6v, h5v, h4v]
      refine ⟨?_, hrest⟩
      refine ttReachedN_merge N (wNode c.p base w10) c.i root p l r [m1, m1 + 2] pn ln rn pn10 cL cR
        hT hp hpn hpL hpR hln hrn
        (by
          intro m hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hm | hm <;> rw [hm]
          · exact hm1N
          · exact (hfree _ (by omega)).1) hN10p hkeep10 ?_ ?_ hother10 ?_ hTt
      · intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with hm | hm <;> rw [hm]
        · exact hnew10a
        · exact hnew10b
      · intro cc z hz
        have hzs : z ∈ (first ++ ks2).map Prod.snd := by
          rw [hE, List.map_append, List.mem_append]
          rcases hz with h | h
          · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
          · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        rw [List.map_append, List.mem_append] at hzs
        rcases hzs with h | h
        · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
          simp only at hqz
          rw [← hqz]
          exact ⟨m1, List.mem_cons_self, _, c', hN10m1,
            (mrg_newKlongs_liveAt_iff _ c.i first hnd1 c' z').mpr hq⟩
        · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
          simp only at hqz
          rw [← hqz]
          exact ⟨m1 + 2, List.mem_cons_of_mem _ List.mem_cons_self, _, c', hN10m2,
            (mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 c' z').mpr hq⟩
      · intro y yn hy hyn
        rcases hy with hy | hy <;> rw [hy] at hyn
        · rcases h10fl with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hlt8 : w10.taken.contains l = false := by
              cases hc : w10.taken.contains l with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hlt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
        · rcases h10fr with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hrt8 : w10.taken.contains r = false := by
              cases hc : w10.taken.contains r with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hrt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt

/-- The writer's merge keeps the take-back's (B) and (C) together (`TakeJ2`): x
at depth d merged with a sibling under a reached inner parent with room, made by
the transaction or not; the premises those of `writerWP_merge_made_take`, the
fresh nodes at or above B and above the values. -/
theorem writerWP_merge_made_j2 (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true)
    (hpos : 0 < c.i) (hJ : TakeJ2 c base B w) (hBnx : B ≤ w.next)
    (hvnx : ∀ y ∈ w.vals.map (·.1), y < w.next) :
    WriterWP (merge x d) c w (fun _ w' => TakeJ2 c base B w') := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpleaf, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TakeJ2 c base B w') := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn h3l h3r
      have hmemL : (cL, l) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      have hv3 : w3.vals = w.vals := hr3.2.2.2.1
      refine writerWP_mono (writerWP_mergeTail_made_j2 c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next B w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT
        hpleaf hclt hcap hadj hll hrl
        (fun cc z h => hlr2 cR r hmemR hclt cc z h)
        (by
          intro cc z h
          have h1 := hlr1 cc z h
          rw [hll] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
              · rcases Nat.eq_zero_or_pos cc with hcc | hcc
                · exact Or.inl hcc
                · exact Or.inr (by omega)
              · exact Or.inr (h0 hc0)
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            rcases Nat.eq_zero_or_pos cL with hc0 | hc0
            · omega
            · exact h1.1 hxl hc0)
        (by
          intro cc z h
          have h1 := hrr1 cc z h
          rw [hrl] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · exact Or.inr (h0 (by omega))
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            exact h1.1 hxl (by omega))
        (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h)
        hwfN hpos (by rw [hv3]; exact hJ) hBnx (by rw [hv3]; exact hvnx) h3l h3r) ?_
      intro _ w' h
      exact h
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            wb.nodes.lookup x = some xn →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TakeJ2 c base B w') := by
          intro wb ia0 cva hrb hpreb hxb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, hlk4s, hwn4, hpre4, hsrc4, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
              (lookup_of_prefix _ _ hpre4 x xn hxb) hlk4s
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, hlk3s, hwn3, hpre3, hsrc3, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn hlk3s
                (lookup_of_prefix _ _ hpre3 x xn hlk2)
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 (lookup_of_prefix _ _ hpre3 x xn hlk2) hsrc03 hLa hax
                (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hlk2 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
