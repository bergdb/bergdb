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

end SIS.Tree
