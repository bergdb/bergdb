/-
The contract package (bergdb 030-04): the setup of a scan's chain
(`Chain.setup`). The chain it makes is a path; every key before the chain is
before the start key, every key after it is after the start key, and the
klong at the chain is the start key itself or, if the tree does not hold the
start key, on the side that the scan leaves behind (`setupGo_spec`).
-/
import Contract.Proof.Chain

namespace Contract

variable {s : Tree}

/-! ## A start key as positions -/

/-- What `Chain.setup` needs of the start key as positions: a long segment
is not the last, a short one is; there is a segment. A key that
`Keys.toSegments` makes meets it, and so do the two keys that stand for no
start key, -1 forward and `Long.MAX_VALUE` backward. -/
structure StartOK (Kp : List Pos) : Prop where
  long : ∀ (idx : Nat) (c : Nat), Kp[idx]? = some (Pos.at c) → isLong c = true → idx + 1 < Kp.length
  short : ∀ (idx : Nat) (c : Nat), Kp[idx]? = some (Pos.at c) → isLong c = false → idx + 1 = Kp.length
  ne : Kp ≠ []

theorem keyWf_spec : ∀ (K : Key), keyWf K = true →
    ∀ (idx : Nat) (c : Nat), K[idx]? = some c → (isLong c = true ↔ idx + 1 < K.length)
  | [], h => by simp [keyWf] at h
  | [c0], h => by
    intro idx c hc
    simp only [keyWf, Bool.not_eq_true'] at h
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simp [h]
    | succ i => simp at hc
  | c0 :: c1 :: rest, h => by
    intro idx c hc
    simp only [keyWf, Bool.and_eq_true] at h
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simp [h.1]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc
      have := keyWf_spec (c1 :: rest) h.2 i c hc
      rw [this]
      simp

theorem startOK_kp {K : Key} (h : keyWf K = true) : StartOK (kp K) := by
  have hs := keyWf_spec K h
  have hget : ∀ (idx : Nat) (c : Nat), (kp K)[idx]? = some (Pos.at c) → K[idx]? = some c := by
    intro idx c hc
    simp only [kp, List.getElem?_map, Option.map_eq_some_iff] at hc
    obtain ⟨c', hc', hcc⟩ := hc
    injection hcc with hcc
    rw [hc', hcc]
  refine ⟨?_, ?_, ?_⟩
  · intro idx c hc hl
    have := (hs idx c (hget idx c hc)).mp hl
    simpa [kp] using this
  · intro idx c hc hl
    have h1 := hs idx c (hget idx c hc)
    have h2 : idx < K.length := by
      have := hget idx c hc
      exact (List.getElem?_eq_some_iff.mp this).1
    have h3 : ¬ idx + 1 < K.length := by
      intro h4
      rw [h1.mpr h4] at hl
      simp at hl
    simp only [kp, List.length_map]
    omega
  · cases K with
    | nil => simp [keyWf] at h
    | cons a r => simp [kp]

theorem startOK_sentinel (fwd : Bool) : StartOK [if fwd then Pos.lo else Pos.hi] := by
  refine ⟨?_, ?_, by simp⟩
  · intro idx c hc
    cases idx with
    | zero => cases fwd <;> simp at hc
    | succ i => simp at hc
  · intro idx c hc
    cases idx with
    | zero => cases fwd <;> simp at hc
    | succ i => simp at hc

theorem kp_append_cons (segs : List Nat) (d : Nat) (rest : List Nat) :
    kp (segs ++ d :: rest) = kp segs ++ Pos.at d :: kp rest := by
  simp [kp]

theorem kp_lt_of_seg {Kp : List Pos} {segs : List Nat} {σ : Pos} {tail : List Pos}
    (hK : Kp = kp segs ++ σ :: tail) {d : Nat} (rest : List Nat) (h : Pos.at d < σ) :
    kp (segs ++ d :: rest) < Kp := by
  rw [hK, kp_append_cons, append_lt_append_iff]
  exact cons_lt_cons_of_lt h _ _

theorem kp_gt_of_seg {Kp : List Pos} {segs : List Nat} {σ : Pos} {tail : List Pos}
    (hK : Kp = kp segs ++ σ :: tail) {d : Nat} (rest : List Nat) (h : σ < Pos.at d) :
    Kp < kp (segs ++ d :: rest) := by
  rw [hK, kp_append_cons, append_lt_append_iff]
  exact cons_lt_cons_of_lt h _ _

/-- With `index` segments of the start key passed and the chain still at the
start key: the start key is the segments passed, the segment looked for, and
the rest. -/
theorem modeA_decomp {Kp : List Pos} {segs : List Nat} {index : Nat} (hi : index < Kp.length)
    (ht : Kp.take index = kp segs) (fwd : Bool) :
    Kp = kp segs ++ startSeg fwd Kp index :: Kp.drop (index + 1) := by
  have h1 : Kp[index]? = some Kp[index] := List.getElem?_eq_getElem hi
  simp only [startSeg, h1]
  rw [← ht, ← List.drop_eq_getElem_cons hi, List.take_append_drop]

/-! ## One klong's keys -/

/-- The keys that a live klong of a sound node holds: each starts with a
segment at or above the klong's compare value (in a segment leaf, the compare
value itself) and below every later live klong's. -/
theorem Good.klong_head {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi)
    {n : KNode} (hobj : s.obj x = some (.key n)) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) {k : Key} {v : Nat}
    (hkv : (k, v) ∈ klongList s n.leaf (L s) c y) :
    ∃ d rest, k = d :: rest ∧ c ≤ d ∧ (n.leaf = true → d = c) ∧
      ∀ c₂ y₂, (c₂, y₂) ∈ live n.ks → c < c₂ → d < c₂ := by
  rcases mem_klongList.mp hkv with ⟨_, _, k', rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl, hkv⟩
  · exact ⟨c, k', rfl, le_refl c, fun _ => rfl, fun _ _ _ h => h⟩
  · exact ⟨c, [], rfl, le_refl c, fun _ => rfl, fun _ _ _ h => h⟩
  · cases h with
    | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      obtain ⟨pre', post, he⟩ := List.append_of_mem hm
      obtain ⟨d, r', hd, hd1, hd2⟩ := (hkid hl pre' c y post he).range k v hkv
      obtain ⟨hpre, _, hpp⟩ := live_split he
      have hbn := below_nextHi hpp (fun b hb => hhi b.1 b.2 (by rw [he]; simp [hb])) hd2
      refine ⟨d, r', hd, le_trans (le_max_right _ _) hd1, fun h0 => by rw [hl] at h0; simp at h0, ?_⟩
      intro c₂ y₂ hm₂ hlt
      rw [he] at hm₂
      rcases List.mem_append.mp hm₂ with h3 | h3
      · have := hpre _ h3
        simp at this; omega
      · rcases List.mem_cons.mp h3 with h3 | h3
        · injection h3 with h3 _; omega
        · exact hbn.2 _ h3

theorem mem_entD {fwd : Bool} {segs : List Nat} {n : KNode} {cs : List (Nat × NodeId)}
    {kv : Key × Nat} :
    kv ∈ entD s fwd segs n cs ↔
      ∃ cy ∈ cs, ∃ k v, (k, v) ∈ klongList s n.leaf (L s) cy.1 cy.2 ∧ kv = (segs ++ k, v) := by
  simp only [entD, List.mem_flatMap]
  constructor
  · rintro ⟨cy, hcy, h⟩
    have h' : kv ∈ (klongList s n.leaf (L s) cy.1 cy.2).map (pre segs) := by
      cases fwd <;> simpa [dir] using h
    obtain ⟨⟨k, v⟩, hk, rfl⟩ := List.mem_map.mp h'
    exact ⟨cy, hcy, k, v, hk, rfl⟩
  · rintro ⟨cy, hcy, k, v, hk, rfl⟩
    refine ⟨cy, hcy, ?_⟩
    have h' : (segs ++ k, v) ∈ (klongList s n.leaf (L s) cy.1 cy.2).map (pre segs) :=
      List.mem_map.mpr ⟨(k, v), hk, rfl⟩
    cases fwd <;> simpa [dir] using h'

theorem mem_pend_iff {fwd : Bool} {n : KNode} {q : Pos} {cy : Nat × NodeId} :
    cy ∈ pend fwd false n q ↔
      cy ∈ live n.ks ∧ (if fwd then q < Pos.at cy.1 else Pos.at cy.1 < q) := by
  cases fwd <;> simp [pend, Pos.below_iff, Pos.above_iff]

/-- A key is on the side of the start key that the scan leaves behind. -/
def Side (fwd : Bool) (Kp : List Pos) (k : Key) : Prop := if fwd then kp k < Kp else Kp < kp k

/-- The keys of the klongs below position q of a node are before the start
key. -/
def NB (s : Tree) (Kp : List Pos) (segs : List Nat) (n : KNode) (q : Pos) : Prop :=
  ∀ c y, (c, y) ∈ live n.ks → Pos.at c < q → ∀ k v, (k, v) ∈ klongList s n.leaf (L s) c y →
    kp (segs ++ k) < Kp

/-- The keys of the klongs above position q of a node are after the start
key. -/
def NA (s : Tree) (Kp : List Pos) (segs : List Nat) (n : KNode) (q : Pos) : Prop :=
  ∀ c y, (c, y) ∈ live n.ks → q < Pos.at c → ∀ k v, (k, v) ∈ klongList s n.leaf (L s) c y →
    Kp < kp (segs ++ k)

theorem NB.entD {Kp : List Pos} {segs : List Nat} {n : KNode} {q : Pos} (h : NB s Kp segs n q) :
    ∀ kv ∈ entD s false segs n (pend false false n q), kp kv.1 < Kp := by
  intro kv hkv
  obtain ⟨⟨c, y⟩, hcy, k, v, hk, rfl⟩ := mem_entD.mp hkv
  have := mem_pend_iff.mp hcy
  simp only [Bool.false_eq_true, ite_false] at this
  exact h c y this.1 this.2 k v hk

theorem NA.entD {Kp : List Pos} {segs : List Nat} {n : KNode} {q : Pos} (h : NA s Kp segs n q) :
    ∀ kv ∈ entD s true segs n (pend true false n q), Kp < kp kv.1 := by
  intro kv hkv
  obtain ⟨⟨c, y⟩, hcy, k, v, hk, rfl⟩ := mem_entD.mp hkv
  have := mem_pend_iff.mp hcy
  simp only [ite_true] at this
  exact h c y this.1 this.2 k v hk

theorem mem_ent_of_klong {segs : List Nat} {n : KNode} {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) {k : Key} {v : Nat}
    (hk : (k, v) ∈ klongList s n.leaf (L s) c y) : (segs ++ k, v) ∈ ent s segs n (live n.ks) := by
  simp only [ent, List.mem_flatMap]
  exact ⟨(c, y), hm, List.mem_map.mpr ⟨(k, v), hk, rfl⟩⟩

theorem not_at_lt_lo (c : Nat) : ¬ Pos.at c < Pos.lo := by
  simp [Pos.lt_def, Pos.rank]

theorem not_hi_lt_at (c : Nat) : ¬ Pos.hi < Pos.at c := by
  have h := @Pos.at_lt_hi c
  exact not_lt_of_gt h

/-! ## The search of the setup in one node -/

/-- What the search of `Chain.setup` finds in a sound node: with the link's
position at the klong found, or at the end that the setup takes when it
finds none, the klongs below the position hold keys before the start key and
the klongs above it keys after it. -/
theorem setupSearch_spec {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi)
    {n : KNode} (hobj : s.obj x = some (.key n)) (fwd hasDiff : Bool) {Kp : List Pos}
    (segs : List Nat) (σ : Pos)
    (hA : hasDiff = false → ∃ tail, Kp = kp segs ++ σ :: tail)
    (hB : hasDiff = true → ∀ kv ∈ ent s segs n (live n.ks), Side fwd Kp kv.1) :
    (setupSearch fwd hasDiff n.leaf n.ks σ = none →
      NB s Kp segs n (if fwd || (!fwd && !hasDiff && !n.leaf) then Pos.lo else Pos.hi) ∧
      NA s Kp segs n (if fwd || (!fwd && !hasDiff && !n.leaf) then Pos.lo else Pos.hi)) ∧
    (∀ c y, setupSearch fwd hasDiff n.leaf n.ks σ = some (c, y) →
      (c, y) ∈ live n.ks ∧ NB s Kp segs n (Pos.at c) ∧ NA s Kp segs n (Pos.at c) ∧
      (hasDiff = false → n.leaf = true → if fwd then Pos.at c ≤ σ else σ ≤ Pos.at c)) := by
  cases hasDiff with
  | true =>
    have hS := hB rfl
    cases fwd with
    | true =>
      simp only [setupSearch, ite_true]
      have hb := searchLt_best n.ks Pos.hi
      cases hres : searchLt n.ks Pos.hi with
      | none =>
        rw [hres] at hb
        have hemp : ∀ b, b ∉ live n.ks := by
          intro b hb'
          have := hb b hb'
          simp [Pos.above] at this
        refine ⟨fun _ => ⟨?_, ?_⟩, fun c y h => by simp at h⟩
        · intro c y hm; exact absurd hm (hemp _)
        · intro c y hm; exact absurd hm (hemp _)
      | some a =>
        rw [hres] at hb
        refine ⟨fun h => by simp at h, ?_⟩
        intro c y h
        injection h with h
        subst h
        refine ⟨hb.1, ?_, ?_, fun h => by simp at h⟩
        · intro c'' y'' hm'' _ k v hk
          have := hS _ (mem_ent_of_klong (segs := segs) hm'' hk)
          simpa [Side] using this
        · intro c'' y'' hm'' hlt k v hk
          have := hb.2.2 (c'', y'') hm'' (by simp [Pos.above])
          rw [Pos.at_lt_at] at hlt
          simp at this
          omega
    | false =>
      simp only [setupSearch, ite_true, Bool.false_eq_true, ite_false]
      have hb := searchGt_best n.ks Pos.lo
      cases hres : searchGt n.ks Pos.lo with
      | none =>
        rw [hres] at hb
        have hemp : ∀ b, b ∉ live n.ks := by
          intro b hb'
          have := hb b hb'
          simp [Pos.below] at this
        refine ⟨fun _ => ⟨?_, ?_⟩, fun c y h => by simp at h⟩
        · intro c y hm; exact absurd hm (hemp _)
        · intro c y hm; exact absurd hm (hemp _)
      | some a =>
        rw [hres] at hb
        refine ⟨fun h => by simp at h, ?_⟩
        intro c y h
        injection h with h
        subst h
        refine ⟨hb.1, ?_, ?_, fun h => by simp at h⟩
        · intro c'' y'' hm'' hlt k v hk
          have := hb.2.2 (c'', y'') hm'' (by simp [Pos.below])
          rw [Pos.at_lt_at] at hlt
          simp at this
          omega
        · intro c'' y'' hm'' _ k v hk
          have := hS _ (mem_ent_of_klong (segs := segs) hm'' hk)
          simpa [Side] using this
  | false =>
    obtain ⟨tail, hK⟩ := hA rfl
    have hLte : (searchLte n.ks σ = none → NB s Kp segs n Pos.lo ∧ NA s Kp segs n Pos.lo) ∧
        (∀ c y, searchLte n.ks σ = some (c, y) →
          (c, y) ∈ live n.ks ∧ NB s Kp segs n (Pos.at c) ∧ NA s Kp segs n (Pos.at c) ∧
            Pos.at c ≤ σ) := by
      have hb := searchLte_best n.ks σ
      cases hres : searchLte n.ks σ with
      | none =>
        rw [hres] at hb
        refine ⟨fun _ => ⟨?_, ?_⟩, fun c y h => by simp at h⟩
        · intro c y _ hlt; exact absurd hlt (not_at_lt_lo c)
        · intro c'' y'' hm'' _ k v hk
          obtain ⟨d, rest, rfl, hd, _, _⟩ := hg.klong_head hobj hm'' hk
          have h1 := hb (c'', y'') hm''
          simp only [Bool.not_eq_false'] at h1
          rw [Pos.below_iff] at h1
          exact kp_gt_of_seg hK rest (lt_of_lt_of_le h1 (Pos.at_le_at.mpr hd))
      | some a =>
        rw [hres] at hb
        refine ⟨fun h => by simp at h, ?_⟩
        intro c y h
        injection h with h
        subst h
        have hcσ : Pos.at c ≤ σ := by
          have := hb.2.1
          simp only [Bool.not_eq_true'] at this
          rw [← Bool.not_eq_true, Pos.below_iff] at this
          exact not_lt.mp this
        refine ⟨hb.1, ?_, ?_, hcσ⟩
        · intro c'' y'' hm'' hlt k v hk
          rw [Pos.at_lt_at] at hlt
          obtain ⟨d, rest, rfl, _, _, hd⟩ := hg.klong_head hobj hm'' hk
          have h1 := hd c y hb.1 hlt
          exact kp_lt_of_seg hK rest (lt_of_lt_of_le (Pos.at_lt_at.mpr h1) hcσ)
        · intro c'' y'' hm'' hlt k v hk
          rw [Pos.at_lt_at] at hlt
          obtain ⟨d, rest, rfl, hd, _, _⟩ := hg.klong_head hobj hm'' hk
          have h1 : σ < Pos.at c'' := by
            by_contra hn
            have := hb.2.2 (c'', y'') hm'' (by
              simp only [Bool.not_eq_true']
              rw [← Bool.not_eq_true, Pos.below_iff]
              exact hn)
            simp at this
            omega
          exact kp_gt_of_seg hK rest (lt_of_lt_of_le h1 (Pos.at_le_at.mpr hd))
    have hGte : n.leaf = true →
        (searchGte n.ks σ = none → NB s Kp segs n Pos.hi ∧ NA s Kp segs n Pos.hi) ∧
        (∀ c y, searchGte n.ks σ = some (c, y) →
          (c, y) ∈ live n.ks ∧ NB s Kp segs n (Pos.at c) ∧ NA s Kp segs n (Pos.at c) ∧
            σ ≤ Pos.at c) := by
      intro hl
      have hb := searchGte_best n.ks σ
      cases hres : searchGte n.ks σ with
      | none =>
        rw [hres] at hb
        refine ⟨fun _ => ⟨?_, ?_⟩, fun c y h => by simp at h⟩
        · intro c'' y'' hm'' _ k v hk
          obtain ⟨d, rest, rfl, _, hdc, _⟩ := hg.klong_head hobj hm'' hk
          have h1 := hb (c'', y'') hm''
          simp only [Bool.not_eq_false'] at h1
          rw [Pos.above_iff] at h1
          rw [hdc hl]
          exact kp_lt_of_seg hK rest h1
        · intro c y _ hlt; exact absurd hlt (not_hi_lt_at c)
      | some a =>
        rw [hres] at hb
        refine ⟨fun h => by simp at h, ?_⟩
        intro c y h
        injection h with h
        subst h
        have hcσ : σ ≤ Pos.at c := by
          have := hb.2.1
          simp only [Bool.not_eq_true'] at this
          rw [← Bool.not_eq_true, Pos.above_iff] at this
          exact not_lt.mp this
        refine ⟨hb.1, ?_, ?_, hcσ⟩
        · intro c'' y'' hm'' hlt k v hk
          rw [Pos.at_lt_at] at hlt
          obtain ⟨d, rest, rfl, _, hdc, _⟩ := hg.klong_head hobj hm'' hk
          have h1 : Pos.at c'' < σ := by
            by_contra hn
            have := hb.2.2 (c'', y'') hm'' (by
              simp only [Bool.not_eq_true']
              rw [← Bool.not_eq_true, Pos.above_iff]
              exact hn)
            simp at this
            omega
          rw [hdc hl]
          exact kp_lt_of_seg hK rest h1
        · intro c'' y'' hm'' hlt k v hk
          obtain ⟨d, rest, rfl, hd, _, _⟩ := hg.klong_head hobj hm'' hk
          exact kp_gt_of_seg hK rest
            (lt_of_le_of_lt hcσ (lt_of_lt_of_le hlt (Pos.at_le_at.mpr hd)))
    cases fwd with
    | true =>
      simp only [setupSearch, Bool.false_eq_true, ite_false, ite_true, Bool.true_or]
      exact ⟨hLte.1, fun c y h => ⟨(hLte.2 c y h).1, (hLte.2 c y h).2.1, (hLte.2 c y h).2.2.1,
        fun _ _ => (hLte.2 c y h).2.2.2⟩⟩
    | false =>
      cases hl : n.leaf with
      | false =>
        simp only [setupSearch, Bool.false_eq_true, ite_false, Bool.not_false, Bool.and_self,
          Bool.or_true, ite_true]
        exact ⟨hLte.1, fun c y h => ⟨(hLte.2 c y h).1, (hLte.2 c y h).2.1, (hLte.2 c y h).2.2.1,
          fun _ h0 => by simp at h0⟩⟩
      | true =>
        simp only [setupSearch, Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
          Bool.not_true, Bool.and_false, Bool.or_false]
        have hG' := hGte hl
        exact ⟨hG'.1, fun c y h => ⟨(hG'.2 c y h).1, (hG'.2 c y h).2.1, (hG'.2 c y h).2.2.1,
          fun _ _ => (hG'.2 c y h).2.2.2⟩⟩

end Contract
