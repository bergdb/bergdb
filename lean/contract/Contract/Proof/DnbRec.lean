/-
bergdb 030-29: Java's record of a walked node (`recOf`, DnbJava.lean) by
what the keys through it do: four klongs for each delete that reaches its
last segment through it (and `deleteBelow`, and a segment tree root's height
as its collapses), a klong for each put that ends at it, and its new segment
trees (`fresh`): one entry for each compare value of the puts whose next
segment it lacks, with their keys in order, and a klong for each.
-/
import Contract.Proof.DnbTree

namespace Contract.PE

open DNB

/-- Key k (a delete if k.2) passes y. -/
def passK (s : Tree) (r y : NodeId) (k : Key × Bool) : Bool := decide (y ∈ pathOf s r k.1)

/-- A delete through y that reaches its last segment. -/
def dlP (s : Tree) (r y : NodeId) (k : Key × Bool) : Bool :=
  passK s r y k && k.2 && (endOf s r k.1).2.2 == .last

/-- A put that ends at y. -/
def peP (s : Tree) (r y : NodeId) (k : Key × Bool) : Bool :=
  passK s r y k && !k.2 && (endOf s r k.1).2.2 == .last && (endOf s r k.1).1 == y

/-- A put whose next segment y lacks. -/
def pfP (s : Tree) (r y : NodeId) (k : Key × Bool) : Bool :=
  passK s r y k && !k.2 && (endOf s r k.1).2.2 == .fresh && (endOf s r k.1).1 == y

/-- The compare value of the segment where key k's walk ends. -/
def cvF (s : Tree) (r : NodeId) (k : Key × Bool) : Nat := k.1[(endOf s r k.1).2.1]?.getD 0

/-- What the proof needs of a record's new segment trees. -/
def FreshOk (s : Tree) (r y : NodeId) (kd : List (Key × Bool)) (w : Walked) : Prop :=
  (w.fresh.map (·.1)).Nodup ∧
  (∀ c, c ∈ w.fresh.map (·.1) ↔ ∃ k ∈ kd, pfP s r y k = true ∧ cvF s r k = c) ∧
  (∀ q ∈ w.fresh, q.2 = ((kd.filter (pfP s r y)).filter (fun k => cvF s r k == q.1)).map (·.1)) ∧
  (w.fresh ≠ [] → ∃ k ∈ kd, pfP s r y k = true ∧ w.freshLevel = (endOf s r k.1).2.1)

theorem filter_append_single {α : Type} (l : List α) (a : α) (p : α → Bool) :
    (l ++ [a]).filter p = l.filter p ++ (if p a then [a] else []) := by
  rw [List.filter_append]; cases h : p a <;> simp [h]

/-- What the record w of node y (key node n) holds after the keys kd. -/
structure RI (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (n : KNode) (kd : List (Key × Bool))
    (w : Walked) : Prop where
  size : w.size = n.ks.length
  dead : w.dead = deadCount n.ks
  del : w.deleteBelow = kd.any (dlP s r y)
  col : w.collapses = (if kd.any (dlP s r y) && E.pleaf y then E.col y else 0)
  klongs : w.klongs = (kd.filter (peP s r y)).length + 4 * (kd.filter (dlP s r y)).length + w.fresh.length
  fresh : FreshOk s r y kd w

theorem any_append_single {α : Type} (l : List α) (a : α) (p : α → Bool) :
    (l ++ [a]).any p = (l.any p || p a) := by simp [List.any_append]

theorem freshOk_same {s : Tree} {r y : NodeId} {kd : List (Key × Bool)} {k : Key × Bool} {w w' : Walked}
    (h : FreshOk s r y kd w) (hf : w'.fresh = w.fresh) (hl : w'.freshLevel = w.freshLevel)
    (hp : pfP s r y k = false) : FreshOk s r y (kd ++ [k]) w' := by
  obtain ⟨hnd, hmem, hq, hfl⟩ := h
  rw [FreshOk, hf, hl]
  refine ⟨hnd, ?_, ?_, ?_⟩
  · intro c; rw [hmem c]
    constructor
    · rintro ⟨k', hk', h1, h2⟩; exact ⟨k', List.mem_append_left _ hk', h1, h2⟩
    · rintro ⟨k', hk', h1, h2⟩
      rcases List.mem_append.mp hk' with hk' | hk'
      · exact ⟨k', hk', h1, h2⟩
      · simp only [List.mem_singleton] at hk'; subst hk'; rw [hp] at h1; cases h1
  · intro q hq'; rw [hq q hq', filter_append_single]; simp [hp]
  · intro h; obtain ⟨k', hk', h4, h5⟩ := hfl h; exact ⟨k', List.mem_append_left _ hk', h4, h5⟩

theorem ri_same {s : Tree} {r : NodeId} {E : TreeFn} {y : NodeId} {n : KNode} {kd : List (Key × Bool)}
    {k : Key × Bool} {w : Walked} (h : RI s r E y n kd w) (h1 : dlP s r y k = false)
    (h2 : peP s r y k = false) (h3 : pfP s r y k = false) : RI s r E y n (kd ++ [k]) w := by
  obtain ⟨hsz, hdd, hdb, hco, hkl, hfr⟩ := h
  refine ⟨hsz, hdd, ?_, ?_, ?_, freshOk_same hfr rfl rfl h3⟩
  · rw [hdb, any_append_single, h1, Bool.or_false]
  · rw [hco, any_append_single, h1, Bool.or_false]
  · rw [hkl, filter_append_single, filter_append_single, h1, h2]; simp

/-- The new segment tree of a put whose next segment y lacks: `addFresh` keeps
`RI`. -/
theorem ri_fresh {s : Tree} {r : NodeId} {E : TreeFn} {y : NodeId} {n : KNode} {kd : List (Key × Bool)}
    {w : Walked} {key : Key} {j : Nat} (h : RI s r E y n kd w) (h1 : dlP s r y (key, false) = false)
    (h2 : peP s r y (key, false) = false) (h3 : pfP s r y (key, false) = true)
    (hcv : cvF s r (key, false) = key[j]?.getD 0) (hj : (endOf s r key).2.1 = j) :
    RI s r E y n (kd ++ [(key, false)]) (Walked.addFresh key j w) := by
  obtain ⟨hsz, hdd, hdb, hco, hkl, hnd, hmem, hq, hfl⟩ := h
  set c := key[j]?.getD 0 with hc
  -- w1: the record with the fresh level set if it had no new tree
  set w1 : Walked := if w.fresh.isEmpty then { w with freshLevel := j } else w with hw1
  have e1 : w1.fresh = w.fresh ∧ w1.klongs = w.klongs ∧ w1.size = w.size ∧ w1.dead = w.dead ∧
      w1.deleteBelow = w.deleteBelow ∧ w1.collapses = w.collapses := by
    rw [hw1]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfl1 : w.fresh ≠ [] → w1.freshLevel = w.freshLevel := by
    intro hne; rw [hw1]
    have : w.fresh.isEmpty = false := by simpa using hne
    simp [this]
  have hfl2 : w.fresh = [] → w1.freshLevel = j := by
    intro he; rw [hw1]; simp [he]
  have hadd : Walked.addFresh key j w =
      if w1.fresh.any (fun q => q.1 == c) then
        { w1 with fresh := w1.fresh.map (fun q => if q.1 == c then (q.1, q.2 ++ [key]) else q) }
      else { w1 with fresh := w1.fresh ++ [(c, [key])], klongs := w1.klongs + 1 } := rfl
  have hdb' : kd.any (dlP s r y) = (kd ++ [(key, false)]).any (dlP s r y) := by
    rw [any_append_single, h1, Bool.or_false]
  have hpe' : (kd ++ [(key, false)]).filter (peP s r y) = kd.filter (peP s r y) := by
    rw [filter_append_single, h2]; simp
  have hdl' : (kd ++ [(key, false)]).filter (dlP s r y) = kd.filter (dlP s r y) := by
    rw [filter_append_single, h1]; simp
  have hpf' : (kd ++ [(key, false)]).filter (pfP s r y) = kd.filter (pfP s r y) ++ [(key, false)] := by
    rw [filter_append_single, h3]; simp
  rw [hadd, e1.1]
  by_cases hany : w.fresh.any (fun q => q.1 == c) = true
  · simp only [hany, ite_true]
    have hcm : c ∈ w.fresh.map (·.1) := by
      obtain ⟨q, hq', hqc⟩ := List.any_eq_true.mp hany
      exact List.mem_map.mpr ⟨q, hq', by simpa using hqc⟩
    refine ⟨e1.2.2.1.trans hsz, e1.2.2.2.1.trans hdd, ?_, ?_, ?_, ?_⟩
    · show w1.deleteBelow = _; rw [e1.2.2.2.2.1, hdb, hdb']
    · show w1.collapses = _; rw [e1.2.2.2.2.2, hco, hdb']
    · show w1.klongs = _
      rw [e1.2.1, hkl, hpe', hdl', List.length_map]
    · have hmf : (w.fresh.map (fun q => if q.1 == c then (q.1, q.2 ++ [key]) else q)).map (·.1) =
          w.fresh.map (·.1) := by
        rw [List.map_map]; congr 1; funext q; simp only [Function.comp_apply]; split <;> rfl
      refine ⟨by rw [hmf]; exact hnd, ?_, ?_, ?_⟩
      · intro c'; rw [hmf, hmem c']
        constructor
        · rintro ⟨k', hk', h4, h5⟩; exact ⟨k', List.mem_append_left _ hk', h4, h5⟩
        · rintro ⟨k', hk', h4, h5⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact ⟨k', hk', h4, h5⟩
          · simp only [List.mem_singleton] at hk'; subst hk'
            rw [hcv] at h5; rw [← h5]; exact (hmem c).mp hcm
      · intro q hq'
        obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq'
        rw [hpf', List.filter_append, List.map_append]
        by_cases hqc : q0.1 = c
        · simp only [hqc, beq_self_eq_true, ite_true]
          rw [hq q0 hq0, hqc]
          simp [hcv]
        · have : (q0.1 == c) = false := by simpa using hqc
          simp only [this, Bool.false_eq_true, ite_false]
          rw [hq q0 hq0]
          simp [hcv, Ne.symm hqc]
      · intro _
        have hne : w.fresh ≠ [] := by
          intro he; rw [he] at hany; simp at hany
        obtain ⟨k', hk', h4, h5⟩ := hfl hne
        refine ⟨k', List.mem_append_left _ hk', h4, ?_⟩
        show w1.freshLevel = _
        rw [hfl1 hne, h5]
  · simp only [hany, Bool.false_eq_true, ite_false]
    have hcm : c ∉ w.fresh.map (·.1) := by
      intro hm
      obtain ⟨q, hq', hqc⟩ := List.mem_map.mp hm
      apply hany
      exact List.any_eq_true.mpr ⟨q, hq', by simp [hqc]⟩
    refine ⟨e1.2.2.1.trans hsz, e1.2.2.2.1.trans hdd, ?_, ?_, ?_, ?_⟩
    · show w1.deleteBelow = _; rw [e1.2.2.2.2.1, hdb, hdb']
    · show w1.collapses = _; rw [e1.2.2.2.2.2, hco, hdb']
    · show w1.klongs + 1 = _
      rw [e1.2.1, hkl, hpe', hdl', List.length_append, List.length_singleton]
      ring
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        exact fun he => hcm (he ▸ ha)
      · intro c'
        rw [List.map_append, List.mem_append, hmem c']
        constructor
        · rintro (⟨k', hk', h4, h5⟩ | hc')
          · exact ⟨k', List.mem_append_left _ hk', h4, h5⟩
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc'
            subst hc'
            exact ⟨(key, false), by simp, h3, hcv⟩
        · rintro ⟨k', hk', h4, h5⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact Or.inl ⟨k', hk', h4, h5⟩
          · simp only [List.mem_singleton] at hk'; subst hk'
            right; simp [← h5, hcv]
      · intro q hq'
        rw [hpf', List.filter_append, List.map_append]
        rcases List.mem_append.mp hq' with hq' | hq'
        · have hqc : q.1 ≠ c := fun he => hcm (he ▸ List.mem_map_of_mem hq')
          rw [hq q hq']
          simp [hcv, Ne.symm hqc]
        · simp only [List.mem_singleton] at hq'
          subst hq'
          have hnone : (kd.filter (pfP s r y)).filter (fun k => cvF s r k == c) = [] := by
            rw [List.filter_eq_nil_iff]
            intro k' hk'
            obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk'
            intro he
            apply hcm
            rw [hmem c]
            exact ⟨k', hk1, hk2, by simpa using he⟩
          simp [hnone, hcv]
      · intro _
        by_cases hne : w.fresh = []
        · refine ⟨(key, false), by simp, h3, ?_⟩
          show w1.freshLevel = _
          rw [hfl2 hne, hj]
        · obtain ⟨k', hk', h4, h5⟩ := hfl hne
          refine ⟨k', List.mem_append_left _ hk', h4, ?_⟩
          show w1.freshLevel = _
          rw [hfl1 hne, h5]

/-- **One key's change of the record** keeps `RI`. -/
theorem ri_step (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (n : KNode) (kd : List (Key × Bool))
    (w : Walked) (h : RI s r E y n kd w) (k : Key × Bool) :
    RI s r E y n (kd ++ [k]) (stepR s r E y w k) := by
  obtain ⟨key, del⟩ := k
  unfold stepR
  by_cases hp : y ∈ pathOf s r key
  · simp only [hp, ite_true]
    have hpk : passK s r y (key, del) = true := by simp [passK, hp]
    rcases he : endOf s r key with ⟨z, j, e⟩
    cases e with
    | stop =>
      exact ri_same h (by simp [dlP, he]) (by simp [peP, he]) (by simp [pfP, he])
    | last =>
      cases del with
      | true =>
        have h1 : dlP s r y (key, true) = true := by simp [dlP, hpk, he]
        have h2 : peP s r y (key, true) = false := by simp [peP]
        have h3 : pfP s r y (key, true) = false := by simp [pfP]
        obtain ⟨hsz, hdd, hdb, hco, hkl, hfr⟩ := h
        have hd : effAt E y key true (z, j, .last) w = delStep E y w := rfl
        rw [hd]
        refine ⟨hsz, hdd, ?_, ?_, ?_, freshOk_same hfr rfl rfl h3⟩
        · show true = _
          rw [any_append_single, h1, Bool.or_true]
        · show (if E.pleaf y then max w.collapses (E.col y) else w.collapses) = _
          rw [any_append_single, h1, Bool.or_true, Bool.true_and, hco]
          cases E.pleaf y
          · simp
          · simp only [ite_true, Bool.and_true]
            split <;> simp
        · show w.klongs + 4 = _
          rw [hkl, filter_append_single, filter_append_single, h1, h2]
          show _ = _ + _ + (delStep E y w).fresh.length
          simp only [delStep, ite_true, Bool.false_eq_true, ite_false, List.append_nil,
            List.length_append, List.length_singleton]
          ring
      | false =>
        have h1 : dlP s r y (key, false) = false := by simp [dlP]
        have h3 : pfP s r y (key, false) = false := by simp [pfP, he]
        by_cases hyz : y = z
        · subst hyz
          have h2 : peP s r y (key, false) = true := by simp [peP, hpk, he]
          have hd : effAt E y key false (y, j, .last) w = { w with klongs := w.klongs + 1 } := by
            simp [effAt]
          rw [hd]
          obtain ⟨hsz, hdd, hdb, hco, hkl, hfr⟩ := h
          refine ⟨hsz, hdd, ?_, ?_, ?_, freshOk_same hfr rfl rfl h3⟩
          · show w.deleteBelow = _; rw [hdb, any_append_single, h1, Bool.or_false]
          · show w.collapses = _; rw [hco, any_append_single, h1, Bool.or_false]
          · show w.klongs + 1 = _
            rw [hkl, filter_append_single, filter_append_single, h1, h2]
            simp only [ite_true, Bool.false_eq_true, ite_false, List.append_nil, List.length_append,
              List.length_singleton]
            ring
        · have hd : effAt E y key false (z, j, .last) w = w := by simp [effAt, hyz]
          rw [hd]
          exact ri_same h h1 (by simp [peP, he, Ne.symm hyz]) h3
    | fresh =>
      have h1 : dlP s r y (key, del) = false := by simp [dlP, he]
      have h2 : peP s r y (key, del) = false := by simp [peP, he]
      cases del with
      | true =>
        have hd : effAt E y key true (z, j, .fresh) w = w := by simp [effAt]
        rw [hd]
        exact ri_same h h1 h2 (by simp [pfP])
      | false =>
        by_cases hyz : y = z
        · subst hyz
          have h3 : pfP s r y (key, false) = true := by simp [pfP, hpk, he]
          have hcv : cvF s r (key, false) = key[j]?.getD 0 := by simp [cvF, he]
          have hj : (endOf s r (key, false).1).2.1 = j := by simp [he]
          have hd : effAt E y key false (y, j, .fresh) w = Walked.addFresh key j w := by simp [effAt]
          rw [hd]
          exact ri_fresh h h1 h2 h3 hcv hj
        · have hd : effAt E y key false (z, j, .fresh) w = w := by simp [effAt, hyz]
          rw [hd]
          exact ri_same h h1 h2 (by simp [pfP, he, Ne.symm hyz])
  · simp only [hp, ite_false]
    exact ri_same h (by simp [dlP, passK, hp]) (by simp [peP, passK, hp]) (by simp [pfP, passK, hp])

/-- **The record of node y after the keys kd** (key node n): `RI`. -/
theorem recOf_RI (s : Tree) (r : NodeId) (E : TreeFn) (y : NodeId) (n : KNode)
    (hn : DNB.getKey s y = some n) : ∀ (kd : List (Key × Bool)),
    RI s r E y n kd (recOf s r E y kd) := by
  intro kd
  induction kd using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [recOf, initR, hn, FreshOk]
  | append_singleton kd k ih =>
    rw [recOf_append]
    exact ri_step s r E y n kd _ ih k

end Contract.PE
