/-
The merge's parent at the level of a node's live klongs (bergdb 024-22,
`OpTreeOK`): `mergeIdx` picks, for each compare value it returns, the last
physical key klong of it that the bitmap does not delete (`mergeIdx_last`),
so that klong is the live one (`keyLookup_of_last`), and pointing it in place
changes the live lookup at that compare value only
(`KNode.repoint_last_live_lookup`).
-/
import SIS.Tree.WriterTreePut2
import SIS.Tree.PhysicalSelection

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Klong i is a key klong of compare value cv that the bitmap keeps, and every
later key klong of cv is deleted. -/
def LastLive (ks : List Klong) (del : List Nat) (i cv : Nat) : Prop :=
  (∃ y, ks[i]? = some (.key cv y)) ∧ i ∉ del ∧
    ∀ j y, i < j → ks[j]? = some (.key cv y) → j ∈ del

/-- What `mergeIdx`'s fold has chosen so far is the last live klong of its
compare value in the klongs seen. -/
def MergeLastOK (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) : Prop :=
  (∀ i, acc.1 = some i → LastLive ks del i cx) ∧
  (∀ i cv, acc.2.1 = some (i, cv) → LastLive ks del i cv ∧ cx < cv) ∧
  (∀ i cv, acc.2.2 = some (i, cv) → LastLive ks del i cv ∧ cv < cx)

theorem getElem?_append_single_lt {α : Type} (l : List α) (a : α) (j : Nat) (hj : j < l.length) :
    (l ++ [a])[j]? = l[j]? := List.getElem?_append_left hj

theorem getElem?_append_single_eq {α : Type} (l : List α) (a : α) :
    (l ++ [a])[l.length]? = some a := by simp

theorem getElem?_append_single_gt {α : Type} (l : List α) (a : α) (j : Nat) (hj : l.length < j) :
    (l ++ [a])[j]? = none := by
  rw [List.getElem?_eq_none_iff]; simp; omega

/-- A klong added at the end that is no live key klong of cv keeps klong i the
last live one of cv. -/
theorem LastLive.append (ks : List Klong) (del : List Nat) (i cv : Nat) (k : Klong)
    (h : LastLive ks del i cv) (hk : ∀ y, k = .key cv y → ks.length ∈ del) :
    LastLive (ks ++ [k]) del i cv := by
  obtain ⟨⟨y0, hy0⟩, hd, hl⟩ := h
  have hi : i < ks.length := by
    rw [List.getElem?_eq_some_iff] at hy0; exact hy0.1
  refine ⟨⟨y0, by rw [getElem?_append_single_lt _ _ _ hi]; exact hy0⟩, hd, ?_⟩
  intro j y hij hj
  rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
  · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact hl j y hij hj
  · subst h1; rw [getElem?_append_single_eq] at hj
    simp only [Option.some.injEq] at hj
    exact hk y hj
  · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj

/-- A live key klong added at the end is the last live one of its compare
value. -/
theorem LastLive.new (ks : List Klong) (del : List Nat) (cv : Nat) (y : NodeId)
    (hd : ks.length ∉ del) : LastLive (ks ++ [.key cv y]) del ks.length cv := by
  refine ⟨⟨y, getElem?_append_single_eq _ _⟩, hd, ?_⟩
  intro j y' hij hj
  rw [getElem?_append_single_gt _ _ _ hij] at hj; cases hj

theorem mergeLastOK_step (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) (k : Klong)
    (ha : MergeLastOK ks del cx acc) :
    MergeLastOK (ks ++ [k]) del cx (mergePhysicalStep del cx acc (k, ks.length)) := by
  obtain ⟨h1, h2, h3⟩ := ha
  -- a klong that is no live key klong of cv keeps the old choices
  have keep : ∀ cv, (∀ y, k = .key cv y → ks.length ∈ del) →
      ∀ i, LastLive ks del i cv → LastLive (ks ++ [k]) del i cv :=
    fun cv hk i h => LastLive.append ks del i cv k h hk
  cases k with
  | time t =>
    exact ⟨fun i h => keep cx (fun y h' => by cases h') i (h1 i h),
      fun i cv h => ⟨keep cv (fun y h' => by cases h') i (h2 i cv h).1, (h2 i cv h).2⟩,
      fun i cv h => ⟨keep cv (fun y h' => by cases h') i (h3 i cv h).1, (h3 i cv h).2⟩⟩
  | del b =>
    exact ⟨fun i h => keep cx (fun y h' => by cases h') i (h1 i h),
      fun i cv h => ⟨keep cv (fun y h' => by cases h') i (h2 i cv h).1, (h2 i cv h).2⟩,
      fun i cv h => ⟨keep cv (fun y h' => by cases h') i (h3 i cv h).1, (h3 i cv h).2⟩⟩
  | key cv' y' =>
    by_cases hd : ks.length ∈ del
    · have hk : ∀ cv, ∀ y, Klong.key cv' y' = .key cv y → ks.length ∈ del := fun _ _ _ => hd
      simp only [mergePhysicalStep, List.contains_eq_mem, hd, decide_true, ↓reduceIte]
      exact ⟨fun i h => keep cx (hk cx) i (h1 i h),
        fun i cv h => ⟨keep cv (hk cv) i (h2 i cv h).1, (h2 i cv h).2⟩,
        fun i cv h => ⟨keep cv (hk cv) i (h3 i cv h).1, (h3 i cv h).2⟩⟩
    · have hne : ∀ cv, cv ≠ cv' → ∀ y, Klong.key cv' y' = .key cv y → ks.length ∈ del := by
        intro cv hcv y h; simp only [Klong.key.injEq] at h; exact absurd h.1.symm hcv
      simp only [mergePhysicalStep, List.contains_eq_mem, hd, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      by_cases hc : cv' = cx
      · subst hc
        simp only [beq_self_eq_true, ↓reduceIte]
        refine ⟨fun i h => ?_, fun i cv h => ?_, fun i cv h => ?_⟩
        · simp only [Option.some.injEq] at h; subst h; exact LastLive.new ks del cv' y' hd
        · obtain ⟨hl, hlt⟩ := h2 i cv h
          exact ⟨keep cv (hne cv (by omega)) i hl, hlt⟩
        · obtain ⟨hl, hlt⟩ := h3 i cv h
          exact ⟨keep cv (hne cv (by omega)) i hl, hlt⟩
      · have hb : (cv' == cx) = false := by simpa using hc
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : cx < cv'
        · simp only [hlt, ↓reduceIte]
          refine ⟨fun i h => keep cx (hne cx (Ne.symm hc)) i (h1 i h), fun i cv h => ?_,
            fun i cv h => ?_⟩
          · simp only at h
            cases hac : acc.2.1 with
            | none =>
              rw [hac] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨LastLive.new ks del cv' y' hd, hlt⟩
            | some pa =>
              rcases pa with ⟨ia, cva⟩
              rw [hac] at h
              simp only at h
              by_cases hle : cv' ≤ cva
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨LastLive.new ks del cv' y' hd, hlt⟩
              · simp only [hle, ↓reduceIte] at h
                obtain ⟨hl, hlt'⟩ := h2 ia cva hac
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨keep cva (hne cva (by omega)) ia hl, hlt'⟩
          · obtain ⟨hl, hlt'⟩ := h3 i cv h
            exact ⟨keep cv (hne cv (by omega)) i hl, hlt'⟩
        · simp only [hlt, ↓reduceIte]
          have hgt : cv' < cx := by omega
          refine ⟨fun i h => keep cx (hne cx (Ne.symm hc)) i (h1 i h), fun i cv h => ?_,
            fun i cv h => ?_⟩
          · obtain ⟨hl, hlt'⟩ := h2 i cv h
            exact ⟨keep cv (hne cv (by omega)) i hl, hlt'⟩
          · simp only at h
            cases hac : acc.2.2 with
            | none =>
              rw [hac] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨LastLive.new ks del cv' y' hd, hgt⟩
            | some pb =>
              rcases pb with ⟨ib, cvb⟩
              rw [hac] at h
              simp only at h
              by_cases hle : cvb ≤ cv'
              · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨LastLive.new ks del cv' y' hd, hgt⟩
              · simp only [hle, ↓reduceIte] at h
                obtain ⟨hl, hlt'⟩ := h3 ib cvb hac
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨keep cvb (hne cvb (by omega)) ib hl, hlt'⟩

theorem mergeLastOK_fold (del : List Nat) (cx : Nat) (ks : List Klong) :
    MergeLastOK ks del cx (ks.zipIdx.foldl (mergePhysicalStep del cx) (none, none, none)) := by
  have key : ∀ rs : List Klong, MergeLastOK rs.reverse del cx
      (rs.reverse.zipIdx.foldl (mergePhysicalStep del cx) (none, none, none)) := by
    intro rs
    induction rs with
    | nil =>
      refine ⟨fun i h => ?_, fun i cv h => ?_, fun i cv h => ?_⟩ <;> cases h
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact mergeLastOK_step rs.reverse del cx _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- `mergeIdx`'s choices are the last live klongs of their compare values. -/
theorem mergeIdx_last (n : KNode) (cx : Nat) : MergeLastOK n.ks n.lastBitmap cx (mergeIdx n cx) :=
  mergeLastOK_fold n.lastBitmap cx n.ks

theorem keyLookup_append_single (ks : List Klong) (del : List Nat) (c : Nat) (k : Klong) :
    keyLookup (ks ++ [k]) del c = keyLookupStep del c (keyLookup ks del c) (k, ks.length) := by
  unfold keyLookup
  rw [List.zipIdx_append, List.foldl_append]
  simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]

/-- The last live key klong of c gives the lookup of c. -/
theorem keyLookup_of_last (del : List Nat) (c : Nat) (ks : List Klong) (i : Nat) (y : NodeId)
    (hk : ks[i]? = some (.key c y)) (hl : LastLive ks del i c) : keyLookup ks del c = some y := by
  have key : ∀ rs : List Klong, ∀ i y, rs.reverse[i]? = some (.key c y) →
      LastLive rs.reverse del i c → keyLookup rs.reverse del c = some y := by
    intro rs
    induction rs with
    | nil => intro i y h; simp at h
    | cons k rs ih =>
      intro i y h hl
      rw [List.reverse_cons] at h hl ⊢
      rw [keyLookup_append_single]
      obtain ⟨_, hd, hlast⟩ := hl
      rcases Nat.lt_trichotomy i rs.reverse.length with h1 | h1 | h1
      · rw [getElem?_append_single_lt _ _ _ h1] at h
        have hl' : LastLive rs.reverse del i c := by
          refine ⟨⟨y, h⟩, hd, fun j y' hij hj => hlast j y' hij ?_⟩
          have hj' : j < rs.reverse.length := by
            rw [List.getElem?_eq_some_iff] at hj; exact hj.1
          rw [getElem?_append_single_lt _ _ _ hj']; exact hj
        rw [ih i y h hl']
        cases k with
        | key a z =>
          show (if del.contains rs.reverse.length then some y
            else if a == c then some z else some y) = some y
          by_cases hdel : rs.reverse.length ∈ del
          · have : del.contains rs.reverse.length = true := by simpa using hdel
            rw [this]; rfl
          · have hac : a ≠ c := by
              intro hac
              subst hac
              exact hdel (hlast _ z h1 (getElem?_append_single_eq _ _))
            have h2 : del.contains rs.reverse.length = false := by simpa using hdel
            have h3 : (a == c) = false := by simpa using hac
            rw [h2, h3]; rfl
        | time t => rfl
        | del b => rfl
      · subst h1
        rw [getElem?_append_single_eq] at h
        simp only [Option.some.injEq] at h
        subst h
        show (if del.contains rs.reverse.length then keyLookup rs.reverse del c
          else if c == c then some y else keyLookup rs.reverse del c) = some y
        have h2 : del.contains rs.reverse.length = false := by simpa using hd
        rw [h2]; simp
      · rw [getElem?_append_single_gt _ _ _ h1] at h; cases h
  have := key ks.reverse i y (by rw [List.reverse_reverse]; exact hk)
    (by rw [List.reverse_reverse]; exact hl)
  rwa [List.reverse_reverse] at this

/-- A compare value's last live klong pointed in place to y: the live lookup
of that compare value is y, of the others as before. -/
theorem KNode.repoint_last_live_lookup (n : KNode) (i c0 : Nat) (old y : NodeId)
    (hk : n.ks[i]? = some (.key c0 old)) (hl : LastLive n.ks n.lastBitmap i c0) (c : Nat) :
    (n.repoint i y).live.lookup c = if c = c0 then some y else n.live.lookup c := by
  have hrep : n.repoint i y = { n with ks := n.ks.set i (.key c0 y) } := by
    unfold KNode.repoint; rw [hk]; rfl
  rw [hrep, KNode.live_lookup, KNode.live_lookup]
  have hdel : ({ n with ks := n.ks.set i (.key c0 y) } : KNode).lastBitmap = n.lastBitmap :=
    lastBitmapOf_set_key n.ks i c0 y ⟨old, hk⟩
  rw [hdel]
  simp only
  have hi : i < n.ks.length := by rw [List.getElem?_eq_some_iff] at hk; exact hk.1
  by_cases hc : c = c0
  · subst hc
    simp only [↓reduceIte]
    apply keyLookup_of_last _ _ _ i
    · rw [List.getElem?_set_self hi]
    · obtain ⟨_, hd, hlast⟩ := hl
      refine ⟨⟨y, by rw [List.getElem?_set_self hi]⟩, hd, fun j y' hij hj => ?_⟩
      rw [List.getElem?_set_ne (by omega)] at hj
      exact hlast j y' hij hj
  · simp only [hc, ↓reduceIte]
    unfold keyLookup
    have hz : (n.ks.set i (Klong.key c0 y)).zipIdx =
        n.ks.zipIdx.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q) := by
      apply List.ext_getElem
      · simp
      · intro j h1 h2
        simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_set, Nat.zero_add]
        by_cases hji : j = i
        · simp [hji]
        · simp [hji, Ne.symm hji]
    rw [hz, List.foldl_map]
    apply foldl_congr_mem
    intro v q hq
    rcases q with ⟨k, j⟩
    by_cases hj : j = i
    · subst hj
      have : k = .key c0 old := by
        have := List.mem_zipIdx_iff_getElem?.mp hq
        rw [hk] at this; simp only [Option.some.injEq] at this; exact this.symm
      subst this
      simp only [↓reduceIte, keyLookupStep]
      have hb : (c0 == c) = false := by simpa using Ne.symm hc
      simp [hb]
    · simp [hj]

/-- Klong i stays the last live klong of c when its klong stays, the new
bitmap keeps it, and every later key klong of c is deleted by the new bitmap
or was one of the old list deleted by both. -/
theorem LastLive.mono (ks ks' : List Klong) (del del' : List Nat) (i c : Nat)
    (h : LastLive ks del i c) (hi : ks'[i]? = ks[i]?) (hd : i ∉ del')
    (hj : ∀ j y, i < j → ks'[j]? = some (.key c y) →
      j ∈ del' ∨ (ks[j]? = some (.key c y) ∧ (j ∈ del → j ∈ del'))) :
    LastLive ks' del' i c := by
  obtain ⟨⟨y0, hy0⟩, _, hl⟩ := h
  refine ⟨⟨y0, by rw [hi]; exact hy0⟩, hd, fun j y hij hjk => ?_⟩
  rcases hj j y hij hjk with h1 | ⟨h1, h2⟩
  · exact h1
  · exact h2 (hl j y hij h1)

/-- An added klong other than a key klong of c leaves the old indices and
adds no key klong of c. -/
theorem KNode.add_getElem?_key (n : KNode) (t : Time) (k : Klong) (c : Nat)
    (hk : ∀ y, k ≠ .key c y) (j : Nat) (y : NodeId)
    (h : (n.add t k).ks[j]? = some (.key c y)) : n.ks[j]? = some (.key c y) := by
  have hex : ∃ extra, (n.add t k).ks = n.ks ++ extra ∧ ∀ e ∈ extra, e = .time t ∨ e = k := by
    rcases n.add_ks t k with he | he
    · exact ⟨[.time t, k], he, by simp⟩
    · exact ⟨[k], he, by simp⟩
  obtain ⟨extra, he, hex⟩ := hex
  rw [he] at h
  by_cases hj : j < n.ks.length
  · rwa [List.getElem?_append_left hj] at h
  · rw [List.getElem?_append_right (by omega)] at h
    have hm := List.mem_of_getElem? h
    rcases hex _ hm with h1 | h1
    · cases h1
    · exact absurd h1.symm (hk y)

theorem KNode.add_getElem?_lt (n : KNode) (t : Time) (k : Klong) (j : Nat) (hj : j < n.ks.length) :
    (n.add t k).ks[j]? = n.ks[j]? := by
  rcases n.add_ks t k with he | he <;> rw [he, List.getElem?_append_left hj]

/-- The merge's parent with the right child's compare value deleted: klong i
of compare value c ≠ cR stays the last live one of c. -/
theorem LastLive.add_delete (n : KNode) (t : Time) (i c cR : Nat) (hc : c ≠ cR)
    (h : LastLive n.ks n.lastBitmap i c) :
    LastLive (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cR)))).ks
      (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cR)))).lastBitmap i c := by
  have hi : i < n.ks.length := by
    obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
    rw [List.getElem?_eq_some_iff] at hy0; exact hy0.1
  rw [KNode.add_delete_lastBitmap]
  apply LastLive.mono n.ks _ n.lastBitmap _ i c h (n.add_getElem?_lt t _ i hi)
  · intro hm
    rcases (mem_bitsUnion_iff _ _ _).mp hm with h1 | h1
    · exact h.2.1 h1
    · obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cR i).mp h1
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
      rw [List.mem_zipIdx_iff_getElem?.mp hy] at hy0
      simp only [Option.some.injEq, Klong.key.injEq] at hy0
      exact hc hy0.1.symm
  · intro j y _ hj
    have := n.add_getElem?_key t _ c (fun y h => by cases h) j y hj
    exact Or.inr ⟨this, fun hd => (mem_bitsUnion_iff _ _ _).mpr (Or.inl hd)⟩

/-- The same with the transaction's own bitmap set in place. -/
theorem LastLive.setAt_delete (n : KNode) (i c cR : Nat) (old : List Nat) (hc : c ≠ cR)
    (hlast : n.ks.getLast? = some (.del old)) (h : LastLive n.ks n.lastBitmap i c) :
    LastLive (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cR)))).ks
      (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cR)))).lastBitmap i c := by
  have hlen : 0 < n.ks.length := by
    cases hk : n.ks with
    | nil => rw [hk] at hlast; simp at hlast
    | cons _ _ => simp
  have hlb : (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cR)))).lastBitmap =
      bitsUnion n.lastBitmap (n.bitsOf cR) := by
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
    simp only [KNode.setAt, KNode.lastBitmap, KNode.size]
    rw [hpre]
    have : (pre ++ [Klong.del old]).length - 1 = pre.length := by simp
    rw [this, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    simp [lastBitmapOf, List.foldl_append]
  rw [hlb]
  have hi : i < n.ks.length - 1 := by
    obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
    have h1 := hy0
    rw [List.getElem?_eq_some_iff] at h1
    obtain ⟨hil, _⟩ := h1
    rcases Nat.lt_or_ge i (n.ks.length - 1) with hlt | hge
    · exact hlt
    · have : i = n.ks.length - 1 := by omega
      subst this
      rw [List.getLast?_eq_getElem?] at hlast
      rw [hlast] at hy0; cases hy0
  apply LastLive.mono n.ks _ n.lastBitmap _ i c h
  · simp only [KNode.setAt, KNode.size]; rw [List.getElem?_set_ne (by omega)]
  · intro hm
    rcases (mem_bitsUnion_iff _ _ _).mp hm with h1 | h1
    · exact h.2.1 h1
    · obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cR i).mp h1
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
      rw [List.mem_zipIdx_iff_getElem?.mp hy] at hy0
      simp only [Option.some.injEq, Klong.key.injEq] at hy0
      exact hc hy0.1.symm
  · intro j y _ hj
    simp only [KNode.setAt, KNode.size] at hj
    by_cases hjl : j = n.ks.length - 1
    · subst hjl
      rw [List.getElem?_set_self (by omega)] at hj; cases hj
    · rw [List.getElem?_set_ne (Ne.symm hjl)] at hj
      exact Or.inr ⟨hj, fun hd => (mem_bitsUnion_iff _ _ _).mpr (Or.inl hd)⟩

/-- A key klong of another compare value added: klong i stays the last live
one of c. -/
theorem LastLive.add_key (n : KNode) (t : Time) (i c a : Nat) (z : NodeId) (ha : a ≠ c)
    (h : LastLive n.ks n.lastBitmap i c) :
    LastLive (n.add t (.key a z)).ks (n.add t (.key a z)).lastBitmap i c := by
  have hi : i < n.ks.length := by
    obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
    rw [List.getElem?_eq_some_iff] at hy0; exact hy0.1
  rw [KNode.add_key_lastBitmap]
  apply LastLive.mono n.ks _ n.lastBitmap _ i c h (n.add_getElem?_lt t _ i hi) h.2.1
  intro j y _ hj
  have := n.add_getElem?_key t _ c (fun y h => by
    simp only [Klong.key.injEq] at h; exact ha h.1) j y hj
  exact Or.inr ⟨this, id⟩

/-- Another klong pointed in place: klong i stays the last live one of c. -/
theorem LastLive.repoint (n : KNode) (i c i' c' : Nat) (old y : NodeId) (hc : c' ≠ c)
    (hk' : n.ks[i']? = some (.key c' old)) (h : LastLive n.ks n.lastBitmap i c) :
    LastLive (n.repoint i' y).ks (n.repoint i' y).lastBitmap i c := by
  have hrep : n.repoint i' y = { n with ks := n.ks.set i' (.key c' y) } := by
    unfold KNode.repoint; rw [hk']; rfl
  have hdel : ({ n with ks := n.ks.set i' (.key c' y) } : KNode).lastBitmap = n.lastBitmap :=
    lastBitmapOf_set_key n.ks i' c' y ⟨old, hk'⟩
  rw [hrep, hdel]
  have hii : i ≠ i' := by
    intro he; subst he
    obtain ⟨⟨y0, hy0⟩, _, _⟩ := h
    rw [hk'] at hy0; simp only [Option.some.injEq, Klong.key.injEq] at hy0; exact hc hy0.1
  apply LastLive.mono n.ks _ n.lastBitmap _ i c h
  · simp only; rw [List.getElem?_set_ne (Ne.symm hii)]
  · exact h.2.1
  · intro j z _ hj
    simp only at hj
    by_cases hji : j = i'
    · subst hji
      have hl' : j < n.ks.length := by rw [List.getElem?_eq_some_iff] at hk'; exact hk'.1
      rw [List.getElem?_set_self hl'] at hj
      simp only [Option.some.injEq, Klong.key.injEq] at hj
      exact absurd hj.1 hc
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      exact Or.inr ⟨hj, id⟩

/-- The merge's parent as `mergeParent` writes it when it has room (024-11,
M4): the right child's compare value deleted unless the second new node takes
it, the left one's klong naming m1, and a klong naming m2. -/
def mergeParentNode (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : KNode :=
  let deleteR := match m2 with
    | some (_, g) => g != cR
    | none => true
  let ofTt := pn.lastTime == some tt
  let after (i : Nat) : Bool := match pn.lastTimeIndex with
    | some ti => decide (ti < i)
    | none => false
  let arrayDel := pn.lastBitmap
  let hasTransDel := (match pn.ks.getLast? with
    | some (.del _) => true
    | _ => false) && ofTt
  let union := if deleteR then bitsUnion arrayDel (pn.bitsOf cR) else arrayDel
  let lInPlace := ofTt && after il
  let rInPlace := !deleteR && ofTt && after ir
  let n1 := if !deleteR then pn
    else if hasTransDel then pn.setAt (pn.size - 1) (.del union)
    else pn.add tt (.del union)
  let n2 := if lInPlace then n1.repoint il m1 else n1.add tt (.key cL m1)
  match m2 with
  | some (y, g) => if rInPlace then n2.repoint ir y else n2.add tt (.key (if deleteR then g else cR) y)
  | none => n2

/-- `mergeParentNode` with its three choices free: the transaction's own
bitmap set in place, the left klong pointed in place, the right one. -/
def mpNode (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) : KNode :=
  let deleteR := match m2 with
    | some (_, g) => g != cR
    | none => true
  let union := if deleteR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap
  let n1 := if !deleteR then pn
    else if htd then pn.setAt (pn.size - 1) (.del union)
    else pn.add tt (.del union)
  let n2 := if lip then n1.repoint il m1 else n1.add tt (.key cL m1)
  match m2 with
  | some (y, g) => if rip then n2.repoint ir y else n2.add tt (.key (if deleteR then g else cR) y)
  | none => n2

theorem mergeParentNode_eq (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    mergeParentNode pn tt il cL m1 ir cR m2 = mpNode pn tt il cL m1 ir cR m2
      ((match pn.ks.getLast? with
        | some (.del _) => true
        | _ => false) && pn.lastTime == some tt)
      ((pn.lastTime == some tt) && (match pn.lastTimeIndex with
        | some ti => decide (ti < il)
        | none => false))
      (!(match m2 with
        | some (_, g) => g != cR
        | none => true) && (pn.lastTime == some tt) && (match pn.lastTimeIndex with
        | some ti => decide (ti < ir)
        | none => false)) := rfl

/-- The live klongs of the merge's parent after: the second new node at g, the
first at the left child's compare value, the right one's deleted, the others
as before. -/
theorem mpNode_live_lookup (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (htd lip rip : Bool) (l r : NodeId)
    (hwf : klongsWf pn.ks = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (htdh : htd = true → ∃ old, pn.ks.getLast? = some (.del old))
    (hrip : rip = true → ∀ y g, m2 = some (y, g) → g = cR) (c : Nat) :
    (mpNode pn tt il cL m1 ir cR m2 htd lip rip).live.lookup c =
      match m2 with
      | some (y, g) => if c = g then some y else if c = cL then some m1
          else if c = cR then none else pn.live.lookup c
      | none => if c = cL then some m1 else if c = cR then none else pn.live.lookup c := by
  -- the right child's compare value is live, so deleting it changes the bitmap
  have hRb : ir ∈ pn.bitsOf cR := (pn.mem_bitsOf_iff cR ir).mpr ⟨r, List.mem_zipIdx_iff_getElem?.mpr hR⟩
  have hne : bitsUnion pn.lastBitmap (pn.bitsOf cR) ≠ pn.lastBitmap := by
    intro he
    have : ir ∈ bitsUnion pn.lastBitmap (pn.bitsOf cR) := (mem_bitsUnion_iff _ _ _).mpr (Or.inr hRb)
    rw [he] at this
    exact hRL.2.1 this
  have hil : il < pn.ks.length := by rw [List.getElem?_eq_some_iff] at hL; exact hL.1
  have hir : ir < pn.ks.length := by rw [List.getElem?_eq_some_iff] at hR; exact hR.1
  -- n1: the delete of cR, or nothing
  have hn1 : ∀ (dR : Bool), (dR = true) → ∀ (htd : Bool),
      (htd = true → ∃ old, pn.ks.getLast? = some (.del old)) →
      let n1 := if htd then pn.setAt (pn.size - 1) (.del (bitsUnion pn.lastBitmap (pn.bitsOf cR)))
        else pn.add tt (.del (bitsUnion pn.lastBitmap (pn.bitsOf cR)))
      klongsWf n1.ks = true ∧ n1.ks[il]? = some (.key cL l) ∧ LastLive n1.ks n1.lastBitmap il cL ∧
        ∀ c', n1.live.lookup c' = if c' == cR then none else pn.live.lookup c' := by
    intro dR _ htd hold
    cases htd with
    | true =>
      obtain ⟨old, hlast⟩ := hold rfl
      simp only [↓reduceIte]
      have hil' : il ≠ pn.size - 1 := by
        intro he
        rw [List.getLast?_eq_getElem?] at hlast
        simp only [KNode.size] at he
        rw [← he, hL] at hlast; cases hlast
      refine ⟨KNode.setAt_delete_wf pn cR old hwf hlast, ?_,
        LastLive.setAt_delete pn il cL cR old hc hlast hLL,
        fun c' => KNode.setAt_delete_live_lookup pn cR c' old hlast⟩
      simp only [KNode.setAt]; rw [List.getElem?_set_ne (Ne.symm hil')]; exact hL
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨KNode.add_delete_wf pn tt cR hwf hne, by rw [pn.add_getElem?_lt tt _ il hil]; exact hL,
        LastLive.add_delete pn tt il cL cR hc hLL, fun c' => KNode.add_delete_live_lookup pn tt cR c'⟩
  -- n2 from n1
  have hn2 : ∀ (n1 : KNode), klongsWf n1.ks = true → n1.ks[il]? = some (.key cL l) →
      LastLive n1.ks n1.lastBitmap il cL → ∀ (lip : Bool),
      let n2 := if lip then n1.repoint il m1 else n1.add tt (.key cL m1)
      klongsWf n2.ks = true ∧ ∀ c', n2.live.lookup c' = if c' = cL then some m1 else n1.live.lookup c' := by
    intro n1 hw1 hk1 hl1 lip
    cases lip with
    | true =>
      simp only [↓reduceIte]
      exact ⟨by rw [KNode.repoint_klongsWf]; exact hw1, KNode.repoint_last_live_lookup n1 il cL l m1 hk1 hl1⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨KNode.add_key_wf n1 tt cL m1 hw1, fun c' => ?_⟩
      rw [KNode.add_key_live_lookup_of_wf n1 tt cL c' m1 hw1]
      by_cases hcc : c' = cL
      · subst hcc; simp
      · have : (cL == c') = false := by simpa using Ne.symm hcc
        simp [this, hcc]
  have hcR : ∀ c', (if c' = cL then some m1 else if c' == cR then none else pn.live.lookup c') =
      (if c' = cL then some m1 else if c' = cR then none else pn.live.lookup c') := by
    intro c'
    by_cases h1 : c' = cR
    · simp [h1]
    · have : (c' == cR) = false := by simpa using h1
      simp [this, h1]
  cases m2 with
  | none =>
    obtain ⟨hw1, hk1, hl1, hlk1⟩ := hn1 true rfl htd htdh
    obtain ⟨_, hlk2⟩ := hn2 _ hw1 hk1 hl1 lip
    unfold mpNode
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hlk2 c, hlk1 c, hcR c]
  | some yg =>
    obtain ⟨y, g⟩ := yg
    by_cases hg : g = cR
    · subst hg
      have hd : (g != g) = false := by simp
      obtain ⟨hw2, hlk2⟩ := hn2 pn hwf hL hLL lip
      -- the right klong in n2
      have hk2 : (if lip then pn.repoint il m1 else pn.add tt (.key cL m1)).ks[ir]? =
          some (.key g r) := by
        cases lip with
        | true =>
          simp only [↓reduceIte]
          have hrep : pn.repoint il m1 = { pn with ks := pn.ks.set il (.key cL m1) } := by
            unfold KNode.repoint; rw [hL]; rfl
          have hii : il ≠ ir := by
            intro he; subst he; rw [hL] at hR
            simp only [Option.some.injEq, Klong.key.injEq] at hR; exact hc hR.1
          rw [hrep]; simp only; rw [List.getElem?_set_ne hii]; exact hR
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [pn.add_getElem?_lt tt _ ir hir]; exact hR
      have hl2 : LastLive (if lip then pn.repoint il m1 else pn.add tt (.key cL m1)).ks
          (if lip then pn.repoint il m1 else pn.add tt (.key cL m1)).lastBitmap ir g := by
        cases lip with
        | true => exact LastLive.repoint pn ir g il cL l m1 hc hL hRL
        | false => exact LastLive.add_key pn tt ir g cL m1 hc hRL
      unfold mpNode
      simp only [hd, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      cases rip with
      | true =>
        simp only [↓reduceIte]
        rw [KNode.repoint_last_live_lookup _ ir g r y hk2 hl2 c, hlk2 c]
        by_cases h1 : c = g
        · simp [h1]
        · simp only [h1, ↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [KNode.add_key_live_lookup_of_wf _ tt g c y hw2, hlk2 c]
        by_cases h1 : c = g
        · subst h1; simp
        · have : (g == c) = false := by simpa using Ne.symm h1
          simp [this, h1]
    · have hd : (g != cR) = true := by simpa using hg
      have hrip' : rip = false := by
        cases hr : rip with
        | false => rfl
        | true => exact absurd (hrip hr y g rfl) hg
      subst hrip'
      obtain ⟨hw1, hk1, hl1, hlk1⟩ := hn1 true rfl htd htdh
      obtain ⟨hw2, hlk2⟩ := hn2 _ hw1 hk1 hl1 lip
      unfold mpNode
      simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [KNode.add_key_live_lookup_of_wf _ tt g c y hw2, hlk2 c, hlk1 c, hcR c]
      by_cases h1 : c = g
      · subst h1; simp
      · have : (g == c) = false := by simpa using Ne.symm h1
        simp [this, h1]

end SIS.Tree
