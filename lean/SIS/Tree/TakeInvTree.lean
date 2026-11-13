/-
The take-back's (B) at node-map level (bergdb 024-12, TP4; TakeBackRun.lean):
`LiveReachedN`, a node with a live klong to a node at or above B is reached;
`OldBelowN`, the klongs of a node before the transaction's time name nodes
below B. Root collapse keeps both: every node reached before but the root that
gives way is reached after (`reach_segCollapse`, `reach_spaceCollapse`), and
that root is taken back or keeps its klongs before the transaction only.
-/
import SIS.Tree.TakeBackRun
import SIS.Tree.RangeCollapseSeg

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (B) at node-map level. -/
def LiveReachedN (N : NodeId → Option KNode) (t : Time) (r B : NodeId) : Prop :=
  ∀ q qn c y, N q = some qn → (c, y) ∈ qn.liveAt t → B ≤ y → TReach N t r q

/-- The klongs of every node before time t name nodes below B. -/
def OldBelowN (N : NodeId → Option KNode) (t : Time) (B : NodeId) : Prop :=
  ∀ q qn, N q = some qn → ∀ cv y, Klong.key cv y ∈ prefixAt qn.ks (t - 1) → y < B

theorem liveReached_iff (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) :
    LiveReached p P t B w ↔ LiveReachedN (wNode p (viewOf P) w) t w.top.rootKey B := Iff.rfl

/-- One live klong per compare value. -/
theorem KNode.liveAt_fun (n : KNode) (t : Time) (k : Nat) (x v : NodeId)
    (h1 : (k, x) ∈ n.liveAt t) (h2 : (k, v) ∈ n.liveAt t) : x = v := by
  have hn : ((n.liveAt t).map Prod.fst).Nodup := by
    rw [n.liveAt_eq_live_prefix]; exact KNode.live_keys_nodup _
  have a := lookup_of_mem_nodup _ hn k x h1
  have b := lookup_of_mem_nodup _ hn k v h2
  rw [a] at b
  exact Option.some.inj b

/-! ## prefixAt -/

theorem prefixAt_append_stop (ks more : List Klong) (t : Time) (s : Time) (hs : t < s)
    (h : (∃ u, Klong.time u ∈ ks ∧ t < u) ∨ more.head? = some (.time s)) :
    prefixAt (ks ++ more) t = prefixAt ks t := by
  unfold prefixAt
  induction ks with
  | nil =>
    rcases h with ⟨u, hu, _⟩ | h
    · cases hu
    · cases more with
      | nil => cases h
      | cons k more =>
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        simp [Nat.not_le.mpr hs]
  | cons k ks ih =>
    have h' : (∃ u, Klong.time u ∈ ks ∧ t < u) ∨ more.head? = some (.time s) ∨
        (∃ u, k = .time u ∧ t < u) := by
      rcases h with ⟨u, hu, htu⟩ | h
      · rcases List.mem_cons.mp hu with he | hu'
        · exact Or.inr (Or.inr ⟨u, he.symm, htu⟩)
        · exact Or.inl ⟨u, hu', htu⟩
      · exact Or.inr (Or.inl h)
    rcases h' with h1 | h1 | ⟨u, hku, htu⟩
    · cases k with
      | time u => simp only [List.cons_append, List.takeWhile_cons]; split <;> simp_all
      | key c y => simp only [List.cons_append, List.takeWhile_cons]; simp only [ih (Or.inl h1)]
      | del b => simp only [List.cons_append, List.takeWhile_cons]; simp only [ih (Or.inl h1)]
    · cases k with
      | time u => simp only [List.cons_append, List.takeWhile_cons]; split <;> simp_all
      | key c y => simp only [List.cons_append, List.takeWhile_cons]; simp only [ih (Or.inr h1)]
      | del b => simp only [List.cons_append, List.takeWhile_cons]; simp only [ih (Or.inr h1)]
    · subst hku
      simp [Nat.not_le.mpr htu]

theorem prefixAt_set_late (ks : List Klong) (t : Time) (j : Nat) (c' : Nat) (y' : NodeId)
    (hj : (prefixAt ks t).length ≤ j) (hk0 : ∀ k0, ks[j]? = some k0 → ∃ c y, k0 = .key c y) :
    prefixAt (ks.set j (.key c' y')) t = prefixAt ks t := by
  unfold prefixAt at hj ⊢
  induction ks generalizing j with
  | nil => simp
  | cons k0 ks ih =>
    cases j with
    | zero =>
      obtain ⟨c, y, rfl⟩ := hk0 k0 rfl
      simp at hj
    | succ j =>
      simp only [List.set_cons_succ]
      cases k0 with
      | time u =>
        by_cases hu : u ≤ t
        · simp only [List.takeWhile_cons, hu, decide_true, ↓reduceIte, List.length_cons] at hj ⊢
          rw [ih j (by omega) (fun k1 h1 => hk0 k1 (by simpa using h1))]
        · simp [hu]
      | key c y =>
        simp only [List.takeWhile_cons, ↓reduceIte, List.length_cons] at hj ⊢
        rw [ih j (by omega) (fun k1 h1 => hk0 k1 (by simpa using h1))]
      | del b =>
        simp only [List.takeWhile_cons, ↓reduceIte, List.length_cons] at hj ⊢
        rw [ih j (by omega) (fun k1 h1 => hk0 k1 (by simpa using h1))]

/-! ## The last time -/

theorem lastTimeFold_noTime (ks : List Klong) (acc : Option Time)
    (h : ∀ s, Klong.time s ∉ ks) :
    ks.foldl (fun t k => match k with
      | .time x => some x
      | _ => t) acc = acc := by
  induction ks generalizing acc with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    cases k with
    | time x => exact absurd (List.mem_cons_self) (h x)
    | key c y => exact ih acc (fun s hs => h s (List.mem_cons_of_mem _ hs))
    | del b => exact ih acc (fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- Well-formed klongs with a time klong of t and none later than t: t is the
last time. -/
theorem KNode.lastTime_of_mem_max (n : KNode) (t : Time) (hw : klongsWf n.ks = true)
    (hm : Klong.time t ∈ n.ks) (hle : ∀ s, Klong.time s ∈ n.ks → s ≤ t) : n.lastTime = some t := by
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hm
  have hal : a < n.ks.length := (List.getElem?_eq_some_iff.mp ha).1
  have hsplit : n.ks = n.ks.take a ++ (Klong.time t :: n.ks.drop (a + 1)) := by
    conv => lhs; rw [← List.take_append_drop a n.ks]
    congr 1
    rw [List.drop_eq_getElem_cons hal]
    congr 1
    have := (List.getElem?_eq_some_iff.mp ha).2
    exact this
  have hno : ∀ s, Klong.time s ∉ n.ks.drop (a + 1) := by
    intro s hs
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hs
    rw [List.getElem?_drop] at hb
    have hlt := klongsWf_times_increase n.ks hw a (a + 1 + b) t s (by omega) ha hb
    have := hle s (List.mem_of_mem_drop hs)
    omega
  unfold KNode.lastTime
  rw [hsplit, List.foldl_append, List.foldl_cons]
  exact lastTimeFold_noTime _ _ hno

/-- A node unlinked (`unlink`: its klongs of time t dropped if its last time is
t) whose klongs before t name nodes below B, well formed and of no later time,
has live klongs to nodes below B only. -/
theorem unlinked_live_below (n : KNode) (t : Time) (B : NodeId) (hpos : 0 < t)
    (hold : ∀ cv y, Klong.key cv y ∈ prefixAt n.ks (t - 1) → y < B)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ c z, (c, z) ∈ (if n.lastTime == some t then n.toPrev (t - 1) else n).liveAt t → z < B := by
  intro c z hz
  split at hz
  · exact hold c z (KNode.liveAt_key_mem _ t c z hz)
  · rename_i hlt
    have hk := KNode.liveAt_key_mem _ t c z hz
    apply hold c z
    rw [prefixAt_of_timesLE n.ks (t - 1) (fun s hs => ?_)]
    · exact hk
    · have h1 := ht s hs
      by_cases hst : s = t
      · subst hst
        exact absurd (by rw [KNode.lastTime_of_mem_max n s hw hs ht]; simp) hlt
      · omega

/-! ## Root collapse at node-map level -/

/-- Root collapse at the segment root x below the segment leaf q, x inner with
its live klongs to y only: every node reached before but x is reached after, and
y is (q's klong k1 names y). -/
theorem reach_segCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r q x y : NodeId)
    (qn qn2 xn : KNode) (k1 : Nat) (hT : TreeOK N1 t r)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hk1 : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some xn) (honly : ∀ c z, (c, z) ∈ xn.liveAt t → z = y)
    (hN2q : N2 q = some qn2) (hq2a : (k1, y) ∈ qn2.liveAt t)
    (hq2b : ∀ c z, (c, z) ∈ qn.liveAt t → c ≠ k1 → (c, z) ∈ qn2.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) :
    ∀ v, TReach N1 t r v → (v ≠ x → TReach N2 t r v) ∧ (v = x → TReach N2 t r y) := by
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hrx : r ≠ x := fun h => hT.rootFree q k1 hq ⟨qn, hqn, h ▸ hk1⟩
  intro v hv
  induction hv with
  | root => exact ⟨fun _ => TReach.root, fun h => absurd h hrx⟩
  | @link a c v ha hl ih =>
    obtain ⟨an, han, hav⟩ := hl
    by_cases hax : a = x
    · rw [hax, hxn] at han
      cases han
      have hvy : v = y := honly c v hav
      rw [hvy]
      exact ⟨fun _ => ih.2 hax, fun _ => ih.2 hax⟩
    · have haR2 := ih.1 hax
      by_cases haq : a = q
      · rw [haq, hqn] at han
        cases han
        rw [haq] at haR2 ha
        by_cases hck : c = k1
        · rw [hck] at hav
          have hvx : x = v := KNode.liveAt_fun qn t k1 x v hk1 hav
          rw [← hvx]
          exact ⟨fun h => absurd rfl h, fun _ => TReach.link haR2 ⟨qn2, hN2q, hq2a⟩⟩
        · refine ⟨fun _ => TReach.link haR2 ⟨qn2, hN2q, hq2b c v hav hck⟩, fun hvx => ?_⟩
          rw [hvx] at hav
          exact absurd (hT.oneLink q c q k1 x ha hq ⟨qn, hqn, hav⟩ ⟨qn, hqn, hk1⟩).2 hck
      · have hl2 : TLink N2 t a c v := ⟨an, by rw [hN2 a haq hax]; exact han, hav⟩
        refine ⟨fun _ => TReach.link haR2 hl2, fun hvx => ?_⟩
        rw [hvx] at hav
        exact absurd (hT.oneLink a c q k1 x ha hq ⟨an, han, hav⟩ ⟨qn, hqn, hk1⟩).1 haq

/-- (B) after root collapse at a segment root x: x taken back, or with live
klongs to nodes below B only. -/
theorem liveReachedN_segCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r q x y B : NodeId)
    (qn qn2 xn : KNode) (k1 : Nat) (hT : TreeOK N1 t r)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hk1 : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some xn) (honly : ∀ c z, (c, z) ∈ xn.liveAt t → z = y)
    (hN2q : N2 q = some qn2) (hq2a : (k1, y) ∈ qn2.liveAt t)
    (hq2b : ∀ c z, (c, z) ∈ qn.liveAt t → c ≠ k1 → (c, z) ∈ qn2.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) (hL : LiveReachedN N1 t r B)
    (hx2 : ∀ xn2, N2 x = some xn2 → ∀ c z, (c, z) ∈ xn2.liveAt t → z < B) :
    LiveReachedN N2 t r B := by
  have hR := reach_segCollapse N1 N2 t r q x y qn qn2 xn k1 hT hq hqn hk1 hxn honly hN2q hq2a hq2b hN2
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hqx : q ≠ x := fun h => hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  intro u un c z hu hl hB
  by_cases hux : u = x
  · rw [hux] at hu
    have := hx2 un hu c z hl
    omega
  · by_cases huq : u = q
    · rw [huq]; exact (hR q hq).1 hqx
    · rw [hN2 u huq hux] at hu
      exact (hR u (hL u un c z hu hl hB)).1 hux

/-- Root collapse at the space root r, inner with its live klongs to y only:
every node reached before but r is reached from y after. -/
theorem reach_spaceCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r y : NodeId) (rn : KNode)
    (hrn : N1 r = some rn) (honly : ∀ c z, (c, z) ∈ rn.liveAt t → z = y)
    (hN2 : ∀ z, z ≠ r → N2 z = N1 z) :
    ∀ v, TReach N1 t r v → v ≠ r → TReach N2 t y v := by
  intro v hv
  induction hv with
  | root => intro h; exact absurd rfl h
  | @link a c v ha hl ih =>
    intro _
    obtain ⟨an, han, hav⟩ := hl
    by_cases har : a = r
    · rw [har, hrn] at han
      cases han
      rw [honly c v hav]
      exact TReach.root
    · exact TReach.link (ih har) ⟨an, by rw [hN2 a har]; exact han, hav⟩

/-- (B) after root collapse at the space root r: r taken back, or with live
klongs to nodes below B only. -/
theorem liveReachedN_spaceCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r y B : NodeId)
    (rn : KNode) (hrn : N1 r = some rn) (honly : ∀ c z, (c, z) ∈ rn.liveAt t → z = y)
    (hN2 : ∀ z, z ≠ r → N2 z = N1 z) (hL : LiveReachedN N1 t r B)
    (hr2 : ∀ rn2, N2 r = some rn2 → ∀ c z, (c, z) ∈ rn2.liveAt t → z < B) :
    LiveReachedN N2 t y B := by
  intro u un c z hu hl hB
  by_cases hur : u = r
  · rw [hur] at hu
    have := hr2 un hu c z hl
    omega
  · rw [hN2 u hur] at hu
    exact reach_spaceCollapse N1 N2 t r y rn hrn honly hN2 u (hL u un c z hu hl hB) hur

/-! ## First times -/

theorem findSome_time_set (ks : List Klong) (j : Nat) (c c' : Nat) (y y' : NodeId)
    (hj : ks[j]? = some (.key c y)) :
    (ks.set j (.key c' y')).findSome? (fun k => match k with
      | .time x => some x
      | _ => none) = ks.findSome? (fun k => match k with
      | .time x => some x
      | _ => none) := by
  induction ks generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [List.set_cons_succ, List.findSome?_cons]
      rw [ih j hj]

theorem KNode.firstTime_repoint (n : KNode) (j : Nat) (y : NodeId) :
    (n.repoint j y).firstTime = n.firstTime := by
  unfold KNode.repoint
  split
  · rename_i c y0 hj
    simp only [KNode.setAt, KNode.firstTime]
    exact findSome_time_set n.ks j c c y0 y hj
  · rfl

theorem KNode.firstTime_add_some (n : KNode) (t : Time) (k : Klong) (s : Time)
    (h : n.firstTime = some s) : (n.add t k).firstTime = some s := by
  unfold KNode.firstTime at h ⊢
  unfold KNode.add
  split
  · split <;> simp only [List.findSome?_append, h, Option.some_or]
  · simp only [List.findSome?_append, h, Option.some_or]

theorem KNode.firstTime_toPrev (n : KNode) (t s : Time) (h : n.firstTime = some s) (hs : s ≤ t) :
    (n.toPrev t).firstTime = some s := by
  unfold KNode.firstTime at h ⊢
  unfold KNode.toPrev prefixAt
  simp only
  generalize n.ks = ks at h
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    cases k with
    | time u =>
      simp only [List.findSome?_cons, Option.some.injEq] at h
      subst h
      simp [hs]
    | key c y =>
      simp only [List.findSome?_cons] at h
      simp only [List.takeWhile_cons, ↓reduceIte, List.findSome?_cons]
      exact ih h
    | del b =>
      simp only [List.findSome?_cons] at h
      simp only [List.takeWhile_cons, ↓reduceIte, List.findSome?_cons]
      exact ih h

/-- The klongs of t-1 of a node with a klong added at t > 0, no time klong after t. -/
theorem KNode.prefixAt_add (n : KNode) (t : Time) (k : Klong) (hpos : 0 < t) :
    prefixAt (n.add t k).ks (t - 1) = prefixAt n.ks (t - 1) := by
  unfold KNode.add
  split
  · rename_i lt hlt
    split
    · exact prefixAt_append_stop n.ks _ (t - 1) t (by omega) (Or.inr rfl)
    · rename_i hge
      obtain ⟨m, _, hm⟩ := KNode.lastTime_anchor n lt hlt
      exact prefixAt_append_stop n.ks _ (t - 1) t (by omega)
        (Or.inl ⟨lt, List.mem_of_getElem? hm, by omega⟩)
  · exact prefixAt_append_stop n.ks _ (t - 1) t (by omega) (Or.inr rfl)

/-- A klong at index j within the klongs of time t is one of them. -/
theorem mem_prefixAt_of_lt (ks : List Klong) (t : Time) (j : Nat) (k : Klong)
    (hj : j < (prefixAt ks t).length) (hk : ks[j]? = some k) : k ∈ prefixAt ks t := by
  obtain ⟨rest, hrest⟩ : ∃ rest, prefixAt ks t ++ rest = ks := List.takeWhile_prefix _
  have h1 : (prefixAt ks t)[j]? = ks[j]? := by
    have h2 : ks[j]? = (prefixAt ks t ++ rest)[j]? := by rw [hrest]
    rw [h2, List.getElem?_append_left hj]
  rw [hk] at h1
  exact List.mem_of_getElem? h1

/-! ## (B) by the klongs of the transaction's time -/

/-- (B) in the form every rule keeps: a node with a klong of time t (one the
transaction changed) is reached from the space root. With the klongs of the
nodes before the transaction below B (`Good`), it gives `LiveReachedN`. -/
def TtReachedN (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  ∀ q qn, N q = some qn → Klong.time t ∈ qn.ks → TReach N t r q

theorem time_le_of_mem_prefixAt (ks : List Klong) (t s : Time) (h : Klong.time s ∈ prefixAt ks t) :
    s ≤ t := by
  unfold prefixAt at h
  induction ks with
  | nil => cases h
  | cons k ks ih =>
    cases k with
    | time u =>
      by_cases hu : u ≤ t
      · simp only [List.takeWhile_cons, hu, decide_true, ↓reduceIte, List.mem_cons,
          Klong.time.injEq] at h
        rcases h with h | h
        · omega
        · exact ih h
      · simp [hu] at h
    | key c y =>
      simp only [List.takeWhile_cons, ↓reduceIte, List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h
    | del b =>
      simp only [List.takeWhile_cons, ↓reduceIte, List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h

theorem time_not_mem_prefixAt (ks : List Klong) (t : Time) (hpos : 0 < t) :
    Klong.time t ∉ prefixAt ks (t - 1) := by
  intro h
  have := time_le_of_mem_prefixAt ks (t - 1) t h
  omega

/-- A klong of ks not among those of time t comes after a time klong later than t. -/
theorem later_time_of_not_mem_prefixAt (ks : List Klong) (t : Time) (k : Klong) (hk : k ∈ ks)
    (hn : k ∉ prefixAt ks t) : ∃ s, Klong.time s ∈ ks ∧ t < s := by
  unfold prefixAt at hn
  induction ks with
  | nil => cases hk
  | cons k0 ks ih =>
    cases k0 with
    | time u =>
      by_cases hu : u ≤ t
      · simp only [List.takeWhile_cons, hu, decide_true, ↓reduceIte, List.mem_cons, not_or] at hn
        rcases List.mem_cons.mp hk with he | hk'
        · exact absurd he hn.1
        · obtain ⟨s, hs, hts⟩ := ih hk' hn.2
          exact ⟨s, List.mem_cons_of_mem _ hs, hts⟩
      · exact ⟨u, List.mem_cons_self, by omega⟩
    | key c y =>
      simp only [List.takeWhile_cons, ↓reduceIte, List.mem_cons, not_or] at hn
      rcases List.mem_cons.mp hk with he | hk'
      · exact absurd he hn.1
      · obtain ⟨s, hs, hts⟩ := ih hk' hn.2
        exact ⟨s, List.mem_cons_of_mem _ hs, hts⟩
    | del b =>
      simp only [List.takeWhile_cons, ↓reduceIte, List.mem_cons, not_or] at hn
      rcases List.mem_cons.mp hk with he | hk'
      · exact absurd he hn.1
      · obtain ⟨s, hs, hts⟩ := ih hk' hn.2
        exact ⟨s, List.mem_cons_of_mem _ hs, hts⟩

/-- A node unlinked at time t > 0, well formed and of no later time, has no klong
of time t. -/
theorem unlinked_no_time (n : KNode) (t : Time) (hpos : 0 < t) (hw : klongsWf n.ks = true)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    Klong.time t ∉ (if n.lastTime == some t then n.toPrev (t - 1) else n).ks := by
  split
  · exact time_not_mem_prefixAt n.ks t hpos
  · rename_i hlt
    intro hm
    exact hlt (by rw [KNode.lastTime_of_mem_max n t hw hm ht]; simp)

/-- (B) after root collapse at a segment root x: x taken back, or without a
klong of time t. -/
theorem ttReachedN_segCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r q x y : NodeId)
    (qn qn2 xn : KNode) (k1 : Nat) (hT : TreeOK N1 t r)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hk1 : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some xn) (honly : ∀ c z, (c, z) ∈ xn.liveAt t → z = y)
    (hN2q : N2 q = some qn2) (hq2a : (k1, y) ∈ qn2.liveAt t)
    (hq2b : ∀ c z, (c, z) ∈ qn.liveAt t → c ≠ k1 → (c, z) ∈ qn2.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) (hL : TtReachedN N1 t r)
    (hx2 : ∀ xn2, N2 x = some xn2 → Klong.time t ∉ xn2.ks) :
    TtReachedN N2 t r := by
  have hR := reach_segCollapse N1 N2 t r q x y qn qn2 xn k1 hT hq hqn hk1 hxn honly hN2q hq2a hq2b hN2
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hqx : q ≠ x := fun h => hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  intro u un hu hm
  by_cases hux : u = x
  · rw [hux] at hu
    exact absurd hm (hx2 un hu)
  · by_cases huq : u = q
    · rw [huq]; exact (hR q hq).1 hqx
    · rw [hN2 u huq hux] at hu
      exact (hR u (hL u un hu hm)).1 hux

/-- (B) after root collapse at the space root r: r taken back, or without a
klong of time t. -/
theorem ttReachedN_spaceCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (rn : KNode) (hrn : N1 r = some rn) (honly : ∀ c z, (c, z) ∈ rn.liveAt t → z = y)
    (hN2 : ∀ z, z ≠ r → N2 z = N1 z) (hL : TtReachedN N1 t r)
    (hr2 : ∀ rn2, N2 r = some rn2 → Klong.time t ∉ rn2.ks) :
    TtReachedN N2 t y := by
  intro u un hu hm
  by_cases hur : u = r
  · rw [hur] at hu
    exact absurd hm (hr2 un hu)
  · rw [hN2 u hur] at hu
    exact reach_spaceCollapse N1 N2 t r y rn hrn honly hN2 u (hL u un hu hm) hur

end SIS.Tree
