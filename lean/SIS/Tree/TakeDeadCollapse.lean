/-
Root collapse keeps the take-back's (C) (bergdb 024-12, TP4; `DeadLiveN`,
TakeBackDead.lean), with (B) (`TtReachedN`) and the facts of the nodes before
the transaction that both need: their klongs before the transaction's time name
nodes below B (`OldBelowN`), their first time is before it (`OldStartN`), the
nodes of the transaction start at it (`MadeStartN`), no node is of a later time
(`TimesN`), and no value of the transaction is a node (`ValsNoNodeN`). With
these, a node with a klong to a node of the transaction is reached and names it
live (`named_reached`), so only the segment leaf above names a root taken back.
-/
import SIS.Tree.TakeBackDead
import SIS.Tree.TakeInvCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- No node of a later time than t. -/
def TimesN (N : NodeId → Option KNode) (t : Time) : Prop :=
  ∀ q qn, N q = some qn → ∀ s, Klong.time s ∈ qn.ks → s ≤ t

/-- The nodes below B have a first time before t. -/
def OldStartN (N : NodeId → Option KNode) (t : Time) (B : NodeId) : Prop :=
  ∀ q qn, N q = some qn → q < B → ∃ s, s < t ∧ qn.firstTime = some s

/-- The nodes at or above B start at time t. -/
def MadeStartN (N : NodeId → Option KNode) (t : Time) (B : NodeId) : Prop :=
  ∀ q qn, N q = some qn → B ≤ q → qn.firstTime = some t

/-- No value of the transaction is a node. -/
def ValsNoNodeN (N : NodeId → Option KNode) (vals : List NodeId) : Prop :=
  ∀ y ∈ vals, N y = none

/-- A klong of a node to a node at or above B comes after a time klong of t. -/
theorem time_of_new (N : NodeId → Option KNode) (t : Time) (B : NodeId) (hpos : 0 < t)
    (hO : OldBelowN N t B) (hTi : TimesN N t) (q : NodeId) (qn : KNode) (hq : N q = some qn)
    (cv : Nat) (y : NodeId) (hk : Klong.key cv y ∈ qn.ks) (hB : B ≤ y) : Klong.time t ∈ qn.ks := by
  have hnot : Klong.key cv y ∉ prefixAt qn.ks (t - 1) := by
    intro hm
    have := hO q qn hq cv y hm
    omega
  obtain ⟨s, hs, hts⟩ := later_time_of_not_mem_prefixAt qn.ks (t - 1) _ hk hnot
  have hle := hTi q qn hq s hs
  have : s = t := by omega
  rw [← this]
  exact hs

/-- A node with a klong to a node of the transaction that is no value is
reached and names it live. -/
theorem named_reached (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (hpos : 0 < t) (hTt : TtReachedN N t r) (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B)
    (hTi : TimesN N t) (q : NodeId) (qn : KNode) (hq : N q = some qn) (i cv : Nat) (y : NodeId)
    (hi : qn.ks[i]? = some (Klong.key cv y)) (hB : B ≤ y) (hv : y ∉ vals) :
    TReach N t r q ∧ ∃ c, (c, y) ∈ qn.liveAt t := by
  have hk : Klong.key cv y ∈ qn.ks := List.mem_of_getElem? hi
  exact ⟨hTt q qn hq (time_of_new N t B hpos hO hTi q qn hq cv y hk hB), (hD q qn hq i cv y hi hB hv).1⟩

theorem lastLive_set_self (ks : List Klong) (del : List Nat) (j k : Nat) (y : NodeId)
    (hj : LastLive ks del j k) : LastLive (ks.set j (.key k y)) del j k := by
  obtain ⟨⟨y0, hy0⟩, hjd, hlater⟩ := hj
  have hjl : j < ks.length := (List.getElem?_eq_some_iff.mp hy0).1
  refine ⟨⟨y, by simp [List.getElem?_set_self hjl]⟩, hjd, ?_⟩
  intro j' y' hjj' h
  rw [List.getElem?_set_ne (by omega)] at h
  exact hlater j' y' hjj' h

theorem lastLive_set_other (ks : List Klong) (del : List Nat) (i cv j k : Nat) (y : NodeId)
    (hi : LastLive ks del i cv) (hj : LastLive ks del j k) (hij : i ≠ j) :
    LastLive (ks.set j (.key k y)) del i cv := by
  obtain ⟨⟨yi, hyi⟩, hid, hilater⟩ := hi
  obtain ⟨⟨yj, hyj⟩, hjd, _⟩ := hj
  refine ⟨⟨yi, by rw [List.getElem?_set_ne (Ne.symm hij)]; exact hyi⟩, hid, ?_⟩
  intro j' y' hij' h
  by_cases hjj : j' = j
  · subst hjj
    have hjl : j' < ks.length := (List.getElem?_eq_some_iff.mp hyj).1
    rw [List.getElem?_set_self hjl] at h
    simp only [Option.some.injEq, Klong.key.injEq] at h
    obtain ⟨hk, _⟩ := h
    subst hk
    exact absurd (hilater j' yj hij' hyj) hjd
  · rw [List.getElem?_set_ne (Ne.symm hjj)] at h
    exact hilater j' y' hij' h


/-- (C) after root collapse at a segment root x taken back: the segment leaf q's
one klong to x names x's child y instead. -/
theorem deadLiveN_segTake (N1 N2 : NodeId → Option KNode) (t : Time) (r B : NodeId)
    (vals : List NodeId) (q x y : NodeId) (qn : KNode) (k j : Nat)
    (hT : TreeOK N1 t r) (hD : DeadLiveN N1 t B vals)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hql : qn.leaf = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hj : qn.linkIndex x k = some j) (hk : (k, x) ∈ qn.liveAt t) (hBx : B ≤ x) (hxv : x ∉ vals)
    (hN2q : N2 q = some (qn.repoint j y)) (hN2x : N2 x = none)
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) : DeadLiveN N2 t B vals := by
  have hjk : qn.ks[j]? = some (.key k x) := kd_linkIndex_some qn x k j hj
  have hLj : LastLive qn.ks qn.lastBitmap j k := (hD q qn hqn j k x hjk hBx hxv).2 hql
  have hrp : qn.repoint j y = qn.setAt j (.key k y) := by
    unfold KNode.repoint; rw [hjk]
  have hbm : (qn.repoint j y).lastBitmap = qn.lastBitmap :=
    KNode.lastBitmap_of_shapeOf (KNode.repoint_shapeOf qn j y)
  intro u un hu i cv z hi hB hv
  by_cases huq : u = q
  · rw [huq, hN2q] at hu
    cases hu
    rw [hrp] at hi
    simp only [KNode.setAt] at hi
    by_cases hij : i = j
    · subst hij
      have hjl : i < qn.ks.length := (List.getElem?_eq_some_iff.mp hjk).1
      rw [List.getElem?_set_self hjl] at hi
      simp only [Option.some.injEq, Klong.key.injEq] at hi
      rw [← hi.1, ← hi.2]
      refine ⟨⟨k, KNode.repoint_liveAt_new qn x y k i t hj hqt⟩, fun _ => ?_⟩
      rw [hbm, hrp]
      exact lastLive_set_self qn.ks qn.lastBitmap i k y hLj
    · rw [List.getElem?_set_ne (Ne.symm hij)] at hi
      obtain ⟨⟨c0, hc0⟩, hL0⟩ := hD q qn hqn i cv z hi hB hv
      have hzx : z ≠ x := by
        intro hzx
        rw [hzx] at hi hc0
        have hLi := hL0 hql
        by_cases hck : cv = k
        · rw [hck] at hLi
          obtain ⟨_, hid, hilater⟩ := hLi
          obtain ⟨_, hjd, hjlater⟩ := hLj
          rcases Nat.lt_or_ge i j with h | h
          · exact hjd (hilater j x h hjk)
          · exact hid (hjlater i x (by omega) (by rw [hi, hck]))
        · have hci : (cv, x) ∈ qn.liveAt t := by
            rw [KNode.liveAt_of_times qn t hqt]
            apply mem_of_lookup_nodup
            rw [KNode.live_lookup]
            exact keyLookup_of_last _ _ _ i x hi hLi
          exact hck (hT.oneLink q cv q k x hq hq ⟨qn, hqn, hci⟩ ⟨qn, hqn, hk⟩).2
      refine ⟨⟨c0, ?_⟩, fun _ => ?_⟩
      · refine KNode.repoint_liveAt_keep qn x y k j t hj hqt c0 z hc0 (fun hck => hzx ?_)
        rw [hck] at hc0
        exact (KNode.liveAt_fun qn t k x z hk hc0).symm
      · rw [hbm, hrp]
        exact lastLive_set_other qn.ks qn.lastBitmap i cv j k y (hL0 hql) hLj hij
  · by_cases hux : u = x
    · rw [hux, hN2x] at hu; cases hu
    · rw [hN2 u huq hux] at hu
      exact hD u un hu i cv z hi hB hv


/-- A node unlinked at time t > 0, its klongs before t naming nodes below B, well
formed and of no later time, names nodes below B only. -/
theorem unlinked_old_ptrs (n : KNode) (t : Time) (B : NodeId) (hpos : 0 < t)
    (hold : ∀ cv y, Klong.key cv y ∈ prefixAt n.ks (t - 1) → y < B)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ cv y, Klong.key cv y ∈ (if n.lastTime == some t then n.toPrev (t - 1) else n).ks → y < B := by
  intro cv y hk
  split at hk
  · exact hold cv y hk
  · rename_i hlt
    apply hold cv y
    rw [prefixAt_of_timesLE n.ks (t - 1) (fun s hs => ?_)]
    · exact hk
    · have h1 := ht s hs
      by_cases hst : s = t
      · subst hst
        exact absurd (by rw [KNode.lastTime_of_mem_max n s hw hs ht]; simp) hlt
      · omega

theorem lastBitmapOf_append_nodel (ks more : List Klong) (h : ∀ b, Klong.del b ∉ more) :
    lastBitmapOf (ks ++ more) = lastBitmapOf ks := by
  unfold lastBitmapOf
  rw [List.foldl_append]
  generalize ks.foldl (fun d k => match k with
    | .del b => b
    | _ => d) [] = acc
  induction more generalizing acc with
  | nil => rfl
  | cons k more ih =>
    simp only [List.foldl_cons]
    cases k with
    | del b => exact absurd List.mem_cons_self (h b)
    | time t => exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) acc
    | key c y => exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) acc

/-- The klongs of a node with a key klong added. -/
theorem KNode.add_key_ks (n : KNode) (t : Time) (k : Nat) (y : NodeId) :
    (n.add t (.key k y)).ks = n.ks ++ [.time t, .key k y] ∨
      (n.add t (.key k y)).ks = n.ks ++ [.key k y] := by
  unfold KNode.add
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

/-- (C) after root collapse at a segment root x replaced: x, below B, unlinked;
the segment leaf q gets a klong k to x's child y. -/
theorem deadLiveN_segReplace (N1 N2 : NodeId → Option KNode) (t : Time) (B : NodeId)
    (vals : List NodeId) (q x y : NodeId) (qn xn : KNode) (k : Nat) (hpos : 0 < t)
    (hD : DeadLiveN N1 t B vals) (hO : OldBelowN N1 t B)
    (hqn : N1 q = some qn) (hqw : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hk : (k, x) ∈ qn.liveAt t) (hxB : x < B)
    (hxn : N1 x = some xn) (hxw : klongsWf xn.ks = true) (hxt : ∀ s, Klong.time s ∈ xn.ks → s ≤ t)
    (hN2q : N2 q = some (qn.add t (.key k y)))
    (hN2x : N2 x = some (if xn.lastTime == some t then xn.toPrev (t - 1) else xn))
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) : DeadLiveN N2 t B vals := by
  intro u un hu i cv z hi hB hv
  by_cases huq : u = q
  · rw [huq, hN2q] at hu
    cases hu
    obtain ⟨more, hks, hnd, hmore, hlastk⟩ : ∃ more, (qn.add t (.key k y)).ks = qn.ks ++ more ∧
        (∀ b, Klong.del b ∉ more) ∧ (∀ c z, Klong.key c z ∈ more → c = k ∧ z = y) ∧
        ∀ i', qn.ks.length ≤ i' → ∀ c z, more[i' - qn.ks.length]? = some (Klong.key c z) →
          ∀ j', i' < j' → more[j' - qn.ks.length]? = none := by
      rcases KNode.add_key_ks qn t k y with h | h
      · refine ⟨[.time t, .key k y], h, by simp, by simp, fun i' hi' c z hm j' hj' => ?_⟩
        have hlt : i' - qn.ks.length < 2 := (List.getElem?_eq_some_iff.mp hm).1
        have hne : i' - qn.ks.length ≠ 0 := by
          intro h0; rw [h0] at hm; simp at hm
        simp only [List.getElem?_eq_none_iff, List.length_cons, List.length_nil]
        omega
      · refine ⟨[.key k y], h, by simp, by simp, fun i' hi' c z hm j' hj' => ?_⟩
        have hlt : i' - qn.ks.length < 1 := (List.getElem?_eq_some_iff.mp hm).1
        simp only [List.getElem?_eq_none_iff, List.length_cons, List.length_nil]
        omega
    have hbm : (qn.add t (.key k y)).lastBitmap = qn.lastBitmap := by
      unfold KNode.lastBitmap
      rw [hks]
      exact lastBitmapOf_append_nodel qn.ks more hnd
    rw [hks] at hi
    rcases Nat.lt_or_ge i qn.ks.length with hil | hil
    · rw [List.getElem?_append_left hil] at hi
      obtain ⟨⟨c0, hc0⟩, hL0⟩ := hD q qn hqn i cv z hi hB hv
      have hck0 : c0 ≠ k := by
        intro h
        rw [h] at hc0
        have := KNode.liveAt_fun qn t k x z hk hc0
        omega
      refine ⟨⟨c0, KNode.add_liveAt_keep qn k y t hqw hqt c0 z hc0 hck0⟩, fun hl => ?_⟩
      have hLi := hL0 (by rw [← KNode.add_leaf qn t (.key k y)]; exact hl)
      have hcvk : cv ≠ k := by
        intro h
        rw [h] at hi hLi
        have hci : (k, z) ∈ qn.liveAt t := by
          rw [KNode.liveAt_of_times qn t hqt]
          apply mem_of_lookup_nodup
          rw [KNode.live_lookup]
          exact keyLookup_of_last _ _ _ i z hi hLi
        have := KNode.liveAt_fun qn t k x z hk hci
        omega
      rw [hbm, hks]
      obtain ⟨⟨y0, hy0⟩, hid, hilater⟩ := hLi
      refine ⟨⟨y0, by rw [List.getElem?_append_left hil]; exact hy0⟩, hid, fun j' y' hij' hj' => ?_⟩
      rcases Nat.lt_or_ge j' qn.ks.length with hjl | hjl
      · rw [List.getElem?_append_left hjl] at hj'
        exact hilater j' y' hij' hj'
      · rw [List.getElem?_append_right hjl] at hj'
        exact absurd (hmore cv y' (List.mem_of_getElem? hj')).1 hcvk
    · rw [List.getElem?_append_right hil] at hi
      have hm := hmore cv z (List.mem_of_getElem? hi)
      obtain ⟨hcv, hzy⟩ := hm
      have hi0 := hi
      rw [hcv, hzy] at hi0
      rw [hcv, hzy]
      refine ⟨⟨k, KNode.add_liveAt_new qn k y t hqw hqt⟩, fun _ => ?_⟩
      rw [hbm, hks]
      refine ⟨⟨y, by rw [List.getElem?_append_right hil]; exact hi0⟩, ?_, ?_⟩
      · intro hid
        have := KNode.wf_bitmap_bounds qn hqw i hid
        simp only [KNode.size] at this
        omega
      · intro j' y' hij' hj'
        exfalso
        rw [List.getElem?_append_right (by omega)] at hj'
        rw [hlastk i hil cv z hi j' hij'] at hj'
        cases hj'
  · by_cases hux : u = x
    · rw [hux, hN2x] at hu
      cases hu
      have := unlinked_old_ptrs xn t B hpos (fun c y h => hO x xn hxn c y h) hxw hxt cv z
        (List.mem_of_getElem? hi)
      omega
    · rw [hN2 u huq hux] at hu
      exact hD u un hu i cv z hi hB hv


/-! ## The node-map invariant of root collapse for (B) and (C) -/

/-- (B), (C) and the node facts they need, at node-map level. -/
def J2N (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId) : Prop :=
  TtReachedN N t r ∧ DeadLiveN N t B vals ∧ OldBelowN N t B ∧ OldStartN N t B ∧
    MadeStartN N t B ∧ ValsNoNodeN N vals

/-- The node facts after a node q changed in place to qn2 with the same klongs
before t and the same first time, and a node x taken back or unlinked. -/
theorem j2facts_step (N1 N2 : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (q x : NodeId) (qn qn2 : KNode) (hpos : 0 < t) (hO : OldBelowN N1 t B) (hS : OldStartN N1 t B)
    (hM : MadeStartN N1 t B) (hV : ValsNoNodeN N1 vals)
    (hqn : N1 q = some qn) (hN2q : N2 q = some qn2)
    (hpre : prefixAt qn2.ks (t - 1) = prefixAt qn.ks (t - 1)) (hft : qn2.firstTime = qn.firstTime)
    (hx : ∀ xn2, N2 x = some xn2 → ∃ xn, N1 x = some xn ∧
      prefixAt xn2.ks (t - 1) = prefixAt xn.ks (t - 1) ∧ x < B ∧
      (∀ s, s < t → xn.firstTime = some s → xn2.firstTime = some s))
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) :
    OldBelowN N2 t B ∧ OldStartN N2 t B ∧ MadeStartN N2 t B ∧ ValsNoNodeN N2 vals := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z zn hz cv y hky
    by_cases hzq : z = q
    · rw [hzq, hN2q] at hz; cases hz
      rw [hpre] at hky; exact hO q qn hqn cv y hky
    · by_cases hzx : z = x
      · rw [hzx] at hz
        obtain ⟨xn, hxn, hpx, _, _⟩ := hx zn hz
        rw [hpx] at hky; exact hO x xn hxn cv y hky
      · rw [hN2 z hzq hzx] at hz; exact hO z zn hz cv y hky
  · intro z zn hz hzB
    by_cases hzq : z = q
    · rw [hzq, hN2q] at hz; cases hz
      rw [hft]; exact hS q qn hqn (by rw [← hzq]; exact hzB)
    · by_cases hzx : z = x
      · rw [hzx] at hz hzB
        obtain ⟨xn, hxn, _, _, hfs⟩ := hx zn hz
        obtain ⟨s, hs, hf⟩ := hS x xn hxn hzB
        exact ⟨s, hs, hfs s hs hf⟩
      · rw [hN2 z hzq hzx] at hz; exact hS z zn hz hzB
  · intro z zn hz hzB
    by_cases hzq : z = q
    · rw [hzq, hN2q] at hz; cases hz
      rw [hft]; exact hM q qn hqn (by rw [← hzq]; exact hzB)
    · by_cases hzx : z = x
      · rw [hzx] at hz hzB
        obtain ⟨_, _, _, hxB, _⟩ := hx zn hz
        omega
      · rw [hN2 z hzq hzx] at hz; exact hM z zn hz hzB
  · intro y hy
    by_cases hyq : y = q
    · rw [hyq] at hy; rw [hV q hy] at hqn; cases hqn
    · by_cases hyx : y = x
      · cases h2 : N2 y with
        | none => rfl
        | some yn =>
          rw [hyx] at h2
          obtain ⟨xn, hxn, _, _, _⟩ := hx yn h2
          rw [← hyx, hV y hy] at hxn; cases hxn
      · rw [hN2 y hyq hyx]; exact hV y hy

/-- A made node is at or above B; a node below B starts before t. -/
theorem ge_of_firstTime2 (N : NodeId → Option KNode) (t : Time) (B : NodeId) (hS : OldStartN N t B)
    (q : NodeId) (qn : KNode) (hq : N q = some qn) (hf : qn.firstTime = some t) : B ≤ q := by
  rcases Nat.lt_or_ge q B with h | h
  · obtain ⟨s, hs, hf'⟩ := hS q qn hq h
    rw [hf] at hf'; cases hf'; omega
  · exact h

theorem lt_of_firstTime_ne (N : NodeId → Option KNode) (t : Time) (B : NodeId) (hM : MadeStartN N t B)
    (q : NodeId) (qn : KNode) (hq : N q = some qn) (hf : qn.firstTime ≠ some t) : q < B := by
  rcases Nat.lt_or_ge q B with h | h
  · exact h
  · exact absurd (hM q qn hq h) hf


/-- The node facts after only x taken back or unlinked. -/
theorem j2facts_only (N1 N2 : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (x : NodeId) (hO : OldBelowN N1 t B) (hS : OldStartN N1 t B)
    (hM : MadeStartN N1 t B) (hV : ValsNoNodeN N1 vals)
    (hx : ∀ xn2, N2 x = some xn2 → ∃ xn, N1 x = some xn ∧
      prefixAt xn2.ks (t - 1) = prefixAt xn.ks (t - 1) ∧ x < B ∧
      (∀ s, s < t → xn.firstTime = some s → xn2.firstTime = some s))
    (hN2 : ∀ z, z ≠ x → N2 z = N1 z) :
    OldBelowN N2 t B ∧ OldStartN N2 t B ∧ MadeStartN N2 t B ∧ ValsNoNodeN N2 vals := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z zn hz cv y hky
    by_cases hzx : z = x
    · rw [hzx] at hz
      obtain ⟨xn, hxn, hpx, _, _⟩ := hx zn hz
      rw [hpx] at hky; exact hO x xn hxn cv y hky
    · rw [hN2 z hzx] at hz; exact hO z zn hz cv y hky
  · intro z zn hz hzB
    by_cases hzx : z = x
    · rw [hzx] at hz hzB
      obtain ⟨xn, hxn, _, _, hfs⟩ := hx zn hz
      obtain ⟨s, hs, hf⟩ := hS x xn hxn hzB
      exact ⟨s, hs, hfs s hs hf⟩
    · rw [hN2 z hzx] at hz; exact hS z zn hz hzB
  · intro z zn hz hzB
    by_cases hzx : z = x
    · rw [hzx] at hz hzB
      obtain ⟨_, _, _, hxB, _⟩ := hx zn hz
      omega
    · rw [hN2 z hzx] at hz; exact hM z zn hz hzB
  · intro y hy
    by_cases hyx : y = x
    · cases h2 : N2 y with
      | none => rfl
      | some yn =>
        rw [hyx] at h2
        obtain ⟨xn, hxn, _, _, _⟩ := hx yn h2
        rw [← hyx, hV y hy] at hxn; cases hxn
    · rw [hN2 y hyx]; exact hV y hy

/-- (C) after only x taken back, or unlinked naming nodes below B only. -/
theorem deadLiveN_only (N1 N2 : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (x : NodeId) (hD : DeadLiveN N1 t B vals)
    (hx : ∀ xn2, N2 x = some xn2 → ∀ cv y, Klong.key cv y ∈ xn2.ks → y < B)
    (hN2 : ∀ z, z ≠ x → N2 z = N1 z) : DeadLiveN N2 t B vals := by
  intro u un hu i cv z hi hB hv
  by_cases hux : u = x
  · rw [hux] at hu
    have := hx un hu cv z (List.mem_of_getElem? hi)
    omega
  · rw [hN2 u hux] at hu
    exact hD u un hu i cv z hi hB hv

/-- The facts of a node unlinked: its klongs before t and its first time before t
kept. -/
theorem unlinked_facts (n : KNode) (t : Time) (hpos : 0 < t) :
    prefixAt (if n.lastTime == some t then n.toPrev (t - 1) else n).ks (t - 1) = prefixAt n.ks (t - 1) ∧
    ∀ s, s < t → n.firstTime = some s →
      (if n.lastTime == some t then n.toPrev (t - 1) else n).firstTime = some s := by
  refine ⟨?_, fun s hs hf => ?_⟩
  · split
    · simp only [KNode.toPrev]; exact prefixAt_idem n.ks (t - 1)
    · rfl
  · split
    · exact KNode.firstTime_toPrev n (t - 1) s hf (by omega)
    · exact hf

/-! ## Root collapse at the writer's level -/

/-- What root collapse keeps of (B) and (C): `J2N` of the writer's nodes. -/
def TakeJ2 (c : Ctx) (base : View BVal) (B : NodeId) (v : W) : Prop :=
  J2N (wNode c.p base v) c.i v.top.rootKey B (v.vals.map (·.1))

theorem takeJ2_of_readsAs (c : Ctx) (base : View BVal) (B : NodeId) (v v' : W)
    (h : TakeJ2 c base B v) (hr : ReadsAs c.p base v v') : TakeJ2 c base B v' := by
  unfold TakeJ2
  rw [hr.1, hr.2.1, hr.2.2.2.1]
  exact h

/-- `takeBackRoot` at a segment root x that the transaction made keeps `TakeJ2`. -/
theorem writerWP_takeBackRoot_seg_j2 (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (B : NodeId) (hpos : 0 < c.i) (hJ : TakeJ2 c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) (hmade : n.firstTime = some c.i)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v (fun _ v' => TakeJ2 c base B v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    rw [writerWP_getNode_known leaf ln c _ (by simpa using hlkL)]
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    split
    · rename_i j hj
      split
      · exact writerWP_throw _ _ _ _
      · simp only [putNode, writerWP_bind, writerWP_modify]
        refine (writerWP_takenBack_iff x c _ _).mpr ?_
        simp only
        have hLt' : (x :: v.taken).contains leaf = false := by
          rw [List.contains_cons]
          have : (leaf == x) = false := by simpa using hlx
          rw [this, Bool.false_or]; exact hLt
        have hyt : ∀ y, y ≠ x → (x :: v.taken).contains y = v.taken.contains y := by
          intro y hyx
          rw [List.contains_cons]
          have : (y == x) = false := by simpa using hyx
          simp [this]
        have hfin : ∀ w' : W, w'.vals = v.vals → w'.taken = x :: v.taken →
            w'.nodes = upsert v.nodes leaf (ln.repoint j child) → w'.top = v.top →
            TakeJ2 c base B w' := by
          intro w' h'v h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hX : wNode c.p base w' x = none := by simp [wNode, h't]
          have hBx : B ≤ x := ge_of_firstTime2 _ _ _ hJ.2.2.2.1 x n hwx hmade
          have hxv : x ∉ v.vals.map (·.1) := fun h => by rw [hJ.2.2.2.2.2 x h] at hwx; cases hwx
          have hjk := kd_linkIndex_some ln x k j hj
          have hlen : (prefixAt ln.ks (c.i - 1)).length ≤ j := by
            rcases Nat.lt_or_ge j (prefixAt ln.ks (c.i - 1)).length with hlt | hge
            · have := hJ.2.2.1 leaf ln hwL k x (mem_prefixAt_of_lt ln.ks _ j _ hlt hjk)
              omega
            · exact hge
          have hpre : prefixAt (ln.repoint j child).ks (c.i - 1) = prefixAt ln.ks (c.i - 1) := by
            unfold KNode.repoint
            rw [hjk]
            exact prefixAt_set_late ln.ks (c.i - 1) j k child hlen
              (fun k0 h0 => by rw [hjk] at h0; cases h0; exact ⟨k, x, rfl⟩)
          have hfacts := j2facts_step (wNode c.p base v) (wNode c.p base w') c.i B (v.vals.map (·.1))
            leaf x ln (ln.repoint j child) hpos hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hwL hL' hpre
            (KNode.firstTime_repoint ln j child) (fun xn2 h => by rw [hX] at h; cases h) hoth
          unfold TakeJ2 J2N
          rw [h'top, h'v]
          refine ⟨?_, ?_, hfacts⟩
          · exact ttReachedN_segCollapse (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf
              x child ln (ln.repoint j child) n k hT hlf hwL hk hwx
              (fun c' z hz => by
                rw [KNode.liveAt_of_times n c.i hnt] at hz
                exact ((hlv c' z).mp hz).2)
              hL' (KNode.repoint_liveAt_new ln x child k j c.i hj hlnt)
              (fun c' z hz hck => KNode.repoint_liveAt_keep ln x child k j c.i hj hlnt c' z hz hck)
              hoth hJ.1 (fun xn2 h => by rw [hX] at h; cases h)
          · exact deadLiveN_segTake (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey B _ leaf x
              child ln k j hT hJ.2.1 hlf hwL hlnl hlnt hj hk hBx hxv hL' hX hoth
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf, with room, keeps
`TakeJ2`. -/
theorem writerWP_replaceRoot_seg_j2 (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (B : NodeId) (hpos : 0 < c.i) (hJ : TakeJ2 c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) (hnm : n.firstTime ≠ some c.i)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v (fun _ v' => TakeJ2 c base B v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_fate x n c _ (by simpa using hlkx)) ?_
    intro _ w1 ⟨h1t, h1top, h1v, h1x, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by
      simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    have hX : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } x =
        some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
      simp only [wNode, h1t, hxt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, Ne.symm hlx, h1x]
    have hnwf := hI.2.2.2.1 x n hxR hwx
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    obtain ⟨s0, hs0⟩ : ∃ s0, ln.firstTime = some s0 := by
      rcases Nat.lt_or_ge leaf B with h | h
      · obtain ⟨s, _, hf⟩ := hJ.2.2.2.1 leaf ln hwL h
        exact ⟨s, hf⟩
      · exact ⟨c.i, hJ.2.2.2.2.1 leaf ln hwL h⟩
    obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
    have hfacts := j2facts_step (wNode c.p base v) _ c.i B (v.vals.map (·.1))
      leaf x ln (ln.add c.i (.key k child)) hpos hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hwL hL'
      (KNode.prefixAt_add ln c.i _ hpos) (by rw [KNode.firstTime_add_some ln c.i _ s0 hs0, hs0])
      (fun xn2 h => by
        rw [hX] at h
        cases h
        exact ⟨n, hwx, hupre, hxB, hufirst⟩) hoth
    show J2N _ c.i w1.top.rootKey B (w1.vals.map (·.1))
    rw [show w1.top.rootKey = v.top.rootKey by rw [h1top],
      show w1.vals.map (·.1) = v.vals.map (·.1) by rw [h1v]]
    refine ⟨?_, ?_, hfacts⟩
    · exact ttReachedN_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf
        x child ln (ln.add c.i (.key k child)) n k hT hlf hwL hk hwx
        (fun c' z hz => by
          rw [KNode.liveAt_of_times n c.i hnt] at hz
          exact ((hlv c' z).mp hz).2)
        hL' (KNode.add_liveAt_new ln k child c.i hlnwf hlnt)
        (fun c' z hz hck => KNode.add_liveAt_keep ln k child c.i hlnwf hlnt c' z hz hck)
        hoth hJ.1 (fun xn2 h => by
          rw [hX] at h
          cases h
          exact unlinked_no_time n c.i hpos hnwf hnt)
    · exact deadLiveN_segReplace (wNode c.p base v) _ c.i B _ leaf x child ln n k hpos hJ.2.1 hJ.2.2.1
        hwL hlnwf hlnt hk hxB hwx hnwf hnt hL' hX hoth



/-- The collapse steps at the space root keep `TakeJ2`. -/
theorem writerWP_rootStep_space_j2 (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v) (B : NodeId) (hpos : 0 < c.i)
    (hJ : TakeJ2 c base B v) (hx : x = v.top.rootKey)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only) :
    WriterWP (takeBackRoot x 0 only) c v (fun _ v' => TakeJ2 c base B v') ∧
    (n.firstTime ≠ some c.i → WriterWP (replaceRoot x 0 only) c v (fun _ v' => TakeJ2 c base B v')) := by
  have hxt : v.taken.contains x = false := by rw [hx]; exact hI.1.2.1 _ TReach.root
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hroot : wNode c.p base v v.top.rootKey = some n := by rw [← hx]; exact hwx
  have hnt := hI.1.2.2.1 _ n TReach.root hroot
  have hnwf := hI.2.2.2.1 _ n TReach.root hroot
  have hfin : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
      w3.vals = v.vals →
      (∀ z, z ≠ x → wNode c.p base w3 z = wNode c.p base v z) →
      (∀ xn2, wNode c.p base w3 x = some xn2 → Klong.time c.i ∉ xn2.ks ∧
        (∀ cv y, Klong.key cv y ∈ xn2.ks → y < B) ∧
        prefixAt xn2.ks (c.i - 1) = prefixAt n.ks (c.i - 1) ∧ x < B ∧
        (∀ s, s < c.i → n.firstTime = some s → xn2.firstTime = some s)) →
      TakeJ2 c base B w3 := by
    intro child hptr w3 h3top h3v hN2 hx2
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hptr
    unfold TakeJ2 J2N
    rw [h3top, h3v]
    refine ⟨?_, ?_, ?_⟩
    · refine ttReachedN_spaceCollapse (wNode c.p base v) (wNode c.p base w3) c.i v.top.rootKey child
        n hroot ?_ (fun z hz => hN2 z (by rw [hx]; exact hz)) hJ.1
        (fun xn2 h => (hx2 xn2 (by rw [hx]; exact h)).1)
      intro c' z hz
      rw [KNode.liveAt_of_times n c.i hnt] at hz
      exact ((hlv c' z).mp hz).2
    · exact deadLiveN_only (wNode c.p base v) (wNode c.p base w3) c.i B _ x hJ.2.1
        (fun xn2 h => (hx2 xn2 h).2.1) hN2
    · exact j2facts_only (wNode c.p base v) (wNode c.p base w3) c.i B _ x hJ.2.2.1 hJ.2.2.2.1
        hJ.2.2.2.2.1 hJ.2.2.2.2.2
        (fun xn2 h => ⟨n, hwx, (hx2 xn2 h).2.2.1, (hx2 xn2 h).2.2.2.1, (hx2 xn2 h).2.2.2.2⟩) hN2
  constructor
  · cases hp : n.ptr? only with
    | none =>
      unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_takeBackRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3n, h3v⟩
      have hX : wNode c.p base w3 x = none := by simp [wNode, h3t]
      refine hfin child hp w3 h3top h3v (fun z hz => ?_) (fun xn2 h => by rw [hX] at h; cases h)
      have : w3.taken.contains z = v.taken.contains z := by
        rw [h3t, List.contains_cons]
        have : (z == x) = false := by simpa using hz
        simp [this]
      simp only [wNode, this, h3n]
  · intro hnm
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    cases hp : n.ptr? only with
    | none =>
      unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_replaceRoot_spaceT _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3v, h3x, h3l⟩
      have hX : wNode c.p base w3 x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
        simp only [wNode, h3t, hxt, Bool.false_eq_true, ↓reduceIte, h3x]
      refine hfin child hp w3 h3top h3v (fun z hz => by simp only [wNode, h3t, h3l z hz]) ?_
      intro xn2 h
      rw [hX] at h
      cases h
      obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
      exact ⟨unlinked_no_time n c.i hpos hnwf hnt,
        unlinked_old_ptrs n c.i B hpos (fun cv y h => hJ.2.2.1 x n hwx cv y h) hnwf hnt,
        hupre, hxB, hufirst⟩

/-- Root collapse at any segment keeps `CollGetInv` and `TakeJ2`, given room in
the segment leaf above each segment root that is replaced (cost's
`writerWP_collapseRoot_coll` with J = `TakeJ2`). -/
theorem writerWP_collapseRoot_j2 (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (hpos : 0 < c.i)
    (hroom : ∀ v x n leaf ln k, CollGetInv c base w0 v → TakeJ2 c base B v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    ∀ fuel v, CollGetInv c base w0 v → TakeJ2 c base B v →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInv c base w0 v' ∧
        TakeJ2 c base B v') := by
  refine writerWP_collapseRoot_coll key seg c base hvc w0 (TakeJ2 c base B)
    (fun v v' hJ hr => takeJ2_of_readsAs c base B v v' hJ hr) hroom ?_ ?_
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_j2 x only n c base w0 v hI B hpos hJ hx hlk honly).1
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen]
      exact writerWP_takeBackRoot_seg_j2 x ps0.length only n L ln k c base w0 v hI B hpos hJ hLr hLlk
        hLl hk hlk honly hcv hxl hm hpd hpk
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    have hP0 := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_j2 x only n c base w0 v hI B hpos hJ hx hlk honly).2 hm
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      obtain ⟨hroom1, hdead⟩ := hroom v x n L ln k hI hJ hP0 hlk hxl hm hLr hLlk hLl hk
      rw [hlen]
      exact writerWP_replaceRoot_seg_j2 x ps0.length only n L ln k c base w0 v hI B hpos hJ hLr hLlk
        hLl hk hlk honly hcv hxl hm hpd hpk hroom1 hdead

end SIS.Tree
