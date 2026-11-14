/-
Root collapse keeps the take-back's (C) (bergdb 024-12, TP4; `DeadLiveN`,
TakeBackDead.lean), with (B) (`TtReachedN`) and the facts of the nodes before
the transaction that both need: their klongs before the transaction's time name
nodes below B (`OldBelowN`), their first time is before it (`OldStartN`), the
nodes of the transaction start at it (`MadeStartN`), no node is of a later time
(`TimesN`), and no value of the transaction is a node (`ValsNoNodeN`). With
these, a node with a klong to a node of the transaction is reached and names it
live, so only the segment leaf above names a root taken back.
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

end SIS.Tree
