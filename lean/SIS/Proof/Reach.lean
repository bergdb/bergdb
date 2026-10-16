/-
Proofs, part 2: reachability as an inductive definition, and how it behaves
when P grows.
-/
import SIS.Proof.Basic

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type}

/-- Reachability at time t, as an inductive definition (3.3). -/
inductive Reach (sp : Spec V T) (P : Struct V) (t : Time) : NodeId → Prop
  | root (n : Node V) : P.get? root = some n → Reach sp P t root
  | child {x y : NodeId} {n m : Node V} : Reach sp P t x → P.get? x = some n →
      y ∈ sp.live (n.hist.upTo t) → P.get? y = some m → m.level < n.level → Reach sp P t y

theorem reachFrom_eq (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) (n : Node V) :
    reachFrom sp P t x n =
      x :: (sp.live (n.hist.upTo t)).flatMap (fun y =>
        match P.get? y with
        | some m => if m.level < n.level then reachFrom sp P t y m else []
        | none => []) := by
  rw [reachFrom]; rfl

theorem Reach.isSome {sp : Spec V T} {P : Struct V} {t : Time} {x : NodeId}
    (h : Reach sp P t x) : (P.get? x).isSome := by
  cases h with
  | root n hn => simp [hn]
  | child _ _ _ hm _ => simp [hm]

theorem reach_of_mem_reachFrom (sp : Spec V T) (P : Struct V) (t : Time) :
    ∀ (k : Nat) (x : NodeId) (n : Node V), n.level < k → P.get? x = some n →
      Reach sp P t x → ∀ z, z ∈ reachFrom sp P t x n → Reach sp P t z := by
  intro k
  induction k with
  | zero => intro x n h; omega
  | succ k ih =>
    intro x n hk hx hr z hz
    rw [reachFrom_eq] at hz
    simp only [List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨y, hy, hz⟩
    · exact hr
    · split at hz
      · rename_i m hm
        split at hz
        · rename_i hlt
          exact ih y m (by omega) hm (Reach.child hr hx hy hm hlt) z hz
        · simp at hz
      · simp at hz

theorem mem_reachFrom_of_child (sp : Spec V T) (P : Struct V) (t : Time) :
    ∀ (k : Nat) (x : NodeId) (n : Node V), n.level < k → P.get? x = some n →
      ∀ z m y m', z ∈ reachFrom sp P t x n → P.get? z = some m → y ∈ sp.live (m.hist.upTo t) →
        P.get? y = some m' → m'.level < m.level → y ∈ reachFrom sp P t x n := by
  intro k
  induction k with
  | zero => intro x n h; omega
  | succ k ih =>
    intro x n hk hx z m y m' hz hzm hy hym hlt
    rw [reachFrom_eq] at hz ⊢
    simp only [List.mem_cons, List.mem_flatMap] at hz ⊢
    rcases hz with rfl | ⟨w, hw, hz⟩
    · rw [hx] at hzm
      cases hzm
      right
      refine ⟨y, hy, ?_⟩
      rw [hym]
      simp only [hlt, ite_true]
      rw [reachFrom_eq]
      simp
    · right
      refine ⟨w, hw, ?_⟩
      split at hz
      · rename_i mw hmw
        split at hz
        · rename_i hlt'
          simp only [hlt', ite_true]
          exact ih w mw (by omega) hmw z m y m' hz hzm hy hym hlt
        · simp at hz
      · simp at hz

theorem reachable_iff (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) :
    reachable sp P t x = true ↔ Reach sp P t x := by
  constructor
  · intro h
    simp only [reachable, reachList, List.contains_iff_mem] at h
    split at h
    · rename_i n hn
      exact reach_of_mem_reachFrom sp P t (n.level + 1) root n (by omega) hn (Reach.root n hn) x h
    · simp at h
  · intro h
    simp only [reachable, reachList, List.contains_iff_mem]
    induction h with
    | root n hn =>
      rw [hn]
      simp only
      rw [reachFrom_eq]
      simp
    | child hx hxn hy hym hlt ih =>
      split at ih
      · rename_i n0 hn0
        exact mem_reachFrom_of_child sp P t (n0.level + 1) root n0 (by omega) hn0 _ _ _ _ ih hxn hy
          hym hlt
      · simp at ih

/-- A node reachable at t is the root or on a lower level than the root. -/
theorem reach_level_root {sp : Spec V T} {P : Struct V} {t : Time} {x : NodeId}
    (h : Reach sp P t x) {n0 : Node V} (h0 : P.get? root = some n0) :
    ∀ n, P.get? x = some n → x = root ∨ n.level < n0.level := by
  induction h with
  | root n' _ => intro _ _; left; rfl
  | @child x y nx m _ hxn _ hym hlt ih =>
    intro n hn
    right
    rw [hym] at hn
    cases hn
    rcases ih nx hxn with h | h
    · subst h
      rw [h0] at hxn
      cases hxn
      exact hlt
    · omega

/-- If every node of P is reachable at some time, no entry points to the
root. -/
theorem ptr_ne_root {sp : Spec V T} {P : Struct V} {n0 : Node V} (h0 : P.get? root = some n0)
    (hp : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, ∀ y ∈ sp.ptrs e.val,
      ∃ m, P.get? y = some m ∧ m.level < n.level)
    (hb : ∀ x, (P.get? x).isSome → ∃ t, Reach sp P t x)
    {x : NodeId} {n : Node V} (hx : P.get? x = some n) {e : Entry V} (he : e ∈ n.hist)
    {y : NodeId} (hy : y ∈ sp.ptrs e.val) : y ≠ root := by
  intro hyr
  subst hyr
  obtain ⟨m, hm, hlt⟩ := hp x n hx e he _ hy
  rw [h0] at hm
  cases hm
  obtain ⟨t, hr⟩ := hb x (by rw [hx]; rfl)
  rcases reach_level_root hr h0 n hx with h | h
  · subst h
    rw [h0] at hx
    cases hx
    omega
  · omega

/-- Two structures with the same nodes have the same reachable nodes. -/
theorem SameNodes.reach {sp : Spec V T} {P P' : Struct V} (h : SameNodes P P') {t : Time}
    {x : NodeId} (hr : Reach sp P t x) : Reach sp P' t x := by
  induction hr with
  | root n hn => exact Reach.root n (by rw [← h]; exact hn)
  | child _ hxn hy hym hlt ih => exact Reach.child ih (by rw [← h]; exact hxn) hy (by rw [← h]; exact hym) hlt

theorem SameNodes.reachable {sp : Spec V T} {P P' : Struct V} (h : SameNodes P P') (t : Time)
    (x : NodeId) : reachable sp P t x = reachable sp P' t x := by
  apply Bool.eq_iff_iff.mpr
  rw [reachable_iff, reachable_iff]
  exact ⟨h.reach, h.symm.reach⟩

theorem SameNodes.view {sp : Spec V T} {P P' : Struct V} (h : SameNodes P P') (t : Time) :
    view sp P t = view sp P' t := by
  funext x
  simp only [SIS.view, h.reachable t x, h x]

/-! ### Growing structures -/

/-- P' extends P up to time k: every node of P is in P' with the same level
and kind, and the same entries up to time k. -/
def Grow (P : Struct V) (k : Time) (P' : Struct V) : Prop :=
  ∀ x n, P.get? x = some n → ∃ n', P'.get? x = some n' ∧ n'.level = n.level ∧
    n'.isData = n.isData ∧ n'.hist.upTo k = n.hist.upTo k

theorem Grow.refl (P : Struct V) (k : Time) : Grow P k P :=
  fun _ n h => ⟨n, h, rfl, rfl, rfl⟩

theorem Grow.mono {P P' : Struct V} {k t : Time} (h : Grow P k P') (ht : t ≤ k) : Grow P t P' := by
  intro x n hn
  obtain ⟨n', h1, h2, h3, h4⟩ := h x n hn
  exact ⟨n', h1, h2, h3, upTo_eq_of_le ht h4⟩

theorem Grow.trans {P P' P'' : Struct V} {k k' : Time} (h : Grow P k P') (h' : Grow P' k' P'')
    (hk : k ≤ k') : Grow P k P'' := by
  intro x n hn
  obtain ⟨n', h1, h2, h3, h4⟩ := h x n hn
  obtain ⟨n'', h1', h2', h3', h4'⟩ := h' x n' h1
  exact ⟨n'', h1', h2'.trans h2, h3'.trans h3, (upTo_eq_of_le hk h4').trans h4⟩

theorem Grow.sameNodes {P P' P'' : Struct V} {k : Time} (h : Grow P k P') (h' : SameNodes P' P'') :
    Grow P k P'' := by
  intro x n hn
  obtain ⟨n', h1, h2, h3, h4⟩ := h x n hn
  exact ⟨n', by rw [← h']; exact h1, h2, h3, h4⟩

/-- The changes of transaction i extend P up to every earlier time. -/
theorem grow_apply (P : Struct V) (i : Time) (c : Changes V) {k : Time} (hk : k < i) :
    Grow P k (P.apply i c) := by
  intro x n hn
  refine ⟨_, get?_apply_of_get? hn, rfl, rfl, ?_⟩
  simp only
  rw [upTo_append, upTo_eq_nil (addsFor c i x) k, List.append_nil]
  intro e he
  rw [mem_addsFor] at he
  obtain ⟨h1, -⟩ := he
  omega

/-- Every pointer of every entry of P leads to a node of P on a lower level (A4). -/
def PtrsOK (sp : Spec V T) (P : Struct V) : Prop :=
  ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, ∀ y ∈ sp.ptrs e.val, ∃ m, P.get? y = some m ∧ m.level < n.level

/-- The live pointers of a history are pointers of its entries (SpecOK.liveSub). -/
def LiveSub (sp : Spec V T) : Prop :=
  ∀ (h : History V) y, y ∈ sp.live h → ∃ e ∈ h, y ∈ sp.ptrs e.val

theorem reach_of_grow {sp : Spec V T} {P P' : Struct V} {k t : Time} (hg : Grow P k P')
    (ht : t ≤ k) {x : NodeId} (hr : Reach sp P t x) : Reach sp P' t x := by
  induction hr with
  | root n hn =>
    obtain ⟨n', h1, -⟩ := hg _ n hn
    exact Reach.root n' h1
  | child _ hxn hy hym hlt ih =>
    obtain ⟨n', h1, h2, -, h4⟩ := hg _ _ hxn
    obtain ⟨m', h1', h2', -, -⟩ := hg _ _ hym
    have h4t := upTo_eq_of_le ht h4
    exact Reach.child ih h1 (by rw [h4t]; exact hy) h1' (by rw [h2, h2']; exact hlt)

theorem reach_of_grow_back {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hroot : (P.get? root).isSome) (hg : Grow P k P') (ht : t ≤ k)
    {x : NodeId} (hr : Reach sp P' t x) : Reach sp P t x := by
  induction hr with
  | root n hn =>
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hroot
    exact Reach.root n0 h0
  | @child x y n m _ hxn hy hym hlt ih =>
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp ih.isSome
    obtain ⟨n', h1, h2, -, h4⟩ := hg _ _ h0
    rw [hxn] at h1
    cases h1
    have h4t := upTo_eq_of_le ht h4
    rw [h4t] at hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨m0, hm0, hlt0⟩ := hp _ _ h0 e (mem_upTo.mp he).1 y hye
    exact Reach.child ih h0 hy hm0 hlt0

theorem reach_grow_iff {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hroot : (P.get? root).isSome) (hg : Grow P k P') (ht : t ≤ k)
    (x : NodeId) : Reach sp P' t x ↔ Reach sp P t x :=
  ⟨reach_of_grow_back hls hp hroot hg ht, reach_of_grow hg ht⟩

theorem reachable_grow {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hroot : (P.get? root).isSome) (hg : Grow P k P') (ht : t ≤ k)
    (x : NodeId) : reachable sp P' t x = reachable sp P t x := by
  apply Bool.eq_iff_iff.mpr
  rw [reachable_iff, reachable_iff]
  exact reach_grow_iff hls hp hroot hg ht x

theorem view_grow {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hroot : (P.get? root).isSome) (hg : Grow P k P') (ht : t ≤ k) :
    view sp P' t = view sp P t := by
  funext x
  simp only [SIS.view, reachable_grow hls hp hroot hg ht x]
  split
  · rename_i hr
    rw [reachable_iff] at hr
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hr.isSome
    obtain ⟨n', h1, h2, h3, h4⟩ := hg _ _ h0
    rw [h0, h1]
    simp only [Option.map_some]
    rw [upTo_eq_of_le ht h4, h2, h3]
  · rfl

end SIS
