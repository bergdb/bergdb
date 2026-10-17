/-
Proofs about reclaim, part 3 (bergdb item 001, WP R4): structures that agree
for lookups from a time f on. A startup from a cut stream rebuilds P that way:
the nodes that lookups from f on reach are P's, a virtual root has P's live
children from f on, and other nodes may be missing or wrong.
-/
import SIS.Proof.CutRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- P' agrees with P for lookups at every time from f to t: both have a root, of
the same level, and with a virtual root the same live children at each of those
times; every other node that is reachable in P at one of those times has P's
node in P'; P' has no node that P lacks; P''s entries are up to t, and a
virtual root's are entries for root children. -/
structure CutAgree (sp : Spec V T) (f t : Time) (P P' : Struct V) : Prop where
  rootP : (P.get? root).isSome
  rootP' : (P'.get? root).isSome
  rootLive : sp.virt = true → ∀ n n', P.get? root = some n → P'.get? root = some n' →
    n.level = n'.level ∧ ∀ t', f ≤ t' → t' ≤ t → sp.live (n.hist.upTo t') = sp.live (n'.hist.upTo t')
  nodes : ∀ x t', f ≤ t' → t' ≤ t → (sp.virt = true → x ≠ root) → reachable sp P t' x = true →
    P'.get? x = P.get? x
  ids : ∀ x, (P'.get? x).isSome → (P.get? x).isSome
  times' : ∀ x n, P'.get? x = some n → ∀ e ∈ n.hist, e.time ≤ t
  rootVals' : sp.virt = true → ∀ n, P'.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z

section Agree

variable {sp : Spec V T} {f t : Time} {P P' : Struct V}

/-- The root's node in P' is P's, without a virtual root. -/
theorem CutAgree.root_eq (h : CutAgree sp f t P P') (hv : sp.virt = false) (hft : f ≤ t) :
    P'.get? root = P.get? root := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
  exact h.nodes root f (Nat.le_refl _) hft (by simp [hv]) ((reachable_iff _ _ _ _).mpr (Reach.root n0 h0))

/-- What is reachable in P at a time from f to t is reachable in P'. -/
theorem CutAgree.reach (h : CutAgree sp f t P P') {t' : Time} (h1 : f ≤ t') (h2 : t' ≤ t)
    {x : NodeId} (hr : Reach sp P t' x) : Reach sp P' t' x := by
  induction hr with
  | root n hn =>
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    exact Reach.root n' hn'
  | @child x y n m hx hxn hy hym hlt ih =>
    have hyr : Reach sp P t' y := Reach.child hx hxn hy hym hlt
    -- y's node in P'.
    have hy' : P'.get? y = some m := by
      by_cases hv : sp.virt = true
      · by_cases hyroot : y = root
        · exfalso
          subst hyroot
          -- the root is not a child: it is on the highest level.
          rcases reach_level_root hx hym n hxn with h3 | h3
          · subst h3
            rw [hym] at hxn
            cases hxn
            omega
          · omega
        · rw [h.nodes y t' h1 h2 (fun _ => hyroot) ((reachable_iff _ _ _ _).mpr hyr), hym]
      · rw [h.nodes y t' h1 h2 (fun h' => absurd h' hv) ((reachable_iff _ _ _ _).mpr hyr), hym]
    by_cases hv : sp.virt = true
    · by_cases hxroot : x = root
      · subst hxroot
        obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
        obtain ⟨hlev, hlive⟩ := h.rootLive hv n n' hxn hn'
        exact Reach.child ih hn' (by rw [← hlive t' h1 h2]; exact hy) hy' (by rw [← hlev]; exact hlt)
      · have hx' : P'.get? x = some n := by
          rw [h.nodes x t' h1 h2 (fun _ => hxroot) ((reachable_iff _ _ _ _).mpr hx), hxn]
        exact Reach.child ih hx' hy hy' hlt
    · have hx' : P'.get? x = some n := by
        rw [h.nodes x t' h1 h2 (fun h' => absurd h' hv) ((reachable_iff _ _ _ _).mpr hx), hxn]
      exact Reach.child ih hx' hy hy' hlt

/-- What is reachable in P' at a time from f to t is reachable in P, if P's
pointers lead to nodes of P on lower levels. -/
theorem CutAgree.reach_back (h : CutAgree sp f t P P') (hls : LiveSub sp) (hp : PtrsOK sp P)
    {t' : Time} (h1 : f ≤ t') (h2 : t' ≤ t) {x : NodeId} (hr : Reach sp P' t' x) : Reach sp P t' x := by
  induction hr with
  | root n hn =>
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
    exact Reach.root n0 h0
  | @child x y n' m' _ hxn hy _ _ ih =>
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ih.isSome
    -- y is a live child at t' of x's node in P.
    have hyP : y ∈ sp.live (n.hist.upTo t') := by
      by_cases hv : sp.virt = true
      · by_cases hxroot : x = root
        · subst hxroot
          obtain ⟨-, hlive⟩ := h.rootLive hv n n' hn hxn
          rw [hlive t' h1 h2]; exact hy
        · rw [h.nodes x t' h1 h2 (fun _ => hxroot) ((reachable_iff _ _ _ _).mpr ih), hn] at hxn
          cases hxn
          exact hy
      · rw [h.nodes x t' h1 h2 (fun h' => absurd h' hv) ((reachable_iff _ _ _ _).mpr ih), hn] at hxn
        cases hxn
        exact hy
    obtain ⟨e, he, hye⟩ := hls _ _ hyP
    obtain ⟨m, hm, hlt⟩ := hp x n hn e (mem_upTo.mp he).1 y hye
    exact Reach.child ih hn hyP hm hlt

theorem CutAgree.reachable_eq (h : CutAgree sp f t P P') (hls : LiveSub sp) (hp : PtrsOK sp P)
    {t' : Time} (h1 : f ≤ t') (h2 : t' ≤ t) (x : NodeId) :
    reachable sp P' t' x = reachable sp P t' x := by
  apply Bool.eq_iff_iff.mpr
  rw [reachable_iff, reachable_iff]
  exact ⟨h.reach_back hls hp h1 h2, h.reach h1 h2⟩

/-- Lookups from f to t give the same in P and P' (`SameFrom`). -/
theorem CutAgree.sameFrom (h : CutAgree sp f t P P') (hls : LiveSub sp) (hp : PtrsOK sp P) :
    SameFrom sp f t P' P := by
  intro t' h1 h2
  refine ⟨fun x hx => ?_, fun hv => ?_⟩
  · simp only [view, h.reachable_eq hls hp h1 h2 x]
    split
    · rename_i hr
      by_cases hv : sp.virt = true
      · rw [h.nodes x t' h1 h2 hx hr]
      · rw [h.nodes x t' h1 h2 (fun h' => absurd h' hv) hr]
    · rfl
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    simp only [view, h.reachable_eq hls hp h1 h2 root,
      show reachable sp P t' root = true from (reachable_iff _ _ _ _).mpr (Reach.root n hn), ite_true,
      hn, hn', Option.map_some, Option.some.injEq]
    exact ((h.rootLive hv n n' hn hn').2 t' h1 h2).symm

/-- A node of P after the changes at time i. -/
theorem get?_apply_some {P : Struct V} {i : Time} {c : Changes V} {x : NodeId} {n : Node V}
    (h : (P.apply i c).get? x = some n) :
    ∃ n0, (P.get? x).or (newNodeOf c x) = some n0 ∧ n = { n0 with hist := n0.hist ++ addsFor c i x } := by
  rw [get?_apply] at h
  cases h0 : (P.get? x).or (newNodeOf c x) with
  | none => rw [h0] at h; cases h
  | some n0 => rw [h0] at h; exact ⟨n0, rfl, (Option.some.inj h).symm⟩

theorem lookup_newNodes (l : List NewNode) {x : NodeId} {n : Node V}
    (h : List.lookup x (l.map (fun n => (n.id, ({ level := n.level, isData := n.isData, hist := [] } : Node V)))) =
      some n) : n.hist = [] := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.lookup_cons] at h
    split at h
    · cases h; rfl
    · exact ih h

theorem newNodeOf_hist {c : Changes V} {x : NodeId} {n : Node V} (h : newNodeOf c x = some n) :
    n.hist = [] := lookup_newNodes c.new h

/-- Agreement up to t, and the same change at t + 1 applied to both: agreement up
to t + 1. -/
theorem CutAgree.apply (h : CutAgree sp f t P P') (hft : f ≤ t) (hls : LiveSub sp) (hp : PtrsOK sp P)
    (htimes : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ t)
    {c : Changes V} (hstep : StepOK sp P (t + 1) c) (hvl : VirtLiveOK sp)
    (hrootv : sp.virt = true → ∀ n, P.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z)
    (hadds : sp.virt = true → ∀ a ∈ c.adds, a.1 = root → ∃ z, a.2 = sp.rootVal z) :
    CutAgree sp f (t + 1) (P.apply (t + 1) c) (P'.apply (t + 1) c) where
  rootP := by
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
    rw [get?_apply_of_get? h0]; rfl
  rootP' := by
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [get?_apply_of_get? h0]; rfl
  rootLive := by
    intro hv n n' hn hn'
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [get?_apply_of_get? h0, Option.some.injEq] at hn
    rw [get?_apply_of_get? h0', Option.some.injEq] at hn'
    subst hn hn'
    obtain ⟨hlev, hlive⟩ := h.rootLive hv n0 n0' h0 h0'
    refine ⟨hlev, fun t' h1 h2 => ?_⟩
    simp only
    have hA : ∀ e ∈ addsFor c (t + 1) root, e.time = t + 1 := fun e he => (mem_addsFor.mp he).1
    rcases Nat.lt_or_ge t' (t + 1) with h3 | h3
    · -- Before the change: as before.
      rw [upTo_append, upTo_append, upTo_eq_nil (addsFor c (t + 1) root) t' (fun e he => by rw [hA e he]; omega),
        List.append_nil, List.append_nil]
      exact hlive t' h1 (by omega)
    · have ht' : t' = t + 1 := by omega
      subst ht'
      rw [upTo_append, upTo_append, upTo_of_forall (addsFor c (t + 1) root) (t + 1) (fun e he => Nat.le_of_eq (hA e he)),
        upTo_of_forall n0.hist (t + 1) (fun e he => by have := htimes root n0 h0 e he; omega),
        upTo_of_forall n0'.hist (t + 1) (fun e he => by have := h.times' root n0' h0' e he; omega)]
      cases hAe : addsFor c (t + 1) root with
      | nil =>
        rw [List.append_nil, List.append_nil,
          ← upTo_of_forall n0.hist t (fun e he => htimes root n0 h0 e he),
          ← upTo_of_forall n0'.hist t (fun e he => h.times' root n0' h0' e he)]
        exact hlive t hft (Nat.le_refl _)
      | cons a as =>
        have hvals : ∀ e ∈ addsFor c (t + 1) root, ∃ z, e.val = sp.rootVal z := by
          intro e he
          obtain ⟨-, hm⟩ := mem_addsFor.mp he
          exact hadds hv _ hm rfl
        rw [hvl hv _ (fun e he => by
              rcases List.mem_append.mp he with he | he
              · exact hrootv hv n0 h0 e he
              · rw [← hAe] at he; exact hvals e he),
          hvl hv _ (fun e he => by
              rcases List.mem_append.mp he with he | he
              · exact h.rootVals' hv n0' h0' e he
              · rw [← hAe] at he; exact hvals e he),
          List.getLast?_append, List.getLast?_append]
        obtain ⟨e7, h7⟩ := Option.isSome_iff_exists.mp (show ((a :: as).getLast?).isSome by simp)
        rw [h7]
        rfl
  nodes := by
    intro x t' h1 h2 hxr hr
    have hsame : P'.get? x = P.get? x := by
      rcases Nat.lt_or_ge t' (t + 1) with h3 | h3
      · obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
        rw [reachable_grow hls hp (by rw [h0]; rfl) (grow_apply P (t + 1) c (k := t') h3) (Nat.le_refl _)] at hr
        exact h.nodes x t' h1 (by omega) hxr hr
      · have ht' : t' = t + 1 := by omega
        subst ht'
        rcases hstep.noRes x hr with h4 | h4
        · exact h.nodes x t hft (Nat.le_refl _) hxr (by simpa using h4)
        · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h4
          have h5 := hstep.fresh nn hnn
          rw [hid] at h5
          rw [h5]
          cases h6 : P'.get? x with
          | none => rfl
          | some _ =>
            have := h.ids x (by rw [h6]; rfl)
            rw [h5] at this; cases this
    rw [get?_apply, get?_apply, hsame]
  ids := by
    intro x hx
    rw [get?_apply] at hx ⊢
    cases h1 : P'.get? x with
    | some n => rw [h1] at hx; have := h.ids x (by rw [h1]; rfl); cases h2 : P.get? x with
      | none => rw [h2] at this; cases this
      | some _ => rfl
    | none =>
      rw [h1] at hx
      simp only [Option.none_or] at hx
      cases h2 : P.get? x with
      | some _ => rfl
      | none => simpa using hx
  times' := by
    intro x n hn e he
    obtain ⟨n0, h0, rfl⟩ := get?_apply_some hn
    rcases List.mem_append.mp he with he | he
    · cases h1 : P'.get? x with
      | some n1 =>
        rw [h1] at h0
        simp only [Option.some_or, Option.some.injEq] at h0
        subst h0
        have := h.times' x n1 h1 e he
        omega
      | none =>
        rw [h1] at h0
        simp only [Option.none_or] at h0
        rw [newNodeOf_hist h0] at he
        cases he
    · rw [(mem_addsFor.mp he).1]
      exact Nat.le_refl _
  rootVals' := by
    intro hv n hn e he
    obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [get?_apply_of_get? h0', Option.some.injEq] at hn
    subst hn
    rcases List.mem_append.mp he with he | he
    · exact h.rootVals' hv n0' h0' e he
    · obtain ⟨-, hm⟩ := mem_addsFor.mp he
      exact hadds hv _ hm rfl

end Agree

end SIS
