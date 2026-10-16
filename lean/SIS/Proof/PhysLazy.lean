/-
Proofs about the physical layer, part 13: the rerun of a lazy startup, one
transaction after another, keeps the invariant (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysStep

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The parts of `lazyStartup` -/

/-- Step 1 of `lazyStartup`, for one node of the section. -/
def secStep (sp : Spec V T) (S : Stream V T) (m : Mem V) (x : NodeId) : Mem V :=
  match newest S (lastSp S) x with
  | some w =>
    if (w.hist.upTo (lastSp S)).isEmpty then m else
    let (m', h) := m.addObj (canonOfVersion sp S (lastSp S) w)
    m'.setTable x h
  | none => m

/-- The memory before step 1. -/
def mem0 (S : Stream V T) : Mem V := { objs := [], table := [], s := lastSp S, root := 0, next := 1 }

/-- Step 1 of `lazyStartup`: the section. -/
def lazySec (sp : Spec V T) (S : Stream V T) : Mem V :=
  (sectionNodes S (lastSp S)).foldl (secStep sp S) (mem0 S)

/-- Step 2 of `lazyStartup`: the root. -/
def lazyRoot (sp : Spec V T) (S : Stream V T) (m1 : Mem V) : Mem V :=
  let s := lastSp S
  if sp.virt then
    let rv := rootVersion sp s (topsRead sp S s true)
    let (m', h) := m1.addObj { (canonOfVersion sp S s rv) with hist := rv.hist, pos := none }
    { m'.setTable root h with root := h }
  else
    match m1.canonicalOf root with
    | some h => { m1 with root := h }
    | none =>
      match topVersion S s true with
      | some w =>
        let (m', h) := m1.addObj (canonOfVersion sp S s w)
        { m'.setTable root h with root := h }
      | none => m1

/-- The memory before the rerun. -/
def lazyBase (sp : Spec V T) (S : Stream V T) : Mem V :=
  (lazyRoot sp S (lazySec sp S)).linkCanonical

/-- One transaction of the rerun (step 3 of `lazyStartup`). -/
def rerunStep (sp : Spec V T) (S : Stream V T) (acc : Mem V × Struct V) (j : Nat) :
    Mem V × Struct V :=
  match S[j]? with
  | some R =>
    match R.trans with
    | some tr =>
      let P := acc.2
      let c := sp.exec tr j (view sp P (j - 1))
      let path := pathOf sp P c j
      let path' := path.mergeSort (fun a b => decide
        (((P.get? b).map (·.level)).getD 0 ≤ ((P.get? a).map (·.level)).getD 0))
      let m := path'.foldl (Mem.reachOnPath sp S P j path) acc.1
      let m := m.applyChange sp P j c
      let m := R.gd.foldl (Mem.canonicalNode sp S) m
      (m, P.apply j c)
    | none => acc
  | none => acc

theorem lazyStartup_eq (sp : Spec V T) (S : Stream V T) :
    lazyStartup sp S = ((sectionIdx S (lastSp S)).foldl (rerunStep sp S)
      (lazyBase sp S, baseStruct sp S (lastSp S) true)).1 := rfl

theorem rerunStep_eq (sp : Spec V T) (S : Stream V T) (acc : Mem V × Struct V) {j : Nat}
    {R : Record V T} {tr : T} (hR : S[j]? = some R) (htr : R.trans = some tr) :
    rerunStep sp S acc j =
      (R.gd.foldl (Mem.canonicalNode sp S)
        ((((pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j).mergeSort
          (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))).foldl
          (Mem.reachOnPath sp S acc.2 j (pathOf sp acc.2 (sp.exec tr j (view sp acc.2 (j - 1))) j))
          acc.1).applyChange sp acc.2 j (sp.exec tr j (view sp acc.2 (j - 1)))),
       acc.2.apply j (sp.exec tr j (view sp acc.2 (j - 1)))) := by
  unfold rerunStep
  rw [hR]
  simp only [htr]
  rfl

/-! ### Facts of the run -/

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem pctx_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length) :
    PCtx sp (st sp al ts k) k :=
  ⟨inv_st sp al ts hok hst k hk, hok.1.liveSub, dataOnce_st sp al ts hok hst k hk⟩

/-- A node reachable at t, not the root, has a parent reachable at t. -/
theorem reach_parent {P : Struct V} {t : Time} {x : NodeId} (hr : reachable sp P t x = true)
    (hx : x ≠ root) :
    ∃ p np nx, reachable sp P t p = true ∧ P.get? p = some np ∧ P.get? x = some nx ∧
      nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo t) := by
  rw [reachable_iff] at hr
  cases hr with
  | root n hn => exact absurd rfl hx
  | child hp hn hy hm hlt => exact ⟨_, _, _, (reachable_iff _ _ _ _).mpr hp, hn, hm, hlt, hy⟩

/-- The paths of a transaction, highest level first. -/
theorem pairwise_byLevelDesc (P : Struct V) (xs : List NodeId) :
    (xs.mergeSort (fun a b => decide (lev P b ≤ lev P a))).Pairwise
      (fun a b => lev P b ≤ lev P a) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (lev P b ≤ lev P a))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  simpa using h

/-- One transaction of the rerun keeps the invariant, from K to K + 1, and
the structure that directs it is the run's. -/
theorem rerunStep_ok (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) {k K : Nat} (hk : k ≤ ts.length)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hKk : K < k) {acc : Mem V × Struct V}
    (hm : MemInv sp (st sp al ts k) K acc.1) (hP : SameNodes acc.2 (st sp al ts K).P) :
    MemInv sp (st sp al ts k) (K + 1) (rerunStep sp (st sp al ts k).S acc (K + 1)).1 ∧
      SameNodes (rerunStep sp (st sp al ts k).S acc (K + 1)).2 (st sp al ts (K + 1)).P := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hctx := pctx_st hok hst hk
  have hls : LiveSub sp := hok.1.liveSub
  have hKt : K < ts.length := by omega
  -- Record K + 1 and its transaction.
  have htr := st_trans sp al ts hok hst (j := K + 1) (k := k) (by omega) (by omega) hk
  simp only [Nat.add_sub_cancel] at htr
  obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[K + 1]? = some R ∧ R.trans = some ts[K] := by
    cases h : (st sp al ts k).S[K + 1]? with
    | none => rw [h] at htr; cases htr
    | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
  -- The states at K and K + 1.
  have hkK : KCtx sp (st sp al ts k) (st sp al ts K) K := kctx_st sp al ts hok hj (by omega) hk
  have hkJ : KCtx sp (st sp al ts k) (st sp al ts (K + 1)) (K + 1) := kctx_st sp al ts hok hj (by omega) hk
  rw [st_succ sp al ts hKt] at hkJ
  have hlenK := st_len sp al ts hok hst (j := K) (by omega)
  -- The change.
  have hc : sp.exec ts[K] (K + 1) (view sp acc.2 (K + 1 - 1)) =
      (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel, hP.view K]
  have hstep : StepOK sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel]
    exact hok.2 K hKt
  have hphs : PhysStep sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel]
    exact hph K hKt
  rw [rerunStep_eq sp _ acc hR hRt, hc]
  generalize hcdef : (parts sp al (st sp al ts K) ts[K]).c = c at hstep hphs
  simp only
  -- The writer reaches the nodes of the paths.
  have hpath : ∀ p ∈ pathOf sp acc.2 c (K + 1), reachable sp (st sp al ts k).P K p = true := by
    intro p hp
    have := (mem_pathOf hp).1
    rw [Nat.add_sub_cancel, hP.reachable] at this
    rw [hkK.reachable_eq hls (Nat.le_refl K)]
    exact this
  have hparent : ∀ x ∈ pathOf sp acc.2 c (K + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp acc.2 c (K + 1), ∃ np nx, acc.2.get? p = some np ∧ acc.2.get? x = some nx ∧
        nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo K) := by
    intro x hx hxr
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent (mem_pathOf hx).1 hxr
    refine ⟨p, pathOf_parent hx hrp hnp hxl hnx hlt, np, nx, hnp, hnx, hlt, ?_⟩
    simpa using hxl
  obtain ⟨hm1, -, hcan1⟩ := MemInv.reachPath_ok hctx hkK hP hpath hparent
    ((pathOf sp acc.2 c (K + 1)).mergeSort (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) []
    acc.1 hm (by simp) (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact pairwise_byLevelDesc _ _)
  -- The change applied.
  rw [applyChange_congr hP]
  subst hcdef
  have hm2 := hm1.applyChange_ok hctx hkK hkJ hok.1 hj hstep hphs
    (fun x hx => hcan1 x (by rw [pathOf_congr hP]; exact hx))
  refine ⟨?_, ?_⟩
  · rw [foldl_canonicalNode_noop sp _ _ R.gd
      (fun x hx => hm2.coverGd (K + 1) R x (by omega) (Nat.le_refl _) hR hx)]
    exact hm2
  · rw [st_P_succ sp al ts hok hst hKt]
    have : (parts sp al (st sp al ts K) ts[K]).c =
        sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K) := by
      rw [parts_c, hlenK, Nat.add_sub_cancel]
    rw [this]
    exact hP.apply _ _

/-- The rerun keeps the invariant, from the startup pos s to k. -/
theorem rerun_fold_ok (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) {k : Nat} (hk : k ≤ ts.length) {m0 : Mem V} {P0 : Struct V}
    (hm0 : MemInv sp (st sp al ts k) (lastSp (st sp al ts k).S) m0)
    (hP0 : SameNodes P0 (st sp al ts (lastSp (st sp al ts k).S)).P) :
    MemInv sp (st sp al ts k) k ((sectionIdx (st sp al ts k).S (lastSp (st sp al ts k).S)).foldl
      (rerunStep sp (st sp al ts k).S) (m0, P0)).1 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ n, n ≤ k - s →
      MemInv sp (st sp al ts k) (s + n)
          ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, P0)).1 ∧
        SameNodes ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S) (m0, P0)).2
          (st sp al ts (s + n)).P := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hm0, hP0⟩
    | succ n ih =>
      intro hn
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      obtain ⟨h1, h2⟩ := ih (by omega)
      have := rerunStep_ok hok hph hj hk (K := s + n) (by rw [hs]; omega) (by omega) h1 h2
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      exact this
  have := (key (k - s) (Nat.le_refl _)).1
  rwa [show s + (k - s) = k by omega] at this

end Run

end SIS
