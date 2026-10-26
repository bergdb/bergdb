/-
R4 checked in linear time (bergdb item 001, WP C2). The assumption R4 of
`VirtStep` asks that every older root child can be reached from the new one
through pointers between root children; the checker evaluated it with
`topClosure`, which walks every path between root children and is
exponential in their number (F1-008-13's review, review-13-claude, section
5.1, in the f1 repository). BergDB's top nodes have ordinals, a top node's
level minus `topLevel` (bergdb 011-11, 8.4), and each top node but
the first points to the one before it (the skip pointer of the lowest set bit
of its ordinal). `PredChain` and `closure_of_chain` are review-13-claude's
`R4Bridge.lean`, with its proofs: if the chain holds after the step, and the
new root child has the largest ordinal, R4 holds. The checker tests these
conditions (`r4Fast`) and evaluates `topClosure` only when they fail. Not part
of the trusted part.
-/
import SIS.Proof.VStep
import Check.Fast

set_option linter.unusedSectionVars false

namespace SIS.TopBridge

open SIS

variable {V T : Type} [DecidableEq V]

/-- Each top with a positive ordinal points to a top with the ordinal one less,
on a lower level. Ordinals of distinct tops differ. -/
structure PredChain (sp : Spec V T) (P : Struct V) (ord : NodeId → Nat) : Prop where
  pred : ∀ z n, P.get? z = some n → z ≠ root → sp.topLevel ≤ n.level → 0 < ord z →
    ∃ y m, P.get? y = some m ∧ y ≠ root ∧ sp.topLevel ≤ m.level ∧ m.level < n.level ∧
      ord y = ord z - 1 ∧ y ∈ pointees sp n.hist
  inj : ∀ y z m n, P.get? y = some m → P.get? z = some n → y ≠ root → z ≠ root →
    sp.topLevel ≤ m.level → sp.topLevel ≤ n.level → ord y = ord z → y = z

/-- Every top with an ordinal at most z's is in z's top closure. -/
theorem mem_topClosure (sp : Spec V T) (P : Struct V) (ord : NodeId → Nat)
    (hc : PredChain sp P ord) :
    ∀ d z n, ord z = d → P.get? z = some n → z ≠ root → sp.topLevel ≤ n.level →
      ∀ y m, P.get? y = some m → y ≠ root → sp.topLevel ≤ m.level → ord y ≤ ord z →
        y ∈ topClosure sp P z n := by
  intro d
  induction d with
  | zero =>
    intro z n hd hz hzr hzl y m hy hyr hyl hle
    have := hc.inj y z m n hy hz hyr hzr hyl hzl (by omega)
    subst this; rw [topClosure_eq sp]; exact List.mem_cons_self
  | succ d ih =>
    intro z n hd hz hzr hzl y m hy hyr hyl hle
    by_cases he : ord y = ord z
    · have := hc.inj y z m n hy hz hyr hzr hyl hzl he
      subst this; rw [topClosure_eq sp]; exact List.mem_cons_self
    · obtain ⟨p, mp, hp, hpr, hpl, hlt, hpo, hpin⟩ := hc.pred z n hz hzr hzl (by omega)
      rw [topClosure_eq sp]
      apply List.mem_cons_of_mem
      rw [List.mem_flatMap]
      refine ⟨p, hpin, ?_⟩
      rw [hp]
      simp only [hpl, hlt, and_self, ite_true]
      exact ih p mp (by omega) hp hpr hpl y m hy hyr hyl (by omega)

/-! ### The checker's test of the chain -/

/-- The ordinal of a node: its level minus `topLevel` (BergDB's top node id). -/
def ordOf (sp : Spec V T) (g : NodeId → Option (Node V)) (z : NodeId) : Nat :=
  match g z with
  | some n => n.level - sp.topLevel
  | none => 0

/-- Is z a top (a root child) of the nodes that g gives? -/
def isTopG (sp : Spec V T) (g : NodeId → Option (Node V)) (z : NodeId) : Bool :=
  z != root && match g z with
    | some n => decide (sp.topLevel ≤ n.level)
    | none => false

/-- The chain, tested on the tops among ids, with the nodes through g: each top
with a positive ordinal has a pointee that is a top on a lower level with the
ordinal one less; no two tops have the same ordinal. -/
def chainB (sp : Spec V T) (g : NodeId → Option (Node V)) (ids : List NodeId) : Bool :=
  let tops := ids.filter (isTopG sp g)
  tops.all (fun z => match g z with
    | some n => ordOf sp g z == 0 || (pointees sp n.hist).any (fun y =>
        isTopG sp g y && match g y with
          | some m => decide (m.level < n.level) && ordOf sp g y == ordOf sp g z - 1
          | none => false)
    | none => false) &&
  tops.all (fun z => tops.all (fun y => y == z || ordOf sp g y != ordOf sp g z))

theorem mem_allIds_of_get? {P : Struct V} {z : NodeId} {n : Node V} (h : P.get? z = some n) :
    z ∈ allIds P := by
  unfold allIds
  rw [List.mem_eraseDups]
  exact List.mem_map.mpr ⟨(z, n), mem_of_get? h, rfl⟩

theorem chainB_sound (sp : Spec V T) (P : Struct V)
    (h : chainB sp (fun y => P.get? y) (allIds P) = true) :
    PredChain sp P (ordOf sp (fun y => P.get? y)) := by
  unfold chainB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hpred, hinj⟩ := h
  have hmem : ∀ z n, P.get? z = some n → z ≠ root → sp.topLevel ≤ n.level →
      z ∈ (allIds P).filter (isTopG sp (fun y => P.get? y)) := by
    intro z n hz hzr hzl
    rw [List.mem_filter]
    refine ⟨mem_allIds_of_get? hz, ?_⟩
    unfold isTopG
    simp [hz, hzr, hzl]
  constructor
  · intro z n hz hzr hzl hord
    have hz' := hpred z (hmem z n hz hzr hzl)
    simp only [hz] at hz'
    have h0 : (ordOf sp (fun y => P.get? y) z == 0) = false := by
      have : 0 < ordOf sp (fun y => P.get? y) z := hord
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    rw [h0, Bool.false_or, List.any_eq_true] at hz'
    obtain ⟨y, hy, hyc⟩ := hz'
    rw [Bool.and_eq_true] at hyc
    obtain ⟨hyt, hyc⟩ := hyc
    cases hgy : P.get? y with
    | none => simp [hgy] at hyc
    | some m =>
      simp only [hgy, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hyc
      unfold isTopG at hyt
      simp only [hgy, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hyt
      exact ⟨y, m, hgy, hyt.1, hyt.2, hyc.1, hyc.2, hy⟩
  · intro y z m n hy hz hyr hzr hyl hzl he
    have hyz := hinj z (hmem z n hz hzr hzl) y (hmem y m hy hyr hyl)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hyz
    rcases hyz with h1 | h1
    · exact h1
    · exact absurd he h1

/-- R4 for the new root child z, by the chain: the chain holds after the step,
z is a top then, and no old top has a larger ordinal. P and P' through hash
maps. -/
def r4Fast (sp : Spec V T) (P P' : Struct V) (z : NodeId) : Bool :=
  let m' := Fast.nodeMap P'
  let g' := fun y => m'[y]?
  let m := Fast.nodeMap P
  let g := fun y => m[y]?
  chainB sp g' (Fast.allIdsFast P') && isTopG sp g' z &&
    (Fast.allIdsFast P).all (fun y => !isTopG sp g y || decide (ordOf sp g' y ≤ ordOf sp g' z))

/-- If the fast test passes, R4 holds for z: every old top is in z's closure.
So the checker need not evaluate `topClosure`, whose list R4's check filters
(`virtFailures`): the filter gives no node. -/
theorem r4Fast_sound (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) (z : NodeId)
    (n : Node V) (hz : (P.apply i c).get? z = some n) (h : r4Fast sp P (P.apply i c) z = true) :
    (allIds P).filter (fun y => isTop sp P y && !(topClosure sp (P.apply i c) z n).contains y) =
      [] := by
  unfold r4Fast at h
  simp only [Fast.nodeMap_get?, ← Fast.allIds_eq_fast', Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hch, hzt⟩, hold⟩ := h
  have hc := chainB_sound sp (P.apply i c) hch
  unfold isTopG at hzt
  simp only [hz, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hzt
  rw [List.filter_eq_nil_iff]
  intro y hy
  simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false]
  intro hyt
  unfold isTop at hyt
  cases hgy : P.get? y with
  | none => simp [hgy] at hyt
  | some m =>
    simp only [hgy, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hyt
    have hle := hold y hy
    have hyr : (y != root) = true := by simp [hyt.1]
    unfold isTopG at hle
    simp only [hgy, hyt.2, decide_true, hyr, Bool.and_true, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] at hle
    have hm := mem_topClosure sp (P.apply i c) _ hc _ z n rfl hz hzt.1 hzt.2 y _
      (get?_apply_of_get? hgy) hyt.1 hyt.2 hle
    simpa using hm

end SIS.TopBridge
