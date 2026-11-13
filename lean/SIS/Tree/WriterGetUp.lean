/-
The upward delete keeps every reading but the key's (bergdb 024-12, TP10's
`OpGetOK`; 024-22): a search outside a node's range finds nothing
(`getEqR_none_above`, `getEqR_none_below`, from putinv's `RangeOrder`); a klong
to a subtree where every search ends in nothing (`DeadBelow`) deleted, at an
inner node (`getFromR_dropKlong`), by LE-b (`getFromR_lebDrop`) or at a segment
leaf (`getFromR_dropLeafKlong`), keeps every reading.
-/
import SIS.Tree.WriterGetCollapseSeg
import SIS.Tree.RangeSim
import SIS.Tree.FuelPaths
import SIS.Tree.WriterTreeChainG
import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A search outside a node's range -/

/-- A search for cv at or above the upper bound of a node's range finds nothing. -/
theorem getEqR_none_above (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true) (cv : Nat) :
    ∀ f x lo b, ReachR N t r x lo (some b) → b ≤ cv → getEqR N t cv f x = none := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _; rfl
  | succ f ih =>
    intro x lo b hx hb
    cases hN : N x with
    | none => simp only [getEqR, hN]
    | some n =>
      have hrange := hR x lo (some b) n hx hN
      simp only [getEqR, hN]
      split
      · rename_i hleaf
        cases hfd : n.searchEq t cv with
        | none => rfl
        | some fd =>
          exfalso
          have hm := KNode.searchEq_mem n t cv fd (hwf x n (reachR_tReach N t r x lo _ hx) hN) hfd
          have := (hrange (cv, fd.y) hm).2
          simp only [UpperBound] at this
          omega
      · rename_i hleaf
        cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          have hm := KNode.searchLte_mem n t cv fd hfd
          obtain ⟨b', hb'⟩ := childBounds_exists (n.liveAt t) (some b) (fd.c, fd.y) hm
          have hy := ReachR.inner x n lo (some b) fd.c fd.y b' hx hN (by simpa using hleaf) hb'
          rcases childBounds_high (n.liveAt t) (some b) (fd.c, fd.y) b' hb' with h1 | ⟨q, hq, h1⟩
          · rw [h1] at hy
            exact ih fd.y _ b hy hb
          · rw [h1] at hy
            have := (hrange q hq).2
            simp only [UpperBound] at this
            exact ih fd.y _ q.1 hy (by omega)

/-- A search for cv below the lower bound of a node's range finds nothing. -/
theorem getEqR_none_below (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true) (cv : Nat) :
    ∀ f x lo hi, ReachR N t r x lo hi → cv < lo → getEqR N t cv f x = none := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _; rfl
  | succ f ih =>
    intro x lo hi hx hlo
    cases hN : N x with
    | none => simp only [getEqR, hN]
    | some n =>
      have hrange := hR x lo hi n hx hN
      simp only [getEqR, hN]
      split
      · rename_i hleaf
        cases hfd : n.searchEq t cv with
        | none => rfl
        | some fd =>
          exfalso
          have hm := KNode.searchEq_mem n t cv fd (hwf x n (reachR_tReach N t r x lo _ hx) hN) hfd
          have := (hrange (cv, fd.y) hm).1
          simp only [hleaf, ↓reduceIte] at this
          omega
      · rename_i hleaf
        have hleaf' : n.leaf = false := by simpa using hleaf
        cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          have hm := KNode.searchLte_mem n t cv fd hfd
          have hfdc : fd.c ≤ cv := by
            have := ((n.searchLte_spec t cv).1 fd hfd).2.1
            simpa using this
          have h0 : fd.c = 0 := by
            have := (hrange (fd.c, fd.y) hm).1
            simp only [hleaf', Bool.false_eq_true, ↓reduceIte] at this
            omega
          obtain ⟨b', hb'⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y) hm
          have hy := ReachR.inner x n lo hi fd.c fd.y b' hx hN hleaf' hb'
          rw [h0] at hy
          simp only [beq_self_eq_true, ↓reduceIte] at hy
          exact ih fd.y lo b' hy hlo

/-! ## A dead chain: nothing below reads a value -/

/-- z reads nothing: no value, and no rest of a key read from it finds one. -/
def DeadAt (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time) (fuel : Nat)
    (z : NodeId) : Prop :=
  V z = none ∧ ∀ rest, rest ≠ [] → getFromR N V t fuel rest z = none

/-- Every search from x ends at a node that reads nothing. -/
def DeadBelow (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time) (fuel : Nat)
    (x : NodeId) : Prop :=
  ∀ cv f z, getEqR N t cv f x = some z → DeadAt N V t fuel z

theorem deadAt_of_deadBelow (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (z : NodeId) (hv : V z = none) (h : DeadBelow N V t fuel z) : DeadAt N V t fuel z := by
  refine ⟨hv, ?_⟩
  intro rest hrest
  cases rest with
  | nil => exact absurd rfl hrest
  | cons cv rest' =>
    cases rest' with
    | nil =>
      simp only [getFromR]
      cases hg : getEqR N t cv fuel z with
      | none => rfl
      | some z' => exact (h cv fuel z' hg).1
    | cons d rest'' =>
      simp only [getFromR]
      cases hg : getEqR N t cv fuel z with
      | none => rfl
      | some z' =>
        simp only
        split
        · exact (h cv fuel z' hg).2 _ (by simp)
        · rfl

/-- A leaf with no live klong: every search ends in nothing. -/
theorem deadBelow_emptyLeaf (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (x : NodeId) (n : KNode) (hx : N x = some n) (hl : n.leaf = true)
    (hw : klongsWf n.ks = true) (hempty : ∀ c z, (c, z) ∉ n.liveAt t) : DeadBelow N V t fuel x := by
  intro cv f z h
  cases f with
  | zero => simp [getEqR] at h
  | succ f =>
    simp only [getEqR, hx, hl, ↓reduceIte] at h
    cases hfd : n.searchEq t cv with
    | none => rw [hfd] at h; cases h
    | some fd => exact absurd (KNode.searchEq_mem n t cv fd hw hfd) (hempty cv fd.y)

/-- An inner node whose live klongs all name y, which is dead below: dead below. -/
theorem deadBelow_inner (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (x y : NodeId) (n : KNode) (hx : N x = some n) (hl : n.leaf = false)
    (hone : ∀ c z, (c, z) ∈ n.liveAt t → z = y) (hy : DeadBelow N V t fuel y) :
    DeadBelow N V t fuel x := by
  intro cv f z h
  cases f with
  | zero => simp [getEqR] at h
  | succ f =>
    simp only [getEqR, hx, hl, Bool.false_eq_true, ↓reduceIte] at h
    cases hfd : n.searchLte t cv with
    | none => rw [hfd] at h; cases h
    | some fd =>
      rw [hfd] at h
      simp only at h
      have hy' := hone fd.c fd.y (KNode.searchLte_mem n t cv fd hfd)
      rw [hy'] at h
      exact hy cv f z h

/-- A segment leaf whose live klongs all name y, which reads nothing: dead below. -/
theorem deadBelow_leaf (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (x y : NodeId) (n : KNode) (hx : N x = some n) (hl : n.leaf = true)
    (hw : klongsWf n.ks = true)
    (hone : ∀ c z, (c, z) ∈ n.liveAt t → z = y) (hy : DeadAt N V t fuel y) :
    DeadBelow N V t fuel x := by
  intro cv f z h
  cases f with
  | zero => simp [getEqR] at h
  | succ f =>
    simp only [getEqR, hx, hl, ↓reduceIte] at h
    cases hfd : n.searchEq t cv with
    | none => rw [hfd] at h; cases h
    | some fd =>
      rw [hfd] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hy' := hone cv fd.y (KNode.searchEq_mem n t cv fd hw hfd)
      rw [← h, hy']
      exact hy

/-! ## Subtrees in a tree -/

/-- Two nodes that both reach x: one reaches the other. -/
theorem tReach_ancestor (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r)
    (y1 y2 : NodeId) (h1 : TReach N t r y1) (h2 : TReach N t r y2) :
    ∀ x, TReach N t y1 x → TReach N t y2 x → TReach N t y1 y2 ∨ TReach N t y2 y1 := by
  intro x hx1
  induction hx1 with
  | root => intro hx2; exact Or.inr hx2
  | @link w c x hw hl ih =>
    intro hx2
    cases hx2 with
    | root => exact Or.inl (TReach.link hw hl)
    | @link w' c' _ hw' hl' =>
      have hwr := tReach_trans N t r y1 h1 w hw
      have hw'r := tReach_trans N t r y2 h2 w' hw'
      have he := (hT.oneLink w c w' c' x hwr hw'r hl hl').1
      subst he
      exact ih hw'

/-- The subtrees of two different children of a node have no node in common. -/
theorem sub_disjoint (N : NodeId → Option KNode) (t : Time) (r s y1 y2 : NodeId) (c1 c2 : Nat)
    (hT : TreeOK N t r) (hs : TReach N t r s) (hl1 : TLink N t s c1 y1) (hl2 : TLink N t s c2 y2)
    (hne : y1 ≠ y2) : ∀ x, TReach N t y1 x → ¬ TReach N t y2 x := by
  have hr1 : TReach N t r y1 := TReach.link hs hl1
  have hr2 : TReach N t r y2 := TReach.link hs hl2
  -- a sibling does not reach the other
  have hno : ∀ a b ca cb, TLink N t s ca a → TLink N t s cb b → a ≠ b → ¬ TReach N t a b := by
    intro a b ca cb hla hlb hab hr
    have hra : TReach N t r a := TReach.link hs hla
    cases hr with
    | root => exact hab rfl
    | @link w c _ hw hl =>
      have hwr := tReach_trans N t r a hra w hw
      have he := (hT.oneLink w c s cb b hwr hs hl hlb).1
      subst he
      obtain ⟨k, hk⟩ := hw.pathLen
      exact hT.no_cycle hra (k := k + 1) (by omega) (PathFromLen.link hk.toFrom hla)
  intro x hx1 hx2
  rcases tReach_ancestor N t r hT y1 y2 hr1 hr2 x hx1 hx2 with h | h
  · exact hno y1 y2 c1 c2 hl1 hl2 hne h
  · exact hno y2 y1 c2 c1 hl2 hl1 (Ne.symm hne) h

/-- A link into the subtree of s's child x1 comes from that subtree or is s's
klong cs to x1. -/
theorem link_into_sub (N : NodeId → Option KNode) (t : Time) (r s x1 : NodeId) (cs : Nat)
    (hT : TreeOK N t r) (hs : TReach N t r s) (hlx : TLink N t s cs x1) :
    ∀ u c z, TReach N t r u → TLink N t u c z → TReach N t x1 z →
      TReach N t x1 u ∨ (u = s ∧ c = cs ∧ z = x1) := by
  intro u c z hu hl hz
  have hx1 : TReach N t r x1 := TReach.link hs hlx
  cases hz with
  | root =>
    have := hT.oneLink u c s cs x1 hu hs hl hlx
    exact Or.inr ⟨this.1, this.2, rfl⟩
  | @link w c' _ hw hl' =>
    have hwr := tReach_trans N t r x1 hx1 w hw
    have he := (hT.oneLink u c w c' z hu hwr hl hl').1
    subst he
    exact Or.inl hw

/-- A node's child does not reach the node. -/
theorem no_back (N : NodeId → Option KNode) (t : Time) (r s y : NodeId) (c : Nat) (hT : TreeOK N t r)
    (hs : TReach N t r s) (hl : TLink N t s c y) (hy : TReach N t y s) : False := by
  obtain ⟨k, hk⟩ := hy.pathLen
  have h1 : PathLen N t s y 1 := PathLen.link PathLen.root hl
  exact hT.no_cycle hs (k := 1 + k) (by omega) (h1.append hk.toFrom).toFrom

/-- A searched node's result as the search set it: from the live klongs. -/
theorem searchLte_same (a b : KNode) (t : Time) (cv : Nat) (fd : Found)
    (ha : a.searchLte t cv = some fd) (hfb : (fd.c, fd.y) ∈ b.liveAt t)
    (hsub : ∀ c z, (c, z) ∈ b.liveAt t → (c, z) ∈ a.liveAt t) :
    ∃ fd', b.searchLte t cv = some fd' ∧ fd'.y = fd.y := by
  have hsa := (a.searchLte_spec t cv).1 fd ha
  have hsb := b.searchLte_spec t cv
  cases hb : b.searchLte t cv with
  | none =>
    have := hsb.2.mp hb (fd.c, fd.y) hfb
    rw [hsa.2.1] at this; cases this
  | some fd' =>
    refine ⟨fd', rfl, ?_⟩
    obtain ⟨hm', ha', hmax'⟩ := hsb.1 fd' hb
    have h1 := hmax' (fd.c, fd.y) hfb hsa.2.1
    have h2 := hsa.2.2 (fd'.c, fd'.y) (hsub _ _ hm') ha'
    simp only [decide_eq_true_eq] at h1 h2
    have hc : fd'.c = fd.c := by omega
    have hnd := KNode.liveAt_keys_nodup b t
    have e1 := lookup_some_of_mem hnd hm'
    have e2 := lookup_some_of_mem hnd hfb
    rw [hc] at e1
    rw [e1] at e2
    exact Option.some.inj e2

/-! ## A klong of an inner node to a dead subtree deleted -/

/-- Inner node s's klong cs to x1, below which every search ends in nothing,
deleted (N' agrees with N but at s and below x1): every key reads as before. -/
theorem getFromR_dropKlong (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r s x1 : NodeId) (cs : Nat) (sn sn' : KNode)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hs : TReach N t r s) (hsn : N s = some sn) (hsl : sn.leaf = false)
    (hsx : (cs, x1) ∈ sn.liveAt t)
    (hsn' : N' s = some sn') (hsl' : sn'.leaf = false)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔ (c, z) ∈ sn.liveAt t ∧ c ≠ cs)
    (hdead : DeadBelow N V t fuel x1)
    (hother : ∀ u, TReach N t r u → u ≠ s → ¬ TReach N t x1 u → N' u = N u) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hlx : TLink N t s cs x1 := ⟨sn, hsn, hsx⟩
  have hx1r : TReach N t r x1 := TReach.link hs hlx
  have hsD : ¬ TReach N t x1 s := fun h => no_back N t r s x1 cs hT hs hlx h
  have hwfS : ∀ x xn, ReachS N t r x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn hx hxn => hwf x xn (reachS_tReach N t r x hx) hxn
  -- the descent from a node outside the subtree
  have hrel : ∀ cv f u, TReach N t r u → ¬ TReach N t x1 u →
      (getEqR N' t cv f u = getEqR N t cv f u ∧
        ∀ z, getEqR N t cv f u = some z → ¬ TReach N t x1 z) ∨
      (getEqR N' t cv f u = none ∧ ∀ z, getEqR N t cv f u = some z → DeadAt N V t fuel z) := by
    intro cv f
    induction f with
    | zero => intro u _ _; left; exact ⟨rfl, fun z h => by simp [getEqR] at h⟩
    | succ f ih =>
      intro u hu huD
      -- a link from u to a node of the subtree is s's klong cs
      have hout : ∀ c z, TLink N t u c z → TReach N t x1 z → u = s ∧ c = cs ∧ z = x1 := by
        intro c z hl hz
        rcases link_into_sub N t r s x1 cs hT hs hlx u c z hu hl hz with h | h
        · exact absurd h huD
        · exact h
      by_cases hus : u = s
      · have hus' : s = u := hus.symm
        subst hus'
        rw [getEqR, getEqR, hsn, hsn']
        simp only [hsl, hsl', Bool.false_eq_true, ↓reduceIte]
        cases hfd : sn.searchLte t cv with
        | none =>
          have hnone : sn'.searchLte t cv = none := by
            apply (sn'.searchLte_spec t cv).2.mpr
            intro q hq
            exact (sn.searchLte_spec t cv).2.mp hfd q ((hlive' q.1 q.2).mp hq).1
          rw [hnone]
          left; exact ⟨rfl, fun z h => by simp at h⟩
        | some fd =>
          have hm := KNode.searchLte_mem sn t cv fd hfd
          have hspec := (sn.searchLte_spec t cv).1 fd hfd
          have hfdc : fd.c ≤ cv := by have := hspec.2.1; simpa using this
          by_cases hc : fd.c = cs
          · have hy : fd.y = x1 := by
              have hnd := KNode.liveAt_keys_nodup sn t
              have e1 := lookup_some_of_mem hnd hm
              have e2 := lookup_some_of_mem hnd hsx
              rw [hc] at e1
              rw [e1] at e2
              exact Option.some.inj e2
            right
            refine ⟨?_, fun z hz => ?_⟩
            · cases hfd' : sn'.searchLte t cv with
              | none => rfl
              | some fd' =>
                simp only
                have hm' := KNode.searchLte_mem sn' t cv fd' hfd'
                obtain ⟨hm1, hne⟩ := (hlive' fd'.c fd'.y).mp hm'
                have hle : fd'.c ≤ cv := by
                  have := ((sn'.searchLte_spec t cv).1 fd' hfd').2.1; simpa using this
                have hlt : fd'.c < cs := by
                  have := hspec.2.2 (fd'.c, fd'.y) hm1 (by simpa using hle)
                  simp only [decide_eq_true_eq] at this
                  omega
                have hl1 : TLink N t s fd'.c fd'.y := ⟨sn, hsn, hm1⟩
                have hyx : fd'.y ≠ x1 := fun he => by
                  rw [he] at hl1
                  have := (hT.oneLink s fd'.c s cs x1 hs hs hl1 hlx).2
                  omega
                obtain ⟨lo, hi, hsR⟩ := reachR_of_reachS N t r s (tReach_reachS N t r s hs)
                obtain ⟨b', hb'⟩ := childBounds_exists (sn.liveAt t) hi (fd'.c, fd'.y) hm1
                obtain ⟨upper, hub, hup⟩ := childBounds_next_le (sn.liveAt t) hi
                  (KNode.liveAt_order sn t) (fd'.c, fd'.y) b' hb' (cs, x1) hsx hlt
                have hyR := ReachR.inner s sn lo hi fd'.c fd'.y b' hsR hsn hsl hb'
                rw [hub] at hyR
                have hnone := getEqR_none_above N t r hR hwf cv f fd'.y _ upper hyR (by omega)
                have hyr : TReach N t r fd'.y := TReach.link hs hl1
                have hdisj := sub_disjoint N t r s fd'.y x1 fd'.c cs hT hs hl1 hlx hyx
                have hsame : ∀ x, ReachS N t fd'.y x → ¬ (x = s ∨ TReach N t x1 x) → N' x = N x := by
                  intro x hx hD
                  exact hother x (tReach_trans N t r fd'.y hyr x (reachS_tReach N t fd'.y x hx))
                    (fun h => hD (Or.inl h)) (fun h => hD (Or.inr h))
                have hlinks : ∀ x xn c z, ReachS N t fd'.y x → N x = some xn → (c, z) ∈ xn.liveAt t →
                    ¬ (z = s ∨ TReach N t x1 z) := by
                  intro x xn c z hx hxn hcz hD
                  have hxT := reachS_tReach N t fd'.y x hx
                  have hxr := tReach_trans N t r fd'.y hyr x hxT
                  rcases hD with hzs | hzD
                  · rw [hzs] at hcz
                    exact no_back N t r s fd'.y fd'.c hT hs hl1 (TReach.link hxT ⟨xn, hxn, hcz⟩)
                  · rcases link_into_sub N t r s x1 cs hT hs hlx x c z hxr ⟨xn, hxn, hcz⟩ hzD with h | h
                    · exact hdisj x hxT h
                    · rw [h.1] at hxT
                      exact no_back N t r s fd'.y fd'.c hT hs hl1 hxT
                rw [getEqR_avoid N N' t fd'.y (fun u => u = s ∨ TReach N t x1 u) hsame hlinks cv f fd'.y
                  ReachS.root (fun hD => hlinks s sn fd'.c fd'.y (by
                    rcases hD with h | h
                    · rw [h] at hl1; exact absurd hl1 (hT.no_self_link s fd'.c hs)
                    · exact absurd h (hdisj fd'.y TReach.root)) hsn hm1 hD)]
                exact hnone
            · simp only at hz
              rw [hy] at hz
              exact hdead cv f z hz
          · have hm' : (fd.c, fd.y) ∈ sn'.liveAt t := (hlive' _ _).mpr ⟨hm, hc⟩
            obtain ⟨fd', hfd', hy'⟩ := searchLte_same sn sn' t cv fd hfd hm'
              (fun c z h => ((hlive' c z).mp h).1)
            rw [hfd']
            simp only
            rw [hy']
            have hl : TLink N t s fd.c fd.y := ⟨sn, hsn, hm⟩
            exact ih fd.y (TReach.link hs hl) (fun hD => hc (hout fd.c fd.y hl hD).2.1)
      · rw [getEqR, getEqR, hother u hu hus huD]
        cases hN : N u with
        | none => left; exact ⟨rfl, fun z h => by simp at h⟩
        | some un =>
          simp only
          split
          · left
            refine ⟨rfl, fun z hz hzD => ?_⟩
            cases hfd : un.searchEq t cv with
            | none => rw [hfd] at hz; cases hz
            | some fd =>
              rw [hfd] at hz
              simp only [Option.map_some, Option.some.injEq] at hz
              have hm := KNode.searchEq_mem un t cv fd (hwf u un hu hN) hfd
              rw [hz] at hm
              exact hus (hout cv z ⟨un, hN, hm⟩ hzD).1
          · cases hfd : un.searchLte t cv with
            | none => left; exact ⟨rfl, fun z h => by simp at h⟩
            | some fd =>
              simp only
              have hm := KNode.searchLte_mem un t cv fd hfd
              have hl : TLink N t u fd.c fd.y := ⟨un, hN, hm⟩
              exact ih fd.y (TReach.link hu hl) (fun hD => hus (hout fd.c fd.y hl hD).1)
  have hmain : ∀ key u, TReach N t r u → ¬ TReach N t x1 u →
      getFromR N' V t fuel key u = getFromR N V t fuel key u := by
    intro key
    induction key with
    | nil => intro u _ _; rfl
    | cons cv rest ih =>
      intro u hu huD
      rcases hrel cv fuel u hu huD with ⟨he, hz⟩ | ⟨he, hz⟩
      · cases rest with
        | nil => simp only [getFromR]; rw [he]
        | cons d rest' =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z =>
            simp only
            have hzD := hz z hg
            have hzR : TReach N t r z := reachS_tReach N t r z
              (getEqR_reach N t r cv hwfS fuel u z (tReach_reachS N t r u hu) hg)
            have hsome : (N' z).isSome = (N z).isSome := by
              by_cases hzs : z = s
              · rw [hzs, hsn, hsn']; rfl
              · rw [hother z hzR hzs hzD]
            rw [hsome, ih z hzR hzD]
      · cases rest with
        | nil =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z => simp [(hz z hg).1]
        | cons d rest' =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z =>
            simp only
            split
            · exact ((hz z hg).2 _ (by simp)).symm
            · rfl
  intro key
  apply hmain key r TReach.root
  intro hD
  cases hD with
  | root => exact hT.rootFree s cs hs hlx
  | link hw hl => exact hT.rootFree _ _ (tReach_trans N t r x1 hx1r _ hw) hl

/-- The reading from a relation of the searches: from every reached node outside
x1's subtree, a search in N' finds what N finds, outside the subtree, or finds
nothing where N finds a dead end. -/
theorem getFromR_of_deadRel (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r x1 : NodeId)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hrx : ¬ TReach N t x1 r)
    (hsome : ∀ u, TReach N t r u → ¬ TReach N t x1 u → (N' u).isSome = (N u).isSome)
    (hrel : ∀ cv u, TReach N t r u → ¬ TReach N t x1 u →
      (getEqR N' t cv fuel u = getEqR N t cv fuel u ∧
        ∀ z, getEqR N t cv fuel u = some z → ¬ TReach N t x1 z) ∨
      (getEqR N' t cv fuel u = none ∧ ∀ z, getEqR N t cv fuel u = some z → DeadAt N V t fuel z)) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hwfS : ∀ x xn, ReachS N t r x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn hx hxn => hwf x xn (reachS_tReach N t r x hx) hxn
  have hmain : ∀ key u, TReach N t r u → ¬ TReach N t x1 u →
      getFromR N' V t fuel key u = getFromR N V t fuel key u := by
    intro key
    induction key with
    | nil => intro u _ _; rfl
    | cons cv rest ih =>
      intro u hu huD
      rcases hrel cv u hu huD with ⟨he, hz⟩ | ⟨he, hz⟩
      · cases rest with
        | nil => simp only [getFromR]; rw [he]
        | cons d rest' =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z =>
            simp only
            have hzD := hz z hg
            have hzR : TReach N t r z := reachS_tReach N t r z
              (getEqR_reach N t r cv hwfS fuel u z (tReach_reachS N t r u hu) hg)
            rw [hsome z hzR hzD, ih z hzR hzD]
      · cases rest with
        | nil =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z => simp [(hz z hg).1]
        | cons d rest' =>
          simp only [getFromR]
          rw [he]
          cases hg : getEqR N t cv fuel u with
          | none => rfl
          | some z =>
            simp only
            split
            · exact ((hz z hg).2 _ (by simp)).symm
            · rfl
  intro key
  exact hmain key r TReach.root hrx

/-- LE-b at the inner node s whose empty key's klong names x1, dead below: the
empty key names jy, the node's next child, whose klong jcv is deleted; every key
reads as before. -/
theorem getFromR_lebDrop (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r s x1 jy : NodeId) (jcv : Nat) (sn sn' : KNode)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hs : TReach N t r s) (hsn : N s = some sn) (hsl : sn.leaf = false)
    (hsx : (0, x1) ∈ sn.liveAt t) (hsj : (jcv, jy) ∈ sn.liveAt t) (hj0 : 0 < jcv)
    (hmin : ∀ c z, (c, z) ∈ sn.liveAt t → c = 0 ∨ jcv ≤ c)
    (hsn' : N' s = some sn') (hsl' : sn'.leaf = false)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔
      (c = 0 ∧ z = jy) ∨ ((c, z) ∈ sn.liveAt t ∧ c ≠ 0 ∧ c ≠ jcv))
    (hdead : DeadBelow N V t fuel x1)
    (hother : ∀ u, TReach N t r u → u ≠ s → ¬ TReach N t x1 u → N' u = N u) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hlx : TLink N t s 0 x1 := ⟨sn, hsn, hsx⟩
  have hlj : TLink N t s jcv jy := ⟨sn, hsn, hsj⟩
  have hx1r : TReach N t r x1 := TReach.link hs hlx
  have hjyr : TReach N t r jy := TReach.link hs hlj
  have hsD : ¬ TReach N t x1 s := fun h => no_back N t r s x1 0 hT hs hlx h
  have hjx : jy ≠ x1 := fun he => by
    rw [he] at hlj
    have := (hT.oneLink s jcv s 0 x1 hs hs hlj hlx).2
    omega
  have hdisj := sub_disjoint N t r s jy x1 jcv 0 hT hs hlj hlx hjx
  -- below jy, N' is N
  have hsame : ∀ x, ReachS N t jy x → ¬ (x = s ∨ TReach N t x1 x) → N' x = N x := by
    intro x hx hD
    exact hother x (tReach_trans N t r jy hjyr x (reachS_tReach N t jy x hx))
      (fun h => hD (Or.inl h)) (fun h => hD (Or.inr h))
  have hlinks : ∀ x xn c z, ReachS N t jy x → N x = some xn → (c, z) ∈ xn.liveAt t →
      ¬ (z = s ∨ TReach N t x1 z) := by
    intro x xn c z hx hxn hcz hD
    have hxT := reachS_tReach N t jy x hx
    have hxr := tReach_trans N t r jy hjyr x hxT
    rcases hD with hzs | hzD
    · rw [hzs] at hcz
      exact no_back N t r s jy jcv hT hs hlj (TReach.link hxT ⟨xn, hxn, hcz⟩)
    · rcases link_into_sub N t r s x1 0 hT hs hlx x c z hxr ⟨xn, hxn, hcz⟩ hzD with h | h
      · exact hdisj x hxT h
      · rw [h.1] at hxT
        exact no_back N t r s jy jcv hT hs hlj hxT
  have hjyD : ¬ (jy = s ∨ TReach N t x1 jy) := by
    rintro (h | h)
    · rw [h] at hlj; exact hT.no_self_link s jcv hs hlj
    · exact hdisj jy TReach.root h
  have hjyEq : ∀ cv f, getEqR N' t cv f jy = getEqR N t cv f jy := fun cv f =>
    getEqR_avoid N N' t jy (fun u => u = s ∨ TReach N t x1 u) hsame hlinks cv f jy ReachS.root hjyD
  -- jy's range starts at jcv
  obtain ⟨lo, hi, hsR⟩ := reachR_of_reachS N t r s (tReach_reachS N t r s hs)
  obtain ⟨bj, hbj⟩ := childBounds_exists (sn.liveAt t) hi (jcv, jy) hsj
  have hjR := ReachR.inner s sn lo hi jcv jy bj hsR hsn hsl hbj
  have hj0' : (jcv == 0) = false := by simpa using (Nat.pos_iff_ne_zero.mp hj0)
  rw [hj0'] at hjR
  simp only [Bool.false_eq_true, ↓reduceIte] at hjR
  apply getFromR_of_deadRel N N' V t fuel r x1 hwf
  · intro hD
    cases hD with
    | root => exact hT.rootFree s 0 hs hlx
    | link hw hl => exact hT.rootFree _ _ (tReach_trans N t r x1 hx1r _ hw) hl
  · intro u hu huD
    by_cases hus : u = s
    · rw [hus, hsn, hsn']; rfl
    · rw [hother u hu hus huD]
  · intro cv
    -- the relation for every fuel
    suffices H : ∀ f u, TReach N t r u → ¬ TReach N t x1 u →
        (getEqR N' t cv f u = getEqR N t cv f u ∧
          ∀ z, getEqR N t cv f u = some z → ¬ TReach N t x1 z) ∨
        (getEqR N' t cv f u = none ∧ ∀ z, getEqR N t cv f u = some z → DeadAt N V t fuel z) from
      H fuel
    intro f
    induction f with
    | zero => intro u _ _; left; exact ⟨rfl, fun z h => by simp [getEqR] at h⟩
    | succ f ih =>
      intro u hu huD
      have hout : ∀ c z, TLink N t u c z → TReach N t x1 z → u = s ∧ c = 0 ∧ z = x1 := by
        intro c z hl hz
        rcases link_into_sub N t r s x1 0 hT hs hlx u c z hu hl hz with h | h
        · exact absurd h huD
        · exact h
      by_cases hus : u = s
      · have hus' : s = u := hus.symm
        subst hus'
        rw [getEqR, getEqR, hsn, hsn']
        simp only [hsl, hsl', Bool.false_eq_true, ↓reduceIte]
        cases hfd : sn.searchLte t cv with
        | none =>
          exfalso
          have := (sn.searchLte_spec t cv).2.mp hfd (0, x1) hsx
          simp at this
        | some fd =>
          have hm := KNode.searchLte_mem sn t cv fd hfd
          have hspec := (sn.searchLte_spec t cv).1 fd hfd
          have hfdc : fd.c ≤ cv := by have := hspec.2.1; simpa using this
          -- sn' finds (0, jy) below jcv, and what sn finds from jcv on (jy at jcv)
          have hs' : ∀ fd', sn'.searchLte t cv = some fd' →
              (fd.c < jcv → fd'.y = jy) ∧ (jcv ≤ fd.c → fd.c = jcv → fd'.y = jy) ∧
              (jcv < fd.c → fd'.y = fd.y) := by
            intro fd' hfd'
            have hm' := KNode.searchLte_mem sn' t cv fd' hfd'
            have hle' : fd'.c ≤ cv := by
              have := ((sn'.searchLte_spec t cv).1 fd' hfd').2.1; simpa using this
            have hmax' := ((sn'.searchLte_spec t cv).1 fd' hfd').2.2
            refine ⟨fun hlt => ?_, fun _ heq => ?_, fun hgt => ?_⟩
            · rcases (hlive' fd'.c fd'.y).mp hm' with ⟨_, h⟩ | ⟨h1, h2, h3⟩
              · exact h
              · have := hspec.2.2 (fd'.c, fd'.y) h1 (by simpa using hle')
                simp only [decide_eq_true_eq] at this
                rcases hmin _ _ h1 with h | h <;> omega
            · rcases (hlive' fd'.c fd'.y).mp hm' with ⟨_, h⟩ | ⟨h1, h2, h3⟩
              · exact h
              · have := hspec.2.2 (fd'.c, fd'.y) h1 (by simpa using hle')
                simp only [decide_eq_true_eq] at this
                rcases hmin _ _ h1 with h | h <;> omega
            · have hfm' : (fd.c, fd.y) ∈ sn'.liveAt t := (hlive' _ _).mpr (Or.inr ⟨hm, by omega, by omega⟩)
              have h1 := hmax' (fd.c, fd.y) hfm' (by simpa using hfdc)
              simp only [decide_eq_true_eq] at h1
              rcases (hlive' fd'.c fd'.y).mp hm' with ⟨h0, _⟩ | ⟨h2, _, _⟩
              · omega
              · have h3 := hspec.2.2 (fd'.c, fd'.y) h2 (by simpa using hle')
                simp only [decide_eq_true_eq] at h3
                have hc : fd'.c = fd.c := by omega
                have hnd := KNode.liveAt_keys_nodup sn t
                have e1 := lookup_some_of_mem hnd h2
                have e2 := lookup_some_of_mem hnd hm
                rw [hc] at e1
                rw [e1] at e2
                exact Option.some.inj e2
          have hs'some : ∃ fd', sn'.searchLte t cv = some fd' := by
            cases h : sn'.searchLte t cv with
            | none =>
              have := (sn'.searchLte_spec t cv).2.mp h (0, jy) ((hlive' 0 jy).mpr (Or.inl ⟨rfl, rfl⟩))
              simp at this
            | some fd' => exact ⟨fd', rfl⟩
          obtain ⟨fd', hfd'⟩ := hs'some
          obtain ⟨hA, hB, hC⟩ := hs' fd' hfd'
          rw [hfd']
          simp only
          rcases hmin fd.c fd.y hm with h0 | h0
          · -- below jcv: N finds x1's dead subtree, N' finds jy, which has nothing below jcv
            have hy : fd.y = x1 := by
              have hnd := KNode.liveAt_keys_nodup sn t
              have e1 := lookup_some_of_mem hnd hm
              have e2 := lookup_some_of_mem hnd hsx
              rw [h0] at e1
              rw [e1] at e2
              exact Option.some.inj e2
            have hcv : cv < jcv := by
              rcases Nat.lt_or_ge cv jcv with h | h
              · exact h
              · have := hspec.2.2 (jcv, jy) hsj (by simpa using h)
                simp only [decide_eq_true_eq] at this
                omega
            right
            refine ⟨?_, fun z hz => ?_⟩
            · rw [hA (by omega), hjyEq]
              exact getEqR_none_below N t r hR hwf cv f jy jcv bj hjR hcv
            · rw [hy] at hz
              exact hdead cv f z hz
          · rcases Nat.lt_or_ge jcv fd.c with hgt | hle
            · rw [hC hgt]
              have hl : TLink N t s fd.c fd.y := ⟨sn, hsn, hm⟩
              exact ih fd.y (TReach.link hs hl) (fun hD => by
                have := (hout fd.c fd.y hl hD).2.1; omega)
            · have heq : fd.c = jcv := by omega
              have hyj : fd.y = jy := by
                have hnd := KNode.liveAt_keys_nodup sn t
                have e1 := lookup_some_of_mem hnd hm
                have e2 := lookup_some_of_mem hnd hsj
                rw [heq] at e1
                rw [e1] at e2
                exact Option.some.inj e2
              rw [hB h0 heq, hyj]
              exact ih jy hjyr (fun hD => hdisj jy TReach.root hD)
      · rw [getEqR, getEqR, hother u hu hus huD]
        cases hN : N u with
        | none => left; exact ⟨rfl, fun z h => by simp at h⟩
        | some un =>
          simp only
          split
          · left
            refine ⟨rfl, fun z hz hzD => ?_⟩
            cases hfd : un.searchEq t cv with
            | none => rw [hfd] at hz; cases hz
            | some fd =>
              rw [hfd] at hz
              simp only [Option.map_some, Option.some.injEq] at hz
              have hm := KNode.searchEq_mem un t cv fd (hwf u un hu hN) hfd
              rw [hz] at hm
              exact hus (hout cv z ⟨un, hN, hm⟩ hzD).1
          · cases hfd : un.searchLte t cv with
            | none => left; exact ⟨rfl, fun z h => by simp at h⟩
            | some fd =>
              simp only
              have hm := KNode.searchLte_mem un t cv fd hfd
              have hl : TLink N t u fd.c fd.y := ⟨un, hN, hm⟩
              exact ih fd.y (TReach.link hu hl) (fun hD => hus (hout fd.c fd.y hl hD).1)

theorem lookup_eq_of_iff (A B : List (Nat × NodeId)) (hA : (A.map Prod.fst).Nodup)
    (hB : (B.map Prod.fst).Nodup) (c : Nat) (h : ∀ z, (c, z) ∈ A ↔ (c, z) ∈ B) :
    A.lookup c = B.lookup c := by
  cases hb : B.lookup c with
  | none =>
    cases ha : A.lookup c with
    | none => rfl
    | some z =>
      have := (h z).mp (lookup_some_mem ha)
      rw [lookup_some_of_mem hB this] at hb; cases hb
  | some z => exact lookup_some_of_mem hA ((h z).mpr (lookup_some_mem hb))

/-- At the segment leaf s, the klong cs to x1, the root of a segment tree that
reads nothing, deleted: every key reads as before. -/
theorem getFromR_dropLeafKlong (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r s x1 : NodeId) (cs : Nat) (sn sn' : KNode)
    (hT : TreeOK N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hs : TReach N t r s) (hsn : N s = some sn) (hsl : sn.leaf = true)
    (hsx : (cs, x1) ∈ sn.liveAt t)
    (hsn' : N' s = some sn') (hsl' : sn'.leaf = true) (hsw' : klongsWf sn'.ks = true)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔ (c, z) ∈ sn.liveAt t ∧ c ≠ cs)
    (hdead : DeadAt N V t fuel x1)
    (hother : ∀ u, TReach N t r u → u ≠ s → ¬ TReach N t x1 u → N' u = N u) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hlx : TLink N t s cs x1 := ⟨sn, hsn, hsx⟩
  have hx1r : TReach N t r x1 := TReach.link hs hlx
  have hsw := hwf s sn hs hsn
  apply getFromR_of_deadRel N N' V t fuel r x1 hwf
  · intro hD
    cases hD with
    | root => exact hT.rootFree s cs hs hlx
    | link hw hl => exact hT.rootFree _ _ (tReach_trans N t r x1 hx1r _ hw) hl
  · intro u hu huD
    by_cases hus : u = s
    · rw [hus, hsn, hsn']; rfl
    · rw [hother u hu hus huD]
  · intro cv
    suffices H : ∀ f u, TReach N t r u → ¬ TReach N t x1 u →
        (getEqR N' t cv f u = getEqR N t cv f u ∧
          ∀ z, getEqR N t cv f u = some z → ¬ TReach N t x1 z) ∨
        (getEqR N' t cv f u = none ∧ ∀ z, getEqR N t cv f u = some z → DeadAt N V t fuel z) from
      H fuel
    intro f
    induction f with
    | zero => intro u _ _; left; exact ⟨rfl, fun z h => by simp [getEqR] at h⟩
    | succ f ih =>
      intro u hu huD
      have hout : ∀ c z, TLink N t u c z → TReach N t x1 z → u = s ∧ c = cs ∧ z = x1 := by
        intro c z hl hz
        rcases link_into_sub N t r s x1 cs hT hs hlx u c z hu hl hz with h | h
        · exact absurd h huD
        · exact h
      by_cases hus : u = s
      · have hus' : s = u := hus.symm
        subst hus'
        rw [getEqR, getEqR, hsn, hsn']
        simp only [hsl, hsl', ↓reduceIte]
        rw [searchEqSpec sn' t cv hsw', searchEqSpec sn t cv hsw]
        by_cases hc : cv = cs
        · subst hc
          right
          refine ⟨?_, fun z hz => ?_⟩
          · cases h : (sn'.liveAt t).lookup cv with
            | none => rfl
            | some z => exact absurd rfl ((hlive' cv z).mp (lookup_some_mem h)).2
          · have := lookup_some_of_mem (KNode.liveAt_keys_nodup sn t) hsx
            rw [this] at hz
            cases hz
            exact hdead
        · left
          refine ⟨lookup_eq_of_iff _ _ (KNode.liveAt_keys_nodup sn' t) (KNode.liveAt_keys_nodup sn t)
            cv (fun z => ⟨fun h => ((hlive' cv z).mp h).1, fun h => (hlive' cv z).mpr ⟨h, hc⟩⟩),
            fun z hz hzD => ?_⟩
          have hm := lookup_some_mem hz
          exact hc (hout cv z ⟨sn, hsn, hm⟩ hzD).2.1
      · rw [getEqR, getEqR, hother u hu hus huD]
        cases hN : N u with
        | none => left; exact ⟨rfl, fun z h => by simp at h⟩
        | some un =>
          simp only
          split
          · left
            refine ⟨rfl, fun z hz hzD => ?_⟩
            cases hfd : un.searchEq t cv with
            | none => rw [hfd] at hz; cases hz
            | some fd =>
              rw [hfd] at hz
              simp only [Option.map_some, Option.some.injEq] at hz
              have hm := KNode.searchEq_mem un t cv fd (hwf u un hu hN) hfd
              rw [hz] at hm
              exact hus (hout cv z ⟨un, hN, hm⟩ hzD).1
          · cases hfd : un.searchLte t cv with
            | none => left; exact ⟨rfl, fun z h => by simp at h⟩
            | some fd =>
              simp only
              have hm := KNode.searchLte_mem un t cv fd hfd
              have hl : TLink N t u fd.c fd.y := ⟨un, hN, hm⟩
              exact ih fd.y (TReach.link hu hl) (fun hD => hus (hout fd.c fd.y hl hD).1)

/-! ## The emptied chain -/

/-- The access path's nodes X (s+1) .. X D below the stop node: each has its live
klongs naming the next, and the last, X D, is a leaf with no live klong. Then
every search from X (s+1) ends in nothing. -/
theorem chain_deadBelow (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat) (hsD : s < D)
    (hN : ∀ i, s < i → i ≤ D → N (X i) = some (Nn i))
    (hwf : ∀ i, s < i → i ≤ D → klongsWf (Nn i).ks = true)
    (hone : ∀ i, s < i → i < D → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hleaf : (Nn D).leaf = true) (hempty : ∀ c z, (c, z) ∉ (Nn D).liveAt t)
    (hnoval : ∀ i, s + 1 < i → i ≤ D → V (X i) = none) :
    DeadBelow N V t fuel (X (s + 1)) := by
  have key : ∀ k, k ≤ D - (s + 1) → DeadBelow N V t fuel (X (D - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact deadBelow_emptyLeaf N V t fuel (X D) (Nn D) (hN D (by omega) (Nat.le_refl _)) hleaf
        (hwf D (by omega) (Nat.le_refl _)) hempty
    | succ k ih =>
      intro hk
      have hi : D - (k + 1) + 1 = D - k := by omega
      have hnext := ih (by omega)
      have hone' := hone (D - (k + 1)) (by omega) (by omega)
      rw [hi] at hone'
      have hNi := hN (D - (k + 1)) (by omega) (by omega)
      cases hl : (Nn (D - (k + 1))).leaf with
      | false => exact deadBelow_inner N V t fuel _ _ _ hNi hl hone' hnext
      | true =>
        exact deadBelow_leaf N V t fuel _ _ _ hNi hl (hwf _ (by omega) (by omega)) hone'
          (deadAt_of_deadBelow N V t fuel _ (by
            have := hnoval (D - k) (by omega) (by omega); exact this) hnext)
  have := key (D - (s + 1)) (Nat.le_refl _)
  have he : D - (D - (s + 1)) = s + 1 := by omega
  rw [he] at this
  exact this

/-! ## The upward delete at tree level -/

/-- The empty leaf: a node with no live klong. -/
def emptyLeaf (t : Time) : KNode := ⟨true, newKlongs t []⟩

theorem emptyLeaf_liveAt (t : Time) : ∀ c z, (c, z) ∉ (emptyLeaf t).liveAt t := by
  intro c z h
  have := (mrg_newKlongs_liveAt_iff true t [] (by simp) c z).mp h
  simp at this

/-- The tree with the key's leaf X D emptied (the key's delete, a node that is no
writer's): it reads every key as N but the key, which reads nothing; it is a
tree with the walk's ranges; the stop node X s is reached; below X (s + 1),
every search ends in nothing. -/
theorem up_prep (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time) (fuel : Nat)
    (hfuel : 1 ≤ fuel) (r : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat)
    (s D : Nat) (hsD : s < D) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hone : ∀ i, s < i → i < D → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hleaf : (Nn D).leaf = true) (honly : ∀ c z, (c, z) ∈ (Nn D).liveAt t → c = cv)
    (hnoval : ∀ i, s + 1 < i → i ≤ D → V (X i) = none)
    (hdist : ∀ i, s ≤ i → i < D → X i ≠ X D)
    (hrk : segRootR N t fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (X D, cv) ∈ eqVisits N t cv fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true → (x, cv) ∈ fromVisits N t fuel key' r →
      (x, cv) ∈ eqVisits N t cv fuel rk → N x = some m → m.leaf = true → key' = pre ++ [cv]) :
    (∀ key', keyWf key' = true → getFromR (updN N (X D) (emptyLeaf t)) V t fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N V t fuel key' r) ∧
    TreeOK (updN N (X D) (emptyLeaf t)) t r ∧ RangeOrder (updN N (X D) (emptyLeaf t)) t r ∧
    (∀ x xn, TReach (updN N (X D) (emptyLeaf t)) t r x → updN N (X D) (emptyLeaf t) x = some xn →
      klongsWf xn.ks = true) ∧
    TReach (updN N (X D) (emptyLeaf t)) t r (X s) ∧
    DeadBelow (updN N (X D) (emptyLeaf t)) V t fuel (X (s + 1)) ∧
    (∀ u i, s < i → i ≤ D → u = X i → TReach (updN N (X D) (emptyLeaf t)) t (X (s + 1)) u) ∧
    (∀ u, TReach (updN N (X D) (emptyLeaf t)) t r u → TReach N t r u) := by
  have hWx : updN N (X D) (Nn D) = N := by
    funext z
    by_cases hz : z = X D
    · rw [hz, updN_self, hN D (by omega) (Nat.le_refl _)]
    · exact updN_ne _ _ _ _ hz
  have hsubL : ∀ c z, (c, z) ∈ (emptyLeaf t).liveAt t → (c, z) ∈ (Nn D).liveAt t :=
    fun c z h => absurd h (emptyLeaf_liveAt t c z)
  obtain ⟨hTa, hRa⟩ := treeOK_updN_sub N t r (X D) (Nn D) (emptyLeaf t) (by rw [hWx]; exact hT) hsubL
  rw [hWx] at hRa
  have hlink : ∀ i, s < i → i ≤ D → ∃ k, TLink N t (X (i - 1)) k (X i) := by
    intro i h1 h2
    exact ⟨K i, Nn (i - 1), hN (i - 1) (by omega) (by omega), hlinkK i h1 h2⟩
  have hanc := chain_anc_reach N t r X s D hT hXs hlink (emptyLeaf t)
  have hLD : N (X D) = some (Nn D) := hN D (by omega) (Nat.le_refl _)
  have hreachX : ∀ k, s + k ≤ D → TReach N t r (X (s + k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hXs
    | succ k ih =>
      intro hk
      obtain ⟨c, hc⟩ := hlink (s + (k + 1)) (by omega) hk
      have h1 : s + (k + 1) - 1 = s + k := by omega
      rw [h1] at hc
      exact TReach.link (ih (by omega)) hc
  have hXi : ∀ i, s ≤ i → i ≤ D → TReach N t r (X i) := by
    intro i h1 h2
    have := hreachX (i - s) (by omega)
    rwa [show s + (i - s) = i by omega] at this
  have hwD := hwf (X D) (Nn D) (hXi D (by omega) (Nat.le_refl _)) hLD
  have hsubR : ∀ u, TReach (updN N (X D) (emptyLeaf t)) t r u → TReach N t r u :=
    tReach_of_sublinks N _ t r (fun x c y hl => by
      obtain ⟨m, hm, hcm⟩ := hl
      by_cases hx : x = X D
      · rw [hx, updN_self] at hm
        cases hm
        exact absurd hcm (emptyLeaf_liveAt t c y)
      · rw [updN_ne _ _ _ _ hx] at hm; exact ⟨m, hm, hcm⟩)
  have hlook0 : ∀ c', ((emptyLeaf t).searchEq t c').map (·.y) = none := by
    intro c'
    rw [searchEqSpec (emptyLeaf t) t c' (klongsWf_newKlongs t [])]
    cases h : ((emptyLeaf t).liveAt t).lookup c' with
    | none => rfl
    | some z => exact absurd (lookup_some_mem h) (emptyLeaf_liveAt t c' z)
  -- the leaf's change
  obtain ⟨hk, hother⟩ := getFromR_leaf_change_seg N (updN N (X D) (emptyLeaf t)) V V t fuel hfuel
    (X D) pre cv r rk (Nn D) (emptyLeaf t) (fun x hx => (updN_ne _ _ _ _ hx).symm) hLD
    (updN_self _ _ _) hleaf rfl
    (by
      intro c' hc'
      rw [hlook0 c', searchEqSpec _ t c' hwD]
      cases h : ((Nn D).liveAt t).lookup c' with
      | none => rfl
      | some z => exact absurd (honly c' z (lookup_some_mem h)) hc')
    hrk hcv hvisL huniq (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  refine ⟨?_, hTa, ?_, ?_, hanc s (Nat.le_refl _) hsD, ?_, ?_, hsubR⟩
  · intro key' hkw
    by_cases he : pre ++ [cv] = key'
    · subst he
      rw [hk, hlook0 cv]
      simp
    · have hb : (pre ++ [cv] == key') = false := by simpa using he
      rw [hb]
      exact hother key' hkw (Ne.symm he)
  · exact rangeOrder_shrink N _ t r (X D) (Nn D) (emptyLeaf t) hR hLD (fun y => rfl)
      (by rw [hleaf]; rfl) hsubL
  · intro x xn hx hxn
    by_cases hxD : x = X D
    · rw [hxD, updN_self] at hxn
      cases hxn
      exact klongsWf_newKlongs t []
    · rw [updN_ne _ _ _ _ hxD] at hxn
      exact hwf x xn (hsubR x hx) hxn
  · apply chain_deadBelow (updN N (X D) (emptyLeaf t)) V t fuel X
      (fun i => if i = D then emptyLeaf t else Nn i) s D hsD
    · intro i h1 h2
      by_cases hi : i = D
      · subst hi; simp only [↓reduceIte]; exact updN_self _ _ _
      · simp only [hi, ↓reduceIte]
        rw [updN_ne _ _ _ _ (hdist i (by omega) (by omega))]
        exact hN i (by omega) h2
    · intro i h1 h2
      by_cases hi : i = D
      · simp only [hi, ↓reduceIte]; exact klongsWf_newKlongs t []
      · simp only [hi, ↓reduceIte]
        exact hwf (X i) (Nn i) (hXi i (by omega) h2) (hN i (by omega) h2)
    · intro i h1 h2
      have hi : i ≠ D := by omega
      simp only [hi, ↓reduceIte]
      exact hone i h1 h2
    · simp [emptyLeaf]
    · simp only [↓reduceIte]; exact emptyLeaf_liveAt t
    · exact hnoval
  · intro u i h1 h2 hu
    subst hu
    have hch : ∀ k, s + 1 + k ≤ D →
        TReach (updN N (X D) (emptyLeaf t)) t (X (s + 1)) (X (s + 1 + k)) := by
      intro k
      induction k with
      | zero => intro _; exact TReach.root
      | succ k ih =>
        intro hk
        have hsrc : X (s + 1 + k) ≠ X D := hdist (s + 1 + k) (by omega) (by omega)
        have hlk : (K (s + 1 + (k + 1)), X (s + 1 + (k + 1))) ∈ (Nn (s + 1 + k)).liveAt t := by
          have := hlinkK (s + 1 + (k + 1)) (by omega) hk
          rwa [show s + 1 + (k + 1) - 1 = s + 1 + k by omega] at this
        exact TReach.link (c := K (s + 1 + (k + 1))) (ih (by omega))
          ⟨Nn (s + 1 + k), by rw [updN_ne _ _ _ _ hsrc]; exact hN _ (by omega) (by omega), hlk⟩
    have := hch (i - (s + 1)) (by omega)
    rwa [show s + 1 + (i - (s + 1)) = i by omega] at this

/-- The upward delete at tree level, the stop node X s inner: the key's leaf X D
emptied, the chain X (s + 1) .. X D left out, X s's klong K (s + 1) to it deleted
(N' agrees with N but at X s and the chain): the key reads nothing, every other
key as before. -/
theorem getFromR_up_inner (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat)
    (s D : Nat) (hsD : s < D) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hone : ∀ i, s < i → i < D → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hleaf : (Nn D).leaf = true) (honly : ∀ c z, (c, z) ∈ (Nn D).liveAt t → c = cv)
    (hnoval : ∀ i, s < i → i ≤ D → V (X i) = none)
    (hdist : ∀ i, s ≤ i → i < D → X i ≠ X D)
    (hrk : segRootR N t fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (X D, cv) ∈ eqVisits N t cv fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true → (x, cv) ∈ fromVisits N t fuel key' r →
      (x, cv) ∈ eqVisits N t cv fuel rk → N x = some m → m.leaf = true → key' = pre ++ [cv])
    (hagree : ∀ u, TReach N t r u → u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsl : (Nn s).leaf = false) (hsn' : N' (X s) = some sn') (hsl' : sn'.leaf = false)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔ (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
    ∀ key', keyWf key' = true → getFromR N' V t fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N V t fuel key' r := by
  obtain ⟨hk, hTa, hRa, hwfa, hXsa, hdead, hchain, hsubR⟩ := up_prep N V t fuel hfuel r X Nn K s D hsD
    pre cv rk hT hR hwf hXs hN hlinkK hone hleaf honly (fun i h1 h2 => hnoval i (by omega) h2) hdist
    hrk hcv hvisL huniq
  have hsa : updN N (X D) (emptyLeaf t) (X s) = some (Nn s) := by
    rw [updN_ne _ _ _ _ (hdist s (Nat.le_refl _) hsD)]; exact hN s (Nat.le_refl _) (by omega)
  have hsx : (K (s + 1), X (s + 1)) ∈ (Nn s).liveAt t := by
    have := hlinkK (s + 1) (by omega) (by omega); simpa using this
  have hother : ∀ u, TReach (updN N (X D) (emptyLeaf t)) t r u → u ≠ X s →
      ¬ TReach (updN N (X D) (emptyLeaf t)) t (X (s + 1)) u → N' u = updN N (X D) (emptyLeaf t) u := by
    intro u hu hus huD
    have hnc : ∀ i, s < i → i ≤ D → u ≠ X i := fun i h1 h2 he => huD (hchain u i h1 h2 he)
    rw [updN_ne _ _ _ _ (hnc D hsD (Nat.le_refl _))]
    exact hagree u (hsubR u hu) hus hnc
  intro key' hkw
  rw [← hk key' hkw]
  exact getFromR_dropKlong _ N' V t fuel r (X s) (X (s + 1)) (K (s + 1)) (Nn s) sn' hTa hRa hwfa
    hXsa hsa hsl hsx hsn' hsl' hlive' hdead hother key'

/-- The upward delete at tree level, LE-b at the inner stop node X s, whose empty
key's klong names the chain: it names jy, the next child, whose klong jcv is
deleted. -/
theorem getFromR_up_leb (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat)
    (s D : Nat) (hsD : s < D) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hone : ∀ i, s < i → i < D → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hleaf : (Nn D).leaf = true) (honly : ∀ c z, (c, z) ∈ (Nn D).liveAt t → c = cv)
    (hnoval : ∀ i, s < i → i ≤ D → V (X i) = none)
    (hdist : ∀ i, s ≤ i → i < D → X i ≠ X D)
    (hrk : segRootR N t fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (X D, cv) ∈ eqVisits N t cv fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true → (x, cv) ∈ fromVisits N t fuel key' r →
      (x, cv) ∈ eqVisits N t cv fuel rk → N x = some m → m.leaf = true → key' = pre ++ [cv])
    (hagree : ∀ u, TReach N t r u → u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (jy : NodeId) (jcv : Nat) (hK0 : K (s + 1) = 0)
    (hsl : (Nn s).leaf = false) (hsj : (jcv, jy) ∈ (Nn s).liveAt t) (hj0 : 0 < jcv)
    (hmin : ∀ c z, (c, z) ∈ (Nn s).liveAt t → c = 0 ∨ jcv ≤ c)
    (hsn' : N' (X s) = some sn') (hsl' : sn'.leaf = false)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔
      (c = 0 ∧ z = jy) ∨ ((c, z) ∈ (Nn s).liveAt t ∧ c ≠ 0 ∧ c ≠ jcv)) :
    ∀ key', keyWf key' = true → getFromR N' V t fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N V t fuel key' r := by
  obtain ⟨hk, hTa, hRa, hwfa, hXsa, hdead, hchain, hsubR⟩ := up_prep N V t fuel hfuel r X Nn K s D hsD
    pre cv rk hT hR hwf hXs hN hlinkK hone hleaf honly (fun i h1 h2 => hnoval i (by omega) h2) hdist
    hrk hcv hvisL huniq
  have hsa : updN N (X D) (emptyLeaf t) (X s) = some (Nn s) := by
    rw [updN_ne _ _ _ _ (hdist s (Nat.le_refl _) hsD)]; exact hN s (Nat.le_refl _) (by omega)
  have hsx : (K (s + 1), X (s + 1)) ∈ (Nn s).liveAt t := by
    have := hlinkK (s + 1) (by omega) (by omega); simpa using this
  have hother : ∀ u, TReach (updN N (X D) (emptyLeaf t)) t r u → u ≠ X s →
      ¬ TReach (updN N (X D) (emptyLeaf t)) t (X (s + 1)) u → N' u = updN N (X D) (emptyLeaf t) u := by
    intro u hu hus huD
    have hnc : ∀ i, s < i → i ≤ D → u ≠ X i := fun i h1 h2 he => huD (hchain u i h1 h2 he)
    rw [updN_ne _ _ _ _ (hnc D hsD (Nat.le_refl _))]
    exact hagree u (hsubR u hu) hus hnc
  intro key' hkw
  rw [← hk key' hkw]
  rw [hK0] at hsx
  exact getFromR_lebDrop _ N' V t fuel r (X s) (X (s + 1)) jy jcv (Nn s) sn' hTa hRa hwfa
    hXsa hsa hsl hsx hsj hj0 hmin hsn' hsl' hlive' hdead hother key'

/-- The upward delete at tree level, the stop node X s a segment leaf, its klong
K (s + 1) to the emptied segment tree deleted. -/
theorem getFromR_up_leaf (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat)
    (s D : Nat) (hsD : s < D) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hT : TreeOK N t r) (hR : RangeOrder N t r)
    (hwf : ∀ x xn, TReach N t r x → N x = some xn → klongsWf xn.ks = true)
    (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hone : ∀ i, s < i → i < D → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hleaf : (Nn D).leaf = true) (honly : ∀ c z, (c, z) ∈ (Nn D).liveAt t → c = cv)
    (hnoval : ∀ i, s < i → i ≤ D → V (X i) = none)
    (hdist : ∀ i, s ≤ i → i < D → X i ≠ X D)
    (hrk : segRootR N t fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (X D, cv) ∈ eqVisits N t cv fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true → (x, cv) ∈ fromVisits N t fuel key' r →
      (x, cv) ∈ eqVisits N t cv fuel rk → N x = some m → m.leaf = true → key' = pre ++ [cv])
    (hagree : ∀ u, TReach N t r u → u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsl : (Nn s).leaf = true) (hsn' : N' (X s) = some sn') (hsl' : sn'.leaf = true)
    (hsw' : klongsWf sn'.ks = true)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔ (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
    ∀ key', keyWf key' = true → getFromR N' V t fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N V t fuel key' r := by
  obtain ⟨hk, hTa, hRa, hwfa, hXsa, hdead, hchain, hsubR⟩ := up_prep N V t fuel hfuel r X Nn K s D hsD
    pre cv rk hT hR hwf hXs hN hlinkK hone hleaf honly (fun i h1 h2 => hnoval i (by omega) h2) hdist
    hrk hcv hvisL huniq
  have hsa : updN N (X D) (emptyLeaf t) (X s) = some (Nn s) := by
    rw [updN_ne _ _ _ _ (hdist s (Nat.le_refl _) hsD)]; exact hN s (Nat.le_refl _) (by omega)
  have hsx : (K (s + 1), X (s + 1)) ∈ (Nn s).liveAt t := by
    have := hlinkK (s + 1) (by omega) (by omega); simpa using this
  have hother : ∀ u, TReach (updN N (X D) (emptyLeaf t)) t r u → u ≠ X s →
      ¬ TReach (updN N (X D) (emptyLeaf t)) t (X (s + 1)) u → N' u = updN N (X D) (emptyLeaf t) u := by
    intro u hu hus huD
    have hnc : ∀ i, s < i → i ≤ D → u ≠ X i := fun i h1 h2 he => huD (hchain u i h1 h2 he)
    rw [updN_ne _ _ _ _ (hnc D hsD (Nat.le_refl _))]
    exact hagree u (hsubR u hu) hus hnc
  intro key' hkw
  rw [← hk key' hkw]
  exact getFromR_dropLeafKlong _ N' V t fuel r (X s) (X (s + 1)) (K (s + 1)) (Nn s) sn' hTa hwfa
    hXsa hsa hsl hsx hsn' hsl' hsw' hlive'
    (deadAt_of_deadBelow _ V t fuel _ (hnoval (s + 1) (by omega) (by omega)) hdead) hother key'

end SIS.Tree
