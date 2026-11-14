import SIS.Tree.GetCascadeIP
import SIS.Tree.FuelPaths
import SIS.Tree.GetFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Splits that make a new root (bergdb 024-12, TP10): the space root's space
split, or a segment root's space split below a segment leaf, puts a new inner
node R above the halves. A reader from R takes one level more than from the old
node; when the new root's segment tree has depth below the fuel (`SegDepthLe`,
`GetFuel.lean`), it finds the same. -/

/-- Paths in N are paths in N' when N' agrees with N on the nodes N reaches. -/
theorem PathLen.of_agree (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ x, TReach N t r x → N' x = N x) : ∀ z k, PathLen N t r z k → PathLen N' t r z k := by
  intro z k hz
  induction hz with
  | root => exact PathLen.root
  | link hp hl ih =>
    obtain ⟨m, hm, hc⟩ := hl
    exact PathLen.link ih ⟨m, by rw [h _ hp.reach]; exact hm, hc⟩

theorem PathsFit.of_agree (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) (fuel : Nat)
    (h : ∀ x, TReach N t r x → N' x = N x) (hf : PathsFit N' t r fuel) : PathsFit N t r fuel :=
  fun z k hz => hf z k (PathLen.of_agree N N' t r h z k hz)

/-- The reading from a new root Y over the halves F and S of the node x's
contents xv is the reading from x, when Y's segment tree has depth at most
fuel - 1 (every path inside it shorter than the fuel). -/
theorem getFromR_newRootRead (V A : NodeId → Option KNode) (Val : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (x F S Y : NodeId) (xv f s : KNode) (sc : Nat)
    (hVx : V x = some xv) (hAY : A Y = some ⟨false, newKlongs t [(0, F), (sc, S)]⟩)
    (hAF : A F = some f) (hAS : A S = some s) (hfl : f.leaf = xv.leaf) (hsl : s.leaf = xv.leaf)
    (hleafF : xv.leaf = true → ∀ c, c < sc → (f.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hleafS : xv.leaf = true → ∀ c, sc ≤ c → (s.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hinF : xv.leaf = false → ∀ c : Nat, c < sc →
      (f.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hinS : xv.leaf = false → ∀ c : Nat, sc ≤ c →
      (s.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hwf : ∀ z zn, ReachS V t x z → V z = some zn → klongsWf zn.ks = true)
    (hagree : ∀ z, ReachS V t x z → z ≠ x → A z = V z)
    (hnox : ∀ z zn c, ReachS V t x z → V z = some zn → (c, x) ∉ zn.liveAt t)
    (hfit : SegDepthLe A t (fuel - 1) Y) (hfuel2 : 2 ≤ fuel) :
    ∀ key, getFromR A Val t fuel key Y = getFromR V Val t fuel key x := by
  -- the nodes below a node other than x are not x
  have hbelow : ∀ y z, ReachS V t x y → y ≠ x → ReachS V t y z → ReachS V t x z ∧ z ≠ x := by
    intro y z hy hyx hz
    refine ⟨reachS_trans V t x y hy z hz, ?_⟩
    cases hz with
    | root => exact hyx
    | step u un c _ hu hun hmem =>
      intro he
      exact hnox u un c (reachS_trans V t x y hy u hu) hun (he ▸ hmem)
  have hvis : ∀ y c f, ReachS V t x y → y ≠ x → ∀ q ∈ eqVisits V t c f y,
      q.1 ≠ x ∧ ReachS V t x q.1 := by
    intro y c f hy hyx q hq
    obtain ⟨a, b⟩ := q
    have hq2 := eqVisits_snd V t c f y (a, b) hq
    simp only at hq2
    subst hq2
    have hr := eqVisits_reach V t y b f y a b ReachS.root hq
    have := hbelow y a hy hyx hr
    exact ⟨this.2, this.1⟩
  have hchild : ∀ y, ReachS V t x y → y ≠ x → ∀ c f, getEqR A t c f y = getEqR V t c f y := by
    intro y hy hyx c f
    exact ((getEqR_frame V A t c f y (fun q hq =>
      Or.inl (hagree q.1 (hvis y c f hy hyx q hq).2 (hvis y c f hy hyx q hq).1).symm)).1).symm
  -- a half searches as xv, one level below the new root
  have hhalf : ∀ (Z : NodeId) (zn : KNode) (c f2 : Nat), A Z = some zn → zn.leaf = xv.leaf →
      (xv.leaf = true → (zn.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y)) →
      (xv.leaf = false → (zn.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y)) →
      (∃ c1, TLink A t Y c1 Z) →
      fuel = f2 + 2 → getEqR A t c (f2 + 1) Z = getEqR V t c (f2 + 2) x := by
    intro Z zn c f2 hZ hzl hEq hLte hYZ hf2
    simp only [getEqR, hZ, hVx, hzl]
    cases hxl : xv.leaf with
    | true => simp only [↓reduceIte]; exact hEq hxl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have he := hLte hxl
      cases h1 : xv.searchLte t c with
      | none =>
        rw [h1] at he
        cases h2 : zn.searchLte t c with
        | none => rfl
        | some _ => rw [h2] at he; cases he
      | some fd =>
        rw [h1] at he
        cases h2 : zn.searchLte t c with
        | none => rw [h2] at he; cases he
        | some fd2 =>
          rw [h2] at he
          simp only [Option.map_some, Option.some.injEq] at he
          simp only
          rw [he]
          have hmem := KNode.searchLte_mem xv t c fd h1
          have hry : ReachS V t x fd.y := ReachS.step x xv fd.c fd.y ReachS.root hVx hmem
          have hyx : fd.y ≠ x := fun h => hnox x xv fd.c ReachS.root hVx (h ▸ hmem)
          rw [hchild fd.y hry hyx c f2]
          -- the child is two levels below Y in A, so V's paths from it fit f2
          obtain ⟨c1, hl1⟩ := hYZ
          have hmem2 := KNode.searchLte_mem zn t c fd2 h2
          rw [he] at hmem2
          have hagy : ∀ u, ReachS V t fd.y u → A u = V u := by
            intro u hu
            have hu' := reachS_trans V t x fd.y hry u hu
            exact hagree u hu' (hbelow fd.y u hry hyx hu).2
          -- Z is one level below Y, fd.y two
          have hZd : SegDepthLe A t f2 Z := by
            obtain ⟨yn, hyn, hyc⟩ := hl1
            rw [hAY] at hyn; cases hyn
            have h1 : fuel - 1 = f2 + 1 := by omega
            rw [h1] at hfit
            exact hfit _ hAY rfl c1 Z hyc
          cases f2 with
          | zero =>
            have := hZd zn hZ
            rw [hzl, hxl] at this; cases this
          | succ f3 =>
            have hyd : SegDepthLe A t f3 fd.y := hZd zn hZ (by rw [hzl, hxl]) fd2.c fd.y hmem2
            have hyV := SegDepthLe.of_agree V A t f3 fd.y hagy hyd
            exact getEqR_fuel_mono V t c f3 fd.y hyV (f3 + 1) (f3 + 1 + 1) (by omega) (by omega)
  have hget : ∀ c, getEqR A t c fuel Y = getEqR V t c fuel x := by
    intro c
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 2 := ⟨fuel - 2, by omega⟩
    have hR := KNode.rootPair_searchLte t F S sc c
    rw [hf2]
    simp only [getEqR, hAY, Bool.false_eq_true, ↓reduceIte]
    cases hs : (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).searchLte t c with
    | none => rw [hs] at hR; cases hR
    | some fd =>
      rw [hs] at hR
      simp only [Option.map_some, Option.some.injEq] at hR
      simp only
      rw [hR]
      have hmemR := KNode.searchLte_mem _ t c fd hs
      by_cases hc : c < sc
      · simp only [hc, ↓reduceIte]
        simp only [hc, ↓reduceIte] at hR
        exact hhalf F f c f2 hAF hfl (fun h => hleafF h c hc) (fun h => hinF h c hc)
          ⟨fd.c, _, hAY, by have := hmemR; rw [hR] at this; exact this⟩ hf2
      · simp only [hc, ↓reduceIte]
        simp only [hc, ↓reduceIte] at hR
        exact hhalf S s c f2 hAS hsl (fun h => hleafS h c (by omega)) (fun h => hinS h c (by omega))
          ⟨fd.c, _, hAY, by have := hmemR; rw [hR] at this; exact this⟩ hf2
  -- what a descent from x finds is below x and not x
  have hfound : ∀ c y, getEqR V t c fuel x = some y → ReachS V t x y ∧ y ≠ x := by
    intro c y h
    obtain ⟨z, zn, hz, hzn, hzl, hs⟩ := getEqR_some_visit V t c fuel x y h
    have hrz := eqVisits_reach V t x c fuel x z c ReachS.root hz
    cases hfd : zn.searchEq t c with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have hmem := KNode.searchEq_mem zn t c fd (hwf z zn hrz hzn) hfd
      exact ⟨ReachS.step z zn c fd.y hrz hzn hmem,
        fun h => hnox z zn c hrz hzn (h ▸ hmem)⟩
  intro key
  cases key with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil => simp only [getFromR]; rw [hget c]
    | cons d more =>
      simp only [getFromR]
      rw [hget c]
      cases hg : getEqR V t c fuel x with
      | none => rfl
      | some y =>
        simp only
        obtain ⟨hry, hyx⟩ := hfound c y hg
        rw [hagree y hry hyx]
        split
        · symm
          have hf1 : 1 ≤ fuel := by
            cases fuel with
            | zero => simp [getEqR] at hg
            | succ f => omega
          apply getFromR_frame V A Val Val t fuel hf1 (d :: more) y
          · intro q hq
            have hwfy : ∀ z zn, ReachS V t y z → V z = some zn → klongsWf zn.ks = true :=
              fun z zn hz hzn => hwf z zn (reachS_trans V t x y hry z hz) hzn
            have hr := fromVisits_reach V t fuel y hwfy (d :: more) y q.1 q.2 ReachS.root hq
            obtain ⟨h1, h2⟩ := hbelow y q.1 hry hyx hr
            exact Or.inl (hagree q.1 h1 h2).symm
          · intro _ _ _ _ _ _ _ _; rfl
        · rfl

end SIS.Tree
