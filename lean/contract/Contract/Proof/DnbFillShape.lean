/-
bergdb 030-37: the live occupancy, shape and dead-klong invariants imply
all of the trace checker's fill rules, with enough fuel for its walk.
-/
import Contract.Proof.DnbDeadHistory

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {s : Tree}

theorem shapeWalk_nil_of_kept (hd : AllDeadSafe cf s) :
    ∀ (f g h : Nat) (x : NodeId) (root : Bool) {lo : Nat} {hi : Option Nat},
      Shaped cf s g h x → Good s x lo hi → Filled cf s root x → s.fuel x ≤ f →
      shapeWalk ⟨cf.H, cf.m, cf.theta⟩ s f x root = []
  | 0, g, h, x, root, lo, hi, hsh, hg, hf, hfu => by
    obtain ⟨n, ho, _⟩ := shaped_obj hsh
    simp only [Tree.fuel, ho] at hfu
    omega
  | f + 1, g, h, x, root, lo, hi, hsh, hg, hf, hfu => by
    obtain ⟨n, ho, hk, hlev, hleaf, hG, hH⟩ := shaped_getKey hsh
    have hF := filled_key hf ho
    have hht : (n.level - 1) % (cf.H + 1) = h := by
      change cf.htOf n.level = h
      rw [hlev]
      exact htOf_lev cf hH
    have hleft : (if !n.leaf && !(live n.ks).isEmpty &&
        ((live n.ks).head?.map (·.1)) != some 0 then ["LeftmostOK"] else []) = [] := by
      cases h with
      | zero => simp [hleaf]
      | succ h => simp [(shaped_inner hsh ho).1]
    have hroots : (if !n.leaf && root && (live n.ks).length < 2 then ["RootsOK"] else []) = [] := by
      cases hl : n.leaf <;> cases hr : root <;> simp only [hl, hr, Bool.not_false, Bool.not_true,
        Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right (by
        simp only [decide_eq_true_eq]
        exact Nat.not_lt.mpr (hF.1 hl hr))]
    have hfill : (if decide (2 ≤ cf.m) && !root && (live n.ks).length < cf.m then
        ["FillOK"] else []) = [] := by
      by_cases hm : 2 ≤ cf.m
      · cases hr : root
        · simp only [hm, decide_true, Bool.not_false, Bool.true_and]
          rw [ite_eq_right (by
            simp only [decide_eq_true_eq]
            exact Nat.not_lt.mpr (hF.2.1 hm hr))]
        · simp [hr]
      · simp [hm]
    have hdead : (if cf.theta != 0 && decide (cf.theta < deadCount n.ks) then
        ["DeadOK"] else []) = [] := by
      rcases hd x n ho with hz | hn
      · simp [hz]
      · simp [Nat.not_lt.mpr hn]
    have hbal : (if n.leaf != ((n.level - 1) % (cf.H + 1) == 0) then
        ["BalancedOK"] else []) = [] := by simp [hht, hleaf]
    have hfu' : n.level ≤ f := by simp only [Tree.fuel, ho] at hfu; omega
    have hkids : (live n.ks).flatMap (fun (c, y) =>
        if n.leaf then (if isLong c then shapeWalk ⟨cf.H, cf.m, cf.theta⟩ s f y true else [])
        else (match s.obj y with
          | some (.key m) => if m.level + 1 != n.level then ["BalancedOK"] else []
          | _ => []) ++ shapeWalk ⟨cf.H, cf.m, cf.theta⟩ s f y false) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      rintro ⟨c, y⟩ hm
      have hfy : s.fuel y ≤ f := le_trans (good_child_fuel hg ho hm) hfu'
      cases h with
      | zero =>
        have hnl : n.leaf = true := by simpa using hleaf
        simp only [hnl, ↓reduceIte]
        split
        · rename_i hlong
          have hshy : Shaped cf s (g + 1) (htIn cf s y) y := by
            cases hsh with
            | leaf ho' _ _ _ hl =>
              rw [ho] at ho'; cases ho'
              exact hl c y hm hlong
          obtain ⟨lo', hi', hgy⟩ := good_key_child hg ho hm (fun _ => hlong)
          exact shapeWalk_nil_of_kept hd f (g + 1) _ y true hshy hgy
            (hF.2.2.1 c y hm hnl hlong) hfy
        · rfl
      | succ h =>
        have hnl : n.leaf = false := by simpa using hleaf
        have hshy := (shaped_inner hsh ho).2 c y hm
        obtain ⟨m, hmy, hml, _⟩ := shaped_obj hshy
        have hlevel : m.level + 1 = n.level := by rw [hml, hlev, Cfg.lev_succ]
        obtain ⟨lo', hi', hgy⟩ := good_key_child hg ho hm (fun he => by rw [hnl] at he; cases he)
        have hwalk := shapeWalk_nil_of_kept hd f g h y false hshy hgy
          (hF.2.2.2 c y hm hnl) hfy
        simp [hnl, hmy, hlevel, hwalk]
    simp only [shapeWalk, ho, hleft, hroots, hfill, hdead, hbal, List.nil_append]
    exact hkids

theorem fillOk_of_kept {b G H : Nat} {t : Time} {tp : Top} {nx : NodeId}
    (hI : Inv (Cfg.java b G H) t s tp nx)
    (hf : RootFilled (Cfg.java b G H) s) (hd : AllDeadSafe (Cfg.java b G H) s) : FillOk b H s := by
  obtain ⟨r, hr, hs⟩ := hI.shaped
  change shapeFaults ⟨(Cfg.java b G H).H, (Cfg.java b G H).m, (Cfg.java b G H).theta⟩ s = []
  simp only [shapeFaults, hr]
  exact shapeWalk_nil_of_kept hd _ 0 _ r true hs (good_of_invOk hr hI.inv) (hf r hr) le_rfl

/-- All of FillOk, including DeadOK and the checker's finite walk, holds
after every PE history from empty. No join restriction is assumed. -/
theorem pe_fillOk_hist {b G H : Nat} (hb : 8 ≤ b)
    {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}
    (hh : PeHist (Cfg.java b G H) (startTree (Cfg.java b G H)) startTop startNext txs s tp nx) :
    FillOk b H s := by
  obtain ⟨h0, hs, ht⟩ := start_inv (cfgOk_java8 hb)
  have hI := (pe_meetsTop (cfgOk_java8 hb) h0 hs ht hh).2
  exact fillOk_of_kept hI (pe_rootFilled_hist hb hh) (pe_allDeadSafe_hist hb hh)

end Contract.PE
