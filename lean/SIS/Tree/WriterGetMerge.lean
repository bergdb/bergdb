/-
The writer's merge keeps every reading (bergdb 024-12, TP10's `OpGetOK`;
024-22): the tree with two sibling key nodes merged into one node, and the
parent's klongs to them made one, reads every key as before, if the siblings'
compare values lie in the ranges their parent's klongs give
(`getFromR_mergeOne`).
-/
import SIS.Tree.WriterTreeCascadeGen2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Searches by the live klongs -/

theorem mrg_searchLte_y (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t) (cv : Nat)
    (k : Nat) (y : NodeId) (hm : (k, y) ∈ m.liveAt t) (hle : k ≤ cv)
    (hmax : ∀ k' y', (k', y') ∈ m.liveAt t → k' ≤ cv → k' ≤ k) :
    (m.searchLte t cv).map (·.y) = some y := by
  rw [KNode.liveAt_of_times m t ht] at hm hmax
  exact KNode.searchLte_of_max m t ht cv k y hm (by exact_mod_cast hle)
    (fun q hq hqc => hmax q.1 q.2 hq (by exact_mod_cast hqc))

theorem mrg_searchLte_none (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t) (cv : Nat)
    (hall : ∀ k y, (k, y) ∈ m.liveAt t → cv < k) : m.searchLte t cv = none := by
  rw [KNode.liveAt_of_times m t ht] at hall
  exact KNode.searchLte_none_of m t ht cv (fun q hq => by have := hall q.1 q.2 hq; omega)

theorem mrg_searchLte_cases (m : KNode) (t : Time) (cv : Nat) :
    (m.searchLte t cv = none ∧ ∀ k y, (k, y) ∈ m.liveAt t → cv < k) ∨
    ∃ fd, m.searchLte t cv = some fd ∧ (fd.c, fd.y) ∈ m.liveAt t ∧ fd.c ≤ cv ∧
      ∀ k y, (k, y) ∈ m.liveAt t → k ≤ cv → k ≤ fd.c := by
  have hs := m.searchLte_spec t cv
  unfold NodeSearchSpec at hs
  cases h : m.searchLte t cv with
  | none =>
    left
    refine ⟨rfl, fun k y hk => ?_⟩
    have := hs.2.mp h (k, y) hk
    simp only [decide_eq_false_iff_not] at this
    omega
  | some fd =>
    right
    obtain ⟨hm, ha, hmax⟩ := hs.1 fd h
    simp only [decide_eq_true_eq] at ha
    refine ⟨fd, rfl, hm, by omega, fun k y hk hkc => ?_⟩
    have := hmax (k, y) hk (by simp only [decide_eq_true_eq]; omega)
    simpa using this

theorem mrg_liveAt_unique (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (k : Nat) (y y' : NodeId) (h1 : (k, y) ∈ m.liveAt t) (h2 : (k, y') ∈ m.liveAt t) : y = y' := by
  rw [KNode.liveAt_of_times m t ht] at h1 h2
  have := (lookup_of_mem_nodup _ (KNode.live_keys_nodup m) k y h1).symm.trans
    (lookup_of_mem_nodup _ (KNode.live_keys_nodup m) k y' h2)
  exact Option.some.inj this

theorem mrg_searchEq_y (m : KNode) (t : Time) (hw : klongsWf m.ks = true) (cv : Nat) :
    (m.searchEq t cv).map (·.y) = (m.liveAt t).lookup cv := searchEqSpec m t cv hw

theorem mrg_lookup_eq_of_iff (m1 m2 : KNode) (t : Time) (h1 : ∀ s, Klong.time s ∈ m1.ks → s ≤ t)
    (h2 : ∀ s, Klong.time s ∈ m2.ks → s ≤ t) (cv : Nat)
    (h : ∀ z, (cv, z) ∈ m1.liveAt t ↔ (cv, z) ∈ m2.liveAt t) :
    (m1.liveAt t).lookup cv = (m2.liveAt t).lookup cv := by
  rw [KNode.liveAt_of_times m1 t h1, KNode.liveAt_of_times m2 t h2] at h ⊢
  cases hl : m1.live.lookup cv with
  | none =>
    cases hl2 : m2.live.lookup cv with
    | none => rfl
    | some z =>
      have := (h z).mpr (lookup_some_mem hl2)
      rw [lookup_of_mem_nodup _ (KNode.live_keys_nodup m1) cv z this] at hl; cases hl
  | some z =>
    have := (h z).mp (lookup_some_mem hl)
    rw [lookup_of_mem_nodup _ (KNode.live_keys_nodup m2) cv z this]

/-! ## The merge into one node -/

/-- The descent for compare value cv in the tree after a merge into one node
finds what it found before, from any node reached but the two merged. -/
theorem getEqR_mergeOne (N N' : NodeId → Option KNode) (t : Time) (r p l rr m1 : NodeId)
    (pn ln rn pn' mn : KNode) (inner : Bool) (cL cR : Nat)
    (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hlt : cL < cR)
    (hadj : ∀ c z, (c, z) ∈ pn.liveAt t → c ≤ cL ∨ cR ≤ c)
    (hln : N l = some ln) (hrn : N rr = some rn) (hll : ln.leaf = !inner) (hrl : rn.leaf = !inner)
    (hlrange : ∀ c z, (c, z) ∈ ln.liveAt t → c < cR)
    (hrrange : ∀ c z, (c, z) ∈ rn.liveAt t → (inner = true → c = 0 ∨ cR < c) ∧
      (inner = false → cR ≤ c))
    (hrhead : inner = true → ∃ y0 tl, rn.live = (0, y0) :: tl)
    (hN'm1 : N' m1 = some mn) (hml : mn.leaf = !inner)
    (hmn : ∀ c z, (c, z) ∈ mn.liveAt t ↔ (c, z) ∈ mergeList inner cR ln.live rn.live)
    (hN'p : N' p = some pn') (hpl' : pn'.leaf = false)
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t ↔ (c = cL ∧ z = m1) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → N' y = N y)
    (hm1 : ¬ TReach N t r m1)
    (htimes : ∀ x xn, N x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ t)
    (hmt : ∀ s, Klong.time s ∈ mn.ks → s ≤ t) (hpt' : ∀ s, Klong.time s ∈ pn'.ks → s ≤ t)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) (hmwf : klongsWf mn.ks = true) :
    ∀ f x, TReach N t r x → x ≠ l → x ≠ rr → ∀ cv, getEqR N' t cv f x = getEqR N t cv f x := by
  have hlt' := htimes l ln hln
  have hrt' := htimes rr rn hrn
  have hlive_l : ln.liveAt t = ln.live := KNode.liveAt_of_times ln t hlt'
  have hlive_r : rn.liveAt t = rn.live := KNode.liveAt_of_times rn t hrt'
  have hpl_link : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hpr_link : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hpl_link
  have hrR : TReach N t r rr := TReach.link hp hpr_link
  -- l and rr have p as their only parent
  have hlpar : ∀ u c, TReach N t r u → TLink N t u c l → u = p ∧ c = cL :=
    fun u c hu h => hT.oneLink u c p cL l hu hp h hpl_link
  have hrpar : ∀ u c, TReach N t r u → TLink N t u c rr → u = p ∧ c = cR :=
    fun u c hu h => hT.oneLink u c p cR rr hu hp h hpr_link
  have hlp : l ≠ p := fun h => hT.no_self_link p cL hp (by rw [h] at hpl_link; exact hpl_link)
  have hrp : rr ≠ p := fun h => hT.no_self_link p cR hp (by rw [h] at hpr_link; exact hpr_link)
  -- a child of a node reached is neither merged node, but from p by cL or cR
  have hchild : ∀ u c z, TReach N t r u → TLink N t u c z → (u ≠ p ∨ (c ≠ cL ∧ c ≠ cR)) →
      z ≠ l ∧ z ≠ rr := by
    intro u c z hu hlk hne
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at hlk
      obtain ⟨a, b⟩ := hlpar u c hu hlk
      rcases hne with hne | ⟨hne, _⟩
      · exact hne a
      · exact hne b
    · rw [h] at hlk
      obtain ⟨a, b⟩ := hrpar u c hu hlk
      rcases hne with hne | ⟨_, hne⟩
      · exact hne a
      · exact hne b
  -- the merged node's live klongs
  have hmn' : ∀ c z, (c, z) ∈ mn.liveAt t ↔ (c, z) ∈ ln.live ∨
      (inner = false ∧ (c, z) ∈ rn.live) ∨
      (inner = true ∧ ∃ y0 tl, rn.live = (0, y0) :: tl ∧ ((c = cR ∧ z = y0) ∨ (c, z) ∈ tl)) := by
    intro c z
    rw [hmn c z]
    unfold mergeList
    rw [List.mem_append]
    cases inner with
    | false => simp
    | true =>
      obtain ⟨y0, tl, htl⟩ := hrhead rfl
      simp only [↓reduceIte, htl, renameHead, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨trivial, y0, tl, rfl, h⟩)
      · rintro (h | ⟨h, _⟩ | ⟨_, y1, tl1, he, h⟩)
        · exact Or.inl h
        · cases h
        · simp only [List.cons.injEq, Prod.mk.injEq, true_and] at he
          obtain ⟨rfl, rfl⟩ := he
          exact Or.inr h
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
  intro x hx hxl hxr cv
  cases f with
  | zero => rfl
  | succ f' =>
  by_cases hxp : x = p
  · subst hxp
    simp only [getEqR, hN'p, hpn, hpl, hpl', Bool.false_eq_true, ↓reduceIte]
    have hpt := htimes x pn hpn
    rcases mrg_searchLte_cases pn t cv with ⟨hnone, hall⟩ | ⟨fd, hfd, hfm, hfle, hfmax⟩
    · rw [hnone, mrg_searchLte_none pn' t hpt' cv (by
        intro k y hk
        rcases (hpn' k y).mp hk with ⟨hk1, _⟩ | ⟨hk1, _, _⟩
        · rw [hk1]; exact hall cL l hl
        · exact hall k y hk1)]
    · rw [hfd]
      by_cases hc1 : fd.c = cL
      · -- the search found l
        have hfy : fd.y = l := mrg_liveAt_unique pn t hpt cL fd.y l (by rw [← hc1]; exact hfm) hl
        have hcv : cv < cR := by
          rcases Nat.lt_or_ge cv cR with h | h
          · exact h
          · have := hfmax cR rr hrr h; omega
        have h2 := mrg_searchLte_y pn' t hpt' cv cL m1 ((hpn' cL m1).mpr (Or.inl ⟨rfl, rfl⟩))
          (by omega) (by
            intro k' y' hk' hkc
            rcases (hpn' k' y').mp hk' with ⟨hk1, _⟩ | ⟨hk1, _, _⟩
            · omega
            · have := hfmax k' y' hk1 hkc; omega)
        cases hfd2 : pn'.searchLte t cv with
        | none => rw [hfd2] at h2; cases h2
        | some fd2 =>
          rw [hfd2] at h2
          simp only [Option.map_some, Option.some.injEq] at h2
          simp only
          rw [h2, hfy]
          cases f' with
          | zero => rfl
          | succ f'' =>
          simp only [getEqR, hN'm1, hln, hml, hll]
          cases inner with
          | false =>
            simp only [Bool.not_false, ↓reduceIte]
            rw [mrg_searchEq_y mn t hmwf cv, mrg_searchEq_y ln t (hwf l ln hln) cv]
            apply mrg_lookup_eq_of_iff mn ln t hmt hlt' cv
            intro z
            rw [hmn' cv z, hlive_l]
            constructor
            · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
              · exact h
              · have := (hrrange cv z (by rw [hlive_r]; exact h)).2 rfl; omega
              · cases h
            · intro h; exact Or.inl h
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rcases mrg_searchLte_cases ln t cv with ⟨hn2, hall2⟩ | ⟨fd', hfd', hfm', hfle', hfmax'⟩
            · rw [hn2, mrg_searchLte_none mn t hmt cv (by
                intro k y hk
                rcases (hmn' k y).mp hk with h | ⟨h, _⟩ | ⟨_, y0, tl, htl, h⟩
                · exact hall2 k y (by rw [hlive_l]; exact h)
                · cases h
                · rcases h with ⟨hk1, _⟩ | h
                  · omega
                  · have := (hrrange k y (by rw [hlive_r, htl]; exact List.mem_cons_of_mem _ h)).1 rfl
                    rcases this with h0 | h0
                    · -- a second key 0 in rn
                      exfalso
                      have hnd := KNode.live_keys_nodup rn
                      rw [htl] at hnd
                      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
                      exact hnd.1 ⟨(k, y), h, h0⟩
                    · omega)]
            · have h3 := mrg_searchLte_y mn t hmt cv fd'.c fd'.y
                ((hmn' _ _).mpr (Or.inl (by rw [← hlive_l]; exact hfm'))) hfle' (by
                  intro k' y' hk' hkc
                  rcases (hmn' k' y').mp hk' with h | ⟨h, _⟩ | ⟨_, y0, tl, htl, h⟩
                  · exact hfmax' k' y' (by rw [hlive_l]; exact h) hkc
                  · cases h
                  · rcases h with ⟨hk1, _⟩ | h
                    · omega
                    · have := (hrrange k' y' (by rw [hlive_r, htl]; exact List.mem_cons_of_mem _ h)).1 rfl
                      rcases this with h0 | h0
                      · exfalso
                        have hnd := KNode.live_keys_nodup rn
                        rw [htl] at hnd
                        simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
                        exact hnd.1 ⟨(k', y'), h, h0⟩
                      · omega)
              rw [hfd']
              cases hfd3 : mn.searchLte t cv with
              | none => rw [hfd3] at h3; cases h3
              | some fd3 =>
                rw [hfd3] at h3
                simp only [Option.map_some, Option.some.injEq] at h3
                simp only
                rw [h3]
                have hlink : TLink N t l fd'.c fd'.y := ⟨ln, hln, hfm'⟩
                have hcR := hchild l fd'.c fd'.y hlR hlink (Or.inl hlp)
                exact ih f'' (by omega) fd'.y (TReach.link hlR hlink) hcR.1 hcR.2 cv
      · by_cases hc2 : fd.c = cR
        · -- the search found rr
          have hfy : fd.y = rr := mrg_liveAt_unique pn t hpt cR fd.y rr (by rw [← hc2]; exact hfm) hrr
          have hcv : cR ≤ cv := by omega
          have h2 := mrg_searchLte_y pn' t hpt' cv cL m1 ((hpn' cL m1).mpr (Or.inl ⟨rfl, rfl⟩))
            (by omega) (by
              intro k' y' hk' hkc
              rcases (hpn' k' y').mp hk' with ⟨hk1, _⟩ | ⟨hk1, hne1, hne2⟩
              · omega
              · have := hfmax k' y' hk1 hkc
                rcases hadj k' y' hk1 with h | h
                · exact h
                · omega)
          cases hfd2 : pn'.searchLte t cv with
          | none => rw [hfd2] at h2; cases h2
          | some fd2 =>
            rw [hfd2] at h2
            simp only [Option.map_some, Option.some.injEq] at h2
            simp only
            rw [h2, hfy]
            cases f' with
            | zero => rfl
            | succ f'' =>
            simp only [getEqR, hN'm1, hrn, hml, hrl]
            cases inner with
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              rw [mrg_searchEq_y mn t hmwf cv, mrg_searchEq_y rn t (hwf rr rn hrn) cv]
              apply mrg_lookup_eq_of_iff mn rn t hmt hrt' cv
              intro z
              rw [hmn' cv z, hlive_r]
              constructor
              · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
                · have := hlrange cv z (by rw [hlive_l]; exact h); omega
                · exact h
                · cases h
              · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨y0, tl, htl⟩ := hrhead rfl
              have hhead : (0, y0) ∈ rn.liveAt t := by rw [hlive_r, htl]; exact List.mem_cons_self
              rcases mrg_searchLte_cases rn t cv with ⟨_, hall2⟩ | ⟨fd', hfd', hfm', hfle', hfmax'⟩
              · have := hall2 0 y0 hhead; omega
              · -- the tail of rn above cR, its head renamed cR
                have htl_gt : ∀ k y, (k, y) ∈ tl → cR < k := by
                  intro k y h
                  have := (hrrange k y (by rw [hlive_r, htl]; exact List.mem_cons_of_mem _ h)).1 rfl
                  rcases this with h0 | h0
                  · exfalso
                    have hnd := KNode.live_keys_nodup rn
                    rw [htl] at hnd
                    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
                    exact hnd.1 ⟨(k, y), h, h0⟩
                  · exact h0
                have hmem_r : ∀ k y, (k, y) ∈ rn.liveAt t → (k = 0 ∧ y = y0) ∨ (k, y) ∈ tl := by
                  intro k y h
                  rw [hlive_r, htl] at h
                  rcases List.mem_cons.mp h with h | h
                  · simp only [Prod.mk.injEq] at h; exact Or.inl h
                  · exact Or.inr h
                have h3 : (mn.searchLte t cv).map (·.y) = some fd'.y := by
                  rcases hmem_r _ _ hfm' with ⟨hk0, hy0⟩ | htlm
                  · -- the head: cR in the merged node
                    rw [hy0]
                    apply mrg_searchLte_y mn t hmt cv cR y0
                      ((hmn' _ _).mpr (Or.inr (Or.inr ⟨rfl, y0, tl, htl, Or.inl ⟨rfl, rfl⟩⟩))) hcv
                    intro k' y' hk' hkc
                    rcases (hmn' k' y').mp hk' with h | ⟨h, _⟩ | ⟨_, y1, tl1, htl1, h⟩
                    · have := hlrange k' y' (by rw [hlive_l]; exact h); omega
                    · cases h
                    · rw [htl] at htl1
                      simp only [List.cons.injEq, Prod.mk.injEq, true_and] at htl1
                      obtain ⟨rfl, rfl⟩ := htl1
                      rcases h with ⟨hk1, _⟩ | h
                      · omega
                      · have h4 := hfmax' k' y' (by rw [hlive_r, htl]; exact List.mem_cons_of_mem _ h) hkc
                        have h5 := htl_gt k' y' h
                        omega
                  · apply mrg_searchLte_y mn t hmt cv fd'.c fd'.y
                      ((hmn' _ _).mpr (Or.inr (Or.inr ⟨rfl, y0, tl, htl, Or.inr htlm⟩))) hfle'
                    intro k' y' hk' hkc
                    have hgt := htl_gt _ _ htlm
                    rcases (hmn' k' y').mp hk' with h | ⟨h, _⟩ | ⟨_, y1, tl1, htl1, h⟩
                    · have := hlrange k' y' (by rw [hlive_l]; exact h); omega
                    · cases h
                    · rw [htl] at htl1
                      simp only [List.cons.injEq, Prod.mk.injEq, true_and] at htl1
                      obtain ⟨rfl, rfl⟩ := htl1
                      rcases h with ⟨hk1, _⟩ | h
                      · omega
                      · exact hfmax' k' y' (by rw [hlive_r, htl]; exact List.mem_cons_of_mem _ h) hkc
                rw [hfd']
                cases hfd3 : mn.searchLte t cv with
                | none => rw [hfd3] at h3; cases h3
                | some fd3 =>
                  rw [hfd3] at h3
                  simp only [Option.map_some, Option.some.injEq] at h3
                  simp only
                  rw [h3]
                  have hlink : TLink N t rr fd'.c fd'.y := ⟨rn, hrn, hfm'⟩
                  have hcR := hchild rr fd'.c fd'.y hrR hlink (Or.inl hrp)
                  exact ih f'' (by omega) fd'.y (TReach.link hrR hlink) hcR.1 hcR.2 cv
        · -- the search found neither: the same child
          have h2 := mrg_searchLte_y pn' t hpt' cv fd.c fd.y ((hpn' _ _).mpr (Or.inr ⟨hfm, hc1, hc2⟩))
            hfle (by
              intro k' y' hk' hkc
              rcases (hpn' k' y').mp hk' with ⟨hk1, _⟩ | ⟨hk1, _, _⟩
              · rw [hk1]; exact hfmax cL l hl (by omega)
              · exact hfmax k' y' hk1 hkc)
          cases hfd2 : pn'.searchLte t cv with
          | none => rw [hfd2] at h2; cases h2
          | some fd2 =>
            rw [hfd2] at h2
            simp only [Option.map_some, Option.some.injEq] at h2
            simp only
            rw [h2]
            have hlink : TLink N t x fd.c fd.y := ⟨pn, hpn, hfm⟩
            have hcR := hchild x fd.c fd.y hx hlink (Or.inr ⟨hc1, hc2⟩)
            exact ih f' (by omega) fd.y (TReach.link hx hlink) hcR.1 hcR.2 cv
  · -- a node that the merge does not change
    have hxm : x ≠ m1 := fun h => hm1 (h ▸ hx)
    have hN' := hother x hxp hxl hxr hxm
    simp only [getEqR, hN']
    cases hN : N x with
    | none => rfl
    | some n =>
      simp only
      cases hnl : n.leaf with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          have hlink : TLink N t x fd.c fd.y := ⟨n, hN, KNode.searchLte_mem n t cv fd hfd⟩
          have hcR := hchild x fd.c fd.y hx hlink (Or.inl hxp)
          exact ih f' (by omega) fd.y (TReach.link hx hlink) hcR.1 hcR.2 cv

/-- What a descent finds is a link of a segment leaf reached. -/
theorem mrg_getEqR_leaf (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) (cv : Nat) :
    ∀ f x y, TReach N t r x → getEqR N t cv f x = some y →
      ∃ u un, TReach N t r u ∧ N u = some un ∧ un.leaf = true ∧ TLink N t u cv y := by
  intro f
  induction f with
  | zero => intro x y _ h; simp [getEqR] at h
  | succ f ih =>
    intro x y hx h
    simp only [getEqR] at h
    cases hN : N x with
    | none => rw [hN] at h; cases h
    | some n =>
      rw [hN] at h
      simp only at h
      cases hl : n.leaf with
      | true =>
        rw [hl] at h
        simp only [↓reduceIte] at h
        cases hfd : n.searchEq t cv with
        | none => rw [hfd] at h; cases h
        | some fd =>
          rw [hfd] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨x, n, hx, hN, hl, n, hN, KNode.searchEq_mem n t cv fd (hwf x n hN) hfd⟩
      | false =>
        rw [hl] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hfd : n.searchLte t cv with
        | none => rw [hfd] at h; cases h
        | some fd =>
          rw [hfd] at h
          simp only at h
          exact ih fd.y y (TReach.link hx ⟨n, hN, KNode.searchLte_mem n t cv fd hfd⟩) h

/-- The tree after a merge into one node reads every key as before. -/
theorem getFromR_mergeOne (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r p l rr m1 : NodeId)
    (pn ln rn pn' mn : KNode) (inner : Bool) (cL cR : Nat)
    (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hlt : cL < cR)
    (hadj : ∀ c z, (c, z) ∈ pn.liveAt t → c ≤ cL ∨ cR ≤ c)
    (hln : N l = some ln) (hrn : N rr = some rn) (hll : ln.leaf = !inner) (hrl : rn.leaf = !inner)
    (hlrange : ∀ c z, (c, z) ∈ ln.liveAt t → c < cR)
    (hrrange : ∀ c z, (c, z) ∈ rn.liveAt t → (inner = true → c = 0 ∨ cR < c) ∧
      (inner = false → cR ≤ c))
    (hrhead : inner = true → ∃ y0 tl, rn.live = (0, y0) :: tl)
    (hN'm1 : N' m1 = some mn) (hml : mn.leaf = !inner)
    (hmn : ∀ c z, (c, z) ∈ mn.liveAt t ↔ (c, z) ∈ mergeList inner cR ln.live rn.live)
    (hN'p : N' p = some pn') (hpl' : pn'.leaf = false)
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t ↔ (c = cL ∧ z = m1) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → N' y = N y)
    (hm1 : ¬ TReach N t r m1)
    (htimes : ∀ x xn, N x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ t)
    (hmt : ∀ s, Klong.time s ∈ mn.ks → s ≤ t) (hpt' : ∀ s, Klong.time s ∈ pn'.ks → s ≤ t)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) (hmwf : klongsWf mn.ks = true) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hE := getEqR_mergeOne N N' t r p l rr m1 pn ln rn pn' mn inner cL cR hT hp hpn hpl hl hrr hlt
    hadj hln hrn hll hrl hlrange hrrange hrhead hN'm1 hml hmn hN'p hpl' hpn' hother hm1 htimes hmt hpt'
    hwf hmwf
  have hpl_link : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hpr_link : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  -- a node found by a descent is neither merged node
  have hfound : ∀ cv x y, TReach N t r x → getEqR N t cv fuel x = some y →
      TReach N t r y ∧ y ≠ l ∧ y ≠ rr ∧ (N' y).isSome = (N y).isSome := by
    intro cv x y hx h
    obtain ⟨u, un, hu, hun, hul, hlk⟩ := mrg_getEqR_leaf N t r hwf cv fuel x y hx h
    have hyR : TReach N t r y := TReach.link hu hlk
    have hup : u ≠ p := fun he => by rw [he, hpn] at hun; cases hun; rw [hpl] at hul; cases hul
    refine ⟨hyR, fun he => ?_, fun he => ?_, ?_⟩
    · rw [he] at hlk; exact hup (hT.oneLink u cv p cL l hu hp hlk hpl_link).1
    · rw [he] at hlk; exact hup (hT.oneLink u cv p cR rr hu hp hlk hpr_link).1
    · by_cases hyp : y = p
      · rw [hyp, hN'p, hpn]; rfl
      · have hyl : y ≠ l := fun he => by
          rw [he] at hlk; exact hup (hT.oneLink u cv p cL l hu hp hlk hpl_link).1
        have hyr : y ≠ rr := fun he => by
          rw [he] at hlk; exact hup (hT.oneLink u cv p cR rr hu hp hlk hpr_link).1
        have hym : y ≠ m1 := fun he => hm1 (he ▸ hyR)
        rw [hother y hyp hyl hyr hym]
  have hrl0 : r ≠ l := fun h => hT.rootFree p cL hp (by rw [h]; exact hpl_link)
  have hrr0 : r ≠ rr := fun h => hT.rootFree p cR hp (by rw [h]; exact hpr_link)
  suffices hgen : ∀ key x, TReach N t r x → x ≠ l → x ≠ rr →
      getFromR N' V t fuel key x = getFromR N V t fuel key x from
    fun key => hgen key r TReach.root hrl0 hrr0
  intro key
  induction key with
  | nil => intro x _ _ _; rfl
  | cons cv rest ih =>
    intro x hx hxl hxr
    cases rest with
    | nil =>
      simp only [getFromR]
      rw [hE fuel x hx hxl hxr cv]
    | cons d rest' =>
      simp only [getFromR]
      rw [hE fuel x hx hxl hxr cv]
      cases hg : getEqR N t cv fuel x with
      | none => rfl
      | some y =>
        simp only
        obtain ⟨hyR, hyl, hyr, hsome⟩ := hfound cv x y hx hg
        rw [hsome]
        split
        · exact ih y hyR hyl hyr
        · rfl

end SIS.Tree
