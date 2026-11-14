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

/-! ## The merge into two nodes: the merged node's halves -/

/-- A node of klongs `newKlongs t l` has l's pairs live, if l's compare values
are distinct. -/
theorem mrg_newKlongs_liveAt_iff (b : Bool) (t : Time) (l : List (Nat × NodeId))
    (hnd : (l.map Prod.fst).Nodup) (c : Nat) (z : NodeId) :
    (c, z) ∈ (⟨b, newKlongs t l⟩ : KNode).liveAt t ↔ (c, z) ∈ l := by
  constructor
  · exact liveAt_newKlongs_mem b t t l c z
  · intro h
    rw [KNode.liveAt_of_times _ t (newKlongs_times t l)]
    apply bk_mem_of_lookup
    rw [KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup l c hnd]
    exact lookup_of_mem_nodup _ hnd c z h

/-- In a list sorted by compare value, cut at h with g the first compare value
of the rest: a search below g in the first part finds what it finds in the
list; at or above g, in the rest with its first klong renamed (an inner node's
empty key), what it finds in the list. -/
theorem mrg_split_search (E : List (Nat × NodeId)) (hs : E.Pairwise (fun a b => a.1 < b.1)) (h : Nat)
    (g : Nat) (yg : NodeId) (hg : (E.drop h).head? = some (g, yg)) (inner : Bool)
    (M F S : KNode) (t : Time) (hMt : ∀ s, Klong.time s ∈ M.ks → s ≤ t)
    (hFt : ∀ s, Klong.time s ∈ F.ks → s ≤ t) (hSt : ∀ s, Klong.time s ∈ S.ks → s ≤ t)
    (hM : ∀ c z, (c, z) ∈ M.liveAt t ↔ (c, z) ∈ E)
    (hF : ∀ c z, (c, z) ∈ F.liveAt t ↔ (c, z) ∈ E.take h)
    (hS : ∀ c z, (c, z) ∈ S.liveAt t ↔ (c, z) ∈ (if inner then renameHead 0 (E.drop h) else E.drop h)) :
    (∀ c : Nat, c < g → (F.searchLte t c).map (·.y) = (M.searchLte t c).map (·.y)) ∧
    (∀ c : Nat, g ≤ c → (S.searchLte t c).map (·.y) = (M.searchLte t c).map (·.y)) ∧
    (∀ c : Nat, c < g → (F.liveAt t).lookup c = (M.liveAt t).lookup c) ∧
    (inner = false → ∀ c : Nat, g ≤ c → (S.liveAt t).lookup c = (M.liveAt t).lookup c) := by
  obtain ⟨tl, htl⟩ : ∃ tl, E.drop h = (g, yg) :: tl := by
    cases hd : E.drop h with
    | nil => rw [hd] at hg; cases hg
    | cons a rest => rw [hd] at hg; simp only [List.head?_cons, Option.some.injEq] at hg; exact ⟨rest, by rw [hg]⟩
  have hsplit : (E.take h ++ E.drop h).Pairwise (fun a b => a.1 < b.1) := by rw [List.take_append_drop]; exact hs
  have hcross : ∀ a ∈ E.take h, ∀ b ∈ E.drop h, a.1 < b.1 := (List.pairwise_append.mp hsplit).2.2
  have hdrop_s : (E.drop h).Pairwise (fun a b => a.1 < b.1) := (List.pairwise_append.mp hsplit).2.1
  rw [htl] at hdrop_s hcross
  have hgtl : ∀ b ∈ tl, g < b.1 := (List.pairwise_cons.mp hdrop_s).1
  have hfirst_lt : ∀ a ∈ E.take h, a.1 < g := fun a ha => hcross a ha (g, yg) List.mem_cons_self
  have hmemE : ∀ q, q ∈ E ↔ q ∈ E.take h ∨ q ∈ (g, yg) :: tl := by
    intro q
    rw [← htl]
    constructor
    · intro hq
      rw [← List.take_append_drop h E] at hq
      exact List.mem_append.mp hq
    · rintro (hq | hq)
      · exact List.mem_of_mem_take hq
      · exact List.mem_of_mem_drop hq
  have hSmem : ∀ c z, (c, z) ∈ S.liveAt t ↔ (c = (if inner then 0 else g) ∧ z = yg) ∨ (c, z) ∈ tl := by
    intro c z
    rw [hS c z, htl]
    cases inner <;> simp [renameHead]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mrg_searchLte_cases M t c with ⟨hn, hall⟩ | ⟨fd, hfd, hfm, hfle, hfmax⟩
    · rw [hn, mrg_searchLte_none F t hFt c (fun k y hk =>
        hall k y ((hM k y).mpr (List.mem_of_mem_take ((hF k y).mp hk))))]
    · rw [hfd]
      have hfE := (hM _ _).mp hfm
      have hfF : (fd.c, fd.y) ∈ E.take h := by
        rcases (hmemE _).mp hfE with h1 | h1
        · exact h1
        · exfalso
          rcases List.mem_cons.mp h1 with h2 | h2
          · simp only [Prod.mk.injEq] at h2; omega
          · have := hgtl _ h2; simp only at this; omega
      exact mrg_searchLte_y F t hFt c fd.c fd.y ((hF _ _).mpr hfF) hfle
        (fun k' y' hk' hkc => hfmax k' y' ((hM _ _).mpr (List.mem_of_mem_take ((hF _ _).mp hk'))) hkc)
  · intro c hc
    have hgE : (g, yg) ∈ E := (hmemE _).mpr (Or.inr List.mem_cons_self)
    rcases mrg_searchLte_cases M t c with ⟨_, hall⟩ | ⟨fd, hfd, hfm, hfle, hfmax⟩
    · have := hall g yg ((hM _ _).mpr hgE); omega
    · rw [hfd]
      have hfE := (hM _ _).mp hfm
      have hge : g ≤ fd.c := hfmax g yg ((hM _ _).mpr hgE) hc
      rcases (hmemE _).mp hfE with h1 | h1
      · have := hfirst_lt _ h1; simp only at this; omega
      · rcases List.mem_cons.mp h1 with h2 | h2
        · -- the head of the rest
          simp only [Prod.mk.injEq] at h2
          obtain ⟨h2c, h2y⟩ := h2
          show _ = some fd.y
          rw [h2y]
          apply mrg_searchLte_y S t hSt c (if inner then 0 else g) yg ((hSmem _ _).mpr (Or.inl ⟨rfl, rfl⟩))
            (by cases inner <;> simp <;> omega)
          intro k' y' hk' hkc
          rcases (hSmem k' y').mp hk' with ⟨hk1, _⟩ | hk1
          · rw [hk1]; exact Nat.le_refl _
          · have h3 := hfmax k' y' ((hM _ _).mpr ((hmemE _).mpr (Or.inr (List.mem_cons_of_mem _ hk1)))) hkc
            have h4 := hgtl _ hk1
            simp only at h4
            omega
        · apply mrg_searchLte_y S t hSt c fd.c fd.y ((hSmem _ _).mpr (Or.inr h2)) hfle
          intro k' y' hk' hkc
          rcases (hSmem k' y').mp hk' with ⟨hk1, _⟩ | hk1
          · rw [hk1]; cases inner <;> simp <;> omega
          · exact hfmax k' y' ((hM _ _).mpr ((hmemE _).mpr (Or.inr (List.mem_cons_of_mem _ hk1)))) hkc
  · intro c hc
    apply mrg_lookup_eq_of_iff F M t hFt hMt c
    intro z
    rw [hF c z, hM c z]
    constructor
    · exact List.mem_of_mem_take
    · intro hz
      rcases (hmemE _).mp hz with h1 | h1
      · exact h1
      · exfalso
        rcases List.mem_cons.mp h1 with h2 | h2
        · simp only [Prod.mk.injEq] at h2; omega
        · have := hgtl _ h2; simp only at this; omega
  · intro hin c hc
    apply mrg_lookup_eq_of_iff S M t hSt hMt c
    intro z
    rw [hSmem c z, hM c z, hin]
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro (⟨h1, h2⟩ | h1)
      · exact (hmemE _).mpr (Or.inr (by rw [h1, h2]; exact List.mem_cons_self))
      · exact (hmemE _).mpr (Or.inr (List.mem_cons_of_mem _ h1))
    · intro hz
      rcases (hmemE _).mp hz with h1 | h1
      · have := hfirst_lt _ h1; simp only at this; omega
      · rcases List.mem_cons.mp h1 with h2 | h2
        · simp only [Prod.mk.injEq] at h2; exact Or.inl h2
        · exact Or.inr h2

/-- The parent after a merge into two nodes m1 and m2, from the parent after a
merge into one node vM: what found vM finds m1 below g, m2 from g on. -/
theorem mrg_parent_search_two (pn pnm pn2 : KNode) (t : Time) (cL cR g : Nat) (vM m1 m2 : NodeId)
    (h2t : ∀ s, Klong.time s ∈ pn2.ks → s ≤ t)
    (hgL : cL < g) (hgU : ∀ k z, (k, z) ∈ pn.liveAt t → cR < k → g < k)
    (hadj : ∀ k z, (k, z) ∈ pn.liveAt t → k ≤ cL ∨ cR ≤ k) (hlt : cL < cR)
    (hvM : ∀ k, (k, vM) ∉ pn.liveAt t)
    (hm : ∀ c z, (c, z) ∈ pnm.liveAt t ↔ (c = cL ∧ z = vM) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (h2 : ∀ c z, (c, z) ∈ pn2.liveAt t ↔ (c = g ∧ z = m2) ∨ (c ≠ g ∧ c = cL ∧ z = m1) ∨
      (c ≠ g ∧ c ≠ cL ∧ c ≠ cR ∧ (c, z) ∈ pn.liveAt t)) :
    ∀ c : Nat, (pn2.searchLte t c).map (·.y) =
      (pnm.searchLte t c).map (fun fd => if fd.y = vM then (if c < g then m1 else m2) else fd.y) := by
  intro c
  -- g is no compare value of pn's but cR
  have hgk : ∀ k z, (k, z) ∈ pn.liveAt t → k ≠ cR → k ≠ g := by
    intro k z hk hkR hkg
    rcases hadj k z hk with h | h
    · omega
    · have := hgU k z hk (by omega); omega
  rcases mrg_searchLte_cases pnm t c with ⟨hn, hall⟩ | ⟨fd, hfd, hfm, hfle, hfmax⟩
  · rw [hn]
    have hcL : c < cL := hall cL vM ((hm _ _).mpr (Or.inl ⟨rfl, rfl⟩))
    rw [mrg_searchLte_none pn2 t h2t c (by
      intro k y hk
      rcases (h2 k y).mp hk with ⟨hk1, _⟩ | ⟨_, hk1, _⟩ | ⟨_, h3, h4, h5⟩
      · omega
      · omega
      · exact hall k y ((hm _ _).mpr (Or.inr ⟨h5, h3, h4⟩)))]
    rfl
  · rw [hfd]
    simp only [Option.map_some]
    rcases (hm _ _).mp hfm with ⟨hc1, hy1⟩ | ⟨hfp, hc1, hc2⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hy1)]
      by_cases hcg : c < g
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hcg)]
        apply mrg_searchLte_y pn2 t h2t c cL m1 ((h2 _ _).mpr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)))
          (by omega)
        intro k' y' hk' hkc
        rcases (h2 k' y').mp hk' with ⟨hk1, _⟩ | ⟨_, hk1, _⟩ | ⟨_, h3, h4, h5⟩
        · omega
        · omega
        · have := hfmax k' y' ((hm _ _).mpr (Or.inr ⟨h5, h3, h4⟩)) hkc; omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hcg)]
        apply mrg_searchLte_y pn2 t h2t c g m2 ((h2 _ _).mpr (Or.inl ⟨rfl, rfl⟩)) (by omega)
        intro k' y' hk' hkc
        rcases (h2 k' y').mp hk' with ⟨hk1, _⟩ | ⟨_, hk1, _⟩ | ⟨_, h3, h4, h5⟩
        · omega
        · omega
        · have := hfmax k' y' ((hm _ _).mpr (Or.inr ⟨h5, h3, h4⟩)) hkc; omega
    · have hyv : fd.y ≠ vM := fun h => hvM fd.c (h ▸ hfp)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hyv)]
      apply mrg_searchLte_y pn2 t h2t c fd.c fd.y
        ((h2 _ _).mpr (Or.inr (Or.inr ⟨hgk _ _ hfp hc2, hc1, hc2, hfp⟩))) hfle
      intro k' y' hk' hkc
      rcases (h2 k' y').mp hk' with ⟨hk1, _⟩ | ⟨_, hk1, _⟩ | ⟨_, h3, h4, h5⟩
      · -- g ≤ c: fd.c is above cL, so above cR
        have hcL := hfmax cL vM ((hm _ _).mpr (Or.inl ⟨rfl, rfl⟩)) (by omega)
        rcases hadj fd.c fd.y hfp with h | h
        · omega
        · have := hgU fd.c fd.y hfp (by omega); omega
      · exact hfmax cL vM ((hm _ _).mpr (Or.inl ⟨rfl, rfl⟩)) (by omega) |> fun h => by omega
      · exact hfmax k' y' ((hm _ _).mpr (Or.inr ⟨h5, h3, h4⟩)) hkc

/-- The parent after a merge into one node vM, as a node: its live klongs but
cR's, cL's naming vM. -/
def mrgPnm (pn : KNode) (t : Time) (cL cR : Nat) (vM : NodeId) : KNode :=
  ⟨false, newKlongs t (((pn.liveAt t).filter (fun q => q.1 != cR)).map
    (fun q => if q.1 = cL then (cL, vM) else q))⟩

theorem mrgPnm_liveAt (pn : KNode) (t : Time) (cL cR : Nat) (vM : NodeId)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t) (hc : cL ≠ cR) (hL : ∃ y, (cL, y) ∈ pn.liveAt t) :
    ∀ c z, (c, z) ∈ (mrgPnm pn t cL cR vM).liveAt t ↔
      (c = cL ∧ z = vM) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR) := by
  have hnd0 : ((pn.liveAt t).map Prod.fst).Nodup := by
    rw [KNode.liveAt_of_times pn t hpt]; exact KNode.live_keys_nodup pn
  have hkeys : (((pn.liveAt t).filter (fun q => q.1 != cR)).map
      (fun q => if q.1 = cL then (cL, vM) else q)).map Prod.fst =
      ((pn.liveAt t).filter (fun q => q.1 != cR)).map Prod.fst := by
    rw [List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply]
    split
    · rename_i h; exact h.symm
    · rfl
  have hnd : ((((pn.liveAt t).filter (fun q => q.1 != cR)).map
      (fun q => if q.1 = cL then (cL, vM) else q)).map Prod.fst).Nodup := by
    rw [hkeys]
    exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hnd0
  intro c z
  unfold mrgPnm
  rw [mrg_newKlongs_liveAt_iff false t _ hnd c z]
  simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨q, ⟨hq, hqR⟩, he⟩
    split at he
    · rename_i h1
      simp only [Prod.mk.injEq] at he
      exact Or.inl ⟨he.1.symm, he.2.symm⟩
    · rename_i h1
      subst he
      exact Or.inr ⟨hq, h1, hqR⟩
  · rintro (⟨hc1, hz1⟩ | ⟨h1, h2, h3⟩)
    · obtain ⟨y, hy⟩ := hL
      exact ⟨(cL, y), ⟨hy, hc⟩, by simp [hc1, hz1]⟩
    · exact ⟨(c, z), ⟨h1, h3⟩, by simp [h2]⟩

/-- The merged list is sorted by compare value, the siblings' compare values in
their ranges. -/
theorem mrg_mergeList_sorted (ln rn : KNode) (t : Time) (inner : Bool) (cR : Nat)
    (hlt' : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt' : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hlrange : ∀ c z, (c, z) ∈ ln.liveAt t → c < cR)
    (hrrange : ∀ c z, (c, z) ∈ rn.liveAt t → (inner = true → c = 0 ∨ cR < c) ∧
      (inner = false → cR ≤ c))
    (hrhead : inner = true → ∃ y0 tl, rn.live = (0, y0) :: tl) :
    (mergeList inner cR ln.live rn.live).Pairwise (fun a b => a.1 < b.1) := by
  rw [KNode.liveAt_of_times ln t hlt'] at hlrange
  rw [KNode.liveAt_of_times rn t hrt'] at hrrange
  unfold mergeList
  rw [List.pairwise_append]
  cases inner with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨ln.live_order, rn.live_order, ?_⟩
    intro a ha b hb
    have h1 := hlrange a.1 a.2 ha
    have h2 := (hrrange b.1 b.2 hb).2 rfl
    omega
  | true =>
    simp only [↓reduceIte]
    obtain ⟨y0, tl, htl⟩ := hrhead rfl
    have hro := rn.live_order
    rw [htl] at hro
    have hnd := KNode.live_keys_nodup rn
    rw [htl] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have htlgt : ∀ b ∈ tl, cR < b.1 := by
      intro b hb
      have := (hrrange b.1 b.2 (by rw [htl]; exact List.mem_cons_of_mem _ hb)).1 rfl
      rcases this with h0 | h0
      · exact absurd ⟨b, hb, h0⟩ hnd.1
      · exact h0
    rw [htl]
    simp only [renameHead]
    refine ⟨ln.live_order, List.pairwise_cons.mpr ⟨fun b hb => htlgt b hb, (List.pairwise_cons.mp hro).2⟩, ?_⟩
    intro a ha b hb
    have h1 := hlrange a.1 a.2 ha
    rcases List.mem_cons.mp hb with hb | hb
    · rw [hb]; exact h1
    · have := htlgt b hb; omega

/-- The tree after a merge into two nodes reads every key as before: as after a
merge into one node at an id vM that is not there, then a split of vM at g. -/
theorem getFromR_mergeTwo (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r p l rr m1 m2 vM : NodeId)
    (pn ln rn pn2 mn1 mn2 : KNode) (inner : Bool) (cL cR h g : Nat) (yg : NodeId)
    (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hlt : cL < cR)
    (hadj : ∀ c z, (c, z) ∈ pn.liveAt t → c ≤ cL ∨ cR ≤ c)
    (hln : N l = some ln) (hrn : N rr = some rn) (hll : ln.leaf = !inner) (hrl : rn.leaf = !inner)
    (hlrange : ∀ c z, (c, z) ∈ ln.liveAt t → c < cR)
    (hrrange : ∀ c z, (c, z) ∈ rn.liveAt t → (inner = true → c = 0 ∨ cR < c) ∧
      (inner = false → cR ≤ c))
    (hrhead : inner = true → ∃ y0 tl, rn.live = (0, y0) :: tl)
    (hgsplit : ((mergeList inner cR ln.live rn.live).drop h).head? = some (g, yg))
    (hgL : cL < g) (hgU : ∀ k z, (k, z) ∈ pn.liveAt t → cR < k → g < k)
    (hN2m1 : N2 m1 = some mn1) (hm1l : mn1.leaf = !inner)
    (hmn1 : ∀ c z, (c, z) ∈ mn1.liveAt t ↔ (c, z) ∈ (mergeList inner cR ln.live rn.live).take h)
    (hN2m2 : N2 m2 = some mn2) (hm2l : mn2.leaf = !inner)
    (hmn2 : ∀ c z, (c, z) ∈ mn2.liveAt t ↔ (c, z) ∈ (if inner then
      renameHead 0 ((mergeList inner cR ln.live rn.live).drop h)
      else (mergeList inner cR ln.live rn.live).drop h))
    (hN2p : N2 p = some pn2) (hpl2 : pn2.leaf = false)
    (hpn2 : ∀ c z, (c, z) ∈ pn2.liveAt t ↔ (c = g ∧ z = m2) ∨ (c ≠ g ∧ c = cL ∧ z = m1) ∨
      (c ≠ g ∧ c ≠ cL ∧ c ≠ cR ∧ (c, z) ∈ pn.liveAt t))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → y ≠ m2 → N2 y = N y)
    (hfresh : ∀ z, (z = m1 ∨ z = m2 ∨ z = vM) →
      N z = none ∧ ∀ u c, TReach N t r u → ¬ TLink N t u c z)
    (h1v : m1 ≠ vM) (h2v : m2 ≠ vM)
    (htimes : ∀ x xn, N x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ t)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hm1t : ∀ s, Klong.time s ∈ mn1.ks → s ≤ t) (hm2t : ∀ s, Klong.time s ∈ mn2.ks → s ≤ t)
    (hp2t : ∀ s, Klong.time s ∈ pn2.ks → s ≤ t)
    (hm1wf : klongsWf mn1.ks = true) (hm2wf : klongsWf mn2.ks = true) :
    ∀ key, getFromR N2 V t fuel key r = getFromR N V t fuel key r := by
  have hpt := htimes p pn hpn
  have hlt' := htimes l ln hln
  have hrt' := htimes rr rn hrn
  have hEs := mrg_mergeList_sorted ln rn t inner cR hlt' hrt' hlrange hrrange hrhead
  generalize hE : mergeList inner cR ln.live rn.live = E at hEs hgsplit hmn1 hmn2
  have hEnd : (E.map Prod.fst).Nodup := List.pairwise_map.mpr (hEs.imp (by intro a b hab; omega))
  have hpl_link : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hpr_link : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hpl_link
  have hrR : TReach N t r rr := TReach.link hp hpr_link
  have hlp : l ≠ p := fun h => hT.no_self_link p cL hp (by rw [h] at hpl_link; exact hpl_link)
  have hrp : rr ≠ p := fun h => hT.no_self_link p cR hp (by rw [h] at hpr_link; exact hpr_link)
  obtain ⟨hvN, hvF⟩ := hfresh vM (Or.inr (Or.inr rfl))
  obtain ⟨hm1N, hm1F⟩ := hfresh m1 (Or.inl rfl)
  obtain ⟨hm2N, hm2F⟩ := hfresh m2 (Or.inr (Or.inl rfl))
  have hvR : ¬ TReach N t r vM := not_reach_fresh N t r vM hT hvN hvF
  have hm1R : ¬ TReach N t r m1 := not_reach_fresh N t r m1 hT hm1N hm1F
  have hm2R : ¬ TReach N t r m2 := not_reach_fresh N t r m2 hT hm2N hm2F
  have hpv : p ≠ vM := fun h => hvR (h ▸ hp)
  -- the merged list's pairs are links of l or rr
  have hEtarget : ∀ c z, (c, z) ∈ E → TReach N t r z ∧ z ≠ l ∧ z ≠ rr := by
    intro c z hm
    rw [← hE] at hm
    rcases mem_mergeList inner cR ln.live rn.live c z hm with h1 | h1 | ⟨c0, h1, _⟩
    · have hk : TLink N t l c z := ⟨ln, hln, by rw [KNode.liveAt_of_times ln t hlt']; exact h1⟩
      refine ⟨TReach.link hlR hk, fun he => ?_, fun he => ?_⟩
      · rw [he] at hk; exact hT.no_self_link l c hlR hk
      · rw [he] at hk; exact hlp (hT.oneLink l c p cR rr hlR hp hk hpr_link).1
    · have hk : TLink N t rr c z :=
        ⟨rn, hrn, by rw [KNode.liveAt_of_times rn t hrt']; exact List.mem_of_mem_tail h1⟩
      refine ⟨TReach.link hrR hk, fun he => ?_, fun he => ?_⟩
      · rw [he] at hk; exact hrp (hT.oneLink rr c p cL l hrR hp hk hpl_link).1
      · rw [he] at hk; exact hT.no_self_link rr c hrR hk
    · have hk : TLink N t rr c0 z :=
        ⟨rn, hrn, by rw [KNode.liveAt_of_times rn t hrt']; exact List.mem_of_mem_head? h1⟩
      refine ⟨TReach.link hrR hk, fun he => ?_, fun he => ?_⟩
      · rw [he] at hk; exact hrp (hT.oneLink rr c0 p cL l hrR hp hk hpl_link).1
      · rw [he] at hk; exact hT.no_self_link rr c0 hrR hk
  -- the tree after a merge into one node at vM
  have hM : ∀ c z, (c, z) ∈ (⟨!inner, newKlongs t E⟩ : KNode).liveAt t ↔ (c, z) ∈ E :=
    mrg_newKlongs_liveAt_iff _ t E hEnd
  have hpnm := mrgPnm_liveAt pn t cL cR vM hpt (by omega) ⟨l, hl⟩
  let Nm : NodeId → Option KNode := fun x =>
    if x = p then some (mrgPnm pn t cL cR vM) else if x = vM then some ⟨!inner, newKlongs t E⟩
    else if x = l ∨ x = rr then N2 x else N x
  have hNmp : Nm p = some (mrgPnm pn t cL cR vM) := by simp [Nm]
  have hNmv : Nm vM = some ⟨!inner, newKlongs t E⟩ := by simp [Nm, Ne.symm hpv]
  have hNmo : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ vM → Nm y = N y := by
    intro y h1 h2 h3 h4; simp [Nm, h1, h2, h3, h4]
  have hA := getFromR_mergeOne N Nm V t fuel r p l rr vM pn ln rn (mrgPnm pn t cL cR vM)
    ⟨!inner, newKlongs t E⟩ inner cL cR
    hT hp hpn hpl hl hrr hlt hadj hln hrn hll hrl hlrange hrrange hrhead hNmv rfl
    (by rw [hE]; exact hM) hNmp rfl hpnm hNmo hvR htimes (newKlongs_times t E) (newKlongs_times t _)
    hwf (klongsWf_newKlongs t E)
  -- what the tree with vM reaches
  have hRm : ∀ x, ReachS Nm t r x → (TReach N t r x ∧ x ≠ l ∧ x ≠ rr) ∨ x = vM := by
    intro x hx
    induction hx with
    | root =>
      left
      refine ⟨TReach.root, fun h => ?_, fun h => ?_⟩
      · exact hT.rootFree p cL hp (by rw [h]; exact hpl_link)
      · exact hT.rootFree p cR hp (by rw [h]; exact hpr_link)
    | step x n c z _ hn hc ih =>
      rcases ih with ⟨hxR, hxl, hxr⟩ | hxv
      · by_cases hxp : x = p
        · rw [hxp, hNmp] at hn
          simp only [Option.some.injEq] at hn
          subst hn
          rcases (hpnm c z).mp hc with ⟨_, hz⟩ | ⟨hm, hc1, hc2⟩
          · exact Or.inr hz
          · have hk : TLink N t p c z := ⟨pn, hpn, hm⟩
            refine Or.inl ⟨TReach.link hp hk, fun he => ?_, fun he => ?_⟩
            · rw [he] at hk; exact hc1 (hT.oneLink p c p cL l hp hp hk hpl_link).2
            · rw [he] at hk; exact hc2 (hT.oneLink p c p cR rr hp hp hk hpr_link).2
        · have hxv : x ≠ vM := fun h => hvR (h ▸ hxR)
          rw [hNmo x hxp hxl hxr hxv] at hn
          have hk : TLink N t x c z := ⟨n, hn, hc⟩
          refine Or.inl ⟨TReach.link hxR hk, fun he => ?_, fun he => ?_⟩
          · rw [he] at hk; exact hxp (hT.oneLink x c p cL l hxR hp hk hpl_link).1
          · rw [he] at hk; exact hxp (hT.oneLink x c p cR rr hxR hp hk hpr_link).1
      · rw [hxv, hNmv] at hn
        simp only [Option.some.injEq] at hn
        subst hn
        exact Or.inl (hEtarget c z ((hM c z).mp hc))
  have hwfm : ∀ x xn, ReachS Nm t r x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxp : x = p
    · rw [hxp, hNmp] at hn; simp only [Option.some.injEq] at hn; subst hn
      exact klongsWf_newKlongs t _
    · by_cases hxv : x = vM
      · rw [hxv, hNmv] at hn; simp only [Option.some.injEq] at hn; subst hn
        exact klongsWf_newKlongs t E
      · rcases hRm x hx with ⟨_, hxl, hxr⟩ | hxv'
        · rw [hNmo x hxp hxl hxr hxv] at hn; exact hwf x xn hn
        · exact absurd hxv' hxv
  -- no link of the tree with vM to vM but p's, none to m1 or m2
  have hlinks : ∀ x xn c z, ReachS Nm t r x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      (x ≠ p → z ≠ vM) ∧ z ≠ m1 ∧ z ≠ m2 := by
    intro x xn c z hx hn hc
    by_cases hxp : x = p
    · rw [hxp, hNmp] at hn; simp only [Option.some.injEq] at hn; subst hn
      refine ⟨fun h => absurd hxp h, ?_⟩
      rcases (hpnm c z).mp hc with ⟨_, hz⟩ | ⟨hm, _, _⟩
      · rw [hz]; exact ⟨Ne.symm h1v, Ne.symm h2v⟩
      · have hk : TLink N t p c z := ⟨pn, hpn, hm⟩
        exact ⟨fun he => hm1F p c hp (he ▸ hk), fun he => hm2F p c hp (he ▸ hk)⟩
    · rcases hRm x hx with ⟨hxR, hxl, hxr⟩ | hxv
      · have hxv : x ≠ vM := fun h => hvR (h ▸ hxR)
        rw [hNmo x hxp hxl hxr hxv] at hn
        have hk : TLink N t x c z := ⟨xn, hn, hc⟩
        exact ⟨fun _ he => hvF x c hxR (he ▸ hk), fun he => hm1F x c hxR (he ▸ hk),
          fun he => hm2F x c hxR (he ▸ hk)⟩
      · rw [hxv, hNmv] at hn; simp only [Option.some.injEq] at hn; subst hn
        obtain ⟨hzR, _, _⟩ := hEtarget c z ((hM c z).mp hc)
        exact ⟨fun _ he => hvR (he ▸ hzR), fun he => hm1R (he ▸ hzR), fun he => hm2R (he ▸ hzR)⟩
  have hsame : ∀ x, x ≠ vM → x ≠ p → x ≠ m1 → x ≠ m2 → N2 x = Nm x := by
    intro x h1 h2 h3 h4
    by_cases hlr' : x = l ∨ x = rr
    · simp [Nm, h2, h1, hlr']
    · have hxl : x ≠ l := fun h => hlr' (Or.inl h)
      have hxr : x ≠ rr := fun h => hlr' (Or.inr h)
      rw [hNmo x h2 hxl hxr h1, hother x h2 hxl hxr h3 h4]
  have hvL : ∀ k, (k, vM) ∉ pn.liveAt t := fun k hk => hvF p k hp ⟨pn, hpn, hk⟩
  have hqsearch := mrg_parent_search_two pn (mrgPnm pn t cL cR vM) pn2 t cL cR g vM m1 m2 hp2t hgL hgU
    hadj hlt hvL hpnm hpn2
  have hsp := mrg_split_search E hEs h g yg hgsplit inner ⟨!inner, newKlongs t E⟩ mn1 mn2 t
    (newKlongs_times t E) hm1t hm2t hM hmn1 hmn2
  -- p and vM are reached in the tree with vM
  have hpRm : TReach Nm t r p := by
    obtain ⟨a, ha⟩ := hp.pathLen
    apply tReach_of_agree_short N Nm t r a p ha
    intro x k hk hka
    have hxp : x ≠ p := fun he => by
      rw [he] at hk; have := PathLen.depth_unique hT a p k ha hk; omega
    have hxl : x ≠ l := fun he => by
      rw [he] at hk; have := PathLen.depth_unique hT (a + 1) l k (PathLen.link ha hpl_link) hk; omega
    have hxr : x ≠ rr := fun he => by
      rw [he] at hk; have := PathLen.depth_unique hT (a + 1) rr k (PathLen.link ha hpr_link) hk; omega
    have hxv : x ≠ vM := fun he => hvR (he ▸ hk.reach)
    exact hNmo x hxp hxl hxr hxv
  have hvRm : ReachS Nm t r vM :=
    ReachS.step p _ cL vM (tReach_reachS _ t r p hpRm) hNmp ((hpnm cL vM).mpr (Or.inl ⟨rfl, rfl⟩))
  have hget : ∀ c (x : NodeId), ReachS Nm t r x → x ≠ vM → x ≠ m1 → x ≠ m2 →
      getEqR N2 t c fuel x = getEqR Nm t c fuel x := by
    intro c x hx h1 h2 h3
    cases inner with
    | false =>
      exact getEqR_split Nm N2 t r vM p m1 m2 (mrgPnm pn t cL cR vM) pn2 ⟨true, newKlongs t E⟩ mn1 mn2 g
        hNmp rfl hN2p hpl2 hqsearch hNmv rfl hN2m1 hm1l hN2m2 hm2l
        (fun c hc => by
          rw [mrg_searchEq_y mn1 t hm1wf c, mrg_searchEq_y _ t (klongsWf_newKlongs t E) c]
          exact hsp.2.2.1 c hc)
        (fun c hc => by
          rw [mrg_searchEq_y mn2 t hm2wf c, mrg_searchEq_y _ t (klongsWf_newKlongs t E) c]
          exact hsp.2.2.2 rfl c hc)
        hsame (fun x xn c z hx hxp hn hz => (hlinks x xn c z hx hn hz).1 hxp)
        (fun x xn c z hx hn hz => ⟨fun _ => (hlinks x xn c z hx hn hz).2.1, (hlinks x xn c z hx hn hz).2.2⟩)
        c fuel x hx h1 h2 h3
    | true =>
      exact (getEqR_split_inner Nm N2 t r vM p m1 m2 (mrgPnm pn t cL cR vM) pn2 ⟨false, newKlongs t E⟩
        mn1 mn2 g hNmp rfl hN2p hpl2 hqsearch hNmv rfl hvRm hN2m1 hm1l hN2m2 hm2l hsp.1 hsp.2.1
        hsame (fun x xn c z hx hxp hn hz => (hlinks x xn c z hx hn hz).1 hxp)
        (fun x xn c z hx hn hz => ⟨(hlinks x xn c z hx hn hz).2.1, (hlinks x xn c z hx hn hz).2.2⟩)
        (Ne.symm hpv) c fuel).1 x hx h1 h2 h3
  have hB := getFromR_split Nm N2 V t fuel r vM p m1 m2 hwfm hget hsame (by rw [hN2p, hNmp]; rfl)
    (fun x xn c z hx hxp hn hz => (hlinks x xn c z hx hn hz).1 hxp)
    (fun xn c z hn _ hleaf => by rw [hNmp] at hn; simp only [Option.some.injEq] at hn; subst hn; cases hleaf)
    (fun x xn c z hx hn hz => ⟨fun _ => (hlinks x xn c z hx hn hz).2.1, (hlinks x xn c z hx hn hz).2.2⟩)
  intro key
  have hrv : r ≠ vM := fun h => hvR (h ▸ TReach.root)
  have hr1 : r ≠ m1 := fun h => hm1R (h ▸ TReach.root)
  have hr2 : r ≠ m2 := fun h => hm2R (h ▸ TReach.root)
  rw [hB key r ReachS.root hrv hr1 hr2, hA key]

end SIS.Tree
