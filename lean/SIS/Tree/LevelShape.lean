import SIS.Tree.ChainShape
import SIS.Tree.GetMergeLevel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The shapes of the nodes that the split of a full node with a last version
given makes or changes (bergdb 024-12, for prover putinv's take-back through a
merge's full parent and a delete's full leaf): `writerWP_appendKlongs_chainShape`
one level up, for `handleFull` of X (D + 1) with the last version `last` and
nothing put. -/

set_option maxHeartbeats 3200000 in
/-- After `handleFull` of X (D + 1) with the last version `last` (a time klong
and key klongs of distinct compare values), with the cascade above it, every
node with an id from the next id on or on the chain has a cascade node's shape
(`ShapePost` from D + 1 with nothing put): on the premises of
`writerWP_appendKlongs_chainShape` for X s .. X D, and for X (D + 1) those of
`writerWP_handleFull_lastVF2` that concern the writer's nodes, with `LastOrd`. -/
theorem writerWP_handleFull_lastShape (c : Ctx)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (hsD : s ≤ D)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (htimes : ∀ i, s ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D + 1 → s ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (last : KNode) (compact : Bool)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length)
    (hrangeL : c.p.splitAbove < last.size → (Nn D).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'')
    (hLO : LastOrd c K Nn D last)
    (w : W) (hpath : w.path = path0)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next)
    (hfr : ∀ z, w.next ≤ z → w.nodes.lookup z = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last compact)
      c w (fun _ w' => ShapePost c X K Nn s (D + 1) [] w w') := by
  have hchainS := writerWP_appendKlongs_chainShape c path0 s D X K Nn
    (fun i h1 h2 => hX i h1 (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen hord
    (fun i h1 h2 => htimes i h1 (by omega)) htop
    (fun i i' h1 h2 h3 h4 => hdist i i' h1 (by omega) h3 (by omega)) (D - s) (by omega)
  have hsD' : s + (D - s) = D := by omega
  rw [hsD'] at hchainS
  obtain ⟨pairs, hks, hnd⟩ := hpairs
  have hlt : ∀ t, Klong.time t ∈ last.ks → t ≤ c.i := by rw [hks]; exact newKlongs_times c.i pairs
  have hlsh : ∀ (lf : Bool) (P : NodeId → Prop), ShadowOK c.i ⟨lf, last.ks⟩ P := by
    intro lf P; rw [hks]; exact shadowOK_newKlongs c.i lf pairs hnd P
  obtain ⟨hlk, hxn⟩ := hS2 (D + 1) (by omega) (Nat.le_refl _)
  obtain ⟨hlq, hqn⟩ := hS2 D hsD (by omega)
  have hj : s < D + 1 := by omega
  have hpq : (w.path[D]?).map (·.2) = some (X D) := by
    rw [hpath]; exact hX D hsD (by omega)
  have hpk : w.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hpath]; exact hK (D + 1) hj (Nat.le_refl _)
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) hj (Nat.le_refl _); simpa using this
  have hqx : X D ≠ X (D + 1) := by
    intro h; have := hdist _ _ hsD (by omega) (by omega) (Nat.le_refl _) h; omega
  have hqt := htimes D hsD (by omega)
  have hKuniq : ∀ y, (K (D + 1), y) ∈ (Nn D).liveAt c.i → y = X (D + 1) :=
    fun y hy => liveAt_cv_unique _ c.i hqt _ _ _ hy hkl
  have hXne : ∀ i, s ≤ i → i ≤ D → X i ≠ X (D + 1) := by
    intro i h1 h2 he; have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) he; omega
  -- after the parent's step: the cascade's post
  have hfin : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (w2 w3 : W),
      (ins'.map Prod.fst).Nodup →
      (∀ q ∈ ins', ∀ y, (q.1, y) ∈ (Nn D).liveAt c.i →
        q.1 = K (D + 1) ∧ y = X (D + 1) ∧ (Nn (D + 1)).firstTime ≠ some c.i) →
      w.next ≤ w1.next →
      (∀ z, z < w.next → z ≠ X (D + 1) → w1.nodes.lookup z = w.nodes.lookup z) →
      (∀ z zn, w.next ≤ z → z < w1.next → w1.nodes.lookup z = some zn →
        ShadowOK c.i zn (ChainShadow c X Nn s (D + 1) [])) →
      ShapePost c X K Nn s D ins' w1 w2 →
      w3.next = w2.next →
      (∀ z, z ≠ X (D + 1) → w3.nodes.lookup z = w2.nodes.lookup z) →
      (∀ zn, w3.nodes.lookup (X (D + 1)) = some zn →
        CascadeNodeShape c X K Nn s (D + 1) [] (X (D + 1)) zn) →
      ShapePost c X K Nn s (D + 1) [] w w3 := by
    intro w1 ins' w2 w3 hnd' hpar h1next h1low h1new ⟨h2next, h2frame, h2fr, h2sh⟩ h3next h3n h3x
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro z hz hzX
      have hzx := hzX (D + 1) (by omega) (Nat.le_refl _)
      rw [h3n z hzx, h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1low z hz hzx]
    · intro z hz
      have hzx : z ≠ X (D + 1) := by intro h; subst h; omega
      rw [h3n z hzx]; exact h2fr z (by omega)
    · intro z zn h hz
      by_cases hzx : z = X (D + 1)
      · subst hzx; exact h3x zn h
      · rw [h3n z hzx] at h
        by_cases hin : w1.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i
        · exact cascadeShape_lift c X K Nn s D [] ins' z zn hnd' hpar hzx hsD (h2sh z zn h hin)
        · have hzw : w.next ≤ z ∧ z < w1.next := by
            rcases hz with hz | ⟨i, h1, h2, h3⟩
            · refine ⟨hz, ?_⟩
              rcases Nat.lt_or_ge z w1.next with h' | h'
              · exact h'
              · exact absurd (Or.inl h') hin
            · exfalso
              rcases Nat.lt_or_ge i (D + 1) with h' | h'
              · exact hin (Or.inr ⟨i, h1, by omega, h3⟩)
              · have : i = D + 1 := by omega
                subst this; exact hzx h3
          have hz1 : w1.nodes.lookup z = some zn := by
            rw [← h2frame z hzw.2 (fun i h1 h2 he => by
              have := (hS2 i h1 (by omega)).2; rw [← he] at this; omega)]
            exact h
          refine Or.inr (Or.inr (Or.inl ⟨h1new z zn hzw.1 hzw.2 hz1, fun i h1 h2 h3 => ?_⟩))
          exfalso
          have := (hS2 i h1 h2).2; rw [← h3] at this; omega
  -- the time split
  have hTIME : (!compact && decide (last.size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last compact) c w (fun _ w' => ShapePost c X K Nn s (D + 1) [] w w') := by
    intro hcs
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termL _ D (X (D + 1))
        (X D) (Nn (D + 1)) (Nn D) last compact c w hlk hlq hpq hmade hcs) ?_
      rintro _ w' ⟨_, _, _, h'next, _, h'n⟩
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro z _ hz
        rw [h'n, lookup_upsert]
        simp only [hz (D + 1) (by omega) (Nat.le_refl _), ↓reduceIte]
      · intro z hz
        rw [h'next] at hz
        have hzx : z ≠ X (D + 1) := by intro h; subst h; omega
        rw [h'n, lookup_upsert]
        simp only [hzx, ↓reduceIte]
        exact hfr z hz
      · intro z zn h hz
        rw [h'n, lookup_upsert] at h
        by_cases hzx : z = X (D + 1)
        · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine Or.inr (Or.inr (Or.inl ⟨hlsh _ _, fun i h1 h2 h3 => ?_⟩))
          have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) (h3.symm.trans hzx)
          subst this; exact hmade
        · simp only [hzx, ↓reduceIte] at h
          rcases hz with hz | ⟨i, h1, h2, h3⟩
          · rw [hfr z hz] at h; cases h
          · rw [h3, (hS2 i h1 h2).1] at h
            cases h
            exact Or.inl ⟨i, h1, h2, h3, rfl⟩
    · apply writerWP_handleFullWith_time_up_last' D (X (D + 1)) (X D)
        (Nn (D + 1)) (Nn D) (K (D + 1)) last compact c w hlk hlq hmade hcs hpq hpk
      intro w1 h1n _ _ h1path h1next _
      have hfree0 := hfr w.next (Nat.le_refl _)
      have h1lk : ∀ z, z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z := fun z hz => by
        rw [h1n]; exact lookup_append_single_ne _ _ _ _ hz
      refine writerWP_mono (hchainS w1 [(K (D + 1), w.next)] (Or.inl ⟨_, _, rfl⟩)
        (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
      · intro i h1 h2
        have hlt' := (hS2 i h1 (by omega)).2
        exact ⟨by rw [h1lk _ (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
      · intro z hz
        rw [h1next] at hz
        rw [h1lk z (by omega)]; exact hfr z (by omega)
      · intro _ w2 hpost
        have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
          rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
            h1lk _ (by omega), hlk]
        simp only [writerWP_bind]
        rw [writerWP_getNode_known _ _ c w2 hlk2]
        simp only [putNode, writerWP_modify]
        refine hfin w1 [(K (D + 1), w.next)] w2 _ (by simp) ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
        · intro q hq y hy
          simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨rfl, hKuniq y hy, hmade⟩
        · intro z hz _; exact h1lk z (by omega)
        · intro z zn h1 h2 h3
          rw [h1next] at h2
          have hzn : z = w.next := by
            refine Classical.byContradiction (fun hne => ?_)
            rw [h1lk z hne, hfr z h1] at h3; cases h3
          subst hzn
          rw [h1n, lookup_append_single_self _ _ _ hfree0] at h3
          cases h3
          exact hlsh _ _
        · intro z hz
          show (upsert w2.nodes _ _).lookup z = _
          rw [lookup_upsert]; simp only [hz, ↓reduceIte]
        · intro zn h
          change (upsert w2.nodes _ _).lookup _ = some zn at h
          rw [lookup_upsert] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          exact Or.inr (Or.inl ⟨D + 1, by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
  -- the space split
  have hSPACE : c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' => ShapePost c X K Nn s (D + 1) [] w w') := by
    intro hsp
    have h2l := hlen2 hsp
    obtain ⟨hF0, hS0, hscpos0, ⟨ysc, hscmem0⟩, _⟩ :=
      halves_node (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) c.i [] hlt h2l List.Pairwise.nil
    rw [hlastV] at hF0 hS0 hscpos0 hscmem0
    have hF : ShadowOK c.i (halves (Nn (D + 1)).leaf c.i last []).1
        (fun y => ∃ c0, (c0, y) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ∧
          c0 ∈ ([] : List (Nat × NodeId)).map Prod.fst) := hF0
    have hS : ShadowOK c.i (halves (Nn (D + 1)).leaf c.i last []).2.1
        (fun y => ∃ c0, (c0, y) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ∧
          c0 ∈ ([] : List (Nat × NodeId)).map Prod.fst) := hS0
    have hscpos : 0 < (halves (Nn (D + 1)).leaf c.i last []).2.2 := hscpos0
    have hscmem : ((halves (Nn (D + 1)).leaf c.i last []).2.2, ysc) ∈
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live := hscmem0
    have hmono : ∀ zn, ShadowOK c.i zn
        (fun y => ∃ c0, (c0, y) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ∧
          c0 ∈ ([] : List (Nat × NodeId)).map Prod.fst) →
        ShadowOK c.i zn (ChainShadow c X Nn s (D + 1) []) :=
      fun zn h => h.mono (fun y hy => by
        obtain ⟨_, _, hc⟩ := hy
        simp at hc)
    have hKsc : (Nn D).leaf = false → K (D + 1) < (halves (Nn (D + 1)).leaf c.i last []).2.2 :=
      fun hql => lastOrd_div c K Nn D last hLO hql hsp hlastV h2l
    have hscpar : (Nn D).leaf = false → ∀ y,
        ((halves (Nn (D + 1)).leaf c.i last []).2.2, y) ∉ (Nn D).liveAt c.i := by
      intro hql y hy
      have hr := (hrangeL hsp hql _ _ hscmem hscpos).2
      rw [KNode.liveAt_of_times _ c.i hqt] at hy
      have := hr _ _ (by simpa using hy) (hKsc hql)
      omega
    have hfree0 := hfr w.next (Nat.le_refl _)
    have hfree2 := hfr (w.next + 2) (by omega)
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · cases hqlf : (Nn D).leaf with
      | false =>
        apply writerWP_handleFullWith_spaceInPlace_up_last D (X (D + 1)) (X D)
          (Nn (D + 1)) (Nn D) last c w hlk hlq hqlf hmade hsp hpq hxn
        intro w1 h1n _ _ h1path h1next _
        have h1lk : ∀ z, z ≠ X (D + 1) → z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z :=
          fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
        refine writerWP_mono (hchainS w1 [((halves (Nn (D + 1)).leaf c.i last []).2.2, w.next)]
          (Or.inl ⟨_, _, rfl⟩) (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
        · intro i h1 h2
          have hlt' := (hS2 i h1 (by omega)).2
          exact ⟨by rw [h1lk _ (hXne i h1 h2) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
        · intro z hz
          rw [h1next] at hz
          rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
        · intro _ w2 hpost
          refine hfin w1 _ w2 w2 (by simp) ?_ (by omega) ?_ ?_ hpost rfl (fun _ _ => rfl) ?_
          · intro q hq y hy
            simp only [List.mem_singleton] at hq
            subst hq
            exact absurd hy (hscpar hqlf y)
          · intro z hz hzx; exact h1lk z hzx (by omega)
          · intro z zn h1 h2 h3
            rw [h1next] at h2
            have hzx : z ≠ X (D + 1) := by omega
            by_cases hzn : z = w.next
            · subst hzn
              rw [h1n] at h3
              simp only [hzx, ↓reduceIte, Option.some.injEq] at h3
              subst h3
              exact hmono _ hS
            · rw [h1lk z hzx hzn, hfr z h1] at h3; cases h3
          · intro zn h
            rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm), h1n] at h
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            refine Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i h1 h2 h3 => ?_⟩))
            have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) h3.symm
            subst this; exact hmade
      | true =>
        refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_termL D (X (D + 1))
          (X D) (Nn (D + 1)) (Nn D) last (K (D + 1)) [] c w hlk hlq hqx hqlf
          hmade hsp hpq hpk hxn hqn hfree2) ?_
        rintro _ w' ⟨idx, hidx, _, _, _, _, h'next, h'n⟩
        refine ⟨by omega, ?_, ?_, ?_⟩
        · intro z hzl hz
          have h1 : z ≠ X (D + 1) := hz _ (by omega) (Nat.le_refl _)
          have h2 : z ≠ X D := hz _ hsD (by omega)
          have h3 : z ≠ w.next := by omega
          have h4 : z ≠ w.next + 2 := by omega
          rw [h'n]
          simp only [h1, h2, h3, h4, ↓reduceIte]
        · intro z hz
          have h1 : z ≠ X (D + 1) := by omega
          have h2 : z ≠ X D := by omega
          have h3 : z ≠ w.next := by omega
          have h4 : z ≠ w.next + 2 := by omega
          rw [h'n]
          simp only [h1, h2, h3, h4, ↓reduceIte]
          exact hfr z (by omega)
        · intro z zn h hz
          rw [h'n] at h
          by_cases h1 : z = X (D + 1)
          · subst h1
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            refine Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i h1 h2 h3 => ?_⟩))
            have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) h3.symm
            subst this; exact hmade
          · by_cases h2 : z = X D
            · subst h2
              simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact Or.inr (Or.inr (Or.inr ⟨D, hsD, by omega, rfl, Or.inr (Or.inr
                ⟨by omega, K (D + 1), idx, w.next + 2, hidx, rfl, hmade, hqlf⟩)⟩))
            · by_cases h3 : z = w.next
              · subst h3
                simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                subst h
                refine Or.inr (Or.inr (Or.inl ⟨hmono _ hS, fun i h1' h2' h3' => ?_⟩))
                exfalso
                have := (hS2 i h1' h2').2; rw [← h3'] at this; omega
              · by_cases h4 : z = w.next + 2
                · subst h4
                  simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  refine Or.inr (Or.inr (Or.inl ⟨shadowOK_root c.i _ _ _ hscpos _,
                    fun i h1' h2' h3' => ?_⟩))
                  exfalso
                  have := (hS2 i h1' h2').2; rw [← h3'] at this; omega
                · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                  rcases hz with hz | ⟨i, h1', h2', h3'⟩
                  · rw [hfr z hz] at h; cases h
                  · rw [h3', (hS2 i h1' h2').1] at h
                    cases h
                    exact Or.inl ⟨i, h1', h2', h3', rfl⟩
    · cases hqlf : (Nn D).leaf with
      | false =>
        apply writerWP_handleFullWith_space_up_last D (X (D + 1)) (X D)
          (Nn (D + 1)) (Nn D) (K (D + 1)) last c w hlk hlq hqlf hmade hsp hpq hpk
        intro w1 h1n _ _ h1path h1next _
        have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → w1.nodes.lookup z = w.nodes.lookup z :=
          fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
        have hKsc' := hKsc hqlf
        refine writerWP_mono (hchainS w1 _ (Or.inr ⟨_, _, _, _, rfl, Nat.le_of_lt hKsc',
          fun c'' z'' hm hlt' => (hrangeL hsp hqlf _ _ hscmem hscpos).2 c'' z'' hm hlt'⟩)
          (List.pairwise_cons.mpr ⟨fun a' ha' => by
            simp only [List.mem_singleton] at ha'; subst ha'; exact hKsc',
            List.pairwise_singleton _ _⟩)
          (by rw [h1path, hpath]) ?_ ?_) ?_
        · intro i h1 h2
          have hlt' := (hS2 i h1 (by omega)).2
          exact ⟨by rw [h1lk _ (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
        · intro z hz
          rw [h1next] at hz
          rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
        · intro _ w2 hpost
          have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
            rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
              h1lk _ (by omega) (by omega), hlk]
          simp only [writerWP_bind]
          rw [writerWP_getNode_known _ _ c w2 hlk2]
          simp only [putNode, writerWP_modify]
          refine hfin w1 _ w2 _ ?_ ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
          · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_true]
            omega
          · intro q hq y hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with hq | hq
            · subst hq; exact ⟨rfl, hKuniq y hy, hmade⟩
            · subst hq; exact absurd hy (hscpar hqlf y)
          · intro z hz _; exact h1lk z (by omega) (by omega)
          · intro z zn h1 h2 h3
            rw [h1next] at h2
            by_cases hz0 : z = w.next
            · subst hz0
              rw [h1n] at h3
              simp only [↓reduceIte, Option.some.injEq] at h3
              subst h3
              exact hmono _ hF
            · by_cases hz2 : z = w.next + 2
              · subst hz2
                rw [h1n] at h3
                simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                subst h3
                exact hmono _ hS
              · rw [h1lk z hz0 hz2, hfr z h1] at h3; cases h3
          · intro z hz
            show (upsert w2.nodes _ _).lookup z = _
            rw [lookup_upsert]; simp only [hz, ↓reduceIte]
          · intro zn h
            change (upsert w2.nodes _ _).lookup _ = some zn at h
            rw [lookup_upsert] at h
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact Or.inr (Or.inl ⟨D + 1, by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
      | true =>
        apply writerWP_handleFullWith_segSpace_upL D (X (D + 1)) (X D)
          (Nn (D + 1)) (Nn D) last (K (D + 1)) [] c w hlk hlq hqlf hmade hsp hpq hpk
        intro w1 h1n _ _ h1path h1next _
        have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
            w1.nodes.lookup z = w.nodes.lookup z :=
          fun z h1 h2 h3 => by rw [h1n]; simp only [h1, h2, h3, ↓reduceIte]
        refine writerWP_mono (hchainS w1 [(K (D + 1), w.next + 2 + 2)]
          (Or.inl ⟨_, _, rfl⟩) (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
        · intro i h1 h2
          have hlt' := (hS2 i h1 (by omega)).2
          exact ⟨by rw [h1lk _ (by omega) (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1,
            by omega⟩
        · intro z hz
          rw [h1next] at hz
          rw [h1lk z (by omega) (by omega) (by omega)]; exact hfr z (by omega)
        · intro _ w2 hpost
          have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
            rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
              h1lk _ (by omega) (by omega) (by omega), hlk]
          simp only [writerWP_bind]
          rw [writerWP_getNode_known _ _ c w2 hlk2]
          simp only [putNode, writerWP_modify]
          refine hfin w1 _ w2 _ (by simp) ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
          · intro q hq y hy
            simp only [List.mem_singleton] at hq
            subst hq
            exact ⟨rfl, hKuniq y hy, hmade⟩
          · intro z hz _; exact h1lk z (by omega) (by omega) (by omega)
          · intro z zn h1 h2 h3
            rw [h1next] at h2
            by_cases hz0 : z = w.next
            · subst hz0
              rw [h1n] at h3
              simp only [↓reduceIte, Option.some.injEq] at h3
              subst h3
              exact hmono _ hF
            · by_cases hz2 : z = w.next + 2
              · subst hz2
                rw [h1n] at h3
                simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                subst h3
                exact hmono _ hS
              · by_cases hz4 : z = w.next + 2 + 2
                · subst hz4
                  rw [h1n] at h3
                  simp only [hz0, hz2, ↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  exact shadowOK_root c.i _ _ _ hscpos _
                · rw [h1lk z hz0 hz2 hz4, hfr z h1] at h3; cases h3
          · intro z hz
            show (upsert w2.nodes _ _).lookup z = _
            rw [lookup_upsert]; simp only [hz, ↓reduceIte]
          · intro zn h
            change (upsert w2.nodes _ _).lookup _ = some zn at h
            rw [lookup_upsert] at h
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact Or.inr (Or.inl ⟨D + 1, by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
  -- the dispatch
  by_cases hsp : (!compact && decide (last.size > c.p.splitAbove)) = true
  · have hcf : compact = false := by
      cases compact with
      | false => rfl
      | true => simp at hsp
    have hsp' : c.p.splitAbove < last.size := by rw [hcf] at hsp; simpa using hsp
    subst hcf
    exact hSPACE hsp'
  · exact hTIME (by simpa using hsp)

end SIS.Tree
