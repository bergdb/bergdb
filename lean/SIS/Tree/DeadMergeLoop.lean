/-
The dead klongs' bound through the merges' loop (bergdb 024-12, section 1, `d4`'s
plan of 2026-11-15, step 3): `writerWP_mergeUp_del` with `DW` kept beside
`DelInv`; each merge keeps `DW` by `dw_merge`, its ranges from the `DelInvF` of
the state it starts from. Then `afterDelete` with root collapse (`dw_collapseRoot`).
-/
import SIS.Tree.DeadMergeStep
import SIS.Tree.DelMergeCaseKd

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- `writerWP_mergeUp_del` with the dead klongs' bound (`DW`) kept beside `DelInv`:
each merge by `dw_merge`, its ranges from `DelInvF` and the path. -/
theorem writerWP_mergeUp_delDW (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0)
    (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInv c base w0 k0 fuelR KO BK v → DW c base v →
      WriterWP (mergeUp key g fuel h merged) c v
        (fun _ v' => DelInv c base w0 k0 fuelR KO BK v' ∧ DW c base v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v ⟨hI, hbk, hik⟩ hdw
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (descentOK c base fuelR w0 k0 key g h v hI)
      (kd_descendToHeight KO BK key g h c v hv hk hbk hik))
      (writerWP_descendToHeight_readsU key g h c base hvc v)) ?_
    intro d v1 ⟨⟨⟨hI1, hPF⟩, hbk1, hik1, _⟩, hrd1⟩
    have hdw1 := dw_of_wNode hrd1.1 hdw
    split
    · simp only [writerWP_pure]; exact ⟨⟨hI1, hbk1, hik1⟩, hdw1⟩
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1⟩ := hPF
      unfold pathNode
      simp only [writerWP_bind, writerWP_get]
      cases hex : v1.path[d]? with
      | none => exact writerWP_throw _ _ _ _
      | some ex =>
        simp only [writerWP_pure]
        cases heq : v1.path[d - 1]? with
        | none => exact writerWP_throw _ _ _ _
        | some eq =>
          simp only [writerWP_pure]
          obtain ⟨B1, t1, hB1, hb1⟩ := hI1.2.2.2.2.2.2
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
            (writerWP_getNode_all eq.2 c v1 base hvc) (writerWP_getNode_cache eq.2 c v1))
            (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1))
            (kd_getNode KO BK eq.2 c v1 hv hk hbk1 hik1)) ?_
          rintro qn v2 ⟨⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩, hbk2, hik2, _⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hdw2 := dw_of_wNode hr2.1 hdw1
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact ⟨⟨hI2, hbk2, hik2⟩, hdw2⟩
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
              (writerWP_getNode_all ex.2 c v2 base hvc) (writerWP_getNode_cache ex.2 c v2))
              (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2))
              (kd_getNode KO BK ex.2 c v2 hv hk hbk2 hik2)) ?_
            rintro xn v3 ⟨⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩, hbk3, hik3, _⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hdw3 := dw_of_wNode hr3.1 hdw2
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact ⟨⟨hI3, hbk3, hik3⟩, hdw3⟩
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              obtain ⟨hX3, _, hS23, _, _⟩ := id hP3
              have hxX : X d = ex.2 := by
                have := hX3 d (Nat.le_refl _)
                rw [hp3, hp2, hex] at this
                exact (Option.some.inj this).symm
              have hqX : X (d - 1) = eq.2 := by
                have := hX3 (d - 1) (by omega)
                rw [hp3, hp2, heq] at this
                exact (Option.some.inj this).symm
              have hqn : Nn (d - 1) = qn := by
                have h1 := (hS23 (d - 1) (by omega)).1
                rw [hqX, hkeep3 _ _ hl2] at h1
                exact (Option.some.inj h1).symm
              have hmg := writerWP_merge_get_inv fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1
                X K Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn X K Nn hI3 hP3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hrg := writerWP_merge_range_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hkd := kd_merge KO BK ex.2 d c v3 hv hk hbk3 hik3 (by omega) ex.1
                (by rw [hp3, hp2, hex]) (by
                  intro a q' hq'
                  rw [hp3, hp2, heq] at hq'
                  simp only [Option.some.injEq] at hq'
                  subst hq'
                  exact ⟨qn, hkeep3 _ _ hl2, hql'⟩)
              have hparM : ∀ p, (v3.path[d - 1]?).map (·.2) = some p →
                  TReach (wNode c.p base v3) c.i v3.top.rootKey p ∧ ∃ pn, wNode c.p base v3 p = some pn ∧
                    pn.leaf = false ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
                    ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base v3 z = some zn →
                      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i := by
                intro p hp
                obtain ⟨hXp, _, hS2p, _, _⟩ := id hP3
                have hpX : p = X (d - 1) := by
                  rw [hXp (d - 1) (by omega)] at hp; exact (Option.some.inj hp).symm
                subst hpX
                have hw' : wNode c.p base v3 (X (d - 1)) = some (Nn (d - 1)) := by
                  obtain ⟨a, b⟩ := hS2p (d - 1) (by omega)
                  simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
                exact ⟨pathOK_reach c base v3 d X K Nn hP3 (d - 1) (by omega), Nn (d - 1), hw',
                  by rw [hqn]; exact hql', hI3.1.times _ _ hw', fun cc z zn _ hz => hI3.1.times z zn hz⟩
              have hdwm := dw_merge base ex.2 d c v3 hvc hth hcap hdw3 hI3.1.tree hI3.2.2.1 hparM
                (fun y hy => hI3.1.untaken y (tReach_reachS _ _ _ _ hy))
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
                (writerWP_and hmg hms) (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) hrg) hkd) hdwm) ?_
              rintro r v4 ⟨⟨⟨⟨⟨⟨hread4, hu4, hF4⟩, hb4⟩, hT4⟩, hR4⟩, hbk4, hik4, _, _⟩, hdw4⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hICE4 := hICEk v4 hbk4 hik4 (fun y hy => hu4 y (tReach_reachS _ _ _ _ hy))
              have hI4 : DelInvF c base w0 k0 fuelR v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk' => by
                  rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk', B1, t1, hB1, hb4⟩
              split
              · simp only [writerWP_pure]; exact ⟨⟨hI4, hbk4, hik4⟩, hdw4⟩
              · exact ih (h + 1) true v4 ⟨hI4, hbk4, hik4⟩ hdw4

/-- `afterDelete` keeps `DW` from a state with `DelInv` and `DW`: the merges' loop
(`writerWP_mergeUp_delDW`), then root collapse (`dw_collapseRoot`). -/
theorem dw_afterDelete (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0)
    (w0 : W) (k0 : Key) (v : W) (hI : DelInv c base w0 k0 fuelR KO BK v) (hdw : DW c base v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DW c base v') := by
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read]
  split
  · rw [writerWP_bind]
    refine writerWP_mono (writerWP_mergeUp_delDW key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap
      hth w0 k0 c.p.fuel h false v hI hdw) ?_
    intro merged v1 ⟨_, hdw1⟩
    split
    · exact dw_collapseRoot base key g c.p.fuel c v1 hvc hth hdw1
    · simp only [writerWP_pure]; exact hdw1
  · simp only [writerWP_pure]; exact hdw

end SIS.Tree
