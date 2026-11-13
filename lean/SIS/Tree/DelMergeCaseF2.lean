import SIS.Tree.GetDescentOK

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Case 4 of 024-12's assembly by the F2 route (bergdb 024-12, case (4)):
`opGetCaseOK_delMergeF`'s reduction without its descent obligation
(`DescentOKF`, whose `MergePathCond` runs within reach violate). The descent is
proved (`descentOKF2`), and the merge's reading and tree need only the state's
invariants (`writerWP_merge_get_invF2`, `writerWP_merge_tree_inv2`). Left are
the merge's and the collapse's obligations (`MergeStepOKF`, `CollapseStepOKF`)
and `DelStepsOKF`. -/

/-- The merges' loop keeps `DelInvF`, given the merge's obligation at f (the
descent and the merge's reading proved: `descentOKF2`, `writerWP_merge_get_invF2`). -/
theorem writerWP_mergeUp_delF2 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF c base fuelR)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvF c base w0 k0 fuelR v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvF c base w0 k0 fuelR v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hI
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (descentOKF2 c base fuelR w0 k0 key g h v hI) ?_
    intro d v1 ⟨hI1, hPF⟩
    split
    · simp only [writerWP_pure]; exact hI1
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
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all eq.2 c v1 base hvc)
            (writerWP_getNode_cache eq.2 c v1)) (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1)) ?_
          rintro qn v2 ⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact hI2
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all ex.2 c v2 base hvc)
              (writerWP_getNode_cache ex.2 c v2)) (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2)) ?_
            rintro xn v3 ⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact hI3
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
              have hmg := writerWP_merge_get_invF2 fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn hI3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hmg hms)
                (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) ?_
              rintro r v4 ⟨⟨⟨hread4, ⟨hu4, hR4, hICE4⟩, hF4⟩, hb4⟩, hT4⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hI4 : DelInvF c base w0 k0 fuelR v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk => by rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk,
                  B1, t1, hB1, hb4⟩
              split
              · simp only [writerWP_pure]; exact hI4
              · exact ih (h + 1) true v4 hI4


/-- `afterDelete` keeps `DelInvF`, given the merge's and the collapse's obligations at f. -/
theorem writerWP_afterDelete_delF2 (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF c base fuelR)
    (hC : CollapseStepOKF c base fuelR) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W) (hI : DelInvF c base w0 k0 fuelR v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvF c base w0 k0 fuelR v') :=
  writerWP_afterDelete_inv key g h c (DelInvF c base w0 k0 fuelR)
    (fun v hI => writerWP_mergeUp_delF2 key g c base hvc fuelR hfR hM hsa2 hcap w0 k0 c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delF key g c base hvc fuelR hfR hC w0 k0 v hI) v hI

/-- Case 4 at the reading fuel p.fuel + 1 inside the delete (option (a)):
`OpGetCaseOK'` from the obligations at f = p.fuel + 1 but the descent's
(`descentOKF2`). -/
theorem opGetCaseOK'_delMerge2 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF p R)
    (hM : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) :
    OpGetCaseOK' p R DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 hP
  obtain ⟨key, hop, hmerges⟩ := hP
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun g h v hv => writerWP_afterDelete_delF2 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) hsa2 hcap w key v hv)
    (fun g h merged v hv => writerWP_mergeUp_delF2 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) hsa2 hcap w key p.fuel h merged v hv)
    (fun seg v hv => writerWP_collapseRoot_delF key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key v hv)

/-- Case 4 (`OpGetCaseOK`) from the obligations at p.fuel + 1 but the descent's,
and the fuel premise along transactions (`TxSegFitsOK`). -/
theorem opGetCaseOK_delMergeF2 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF p R)
    (hM : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMerge2 p R hS hM hC hsa2 hcap) hfit

end SIS.Tree
