/-
bergdb 030-37: root collapse and root growth preserve the virtual fill
conditions. A settled inner root has at least two final entries.
-/
import Contract.Proof.DnbFillFinal

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

theorem Filled.asRoot {x : Nat} (hm2 : 2 ≤ cf.m) (hf : Filled cf s false x) :
    Filled cf s true x := by
  cases hf with
  | key ho _ hmin hlong hinner =>
    exact Filled.key ho (fun _ _ => le_trans hm2 (hmin hm2 rfl))
      (fun _ h => Bool.noConfusion h) hlong hinner
  | other hn => exact Filled.other hn

theorem Filled.asChild {x : Nat} {root : Bool} (hf : Filled cf s root x)
    (hmin : ∀ n, s.obj x = some (.key n) → cf.m ≤ (live n.ks).length) : Filled cf s false x := by
  cases hf with
  | key ho _ _ hlong hinner =>
    exact Filled.key ho (fun _ h => Bool.noConfusion h) (fun _ _ => hmin _ ho) hlong hinner
  | other hn => exact Filled.other hn

theorem VFill.asRoot {g h : Nat} {v : VN} (hm2 : 2 ≤ cf.m)
    (hv : VFill cf i s g false h v) : VFill cf i s g true h v := by
  cases hv with
  | old hs hf => exact VFill.old hs (hf.asRoot hm2)
  | leaf hp hF hd _ => exact VFill.leaf hp hF hd (fun h _ => Bool.noConfusion h)
  | inner hc hn he hF hd _ => exact VFill.inner hc hn he hF hd (fun h _ => Bool.noConfusion h)

theorem VFill.asChild {g h : Nat} {v : VN} {root : Bool}
    (hv : VFill cf i s g root h v) (hmin : cf.m ≤ cntOf s v) : VFill cf i s g false h v := by
  cases hv with
  | old hs hf =>
    obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hs
    apply VFill.old hs
    apply hf.asChild
    intro n' hn'
    rw [ho] at hn'; cases hn'
    simpa only [cntOf, hk] using hmin
  | leaf hp hF hd _ => exact VFill.leaf hp hF hd (fun _ _ => hmin)
  | inner hc hn he hF hd _ => exact VFill.inner hc hn he hF hd (fun _ _ => hmin)

theorem VFill.old_own {g h y : Nat} {root : Bool} (hm2 : 2 ≤ cf.m)
    (hv : VFill cf i s g root h (.old y)) : OwnFill cf root h (cntOf s (.old y)) := by
  cases hv with
  | old hs hf =>
    obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hs
    have hn := (nodeFill_view hm2 h hs hf).own
    have hlen : (view h s y).length = cntOf s (.old y) := by
      cases h with
      | zero => simp only [view, ho, cntOf, hk]; rfl
      | succ h =>
        simp only [view, ho, cntOf, hk, ofKids]
        exact List.length_map _
    rwa [hlen] at hn

/-- All root collapses and new roots above cuts, with their final root
occupancy. This is independent of the dirty-bound join restriction. -/
theorem settleRoot_vfill {b G H : Nat} (hb : 8 ≤ b) :
    ∀ (f g h : Nat) (v v' : VN) (space : Bool), VFill (Cfg.java b G H) i s g true h v →
      settleRoot (Cfg.java b G H) i s f g v space = some (some v') →
      ∃ h', VFill (Cfg.java b G H) i s g true h' v' ∧
        OwnFill (Cfg.java b G H) true h' (cntOf s v')
  | 0, _, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, g, h, v, v', space, hv, hs => by
    have hm2 := (java_params (G := G) (H := H) hb).1
    have hdone (hown : OwnFill (Cfg.java b G H) true h (cntOf s v)) :
        ∃ h', VFill (Cfg.java b G H) i s g true h' v ∧
          OwnFill (Cfg.java b G H) true h' (cntOf s v) := ⟨h, hv, hown⟩
    rw [settleRoot.eq_def] at hs
    simp only at hs
    cases v with
    | old y =>
      have hs0 := hv
      cases hs0 with
      | old hshape hfilled =>
        obtain ⟨n, ho, hk, _, _, _, _⟩ := shaped_getKey hshape
        simp only at hs
        rw [hk] at hs
        simp only at hs
        split at hs
        · rename_i c z hl
          split at hs
          · cases hs; exact hdone (hv.old_own hm2)
          · rename_i hleaf
            have hf2 := (filled_key hfilled ho).1 (by simpa using hleaf) rfl
            rw [hl] at hf2
            simp at hf2
        · cases hs; exact hdone (hv.old_own hm2)
    | node base g' h' j es F d =>
      have hgh : g' = g ∧ h' = h := by cases hv <;> exact ⟨rfl, rfl⟩
      have hg' := hgh.1
      have hh' := hgh.2
      subst g' h'
      simp only at hs
      split at hs
      · rename_i hFe
        split at hs
        · cases hs
        · split at hs
          · rename_i hh
            have hh0 : h = 0 := by simpa using hh
            subst hh0
            cases hs
            exact hdone ⟨fun _ hh => (hh rfl).elim, fun hh => Bool.noConfusion hh⟩
          · cases hm : mkNode (Cfg.java b G H) i s none g 0 false [] with
            | none => rw [hm] at hs; cases hs
            | some w =>
              rw [hm] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              subst hs
              have hw := mkNode_vfill_leaf (isRoot := true) (by simp) (by simp) hm
              exact ⟨0, hw, ⟨fun _ hh => (hh rfl).elim, fun hh => Bool.noConfusion hh⟩⟩
      · rename_i hFe
        have hFpos : 0 < F.length := List.length_pos_iff_ne_nil.mpr (by
          simpa only [List.isEmpty_iff] using hFe)
        split at hs
        · rename_i hcollapse
          have hc : h ≠ 0 ∧ F.length = 1 := by
            simpa only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hcollapse
          have hh : h ≠ 0 := hc.1
          cases h with
          | zero => exact (hh rfl).elim
          | succ h =>
            cases es with
            | nil => simp at hs
            | cons p rest =>
              cases rest with
              | nil =>
                obtain ⟨c, ch⟩ := p
                have hchild : VFill (Cfg.java b G H) i s g false h ch := by
                  cases hv with
                  | inner hchildren _ _ _ _ _ => exact hchildren (c, ch) List.mem_cons_self
                simp only at hs
                exact settleRoot_vfill hb f g h ch v' space (hchild.asRoot hm2) hs
              | cons _ _ => simp at hs
        · rename_i hcollapse
          have hown : OwnFill (Cfg.java b G H) true h
              (cntOf s (.node base g h j es F d)) := by
            refine ⟨?_, fun hh => Bool.noConfusion hh⟩
            intro _ hh
            have hnot : ¬(h != 0 && F.length == 1) = true := hcollapse
            simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hnot
            change 2 ≤ F.length
            omega
          cases d with
          | same => simp only [Option.some.injEq] at hs; subst hs; exact hdone hown
          | append => simp only [Option.some.injEq] at hs; subst hs; exact hdone hown
          | parts k =>
            simp only at hs
            change (if 2 ≤ k then
              match mkNode (Cfg.java b G H) i s none g (h + 1) false
                [(0, .node base g h j es F (.parts k))] with
              | some w => settleRoot (Cfg.java b G H) i s f g w space
              | none => none
              else some (some (.node base g h j es F (.parts k)))) = some (some v') at hs
            split at hs
            · rename_i hk
              have hd := hv.node_decision
              obtain ⟨_, hmc, _, hcap, hhc, hcap1, _⟩ := java_params (G := G) (H := H) hb
              have hmin : (Cfg.java b G H).m ≤ F.length := by
                by_contra hn
                have hk1 := decideNode_small_parts_one (by omega) hmc (by omega)
                  (show F.length < (Cfg.java b G H).m by omega) hd.symm
                omega
              have hvc := hv.asChild hmin
              cases hm : mkNode (Cfg.java b G H) i s none g (h + 1) false
                  [(0, .node base g h j es F (.parts k))] with
              | none => rw [hm] at hs; cases hs
              | some w =>
                rw [hm] at hs
                simp only at hs
                have hw := mkNode_vfill_inner (isRoot := true)
                  (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hvc)
                  (by intro e he; simp only [List.mem_singleton] at he; subst he;
                      simp [VN.isEmpty]; exact List.ne_nil_of_length_pos hFpos)
                  (Or.inl (by simp)) (by simp) hm
                exact settleRoot_vfill hb f g (h + 1) w v' space hw hs
            · simp only [Option.some.injEq] at hs; subst hs; exact hdone hown

theorem vok_height_of_vfill {g h0 h1 : Nat} {root : Bool} {v : VN}
    (hf : VFill cf i s g root h1 v) (hv : VOk cf s g h0 v) : VOk cf s g h1 v := by
  cases v with
  | old y =>
    cases hf with
    | old hshape _ =>
      cases hv with
      | old _ hgood hne =>
        obtain ⟨n, ho, _, _, _, _, _⟩ := shaped_getKey hshape
        exact VOk.old hshape hgood ((b_view_ne_iff ho h1).mpr ((b_view_ne_iff ho h0).mp hne))
  | node base g' h' j es F d =>
    have h1' : h' = h1 := by cases hf <;> rfl
    have h0' := hv.ht.1
    have hh : h0 = h1 := h0'.symm.trans h1'
    rwa [hh] at hv

theorem VFill.height_eq {g h0 h1 : Nat} {root : Bool} {v : VN}
    (hf : VFill cf i s g root h1 v) (hv : VOk cf s g h0 v) : h1 = h0 := by
  cases v with
  | old y =>
    cases hf with
    | old hshape _ =>
      cases hv with
      | old hs _ _ =>
        obtain ⟨n, _, hk, hl, _, _, _⟩ := shaped_getKey hshape
        obtain ⟨m, _, hkm, hlm, _, _, _⟩ := shaped_getKey hs
        rw [hk] at hkm; cases hkm
        simp only [Cfg.lev] at hl hlm
        omega
  | node base g' h' j es F d =>
    have h1' : h' = h1 := by cases hf <;> rfl
    exact h1'.symm.trans hv.ht.1

theorem settleRoot_nodeFill_at {b G H f g h h' : Nat} (hb : 8 ≤ b) {v v' : VN} {space : Bool}
    (hf : VFill (Cfg.java b G H) i s g true h v)
    (hs : settleRoot (Cfg.java b G H) i s f g v space = some (some v'))
    (hv' : VOk (Cfg.java b G H) s g h' v') :
    NodeFill (Cfg.java b G H) h' true (fin s h' v') := by
  obtain ⟨hF, hf', hown⟩ := settleRoot_vfill hb f g h v v' space hf hs
  have heq := hf'.height_eq hv'
  subst hF
  exact (vfill_final_pieces hb h').1 g true v' hf' hv' hown

/-- At arbitrary join heights, a settled root's final abstract tree meets
the root and descendant occupancy rules. Its next-segment trees are not
part of this one-segment statement. -/
theorem settleRoot_nodeFill {b G H f g h : Nat} (hb : 8 ≤ b) {v v' : VN} {space : Bool}
    (hf : VFill (Cfg.java b G H) i s g true h v) (hv : VOk (Cfg.java b G H) s g h v)
    (hs : settleRoot (Cfg.java b G H) i s f g v space = some (some v')) :
    ∃ h', VOk (Cfg.java b G H) s g h' v' ∧ NodeFill (Cfg.java b G H) h' true (fin s h' v') := by
  obtain ⟨h', hf', hown⟩ := settleRoot_vfill hb f g h v v' space hf hs
  obtain ⟨⟨h0, hv0⟩, _⟩ := b_settle (cfgOk_java8 hb) f g space h v v' hv hs
  have hv' := vok_height_of_vfill hf' hv0
  exact ⟨h', hv', (vfill_final_pieces hb h').1 g true v' hf' hv' hown⟩

end Contract.PE
