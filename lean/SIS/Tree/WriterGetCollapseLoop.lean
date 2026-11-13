/-
Root collapse at any segment (bergdb 024-22): the loop of `collapseRoot` for any
invariant that its descent, its node read and its two steps keep.
-/
import SIS.Tree.WriterGetUpTake
import SIS.Tree.GetPutPath

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `collapseRoot` keeps any invariant Inv that its steps keep: the descent to
the segment root (which gives facts Pd of the root and the state), the read of
the root's node, and the two collapse steps, `takeBackRoot` for a root the
transaction made by a split, `replaceRoot` for another, each at an inner root
whose only live klong is the empty key's, at the depth of the path's end. -/
theorem writerWP_collapseRoot_inv (key : Key) (seg : Nat) (c : Ctx) (Inv : W → Prop)
    (Pd : NodeId → W → Prop)
    (hdesc : ∀ v, Inv v → WriterWP (descendToSegmentRoot key seg) c v (fun x v' => Inv v' ∧ Pd x v'))
    (hget : ∀ x v, Inv v → Pd x v → WriterWP (getNode x) c v (fun n v' =>
      Inv v' ∧ Pd x v' ∧ v'.nodes.lookup x = some n ∧ v'.path = v.path))
    (hstepT : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime = some c.i → (v.madeFor.lookup x).isSome = true →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v'))
    (hstepR : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v')) :
    ∀ fuel v, Inv v → WriterWP (collapseRoot key seg fuel) c v (fun _ v' => Inv v') := by
  intro fuel
  induction fuel with
  | zero => intro v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro v hI
    unfold collapseRoot
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (hdesc v hI) ?_
    rintro x v1 ⟨hI1, hP1⟩
    refine writerWP_mono (hget x v1 hI1 hP1) ?_
    rintro n v2 ⟨hI2, hP2, hl2, _⟩
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte, writerWP_pure]; exact hI2
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      unfold replacedBy
      simp only [writerWP_bind, writerWP_get, writerWP_pure]
      split
      · simp only [writerWP_pure]; exact hI2
      · rename_i hmr
        split
        · simp only [writerWP_pure]; exact hI2
        · rename_i only honly
          split
          · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
          · rename_i hcv
            have hcv' : n.cv? only = some 0 := by simpa using hcv
            unfold pathSize
            simp only [writerWP_bind, writerWP_get, writerWP_pure]
            split
            · rename_i hmade
              have hm : n.firstTime = some c.i := by simpa using hmade
              have hrb : (v2.madeFor.lookup x).isSome = true := by
                simp only [hmade, Bool.true_and, Option.isNone_iff_eq_none] at hmr
                cases h : v2.madeFor.lookup x with
                | none => exact absurd h hmr
                | some _ => rfl
              rw [writerWP_bind]
              exact writerWP_mono (hstepT x v2 n only hI2 hP2 hl2 hleaf' hm hrb honly hcv')
                (fun _ v3 h3 => ih v3 h3)
            · rename_i hmade
              have hm : n.firstTime ≠ some c.i := by simpa using hmade
              rw [writerWP_bind]
              exact writerWP_mono (hstepR x v2 n only hI2 hP2 hl2 hleaf' hm honly hcv')
                (fun _ v3 h3 => ih v3 h3)

/-- The descent to a segment root on the key's path: the path after is the
space root and steps linked from it in the state before, each node but the last
read into the writer's nodes; the last step, if any, is from a segment leaf. The
state reads as before. -/
theorem writerWP_descendToSegmentRoot_linked (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hwf : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      klongsWf yn.ks = true) :
    WriterWP (descendToSegmentRoot key seg) c w (fun x v =>
      ReadsAs c.p base w v ∧ w.nodes.IsPrefix v.nodes ∧
      TReach (wNode c.p base w) c.i w.top.rootKey x ∧
      ∃ ps, v.path = (none, w.top.rootKey) :: ps ∧
        LinkedFrom (wNode c.p base w) c.i w.top.rootKey ps ∧ pathEnd w.top.rootKey ps = x ∧
        (∀ z ∈ (w.top.rootKey :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w z = some zn →
          v.nodes.lookup z = some zn) ∧
        (ps = [] ∨ ∃ ps0 k L ln, ps = ps0 ++ [(some k, x)] ∧ pathEnd w.top.rootKey ps0 = L ∧
          wNode c.p base w L = some ln ∧ ln.leaf = true)) := by
  unfold descendToSegmentRoot pathClear findRoot pathAdd
  simp only [writerWP_bind, writerWP_read, writerWP_modify, writerWP_get]
  generalize hw1 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w1
  have hr01 : ReadsAs c.p base w w1 := by subst hw1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hp1 : w1.path = [(none, w.top.rootKey)] := by subst hw1; rfl
  have hn1 : w1.nodes = w.nodes := by subst hw1; rfl
  have htop1 : w1.top = w.top := by subst hw1; rfl
  simp only [writerWP_pure]
  rw [← htop1]
  have hN1 : wNode c.p base w1 = wNode c.p base w := hr01.1
  rw [← htop1, ← hN1] at hRt hwf
  have hRt1 : ∀ y, TReach (wNode c.p base w1) c.i w1.top.rootKey y → w1.taken.contains y = false := by
    intro y hy; rw [hr01.2.2.1]; exact hRt y hy
  let r := w1.top.rootKey
  let inv : NodeId → W → Prop := fun x v =>
    ReadsAs c.p base w1 v ∧ w1.nodes.IsPrefix v.nodes ∧ TReach (wNode c.p base w1) c.i r x ∧
    ∃ ps, v.path = w1.path ++ ps ∧ LinkedFrom (wNode c.p base w1) c.i r ps ∧ pathEnd r ps = x ∧
      (∀ z ∈ (r :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w1 z = some zn →
        v.nodes.lookup z = some zn) ∧
      (ps = [] ∨ ∃ ps0 k L ln, ps = ps0 ++ [(some k, x)] ∧ pathEnd r ps0 = L ∧
        wNode c.p base w1 L = some ln ∧ ln.leaf = true)
  refine writerWP_mono (writerWP_foldlM_state _ _ r c w1 inv
    ⟨ReadsAs.refl _ _ _, List.prefix_refl _, TReach.root, [], by simp, LinkedFrom.nil r, rfl,
      by simp, Or.inl rfl⟩ ?_) ?_
  · intro a b v ⟨hrv, hpre, hra, ps, hvp, hlf, hend, hcache, _⟩
    have hNv : wNode c.p base v = wNode c.p base w1 := hrv.1
    have ht1 : ∀ q ∈ eqVisits (wNode c.p base v) c.i b c.p.fuel a, v.taken.contains q.1 = false := by
      intro q hq
      rw [hrv.2.2.1]
      rw [hNv] at hq
      exact hRt1 q.1 (reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ _ _ a q.1 q.2
        (tReach_reachS _ _ _ _ hra) hq))
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendLte_reads b c base hvc c.p.fuel a v ht1)
      (writerWP_descendLte_steps b c base hvc c.p.fuel a v ht1))
      (writerWP_descendLte_cache b c base hvc c.p.fuel a v ht1)) ?_
    intro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps1, hpf, hp3, hLe⟩⟩,
      ⟨hcache3, _, hpre3⟩⟩
    rw [writerWP_getNode_known L n c _ hlk3]
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      rw [hNv] at hn hpf hvisL hcache3
      have hLr : TReach (wNode c.p base w1) c.i r L :=
        reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ _ _ a L b (tReach_reachS _ _ _ _ hra) hvisL)
      have hfdc : fd.c = b := KNode.searchEq_c n c.i b fd hfd
      have hlink : (fd.c, fd.y) ∈ n.liveAt c.i := by
        rw [hfdc]
        exact KNode.searchEq_mem n c.i b fd (hwf L n hLr hn) hfd
      have hvisAll := PathFrom.mem_eqVisits _ _ _ c.p.fuel a steps1 hpf
        (fun m hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
      refine ⟨ReadsAs.trans _ _ _ _ _ hrv (ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩),
        hpre.trans hpre3, TReach.link hLr ⟨n, hn, hlink⟩, ps ++ steps1 ++ [(some fd.c, fd.y)],
        by simp [hp3, hvp], ?_, ?_, ?_, Or.inr ⟨ps ++ steps1, fd.c, L, n, rfl, ?_, hn, hnl⟩⟩
      · rw [List.append_assoc]
        refine LinkedFrom.append _ _ r ps _ hlf ?_
        rw [hend]
        refine LinkedFrom.append _ _ a steps1 _ (LinkedFrom.of_pathFrom _ _ b a steps1 hpf) ?_
        rw [← hLe]
        exact LinkedFrom.cons L n fd.c fd.y [] hn hlink (LinkedFrom.nil _)
      · have := pathEnd_cons_append r fd.y (some fd.c) (ps ++ steps1) []
        simp [pathEnd] at this ⊢
      · intro z hz zn hzn
        have hsplit : (r :: (ps ++ steps1 ++ [(some fd.c, fd.y)]).map (·.2)).dropLast =
            (r :: ps.map (·.2)) ++ steps1.map (·.2) := by
          simp only [List.map_append, List.map_cons, List.map_nil]
          rw [← List.cons_append, List.dropLast_concat]
          rfl
        rw [hsplit] at hz
        rcases List.mem_append.mp hz with hz | hz
        · -- a node of the path before, or its end a
          have hlast : (r :: ps.map (·.2)) = (r :: ps.map (·.2)).dropLast ++ [a] := by
            rw [← hend]
            cases hps : ps.reverse with
            | nil => simp at hps; subst hps; simp [pathEnd]
            | cons e rest =>
              have : ps = rest.reverse ++ [e] := by
                rw [← List.reverse_reverse ps, hps]; simp
              subst this
              simp only [pathEnd, List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
                List.getLast?_singleton]
              rw [← List.cons_append, List.dropLast_concat]
              simp
          rw [hlast] at hz
          rcases List.mem_append.mp hz with hz | hz
          · have h1 := hcache z hz zn hzn
            exact lookup_of_isPrefix _ _ hpre3 z zn h1
          · have hza : z = a := by simpa using hz
            rw [hza] at hzn ⊢
            exact hcache3 a zn hvisAll.1 hzn
        · obtain ⟨e, he1, he2⟩ := List.mem_map.mp hz
          rw [← he2] at hzn ⊢
          exact hcache3 e.2 zn (hvisAll.2 e he1) hzn
      · rw [pathEnd_append_gen, hend, hLe]
  · rintro x v ⟨hrv, hpre, hrx, ps, hvp, hlf, hend, hcache, hlast⟩
    refine ⟨ReadsAs.trans _ _ _ _ _ hr01 hrv, by rw [hn1] at hpre; exact hpre, ?_, ps,
      by rw [hvp, hp1, htop1]; rfl, ?_, hend, ?_, ?_⟩
    · rw [← hN1]; exact hrx
    · rw [← hN1]; exact hlf
    · intro z hz zn hzn
      rw [← hN1] at hzn
      exact hcache z hz zn hzn
    · rcases hlast with h | ⟨ps0, k, L, ln, h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨ps0, k, L, ln, h1, h2, by rw [← hN1]; exact h3, h4⟩

end SIS.Tree
