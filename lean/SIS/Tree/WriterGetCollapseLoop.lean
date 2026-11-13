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

/-! ## Root collapse at a segment root keeps `CollGetInv` -/

/-- A segment-root collapse at node-map level: the leaf lf's klong k to the
root rt names rt's child y instead; nothing else changes but at lf and rt. Every
path from r0 after is a path before, as long or longer, that avoids rt. -/
theorem segCollapse_pathLen (L L' : NodeId → Option KNode) (t : Time) (r0 lf rt y : NodeId)
    (k c : Nat) (ln ln' rn : KNode) (ht : TreeOK L t r0)
    (hlf : TReach L t r0 lf) (hln : L lf = some ln) (hk : (k, rt) ∈ ln.liveAt t)
    (hrn : L rt = some rn) (hy : (c, y) ∈ rn.liveAt t)
    (hln' : L' lf = some ln')
    (hlinks : ∀ c' z, (c', z) ∈ ln'.liveAt t → (c' = k ∧ z = y) ∨ ((c', z) ∈ ln.liveAt t ∧ c' ≠ k))
    (hother : ∀ x, x ≠ lf → x ≠ rt → L' x = L x) :
    ∀ z n, PathLen L' t r0 z n → z ≠ rt ∧ ∃ m, n ≤ m ∧ PathLen L t r0 z m := by
  have hlk : TLink L t lf k rt := ⟨ln, hln, hk⟩
  have hrtR : TReach L t r0 rt := TReach.link hlf hlk
  have hry : TLink L t rt c y := ⟨rn, hrn, hy⟩
  have hrty : rt ≠ y := fun h => ht.no_self_link rt c hrtR (by rw [← h] at hry; exact hry)
  have hnamert : ∀ u c', TReach L t r0 u → TLink L t u c' rt → u = lf ∧ c' = k :=
    fun u c' hu hl' => ht.oneLink u c' lf k rt hu hlf hl' hlk
  intro z n hz
  induction hz with
  | root =>
    refine ⟨fun h => ht.rootFree lf k hlf (by rw [h]; exact hlk), 0, Nat.le_refl _, PathLen.root⟩
  | @link u c' z n hu hl ih =>
    obtain ⟨hurt, m, hnm, hum⟩ := ih
    have huR : TReach L t r0 u := hum.reach
    obtain ⟨un, hun, hcz⟩ := hl
    by_cases hul : u = lf
    · rw [hul, hln'] at hun
      cases hun
      rcases hlinks c' z hcz with ⟨_, hz⟩ | ⟨hmem, hck⟩
      · rw [hz]
        refine ⟨Ne.symm hrty, m + 2, by omega, ?_⟩
        have h1 : PathLen L t r0 rt (m + 1) := PathLen.link (by rw [← hul]; exact hum) hlk
        exact PathLen.link h1 hry
      · have hl0 : TLink L t lf c' z := ⟨ln, hln, hmem⟩
        refine ⟨fun hzr => ?_, m + 1, by omega, PathLen.link (by rw [← hul]; exact hum) hl0⟩
        rw [hzr] at hl0
        exact hck (hnamert lf c' hlf hl0).2
    · rw [hother u hul hurt] at hun
      have hl0 : TLink L t u c' z := ⟨un, hun, hcz⟩
      refine ⟨fun hzr => ?_, m + 1, by omega, PathLen.link hum hl0⟩
      rw [hzr] at hl0
      exact hul (hnamert u c' huR hl0).1

/-- One collapse step at a segment root keeps `CollGetInv`: the leaf lf's
klong k to the root rt names rt's child y instead, with lf's new node a well-formed
leaf of no later time; nothing else changes but lf and rt, whose taking back is
the only change of the taken nodes; and every key reads as before. -/
theorem collGetInv_segStep (c : Ctx) (base : View BVal) (w0 v v' : W) (lf rt y : NodeId)
    (k cc : Nat) (ln ln' rn : KNode) (hI : CollGetInv c base w0 v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey lf) (hln : wNode c.p base v lf = some ln)
    (hk : (k, rt) ∈ ln.liveAt c.i) (hrn : wNode c.p base v rt = some rn) (hy : (cc, y) ∈ rn.liveAt c.i)
    (hln' : wNode c.p base v' lf = some ln') (hl'leaf : ln'.leaf = true)
    (hlwf' : klongsWf ln'.ks = true) (hlt' : ∀ s, Klong.time s ∈ ln'.ks → s ≤ c.i)
    (hlinks : ∀ c' z, (c', z) ∈ ln'.liveAt c.i → (c' = k ∧ z = y) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k))
    (hother : ∀ z, z ≠ lf → z ≠ rt → wNode c.p base v' z = wNode c.p base v z)
    (htop : v'.top = v.top) (hv : v'.vals = v.vals)
    (ht : ∀ z, z ≠ rt → v'.taken.contains z = v.taken.contains z)
    (hread : ∀ key, wGet c.p c.i base v' key = wGet c.p c.i base v key) :
    CollGetInv c base w0 v' := by
  obtain ⟨⟨hT, hU, hTi, hICE⟩, hG, hD, hW, hNV⟩ := hI
  have hT' := treeOK_collapseSegment (wNode c.p base v) (wNode c.p base v') c.i v.top.rootKey lf rt y
    k cc ln ln' rn hT hlf hln hk hrn hy hln' hlinks hother
  have hP := segCollapse_pathLen (wNode c.p base v) (wNode c.p base v') c.i v.top.rootKey lf rt y
    k cc ln ln' rn hT hlf hln hk hrn hy hln' hlinks hother
  have hR : ∀ z, TReach (wNode c.p base v') c.i v.top.rootKey z →
      z ≠ rt ∧ TReach (wNode c.p base v) c.i v.top.rootKey z := by
    intro z hz
    obtain ⟨n, hn⟩ := hz.pathLen
    obtain ⟨h1, m, _, h2⟩ := hP z n hn
    exact ⟨h1, h2.reach⟩
  have hV : wValue base v' = wValue base v :=
    wValue_eq_of_taken base v v' hv (fun z => z = rt) (fun z hz => ht z hz)
      (fun z hz => by rw [hz]; exact ⟨hU rt (TReach.link hlf ⟨ln, hln, hk⟩), hNV rt rn
        (TReach.link hlf ⟨ln, hln, hk⟩) hrn⟩)
  -- a reached node's node after: lf's new node, or the one before
  have hnode : ∀ z zn, TReach (wNode c.p base v') c.i v.top.rootKey z → wNode c.p base v' z = some zn →
      (z = lf ∧ zn = ln') ∨ wNode c.p base v z = some zn := by
    intro z zn hz hzn
    by_cases hzl : z = lf
    · left; rw [hzl, hln'] at hzn; exact ⟨hzl, (Option.some.inj hzn).symm⟩
    · right; rw [← hother z hzl (hR z hz).1]; exact hzn
  rw [← htop] at hT' hR hnode hP
  refine ⟨⟨hT', fun z hz => ?_, fun z zn hz hzn => ?_, fun z zn c' z' hz hzn hzl hmem => ?_⟩,
    fun key => by rw [hread key]; exact hG key, ?_, fun z zn hz hzn => ?_, fun z zn hz hzn => ?_⟩
  · obtain ⟨h1, h2⟩ := hR z hz
    rw [ht z h1]; rw [htop] at h2; exact hU z h2
  · rcases hnode z zn hz hzn with ⟨_, rfl⟩ | h
    · exact hlt'
    · exact hTi z zn (by have := (hR z hz).2; rw [htop] at this; exact this) h
  · rcases hnode z zn hz hzn with ⟨_, rfl⟩ | h
    · rw [hl'leaf] at hzl; cases hzl
    · have hzR := (hR z hz).2
      rw [htop] at hzR
      have hz'R : TReach (wNode c.p base v') c.i v'.top.rootKey z' :=
        TReach.link hz ⟨zn, hzn, hmem⟩
      by_cases hz'l : z' = lf
      · exact ⟨ln', by rw [hz'l]; exact hln'⟩
      · rw [hother z' hz'l (hR z' hz'R).1]
        have hmem' : (c', z') ∈ zn.liveAt c.i := hmem
        exact hICE z zn c' z' hzR h hzl hmem'
  · intro z n hz
    obtain ⟨_, m, hnm, hm⟩ := hP z n hz
    have := hD z m (by rw [htop] at hm; exact hm)
    omega
  · rcases hnode z zn hz hzn with ⟨_, rfl⟩ | h
    · exact hlwf'
    · exact hW z zn (by have := (hR z hz).2; rw [htop] at this; exact this) h
  · rw [hV]
    rcases hnode z zn hz hzn with ⟨hzl, _⟩ | h
    · rw [hzl]; exact hNV lf ln hlf hln
    · exact hNV z zn (by have := (hR z hz).2; rw [htop] at this; exact this) h

/-- `takeBackRoot` at a segment root x that the transaction made, below the
segment leaf `leaf` of the path, keeps `CollGetInv`. -/
theorem writerWP_takeBackRoot_seg_coll (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v (fun _ v' => CollGetInv c base w0 v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    rw [writerWP_getNode_known leaf ln c _ (by simpa using hlkL)]
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    split
    · rename_i j hj
      split
      · exact writerWP_throw _ _ _ _
      · simp only [putNode, writerWP_bind, writerWP_modify]
        refine (writerWP_takenBack_iff x c _ _).mpr ?_
        simp only
        have hLt' : (x :: v.taken).contains leaf = false := by
          rw [List.contains_cons]
          have : (leaf == x) = false := by simpa using hlx
          rw [this, Bool.false_or]; exact hLt
        have hyt : ∀ y, y ≠ x → (x :: v.taken).contains y = v.taken.contains y := by
          intro y hyx
          rw [List.contains_cons]
          have : (y == x) = false := by simpa using hyx
          simp [this]
        have hfin : ∀ w' : W, w'.vals = v.vals → w'.taken = x :: v.taken →
            w'.nodes = upsert v.nodes leaf (ln.repoint j child) → w'.top = v.top →
            CollGetInv c base w0 w' := by
          intro w' h'v h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hlinks : ∀ c' z, (c', z) ∈ (ln.repoint j child).liveAt c.i →
              (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
            intro c' z hmm
            rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times ln j child c.i hlnt)] at hmm
            have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
            rw [KNode.repoint_live_lookup ln x child k j hj c'] at hlk
            by_cases hck : k = c'
            · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
            · have hb : (k == c') = false := by simpa using hck
              rw [hb] at hlk
              simp only [Bool.false_eq_true, ↓reduceIte] at hlk
              refine Or.inr ⟨?_, Ne.symm hck⟩
              rw [KNode.liveAt_of_times ln c.i hlnt]
              exact mem_of_lookup_nodup _ c' z hlk
          have hV : wValue base w' = wValue base v :=
            wValue_eq_of_taken base v w' h'v (fun z => z = x) (fun z hz => by rw [h't]; exact hyt z hz)
              (fun z hz => by rw [hz]; exact ⟨hxt, hI.2.2.2.2 x n hxR hwx⟩)
          refine collGetInv_segStep c base w0 v w' leaf x child k 0 ln (ln.repoint j child) n hI hlf hwL
            hk hwx hcl hL' (by rw [mrg_repoint_leaf]; exact hlnl)
            (by rw [KNode.repoint_klongsWf]; exact hlnwf) (KNode.repoint_times ln j child c.i hlnt)
            hlinks hoth h'top h'v (fun z hz => by rw [h't]; exact hyt z hz) ?_
          intro key
          unfold wGet
          rw [hV, h'top]
          exact getFromR_segCollapse (wNode c.p base v) _ (wValue base v) c.i c.p.fuel v.top.rootKey
            leaf x child k ln (ln.repoint j child) n hT hlf hwL hL' hlnl
            (by rw [mrg_repoint_leaf]; exact hlnl)
            hlnwf (by rw [KNode.repoint_klongsWf]; exact hlnwf) hlnt
            (KNode.repoint_times ln j child c.i hlnt)
            (KNode.repoint_live_lookup ln x child k j hj) hk hwx hxl hlv hnt ⟨m, hm⟩ hoth hwfS hI.2.2.1
            (by rw [hI.2.2.2.2 child m hchR hm, hI.2.2.2.2 x n hxR hwx]) key
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf `leaf` of the path,
the leaf with room for the klong to x's child, keeps `CollGetInv`. -/
theorem writerWP_replaceRoot_seg_coll (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v (fun _ v' => CollGetInv c base w0 v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_frameV x c _) ?_
    intro _ w1 ⟨h1t, h1top, _, h1v, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by
      simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    have hV : wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        wValue base v := wValue_congr' base _ v h1t h1v
    refine collGetInv_segStep c base w0 v _ leaf x child k 0 ln (ln.add c.i (.key k child)) n hI hlf hwL
      hk hwx hcl hL' (by rw [KNode.add_leaf]; exact hlnl) (KNode.add_key_wf ln c.i k child hlnwf)
      (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt) ?_ hoth h1top h1v
      (fun z _ => by simp only [h1t]) ?_
    · intro c' z hmm
      rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
    · intro key
      unfold wGet
      rw [hV]
      simp only
      rw [h1top]
      exact getFromR_segCollapse (wNode c.p base v) _ (wValue base v) c.i c.p.fuel v.top.rootKey
        leaf x child k ln (ln.add c.i (.key k child)) n hT hlf hwL hL' hlnl
        (by rw [KNode.add_leaf]; exact hlnl) hlnwf (KNode.add_key_wf ln c.i k child hlnwf) hlnt
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt)
        (fun cc => KNode.add_key_live_lookup_of_wf ln c.i k cc child hlnwf) hk hwx hxl hlv hnt ⟨m, hm⟩
        hoth hwfS hI.2.2.1 (by rw [hI.2.2.2.2 child m hchR hm, hI.2.2.2.2 x n hxR hwx]) key

/-- The collapse steps at the space root keep `CollGetInv` (the steps of
`writerWP_collapseRoot_space_get`). -/
theorem writerWP_rootStep_space_coll (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v) (hx : x = v.top.rootKey)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) :
    WriterWP (takeBackRoot x 0 only) c v (fun _ v' => CollGetInv c base w0 v') ∧
    WriterWP (replaceRoot x 0 only) c v (fun _ v' => CollGetInv c base w0 v') := by
  have hxt : v.taken.contains x = false := by rw [hx]; exact hI.1.2.1 _ TReach.root
  have hroot : wNode c.p base v v.top.rootKey = some n := by
    rw [← hx]; simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hstep : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
      w3.vals = v.vals →
      (∀ z, z ≠ v.top.rootKey → w3.taken.contains z = v.taken.contains z) →
      (∀ z, z ≠ v.top.rootKey → w3.nodes.lookup z = v.nodes.lookup z) →
      CollGetInv c base w0 w3 := by
    intro child hptr w3 h3top h3v h3t h3n
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hptr
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv
      simpa using hcv
    subst hc0
    exact collGetInv_step c base w0 v w3 child n hI hroot hxl hlv h3top h3v h3t h3n
  constructor
  · cases hp : n.ptr? only with
    | none =>
      unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_takeBackRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3n, h3v⟩
      apply hstep child hp w3 h3top h3v
      · intro z hz
        rw [h3t, List.contains_cons]
        have : (z == x) = false := by rw [hx]; simpa using hz
        simp [this]
      · intro z _; rw [h3n]
  · cases hp : n.ptr? only with
    | none =>
      unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_replaceRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3v, h3n⟩
      apply hstep child hp w3 h3top h3v
      · intro z _; rw [h3t]
      · intro z hz; exact h3n z (by rw [hx]; exact hz)

/-- The descent's facts at a state: the path is the space root and steps linked
from it, ending at x, each node but the last in the writer's nodes; the last
step, if any, is from a segment leaf. -/
def SegDesc (c : Ctx) (base : View BVal) (x : NodeId) (v : W) : Prop :=
  TReach (wNode c.p base v) c.i v.top.rootKey x ∧
  ∃ ps, v.path = (none, v.top.rootKey) :: ps ∧
    LinkedFrom (wNode c.p base v) c.i v.top.rootKey ps ∧ pathEnd v.top.rootKey ps = x ∧
    (∀ z ∈ (v.top.rootKey :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base v z = some zn →
      v.nodes.lookup z = some zn) ∧
    (ps = [] ∨ ∃ ps0 k L ln, ps = ps0 ++ [(some k, x)] ∧ pathEnd v.top.rootKey ps0 = L ∧
      wNode c.p base v L = some ln ∧ ln.leaf = true)

theorem segDesc_of_readsAs (c : Ctx) (base : View BVal) (x : NodeId) (v v' : W)
    (h : SegDesc c base x v) (hr : ReadsAs c.p base v v') (hpre : v.nodes.IsPrefix v'.nodes)
    (hp : v'.path = v.path) : SegDesc c base x v' := by
  obtain ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩ := h
  unfold SegDesc
  rw [hr.1, hr.2.1, hp]
  exact ⟨hx, ps, hvp, hlf, hend, fun z hz zn hzn => lookup_of_isPrefix _ _ hpre z zn (hcache z hz zn hzn),
    hlast⟩

/-- The last link of steps linked from r. -/
theorem LinkedFrom.last (N : NodeId → Option KNode) (t : Time) (k : Nat) (x : NodeId) :
    ∀ (ps0 : List (Option Nat × NodeId)) (r : NodeId), LinkedFrom N t r (ps0 ++ [(some k, x)]) →
      ∃ ln, N (pathEnd r ps0) = some ln ∧ (k, x) ∈ ln.liveAt t := by
  intro ps0
  induction ps0 with
  | nil =>
    intro r h
    cases h with
    | cons _ n _ _ _ hn hl _ => exact ⟨n, by simpa [pathEnd] using hn, hl⟩
  | cons e rest ih =>
    intro r h
    cases h with
    | cons _ n k' y _ hn hl hr =>
      obtain ⟨ln, h1, h2⟩ := ih y hr
      refine ⟨ln, ?_, h2⟩
      have := pathEnd_cons_append r y (some k') [] rest
      simp only [List.nil_append] at this
      rw [this]; exact h1

/-- At a segment root below a segment leaf: the leaf's facts from `SegDesc`. -/
theorem segDesc_seg (c : Ctx) (base : View BVal) (x : NodeId) (v : W)
    (ps0 : List (Option Nat × NodeId)) (k : Nat) (L : NodeId) (ln : KNode)
    (hvp : v.path = (none, v.top.rootKey) :: (ps0 ++ [(some k, x)]))
    (hlf : LinkedFrom (wNode c.p base v) c.i v.top.rootKey (ps0 ++ [(some k, x)]))
    (hcache : ∀ z ∈ (v.top.rootKey :: (ps0 ++ [(some k, x)]).map (·.2)).dropLast, ∀ zn,
      wNode c.p base v z = some zn → v.nodes.lookup z = some zn)
    (hL : pathEnd v.top.rootKey ps0 = L) (hLn : wNode c.p base v L = some ln) :
    TReach (wNode c.p base v) c.i v.top.rootKey L ∧ v.nodes.lookup L = some ln ∧
      (k, x) ∈ ln.liveAt c.i ∧ v.path.length - 1 = ps0.length + 1 ∧
      (v.path[ps0.length]?).map (·.2) = some L ∧ v.path[ps0.length + 1]? = some (some k, x) := by
  have hnat : nodeAt v.top.rootKey (ps0 ++ [(some k, x)]) ps0.length = L := by
    rw [nodeAt_append_left _ _ _ _ (Nat.le_refl _), nodeAt_last, hL]
  obtain ⟨ln0, h1, h2⟩ := LinkedFrom.last _ _ k x ps0 _ hlf
  rw [hL, hLn] at h1
  cases h1
  refine ⟨?_, ?_, h2, by rw [hvp]; simp, ?_, ?_⟩
  · have := LinkedFrom.pathLen _ _ _ _ hlf ps0.length (by simp)
    rw [hnat] at this
    exact this.reach
  · apply hcache L _ ln hLn
    rw [← hnat]
    exact nodeAt_mem_dropLast _ _ _ (by simp)
  · rw [hvp, ← hnat]
    unfold nodeAt
    have hlen : ps0.length < (v.top.rootKey :: (ps0 ++ [(some k, x)]).map (·.2)).length := by
      simp only [List.length_cons, List.length_map, List.length_append, List.length_singleton]; omega
    rw [List.getElem?_eq_getElem hlen]
    simp only [Option.getD_some]
    rw [← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem (by simpa using hlen)]
  · rw [hvp]
    simp

/-- Root collapse at any segment keeps `CollGetInv`, with any invariant J of
the caller's that the reads keep and the two steps keep, given room in the
segment leaf above each segment root that is replaced (`hroom`; a full leaf, a
cascade, is not taken here). -/
theorem writerWP_collapseRoot_coll (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (J : W → Prop)
    (hJra : ∀ v v', J v → ReadsAs c.p base v v' → J v')
    (hroom : ∀ v x n leaf ln k, CollGetInv c base w0 v → J v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false)
    (hJT : ∀ v x n only, CollGetInv c base w0 v → J v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => J v'))
    (hJR : ∀ v x n only, CollGetInv c base w0 v → J v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => J v')) :
    ∀ fuel v, CollGetInv c base w0 v → J v →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInv c base w0 v' ∧ J v') := by
  intro fuel v hI hJ
  refine writerWP_collapseRoot_inv key seg c (fun v => CollGetInv c base w0 v ∧ J v) (SegDesc c base)
    ?_ ?_ ?_ ?_ fuel v ⟨hI, hJ⟩
  · rintro v ⟨hI, hJ⟩
    refine writerWP_mono (writerWP_descendToSegmentRoot_linked key seg c base hvc v hI.1.2.1 hI.2.2.2.1) ?_
    rintro x v' ⟨hr, _, hx, ps, hvp, hlf, hend, hcache, hlast⟩
    refine ⟨⟨collGetInv_of_readsAs c base w0 v v' hr hI, hJra v v' hJ hr⟩, ?_⟩
    unfold SegDesc
    rw [hr.1, hr.2.1]
    exact ⟨hx, ps, hvp, hlf, hend, hcache, hlast⟩
  · rintro x v ⟨hI, hJ⟩ hP
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c v base hvc) (writerWP_getNode_cache x c v)) ?_
    rintro n v' ⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩
    exact ⟨⟨collGetInv_of_readsAs c base w0 v v' hr hI, hJra v v' hJ hr⟩,
      segDesc_of_readsAs c base x v v' hP hr hpre hp, hl, hp⟩
  · rintro x v n only ⟨hI, hJ⟩ hP hlk hxl hm _ honly hcv
    refine writerWP_and ?_ (hJT v x n only hI hJ hP hlk hxl hm honly hcv)
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_coll x only n c base w0 v hI hx hlk honly hcv hxl).1
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen]
      exact writerWP_takeBackRoot_seg_coll x ps0.length only n L ln k c base w0 v hI hLr hLlk hLl hk hlk
        honly hcv hxl hpd hpk
  · rintro x v n only ⟨hI, hJ⟩ hP hlk hxl hm honly hcv
    refine writerWP_and ?_ (hJR v x n only hI hJ hP hlk hxl hm honly hcv)
    have hP' := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_coll x only n c base w0 v hI hx hlk honly hcv hxl).2
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      obtain ⟨hr1, hr2⟩ := hroom v x n L ln k hI hJ hP' hlk hxl hm hLr hLlk hLl hk
      rw [hlen]
      exact writerWP_replaceRoot_seg_coll x ps0.length only n L ln k c base w0 v hI hLr hLlk hLl hk hlk
        honly hcv hxl hpd hpk hr1 hr2

end SIS.Tree
