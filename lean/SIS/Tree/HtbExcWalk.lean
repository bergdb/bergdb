/-
`htb`'s sites (bergdb 025-05, step 8): the merges' loop's last merge with a tall parent q.
A merge into two keeps q, a node of the transaction, in place: with room q names both new
nodes; full, q becomes its last version, which names both, or, split in place, the first
half of it, which has two live klongs or names the second new node beside the first new
node or a live child of q (`Shape1`). Retargeting q to the first new node keeps that.
-/
import SIS.Tree.HtbExcShape
import SIS.Tree.HeightsFit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Node facts -/

theorem pairFold_isSome (pairs : List (Nat × NodeId)) (q : Nat × NodeId) (hq : q ∈ pairs) :
    (pairs.foldl (pairLookupStep q.1) none).isSome = true := by
  rw [pairLookupFold_reverse, Option.or_none]
  cases h : pairs.reverse.lookup q.1 with
  | some _ => rfl
  | none =>
    have := List.lookup_eq_none_iff.mp h q (List.mem_reverse.mpr hq)
    simp at this

theorem cnt_two_of_pairs (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId)) (a b : Nat × NodeId)
    (ha : a ∈ pairs) (hb : b ∈ pairs) (hab : a.1 ≠ b.1) :
    2 ≤ (⟨leaf, newKlongs t pairs⟩ : KNode).cnt := by
  have hm : ∀ q ∈ pairs, q.1 ∈ (⟨leaf, newKlongs t pairs⟩ : KNode).live.map Prod.fst := by
    intro q hq
    have h1 := pairFold_isSome pairs q hq
    rw [← KNode.newKlongs_live_lookup_fold leaf t] at h1
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h1
    exact List.mem_map.mpr ⟨_, bk_mem_of_lookup _ _ _ hy, rfl⟩
  have hsub : ∀ k ∈ [a.1, b.1], k ∈ (⟨leaf, newKlongs t pairs⟩ : KNode).live.map Prod.fst := by
    intro k hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl
    · exact hm a ha
    · exact hm b hb
  have hnd : [a.1, b.1].Nodup := by simp [hab]
  have := hnd.length_le_of_subset hsub
  simpa [KNode.cnt] using this

theorem newKlongs_idx (t : Time) (pairs : List (Nat × NodeId)) (q : Nat × NodeId) (h : q ∈ pairs) :
    ∃ i : Nat, (newKlongs t pairs)[i]? = some (Klong.key q.1 q.2) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i + 1, by simp [newKlongs, hi]⟩

theorem halves_first_ks (leaf : Bool) (t : Time) (last : KNode) (pairs : List (Nat × NodeId))
    (hks : last.ks = newKlongs t pairs) :
    (halves leaf t last []).1.ks = newKlongs t (pairs.take (pairs.length / 2)) := by
  obtain ⟨lf, ks⟩ := last
  simp only at hks
  subst hks
  cases hdrop : pairs.drop (pairs.length / 2) with
  | nil => simp [halves, newKlongs, KNode.size, ← List.map_take, ← List.map_drop, hdrop]
  | cons q rest => simp [halves, newKlongs, KNode.size, ← List.map_take, ← List.map_drop, hdrop]

/-- The parent's node after the merge's parent step: it names the second new node m2 and
another node, the first new node m1 or one of S0, or has two live klongs. -/
def Shape1 (m1 m2 : NodeId) (S0 : NodeId → Prop) (n : KNode) : Prop :=
  (∃ (i j cv1 cv2 : Nat) (y1 : NodeId), n.ks[i]? = some (Klong.key cv1 y1) ∧
    n.ks[j]? = some (Klong.key cv2 m2) ∧ y1 ≠ m2 ∧ (y1 = m1 ∨ S0 y1)) ∨ 2 ≤ n.cnt

/-- The parent's node after the merge's parent step, by its three cases. -/
theorem shape_mp (p : Params) (hp : MergeParamsOK p) (pn : KNode) (tt : Time) (il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : NodeId) (g2 : Nat) (l r : NodeId) (S0 : NodeId → Prop)
    (hL : pn.ks[il]? = some (Klong.key cL l)) (hR : pn.ks[ir]? = some (Klong.key cR r)) (hc : cL ≠ cR)
    (hS : ∀ cv y, (cv, y) ∈ pn.live → S0 y) (hm2 : ¬ S0 m2) (h12 : m1 ≠ m2)
    (hpos : 0 < tt) (htimes : ∀ s, Klong.time s ∈ pn.ks → s ≤ tt) (hnew : pn.firstTime = some tt)
    (hleaf : pn.leaf = false) (m : KNode)
    (hm : m = mergeParentNode pn tt il cL m1 ir cR (some (m2, g2)) ∨
      ∃ last, mergeFullLast pn tt cL m1 cR (some (m2, g2)) = some last ∧
        (m = { last with leaf := pn.leaf } ∨
          (m = (halves pn.leaf tt last []).1 ∧ p.splitAbove < last.size))) :
    m.leaf = false ∧ m.firstTime = some tt ∧ Shape1 m1 m2 S0 m := by
  rcases hm with rfl | ⟨last, hlast, hm⟩
  · refine ⟨by rw [mrg_mergeParentNode_leaf, hleaf],
      (mergeParentNode_facts pn tt il cL m1 ir cR _ hpos htimes).2.1 tt hnew, Or.inl ?_⟩
    obtain ⟨⟨i, cv, hi⟩, ⟨j, cv', hj⟩⟩ := mergeParentNode_names pn tt il cL m1 ir cR m2 g2 l r hL hR hc
    exact ⟨i, j, cv, cv', m1, hi, hj, h12, Or.inl rfl⟩
  · obtain ⟨pairs, hks, ⟨cv1, hm1⟩, ⟨cv2, hm2'⟩, -, hfirst⟩ :=
      mergeFullLast_two pn tt cL m1 cR m2 g2 last hc hlast
    rcases hm with rfl | ⟨rfl, hsz⟩
    · refine ⟨hleaf, ?_, Or.inl ?_⟩
      · show (⟨pn.leaf, last.ks⟩ : KNode).firstTime = some tt
        rw [hks]; exact KNode.firstTime_newKlongs _ _ _
      · obtain ⟨i, hi⟩ := newKlongs_idx tt pairs _ hm1
        obtain ⟨j, hj⟩ := newKlongs_idx tt pairs _ hm2'
        refine ⟨i, j, cv1, cv2, m1, ?_, ?_, h12, Or.inl rfl⟩
        · show last.ks[i]? = _
          rw [hks]; exact hi
        · show last.ks[j]? = _
          rw [hks]; exact hj
    · obtain ⟨hfl, hff⟩ := halves_fst_facts pn.leaf tt last []
      refine ⟨by rw [hfl, hleaf], hff, ?_⟩
      have hlen : 4 ≤ pairs.length := by
        have h1 : last.size = pairs.length + 1 := by simp [KNode.size, hks, newKlongs]
        unfold MergeParamsOK at hp
        omega
      have hk := halves_first_ks pn.leaf tt last pairs hks
      obtain ⟨a, b, rest, hpairs⟩ : ∃ a b rest, pairs = a :: b :: rest := by
        match pairs, hlen with
        | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
      obtain ⟨k, hk2⟩ : ∃ k, pairs.length / 2 = k + 2 := ⟨pairs.length / 2 - 2, by omega⟩
      have htake : pairs.take (pairs.length / 2) = a :: b :: rest.take k := by
        rw [hk2, hpairs]; rfl
      rw [htake] at hk
      generalize (halves pn.leaf tt last []).1 = f at hk ⊢
      obtain ⟨fl, fks⟩ := f
      simp only at hk
      subst hk
      rcases hfirst a b rest hpairs with hab | ⟨hb2, ha⟩
      · exact Or.inr (cnt_two_of_pairs fl tt _ a b List.mem_cons_self
          (List.mem_cons_of_mem _ List.mem_cons_self) hab)
      · refine Or.inl ⟨1, 2, a.1, b.1, a.2, by simp [newKlongs], by simp [newKlongs, hb2], ?_, ?_⟩
        · rcases ha with ha | ha
          · rw [ha]; exact h12
          · intro e; exact hm2 (e ▸ hS a.1 a.2 ha)
        · rcases ha with ha | ha
          · exact Or.inl ha
          · exact Or.inr (hS a.1 a.2 ha)

/-! ## Frames of q -/

section Q

variable {y : NodeId} {k N : Nat}

theorem FrameD.zero {m : KNode} {w : W} (h : FrameD y m k N w) : FrameD y m 0 N w :=
  ⟨h.1, h.2.1, h.2.2.1, fun _ _ _ hj => absurd hj (Nat.not_lt_zero _), h.2.2.2.2⟩

theorem fd_putNode_self (m n : KNode) (c : Ctx) (w : W) (hw : FrameD y m k N w) :
    WriterWP (putNode y n) c w (fun _ v => FrameD y n k N v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  simp only [putNode, writerWP_modify]
  exact ⟨h1, by rw [lookup_upsert]; simp, h3, h4, h5⟩

theorem fd_takenBack {m : KNode} (x : NodeId) (hxy : x ≠ y) : FrameKeepsD y m k N (takenBack x) := by
  intro c w hw
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  simp only [takenBack, writerWP_modify]
  refine ⟨h1, h2, ?_, h4, h5⟩
  simp only [List.contains_cons, Bool.or_eq_false_iff]
  exact ⟨by simpa using Ne.symm hxy, h3⟩

theorem fd_unlink {m : KNode} (x : NodeId) (hxy : x ≠ y) : FrameKeepsD y m k N (unlink x) := by
  intro c w hw
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (fd_getNode x c w hw) ?_
  intro n v hv
  split
  · exact fd_putNode x _ hxy c v hv
  · exact (writerWP_pure _ _ _ _).mpr hv

theorem fd_ite_note {m : KNode} (b : Bool) (s : String) :
    FrameKeepsD y m k N (if b = true then note s else (pure PUnit.unit : M PUnit)) := by
  intro c w hw
  split
  · exact fd_note s c w hw
  · exact (writerWP_pure _ _ _ _).mpr hw

theorem replaceOrAdd_nil (last : KNode) :
    replaceOrAdd last [] = (do let _ ← (read : M Ctx); pure last) := by
  unfold replaceOrAdd; rfl

theorem writerWP_newKey_facts (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W) :
    WriterWP (newKey g h leaf ks) c w (fun r v => r = w.next ∧ (r, g, h) ∈ v.gh ∧ w.next < v.next ∧
      (∀ e ∈ w.gh, e ∈ v.gh)) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  split
  all_goals
    simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      first | rfl | trivial | omega | (intro e he; simp [he]) | simp

theorem qn_newKey {m : KNode} (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (newKey g h leaf ks) c w (fun r v => r = w.next ∧ (r, g, h) ∈ v.gh ∧ w.next < v.next ∧
      (∀ e ∈ w.gh, e ∈ v.gh) ∧ FrameD y m k N v) :=
  writerWP_mono (writerWP_and (writerWP_newKey_facts g h leaf ks c w) (fd_newKey g h leaf ks c w hw))
    (fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.2⟩)

/-- `replacedBy` or its default, then `setMadeFor`: the frame and the cached heights kept. -/
theorem qn_made {m : KNode} (x o : NodeId) (b : Prop) [Decidable b] (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (do setMadeFor x (← if b then replacedBy o else pure (some o))) c w
      (fun _ v => FrameD y m k N v ∧ v.gh = w.gh) := by
  have hs : ∀ old (v : W), FrameD y m k N v → v.gh = w.gh →
      WriterWP (setMadeFor x old) c v (fun _ v' => FrameD y m k N v' ∧ v'.gh = w.gh) := by
    intro old v hv hg
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact ⟨hv.same (Nat.le_refl _) rfl rfl rfl, hg⟩
    · simp only [writerWP_pure]; exact ⟨hv, hg⟩
  split
  · simp only [writerWP_bind]
    refine writerWP_mono (kd_replacedBy o c w) ?_
    rintro old v ⟨rfl, -⟩
    exact hs old _ hw rfl
  · simp only [writerWP_bind, writerWP_pure]
    exact hs _ w hw rfl

set_option maxHeartbeats 6400000 in
/-- A full node of the transaction at `depth` of the path, split in place: it becomes its
last version (a time split) or the first half of it (a space split). -/
theorem qx_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (x : NodeId)
    (last : KNode) (compact : Bool) (n : KNode)
    (hup : ∀ q more, q ≠ x → ∀ m, FrameKeepsD x m depth N (up q more))
    (c : Ctx) (w : W) (hw : FrameD x n depth N w) (hnew : n.firstTime = some c.i) :
    WriterWP (handleFullWith up depth x [] last compact) c w (fun _ v => ∃ m, FrameD x m depth N v ∧
      (m = { last with leaf := n.leaf } ∨
        (m = (halves n.leaf c.i last []).1 ∧ (!compact && decide (c.p.splitAbove < last.size)) = true))) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hw.2.1]
  simp only [hnew, beq_self_eq_true, Bool.not_true, replaceOrAdd_nil, Bool.false_eq_true, ↓reduceIte]
  repeat' first
    | (with_reducible assumption)
    | (simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure, writerWP_modify])
    | (with_unfolding_none exact writerWP_throw _ _ _ _)
    | ((with_unfolding_none guard_target = WriterWP (putNode x _) _ _ _)
       refine writerWP_mono (fd_putNode_self _ _ c _ (by assumption)) ?_; intro _ _ _)
    | fdCore
    | (refine writerWP_mono (hup _ _ (by first | assumption | exact frameNe_some (by assumption)) _ _ _
        (by assumption)) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
  all_goals first
    | exact ⟨_, by assumption, Or.inl rfl⟩
    | exact ⟨_, by assumption, Or.inr ⟨rfl, by assumption⟩⟩

theorem qx_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) (n : KNode)
    (c : Ctx) (w : W) (hw : FrameD x n depth N w) (hnew : n.firstTime = some c.i) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => ∃ m, FrameD x m depth N v ∧
      (m = { last with leaf := n.leaf } ∨
        (m = (halves n.leaf c.i last []).1 ∧ (!compact && decide (c.p.splitAbove < last.size)) = true))) := by
  unfold handleFull
  refine qx_handleFullWith _ depth x last compact n ?_ c w hw hnew
  intro q more hq m
  cases depth with
  | zero => intro c w _; exact writerWP_throw _ _ _ _
  | succ e => exact fd_appendKlongs e q more hq (by omega)

/-- The merge's parent step at a parent of the transaction: the parent's node by its cases. -/
theorem qx_mergeParent (q : NodeId) (pn : KNode) (d il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : NodeId) (g2 : Nat) (c : Ctx) (w : W) (hw : FrameD q pn d N w)
    (hnew : pn.firstTime = some c.i) :
    WriterWP (mergeParent q d il cL m1 ir cR (some (m2, g2))) c w (fun _ v => ∃ m, FrameD q m d N v ∧
      (m = mergeParentNode pn c.i il cL m1 ir cR (some (m2, g2)) ∨
       ∃ last, mergeFullLast pn c.i cL m1 cR (some (m2, g2)) = some last ∧
        (m = { last with leaf := pn.leaf } ∨
          (m = (halves pn.leaf c.i last []).1 ∧ c.p.splitAbove < last.size)))) := by
  refine writerWP_mergeParent_cases q pn d il cL m1 ir cR _ c w _ hw.2.1 (fun s => ?_)
    (fun last compact s hlast => ?_)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    exact ⟨_, ⟨h1, by simp [lookup_upsert], h3, h4, h5⟩, Or.inl rfl⟩
  · refine writerWP_mono (qx_handleFull d q last compact pn c _
      (hw.same (Nat.le_refl _) rfl rfl rfl) hnew) ?_
    rintro _ v ⟨m, hm, h | ⟨h, hs⟩⟩
    · exact ⟨m, hm, Or.inr ⟨last, hlast, Or.inl h⟩⟩
    · refine ⟨m, hm, Or.inr ⟨last, hlast, Or.inr ⟨h, ?_⟩⟩⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hs.2

/-- `retarget` of q: each key klong keeps its compare value, and names its node or dst,
dst only in place of src. -/
theorem qx_retarget (q src dst : NodeId) (n : KNode) (c : Ctx) (w : W) (hw : FrameD q n k N w) :
    WriterWP (retarget q src dst) c w (fun _ v => ∃ n', FrameD q n' k N v ∧ n'.leaf = n.leaf ∧
      n'.firstTime = n.firstTime ∧ n'.cnt = n.cnt ∧
      ∀ (i cv : Nat) (z : NodeId), n.ks[i]? = some (Klong.key cv z) →
        n'.ks[i]? = some (Klong.key cv z) ∨ (z = src ∧ n'.ks[i]? = some (Klong.key cv dst))) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q n c w hw.2.1]
  split
  · have hf := KNode.retarget_facts n (n.lastTimeIndex.getD 0) src dst
    refine writerWP_mono (fd_putNode_self n _ c w hw) ?_
    intro _ v hv
    refine ⟨_, hv, hf.1, hf.2.1, hf.2.2, fun i cv z hi => ?_⟩
    show (retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst)[i]? = _ ∨ (_ ∧
      (retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst)[i]? = _)
    rw [retargetKlongs_getElem, hi]
    simp only [Option.map_some, Option.some.injEq]
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      exact Or.inr ⟨hcond.2, rfl⟩
    · exact Or.inl rfl
  · rw [writerWP_pure]
    exact ⟨n, hw, rfl, rfl, rfl, fun i cv z hi => Or.inl hi⟩

/-- The walk's state after the merge's parent step. -/
def QW (q m1 m2 : NodeId) (S0 : NodeId → Prop) (e1 e2 : NodeId × Nat × Nat) (N : Nat) (c : Ctx)
    (v : W) : Prop :=
  e1 ∈ v.gh ∧ e2 ∈ v.gh ∧ ∃ n, FrameD q n 0 N v ∧ n.leaf = false ∧ n.firstTime = some c.i ∧
    Shape1 m1 m2 S0 n

theorem shape1_retarget (m1 m2 o : NodeId) (S0 : NodeId → Prop) (n n' : KNode) (h12 : m1 ≠ m2)
    (hom : o ≠ m2) (hc : n'.cnt = n.cnt)
    (hks : ∀ (i cv : Nat) (z : NodeId), n.ks[i]? = some (Klong.key cv z) →
      n'.ks[i]? = some (Klong.key cv z) ∨ (z = o ∧ n'.ks[i]? = some (Klong.key cv m1)))
    (h : Shape1 m1 m2 S0 n) : Shape1 m1 m2 S0 n' := by
  rcases h with ⟨i, j, cv1, cv2, y1, hi, hj, hne, hy⟩ | h
  · have hj' : n'.ks[j]? = some (Klong.key cv2 m2) := by
      rcases hks j cv2 m2 hj with h1 | ⟨h1, -⟩
      · exact h1
      · exact absurd h1.symm hom
    rcases hks i cv1 y1 hi with h1 | ⟨-, h1⟩
    · exact Or.inl ⟨i, j, cv1, cv2, y1, h1, hj', hne, hy⟩
    · exact Or.inl ⟨i, j, cv1, cv2, m1, h1, hj', h12, Or.inl rfl⟩
  · exact Or.inr (by rw [hc]; exact h)

/-- The merge's cleanup keeps the walk's state: it retargets q from the merged nodes, which
are none of q and m2, to m1. -/
theorem qx_cleanup (q m1 m2 : NodeId) (S0 : NodeId → Prop) (e1 e2 : NodeId × Nat × Nat) (c : Ctx)
    (h12 : m1 ≠ m2) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ o ∈ xs, o.1 ≠ q ∧ o.1 ≠ m2) →
    QW q m1 m2 S0 e1 e2 N c w →
    WriterWP (forIn xs PUnit.unit (fun o _ => if o.2 = true then (do
        retarget q o.1 m1
        checkFree o.1
        takenBack o.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink o.1
        pure (ForInStep.yield PUnit.unit)))) c w (fun _ v => QW q m1 m2 S0 e1 e2 N c v) := by
  intro xs
  induction xs with
  | nil => intro w _ h; rw [List.forIn_nil]; exact (writerWP_pure _ _ _ _).mpr h
  | cons o os ih =>
    intro w hT h
    rw [List.forIn_cons]
    obtain ⟨hoq, hom⟩ := hT o List.mem_cons_self
    have hk : ∀ v, QW q m1 m2 S0 e1 e2 N c v →
        WriterWP (forIn os PUnit.unit _) c v (fun _ v => QW q m1 m2 S0 e1 e2 N c v) :=
      fun v hv => ih v (fun o' ho' => hT o' (List.mem_cons_of_mem _ ho')) hv
    simp only [writerWP_bind]
    obtain ⟨he1, he2, n, hfd, hnl, hnf, hsh⟩ := h
    split
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and (qx_retarget q o.1 m1 n c w hfd)
        (@fields_retarget (ghHasFields e1) q o.1 m1 c w he1))
        (@fields_retarget (ghHasFields e2) q o.1 m1 c w he2)) ?_
      rintro _ w1 ⟨⟨⟨n', hfd1, hl1, hf1, hc1, hks1⟩, he11⟩, he21⟩
      have hsh1 := shape1_retarget m1 m2 o.1 S0 n n' h12 hom hc1 hks1 hsh
      refine writerWP_mono (writerWP_checkFree o.1 c w1) ?_
      rintro _ w2 ⟨hw2, -⟩
      subst hw2
      refine writerWP_mono (writerWP_and (writerWP_and (fd_takenBack o.1 hoq c w2 hfd1)
        (@fields_takenBack (ghHasFields e1) o.1 c w2 he11))
        (@fields_takenBack (ghHasFields e2) o.1 c w2 he21)) ?_
      rintro _ w3 ⟨⟨hfd3, he13⟩, he23⟩
      refine writerWP_mono (writerWP_and (writerWP_and (fd_note _ c w3 hfd3)
        (@fields_note (ghHasFields e1) _ c w3 he13))
        (@fields_note (ghHasFields e2) _ c w3 he23)) ?_
      rintro _ w4 ⟨⟨hfd4, he14⟩, he24⟩
      simp only [writerWP_pure]
      exact hk w4 ⟨he14, he24, n', hfd4, by rw [hl1, hnl], by rw [hf1, hnf], hsh1⟩
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_and (fd_unlink o.1 hoq c w hfd)
        (@fields_unlink (ghHasFields e1) o.1 c w he1))
        (@fields_unlink (ghHasFields e2) o.1 c w he2)) ?_
      rintro _ w1 ⟨⟨hfd1, he11⟩, he21⟩
      simp only [writerWP_pure]
      exact hk w1 ⟨he11, he21, n, hfd1, hnl, hnf, hsh⟩

end Q

end SIS.Tree
