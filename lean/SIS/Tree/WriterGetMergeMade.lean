/-
The writer's merge keeps every reading also for nodes the transaction made
(bergdb 024-12, TP10's `OpGetOK`; 024-22): the parent's klongs of the
transaction that name a merged node made by it are retargeted to the new node,
which none live of them does after the merge, so the parent's live klongs are
kept; the merged nodes are taken back, and had no value.
-/
import SIS.Tree.WriterGetMergeTail
import SIS.Tree.WriterTreeRetarget

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node retargeted keeps every live klong that does not name the source. -/
theorem KNode.retarget_liveAt_of (n : KNode) (ti : Nat) (src dst : NodeId) (t : Time) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ n.liveAt t) (hz : z ≠ src) :
    (c, z) ∈ ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).liveAt t := by
  have hp : ∀ q, (fun k => match k with
      | Klong.time x => decide (x ≤ t)
      | _ => true) (retargetStep ti src dst q) = (fun k => match k with
      | Klong.time x => decide (x ≤ t)
      | _ => true) q.1 := by
    intro q
    rcases q with ⟨k, i⟩
    cases k with
    | key cv y =>
      by_cases hc : (decide (ti < i) && y == src) = true
      · simp only [retargetStep, hc, ↓reduceIte]
      · simp only [retargetStep, hc, Bool.false_eq_true, ↓reduceIte]
    | time u => rfl
    | del b => rfl
  have hpre : prefixAt (retargetKlongs n.ks ti src dst) t =
      ((prefixAt n.ks t).zipIdx).map (retargetStep ti src dst) := by
    rw [retargetKlongs_eq]
    unfold prefixAt
    exact takeWhile_zipIdx_map _ _ hp n.ks 0
  have hdel : ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).delAt t = n.delAt t := by
    unfold KNode.delAt
    simp only
    rw [hpre]
    unfold lastBitmapOf
    exact lastBitmapOf_zipIdx_map ti src dst _ 0 []
  have hl := lookup_of_mem_nodup _ (KNode.liveAt_keys_nodup n t) c z h
  rw [KNode.liveAt_lookup] at hl
  apply bk_mem_of_lookup _ c z
  rw [KNode.liveAt_lookup]
  simp only
  rw [hpre, hdel]
  unfold keyLookup at hl ⊢
  rw [zipIdx_map_zipIdx]
  rcases keyLookupFold_retarget (n.delAt t) c ti src dst _ none none (Or.inl rfl) with h1 | ⟨h1, h2⟩
  · rw [h1]; exact hl
  · rw [hl] at h1
    simp only [Option.some.injEq] at h1
    exact absurd h1 hz

/-- A node retargeted keeps its leaf flag and its time klongs. -/
theorem KNode.retarget_times (n : KNode) (ti : Nat) (src dst : NodeId) (t : Time)
    (h : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ s, Klong.time s ∈ (retargetKlongs n.ks ti src dst) → s ≤ t := by
  intro s hs
  rw [retargetKlongs_eq, List.mem_map] at hs
  obtain ⟨q, hq, hqs⟩ := hs
  have h1 := (retargetStep_time ti src dst q s).mp hqs
  apply h s
  have : q.1 ∈ n.ks := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq)
  rw [← h1]; exact this

theorem writerWP_retarget_frameV (p src dst : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some n) :
    WriterWP (retarget p src dst) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      ∃ n', w'.nodes.lookup p = some n' ∧
        (n' = n ∨ ∃ ti, n' = { n with ks := retargetKlongs n.ks ti src dst })) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p n c w hlk]
  split
  · unfold putNode
    refine (writerWP_modify _ c w _).mpr ?_
    have hrk : ∃ n' : KNode, n' = { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst } :=
      ⟨_, rfl⟩
    obtain ⟨n', hn'⟩ := hrk
    refine ⟨rfl, rfl, rfl, rfl, fun y hy => ?_, n', ?_, Or.inr ⟨_, hn'⟩⟩
    · show (upsert w.nodes p _).lookup y = _
      rw [lookup_upsert]; simp [hy]
    · show (upsert w.nodes p _).lookup p = _
      rw [lookup_upsert, hn']; simp only [↓reduceIte]; rfl
  · refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, n, hlk, Or.inl rfl⟩

/-- `writerWP_mergeCleanup_frame` with the values kept and the parent's live
klongs exactly kept (none names a node of the list). -/
theorem writerWP_mergeCleanup_frameV (p m1 : NodeId) (t : Time) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W) (n : KNode), (∀ q ∈ xs, q.1 ≠ p) →
    w.nodes.lookup p = some n → (∀ q ∈ xs, ∀ c', (c', q.1) ∉ n.liveAt t) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
        (∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.taken.contains y = w.taken.contains y) ∧
        (∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
        ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧
          ((∀ s, Klong.time s ∈ n.ks → s ≤ t) → ∀ s, Klong.time s ∈ n'.ks → s ≤ t) ∧
          ∀ c' z, (c', z) ∈ n'.liveAt t ↔ (c', z) ∈ n.liveAt t) := by
  intro xs
  induction xs with
  | nil =>
    intro w n _ hlk _
    rw [List.forIn_nil]
    refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, n, hlk, rfl, fun h => h,
      fun _ _ => Iff.rfl⟩
  | cons q qs ih =>
    intro w n hne hlk hno
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W) (n1 : KNode), w1.top = w.top → w1.next = w.next → w1.vals = w.vals →
        (∀ y, y ≠ q.1 → w1.taken.contains y = w.taken.contains y) →
        (∀ y, y ≠ p → y ≠ q.1 → w1.nodes.lookup y = w.nodes.lookup y) →
        w1.nodes.lookup p = some n1 → n1.leaf = n.leaf →
        ((∀ s, Klong.time s ∈ n.ks → s ≤ t) → ∀ s, Klong.time s ∈ n1.ks → s ≤ t) →
        (∀ c' z, (c', z) ∈ n1.liveAt t ↔ (c', z) ∈ n.liveAt t) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
          (∀ y, (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.taken.contains y = w.taken.contains y) ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
          ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧
            ((∀ s, Klong.time s ∈ n.ks → s ≤ t) → ∀ s, Klong.time s ∈ n'.ks → s ≤ t) ∧
            ∀ c' z, (c', z) ∈ n'.liveAt t ↔ (c', z) ∈ n.liveAt t) := by
      intro w1 n1 h1top h1next h1v h1t h1l h1p h1leaf h1times h1iff
      refine writerWP_mono (ih w1 n1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1p
        (fun q' hq' c' hm => hno q' (List.mem_cons_of_mem _ hq') c' ((h1iff _ _).mp hm))) ?_
      intro _ w2 ⟨h2top, h2next, h2v, h2t, h2l, n2, h2p, h2leaf, h2times, h2iff⟩
      refine ⟨h2top.trans h1top, h2next.trans h1next, h2v.trans h1v, fun y hy => ?_,
        fun y hyp hy => ?_, n2, h2p, h2leaf.trans h1leaf, fun ht => h2times (h1times ht),
        fun c' z => (h2iff c' z).trans (h1iff c' z)⟩
      · rw [h2t y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1t y (hy q List.mem_cons_self)]
      · rw [h2l y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1l y hyp (hy q List.mem_cons_self)]
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_frameV p q.1 m1 n c w hlk) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1v, h1l, n1, h1p, h1n⟩
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      refine hrest _ n1 h1top h1next h1v ?_ ?_ h1p ?_ ?_ ?_
      · intro y hy
        show (q.1 :: w1.taken).contains y = _
        rw [List.contains_cons, h1t]
        have : (y == q.1) = false := by simpa using hy
        simp [this]
      · intro y hyp _; exact h1l y hyp
      · rcases h1n with he | ⟨ti, he⟩ <;> rw [he]
      · intro ht
        rcases h1n with he | ⟨ti, he⟩ <;> rw [he]
        · exact ht
        · exact KNode.retarget_times n ti q.1 m1 t ht
      · intro c' z
        rcases h1n with he | ⟨ti, he⟩ <;> rw [he]
        constructor
        · intro hm
          rcases KNode.retarget_liveAt n ti q.1 m1 t c' z hm with h | ⟨_, h⟩
          · exact h
          · exact absurd h (hno q List.mem_cons_self c')
        · intro hm
          exact KNode.retarget_liveAt_of n ti q.1 m1 t c' z hm (fun h => by
            rw [h] at hm; exact hno q List.mem_cons_self c' hm)
    · have hq2' : q.2 = false := by simpa using hq2
      simp only [writerWP_bind, hq2', Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_frameV q.1 c w) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1v, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      apply hrest _ n h1top h1next h1v
      · intro y _; rw [h1t]
      · intro y _ hy; exact h1l y hy
      · rw [h1l p (Ne.symm hqp)]; exact hlk
      · rfl
      · exact fun h => h
      · exact fun _ _ => Iff.rfl

/-- The values after a step that kept them and took back no node but in S, whose
nodes were not taken and had no value: as before. -/
theorem wValue_eq_of_taken (base : View BVal) (w w' : W) (hv : w'.vals = w.vals)
    (S : NodeId → Prop) (ht : ∀ y, ¬ S y → w'.taken.contains y = w.taken.contains y)
    (hS : ∀ y, S y → w.taken.contains y = false ∧ wValue base w y = none) :
    wValue base w' = wValue base w := by
  funext y
  by_cases hy : S y
  · obtain ⟨htf, hvn⟩ := hS y hy
    rw [hvn]
    unfold wValue at hvn ⊢
    simp only [htf, Bool.false_eq_true, ↓reduceIte] at hvn
    cases h : w'.taken.contains y with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hv]; exact hvn
  · unfold wValue
    rw [ht y hy, hv]

end SIS.Tree
