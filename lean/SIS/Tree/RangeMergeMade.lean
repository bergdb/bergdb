import SIS.Tree.WriterGetMergeTail
import SIS.Tree.RangeMerge
import SIS.Tree.WriterTreeRetarget

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The writer's merge keeps the walk's ranges also when the transaction made
the merged nodes (bergdb 024-12, TP10; `RangeOrder`), on prover cost's
`writerWP_mergeTail_made_tree` and `writerWP_merge_made_tree`: the merge's last
loop keeps the parent's live klongs (`writerWP_mergeCleanup_keep`). -/

/-- A node retargeted keeps a live klong that does not name src. -/
theorem KNode.retarget_liveAt_keep (n : KNode) (ti : Nat) (src dst : NodeId) (t : Time) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ n.liveAt t) (hz : z ≠ src) :
    (c, z) ∈ ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).liveAt t := by
  have hl := lookup_of_mem_nodup _ (KNode.liveAt_keys_nodup n t) c z h
  rw [KNode.liveAt_lookup] at hl
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
  apply mem_of_lookup_nodup _ c z
  rw [KNode.liveAt_lookup]
  simp only
  rw [hpre, hdel]
  unfold keyLookup at hl ⊢
  rw [zipIdx_map_zipIdx]
  rcases keyLookupFold_retarget (n.delAt t) c ti src dst _ none none (Or.inl rfl) with h1 | ⟨h1, _⟩
  · rw [h1]; exact hl
  · rw [hl] at h1
    simp only [Option.some.injEq] at h1
    exact absurd h1 hz

/-- `writerWP_mergeCleanup_frame` (prover cost's) with the parent's leaf flag and
live klongs kept: no live klong of the parent names a node of the loop, so the
retargets change none. -/
theorem writerWP_mergeCleanup_keep (p m1 : NodeId) (t : Time) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W) (n : KNode), (∀ q ∈ xs, q.1 ≠ p) →
    w.nodes.lookup p = some n → (∀ q ∈ xs, ∀ c', (c', q.1) ∉ n.liveAt t) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧
        (∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.taken.contains y = w.taken.contains y) ∧
        (∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
        ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧
          ∀ c' z, (c', z) ∈ n'.liveAt t ↔ (c', z) ∈ n.liveAt t) := by
  intro xs
  induction xs with
  | nil =>
    intro w n _ hlk _
    rw [List.forIn_nil]
    refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, n, hlk, rfl, fun _ _ => Iff.rfl⟩
  | cons q qs ih =>
    intro w n hne hlk hno
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W) (n1 : KNode), w1.top = w.top → w1.next = w.next →
        (∀ y, y ≠ q.1 → w1.taken.contains y = w.taken.contains y) →
        (∀ y, y ≠ p → y ≠ q.1 → w1.nodes.lookup y = w.nodes.lookup y) →
        w1.nodes.lookup p = some n1 → n1.leaf = n.leaf →
        (∀ c' z, (c', z) ∈ n1.liveAt t ↔ (c', z) ∈ n.liveAt t) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧
          (∀ y, (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.taken.contains y = w.taken.contains y) ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
          ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧
          ∀ c' z, (c', z) ∈ n'.liveAt t ↔ (c', z) ∈ n.liveAt t) := by
      intro w1 n1 h1top h1next h1t h1l h1p h1leaf h1sub
      refine writerWP_mono (ih w1 n1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1p
        (fun q' hq' c' hm => hno q' (List.mem_cons_of_mem _ hq') c' ((h1sub _ _).mp hm))) ?_
      intro _ w2 ⟨h2top, h2next, h2t, h2l, n2, h2p, h2leaf, h2sub⟩
      refine ⟨h2top.trans h1top, h2next.trans h1next, fun y hy => ?_, fun y hyp hy => ?_,
        n2, h2p, h2leaf.trans h1leaf, fun c' z => (h2sub c' z).trans (h1sub c' z)⟩
      · rw [h2t y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1t y (hy q List.mem_cons_self)]
      · rw [h2l y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1l y hyp (hy q List.mem_cons_self)]
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_frame p q.1 m1 n c w hlk) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1l, n1, h1p, h1n⟩
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      refine hrest _ n1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact h1top
      · exact h1next
      · intro y hy
        show (q.1 :: w1.taken).contains y = _
        rw [List.contains_cons, h1t]
        have : (y == q.1) = false := by simpa using hy
        simp [this]
      · intro y hyp _; exact h1l y hyp
      · exact h1p
      · rcases h1n with he | ⟨ti, he⟩ <;> rw [he]
      · intro c' z
        constructor
        · intro hm
          rcases h1n with he | ⟨ti, he⟩
          · rw [he] at hm; exact hm
          · rw [he] at hm
            rcases KNode.retarget_liveAt n ti q.1 m1 t c' z hm with h | ⟨_, h⟩
            · exact h
            · exact absurd h (hno q List.mem_cons_self c')
        · intro hm
          rcases h1n with he | ⟨ti, he⟩
          · rw [he]; exact hm
          · rw [he]
            exact KNode.retarget_liveAt_keep n ti q.1 m1 t c' z hm
              (fun hzq => hno q List.mem_cons_self c' (hzq ▸ hm))
    · have hq2' : q.2 = false := by simpa using hq2
      simp only [writerWP_bind, hq2', Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_frame q.1 c w) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      apply hrest _ n h1top h1next
      · intro y _; rw [h1t]
      · intro y _ hy; exact h1l y hy
      · rw [h1l p (Ne.symm hqp)]; exact hlk
      · rfl
      · intro c' z; exact Iff.rfl

end SIS.Tree
