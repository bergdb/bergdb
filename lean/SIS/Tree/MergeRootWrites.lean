import SIS.Tree.MergeHeightOrigins

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_getNode_noOutside (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun _ v => v.outside = w.outside) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
    · exact writerWP_throw _ _ _ _

theorem writerWP_ghOf_noOutside (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun _ v => v.outside = w.outside) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_noOutside x c w) ?_
  intro n v hv
  simp only [writerWP_get]
  split
  · simpa only [writerWP_pure] using hv
  · exact writerWP_throw _ _ _ _

theorem writerWP_replaceOrAdd_noOutside (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun _ v => v.outside = w.outside) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_foldlM_state _ _ _ _ _ (fun _ v => v.outside = w.outside) rfl ?_
  intro n more v hv
  split
  · exact writerWP_throw _ _ _ _
  · simpa only [writerWP_pure] using hv
  · simpa only [writerWP_pure] using hv

/-- Compacting a node made by this transaction replaces it in place, without
making another node outside the bounds. The upward callback is not used. -/
theorem writerWP_handleFullWith_compact_inplace
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (x : NodeId)
    (ins : List (Nat × NodeId)) (last n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (ht : n.firstTime = some c.i) :
    WriterWP (handleFullWith up depth x ins last true) c w
      (fun _ v => v.outside = w.outside) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  refine writerWP_mono (writerWP_ghOf_noOutside x c w) ?_
  intro gh v hv
  simp only [ht, BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [note, putNode]
    | exact writerWP_throw _ _ _ _
    | (with_unfolding_none refine writerWP_mono (writerWP_getNode_noOutside _ _ _) ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_mono (writerWP_replaceOrAdd_noOutside _ _ _ _) ?_; intro _ _ _)
    | split
    | (solve | simp_all)

theorem writerWP_handleFull_compact_inplace (depth : Nat) (x : NodeId)
    (last n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (ht : n.firstTime = some c.i) :
    WriterWP (handleFull depth x last true) c w (fun _ v => v.outside = w.outside) := by
  unfold handleFull
  exact writerWP_handleFullWith_compact_inplace _ depth x [] last n c w hn ht

/-- With room by size, a write to a node made by this transaction either
appends its klongs or compacts in place. Neither branch creates an outside node. -/
theorem writerWP_appendKlongs_inplace_noOutside (depth : Nat) (x : NodeId)
    (ins : List (Nat × NodeId)) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (ht : n.firstTime = some c.i)
    (hroom : n.size + ins.length + 1 ≤ c.p.M) :
    WriterWP (appendKlongs depth x ins) c w (fun _ v => v.outside = w.outside) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  have hnot : ¬ n.size + ins.length + 1 > c.p.M := by omega
  simp only [hnot, ↓reduceIte]
  split
  · exact writerWP_handleFullWith_compact_inplace _ depth x ins (n.lastVersion c.i) n c w hn ht
  · unfold addKeys
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known x n c w hn]
    simp only [putNode, writerWP_modify]

theorem mergeParamsOK_size_six (p : Params) (hp : MergeParamsOK p) : 6 ≤ p.M := by
  obtain ⟨hm,hmc,hmh,hcM,hhM,hfit⟩ := hp
  omega

/-- A freshly made root's two key klongs leave room for its first upward
write, including the two klongs of a split and the reserved time klong. -/
theorem writerWP_appendKlongs_newRoot_noOutside (depth : Nat) (x a b : NodeId)
    (sc : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p) (hi : ins.length ≤ 2)
    (hn : w.nodes.lookup x = some ⟨false,[.time c.i,.key 0 a,.key sc b]⟩) :
    WriterWP (appendKlongs depth x ins) c w (fun _ v => v.outside = w.outside) := by
  apply writerWP_appendKlongs_inplace_noOutside depth x ins _ c w hn rfl
  have hm := mergeParamsOK_size_six c.p hp
  simp only [KNode.size, List.length_cons, List.length_nil]
  omega

set_option maxHeartbeats 400000 in
/-- Updating a freshly made root after a merge also fits: the existing
klongs can be repointed in place, with at most a bitmap and one new key. -/
theorem writerWP_mergeParent_newRoot_noOutside (depth : Nat) (x a b m1 : NodeId)
    (sc : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p)
    (hn : w.nodes.lookup x = some ⟨false,[.time c.i,.key 0 a,.key sc b]⟩) :
    WriterWP (mergeParent x depth 1 0 m1 2 sc m2) c w
      (fun _ v => v.outside = w.outside) := by
  let rn : KNode := ⟨false,[.time c.i,.key 0 a,.key sc b]⟩
  have htime : rn.lastTime = some c.i := rfl
  have hindex : rn.lastTimeIndex = some 0 := rfl
  have hsize : rn.size = 3 := rfl
  have hlast : rn.ks.getLast? = some (.key sc b) := rfl
  have hm := mergeParamsOK_size_six c.p hp
  have h3 : 3 ≤ c.p.M := by omega
  have h4 : 4 ≤ c.p.M := by omega
  have h5 : 5 ≤ c.p.M := by omega
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known x rn c w hn]
    simp [htime,hindex,hsize,hlast,h4]
    repeat' first
      | wpSimplify
      | simp only [note,putNode]
      | exact writerWP_throw _ _ _ _
      | split
      | (solve | simp_all)
    all_goals exact writerWP_handleFull_compact_inplace _ _ _ rn _ _ (by exact hn) rfl
  | some yg =>
    rcases yg with ⟨y,g⟩
    by_cases hg : g = sc
    all_goals
      unfold mergeParent
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known x rn c w hn]
      simp [htime,hindex,hsize,hlast,h3,h5,hg]
      repeat' first
        | wpSimplify
        | simp only [note,putNode]
        | exact writerWP_throw _ _ _ _
        | split
        | (solve | simp_all)
      all_goals exact writerWP_handleFull_compact_inplace _ _ _ rn _ _ (by exact hn) rfl

end SIS.Tree
