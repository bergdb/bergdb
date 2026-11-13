import SIS.Tree.NodeMap
import SIS.Tree.WriterDeleteCount
import SIS.Tree.HistoricalPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

def DeleteMapChange (before after : KNode) (cv : Nat) : Prop :=
  ∀ c, after.live.lookup c = if c == cv then none else before.live.lookup c

/-- In a current-transaction node with room, the actual delete writer
implements an exact one-entry map deletion. Both bitmap update modes and
both dead-compaction routes preserve all other pointers. -/
theorem writerWP_appendDeleteKlong_new_room_map (b : NodeGuard)
    (depth cv : Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hroom : b.node.size + 1 < c.p.M) :
    WriterWP (appendDeleteKlong b.id depth cv) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ DeleteMapChange b.node after cv) := by
  have hold (hu : bitsUnion b.node.lastBitmap (b.node.bitsOf cv) = b.node.lastBitmap) :
      DeleteMapChange b.node b.node cv := b.node.delete_lookup_noop cv hu
  have hadd : DeleteMapChange b.node
      (b.node.add c.i (.del (bitsUnion b.node.lastBitmap (b.node.bitsOf cv)))) cv :=
    b.node.add_delete_live_lookup c.i cv
  have hset := fun old hl => (fun q => b.node.setAt_delete_live_lookup cv q old hl)
  have hcompact : DeleteMapChange b.node
      (b.node.lastVersionGivenDel c.i (bitsUnion b.node.lastBitmap (b.node.bitsOf cv))) cv :=
    b.node.delete_live_lookup c.i cv
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  repeat' first
    | wpSimplify
    | simp only [note, hroom, ↓reduceIte]
    | ((with_unfolding_none guard_target = WriterWP (handleFull _ _ _ true) _ _ _)
       unfold handleFull
       refine writerWP_mono (writerWP_handleFullWith_compact_new_same b _ _ _ _ _ (by kgState) ht) ?_
       intro result state hv
       try wpSimplify
       exact ⟨_, hv, hcompact⟩)
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro result state hv
       try wpSimplify
       refine ⟨_, hv, ?_⟩
       first
       | exact hadd
       | (apply hset; assumption)
       | (exfalso; simp_all))
    | exact writerWP_throw _ _ _ _
    | split
  all_goals
    refine ⟨b.node, hw, hold ?_⟩
    apply beq_iff_eq.mp
    cases hd : (bitsUnion b.node.lastBitmap (b.node.bitsOf cv) == b.node.lastBitmap) <;> simp_all

theorem writerWP_descendLte_cached_leaf (b : NodeGuard) (cv fuel : Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (hleaf : b.node.leaf = true) (hf : 0 < fuel)
    (post : NodeId → W → Prop) : WriterWP (descendLte cv fuel b.id) c w post ↔ post b.id w := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known b.id b.node c w hw.1]
    simp only [hleaf, ↓reduceIte, writerWP_pure]

/-- The ordinary room branch of the actual value writer stores the freshly
allocated pointer at exactly the requested compare value and preserves past
physical prefixes. No current-transaction or parameter-validity premise is
needed; the dead-compaction branch is excluded explicitly. -/
theorem writerWP_setValue_room_map (b : NodeGuard) (cv value : Nat) (key : Key)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (hleaf : b.node.leaf = true)
    (hwf : klongsWf b.node.ks = true) (hroom : b.node.size + 1 < c.p.M)
    (hdead : deadOver c.p (b.node.add c.i (.key cv w.next)) = false) :
    WriterWP (setValue b.id cv key (some value)) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧
        (∀ q, after.live.lookup q = if cv == q then some w.next else b.node.live.lookup q) ∧
        ∀ t < c.i, prefixAt after.ks t = prefixAt b.node.ks t) := by
  unfold setValue
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_descendLte_cached_leaf b cv c.p.fuel c w hw hleaf
    (by unfold Params.fuel; omega)]
  unfold newValue fresh
  wpSimplify
  have hguard : GuardHeld b {w with
      next := w.next + 2, vals := w.vals ++ [(w.next, value)],
      made := w.made ++ [⟨w.next, 0, true⟩]} := by
    refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
    change b.id < w.next + 2
    have hh := hw.2.2.2
    omega
  rw [writerWP_getNode_known b.id b.node _ _ hguard.1]
  simp only [hroom, decide_true, hdead, Bool.not_false, Bool.and_self, ↓reduceIte]
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ hguard) ?_
  intro _ v hv
  simp only [writerWP_pure]
  refine ⟨_, hv, ?_, ?_⟩
  · intro q
    exact b.node.add_key_live_lookup_of_wf c.i cv q w.next hwf
  · intro t ht
    exact b.node.add_prefixAt_past c.i t ht (.key cv w.next)

end SIS.Tree
