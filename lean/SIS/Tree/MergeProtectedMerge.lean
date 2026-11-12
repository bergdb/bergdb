import SIS.Tree.MergeKeptNode

namespace SIS.Tree

open SIS SIS.Check

theorem mergeIdx_splitRoot_right (t : Time) (l x : NodeId) (sc : Nat) (hsc : 0 < sc) :
    mergeIdx ⟨false,[.time t,.key 0 l,.key sc x]⟩ sc = (some 2,none,some (1,0)) := by
  have hz : 0 ≠ sc := Nat.ne_of_lt hsc
  simp [mergeIdx,KNode.lastBitmap,lastBitmapOf,hz]

set_option maxHeartbeats 4000000 in
/-- A merge of the right child of a cached new split root leaves its first
output cached, tagged at the old height, and not taken back. This covers
both one-node and two-node results and both cleanup routes. -/
theorem writerWP_merge_newRoot_right_first (base : NodeId) (q l x : NodeId)
    (d sc g h : Nat) (nl nx : KNode) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p) (hw : FreshCache base w) (hsc : 0 < sc)
    (hparent : w.path[d-1]? = some (none,q))
    (hpath : w.path[d]? = some (some sc,x))
    (hq : w.nodes.lookup q = some ⟨false,[.time c.i,.key 0 l,.key sc x]⟩)
    (hl : w.nodes.lookup l = some nl) (hx : w.nodes.lookup x = some nx)
    (hg : w.gh.lookup x = some (g,h)) :
    WriterWP (merge x d) c w (fun _ v => ∃ first,
      GuardHeld ⟨first,⟨nx.leaf,newKlongs c.i
        (mergeKlongs (!nx.leaf) c.p.mergeMax sc nl.live nx.live).1⟩,g,h⟩ v) := by
  let rn : KNode := ⟨false,[.time c.i,.key 0 l,.key sc x]⟩
  have hqbound := freshCache_lookup_lt base w hw q rn hq
  have hlbound := freshCache_lookup_lt base w hw l nl hl
  have hxbound := freshCache_lookup_lt base w hw x nx hx
  have hidx : mergeIdx rn sc = (some 2,none,some (1,0)) := mergeIdx_splitRoot_right c.i l x sc hsc
  have hptr1 : rn.ptr? 1 = some l := rfl
  have hptr2 : rn.ptr? 2 = some x := rfl
  have hcv1 : rn.cv? 1 = some 0 := rfl
  have hcv2 : rn.cv? 2 = some sc := rfl
  unfold merge
  simp only [writerWP_bind,writerWP_read,pathNode,writerWP_get,hparent,writerWP_pure]
  rw [writerWP_getNode_known q rn c w hq]
  rw [writerWP_getNode_known x nx c w hx]
  simp only [klongAt,writerWP_bind,writerWP_get,hpath,writerWP_pure]
  simp only [hidx,hptr2,hcv1,hcv2,
    Bool.false_eq_true,Bool.true_or, bne_self_eq_false,Option.isNone_none,↓reduceIte,writerWP_bind,writerWP_pure]
  unfold sibling
  simp only [writerWP_bind,writerWP_read,hptr1]
  rw [writerWP_getNode_known l nl c w hl]
  repeat' first
    | wpSimplify
    | simp only [note,ghOf,getNode,hx,hg,Bool.not_not]
    | exact writerWP_throw _ _ _ _
    | wpSplit
    | split
  all_goals
    refine writerWP_mono (writerWP_newKey_allocated base _ _ _ _ _ _ (by frState)) ?_
    rintro first v ⟨hv,hfirst,hnext,hns,hgh,htaken,hguard⟩
    let firstKs := newKlongs c.i (mergeKlongs (!nx.leaf) c.p.mergeMax sc nl.live nx.live).1
    let b : NodeGuard := ⟨first,⟨nx.leaf,firstKs⟩,g,h⟩
    have hb : GuardHeld b v := by simpa only [b,firstKs,Bool.not_not] using hguard
    have hf : first = w.next := by simpa only using hfirst
    have hbq : b.id ≠ q := by change first ≠ q; omega
    have hbl : b.id ≠ l := by change first ≠ l; omega
    have hbx : b.id ≠ x := by change first ≠ x; omega
    have hqv : v.nodes.lookup q = some rn := by
      rw [hns]
      simp [List.lookup_append,hq,rn]
    repeat' first
      | wpSimplify
      | simp only [replacedBy,setMadeFor,List.forIn_cons,List.forIn_nil]
      | ((with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
         refine writerWP_mono (writerWP_newKey_allocated_keep b base _ _ _ _ _ _ (by frState) (by kgState)) ?_
         rintro second u ⟨⟨_,_,_,_,_,_,_⟩,_⟩)
      | ((with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
         refine writerWP_mono (writerWP_mergeParent_newRoot_guard b _ q l x _ sc _ _ _ hp (by simp_all [List.lookup_append]) hbq (by kgState)) ?_
         intro _ _ _)
      | kgRetarget b
      | kgTake b
      | kgUnlink b
      | (refine ⟨first,?_⟩; change GuardHeld b _; kgState)
      | exact writerWP_throw _ _ _ _
      | wpSplit
      | split

/-- The first output of this actual merge retains m live compare values
from the left input and cannot pass the unary-root collapse test. -/
theorem writerWP_merge_newRoot_right_protected (base : NodeId) (q l x : NodeId)
    (d sc g h : Nat) (nl nx : KNode) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p) (hw : FreshCache base w) (hsc : 0 < sc)
    (hparent : w.path[d-1]? = some (none,q))
    (hpath : w.path[d]? = some (some sc,x))
    (hq : w.nodes.lookup q = some ⟨false,[.time c.i,.key 0 l,.key sc x]⟩)
    (hl : w.nodes.lookup l = some nl) (hx : w.nodes.lookup x = some nx)
    (hg : w.gh.lookup x = some (g,h)) (hleft : c.p.mergeBelow ≤ nl.cnt) :
    WriterWP (merge x d) c w (fun _ v => ∃ first after,
      GuardHeld ⟨first,after,g,h⟩ v ∧
      (newKlongs c.i (nl.live.take c.p.mergeBelow)).IsPrefix after.ks ∧
      c.p.mergeBelow ≤ after.cnt ∧ after.onlyLiveKlong = none) := by
  let after : KNode := ⟨nx.leaf,newKlongs c.i
    (mergeKlongs (!nx.leaf) c.p.mergeMax sc nl.live nx.live).1⟩
  have hc : c.p.mergeBelow ≤ after.cnt := by
    simpa only [after,Bool.not_not] using
      mergeKlongs_first_protected_fill c.p hp (!nx.leaf) c.i sc nl.live nx.live
        nl.live_keys_nodup hleft
  have hpref : (newKlongs c.i (nl.live.take c.p.mergeBelow)).IsPrefix after.ks := by
    obtain ⟨rest,hr⟩ := mergeKlongs_first_protected_prefix c.p hp (!nx.leaf) sc
      nl.live nx.live hleft
    refine ⟨rest.map (fun a => .key a.1 a.2),?_⟩
    simp only [after,newKlongs,List.cons_append,← List.map_append,hr]
  refine writerWP_mono
    (writerWP_merge_newRoot_right_first base q l x d sc g h nl nx c w
      hp hw hsc hparent hpath hq hl hx hg) ?_
  rintro _ v ⟨first,hguard⟩
  exact ⟨first,after,hguard,hpref,hc,
    KNode.onlyLiveKlong_none_of_cnt_ge_two after (Nat.le_trans hp.1 hc)⟩

/-- A new root's space split supplies a guarded first half with m live
entries. The parent callback is required to preserve allocation freshness;
the rule itself is for depth zero. -/
theorem writerWP_handleFullWith_new_root_guard (base : NodeId) (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (ins pairs : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p) (hf : FreshCache base w)
    (hv : ViewIdsBelow base c.view) (hb : GuardHeld b w)
    (hup : ∀ q more, KeepsFreshCache base (up q more))
    (ht : b.node.firstTime = some c.i)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : c.p.splitAbove < (⟨b.node.leaf,newKlongs c.i pairs⟩ : KNode).size) :
    let first := (halves b.node.leaf c.i ⟨b.node.leaf,newKlongs c.i pairs⟩ ins).1
    WriterWP (handleFullWith up 0 b.id ins ⟨b.node.leaf,newKlongs c.i pairs⟩ false) c w
      (fun _ v => GuardHeld {b with node := first} v ∧
        (newKlongs c.i (pairs.take c.p.mergeBelow)).IsPrefix first.ks ∧
        c.p.mergeBelow ≤ first.cnt ∧ first.onlyLiveKlong = none) := by
  dsimp only
  intro r v he
  obtain ⟨hn,hgh,htaken⟩ := writerWP_handleFullWith_new_root_first up b.id ins _ b.node
    b.g b.h c w hb.1 hb.2.1 ht hb.2.2.2 hfull r v he
  have hnext := (freshCache_handleFullWith up 0 b.id ins
    ⟨b.node.leaf,newKlongs c.i pairs⟩ false hup c w hv hf r v he).2
  refine ⟨⟨hn,hgh,?_,Nat.lt_of_lt_of_le hb.2.2.2 hnext⟩,?_,?_,?_⟩
  · simpa only [htaken] using hb.2.2.1
  · exact (halves_first_protected_prefix c.p hp b.node.leaf c.i pairs ins hs hfull).2.2
  · exact halves_first_protected_fill c.p hp b.node.leaf c.i pairs ins hs hfull
  · exact halves_first_protected_not_unary c.p hp b.node.leaf c.i pairs ins hs hfull

end SIS.Tree
