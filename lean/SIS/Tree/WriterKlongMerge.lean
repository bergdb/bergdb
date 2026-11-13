import SIS.Tree.WriterCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "kwCachedUse " q:term " with " pn:term " using " hf:term " and " hc:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_klongsWf_cached $hf $hc $q $pn _ _ _ ?kwView ?kwState ?kwCache ?kwPost)
  case kwView => assumption
  case kwState => assumption
  case kwCache => assumption
  intro _ _ _ _))

macro "kwCachedNode " q:term " with " pn:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  refine writerWP_mono (klongsWf_getNode_cached _ $q $pn _ _ ?kwView ?kwState ?kwCache) ?kwPost
  case kwView => assumption
  case kwState => assumption
  case kwCache => assumption
  rintro _ _ ⟨_, _, _⟩))

macro "kwCachedSibling " q:term " with " pn:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  refine writerWP_mono (klongsWf_sibling_cached $q $pn _ _ _ _ _ _ ?kwView ?kwState ?kwCache) ?kwPost
  case kwView => assumption
  case kwState => assumption
  case kwCache => assumption
  rintro _ _ ⟨_, _, _⟩))

macro "kwCachedCreate " q:term " with " pn:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf_cached (klongsWf_newKey _ _ _ _ ?kwInput) (cache_newKey _ _ _ _) $q $pn _ _ _ ?kwView ?kwState ?kwCache ?kwPost)
  case kwInput => kwKs
  case kwView => assumption
  case kwState => assumption
  case kwCache => assumption
  intro _ _ _ _))

macro "kwCachedCore " q:term " with " pn:term : tactic => `(tactic| first
  | kwCachedNode $q with $pn
  | kwCachedSibling $q with $pn
  | kwCachedCreate $q with $pn
  | kwCachedUse $q with $pn using (klongsWf_note _) and (cache_note _)
  | kwCachedUse $q with $pn using (klongsWf_ghOf _) and (cache_ghOf _)
  | kwCachedUse $q with $pn using (klongsWf_klongAt _) and (cache_klongAt _)
  | kwCachedUse $q with $pn using (klongsWf_pathNode _) and (cache_pathNode _)
  | kwCachedUse $q with $pn using (klongsWf_replacedBy _) and (cache_replacedBy _)
  | kwCachedUse $q with $pn using (klongsWf_setMadeFor _ _) and (cache_setMadeFor _ _)
  | exact writerWP_throw _ _ _ _)

macro "kwMergeRightLive" : tactic => `(tactic| first
  | exact KNode.mergeIdx_current_cv_live _ _ _ _ (by assumption) (by assumption)
  | exact KNode.mergeIdx_above_cv_live _ _ _ _ _ (by assumption) (by assumption)
  | exact KNode.mergeIdx_below_cv_live _ _ _ _ _ (by assumption) (by assumption))

theorem klongsWf_mergeCleanup (parent m1 : NodeId) (xs : List (NodeId × Bool)) :
    KeepsKlongsWf (forIn xs PUnit.unit (fun q _ => do
      if q.2 then
        retarget parent q.1 m1
        takenBack q.1
        note "merge.takeback"
      else unlink q.1
      pure (ForInStep.yield PUnit.unit))) := by
  apply klongsWf_forIn
  intro q stateToken c w hv hw
  repeat' first
    | contradiction
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_unlink _)
    | kwUse (klongsWf_retarget _ _ _)
    | wpSplit
    | split

macro "kwMergeParentDone " q:term " with " pn:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (writerWP_mergeParent_wf $q $pn _ _ _ _ _ _ _ _ _ ?kwView ?kwState ?kwCache ?kwRight) ?kwPost)
  case kwView => assumption
  case kwState => assumption
  case kwCache => assumption
  case kwRight => kwMergeRightLive
  intro _ _ _))

set_option maxHeartbeats 1800000 in
/-- The complete merge writer preserves physical-history well-formedness.
The parent's selected live separator supplies strict bitmap growth; loads
and allocations retain its cached snapshot until the parent update. All
one/two-output, leaf/inner and old/new cleanup cases are included. -/
theorem klongsWf_merge (x : NodeId) (d : Nat) : KeepsKlongsWf (merge x d) := by
  intro c w hv hw
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (klongsWf_pathNode (d - 1) c w hv hw) ?_
  intro parent state hstate
  refine writerWP_mono (klongsWf_getNode_caches parent c state hv hstate) ?_
  rintro pn state ⟨hstate, hpn, hcache⟩
  repeat' first
    | contradiction
    | wpSimplify
    | kwCachedCore parent with pn
    | kwMergeParentDone parent with pn
    | kwUse (klongsWf_mergeCleanup _ _ _)
    | assumption
    | wpSplit
    | split
    | contradiction

end SIS.Tree
