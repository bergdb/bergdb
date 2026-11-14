/-
Step 4 (B), part 2 (bergdb 024-22; 024-12's (4)): a merge adds at most one to
the heights. Its new nodes have the merged node's height; its parent, the
path's node above it, takes them in place or by a split whose cascade goes up
the path (`sb_mergeParent`, `sb_merge`, `seenHeight_merge`).
-/
import SIS.Tree.HeightsFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "sbState2" : tactic => `(tactic| first
  | assumption
  | (refine SBInv.congr (v := ?sbV) ?sbHv ?sbG1 ?sbG2 ?sbG3
     case sbHv => assumption
     all_goals rfl))

macro "sbUse2 " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_sb (b := ?sbB) $h _ ?sbW0 _ _ ?sbHH ?sbS ?sbPost)
  case sbS => sbState2
  case sbHH => assumption
  intro _ _ _))

macro "sbFrame2" : tactic => `(tactic| (
  intro c w
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
        writerWP_set, writerWP_modify, note, fresh, putNode, newValue,
        setMadeFor, replacedBy, takenBack, pathSize, pathNode,
        klongAt, parentAt, newSuperRoot, addKeys]
    | exact writerWP_throw _ _ _ _
    | (refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial | exact Nat.le_refl _ | omega)
    | wpSplit
    | split
    | contradiction))

theorem sb_takenBack (b : Nat) (x : NodeId) : KeepsSB b (takenBack x) := sb_of_frame (by sbFrame2)

theorem sb_retarget (b : Nat) (q src dst : NodeId) : KeepsSB b (retarget q src dst) := by
  intro c w0 w hH hw
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sb_getNode b q c w0 w hH hw) ?_
  intro n v hv
  split
  · exact sb_putNode b q _ c w0 v hH hv
  · rw [writerWP_pure]; exact hv

theorem sb_unlink (b : Nat) (x : NodeId) : KeepsSB b (unlink x) := by
  intro c w0 w hH hw
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sb_getNode b x c w0 w hH hw) ?_
  intro n v hv
  split
  · exact sb_putNode b x _ c w0 v hH hv
  · rw [writerWP_pure]; exact hv

theorem sb_sibling (b : Nat) (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsSB b (sibling p pn i inner) := by
  intro c w0 w hH hw
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · simp only [writerWP_bind]
    refine writerWP_mono (sb_getNode b _ c w0 w hH hw) ?_
    intro n v hv
    split
    · exact writerWP_throw _ _ _ _
    · rw [writerWP_pure]; exact hv

set_option maxHeartbeats 2000000 in
/-- `sb_handleFullWith` for a node x below b, on the path or not. -/
theorem sb_handleFullWithX (b : Nat) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w0 w : W) (hH : c.p.H < b) (hw : SBInv c.p b w0 w) (hpb : PathBelowSB b w0)
    (hxb : x < w0.next ∧ ∀ g h, (x, g, h) ∈ w0.gh → h < b)
    (hup : ∀ e, depth = e + 1 → ∀ q more v, SBInv c.p b w0 v →
      (∃ a', w0.path[e]? = some (a', q)) →
      WriterWP (up q more) c v (fun _ v' => SBInv c.p b w0 v')) :
    WriterWP (handleFullWith up depth x ins last compact) c w (fun _ v => SBInv c.p b w0 v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sb_getNode b x c w0 w hH hw) ?_
  intro n w1 hw1
  refine writerWP_mono (sb_ghOf b x c w0 w1 hH hw1) ?_
  rintro ⟨g, h⟩ w2 ⟨hw2, hm2⟩
  have hhb : h < b := by
    rcases hw2.2.2.2 x g h hm2 hxb.1 with h0 | h0
    · exact hxb.2 g h h0
    · omega
  refine writerWP_mono (kd_parentAt depth c w2) ?_
  rintro parent _ ⟨rfl, hpar0, hpar1⟩
  cases depth with
  | zero =>
    obtain rfl := hpar0 rfl
    clear hpar1 hup
    repeat' first
      | wpSimplify
      | sbCore
      | wpSplit
      | split
      | contradiction
  | succ e =>
    obtain ⟨a', q, rfl, hpe⟩ := hpar1 e rfl
    have hpe0 : w0.path[e]? = some (a', q) := by rw [← hw2.2.2.1]; exact hpe
    have hup' := hup e rfl
    clear hup
    repeat' first
      | wpSimplify
      | sbCore
      | (refine writerWP_mono (hup' q _ _ (by sbState) ⟨a', hpe0⟩) ?_; intro _ _ _)
      | wpSplit
      | split
      | contradiction

/-- `sb_appendKlongs` for a node x below b, on the path or not; the cascade
goes up the path above depth. -/
theorem sb_appendKlongsX (b : Nat) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (c : Ctx) (w0 w : W) (hH : c.p.H < b) (hw : SBInv c.p b w0 w) (hpb : PathBelowSB b w0)
    (hxb : x < w0.next ∧ ∀ g h, (x, g, h) ∈ w0.gh → h < b) :
    WriterWP (appendKlongs depth x ins) c w (fun _ v => SBInv c.p b w0 v) := by
  cases depth with
  | zero =>
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (sb_getNode b x c w0 w hH hw) ?_
    intro n v hv
    have hfin : ∀ cp, WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0")
        0 x ins (n.lastVersion c.i) cp) c v (fun _ u => SBInv c.p b w0 u) :=
      fun cp => sb_handleFullWithX b _ 0 x ins _ cp c w0 v hH hv hpb hxb (fun e he => by cases he)
    split
    · exact hfin false
    · split
      · exact hfin true
      · exact sb_addKeys b x ins c w0 v hH hv
  | succ d =>
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (sb_getNode b x c w0 w hH hw) ?_
    intro n v hv
    have hup : ∀ e, d + 1 = e + 1 → ∀ q more u, SBInv c.p b w0 u →
        (∃ a', w0.path[e]? = some (a', q)) →
        WriterWP ((fun q more => appendKlongs d q more) q more) c u (fun _ u' => SBInv c.p b w0 u') := by
      intro e he q more u hu hq
      cases he
      exact sb_appendKlongs b d q more c w0 u hH hu hpb hq
    have hfin : ∀ cp, WriterWP (handleFullWith (fun q more => appendKlongs d q more)
        (d + 1) x ins (n.lastVersion c.i) cp) c v (fun _ u => SBInv c.p b w0 u) :=
      fun cp => sb_handleFullWithX b _ (d + 1) x ins _ cp c w0 v hH hv hpb hxb hup
    split
    · exact hfin false
    · split
      · exact hfin true
      · exact sb_addKeys b x ins c w0 v hH hv

set_option maxHeartbeats 3200000 in
/-- The merge's parent, the path's node at depth: in place, or a full node's
replacement whose cascade goes up the path. -/
theorem sb_mergeParent (b : Nat) (p : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (c : Ctx) (w0 w : W) (hH : c.p.H < b)
    (hw : SBInv c.p b w0 w) (hpb : PathBelowSB b w0) (a : Option Nat)
    (hpx : w0.path[depth]? = some (a, p)) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w (fun _ v => SBInv c.p b w0 v) := by
  unfold mergeParent
  repeat' first
    | wpSimplify
    | sbCore
    | (refine writerWP_mono (sb_handleFull b depth p _ _ c w0 _ hH (by sbState) hpb a hpx) ?_;
       intro _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 6400000 in
/-- A merge of x, the path's node at depth d: every height stays at most b
when the path's nodes are below b. -/
theorem sb_merge (b : Nat) (x : NodeId) (d : Nat) (c : Ctx) (w0 w : W) (hH : c.p.H < b)
    (hw : SBInv c.p b w0 w) (hpb : PathBelowSB b w0) :
    WriterWP (merge x d) c w (fun _ v => SBInv c.p b w0 v) := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_pathNode (d - 1) c w) ?_
  rintro p w1 ⟨hw1, ap, hpp⟩
  subst w1
  have hpp0 : w0.path[d - 1]? = some (ap, p) := by rw [← hw.2.2.1]; exact hpp
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | sbUse2 (sb_note _ _)
    | sbCore
    | sbUse (sb_unlink _ _)
    | sbUse (sb_retarget _ _ _ _)
    | sbUse (sb_takenBack _ _)
    | sbUse (sb_sibling _ _ _ _ _)
    | (refine writerWP_mono (sb_ghOf b _ c w0 _ hH (by sbState)) ?_
       rintro ⟨_, _⟩ _ ⟨hsbv, hsbm⟩
       have := hsbv.1 _ _ _ hsbm)
    | (refine writerWP_mono (sb_mergeParent b p (d - 1) _ _ _ _ _ _ c w0 _ hH (by sbState) hpb ap
        hpp0) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction

/-- (B) for a merge: from every cached height at most m (and H at most m), with
the path's nodes cached, a merge leaves every cached height at most m + 1. -/
theorem seenHeight_merge {B : NodeId} {c : Ctx} {w : W} {m : Nat} (hb : Book B c w)
    (hs : SeenHeightBound m w) (hHm : c.p.H ≤ m)
    (hpg : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1))
    (x : NodeId) (d : Nat) :
    WriterWP (merge x d) c w (fun _ v => SeenHeightBound (m + 1) v) :=
  writerWP_mono (sb_merge (m + 1) x d c w w (by omega) (SBInv.refl (hs.mono (Nat.le_succ m)))
    (pathBelowSB_of hb hs hpg)) (fun _ _ h => h.1)

end SIS.Tree
