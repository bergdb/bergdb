import SIS.Tree.MergeRootWrites

namespace SIS.Tree

open SIS SIS.Check

/-- Each space split can add at most one to the largest cached height. -/
def HeightSplitBound (p : Params) (w : W) : Prop :=
  SeenHeightBound (p.H + w.spaceSplits) w

def KeepsHeightSplitBound {α : Type} (f : M α) : Prop :=
  ∀ c w, HeightSplitBound c.p w →
    WriterWP f c w (fun _ v => HeightSplitBound c.p v ∧ w.spaceSplits ≤ v.spaceSplits)

theorem heightSplitBound_of_same (p : Params) (w v : W) (hw : HeightSplitBound p w)
    (hg : v.gh = w.gh) (hs : w.spaceSplits ≤ v.spaceSplits) : HeightSplitBound p v := by
  intro x g h hx
  rw [hg] at hx
  have hh := hw x g h hx
  omega

theorem heightSplitBound_inc (p : Params) (w : W) (hw : HeightSplitBound p w) :
    HeightSplitBound p {w with spaceSplits := w.spaceSplits+1} := by
  exact heightSplitBound_of_same p w _ hw rfl (by change w.spaceSplits ≤ w.spaceSplits+1; omega)

theorem writerWP_of_heightSplit {α : Type} {f : M α} (hf : KeepsHeightSplitBound f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : HeightSplitBound c.p w)
    (hp : ∀ r v, HeightSplitBound c.p v → w.spaceSplits ≤ v.spaceSplits → post r v) :
    WriterWP f c w post := by
  exact writerWP_mono (hf c w hw) (fun r v hv => hp r v hv.1 hv.2)

theorem heightSplit_getNode (x : NodeId) : KeepsHeightSplitBound (getNode x) := by
  intro c w hw
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simpa only [writerWP_pure] using And.intro hw (Nat.le_refl w.spaceSplits)
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, Nat.le_refl _⟩
        intro a b d hd
        simp only [List.mem_cons, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩ | hd
        · exact Nat.le_trans (heightOf_le c.p _) (Nat.le_add_right _ _)
        · exact hw a b d hd
    · exact writerWP_throw _ _ _ _

theorem writerWP_ghOf_heightSplit (x : NodeId) (c : Ctx) (w : W)
    (hw : HeightSplitBound c.p w) :
    WriterWP (ghOf x) c w (fun gh v =>
      HeightSplitBound c.p v ∧ w.spaceSplits ≤ v.spaceSplits ∧ gh.2 ≤ c.p.H+v.spaceSplits) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (heightSplit_getNode x c w hw) ?_
  rintro n v ⟨hv,hs⟩
  simp only [writerWP_get]
  split
  · rename_i gh hh
    simp only [writerWP_pure]
    exact ⟨hv,hs,hv x gh.1 gh.2 (gh_lookup_mem hh)⟩
  · exact writerWP_throw _ _ _ _

theorem writerWP_newKey_heightSplit (g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hw : HeightSplitBound c.p w) (hh : h ≤ c.p.H+w.spaceSplits) :
    WriterWP (newKey g h leaf ks) c w
      (fun _ v => HeightSplitBound c.p v ∧ w.spaceSplits ≤ v.spaceSplits) := by
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    refine ⟨?_, Nat.le_refl _⟩
    intro a b d hd
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl,rfl,rfl⟩ | hd
    · exact hh
    · exact hw a b d hd

macro "hsState" : tactic => `(tactic| first
  | assumption
  | (exact heightSplitBound_inc _ _ (by assumption))
  | (refine heightSplitBound_of_same _ _ _ ?_ ?_ ?_
     · assumption
     · rfl
     · try dsimp only
       omega))

macro "hsUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_heightSplit $h _ _ _ ?hsState ?hsPost)
  case hsState => hsState
  intro _ _ _ _))

macro "hsFinish" : tactic => `(tactic| (
  (with_unfolding_none refine And.intro ?hsFinal ?hsCounter)
  case hsFinal => hsState
  case hsCounter =>
    try dsimp only at *
    omega))

macro "hsNeutral" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
        writerWP_set, writerWP_modify, note, fresh, putNode, newValue,
        setMadeFor, replacedBy, takenBack, pathClear, pathAdd, pathSize, pathNode,
        klongAt, parentAt, newSuperRoot, findRoot, addKeys, replaceOrAdd]
    | exact writerWP_throw _ _ _ _
    | hsUse (heightSplit_getNode _)
    | wpSplit
    | split
    | hsFinish
    | contradiction))

theorem heightSplit_note (s : String) : KeepsHeightSplitBound (note s) := by hsNeutral
theorem heightSplit_fresh : KeepsHeightSplitBound fresh := by hsNeutral
theorem heightSplit_putNode (x : NodeId) (n : KNode) : KeepsHeightSplitBound (putNode x n) := by hsNeutral
theorem heightSplit_newValue (h : Nat) : KeepsHeightSplitBound (newValue h) := by hsNeutral
theorem heightSplit_setMadeFor (x : NodeId) (o : Option NodeId) : KeepsHeightSplitBound (setMadeFor x o) := by hsNeutral
theorem heightSplit_replacedBy (x : NodeId) : KeepsHeightSplitBound (replacedBy x) := by hsNeutral
theorem heightSplit_takenBack (x : NodeId) : KeepsHeightSplitBound (takenBack x) := by hsNeutral
theorem heightSplit_pathClear : KeepsHeightSplitBound pathClear := by hsNeutral
theorem heightSplit_pathAdd (c : Option Nat) (x : NodeId) : KeepsHeightSplitBound (pathAdd c x) := by hsNeutral
theorem heightSplit_pathSize : KeepsHeightSplitBound pathSize := by hsNeutral
theorem heightSplit_pathNode (d : Nat) : KeepsHeightSplitBound (pathNode d) := by hsNeutral
theorem heightSplit_klongAt (d : Nat) : KeepsHeightSplitBound (klongAt d) := by hsNeutral
theorem heightSplit_parentAt (d : Nat) : KeepsHeightSplitBound (parentAt d) := by hsNeutral
theorem heightSplit_newSuperRoot (x : NodeId) : KeepsHeightSplitBound (newSuperRoot x) := by hsNeutral
theorem heightSplit_findRoot : KeepsHeightSplitBound findRoot := by hsNeutral
theorem heightSplit_addKeys (x : NodeId) (ins : List (Nat × NodeId)) : KeepsHeightSplitBound (addKeys x ins) := by hsNeutral


theorem heightSplit_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsHeightSplitBound (f b a)) : KeepsHeightSplitBound (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil,writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons,writerWP_bind]
    refine writerWP_mono (hf init a c w hw) ?_
    rintro b v ⟨hv,hs⟩
    refine writerWP_mono (ih b c v hv) ?_
    rintro r u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩

theorem heightSplit_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsHeightSplitBound (f a b)) :
    KeepsHeightSplitBound (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.forIn_nil,writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons a xs ih =>
    intro c w hw
    rw [List.forIn_cons,writerWP_bind]
    refine writerWP_mono (hf a init c w hw) ?_
    rintro step v ⟨hv,hs⟩
    cases step with
    | done b => simpa only [writerWP_pure] using And.intro hv hs
    | yield b =>
      refine writerWP_mono (ih b c v hv) ?_
      rintro r u ⟨hu,ht⟩
      exact ⟨hu,Nat.le_trans hs ht⟩

macro "hsGH" : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_ghOf_heightSplit _ _ _ ?hsState) ?hsPost)
  case hsState => hsState
  rintro ⟨_,_⟩ _ ⟨_,_,_⟩))

macro "hsCreate" : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_newKey_heightSplit _ _ _ _ _ _ ?hsState ?hsHeight) ?hsPost)
  case hsState => hsState
  case hsHeight =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "hsCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | hsUse (heightSplit_getNode _)
  | hsGH
  | hsCreate
  | hsUse (heightSplit_note _)
  | hsUse heightSplit_fresh
  | hsUse (heightSplit_putNode _ _)
  | hsUse (heightSplit_newValue _)
  | hsUse (heightSplit_setMadeFor _ _)
  | hsUse (heightSplit_replacedBy _)
  | hsUse (heightSplit_takenBack _)
  | hsUse heightSplit_pathClear
  | hsUse (heightSplit_pathAdd _ _)
  | hsUse heightSplit_pathSize
  | hsUse (heightSplit_pathNode _)
  | hsUse (heightSplit_klongAt _)
  | hsUse (heightSplit_parentAt _)
  | hsUse (heightSplit_newSuperRoot _)
  | hsUse heightSplit_findRoot
  | hsUse (heightSplit_addKeys _ _)
  | hsFinish)

macro "hsFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_heightSplit (heightSplit_foldlM _ _ _ ?hsBody) _ _ _ ?hsState ?hsPost)
  case hsBody =>
    intro b a c w hw
    repeat' first
      | wpSimplify
      | hsCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case hsState => hsState
  intro _ _ _ _))

macro "hsFold" : tactic => `(tactic| hsFoldWith fail)

theorem heightSplit_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsHeightSplitBound (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first
    | wpSimplify
    | hsCore
    | hsFold
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem heightSplit_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsHeightSplitBound (up q more)) :
    KeepsHeightSplitBound (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | hsCore
    | hsFold
    | hsUse (heightSplit_replaceOrAdd _ _)
    | hsUse (hup _ _)
    | wpSplit
    | split
    | contradiction


theorem heightSplit_throw {α : Type} (e : String) : KeepsHeightSplitBound (throw e : M α) := by
  intro c w hw
  exact writerWP_throw _ _ _ _

theorem heightSplit_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsHeightSplitBound (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | hsCore
      | hsUse (heightSplit_handleFullWith _ _ _ _ _ _ (fun _ _ => heightSplit_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | hsCore
      | hsUse (heightSplit_handleFullWith _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem heightSplit_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsHeightSplitBound (handleFull depth x last compact) := by
  unfold handleFull
  refine heightSplit_handleFullWith _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact heightSplit_throw _
  | succ d => exact heightSplit_appendKlongs _ _ _

theorem heightSplit_descendLte (cv fuel : Nat) (x : NodeId) :
    KeepsHeightSplitBound (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact heightSplit_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | hsCore
      | hsUse (ih _)
      | wpSplit
      | split
      | contradiction

macro "hsAppend" : tactic => `(tactic| first
  | hsUse (heightSplit_handleFull _ _ _ _)
  | hsUse (heightSplit_appendKlongs _ _ _)
  | hsUse (heightSplit_descendLte _ _ _))

theorem heightSplit_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsHeightSplitBound (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | hsCore
    | hsFoldWith hsAppend
    | hsAppend
    | wpSplit
    | split
    | contradiction

macro "hsDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem heightSplit_appendDeleteKlong (x : NodeId) (depth cv : Nat) : KeepsHeightSplitBound (appendDeleteKlong x depth cv) := by
  intro c w hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | hsDeleteSimplify
    | hsCore
    | hsAppend
    | wpSplit
    | split
    | contradiction

theorem heightSplit_emptyKeyNext (x : NodeId) (depth : Nat) : KeepsHeightSplitBound (emptyKeyNext x depth) := by
  intro c w hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | hsDeleteSimplify
    | hsCore
    | hsAppend
    | wpSplit
    | split
    | contradiction

theorem heightSplit_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsHeightSplitBound (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact heightSplit_throw _
  | succ fuel ih =>
    intro c w hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | hsDeleteSimplify
      | hsCore
      | hsAppend
      | hsUse (heightSplit_descendToSegmentRoot _ _)
      | hsUse ih
      | wpSplit
      | split
      | contradiction

theorem heightSplit_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsHeightSplitBound (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact heightSplit_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | hsCore
      | hsUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem heightSplit_descendToHeight (key : Key) (g h : Nat) :
    KeepsHeightSplitBound (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | hsCore
    | hsUse (heightSplit_descendToSegmentRoot _ _)
    | hsUse (heightSplit_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem heightSplit_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsHeightSplitBound (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hw
  unfold mergeParent
  repeat' first
    | wpSimplify
    | hsCore
    | hsAppend
    | wpSplit
    | split
    | contradiction

theorem heightSplit_unlink (x : NodeId) : KeepsHeightSplitBound (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first
    | wpSimplify
    | hsCore
    | wpSplit
    | split
    | contradiction

theorem heightSplit_retarget (q src dst : NodeId) : KeepsHeightSplitBound (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first
    | wpSimplify
    | hsCore
    | wpSplit
    | split
    | contradiction

theorem heightSplit_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) : KeepsHeightSplitBound (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first
    | wpSimplify
    | hsCore
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem heightSplit_merge (x : NodeId) (d : Nat) : KeepsHeightSplitBound (merge x d) := by
  intro c w hw
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | hsCore
    | hsUse (heightSplit_unlink _)
    | hsUse (heightSplit_retarget _ _ _)
    | hsUse (heightSplit_sibling _ _ _ _)
    | hsUse (heightSplit_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem heightSplit_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsHeightSplitBound (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact heightSplit_throw _
  | succ fuel ih =>
    intro c w hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | hsCore
      | hsUse (heightSplit_descendToHeight _ _ _)
      | hsUse (heightSplit_merge _ _)
      | hsUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem heightSplit_afterDelete (key : Key) (g h : Nat) : KeepsHeightSplitBound (afterDelete key g h) := by
  intro c w hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | hsCore
    | hsUse (heightSplit_mergeUp _ _ _ _ _)
    | hsUse (heightSplit_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem heightSplit_climb (depth : Nat) : KeepsHeightSplitBound (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first
      | wpSimplify
      | hsCore
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | wpSimplify
      | hsDeleteSimplify
      | hsCore
      | hsUse ih
      | wpSplit
      | split
      | contradiction

macro "hsForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_heightSplit (heightSplit_forIn _ _ _ ?tagBody) _ _ _ ?tagState ?tagPost)
  case tagBody =>
    intro a b c w hw
    repeat' first
      | wpSimplify
      | hsDeleteSimplify
      | hsCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tagState => hsState
  intro _ _ _ _))

theorem heightSplit_segmentCount (path : List (Option Nat × NodeId)) (stop : Nat) :
    KeepsHeightSplitBound ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  intro c w hw
  hsFold
  hsFinish

theorem heightSplit_unlinkLoop (depth tt : Nat) (js : List Nat) :
    KeepsHeightSplitBound (forIn js () (fun j _ => do
      let x ← pathNode (depth - j)
      let xn ← getNode x
      if xn.firstTime == some tt then
        let q ← pathNode (depth - j - 1)
        let k ← klongAt (depth - j)
        takeBack x q k
        pure (ForInStep.yield ())
      else
        note "up.unlink"
        unlink x
        pure (ForInStep.yield ()))) := by
  intro c w hw
  hsForWith hsAppend
  hsFinish

theorem heightSplit_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsHeightSplitBound (deleteUpward leaf depth cv key) := by
  intro c w hw
  unfold deleteUpward afterDelete
  repeat' first
    | wpSimplify
    | hsDeleteSimplify
    | hsCore
    | hsAppend
    | hsFold
    | hsForWith hsAppend
    | hsUse (heightSplit_climb _)
    | hsUse (heightSplit_mergeUp _ _ _ _ _)
    | hsUse (heightSplit_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem heightSplit_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsHeightSplitBound (setValue segRoot cv key value) := by
  intro c w hw
  unfold setValue
  repeat' first
    | wpSimplify
    | hsCore
    | hsAppend
    | hsUse (heightSplit_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem heightSplit_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsHeightSplitBound (setNode segRoot cv create) := by
  intro c w hw
  unfold setNode
  repeat' first
    | wpSimplify
    | hsCore
    | hsAppend
    | wpSplit
    | split
    | contradiction

theorem heightSplit_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsHeightSplitBound (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact heightSplit_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact heightSplit_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | hsCore
        | hsUse (heightSplit_setNode _ _ _)
        | hsUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem heightSplit_putKv (op : Tree.Op) : KeepsHeightSplitBound (putKv op) := by
  intro c w hw
  unfold putKv
  repeat' first
    | wpSimplify
    | hsCore
    | hsUse (heightSplit_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem heightSplit_ops (ops : List Tree.Op) : KeepsHeightSplitBound (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hw; simpa only [List.mapM_nil, writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons op ops ih =>
    intro c w hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (heightSplit_putKv op c w hw) ?_
    rintro noop v ⟨hv,hs⟩
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (ih c v hv) ?_
    rintro bs u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩


/-- Node heights read from the prior view are at most H; every additional
height seen by the writer is accounted for by a space split. -/
theorem execW_heightSplitBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) : HeightSplitBound p w := by
  unfold execW runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => simp [hz] at h
  | some z =>
    simp only [hz] at h
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at h
    | ok top =>
      simp only [ht] at h
      have hr := boundsOK_ok p _ bs w h
      have hw : HeightSplitBound p {next := tx.base, top := top} := by
        intro x g height hx
        simp at hx
      exact (heightSplit_ops tx.ops {p := p,i := i,view := rootless v}
        {next := tx.base,top := top} hw bs w hr).1

theorem execW_maxSeenHeight_le_splits (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) :
    maxSeenHeight w.gh ≤ p.H+w.spaceSplits := by
  exact maxSeenHeight_le w.gh _ (execW_heightSplitBound p tx i v bs w h)

/-- A parameter-and-counter bound, independent of key order and freshness. -/
theorem execW_mergeSpaceSplitBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) :
    w.merges ≤ deletesOf tx bs * (p.H+w.spaceSplits) := by
  exact execW_mergeRootHeightBound_of_cache p tx i v bs w _ h
    (execW_heightSplitBound p tx i v bs w h)

/-- At most one space split is a sufficient, independently counted premise
for H+1. It is not asserted here for all sorted transactions. -/
theorem execW_mergeOpBound_of_oneSpaceSplit (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) (hs : w.spaceSplits ≤ 1) :
    w.merges ≤ deletesOf tx bs * (p.H+1) := by
  exact Nat.le_trans (execW_mergeSpaceSplitBound p tx i v bs w h)
    (Nat.mul_le_mul_left _ (by omega))

/-- Both unconditional bounds are available, so their smaller factor is
sufficient for every successful transaction. -/
theorem execW_mergeFuelSeenHeightBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) :
    w.merges ≤ deletesOf tx bs * min p.fuel (maxSeenHeight w.gh) := by
  by_cases hc : p.fuel ≤ maxSeenHeight w.gh
  · rw [Nat.min_eq_left hc]
    exact execW_mergeFuelBound p tx i v bs w h
  · rw [Nat.min_eq_right (by omega)]
    exact execW_mergeRootSeenHeightBound p tx i v bs w h

end SIS.Tree
