import SIS.Tree.MergeProtectedNode

namespace SIS.Tree

open SIS SIS.Check

/-- The old view lies below the transaction's first fresh id. -/
def ViewIdsBelow (base : NodeId) (v : View BVal) : Prop :=
  ∀ x n, v x = some n → x < base

/-- Every cached node, height tag and taken-back id lies below the next
fresh id. -/
def FreshCache (base : NodeId) (w : W) : Prop :=
  base ≤ w.next ∧ (∀ q ∈ w.nodes, q.1 < w.next) ∧
    (∀ q ∈ w.gh, q.1 < w.next) ∧ ∀ x ∈ w.taken, x < w.next

def KeepsFreshCache (base : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow base c.view → FreshCache base w →
    WriterWP f c w (fun _ v => FreshCache base v ∧ w.next ≤ v.next)

theorem freshCache_of_same (base : NodeId) (w v : W) (hw : FreshCache base w)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (ht : v.taken = w.taken)
    (hnext : w.next ≤ v.next) :
    FreshCache base v := by
  refine ⟨Nat.le_trans hw.1 hnext,?_,?_,?_⟩
  · intro q hq
    rw [hn] at hq
    exact Nat.lt_of_lt_of_le (hw.2.1 q hq) hnext
  · intro q hq
    rw [hg] at hq
    exact Nat.lt_of_lt_of_le (hw.2.2.1 q hq) hnext
  · intro x hx
    rw [ht] at hx
    exact Nat.lt_of_lt_of_le (hw.2.2.2 x hx) hnext

theorem freshCache_lookup_lt (base : NodeId) (w : W) (hw : FreshCache base w)
    (x : NodeId) (n : KNode) (hn : w.nodes.lookup x = some n) : x < w.next := by
  obtain ⟨pre,post,he,_⟩ := List.lookup_eq_some_iff.mp hn
  have hm : (x,n) ∈ w.nodes := by rw [he]; simp
  exact hw.2.1 _ hm

theorem writerWP_getNode_freshCache (base x : NodeId) (c : Ctx) (w : W)
    (hv : ViewIdsBelow base c.view) (hw : FreshCache base w) :
    WriterWP (getNode x) c w (fun _ v =>
      FreshCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  unfold getNode
  simp only [writerWP_bind,writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw,Nat.le_refl _,freshCache_lookup_lt base w hw x n hn⟩
  · simp only [writerWP_bind,writerWP_read]
    split
    · rename_i n hn
      split
      · exact writerWP_throw _ _ _ _
      · have hx : x < w.next := Nat.lt_of_lt_of_le (hv x n hn) hw.1
        simp only [writerWP_bind,writerWP_set,writerWP_pure]
        refine ⟨⟨hw.1,?_,?_,hw.2.2.2⟩,Nat.le_refl _,hx⟩
        · intro q hq
          simp only [List.mem_append,List.mem_singleton] at hq
          rcases hq with hq | rfl
          · exact hw.2.1 q hq
          · exact hx
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hx
          · exact hw.2.2.1 q hq
    · exact writerWP_throw _ _ _ _

theorem writerWP_of_freshCache {α : Type} {f : M α} (base : NodeId)
    (hf : KeepsFreshCache base f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hv : ViewIdsBelow base c.view) (hw : FreshCache base w)
    (hp : ∀ r v, FreshCache base v → w.next ≤ v.next → post r v) :
    WriterWP f c w post := by
  exact writerWP_mono (hf c w hv hw) (fun r v h => hp r v h.1 h.2)

theorem upsert_ids_below (nodes : List (NodeId × KNode)) (bound x : NodeId) (n : KNode)
    (hn : ∀ q ∈ nodes, q.1 < bound) (hx : x < bound) :
    ∀ q ∈ upsert nodes x n, q.1 < bound := by
  unfold upsert
  split
  · intro q hq
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hq
    split at he
    · cases he
      exact hx
    · cases he
      exact hn _ ha
  · intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hn q hq
    · exact hx

theorem writerWP_putNode_freshCache (base x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hw : FreshCache base w) (hx : x < w.next) :
    WriterWP (putNode x n) c w (fun _ v => FreshCache base v ∧ w.next ≤ v.next) := by
  simp only [putNode,writerWP_modify]
  exact ⟨⟨hw.1,upsert_ids_below w.nodes w.next x n hw.2.1 hx,hw.2.2⟩,Nat.le_refl _⟩

theorem writerWP_fresh_freshCache (base : NodeId) (c : Ctx) (w : W)
    (hw : FreshCache base w) :
    WriterWP fresh c w (fun x v =>
      FreshCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  simp only [fresh,writerWP_bind,writerWP_get,writerWP_set,writerWP_pure]
  exact ⟨freshCache_of_same base w _ hw rfl rfl rfl (by simp),by simp,by simp⟩

theorem writerWP_newKey_freshCache (base g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hw : FreshCache base w) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      FreshCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  unfold newKey
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_mono (writerWP_fresh_freshCache base c w hw) ?_
  rintro x v ⟨hv,hnext,hx⟩
  split <;> wpSimplify
  all_goals
    refine ⟨⟨hv.1,?_,?_,hv.2.2.2⟩,hnext,hx⟩
    · intro q hq
      simp only [List.mem_append,List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hv.2.1 q hq
      · exact hx
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hx
      · exact hv.2.2.1 q hq

theorem writerWP_takenBack_freshCache (base x : NodeId) (c : Ctx) (w : W)
    (hw : FreshCache base w) (hx : x < w.next) :
    WriterWP (takenBack x) c w (fun _ v => FreshCache base v ∧ w.next ≤ v.next) := by
  simp only [takenBack,writerWP_modify]
  refine ⟨⟨hw.1,hw.2.1,hw.2.2.1,?_⟩,Nat.le_refl _⟩
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hw.2.2.2 y hy

macro "frState" : tactic => `(tactic| first
  | assumption
  | (grind [FreshCache]))

macro "frUse " base:term " using " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_freshCache $base $h _ _ _ ?frView ?frState ?frPost)
  case frView => assumption
  case frState => frState
  intro _ _ _ _))

macro "frFinish" : tactic => `(tactic| (
  (with_unfolding_none refine And.intro ?frFinal ?frNext)
  case frFinal => frState
  case frNext =>
    try dsimp only at *
    omega))

macro "frLoad " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_getNode_freshCache $base _ _ _ ?frView ?frState) ?frPost)
  case frView => assumption
  case frState => frState
  rintro _ _ ⟨_,_,_⟩))

macro "frCreate " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_newKey_freshCache $base _ _ _ _ _ _ ?frState) ?frPost)
  case frState => frState
  rintro _ _ ⟨_,_,_⟩))

macro "frPut " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_putNode_freshCache $base _ _ _ _ ?frState ?frId) ?frPost)
  case frState => frState
  case frId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "frTake " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_takenBack_freshCache $base _ _ _ ?frState ?frId) ?frPost)
  case frState => frState
  case frId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "frNeutral " bound:term : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,writerWP_set,
        writerWP_modify,note,fresh,newValue,setMadeFor,replacedBy,takenBack,pathClear,
        pathAdd,pathSize,pathNode,klongAt,parentAt,newSuperRoot,findRoot]
    | exact writerWP_throw _ _ _ _
    | frLoad $bound
    | frPut $bound
    | wpSplit
    | split
    | frFinish
    | contradiction))

theorem freshCache_note {base : NodeId} (s : String) : KeepsFreshCache base (note s) := by frNeutral base
theorem freshCache_fresh {base : NodeId} : KeepsFreshCache base fresh := by frNeutral base
theorem freshCache_newValue {base : NodeId} (h : Nat) : KeepsFreshCache base (newValue h) := by frNeutral base
theorem freshCache_setMadeFor {base : NodeId} (x : NodeId) (old : Option NodeId) : KeepsFreshCache base (setMadeFor x old) := by frNeutral base
theorem freshCache_replacedBy {base : NodeId} (x : NodeId) : KeepsFreshCache base (replacedBy x) := by frNeutral base
theorem freshCache_pathClear {base : NodeId} : KeepsFreshCache base pathClear := by frNeutral base
theorem freshCache_pathAdd {base : NodeId} (cv : Option Nat) (x : NodeId) : KeepsFreshCache base (pathAdd cv x) := by frNeutral base
theorem freshCache_pathSize {base : NodeId} : KeepsFreshCache base pathSize := by frNeutral base
theorem freshCache_pathNode {base : NodeId} (d : Nat) : KeepsFreshCache base (pathNode d) := by frNeutral base
theorem freshCache_klongAt {base : NodeId} (d : Nat) : KeepsFreshCache base (klongAt d) := by frNeutral base
theorem freshCache_parentAt {base : NodeId} (d : Nat) : KeepsFreshCache base (parentAt d) := by frNeutral base
theorem freshCache_newSuperRoot {base : NodeId} (x : NodeId) : KeepsFreshCache base (newSuperRoot x) := by frNeutral base
theorem freshCache_findRoot {base : NodeId} : KeepsFreshCache base findRoot := by frNeutral base

theorem freshCache_addKeys {base : NodeId} (x : NodeId) (ins : List (Nat × NodeId)) : KeepsFreshCache base (addKeys x ins) := by
  intro c w hv hw
  unfold addKeys
  repeat' first | wpSimplify | frLoad base | frPut base | frFinish

theorem freshCache_foldlM {base : NodeId} {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsFreshCache base (f b a)) : KeepsFreshCache base (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hview hw; simpa only [List.foldlM_nil,writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons a xs ih =>
    intro c w hview hw
    rw [List.foldlM_cons,writerWP_bind]
    refine writerWP_mono (hf init a c w hview hw) ?_
    rintro b v ⟨hv,hs⟩
    refine writerWP_mono (ih b c v hview hv) ?_
    rintro r u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩

theorem freshCache_forIn {base : NodeId} {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsFreshCache base (f a b)) :
    KeepsFreshCache base (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hview hw; simpa only [List.forIn_nil,writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons a xs ih =>
    intro c w hview hw
    rw [List.forIn_cons,writerWP_bind]
    refine writerWP_mono (hf a init c w hview hw) ?_
    rintro step v ⟨hv,hs⟩
    cases step with
    | done b => simpa only [writerWP_pure] using And.intro hv hs
    | yield b =>
      refine writerWP_mono (ih b c v hview hv) ?_
      rintro r u ⟨hu,ht⟩
      exact ⟨hu,Nat.le_trans hs ht⟩

theorem freshCache_ghOf {base : NodeId} (x : NodeId) : KeepsFreshCache base (ghOf x) := by
  intro c w hview hw
  unfold ghOf
  repeat' first | wpSimplify | frLoad base | frFinish | exact writerWP_throw _ _ _ _ | split

macro "frCore " bound:term : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | frLoad $bound
  | frUse $bound using (freshCache_ghOf _)
  | frCreate $bound
  | frPut $bound
  | frUse $bound using (freshCache_note _)
  | frUse $bound using freshCache_fresh
  | frUse $bound using (freshCache_newValue _)
  | frUse $bound using (freshCache_setMadeFor _ _)
  | frUse $bound using (freshCache_replacedBy _)
  | frTake $bound
  | frUse $bound using freshCache_pathClear
  | frUse $bound using (freshCache_pathAdd _ _)
  | frUse $bound using freshCache_pathSize
  | frUse $bound using (freshCache_pathNode _)
  | frUse $bound using (freshCache_klongAt _)
  | frUse $bound using (freshCache_parentAt _)
  | frUse $bound using (freshCache_newSuperRoot _)
  | frUse $bound using freshCache_findRoot
  | frUse $bound using (freshCache_addKeys _ _)
  | frFinish)

macro "frFoldWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_freshCache $bound (freshCache_foldlM _ _ _ ?frBody) _ _ _ ?frView ?frState ?frPost)
  case frBody =>
    intro b a c w hview hw
    repeat' first
      | wpSimplify
      | frCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case frView => assumption
  case frState => frState
  intro _ _ _ _))

macro "frFold " bound:term : tactic => `(tactic| frFoldWith $bound using fail)

theorem freshCache_replaceOrAdd {base : NodeId} (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsFreshCache base (replaceOrAdd last ins) := by
  intro c w hview hw
  unfold replaceOrAdd
  repeat' first
    | wpSimplify
    | frCore base
    | frFold base
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem freshCache_handleFullWith {base : NodeId} (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsFreshCache base (up q more)) :
    KeepsFreshCache base (handleFullWith up depth x ins last compact) := by
  intro c w hview hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | frCore base
    | frFold base
    | frUse base using (freshCache_replaceOrAdd _ _)
    | frUse base using (hup _ _)
    | wpSplit
    | split
    | contradiction

theorem freshCache_throw {base : NodeId} {α : Type} (e : String) : KeepsFreshCache base (throw e : M α) := by
  intro c w hview hw
  exact writerWP_throw _ _ _ _

theorem freshCache_appendKlongs {base : NodeId} (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsFreshCache base (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | frCore base
      | frUse base using (freshCache_handleFullWith _ _ _ _ _ _ (fun _ _ => freshCache_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | frCore base
      | frUse base using (freshCache_handleFullWith _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem freshCache_handleFull {base : NodeId} (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsFreshCache base (handleFull depth x last compact) := by
  unfold handleFull
  refine freshCache_handleFullWith _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact freshCache_throw _
  | succ d => exact freshCache_appendKlongs _ _ _

theorem freshCache_descendLte {base : NodeId} (cv fuel : Nat) (x : NodeId) :
    KeepsFreshCache base (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact freshCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | frCore base
      | frUse base using (ih _)
      | wpSplit
      | split
      | contradiction

macro "frAppend " bound:term : tactic => `(tactic| first
  | frUse $bound using (freshCache_handleFull _ _ _ _)
  | frUse $bound using (freshCache_appendKlongs _ _ _)
  | frUse $bound using (freshCache_descendLte _ _ _))

theorem freshCache_descendToSegmentRoot {base : NodeId} (key : Key) (segment : Nat) :
    KeepsFreshCache base (descendToSegmentRoot key segment) := by
  intro c w hview hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | frCore base
    | frFoldWith base using (frAppend base)
    | frAppend base
    | wpSplit
    | split
    | contradiction

macro "frDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem freshCache_appendDeleteKlong {base : NodeId} (x : NodeId) (depth cv : Nat) : KeepsFreshCache base (appendDeleteKlong x depth cv) := by
  intro c w hview hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem freshCache_emptyKeyNext {base : NodeId} (x : NodeId) (depth : Nat) : KeepsFreshCache base (emptyKeyNext x depth) := by
  intro c w hview hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem freshCache_collapseRoot {base : NodeId} (key : Key) (segment fuel : Nat) :
    KeepsFreshCache base (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact freshCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | frDeleteSimplify
      | frCore base
      | frAppend base
      | frUse base using (freshCache_descendToSegmentRoot _ _)
      | frUse base using ih
      | wpSplit
      | split
      | contradiction

theorem freshCache_descendHeight {base : NodeId} (cv h fuel : Nat) (x : NodeId) :
    KeepsFreshCache base (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact freshCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | frCore base
      | frUse base using (ih _)
      | wpSplit
      | split
      | contradiction

theorem freshCache_descendToHeight {base : NodeId} (key : Key) (g h : Nat) :
    KeepsFreshCache base (descendToHeight key g h) := by
  intro c w hview hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | frCore base
    | frUse base using (freshCache_descendToSegmentRoot _ _)
    | frUse base using (freshCache_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem freshCache_mergeParent {base : NodeId} (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsFreshCache base (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hview hw
  unfold mergeParent
  repeat' first
    | wpSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem freshCache_unlink {base : NodeId} (x : NodeId) : KeepsFreshCache base (unlink x) := by
  intro c w hview hw
  unfold unlink
  repeat' first
    | wpSimplify
    | frCore base
    | wpSplit
    | split
    | contradiction

theorem freshCache_retarget {base : NodeId} (q src dst : NodeId) : KeepsFreshCache base (retarget q src dst) := by
  intro c w hview hw
  unfold retarget
  repeat' first
    | wpSimplify
    | frCore base
    | wpSplit
    | split
    | contradiction

theorem writerWP_sibling_freshCache (base : NodeId) (q : NodeId) (pn : KNode)
    (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hview : ViewIdsBelow base c.view) (hw : FreshCache base w) :
    WriterWP (sibling q pn i inner) c w (fun r v =>
      FreshCache base v ∧ w.next ≤ v.next ∧ r.1 < v.next) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | frLoad base
    | exact writerWP_throw _ _ _ _
    | (solve |
        refine ⟨?_,?_,?_⟩
        · frState
        · omega
        · assumption)
    | split

macro "frSibling " bound:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_sibling_freshCache $bound _ _ _ _ _ _ ?frView ?frState) ?frPost)
  case frView => assumption
  case frState => frState
  rintro ⟨_,_⟩ _ ⟨_,_,_⟩))

set_option maxHeartbeats 2000000 in
theorem freshCache_merge {base : NodeId} (x : NodeId) (d : Nat) : KeepsFreshCache base (merge x d) := by
  intro c w hview hw
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | frCore base
    | frUse base using (freshCache_unlink _)
    | frUse base using (freshCache_retarget _ _ _)
    | frSibling base
    | frUse base using (freshCache_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem freshCache_mergeUp {base : NodeId} (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsFreshCache base (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact freshCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | frCore base
      | frUse base using (freshCache_descendToHeight _ _ _)
      | frUse base using (freshCache_merge _ _)
      | frUse base using (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem freshCache_climb {base : NodeId} (depth : Nat) : KeepsFreshCache base (climb depth) := by
  induction depth with
  | zero =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | frCore base
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | frDeleteSimplify
      | frCore base
      | frUse base using ih
      | wpSplit
      | split
      | contradiction

macro "frForWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_freshCache $bound (freshCache_forIn _ _ _ ?frBody) _ _ _ ?frView ?frState ?frPost)
  case frBody =>
    intro a b c w hview hw
    repeat' first
      | wpSimplify
      | frDeleteSimplify
      | frCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case frView => assumption
  case frState => frState
  intro _ _ _ _))

theorem freshCache_deleteUpward {base : NodeId} (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsFreshCache base (deleteUpward leaf depth cv key) := by
  intro c w hview hw
  unfold deleteUpward afterDelete
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frAppend base
    | frFold base
    | frForWith base using (frAppend base)
    | frUse base using (freshCache_climb _)
    | frUse base using (freshCache_mergeUp _ _ _ _ _)
    | frUse base using (freshCache_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem freshCache_setValue {base : NodeId} (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsFreshCache base (setValue segRoot cv key value) := by
  intro c w hview hw
  unfold setValue
  repeat' first
    | wpSimplify
    | frCore base
    | frAppend base
    | frUse base using (freshCache_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem freshCache_setNode {base : NodeId} (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsFreshCache base (setNode segRoot cv create) := by
  intro c w hview hw
  unfold setNode
  repeat' first
    | wpSimplify
    | frCore base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem freshCache_putSegs {base : NodeId} (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsFreshCache base (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact freshCache_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact freshCache_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hview hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | frCore base
        | frUse base using (freshCache_setNode _ _ _)
        | frUse base using (ih _)
        | wpSplit
        | split
        | contradiction

theorem freshCache_putKv {base : NodeId} (op : Tree.Op) : KeepsFreshCache base (putKv op) := by
  intro c w hview hw
  unfold putKv
  repeat' first
    | wpSimplify
    | frCore base
    | frUse base using (freshCache_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem freshCache_ops {base : NodeId} (ops : List Tree.Op) : KeepsFreshCache base (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hview hw; simpa only [List.mapM_nil, writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons op ops ih =>
    intro c w hview hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (freshCache_putKv op c w hview hw) ?_
    rintro noop v ⟨hv,hs⟩
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (ih c v hview hv) ?_
    rintro bs u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩

theorem viewIdsBelow_rootless (base : NodeId) (v : View BVal) (hv : ViewIdsBelow base v) :
    ViewIdsBelow base (rootless v) := by
  intro x n hx
  unfold rootless at hx
  split at hx
  · cases hx
  · exact hv x n hx

theorem viewIdsBelow_view (p : Params) (P : Struct BVal) (t : Time) (base : NodeId)
    (hfresh : ∀ q ∈ P, q.1 < base) : ViewIdsBelow base (view (treeSpec p) P t) := by
  intro x n hx
  unfold view at hx
  split at hx
  · cases hp : P.get? x with
    | none => simp [hp] at hx
    | some old =>
      obtain ⟨pre,post,he,_⟩ := List.lookup_eq_some_iff.mp hp
      have hm : (x,old) ∈ P := by rw [he]; simp
      exact hfresh _ hm
  · cases hx

end SIS.Tree
