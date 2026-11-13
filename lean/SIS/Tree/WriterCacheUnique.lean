import SIS.Tree.FreshCache
import SIS.Tree.WriterCache
import SIS.Tree.ExportHistory

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every cache id occurs exactly once, independently of klong contents. -/
def CacheUnique (w : W) : Prop := (w.nodes.map Prod.fst).Nodup

def UniqueCache (base : NodeId) (w : W) : Prop := FreshCache base w ∧ CacheUnique w

def KeepsUniqueCache (base : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow base c.view → UniqueCache base w →
    WriterWP f c w (fun _ v => UniqueCache base v ∧ w.next ≤ v.next)

theorem uniqueCache_of_same (base : NodeId) (w v : W) (hw : UniqueCache base w)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (ht : v.taken = w.taken)
    (hnext : w.next ≤ v.next) : UniqueCache base v :=
  ⟨freshCache_of_same base w v hw.1 hn hg ht hnext, by
    simpa only [CacheUnique, hn] using hw.2⟩

theorem unique_ids_append (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hu : (ns.map Prod.fst).Nodup) (hx : ns.lookup x = none) :
    ((ns ++ [(x,n)]).map Prod.fst).Nodup := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨hu, by simp, ?_⟩
  intro a ha b hb hab
  have hb' : b = x := List.mem_singleton.mp hb
  obtain ⟨q, hq, hqa⟩ := List.mem_map.mp ha
  have hh := List.lookup_eq_none_iff.mp hx q hq
  simp only [bne_iff_ne] at hh
  exact hh (by omega)

theorem upsert_unique (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hu : (ns.map Prod.fst).Nodup) : ((upsert ns x n).map Prod.fst).Nodup := by
  unfold upsert
  split
  · have hmap : ((ns.map (fun q => if q.1 == x then (x,n) else q)).map Prod.fst) =
        ns.map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro q hq
      dsimp only [Function.comp_def]
      split
      · rename_i he
        have hx : q.1 = x := by simpa using he
        exact hx.symm
      · rfl
    rwa [hmap]
  · rename_i hno
    have hno' : ns.any (fun q => q.1 == x) = false := by
      cases he : ns.any (fun q => q.1 == x) <;> simp_all
    apply unique_ids_append ns x n hu
    apply List.lookup_eq_none_iff.mpr
    intro q hq
    have h := List.any_eq_false.mp hno' q hq
    have hxq : q.1 ≠ x := by simpa only [beq_iff_eq] using h
    simpa only [bne_iff_ne] using Ne.symm hxq

theorem writerWP_getNode_uniqueCache (base x : NodeId) (c : Ctx) (w : W)
    (hv : ViewIdsBelow base c.view) (hw : UniqueCache base w) :
    WriterWP (getNode x) c w (fun _ v =>
      UniqueCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  have huniq : WriterWP (getNode x) c w (fun _ v => CacheUnique v) := by
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw.2
    · rename_i hn
      simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact unique_ids_append w.nodes x _ hw.2 hn
      · exact writerWP_throw _ _ _ _
  intro r v he
  have hf := writerWP_getNode_freshCache base x c w hv hw.1 r v he
  exact ⟨⟨hf.1, huniq r v he⟩, hf.2⟩

theorem writerWP_of_uniqueCache {α : Type} {f : M α} (base : NodeId)
    (hf : KeepsUniqueCache base f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hv : ViewIdsBelow base c.view) (hw : UniqueCache base w)
    (hp : ∀ r v, UniqueCache base v → w.next ≤ v.next → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hv hw) (fun r v h => hp r v h.1 h.2)

theorem writerWP_putNode_uniqueCache (base x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hw : UniqueCache base w) (hx : x < w.next) :
    WriterWP (putNode x n) c w (fun _ v => UniqueCache base v ∧ w.next ≤ v.next) := by
  intro r v he
  have hf := writerWP_putNode_freshCache base x n c w hw.1 hx r v he
  have hu : WriterWP (putNode x n) c w (fun _ v => CacheUnique v) := by
    simp only [putNode, writerWP_modify]
    exact upsert_unique w.nodes x n hw.2
  exact ⟨⟨hf.1, hu r v he⟩, hf.2⟩

theorem writerWP_newKey_uniqueCache (base g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hw : UniqueCache base w) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      UniqueCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  have hx : w.nodes.lookup w.next = none := by
    apply List.lookup_eq_none_iff.mpr
    intro q hq
    have hl := hw.1.2.1 q hq
    simp only [bne_iff_ne]
    omega
  have hu : WriterWP (newKey g h leaf ks) c w (fun _ v => CacheUnique v) := by
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;> exact unique_ids_append w.nodes w.next _ hw.2 hx
  intro r v he
  have hf := writerWP_newKey_freshCache base g h leaf ks c w hw.1 r v he
  exact ⟨⟨hf.1, hu r v he⟩, hf.2⟩

theorem writerWP_takenBack_uniqueCache (base x : NodeId) (c : Ctx) (w : W)
    (hw : UniqueCache base w) (hx : x < w.next) :
    WriterWP (takenBack x) c w (fun _ v => UniqueCache base v ∧ w.next ≤ v.next) := by
  intro r v he
  have hf := writerWP_takenBack_freshCache base x c w hw.1 hx r v he
  have hu : WriterWP (takenBack x) c w (fun _ v => CacheUnique v) := by
    simpa only [takenBack, writerWP_modify, CacheUnique] using hw.2
  exact ⟨⟨hf.1, hu r v he⟩, hf.2⟩

macro "ucState" : tactic => `(tactic| first
  | assumption
  | (grind [UniqueCache, CacheUnique, FreshCache]))

macro "ucUse " base:term " using " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_uniqueCache $base $h _ _ _ ?ucView ?ucState ?ucPost)
  case ucView => assumption
  case ucState => ucState
  intro _ _ _ _))

macro "ucFinish" : tactic => `(tactic| (
  (with_unfolding_none refine And.intro ?ucFinal ?ucNext)
  case ucFinal => ucState
  case ucNext =>
    try dsimp only at *
    omega))

macro "ucLoad " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_getNode_uniqueCache $base _ _ _ ?ucView ?ucState) ?ucPost)
  case ucView => assumption
  case ucState => ucState
  rintro _ _ ⟨_,_,_⟩))

macro "ucCreate " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_newKey_uniqueCache $base _ _ _ _ _ _ ?ucState) ?ucPost)
  case ucState => ucState
  rintro _ _ ⟨_,_,_⟩))

macro "ucPut " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_putNode_uniqueCache $base _ _ _ _ ?ucState ?ucId) ?ucPost)
  case ucState => ucState
  case ucId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "ucTake " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_takenBack_uniqueCache $base _ _ _ ?ucState ?ucId) ?ucPost)
  case ucState => ucState
  case ucId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "ucNeutral " bound:term : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,writerWP_set,
        writerWP_modify,note,fresh,newValue,setMadeFor,replacedBy,takenBack,pathClear,
        pathAdd,pathSize,pathNode,klongAt,parentAt,newSuperRoot,findRoot]
    | exact writerWP_throw _ _ _ _
    | ucLoad $bound
    | ucPut $bound
    | wpSplit
    | split
    | ucFinish
    | contradiction))

theorem uniqueCache_note {base : NodeId} (s : String) : KeepsUniqueCache base (note s) := by ucNeutral base
theorem uniqueCache_fresh {base : NodeId} : KeepsUniqueCache base fresh := by ucNeutral base
theorem uniqueCache_newValue {base : NodeId} (h : Nat) : KeepsUniqueCache base (newValue h) := by ucNeutral base
theorem uniqueCache_setMadeFor {base : NodeId} (x : NodeId) (old : Option NodeId) : KeepsUniqueCache base (setMadeFor x old) := by ucNeutral base
theorem uniqueCache_replacedBy {base : NodeId} (x : NodeId) : KeepsUniqueCache base (replacedBy x) := by ucNeutral base
theorem uniqueCache_pathClear {base : NodeId} : KeepsUniqueCache base pathClear := by ucNeutral base
theorem uniqueCache_pathAdd {base : NodeId} (cv : Option Nat) (x : NodeId) : KeepsUniqueCache base (pathAdd cv x) := by ucNeutral base
theorem uniqueCache_pathSize {base : NodeId} : KeepsUniqueCache base pathSize := by ucNeutral base
theorem uniqueCache_pathNode {base : NodeId} (d : Nat) : KeepsUniqueCache base (pathNode d) := by ucNeutral base
theorem uniqueCache_klongAt {base : NodeId} (d : Nat) : KeepsUniqueCache base (klongAt d) := by ucNeutral base
theorem uniqueCache_parentAt {base : NodeId} (d : Nat) : KeepsUniqueCache base (parentAt d) := by ucNeutral base
theorem uniqueCache_newSuperRoot {base : NodeId} (x : NodeId) : KeepsUniqueCache base (newSuperRoot x) := by ucNeutral base
theorem uniqueCache_findRoot {base : NodeId} : KeepsUniqueCache base findRoot := by ucNeutral base

theorem uniqueCache_addKeys {base : NodeId} (x : NodeId) (ins : List (Nat × NodeId)) : KeepsUniqueCache base (addKeys x ins) := by
  intro c w hv hw
  unfold addKeys
  repeat' first | wpSimplify | ucLoad base | ucPut base | ucFinish

theorem uniqueCache_foldlM {base : NodeId} {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsUniqueCache base (f b a)) : KeepsUniqueCache base (xs.foldlM f init) := by
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

theorem uniqueCache_forIn {base : NodeId} {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsUniqueCache base (f a b)) :
    KeepsUniqueCache base (forIn xs init f) := by
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

theorem uniqueCache_ghOf {base : NodeId} (x : NodeId) : KeepsUniqueCache base (ghOf x) := by
  intro c w hview hw
  unfold ghOf
  repeat' first | wpSimplify | ucLoad base | ucFinish | exact writerWP_throw _ _ _ _ | split

macro "ucCore " bound:term : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | ucLoad $bound
  | ucUse $bound using (uniqueCache_ghOf _)
  | ucCreate $bound
  | ucPut $bound
  | ucUse $bound using (uniqueCache_note _)
  | ucUse $bound using uniqueCache_fresh
  | ucUse $bound using (uniqueCache_newValue _)
  | ucUse $bound using (uniqueCache_setMadeFor _ _)
  | ucUse $bound using (uniqueCache_replacedBy _)
  | ucTake $bound
  | ucUse $bound using uniqueCache_pathClear
  | ucUse $bound using (uniqueCache_pathAdd _ _)
  | ucUse $bound using uniqueCache_pathSize
  | ucUse $bound using (uniqueCache_pathNode _)
  | ucUse $bound using (uniqueCache_klongAt _)
  | ucUse $bound using (uniqueCache_parentAt _)
  | ucUse $bound using (uniqueCache_newSuperRoot _)
  | ucUse $bound using uniqueCache_findRoot
  | ucUse $bound using (uniqueCache_addKeys _ _)
  | ucFinish)

macro "ucFoldWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_uniqueCache $bound (uniqueCache_foldlM _ _ _ ?ucBody) _ _ _ ?ucView ?ucState ?ucPost)
  case ucBody =>
    intro b a c w hview hw
    repeat' first
      | wpSimplify
      | ucCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ucView => assumption
  case ucState => ucState
  intro _ _ _ _))

macro "ucFold " bound:term : tactic => `(tactic| ucFoldWith $bound using fail)

theorem uniqueCache_replaceOrAdd {base : NodeId} (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsUniqueCache base (replaceOrAdd last ins) := by
  intro c w hview hw
  unfold replaceOrAdd
  repeat' first
    | wpSimplify
    | ucCore base
    | ucFold base
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem uniqueCache_handleFullWith {base : NodeId} (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsUniqueCache base (up q more)) :
    KeepsUniqueCache base (handleFullWith up depth x ins last compact) := by
  intro c w hview hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | ucCore base
    | ucFold base
    | ucUse base using (uniqueCache_replaceOrAdd _ _)
    | ucUse base using (hup _ _)
    | wpSplit
    | split
    | contradiction


theorem uniqueCache_throw {base : NodeId} {α : Type} (e : String) : KeepsUniqueCache base (throw e : M α) := by
  intro c w hview hw
  exact writerWP_throw _ _ _ _

theorem uniqueCache_appendKlongs {base : NodeId} (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsUniqueCache base (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ucCore base
      | ucUse base using (uniqueCache_handleFullWith _ _ _ _ _ _ (fun _ _ => uniqueCache_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ucCore base
      | ucUse base using (uniqueCache_handleFullWith _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem uniqueCache_handleFull {base : NodeId} (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsUniqueCache base (handleFull depth x last compact) := by
  unfold handleFull
  refine uniqueCache_handleFullWith _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact uniqueCache_throw _
  | succ d => exact uniqueCache_appendKlongs _ _ _

theorem uniqueCache_descendLte {base : NodeId} (cv fuel : Nat) (x : NodeId) :
    KeepsUniqueCache base (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact uniqueCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | ucCore base
      | ucUse base using (ih _)
      | wpSplit
      | split
      | contradiction

macro "ucAppend " bound:term : tactic => `(tactic| first
  | ucUse $bound using (uniqueCache_handleFull _ _ _ _)
  | ucUse $bound using (uniqueCache_appendKlongs _ _ _)
  | ucUse $bound using (uniqueCache_descendLte _ _ _))

theorem uniqueCache_descendToSegmentRoot {base : NodeId} (key : Key) (segment : Nat) :
    KeepsUniqueCache base (descendToSegmentRoot key segment) := by
  intro c w hview hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | ucCore base
    | ucFoldWith base using (ucAppend base)
    | ucAppend base
    | wpSplit
    | split
    | contradiction

macro "ucDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem uniqueCache_appendDeleteKlong {base : NodeId} (x : NodeId) (depth cv : Nat) : KeepsUniqueCache base (appendDeleteKlong x depth cv) := by
  intro c w hview hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | ucDeleteSimplify
    | ucCore base
    | ucAppend base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_emptyKeyNext {base : NodeId} (x : NodeId) (depth : Nat) : KeepsUniqueCache base (emptyKeyNext x depth) := by
  intro c w hview hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | ucDeleteSimplify
    | ucCore base
    | ucAppend base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_collapseRoot {base : NodeId} (key : Key) (segment fuel : Nat) :
    KeepsUniqueCache base (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact uniqueCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | ucDeleteSimplify
      | ucCore base
      | ucAppend base
      | ucUse base using (uniqueCache_descendToSegmentRoot _ _)
      | ucUse base using ih
      | wpSplit
      | split
      | contradiction

theorem uniqueCache_descendHeight {base : NodeId} (cv h fuel : Nat) (x : NodeId) :
    KeepsUniqueCache base (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact uniqueCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | ucCore base
      | ucUse base using (ih _)
      | wpSplit
      | split
      | contradiction

theorem uniqueCache_descendToHeight {base : NodeId} (key : Key) (g h : Nat) :
    KeepsUniqueCache base (descendToHeight key g h) := by
  intro c w hview hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | ucCore base
    | ucUse base using (uniqueCache_descendToSegmentRoot _ _)
    | ucUse base using (uniqueCache_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem uniqueCache_mergeParent {base : NodeId} (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsUniqueCache base (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hview hw
  unfold mergeParent
  repeat' first
    | wpSimplify
    | ucCore base
    | ucAppend base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_unlink {base : NodeId} (x : NodeId) : KeepsUniqueCache base (unlink x) := by
  intro c w hview hw
  unfold unlink
  repeat' first
    | wpSimplify
    | ucCore base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_retarget {base : NodeId} (q src dst : NodeId) : KeepsUniqueCache base (retarget q src dst) := by
  intro c w hview hw
  unfold retarget
  repeat' first
    | wpSimplify
    | ucCore base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_sibling {base : NodeId} (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) : KeepsUniqueCache base (sibling q pn i inner) := by
  intro c w hview hw
  unfold sibling
  repeat' first
    | wpSimplify
    | ucCore base
    | wpSplit
    | split
    | contradiction

theorem writerWP_sibling_uniqueCache (base : NodeId) (q : NodeId) (pn : KNode)
    (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hview : ViewIdsBelow base c.view) (hw : UniqueCache base w) :
    WriterWP (sibling q pn i inner) c w (fun r v =>
      UniqueCache base v ∧ w.next ≤ v.next ∧ r.1 < v.next) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | ucLoad base
    | exact writerWP_throw _ _ _ _
    | (solve |
        refine ⟨?_,?_,?_⟩
        · ucState
        · omega
        · assumption)
    | split

macro "ucSibling " bound:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_sibling_uniqueCache $bound _ _ _ _ _ _ ?ucView ?ucState) ?ucPost)
  case ucView => assumption
  case ucState => ucState
  rintro ⟨_,_⟩ _ ⟨_,_,_⟩))

set_option maxHeartbeats 2000000 in
theorem uniqueCache_merge {base : NodeId} (x : NodeId) (d : Nat) : KeepsUniqueCache base (merge x d) := by
  intro c w hview hw
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | ucCore base
    | ucUse base using (uniqueCache_unlink _)
    | ucUse base using (uniqueCache_retarget _ _ _)
    | ucSibling base
    | ucUse base using (uniqueCache_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_mergeUp {base : NodeId} (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsUniqueCache base (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact uniqueCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | ucCore base
      | ucUse base using (uniqueCache_descendToHeight _ _ _)
      | ucUse base using (uniqueCache_merge _ _)
      | ucUse base using (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem uniqueCache_afterDelete {base : NodeId} (key : Key) (g h : Nat) : KeepsUniqueCache base (afterDelete key g h) := by
  intro c w hview hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | ucCore base
    | ucUse base using (uniqueCache_mergeUp _ _ _ _ _)
    | ucUse base using (uniqueCache_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_climb {base : NodeId} (depth : Nat) : KeepsUniqueCache base (climb depth) := by
  induction depth with
  | zero =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | ucCore base
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | ucDeleteSimplify
      | ucCore base
      | ucUse base using ih
      | wpSplit
      | split
      | contradiction

macro "ucForWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_uniqueCache $bound (uniqueCache_forIn _ _ _ ?ucBody) _ _ _ ?ucView ?ucState ?ucPost)
  case ucBody =>
    intro a b c w hview hw
    repeat' first
      | wpSimplify
      | ucDeleteSimplify
      | ucCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ucView => assumption
  case ucState => ucState
  intro _ _ _ _))

theorem uniqueCache_segmentCount {base : NodeId} (path : List (Option Nat × NodeId)) (stop : Nat) :
    KeepsUniqueCache base ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  intro c w hview hw
  ucFold base
  ucFinish

theorem uniqueCache_unlinkLoop {base : NodeId} (depth tt : Nat) (js : List Nat) :
    KeepsUniqueCache base (forIn js () (fun j _ => do
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
  intro c w hview hw
  ucForWith base using (ucAppend base)
  ucFinish

theorem uniqueCache_deleteUpward {base : NodeId} (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsUniqueCache base (deleteUpward leaf depth cv key) := by
  intro c w hview hw
  unfold deleteUpward afterDelete
  repeat' first
    | wpSimplify
    | ucDeleteSimplify
    | ucCore base
    | ucAppend base
    | ucFold base
    | ucForWith base using (ucAppend base)
    | ucUse base using (uniqueCache_climb _)
    | ucUse base using (uniqueCache_mergeUp _ _ _ _ _)
    | ucUse base using (uniqueCache_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_setValue {base : NodeId} (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsUniqueCache base (setValue segRoot cv key value) := by
  intro c w hview hw
  unfold setValue
  repeat' first
    | wpSimplify
    | ucCore base
    | ucAppend base
    | ucUse base using (uniqueCache_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_setNode {base : NodeId} (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsUniqueCache base (setNode segRoot cv create) := by
  intro c w hview hw
  unfold setNode
  repeat' first
    | wpSimplify
    | ucCore base
    | ucAppend base
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_putSegs {base : NodeId} (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsUniqueCache base (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact uniqueCache_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact uniqueCache_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hview hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | ucCore base
        | ucUse base using (uniqueCache_setNode _ _ _)
        | ucUse base using (ih _)
        | wpSplit
        | split
        | contradiction

theorem uniqueCache_putKv {base : NodeId} (op : Tree.Op) : KeepsUniqueCache base (putKv op) := by
  intro c w hview hw
  unfold putKv
  repeat' first
    | wpSimplify
    | ucCore base
    | ucUse base using (uniqueCache_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem uniqueCache_ops {base : NodeId} (ops : List Tree.Op) : KeepsUniqueCache base (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hview hw; simpa only [List.mapM_nil, writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons op ops ih =>
    intro c w hview hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (uniqueCache_putKv op c w hview hw) ?_
    rintro noop v ⟨hv,hs⟩
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (ih c v hview hv) ?_
    rintro bs u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩

/-- Every successful transaction with a fresh input view has unique cache
ids. No sortedness, encoding, threshold or tree invariant is required. -/
theorem execW_cacheUnique (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewIdsBelow tx.base v)
    (he : execW p tx i v = .ok (bs,w)) : CacheUnique w := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      have hw : UniqueCache tx.base {next := tx.base, top := top} := by
        constructor
        · exact ⟨Nat.le_refl _, by simp, by simp, by simp⟩
        · simp [CacheUnique]
      exact ((uniqueCache_ops (base := tx.base) tx.ops
        {p := p, i := i, view := rootless v} {next := tx.base, top := top}
        (viewIdsBelow_rootless tx.base v hv) hw bs w hr).1).2

end SIS.Tree
