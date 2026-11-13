/-
The tree model (bergdb 024-12, TP7): the writer's overlay holds a key node
once. `NodupCache` is `FreshCache` (every cached id, height tag and taken-back
id below the next fresh id) with: no id twice in the overlay. The walk
through the writer is that of SIS/Tree/FreshCache.lean, with the overlay's
changes (a node read, a node stored, a node made) proved for the larger
statement. With it the changes of a transaction (`changesOf`) hold the
entries of one overlay node for each id.
-/
import SIS.Tree.FreshCache

namespace SIS.Tree

open SIS SIS.Check

/-- `FreshCache`, and no id twice in the overlay. -/
def NodupCache (base : NodeId) (w : W) : Prop :=
  base ≤ w.next ∧ (∀ q ∈ w.nodes, q.1 < w.next) ∧
    (∀ q ∈ w.gh, q.1 < w.next) ∧ (∀ x ∈ w.taken, x < w.next) ∧
    (w.nodes.map (·.1)).Nodup

def KeepsNodupCache (base : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow base c.view → NodupCache base w →
    WriterWP f c w (fun _ v => NodupCache base v ∧ w.next ≤ v.next)

theorem NodupCache.fresh {base : NodeId} {w : W} (h : NodupCache base w) : FreshCache base w :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem nodupCache_of_same (base : NodeId) (w v : W) (hw : NodupCache base w)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (ht : v.taken = w.taken)
    (hnext : w.next ≤ v.next) :
    NodupCache base v := by
  refine ⟨Nat.le_trans hw.1 hnext,?_,?_,?_,?_⟩
  · intro q hq
    rw [hn] at hq
    exact Nat.lt_of_lt_of_le (hw.2.1 q hq) hnext
  · intro q hq
    rw [hg] at hq
    exact Nat.lt_of_lt_of_le (hw.2.2.1 q hq) hnext
  · intro x hx
    rw [ht] at hx
    exact Nat.lt_of_lt_of_le (hw.2.2.2.1 x hx) hnext
  · rw [hn]
    exact hw.2.2.2.2

theorem nodupCache_lookup_lt (base : NodeId) (w : W) (hw : NodupCache base w)
    (x : NodeId) (n : KNode) (hn : w.nodes.lookup x = some n) : x < w.next :=
  freshCache_lookup_lt base w hw.fresh x n hn

theorem lookup_none_not_mem_ids (nodes : List (NodeId × KNode)) (x : NodeId)
    (h : nodes.lookup x = none) : x ∉ nodes.map (·.1) := by
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have := List.lookup_eq_none_iff.mp h q hq
  simp [he] at this

theorem nodup_ids_append (nodes : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hn : (nodes.map (·.1)).Nodup) (hx : x ∉ nodes.map (·.1)) :
    ((nodes ++ [(x, n)]).map (·.1)).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  subst hab
  exact hx ha

theorem upsert_ids_nodup (nodes : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hn : (nodes.map (·.1)).Nodup) : ((upsert nodes x n).map (·.1)).Nodup := by
  unfold upsert
  split
  · have he : (nodes.map (fun q => if q.1 == x then (x, n) else q)).map (·.1) = nodes.map (·.1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro q _
      by_cases hq : q.1 = x
      · simp [hq]
      · simp [hq]
    rw [he]
    exact hn
  · rename_i hany
    apply nodup_ids_append nodes x n hn
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    apply hany
    exact List.any_eq_true.mpr ⟨q, hq, by simp [he]⟩

theorem writerWP_getNode_nodupCache (base x : NodeId) (c : Ctx) (w : W)
    (hv : ViewIdsBelow base c.view) (hw : NodupCache base w) :
    WriterWP (getNode x) c w (fun _ v =>
      NodupCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  unfold getNode
  simp only [writerWP_bind,writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw,Nat.le_refl _,nodupCache_lookup_lt base w hw x n hn⟩
  · rename_i hnone
    simp only [writerWP_bind,writerWP_read]
    split
    · rename_i n hn
      split
      · exact writerWP_throw _ _ _ _
      · have hx : x < w.next := Nat.lt_of_lt_of_le (hv x n hn) hw.1
        have hlook : w.nodes.lookup x = none := hnone
        simp only [writerWP_bind,writerWP_set,writerWP_pure]
        refine ⟨⟨hw.1,?_,?_,hw.2.2.2.1,?_⟩,Nat.le_refl _,hx⟩
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
        · exact nodup_ids_append w.nodes x _ hw.2.2.2.2 (lookup_none_not_mem_ids w.nodes x hlook)
    · exact writerWP_throw _ _ _ _

theorem writerWP_of_nodupCache {α : Type} {f : M α} (base : NodeId)
    (hf : KeepsNodupCache base f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hv : ViewIdsBelow base c.view) (hw : NodupCache base w)
    (hp : ∀ r v, NodupCache base v → w.next ≤ v.next → post r v) :
    WriterWP f c w post := by
  exact writerWP_mono (hf c w hv hw) (fun r v h => hp r v h.1 h.2)

theorem writerWP_putNode_nodupCache (base x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hw : NodupCache base w) (hx : x < w.next) :
    WriterWP (putNode x n) c w (fun _ v => NodupCache base v ∧ w.next ≤ v.next) := by
  simp only [putNode,writerWP_modify]
  exact ⟨⟨hw.1,upsert_ids_below w.nodes w.next x n hw.2.1 hx,hw.2.2.1,hw.2.2.2.1,
    upsert_ids_nodup w.nodes x n hw.2.2.2.2⟩,Nat.le_refl _⟩

theorem writerWP_fresh_nodupCache (base : NodeId) (c : Ctx) (w : W)
    (hw : NodupCache base w) :
    WriterWP fresh c w (fun x v =>
      NodupCache base v ∧ w.next ≤ v.next ∧ x < v.next ∧ x = w.next ∧ v.nodes = w.nodes) := by
  simp only [fresh,writerWP_bind,writerWP_get,writerWP_set,writerWP_pure]
  exact ⟨nodupCache_of_same base w _ hw rfl rfl rfl (by simp),by simp,by simp,trivial,trivial⟩

theorem writerWP_newKey_nodupCache (base g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hw : NodupCache base w) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      NodupCache base v ∧ w.next ≤ v.next ∧ x < v.next) := by
  unfold newKey
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_mono (writerWP_fresh_nodupCache base c w hw) ?_
  rintro x v ⟨hv,hnext,hx,hxe,hnodes⟩
  have hnot : x ∉ v.nodes.map (·.1) := by
    rw [hnodes, hxe]
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    have := hw.2.1 q hq
    omega
  split <;> wpSimplify
  all_goals
    refine ⟨⟨hv.1,?_,?_,hv.2.2.2.1,?_⟩,hnext,hx⟩
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
    · exact nodup_ids_append v.nodes x _ hv.2.2.2.2 hnot

theorem writerWP_takenBack_nodupCache (base x : NodeId) (c : Ctx) (w : W)
    (hw : NodupCache base w) (hx : x < w.next) :
    WriterWP (takenBack x) c w (fun _ v => NodupCache base v ∧ w.next ≤ v.next) := by
  simp only [takenBack,writerWP_modify]
  refine ⟨⟨hw.1,hw.2.1,hw.2.2.1,?_,hw.2.2.2.2⟩,Nat.le_refl _⟩
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hw.2.2.2.1 y hy

macro "ndState" : tactic => `(tactic| first
  | assumption
  | (grind [NodupCache]))

macro "ndUse " base:term " using " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_nodupCache $base $h _ _ _ ?ndView ?ndState ?ndPost)
  case ndView => assumption
  case ndState => ndState
  intro _ _ _ _))

macro "ndFinish" : tactic => `(tactic| (
  (with_unfolding_none refine And.intro ?ndFinal ?ndNext)
  case ndFinal => ndState
  case ndNext =>
    try dsimp only at *
    omega))

macro "ndLoad " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_getNode_nodupCache $base _ _ _ ?ndView ?ndState) ?ndPost)
  case ndView => assumption
  case ndState => ndState
  rintro _ _ ⟨_,_,_⟩))

macro "ndCreate " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_newKey_nodupCache $base _ _ _ _ _ _ ?ndState) ?ndPost)
  case ndState => ndState
  rintro _ _ ⟨_,_,_⟩))

macro "ndPut " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_putNode_nodupCache $base _ _ _ _ ?ndState ?ndId) ?ndPost)
  case ndState => ndState
  case ndId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "ndTake " base:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_takenBack_nodupCache $base _ _ _ ?ndState ?ndId) ?ndPost)
  case ndState => ndState
  case ndId =>
    try dsimp only at *
    omega
  rintro _ _ ⟨_,_⟩))

macro "ndNeutral " bound:term : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,writerWP_set,
        writerWP_modify,note,fresh,newValue,setMadeFor,replacedBy,takenBack,pathClear,
        pathAdd,pathSize,pathNode,klongAt,parentAt,newSuperRoot,findRoot]
    | exact writerWP_throw _ _ _ _
    | ndLoad $bound
    | ndPut $bound
    | wpSplit
    | split
    | ndFinish
    | contradiction))

theorem nodupCache_note {base : NodeId} (s : String) : KeepsNodupCache base (note s) := by ndNeutral base
theorem nodupCache_fresh {base : NodeId} : KeepsNodupCache base fresh := by ndNeutral base
theorem nodupCache_newValue {base : NodeId} (h : Nat) : KeepsNodupCache base (newValue h) := by ndNeutral base
theorem nodupCache_setMadeFor {base : NodeId} (x : NodeId) (old : Option NodeId) : KeepsNodupCache base (setMadeFor x old) := by ndNeutral base
theorem nodupCache_replacedBy {base : NodeId} (x : NodeId) : KeepsNodupCache base (replacedBy x) := by ndNeutral base
theorem nodupCache_pathClear {base : NodeId} : KeepsNodupCache base pathClear := by ndNeutral base
theorem nodupCache_pathAdd {base : NodeId} (cv : Option Nat) (x : NodeId) : KeepsNodupCache base (pathAdd cv x) := by ndNeutral base
theorem nodupCache_pathSize {base : NodeId} : KeepsNodupCache base pathSize := by ndNeutral base
theorem nodupCache_pathNode {base : NodeId} (d : Nat) : KeepsNodupCache base (pathNode d) := by ndNeutral base
theorem nodupCache_klongAt {base : NodeId} (d : Nat) : KeepsNodupCache base (klongAt d) := by ndNeutral base
theorem nodupCache_parentAt {base : NodeId} (d : Nat) : KeepsNodupCache base (parentAt d) := by ndNeutral base
theorem nodupCache_newSuperRoot {base : NodeId} (x : NodeId) : KeepsNodupCache base (newSuperRoot x) := by ndNeutral base
theorem nodupCache_findRoot {base : NodeId} : KeepsNodupCache base findRoot := by ndNeutral base

theorem nodupCache_addKeys {base : NodeId} (x : NodeId) (ins : List (Nat × NodeId)) : KeepsNodupCache base (addKeys x ins) := by
  intro c w hv hw
  unfold addKeys
  repeat' first | wpSimplify | ndLoad base | ndPut base | ndFinish

theorem nodupCache_foldlM {base : NodeId} {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsNodupCache base (f b a)) : KeepsNodupCache base (xs.foldlM f init) := by
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

theorem nodupCache_forIn {base : NodeId} {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsNodupCache base (f a b)) :
    KeepsNodupCache base (forIn xs init f) := by
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

theorem nodupCache_ghOf {base : NodeId} (x : NodeId) : KeepsNodupCache base (ghOf x) := by
  intro c w hview hw
  unfold ghOf
  repeat' first | wpSimplify | ndLoad base | ndFinish | exact writerWP_throw _ _ _ _ | split

macro "ndCore " bound:term : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | ndLoad $bound
  | ndUse $bound using (nodupCache_ghOf _)
  | ndCreate $bound
  | ndPut $bound
  | ndUse $bound using (nodupCache_note _)
  | ndUse $bound using nodupCache_fresh
  | ndUse $bound using (nodupCache_newValue _)
  | ndUse $bound using (nodupCache_setMadeFor _ _)
  | ndUse $bound using (nodupCache_replacedBy _)
  | ndTake $bound
  | ndUse $bound using nodupCache_pathClear
  | ndUse $bound using (nodupCache_pathAdd _ _)
  | ndUse $bound using nodupCache_pathSize
  | ndUse $bound using (nodupCache_pathNode _)
  | ndUse $bound using (nodupCache_klongAt _)
  | ndUse $bound using (nodupCache_parentAt _)
  | ndUse $bound using (nodupCache_newSuperRoot _)
  | ndUse $bound using nodupCache_findRoot
  | ndUse $bound using (nodupCache_addKeys _ _)
  | ndFinish)

macro "ndFoldWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_nodupCache $bound (nodupCache_foldlM _ _ _ ?ndBody) _ _ _ ?ndView ?ndState ?ndPost)
  case ndBody =>
    intro b a c w hview hw
    repeat' first
      | wpSimplify
      | ndCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ndView => assumption
  case ndState => ndState
  intro _ _ _ _))

macro "ndFold " bound:term : tactic => `(tactic| ndFoldWith $bound using fail)

theorem nodupCache_replaceOrAdd {base : NodeId} (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsNodupCache base (replaceOrAdd last ins) := by
  intro c w hview hw
  unfold replaceOrAdd
  repeat' first
    | wpSimplify
    | ndCore base
    | ndFold base
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem nodupCache_handleFullWith {base : NodeId} (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsNodupCache base (up q more)) :
    KeepsNodupCache base (handleFullWith up depth x ins last compact) := by
  intro c w hview hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | ndCore base
    | ndFold base
    | ndUse base using (nodupCache_replaceOrAdd _ _)
    | ndUse base using (hup _ _)
    | wpSplit
    | split
    | contradiction


theorem nodupCache_throw {base : NodeId} {α : Type} (e : String) : KeepsNodupCache base (throw e : M α) := by
  intro c w hview hw
  exact writerWP_throw _ _ _ _

theorem nodupCache_appendKlongs {base : NodeId} (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsNodupCache base (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ndCore base
      | ndUse base using (nodupCache_handleFullWith _ _ _ _ _ _ (fun _ _ => nodupCache_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ndCore base
      | ndUse base using (nodupCache_handleFullWith _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem nodupCache_handleFull {base : NodeId} (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsNodupCache base (handleFull depth x last compact) := by
  unfold handleFull
  refine nodupCache_handleFullWith _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact nodupCache_throw _
  | succ d => exact nodupCache_appendKlongs _ _ _

theorem nodupCache_descendLte {base : NodeId} (cv fuel : Nat) (x : NodeId) :
    KeepsNodupCache base (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact nodupCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | ndCore base
      | ndUse base using (ih _)
      | wpSplit
      | split
      | contradiction

macro "ndAppend " bound:term : tactic => `(tactic| first
  | ndUse $bound using (nodupCache_handleFull _ _ _ _)
  | ndUse $bound using (nodupCache_appendKlongs _ _ _)
  | ndUse $bound using (nodupCache_descendLte _ _ _))

theorem nodupCache_descendToSegmentRoot {base : NodeId} (key : Key) (segment : Nat) :
    KeepsNodupCache base (descendToSegmentRoot key segment) := by
  intro c w hview hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | ndCore base
    | ndFoldWith base using (ndAppend base)
    | ndAppend base
    | wpSplit
    | split
    | contradiction

macro "ndDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem nodupCache_appendDeleteKlong {base : NodeId} (x : NodeId) (depth cv : Nat) : KeepsNodupCache base (appendDeleteKlong x depth cv) := by
  intro c w hview hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | ndDeleteSimplify
    | ndCore base
    | ndAppend base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_emptyKeyNext {base : NodeId} (x : NodeId) (depth : Nat) : KeepsNodupCache base (emptyKeyNext x depth) := by
  intro c w hview hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | ndDeleteSimplify
    | ndCore base
    | ndAppend base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_collapseRoot {base : NodeId} (key : Key) (segment fuel : Nat) :
    KeepsNodupCache base (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact nodupCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | ndDeleteSimplify
      | ndCore base
      | ndAppend base
      | ndUse base using (nodupCache_descendToSegmentRoot _ _)
      | ndUse base using ih
      | wpSplit
      | split
      | contradiction

theorem nodupCache_descendHeight {base : NodeId} (cv h fuel : Nat) (x : NodeId) :
    KeepsNodupCache base (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact nodupCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | ndCore base
      | ndUse base using (ih _)
      | wpSplit
      | split
      | contradiction

theorem nodupCache_descendToHeight {base : NodeId} (key : Key) (g h : Nat) :
    KeepsNodupCache base (descendToHeight key g h) := by
  intro c w hview hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | ndCore base
    | ndUse base using (nodupCache_descendToSegmentRoot _ _)
    | ndUse base using (nodupCache_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 2000000 in
theorem nodupCache_mergeParent {base : NodeId} (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsNodupCache base (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hview hw
  unfold mergeParent
  repeat' first
    | wpSimplify
    | ndCore base
    | ndAppend base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_unlink {base : NodeId} (x : NodeId) : KeepsNodupCache base (unlink x) := by
  intro c w hview hw
  unfold unlink
  repeat' first
    | wpSimplify
    | ndCore base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_retarget {base : NodeId} (q src dst : NodeId) : KeepsNodupCache base (retarget q src dst) := by
  intro c w hview hw
  unfold retarget
  repeat' first
    | wpSimplify
    | ndCore base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_sibling {base : NodeId} (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) : KeepsNodupCache base (sibling q pn i inner) := by
  intro c w hview hw
  unfold sibling
  repeat' first
    | wpSimplify
    | ndCore base
    | wpSplit
    | split
    | contradiction

theorem writerWP_sibling_nodupCache (base : NodeId) (q : NodeId) (pn : KNode)
    (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hview : ViewIdsBelow base c.view) (hw : NodupCache base w) :
    WriterWP (sibling q pn i inner) c w (fun r v =>
      NodupCache base v ∧ w.next ≤ v.next ∧ r.1 < v.next) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | ndLoad base
    | exact writerWP_throw _ _ _ _
    | (solve |
        refine ⟨?_,?_,?_⟩
        · ndState
        · omega
        · assumption)
    | split

macro "ndSibling " bound:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (writerWP_sibling_nodupCache $bound _ _ _ _ _ _ ?ndView ?ndState) ?ndPost)
  case ndView => assumption
  case ndState => ndState
  rintro ⟨_,_⟩ _ ⟨_,_,_⟩))

set_option maxHeartbeats 2000000 in
theorem nodupCache_merge {base : NodeId} (x : NodeId) (d : Nat) : KeepsNodupCache base (merge x d) := by
  intro c w hview hw
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | ndCore base
    | ndUse base using (nodupCache_unlink _)
    | ndUse base using (nodupCache_retarget _ _ _)
    | ndSibling base
    | ndUse base using (nodupCache_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nodupCache_mergeUp {base : NodeId} (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsNodupCache base (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact nodupCache_throw _
  | succ fuel ih =>
    intro c w hview hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | ndCore base
      | ndUse base using (nodupCache_descendToHeight _ _ _)
      | ndUse base using (nodupCache_merge _ _)
      | ndUse base using (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem nodupCache_afterDelete {base : NodeId} (key : Key) (g h : Nat) : KeepsNodupCache base (afterDelete key g h) := by
  intro c w hview hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | ndCore base
    | ndUse base using (nodupCache_mergeUp _ _ _ _ _)
    | ndUse base using (nodupCache_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nodupCache_climb {base : NodeId} (depth : Nat) : KeepsNodupCache base (climb depth) := by
  induction depth with
  | zero =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | ndCore base
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hview hw
    unfold climb
    repeat' first
      | wpSimplify
      | ndDeleteSimplify
      | ndCore base
      | ndUse base using ih
      | wpSplit
      | split
      | contradiction

macro "ndForWith " bound:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_nodupCache $bound (nodupCache_forIn _ _ _ ?ndBody) _ _ _ ?ndView ?ndState ?ndPost)
  case ndBody =>
    intro a b c w hview hw
    repeat' first
      | wpSimplify
      | ndDeleteSimplify
      | ndCore $bound
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ndView => assumption
  case ndState => ndState
  intro _ _ _ _))

theorem nodupCache_segmentCount {base : NodeId} (path : List (Option Nat × NodeId)) (stop : Nat) :
    KeepsNodupCache base ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  intro c w hview hw
  ndFold base
  ndFinish

theorem nodupCache_unlinkLoop {base : NodeId} (depth tt : Nat) (js : List Nat) :
    KeepsNodupCache base (forIn js () (fun j _ => do
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
  ndForWith base using (ndAppend base)
  ndFinish

theorem nodupCache_deleteUpward {base : NodeId} (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsNodupCache base (deleteUpward leaf depth cv key) := by
  intro c w hview hw
  unfold deleteUpward afterDelete
  repeat' first
    | wpSimplify
    | ndDeleteSimplify
    | ndCore base
    | ndAppend base
    | ndFold base
    | ndForWith base using (ndAppend base)
    | ndUse base using (nodupCache_climb _)
    | ndUse base using (nodupCache_mergeUp _ _ _ _ _)
    | ndUse base using (nodupCache_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nodupCache_setValue {base : NodeId} (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsNodupCache base (setValue segRoot cv key value) := by
  intro c w hview hw
  unfold setValue
  repeat' first
    | wpSimplify
    | ndCore base
    | ndAppend base
    | ndUse base using (nodupCache_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nodupCache_setNode {base : NodeId} (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsNodupCache base (setNode segRoot cv create) := by
  intro c w hview hw
  unfold setNode
  repeat' first
    | wpSimplify
    | ndCore base
    | ndAppend base
    | wpSplit
    | split
    | contradiction

theorem nodupCache_putSegs {base : NodeId} (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsNodupCache base (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact nodupCache_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact nodupCache_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hview hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | ndCore base
        | ndUse base using (nodupCache_setNode _ _ _)
        | ndUse base using (ih _)
        | wpSplit
        | split
        | contradiction

theorem nodupCache_putKv {base : NodeId} (op : Tree.Op) : KeepsNodupCache base (putKv op) := by
  intro c w hview hw
  unfold putKv
  repeat' first
    | wpSimplify
    | ndCore base
    | ndUse base using (nodupCache_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nodupCache_ops {base : NodeId} (ops : List Tree.Op) : KeepsNodupCache base (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hview hw; simpa only [List.mapM_nil, writerWP_pure] using And.intro hw (Nat.le_refl _)
  | cons op ops ih =>
    intro c w hview hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (nodupCache_putKv op c w hview hw) ?_
    rintro noop v ⟨hv,hs⟩
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (ih c v hview hv) ?_
    rintro bs u ⟨hu,ht⟩
    exact ⟨hu,Nat.le_trans hs ht⟩

/-- A successful transaction of the writer holds each key node once in its
overlay, at an id below the next fresh one. -/
theorem execW_nodupCache (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewIdsBelow tx.base v)
    (he : execW p tx i v = .ok (bs,w)) : NodupCache tx.base w := by
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
      have hw : NodupCache tx.base {next := tx.base,top := top} := by
        exact ⟨Nat.le_refl _,by simp,by simp,by simp,by simp⟩
      exact (nodupCache_ops (base := tx.base) tx.ops
        {p := p,i := i,view := rootless v} {next := tx.base,top := top}
        (viewIdsBelow_rootless tx.base v hv) hw bs w hr).1

end SIS.Tree
