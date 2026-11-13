import SIS.Tree.CvEncoding
import SIS.Tree.WriterStateInvariant
import SIS.Tree.AllocationIds

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

def ViewEncoded (view : View BVal) : Prop :=
  ∀ x n, view x = some n → HistoryEncoded n.hist

def PathCvEncoded : Option Nat → Prop
  | none => True
  | some c => CompareValueOK c

def WriterEncoded (w : W) : Prop :=
  (∀ q ∈ w.nodes, KlongsEncoded q.2.ks) ∧
  ∀ q ∈ w.path, PathCvEncoded q.1

def KeepsEncoded {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewEncoded c.view → WriterEncoded w →
    WriterWP f c w (fun _ v => WriterEncoded v)

theorem writerEncoded_lookup (w : W) (hw : WriterEncoded w) (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) : KlongsEncoded n.ks := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hn
  apply hw.1 (x, n)
  rw [he]
  simp

theorem encoded_getNode (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewEncoded c.view) (hw : WriterEncoded w) :
    WriterWP (getNode x) c w (fun n v => WriterEncoded v ∧ KlongsEncoded n.ks) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw, writerEncoded_lookup w hw x n hn⟩
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hn
      split
      · exact writerWP_throw _ _ _ _
      · have hks := klongsOf_encoded nd.hist (hv x nd hn)
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨⟨?_, hw.2⟩, hks⟩
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hw.1 q hq
        · have heq := List.mem_singleton.mp hq
          subst q
          exact hks
    · exact writerWP_throw _ _ _ _

theorem encoded_putNode (x : NodeId) (n : KNode) (hn : KlongsEncoded n.ks) :
    KeepsEncoded (putNode x n) := by
  intro c w _ hw
  simp only [putNode, writerWP_modify]
  refine ⟨?_, hw.2⟩
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact hn
    · cases he; exact hw.1 _ ha
  · rcases List.mem_append.mp hq with hq | hq
    · exact hw.1 q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hn

theorem encoded_newKey (g h : Nat) (leaf : Bool) (ks : List Klong)
    (hks : KlongsEncoded ks) : KeepsEncoded (newKey g h leaf ks) := by
  intro c w _ hw
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    refine ⟨?_, hw.2⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hw.1 q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hks

theorem encoded_fresh : KeepsEncoded fresh := by
  intro c w _ hw
  unfold fresh
  wpSimplify
  exact hw

theorem encoded_note (s : String) : KeepsEncoded (note s) := by
  intro c w _ hw
  simp only [note, writerWP_modify]
  exact hw

theorem encoded_takenBack (x : NodeId) : KeepsEncoded (takenBack x) := by
  intro c w _ hw
  simp only [takenBack, writerWP_modify]
  exact hw

theorem encoded_pathClear : KeepsEncoded pathClear := by
  intro c w _ hw
  simp only [pathClear, writerWP_modify]
  exact ⟨hw.1, by simp⟩

theorem encoded_pathAdd (cv : Option Nat) (x : NodeId) (hc : PathCvEncoded cv) :
    KeepsEncoded (pathAdd cv x) := by
  intro c w _ hw
  simp only [pathAdd, writerWP_modify]
  refine ⟨hw.1, ?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hw.2 q hq
  · have he := List.mem_singleton.mp hq
    subst q; exact hc

theorem encoded_setMadeFor (x : NodeId) (old : Option NodeId) : KeepsEncoded (setMadeFor x old) := by
  intro c w _ hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw
  · simpa only [writerWP_pure] using hw

theorem encoded_newValue (h : Nat) : KeepsEncoded (newValue h) := by
  intro c w _ hw
  unfold newValue fresh
  wpSimplify
  exact hw

theorem encoded_newSuperRoot (x : NodeId) : KeepsEncoded (newSuperRoot x) := by
  intro c w _ hw
  unfold newSuperRoot note fresh
  wpSimplify
  split <;> wpSimplify <;> exact hw

theorem encoded_klongAt (d : Nat) (c : Ctx) (w : W) (hw : WriterEncoded w) :
    WriterWP (klongAt d) c w (fun cv v => WriterEncoded v ∧ CompareValueOK cv) := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i cv x hget
    simp only [writerWP_pure]
    exact ⟨hw, hw.2 _ (List.mem_of_getElem? hget)⟩
  · exact writerWP_throw _ _ _ _

theorem writerWP_of_encoded {α : Type} {f : M α} (hf : KeepsEncoded f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewEncoded c.view)
    (hw : WriterEncoded w) (hp : ∀ r v, WriterEncoded v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hv hw) hp

macro "encHeld" : tactic => `(tactic| first
  | assumption
  | (constructor <;> assumption))

macro "encUse " h:term : tactic => `(tactic| (
  (with_reducible refine writerWP_of_encoded $h _ _ _ ?encView ?encState ?encPost)
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (encoded_getNode _ _ _ ?encView ?encState) ?encPost)
  case encView => assumption
  case encState => encHeld
  rintro _ _ ⟨_, _⟩))

macro "encKlongAt" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
  (refine writerWP_mono (encoded_klongAt _ _ _ ?encState) ?encPost)
  case encState => encHeld
  rintro _ _ ⟨_, _⟩))

macro "encNeutral" : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | wpSimplify
    | encNode
    | encUse (encoded_pathAdd none _ trivial)
    | encKlongAt
    | exact writerWP_throw _ _ _ _
    | split
    | encHeld
    | contradiction))

theorem encoded_ghOf (x : NodeId) : KeepsEncoded (ghOf x) := by unfold ghOf; encNeutral
theorem encoded_replacedBy (x : NodeId) : KeepsEncoded (replacedBy x) := by unfold replacedBy; encNeutral
theorem encoded_pathSize : KeepsEncoded pathSize := by unfold pathSize; encNeutral
theorem encoded_pathNode (d : Nat) : KeepsEncoded (pathNode d) := by unfold pathNode; encNeutral
theorem encoded_parentAt (d : Nat) : KeepsEncoded (parentAt d) := by
  cases d with
  | zero => intro c w hv hw; simpa only [parentAt, writerWP_pure] using hw
  | succ d =>
    intro c w hv hw
    unfold parentAt
    simp only [writerWP_bind]
    encUse (encoded_pathNode _)
    simpa only [writerWP_pure] using ‹WriterEncoded _›
theorem encoded_findRoot : KeepsEncoded findRoot := by
  intro c w hv hw
  unfold findRoot
  wpSimplify
  exact encoded_pathAdd none _ trivial c w hv hw

syntax "encScalar" : tactic
syntax "encKs" : tactic
syntax "encPairs" : tactic
syntax "encKlong" : tactic

macro_rules
  | `(tactic| encScalar) => `(tactic| first
    | assumption
    | exact compareValueOK_zero
    | (apply encoded_searchLte
       · assumption
       · encKs)
    | (apply encoded_cv
       · assumption
       · encKs)
    | (apply encoded_mergeOutput
       · assumption
       · assumption)
    | (apply encoded_searchEq
       · assumption
       · encKs)
    | (apply encoded_halves_cv
       · encKs
       · encPairs)
    | (apply encoded_merge_second_value
       · assumption
       · encPairs
       · encPairs
       · encScalar))
  | `(tactic| encKlong) => `(tactic| first
    | assumption
    | trivial
    | (change CompareValueOK _; encScalar)
    | (apply encoded_head_eq
       · assumption
       · encKs))
  | `(tactic| encKs) => `(tactic| first
    | assumption
    | exact klongsEncoded_nil
    | (apply (klongsEncoded_cons _ _).mpr; constructor
       · encKlong
       · encKs)
    | (apply (klongsEncoded_append _ _).mpr; constructor <;> encKs)
    | (apply KlongsEncoded.add
       · encKs
       · encKlong)
    | (apply KlongsEncoded.repoint; encKs)
    | (apply KlongsEncoded.set
       · encKs
       · encKlong)
    | (apply KlongsEncoded.lastVersionGivenDel; encKs)
    | (apply KlongsEncoded.lastVersion; encKs)
    | (apply KlongsEncoded.prefixAt; encKs)
    | (apply KlongsEncoded.toPrev; encKs)
    | (apply encoded_replacedKlong
       · assumption
       · encKs)
    | (apply KlongsEncoded.newKlongs; encPairs)
    | (apply encoded_halves_first
       · encKs
       · encPairs)
    | (apply encoded_halves_second
       · encKs
       · encPairs)
    | (apply KlongsEncoded.insertSorted
       · encKs
       · encScalar)
    | (apply klongsEncoded_of_shape _ _ (retargetKlongs_shape _ _ _ _); encKs)
    | (apply encoded_tail_two_eq
       · assumption
       · encKs)
    | (apply encoded_tail_eq
       · assumption
       · encKs))
  | `(tactic| encPairs) => `(tactic| first
    | assumption
    | exact pairsEncoded_nil
    | (apply (pairsEncoded_cons _ _).mpr; constructor
       · encScalar
       · encPairs)
    | (apply (pairsEncoded_append _ _).mpr; constructor <;> encPairs)
    | (apply KlongsEncoded.live; encKs)
    | (apply encoded_merge_first
       · encPairs
       · encPairs
       · encScalar)
    | (apply encoded_merge_second_list
       · assumption
       · encPairs
       · encPairs
       · encScalar))

macro "encStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_putNode _ _ ?encInput) _ _ _ ?encView ?encState ?encPost)
  case encInput => encKs
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_newKey _ _ _ _ ?encInput) _ _ _ ?encView ?encState ?encPost)
  case encInput => encKs
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encPath" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (pathAdd _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_pathAdd _ _ ?encInput) _ _ _ ?encView ?encState ?encPost)
  case encInput => first | trivial | (change CompareValueOK _; encScalar)
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encCore" : tactic => `(tactic| first
  | encNode
  | encKlongAt
  | encStore
  | encCreate
  | encPath
  | encUse (encoded_ghOf _)
  | encUse (encoded_replacedBy _)
  | encUse encoded_pathSize
  | encUse (encoded_pathNode _)
  | encUse (encoded_parentAt _)
  | encUse encoded_findRoot
  | encUse (encoded_note _)
  | encUse encoded_fresh
  | encUse (encoded_newValue _)
  | encUse (encoded_newSuperRoot _)
  | encUse (encoded_setMadeFor _ _)
  | encUse (encoded_takenBack _)
  | encUse encoded_pathClear
  | encHeld
  | exact writerWP_throw _ _ _ _)

theorem encoded_fold_add (n : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hn : KlongsEncoded n.ks) (hi : PairsEncoded ins) :
    KlongsEncoded (ins.foldl (fun n q => n.add t (.key q.1 q.2)) n).ks := by
  induction ins generalizing n with
  | nil => exact hn
  | cons q ins ih =>
    have hh := (pairsEncoded_cons _ _).mp hi
    exact ih (n.add t (.key q.1 q.2)) (KlongsEncoded.add n t _ hn hh.1) hh.2

theorem encoded_addKeys (x : NodeId) (ins : List (Nat × NodeId)) (hi : PairsEncoded ins) :
    KeepsEncoded (addKeys x ins) := by
  intro c w hv hw
  unfold addKeys
  wpSimplify
  encNode
  exact encoded_putNode _ _ (encoded_fold_add _ _ _ (by assumption) hi) _ _ hv (by encHeld)

theorem encoded_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId))
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun out v => KlongsEncoded out.ks ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨hlast, trivial⟩
  | cons q ins ih =>
    have hh := (pairsEncoded_cons _ _).mp hins
    rw [List.foldlM_cons, writerWP_bind]
    cases hr : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih (last.add c.i (.key q.1 q.2)) (KlongsEncoded.add _ _ _ hlast hh.1) hh.2
      | some ks =>
        simp only [writerWP_pure]
        exact ih {last with ks := ks} (KlongsEncoded.replaceKlong _ _ _ _ hlast ks hr) hh.2

macro "encReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (encoded_replaceOrAdd _ _ ?encLast ?encIns _ _) ?encPost
  case encLast => encKs
  case encIns => encPairs
  rintro out v ⟨hout, heq⟩
  subst v))

macro "encUp " h:term : tactic => `(tactic| (
  (with_reducible refine writerWP_of_encoded ($h _ _ ?encInput) _ _ _ ?encView ?encState ?encPost)
  case encInput => encPairs
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

set_option maxHeartbeats 1200000 in
theorem encoded_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins)
    (hup : ∀ q more, PairsEncoded more → KeepsEncoded (up q more)) :
    KeepsEncoded (handleFullWith up depth x ins last compact) := by
  intro c w hv hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | encCore
    | encReplace
    | encUp hup
    | wpSplit
    | split
    | contradiction

macro "encAdd" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (addKeys _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_addKeys _ _ ?encInput) _ _ _ ?encView ?encState ?encPost)
  case encInput => encPairs
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_handleFullWith _ _ _ _ _ _ ?encLast ?encIns ?encUp) _ _ _ ?encView ?encState ?encPost)
  case encLast => encKs
  case encIns => encPairs
  case encUp => exact $hup
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

theorem encoded_throw {α : Type} (e : String) : KeepsEncoded (throw e : M α) := by
  intro c w hv hw
  exact writerWP_throw _ _ _ _

set_option maxHeartbeats 1200000 in
theorem encoded_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (hins : PairsEncoded ins) : KeepsEncoded (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | encCore
      | encAdd
      | encFullWith (fun _ _ _ => encoded_throw _)
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | encCore
      | encAdd
      | encFullWith (fun q more hh => ih q more hh)
      | wpSplit
      | split
      | contradiction

theorem encoded_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (hlast : KlongsEncoded last.ks) : KeepsEncoded (handleFull depth x last compact) := by
  unfold handleFull
  refine encoded_handleFullWith _ _ _ _ _ _ hlast pairsEncoded_nil ?_
  intro q more hh
  cases depth with
  | zero => exact encoded_throw _
  | succ depth => exact encoded_appendKlongs depth q more hh

macro "encHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_handleFull _ _ _ _ ?encLast) _ _ _ ?encView ?encState ?encPost)
  case encLast => encKs
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

macro "encAppend" : tactic => `(tactic| first
  | encAdd
  | encHandle
  | ((with_unfolding_none guard_target = WriterWP (appendKlongs _ _ _) _ _ _)
     (with_reducible refine writerWP_of_encoded (encoded_appendKlongs _ _ _ ?encIns) _ _ _ ?encView ?encState ?encPost)
     case encIns => encPairs
     case encView => assumption
     case encState => encHeld
     intro _ _ _))

theorem encoded_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsEncoded (f b a)) : KeepsEncoded (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hv hw) (fun b v hh => ih b c v hv hh)

theorem encoded_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsEncoded (f a b)) :
    KeepsEncoded (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.forIn_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hw) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b c v hv hh

macro "encFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_encoded (encoded_foldlM _ _ _ ?encBody) _ _ _ ?encView ?encState ?encPost)
  case encBody =>
    intro b a c w hv hw
    repeat' first
      | wpSimplify
      | encCore
      | encAppend
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

theorem encoded_descendLte (cv fuel : Nat) (x : NodeId) :
    KeepsEncoded (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact encoded_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | encCore
      | encUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem encoded_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsEncoded (descendToSegmentRoot key segment) := by
  intro c w hv hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | encCore
    | encFoldWith (encUse (encoded_descendLte _ _ _))
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1200000 in
theorem encoded_appendDeleteKlong (x : NodeId) (depth cv : Nat) :
    KeepsEncoded (appendDeleteKlong x depth cv) := by
  intro c w hv hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1200000 in
theorem encoded_emptyKeyNext (x : NodeId) (depth : Nat) : KeepsEncoded (emptyKeyNext x depth) := by
  intro c w hv hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | wpSplit
    | split
    | contradiction

theorem encoded_unlink (x : NodeId) : KeepsEncoded (unlink x) := by
  intro c w hv hw
  unfold unlink
  repeat' first | wpSimplify | encCore | wpSplit | split | contradiction

theorem encoded_retarget (q src dst : NodeId) : KeepsEncoded (retarget q src dst) := by
  intro c w hv hw
  unfold retarget
  repeat' first | wpSimplify | encCore | wpSplit | split | contradiction

theorem encoded_canTakeBack (x parent : NodeId) (cv : Nat) : KeepsEncoded (canTakeBack x parent cv) := by
  intro c w hv hw
  unfold canTakeBack
  repeat' first | wpSimplify | encCore | wpSplit | split | contradiction

theorem encoded_takeBack (x parent : NodeId) (cv : Nat) : KeepsEncoded (takeBack x parent cv) := by
  intro c w hv hw
  unfold takeBack
  repeat' first
    | wpSimplify
    | encCore
    | encUse (encoded_retarget _ _ _)
    | wpSplit
    | split
    | contradiction

theorem encoded_takeBackRoot (x : NodeId) (depth only : Nat) :
    KeepsEncoded (takeBackRoot x depth only) := by
  intro c w hv hw
  unfold takeBackRoot
  repeat' first | wpSimplify | encCore | wpSplit | split | contradiction

theorem encoded_replaceRoot (x : NodeId) (depth only : Nat) :
    KeepsEncoded (replaceRoot x depth only) := by
  intro c w hv hw
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | encUse (encoded_unlink _)
    | wpSplit
    | split
    | contradiction

theorem encoded_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsEncoded (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact encoded_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | encCore
      | encUse (encoded_descendToSegmentRoot _ _)
      | encUse (encoded_takeBackRoot _ _ _)
      | encUse (encoded_replaceRoot _ _ _)
      | encUse ih
      | wpSplit
      | split
      | contradiction

theorem encoded_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsEncoded (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact encoded_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | encCore
      | encUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem encoded_descendToHeight (key : Key) (g h : Nat) :
    KeepsEncoded (descendToHeight key g h) := by
  intro c w hv hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | encCore
    | encUse (encoded_descendToSegmentRoot _ _)
    | encUse (encoded_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem encoded_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hL : CompareValueOK cL) (hR : CompareValueOK cR)
    (h2 : MergeOutputEncoded m2) : KeepsEncoded (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hv hw
  unfold mergeParent
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | wpSplit
    | split
    | contradiction

theorem encoded_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewEncoded c.view) (hw : WriterEncoded w) :
    WriterWP (sibling q pn i inner) c w
      (fun result v => WriterEncoded v ∧ KlongsEncoded result.2.ks) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | encCore
    | (constructor <;> assumption)
    | wpSplit
    | split
    | contradiction

macro "encSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  refine writerWP_mono (encoded_sibling _ _ _ _ _ _ ?encView ?encState) ?encPost
  case encView => assumption
  case encState => encHeld
  rintro result v ⟨hstate, hnode⟩))

macro "encMergeParent" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_mergeParent _ _ _ _ _ _ _ _ ?encLeft ?encRight ?encSecond) _ _ _ ?encView ?encState ?encPost)
  case encLeft => encScalar
  case encRight => encScalar
  case encSecond => first | trivial | (change CompareValueOK _; encScalar)
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

set_option maxHeartbeats 1600000 in
theorem encoded_merge (x : NodeId) (d : Nat) : KeepsEncoded (merge x d) := by
  intro c w hv hw
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | encCore
    | encSibling
    | encMergeParent
    | encUse (encoded_unlink _)
    | encUse (encoded_retarget _ _ _)
    | wpSplit
    | split
    | contradiction

end SIS.Tree
