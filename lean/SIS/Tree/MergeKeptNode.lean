import SIS.Tree.FreshCache

namespace SIS.Tree

open SIS SIS.Check

structure NodeGuard where
  id : NodeId
  node : KNode
  g : Nat
  h : Nat

def GuardHeld (b : NodeGuard) (w : W) : Prop :=
  w.nodes.lookup b.id = some b.node ∧ w.gh.lookup b.id = some (b.g,b.h) ∧
    b.id ∉ w.taken ∧ b.id < w.next

def KeepsGuard (b : NodeGuard) {α : Type} (f : M α) : Prop :=
  ∀ c w, GuardHeld b w → WriterWP f c w (fun _ v => GuardHeld b v)

theorem writerWP_of_keepsGuard (b : NodeGuard) {α : Type} {f : M α} (hf : KeepsGuard b f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : GuardHeld b w)
    (hp : ∀ r v, GuardHeld b v → post r v) : WriterWP f c w post := by
  exact writerWP_mono (hf c w hw) hp

theorem guard_getNode (b : NodeGuard) (x : NodeId) : KeepsGuard b (getNode x) := by
  intro c w hw
  unfold getNode
  simp only [writerWP_bind,writerWP_get]
  split
  · simpa only [writerWP_pure] using hw
  · rename_i hnone
    have hbx : b.id ≠ x := by
      intro he
      rw [← he,hw.1] at hnone
      cases hnone
    have hbeq : (b.id == x) = false := beq_eq_false_iff_ne.mpr hbx
    simp only [writerWP_bind,writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind,writerWP_set,writerWP_pure]
        refine ⟨?_,?_,hw.2.2.1,hw.2.2.2⟩
        · simp [List.lookup_append,hw.1]
        · simpa only [List.lookup_cons,hbeq] using hw.2.1
    · exact writerWP_throw _ _ _ _

theorem guard_putNode (b : NodeGuard) (x : NodeId) (n : KNode) (hbx : b.id ≠ x) :
    KeepsGuard b (putNode x n) := by
  intro c w hw
  simp only [putNode,writerWP_modify]
  exact ⟨by rw [upsert_lookup_other _ b.id x n hbx]; exact hw.1,hw.2⟩

theorem guard_takenBack (b : NodeGuard) (x : NodeId) (hbx : b.id ≠ x) :
    KeepsGuard b (takenBack x) := by
  intro c w hw
  simp only [takenBack,writerWP_modify]
  exact ⟨hw.1,hw.2.1,by simpa only [List.mem_cons,not_or] using And.intro hbx hw.2.2.1,hw.2.2.2⟩

theorem guard_newKey (b : NodeGuard) (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsGuard b (newKey g h leaf ks) := by
  intro c w hw
  have hbeq : (b.id == w.next) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hw.2.2.2)
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    refine ⟨?_,?_,hw.2.2.1,by change b.id < w.next+2; have := hw.2.2.2; omega⟩
    · simp [List.lookup_append,hw.1]
    · simpa only [List.lookup_cons,hbeq] using hw.2.1

macro "kgState" : tactic => `(tactic| first | assumption | (grind [GuardHeld]))

macro "kgUse " b:term " using " hf:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_keepsGuard $b $hf _ _ _ ?kgHeld ?kgPost)
  case kgHeld => kgState
  intro _ _ _))

macro "kgPut " b:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_keepsGuard $b (guard_putNode $b _ _ ?kgNe) _ _ _ ?kgHeld ?kgPost)
  case kgNe =>
    try dsimp only at *
    first | assumption | omega
  case kgHeld => kgState
  intro _ _ _))

macro "kgNeutral " b:term : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,writerWP_set,
        writerWP_modify,note,fresh,setMadeFor,replacedBy,takenBack,pathClear,
        pathAdd,pathSize,pathNode,klongAt,parentAt,newSuperRoot,findRoot]
    | exact writerWP_throw _ _ _ _
    | kgUse $b using (guard_getNode $b _)
    | kgState
    | split))

theorem guard_note (b : NodeGuard) (s : String) : KeepsGuard b (note s) := by kgNeutral b
theorem guard_fresh (b : NodeGuard) : KeepsGuard b fresh := by kgNeutral b
theorem guard_setMadeFor (b : NodeGuard) (x : NodeId) (old : Option NodeId) : KeepsGuard b (setMadeFor x old) := by kgNeutral b
theorem guard_replacedBy (b : NodeGuard) (x : NodeId) : KeepsGuard b (replacedBy x) := by kgNeutral b
theorem guard_newSuperRoot (b : NodeGuard) (x : NodeId) : KeepsGuard b (newSuperRoot x) := by kgNeutral b

theorem guard_ghOf (b : NodeGuard) (x : NodeId) : KeepsGuard b (ghOf x) := by
  intro c w hw
  unfold ghOf
  repeat' first
    | wpSimplify
    | kgUse b using (guard_getNode b _)
    | exact writerWP_throw _ _ _ _
    | kgState
    | split

theorem guard_replaceOrAdd (b : NodeGuard) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsGuard b (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_foldlM_state _ _ _ _ _ (fun _ v => GuardHeld b v) hw ?_
  intro n more v hv
  split
  · exact writerWP_throw _ _ _ _
  · simpa only [writerWP_pure] using hv
  · simpa only [writerWP_pure] using hv

/-- Compacting another cached node made in this transaction preserves the
guarded node, its height tag, and its live allocation status. -/
theorem writerWP_handleFullWith_compact_guard (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (x : NodeId)
    (ins : List (Nat × NodeId)) (last n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (ht : n.firstTime = some c.i)
    (hbx : b.id ≠ x) (hw : GuardHeld b w) :
    WriterWP (handleFullWith up depth x ins last true) c w (fun _ v => GuardHeld b v) := by
  unfold handleFullWith
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  refine writerWP_mono (guard_ghOf b x c w hw) ?_
  intro gh v hv
  simp only [ht,BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [Bool.not_true,Bool.false_eq_true,Bool.false_and,↓reduceIte]
    | simp only [note]
    | kgUse b using (guard_getNode b _)
    | kgUse b using (guard_replaceOrAdd b _ _)
    | kgPut b
    | exact writerWP_throw _ _ _ _
    | kgState
    | split

theorem writerWP_handleFull_compact_guard (b : NodeGuard) (depth : Nat) (x : NodeId)
    (last n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (ht : n.firstTime = some c.i)
    (hbx : b.id ≠ x) (hw : GuardHeld b w) :
    WriterWP (handleFull depth x last true) c w (fun _ v => GuardHeld b v) := by
  unfold handleFull
  exact writerWP_handleFullWith_compact_guard b _ depth x [] last n c w hn ht hbx hw

theorem guard_retarget (b : NodeGuard) (q src dst : NodeId) (hbq : b.id ≠ q) :
    KeepsGuard b (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first
    | wpSimplify
    | kgUse b using (guard_getNode b _)
    | kgPut b
    | kgState
    | split

theorem guard_unlink (b : NodeGuard) (x : NodeId) (hbx : b.id ≠ x) :
    KeepsGuard b (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first
    | wpSimplify
    | kgUse b using (guard_getNode b _)
    | kgPut b
    | kgState
    | split

def KeyAllocated (base g h : Nat) (leaf : Bool) (ks : List Klong) (w : W)
    (x : NodeId) (v : W) : Prop :=
  FreshCache base v ∧ x = w.next ∧ v.next = w.next+2 ∧
    v.nodes = w.nodes ++ [(x,⟨leaf,ks⟩)] ∧ v.gh = (x,g,h) :: w.gh ∧
    v.taken = w.taken ∧ GuardHeld ⟨x,⟨leaf,ks⟩,g,h⟩ v

theorem writerWP_newKey_allocated (base g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hw : FreshCache base w) :
    WriterWP (newKey g h leaf ks) c w (KeyAllocated base g h leaf ks w) := by
  have hf : WriterWP (newKey g h leaf ks) c w (fun x v =>
      v.nodes = w.nodes ++ [(x,⟨leaf,ks⟩)] ∧ v.gh = (x,g,h) :: w.gh ∧ v.taken = w.taken) := by
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;> trivial
  intro x v he
  obtain ⟨hx,hnext,hnode,hgh,htaken,hfresh⟩ :=
    writerWP_newKey_freshCache_cached base g h leaf ks c w hw x v he
  obtain ⟨hns,hgs,ht⟩ := hf x v he
  exact ⟨hfresh,hx,hnext,hns,hgs,ht,hnode,hgh,htaken,by change x < v.next; rw [hx,hnext]; omega⟩

theorem writerWP_newKey_allocated_keep (b : NodeGuard) (base g h : Nat)
    (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : FreshCache base w) (hb : GuardHeld b w) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      KeyAllocated base g h leaf ks w x v ∧ GuardHeld b v) := by
  intro x v he
  exact ⟨writerWP_newKey_allocated base g h leaf ks c w hw x v he,
    guard_newKey b g h leaf ks c w hb x v he⟩

macro "kgTake " b:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_keepsGuard $b (guard_takenBack $b _ ?kgNe) _ _ _ ?kgHeld ?kgPost)
  case kgNe =>
    try dsimp only at *
    first | assumption | omega
  case kgHeld => kgState
  intro _ _ _))

macro "kgRetarget " b:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_keepsGuard $b (guard_retarget $b _ _ _ ?kgNe) _ _ _ ?kgHeld ?kgPost)
  case kgNe =>
    try dsimp only at *
    first | assumption | omega
  case kgHeld => kgState
  intro _ _ _))

macro "kgUnlink " b:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_keepsGuard $b (guard_unlink $b _ ?kgNe) _ _ _ ?kgHeld ?kgPost)
  case kgNe =>
    try dsimp only at *
    first | assumption | omega
  case kgHeld => kgState
  intro _ _ _))

set_option maxHeartbeats 1000000 in
/-- A first merge-parent update of a new split root has room by size; a
dead-klong compaction is in place. It preserves a different guarded node. -/
theorem writerWP_mergeParent_newRoot_guard (b : NodeGuard) (depth : Nat)
    (q a r m1 : NodeId) (sc : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p)
    (hn : w.nodes.lookup q = some ⟨false,[.time c.i,.key 0 a,.key sc r]⟩)
    (hbq : b.id ≠ q) (hw : GuardHeld b w) :
    WriterWP (mergeParent q depth 1 0 m1 2 sc m2) c w (fun _ v => GuardHeld b v) := by
  let rn : KNode := ⟨false,[.time c.i,.key 0 a,.key sc r]⟩
  have htime : rn.lastTime = some c.i := rfl
  have hindex : rn.lastTimeIndex = some 0 := rfl
  have hsize : rn.size = 3 := rfl
  have hlast : rn.ks.getLast? = some (.key sc r) := rfl
  have hm := mergeParamsOK_size_six c.p hp
  have h3 : 3 ≤ c.p.M := by omega
  have h4 : 4 ≤ c.p.M := by omega
  have h5 : 5 ≤ c.p.M := by omega
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind,writerWP_read]
    rw [writerWP_getNode_known q rn c w hn]
    simp [htime,hindex,hsize,hlast,h4]
    repeat' first
      | wpSimplify
      | simp only [note]
      | kgPut b
      | exact writerWP_throw _ _ _ _
      | kgState
      | split
    all_goals exact writerWP_handleFull_compact_guard b _ q _ rn _ _ hn rfl hbq (by kgState)
  | some yg =>
    rcases yg with ⟨y,g⟩
    by_cases hg : g = sc
    all_goals
      unfold mergeParent
      simp only [writerWP_bind,writerWP_read]
      rw [writerWP_getNode_known q rn c w hn]
      simp [htime,hindex,hsize,hlast,h3,h5,hg]
      repeat' first
        | wpSimplify
        | simp only [note]
        | kgPut b
        | exact writerWP_throw _ _ _ _
        | kgState
        | split
      all_goals exact writerWP_handleFull_compact_guard b _ q _ rn _ _ hn rfl hbq (by kgState)

/-- A guard retained until successful completion has a height within H. -/
theorem execW_guard_height_le (p : Params) (tx : Tx) (i : Time) (view : View BVal)
    (bs : List Bool) (w : W) (b : NodeGuard)
    (he : execW p tx i view = .ok (bs,w)) (hb : GuardHeld b w) : b.h ≤ p.H := by
  by_cases h : b.h ≤ p.H
  · exact h
  have hh : p.H < b.h := by omega
  obtain ⟨pre,post,hgh,_⟩ := List.lookup_eq_some_iff.mp hb.2.1
  have hm : (b.id,b.g,b.h) ∈ w.gh := by rw [hgh]; simp
  have ht := execW_heightsTaken p tx i view bs w he b.id b.g b.h hm hh
  have hmem : b.id ∈ w.taken := by simpa using ht
  exact False.elim (hb.2.2.1 hmem)

end SIS.Tree
