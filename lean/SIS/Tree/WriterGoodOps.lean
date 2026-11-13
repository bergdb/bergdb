/-
The tree model (bergdb 024-12, TP7): the writer keeps the klongs of earlier
times, continued from SIS/Tree/WriterGood.lean: `appendKlongs`, the descents,
the delete with LE-b, the take-back and root collapse, the merges, a put, and
a transaction (`execW_good`).
-/
import SIS.Tree.WriterGood

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "gdFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (good_handleFullWith _ _ _ _ _ _ _ _ _ ?gdView ?gdState ?gdLast $hup) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case gdLast => gdFlat
  intro _ _ _))

theorem good_appendKlongs (B : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsGood B (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | gdNode
      | gdFullWith (fun _ _ => good_throw B _)
      | gdUse (good_addKeys _ _ _)
      | assumption
      | wpSplit
      | split
  | succ depth ih =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | gdNode
      | gdFullWith (fun q more => ih q more)
      | gdUse (good_addKeys _ _ _)
      | assumption
      | wpSplit
      | split

/-- A full node's replacement by a last version at the transaction's time. -/
theorem good_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w) (hlast : FlatAt c.i last.ks) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => CacheGood B c v) := by
  unfold handleFull
  refine good_handleFullWith B _ depth x [] last compact c w hv hw hlast ?_
  intro q more
  cases depth with
  | zero => exact good_throw B _
  | succ d => exact good_appendKlongs B _ _ _

theorem good_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsGood B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact good_throw B _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem good_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsGood B (f b a)) : KeepsGood B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hv hw) (fun b v hh => ih b c v hv hh)

theorem good_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsGood B (f a b)) :
    KeepsGood B (forIn xs init f) := by
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

theorem good_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsGood B (descendToSegmentRoot key segment) := by
  intro c w hv hw
  unfold descendToSegmentRoot
  wpSimplify
  gdUse (good_pathClear _)
  gdUse (good_findRoot _)
  refine good_foldlM B _ _ _ ?_ c _ hv (by assumption)
  intro node cv c w hv hw
  repeat' first
    | wpSimplify
    | gdCore
    | gdUse (good_descendLte _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## Klongs of the transaction changed in place -/

/-- The test of the writer for "the node's last klong is the transaction's
own bitmap". -/
abbrev lastDelFlag (n : KNode) (i : Time) : Bool :=
  (match n.ks.getLast? with
    | some (.del _) => true
    | _ => false) && n.lastTime == some i

/-- The test of the writer for "klong e is of the transaction": after the
node's last time klong, which is the transaction's. -/
abbrev afterFlag (n : KNode) (i : Time) (e : Nat) : Bool :=
  n.lastTime == some i && (match n.lastTimeIndex with
    | some ti => decide (ti < e)
    | none => false)

theorem and3_right (a b c : Bool) (h : (a && b && c) = true) : (b && c) = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The time klongs of n are at their places in n'. -/
def KeepsTimes (n n' : KNode) : Prop :=
  ∀ (m : Nat) (u : Time), n.ks[m]? = some (Klong.time u) → n'.ks[m]? = some (Klong.time u)

theorem keepsTimes_refl (n : KNode) : KeepsTimes n n := fun _ _ h => h

theorem KeepsTimes.trans {a b c : KNode} (h1 : KeepsTimes a b) (h2 : KeepsTimes b c) :
    KeepsTimes a c := fun m u h => h2 m u (h1 m u h)

theorem keepsTimes_add (n : KNode) (t : Time) (k : Klong) : KeepsTimes n (n.add t k) := by
  intro m u h
  have hm : m < n.ks.length := (List.getElem?_eq_some_iff.mp h).1
  rcases n.add_ks t k with he | he <;> rw [he, List.getElem?_append_left hm] <;> exact h

theorem keepsTimes_repoint (n : KNode) (e : Nat) (y : NodeId) : KeepsTimes n (n.repoint e y) := by
  intro m u h
  unfold KNode.repoint
  split
  · rename_i cv y' he
    have hne : e ≠ m := by
      intro heq
      rw [heq, h] at he
      cases he
    show (n.ks.set e _)[m]? = _
    rw [List.getElem?_set_ne hne]
    exact h
  · exact h

theorem keepsTimes_setLastDel (n : KNode) (i : Time) (bits : List Nat)
    (hflag : lastDelFlag n i = true) : KeepsTimes n (n.setAt (n.size - 1) (.del bits)) := by
  intro m u h
  simp only [lastDelFlag, Bool.and_eq_true] at hflag
  have hne : n.size - 1 ≠ m := by
    intro heq
    have hl := hflag.1
    rw [List.getLast?_eq_getElem?] at hl
    unfold KNode.size at heq
    rw [heq, h] at hl
    simp at hl
  show (n.ks.set (n.size - 1) _)[m]? = _
  rw [List.getElem?_set_ne hne]
  exact h

/-- A klong of the transaction in n, pointed in place in n', a node made from
n by changes that keep its time klongs. -/
theorem Good.repointKept (B : NodeId) (c : Ctx) (x : NodeId) (n n' : KNode) (e : Nat) (y : NodeId)
    (hpos : 0 < c.i) (h : Good B c x n') (hk : KeepsTimes n n')
    (hflag : afterFlag n c.i e = true) : Good B c x (n'.repoint e y) := by
  simp only [afterFlag, Bool.and_eq_true, beq_iff_eq] at hflag
  obtain ⟨hlt, hidx⟩ := hflag
  obtain ⟨m, hmi, hm⟩ := n.lastTime_anchor c.i hlt
  rw [hmi] at hidx
  exact Good.repoint_gt B c x n' m e y hpos (hk m c.i hm) (by simpa using hidx) h

theorem Good.setLastDel' (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (hpos : 0 < c.i) (h : Good B c x n) (hflag : lastDelFlag n c.i = true) :
    Good B c x (n.setAt (n.size - 1) (.del bits)) :=
  Good.setLastDel B c x n bits hpos h hflag

/-- The bitmap of a delete, in place or new. -/
theorem Good.delWrite (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (hasTransDel : Bool) (hpos : 0 < c.i) (h : Good B c x n)
    (hT : hasTransDel = lastDelFlag n c.i) :
    Good B c x (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add c.i (.del bits)) ∧
    KeepsTimes n (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add c.i (.del bits)) := by
  cases hd : hasTransDel with
  | true =>
    simp only [↓reduceIte]
    rw [hd] at hT
    exact ⟨Good.setLastDel B c x n bits hpos h hT.symm, keepsTimes_setLastDel n c.i bits hT.symm⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨Good.add_del B c x n bits hpos h, keepsTimes_add n c.i _⟩

/-- A pointer of a node of the transaction, set in place or by a new klong. -/
theorem Good.ptrWrite (B : NodeId) (c : Ctx) (x : NodeId) (n n' : KNode) (inPlace : Bool)
    (e cv : Nat) (y : NodeId) (hpos : 0 < c.i) (h : Good B c x n') (hk : KeepsTimes n n')
    (hI : inPlace = true → afterFlag n c.i e = true) :
    Good B c x (if inPlace then n'.repoint e y else n'.add c.i (.key cv y)) ∧
    KeepsTimes n (if inPlace then n'.repoint e y else n'.add c.i (.key cv y)) := by
  cases hd : inPlace with
  | true =>
    simp only [↓reduceIte]
    exact ⟨Good.repointKept B c x n n' e y hpos h hk (hI hd), hk.trans (keepsTimes_repoint n' e y)⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨Good.add_key B c x n' cv y hpos h, hk.trans (keepsTimes_add n' c.i _)⟩

/-- LE-b's write with room: the next child's compare value deleted, the
empty key pointed to the next child. -/
theorem Good.lebWrite (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (hasTransDel inPlace : Bool) (e : Nat) (y : NodeId) (hpos : 0 < c.i) (h : Good B c x n)
    (hT : hasTransDel = lastDelFlag n c.i) (hI : inPlace = afterFlag n c.i e) :
    Good B c x (if inPlace then
        (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add c.i (.del bits)).repoint e y
      else (if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add c.i (.del bits)).add c.i (.key 0 y)) := by
  obtain ⟨h1, k1⟩ := Good.delWrite B c x n bits hasTransDel hpos h hT
  exact (Good.ptrWrite B c x n _ inPlace e 0 y hpos h1 k1 (fun hh => by rw [← hI]; exact hh)).1

/-- The merge parent's write with room. -/
theorem Good.mergeWrite (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (bits : List Nat)
    (deleteR hasTransDel lInPlace rInPlace : Bool) (il ir cL : Nat) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) (kcv : Nat → Nat) (hpos : 0 < c.i) (h : Good B c x n)
    (hT : hasTransDel = lastDelFlag n c.i) (hL : lInPlace = afterFlag n c.i il)
    (hR : rInPlace = true → afterFlag n c.i ir = true) :
    Good B c x (match m2 with
      | some (y, g) =>
        if rInPlace then
          (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add c.i (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add c.i (.del bits)).add c.i (.key cL m1)).repoint ir y
        else (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add c.i (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add c.i (.del bits)).add c.i (.key cL m1)).add c.i (.key (kcv g) y)
      | none =>
        if lInPlace then
          (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add c.i (.del bits)).repoint il m1
        else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add c.i (.del bits)).add c.i (.key cL m1)) := by
  have h1 : Good B c x (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add c.i (.del bits)) ∧
      KeepsTimes n (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add c.i (.del bits)) := by
    cases deleteR with
    | false => simpa only [Bool.not_false, ↓reduceIte] using ⟨h, keepsTimes_refl n⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact Good.delWrite B c x n bits hasTransDel hpos h hT
  obtain ⟨h2, k2⟩ := Good.ptrWrite B c x n _ lInPlace il cL m1 hpos h1.1 h1.2
    (fun hh => by rw [← hL]; exact hh)
  cases m2 with
  | none => exact h2
  | some pair =>
    obtain ⟨y, g⟩ := pair
    exact (Good.ptrWrite B c x n _ rInPlace ir (kcv g) y hpos h2 k2 hR).1

/-! ## The delete -/

macro "gdHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (good_handleFull ?gdB _ _ _ _ _ _ ?gdView ?gdState ?gdLast) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case gdLast => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  intro _ _ _))

macro "gdAppend" : tactic => `(tactic| first
  | gdHandle
  | gdUse (good_appendKlongs _ _ _ _)
  | gdUse (good_addKeys _ _ _)
  | gdUse (good_descendLte _ _ _ _))

/-- A node's klongs of the transaction changed in place, or klongs added. -/
macro "gdWrite" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine good_putNode ?gdB _ _ _ _ _ ?gdState ?gdInput ?gdPost)
  case gdState => assumption
  case gdInput => first
    | (apply Good.setLastDel' _ _ _ _ _ (by assumption) (by assumption); assumption)
    | (refine Good.lebWrite _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) rfl rfl)
    | (refine Good.mergeWrite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) rfl rfl ?_
       first
        | exact and3_right _ _ _
        | exact fun h => h)
  intro _ _ _))

set_option maxHeartbeats 1000000 in
theorem good_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsGood B (appendDeleteKlong x depth cv) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | gdWrite
    | gdCore
    | gdAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1400000 in
theorem good_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) :
    KeepsGood B (emptyKeyNext x depth) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | gdWrite
    | gdCore
    | gdAppend
    | wpSplit
    | split
    | contradiction

theorem good_unlink (B : NodeId) (x : NodeId) : KeepsGood B (unlink x) := by
  intro c w hv hw
  unfold unlink
  repeat' first | wpSimplify | gdCore | wpSplit | split | contradiction

theorem good_retarget (B : NodeId) (q src dst : NodeId) : KeepsGood B (retarget q src dst) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold retarget
  repeat' first
    | wpSimplify
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine good_putNode B _ _ _ _ _ (by assumption)
         (Good.retarget B _ _ _ _ _ hpos (by assumption) (by assumption)) ?_
       intro _ _ _)
    | gdCore
    | wpSplit
    | split
    | contradiction

theorem good_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsGood B (canTakeBack x parent cv) := by
  intro c w hv hw
  unfold canTakeBack
  repeat' first | wpSimplify | gdCore | wpSplit | split | contradiction

theorem good_takeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsGood B (takeBack x parent cv) := by
  intro c w hv hw
  unfold takeBack
  repeat' first
    | wpSimplify
    | gdCore
    | gdUse (good_retarget _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-- `takeBackRoot` of a node of the transaction: the klong that links it is
of the transaction, and is pointed in place. -/
theorem good_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hx : B ≤ x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => CacheGood B c v) := by
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | ((with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
       refine good_putNode B _ _ _ _ _ (by assumption)
         (Good.repointLink B _ _ _ _ _ _ _ hv (by assumption) (by assumption) hx) ?_
       intro _ _ _)
    | gdCore
    | wpSplit
    | split
    | contradiction

theorem good_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsGood B (replaceRoot x depth only) := by
  intro c w hv hw
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | gdCore
    | gdAppend
    | gdUse (good_unlink _ _)
    | wpSplit
    | split
    | contradiction

theorem good_collapseRoot (B : NodeId) (key : Key) (segment fuel : Nat) :
    KeepsGood B (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact good_throw B _
  | succ fuel ih =>
    intro c w hv hw
    have hpos := hv.pos
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (good_descendToSegmentRoot _ _ _)
      | ((with_unfolding_none guard_target = WriterWP (takeBackRoot _ _ _) _ _ _)
         refine writerWP_mono (good_takeBackRoot B _ _ _ _ _ hv (by assumption)
           (Blank.ge B _ _ hv (blank_of_firstTime B _ _ _ hpos (by assumption) (by assumption)))) ?_
         intro _ _ _)
      | gdUse (good_replaceRoot _ _ _ _)
      | gdUse ih
      | wpSplit
      | split
      | contradiction

/-! ## The merges -/

theorem good_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsGood B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact good_throw B _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem good_descendToHeight (B : NodeId) (key : Key) (g h : Nat) :
    KeepsGood B (descendToHeight key g h) := by
  intro c w hv hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | gdCore
    | gdUse (good_descendToSegmentRoot _ _ _)
    | gdUse (good_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem good_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsGood B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold mergeParent
  repeat' first
    | wpSimplify
    | gdWrite
    | gdCore
    | gdAppend
    | wpSplit
    | split
    | contradiction

theorem good_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsGood B (sibling q pn i inner) := by
  intro c w hv hw
  unfold sibling
  repeat' first | wpSimplify | gdCore | wpSplit | split | contradiction

set_option maxHeartbeats 1600000 in
theorem good_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsGood B (merge x d) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | gdCore
    | gdUse (good_unlink _ _)
    | gdUse (good_retarget _ _ _ _)
    | gdUse (good_sibling _ _ _ _ _)
    | gdUse (good_mergeParent _ _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem good_mergeUp (B : NodeId) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsGood B (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact good_throw B _
  | succ fuel ih =>
    intro c w hv hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (good_descendToHeight _ _ _ _)
      | gdUse (good_merge _ _ _)
      | gdUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem good_afterDelete (B : NodeId) (key : Key) (g h : Nat) :
    KeepsGood B (afterDelete key g h) := by
  intro c w hv hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | gdCore
    | gdUse (good_mergeUp _ _ _ _ _ _)
    | gdUse (good_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The upward unlink, a put, a transaction -/

theorem good_climb (B : NodeId) (depth : Nat) : KeepsGood B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hw
    unfold climb
    repeat' first | wpSimplify | gdCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hw
    unfold climb
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (good_canTakeBack _ _ _ _)
      | gdUse ih
      | wpSplit
      | split
      | contradiction

macro "gdFoldWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_good (good_foldlM $b _ _ _ ?gdBody) _ _ _ ?gdView ?gdState ?gdPost)
  case gdBody =>
    intro b a c w hv hw
    repeat' first
      | wpSimplify
      | gdCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case gdView => assumption
  case gdState => assumption
  intro _ _ _))

macro "gdForWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_good (good_forIn $b _ _ _ ?gdBody) _ _ _ ?gdView ?gdState ?gdPost)
  case gdBody =>
    intro a b c w hv hw
    repeat' first
      | wpSimplify
      | gdCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case gdView => assumption
  case gdState => assumption
  intro _ _ _))

set_option maxHeartbeats 1600000 in
theorem good_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsGood B (deleteUpward leaf depth cv key) := by
  intro c w hv hw
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | gdCore
    | gdUse (good_appendDeleteKlong _ _ _ _)
    | gdUse (good_emptyKeyNext _ _ _)
    | gdUse (good_afterDelete _ _ _ _)
    | gdFoldWith B using fail
    | gdForWith B using (first | gdUse (good_takeBack _ _ _ _) | gdUse (good_unlink _ _))
    | gdUse (good_climb _ _)
    | gdUse (good_mergeUp _ _ _ _ _ _)
    | gdUse (good_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem good_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsGood B (setValue segRoot cv key value) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | gdCore
    | gdAppend
    | gdUse (good_deleteUpward _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem good_setNode (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsGood B (setNode segRoot cv create) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold setNode
  repeat' first
    | wpSimplify
    | gdCore
    | gdAppend
    | wpSplit
    | split
    | contradiction

theorem good_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsGood B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact good_throw B _
  | cons cv rest ih =>
    cases rest with
    | nil => exact good_setValue B _ _ _ _
    | cons cv2 rest =>
      intro c w hv hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | gdCore
        | gdUse (good_setNode _ _ _ _)
        | gdUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem good_putKv (B : NodeId) (op : Op) : KeepsGood B (putKv op) := by
  cases op <;> (intro c w hv hw; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | gdCore
      | gdUse (good_putSegs _ _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem good_ops (B : NodeId) (ops : List Op) : KeepsGood B (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hv hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (good_putKv B op c w hv hw) ?_
    intro noop v hh
    have hi := ih c v hv hh
    simpa only [writerWP_bind, writerWP_pure] using hi

/-- A successful transaction of the writer changes no klong of an earlier
time: every node of its overlay has, before the transaction's time, the
klongs that the node has in the writer's view, and no later time klong. -/
theorem execW_good (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hv : ViewGood tx.base { p := p, i := i, view := rootless v })
    (he : execW p tx i v = .ok (bs, w)) :
    CacheGood tx.base { p := p, i := i, view := rootless v } w := by
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
      exact good_ops tx.base tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } hv
        ⟨Nat.le_refl _, by intro q hq; cases hq⟩ bs w hr

end SIS.Tree
