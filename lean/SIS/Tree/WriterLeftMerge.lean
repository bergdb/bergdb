/-
The tree model (bergdb 024-12, TP7): the empty key in every inner node of the
writer's overlay, continued from SIS/Tree/WriterLeftSplit.lean: the delete's
bitmaps, LE-b, the unlink, the take-back, root collapse and the merges.
-/
import SIS.Tree.WriterLeftSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The bitmaps of a delete -/

theorem left_lastDel {n : KNode} {t : Time} (h : lastDelFlag n t = true) :
    ∃ b0, n.ks.getLast? = some (.del b0) := by
  simp only [lastDelFlag, Bool.and_eq_true] at h
  obtain ⟨h1, _⟩ := h
  revert h1
  cases hl : n.ks.getLast? with
  | none => simp
  | some k => cases k <;> simp

theorem left_add_del' (n : KNode) (t : Time) (bits : List Nat)
    (hG : n.leaf = false → Live0Given n.ks bits) : LeftNode (n.add t (.del bits)) := by
  cases hn : n.leaf with
  | true => exact left_leaf _ (by rw [KNode.add_leaf]; exact hn)
  | false => exact left_add_del n t bits (hG hn)

theorem left_setAt_del' (n : KNode) (t : Time) (bits : List Nat) (hflag : lastDelFlag n t = true)
    (hG : n.leaf = false → Live0Given n.ks bits) :
    LeftNode (n.setAt (n.size - 1) (.del bits)) := by
  cases hn : n.leaf with
  | true => exact left_leaf _ hn
  | false =>
    obtain ⟨b0, hb0⟩ := left_lastDel hflag
    exact left_setAt_del n bits b0 hb0 (hG hn)

theorem left_delWrite (n : KNode) (t : Time) (bits : List Nat) (hasTransDel : Bool)
    (hT : hasTransDel = lastDelFlag n t) (hG : n.leaf = false → Live0Given n.ks bits) :
    LeftNode (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)) := by
  cases hd : hasTransDel with
  | true => exact left_setAt_del' n t bits (by rw [← hT, hd]) hG
  | false => exact left_add_del' n t bits hG

/-- The bitmap of a delete of compare value cv: an inner node's cv is not the
empty key's. -/
theorem left_given_del (n : KNode) (cv : Nat) (hcv : n.leaf = false → cv ≠ 0) (hL : LeftNode n) :
    n.leaf = false → Live0Given n.ks (bitsUnion n.lastBitmap (n.bitsOf cv)) :=
  fun h => left_given_union n cv (hcv h) (hL h).2

theorem left_head_del (n : KNode) (t : Time) (cv : Nat) (hcv : n.leaf = false → cv ≠ 0)
    (hL : LeftNode n) :
    n.leaf = false → Head0 (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks :=
  fun h => left_head0_lastVersionGivenDel n t _ (left_given_del n cv hcv hL h)

/-! ## LE-b -/

/-- LE-b's next child is not the empty key: every klong of the empty key is in
the bitmap it skips. -/
theorem left_leb_jcv (n : KNode) (i jcv : Nat) (jy : NodeId)
    (h : n.ks.zipIdx.foldl (nextPhysicalStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none =
      some (i, jcv, jy)) : jcv ≠ 0 := by
  have hh := nextPhysical_live n.ks (bitsUnion n.lastBitmap (n.bitsOf 0)) i jcv jy h
  intro h0
  subst h0
  apply hh.2
  rw [mem_bitsUnion_iff]
  exact Or.inr ((n.mem_bitsOf_iff 0 i).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hh.1⟩)

/-- LE-b's bitmap keeps the empty key's last klong e live. -/
theorem left_leb_given (n : KNode) (e jcv : Nat) (he : (n.bitsOf 0).getLast? = some e)
    (hc : ¬ n.lastBitmap.contains e = true) (hj : jcv ≠ 0) :
    Live0Given n.ks (bitsUnion n.lastBitmap (n.bitsOf jcv)) := by
  have hm : e ∈ n.bitsOf 0 := List.mem_of_getLast? he
  obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff 0 e).mp hm
  refine ⟨e, y, List.mem_zipIdx_iff_getElem?.mp hy, ?_⟩
  have hn : e ∉ bitsUnion n.lastBitmap (n.bitsOf jcv) := by
    rw [mem_bitsUnion_iff]
    rintro (h1 | h1)
    · simp [h1] at hc
    · exact n.not_mem_bitsOf_of_key_ne 0 jcv y e hy (Ne.symm hj) h1
  simpa using hn

/-- LE-b's write with room. -/
theorem left_lebWrite (n : KNode) (t : Time) (bits : List Nat) (hasTransDel inPlace : Bool)
    (e : Nat) (y : NodeId) (hT : hasTransDel = lastDelFlag n t)
    (hG : Live0Given n.ks bits) :
    LeftNode (if inPlace then
        (if hasTransDel then n.setAt (n.size - 1) (.del bits) else n.add t (.del bits)).repoint e y
      else (if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).add t (.key 0 y)) := by
  have h1 := left_delWrite n t bits hasTransDel hT (fun _ => hG)
  cases inPlace
  · exact h1.add_key _ _ _
  · exact h1.repoint _ _

/-! ## The merge parent -/

theorem left_mp_given (n : KNode) (cR : Nat) (d : Bool) (hcR : cR ≠ 0) (hL : LeftNode n) :
    n.leaf = false →
      Live0Given n.ks (if d then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap) := by
  intro h
  cases d
  · exact (hL h).2
  · exact left_given_union n cR hcR (hL h).2

theorem left_mergeWrite (n : KNode) (t : Time) (bits : List Nat)
    (deleteR hasTransDel lInPlace rInPlace : Bool) (il ir cL : Nat) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) (kcv : Nat → Nat) (hL : LeftNode n)
    (hT : hasTransDel = lastDelFlag n t) (hG : n.leaf = false → Live0Given n.ks bits) :
    LeftNode (match m2 with
      | some (y, g) =>
        if rInPlace then
          (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).add t (.key cL m1)).repoint ir y
        else (if lInPlace then
            (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).repoint il m1
          else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
              else n.add t (.del bits)).add t (.key cL m1)).add t (.key (kcv g) y)
      | none =>
        if lInPlace then
          (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add t (.del bits)).repoint il m1
        else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
            else n.add t (.del bits)).add t (.key cL m1)) := by
  have h1 : LeftNode (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
      else n.add t (.del bits)) := by
    cases deleteR
    · exact hL
    · exact left_delWrite n t bits hasTransDel hT hG
  have h2 : LeftNode (if lInPlace then
      (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).repoint il m1
    else (if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del bits)
        else n.add t (.del bits)).add t (.key cL m1)) := by
    cases lInPlace
    · exact h1.add_key _ _ _
    · exact h1.repoint _ _
  cases m2 with
  | none => exact h2
  | some p =>
    obtain ⟨y, g⟩ := p
    cases rInPlace
    · exact h2.add_key _ _ _
    · exact h2.repoint _ _

/-! ## The retarget -/

theorem left_retarget_node (n : KNode) (F : Klong × Nat → Klong)
    (hF : ∀ q, klongShape (F q) = klongShape q.1) (hL : LeftNode n) :
    LeftNode { n with ks := n.ks.zipIdx.map F } :=
  hL.of_shape _ rfl (left_zipIdx_shape n.ks F hF)

/-! ## The walk: the delete's steps -/

theorem left_takenBack (B x : NodeId) (E : List NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE E w)
    (hl : vr.nodes.lookup x = some n) (hk : Kept vr w) :
    WriterWP (takenBack x) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE E v) := by
  refine writerWP_mono (writerWP_and (writerWP_and (good_takenBack B x c w hv hw)
    (book_takenBack B x c vr w n hl hk hb))
    (?_ : WriterWP (takenBack x) c w (fun _ v => v.nodes = w.nodes))) ?_
  · simp only [takenBack, writerWP_modify]
  · rintro _ v ⟨⟨hc, hb', hk'⟩, he⟩
    refine ⟨hc, hb', hk', fun q hq => hn q ?_⟩
    rw [he] at hq
    exact hq

macro "lfTake" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
  (refine writerWP_mono (left_takenBack ?gdB _ ?lfE _ ?bkVr _ ?bkN ?gdView ?gdState ?bkState ?lfState ?bkLook ?bkKept) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case bkLook => assumption
  case bkKept => bkChain
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_retarget_shape (ti : Nat) (src dst : NodeId) (q : Klong × Nat) :
    klongShape ((fun (q : Klong × Nat) => match q with
      | (k, i) => match k with
        | .key cv y => if ti < i && y == src then Klong.key cv dst else k
        | _ => k) q) = klongShape q.1 := by
  rcases q with ⟨k, i⟩
  cases k with
  | key cv y =>
    simp only
    split <;> rfl
  | time t => rfl
  | del b => rfl

macro_rules
  | `(tactic| lfKs) => `(tactic| first
    | exact left_retarget_node _ _ (left_retarget_shape _ _ _) (by lfRead)
    | exact left_setAt_del' _ _ _ (by assumption) (by assumption)
    | exact left_add_del' _ _ _ (by assumption)
    | exact left_lebWrite _ _ _ _ _ _ _ rfl
        (left_leb_given _ _ _ (by assumption) (by assumption)
          (left_leb_jcv _ _ _ _ (by assumption)))
    | exact left_mergeWrite _ _ _ _ _ _ _ _ _ _ _ _ _ (by lfRead) rfl
        (left_mp_given _ _ _ (by assumption) (by lfRead)))

theorem left_head0_rename (i : Time) (old : List Klong) (k : Klong) (c1 : Nat) (y1 : NodeId)
    (rest : List Klong) (he : old = k :: .key c1 y1 :: rest) (hf : FlatAt i old) :
    Head0 (k :: .key 0 y1 :: rest) := by
  obtain ⟨r', hr', _⟩ := hf
  rw [he] at hr'
  injection hr' with h1 _
  subst h1
  exact ⟨i, y1, rest, rfl⟩

syntax "lfHead" : tactic
macro_rules
  | `(tactic| lfHead) => `(tactic| first
    | exact left_head0_lastVersionGivenDel _ _ _
        (left_mp_given _ _ _ (by assumption) (by lfRead) (by assumption))
    | (refine Head0.replaceK ?_ _ _ _ _ (by assumption); lfHead)
    | (refine Head0.insertKey ?_ _ _; lfHead))

macro "lfHeadMP" : tactic => `(tactic| (intro _; lfHead))

macro "lfHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (left_handleFull ?gdB _ _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdLast ?lfX) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case gdLast => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  case lfX => first
    | exact ⟨_, _, by assumption, by bkChain, by assumption⟩
    | exact ⟨_, _, by assumption, by bkChain, fun _ => left_head0_rename _ _ _ _ _ _ (by assumption) (by gdFlat)⟩
    | exact ⟨_, _, by assumption, by bkChain, by lfHeadMP⟩
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_unlink (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hv : ViewGood B c)
    (_hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : baseKlongs c.view x ≠ [] ∨ ∃ n0, w.nodes.lookup x = some n0 ∧ n0.leaf = true) :
    WriterWP (unlink x) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE [] v) := by
  unfold unlink
  wpSimplify
  refine writerWP_mono (left_getNode B [] x c w hv hl hw hb hn) ?_
  rintro n w1 ⟨hc1, hb1, hk1, hn1, hg1, hlk1, hr1⟩
  have hbase : n.leaf = false → baseKlongs c.view x ≠ [] := by
    intro hlf
    rcases hx with h | ⟨n0, hl0, hlf0⟩
    · exact h
    · rw [nex_run_kept_leaf hk1 hl0 hlk1, hlf0] at hlf
      cases hlf
  split
  · refine left_putNode_toPrev B [] x n c w1 _ hv hl hc1 hb1 hn1 hg1 hlk1 hbase ?_
    intro _ v hc hb' hk hn'
    exact ⟨hc, hb', hk1.trans hk, hn'⟩
  · simp only [writerWP_pure]
    exact ⟨hc1, hb1, hk1, hn1⟩

macro "lfUnlink " h:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (unlink _) _ _ _)
  (refine writerWP_mono (left_unlink ?gdB _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState $h) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_retarget (B : NodeId) (q src dst : NodeId) : KeepsLeft0 B (retarget q src dst) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold retarget
  repeat' first
    | wpSimplify
    | lfCore
    | wpSplit
    | split
    | contradiction

theorem left_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsLeft0 B (canTakeBack x parent cv) := by
  intro c w hv hp hl hw hb hn
  unfold canTakeBack
  repeat' first | wpSimplify | lfCore | wpSplit | split | contradiction

theorem left_takeBack (B x parent : NodeId) (cv : Nat) (c : Ctx) (w vr : W) (n : KNode)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hlk : vr.nodes.lookup x = some n) (hk : Kept vr w) :
    WriterWP (takeBack x parent cv) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE [] v) := by
  unfold takeBack
  repeat' first
    | wpSimplify
    | lfCore
    | lfTake
    | lfUse0 (left_retarget _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem left_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w) (hx : B ≤ x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ LeftCacheE [] v) := by
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | lfCore
    | lfTake
    | wpSplit
    | split
    | contradiction

theorem left_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : baseKlongs c.view x ≠ []) :
    WriterWP (replaceRoot x depth only) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ LeftCacheE [] v) := by
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | lfCore
    | lfUnlink (Or.inl hx)
    | lfUse0 (left_appendKlongs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem left_base_ne (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hg : Good B c x n)
    (hpos : 0 < c.i) (hr : LeftRead [] x n) (hlf : ¬ n.leaf = true)
    (hf : ¬ (n.firstTime == some c.i) = true) : baseKlongs c.view x ≠ [] :=
  nex_base B c x n hg hpos (hr.node (by simpa using hlf)).1 hf

macro "lfRR" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceRoot _ _ _) _ _ _)
  (refine writerWP_mono (left_replaceRoot ?gdB _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?lfBase) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfBase => exact left_base_ne _ _ _ _ ‹_› ‹_› (by assumption) (by assumption) (by assumption)
  rintro _ _ ⟨_, _, _, _⟩))

macro "lfTBR" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takeBackRoot _ _ _) _ _ _)
  (refine writerWP_mono (left_takeBackRoot ?gdB _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdX) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case gdX => exact Blank.ge _ _ _ ‹ViewGood _ _› (blank_of_firstTime _ _ _ _ (by assumption) (by assumption) (by assumption))
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_collapseRoot (B : NodeId) (key : Key) (segment fuel : Nat) :
    KeepsLeft0 B (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact (left_throw B _).zero
  | succ fuel ih =>
    intro c w hv hp hl hw hb hn
    have hpos := hv.pos
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (left_descendToSegmentRoot _ _ _)
      | lfTBR
      | lfRR
      | lfUse0 ih
      | wpSplit
      | split
      | contradiction

set_option maxHeartbeats 1600000 in
/-- The delete's bitmap in node x: an inner x does not lose its empty key, as
the compare value deleted in it is not the empty key's. -/
theorem left_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : ∃ n0, w.nodes.lookup x = some n0 ∧ (n0.leaf = false → cv ≠ 0)) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ LeftCacheE [] v) := by
  have hpos := hv.pos
  obtain ⟨n0, hl0, hcv0⟩ := hx
  unfold appendDeleteKlong
  wpSimplify
  refine writerWP_mono (left_getNode B [] x c w hv hl hw hb hn) ?_
  rintro n w1 ⟨hc1, hb1, hk1, hn1, hg1, hlk1, hr1⟩
  have hcv : n.leaf = false → cv ≠ 0 := fun h => hcv0 (by rw [← nex_run_kept_leaf hk1 hl0 hlk1]; exact h)
  have hLN : LeftNode n := hr1.node
  have hG := left_given_del n cv hcv hLN
  have hH := left_head_del n c.i cv hcv hLN
  clear hn
  repeat' first
    | wpSimplify
    | lfCore
    | lfHandle
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
/-- LE-b: the empty key gets the next child's pointer and stays live. -/
theorem left_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) :
    KeepsLeft0 B (emptyKeyNext x depth) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | lfCore
    | lfHandle
    | wpSplit
    | split
    | contradiction

theorem left_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsLeft0 B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact (left_throw B _).zero
  | succ fuel ih =>
    intro c w hv hp hl hw hb hn
    unfold descendHeight
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (ih _)
      | wpSplit
      | split
      | contradiction

theorem left_descendToHeight (B : NodeId) (key : Key) (g h : Nat) :
    KeepsLeft0 B (descendToHeight key g h) := by
  intro c w hv hp hl hw hb hn
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | lfCore
    | lfUse0 (left_descendToSegmentRoot _ _ _)
    | lfUse0 (left_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

macro "lfGiven" : tactic => `(tactic| first
  | assumption
  | exact fun h => ((LeftRead.node (by assumption)) h).2
  | exact left_given_del _ _ (fun _ => (by assumption)) (by lfRead))

macro_rules
  | `(tactic| lfKs) => `(tactic| first
    | exact left_add_del' _ _ _ (by lfGiven)
    | exact left_setAt_del' _ _ _ (by assumption) (by lfGiven)
    | (refine LeftNode.add_key ?_ _ _ _; lfKs)
    | (refine LeftNode.repoint ?_ _ _; lfKs))

set_option maxHeartbeats 1600000 in
/-- The merge's parent: the right child's compare value, deleted or pointed,
is not the empty key's. -/
theorem left_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (hcR : cR ≠ 0) :
    KeepsLeft0 B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold mergeParent
  repeat' first
    | wpSimplify
    | lfCore
    | lfHandle
    | wpSplit
    | split
    | contradiction

/-! ## The merge -/

theorem left_cap {p : Params} (hp : MergeParamsOK p) : 1 ≤ p.mergeMax := by
  obtain ⟨h1, h2, -⟩ := hp
  omega

theorem left_merge_new1 (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId)) (t : Time)
    (hcap : 1 ≤ cap)
    (hchk : ¬ (inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0)) = true) :
    LeftNode ⟨!inner, newKlongs t (mergeKlongs inner cap cR lvL lvR).1⟩ := by
  cases inner with
  | false => exact left_leaf _ rfl
  | true =>
    have hL : lvL.head?.map (·.1) = some 0 := by
      cases h : lvL.head?.map (·.1) with
      | none => simp [h] at hchk
      | some a => by_cases ha : a = 0 <;> simp_all
    exact left_newKlongs _ t _ (left_mergeKlongs cap cR lvL lvR hcap hL).1

theorem left_merge_new2 (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId)) (t : Time)
    (ks2 : List (Nat × NodeId)) (g2 : Nat) (hcap : 1 ≤ cap)
    (hchk : ¬ (inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0)) = true)
    (he : (mergeKlongs inner cap cR lvL lvR).2 = some (ks2, g2)) :
    LeftNode ⟨!inner, newKlongs t ks2⟩ := by
  cases inner with
  | false => exact left_leaf _ rfl
  | true =>
    have hL : lvL.head?.map (·.1) = some 0 := by
      cases h : lvL.head?.map (·.1) with
      | none => simp [h] at hchk
      | some a => by_cases ha : a = 0 <;> simp_all
    exact left_newKlongs _ t _ ((left_mergeKlongs cap cR lvL lvR hcap hL).2 ks2 g2 he)

theorem left_cv_of (n : KNode) (i c : Nat) (y : NodeId) (h : n.ks[i]? = some (.key c y)) :
    n.cv? i = some c := by
  simp [KNode.cv?, h]

/-- The merge with the left sibling: the right node is x, whose compare value
is above the left one's. -/
theorem left_cR_left (pn : KNode) (cx ix ib b cR : Nat) (hix : (mergeIdx pn cx).1 = some ix)
    (hib : (mergeIdx pn cx).2.2 = some (ib, b)) (hc : pn.cv? ix = some cR) : cR ≠ 0 := by
  have ho := left_mergeIdx_ord pn cx
  obtain ⟨y, hy⟩ := ho.1 ix hix
  obtain ⟨hb, -⟩ := ho.2.2 ib b hib
  rw [left_cv_of pn ix cx y hy] at hc
  cases hc
  omega

/-- The merge with the right sibling: its compare value is above x's. -/
theorem left_cR_right (pn : KNode) (cx ia a cR : Nat) (hia : (mergeIdx pn cx).2.1 = some (ia, a))
    (hc : pn.cv? ia = some cR) : cR ≠ 0 := by
  have ho := left_mergeIdx_ord pn cx
  obtain ⟨ha, y, hy⟩ := ho.2.1 ia a hia
  rw [left_cv_of pn ia a y hy] at hc
  cases hc
  omega

theorem left_live_ks (n : KNode) (h : n.live ≠ []) : n.ks ≠ [] := by
  intro hk
  apply h
  obtain ⟨leaf, ks⟩ := n
  simp only at hk
  subst hk
  simp [KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel]

theorem left_chk_l (a b : KNode) (h : ¬ (a.live.isEmpty || b.live.isEmpty) = true) : a.ks ≠ [] :=
  left_live_ks a (by intro he; simp [he] at h)

theorem left_chk_r (a b : KNode) (h : ¬ (a.live.isEmpty || b.live.isEmpty) = true) : b.ks ≠ [] :=
  left_live_ks b (by intro he; simp [he] at h)

/-- The sibling read: `Good`, in the overlay. -/
theorem left_sibling' (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx)
    (w : W) (hv : ViewGood B c) (_hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w) :
    WriterWP (sibling q pn i inner) c w (fun r v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE [] v ∧ Good B c r.1 r.2 ∧ v.nodes.lookup r.1 = some r.2) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | lfNode
    | exact writerWP_throw _ _ _ _
    | exact ⟨by assumption, by assumption, by bkChain, by assumption, by assumption,
        by assumption⟩
    | wpSplit
    | split
    | contradiction

macro "lfSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (left_sibling' ?gdB _ _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  rintro ⟨_, _⟩ _ ⟨_, _, _, _, _, _⟩))

macro "lfMP" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (mergeParent _ _ _ _ _ _ _ _) _ _ _)
  (refine' writerWP_of_left0 (left_mergeParent _ _ _ _ _ _ _ _ _ ?lfCR) _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdPost)
  case lfCR => first
    | exact left_cR_left _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
    | exact left_cR_right _ _ _ _ _ (by assumption) (by assumption)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  intro _ _ _ _ _ _))

macro "lfUnlinkM" : tactic => `(tactic| first
  | lfUnlink (Or.inl (nex_base _ _ _ _ (by assumption) (by assumption) (left_chk_l _ _ (by assumption)) (by assumption)))
  | lfUnlink (Or.inl (nex_base _ _ _ _ (by assumption) (by assumption) (left_chk_r _ _ (by assumption)) (by assumption))))

macro_rules
  | `(tactic| lfKs) => `(tactic| first
    | exact left_merge_new1 _ _ _ _ _ _ (left_cap (by assumption)) (by assumption)
    | exact left_merge_new2 _ _ _ _ _ _ _ _ (left_cap (by assumption)) (by assumption) (by assumption))

set_option maxHeartbeats 3200000 in
/-- A merge: its new nodes start with the empty key when inner (the writer
checks that both live lists do), the parent's right compare value is not the
empty key's, and the nodes merged are left out as nodes of the view. -/
theorem left_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsLeft0 B (merge x d) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | lfCore
    | lfTake
    | lfUnlinkM
    | lfUse0 (left_retarget _ _ _ _)
    | lfSibling
    | lfMP
    | wpSplit
    | split
    | contradiction

end SIS.Tree
