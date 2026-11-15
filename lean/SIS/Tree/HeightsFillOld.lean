/-
`hchk`'s `checkOld3` proved (bergdb 024-12): the node a take-back's parent is
pointed to, the take-back's made-for id, is a node of the view at every state
between operations (`stateOK_madeForView`, MadeForView.lean), and the delete's
steps up to the upward loop keep the made-for ids. So `putKvDelChk4`, the checked
copy with neither the stop-node checks nor `checkOld3`, runs as `putKvDelChk2`
from every state with `PutInv`, the fill and that fact (`rwp_putKvDelChk4`), and
`OpDelChk4OKL` gives `OpDelChk2OKL` (`opDelChk2OKR_of_chk4`). Left in `hchk`: the
holders before each take-back (`checkFree`, `checkRoot`); the upward loop's
`checkFree` is proved in HeightsFillLoop.lean, whose top theorem
`invGetScanOK_merges_joint5` takes `OpDelChk5OKL`.
-/
import SIS.Tree.HeightsFillStop
import SIS.Tree.MadeForView

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The copy without the take-back's `checkOld3` -/

/-- `takeBackChk3` without `checkOld3`. -/
def takeBackChk4 (x parent : NodeId) (cv : Nat) : M Unit := do
  let c ← read
  let pn ← getNode parent
  match (← replacedBy x), pn.linkIndex x cv with
  | some old, some _ =>
    if pn.lastTime != some c.i then
      throw s!"Bug: take back of key node {x} at {c.i}: no klong of tt to it"
    retarget parent x old
    checkFree x
    takenBack x
    note "up.takeback"
  | _, _ => throw s!"Bug: take back of key node {x} at {c.i}: no node it replaces, or no klong to it"

/-- `deleteUpwardChk3` with `takeBackChk4`. -/
def deleteUpwardChk4 (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    afterDeleteChk key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBackChk4 x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if sn.leaf then
    note "up.stop-at-segment-leaf"
    let _ ← appendDeleteKlong s stop cs
    afterDeleteChk key gs hs
    return false
  if sn.smallestLive != some 0 then
    throw s!"Bug: the upward unlink at {tt}: inner node {s} has no live klong of the empty key"
  if cs != 0 then
    let _ ← appendDeleteKlong s stop cs
  else
    emptyKeyNext s stop
  if c.p.merges then
    let _ ← mergeUp key gs c.p.fuel hs false
  collapseRoot key segment (c.p.fuel)
  return false

/-- `setValueDelChk3` with `deleteUpwardChk4`. -/
def setValueDelChk4 (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk4 leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk3` with `setValueDelChk4`. -/
def putSegsDelChk4 (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk4 segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk4 key rest next

/-- The delete's checked copy with the holders' checks only. -/
def putKvDelChk4 (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk4 key key root

/-! ## The frame, with the made-for ids -/

/-- `LeafFr` with the same made-for ids. -/
def LeafFrM (w v : W) : Prop := LeafFr w v ∧ v.madeFor = w.madeFor

theorem LeafFrM.refl (w : W) : LeafFrM w w := ⟨LeafFr.refl w, rfl⟩

theorem LeafFrM.trans {a b d : W} (h1 : LeafFrM a b) (h2 : LeafFrM b d) : LeafFrM a d :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem leafFrM_getNode (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun n v => LeafFrM w v ∧ v.nodes.lookup x = some n) :=
  writerWP_mono (writerWP_and (leafFr_getNode x c w) (writerWP_getNode_frame x c w))
    (fun _ _ h => ⟨⟨h.1.1, h.2.2.2.2.2.2.1⟩, h.1.2⟩)

theorem leafFrM_note (s : String) (c : Ctx) (w : W) : WriterWP (note s) c w (fun _ v => LeafFrM w v) := by
  unfold note; simp only [writerWP_modify]; exact ⟨⟨rfl, fun y n hy => ⟨n, hy, rfl⟩⟩, rfl⟩

theorem leafFrM_takenBack (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (takenBack x) c w (fun _ v => LeafFrM w v) := by
  unfold takenBack; simp only [writerWP_modify]; exact ⟨⟨rfl, fun y n hy => ⟨n, hy, rfl⟩⟩, rfl⟩

theorem leafFrM_putNode (x : NodeId) (m : KNode) (c : Ctx) (w : W)
    (hm : ∀ n, w.nodes.lookup x = some n → m.leaf = n.leaf) :
    WriterWP (putNode x m) c w (fun _ v => LeafFrM w v) := by
  refine writerWP_mono (writerWP_and (leafFr_putNode x m c w hm) (?_ : WriterWP (putNode x m) c w
    (fun _ v => v.madeFor = w.madeFor))) (fun _ _ h => ⟨h.1, h.2⟩)
  unfold putNode; simp only [writerWP_modify]

theorem leafFrM_unlink (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (unlink x) c w (fun _ v => LeafFrM w v) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFrM_getNode x c w) ?_
  rintro n v ⟨hv, hl⟩
  split
  · refine writerWP_mono (leafFrM_putNode x _ c v (fun n' h => by rw [hl] at h; cases h; rfl)) ?_
    exact fun _ u hu => hv.trans hu
  · simp only [writerWP_pure]; exact hv

theorem leafFrM_retarget (q src dst : NodeId) (c : Ctx) (w : W) :
    WriterWP (retarget q src dst) c w (fun _ v => LeafFrM w v) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFrM_getNode q c w) ?_
  rintro n v ⟨hv, hl⟩
  split
  · refine writerWP_mono (leafFrM_putNode q _ c v (fun n' h => by rw [hl] at h; cases h; rfl)) ?_
    exact fun _ u hu => hv.trans hu
  · simp only [writerWP_pure]; exact hv

theorem leafFrM_checkFree (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (checkFree o) c w (fun _ v => LeafFrM w v) :=
  writerWP_mono (writerWP_checkFree o c w) (fun _ v h => by rw [h.1]; exact LeafFrM.refl w)

theorem leafFrM_takeBackChk4 (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W) :
    WriterWP (takeBackChk4 x parent cv) c w (fun _ v => LeafFrM w v) := by
  unfold takeBackChk4 replacedBy
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFrM_getNode parent c w) ?_
  rintro pn v ⟨hv, _⟩
  simp only [writerWP_get, writerWP_pure]
  split
  · split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_bind]
      refine writerWP_mono (leafFrM_retarget _ _ _ c v) ?_
      intro _ v2 h2
      refine writerWP_mono (leafFrM_checkFree _ c v2) ?_
      intro _ v3 h3
      refine writerWP_mono (leafFrM_takenBack _ c v3) ?_
      intro _ v4 h4
      refine writerWP_mono (leafFrM_note _ c v4) ?_
      intro _ v5 h5
      exact hv.trans (h2.trans (h3.trans (h4.trans h5)))
  · exact writerWP_throw _ _ _ _

theorem leafFrM_foldlM {β α : Type} (c : Ctx) (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a v, WriterWP (f b a) c v (fun _ v' => LeafFrM v v')) :
    ∀ w, WriterWP (xs.foldlM f init) c w (fun _ v => LeafFrM w v) := by
  induction xs generalizing init with
  | nil => intro w; simp only [List.foldlM_nil, writerWP_pure]; exact LeafFrM.refl w
  | cons a xs ih =>
    intro w
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a w) (fun b v hv => writerWP_mono (ih b v) (fun _ u hu => hv.trans hu))

theorem checkOld_ok (pn : KNode) (old : NodeId) (c : Ctx) (w : W)
    (hl : pn.leaf = true) (hv : (c.view old).isSome = true) :
    checkOld pn old c w = .ok ((), w) := by
  simp [checkOld, hl, hv, bind, ReaderT.bind, StateT.bind, Except.bind, read, readThe,
    MonadReaderOf.read, ReaderT.read, pure, ReaderT.pure, StateT.pure, Except.pure]

theorem rwp_checkOld {β : Type} (pn : KNode) (old : NodeId) (c : Ctx) (w : W) (k : Unit → M β)
    (hl : pn.leaf = true) (hv : (c.view old).isSome = true) :
    RWP (k ()) (checkOld pn old >>= k) c w :=
  fun y hy => (m_bind_ok _ k c w y).mpr ⟨(), w, checkOld_ok pn old c w hl hv, hy⟩

/-- With the parent a segment leaf and the made-for id a node of the view, the
take-back's copies run alike. -/
theorem rwp_takeBackChk4 (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W) (pn : KNode)
    (hpn : w.nodes.lookup parent = some pn) (hleaf : pn.leaf = true)
    (hmf : ∀ o, w.madeFor.lookup x = some o → (c.view o).isSome = true) :
    RWP (takeBackChk4 x parent cv) (takeBackChk x parent cv) c w := by
  unfold takeBackChk4 takeBackChk
  refine rwp_read ?_
  refine rwp_getNode_known parent pn hpn ?_
  refine rwp_bind (fun r v => v = w ∧ ∀ o, r = some o → (c.view o).isSome = true)
    (by unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure]; exact ⟨trivial, hmf⟩) ?_
  rintro r v ⟨hv, hr⟩
  subst v
  rcases r with _ | old
  · exact rwp_refl _ _ _
  · cases hli : pn.linkIndex x cv with
    | none => exact rwp_refl _ _ _
    | some j =>
      simp only []
      by_cases hlt : (pn.lastTime != some c.i) = true
      · simp only [hlt, ↓reduceIte]; exact rwp_refl _ _ _
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
        exact rwp_checkOld pn old c w (fun _ => do
          retarget parent x old
          checkFree x
          takenBack x
          note "up.takeback") hleaf (hr old rfl)

set_option maxHeartbeats 1600000 in
/-- The upward delete's two copies run alike when the fill holds at the
delete's start: the take-back's parent and the stop node are segment leaves
(`stopLeaf_of_liveCounts`). -/
theorem rwp_deleteUpwardChk4 (c : Ctx) (base : View BVal) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (w3 : W) (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hmf : ∀ x o, w3.madeFor.lookup x = some o → (c.view o).isSome = true)
    (cv : Nat) (key : Key) :
    RWP (deleteUpwardChk4 (X depth) depth cv key) (deleteUpwardChk2 (X depth) depth cv key) c w3 := by
  unfold deleteUpwardChk4 deleteUpwardChk2
  refine rwp_read ?_
  refine rwp_getNode_known (X depth) (Nn depth) (hlkX depth (Nat.le_refl _)) ?_
  dsimp only
  by_cases h1 : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = true
  · simp only [h1, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!(Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv))) = true
  · simp only [h2, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  have hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true := by
    simpa using h2
  refine rwp_bind _ (writerWP_climb c X Nn K depth w3 hpX hpK hlkX) ?_
  rintro stop v ⟨hv, hsle, hbetween, -, -, -⟩
  subst v
  by_cases h3 : (stop == depth) = true
  · simp only [h3, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by
    have : stop ≠ depth := fun he => h3 (by simp [he])
    omega
  -- the fill: below the stop node, every node of the path is the parent of an emptied node
  have hleafAt : ∀ k, stop < k → k ≤ depth → (Nn (k - 1)).leaf = true := by
    intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases hl : (Nn j).leaf with
    | true => rfl
    | false =>
      exfalso
      rcases Nat.lt_or_ge (j + 1) depth with hlt | hge
      · exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K depth hX0
          hXN hlinkK j hk2 hl (K (j + 1 + 1)) (htimes _ _ (hXN (j + 1) hk2))
          (hbetween (j + 1) hk1 hlt)
      · have he : j + 1 = depth := by omega
        subst he
        exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K (j + 1) hX0
          hXN hlinkK j (Nat.le_refl _) hl cv (htimes _ _ (hXN (j + 1) (Nat.le_refl _))) hall
  -- note, the path, the segment's fold: the path and the cached nodes' kinds kept
  refine rwp_bind (fun _ v => LeafFrM w3 v) (leafFrM_note _ c w3) ?_
  intro _ v1 hv1
  refine rwp_bind (fun a v => a = v1 ∧ v = v1) ((writerWP_get c v1 _).mpr ⟨rfl, rfl⟩) ?_
  rintro a v2 ⟨ha, hv2⟩
  refine rwp_bind (fun _ v => LeafFrM v2 v) (leafFrM_foldlM c _ _ 0 ?_ v2) ?_
  · intro b e v
    simp only [writerWP_bind]
    exact writerWP_mono (leafFrM_getNode _ c v) (fun d v' h => by simp only [writerWP_pure]; exact h.1)
  intro seg v3 hv3
  have hv3' : LeafFrM w3 v3 := hv1.trans (hv2 ▸ hv3)
  refine rwp_forIn_bind c _ _ _ _ (LeafFrM w3) _ ?_ v3 hv3' ?_
  · -- a step of the loop
    intro j hj v hv
    have hjl : j < depth - stop := List.mem_range.mp hj
    have hk1 : stop < depth - j := by omega
    have hk2 : depth - j ≤ depth := by omega
    have hpar : (Nn (depth - j - 1)).leaf = true := hleafAt (depth - j) hk1 hk2
    obtain ⟨n', hn', hl'⟩ := hv.1.2 _ _ (hlkX _ hk2)
    obtain ⟨pn, hpn, hpl⟩ := hv.1.2 _ _ (hlkX (depth - j - 1) (by omega))
    have hpx : (v.path[depth - j]?).map (·.2) = some (X (depth - j)) := by rw [hv.1.1]; exact hpX _ hk2
    have hpx1 : (v.path[depth - j - 1]?).map (·.2) = some (X (depth - j - 1)) := by
      rw [hv.1.1]; exact hpX _ (by omega)
    have hpk : v.path[depth - j]? = some (some (K (depth - j)), X (depth - j)) := by
      rw [hv.1.1]; exact hpK _ (by omega) hk2
    refine ⟨?_, ?_⟩
    · refine rwp_bind (fun x v' => x = X (depth - j) ∧ v' = v)
        (writerWP_pathNode_known _ _ c v hpx _ ⟨rfl, rfl⟩) ?_
      rintro x v' ⟨hx, hv'⟩
      subst hx; subst v'
      refine rwp_getNode_known _ n' hn' ?_
      by_cases hf : (n'.firstTime == some c.i) = true
      · simp only [hf, ↓reduceIte]
        refine rwp_bind (fun y v' => y = X (depth - j - 1) ∧ v' = v)
          (writerWP_pathNode_known _ _ c v hpx1 _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        refine rwp_bind (fun y v' => y = K (depth - j) ∧ v' = v)
          (writerWP_klongAt_known _ _ _ c v hpk _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        exact rwp_bind2 (fun _ _ => True)
          (rwp_takeBackChk4 _ _ _ c v pn hpn (by rw [hpl]; exact hpar)
            (fun o ho => hmf _ o (hv.2 ▸ ho))) (fun _ _ _ => trivial)
          (fun _ _ _ => rwp_refl _ _ _)
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact rwp_refl _ _ _
    · simp only [writerWP_bind]
      refine writerWP_pathNode_known _ _ c v hpx _ ?_
      refine (writerWP_getNode_known _ n' c v hn' _).mpr ?_
      split
      · simp only [writerWP_bind]
        refine writerWP_pathNode_known _ _ c v hpx1 _ ?_
        refine writerWP_klongAt_known _ _ _ c v hpk _ ?_
        refine writerWP_mono (leafFrM_takeBackChk4 _ _ _ c v) ?_
        intro _ u hu
        simp only [writerWP_pure]
        exact ⟨trivial, hv.trans hu⟩
      · simp only [writerWP_bind]
        refine writerWP_mono (leafFrM_note _ c v) ?_
        intro _ u hu
        refine writerWP_mono (leafFrM_unlink _ c u) ?_
        intro _ u' hu'
        simp only [writerWP_pure]
        exact ⟨trivial, hv.trans (hu.trans hu')⟩
  · -- the stop node
    intro v4 hv4
    have hps : (v4.path[stop]?).map (·.2) = some (X stop) := by rw [hv4.1.1]; exact hpX _ (by omega)
    have hpk : v4.path[stop + 1]? = some (some (K (stop + 1)), X (stop + 1)) := by
      rw [hv4.1.1]; exact hpK _ (by omega) (by omega)
    obtain ⟨sn, hsn, hsl⟩ := hv4.1.2 _ _ (hlkX stop (by omega))
    have hsleaf : sn.leaf = true := by
      rw [hsl]; have := hleafAt (stop + 1) (by omega) (by omega); simpa using this
    refine rwp_bind (fun x v' => x = X stop ∧ v' = v4)
      (writerWP_pathNode_known _ _ c v4 hps _ ⟨rfl, rfl⟩) ?_
    rintro x v' ⟨hx, hv'⟩
    subst hx; subst v'
    refine rwp_bind (fun y v' => y = K (stop + 1) ∧ v' = v4)
      (writerWP_klongAt_known _ _ _ c v4 hpk _ ⟨rfl, rfl⟩) ?_
    rintro y v' ⟨hy, hv'⟩
    subst hy; subst v'
    refine rwp_getNode_known _ sn hsn ?_
    refine rwp_bind_any (fun gh v5 => ?_)
    simp only [hsleaf, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact rwp_refl _ _ _


/-- A segment's step of the delete's descent keeps the made-for ids. -/
theorem writerWP_setNode_madeFor (r : NodeId) (s : Nat) (c : Ctx) (w : W) :
    WriterWP (setNode r s false) c w (fun _ v => v.madeFor = w.madeFor) := by
  unfold setNode
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_descendLte_madeFor s c c.p.fuel r w) ?_
  intro L w1 h1
  refine writerWP_mono (writerWP_getNode_frame L c w1) ?_
  intro n w2 h2
  split
  · simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
    exact h2.2.2.2.2.2.1.trans h1
  · simp only [Bool.not_false, ↓reduceIte, writerWP_pure]
    exact h2.2.2.2.2.2.1.trans h1

set_option maxHeartbeats 1600000 in
/-- The last segment's descent and the upward delete, for the two copies: the
path from w0's root as the upward delete's refinement asks. -/
theorem rwp_setValueDelChk4 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (r : NodeId) (cv : Nat) (key : Key) (w : W) (hS : SegInv c base w0 w r) (hmw : w.madeFor = w0.madeFor)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false) :
    RWP (setValueDelChk4 r cv key) (setValueDelChk2 r cv key) c w := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  unfold setValueDelChk4 setValueDelChk2
  refine rwp_read ?_
  refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_madeFor cv c c.p.fuel r w)) ?_
  rintro L w3 ⟨⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, -⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩, hm3⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  refine rwp_bind _ (kd_pathSize c w3) ?_
  rintro sz v ⟨hv, hsz⟩
  subst hsz; subst v
  refine rwp_bind2 (fun _ _ => True) ?_ (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
  -- the path from w0's root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w0.top.rootKey) :: P := by rw [hp3, hp, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hl (by rw [he]; exact LinkedFrom.of_pathFrom _ _ cv r steps hpf)
  have hXD : nodeAt w0.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, he, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps hpf
    (fun mm hmm => by rw [← hLe, hn] at hmm; cases hmm; exact hnl) (by rw [← hLe]; exact hvisL)
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w0 (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hmem : nodeAt w0.top.rootKey P i ∈ (w0.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hc _ hmem _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w0.top.rootKey P i = nodeAt r steps j := by
        rw [hP, hj, nodeAt_append_right, he]
      have hvj : (nodeAt r steps j, cv) ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps r steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w0.top.rootKey P i) ∈
        ((wNode c.p base w0 (nodeAt w0.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w0.top.rootKey P i) := by
    intro i hi
    have hl' : i < (w0.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl']
    simp [nodeAt, List.getElem?_eq_getElem hl']
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hlen : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen, ← hXD]
  exact rwp_deleteUpwardChk4 c base w0 hLC hm htimes (fun i => nodeAt w0.top.rootKey P i)
    (fun i => (wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) w3 hpX hpK hlkX
    (fun x o ho => hmf0 x o (by rw [← hmw, ← hm3]; exact ho)) cv key

/-- The delete's segments, for the two copies. -/
theorem rwp_putSegsDelChk4 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hwf : ∀ x xn, wNode c.p base w0 x = some xn → klongsWf xn.ks = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId) (w : W), SegInv c base w0 w r → w.madeFor = w0.madeFor →
      (∀ q ∈ fromVisits (wNode c.p base w0) c.i c.p.fuel segs r, w0.taken.contains q.1 = false) →
      RWP (putSegsDelChk4 key segs r) (putSegsDelChk2 key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro r w _ _ _; unfold putSegsDelChk4 putSegsDelChk2; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro r w hS hmw ht
    cases rest with
    | nil =>
      unfold putSegsDelChk4 putSegsDelChk2
      exact rwp_setValueDelChk4 c base hvc w0 hLC hm htimes hmf0 r cv key w hS hmw
        (fun q hq => ht q (by simpa [fromVisits] using hq))
    | cons d rest' =>
      unfold putSegsDelChk4 putSegsDelChk2
      have ht0 : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false :=
        fun q hq => ht q (by simp only [fromVisits]; exact List.mem_append_left _ hq)
      refine rwp_bind _ (writerWP_and (writerWP_setNode_seg c base hvc w0 cv r w hS ht0 hwf)
        (writerWP_setNode_madeFor r cv c w)) ?_
      rintro res v ⟨hres, hmv⟩
      cases res with
      | none => exact rwp_refl _ _ _
      | some y =>
        obtain ⟨hS', hg⟩ := hres y rfl
        refine ih y v hS' (hmv.trans hmw) ?_
        intro q hq
        apply ht q
        simp only [fromVisits]
        apply List.mem_append_right
        rw [hg]
        exact hq

/-- The delete's two copies run alike from a state with `PutInv`, the fill and
the made-for ids nodes of the view. -/
theorem rwp_putKvDelChk4 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hI : PutInv c base w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (key : Key) : RWP (putKvDelChk4 key) (putKvDelChk2 key) c w0 := by
  unfold putKvDelChk4 putKvDelChk2
  refine rwp_bind (fun _ v => v = { w0 with path := [] })
    (by unfold pathClear; simp only [writerWP_modify]) ?_
  rintro _ v1 hv1
  subst hv1
  refine rwp_bind (fun a v => a = w0.top.rootKey ∧
      v = { ({ w0 with path := [] } : W) with path := [(none, w0.top.rootKey)] })
    (by simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure]
        simp) ?_
  rintro a v2 ⟨ha, hv2⟩
  subst ha; subst hv2
  refine rwp_putSegsDelChk4 c base hvc w0 hLC hm hI.times hI.wf hmf0 key key _ _ ?_ rfl (hI.pathUntaken key)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, List.prefix_refl _, [], rfl, LinkedFrom.nil _, rfl, ?_⟩
  intro z hz
  simp at hz


/-! ## The made-for ids at every state between operations -/

/-- At every state between operations of a transaction after a run of R (whose
runs have TP4's links), every made-for id is below the transaction's first id and
a node of the view (putinv2's `stateOK_madeFor` with the view). -/
theorem stateOK_madeForView (p : Params) (hM : 4 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) :
    StateOK p R (fun ts tx w => ∀ x o, w.madeFor.lookup x = some o →
      o < tx.base ∧ ((ctxOf p ts).view o).isSome = true) := by
  intro ts tx hw hr z top _ _ pre post _ r w he
  obtain ⟨hP', _, hN⟩ := hR _ _ hr
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hvg : ViewGood tx.base (ctxOf p ts) :=
    viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have h := gmf_opsV tx.base pre (ctxOf p ts) (wInit tx top) hM hvg
    ⟨Nat.le_refl _, by intro q hq; cases hq⟩ (by intro q hq; cases hq) r w he
  exact mfv_lookup tx.base (ctxOf p ts) w h.2

/-! ## The premise with `checkOld3` proved too -/

/-- `OpDelChk3OKR` with `putKvDelChk4`: at the deletes of the runs of R whose start
has `PutInv`, the walk's ranges, TP7's fill and the heights' walk, the delete runs
as its checked copy with the holders' checks only. -/
def OpDelChk4OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk4 key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk4OKR` at the induction's runs: `hchk` with its stop-node checks and
`checkOld3` proved. -/
def OpDelChk4OKL (p : Params) : Prop := OpDelChk4OKR p (RunTreeQ p (LatestQD p))

/-- `OpDelChk2OKR` from `OpDelChk4OKR`, the merges on, node size at least 4. -/
theorem opDelChk2OKR_of_chk4 (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 4 ≤ p.M) (hRL : ∀ P t, R P t → RunLinksOK p P t) (h : OpDelChk4OKR p R) :
    OpDelChk2OKR p R :=
  fun ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH r' v he => by
    have hmf := stateOK_madeForView p hM R hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
    exact rwp_putKvDelChk4 (ctxOf p ts) (viewOf (treeRun p ts)) (viewCoherent_ctxOf p ts) w hI hL hm
      (fun x o ho => (hmf x o ho).2) key _
      (h ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH r' v he)

end SIS.Tree
