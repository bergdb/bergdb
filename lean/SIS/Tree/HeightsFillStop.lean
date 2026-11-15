/-
The stop-node part of `hchk` (bergdb 024-12; 024-22, step 4): with TP7's fill at
the delete's start, the upward delete's stop node and the take-back's parent are
segment leaves (`stopLeaf_of_liveCounts`), so the checked copy's two checks of them
pass. `putKvDelChk3` is `putKvDelChk2` without them: its stop node, if inner, runs
as the writer's, and its take-back checks only that the node the parent is pointed
to is a node of the view (`checkOld3`). From a state with `PutInv` and the fill the
two copies run alike (`rwp_putKvDelChk3`, a refinement at the state, `RWP`, through
the delete's descent and the upward delete's loop), so the narrowed premise
`OpDelChk2OKL` follows from the same with `putKvDelChk3` (`OpDelChk3OKL`,
`opDelChk2OKR_of_chk3`), and the top theorem holds with it, and without `hMF`
(`invGetScanOK_merges_chk3L`). Left in `hchk`: the holders before each take-back
(`checkFree`, `checkRoot`) and the view's node (`checkOld3`).
-/
import SIS.Tree.HeightsFill
import SIS.Tree.LatestTopMadeFor
import SIS.Tree.DelChkRefines
import SIS.Tree.WriterGetUpW

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The copy without the two checks of the fill -/

/-- `checkOld` without its segment-leaf part: the node the parent is pointed to
is a node of the view. -/
def checkOld3 (old : NodeId) : M Unit := do
  let c ← read
  if (c.view old).isSome then pure ()
  else throw "check: the take-back's parent is no segment leaf, or the node it names is not of the view"

/-- `takeBackChk` with `checkOld3`. -/
def takeBackChk3 (x parent : NodeId) (cv : Nat) : M Unit := do
  let c ← read
  let pn ← getNode parent
  match (← replacedBy x), pn.linkIndex x cv with
  | some old, some _ =>
    if pn.lastTime != some c.i then
      throw s!"Bug: take back of key node {x} at {c.i}: no klong of tt to it"
    checkOld3 old
    retarget parent x old
    checkFree x
    takenBack x
    note "up.takeback"
  | _, _ => throw s!"Bug: take back of key node {x} at {c.i}: no node it replaces, or no klong to it"

/-- `deleteUpwardChk2` without the stop node's check (an inner stop node runs as
the writer's) and with `takeBackChk3`. -/
def deleteUpwardChk3 (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
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
    if xn.firstTime == some tt then takeBackChk3 x (← pathNode (k - 1)) (← klongAt k)
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

/-! ## Refinement at a state -/

/-- Every successful run of f from w is one of g. -/
def RWP {α : Type} (f g : M α) (c : Ctx) (w : W) : Prop := ∀ x, f c w = .ok x → g c w = .ok x

theorem rwp_refl {α : Type} (f : M α) (c : Ctx) (w : W) : RWP f f c w := fun _ h => h

theorem rwp_bind {α β : Type} {m : M α} {k1 k2 : α → M β} {c : Ctx} {w : W} (P : α → W → Prop)
    (hm : WriterWP m c w P) (hk : ∀ a w', P a w' → RWP (k1 a) (k2 a) c w') :
    RWP (m >>= k1) (m >>= k2) c w := by
  intro x h
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok m k1 c w x).mp h
  exact (m_bind_ok m k2 c w x).mpr ⟨a, w', h1, hk a w' (hm a w' h1) x h2⟩

theorem rwp_bind2 {α β : Type} {m1 m2 : M α} {k1 k2 : α → M β} {c : Ctx} {w : W} (P : α → W → Prop)
    (h12 : RWP m1 m2 c w) (hm : WriterWP m1 c w P) (hk : ∀ a w', P a w' → RWP (k1 a) (k2 a) c w') :
    RWP (m1 >>= k1) (m2 >>= k2) c w := by
  intro x h
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok m1 k1 c w x).mp h
  exact (m_bind_ok m2 k2 c w x).mpr ⟨a, w', h12 _ h1, hk a w' (hm a w' h1) x h2⟩

theorem rwp_bind_any {α β : Type} {m : M α} {k1 k2 : α → M β} {c : Ctx} {w : W}
    (hk : ∀ a w', RWP (k1 a) (k2 a) c w') : RWP (m >>= k1) (m >>= k2) c w :=
  rwp_bind (fun _ _ => True) (fun _ _ _ => trivial) (fun a w' _ => hk a w')

theorem writerWP_self {α : Type} (f : M α) (c : Ctx) (w : W) :
    WriterWP f c w (fun r v => f c w = .ok (r, v)) := fun _ _ h => h

/-- A later state: the same key access path, every cached node still cached, of
the same kind (leaf or inner). -/
def LeafFr (w v : W) : Prop :=
  v.path = w.path ∧ ∀ y n, w.nodes.lookup y = some n → ∃ n', v.nodes.lookup y = some n' ∧ n'.leaf = n.leaf

theorem LeafFr.refl (w : W) : LeafFr w w := ⟨rfl, fun _ n h => ⟨n, h, rfl⟩⟩

theorem LeafFr.trans {a b d : W} (h1 : LeafFr a b) (h2 : LeafFr b d) : LeafFr a d := by
  refine ⟨h2.1.trans h1.1, fun y n h => ?_⟩
  obtain ⟨n1, h1', e1⟩ := h1.2 y n h
  obtain ⟨n2, h2', e2⟩ := h2.2 y n1 h1'
  exact ⟨n2, h2', e2.trans e1⟩

theorem leafFr_getNode (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun n v => LeafFr w v ∧ v.nodes.lookup x = some n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  cases hx : w.nodes.lookup x with
  | some n => simp only [writerWP_pure]; exact ⟨LeafFr.refl w, hx⟩
  | none =>
    simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨⟨rfl, fun y n hy => ⟨n, ?_, rfl⟩⟩, ?_⟩
        · simp only [List.lookup_append, hy, Option.some_or]
        · simp [List.lookup_append, hx]
    · exact writerWP_throw _ _ _ _

theorem leafFr_putNode (x : NodeId) (m : KNode) (c : Ctx) (w : W)
    (hm : ∀ n, w.nodes.lookup x = some n → m.leaf = n.leaf) :
    WriterWP (putNode x m) c w (fun _ v => LeafFr w v) := by
  unfold putNode
  simp only [writerWP_modify]
  refine ⟨rfl, fun y n hy => ?_⟩
  simp only [lookup_upsert]
  by_cases hyx : y = x
  · subst hyx; simp only [↓reduceIte]; exact ⟨m, rfl, hm n hy⟩
  · simp only [hyx, ↓reduceIte]; exact ⟨n, hy, rfl⟩

theorem leafFr_modify (f : W → W) (c : Ctx) (w : W) (hp : (f w).path = w.path)
    (hn : (f w).nodes = w.nodes) : WriterWP (modify f) c w (fun _ v => LeafFr w v) := by
  simp only [writerWP_modify]
  exact ⟨hp, fun y n hy => ⟨n, by rw [hn]; exact hy, rfl⟩⟩

theorem leafFr_note (s : String) (c : Ctx) (w : W) : WriterWP (note s) c w (fun _ v => LeafFr w v) :=
  leafFr_modify _ c w rfl rfl

theorem leafFr_takenBack (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (takenBack x) c w (fun _ v => LeafFr w v) :=
  leafFr_modify _ c w rfl rfl

theorem leafFr_unlink (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (unlink x) c w (fun _ v => LeafFr w v) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFr_getNode x c w) ?_
  rintro n v ⟨hv, hl⟩
  split
  · refine writerWP_mono (leafFr_putNode x _ c v (fun n' h => by rw [hl] at h; cases h; rfl)) ?_
    exact fun _ u hu => hv.trans hu
  · simp only [writerWP_pure]; exact hv

theorem leafFr_retarget (q src dst : NodeId) (c : Ctx) (w : W) :
    WriterWP (retarget q src dst) c w (fun _ v => LeafFr w v) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFr_getNode q c w) ?_
  rintro n v ⟨hv, hl⟩
  split
  · refine writerWP_mono (leafFr_putNode q _ c v (fun n' h => by rw [hl] at h; cases h; rfl)) ?_
    exact fun _ u hu => hv.trans hu
  · simp only [writerWP_pure]; exact hv

theorem leafFr_checkFree (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (checkFree o) c w (fun _ v => LeafFr w v) :=
  writerWP_mono (writerWP_checkFree o c w) (fun _ v h => by rw [h.1]; exact LeafFr.refl w)

theorem leafFr_checkOld3 (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (checkOld3 o) c w (fun _ v => LeafFr w v) := by
  unfold checkOld3
  simp only [writerWP_bind, writerWP_read]
  split
  · simp only [writerWP_pure]; exact LeafFr.refl w
  · exact writerWP_throw _ _ _ _

theorem leafFr_takeBackChk3 (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W) :
    WriterWP (takeBackChk3 x parent cv) c w (fun _ v => LeafFr w v) := by
  unfold takeBackChk3 replacedBy
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (leafFr_getNode parent c w) ?_
  rintro pn v ⟨hv, _⟩
  simp only [writerWP_get, writerWP_pure]
  split
  · split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_bind]
      refine writerWP_mono (leafFr_checkOld3 _ c v) ?_
      intro _ v1 h1
      refine writerWP_mono (leafFr_retarget _ _ _ c v1) ?_
      intro _ v2 h2
      refine writerWP_mono (leafFr_checkFree _ c v2) ?_
      intro _ v3 h3
      refine writerWP_mono (leafFr_takenBack _ c v3) ?_
      intro _ v4 h4
      refine writerWP_mono (leafFr_note _ c v4) ?_
      intro _ v5 h5
      exact hv.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  · exact writerWP_throw _ _ _ _

theorem rwp_read {β : Type} {k1 k2 : Ctx → M β} {c : Ctx} {w : W} (h : RWP (k1 c) (k2 c) c w) :
    RWP (read >>= k1) (read >>= k2) c w :=
  rwp_bind (fun a v => a = c ∧ v = w) ((writerWP_read c w _).mpr ⟨rfl, rfl⟩)
    (fun a v ⟨ha, hv⟩ => by subst ha; subst hv; exact h)

theorem rwp_getNode_known {β : Type} {k1 k2 : KNode → M β} {c : Ctx} {w : W} (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) (h : RWP (k1 n) (k2 n) c w) :
    RWP (getNode x >>= k1) (getNode x >>= k2) c w :=
  rwp_bind (fun a v => a = n ∧ v = w) ((writerWP_getNode_known x n c w hn _).mpr ⟨rfl, rfl⟩)
    (fun a v ⟨ha, hv⟩ => by subst ha; subst hv; exact h)

theorem checkOld_of_leaf (pn : KNode) (old : NodeId) (h : pn.leaf = true) :
    checkOld pn old = checkOld3 old := by
  unfold checkOld checkOld3
  simp [h]

/-- With the parent a segment leaf, the take-back's two copies run alike. -/
theorem rwp_takeBackChk3 (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W) (pn : KNode)
    (hpn : w.nodes.lookup parent = some pn) (hleaf : pn.leaf = true) :
    RWP (takeBackChk3 x parent cv) (takeBackChk x parent cv) c w := by
  unfold takeBackChk3 takeBackChk
  refine rwp_read ?_
  refine rwp_getNode_known parent pn hpn ?_
  simp only [checkOld_of_leaf pn _ hleaf]
  exact rwp_refl _ _ _

/-- A loop whose every step refines and keeps I. -/
theorem rwp_forIn {α : Type} (c : Ctx) (f g : α → PUnit → M (ForInStep PUnit)) (I : W → Prop)
    (l : List α)
    (hstep : ∀ j ∈ l, ∀ v, I v → RWP (f j PUnit.unit) (g j PUnit.unit) c v ∧
      WriterWP (f j PUnit.unit) c v (fun r v' => r = ForInStep.yield PUnit.unit ∧ I v')) :
    ∀ v, I v → RWP (forIn l PUnit.unit f) (forIn l PUnit.unit g) c v := by
  induction l with
  | nil => intro v _; simp only [List.forIn_nil]; exact rwp_refl _ _ _
  | cons a l ih =>
    intro v hv
    rw [List.forIn_cons, List.forIn_cons]
    obtain ⟨h1, h2⟩ := hstep a List.mem_cons_self v hv
    refine rwp_bind2 _ h1 h2 ?_
    rintro r v' ⟨hr, hv'⟩
    subst hr
    exact ih (fun j hj => hstep j (List.mem_cons_of_mem _ hj)) v' hv'

theorem leafFr_foldlM {β α : Type} (c : Ctx) (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a v, WriterWP (f b a) c v (fun _ v' => LeafFr v v')) :
    ∀ w, WriterWP (xs.foldlM f init) c w (fun _ v => LeafFr w v) := by
  induction xs generalizing init with
  | nil => intro w; simp only [List.foldlM_nil, writerWP_pure]; exact LeafFr.refl w
  | cons a xs ih =>
    intro w
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a w) (fun b v hv => writerWP_mono (ih b v) (fun _ u hu => hv.trans hu))

/-- A loop whose every step refines and keeps I, then two continuations that
refine from every state with I. -/
theorem rwp_forIn_bind {α β : Type} (c : Ctx) (f g : α → PUnit → M (ForInStep PUnit))
    (k1 k2 : PUnit → M β) (I : W → Prop) (l : List α)
    (hstep : ∀ j ∈ l, ∀ v, I v → RWP (f j PUnit.unit) (g j PUnit.unit) c v ∧
      WriterWP (f j PUnit.unit) c v (fun r v' => r = ForInStep.yield PUnit.unit ∧ I v'))
    (v : W) (hv : I v) (hk : ∀ v', I v' → RWP (k1 PUnit.unit) (k2 PUnit.unit) c v') :
    RWP (forIn l PUnit.unit f >>= k1) (forIn l PUnit.unit g >>= k2) c v :=
  rwp_bind2 (fun _ v => I v) (rwp_forIn c f g I l hstep v hv)
    (ht_forIn_inv_mem c f I l (fun j hj v hv => (hstep j hj v hv).2) v hv)
    (fun a v' hv' => by cases a; exact hk v' hv')

set_option maxHeartbeats 1600000 in
/-- The upward delete's two copies run alike when the fill holds at the
delete's start: the take-back's parent and the stop node are segment leaves
(`stopLeaf_of_liveCounts`). -/
theorem rwp_deleteUpwardChk3 (c : Ctx) (base : View BVal) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (w3 : W) (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (cv : Nat) (key : Key) :
    RWP (deleteUpwardChk3 (X depth) depth cv key) (deleteUpwardChk2 (X depth) depth cv key) c w3 := by
  unfold deleteUpwardChk3 deleteUpwardChk2
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
  refine rwp_bind (fun _ v => LeafFr w3 v) (leafFr_note _ c w3) ?_
  intro _ v1 hv1
  refine rwp_bind (fun a v => a = v1 ∧ v = v1) ((writerWP_get c v1 _).mpr ⟨rfl, rfl⟩) ?_
  rintro a v2 ⟨ha, hv2⟩
  refine rwp_bind (fun _ v => LeafFr v2 v) (leafFr_foldlM c _ _ 0 ?_ v2) ?_
  · intro b e v
    simp only [writerWP_bind]
    exact writerWP_mono (leafFr_getNode _ c v) (fun d v' h => by simp only [writerWP_pure]; exact h.1)
  intro seg v3 hv3
  have hv3' : LeafFr w3 v3 := hv1.trans (hv2 ▸ hv3)
  refine rwp_forIn_bind c _ _ _ _ (LeafFr w3) _ ?_ v3 hv3' ?_
  · -- a step of the loop
    intro j hj v hv
    have hjl : j < depth - stop := List.mem_range.mp hj
    have hk1 : stop < depth - j := by omega
    have hk2 : depth - j ≤ depth := by omega
    have hpar : (Nn (depth - j - 1)).leaf = true := hleafAt (depth - j) hk1 hk2
    obtain ⟨n', hn', hl'⟩ := hv.2 _ _ (hlkX _ hk2)
    obtain ⟨pn, hpn, hpl⟩ := hv.2 _ _ (hlkX (depth - j - 1) (by omega))
    have hpx : (v.path[depth - j]?).map (·.2) = some (X (depth - j)) := by rw [hv.1]; exact hpX _ hk2
    have hpx1 : (v.path[depth - j - 1]?).map (·.2) = some (X (depth - j - 1)) := by
      rw [hv.1]; exact hpX _ (by omega)
    have hpk : v.path[depth - j]? = some (some (K (depth - j)), X (depth - j)) := by
      rw [hv.1]; exact hpK _ (by omega) hk2
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
          (rwp_takeBackChk3 _ _ _ c v pn hpn (by rw [hpl]; exact hpar)) (fun _ _ _ => trivial)
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
        refine writerWP_mono (leafFr_takeBackChk3 _ _ _ c v) ?_
        intro _ u hu
        simp only [writerWP_pure]
        exact ⟨trivial, hv.trans hu⟩
      · simp only [writerWP_bind]
        refine writerWP_mono (leafFr_note _ c v) ?_
        intro _ u hu
        refine writerWP_mono (leafFr_unlink _ c u) ?_
        intro _ u' hu'
        simp only [writerWP_pure]
        exact ⟨trivial, hv.trans (hu.trans hu')⟩
  · -- the stop node
    intro v4 hv4
    have hps : (v4.path[stop]?).map (·.2) = some (X stop) := by rw [hv4.1]; exact hpX _ (by omega)
    have hpk : v4.path[stop + 1]? = some (some (K (stop + 1)), X (stop + 1)) := by
      rw [hv4.1]; exact hpK _ (by omega) (by omega)
    obtain ⟨sn, hsn, hsl⟩ := hv4.2 _ _ (hlkX stop (by omega))
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

/-! ## The delete's descent, for the two copies at once -/

/-- `setValueDelChk2` with `deleteUpwardChk3`. -/
def setValueDelChk3 (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk3 leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk2` with `setValueDelChk3`. -/
def putSegsDelChk3 (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk3 segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk3 key rest next

/-- The delete's checked copy without the stop node's check and `checkOld`'s
segment-leaf part (`putKvDelChk2` with `deleteUpwardChk3`). -/
def putKvDelChk3 (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk3 key key root

/-- At the start of a segment's descent: the path from the delete's start state
w0's root, linked in its tree, its nodes but the last cached as w0 has them. -/
def SegInv (c : Ctx) (base : View BVal) (w0 w : W) (r : NodeId) : Prop :=
  ReadsAs c.p base w0 w ∧ w0.nodes.IsPrefix w.nodes ∧
  ∃ ps, w.path = (none, w0.top.rootKey) :: ps ∧ LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey ps ∧
    pathEnd w0.top.rootKey ps = r ∧
    ∀ z ∈ (w0.top.rootKey :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w0 z = some zn →
      w.nodes.lookup z = some zn

theorem mem_cons_map_dropLast (x : NodeId) (ps : List (Option Nat × NodeId)) (z : NodeId)
    (h : z ∈ x :: ps.map (·.2)) : z ∈ (x :: ps.map (·.2)).dropLast ∨ z = pathEnd x ps := by
  induction ps generalizing x with
  | nil => right; simpa [pathEnd] using h
  | cons e rest ih =>
    obtain ⟨k, y⟩ := e
    have hpe : pathEnd x ((k, y) :: rest) = pathEnd y rest := pathEnd_cons_append x y k [] rest
    rw [hpe]
    simp only [List.map_cons, List.mem_cons] at h
    simp only [List.map_cons, List.dropLast_cons_cons, List.mem_cons]
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases ih y (by simpa using h) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-- A segment's step of the delete's descent: the next segment's root, the
path linked from w0's root through it. -/
theorem writerWP_setNode_seg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (s : Nat) (r : NodeId) (w : W) (hS : SegInv c base w0 w r)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i s c.p.fuel r, w0.taken.contains q.1 = false)
    (hwf : ∀ x xn, wNode c.p base w0 x = some xn → klongsWf xn.ks = true) :
    WriterWP (setNode r s false) c w (fun res v => ∀ y, res = some y →
      SegInv c base w0 v y ∧ getEqR (wNode c.p base w0) c.i s c.p.fuel r = some y) := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  unfold setNode
  wpSimplify
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps s c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) ?_
  rintro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, hget⟩, ⟨steps1, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩
  rw [hr0.1] at hn hvisL hpf hcache3 hget
  rw [writerWP_getNode_known L n c _ hlk3]
  cases hfd : n.searchEq c.i s with
  | none =>
    simp only [Bool.not_false, ↓reduceIte, writerWP_pure]
    intro y hy
    cases hy
  | some fd =>
    simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
    intro y hy
    cases hy
    have hget' : getEqR (wNode c.p base w0) c.i s c.p.fuel r = some fd.y := by rw [hget, hfd]; rfl
    have hlink : (fd.c, fd.y) ∈ n.liveAt c.i := by
      have hm := KNode.searchEq_mem n c.i s fd (hwf L n hn) hfd
      rw [KNode.searchEq_c n c.i s fd hfd]
      exact hm
    have hvisAll := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps1 hpf
      (fun m hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
    refine ⟨⟨hr0.trans _ _ _ _ _ (hr3.trans _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩),
      hpre0.trans hpre3, ps ++ steps1 ++ [(some fd.c, fd.y)], ?_, ?_, ?_, ?_⟩, hget'⟩
    · simp [hp3, hp]
    · rw [List.append_assoc]
      refine LinkedFrom.append _ _ _ ps _ hl ?_
      rw [he]
      refine LinkedFrom.append _ _ r steps1 _ (LinkedFrom.of_pathFrom _ _ s r steps1 hpf) ?_
      rw [← hLe]
      exact LinkedFrom.cons L n fd.c fd.y [] hn hlink (LinkedFrom.nil _)
    · simp [pathEnd]
    · intro z hz zn hzn
      have hsplit : (w0.top.rootKey :: (ps ++ steps1 ++ [(some fd.c, fd.y)]).map (·.2)) =
          (w0.top.rootKey :: ps.map (·.2) ++ steps1.map (·.2)) ++ [fd.y] := by simp
      rw [hsplit, List.dropLast_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · rcases mem_cons_map_dropLast _ _ _ hz with hz | hz
        · exact lookup_of_isPrefix _ _ hpre3 z zn (hc z hz zn hzn)
        · rw [he] at hz
          subst hz
          exact hcache3 _ zn hvisAll.1 hzn
      · obtain ⟨e, he1, he2⟩ := List.mem_map.mp hz
        rw [← he2] at hzn ⊢
        exact hcache3 _ zn (hvisAll.2 e he1) hzn

set_option maxHeartbeats 1600000 in
/-- The last segment's descent and the upward delete, for the two copies: the
path from w0's root as the upward delete's refinement asks. -/
theorem rwp_setValueDelChk3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (r : NodeId) (cv : Nat) (key : Key) (w : W) (hS : SegInv c base w0 w r)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false) :
    RWP (setValueDelChk3 r cv key) (setValueDelChk2 r cv key) c w := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  unfold setValueDelChk3 setValueDelChk2
  refine rwp_read ?_
  refine rwp_bind _ (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel r w ht1)) ?_
  rintro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, -⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩
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
  exact rwp_deleteUpwardChk3 c base w0 hLC hm htimes (fun i => nodeAt w0.top.rootKey P i)
    (fun i => (wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) w3 hpX hpK hlkX cv key

/-- The delete's segments, for the two copies. -/
theorem rwp_putSegsDelChk3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (htimes : ∀ x xn, wNode c.p base w0 x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hwf : ∀ x xn, wNode c.p base w0 x = some xn → klongsWf xn.ks = true) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId) (w : W), SegInv c base w0 w r →
      (∀ q ∈ fromVisits (wNode c.p base w0) c.i c.p.fuel segs r, w0.taken.contains q.1 = false) →
      RWP (putSegsDelChk3 key segs r) (putSegsDelChk2 key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro r w _ _; unfold putSegsDelChk3 putSegsDelChk2; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro r w hS ht
    cases rest with
    | nil =>
      unfold putSegsDelChk3 putSegsDelChk2
      exact rwp_setValueDelChk3 c base hvc w0 hLC hm htimes r cv key w hS
        (fun q hq => ht q (by simpa [fromVisits] using hq))
    | cons d rest' =>
      unfold putSegsDelChk3 putSegsDelChk2
      have ht0 : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false :=
        fun q hq => ht q (by simp only [fromVisits]; exact List.mem_append_left _ hq)
      refine rwp_bind _ (writerWP_setNode_seg c base hvc w0 cv r w hS ht0 hwf) ?_
      intro res v hres
      cases res with
      | none => exact rwp_refl _ _ _
      | some y =>
        obtain ⟨hS', hg⟩ := hres y rfl
        refine ih y v hS' ?_
        intro q hq
        apply ht q
        simp only [fromVisits]
        apply List.mem_append_right
        rw [hg]
        exact hq

/-- The delete's two copies run alike from a state with `PutInv` and the fill. -/
theorem rwp_putKvDelChk3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hI : PutInv c base w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (key : Key) : RWP (putKvDelChk3 key) (putKvDelChk2 key) c w0 := by
  unfold putKvDelChk3 putKvDelChk2
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
  refine rwp_putSegsDelChk3 c base hvc w0 hLC hm hI.times hI.wf key key _ _ ?_ (hI.pathUntaken key)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, List.prefix_refl _, [], rfl, LinkedFrom.nil _, rfl, ?_⟩
  intro z hz
  simp at hz

/-! ## The premise with the two checks of the fill proved -/

/-- `OpDelChk2OKR` with `putKvDelChk3`: at the deletes of the runs of R whose start
has `PutInv`, the walk's ranges, TP7's fill and the heights' walk, the delete runs
as its checked copy without the stop node's check and `checkOld`'s segment leaf. -/
def OpDelChk3OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
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
      putKvDelChk3 key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk3OKR` at the induction's runs: `hchk` with its stop-node checks
proved. -/
def OpDelChk3OKL (p : Params) : Prop := OpDelChk3OKR p (RunTreeQ p (LatestQD p))

/-- The two checks of the fill hold: `OpDelChk2OKR` from `OpDelChk3OKR`, the
merges on. -/
theorem opDelChk2OKR_of_chk3 (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (h : OpDelChk3OKR p R) : OpDelChk2OKR p R :=
  fun ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH r' v he =>
    rwp_putKvDelChk3 (ctxOf p ts) (viewOf (treeRun p ts)) (viewCoherent_ctxOf p ts) w hI hL hm key _
      (h ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH r' v he)

/-- The top theorem with `hchk` narrowed to the deletes whose start has the fill,
`PutInv`, the ranges and the heights, and without its two checks of the fill
(`OpDelChk3OKL`); without `hMF` (putinv2's `stateOK_madeFor`). -/
theorem invGetScanOK_merges_chk3L (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk3 : OpDelChk3OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hMF := stateOK_madeFor p (four_le_M p hp) (RunOK p) (fun _ _ h => h.1)
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  exact invGetScanOK_merges p hp hth
    (opDelChk2OK_of_chk2L p hp hth (opDelChk2OKR_of_chk3 p _ hm hchk3) htb d4 l4 hU hHL hMSF hCoF hCoU hMF)
    htb d4 l4 hU hHL hMSF hCoF hCoU hMF

end SIS.Tree
