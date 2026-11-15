/-
`DelInvJ` carried to the leaf's call of `afterDelete` (bergdb 024-12, section 1):
a delete whose leaf keeps a live klong calls `afterDelete` after the leaf's bitmap,
at a state with `DelInvJ` and the books (`DelHoleJ`), from every state between a
transaction's operations with the facts the joint route has. So the premise
`OpDelChk7OKL` asks `DelHoleJ` only at the upward delete's call, after its stop
node's bitmap (`putKvDelChk7`), and `opDelChk6OKR_of_chk7` gives `OpDelChk6OKR`
from it.

* `deleteUpwardP2 adK adC` is the upward delete with its two calls of
  `afterDelete` apart: `adK` after the leaf's bitmap, `adC` after the stop
  node's;
* the descent to the last segment's leaf is the same in both copies
  (`rwp_putKvG`, a generic upward delete `du` at its end, the path and the
  kinds' and heights' books from the delete's start, as `writerWP_del_toLeafMKH`
  gives them);
* at the leaf, the bitmap with room or full keeps `DelInvJ` and the books
  (the cases of `delStepsCaseJ2OK_roomR` and `delStepsCaseJ2OK_fullS`).
-/
import SIS.Tree.DelHoleRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The upward delete with its two calls of `afterDelete` apart -/

/-- `deleteUpwardP` with `adK` at the leaf's call and `adC` at the stop node's. -/
def deleteUpwardP2 (adK adC : Key → Nat → Nat → M Unit) (leaf : NodeId) (depth : Nat) (cv : Nat)
    (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    adK key g h
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
    if xn.firstTime == some tt then takeBack x (← pathNode (k - 1)) (← klongAt k)
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
    adC key gs hs
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

/-- `setValueDP` with any upward delete `du`. -/
def setValueG (du : NodeId → Nat → Nat → Key → M Bool) (segRoot : NodeId) (cv : Nat) (key : Key) :
    M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← du leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDP` with `setValueG du`. -/
def putSegsG (du : NodeId → Nat → Nat → Key → M Bool) (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueG du segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsG du key rest next

/-- The delete with any upward delete `du`. -/
def putKvG (du : NodeId → Nat → Nat → Key → M Bool) (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsG du key key root

theorem putSegsDP_eqG (a : Key → Nat → Nat → M Unit) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId), putSegsDP a key segs r = putSegsG (deleteUpwardP a) key segs r := by
  intro segs
  induction segs with
  | nil => intro r; rfl
  | cons cv rest ih =>
    intro r
    cases rest with
    | nil => rfl
    | cons d rest' =>
      unfold putSegsDP putSegsG
      simp only [ih]
      rfl

theorem putKvDP_eqG (a : Key → Nat → Nat → M Unit) (key : Key) :
    putKvDP a key = putKvG (deleteUpwardP a) key := by
  unfold putKvDP putKvG
  simp only [putSegsDP_eqG]

theorem deleteUpwardP_eq2 (a : Key → Nat → Nat → M Unit) :
    deleteUpwardP a = deleteUpwardP2 a a := rfl

/-! ## The descent, for any two upward deletes -/

theorem segRootR_snoc_of (N : NodeId → Option KNode) (t : Time) (f : Nat) :
    ∀ (pre : List Nat) (r0 r y : NodeId) (s : Nat), segRootR N t f pre r0 = some r →
      getEqR N t s f r = some y → (N y).isSome = true → segRootR N t f (pre ++ [s]) r0 = some y := by
  intro pre
  induction pre with
  | nil =>
    intro r0 r y s h1 h2 h3
    simp only [segRootR, Option.some.injEq] at h1
    subst h1
    simp [segRootR, h2, h3]
  | cons a rest ih =>
    intro r0 r y s h1 h2 h3
    simp only [List.cons_append, segRootR] at h1 ⊢
    cases hg : getEqR N t a f r0 with
    | none => rw [hg] at h1; cases h1
    | some z =>
      rw [hg] at h1
      simp only at h1 ⊢
      split at h1
      · rename_i hz
        simp only [hz, ↓reduceIte]
        exact ih z r y s h1 h2 h3
      · cases h1

/-- A segment's step of the descent, as `writerWP_setNode_seg`, with J kept and
the segment's root a node. -/
theorem writerWP_setNode_segJ (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (s : Nat) (r : NodeId) (w : W) (hS : SegInv c base w0 w r)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i s c.p.fuel r, w0.taken.contains q.1 = false)
    (hwf : ∀ x xn, wNode c.p base w0 x = some xn → klongsWf xn.ks = true)
    (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Nat) (fd : Found) (L : NodeId) (n : KNode) (v : W), J v → KdPathLast v L →
      v.nodes.lookup L = some n → n.leaf = true → n.searchEq c.i s = some fd →
      J { v with path := v.path ++ [(some fd.c, fd.y)] })
    (hJ : J w) :
    WriterWP (setNode r s false) c w (fun res v => ∀ y, res = some y →
      SegInv c base w0 v y ∧ getEqR (wNode c.p base w0) c.i s c.p.fuel r = some y ∧ J v ∧
      (wNode c.p base w0 r).isSome = true) := by
  have hseg := writerWP_setNode_seg c base hvc w0 s r w hS ht hwf
  obtain ⟨hr0, _, ps, hp, _, he, _⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  have hKP : KdPathLast w r := by
    have := kdPathLast_steps w [(none, w0.top.rootKey)] ps w0.top.rootKey (by rw [hp]; rfl) rfl
    rwa [he] at this
  have hrest : WriterWP (setNode r s false) c w (fun res v => ∀ y, res = some y →
      J v ∧ (wNode c.p base w0 r).isSome = true) := by
    unfold setNode
    wpSimplify
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
      (writerWP_descendLte_steps s c base hvc c.p.fuel r w ht1)) (hJd s c.p.fuel r w hJ hKP)) ?_
    rintro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, _, _⟩, ⟨steps1, hpf, hp3, hLe⟩⟩, hJ3⟩
    have hrs : (wNode c.p base w0 r).isSome = true := by
      rw [← hr0.1]
      cases steps1 with
      | nil => simp only [pathEnd, List.getLast?_nil, Option.map_none, Option.getD_none] at hLe; rw [← hLe, hn]; rfl
      | cons e rest => cases hpf with | cons _ nr _ _ h1 _ _ _ => rw [h1]; rfl
    have hPL3 : KdPathLast w3 L := by
      have hpl : w.path.getLast?.map (·.2) = some r := by
        rw [hp, ← he]; unfold pathEnd
        cases h : ps.getLast? <;> simp [List.getLast?_cons, h]
      have := kdPathLast_steps w3 w.path steps1 r hp3 hpl
      rwa [← hLe] at this
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
      exact ⟨hJp s fd L n w3 hJ3 hPL3 hlk3 hnl hfd, hrs⟩
  refine writerWP_mono (writerWP_and hseg hrest) ?_
  intro res v ⟨h1, h2⟩ y hy
  obtain ⟨a1, a2⟩ := h1 y hy
  obtain ⟨b1, b2⟩ := h2 y hy
  exact ⟨a1, a2, b1, b2⟩

/-- What the descent gives at the last segment's leaf, for an upward delete. -/
def LeafHole (c : Ctx) (base : View BVal) (w0 : W) (J : W → Prop) (key : Key)
    (du1 du2 : NodeId → Nat → Nat → Key → M Bool) : Prop :=
  ∀ (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W),
    key = pre ++ [cv] →
    segRootR (wNode c.p base w0) c.i c.p.fuel pre w0.top.rootKey = some rk →
    (L, cv) ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel rk → wNode c.p base w0 L = some n →
    n.leaf = true → ReadsAs c.p base w0 w3 → J w3 → w3.nodes.lookup L = some n →
    w3.path = (none, w0.top.rootKey) :: P →
    LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey P →
    nodeAt w0.top.rootKey P P.length = L →
    (∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n)) →
    RWP (du1 L P.length cv key) (du2 L P.length cv key) c w3

set_option maxHeartbeats 1600000 in
/-- The last segment's descent, for two upward deletes: as `rwp_setValueDelChk5`,
with J kept and the facts that `writerWP_del_toLeafMKH` gives at the leaf. -/
theorem rwp_setValueG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (du1 du2 : NodeId → Nat → Nat → Key → M Bool) (key : Key) (hdu : LeafHole c base w0 J key du1 du2)
    (pre : List Nat) (r : NodeId) (cv : Nat) (hkey : key = pre ++ [cv]) (w : W)
    (hS : SegInv c base w0 w r) (hJ : J w)
    (hseg : (wNode c.p base w0 r).isSome = true →
      segRootR (wNode c.p base w0) c.i c.p.fuel pre w0.top.rootKey = some r)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false) :
    RWP (setValueG du1 r cv key) (setValueG du2 r cv key) c w := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  have hKP : KdPathLast w r := by
    have := kdPathLast_steps w [(none, w0.top.rootKey)] ps w0.top.rootKey (by rw [hp]; rfl) rfl
    rwa [he] at this
  unfold setValueG
  refine rwp_read ?_
  refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel r w ht1))
    (hJd cv c.p.fuel r w hJ hKP)) ?_
  rintro L w3 ⟨⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, -⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩, hJ3⟩
  have hr03 : ReadsAs c.p base w0 w3 := ReadsAs.trans c.p base w0 w w3 hr0 hr3
  have hrs : (wNode c.p base w0 r).isSome = true := by
    rw [← hr0.1]
    cases steps with
    | nil => simp only [pathEnd, List.getLast?_nil, Option.map_none, Option.getD_none] at hLe; rw [← hLe, hn]; rfl
    | cons e rest => cases hpf with | cons _ nr _ _ h1 _ _ _ => rw [h1]; rfl
  rw [hr0.1] at hn hvisL hpf hcache3
  refine rwp_bind _ (kd_pathSize c w3) ?_
  rintro sz v ⟨hv, hsz⟩
  subst hsz; subst v
  refine rwp_bind2 (fun _ _ => True) ?_ (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
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
  have hlen : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen]
  exact hdu pre cv r L n P w3 hkey (hseg hrs) hvisL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX

/-- The delete's segments, for two upward deletes. -/
theorem rwp_putSegsG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hwf : ∀ x xn, wNode c.p base w0 x = some xn → klongsWf xn.ks = true)
    (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Nat) (fd : Found) (L : NodeId) (n : KNode) (v : W), J v → KdPathLast v L →
      v.nodes.lookup L = some n → n.leaf = true → n.searchEq c.i s = some fd →
      J { v with path := v.path ++ [(some fd.c, fd.y)] })
    (du1 du2 : NodeId → Nat → Nat → Key → M Bool) (key : Key) (hdu : LeafHole c base w0 J key du1 du2) :
    ∀ (segs pre : List Nat) (r : NodeId) (w : W), key = pre ++ segs → SegInv c base w0 w r → J w →
      ((wNode c.p base w0 r).isSome = true →
        segRootR (wNode c.p base w0) c.i c.p.fuel pre w0.top.rootKey = some r) →
      (∀ q ∈ fromVisits (wNode c.p base w0) c.i c.p.fuel segs r, w0.taken.contains q.1 = false) →
      RWP (putSegsG du1 key segs r) (putSegsG du2 key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro pre r w _ _ _ _ _; unfold putSegsG; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro pre r w hk hS hJ hseg ht
    cases rest with
    | nil =>
      unfold putSegsG
      exact rwp_setValueG c base hvc w0 J hJd du1 du2 key hdu pre r cv hk w hS hJ hseg
        (fun q hq => ht q (by simpa [fromVisits] using hq))
    | cons d rest' =>
      unfold putSegsG
      have ht0 : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false :=
        fun q hq => ht q (by simp only [fromVisits]; exact List.mem_append_left _ hq)
      refine rwp_bind _ (writerWP_setNode_segJ c base hvc w0 cv r w hS ht0 hwf J hJd hJp hJ) ?_
      rintro res v hres
      cases res with
      | none => exact rwp_refl _ _ _
      | some y =>
        obtain ⟨hS', hg, hJv, hrs⟩ := hres y rfl
        refine ih (pre ++ [cv]) y v (by rw [hk]; simp) hS' hJv
          (fun hy => segRootR_snoc_of _ _ _ pre _ r y cv (hseg hrs) hg hy) ?_
        intro q hq
        apply ht q
        simp only [fromVisits]
        apply List.mem_append_right
        rw [hg]
        exact hq

/-- The delete, for two upward deletes: the descent is the same; at the last
segment's leaf, `LeafHole`. -/
theorem rwp_putKvG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W)
    (hI : PutInv c base w0) (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Nat) (fd : Found) (L : NodeId) (n : KNode) (v : W), J v → KdPathLast v L →
      v.nodes.lookup L = some n → n.leaf = true → n.searchEq c.i s = some fd →
      J { v with path := v.path ++ [(some fd.c, fd.y)] })
    (hJ0 : J ({ ({ w0 with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w0.top.rootKey)] } : W))
    (du1 du2 : NodeId → Nat → Nat → Key → M Bool) (key : Key) (hdu : LeafHole c base w0 J key du1 du2) :
    RWP (putKvG du1 key) (putKvG du2 key) c w0 := by
  unfold putKvG
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
  refine rwp_putSegsG c base hvc w0 hI.wf J hJd hJp du1 du2 key hdu key [] _ _ (by simp) ?_ hJ0
    (fun _ => rfl) (hI.pathUntaken key)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, List.prefix_refl _, [], rfl, LinkedFrom.nil _, rfl, ?_⟩
  intro z hz
  simp at hz

/-! ## The leaf's call -/

/-- At a state of J, the call with the merges' check only runs as the one that
checks J too. -/
theorem rwp_afterDeleteJ_true (J : W → Prop) (key : Key) (g h : Nat) (c : Ctx) (v : W) (hJ : J v) :
    RWP (afterDeleteJ (fun _ => True) key g h) (afterDeleteJ J key g h) c v := by
  intro x hx
  unfold afterDeleteJ at hx ⊢
  obtain ⟨a, v1, h1, h2⟩ := (m_bind_ok _ _ c v x).mp hx
  obtain ⟨ha, hv1⟩ := ((writerWP_read c v (fun a w' => a = c ∧ w' = v)).mpr ⟨rfl, rfl⟩) a v1 h1
  subst a; subst v1
  obtain ⟨b, v2, h3, h4⟩ := (m_bind_ok _ _ c v x).mp h2
  obtain ⟨hb, hv2⟩ := ((writerWP_get c v (fun b w' => b = v ∧ w' = v)).mpr ⟨rfl, rfl⟩) b v2 h3
  subst b; subst v2
  refine (m_bind_ok _ _ c v x).mpr ⟨c, v, h1, (m_bind_ok _ _ c v x).mpr ⟨v, v, h3, ?_⟩⟩
  split at h4
  · rename_i hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hJ, hc.2⟩)]
    exact h4
  · exact ((writerWP_throw _ c v (fun _ _ => False)) _ _ h4).elim

/-- The upward delete with the leaf's call apart: from the leaf's node, a bitmap
that keeps a live klong leads to a state of Q, where the two calls run alike. -/
theorem rwp_deleteUpwardP2_keeps (a1 a2 aC : Key → Nat → Nat → M Unit) (c : Ctx) (L : NodeId) (n : KNode)
    (d cv : Nat) (key : Key) (w3 : W) (hlk : w3.nodes.lookup L = some n) (Q : W → Prop)
    (hbit : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap →
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false →
      WriterWP (appendDeleteKlong L d cv) c w3 (fun _ v => Q v))
    (hK : ∀ g h v, Q v → RWP (a1 key g h) (a2 key g h) c v) :
    RWP (deleteUpwardP2 a1 aC L d cv key) (deleteUpwardP2 a2 aC L d cv key) c w3 := by
  unfold deleteUpwardP2
  refine rwp_read ?_
  refine rwp_getNode_known L n hlk ?_
  dsimp only
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun hne => ?_)
  refine rwp_ite (fun hk => ?_) (fun _ => rwp_refl _ _ _)
  have hne' : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := by simpa using hne
  have hk' : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false := by simpa using hk
  refine rwp_bind (fun _ v => v = w3) (writerWP_ghOf_cached L n c w3 hlk _ (fun _ => rfl)) ?_
  rintro gh v hv
  subst hv
  rcases gh with ⟨g, hh⟩
  dsimp only
  refine rwp_bind (fun _ v => Q v) (hbit hne' hk') ?_
  rintro _ v hQ
  exact rwp_bind_left (hK g hh v hQ)

/-- The copy that checks `DelHoleJ` only at the upward delete's call, after its
stop node's bitmap; the leaf's call checks the merges' loop only. -/
noncomputable def putKvDelChk7 (J : W → Prop) (key : Key) : M Bool :=
  putKvG (deleteUpwardP2 (afterDeleteJ (fun _ => True)) (afterDeleteJ J)) key

/-- `OpDelChk6OKR` with `putKvDelChk7`. -/
def OpDelChk7OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk7 (DelHoleJ p ts tx top w key) key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk7OKR` at the induction's runs. -/
def OpDelChk7OKL (p : Params) : Prop := OpDelChk7OKR p (RunTreeQ p (LatestQD p))

set_option maxHeartbeats 3200000 in
/-- `OpDelChk6OKR` from `OpDelChk7OKR`: at the leaf's call of `afterDelete`,
`DelHoleJ` holds (the bitmap with room as `delStepsCaseJ2OK_roomR`, full as
`delStepsCaseJ2OK_fullS`, from the facts at the delete's start). -/
theorem opDelChk6OKR_of_chk7 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (htb : TakeBelowFuelDelOK p) (h7 : OpDelChk7OKR p R) : OpDelChk6OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have h7' := h7 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hHS := htStart_of_ht p R hRL hRK hRH htb ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre hH
  have hF := segFits_of_htStart p ts tx w hHS
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := hHS
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post) hs r w
    hpre (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hSV := leafVals_reached p hM ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr) (hRK _ _ hr)
  have hkey' : keyWf key = true := within_op_keyWf p ts tx hw pre _ post hs
  have hJw : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hSB : tx.base ≤ w.next := hb0.next
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  show putKvDP (afterDeleteJ (DelHoleJ p ts tx top w key)) key (ctxOf p ts) w = .ok (r', v)
  rw [putKvDP_eqG, deleteUpwardP_eq2]
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ' hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ' hx)
    (fun s fd L n v hJ' hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ' hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w ⟨hbook, hb0, hi0⟩ hhi hwfw hub) _ _ key ?_ _ h7'
  intro pre' cv rk L n P w3 hkey hrk hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  subst hkey
  refine rwp_deleteUpwardP2_keeps _ _ _ (ctxOf p ts) L n P.length cv _ w3 hlk3
    (DelHoleJ p ts tx top w (pre' ++ [cv])) ?_ (fun g h v hQ => rwp_afterDeleteJ_true _ _ g h _ v hQ)
  intro hne hkeep
  have hLV := leafVals_all hSV hkey' hrk
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre' cv _ rk hrk _ hL)
  have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJw hr03
  by_cases hroom : DelRoom (ctxOf p ts) cv n
  · obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1.1))
      (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.1.2.1 hJ3.1.2.2 a hpx)) ?_
    rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
    refine ⟨⟨⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre' cv rk L n hI hRO hICE hF
      hkey' hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩, ?_, ?_⟩, hbv⟩
    · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n hpos hJ23 hlk3
        (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
        (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
        (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
        (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
    · rw [h5, hr03.2.2.2.2]; exact hSB
  · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
    have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
      (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
      (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
      (by rw [hr03.1, hr03.2.1]; exact hRO) hJ23 (by rw [hr03.2.2.2.2]; exact hSB) hsa2
      P.length _ _ _ hPOK cv n
      (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
      hnl hne hroom (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
    simp only [hXD] at hJ2
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_appendDeleteKlong_full_delH (ctxOf p ts) _
      (viewCoherent_ctxOf p ts) _ tx.base (delFullRootStepOK_ctx p ts) _
      (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
      hsa2 hv hk hICEk w pre' cv rk tx.base top hB hI hRO hF
      hkey' hrk L n P w3 hL hn hnl hne hroom hr03 hJ3.1 hJ3.2 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1.1)) ?_
    rintro _ v ⟨⟨hv', hj⟩, hbv⟩
    exact ⟨⟨hv', hj.1, hj.2⟩, hbv⟩

end SIS.Tree
