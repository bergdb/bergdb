/-
Case 4 of 024-12's assembly, a delete with the merges on (bergdb 024-22):
`OpGetCaseOK p R DelMergeCase` reduced to named step obligations. The merges'
loop (`mergeUp`) and the root collapse after it keep the delete's inner invariant
(`DelInv`: PutInv, its global parts, the walk's ranges, inner children there, the
fuel, and the reading of the delete) from cost's merge and collapse lemmas
(`writerWP_merge_get_inv`, `writerWP_collapseRoot_coll`), given:

* `MergeStepOK`: a merge of the loop keeps PutInv, PutInvG, the ranges and inner
  children, and the state after it fits the fuel (StepFits for a merge);
* `DescentOK`: the loop's descent keeps `DelInv` and gives the path down to the
  node it stops at, with the merge's conditions on it (the path facts);
* `CollapseStepOK`: the collapse's steps keep PutInv, PutInvG, the ranges and
  inner children, and a segment leaf has room for a replaced root's klong;
* `DelStepsOK`: the delete's other steps (the walk, the leaf's bitmap or split
  with its cascade, the upward delete) end in the delete's reading when the
  merges' loop and the collapse keep `DelInv` (PutInv and StepFits across
  `appendDeleteKlong` with its cascade are inside it).
-/
import SIS.Tree.GetMergeInv
import SIS.Tree.WriterMergeUpLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge's named conditions on the path down to the merged node at depth d
(`writerWP_merge_get_inv`): no space split in place below a segment leaf, and the
full parent's last version in the range of its link. -/
def MergePathCond (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (d : Nat) :
    Prop :=
  (∀ i, 0 < i → i + 2 ≤ d → (Nn (i - 1)).leaf = true → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → (Nn i).firstTime ≠ some c.i) ∧
  (2 ≤ d → (Nn (d - 2)).leaf = true → ∀ cL cR m1 m2 last,
      mergeFullLast (Nn (d - 1)) c.i cL m1 cR m2 = some last → c.p.splitAbove < last.size →
      (Nn (d - 1)).firstTime ≠ some c.i) ∧
  (2 ≤ d → ∀ cL cR m1 m2 last, mergeFullLast (Nn (d - 1)) c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → (Nn (d - 2)).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨(Nn (d - 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (d - 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (d - 2)).live → K (d - 1) < c'' → c' < c'')

/-- The invariants a step inside the delete keeps, but the reading. -/
def StepInv (c : Ctx) (base : View BVal) (v : W) : Prop :=
  PutInv c base v ∧ PutInvG c base v ∧ RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
  InnerChildrenExist (wNode c.p base v) c.i v.top.rootKey

/-- Obligation (StepFits and PutInv across a merge): a merge of the loop, from a
state inside a delete, keeps `StepInv` and the state after it fits the fuel. -/
def MergeStepOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode),
    DelInv c base w0 key v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' => StepInv c base v' ∧
      SegFits (wNode c.p base v') c.i (c.p.fuel - 1) v'.top.rootKey)

/-- Obligation (the path facts): the loop's descent keeps `DelInv` and gives
the key access path down to the node it stops at, with the merge's conditions. -/
def DescentOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w0 : W) (k0 key : Key) (g h : Nat) (v : W), DelInv c base w0 k0 v →
    WriterWP (descendToHeight key g h) c v (fun d v' => DelInv c base w0 k0 v' ∧
      (0 < d → ∃ X K Nn, PathOK c v' d X K Nn ∧ MergePathCond c X K Nn d))

/-- Obligation (PutInv across the collapse): the collapse's steps keep `StepInv`,
and a segment leaf has room for a replaced root's klong
(`writerWP_collapseRoot_coll`'s premises). -/
def CollapseStepOK (c : Ctx) (base : View BVal) : Prop :=
  (∀ w0 v x n leaf ln k, CollGetInv c base w0 v → StepInv c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) ∧
  (∀ w0 v x n only, CollGetInv c base w0 v → StepInv c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => StepInv c base v')) ∧
  (∀ w0 v x n only, CollGetInv c base w0 v → StepInv c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => StepInv c base v'))

/-- The collapse keeps `DelInv`. -/
theorem writerWP_collapseRoot_del (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hC : CollapseStepOK c base) (w0 : W) (k0 : Key) (v : W)
    (hI : DelInv c base w0 k0 v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInv c base w0 k0 v') := by
  obtain ⟨hP, hG, hR, hICE, hF, hread⟩ := hI
  have hCI : CollGetInv c base v v := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_collapseRoot_coll key seg c base hvc v (StepInv c base)
    (fun v v' hJ hr => ⟨putInv_of_readsAs c base v v' hJ.1 hr, putInvG_of_readsAs c base v v' hJ.2.1 hr,
      by rw [hr.1, hr.2.1]; exact hJ.2.2.1, by rw [hr.1, hr.2.1]; exact hJ.2.2.2⟩)
    (hC.1 v) (hC.2.1 v) (hC.2.2 v) c.p.fuel v hCI ⟨hP, hG, hR, hICE⟩) ?_
  rintro _ v' ⟨⟨_, hread', hF', _, _⟩, hJ'⟩
  refine ⟨hJ'.1, hJ'.2.1, hJ'.2.2.1, hJ'.2.2.2, hF', fun key' hk => ?_⟩
  rw [hread' key']
  exact hread key' hk

/-- The path facts carry over to a state with the same path, top and taken ids
and the overlay's nodes kept. -/
theorem pathOK_transport (c : Ctx) (v v' : W) (d : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (h : PathOK c v d X K Nn) (hp : v'.path = v.path)
    (hl : ∀ z zn, v.nodes.lookup z = some zn → v'.nodes.lookup z = some zn)
    (ht : v'.taken = v.taken) (htop : v'.top = v.top) : PathOK c v' d X K Nn := by
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := h
  refine ⟨fun i hi => by rw [hp]; exact hX i hi, fun i h1 h2 => by rw [hp]; exact hK i h1 h2,
    fun i hi => ⟨hl _ _ (hS2 i hi).1, by rw [ht]; exact (hS2 i hi).2⟩, hlink, by rw [htop]; exact h0⟩

/-- The merges' loop keeps `DelInv`, given the obligations. -/
theorem writerWP_mergeUp_del (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hM : MergeStepOK c base) (hD : DescentOK c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInv c base w0 k0 v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInv c base w0 k0 v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hI
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (hD w0 k0 key g h v hI) ?_
    intro d v1 ⟨hI1, hPF⟩
    split
    · simp only [writerWP_pure]; exact hI1
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1, hcond⟩ := hPF hd
      unfold pathNode
      simp only [writerWP_bind, writerWP_get]
      cases hex : v1.path[d]? with
      | none => exact writerWP_throw _ _ _ _
      | some ex =>
        simp only [writerWP_pure]
        cases heq : v1.path[d - 1]? with
        | none => exact writerWP_throw _ _ _ _
        | some eq =>
          simp only [writerWP_pure]
          refine writerWP_mono (writerWP_and (writerWP_getNode_all eq.2 c v1 base hvc)
            (writerWP_getNode_cache eq.2 c v1)) ?_
          rintro qn v2 ⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩
          have hI2 := delInv_of_readsAs c base w0 k0 v1 v2 hI1 hr2
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact hI2
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_getNode_all ex.2 c v2 base hvc)
              (writerWP_getNode_cache ex.2 c v2)) ?_
            rintro xn v3 ⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩
            have hI3 := delInv_of_readsAs c base w0 k0 v2 v3 hI2 hr3
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact hI3
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              obtain ⟨hX3, _, hS23, _, _⟩ := id hP3
              have hxX : X d = ex.2 := by
                have := hX3 d (Nat.le_refl _)
                rw [hp3, hp2, hex] at this
                exact (Option.some.inj this).symm
              have hqX : X (d - 1) = eq.2 := by
                have := hX3 (d - 1) (by omega)
                rw [hp3, hp2, heq] at this
                exact (Option.some.inj this).symm
              have hqn : Nn (d - 1) = qn := by
                have h1 := (hS23 (d - 1) (by omega)).1
                rw [hqX, hkeep3 _ _ hl2] at h1
                exact (Option.some.inj h1).symm
              obtain ⟨hc1, hc2, hc3⟩ := hcond
              have hmg := writerWP_merge_get_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap hc1 hc2 hc3
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn hI3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              refine writerWP_mono (writerWP_and hmg hms) ?_
              rintro r v4 ⟨hread4, ⟨hP4, hG4, hR4, hICE4⟩, hF4⟩
              have hI4 : DelInv c base w0 k0 v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk => by rw [hread4 hF4 key']; exact hI3.2.2.2.2.2 key' hk⟩
              split
              · simp only [writerWP_pure]; exact hI4
              · exact ih (h + 1) true v4 hI4

/-- `afterDelete` keeps `DelInv`, given the obligations. -/
theorem writerWP_afterDelete_del (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hM : MergeStepOK c base) (hD : DescentOK c base)
    (hC : CollapseStepOK c base) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (w0 : W) (k0 : Key) (v : W) (hI : DelInv c base w0 k0 v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInv c base w0 k0 v') :=
  writerWP_afterDelete_inv key g h c (DelInv c base w0 k0)
    (fun v hI => writerWP_mergeUp_del key g c base hvc hM hD hsa2 hcap w0 k0 c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_del key g c base hvc hC w0 k0 v hI) v hI

/-- Obligation (the delete's other steps): a delete with the merges on, from a
state between operations of a transaction within reach that meets `PutInv` and
the walk's ranges, changes the reading by itself alone when the state after it
fits the fuel, given that the merges' loop, `afterDelete` and the collapse keep
the delete's inner invariant. It holds the walk, the leaf's bitmap or split with
its cascade (PutInv and the fuel across `appendDeleteKlong` inside the delete),
and the upward delete; it is `writerWP_del_accessPathR`, `writerWP_del_bitmap_segR`
and `writerWP_deleteUpward_upT` with the merges' steps given. -/
def DelStepsOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v')) →
    (∀ g h merged v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v')) →
    (∀ seg v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

/-- Case 4 of 024-12's assembly, a delete with the merges on, from the named
step obligations: the delete's other steps (`DelStepsOK`), the merges' steps
(`MergeStepOK`), the loop's descent (`DescentOK`) and the collapse's steps
(`CollapseStepOK`), for 2 ≤ splitAbove and 1 ≤ mergeMax. -/
theorem opGetCaseOK_delMerge (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOK p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hD : ∀ ts, DescentOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) :
    OpGetCaseOK p R DelMergeCase := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  obtain ⟨key, hop, hmerges⟩ := hP
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO key hop hmerges
    (fun g h v hv => writerWP_afterDelete_del key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (hM ts) (hD ts) (hC ts) hsa2 hcap w key v hv)
    (fun g h merged v hv => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (hM ts) (hD ts) hsa2 hcap w key p.fuel h merged v hv)
    (fun seg v hv => writerWP_collapseRoot_del key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (hC ts) w key v hv)

/-! ## The obligations are not void

A run within reach (`Within`'s conditions as a Bool) of two transactions, twelve
puts and then ten deletes of them, node size 8, G 1, H 2, the merges on
(mergeBelow 2, mergeMax 3, splitAbove 4): every state between the deletes'
operations fits the fuel, and the writer merges in the deletes. So the
hypotheses of `OpGetCaseOK p R DelMergeCase` and of `MergeStepOK` (a merge of
the loop inside a delete) are met by a run. -/

/-- `Within p ts` as a Bool, and the run's last transaction tx = ts's last: every
state between its operations fits the fuel, its deletes run with the merges on,
and the writer merged at least once in it. -/
def dmCheck (p : Params) (ts : List Tx) (tx : Tx) : Bool :=
  let all := ts ++ [tx]
  all.all (fun t => t.sorted && t.wf) &&
  (List.range all.length).all (fun j =>
    match all[j]? with
    | none => false
    | some tj => (treeRun p (all.take j)).all (fun q => decide (q.1 < tj.base)) &&
        isOk (exec? p tj (j + 1) (view (treeSpec p) (treeRun p (all.take j)) j))) &&
  p.merges &&
  let v := view (treeSpec p) (treeRun p ts) ts.length
  match lastTop v with
  | none => false
  | some z =>
    match topOf p (ctxOf p ts).view z with
    | .error _ => false
    | .ok top =>
      (List.range (tx.ops.length + 1)).all (fun k =>
        match ((tx.ops.take k).mapM putKv) (ctxOf p ts) (wInit tx top) with
        | .ok (_, w) => asmFitsB p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
        | .error _ => false) &&
      tx.ops.any (fun o => match o with | .del _ => true | _ => false) &&
      match (tx.ops.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | .ok (_, w) => decide (0 < w.merges)
      | .error _ => false
def dmP : Params := {M := 8, G := 1, H := 2, mergeBelow := 2, mergeMax := 3, splitAbove := 4}
def dmTs : List Tx := [{base := 1000, ops := (List.range 12).map (fun j => .put [120, 64*j+8] (j+1))}]
def dmTx : Tx := {base := 2000, ops := (List.range 10).map (fun j => .del [120, 64*j+8])}
#guard dmCheck dmP dmTs dmTx

end SIS.Tree
