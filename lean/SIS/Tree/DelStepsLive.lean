/-
The upward delete with the fill at the delete's start (bergdb 024-12,
`LiveCounts`): with the merges on, the stop node of an upward delete is a
segment leaf (cost's `stopLeaf_of_liveCounts`), so LE-b never comes
(`lebStop_false`); `writerWP_del_emptyAnyMKL` and `writerWP_del_emptyAnyMJKL`
are the walks of `DelEmptyCascM` without LE-b's obligations.
-/
import SIS.Tree.DelStepsTree
import SIS.Tree.StopLeafLive

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The fill at a state of the transaction after the run ts. -/
def LiveCountsW (p : Params) (ts : List Tx) (w : W) : Prop :=
  LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey

/-- `DelEmptyCascM` with the fill at the delete's start. -/
def DelEmptyCascML (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelEmptyCascM c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey

/-- Case (4) with the fill at the operation's start. -/
def DelMergeCaseL (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey

/-- With the fill at the delete's start and the merges on, the upward delete's
stop node is no inner node: the node below it empties. -/
theorem lebStop_false (c : Ctx) (base : View BVal) (w : W)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) (hm : c.p.merges = true)
    (hI : PutInv c base w) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop cv : Nat)
    (hX0 : X 0 = w.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hsD : stop < depth)
    (hbetween : ∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hsl : (Nn stop).leaf = false) : False := by
  rcases Nat.lt_or_ge (stop + 1) depth with h | h
  · exact stopLeaf_of_liveCounts c.p (wNode c.p base w) c.i w.top.rootKey hLC hm X Nn K depth hX0 hXN hlinkK
      stop (by omega) hsl (K (stop + 1 + 1)) (hI.times _ _ (hXN (stop + 1) (by omega)))
      (hbetween (stop + 1) (by omega) h)
  · have he : depth = stop + 1 := by omega
    subst he
    exact stopLeaf_of_liveCounts c.p (wNode c.p base w) c.i w.top.rootKey hLC hm X Nn K (stop + 1) hX0 hXN
      hlinkK stop (Nat.le_refl _) hsl cv (hI.times _ _ (hXN (stop + 1) (Nat.le_refl _))) hall

/-- The delete's steps with the post `QdW`, the merges on, the fill at the
operation's start in the case. -/
def DelStepsQdL (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsCaseQd p R (fun c base w op => (∃ key, op = .del key ∧ c.p.merges = true) ∧
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)

/-- The delete with the merges on (case (4)) keeps `QdW`: `DelStepsQd` with the
merges' loop (`writerWP_mergeUp_del`) and root collapse
(`writerWP_collapseRoot_del`, `writerWP_afterDelete_del`), the fuel at the
operation's start from `TxSegFitsOK`. -/
theorem opCaseOK_qdW_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (fun ts _ _ w' => QdW p ts w') DelMergeCaseL := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  obtain ⟨⟨key, hop, hmerges⟩, hLCw⟩ := hP
  have hF0 := hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop ⟨⟨key, hop, hmerges⟩, hLCw⟩
    (fun g h v hv' => writerWP_afterDelete_del key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_del key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- `t4`, `i4` and `r4` with the fill at the operation's start (`DelMergeCaseL`): the delete with the merges on keeps the writer's tree
(`QTree`), `PutInv` (`QPutInv`) and the walk's ranges (`QRange`). -/
theorem opCaseOK_treeInvRange_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (QTree p) DelMergeCaseL ∧ OpCaseOK p R (QPutInv p) DelMergeCaseL ∧
      OpCaseOK p R (QRange p) DelMergeCaseL := by
  have h := opCaseOK_qdW_delMergeRL p R hS hM hC hsa2 hcap hRP hRK hfit
  refine ⟨?_, ?_, ?_⟩
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq => hq.1.tree)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.1)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.2)

end SIS.Tree
