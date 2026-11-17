/-
`l4` assembled (bergdb 030-01, step 7): the live family's cases at one delete of the
induction's runs give `l4L` (`LiveDelSL`), so the top theorem holds with the open
narrow pieces as its premises: the merge's tail with its parent full in the
cases left (`MergeTailFullRest3OK`), R3 at the calls of `afterDelete`
(`R3Calls`), the full leaf split in time below a parent without room
(`DelFullTimeCascM`, R4) and the upward delete whose stop node has no room
(`DelEmptyCascM`). Every other case is proved: the noop, the key with no leaf,
(4a), the bitmap with room, the full leaf's splits (`delFullM_cover`), the emptied
space root and the upward delete with room.
-/
import SIS.Tree.LiveTop
import SIS.Tree.HtbNoTb
import SIS.Tree.LiveMergeSpace
import SIS.Tree.LiveUpRoomH
import SIS.Tree.LiveDelRootMade
import SIS.Tree.LiveDelSegSpaceMade
import SIS.Tree.LiveDelSpaceChain2
import SIS.Tree.LiveDelFullDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The cases' common form -/

/-- The form of the delete's cases (bergdb 030-01, steps 5 and 6): a delete of case
P from the first stratum's start, at a state of a run of R, calls `afterDelete` at
its node's pair (g, 0) with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`:
any continuation from there that gives Q gives Q after the delete. -/
def DelCaseLive (p : Params) (R : Struct BVal → Time → Prop) (P : Ctx → View BVal → W → Op → Prop) :
    Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
    (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
        tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
      LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w')

/-- The full leaf split in time below a parent without room for the copy's klong:
the cascade with the copy the hole below the chain (030-01's R4, open). -/
def DelFullTimeCascM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeGM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ¬ ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false

/-- R3 at the calls of `afterDelete` of the runs of R (030-01, section 2.3): after
the merges' loop that merged, the segment root that root collapse's first round
finds, made by the transaction with no made-for entry and inner, has no only live
klong (`R3At`), at every call with the delete's facts. -/
def R3Calls (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
        tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
      LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (mergeUp key g p.fuel 0 false) (ctxOf p ts) v
        (fun merged v' => merged = true → R3At key g (ctxOf p ts) v')

/-- The merge's tail with its parent full in the cases left (prover l4c's
`MergeTailFullRest3OK`) at the contexts of the runs of R. -/
def MergeTailRuns (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    MergeTailFullRest3OK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts))

/-! ## The full leaf's cases -/

/-- Every full leaf's delete is in one of the full leaf's cases: the made leaf split
in time in place; split in time below a parent with room, or without (R4); at the
space root, not made; the made space root split in space; split in space below an
inner parent or a segment leaf, made by the transaction or not. -/
theorem delFullM_cover (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey) (h : DelFullM c base w op) :
    (DelFullTimeGM c base w op ∧ ∀ pre' cv' L' n', op = .del (pre' ++ [cv']) →
      KeyLeaf c base w pre' cv' L' n' → n'.firstTime = some c.i) ∨
    DelFullTimeRoomGM c base w op ∨ DelFullTimeCascM c base w op ∨ DelFullRootM c base w op ∨
    DelFullRootSpaceMadeM c base w op ∨ DelFullSpaceChainM c base w op ∨
    DelFullSegSpaceChainM c base w op ∨ DelFullSpaceMadeChainM c base w op ∨
    DelFullSegSpaceMadeM c base w op := by
  obtain ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, hfull⟩ := h
  have huniq : ∀ (P : NodeId → KNode → Prop), P L n → ∀ pre' cv' L' n', op = .del (pre' ++ [cv']) →
      KeyLeaf c base w pre' cv' L' n' → P L' n' := by
    intro P hP pre' cv' L' n' hop' hK'
    rw [hop] at hop'
    injection hop' with hk
    obtain ⟨h1, h2⟩ := List.append_inj hk (by simpa using congrArg List.length hk)
    have h3 : cv = cv' := by simpa using h2
    subst h1 h3
    obtain ⟨rk', hrk', hL', hn', hnl'⟩ := hK'
    exact keyLeaf_all2 hK hrk' P hP L' n' hL' hn' hnl'
  have hone : ∀ q qn k1 q' qn' k1', TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → (k1, L) ∈ qn.liveAt c.i →
      TReach (wNode c.p base w) c.i w.top.rootKey q' → wNode c.p base w q' = some qn' →
      (k1', L) ∈ qn'.liveAt c.i → qn' = qn := by
    intro q qn k1 q' qn' k1' hq hqn hk hq' hqn' hk'
    obtain ⟨he, _⟩ := hT.oneLink q k1 q' k1' L hq hq' ⟨qn, hqn, hk⟩ ⟨qn', hqn', hk'⟩
    subst he
    rw [hqn] at hqn'
    exact (Option.some.inj hqn').symm
  by_cases hTP : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove ∨
      ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∨ n.size + 1 < c.p.M
  · have hG : DelFullTimeGM c base w op := ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, hfull, hTP⟩
    by_cases hmade : n.firstTime = some c.i
    · exact Or.inl ⟨hG, huniq (fun _ m => m.firstTime = some c.i) hmade⟩
    by_cases hroot : L = w.top.rootKey
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, hfull, hmade, hroot⟩)))
    by_cases hroom : ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (k1, L) ∈ qn.liveAt c.i →
        qn.size + 2 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false
    · exact Or.inr (Or.inl ⟨hG, huniq (fun L' m => m.firstTime ≠ some c.i ∧ L' ≠ w.top.rootKey ∧
        ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
          (k1, L') ∈ qn.liveAt c.i → qn.size + 2 ≤ c.p.M ∧
            deadOver c.p (qn.add c.i (.key k1 w.next)) = false) ⟨hmade, hroot, hroom⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hG, huniq (fun L' m => m.firstTime ≠ some c.i ∧ L' ≠ w.top.rootKey ∧
        ¬ ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
          (k1, L') ∈ qn.liveAt c.i → qn.size + 2 ≤ c.p.M ∧
            deadOver c.p (qn.add c.i (.key k1 w.next)) = false) ⟨hmade, hroot, hroom⟩⟩))
  · have hsp : c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size := by
      apply Classical.byContradiction; intro h'; exact hTP (Or.inl (by omega))
    have htd : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) :=
      fun h' => hTP (Or.inr (Or.inl h'))
    have hsz : c.p.M ≤ n.size + 1 := by
      apply Classical.byContradiction; intro h'; exact hTP (Or.inr (Or.inr (by omega)))
    by_cases hroot : L = w.top.rootKey
    · by_cases hmade : n.firstTime = some c.i
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, htd, hsz, hsp, hmade, hroot⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, hfull, hmade, hroot⟩)))
    by_cases hinner : ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (k1, L) ∈ qn.liveAt c.i → qn.leaf = false
    · by_cases hmade : n.firstTime = some c.i
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, htd, hsz, hsp, hmade, hroot, hinner⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, htd, hsz, hsp, hmade, hroot, hinner⟩)))))
    · have hseg : ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q →
          wNode c.p base w q = some qn → (k1, L) ∈ qn.liveAt c.i → qn.leaf = true := by
        intro q qn k1 hq hqn hk
        apply Classical.byContradiction; intro hlf
        apply hinner
        intro q' qn' k1' hq' hqn' hk'
        rw [hone q qn k1 q' qn' k1' hq hqn hk hq' hqn' hk']
        simpa using hlf
      by_cases hmade : n.firstTime = some c.i
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, htd, hsz, hsp, hmade, hroot, hseg⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨pre, cv, L, n, hop, hm, hK, hne, hkeep, htd, hsz, hsp, hmade, hroot, hseg⟩))))))

/-! ## The call of `afterDelete`, the family and the top theorem -/

set_option maxHeartbeats 1600000 in
/-- `afterDelete` at the calls of the runs: from the call's facts, the live counts
after, given the merge's tail's open cases and R3 (prover l4c's
`writerWP_afterDelete_liveTR3`). -/
theorem afterDelete_live_runs (p : Params) (R : Struct BVal → Time → Prop) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hF : MergeTailRuns p R) (hR3 : R3Calls p R) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → SJ0 p ts tx w →
      ∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' =>
          LiveEdges p (wNode p (viewOf (treeRun p ts)) v') (ts.length + 1) v'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre key post hops r w hpre hS g v hD hpb hhi hLH
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hm : (ctxOf p ts).p.merges = true := by
    show p.merges = true
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa2 : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p (by omega) ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre
    (Op.del key :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  exact writerWP_afterDelete_liveTR3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp _ tx.base hv hk
    hICEk hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hF ts tx hw hr) v (delInvJAE_of_T _ _ _ _ _ v hD)
    hpb hhi hLH (hR3 ts tx hw hr z top hz htop pre key post hops g v hD hpb hhi hLH)

set_option maxHeartbeats 3200000 in
/-- `l4L` from the open narrow pieces (bergdb 030-01, step 7): at a delete of the
induction's runs in the open case, the first stratum's start (`SJ0`) from the
induction's facts, then by the delete's cases (`delMerge_cover`, `delEmptyM_split`,
`delEmptyOther_split`, `delFullM_cover`), each proved but `DelFullTimeCascM` (R4)
and `DelEmptyCascM`, with `afterDelete` from the merge's tail's open cases and R3. -/
theorem liveDelSL_of_pieces (p : Params) (hp : MergeParamsOK p)
    (hF : MergeTailRuns p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeCascM)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    LiveDelSL p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa2 : 2 ≤ p.splitAbove := by omega
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRP : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t := fun _ _ h => h.2.2.1.2.2.2.1
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRo hL hH _ hJ hC
  have hSJ : SJ0 p ts tx w :=
    ⟨⟨⟨⟨⟨hI, leafVals_reached p (by omega) ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr)
      (hRK _ _ hr)⟩, base_le_next_reached p (by omega) ts tx hw top pre (Op.del key :: post) hs r w hpre
      (hRP _ _ hr) (hRK _ _ hr)⟩, hRo⟩,
      stateOK_madeFor p hM4 _ hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre⟩,
      htStart0_of_ht p _ hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH, hL⟩
  have hJ2 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hfr : ∀ v, LiveEdges p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey →
      WriterWP fresh (ctxOf p ts) v (fun _ v' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) v') (ts.length + 1) v'.top.rootKey) := by
    intro v hv
    unfold fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hv
  have hA := afterDelete_live_runs p _ hp hRL hRP hRK hF hR3 ts tx hw hr z top hz htop pre key post hs r w
    hpre hSJ
  have run : ∀ P : Ctx → View BVal → W → Op → Prop, DelCaseLive p (RunTreeQ p (LatestQD p)) P →
      P (ctxOf p ts) (viewOf (treeRun p ts)) w (Op.del key) →
      WriterWP (putKv (Op.del key)) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) :=
    fun P hP hc => hP ts tx hw hr z top hz htop pre (Op.del key) post hs r w hpre hSJ hJ2 key rfl hc _ hfr hA
  have hlive : WriterWP (putKv (Op.del key)) (ctxOf p ts) w (fun _ w' =>
      LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
    obtain ⟨_, hNo, hNL⟩ := hC
    rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
    · exact absurd h hNL
    · exact absurd h hNo
    · rcases delEmptyM_split _ _ _ _ h with h1 | h1
      · exact run _ (liveDel_upRoomH p _ (by omega) hRL hRP hRK) h1
      · rcases delEmptyOther_split _ _ _ _ h1 with h2 | h2
        · exact liveDel_emptyRoot p _ hsa2 hRL ts tx hw hr z top hz htop pre _ post hs r w hpre hI h2
        · exact run _ hCasc h2
    · exact run _ (liveDel_room p _ (by omega) hRL hRP hRK) h
    · rcases delFullM_cover _ _ _ _ hI.tree h with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
      · exact liveDel_fullMadeG p _ (by omega) hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre _ post hs r w
          hpre hSJ hJ2 key rfl h1.1 h1.2 _ hfr hA
      · exact run _ (liveDel_fullTimeRoomG p _ (by omega) hsa2 hRL hRP hRK) h1
      · exact run _ hR4 h1
      · exact run _ (liveDel_fullRoot p _ (by omega) hsa2 hp hRL hRP hRK) h1
      · exact run _ (liveDel_fullRootSpaceMade p _ (by omega) hsa2 hp hRL hRP hRK) h1
      · exact run _ (liveDel_fullSpaceChain p _ (by omega) hsa2 hp hRL hRP hRK) h1
      · exact run _ (liveDel_fullSegSpaceChain p _ (by omega) hsa2 hp hRL hRP hRK) h1
      · exact run _ (liveDel_fullSpaceMadeChain p _ (by omega) hsa2 hp hRL hRP hRK) h1
      · exact run _ (liveDel_fullSegSpaceMade p _ (by omega) hsa2 hp hRL hRP hRK) h1
  refine writerWP_mono hlive ?_
  intro _ w' hE _ _
  exact liveCounts_of_edges _ _ _ _ hE

/-- TP7, TP10 and TP11 for Java's parameters without `l4` (bergdb 030-01, step 7):
from `hp`, `hth` and the open narrow pieces of `l4`, each stated at the induction's
runs: the merge's tail with its parent full in the cases left (`MergeTailRuns`,
prover l4c's `MergeTailFullRest3OK`), R3 at the calls of `afterDelete`
(`R3Calls`), the full leaf split in time below a parent without room
(`DelFullTimeCascM`, R4) and the upward delete whose stop node has no room
(`DelEmptyCascM`), the last two in the delete cases' form (`DelCaseLive`). -/
theorem invGetScanOK_merges_noL4 (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeCascM)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_l4L p hp hth (takeBelowFuelDelSL_holds p hp)
    (liveDelSL_of_pieces p hp hF hR3 hR4 hCasc)

/-! ## Successors as pieces land -/

/-- The merge's tail with its parent full in the cases left after l4c's fifth part
(`MergeTailFullRest4OK`) at the contexts of the runs of R. -/
def MergeTailRuns4 (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    MergeTailFullRest4OK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts))

/-- `MergeTailRuns` from `MergeTailRuns4` (`mergeTailFullRest3OK_of_rest4`). -/
theorem mergeTailRuns_of_4 (p : Params) (hp : MergeParamsOK p) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (h4 : MergeTailRuns4 p R) : MergeTailRuns p R := by
  intro ts tx hw hr
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hm : (ctxOf p ts).p.merges = true := by
    show p.merges = true
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  exact mergeTailFullRest3OK_of_rest4 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp
    (viewHtOK_of_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr)) (h4 ts tx hw hr)

/-- `invGetScanOK_merges_noL4` with the merge's tail's open cases narrowed
(`MergeTailRuns4`, prover l4c's `MergeTailFullRest4OK`). -/
theorem invGetScanOK_merges_noL4b (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns4 p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeCascM)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_noL4 p hp hth
    (mergeTailRuns_of_4 p hp _ (fun _ _ h => h.1) (fun _ _ h => h.2.2.1.2.2.1) (fun _ _ h => h.2.2.1.2.2.2.1) hF)
    hR3 hR4 hCasc

end SIS.Tree
