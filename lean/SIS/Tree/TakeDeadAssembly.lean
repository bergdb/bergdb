/-
The take-back's (B), (C) and their node facts over latest's operation cases
(bergdb 024-12, TP7; `OpJ2OK`, TakeBackRunJ2.lean): per case `OpJ2CaseOK`, over
the nine cases (`opCase_cover`) `opJ2OK_of_cases`; the cases (1), (5), (6) and
(8) proved from `PutInv` and `LeafVals` (a key's leaf names values by its
klong of the key's last segment: no node, below B or a value of the
transaction), which the state predicate gives.
-/
import SIS.Tree.TakeBackRunJ2
import SIS.Tree.TakeDeadCases
import SIS.Tree.ChildrenKinds
import SIS.Tree.GetOpAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- An operation case P keeps `J2At` from a state with the writer's tree and S. -/
def OpJ2CaseOK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w → S ts tx w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w')

/-- Over the nine cases. -/
theorem opJ2OK_of_cases (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (c1 : OpJ2CaseOK p R S PutLeafRoomCase) (c2 : OpJ2CaseOK p R S PutLeafFullCase)
    (c3 : OpJ2CaseOK p R S PutNewSegCase) (c4 : OpJ2CaseOK p R S DelMergeCase)
    (c5 : OpJ2CaseOK p R S DelNoLeafCase) (c6 : OpJ2CaseOK p R S DelNoopCase)
    (c7 : OpJ2CaseOK p R S DelEmptyCase) (c8 : OpJ2CaseOK p R S DelRoomCase)
    (c9 : OpJ2CaseOK p R S DelFullCase) : OpJ2OK p R S := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with h | h | h | h | h | h | h | h | h
  · exact c1 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c2 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c3 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c4 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c5 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c6 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c7 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c8 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h
  · exact c9 ts tx hw hr z top hz htop pre op post hsplit r w hpre hT hS hJ h

/-- A key's leaf names values by its klong of the key's last segment: no node,
below B or a value of the transaction. -/
def LeafVals (c : Ctx) (base : View BVal) (B : NodeId) (w : W) : Prop :=
  ∀ pre cv L n, keyWf (pre ++ [cv]) = true → KeyLeaf c base w pre cv L n →
    ∀ y, (cv, y) ∈ n.liveAt c.i → wNode c.p base w y = none ∧ (y < B ∨ y ∈ w.vals.map (·.1))

/-- The leaf of a key's descent is reached. -/
theorem keyLeaf_reached {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    {pre : List Nat} {cv : Nat} {rk : NodeId}
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) :
    ∀ L, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      TReach (wNode c.p base w) c.i w.top.rootKey L := fun L hL =>
  reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) (pre ++ [cv]) _ L cv
    ReachS.root (fromVisits_append _ _ _ pre cv _ rk hrk _ hL))

/-- `LeafVals` for every leaf of the key's descent. -/
theorem leafVals_all {c : Ctx} {base : View BVal} {B : NodeId} {w : W} (hV : LeafVals c base B w)
    {pre : List Nat} {cv : Nat} {rk : NodeId} (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) :
    ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none ∧ (y < B ∨ y ∈ w.vals.map (·.1)) :=
  fun L n hL hn hnl y hy => hV pre cv L n hkey ⟨rk, hrk, hL, hn, hnl⟩ y hy

/-- The next id is no node. -/
theorem PutInv.nextNone {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w) :
    wNode c.p base w w.next = none := by
  obtain ⟨hidn, _, hidt, _, _⟩ := hI.ids
  have ht : w.taken.contains w.next = false := by
    cases h' : w.taken.contains w.next with
    | false => rfl
    | true => have := hidt _ h'; omega
  have hl : w.nodes.lookup w.next = none := by
    cases h' : w.nodes.lookup w.next with
    | none => rfl
    | some _ => have := hidn _ (by rw [h']; rfl); omega
  simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh w.next (Nat.le_refl _)).1]

/-! ## The cases (1), (5), (6), (8) -/

theorem opJ2Case_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :
    OpJ2CaseOK p R S PutLeafRoomCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ _ hS hJ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_put_room_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk
    tx.base w (by simp [ctxOf]) hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)
      ⟨hI.wf L n hn, hI.times L n hn, hroom.1, hroom.2⟩)
    hJ (keyLeaf_reached hI hrk) (leafVals_all (hSV ts tx w hS) hkey hrk) hI.nextNone) ?_
  intro _ w' h _
  exact h

theorem opJ2Case_delNoLeaf (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :
    OpJ2CaseOK p R S DelNoLeafCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ _ hS hJ hP
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  refine writerWP_mono (writerWP_del_noLeaf_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key tx.base w
    hne (hI.pathUntaken key) hno' hJ) ?_
  intro _ w' h _
  exact h

theorem opJ2Case_delNoop (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :
    OpJ2CaseOK p R S DelNoopCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ _ hS hJ hP
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_del_noop_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk tx.base
    w hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap)
      hnoop) hJ) ?_
  intro _ w' h _
  exact h

theorem opJ2Case_delRoom (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :
    OpJ2CaseOK p R S DelRoomCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ _ hS hJ hP
  obtain ⟨pre, cv, L, n, hop, hmerges, hK, hne, hkeep, hroom⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_del_room_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk tx.base
    w hmerges (by simp [ctxOf]) hrk (hI.pathUntaken _) (keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L n hn, hI.times L n hn, hne, hkeep, hroom⟩)
    hJ (keyLeaf_reached hI hrk) (leafVals_all (hSV ts tx w hS) hkey hrk)) ?_
  intro _ w' h _
  exact h

/-! ## `LeafVals` from the walk of the kinds -/

/-- A leaf's klong of a last segment's compare value names a value: by the
overlay's kinds for a cached leaf, by the view's for one of the base. -/
theorem leafVals_of_kinds (K : KindOracle) (B : NodeId) (c : Ctx) (base : View BVal) (w : W)
    (hkc : KindCache K w) (hvk : ViewKinds K B c)
    (hvals : ∀ q ∈ w.vals, B ≤ q.1 ∧ q.1 < w.next ∧ q.1 ∉ w.gh.map (·.1)) (hb : Book B c w)
    (hbaseNew : ∀ z, B ≤ z → knodeOf c.p base z = none)
    (hbaseVal : ∀ z, K.val z → knodeOf c.p base z = none)
    (hbaseView : ∀ x n, knodeOf c.p base x = some n → ∃ nd, c.view x = some nd ∧ nd.isData = false ∧
      nd.level ≤ c.p.keyMax ∧ n = ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩) :
    LeafVals c base B w := by
  intro pre cv L n hkey hK y hy
  obtain ⟨_, _, _, hn, hnl⟩ := hK
  have hcv : segLen cv ≠ 7 := segLen_last_of_keyWf pre cv hkey
  have hk : Klong.key cv y ∈ n.ks := KNode.liveAt_key_mem n c.i cv y hy
  have hval : IsValId K w y := by
    have hLt : w.taken.contains L = false := by
      cases h : w.taken.contains L with
      | false => rfl
      | true =>
        have : wNode c.p base w L = none := by simp only [wNode, h, ↓reduceIte]
        rw [this] at hn; cases hn
    cases hl : w.nodes.lookup L with
    | some m =>
      have hm : wNode c.p base w L = some m := by
        simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hl]
      rw [hn] at hm
      cases hm
      have hmem := mem_ids_of_lookup w.nodes L n hl
      have hxg : L ∈ w.gh.map (·.1) := by
        rw [← List.mem_reverse, ← hb.ids]
        exact List.mem_map.mpr ⟨(L, n), hmem, rfl⟩
      obtain ⟨⟨L', g, h⟩, hq, hL'⟩ := List.mem_map.mp hxg
      simp only at hL'
      subst hL'
      have hh : h = 0 := by
        have := hb.leaf L' n g h hmem hq
        rw [hnl] at this
        simpa using this.symm
      subst hh
      exact ((hkc L' n g 0 hmem hq cv y hk).2 rfl).2 hcv
    | none =>
      have hkn : knodeOf c.p base L = some n := by
        simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hl] at hn
        exact hn
      obtain ⟨nd, hnd, hd, hlv, rfl⟩ := hbaseView L n hkn
      have hh : c.p.heightOf nd.level = 0 := by simpa using hnl
      exact Or.inr ((hvk.klongs L nd hnd hd hlv cv y hk).2 hh |>.2 hcv)
  refine ⟨wNode_val_none K B c base w hvk hvals hb hbaseNew hbaseVal y hval, ?_⟩
  rcases hval with ⟨hh, hm⟩ | hv
  · exact Or.inr (List.mem_map.mpr ⟨_, hm, rfl⟩)
  · exact Or.inl (hvk.oldVal y hv)

/-! ## `LeafVals` with the base's leaves by a premise -/

/-- A leaf's klong of a last segment's compare value names a value: by the
overlay's kinds for a cached leaf, by the view's for one of the base. -/
theorem leafVals_of_kindsB (K : KindOracle) (B : NodeId) (c : Ctx) (base : View BVal) (w : W)
    (hkc : KindCache K w) (hvk : ViewKinds K B c)
    (hvals : ∀ q ∈ w.vals, B ≤ q.1 ∧ q.1 < w.next ∧ q.1 ∉ w.gh.map (·.1)) (hb : Book B c w)
    (hbaseNew : ∀ z, B ≤ z → knodeOf c.p base z = none)
    (hbaseVal : ∀ z, K.val z → knodeOf c.p base z = none)
    (hbaseLeaf : ∀ x n, knodeOf c.p base x = some n → n.leaf = true → ∀ cv y,
      Klong.key cv y ∈ n.ks → segLen cv ≠ 7 → K.val y) :
    LeafVals c base B w := by
  intro pre cv L n hkey hK y hy
  obtain ⟨_, _, _, hn, hnl⟩ := hK
  have hcv : segLen cv ≠ 7 := segLen_last_of_keyWf pre cv hkey
  have hk : Klong.key cv y ∈ n.ks := KNode.liveAt_key_mem n c.i cv y hy
  have hval : IsValId K w y := by
    have hLt : w.taken.contains L = false := by
      cases h : w.taken.contains L with
      | false => rfl
      | true =>
        have : wNode c.p base w L = none := by simp only [wNode, h, ↓reduceIte]
        rw [this] at hn; cases hn
    cases hl : w.nodes.lookup L with
    | some m =>
      have hm : wNode c.p base w L = some m := by
        simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hl]
      rw [hn] at hm
      cases hm
      have hmem := mem_ids_of_lookup w.nodes L n hl
      have hxg : L ∈ w.gh.map (·.1) := by
        rw [← List.mem_reverse, ← hb.ids]
        exact List.mem_map.mpr ⟨(L, n), hmem, rfl⟩
      obtain ⟨⟨L', g, h⟩, hq, hL'⟩ := List.mem_map.mp hxg
      simp only at hL'
      subst hL'
      have hh : h = 0 := by
        have := hb.leaf L' n g h hmem hq
        rw [hnl] at this
        simpa using this.symm
      subst hh
      exact ((hkc L' n g 0 hmem hq cv y hk).2 rfl).2 hcv
    | none =>
      have hkn : knodeOf c.p base L = some n := by
        simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hl] at hn
        exact hn
      exact Or.inr (hbaseLeaf L n hkn hnl cv y hk hcv)
  refine ⟨wNode_val_none K B c base w hvk hvals hb hbaseNew hbaseVal y hval, ?_⟩
  rcases hval with ⟨hh, hm⟩ | hv
  · exact Or.inr (List.mem_map.mpr ⟨_, hm, rfl⟩)
  · exact Or.inl (hvk.oldVal y hv)

/-- `LeafVals` at every state that a prefix of a transaction's operations
reaches: the books and the overlay's kinds by the walk (`kd_ops`), the base's
by `KindsAllOK` and `PointersOK` of P. -/
theorem leafVals_reached (p : Params) (hM : 2 ≤ p.M) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (top : Top) (pre post : List Op) (hsplit : tx.ops = pre ++ post)
    (r : List Bool) (w : W) (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hPt : PointersOK (treeRun p ts)) (hK : KindsAllOK p (treeRun p ts)) :
    LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := by
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hvk := viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) hPt hK
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top)
    (viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh))
    hvk (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  refine leafVals_of_kindsB (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) _ w hkd.2.1.cache hvk
    hkd.2.1.vals hkd.1 ?_ ?_ ?_
  · intro z hz
    show knodeOf p (viewOf (treeRun p ts)) z = none
    cases hk : knodeOf p (viewOf (treeRun p ts)) z with
    | none => rfl
    | some n =>
      obtain ⟨nd, hg, _, _, _⟩ := knodeOf_viewOf p _ z n hk
      have := hfresh _ (mem_of_get? hg)
      simp only at this
      omega
  · rintro z ⟨ny, hny, hd⟩
    show knodeOf p (viewOf (treeRun p ts)) z = none
    cases hk : knodeOf p (viewOf (treeRun p ts)) z with
    | none => rfl
    | some n =>
      obtain ⟨nd, hg, hd', _, _⟩ := knodeOf_viewOf p _ z n hk
      rw [hny] at hg
      cases hg
      rw [hd] at hd'
      cases hd'
  · intro x n hk hnl cv y hky hcv
    obtain ⟨nd, hg, hd, hlv, rfl⟩ := knodeOf_viewOf p _ x n (by exact hk)
    have hh : p.heightOf nd.level = 0 := by simpa using hnl
    obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist cv y hky
    have hy := hPt _ (mem_of_get? hg) e he y (by rw [hv]; simp [bptrs])
    obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hy
    exact ⟨ny, hny, ((hK x nd hg hd hlv cv y hky ny hny).2 hh).2 hcv⟩

/-- No node taken back is a value at a transaction's end, for runs whose
structure has its pointers and kinds (`execW_takenNotVal`). -/
theorem takenNotValOK_of (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    TakenNotValOK p R := by
  intro ts tx hw hr noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (noops, w) := hrun
  have hvk := viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts)
    (hRP _ _ hr) (hRK _ _ hr)
  exact execW_takenNotVal (kindOracleOf p (treeRun p ts)) p tx (ts.length + 1) _ noops w hM hwf
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hvk he

/-! ## TP7's take-back from the open cases -/

/-- The state predicate of the take-back's assembly: `PutInv` and `LeafVals`. -/
def TakeS (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
    LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w

/-- TP7's take-back statement (`TakeBackOKUnder p (RunLinksOK p)`) from: the
run induction's Q with P's pointers and kinds; the writer's tree under the run
premise (latest's `opTreeOKUnder_of_any`); `PutInv` at every state between
operations (latest's `joint_reached`); P's key nodes starting before the next
transaction; and the take-back's five open operation cases (2), (3), (4), (7),
(9). The cases (1), (5), (6), (8) are proved. -/
theorem takeBackOK_of_cases (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c2 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) PutLeafFullCase)
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) PutNewSegCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) DelFullCase) :
    TakeBackOKUnder p (RunLinksOK p) := by
  have hSI : ∀ ts tx w, TakeS p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1
  have hSV : ∀ ts tx w, TakeS p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.2
  have hS : StateOK p (RunTreeQ p Q) (TakeS p) := by
    intro ts tx hw hr z top hz htop pre post hsplit r w h
    exact ⟨hPI ts tx hw hr z top hz htop pre post hsplit r w h,
      leafVals_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩
  have hSRF : ∀ ts tx w, TakeS p ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w :=
    fun ts _ w h y hy => h.1.untaken y (tReach_reachS _ _ _ _ hy)
  have hO : OpJ2OK p (RunTreeQ p Q) (TakeS p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV) c2 c3 c4
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI) c7 (opJ2Case_delRoom p _ _ hSI hSV) c9
  exact takeBackOK_of_jointJ2 p hM Q hQ0 hQs ho (TakeS p) hO hS hSRF hB
    (takenNotValOK_of p hM _ (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-! ## With the merges on: the cases (5) to (9) void -/

theorem opJ2CaseOK_void (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (hm : p.merges = true)
    (hP : ∀ c base w op, P c base w op → c.p.merges = false) : OpJ2CaseOK p R S P := by
  intro ts _ _ _ _ _ _ _ _ op _ _ _ w _ _ _ _ hPc
  have h : p.merges = false := hP _ _ _ _ hPc
  rw [hm] at h
  cases h

/-- TP7's take-back statement with the merges on: `takeBackOK_of_cases` with the
cases (5) to (9) void, so only (2), (3) and (4) open. -/
theorem takeBackOK_of_cases_merges (p : Params) (hM : 2 ≤ p.M) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c2 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) PutLeafFullCase)
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) PutNewSegCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS p) DelMergeCase) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_cases p hM Q hQ0 hQs hQP hQK ho hPI hB c2 c3 c4
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

end SIS.Tree
