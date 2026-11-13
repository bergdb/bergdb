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

end SIS.Tree
