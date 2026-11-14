/-
The deletes with the merges on that change nothing the writer reads (bergdb
024-12, cases of `l4` and `d4`): a delete of a key that has no leaf, and one
whose bitmap changes nothing, read as before (`writerWP_del_noLeaf_reads`,
`writerWP_del_noop_reads`), so they keep every property of the nodes the writer
reads and its top, `QLive` and `QDead` among them. `l4` and `d4` narrow to the
deletes that change the tree and are not (4a): `DelMergeOpenCase`,
`DelMergeDOpenCase`.
-/
import SIS.Tree.LiveDelRoom
import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete whose bitmap changes nothing reads as before. -/
theorem writerWP_del_noop_reads (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ReadsAs c.p base w w') := by
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnoop := hleaf L n hvisL hn hnl
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnoopb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by
    rw [hnoop]; simp
  simp only [hnoopb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
  exact hr03

/-- A delete of a key that has no leaf reads as before. -/
theorem writerWP_del_noLeaf_reads (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (w : W) (hI : PutInv c base w) (hne : key ≠ [])
    (hno : ¬ ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n) :
    WriterWP (putKv (.del key)) c w (fun _ w' => ReadsAs c.p base w w') := by
  have hno' : NoLeafFrom (wNode c.p base w) c.i c.p.fuel key w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by
    subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_mono (writerWP_putSegs_del_noLeaf c _ hvc key key w.top.rootKey w2 hne ?_ ?_) ?_
  · intro q hq
    rw [hr02.2.2.1]
    rw [hr02.1] at hq
    exact hI.pathUntaken key q hq
  · rw [hr02.1]; exact hno'
  · intro _ w' hr'
    exact ReadsAs.trans _ _ _ _ _ hr02 hr'

/-- A property of the operation's states that reading as before keeps. -/
def KeptByReads (p : Params) (Q : List Tx → Op → W → W → Prop) : Prop :=
  ∀ ts op w w', ReadsAs p (viewOf (treeRun p ts)) w w' → Q ts op w w'

theorem keptByReads_live (p : Params) : KeptByReads p (QLive p) := by
  intro ts op w w' hr _ hL
  have e : wNode p (viewOf (treeRun p ts)) w' = wNode p (viewOf (treeRun p ts)) w := hr.1
  rw [e, hr.2.1]
  exact hL

theorem keptByReads_dead (p : Params) : KeptByReads p (QDead p) := by
  intro ts op w w' hr hD h0 x n hx
  have e : wNode p (viewOf (treeRun p ts)) w' = wNode p (viewOf (treeRun p ts)) w := hr.1
  change wNode p (viewOf (treeRun p ts)) w' x = some n at hx
  rw [e] at hx
  exact hD h0 x n hx

/-- A noop delete keeps what reading as before keeps. -/
theorem opCaseOK_delNoop (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hQ : KeptByReads p Q) : OpCaseOK p R Q DelNoopM := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hleaf := keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap) hnoop
  exact writerWP_mono (writerWP_del_noop_reads (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    hI hrk hleaf) (fun _ w' hr => hQ ts _ w w' hr)

/-- A delete of a key with no leaf keeps what reading as before keeps. -/
theorem opCaseOK_delNoLeaf (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hQ : KeptByReads p Q) : OpCaseOK p R Q DelNoLeafM := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ hP
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  exact writerWP_mono (writerWP_del_noLeaf_reads (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key w hI hne
    hno) (fun _ w' hr => hQ ts _ w w' hr)

/-- `l4`'s open case: (4) but (4a), a noop, and a key without a leaf. -/
def DelMergeOpenCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelMergeRestCase c base w op ∧ ¬ DelNoopM c base w op ∧ ¬ DelNoLeafM c base w op

/-- `d4`'s open case: (4) but (4a) for the dead bound, a noop, and a key
without a leaf. -/
def DelMergeDOpenCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelMergeDRestCase c base w op ∧ ¬ DelNoopM c base w op ∧ ¬ DelNoLeafM c base w op

/-- A case that the noops and the keys without a leaf leave open. -/
theorem opCaseOK_of_open (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hQ : KeptByReads p Q)
    (C : Ctx → View BVal → W → Op → Prop)
    (h : OpCaseOK p R Q (fun c base w op => C c base w op ∧ ¬ DelNoopM c base w op ∧
      ¬ DelNoLeafM c base w op)) : OpCaseOK p R Q C :=
  opCaseOK_or p R Q C DelNoopM (fun c base w op => C c base w op ∧ ¬ DelNoopM c base w op)
    (fun c base w op hC => (Classical.em (DelNoopM c base w op)).elim Or.inl
      (fun hn => Or.inr ⟨hC, hn⟩))
    (opCaseOK_delNoop p R Q hQ)
    (opCaseOK_or p R Q _ DelNoLeafM _
      (fun c base w op hC => (Classical.em (DelNoLeafM c base w op)).elim Or.inl
        (fun hn => Or.inr ⟨hC.1, hC.2, hn⟩))
      (opCaseOK_delNoLeaf p R Q hQ) h)

end SIS.Tree
