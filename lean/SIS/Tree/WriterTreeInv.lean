/-
The writer's tree under prover putinv's `PutInv` (bergdb 024-22, `OpTreeOK`;
024-12, TP10). `OpTreeInvOK`: each operation from a state that meets `PutInv`
keeps the writer's tree; it follows from `OpTreeOK` and is enough, with
`OpPutInvOK`, for `PutInv` at every state a prefix reaches
(`putInv_reached_inv`). The rules for which both are proved keep `PutInv`
with no premise on the tree after (`putInv_*_full`).
-/
import SIS.Tree.PutInvRun
import SIS.Tree.WriterTreeDelFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Each operation of a transaction within reach, after a run whose structure
meets R, from a state that its earlier operations reach and that meets
`PutInv`, keeps the writer's tree. -/
def OpTreeInvOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

theorem opTreeInvOK_of_opTreeOK (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOK p) :
    OpTreeInvOK p R := by
  intro ts tx hw _ z top hz htop pre op post hsplit r w hpre hI
  exact ho ts tx hw z top hz htop pre op post hsplit r w hpre hI.tree

/-- `PutInv` at every state that a prefix of a transaction's operations
reaches, from `OpTreeInvOK` and `OpPutInvOK` (as `putInv_reached`, with the
tree kept only from states that meet `PutInv`). -/
theorem putInv_reached_inv (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (ho : OpTreeInvOK p R) (hP : OpPutInvOK p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact putInv_init p ts tx hw (hR _ _ hr) hT hI z top hz htop
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 := ho ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 a w2 h2
          have := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 a w2 h2 hT2
          rw [← h.2]
          exact this

/-- The writer's tree at every state that a prefix reaches, from
`OpTreeInvOK` and `OpPutInvOK`. -/
theorem writerTreeOK_reached_inv (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (ho : OpTreeInvOK p R) (hP : OpPutInvOK p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (pre post : List Op) (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  (putInv_reached_inv p R hR ho hP ts tx hw hr hT hI z top hz htop pre post hsplit r w hpre).tree

/-! ## Rules that keep `PutInv` with no premise on the tree after -/

theorem writerWP_and_imp {α : Type} (m : M α) (c : Ctx) (w : W) (P Q : W → Prop)
    (h1 : WriterWP m c w (fun _ w' => P w')) (h2 : WriterWP m c w (fun _ w' => P w' → Q w')) :
    WriterWP m c w (fun _ w' => Q w') :=
  writerWP_mono (writerWP_and h1 h2) (fun _ _ h => h.2 h.1)

theorem putInv_put_leafBelow_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => PutInv c base w') :=
  writerWP_and_imp _ c w _ _
    (writerWP_put_leafBelow_tree c base hB.coherent pre cv h rk w hI hsa hrk hinner hparent)
    (putInv_put_leafBelow c base B top0 hB pre cv h rk w hI hw hsa hrk hinner hparent)

theorem putInv_put_leafRoot_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => PutInv c base w') :=
  writerWP_and_imp _ c w _ _
    (writerWP_put_leafRoot_tree c base hB.coherent cv h w n hI hsa hroot hnl)
    (putInv_put_leafRoot c base B top0 hB cv h w n hI hw hsa hroot hnl)

theorem putInv_put_segLeaf_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' => PutInv c base w') :=
  writerWP_and_imp _ c w _ _
    (writerWP_put_segLeaf_tree c base hB.coherent pre0 k1 cv h rq L n w hI hsa hrq hL hNL hnl hseg)
    (putInv_put_segLeaf c base B top0 hB pre0 k1 cv h rq L n w hI hw hsa hrq hL hNL hnl hseg)

theorem putInv_put_newSeg_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' => PutInv c base w') :=
  writerWP_and_imp _ c w _ _
    (writerWP_put_newSeg_inv_tree c base hB.coherent pre c0 cl h rk0 w hI hM hrk hcur)
    (putInv_put_newSeg c base B top0 hB pre c0 cl h rk0 w hI hw hM hrk hcur)

theorem putInv_del_noop_seg_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨_, _, _, _, htk⟩ := PutInv.facts c base w hI
  exact writerWP_and_imp _ c w _ _
    (writerWP_del_noop_seg_tree c base hB.coherent pre cv rk w hrk (htk _) hleaf hI.tree)
    (putInv_del_noop_seg c base B top0 hB pre cv rk w hI hw hrk hleaf)

theorem putInv_del_bitmap_seg_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      deadOver c.p (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false ∧
      deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false ∧
      (lastIsDel n.ks = false ∨ n.lastTime ≠ some c.i → n.size + 1 < c.p.M)) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨_, _, _, _, htk⟩ := PutInv.facts c base w hI
  exact writerWP_and_imp _ c w _ _
    (writerWP_del_bitmap_seg_tree c base hB.coherent pre cv rk w hmerges hrk (htk _)
      (fun L n hL hn hnl => ⟨hI.times L n hn, hleaf L n hL hn hnl⟩) hI.tree)
    (putInv_del_bitmap_seg c base B top0 hB pre cv rk w hI hw hmerges hrk hleaf)

theorem putInv_del_leafBelow_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_del_leafBelow_tree c base hB.coherent pre cv rk w hmerges hrk (htk _)
      ⟨hidn, hidv, hidt⟩ hbaseF hwf (fun x xn _ hn => hI.times x xn hn) hinner hleaf hparent hI.tree
      hfreshT)
    (putInv_del_leafBelow c base B top0 hB pre cv rk w hI hw hmerges hrk hinner hleaf hparent)

end SIS.Tree
