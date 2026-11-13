/-
The four two-level cascades keep `PutInv` with no premise on the tree after
(bergdb 024-22, `OpTreeOK`; 024-12, TP10): prover putinv's
`putInv_put_timeSplit2`, `_spaceSplitTime`, `_timeSpace`, `_spaceSpace` with
the writer's tree kept (`writerWP_put_timeSplit2_tree` and the others).
-/
import SIS.Tree.PutInvChain
import SIS.Tree.PutInvTimeSpace
import SIS.Tree.PutInvSpaceSpace
import SIS.Tree.WriterTreeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem putInv_put_timeSplit2_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_put_timeSplit2_tree c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk (htk _)
      ⟨hidn, hidv, hidt⟩ hbaseF hwf hpath hNL hnl hNq hNg ⟨hI.times L n hNL, hleaf⟩
      ⟨hI.times q qn hNq, hparent⟩ ⟨hI.times _ gn hNg, hgp⟩ hI.tree hfreshT)
    (putInv_put_timeSplit2 c base B top0 hB pre cv h rk w S0 kq k1 q L n qn gn hI hw hrk hpath hNL
      hnl hNq hNg hleaf hparent hgp)

theorem putInv_put_spaceSplitTime_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧
      c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 (w.next + 2))).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 (w.next + 2 + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_put_spaceSplitTime_tree c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk
      (htk _) ⟨hidn, hidv, hidt⟩ hbaseF hwf hpath hNL hnl hNq hNg ⟨hI.times L n hNL, hleaf⟩
      ⟨hI.times q qn hNq, hparent⟩ ⟨hI.times _ gn hNg, hgp⟩ hI.tree hfreshT)
    (putInv_put_spaceSplitTime c base B top0 hB pre cv h rk w S0 kq k1 q L n qn gn hI hw hrk hpath
      hNL hnl hNq hNg hleaf hparent hgp)

theorem putInv_put_timeSpace_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : c.p.M < qn.size + 1 + 1 ∧ qn.firstTime ≠ some c.i ∧
      c.p.splitAbove < (qn.lastVersion c.i).size ∧ 2 ≤ qn.live.length)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_put_timeSpace_tree c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk (htk _)
      ⟨hidn, hidv, hidt⟩ hbaseF hwf hpath hNL hnl hNq hNg ⟨hI.times L n hNL, hleaf⟩
      ⟨hI.times q qn hNq, hparent⟩ ⟨hI.times _ gn hNg, hgp⟩ hI.tree hfreshT)
    (putInv_put_timeSpace c base B top0 hB pre cv h rk w S0 kq k1 q L n qn gn hI hw hrk hpath hNL
      hnl hNq hNg hleaf hparent hrangeq hgp)

theorem putInv_put_spaceSpace_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧
      c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : c.p.M < qn.size + 2 + 1 ∧ qn.firstTime ≠ some c.i ∧
      c.p.splitAbove < (qn.lastVersion c.i).size ∧ 2 ≤ qn.live.length)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_put_spaceSpace_tree c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk (htk _)
      ⟨hidn, hidv, hidt⟩ hbaseF hwf hpath hNL hnl hNq hNg ⟨hI.times L n hNL, hleaf⟩
      ⟨hI.times q qn hNq, hparent⟩ ⟨hI.times _ gn hNg, hgp⟩ hI.tree hfreshT)
    (putInv_put_spaceSpace c base B top0 hB pre cv h rk w S0 kq k1 q L n qn gn hI hw hrk hpath hNL
      hnl hNq hNg hleaf hparent hrangeq hgp)

end SIS.Tree
