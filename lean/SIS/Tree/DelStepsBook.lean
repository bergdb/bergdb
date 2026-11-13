/-
The books (`PutBook`) across the upward delete's changing steps (bergdb 024-12,
case (4)'s delete steps): the J of `writerWP_deleteUpward_upT_getJMB`.
-/
import SIS.Tree.DelStepsUp
import SIS.Tree.DelStepsWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem state_takeBackX [WriterStateInvariant] (x p : NodeId) (k : Nat) : KeepsState (takeBack x p k) := by
  intro c w hw
  unfold takeBack
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem writerWP_takeBack_freshCacheX (base x p : NodeId) (k : Nat) (c : Ctx) (w : W)
    (hview : ViewIdsBelow base c.view) (hw : FreshCache base w) (hx : x < w.next) :
    WriterWP (takeBack x p k) c w (fun _ v => FreshCache base v ∧ w.next ≤ v.next) := by
  unfold takeBack
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frTake base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem putBook_note (s : String) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    PutBook c B top0 { w with trail := s :: w.trail } := by
  have h := putBook_of_keeps (note s) c base B top0 hB w hw (klongsWf_note s) (good_note B s)
    (book_note B s) (@state_note (allocatedIdsInvariant B) s)
    (@state_note (commitInvariant top0) s) (freshCache_note s) (ptrs_note _ s)
  simp only [note, writerWP_modify] at h
  exact h

theorem putBook_unlink (x : NodeId) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (unlink x) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_unlink x) (good_unlink B x) (book_unlink B x)
    (@state_unlink (allocatedIdsInvariant B) x) (@state_unlink (commitInvariant top0) x)
    (freshCache_unlink x) (ptrs_unlink _ x)

theorem putBook_emptyKeyNext (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (emptyKeyNext x d) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_emptyKeyNext x d) (good_emptyKeyNext B x d)
    (book_emptyKeyNext B x d) (@state_emptyKeyNext (allocatedIdsInvariant B) x d)
    (@state_emptyKeyNext (commitInvariant top0) x d) (freshCache_emptyKeyNext x d) (ptrs_emptyKeyNext _ x d)

theorem putBook_takeBack (x p : NodeId) (k : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w)
    (hx : ∃ xn, w.nodes.lookup x = some xn) :
    WriterWP (takeBack x p k) c w (fun _ w' => PutBook c B top0 w') := by
  obtain ⟨xn, hl⟩ := hx
  have g1 := klongsWf_takeBack x p k c w hB.wf hw.klongs
  have g2 := good_takeBack B x p k c w hB.good hw.good
  have g3 := book_takeBack B x p k c w w xn hB.good.ids hw.book hl (Kept.refl w)
  have g4 := @state_takeBackX (allocatedIdsInvariant B) x p k c w hw.alloc
  have g5 := @state_takeBackX (commitInvariant top0) x p k c w hw.commit
  have g6 := writerWP_takeBack_freshCacheX B x p k c w hB.good.ids hw.fresh
    (hw.fresh.2.1 (x, xn) (sizeStep_lookup_mem _ x xn hl))
  have g7 := ptrs_takeBack (fun y => y < B) x p k c w (putBase_ptrs c base B hB) hw.ptrs
  intro r w' h
  exact ⟨g1 r w' h, g2 r w' h, (g3 r w' h).1, g4 r w' h, g5 r w' h, (g6 r w' h).1, (g7 r w' h).1⟩

/-- `takeJ2_deleteUpward_upTM` with an invariant J carried to the continuations
(`writerWP_deleteUpward_upT_getJMB`). `takeJ2_deleteUpward_upT` with the merges on, for any post Q: the
continuations (the merges' loop and the root collapse after an inner stop
node's change, `afterDelete` after a segment leaf's) are given `TakeJ2` and
`CollGetInv` at the state they start from, with the facts of
`writerWP_deleteUpward_upT_getJM`. -/
theorem takeJ2_deleteUpward_upTMB (c : Ctx) (base : View BVal)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (rk B : NodeId) (w : W) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hTimesR : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hfit : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = true)
    (hkids : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (Q : W → Prop) (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → WriterWP (unlink x) c v (fun _ v' => J v'))
    (hJadk : ∀ (x : NodeId) (d k : Nat) (v : W), J v →
      WriterWP (appendDeleteKlong x d k) c v (fun _ v' => J v'))
    (hJekn : ∀ (x : NodeId) (d : Nat) (v : W), J v → WriterWP (emptyKeyNext x d) c v (fun _ v' => J v'))
    (hcollM : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      (∃ S, RetFormS c.i B (Nn stop) S ∧
        ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) ∧
        BitmapOf S sn' c.i (K (stop + 1))) →
      TakeJ2 c base B w' → CollGetInv c base w' w' → J w' →
      ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w'')))
    (hleafM : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      (∃ S, RetFormS c.i B (Nn stop) S ∧
        ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) ∧
        BitmapOf S sn' c.i (K (stop + 1))) →
      TakeJ2 c base B w' → CollGetInv c base w' w' → J w' →
      ∀ gs hs : Nat, WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w''))
    (hcollLebM : ∀ (seg stop : Nat) (w' : W) (sn' : KNode) (jcv : Nat) (jy : NodeId), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) → (Nn stop).leaf = false → K (stop + 1) = 0 →
      (jcv, jy) ∈ (Nn stop).liveAt c.i → 0 < jcv →
      (∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' ≠ 0 → jcv ≤ c') →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔
        (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      (∃ S, RetFormS c.i B (Nn stop) S ∧
        ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) ∧
        ∃ htd lip e0, sn' = lebNode S c.i htd lip e0 jcv jy ∧
          (htd = true → (∃ old, S.ks.getLast? = some (.del old)) ∧ S.lastTime = some c.i) ∧
          (lip = true → S.lastTime = some c.i ∧ ∃ ti, S.lastTimeIndex = some ti ∧ ti < e0)) →
      TakeJ2 c base B w' → CollGetInv c base w' w' → J w' →
      ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w''))) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ2
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInv_after_upT c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  -- the facts after the stop node's change, before root collapse
  have hafter : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) → ∃ c'', (c'', z) ∈ sn'.liveAt c.i) →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      TtReachedN (wNode c.p base w') c.i w'.top.rootKey := by
    intro stop w' sn' hsD hbetween ht htop hnodes hsn' hkeep hfate
    have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
      fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
    have hsnw : wNode c.p base w' (X stop) = some sn' := by
      simp only [wNode, ht (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hone' : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
      intro i h1 h2 c' z hm
      have hti := htimes i (by omega)
      have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i hti]; exact hm
      have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
      have hl := hlinkK (i + 1) (by omega) (by omega)
      rw [show i + 1 - 1 = i by omega] at hl
      rw [KNode.liveAt_of_times _ c.i hti] at hl
      have hnd := KNode.live_keys_nodup (Nn i)
      have e1 := lookup_some_of_mem hnd hm'
      have e2 := lookup_some_of_mem hnd hl
      rw [hc] at e1
      rw [e1] at e2
      exact Option.some.inj e2
    rw [htop]
    refine ttReachedN_up (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey X Nn stop depth hsD
      (fun i _ h2 => hN i h2) hone' hkids sn' hsnw hkeep
      (fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc]) hXs (hreach stop (by omega))
      ?_ hTt
    intro k h1 h2 un hun
    rcases hfate k h1 h2 with hf | ⟨S0, hS1, hS2⟩
    · unfold wNode at hun
      rw [hf] at hun
      cases hun
    · have hkt : w'.taken.contains (X k) = false := by
        cases hc : w'.taken.contains (X k) with
        | false => rfl
        | true =>
          unfold wNode at hun
          rw [hc] at hun
          cases hun
      simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS1, Option.some.injEq] at hun
      rw [← hun]
      exact hS2
  -- the stop node keeps its other live klongs, after a bitmap
  have hkeepBit : ∀ (stop : Nat) (sn' : KNode), stop < depth →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) → ∃ c'', (c'', z) ∈ sn'.liveAt c.i := by
    intro stop sn' hsD hlive' c' z hm hz
    refine ⟨c', (hlive' c' z).mpr ⟨hm, fun hck => hz ?_⟩⟩
    have hl := hlinkK (stop + 1) (by omega) (by omega)
    rw [show stop + 1 - 1 = stop by omega] at hl
    rw [hck] at hm
    exact (KNode.liveAt_fun _ _ _ _ _ hl hm).symm
  -- (C) and the node facts after the stop node's change
  have hrestJ : ∀ (stop : Nat) (w' : W) (sn' S : KNode) (Extra : NodeId → Prop), stop < depth →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      RetFormS c.i B (Nn stop) S →
      ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) →
      prefixAt sn'.ks (c.i - 1) = prefixAt S.ks (c.i - 1) →
      (∀ s, S.firstTime = some s → sn'.firstTime = some s) →
      (∀ (i c' : Nat) (y : NodeId), sn'.ks[i]? = some (Klong.key c' y) →
        S.ks[i]? = some (Klong.key c' y) ∨ Extra y) →
      (∀ y, Extra y → (∃ c', (c', y) ∈ sn'.liveAt c.i) ∧ sn'.leaf = false) →
      (∀ c' y, (c', y) ∈ (Nn stop).liveAt c.i → c' ≠ K (stop + 1) → ∃ c'', (c'', y) ∈ sn'.liveAt c.i) →
      (sn'.leaf = true → S.leaf = true ∧ ∀ (i c' : Nat), LastLive S.ks S.lastBitmap i c' →
        c' ≠ K (stop + 1) → LastLive sn'.ks sn'.lastBitmap i c') →
      DeadLiveN (wNode c.p base w') c.i B (w.vals.map (·.1)) ∧ OldBelowN (wNode c.p base w') c.i B ∧
        OldStartN (wNode c.p base w') c.i B ∧ MadeStartN (wNode c.p base w') c.i B ∧
        ValsNoNodeN (wNode c.p base w') (w.vals.map (·.1)) := by
    intro stop w' sn' S Extra hsD ht hnodes hsn' hfJ hSR hSF hspre hsft hskey hsextra hskeep hsleaf
    have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
      fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
    have hsnw : wNode c.p base w' (X stop) = some sn' := by
      simp only [wNode, ht (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hlink : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
      have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
    have hwfs : klongsWf (Nn stop).ks = true := hwf _ _ (hreach stop (by omega)) (hN stop (by omega))
    refine j2rest_up (wNode c.p base w) (wNode c.p base w') c.i B _ X Nn stop depth (K (stop + 1)) hsD
      hpos hD hO hS hM hV (fun i _ h2 => hN i h2) (fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he) ?_
      hwfs (htimes stop (by omega)) hlink S sn' Extra hSR hSF hsnw hspre hsft hskey hsextra hskeep
      hsleaf (fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc])
    intro k h1 h2
    obtain ⟨hm, hu⟩ := hfJ k h1 h2
    refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
    obtain ⟨ht0, S0, hS0, hl0⟩ := hu hf
    exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩
  apply writerWP_deleteUpward_upT_getJMB c base X Nn K depth cv pre rk B w _ J hJ0 hJnote hJtake hJunlink
    hJadk hJekn hMF hdepth hfuel hpos hp hk
    hlk htk htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst hJw'
    have hI := hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)
    have hst0 := hst
    obtain ⟨S, hSR, hSF, hbm⟩ := hst
    have hJ : TakeJ2 c base B w' := by
      unfold TakeJ2
      rw [hv]
      refine ⟨hafter stop w' sn' hsD hbetween ht htop hnodes hsn' (hkeepBit stop sn' hsD hlive') hfate, ?_⟩
      exact hrestJ stop w' sn' S (fun _ => False) hsD ht hnodes hsn' hfJ hSR hSF
        (bitmapOf_prefix S sn' c.i _ hbm hpos) (bitmapOf_firstTime S sn' c.i _ hbm)
        (fun i c' y h => Or.inl (bitmapOf_key S sn' c.i _ hbm i c' y h)) (fun y h => h.elim)
        (fun c' y hm hc => ⟨c', (hlive' c' y).mpr ⟨hm, hc⟩⟩)
        (fun hl => ⟨by rw [← bitmapOf_leaf S sn' c.i _ hbm]; exact hl,
          fun i c' hL hc => bitmapOf_lastLive S sn' c.i _ hbm i c' hL hc⟩)
    exact hcollM seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ
      hst0 hJ hI hJw'
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst hJw'
    have hI := hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)
    have hst0 := hst
    obtain ⟨S, hSR, hSF, hbm⟩ := hst
    refine hleafM stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst0
      ?_ hI hJw'
    unfold TakeJ2
    rw [hv]
    refine ⟨hafter stop w' sn' hsD hbetween ht htop hnodes hsn' (hkeepBit stop sn' hsD hlive') hfate, ?_⟩
    exact hrestJ stop w' sn' S (fun _ => False) hsD ht hnodes hsn' hfJ hSR hSF
      (bitmapOf_prefix S sn' c.i _ hbm hpos) (bitmapOf_firstTime S sn' c.i _ hbm)
      (fun i c' y h => Or.inl (bitmapOf_key S sn' c.i _ hbm i c' y h)) (fun y h => h.elim)
      (fun c' y hm hc => ⟨c', (hlive' c' y).mpr ⟨hm, hc⟩⟩)
      (fun hl => ⟨by rw [← bitmapOf_leaf S sn' c.i _ hbm]; exact hl,
        fun i c' hL hc => bitmapOf_lastLive S sn' c.i _ hbm i c' hL hc⟩)
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hNl hK0 hj hj0 hmin
      hlive' hread hfate hfJ hst hJw'
    have hI := hpost stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv
      hnodes hsn' hsl' hsw' hst' (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩)
    have hkeep : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) →
        ∃ c'', (c'', z) ∈ sn'.liveAt c.i := by
      intro c' z hm hz
      have hl := hlinkK (stop + 1) (by omega) (by omega)
      rw [show stop + 1 - 1 = stop by omega, hK0] at hl
      have hc0 : c' ≠ 0 := fun h => hz (by rw [h] at hm; exact (KNode.liveAt_fun _ _ _ _ _ hl hm).symm)
      by_cases hcj : c' = jcv
      · rw [hcj] at hm
        have hzy : jy = z := KNode.liveAt_fun _ _ _ _ _ hj hm
        exact ⟨0, (hlive' 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
      · exact ⟨c', (hlive' c' z).mpr (Or.inr ⟨hm, hc0, hcj⟩)⟩
    have hst0 := hst
    obtain ⟨S, hSR, hSF, htd, lip, e0, hleb, hhtd, hlip⟩ := hst
    have hSt : ∀ s, Klong.time s ∈ S.ks → s ≤ c.i := by
      rcases hSR with rfl | ⟨_, src, dst, _, rfl⟩
      · exact htimes stop (by omega)
      · exact KNode.retarget_times _ _ _ _ _ (htimes stop (by omega))
    have hlf := lebNode_facts S c.i htd lip e0 jcv jy hpos hSt hhtd hlip
    have hl0 : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
      have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
    have hJ : TakeJ2 c base B w' := by
      unfold TakeJ2
      rw [hv]
      refine ⟨hafter stop w' sn' hsD hbetween ht htop hnodes hsn' hkeep hfate, ?_⟩
      refine hrestJ stop w' sn' S (fun y => y = jy) hsD ht hnodes hsn' hfJ hSR hSF
        (by rw [hleb]; exact hlf.1) (fun s hs => by rw [hleb]; exact hlf.2 s hs)
        (fun i c' y h => by
          rw [hleb] at h
          exact lebNode_key S c.i htd lip e0 jcv jy (fun h => (hhtd h).1) i c' y h)
        (fun y hy => ⟨⟨0, (hlive' 0 y).mpr (Or.inl ⟨rfl, hy⟩)⟩, by rw [hsl', hNl]⟩) ?_
        (fun hl => by rw [hsl', hNl] at hl; cases hl)
      intro c' z hm hc
      rw [hK0] at hc
      by_cases hcj : c' = jcv
      · rw [hcj] at hm
        have hzy : jy = z := KNode.liveAt_fun _ _ _ _ _ hj hm
        exact ⟨0, (hlive' 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
      · exact ⟨c', (hlive' c' z).mpr (Or.inr ⟨hm, hc, hcj⟩)⟩
    exact hcollLebM seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hNl hK0 hj hj0
      hmin hlive' hread hfate hfJ hst0 hJ hI hJw'

end SIS.Tree
