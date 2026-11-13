/-
Case (4)'s delete steps, a leaf that empties (the upward delete), the merges
on (bergdb 024-12, TP7 and TP10): when the leaf is not the space root and the
stop node has room for its bitmap or LE-b (`DelEmptyRoomM`), `DelInvF` where
`afterDelete` and the merges' loop start (`delInvF_of_collGetInv`) and the
reading of the delete (`delStepsCaseOKF_emptyRoom`).
-/
import SIS.Tree.DelStepsUpWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A bound above every node the transaction's nodes replaced. -/
def madeForBound (w : W) : NodeId := w.madeFor.foldr (fun q m => max q.2 m) 0 + 1

theorem madeFor_lt_bound (w : W) : ∀ x o, w.madeFor.lookup x = some o → o < madeForBound w := by
  intro x o h
  have hmem : (x, o) ∈ w.madeFor := by
    obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
    rw [he]; simp
  have hle : ∀ (l : List (NodeId × NodeId)) (q : NodeId × NodeId), q ∈ l →
      q.2 ≤ l.foldr (fun q m => max q.2 m) 0 := by
    intro l
    induction l with
    | nil => intro q hq; cases hq
    | cons a l ih =>
      intro q hq
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih q hq) (Nat.le_max_right _ _)
  have := hle w.madeFor (x, o) hmem
  unfold madeForBound
  omega

/-- Room at the stop node of an upward delete along the path X, Nn, K to depth:
the stop node's bitmap (a segment leaf, or an inner node's klong to a chain
node other than the empty key's) or its LE-b fits without a cascade. -/
def StopRoomP (c : Ctx) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) : Prop :=
  ∀ s, s < depth → (∀ i, s < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
      deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
        (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
      deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
        false) ∧
    ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
      ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false)

/-- The upward delete from the leaf L (node n) of w's tree has room: L is not
the space root, and its stop node has room, along the path to L. -/
def UpRoom (c : Ctx) (base : View BVal) (w : W) (L : NodeId) (n : KNode) : Prop :=
  ∀ P, LinkedFrom (wNode c.p base w) c.i w.top.rootKey P → nodeAt w.top.rootKey P P.length = L →
    0 < P.length ∧ StopRoomP c (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length

/-- A delete, the merges on, that empties its leaf, with room for the upward
delete. -/
def DelEmptyRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n

/-- A delete, the merges on, that empties its leaf, without room for the upward
delete: the leaf is the space root, or its stop node cascades. -/
def DelEmptyOtherM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ ¬ UpRoom c base w L n

theorem delEmptyM_split (c : Ctx) (base : View BVal) (w : W) (op : Op) (h : DelEmptyM c base w op) :
    DelEmptyRoomM c base w op ∨ DelEmptyOtherM c base w op := by
  obtain ⟨pre, cv, L, n, hop, hm, hK, hne, hall⟩ := h
  by_cases hr : UpRoom c base w L n
  · exact Or.inl ⟨pre, cv, L, n, hop, hm, hK, hne, hall, hr⟩
  · exact Or.inr ⟨pre, cv, L, n, hop, hm, hK, hne, hall, hr⟩

theorem delStepsCaseOKF_or (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseOKF p R P1) (h2 : DelStepsCaseOKF p R P2) : DelStepsCaseOKF p R P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hA hMU hCR

/-- The upward delete with room, the merges on, keeps `DelInvF` up to the
merges' loop and `afterDelete`, which the caller's obligations take over: from
w with `PutInv`, the walk's ranges, the fuel premise, inner children and the
books, a delete whose leaf empties ends in any Post that `DelInvF` gives and
`fresh` keeps. -/
theorem writerWP_del_emptyRoomM (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hA : ∀ g h v, DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v'))
    (hMU : ∀ g h merged v, DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v'))
    (hCR : ∀ seg v, DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafM c base hvc pre cv rk w (PutBook c B top0) hbook
    (fun s f x v hv => putBook_descendLte s f x c base B top0 hB v hv)
    (fun s x v hv => putBook_pathAdd s x c base B top0 hB v hv)
    (fun v hv => putBook_pathClear c base B top0 hB v hv) hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hb3 hlk3 hp3' hlinkP hXD hlkX
  obtain ⟨hne, hall, hup⟩ := hleafC L n hL hn hnl
  obtain ⟨hdepth, hstopOK⟩ := hup P hlinkP hXD
  -- the path, at w
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hI.tree _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  -- the facts at w3
  have hN3 : ∀ i, i ≤ P.length → wNode c.p base w3 (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have htk3 : ∀ i, i ≤ P.length → w3.taken.contains (nodeAt w.top.rootKey P i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreachX i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hI.tree
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hRt3 : ∀ y, TReach (wNode c.p base w3) c.i w3.top.rootKey y → w3.taken.contains y = false := by
    intro y hy
    rw [hr03.1, hr03.2.1] at hy
    rw [hr03.2.2.1]
    exact hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hTimesR3 : ∀ y yn, TReach (wNode c.p base w3) c.i w3.top.rootKey y → wNode c.p base w3 y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i := fun y yn _ h => by rw [hr03.1] at h; exact hI.times y yn h
  have hICE3 : InnerChildrenExist (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hICE
  have hfit3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
  have hnovalAll3 : ∀ y yn, wNode c.p base w3 y = some yn → wValue base w3 y = none := by
    intro y yn h
    rw [hr03.1] at h
    rw [ReadsAs.value _ _ _ _ hr03]
    exact hI.keyNoValue y yn h
  have hreach3 : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w3) c.i w3.top.rootKey (nodeAt w.top.rootKey P i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreachX i hi
  have hlinkK : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i :=
    fun i h1 h2 => (hKP i h1 h2).2
  have hNnD : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n = n := by rw [hXD, hn]; rfl
  -- DelInvF at a continuation of the upward delete
  have hD : ∀ (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      w'.top = w3.top → w'.vals = w3.vals →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      sn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf →
      klongsWf sn'.ks = true → (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i →
        ∃ c0, (c0, z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).liveAt c.i ∧
          c0 ≠ ((P[stop + 1 - 1]?).bind (·.1)).getD 0 ∧ f c0 = c') →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      PutBook c B top0 w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key') →
      DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hread
    have hCG := collGetInv_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    exact delInvF_of_collGetInv c base B top0 hB w w3 w' (pre ++ [cv]) hI hF hr03 hCG hRO' hb' hread
  -- the frame facts at a continuation
  have hXs : ∀ stop, stop < P.length → ∀ k, stop < k → k ≤ P.length →
      nodeAt w.top.rootKey P stop ≠ nodeAt w.top.rootKey P k :=
    fun stop _ k h1 h2 he => by have := hdistP _ _ (by omega) h2 he; omega
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      (∀ u, u ≠ nodeAt w.top.rootKey P stop → (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w3 u) ∧
      wNode c.p base w' (nodeAt w.top.rootKey P stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht _ (hXs stop hsD), htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  rw [← hXD]
  refine writerWP_deleteUpward_upT_getJMB c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk (madeForBound w3) w3 Post
    (PutBook c B top0) hb3 (fun s v hv => putBook_note s c base B top0 hB v hv)
    (fun x q k v hv hx => putBook_takeBack x q k c base B top0 hB v hv hx)
    (fun x v hv => putBook_unlink x c base B top0 hB v hv)
    (fun x d k v hv => putBook_appendDeleteKlong x d k c base B top0 hB v hv)
    (fun x d v hv => putBook_emptyKeyNext x d c base B top0 hB v hv)
    (madeFor_lt_bound w3) hdepth hfuel hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hreach3
    hlinkK (fun i hi => hnovalAll3 _ _ (hN3 i hi)) (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hstopOK hm ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb' hread
    refine writerWP_mono (hMU gs hs false w' hDv) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb' hread
    exact writerWP_mono (hA gs hs w' hDv) (fun _ w2 hD2 => hpost w2 hD2)
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_leb (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    have hDv := hD stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩) hRO' hb' hread
    refine writerWP_mono (hMU gs hs false w' hDv) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)

/-- What holds of the key's leaf and its node holds of every leaf of the descent. -/
theorem keyLeaf_all2 {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {cv : Nat}
    {L : NodeId} {n : KNode} {rk : NodeId} (hK : KeyLeaf c base w pre cv L n)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (P : NodeId → KNode → Prop) (hP : P L n) :
    ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L' = some n' → n'.leaf = true → P L' n' := by
  obtain ⟨rk', hrk', hL, hn, hnl⟩ := hK
  rw [hrk] at hrk'
  cases hrk'
  intro L' n' hL' hn' hnl'
  have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
  subst he
  rw [hn] at hn'
  cases hn'
  exact hP

/-- The reading of a delete whose leaf empties, the upward delete with room. -/
theorem delStepsCaseOKF_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    DelStepsCaseOKF p R DelEmptyRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  refine writerWP_del_emptyRoomM (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm (by simp [ctxOf]) hA hMU hCR _
    (fun v hv => by unfold fresh; wpSimplify; exact hv) ?_
  intro v hv hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

/-! ## The two obligations with the open cases named -/

/-- `DelStepsOKF` with every case proved but the upward delete without room
(`DelEmptyOtherM`: the leaf is the space root, or the stop node cascades) and
the full leaf (`DelFullM`). -/
theorem delStepsOKF_of_open2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (c7 : DelStepsCaseOKF p R DelEmptyOtherM) (c9 : DelStepsCaseOKF p R DelFullM) : DelStepsOKF p R :=
  delStepsOKF_of_open p R hM hRL hP
    (delStepsCaseOKF_or p R _ _ _ delEmptyM_split (delStepsCaseOKF_emptyRoom p R hM hRL hP) c7) c9

end SIS.Tree
