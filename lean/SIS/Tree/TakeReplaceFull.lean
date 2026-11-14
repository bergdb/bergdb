/-
A replaceRoot at a segment root whose segment leaf is full keeps the take-back's
facts (bergdb 024-12, TP7, `ReplaceRootFullJ2OK`): `unlink x`, then the leaf's
cascade (`writerWP_appendKlongs_j2U`, the cascade's take-back with the nodes of
the transaction's time reached in the tree with the klongs put, instead of
`TakeJ2` and kept children before it), with the tree after the unlink from
`CollapseUnlinkOK`.
-/
import SIS.Tree.TakeDelMergeF4
import SIS.Tree.TakeDeadChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `ttReachedN_cascade` with the nodes of time t reached in U directly. -/
theorem ttReachedN_cascadeU (N N' U : NodeId → Option KNode) (t : Time) (r r' : NodeId)
    (nx : NodeId) (Ch : NodeId → Prop)
    (hTU : ∀ u un, N u = some un → Klong.time t ∈ un.ks → TReach U t r u)
    (hkeepR : ∀ z, TReach U t r z → ¬ Ch z → TReach N' t r' z)
    (hch : ∀ z, Ch z → TReach N' t r' z ∨ ∀ zn, N' z = some zn → Klong.time t ∉ zn.ks)
    (hnew : ∀ z zn, nx ≤ z → N' z = some zn → TReach N' t r' z)
    (hold : ∀ z, z < nx → ¬ Ch z → N' z = N z) : TtReachedN N' t r' := by
  intro u un hu hm
  by_cases hc : Ch u
  · rcases hch u hc with h | h
    · exact h
    · exact absurd hm (h un hu)
  · rcases Nat.lt_or_ge u nx with hlt | hge
    · rw [hold u hlt hc] at hu
      exact hkeepR u (hTU u un hu hm) hc
    · exact hnew u un hge hu

/-- `writerWP_appendKlongs_take` with the nodes of the transaction's time reached in
the tree with the klongs put (`hTU`) instead of `TtReachedN` and kept children. -/
theorem writerWP_appendKlongs_takeU (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0) →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      (∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) → 0 < c.i →
      (∀ u un, wNode c.p base w u = some un → Klong.time c.i ∈ un.ks →
        TReach (updN (wNode c.p base w) (X (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey u) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w
        (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV hOrd hpos hTU
  refine writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV) ?_
  rintro _ w' ⟨_, ⟨_, ht', _, _, _⟩, hf, _, _, _, _, hRK, hRN⟩
  obtain ⟨hR2, hR3⟩ := hRN hOrd
  have hR := hRK hOrd
  have hx : wNode c.p base w (X (s + e)) = some (Nn (s + e)) := by
    simp only [wNode, (h4 (s + e) (by omega) (Nat.le_refl _)).2, Bool.false_eq_true, ↓reduceIte,
      (h4 (s + e) (by omega) (Nat.le_refl _)).1]
  apply ttReachedN_cascadeU (wNode c.p base w) (wNode c.p base w') _ c.i w.top.rootKey w'.top.rootKey
    w.next (fun z => ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i) hTU
  · intro z hz hnc
    exact hR z hz (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩)
  · rintro z ⟨i, hi1, hi2, rfl⟩
    rcases hR2 i hi1 hi2 with h | h
    · exact Or.inl h
    · right
      intro zn hzn
      have hw' : wNode c.p base w' (X i) = some ((Nn i).toPrev (c.i - 1)) := by
        simp only [wNode, ht', (h4 i hi1 hi2).2, Bool.false_eq_true, ↓reduceIte, h]
      rw [hw'] at hzn
      cases hzn
      exact time_not_mem_prefixAt (Nn i).ks c.i hpos
  · intro z zn hz hzn
    apply hR3 z hz
    obtain ⟨_, htz, hkz⟩ := h7 z hz
    unfold wNode at hzn
    rw [ht', htz] at hzn
    simp only [Bool.false_eq_true, ↓reduceIte] at hzn
    cases hl : w'.nodes.lookup z with
    | none => rw [hl, hkz] at hzn; cases hzn
    | some _ => rfl
  · intro z hz hnc
    unfold wNode
    rw [ht', hf z hz (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩)]

/-- `writerWP_appendKlongs_j2` with `TakeJ2`'s node facts before and the nodes of the
transaction's time reached in the tree with the klongs put (`hTU`). -/
theorem writerWP_appendKlongs_j2U (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i'))))
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i) (B : NodeId) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → ins.Pairwise (fun a b => a.1 < b.1) → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0) →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      0 < c.i →
      (DeadLiveN (wNode c.p base w) c.i B (w.vals.map (·.1)) ∧ OldBelowN (wNode c.p base w) c.i B ∧
        OldStartN (wNode c.p base w) c.i B ∧ MadeStartN (wNode c.p base w) c.i B ∧
        ValsNoNodeN (wNode c.p base w) (w.vals.map (·.1))) →
      (∀ u un, wNode c.p base w u = some un → Klong.time c.i ∈ un.ks →
        TReach (updN (wNode c.p base w) (X (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey u) →
      B ≤ w.next →
      (∀ y ∈ w.vals.map (·.1), y < w.next) →
      (∀ q ∈ ins, ∀ y, (q.1, y) ∈ (Nn (s + e)).liveAt c.i → y < B ∨ y ∈ w.vals.map (·.1)) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        ∀ i, s ≤ i → i ≤ s + e → (w'.nodes.lookup (X i)).isSome = true) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' => TakeJ2 c base B w') := by
  intro e hle w ins h1 hpw h2 h3 h4 h5 h6 h7 h8 h9 hW hV hpos hJ hTU hBn hvn hins hextra
  have hnd : (ins.map Prod.fst).Nodup := List.pairwise_map.mpr (hpw.imp (fun h => Nat.ne_of_lt h))
  have hTt := writerWP_appendKlongs_takeU c base path0 s D X K Nn hX hK hlinkK hrange hlen hwf htimes htop
    hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV (fun i h1 h2 => hord i h1 (by omega))
    hpos hTU
  have hG := writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV
  have hSh := writerWP_appendKlongs_chainShape c path0 s D X K Nn hX hK hlinkK hrange hlen hord htimes
    htop hdist e hle w ins h1 hpw h3 (fun i a b => ⟨(h4 i a b).1,
      by
        rcases Nat.lt_or_ge (X i) w.next with h | h
        · exact h
        · have := (h7 (X i) h).1; rw [(h4 i a b).1] at this; cases this⟩)
    (fun z hz => (h7 z hz).1)
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hTt hG) hSh) hextra) ?_
  rintro _ w' ⟨⟨⟨hTt', hG'⟩, hSh'⟩, hcached⟩
  obtain ⟨_, ⟨_, ht', _, _, hv'⟩, hf, _⟩ := hG'
  obtain ⟨_, _, _, hshape⟩ := hSh'
  obtain ⟨hD, hO, hS, hM, hV0⟩ := hJ
  have hN : ∀ i, s ≤ i → i ≤ s + e → wNode c.p base w (X i) = some (Nn i) := fun i a b => by
    simp only [wNode, (h4 i a b).2, Bool.false_eq_true, ↓reduceIte, (h4 i a b).1]
  unfold TakeJ2
  rw [hv']
  refine ⟨hTt', ?_⟩
  refine j2rest_cascade2 (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey B _ X Nn s (s + e)
    w.next hpos h5 hD hO hS hM hV0 hN (fun i a b => hwf i a (by omega))
    (fun i a b => htimes i a (by omega)) h6 hvn ?_ ?_
  · intro z hz hnc
    simp only [wNode, ht', hf z hz hnc]
  · intro z zn hzn hz
    have htz : w'.taken.contains z = false := by
      rw [ht']
      rcases hz with hz | ⟨i, a, b, rfl⟩
      · exact (h7 z hz).2.1
      · exact (h4 i a b).2
    have hlk : w'.nodes.lookup z = some zn := by
      unfold wNode at hzn
      rw [htz] at hzn
      simp only [Bool.false_eq_true, ↓reduceIte] at hzn
      cases hl : w'.nodes.lookup z with
      | some m => rw [hl] at hzn; exact hzn
      | none =>
        exfalso
        rw [hl] at hzn
        rcases hz with hz | ⟨i, a, b, rfl⟩
        · rw [(h7 z hz).2.2] at hzn; cases hzn
        · have := hcached i a b
          rw [hl] at this; cases this
    exact cascadeShapeJ2_of c (wNode c.p base w) B _ X K Nn s (s + e) ins w.next hS hM hN
      (fun i a b => htimes i a (by omega)) hBn hnd hins z zn hz (hshape z zn hlk hz)

set_option maxHeartbeats 3200000 in
/-- `ReplaceRootFullJ2OK` holds: a replaceRoot at a segment root x whose segment
leaf is full keeps `TakeJ2` and B at most the next id. After `unlink x` the
writer's tree is a tree (`CollapseUnlinkOK`); the leaf's cascade with its klong
k to x's child keeps the node facts, and every node of the transaction's time is
reached in the tree with the leaf naming the child (`ttReachedN_segCollapse`),
so after the cascade (`writerWP_appendKlongs_j2U`). -/
theorem replaceRootFullJ2OK_holds (c : Ctx) (base : View BVal) (f : Nat) (hf2 : 2 ≤ f) (B : NodeId)
    (hpos : 0 < c.i) (hsa2 : 2 ≤ c.p.splitAbove) : ReplaceRootFullJ2OK c base f B := by
  intro w0 v x n only leaf ln k ps0 hI hR hJ hBn hvp hlf hPC hLr hlkL hlnl hk hpd hpk hlkx honly hcv hxl hnm
    hG hU _
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hLr
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hLr ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hLr hwL
  have hlnwf := hI.2.2.2.1 leaf ln hLr hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hLr ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  -- the key's path down to x
  have hP0 := pathOK_of_linked c base v v (ps0 ++ [(some k, x)]) (ReadsAs.refl _ _ _) hvp hlf hPC
    (fun y hy => hI.1.2.1 y hy)
  have hlen0 : (ps0 ++ [(some k, x)]).length = ps0.length + 1 := by simp
  rw [hlen0] at hP0
  obtain ⟨X, K, Nn, hP⟩ : ∃ X K Nn, PathOK c v (ps0.length + 1) X K Nn := ⟨_, _, _, hP0⟩
  clear hP0
  have hP' := hP
  obtain ⟨hX, hK, hS2v, hlink, h0⟩ := hP'
  generalize hd : ps0.length = d at hpd hpk hP hX hK hS2v hlink ⊢
  have hXd : X d = leaf := by
    have := hX d (by omega); rw [hpd] at this; exact (Option.some.inj this).symm
  have hXx : X (d + 1) = x := by
    have := hX (d + 1) (Nat.le_refl _)
    rw [hpk] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact this.symm
  have hNd : Nn d = ln := by
    have := (hS2v d (by omega)).1; rw [hXd, hlkL] at this; exact (Option.some.inj this).symm
  have hw : ∀ j, j ≤ d + 1 → wNode c.p base v (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2v j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hreach := pathOK_reach c base v (d + 1) X K Nn hP
  have hdist := pathOK_dist c base v (d + 1) X K Nn hP hT
  have hXne : ∀ i, i ≤ d → X i ≠ x := by
    intro i hi he
    rw [← hXx] at he
    have := hdist i (d + 1) (by omega) (Nat.le_refl _) he
    omega
  have hO := ordG_of_rangeOrder c _ _ hR hG.times
  -- the program
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    have hchn : child < v.next := hG.links x n 0 child hwx hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_and (writerWP_unlink_seg x n c base _ (by exact hlkx) (by exact hxt))
      (writerWP_unlink_fate x n c _ (by exact hlkx))) ?_
    rintro _ w1 ⟨⟨h1t, h1top, h1next, h1v, h1path, h1l, mx, h1x, hW1, hmx⟩, ⟨_, _, _, h1xF, _⟩⟩
    have hmxE : mx = (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
      rw [h1x] at h1xF; exact Option.some.inj h1xF
    -- the state after unlink: x's node is mx, the rest as before
    have h1t' : w1.taken = v.taken := h1t
    have h1top' : w1.top = v.top := h1top
    have h1next' : w1.next = v.next := h1next
    have h1v' : w1.vals = v.vals := h1v
    have h1path' : w1.path = v.path := h1path
    have h1l' : ∀ y, y ≠ x → w1.nodes.lookup y = v.nodes.lookup y := h1l
    have hW1' : wNode c.p base w1 = updN (wNode c.p base v) x mx := hW1
    have hxn : x < v.next := hG.ids.1 x (by rw [hlkx]; rfl)
    have hmxwf : klongsWf mx.ks = true := by
      rcases hmx with h | ⟨_, h⟩ <;> rw [h]
      · exact hG.wf x n hwx
      · exact KNode.toPrev_wf _ _ (hG.wf x n hwx)
    have hT1 : TreeOK (wNode c.p base w1) c.i w1.top.rootKey := by
      rw [hW1', h1top']
      rcases hmx with h | ⟨hlt, h⟩
      · rw [h]
        have he : updN (wNode c.p base v) x n = wNode c.p base v := by
          funext z
          by_cases hz : z = x
          · subst hz; rw [updN_self, hwx]
          · rw [updN_ne _ _ _ _ hz]
        rw [he]; exact hT
      · rw [h]; exact (hU hlt).1
    have hS6' : ∀ u c' z, TLink (wNode c.p base w1) c.i u c' z → z < w1.next := by
      intro u c' z hl
      obtain ⟨un, hun, hc⟩ := hl
      rw [h1next']
      rw [hW1'] at hun
      by_cases hux : u = x
      · subst hux
        rw [updN_self] at hun
        cases hun
        rcases hmx with h | ⟨hlt, h⟩
        · rw [h] at hc; exact hG.links _ n c' z hwx hc
        · rw [h] at hc; exact (hU hlt).2 c' z hc
      · rw [updN_ne _ _ _ _ hux] at hun; exact hG.links u un c' z hun hc
    have hW' : ∀ z zn, wNode c.p base w1 z = some zn → klongsWf zn.ks = true := by
      intro z zn hz
      rw [hW1'] at hz
      by_cases hzx : z = x
      · subst hzx; rw [updN_self] at hz; cases hz; exact hmxwf
      · rw [updN_ne _ _ _ _ hzx] at hz; exact hG.wf z zn hz
    have hP1 : PathOK c w1 d X K Nn := by
      refine ⟨fun i hi => by rw [h1path']; exact hX i (by omega),
        fun i h1 h2 => by rw [h1path']; exact hK i h1 (by omega),
        fun i hi => ⟨by rw [h1l' (X i) (hXne i hi)]; exact (hS2v i (by omega)).1,
          by rw [h1t']; exact (hS2v i (by omega)).2⟩,
        fun i h1 h2 => hlink i h1 (by omega), by rw [h1top']; exact h0⟩
    have hreach1 := pathOK_reach c base w1 d X K Nn hP1
    have hS5' : ∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
        knodeOf c.p base z = none := by
      intro z hz
      rw [h1next'] at hz
      have hzx : z ≠ x := by intro h; rw [h] at hz; omega
      refine ⟨?_, ?_, (hG.fresh z hz).1⟩
      · rw [h1l' z hzx]
        cases h : v.nodes.lookup z with
        | none => rfl
        | some _ => have := hG.ids.1 z (by rw [h]; rfl); omega
      · rw [h1t']
        cases h : v.taken.contains z with
        | false => rfl
        | true => have := hG.ids.2.2.1 z h; omega
    -- the virtual state: the room case's, the leaf naming x's child
    have hlk1L : w1.nodes.lookup leaf = some ln := by rw [h1l' leaf hlx]; exact hlkL
    have hLt1 : w1.taken.contains leaf = false := by rw [h1t']; exact hLt
    have hWV : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        updN (wNode c.p base w1) leaf (ln.add c.i (.key k child)) :=
      wNode_upsert_updN c.p base w1 _ leaf _ rfl rfl hLt1
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by rw [hWV, updN_self]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      rw [hWV, updN_ne _ _ _ _ hyl, hW1', updN_ne _ _ _ _ hyx]
    have hVv : wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        wValue base v := wValue_congr' base _ v h1t' h1v'
    have hlinksL : ∀ c' z, (c', z) ∈ (ln.add c.i (.key k child)).liveAt c.i →
        (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
      intro c' z hmm
      rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
    have hVI : CollGetInvF c base w0
        { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } f := by
      refine collGetInv_segStepF f hf2 c base w0 v _ leaf x child k 0 ln
        (ln.add c.i (.key k child)) n hI hLr hwL hk hwx hcl hL' (by rw [KNode.add_leaf]; exact hlnl)
        (KNode.add_key_wf ln c.i k child hlnwf)
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt) hlinksL hoth h1top' h1v'
        (fun z _ => by rw [show ({ w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } : W).taken
          = v.taken from h1t']) ?_
      intro key
      unfold wGetAt
      rw [hVv]
      show getFromR _ (wValue base v) c.i f key w1.top.rootKey = _
      rw [h1top']
      exact getFromR_segCollapse (wNode c.p base v) _ (wValue base v) c.i f v.top.rootKey
        leaf x child k ln (ln.add c.i (.key k child)) n hT hLr hwL hL' hlnl
        (by rw [KNode.add_leaf]; exact hlnl) hlnwf (KNode.add_key_wf ln c.i k child hlnwf) hlnt
        (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt)
        (fun cc => KNode.add_key_live_lookup_of_wf ln c.i k cc child hlnwf) hk hwx hxl hlv hnt ⟨m, hm⟩
        hoth hwfS hI.2.2.1 (by rw [hI.2.2.2.2 child m hchR hm, hI.2.2.2.2 x n hxR hwx]) key
    have hVR : RangeOrder (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
        c.i v.top.rootKey := by
      refine rangeOrder_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf x
        child ln (ln.add c.i (.key k child)) n k hR hT hLr hwL hlnl hk hwx hxl hcl ?_ hL'
        (by rw [KNode.add_leaf]; exact hlnl) ?_ hoth
      · intro c' z hz
        rw [KNode.liveAt_of_times n c.i hnt] at hz
        exact (hlv c' z).mp hz
      · intro c' z hmm
        rcases KNode.add_key_liveAt_mem ln c.i k child hlnwf hlnt c' z hmm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    have hVeq : updN (wNode c.p base w1) (X d) ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn d)) = wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } := by
      rw [hXd, hNd, hWV]; rfl
    -- the leaf's cascade
    have hrangeC : ∀ i, 0 < i → i ≤ d → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
        ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
        K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'' :=
      fun i h1 hi hNR hql' c' z hz hpos =>
        rangeG_of_rangeOrder c _ _ hR hG.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
          (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
          (hw i (by omega)) hNR c' z hz hpos
    have hlenC : ∀ i, 0 ≤ i → i ≤ d → ¬ ChainRoom c (Nn i) →
        c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length :=
      fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
        (hw i (by omega)) hNR hsp
    -- the take-back's facts after the unlink
    have hxB : x < B := lt_of_firstTime_ne _ _ _ hJ.2.2.2.2.1 x n hwx hnm
    have hnwf : klongsWf n.ks = true := hG.wf x n hwx
    have hw1x : wNode c.p base w1 x = some mx := by rw [hW1', updN_self]
    have hw1o : ∀ z, z ≠ x → wNode c.p base w1 z = wNode c.p base v z := fun z hz => by
      rw [hW1', updN_ne _ _ _ _ hz]
    have hw1L : wNode c.p base w1 leaf = some ln := by rw [hw1o leaf hlx]; exact hwL
    obtain ⟨hupre, hufirst⟩ := unlinked_facts n c.i hpos
    have hfacts := j2facts_step (wNode c.p base v) (wNode c.p base w1) c.i B (v.vals.map (·.1)) leaf x ln ln
      hpos hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hwL hw1L rfl rfl
      (fun xn2 h => by
        rw [hw1x] at h
        cases h
        exact ⟨n, hwx, by rw [hmxE]; exact hupre, hxB, fun s hs hf => by rw [hmxE]; exact hufirst s hs hf⟩)
      (fun z _ hzx => hw1o z hzx)
    have hDL1 : DeadLiveN (wNode c.p base w1) c.i B (v.vals.map (·.1)) := by
      intro q qn hq
      by_cases hqx : q = x
      · subst hqx
        rw [hw1x] at hq
        cases hq
        rw [hmxE]
        exact (unlinked_j2 (wNode c.p base v) c.i B _ hpos hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 q n hwx hxB).1
      · rw [hw1o q hqx] at hq
        exact hJ.2.1 q qn hq
    have hTtV : TtReachedN (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
        c.i v.top.rootKey :=
      ttReachedN_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf x child ln (ln.add c.i (.key k child))
        n k hT hLr hwL hk hwx
        (fun c' z hz => by
          rw [KNode.liveAt_of_times n c.i hnt] at hz
          exact ((hlv c' z).mp hz).2)
        hL' (KNode.add_liveAt_new ln k child c.i hlnwf hlnt)
        (fun c' z hz hck => KNode.add_liveAt_keep ln k child c.i hlnwf hlnt c' z hz hck)
        hoth hJ.1 (fun xn2 h => by
          rw [hWV, updN_ne _ _ _ _ (Ne.symm hlx), hw1x] at h
          cases h
          rw [hmxE]
          exact unlinked_no_time n c.i hpos hnwf hnt)
    have hTUc : ∀ u un, wNode c.p base w1 u = some un → Klong.time c.i ∈ un.ks →
        TReach (wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) })
          c.i v.top.rootKey u := by
      intro u un hu hm
      by_cases hul : u = leaf
      · rw [hul, hWV]
        have h1 := hreach1 d (Nat.le_refl _)
        rw [hXd, h1top'] at h1
        rw [h1top'] at hT1
        exact tReach_updN_self _ c.i _ _ _ hT1 h1
      · have hVu : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } u =
            wNode c.p base w1 u := by rw [hWV, updN_ne _ _ _ _ hul]
        exact hTtV u un (by rw [hVu]; exact hu) hm
    have hspaceC : ∀ i, 0 ≤ i → i ≤ d → ¬ ChainRoom c (Nn i) →
        c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (0 < i ∧ ((Nn (i - 1)).leaf = false ∨
          ((Nn i).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < i → ChainOrd c K Nn i'))) := by
      intro i _ hi hNR hsp
      rcases Nat.eq_zero_or_pos i with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 =>
          chainOrd_of_ordG c base v (d + 1) X K Nn hP hO i' h1 (by omega))⟩
    have hS2w1 : ∀ i, 0 ≤ i → i ≤ 0 + d →
        w1.nodes.lookup (X i) = some (Nn i) ∧ w1.taken.contains (X i) = false :=
      fun i _ hi => ⟨by rw [h1l' (X i) (hXne i (by omega))]; exact (hS2v i (by omega)).1,
        by rw [h1t']; exact (hS2v i (by omega)).2⟩
    have hj := writerWP_appendKlongs_j2U c base v.path 0 d X K Nn
      (fun i _ hi => hX i (by omega)) (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega)) hrangeC hlenC
      (fun i _ hi => hG.wf _ _ (hw i (by omega))) (fun i _ hi => hG.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      hspaceC (fun i h1 h2 => chainOrd_of_ordG c base v (d + 1) X K Nn hP hO i h1 (by omega)) B
      d (by omega) w1 [(k, child)] (Or.inl ⟨k, child, rfl⟩) (List.pairwise_singleton _ _)
      (by
        intro q hq
        simp only [List.mem_singleton] at hq
        rw [hq, h1next']; exact hchn)
      h1path' hS2w1 hT1 (fun i _ hi => hreach1 i (by omega)) hS5' hS6'
      (fun _ _ => by rw [h1top']; exact h0.symm) hW'
      (by simp only [Nat.zero_add]; rw [hVeq]; exact hVI.1.1) hpos
      (by rw [h1v']; exact ⟨hDL1, hfacts⟩)
      (by simp only [Nat.zero_add]; rw [hVeq, h1top']; exact hTUc)
      (by rw [h1next']; exact hBn)
      (by
        intro y hy
        rw [h1v'] at hy
        rw [h1next']
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        exact hG.ids.2.2.2 e he)
      (by
        intro q hq y hy
        simp only [List.mem_singleton] at hq
        rw [hq] at hy
        simp only [Nat.zero_add] at hy
        rw [hNd] at hy
        have hyx : y = x := KNode.liveAt_fun _ _ _ _ _ hy hk
        exact Or.inl (by rw [hyx]; exact hxB))
      (by
        refine writerWP_mono (writerWP_appendKlongs_cached _ _ _ c w1) ?_
        intro _ w' h' i _ hi
        exact h' (X i) (by rw [(hS2w1 i (Nat.zero_le _) hi).1]; rfl))
    simp only [Nat.zero_add] at hj
    rw [hXd] at hj
    have hnx := @state_appendKlongs (nextFromInvariant w1) d leaf [(k, child)] c w1 (Nat.le_refl _)
    refine writerWP_mono (writerWP_and hj hnx) ?_
    rintro _ w2 ⟨hJ2, hn2⟩
    exact ⟨hJ2, Nat.le_trans hBn (by rw [← h1next']; exact hn2)⟩

/-- `ReplaceRootFullJ2OK` at every run, for the take-back's top theorems' `hRJ`. -/
theorem replaceRootFullJ2OK_run (p : Params) (hsa2 : 2 ≤ p.splitAbove) :
    ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B := by
  intro ts B
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  exact replaceRootFullJ2OK_holds (ctxOf p ts) _ (p.fuel + 1) hf2 B (by simp [ctxOf])
    (by simpa [ctxOf] using hsa2)

end SIS.Tree
