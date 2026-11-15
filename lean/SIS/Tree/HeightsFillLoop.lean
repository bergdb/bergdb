/-
`hchk`'s upward loop `checkFree` proved (bergdb 024-12): with the take-back's node
facts at the delete's start (`TakeJ2`), a holder of a node of the transaction is
reached and is its tree parent (putinv2's `liveHolder_unique`), so before the loop
takes back chain node X k, after its parent is pointed to the old node, no kept node
holds X k (`holderFree_loop`). The loop keeps an invariant on the holders of the
chain's nodes (`HoldInv`: the nodes off the chain from k down as at the loop's
start, the chain's nodes below k naming old nodes only, X k's node the start's,
perhaps retargeted; `step_takeBack`, `step_unlink`). So `putKvDelChk5`, the checked
copy without the stop-node checks, `checkOld3` and the loop's `checkFree`, runs as
`putKvDelChk2` from every state with `PutInv`, the fill, the made-for ids, the
take-back's node facts and the cache's books (`rwp_putKvDelChk5`), and
`OpDelChk5OKR` gives `OpDelChk2ORJ` (`opDelChk2ORJ_of_chk5`). Left in `hchk`: the
merge's `checkFree` and root collapse's `checkRoot`. The top theorem with it is
`invGetScanOK_merges_joint5`, on the joint route, which has `TakeJ2` at every
delete's start (`jointHtJ_reachedJ`). `checkRoot` passes at every state with
`PutInv`, `TakeJ2` and the path to the node it takes back (`checkRoot_ok_of_J2`);
not yet used: the states of root collapse inside a delete have `TakeJ2` by
putinv's `DelInvJ`, but `DelInvJ` at the delete's calls of `afterDelete` is not
stated.
-/
import SIS.Tree.HeightsFillTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The state after `retarget p src dst` from w, with p's node pn cached. -/
def retState (c : Ctx) (w : W) (p : NodeId) (pn : KNode) (src dst : NodeId) : W :=
  if pn.lastTime == some c.i then
    { w with nodes := upsert w.nodes p { pn with ks := retargetKlongs pn.ks (pn.lastTimeIndex.getD 0) src dst } }
  else w

theorem writerWP_retarget_known (p src dst : NodeId) (c : Ctx) (w : W) (pn : KNode)
    (hp : w.nodes.lookup p = some pn) :
    WriterWP (retarget p src dst) c w (fun _ v => v = retState c w p pn src dst) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hp]
  unfold retState
  split
  · rename_i h
    simp only [putNode, writerWP_modify]
    unfold retargetKlongs
    rfl
  · rename_i h
    simp only [writerWP_pure]

/-- A key klong of a retargeted node naming src lies before the last time klong. -/
theorem retargetKlongs_src_mem (ks : List Klong) (ti : Nat) (src dst : NodeId) (hsd : dst ≠ src)
    (cv : Nat) (hk : Klong.key cv src ∈ retargetKlongs ks ti src dst) :
    ∃ i, ks[i]? = some (Klong.key cv src) ∧ i ≤ ti := by
  unfold retargetKlongs at hk
  obtain ⟨⟨k, i⟩, hm, he⟩ := List.mem_map.mp hk
  have hi : ks[i]? = some k := List.mk_mem_zipIdx_iff_getElem?.mp hm
  cases k with
  | key cv' y =>
    simp only at he
    by_cases hc : ti < i ∧ y = src
    · simp [hc] at he
      first | exact (hsd he.2).elim | exact (hsd he.2.symm).elim
    · have : (ti < i && y == src) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
        by_cases h1 : ti < i
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      rw [this] at he
      simp only [Bool.false_eq_true, ↓reduceIte, Klong.key.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨i, hi, ?_⟩
      by_cases h1 : ti < i
      · exact absurd ⟨h1, rfl⟩ hc
      · omega
  | time s => simp at he
  | del b => simp at he

set_option maxHeartbeats 1600000 in
/-- The upward loop's check before taking back X k, after its parent X (k - 1)
is retargeted: no kept node holds X k, by the take-back's node facts at the
delete's start (a holder of a node of the transaction is reached and is its tree
parent, `liveHolder_unique`) and the loop's writes so far (`hU`: the nodes not on
the chain below k as at the start; `hM`: the chain's nodes below kept only with
old klongs; `hMk`: X k names no X k). -/
theorem holderFree_loop (c : Ctx) (base : View BVal) (w0 w3 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hr03 : ReadsAs c.p base w0 w3)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth k : Nat) (hk0 : 0 < k) (hk2 : k ≤ depth)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hlk3 : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (v : W) (hcg : CacheGood B c v) (htop : v.top = w3.top)
    (htk : ∀ y, w3.taken.contains y = true → v.taken.contains y = true)
    (hU : ∀ y, (∀ j, k ≤ j → j ≤ depth → y ≠ X j) → v.nodes.lookup y = w3.nodes.lookup y)
    (hM : ∀ j, k < j → j ≤ depth → v.taken.contains (X j) = false → ∀ n, v.nodes.lookup (X j) = some n →
      ∀ cv z, Klong.key cv z ∈ n.ks → z < B)
    (hMk : ∀ n, v.nodes.lookup (X k) = some n → ∀ cv z, Klong.key cv z ∈ n.ks → B ≤ z → z ≠ X k)
    (hBx : B ≤ X k) (old : NodeId) (hold : old < B)
    (pn : KNode) (hpn : v.nodes.lookup (X (k - 1)) = some pn) (hlt : pn.lastTime = some c.i)
    (hnd1 : ((retState c v (X (k - 1)) pn (X k) old).nodes.map Prod.fst).Nodup)
    (hcg1 : CacheGood B c (retState c v (X (k - 1)) pn (X k) old)) :
    holderFree c (retState c v (X (k - 1)) pn (X k) old) (X k) = true := by
  have hpos := hvg.pos
  obtain ⟨hTt, _, hOB, _, _, _⟩ := hJ2
  have hTi : TimesN (wNode c.p base w0) c.i := fun q qn hq s hs => hI0.times q qn hq s hs
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w0) c.i w0.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by simpa using hlinkK (i + 1) (by omega) hi⟩
  have hpnN : pn = Nn (k - 1) := by
    have h := hU (X (k - 1)) (fun j h1 h2 he => by have := hdist (k - 1) j (by omega) h2 he; omega)
    rw [hpn, hlk3 (k - 1) (by omega)] at h
    cases h; rfl
  have hv1 : retState c v (X (k - 1)) pn (X k) old =
      { v with nodes := (upsert v.nodes (X (k - 1))
        ({ pn with ks := retargetKlongs pn.ks (pn.lastTimeIndex.getD 0) (X k) old } : KNode)) } := by
    unfold retState; simp [hlt]
  rw [hv1] at hnd1 hcg1 ⊢
  unfold holderFree
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨q, n⟩ hq
    simp only
    by_cases htq : v.taken.contains q = true
    · exact Or.inl htq
    right
    have hlq := lookup_of_mem_nodup _ hnd1 q n hq
    have hgq : Good B c q n := hcg1.2 (q, n) hq
    -- the version before the transaction names old nodes only
    have hprev : ∀ e ∈ (n.toPrev (c.i - 1)).live, ¬ e.2 = X k := by
      rintro ⟨cv, z⟩ he hz
      simp only at hz
      subst hz
      obtain ⟨c0, hk⟩ := live_key_mem _ cv (X k) he
      have := ptr_lt_of_prefix B c hvg q n hgq c0 (X k) hk
      omega
    refine ⟨?_, hprev⟩
    rintro ⟨cv, z⟩ he hz
    simp only at hz
    subst hz
    obtain ⟨c0, hkm⟩ := live_key_mem _ cv (X k) he
    by_cases hqp : q = X (k - 1)
    · subst hqp
      rw [lookup_upsert] at hlq
      simp only [↓reduceIte, Option.some.injEq] at hlq
      subst hlq
      have hsd : old ≠ X k := by omega
      obtain ⟨i, hi, hile⟩ := retargetKlongs_src_mem pn.ks _ (X k) old hsd c0 hkm
      obtain ⟨m, hm1, hm2⟩ := KNode.lastTime_anchor pn c.i hlt
      rw [hm1] at hile
      simp only [Option.getD_some] at hile
      have him : i ≠ m := by intro h; rw [h, hm2] at hi; cases hi
      have hwf : klongsWf pn.ks = true := by
        rw [hpnN]; exact hI0.wf _ _ (hXN (k - 1) (by omega))
      have htm : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i := by
        rw [hpnN]; exact hI0.times _ _ (hXN (k - 1) (by omega))
      have hpre := mem_prefixAt_before_time pn.ks c.i hpos hwf htm m hm2 i (by omega) _ hi
      have hgp : Good B c (X (k - 1)) pn := cacheGood_lookup B c v hcg _ _ hpn
      have := ptr_lt_of_prefix B c hvg _ pn hgp c0 (X k) hpre
      omega
    · rw [lookup_upsert] at hlq
      simp only [hqp, ↓reduceIte] at hlq
      by_cases hqc : ∃ j, k ≤ j ∧ j ≤ depth ∧ q = X j
      · obtain ⟨j, hj1, hj2, rfl⟩ := hqc
        rcases Nat.lt_or_ge k j with hkj | hkj
        · have := hM j hkj hj2 (by simpa using htq) n hlq c0 (X k) hkm
          omega
        · have hjk : j = k := by omega
          subst hjk
          exact hMk n hlq c0 (X j) hkm hBx rfl
      · have hnc : ∀ j, k ≤ j → j ≤ depth → q ≠ X j := fun j h1 h2 he => hqc ⟨j, h1, h2, he⟩
        have h3 : w3.nodes.lookup q = some n := by rw [← hU q hnc]; exact hlq
        have ht3 : w3.taken.contains q = false := by
          cases h : w3.taken.contains q with
          | false => rfl
          | true => exact absurd (htk q h) htq
        have hw3 : wNode c.p base w3 q = some n := by
          unfold wNode; rw [ht3]; simp [h3]
        have hw0 : wNode c.p base w0 q = some n := by rw [← hr03.1]; exact hw3
        have hlive : (cv, X k) ∈ n.liveAt c.i := by
          rw [KNode.liveAt_of_times n c.i (hI0.times q n hw0)]; exact he
        have hreach := (hPL (k - 1) (by omega)).reach
        have hl : TLink (wNode c.p base w0) c.i (X (k - 1)) (K k) (X k) :=
          ⟨Nn (k - 1), hXN (k - 1) (by omega), by simpa using hlinkK k hk0 hk2⟩
        have := (liveHolder_unique _ c.i w0.top.rootKey B hpos hTt hOB hTi hI0.tree (X k) hBx (X (k - 1)) (K k)
          hreach hl q n hw0 cv hlive).1
        exact hqp this
  · intro he
    have h0 : v.top.rootKey = X 0 := by rw [htop, hr03.2.1, hX0]
    rw [h0] at he
    have := hdist 0 k (by omega) hk2 he
    omega
  · cases hvx : c.view (X k) with
    | none => rfl
    | some nd => have := hvg.ids _ nd hvx; omega

/-- The state after `unlink x` from w, with x's node n cached. -/
def unlState (c : Ctx) (w : W) (x : NodeId) (n : KNode) : W :=
  if n.lastTime == some c.i then { w with nodes := upsert w.nodes x (n.toPrev (c.i - 1)) } else w

theorem writerWP_unlink_known (x : NodeId) (c : Ctx) (w : W) (n : KNode)
    (hx : w.nodes.lookup x = some n) :
    WriterWP (unlink x) c w (fun _ v => v = unlState c w x n) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hx]
  unfold unlState
  split
  · simp only [putNode, writerWP_modify]
  · simp only [writerWP_pure]

theorem checkFree_ok (o : NodeId) (c : Ctx) (w : W) (h : holderFree c w o = true) :
    checkFree o c w = .ok ((), w) := by
  unfold checkFree
  rw [m_bind_ok]
  refine ⟨c, w, rfl, ?_⟩
  rw [m_bind_ok]
  refine ⟨w, w, rfl, ?_⟩
  simp only [h, ↓reduceIte]
  rfl

theorem rwp_checkFree {β : Type} (o : NodeId) (c : Ctx) (w : W) (k : Unit → M β)
    (h : holderFree c w o = true) : RWP (k ()) (checkFree o >>= k) c w :=
  fun y hy => (m_bind_ok _ k c w y).mpr ⟨(), w, checkFree_ok o c w h, hy⟩

/-- A key klong of a retargeted node: one of the node's, or naming dst. -/
theorem retargetKlongs_key_mem (ks : List Klong) (ti : Nat) (src dst : NodeId) (cv : Nat) (z : NodeId)
    (hk : Klong.key cv z ∈ retargetKlongs ks ti src dst) : Klong.key cv z ∈ ks ∨ z = dst := by
  unfold retargetKlongs at hk
  obtain ⟨⟨k, i⟩, hm, he⟩ := List.mem_map.mp hk
  have hk' : k ∈ ks := List.fst_mem_of_mem_zipIdx hm
  cases k with
  | key cv' y =>
    simp only at he
    split at he
    · simp only [Klong.key.injEq] at he; exact Or.inr he.2.symm
    · rw [← he]; exact Or.inl hk'
  | time s => simp at he
  | del b => simp at he


theorem rwp_trans_checkOld {β : Type} (pn : KNode) (old : NodeId) (c : Ctx) (w : W) {f : M β}
    {k : Unit → M β} (hl : pn.leaf = true) (hv : (c.view old).isSome = true) (h : RWP f (k ()) c w) :
    RWP f (checkOld pn old >>= k) c w :=
  fun y hy => rwp_checkOld pn old c w k hl hv y (h y hy)

/-! ## The loop's invariant: the holders of the chain's nodes -/

/-- The state of the upward loop before it takes chain node X k: the frame of
`LeafFrM`, the books it needs, the nodes not on the chain from k down as at the
loop's start, the chain's nodes below k (unlinked) naming old nodes only, and X k's
node the start's, perhaps retargeted to an old node. -/
def HoldInv (c : Ctx) (w3 : W) (B : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (depth k : Nat)
    (v : W) : Prop :=
  LeafFrM w3 v ∧ CacheGood B c v ∧ (v.nodes.map Prod.fst).Nodup ∧ v.top = w3.top ∧
  (∀ y, w3.taken.contains y = true → v.taken.contains y = true) ∧
  (∀ y, (∀ j, k ≤ j → j ≤ depth → y ≠ X j) → v.nodes.lookup y = w3.nodes.lookup y) ∧
  (∀ j, k < j → j ≤ depth → v.taken.contains (X j) = false → ∀ n, v.nodes.lookup (X j) = some n →
    ∀ cv z, Klong.key cv z ∈ n.ks → z < B) ∧
  (∃ n, v.nodes.lookup (X k) = some n ∧
    (n = Nn k ∨ ∃ ti src dst, dst < B ∧ n = { Nn k with ks := retargetKlongs (Nn k).ks ti src dst }))

theorem leafFrM_retState (c : Ctx) (v : W) (p : NodeId) (pn : KNode) (src dst : NodeId)
    (hp : v.nodes.lookup p = some pn) : LeafFrM v (retState c v p pn src dst) := by
  unfold retState
  split
  · refine ⟨⟨rfl, fun y n hy => ?_⟩, rfl⟩
    simp only [lookup_upsert]
    by_cases hyp : y = p
    · subst hyp; rw [hp] at hy; cases hy; simp
    · simp [hyp, hy]
  · exact LeafFrM.refl v

/-- A chain node's klong to a node of the transaction is not to itself. -/
theorem chain_no_self (c : Ctx) (base : View BVal) (w0 : W) (B : NodeId) (hI0 : PutInv c base w0)
    (hJ2 : TakeJ2 c base B w0)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (k : Nat) (hk : k ≤ depth) (n : KNode)
    (hn : n = Nn k ∨ ∃ ti src dst, dst < B ∧ n = { Nn k with ks := retargetKlongs (Nn k).ks ti src dst })
    (cv : Nat) (z : NodeId) (hkz : Klong.key cv z ∈ n.ks) (hBz : B ≤ z) : z ≠ X k := by
  intro hz
  subst hz
  have hkm : Klong.key cv (X k) ∈ (Nn k).ks := by
    rcases hn with rfl | ⟨ti, src, dst, hdst, rfl⟩
    · exact hkz
    · rcases retargetKlongs_key_mem _ ti src dst cv (X k) hkz with h | h
      · exact h
      · omega
  obtain ⟨_, hDL, _, _, _, hVN⟩ := hJ2
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hkm
  have hnv : X k ∉ w0.vals.map (·.1) := by
    intro hv
    have := hVN _ hv
    rw [hXN k hk] at this
    cases this
  obtain ⟨⟨c', hc'⟩, _⟩ := hDL (X k) (Nn k) (hXN k hk) i cv (X k) hi hBz hnv
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w0) c.i w0.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by simpa using hlinkK (i + 1) (by omega) hi⟩
  have h1 := hPL k hk
  have h2 : PathLen (wNode c.p base w0) c.i w0.top.rootKey (X k) (k + 1) :=
    PathLen.link h1 ⟨Nn k, hXN k hk, hc'⟩
  have := PathLen.depth_unique hI0.tree _ _ _ h1 h2
  omega

/-- `takeBackChk4` without `checkFree`. -/
def takeBackChk5 (x parent : NodeId) (cv : Nat) : M Unit := do
  let c ← read
  let pn ← getNode parent
  match (← replacedBy x), pn.linkIndex x cv with
  | some old, some _ =>
    if pn.lastTime != some c.i then
      throw s!"Bug: take back of key node {x} at {c.i}: no klong of tt to it"
    retarget parent x old
    takenBack x
    note "up.takeback"
  | _, _ => throw s!"Bug: take back of key node {x} at {c.i}: no node it replaces, or no klong to it"

set_option maxHeartbeats 3200000 in
/-- The take-back of chain node X k in the upward loop, from a state with the
loop's invariant: the copy without the checks runs as the checked one (the
parent a segment leaf, the made-for id a node of the view, no kept holder,
`holderFree_loop`), and the invariant holds for k - 1 after it. -/
theorem step_takeBack (c : Ctx) (base : View BVal) (w0 w3 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hr03 : ReadsAs c.p base w0 w3)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth k : Nat) (hk0 : 0 < k) (hk2 : k ≤ depth)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hlk3 : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hpar : (Nn (k - 1)).leaf = true)
    (hmf : ∀ x o, w3.madeFor.lookup x = some o → (c.view o).isSome = true)
    (v : W) (hH : HoldInv c w3 B X Nn depth k v) (xn : KNode) (hxn : v.nodes.lookup (X k) = some xn)
    (hft : xn.firstTime = some c.i) :
    RWP (takeBackChk5 (X k) (X (k - 1)) (K k)) (takeBackChk (X k) (X (k - 1)) (K k)) c v ∧
    WriterWP (takeBackChk5 (X k) (X (k - 1)) (K k)) c v (fun _ v' => HoldInv c w3 B X Nn depth (k - 1) v') := by
  obtain ⟨hLF, hcg, hnd, htop, htk, hU, hM, hMk⟩ := hH
  have hpos := hvg.pos
  have hpn : v.nodes.lookup (X (k - 1)) = some (Nn (k - 1)) := by
    rw [hU (X (k - 1)) (fun j h1 h2 he => by have := hdist (k - 1) j (by omega) h2 he; omega)]
    exact hlk3 (k - 1) (by omega)
  have hBx : B ≤ X k := Blank.ge B c (X k) hvg
    (blank_of_firstTime B c (X k) xn hpos (cacheGood_lookup B c v hcg (X k) xn hxn) (by simp [hft]))
  have hmfv : ∀ o, v.madeFor.lookup (X k) = some o → (c.view o).isSome = true :=
    fun o ho => hmf (X k) o (by rw [← hLF.2]; exact ho)
  obtain ⟨nk, hnk, hnkF⟩ := hMk
  have hMk' : ∀ n, v.nodes.lookup (X k) = some n → ∀ cv z, Klong.key cv z ∈ n.ks → B ≤ z → z ≠ X k := by
    intro n hn cv z hkz hBz
    rw [hnk] at hn; cases hn
    exact chain_no_self c base w0 B hI0 hJ2 X Nn K depth hX0 hXN hlinkK k hk2 nk hnkF cv z hkz hBz
  refine ⟨?_, ?_⟩
  · unfold takeBackChk5 takeBackChk
    refine rwp_read ?_
    refine rwp_getNode_known (X (k - 1)) (Nn (k - 1)) hpn ?_
    refine rwp_bind (fun r v' => v' = v ∧ ∀ o, r = some o → (c.view o).isSome = true)
      (by unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure]; exact ⟨trivial, hmfv⟩) ?_
    rintro r v' ⟨hv', hr⟩
    subst v'
    rcases r with _ | old
    · exact rwp_refl _ _ _
    · cases hli : (Nn (k - 1)).linkIndex (X k) (K k) with
      | none => exact rwp_refl _ _ _
      | some j =>
        simp only []
        by_cases hlt : ((Nn (k - 1)).lastTime != some c.i) = true
        · simp only [hlt, ↓reduceIte]; exact rwp_refl _ _ _
        · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
          have hlt' : (Nn (k - 1)).lastTime = some c.i := by simpa using hlt
          have hvo := hr old rfl
          have hold : old < B := by
            cases hvx : c.view old with
            | none => rw [hvx] at hvo; cases hvo
            | some nd => exact hvg.ids old nd hvx
          refine rwp_trans_checkOld (Nn (k - 1)) old c v hpar hvo ?_
          refine rwp_bind (fun _ v1 => v1 = retState c v (X (k - 1)) (Nn (k - 1)) (X k) old ∧ CacheGood B c v1)
            (writerWP_and (writerWP_retarget_known _ _ _ c v _ hpn) (good_retarget B _ _ _ c v hvg hcg)) ?_
          rintro _ v1 ⟨hv1, hcg1⟩
          subst hv1
          have hnd1 : ((retState c v (X (k - 1)) (Nn (k - 1)) (X k) old).nodes.map Prod.fst).Nodup := by
            unfold retState; split
            · exact upsert_unique _ _ _ hnd
            · exact hnd
          exact rwp_checkFree (X k) c _ (fun _ => do
              takenBack (X k)
              note "up.takeback")
            (holderFree_loop c base w0 w3 B hvg hI0 hJ2 hr03 X Nn K depth k hk0 hk2
              hX0 hXN hlinkK hdist hlk3 v hcg htop htk hU hM hMk' hBx old hold (Nn (k - 1)) hpn hlt' hnd1 hcg1)
  · unfold takeBackChk5 replacedBy
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known (X (k - 1)) (Nn (k - 1)) c v hpn]
    simp only [writerWP_get, writerWP_pure]
    cases hro : v.madeFor.lookup (X k) with
    | none => exact writerWP_throw _ _ _ _
    | some old =>
      cases hli : (Nn (k - 1)).linkIndex (X k) (K k) with
      | none => exact writerWP_throw _ _ _ _
      | some j =>
        simp only []
        by_cases hlt : ((Nn (k - 1)).lastTime != some c.i) = true
        · simp only [hlt, ↓reduceIte]; exact writerWP_throw _ _ _ _
        simp only [hlt, Bool.false_eq_true, ↓reduceIte]
        have hlt' : (Nn (k - 1)).lastTime = some c.i := by simpa using hlt
        have hvo := hmfv old hro
        have hold : old < B := by
          cases hvx : c.view old with
          | none => rw [hvx] at hvo; cases hvo
          | some nd => exact hvg.ids old nd hvx
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_and (writerWP_retarget_known _ _ _ c v _ hpn)
          (good_retarget B _ _ _ c v hvg hcg)) ?_
        rintro _ v1 ⟨hv1, hcg1⟩
        subst hv1
        simp only [takenBack, note, writerWP_modify]
        have hv1e : retState c v (X (k - 1)) (Nn (k - 1)) (X k) old =
            { v with nodes := (upsert v.nodes (X (k - 1)) ({ Nn (k - 1) with
              ks := (retargetKlongs (Nn (k - 1)).ks ((Nn (k - 1)).lastTimeIndex.getD 0) (X k) old) } : KNode)) } := by
          unfold retState; simp [hlt']
        rw [hv1e] at hcg1 ⊢
        refine ⟨?_, hcg1, upsert_unique _ _ _ hnd, htop, fun y hy => ?_, fun y hy => ?_, fun j hj1 hj2 htj n hn => ?_, ?_⟩
        · have h1 := leafFrM_retState c v (X (k - 1)) (Nn (k - 1)) (X k) old hpn
          rw [hv1e] at h1
          exact hLF.trans (h1.trans ⟨⟨rfl, fun y n hy => ⟨n, hy, rfl⟩⟩, rfl⟩)
        · simp only [List.contains_cons, Bool.or_eq_true]; exact Or.inr (htk y hy)
        · simp only [lookup_upsert]
          have hne : y ≠ X (k - 1) := fun he => hy (k - 1) (by omega) (by omega) he
          simp only [hne, ↓reduceIte]
          exact hU y (fun j h1 h2 => hy j (by omega) h2)
        · simp only [lookup_upsert] at hn
          have hne : X j ≠ X (k - 1) := fun he => by have := hdist j (k - 1) hj2 (by omega) he; omega
          simp only [hne, ↓reduceIte] at hn
          rcases Nat.lt_or_ge k j with hkj | hkj
          · have htj' : v.taken.contains (X j) = false := by
              simp only [List.contains_cons] at htj
              cases h : v.taken.contains (X j) with
              | false => rfl
              | true => rw [h] at htj; simp at htj
            exact hM j hkj hj2 htj' n hn
          · have hjk : j = k := by omega
            subst hjk
            simp at htj
        · refine ⟨_, ?_, Or.inr ⟨(Nn (k - 1)).lastTimeIndex.getD 0, X k, old, hold, rfl⟩⟩
          simp [lookup_upsert]

set_option maxHeartbeats 1600000 in
/-- The unlink of chain node X k in the upward loop (a node not of the
transaction) keeps the loop's invariant for k - 1. -/
theorem step_unlink (c : Ctx) (base : View BVal) (w0 w3 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0)
    (X : Nat → NodeId) (Nn : Nat → KNode) (depth k : Nat) (hk0 : 0 < k) (hk2 : k ≤ depth)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hlk3 : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (v : W) (hH : HoldInv c w3 B X Nn depth k v) :
    WriterWP (do note "up.unlink"; unlink (X k)) c v (fun _ v' => HoldInv c w3 B X Nn depth (k - 1) v') := by
  obtain ⟨hLF, hcg, hnd, htop, htk, hU, hM, ⟨nk, hnk, hnkF⟩⟩ := hH
  have hpos := hvg.pos
  simp only [writerWP_bind, note, writerWP_modify]
  have hcgu : CacheGood B c { v with trail := "up.unlink" :: v.trail } := hcg
  have hnku : ({ v with trail := "up.unlink" :: v.trail } : W).nodes.lookup (X k) = some nk := hnk
  refine writerWP_mono (writerWP_and (writerWP_unlink_known (X k) c _ nk hnku) (good_unlink B (X k) c _ hvg hcgu)) ?_
  rintro _ v' ⟨hv', hcg'⟩
  subst hv'
  have hwf : klongsWf nk.ks = true := by
    rcases hnkF with rfl | ⟨ti, src, dst, _, rfl⟩
    · exact hI0.wf _ _ (hXN k hk2)
    · simp only [klongsWf_retargetKlongs]; exact hI0.wf _ _ (hXN k hk2)
  have hgk : Good B c (X k) nk := cacheGood_lookup B c v hcg (X k) nk hnk
  have hkeys : ∀ cv z, Klong.key cv z ∈
      (((unlState c { v with trail := "up.unlink" :: v.trail } (X k) nk).nodes.lookup (X k)).getD nk).ks →
      z < B := by
    intro cv z hk
    unfold unlState at hk
    split at hk
    · simp only [lookup_upsert, ↓reduceIte, Option.getD_some] at hk
      exact ptr_lt_of_prefix B c hvg (X k) nk hgk cv z hk
    · rename_i hlt
      simp only [hnku, Option.getD_some] at hk
      exact ptr_lt_of_good_old B c hvg (X k) nk hgk hwf (by simpa using hlt) cv z hk
  have hlkU : ∀ y, y ≠ X k → (unlState c { v with trail := "up.unlink" :: v.trail } (X k) nk).nodes.lookup y =
      v.nodes.lookup y := by
    intro y hy
    unfold unlState
    split
    · simp only [lookup_upsert, hy, ↓reduceIte]
    · rfl
  refine ⟨?_, hcg', ?_, ?_, ?_, fun y hy => ?_, fun j hj1 hj2 htj n hn => ?_, ?_⟩
  · refine hLF.trans ⟨⟨?_, fun y n hy => ?_⟩, ?_⟩
    · unfold unlState; split <;> rfl
    · by_cases hyk : y = X k
      · subst hyk
        rw [hnk] at hy; cases hy
        unfold unlState; split
        · simp [lookup_upsert, KNode.toPrev]
        · exact ⟨nk, hnku, rfl⟩
      · rw [hlkU y hyk]; exact ⟨n, hy, rfl⟩
    · unfold unlState; split <;> rfl
  · unfold unlState; split
    · exact upsert_unique _ _ _ hnd
    · exact hnd
  · unfold unlState; split <;> exact htop
  · intro y hy
    have : (unlState c { v with trail := "up.unlink" :: v.trail } (X k) nk).taken = v.taken := by
      unfold unlState; split <;> rfl
    rw [this]; exact htk y hy
  · have hyk : y ≠ X k := fun he => hy k (by omega) hk2 he
    rw [hlkU y hyk]
    exact hU y (fun j h1 h2 => hy j (by omega) h2)
  · have htv : (unlState c { v with trail := "up.unlink" :: v.trail } (X k) nk).taken = v.taken := by
      unfold unlState; split <;> rfl
    rw [htv] at htj
    rcases Nat.lt_or_ge k j with hkj | hkj
    · have hjk : X j ≠ X k := fun he => by have := hdist j k hj2 hk2 he; omega
      rw [hlkU (X j) hjk] at hn
      exact hM j hkj hj2 htj n hn
    · have hjk : j = k := by omega
      subst hjk
      intro cv z hk
      apply hkeys cv z
      rw [hn]; exact hk
  · have hne : X (k - 1) ≠ X k := fun he => by have := hdist (k - 1) k (by omega) hk2 he; omega
    refine ⟨Nn (k - 1), ?_, Or.inl rfl⟩
    rw [hlkU _ hne, hU (X (k - 1)) (fun j h1 h2 he => by have := hdist (k - 1) j (by omega) h2 he; omega)]
    exact hlk3 (k - 1) (by omega)

/-- A fold whose every step leaves the state as it is. -/
theorem writerWP_foldlM_same {α β : Type} (c : Ctx) (l : List α) (f : β → α → M β) (w : W)
    (hf : ∀ b, ∀ a ∈ l, WriterWP (f b a) c w (fun _ v => v = w)) :
    ∀ init, WriterWP (l.foldlM f init) c w (fun _ v => v = w) := by
  induction l with
  | nil => intro init; simp only [List.foldlM_nil, writerWP_pure]
  | cons a l ih =>
    intro init
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a List.mem_cons_self) ?_
    intro b v hv
    subst hv
    exact ih (fun b a ha => hf b a (List.mem_cons_of_mem _ ha)) b

/-- A loop over `List.range' s n` whose step j refines and takes I j to I (j + 1). -/
theorem rwp_forIn_range' (c : Ctx) (f g : Nat → PUnit → M (ForInStep PUnit)) (I : Nat → W → Prop) :
    ∀ n s, (∀ j, s ≤ j → j < s + n → ∀ v, I j v → RWP (f j PUnit.unit) (g j PUnit.unit) c v ∧
      WriterWP (f j PUnit.unit) c v (fun r v' => r = ForInStep.yield PUnit.unit ∧ I (j + 1) v')) →
    ∀ v, I s v → RWP (forIn (List.range' s n) PUnit.unit f) (forIn (List.range' s n) PUnit.unit g) c v ∧
      WriterWP (forIn (List.range' s n) PUnit.unit f) c v (fun _ v' => I (s + n) v') := by
  intro n
  induction n with
  | zero =>
    intro s _ v hv
    simp only [List.range'_zero, List.forIn_nil]
    exact ⟨rwp_refl _ _ _, by simp only [writerWP_pure]; exact hv⟩
  | succ n ih =>
    intro s hstep v hv
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons]
    obtain ⟨h1, h2⟩ := hstep s (Nat.le_refl _) (by omega) v hv
    have hih := fun v' (hv' : I (s + 1) v') =>
      ih (s + 1) (fun j hj1 hj2 => hstep j (by omega) (by omega)) v' hv'
    refine ⟨rwp_bind2 _ h1 h2 ?_, ?_⟩
    · rintro r v' ⟨hr, hv'⟩
      subst hr
      exact (hih v' hv').1
    · rw [writerWP_bind]
      refine writerWP_mono h2 ?_
      rintro r v' ⟨hr, hv'⟩
      subst hr
      have := (hih v' hv').2
      rw [show s + (n + 1) = s + 1 + n by omega]
      exact this

theorem rwp_forIn_range'_bind {β : Type} (c : Ctx) (f g : Nat → PUnit → M (ForInStep PUnit))
    (k1 k2 : PUnit → M β) (I : Nat → W → Prop) (n s : Nat)
    (hstep : ∀ j, s ≤ j → j < s + n → ∀ v, I j v → RWP (f j PUnit.unit) (g j PUnit.unit) c v ∧
      WriterWP (f j PUnit.unit) c v (fun r v' => r = ForInStep.yield PUnit.unit ∧ I (j + 1) v'))
    (v : W) (hv : I s v) (hk : ∀ v', I (s + n) v' → RWP (k1 PUnit.unit) (k2 PUnit.unit) c v') :
    RWP (forIn (List.range' s n) PUnit.unit f >>= k1) (forIn (List.range' s n) PUnit.unit g >>= k2) c v :=
  have h := rwp_forIn_range' c f g I n s hstep v hv
  rwp_bind2 (fun _ v => I (s + n) v) h.1 h.2 (fun a v' hv' => by cases a; exact hk v' hv')

/-- The nodes of a path from the root of the writer's tree are distinct. -/
theorem chain_dist (c : Ctx) (base : View BVal) (w0 : W) (hI0 : PutInv c base w0)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) :
    ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w0) c.i w0.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by simpa using hlinkK (i + 1) (by omega) hi⟩
  intro i i' hi hi' he
  have h1 := hPL i hi
  have h2 := hPL i' hi'
  rw [he] at h1
  exact PathLen.depth_unique hI0.tree _ _ _ h1 h2

/-- `deleteUpwardChk4` with `takeBackChk5`: no `checkFree` in the loop. -/
def deleteUpwardChk5 (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    afterDeleteChk key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBackChk5 x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if sn.leaf then
    note "up.stop-at-segment-leaf"
    let _ ← appendDeleteKlong s stop cs
    afterDeleteChk key gs hs
    return false
  if sn.smallestLive != some 0 then
    throw s!"Bug: the upward unlink at {tt}: inner node {s} has no live klong of the empty key"
  if cs != 0 then
    let _ ← appendDeleteKlong s stop cs
  else
    emptyKeyNext s stop
  if c.p.merges then
    let _ ← mergeUp key gs c.p.fuel hs false
  collapseRoot key segment (c.p.fuel)
  return false

set_option maxHeartbeats 3200000 in
/-- The upward delete without the loop's `checkFree` runs as `deleteUpwardChk2`
when the fill, `PutInv` and the take-back's node facts hold at the delete's
start: the loop's invariant `HoldInv` gives each take-back's check
(`step_takeBack`, `step_unlink`). -/
theorem rwp_deleteUpwardChk5 (c : Ctx) (base : View BVal) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (w3 : W) (hr03 : ReadsAs c.p base w0 w3) (hcg3 : CacheGood B c w3)
    (hnd3 : (w3.nodes.map Prod.fst).Nodup)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hmf : ∀ x o, w3.madeFor.lookup x = some o → (c.view o).isSome = true)
    (cv : Nat) (key : Key) :
    RWP (deleteUpwardChk5 (X depth) depth cv key) (deleteUpwardChk2 (X depth) depth cv key) c w3 := by
  have htimes := hI0.times
  have hdist := chain_dist c base w0 hI0 X Nn K depth hX0 hXN hlinkK
  unfold deleteUpwardChk5 deleteUpwardChk2
  refine rwp_read ?_
  refine rwp_getNode_known (X depth) (Nn depth) (hlkX depth (Nat.le_refl _)) ?_
  dsimp only
  by_cases h1 : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = true
  · simp only [h1, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!(Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv))) = true
  · simp only [h2, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  have hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true := by
    simpa using h2
  refine rwp_bind _ (writerWP_climb c X Nn K depth w3 hpX hpK hlkX) ?_
  rintro stop v ⟨hv, hsle, hbetween, -, -, -⟩
  subst v
  by_cases h3 : (stop == depth) = true
  · simp only [h3, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by
    have : stop ≠ depth := fun he => h3 (by simp [he])
    omega
  -- the fill: below the stop node, every node of the path is the parent of an emptied node
  have hleafAt : ∀ k, stop < k → k ≤ depth → (Nn (k - 1)).leaf = true := by
    intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases hl : (Nn j).leaf with
    | true => rfl
    | false =>
      exfalso
      rcases Nat.lt_or_ge (j + 1) depth with hlt | hge
      · exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K depth hX0
          hXN hlinkK j hk2 hl (K (j + 1 + 1)) (htimes _ _ (hXN (j + 1) hk2))
          (hbetween (j + 1) hk1 hlt)
      · have he : j + 1 = depth := by omega
        subst he
        exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K (j + 1) hX0
          hXN hlinkK j (Nat.le_refl _) hl cv (htimes _ _ (hXN (j + 1) (Nat.le_refl _))) hall
  -- note, the path, the segment's fold: the state kept but the trail
  refine rwp_bind (fun _ v => v = { w3 with trail := "up.climb" :: w3.trail })
    (by simp only [note, writerWP_modify]) ?_
  rintro _ v1 hv1
  subst hv1
  refine rwp_bind (fun a v => a = { w3 with trail := "up.climb" :: w3.trail } ∧
      v = { w3 with trail := "up.climb" :: w3.trail })
    ((writerWP_get c _ _).mpr ⟨rfl, rfl⟩) ?_
  rintro a v2 ⟨ha, hv2⟩
  subst ha; subst hv2
  refine rwp_bind (fun _ v => v = { w3 with trail := "up.climb" :: w3.trail })
    (writerWP_foldlM_same c _ _ _ ?_ 0) ?_
  · intro b e he
    simp only [writerWP_bind]
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hi
    split at hi
    · rename_i hil
      have hx := hpX i (by omega)
      have hi' : w3.path[i]? = some e := hi
      rw [hi'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      rw [writerWP_getNode_known e.2 (Nn i) c _ (by rw [hx]; exact hlkX i (by omega))]
      simp only [writerWP_pure]
    · cases hi
  intro seg v3 hv3
  subst hv3
  rw [List.range_eq_range']
  refine rwp_forIn_range'_bind c _ _ _ _ (fun j v => HoldInv c w3 B X Nn depth (depth - j) v)
    (depth - stop) 0 ?_ _ ?_ ?_
  · -- a step of the loop
    intro j _ hj v hH
    have hk1 : stop < depth - j := by omega
    have hk2 : depth - j ≤ depth := by omega
    have hk0 : 0 < depth - j := by omega
    have hpar : (Nn (depth - j - 1)).leaf = true := hleafAt (depth - j) hk1 hk2
    obtain ⟨n', hn', -⟩ := hH.2.2.2.2.2.2.2
    have hpx : (v.path[depth - j]?).map (·.2) = some (X (depth - j)) := by rw [hH.1.1.1]; exact hpX _ hk2
    have hpx1 : (v.path[depth - j - 1]?).map (·.2) = some (X (depth - j - 1)) := by
      rw [hH.1.1.1]; exact hpX _ (by omega)
    have hpk : v.path[depth - j]? = some (some (K (depth - j)), X (depth - j)) := by
      rw [hH.1.1.1]; exact hpK _ (by omega) hk2
    have hidx : depth - (j + 1) = depth - j - 1 := by omega
    refine ⟨?_, ?_⟩
    · refine rwp_bind (fun x v' => x = X (depth - j) ∧ v' = v)
        (writerWP_pathNode_known _ _ c v hpx _ ⟨rfl, rfl⟩) ?_
      rintro x v' ⟨hx, hv'⟩
      subst hx; subst v'
      refine rwp_getNode_known _ n' hn' ?_
      by_cases hf : (n'.firstTime == some c.i) = true
      · simp only [hf, ↓reduceIte]
        refine rwp_bind (fun y v' => y = X (depth - j - 1) ∧ v' = v)
          (writerWP_pathNode_known _ _ c v hpx1 _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        refine rwp_bind (fun y v' => y = K (depth - j) ∧ v' = v)
          (writerWP_klongAt_known _ _ _ c v hpk _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        have hst := step_takeBack c base w0 w3 B hvg hI0 hJ2 hr03 X Nn K depth (depth - j) hk0 hk2 hX0 hXN
          hlinkK hdist hlkX hpar hmf v hH n' hn' (by simpa using hf)
        exact rwp_bind2 (fun _ _ => True) hst.1 (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact rwp_refl _ _ _
    · simp only [writerWP_bind]
      refine writerWP_pathNode_known _ _ c v hpx _ ?_
      refine (writerWP_getNode_known _ n' c v hn' _).mpr ?_
      split
      · rename_i hf
        simp only [writerWP_bind]
        refine writerWP_pathNode_known _ _ c v hpx1 _ ?_
        refine writerWP_klongAt_known _ _ _ c v hpk _ ?_
        have hst := step_takeBack c base w0 w3 B hvg hI0 hJ2 hr03 X Nn K depth (depth - j) hk0 hk2 hX0 hXN
          hlinkK hdist hlkX hpar hmf v hH n' hn' (by simpa using hf)
        refine writerWP_mono hst.2 ?_
        intro _ u hu
        simp only [writerWP_pure]
        refine ⟨by first | trivial | rfl, ?_⟩
        rw [hidx]; exact hu
      · have hsu := step_unlink c base w0 w3 B hvg hI0 X Nn depth (depth - j) hk0 hk2 hXN hdist hlkX v hH
        simp only [writerWP_bind] at hsu ⊢
        refine writerWP_mono hsu ?_
        intro _ u hu
        refine writerWP_mono hu ?_
        intro _ u' hu'
        simp only [writerWP_pure]
        refine ⟨by first | trivial | rfl, ?_⟩
        rw [hidx]; exact hu'
  · -- the loop's start
    show HoldInv c w3 B X Nn depth (depth - 0) _
    rw [Nat.sub_zero]
    refine ⟨⟨⟨rfl, fun y n hy => ⟨n, hy, rfl⟩⟩, rfl⟩, hcg3, hnd3, rfl, fun y hy => hy, fun y _ => rfl,
      fun j h1 h2 => absurd h2 (by omega), Nn depth, hlkX depth (Nat.le_refl _), Or.inl rfl⟩
  · -- the stop node
    intro v4 hH4
    have hv4 : LeafFrM w3 v4 := hH4.1
    have hps : (v4.path[stop]?).map (·.2) = some (X stop) := by rw [hv4.1.1]; exact hpX _ (by omega)
    have hpk : v4.path[stop + 1]? = some (some (K (stop + 1)), X (stop + 1)) := by
      rw [hv4.1.1]; exact hpK _ (by omega) (by omega)
    obtain ⟨sn, hsn, hsl⟩ := hv4.1.2 _ _ (hlkX stop (by omega))
    have hsleaf : sn.leaf = true := by
      rw [hsl]; have := hleafAt (stop + 1) (by omega) (by omega); simpa using this
    refine rwp_bind (fun x v' => x = X stop ∧ v' = v4)
      (writerWP_pathNode_known _ _ c v4 hps _ ⟨rfl, rfl⟩) ?_
    rintro x v' ⟨hx, hv'⟩
    subst hx; subst v'
    refine rwp_bind (fun y v' => y = K (stop + 1) ∧ v' = v4)
      (writerWP_klongAt_known _ _ _ c v4 hpk _ ⟨rfl, rfl⟩) ?_
    rintro y v' ⟨hy, hv'⟩
    subst hy; subst v'
    refine rwp_getNode_known _ sn hsn ?_
    refine rwp_bind_any (fun gh v5 => ?_)
    simp only [hsleaf, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact rwp_refl _ _ _


/-- `setValueDelChk4` with `deleteUpwardChk5`. -/
def setValueDelChk5 (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk5 leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk4` with `setValueDelChk5`. -/
def putSegsDelChk5 (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk5 segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk5 key rest next

/-- The delete's checked copy with the merge's and the root collapse's holder
checks only. -/
def putKvDelChk5 (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk5 key key root

set_option maxHeartbeats 1600000 in
/-- The last segment's descent and the upward delete, for the two copies: the
path from w0's root as the upward delete's refinement asks, the cache's books kept. -/
theorem rwp_setValueDelChk5 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (r : NodeId) (cv : Nat) (key : Key) (w : W) (hS : SegInv c base w0 w r) (hmw : w.madeFor = w0.madeFor)
    (hcg : CacheGood B c w) (hu : UniqueCache B w)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false) :
    RWP (setValueDelChk5 r cv key) (setValueDelChk2 r cv key) c w := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  unfold setValueDelChk5 setValueDelChk2
  refine rwp_read ?_
  refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_madeFor cv c c.p.fuel r w))
    (good_descendLte B cv c.p.fuel r c w hvg hcg))
    (uniqueCache_descendLte (base := B) cv c.p.fuel r c w hvg.ids hu)) ?_
  rintro L w3 ⟨⟨⟨⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, -⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩, hm3⟩, hcg3⟩,
    hu3, -⟩
  have hr03 : ReadsAs c.p base w0 w3 := ReadsAs.trans c.p base w0 w w3 hr0 hr3
  rw [hr0.1] at hn hvisL hpf hcache3
  refine rwp_bind _ (kd_pathSize c w3) ?_
  rintro sz v ⟨hv, hsz⟩
  subst hsz; subst v
  refine rwp_bind2 (fun _ _ => True) ?_ (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
  -- the path from w0's root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w0.top.rootKey) :: P := by rw [hp3, hp, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hl (by rw [he]; exact LinkedFrom.of_pathFrom _ _ cv r steps hpf)
  have hXD : nodeAt w0.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, he, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps hpf
    (fun mm hmm => by rw [← hLe, hn] at hmm; cases hmm; exact hnl) (by rw [← hLe]; exact hvisL)
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w0 (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hmem : nodeAt w0.top.rootKey P i ∈ (w0.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hc _ hmem _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w0.top.rootKey P i = nodeAt r steps j := by
        rw [hP, hj, nodeAt_append_right, he]
      have hvj : (nodeAt r steps j, cv) ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps r steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w0.top.rootKey P i) ∈
        ((wNode c.p base w0 (nodeAt w0.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w0.top.rootKey P i) := by
    intro i hi
    have hl' : i < (w0.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl']
    simp [nodeAt, List.getElem?_eq_getElem hl']
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hlen : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen, ← hXD]
  exact rwp_deleteUpwardChk5 c base w0 B hvg hI0 hJ2 hLC hm (fun i => nodeAt w0.top.rootKey P i)
    (fun i => (wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) w3 hr03 hcg3 hu3.2 hpX hpK hlkX
    (fun x o ho => hmf0 x o (by rw [← hmw, ← hm3]; exact ho)) cv key

/-- The delete's segments, for the two copies. -/
theorem rwp_putSegsDelChk5 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId) (w : W), SegInv c base w0 w r → w.madeFor = w0.madeFor →
      CacheGood B c w → UniqueCache B w →
      (∀ q ∈ fromVisits (wNode c.p base w0) c.i c.p.fuel segs r, w0.taken.contains q.1 = false) →
      RWP (putSegsDelChk5 key segs r) (putSegsDelChk2 key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro r w _ _ _ _ _; unfold putSegsDelChk5 putSegsDelChk2; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro r w hS hmw hcg hu ht
    cases rest with
    | nil =>
      unfold putSegsDelChk5 putSegsDelChk2
      exact rwp_setValueDelChk5 c base hvc w0 B hvg hI0 hJ2 hLC hm hmf0 r cv key w hS hmw hcg hu
        (fun q hq => ht q (by simpa [fromVisits] using hq))
    | cons d rest' =>
      unfold putSegsDelChk5 putSegsDelChk2
      have ht0 : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false :=
        fun q hq => ht q (by simp only [fromVisits]; exact List.mem_append_left _ hq)
      refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and
        (writerWP_setNode_seg c base hvc w0 cv r w hS ht0 hI0.wf)
        (writerWP_setNode_madeFor r cv c w)) (good_setNode B r cv false c w hvg hcg))
        (uniqueCache_setNode (base := B) r cv false c w hvg.ids hu)) ?_
      rintro res v ⟨⟨⟨hres, hmv⟩, hcgv⟩, huv, -⟩
      cases res with
      | none => exact rwp_refl _ _ _
      | some y =>
        obtain ⟨hS', hg⟩ := hres y rfl
        refine ih y v hS' (hmv.trans hmw) hcgv huv ?_
        intro q hq
        apply ht q
        simp only [fromVisits]
        apply List.mem_append_right
        rw [hg]
        exact hq

/-- The delete's two copies run alike from a state with `PutInv`, the fill, the
made-for ids nodes of the view, the take-back's node facts and the cache's books. -/
theorem rwp_putKvDelChk5 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hcg : CacheGood B c w0) (hu : UniqueCache B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (key : Key) : RWP (putKvDelChk5 key) (putKvDelChk2 key) c w0 := by
  unfold putKvDelChk5 putKvDelChk2
  refine rwp_bind (fun _ v => v = { w0 with path := [] })
    (by unfold pathClear; simp only [writerWP_modify]) ?_
  rintro _ v1 hv1
  subst hv1
  refine rwp_bind (fun a v => a = w0.top.rootKey ∧
      v = { ({ w0 with path := [] } : W) with path := [(none, w0.top.rootKey)] })
    (by simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure]
        simp) ?_
  rintro a v2 ⟨ha, hv2⟩
  subst ha; subst hv2
  refine rwp_putSegsDelChk5 c base hvc w0 B hvg hI hJ2 hLC hm hmf0 key key _ _ ?_ rfl hcg hu (hI.pathUntaken key)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, List.prefix_refl _, [], rfl, LinkedFrom.nil _, rfl, ?_⟩
  intro z hz
  simp at hz



/-! ## The premise without the loop's `checkFree` -/

/-- The cache ids are distinct at every state between operations. -/
theorem uniqueCache_reached (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (top : Top) (pre : List Op) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ViewGood tx.base (ctxOf p ts) ∧ UniqueCache tx.base w := by
  obtain ⟨hP', _, hN⟩ := hR
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hvg : ViewGood tx.base (ctxOf p ts) :=
    viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have hw0 : UniqueCache tx.base (wInit tx top) := by
    constructor
    · exact ⟨Nat.le_refl _, by simp [wInit], by simp [wInit], by simp [wInit]⟩
    · simp [CacheUnique, wInit]
  exact ⟨hvg, (uniqueCache_ops (base := tx.base) pre (ctxOf p ts) (wInit tx top) hvg.ids hw0 r w hpre).1⟩

/-- `OpDelChk4OKR` with `putKvDelChk5`, and the take-back's node facts at the
delete's start: at the deletes of the runs of R, the delete runs as its checked
copy with the merge's and the root collapse's holder checks only. -/
def OpDelChk5OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk5 key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk5OKR` at the induction's runs: `hchk` with the stop-node checks,
`checkOld3` and the upward loop's `checkFree` proved. -/
def OpDelChk5OKL (p : Params) : Prop := OpDelChk5OKR p (RunTreeQ p (LatestQD p))

/-- `OpDelChk2ORJ` from `OpDelChk5OKR`, the merges on, node size at least 4. -/
theorem opDelChk2ORJ_of_chk5 (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 4 ≤ p.M) (hRL : ∀ P t, R P t → RunLinksOK p P t) (h : OpDelChk5OKR p R) :
    OpDelChk2ORJ p R :=
  fun ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he => by
    have hmf := stateOK_madeForView p hM R hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
    have hbk := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
    obtain ⟨hvg, hu⟩ := uniqueCache_reached p ts tx hw (hRL _ _ hr) top pre r w hpre
    exact rwp_putKvDelChk5 (ctxOf p ts) (viewOf (treeRun p ts)) (viewCoherent_ctxOf p ts) w tx.base hvg hI hJ
      hbk.good hu hL hm (fun x o ho => (hmf x o ho).2) key _
      (h ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he)

/-! ## The top theorem -/

set_option maxHeartbeats 3200000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, without `hHL` and
`hMF`, and with `hchk` narrowed to the merge's and the root collapse's holder
checks at the deletes whose start has the fill, `PutInv`, the ranges, the heights
and the take-back's node facts (`OpDelChk5OKL`): the joint route
(`jointHtJ_reachedJ`). -/
theorem invGetScanOK_merges_joint5 (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk5 : OpDelChk5OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  have hCo : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => ⟨hCoF ts, hCoU ts⟩
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4))
  -- the joint induction's cases
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
  have hTp := opCaseOK_put_of_cases p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hPp := opCaseOK_put_of_cases p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hOp := opCaseOK_put_of_cases p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hTIRJ := opCaseOKJ_treeInvRange_delMergeRL p _
    (delStepsQdLJ_of_openR p _ (by omega) hsa hRL' hRP' hRK' hRH' hU) hMS hCo hsa hcap hRP' hRK'
  have hSI : ∀ ts tx w, SJ p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1.1
  have hSV : ∀ ts tx w, SJ p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.1.2
  have hSB : ∀ ts tx w, SJ p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.1.2
  have hSR : ∀ ts tx w, SJ p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.1.2
  have hSF : ∀ ts tx w, SJ p ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey :=
    fun _ _ _ h => h.1.2.1
  have hSM : ∀ ts tx w, SJ p ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base :=
    fun _ _ _ h => h.1.2.2
  have hDSJ : DelStepsJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    delStepsJ2OKS_of_openR p _ (SJ p) (by omega) hsa hRL' hRP' hRK' hSI hSV hSB hSR hSF hSM hRH'
      (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hU
  have hJ2O : OpJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ hRL' hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ (by omega) hSI hSB (opJ2Case_putNewSegFull p _ _ hRL' (by omega) hsa hSI hSB hSR))
      (opJ2Case_delMergeR p _ _ hDSJ hMS hCo (replaceRootFullJ2OK_run p hsa) hsa hcap hRP' hRK')
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI)
      (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2Case_delRoom p _ _ hSI hSV)
      (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)
  have hchkR := opDelChk2ORJ_of_chk5 p _ hm hM4 hRL' hchk5
  have joint := jointHtJ_reachedJ p _ hm (by omega) hM4 (baseStartOK_runTreeQ p (LatestQD p)) hRL' hRT' hRI'
    hRP' hRK' hRH' htb hTp hPp hOp hTIRJ.1 hTIRJ.2.1 hTIRJ.2.2 hJ2O hLv hchkR
  -- from the joint induction: the heights' delete side, the fuel, the cases at every operation
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
    obtain ⟨hI, hRo, hL, _, _, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
    have hc := hchkR ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi hJ r' v he
    obtain ⟨-, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP' _ _ hr) (hRK' _ _ hr) hw top pre
      (Op.del key :: post) hsplit r w hpre
    exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
      (by simpa [ctxOf] using (show 2 ≤ p.M by omega)) r' v hc).2.1
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHU p (by omega) _ hRL' hRK' hRH' hht htb
  have hnext : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      ∀ z top, lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → ∀ a w', putKv op (ctxOf p ts) w = .ok (a, w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' ∧
        PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w' ∧
        RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre a w' he
    obtain ⟨hI', hR', _, _, hT', _⟩ := joint ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hs]; simp)
      (r ++ [a]) w' (mapM_snoc_ok _ _ pre op r w a w' hpre he)
    exact ⟨hT', hI', hR'⟩
  have hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).1
  have hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.1
  have hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.2
  have hLC : StateOK p (RunTreeQ p (LatestQD p)) (fun ts _ w => LiveCountsW p ts w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.1
  have hJ2S : StateOK p (RunTreeQ p (LatestQD p))
      (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.2.2.2
  have hMFS := stateOK_madeFor p hM4 (RunTreeQ p (LatestQD p)) hRL'
  -- from here as in `invGetScanOK_merges`, the delete's steps without `hHL`
  have d4' := opCaseOK_anti p _ _ hR _ _ (deadCase_delMergeL_of_rest p (RunOK p) hRL
    (opCaseOK_of_open p (RunOK p) (QDead p) (keptByReads_dead p) DelMergeDRestCase d4))
  have hTL := opCaseOK_L_of_any p _ _ hT
  have hPIL := opCaseOK_L_of_any p _ _ hPI
  have hOL := opCaseOK_L_of_any p _ _ hO
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesS p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ hMFS
    (delStepsJ2OKJ_of_openR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htb hU hLC)
    hMS hCo (replaceRootFullJ2OK_run p hsa)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hT))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hPI))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hO))
    (opGetCaseOK_delMerge p (RunOK p)
      (delStepsOK_of_within p (RunOK p) _ hW
        (delStepsOKJ_of_open p _ (by omega) hsa hRL' hP hRK' hRH' hht htb hU hLC hJ2S hMFS))
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

/-! ## Root collapse's check, at a state with the take-back's node facts -/

set_option maxHeartbeats 1600000 in
/-- Root collapse's check before it takes back X depth, a node that the
transaction made, at the end of a path from the space root, at a state with
`PutInv` and the take-back's node facts: its one live holder is the path's node
above it, by the klong that the path names (`liveHolder_unique`; none at depth 0,
the root has no holder); the klongs before the transaction name ids below the
first id; at a depth above 0 it is not the space root; and it is no node of the
view. -/
theorem checkRoot_ok_of_J2 (c : Ctx) (base : View BVal) (v : W) (B : NodeId)
    (hvg : ViewGood B c) (hI : PutInv c base v) (hJ2 : TakeJ2 c base B v) (hcg : CacheGood B c v)
    (hnd : (v.nodes.map Prod.fst).Nodup)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = v.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base v (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hpX : ∀ i, i ≤ depth → (v.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → v.path[i]? = some (some (K i), X i))
    (xn : KNode) (hxn : v.nodes.lookup (X depth) = some xn) (hft : xn.firstTime = some c.i) :
    checkRoot (X depth) depth c v = .ok ((), v) := by
  have hpos := hvg.pos
  have hBx : B ≤ X depth := Blank.ge B c (X depth) hvg
    (blank_of_firstTime B c (X depth) xn hpos (cacheGood_lookup B c v hcg (X depth) xn hxn) (by simp [hft]))
  obtain ⟨hTt, _, hOB, _, _, _⟩ := hJ2
  have hTi : TimesN (wNode c.p base v) c.i := fun q qn hq s hs => hI.times q qn hq s hs
  have hdist := chain_dist c base v hI X Nn K depth hX0 hXN hlinkK
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base v) c.i v.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by simpa using hlinkK (i + 1) (by omega) hi⟩
  have hA : holderAtB c v (X depth) depth = true := by
    unfold holderAtB
    rw [List.all_eq_true]
    rintro ⟨q, n⟩ hq
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_false,
      beq_iff_eq]
    by_cases htq : v.taken.contains q = true
    · exact Or.inl htq
    right
    have hlq := lookup_of_mem_nodup _ hnd q n hq
    have hgq : Good B c q n := hcg.2 (q, n) hq
    have hw : wNode c.p base v q = some n := by
      unfold wNode; rw [show v.taken.contains q = false by simpa using htq]; simp [hlq]
    refine ⟨?_, ?_⟩
    · rintro ⟨cv, z⟩ he
      by_cases hz : z = X depth
      · subst hz
        have hlive : (cv, X depth) ∈ n.liveAt c.i := by
          rw [KNode.liveAt_of_times n c.i (hI.times q n hw)]; exact he
        rcases Nat.eq_zero_or_pos depth with h0 | h0
        · exfalso
          have hk : Klong.key cv (X depth) ∈ n.ks := KNode.liveAt_key_mem n c.i cv (X depth) hlive
          have htm := time_of_new _ c.i B hpos hOB hTi q n hw cv (X depth) hk hBx
          have hr := hTt q n hw htm
          have hroot : X depth = v.top.rootKey := by rw [h0]; exact hX0
          rw [hroot] at hlive
          exact hI.tree.rootFree q cv hr ⟨n, hw, hlive⟩
        · have hreach := (hPL (depth - 1) (by omega)).reach
          have hl : TLink (wNode c.p base v) c.i (X (depth - 1)) (K depth) (X depth) :=
            ⟨Nn (depth - 1), hXN (depth - 1) (by omega), hlinkK depth h0 (Nat.le_refl _)⟩
          obtain ⟨hqx, hcv⟩ := liveHolder_unique _ c.i v.top.rootKey B hpos hTt hOB hTi hI.tree (X depth) hBx
            (X (depth - 1)) (K depth) hreach hl q n hw cv hlive
          subst hqx; subst hcv
          have h1 := hpX (depth - 1) (by omega)
          have h2 := hpK depth h0 (Nat.le_refl _)
          simp [h1, h2, show depth ≠ 0 by omega]
      · simp [hz]
    · rintro ⟨cv, z⟩ he hz
      simp only at hz
      subst hz
      obtain ⟨c0, hk⟩ := live_key_mem _ cv (X depth) he
      have := ptr_lt_of_prefix B c hvg q n hgq c0 (X depth) hk
      omega
  have hR : (depth == 0 || v.top.rootKey != X depth) = true := by
    rcases Nat.eq_zero_or_pos depth with h0 | h0
    · simp [h0]
    · have : v.top.rootKey ≠ X depth := by
        intro he
        rw [← hX0] at he
        have := hdist 0 depth (by omega) (Nat.le_refl _) he
        omega
      simp [this]
  have hV : (c.view (X depth)).isNone = true := by
    cases hvx : c.view (X depth) with
    | none => rfl
    | some nd => have := hvg.ids _ nd hvx; omega
  unfold checkRoot
  rw [m_bind_ok]
  refine ⟨c, v, rfl, ?_⟩
  rw [m_bind_ok]
  refine ⟨v, v, rfl, ?_⟩
  simp only [hA, hR, hV, Bool.and_self, ↓reduceIte]
  rfl

end SIS.Tree
