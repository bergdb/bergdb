/-
True forms of two premises that are false as stated (bergdb 024-22, section
11.1; the counterexamples in SIS/Tree/PremisesFalse.lean), with what their
consumers have in scope:

* `hCoU`'s second half from the books (`collapseUnlink_ids_of_book`), so that
  with the books `CollapseUnlinkOK` needs its tree half only
  (`collapseUnlinkOK_of_tree`);
* `hHL` (`UpHolderLiveRunOK`'s conclusion) from the take-back's node facts at
  the delete's start (`TakeJ2`), the nodes taken back of the transaction
  (`TakenAbove`) and the books (`upHolderLive_of_J2`).

`hU` and `hCoU`'s tree half stay open: they need an invariant on the nodes that
the transaction left out.
-/
import SIS.Tree.LatestTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## `hCoU`: the ids of the previous version -/

/-- `hCoU`'s second half from the books: a cached node's version before the
transaction is its node in P, whose klongs name ids below the first id B, so
below the next id. -/
theorem collapseUnlink_ids_of_book (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (v : W)
    (x : NodeId) (n : KNode) (hB : PutBase c base B) (hb : PutBook c B top0 v)
    (hlk : v.nodes.lookup x = some n) :
    ∀ c' z, (c', z) ∈ (n.toPrev (c.i - 1)).liveAt c.i → z < v.next := by
  intro c' z hz
  have hk := KNode.liveAt_key_mem _ _ _ _ hz
  have hg := cacheGood_lookup B c v hb.good x n hlk
  have hk' : Klong.key c' z ∈ baseKlongs c.view x := by
    rw [← hg.old]; exact hk
  unfold baseKlongs at hk'
  cases hvx : c.view x with
  | none => rw [hvx] at hk'; cases hk'
  | some nd =>
    rw [hvx] at hk'
    have := hB.good.ptrs x nd hvx c' z hk'
    have := hb.good.1
    omega

/-- `CollapseUnlinkOK` with the books from its tree half alone. -/
theorem collapseUnlinkOK_of_tree (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (v : W)
    (x : NodeId) (n : KNode) (hB : PutBase c base B) (hb : PutBook c B top0 v)
    (hlk : v.nodes.lookup x = some n)
    (hT : n.lastTime = some c.i →
      TreeOK (updN (wNode c.p base v) x (n.toPrev (c.i - 1))) c.i v.top.rootKey) :
    CollapseUnlinkOK c base v x n :=
  fun h => ⟨hT h, collapseUnlink_ids_of_book c base B top0 v x n hB hb hlk⟩


/-! ## `hHL` from the take-back's node facts -/

/-- Where the klongs of time u end: at a time klong after u. -/
theorem prefixAt_stop_idx (u : Time) : ∀ (ks : List Klong), (prefixAt ks u).length < ks.length →
    ∃ s, ks[(prefixAt ks u).length]? = some (.time s) ∧ u < s := by
  intro ks
  induction ks with
  | nil => intro h; simp at h
  | cons k r ih =>
    intro h
    cases k with
    | time s =>
      by_cases hs : s ≤ u
      · have he : prefixAt (Klong.time s :: r) u = Klong.time s :: prefixAt r u := by
          simp [prefixAt, hs]
        rw [he] at h ⊢
        simp only [List.length_cons] at h ⊢
        exact ih (by omega)
      · have he : prefixAt (Klong.time s :: r) u = [] := by
          simp [prefixAt, hs]
        rw [he]
        exact ⟨s, rfl, by omega⟩
    | key cv y =>
      have he : prefixAt (Klong.key cv y :: r) u = Klong.key cv y :: prefixAt r u := by
        simp [prefixAt]
      rw [he] at h ⊢
      simp only [List.length_cons] at h ⊢
      exact ih (by omega)
    | del b =>
      have he : prefixAt (Klong.del b :: r) u = Klong.del b :: prefixAt r u := by
        simp [prefixAt]
      rw [he] at h ⊢
      simp only [List.length_cons] at h ⊢
      exact ih (by omega)

/-- In well-formed klongs whose last time klong t is at ti, every klong before ti
is of an earlier time. -/
theorem mem_prefixAt_before_time (ks : List Klong) (t : Time) (hpos : 0 < t)
    (hw : klongsWf ks = true) (hle : ∀ s, Klong.time s ∈ ks → s ≤ t) (ti : Nat)
    (hti : ks[ti]? = some (.time t)) (j : Nat) (hj : j < ti) (k : Klong) (hk : ks[j]? = some k) :
    k ∈ prefixAt ks (t - 1) := by
  apply mem_prefixAt_of_lt ks (t - 1) j k _ hk
  apply Classical.byContradiction
  intro hlt
  have hlen : (prefixAt ks (t - 1)).length < ks.length := by
    have := (List.getElem?_eq_some_iff.mp hti).1
    omega
  obtain ⟨s, hs, hst⟩ := prefixAt_stop_idx (t - 1) ks hlen
  have hsl := hle s (List.mem_of_getElem? hs)
  have hseq : s = t := by omega
  subst hseq
  have hL : (prefixAt ks (s - 1)).length < ti := by omega
  have := klongsWf_times_increase ks hw _ ti s s hL hs hti
  omega

/-- A `Good` node of well-formed klongs whose last time is not the transaction's
names only nodes below B. -/
theorem ptr_lt_of_good_old (B : NodeId) (c : Ctx) (hv : ViewGood B c) (y : NodeId) (n : KNode)
    (hg : Good B c y n) (hw : klongsWf n.ks = true) (hl : n.lastTime ≠ some c.i)
    (cv : Nat) (z : NodeId) (hk : Klong.key cv z ∈ n.ks) : z < B := by
  have hpos := hv.pos
  by_cases hp : Klong.key cv z ∈ prefixAt n.ks (c.i - 1)
  · rw [hg.old] at hp
    unfold baseKlongs at hp
    cases hvy : c.view y with
    | none => rw [hvy] at hp; cases hp
    | some nd => rw [hvy] at hp; exact hv.ptrs y nd hvy cv z hp
  · obtain ⟨s, hs, hlt⟩ := later_time_of_not_mem_prefixAt n.ks (c.i - 1) _ hk hp
    have hsl := hg.times s hs
    have hseq : s = c.i := by omega
    rw [hseq] at hs
    exact absurd (KNode.lastTime_of_mem_max n c.i hw hs hg.times) hl

/-- The live klongs of a node are among its key klongs. -/
theorem live_key_mem (n : KNode) (cv : Nat) (z : NodeId) (h : (cv, z) ∈ n.live) :
    ∃ c0, Klong.key c0 z ∈ n.ks :=
  ptrsPairs_live (P := fun y => ∃ c0, Klong.key c0 y ∈ n.ks) (fun c _ hk => ⟨c, hk⟩) (cv, z) h

theorem lastTime_toPrev_ne (n : KNode) (t : Time) (hpos : 0 < t) :
    (n.toPrev (t - 1)).lastTime ≠ some t := by
  intro h
  obtain ⟨m, _, hm⟩ := KNode.lastTime_anchor _ t h
  exact time_not_mem_prefixAt n.ks t hpos (List.mem_of_getElem? hm)

theorem ptr_lt_of_prefix (B : NodeId) (c : Ctx) (hv : ViewGood B c) (y : NodeId) (n : KNode)
    (hg : Good B c y n) (cv : Nat) (z : NodeId) (hk : Klong.key cv z ∈ prefixAt n.ks (c.i - 1)) :
    z < B := by
  rw [hg.old] at hk
  unfold baseKlongs at hk
  cases hvy : c.view y with
  | none => rw [hvy] at hk; cases hk
  | some nd => rw [hvy] at hk; exact hv.ptrs y nd hvy cv z hk

set_option maxHeartbeats 800000 in
/-- `hHL`'s true form: at the upward loop's end no node not taken back holds, by
a live klong now or before the transaction, a node taken back, given at the
delete's start the take-back's node facts (`TakeJ2`), the nodes taken back of
the transaction (`TakenAbove`), and the books, as the take-back's route has them.
A node with a klong of the transaction is reached, so the nodes it names are
reached and not taken back; a chain node taken back has one holder, its parent
on the chain (`liveHolder_unique`), which is taken back, unlinked to its node in
P, or the stop node, whose klongs of the transaction to it are retargeted. -/
theorem upHolderLive_of_J2 (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hv : ViewGood B c)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W)
    (S : KNode)
    (hI : PutInv c base w) (hJ : TakeJ2 c base B w) (hTA : TakenAbove B w)
    (hb3 : PutBook c B top0 w3) (hb2 : PutBook c B top0 w2)
    (hvals : ∀ y, w2.taken.contains y = true → y ∉ w2.vals.map (·.1))
    (hr : ReadsAs c.p base w w3)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlk : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hlink : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i') (hs : stop < depth)
    (hLE : UpLoopEnd c B X Nn depth stop w3 w2 S) :
    ∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
      ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) →
        w2.taken.contains z = false := by
  have hpos := hv.pos
  obtain ⟨hT2, _, hvals2, _, _, _, hfr, hSl, _, hRS, hRF, _, hCW⟩ := hLE
  obtain ⟨hTt, hDL, hOB, _, _, _⟩ := hJ
  have hTi : TimesN (wNode c.p base w) c.i := fun q qn hq s hs => hI.times q qn hq s hs
  have hreach : ∀ q qn, wNode c.p base w q = some qn → ∀ cv y', Klong.key cv y' ∈ qn.ks → B ≤ y' →
      TReach (wNode c.p base w) c.i w.top.rootKey q := fun q qn hq cv y' hk hB =>
    hTt q qn hq (time_of_new _ c.i B hpos hOB hTi q qn hq cv y' hk hB)
  have huntk : ∀ q, TReach (wNode c.p base w) c.i w.top.rootKey q → w.taken.contains q = false :=
    fun q hq => hI.untaken q (tReach_reachS _ _ _ _ hq)
  have htk3 : ∀ q, (∀ k, stop < k → k ≤ depth → q ≠ X k) →
      w2.taken.contains q = w.taken.contains q := by
    intro q hq; rw [hT2 q hq, hr.2.2.1]
  intro y n hy hyt cv z hz
  apply Classical.byContradiction
  intro hzt
  have hzt' : w2.taken.contains z = true := by simpa using hzt
  -- a node taken back here and reached at the start is a chain node
  have hchain : w.taken.contains z = false → ∃ k, stop < k ∧ k ≤ depth ∧ z = X k := by
    intro hzw
    apply Classical.byContradiction
    intro hno
    have hz1 : ∀ k, stop < k → k ≤ depth → z ≠ X k := fun k h1 h2 he => hno ⟨k, h1, h2, he⟩
    rw [htk3 z hz1, hzw] at hzt'
    cases hzt'
  -- z is a node of the transaction
  have hBz : B ≤ z := by
    by_cases hzc : ∃ k, stop < k ∧ k ≤ depth ∧ z = X k
    · obtain ⟨k, hk1, hk2, rfl⟩ := hzc
      by_cases hf : (Nn k).firstTime = some c.i
      · have hg := cacheGood_lookup B c w3 hb3.good (X k) (Nn k) (hlk k hk2)
        exact Blank.ge B c _ hv (blank_of_firstTime B c _ _ hpos hg (by simp [hf]))
      · rw [((hCW k hk1 hk2).2 hf).1] at hzt'; cases hzt'
    · have hz1 : ∀ k, stop < k → k ≤ depth → z ≠ X k := fun k h1 h2 he => hzc ⟨k, h1, h2, he⟩
      rw [htk3 z hz1] at hzt'
      exact hTA z (by simpa using hzt')
  have hzv : z ∉ w.vals.map (·.1) := by
    have := hvals z hzt'
    rwa [hvals2, hr.2.2.2.1] at this
  have hgn := cacheGood_lookup B c w2 hb2.good y n hy
  have hwn : klongsWf n.ks = true := writerKlongsWf_lookup w2 hb2.klongs y n hy
  -- a chain node X k taken back is held only by X (k - 1)
  have hholder : ∀ k, stop < k → k ≤ depth → B ≤ X k → ∀ q qn, wNode c.p base w q = some qn →
      ∀ c1, (c1, X k) ∈ qn.liveAt c.i → q = X (k - 1) := by
    intro k hk1 hk2 hBk q qn hq c1 hc1
    have hNk1 := hXN (k - 1) (by omega)
    have hl := hlink k (by omega) hk2
    have hRk1 := hreach _ _ hNk1 (K k) (X k) (KNode.liveAt_key_mem _ _ _ _ hl) hBk
    exact (liveHolder_unique _ c.i w.top.rootKey B hpos hTt hOB hTi hI.tree (X k) hBk (X (k - 1)) (K k)
      hRk1 ⟨Nn (k - 1), hNk1, hl⟩ q qn hq c1 hc1).1
  rcases hz with hz | hz
  rotate_left
  · obtain ⟨c0, hk⟩ := live_key_mem _ cv z hz
    have := ptr_lt_of_prefix B c hv y n hgn c0 z hk
    omega
  obtain ⟨c0, hk⟩ := live_key_mem n cv z hz
  by_cases hys : y = X stop
  · -- the stop node
    subst hys
    rw [hSl] at hy; cases hy
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
    rcases retFormS_key c.i B (Nn stop) S hRS i c0 z hi with hlt | hi'
    · omega
    have hNs := hXN stop (by omega)
    obtain ⟨⟨c1, hc1⟩, _⟩ := hDL (X stop) (Nn stop) hNs i c0 z hi' hBz hzv
    have hRs := hreach _ _ hNs c0 z (List.mem_of_getElem? hi') hBz
    have hzw := huntk z (TReach.link hRs ⟨Nn stop, hNs, hc1⟩)
    obtain ⟨k, hk1, hk2, rfl⟩ := hchain hzw
    have heq := hholder k hk1 hk2 hBz (X stop) (Nn stop) hNs c1 hc1
    have hk' : stop = k - 1 := hdist stop (k - 1) (by omega) (by omega) heq
    have hkk : k = stop + 1 := by omega
    subst hkk
    have hft : (Nn (stop + 1)).firstTime = some c.i := by
      apply Classical.byContradiction
      intro hf
      rw [((hCW (stop + 1) hk1 hk2).2 hf).1] at hzt'; cases hzt'
    have hRF' := hRF hft
    rcases retFrom_key c.i B (Nn stop) (X (stop + 1)) S hRF' i c0 (X (stop + 1)) hi with hlt | ⟨hi2, hti⟩
    · omega
    obtain ⟨ti, hti1, hile⟩ := hti rfl
    obtain ⟨m, hm1, hm2⟩ := KNode.lastTime_anchor _ c.i hRF'.1
    have hmti : m = ti := by rw [hti1] at hm1; cases hm1; rfl
    rw [hmti] at hm2
    have hilt : i < ti := by
      rcases Nat.lt_or_ge i ti with h | h
      · exact h
      · have him : i = ti := by omega
        rw [← him, hi2] at hm2; cases hm2
    have hmem := mem_prefixAt_before_time (Nn stop).ks c.i hpos (hI.wf _ _ hNs) (hI.times _ _ hNs) ti hm2
      i hilt _ hi2
    have := hOB _ _ hNs c0 (X (stop + 1)) hmem
    omega
  by_cases hyc : ∃ k, stop < k ∧ k ≤ depth ∧ y = X k
  · -- a chain node not taken back: unlinked to its node in P
    obtain ⟨k, hk1, hk2, rfl⟩ := hyc
    have hfw := hCW k hk1 hk2
    by_cases hf : (Nn k).firstTime = some c.i
    · rw [hfw.1 hf] at hyt; cases hyt
    obtain ⟨_, S', _, hlS⟩ := hfw.2 hf
    rw [hy] at hlS
    cases hlS
    have hl : (unlinkedNode S' c.i).lastTime ≠ some c.i := by
      unfold unlinkedNode
      split
      · exact lastTime_toPrev_ne S' c.i hpos
      · rename_i h
        intro h2
        apply h
        simp [h2]
    have := ptr_lt_of_good_old B c hv _ _ hgn hwn hl c0 z hk
    omega
  -- another node: its node is the one at the delete's start
  have hy1 : ∀ k, stop < k → k ≤ depth → y ≠ X k := fun k h1 h2 he => hyc ⟨k, h1, h2, he⟩
  have hy3 : w3.nodes.lookup y = some n := by rw [← hfr y hys hy1]; exact hy
  have hyt3 : w3.taken.contains y = false := by rw [← hT2 y hy1]; exact hyt
  have hNy : wNode c.p base w y = some n := by
    rw [← hr.1]; simp only [wNode, hyt3, Bool.false_eq_true, ↓reduceIte, hy3]
  have hRy := hreach y n hNy c0 z hk hBz
  have hlive : (cv, z) ∈ n.liveAt c.i := by
    rw [KNode.liveAt_of_times n c.i (hI.times y n hNy)]; exact hz
  have hzw := huntk z (TReach.link hRy ⟨n, hNy, hlive⟩)
  obtain ⟨k, hk1, hk2, rfl⟩ := hchain hzw
  have heq := hholder k hk1 hk2 hBz y n hNy cv hlive
  rcases Nat.lt_or_ge stop (k - 1) with h | h
  · exact hyc ⟨k - 1, h, by omega, heq⟩
  · have hk' : k - 1 = stop := by omega
    rw [hk'] at heq
    exact hys heq

end SIS.Tree
