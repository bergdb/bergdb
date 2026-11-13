import SIS.Tree.PutInvNewSeg
import SIS.Tree.WriterTreePut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the delete rules that change at most one node by shrinking
its live klongs (bergdb 024-12, TP10; prover latest's `writerWP_del_noop_seg`,
`writerWP_del_bitmap_seg`): a delete of a key without a value changes nothing
the state reads (`putInv_del_noop_seg`); a delete by a bitmap in a segment leaf
that keeps a live klong, the merges off, takes live klongs of one node only
(`putInv_del_bitmap_seg`). The parts about the tree after any change that only
takes live klongs of one node: `putInvT_shrink`. -/

/-- A state that reads as w meets the parts about the tree that w meets. -/
theorem putInvT_of_readsAs (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (hr : ReadsAs c.p base w w') : PutInvT c base w' := by
  obtain ⟨hN, htop, htk, _, _⟩ := hr
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hN, htop] at hx
    rw [htk]
    exact hI.untaken x hx
  · intro q qn L n k1 hq hqn hql hn hnl hk
    rw [hN, htop] at hq
    rw [hN] at hqn hn
    exact hI.order q qn L n k1 hq hqn hql hn hnl hk

/-- The parts about the tree after a change of one node x that only takes live
klongs of it, of the same kind. -/
theorem putInvT_shrink (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (x : NodeId) (n n' : KNode) (hn : wNode c.p base w x = some n) (hl : n'.leaf = n.leaf)
    (ht' : ∀ s, Klong.time s ∈ n'.ks → s ≤ c.i)
    (hsub : ∀ c' z, (c', z) ∈ n'.live → (c', z) ∈ n.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hx' : wNode c.p base w' x = some n')
    (hother : ∀ y, y ≠ x → wNode c.p base w' y = wNode c.p base w y) :
    PutInvT c base w' := by
  have hnt := hI.times x n hn
  have hsubAt : ∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z h
    rw [KNode.liveAt_of_times _ c.i ht'] at h
    rw [KNode.liveAt_of_times _ c.i hnt]
    exact hsub c' z h
  have hsub' : ∀ y, ReachS (wNode c.p base w') c.i w'.top.rootKey y →
      ReachS (wNode c.p base w) c.i w.top.rootKey y := by
    rw [htop]
    apply reachS_closed _ _ _ (fun y => ReachS (wNode c.p base w) c.i w.top.rootKey y) ReachS.root
    intro y yn cc z hy hyn hz
    by_cases hyx : y = x
    · subst hyx
      rw [hx'] at hyn; cases hyn
      exact ReachS.step y n cc z hy hn (hsubAt cc z hz)
    · rw [hother y hyx] at hyn
      exact ReachS.step y yn cc z hy hyn hz
  refine ⟨?_, ?_⟩
  · intro y hy; rw [htk]; exact hI.untaken y (hsub' y hy)
  · intro q qn L m k1 hq hqn hql hm hml hk
    have hq' := hsub' q hq
    by_cases hqx : q = x
    · subst hqx
      rw [hx'] at hqn; cases hqn
      have hk' := hsub k1 L hk
      have hql' : n.leaf = false := by rw [← hl]; exact hql
      by_cases hLx : L = q
      · subst hLx; rw [hx'] at hm; cases hm; rw [hql] at hml; cases hml
      rw [hother L hLx] at hm
      have hold := hI.order q n L m k1 hq' hn hql' hm hml hk'
      intro c' z hz
      exact ⟨(hold c' z hz).1, fun c'' z'' hz'' hlt => (hold c' z hz).2 c'' z'' (hsub c'' z'' hz'') hlt⟩
    · rw [hother q hqx] at hqn
      by_cases hLx : L = x
      · subst hLx
        rw [hx'] at hm; cases hm
        have hold := hI.order q qn L n k1 hq' hqn hql hn (by rw [← hl]; exact hml) hk
        exact fun c' z hz => hold c' z (hsub c' z hz)
      · rw [hother L hLx] at hm
        exact hI.order q qn L m k1 hq' hqn hql hm hml hk

/-- A delete of a key without a value keeps `PutInv` (it changes nothing that
the state reads). -/
theorem putInv_del_noop_seg (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hB.coherent (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hB.coherent c.p.fuel rk w2' ht2) ?_
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
  exact putInvT_of_readsAs c base w w3 hI hr03

/-- A delete's bitmap in node x with room for it (or the transaction's own
bitmap set in place), not full by its dead klongs: x loses live klongs only. -/
theorem writerWP_appendDeleteKlong_room_after (base : View BVal) (x : NodeId) (depth cv : Nat)
    (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : lastIsDel n.ks = false ∨ n.lastTime ≠ some c.i → n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => ∃ n' : KNode, n'.leaf = n.leaf ∧
      (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
      (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) ∧
      w'.taken = w.taken ∧ w'.top = w.top ∧
      ∀ y, wNode c.p base w' y = if y = x then some n' else wNode c.p base w y) := by
  have hwn : ∀ (n' : KNode) (w' : W), w'.nodes = upsert w.nodes x n' → w'.taken = w.taken →
      ∀ y, wNode c.p base w' y = if y = x then some n' else wNode c.p base w y := by
    intro n' w' h1 h2 y
    by_cases hy : y = x
    · subst hy; simp only [wNode, h2, hxt, Bool.false_eq_true, ↓reduceIte, h1, lookup_upsert]
    · simp only [wNode, h2, h1, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun old hold c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z,
      (c', z) ∈ (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  have haddt := KNode.add_times n c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))
    (fun s h => by cases h) hnt
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hdead1 hdead2 hsetAt hadd haddt
    cases hno : (U == n.lastBitmap)
    · cases hgl : n.ks.getLast? with
      | none =>
        have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
        have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
        simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
      | some k =>
        cases k with
        | del old =>
          cases hlt : (n.lastTime == some c.i)
          · have hlt' : n.lastTime ≠ some c.i := by simpa using hlt
            have hroom' : n.size + 1 < c.p.M := hroom (Or.inr hlt')
            simp only [hroom', hdead2, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
          · simp only [hdead1, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact ⟨_, KNode.setAt_leaf _ _ _, KNode.setAt_last_del_times n c.i old _ hgl hnt,
              hsetAt old hgl, trivial, trivial, hwn _ _ rfl rfl⟩
        | _ =>
          have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
          have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
          simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
          exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      refine ⟨n, rfl, hnt, fun _ _ h => h, trivial, trivial, ?_⟩
      intro y
      by_cases hy : y = x
      · subst hy; simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
      · simp only [hy, ↓reduceIte]

/-- A delete of a key by a bitmap in its segment leaf, which keeps a live klong,
the merges off, keeps `PutInv` (the writer's tree after it given). -/
theorem putInv_del_bitmap_seg (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
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
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hB.coherent (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hB.coherent c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hne, hkeep, hd1, hd2, hroom⟩ := hleaf L n hvisL hn hnl
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_room_after base L _ cv n c w3 hlk3
    (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn) hroom hd1 hd2) ?_
  intro _ w4 ⟨n', hl', ht', hsub, h4t, h4top, hN4⟩
  have hdesc : PutInvT c base w4 := by
    refine putInvT_shrink c base w w4 hI L n n' hn (by rw [hl']) ht' ?_ (h4t.trans hr03.2.2.1)
      (h4top.trans hr03.2.1) (by rw [hN4]; simp) (fun y hy => by
        rw [hN4]; simp only [hy, ↓reduceIte]; rw [hr03.1])
    intro c' z hz
    rw [← KNode.liveAt_of_times _ c.i ht'] at hz
    have := hsub c' z hz
    rwa [KNode.liveAt_of_times _ c.i (hI.times L n hn)] at this
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hdesc

end SIS.Tree
