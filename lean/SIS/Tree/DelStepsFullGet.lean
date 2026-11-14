/-
The delete's invariant after the bitmap into a full leaf below the space root
(bergdb 024-12, TP10, case (4)'s full leaf): the tree and the walk's
ranges (`writerWP_delLeaf_chainGRange`), the reading (`writerWP_handleFull_lastVF2`
and the leaf's change, `wGet_leaf_change_seg`), the books; the fuel premise
after the split is a named input (cost's step 4).
-/
import SIS.Tree.DelStepsF3
import SIS.Tree.RangeDelChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete's bitmap into a full leaf, any post: each branch the writer takes
replaces the leaf by its last version without cv (`handleFull`). -/
theorem writerWP_appendDeleteKlong_full_of (x : NodeId) (d cv : Nat) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) (hfull : ¬ DelRoom c cv n)
    (Q : W → Prop)
    (hQ : ∀ (compact : Bool) (s : String),
      WriterWP (handleFull d x (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c
        ({ w with trail := s :: w.trail } : W) (fun _ v => Q v)) :
    WriterWP (appendDeleteKlong x d cv) c w (fun _ v => Q v) := by
  have hhf : ∀ (compact : Bool) (s : String), WriterWP (do
      note s
      handleFull d x (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact
      pure false) c w (fun _ v => Q v) := by
    intro compact s
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (hQ compact s) ?_
    intro _ v hv
    simp only [writerWP_pure]; exact hv
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
    simp only [hno, Bool.not_false, ↓reduceIte]
    apply writerWP_ite_cases
    · intro htd
      apply writerWP_ite_cases
      · intro _; exact hhf true _
      · intro hdead
        exfalso; apply hfull; left
        have hdead' : deadOver c.p (n.setAt (n.size - 1)
            (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by simpa using hdead
        cases hgl : n.ks.getLast? with
        | none => simp [hgl] at htd
        | some k =>
          cases k with
          | del old =>
            simp [hgl] at htd
            exact ⟨⟨old, rfl⟩, htd, hdead'⟩
          | time t => simp [hgl] at htd
          | key a y => simp [hgl] at htd
    · intro htd
      apply writerWP_ite_cases
      · intro hroom
        apply writerWP_ite_cases
        · intro _; exact hhf true _
        · intro hdead
          exfalso; apply hfull; right
          refine ⟨?_, hroom, ?_⟩
          · rintro ⟨⟨old, hold⟩, hlt'⟩
            apply htd
            simp [hold, hlt']
          · simpa using hdead
      · intro _; exact hhf false _

set_option maxHeartbeats 3200000 in
/-- A delete's bitmap into the full leaf X (D + 1) at the end of the key access
path (D + 1 ≥ 1): the writer's tree after it is a tree whose reached nodes were
reached or are new, with the walk's ranges, the taken ids and the values kept,
and when it fits the fuel it reads as before with the key deleted. -/
theorem writerWP_appendDeleteKlong_full_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey) (hsa2 : 2 ≤ c.p.splitAbove)
    (D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w (D + 1) X K Nn)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (X (D + 1), cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hnl : (Nn (D + 1)).leaf = true)
    (hne : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf cv) ≠ (Nn (D + 1)).lastBitmap)
    (hfull : ¬ DelRoom c cv (Nn (D + 1))) :
    WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) cv) c w (fun _ v =>
      TreeOK (wNode c.p base v) c.i v.top.rootKey ∧ v.taken = w.taken ∧ v.vals = w.vals ∧
      w.next ≤ v.next ∧
      (∀ z, TReach (wNode c.p base v) c.i v.top.rootKey z → TReach (wNode c.p base w) c.i w.top.rootKey z ∨
        w.next ≤ z) ∧
      RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
      (SegFits (wNode c.p base v) c.i c.p.fuel v.top.rootKey → ∀ key', keyWf key' = true →
        wGetAt c.p c.i base v (c.p.fuel + 1) key' =
          if pre ++ [cv] == key' then none else wGetAt c.p c.i base w (c.p.fuel + 1) key')) := by
  have hP' := hP
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := hP'
  have hT := hI.tree
  have hreach := pathOK_reach c base w (D + 1) X K Nn hP
  have hdist := pathOK_dist c base w (D + 1) X K Nn hP hT
  have hw : ∀ j, j ≤ D + 1 → wNode c.p base w (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hO := ordG_of_rangeOrder c _ _ hRO hI.times
  have hord : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn i :=
    fun i h1 h2 => chainOrd_of_ordG c base w (D + 1) X K Nn hP hO i h1 (by omega)
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hlk : w.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := (hS2 (D + 1) (Nat.le_refl _)).1
  have hnt : ∀ s, Klong.time s ∈ (Nn (D + 1)).ks → s ≤ c.i := hI.times _ _ (hw (D + 1) (Nat.le_refl _))
  have hnwf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hw (D + 1) (Nat.le_refl _))
  have hLt : w.taken.contains (X (D + 1)) = false := (hS2 (D + 1) (Nat.le_refl _)).2
  -- the leaf's last version
  obtain ⟨hleq, hlt, _⟩ := delLast_facts (Nn (D + 1)) c.i cv
  have hdl : ∀ c', ((Nn (D + 1)).lastVersionGivenDel c.i
      (bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf cv))).live.lookup c' =
      if c' == cv then none else (Nn (D + 1)).live.lookup c' :=
    fun c' => KNode.delete_live_lookup _ c.i cv c'
  generalize hlast : (Nn (D + 1)).lastVersionGivenDel c.i
    (bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf cv)) = last at hleq hlt hdl
  have hiff := liveAt_iff_of_delete_lookup (Nn (D + 1)) last c.i cv hnt hlt hdl
  have hsub : ∀ c' z, (c', z) ∈ last.liveAt c.i → (c', z) ∈ (Nn (D + 1)).liveAt c.i :=
    fun c' z h => ((hiff c' z).mp h).1
  obtain ⟨pairs, hks, hsorted⟩ := (Nn (D + 1)).lastVersionGivenDel_order c.i
    (bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf cv))
  rw [hlast] at hks
  have hks' : last.ks = newKlongs c.i pairs := by rw [hks]; rfl
  have hlwf : klongsWf last.ks = true := by rw [hks']; exact klongsWf_newKlongs c.i pairs
  have hsize : last.size = pairs.length + 1 := by simp [KNode.size, hks', newKlongs]
  have hlive : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live = pairs := by
    rw [hks']; exact KNode.live_newKlongs_sorted _ _ _ hsorted
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlink (D + 1) (by omega) (Nat.le_refl _); simpa using this
  -- the virtual state with the leaf's last version
  generalize hw3 : ({ w with nodes := upsert w.nodes (X (D + 1)) last } : W) = w3
  have hN3 : ∀ y, wNode c.p base w3 y = if y = X (D + 1) then some last else wNode c.p base w y := by
    intro y
    rw [← hw3]
    by_cases hy : y = X (D + 1)
    · subst hy
      simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hN3u : wNode c.p base w3 = updN (wNode c.p base w) (X (D + 1)) last := by
    funext y
    rw [hN3 y]
    by_cases hy : y = X (D + 1)
    · subst hy; simp [updN]
    · simp [updN, hy]
  have h3top : w3.top = w.top := by rw [← hw3]
  have hV3 : wValue base w3 = wValue base w := by
    rw [← hw3]; exact wValue_congr' base _ w rfl rfl
  have hvL : wNode c.p base w3 (X (D + 1)) = some last := by rw [hN3]; simp
  have hvo : ∀ y, y ≠ X (D + 1) → wNode c.p base w3 y = wNode c.p base w y := by
    intro y hy; rw [hN3 y]; simp [hy]
  have hl' : last.leaf = (Nn (D + 1)).leaf := by rw [← hleq]
  -- the fuel premise for the virtual state
  have hRS : ∀ u, ReachS (wNode c.p base w3) c.i w3.top.rootKey u →
      ReachS (wNode c.p base w) c.i w.top.rootKey u := by
    rw [h3top]
    apply reachS_closed _ _ _ (fun y => ReachS (wNode c.p base w) c.i w.top.rootKey y) ReachS.root
    intro y yn cc z hy hyn hz
    by_cases hyx : y = X (D + 1)
    · subst hyx
      rw [hvL] at hyn; cases hyn
      exact ReachS.step _ _ cc z hy (hw (D + 1) (Nat.le_refl _)) (hsub cc z hz)
    · rw [hvo y hyx] at hyn
      exact ReachS.step y yn cc z hy hyn hz
  have hF3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey :=
    segFits_transfer _ _ c.i _ _ _ hF hRS (fun u un' _ hun' hl => by
      by_cases hu : u = X (D + 1)
      · subst hu; rw [hvL] at hun'; cases hun'; rw [hl', hnl] at hl; cases hl
      · rw [hvo u hu] at hun'
        exact ⟨un', hun', hl, fun c' y hy => ⟨c', hy⟩⟩)
  -- the reading of the virtual state
  have hread3 : ∀ key', keyWf key' = true →
      wGetAt c.p c.i base w3 (c.p.fuel + 1) key' =
        if pre ++ [cv] == key' then none else wGetAt c.p c.i base w (c.p.fuel + 1) key' := by
    intro key' hk'
    have hwf3 : ∀ x xn, ReachS (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
        klongsWf xn.ks = true := by
      intro x xn _ h
      by_cases hx : x = X (D + 1)
      · subst hx; rw [hvL] at h; cases h; exact hlwf
      · rw [hvo x hx] at h; exact hI.wf x xn h
    have hwfw : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => hI.wf x xn h
    rw [wGetAt_eq_wGet c base w3 _ (by omega) hwf3 hF3, wGetAt_eq_wGet c base w _ (by omega) hwfw hF]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w3 (X (D + 1)) pre cv rk (Nn (D + 1)) last
      hfuel h3top (fun x hx => (hvo x hx).symm) (hw (D + 1) (Nat.le_refl _)) hvL hnl (by rw [hl']; exact hnl)
      (fun c' hc' => by
        rw [KNode.searchEq_live _ c.i hnwf hnt, KNode.searchEq_live last c.i hlwf hlt, hdl c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL huniq
      (fun _ _ _ _ y _ _ _ _ _ => by rw [hV3])
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, KNode.searchEq_live last c.i hlwf hlt, hdl cv]
      simp
    · have hk2 : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk2, Bool.false_eq_true, ↓reduceIte]
      exact hother key' hk' (fun h => hk h.symm)
  -- the handleFull of the last version, for both kinds
  refine writerWP_appendDeleteKlong_full_of (X (D + 1)) (D + 1) cv (Nn (D + 1)) c w hlk hne hfull _ ?_
  intro compact s
  rw [hlast]
  have hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    refine ⟨?_, ?_, (hI.fresh z hz).1⟩
    · cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    · cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
  have hrange : ∀ i, 0 < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'' :=
    fun i h1 hi hNR hql' c' z hz hpos' =>
      rangeG_of_rangeOrder c _ _ hRO hI.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
        (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
        (hw i (by omega)) hNR c' z hz hpos'
  have hlen : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length :=
    fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
      (hw i (by omega)) hNR hsp
  have hspace : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (0 < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < i → ChainOrd c K Nn i'))) := by
    intro i _ hi hNR hsp
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 => hord i' h1 (by omega))⟩
  have hrangeLn : (Nn D).leaf = false → ∀ c' z, (c', z) ∈ (Nn (D + 1)).live →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'' := by
    intro hql c' z hz
    have hzn : (c', z) ∈ (Nn (D + 1)).liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hnt]; exact hz
    obtain ⟨hP1, hP2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hRO (X D) (Nn D)
      (tReach_reachS _ _ _ _ (hreach D (by omega))) (hw D (by omega)) hql (K (D + 1)) (X (D + 1)) (Nn (D + 1))
      hkl (hw (D + 1) (Nat.le_refl _))
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
      · omega
      · exact (hP1 c' z hzn).1 hnl hk0
    · intro c'' z' hz2 hlt2
      exact hP2 c'' z' (by rw [KNode.liveAt_of_times _ c.i (hI.times _ _ (hw D (by omega)))]; exact hz2)
        hlt2 c' z hzn
  have hrangeG := writerWP_delLeaf_chainGRange c base w.path 0 D X K Nn cv compact (Nat.zero_le _)
    (fun i _ hi => hX i hi) (fun i h1 hi => hK i h1 hi) (fun i h1 hi => hlink i h1 hi) hrange hlen
    (fun i _ hi => hI.wf _ _ (hw i hi)) (fun i _ hi => hI.times _ _ (hw i hi)) (Or.inr rfl)
    (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hnl hsa2 hrangeLn
    ({ w with trail := s :: w.trail } : W) rfl (fun i _ hi => hS2 i hi) hT (fun i _ hi => hreach i hi)
    hS5 (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) (fun _ => h0.symm) hRO
  rw [hlast] at hrangeG
  have hlevel := writerWP_handleFull_lastVF2 (c.p.fuel + 1) (by omega) c base w.path 0 D X K Nn (Nat.zero_le _)
    (fun i _ hi => hX i hi) (fun i h1 hi => hK i h1 hi) (fun i h1 hi => hlink i h1 hi) hrange hlen
    (fun i _ hi => hI.wf _ _ (hw i hi)) (fun i _ hi => hI.times _ _ (hw i hi)) (Or.inr rfl)
    (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hspace last compact hlwf hlt
    (by
      have hlastEq : last = ⟨(Nn (D + 1)).leaf, newKlongs c.i pairs⟩ := by rw [← hks', hleq]
      rw [hleq, hlastEq, KNode.lastVersion_newKlongs_sorted _ _ _ hsorted])
    (by intro h; rw [hlive]; omega)
    (by
      intro _ hql c' z hz hpos'
      rw [hleq] at hz
      have hz' : (c', z) ∈ last.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hlt]; exact hz
      have hzn := hsub c' z hz'
      rw [KNode.liveAt_of_times _ c.i hnt] at hzn
      exact hrangeLn hql c' z hzn)
    (fun _ => Or.inr (fun _ i' h1 h2 => hord i' h1 (by omega)))
    ({ w with trail := s :: w.trail } : W) rfl (fun i _ hi => hS2 i hi) hT (fun i _ hi => hreach i hi)
    hS5 (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) (fun _ _ => h0.symm) hI.wf
    (by
      rw [hleq]
      exact treeOK_of_node_shrink (wNode c.p base w) _ c.i _ (X (D + 1)) (Nn (D + 1)) last hT
        (hw (D + 1) (Nat.le_refl _)) (updN_self _ _ _)
        (fun y hy => by simp only [updN, hy, ↓reduceIte]; rfl) hsub)
    (by
      intro c' z hz
      rw [hleq] at hz
      exact hG.links _ (Nn (D + 1)) c' z (hw (D + 1) (Nat.le_refl _)) (hsub c' z hz))
  refine writerWP_mono (writerWP_and hrangeG hlevel) ?_
  rintro _ v ⟨⟨hTv, ⟨_, htv, _, hnv, hvv⟩, _, hreachv, hRv⟩, ⟨_, _, _, _, _, hRead, _⟩⟩
  refine ⟨hTv, htv, hvv, hnv, hreachv, hRv, ?_⟩
  intro hFv key' hk'
  have hVal : ∀ z, (w.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ D + 1 ∧ z = X i) → wValue base v z = none := by
    intro z hz
    rw [wValue_congr' base v w htv hvv]
    rcases hz with hz | ⟨i, _, hi, rfl⟩
    · have htz : w.taken.contains z = false := (hS5 z hz).2.1
      have hvz : w.vals.lookup z = none := by
        cases h' : w.vals.lookup z with
        | none => rfl
        | some _ =>
          have hm := lookup_some_mem h'
          have := hI.ids.2.2.2.1 _ hm
          simp only at this; omega
      simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz, (hI.fresh z hz).2]
    · exact hI.keyNoValue _ _ (hw i hi)
  have hR := hRead (wValue base v) hVal (Or.inl (by simpa using hFv)) key'
  have h1 : wGetAt c.p c.i base v (c.p.fuel + 1) key' = wGetAt c.p c.i base w3 (c.p.fuel + 1) key' := by
    unfold wGetAt
    rw [hR, hN3u, h3top, hV3, ← wValue_congr' base v w htv hvv, hleq]
    rfl
  rw [h1]
  exact hread3 key' hk'

/-! ## The named inputs and the step with the kinds' books -/

/-- Named input (cost's step 4, the heights): after a delete's bitmap into a
full leaf at the end of the key access path, the state fits the writer's fuel
(one level more than before at most). -/
def DelFullFitsOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w : W), PutInv c base w → SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey →
    ∀ (d : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode), PathOK c w d X K Nn →
    ∀ (cv : Nat), (Nn d).leaf = true → bitsUnion (Nn d).lastBitmap ((Nn d).bitsOf cv) ≠ (Nn d).lastBitmap →
      ¬ DelRoom c cv (Nn d) →
      WriterWP (appendDeleteKlong (X d) d cv) c w
        (fun _ v => SegFits (wNode c.p base v) c.i c.p.fuel v.top.rootKey)

/-- Obligation (the reading's side at the space root): `writerWP_appendDeleteKlong_full_inv`
for the leaf that is the space root (d = 0, the root's split,
`writerWP_handleFull_rootVF2`). -/
def DelFullRootStepOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w : W), PutInv c base w → PutInvG c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey → 2 ≤ c.p.splitAbove →
    ∀ (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode), PathOK c w 0 X K Nn →
    ∀ (pre : List Nat) (cv : Nat) (rk : NodeId), keyWf (pre ++ [cv]) = true →
      segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk →
      (X 0, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (∀ key' x m, keyWf key' = true →
        (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
        wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv]) →
      (Nn 0).leaf = true → bitsUnion (Nn 0).lastBitmap ((Nn 0).bitsOf cv) ≠ (Nn 0).lastBitmap →
      ¬ DelRoom c cv (Nn 0) →
      WriterWP (appendDeleteKlong (X 0) 0 cv) c w (fun _ v =>
        TreeOK (wNode c.p base v) c.i v.top.rootKey ∧ v.taken = w.taken ∧ v.vals = w.vals ∧
        w.next ≤ v.next ∧
        (∀ z, TReach (wNode c.p base v) c.i v.top.rootKey z →
          TReach (wNode c.p base w) c.i w.top.rootKey z ∨ w.next ≤ z) ∧
        RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
        (SegFits (wNode c.p base v) c.i c.p.fuel v.top.rootKey → ∀ key', keyWf key' = true →
          wGetAt c.p c.i base v (c.p.fuel + 1) key' =
            if pre ++ [cv] == key' then none else wGetAt c.p c.i base w (c.p.fuel + 1) key'))

/-- `writerWP_appendDeleteKlong_full_inv` at every depth, the space root by the
obligation. -/
theorem writerWP_appendDeleteKlong_full_inv_any (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hRoot : DelFullRootStepOK c base)
    (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey) (hsa2 : 2 ≤ c.p.splitAbove)
    (d : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (X d, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hnl : (Nn d).leaf = true)
    (hne : bitsUnion (Nn d).lastBitmap ((Nn d).bitsOf cv) ≠ (Nn d).lastBitmap)
    (hfull : ¬ DelRoom c cv (Nn d)) :
    WriterWP (appendDeleteKlong (X d) d cv) c w (fun _ v =>
      TreeOK (wNode c.p base v) c.i v.top.rootKey ∧ v.taken = w.taken ∧ v.vals = w.vals ∧
      w.next ≤ v.next ∧
      (∀ z, TReach (wNode c.p base v) c.i v.top.rootKey z → TReach (wNode c.p base w) c.i w.top.rootKey z ∨
        w.next ≤ z) ∧
      RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
      (SegFits (wNode c.p base v) c.i c.p.fuel v.top.rootKey → ∀ key', keyWf key' = true →
        wGetAt c.p c.i base v (c.p.fuel + 1) key' =
          if pre ++ [cv] == key' then none else wGetAt c.p c.i base w (c.p.fuel + 1) key')) := by
  cases d with
  | zero => exact hRoot w hI hG hRO hF hsa2 X K Nn hP pre cv rk hkey hrk hvisL huniq hnl hne hfull
  | succ D =>
    exact writerWP_appendDeleteKlong_full_inv c base hvc w hI hG hRO hF hsa2 D X K Nn hP pre cv rk hkey hrk
      hvisL huniq hnl hne hfull

set_option maxHeartbeats 1600000 in
/-- The delete's invariant with the kinds' books (`DelInvF3`) after the bitmap
into a full leaf at the walk's end, from the state w between operations: the
reading's facts (`writerWP_appendDeleteKlong_full_inv_any`), the fuel premise
after (`DelFullFitsOK`), the books, and the inner children from the kinds. -/
theorem writerWP_appendDeleteKlong_full_delF3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hRoot : DelFullRootStepOK c base) (hFits : DelFullFitsOK c base) (hsa2 : 2 ≤ c.p.splitAbove)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (w : W) (pre : List Nat) (cv : Nat) (rk B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hn : wNode c.p base w L = some n)
    (hnl : n.leaf = true) (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hfull : ¬ DelRoom c cv n)
    (hr03 : ReadsAs c.p base w w3) (hJ3 : KdJ c B top0 KO BK w3)
    (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)) :
    WriterWP (appendDeleteKlong L P.length cv) c w3
      (fun _ v => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v) := by
  have hPOK := pathOK_of_toLeaf c base w w3 P n hI hr03 hp3' hlinkP hlkX
  have hNn : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD ⟨true, []⟩ = n := by
    rw [hXD, hn]; rfl
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have hG3 := putInvG_of_book c base B top0 w3 hB hJ3.1
  have hRO3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hF3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hinv := writerWP_appendDeleteKlong_full_inv_any c base hvc hRoot w3 hI3 hG3 hRO3 hF3 hsa2 P.length _ _ _
    hPOK pre cv rk hkey (by rw [hr03.1, hr03.2.1]; exact hrk)
    (by show (nodeAt w.top.rootKey P P.length, cv) ∈ _; rw [hXD, hr03.1]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
    (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne) (by rw [hNn]; exact hfull)
  have hfit := hFits w3 hI3 hF3 P.length _ _ _ hPOK cv (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne)
    (by rw [hNn]; exact hfull)
  simp only [hXD] at hinv hfit
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hinv hfit)
    (putBook_appendDeleteKlong L _ cv c base B top0 hB w3 hJ3.1))
    (kd_appendDeleteKlong KO BK L P.length cv c w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
  rintro _ v ⟨⟨⟨⟨hTv, htv, hvv, hnv, hreachv, hRv, hreadv⟩, hFv⟩, hbv⟩, hbk, hik, _⟩
  have hun : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false := by
    intro y hy
    rw [htv]
    rcases hreachv y hy with h | h
    · exact hI3.untaken y (tReach_reachS _ _ _ _ h)
    · cases h' : w3.taken.contains y with
      | false => rfl
      | true => have := hI3.ids.2.2.1 y h'; omega
  obtain ⟨hPv, hGv⟩ := putInv_after_step c base v B top0 hB hbv hTv
    (fun y hy => hun y (reachS_tReach _ _ _ _ hy)) hRv
  refine ⟨⟨hPv, hGv, hRv, hICEk v hbk hik hun, by simpa using hFv, fun key' hk' => ?_, B, top0, hB, hbv⟩,
    hbk, hik⟩
  rw [hreadv hFv key' hk']
  have hw3w : wGetAt c.p c.i base w3 (c.p.fuel + 1) key' = wGetAt c.p c.i base w (c.p.fuel + 1) key' := by
    unfold wGetAt
    rw [hr03.1, hr03.2.1, ReadsAs.value _ _ _ _ hr03]
  rw [hw3w]

/-- The reading of a delete into a full leaf, the merges on, on the F3 route:
from the fuel premise after the split (`DelFullFitsOK`, cost's step 4) and the
leaf at the space root (`DelFullRootStepOK`), for runs with their links and
TP4 at every run, 2 ≤ splitAbove. -/
theorem delStepsCaseOKF3_full2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseOKF3 p R DelFullM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _
      (writerWP_appendDeleteKlong_full_delF3 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (hRoot ts) (hFits ts)
        hsa2 _ tx.base hv hk hICEk w pre cv rk tx.base top hB hI hRO hF hkey hrk L n P w3 hL hn hnl hne hfull
        hr03 hJ3 hp3' hlinkP hXD hlkX) ?_
    intro g h v hv'
    refine writerWP_mono (hA g h v hv') ?_
    intro _ v' hv'' hFv' key' hk'
    have := runGet_of_delInvF p ts w v' (pre ++ [cv]) hv''.1 hI hF hFv' key' hk'
    simpa [Op.key, Op.value] using this

/-- `DelStepsOKF3` with every case proved but the upward delete without room
(`DelEmptyOtherM`); the full leaf from the fuel premise after its split
(`DelFullFitsOK`, cost's) and the leaf at the space root (`DelFullRootStepOK`). -/
theorem delStepsOKF3_of_open2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (c7 : DelStepsCaseOKF3 p R DelEmptyOtherM)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_cases p R (delStepsCaseOKF3_noLeaf p R) (delStepsCaseOKF3_noop p R)
    (delStepsCaseOKF3_or p R _ _ _ delEmptyM_split (delStepsCaseOKF3_emptyRoom p R hM hRL hP) c7)
    (delStepsCaseOKF3_room p R hM hRL hP) (delStepsCaseOKF3_full2 p R hM hsa2 hRL hP hFits hRoot)

end SIS.Tree
