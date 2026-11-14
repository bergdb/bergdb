/-
Case (3) of the take-back below a full leaf (bergdb 024-12, TP7;
`PutNewSegFullCase`): latest's `writerWP_put_newSegFullR` with the take-back's
(B), (C) and node facts. The new segment leaf, made empty before the cascade,
is no node of the cascade: (C) and the node facts of the cascade come from
`j2rest_cascade2` on the writer's nodes before the put, with the empty leaf left
out; the leaf is reached after the cascade as it is in the tree with its klong
put (`j2NE_start`), and the new segments end in `TakeJ2`
(`writerWP_putSegs_new_j2`).
-/
import SIS.Tree.TakeDeadPutFull
import SIS.Tree.GetNewSegFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1600000 in
/-- (3) below a full leaf, with the take-back's (B), (C) and node facts:
`writerWP_put_newSegFullR`'s premises on the nodes reached, the walk's order
(`OrdG`), `TakeJ2` before and B at or below the next id. -/
theorem writerWP_put_newSegFull_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 B : NodeId) (w : W)
    (hM : 2 ≤ c.p.M) (hpos : 0 < c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i →
        qn.leaf = false ∨ OrdG c (wNode c.p base w) w.top.rootKey)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ ¬ n.size + 1 < c.p.M)
    (hOrdG : OrdG c (wNode c.p base w) w.top.rootKey)
    (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' => TakeJ2 c base B w') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk0 :=
    segRootR_reach _ _ _ _ hwfR pre _ rk0 ReachS.root hrk
  have htkN : ∀ z zn, wNode c.p base w z = some zn → w.taken.contains z = false := by
    intro z zn hz
    cases hc : w.taken.contains z with
    | false => rfl
    | true => unfold wNode at hz; rw [hc] at hz; simp at hz
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hw2p : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  refine writerWP_putSegs_prefix_linkedS c base hvc (pre ++ c0 :: tail) (some h) (c0 :: tail)
    (by simp) _ pre w.top.rootKey rk0 w2
    (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by rw [hw2p]; simp) ?_
  intro w2' hr2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 tail htail]
  unfold setNode
  wpSimplify
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht2)
    (writerWP_descendLte_steps c0 c base hvc c.p.fuel rk0 w2' ht2))
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht2)) ?_
  intro L w3 ⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, hpre3⟩⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnone, hfull⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, hfull, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  -- the whole path from the space root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ c0 rk0 steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk0 steps hpf
    (fun mm hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
  -- the chain's nodes, klongs and contents
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
    exact PathLen.depth_unique hT _ _ _ a b
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hm : nodeAt w.top.rootKey P i ∈ (w.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hpsc _ hm _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w.top.rootKey P i = nodeAt rk0 steps j := by
        rw [hP, hj, nodeAt_append_right, hpse]
      have hvj : (nodeAt rk0 steps j, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps rk0 steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  -- ids
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hXlt : ∀ i, i ≤ P.length → nodeAt w.top.rootKey P i < w.next :=
    fun i hi => hsrcw3 _ (by rw [hlkX i hi]; rfl)
  -- the writer's path
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
  have hLlt : L < w.next := by rw [← hXD]; exact hXlt _ (Nat.le_refl _)
  have hLreach : TReach (wNode c.p base w) c.i w.top.rootKey L := by
    rw [← hXD]; exact hreachX _ (Nat.le_refl _)
  have hfree0 : w3.nodes.lookup w3.next = none := by
    cases h' : w3.nodes.lookup w3.next with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have hnone : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnone, (hbase z hz).1]
  have hyRW : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z :=
    fun z hz => not_reach_fresh _ c.i _ z hT (hfreshN z hz)
      (fun u c' _ hl => by have := hlinksAll u c' z hl; omega)
  -- after newKey and before appendKlongs
  have hrest : ∀ ws1 : W, ws1.nodes = w3.nodes ++ [(w3.next, (⟨true, []⟩ : KNode))] →
      ws1.next = w3.next + 2 → ws1.taken = w3.taken → ws1.vals = w3.vals → ws1.top = w3.top →
      ws1.path = w3.path →
      WriterWP pathSize c ws1 (fun a1 w' =>
        WriterWP (appendKlongs (a1 - 1) L [(c0, w3.next)]) c w' (fun _ w'' =>
          WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c w'' (fun _ w' =>
            TakeJ2 c base B w'))) := by
    intro ws1 g1 g2 g3 g4 g5 g6
    have hws1N : wNode c.p base ws1 = updN (wNode c.p base w) w.next ⟨true, []⟩ := by
      rw [wNode_append_updN c.p base w3 ws1 _ g1 g3 hfree0
        (by rw [hr03.2.2.1, hnext3]; exact hntake _ (Nat.le_refl _)), hr03.1, hnext3]
    rw [hnext3] at g1 g2 ⊢
    have hlen3 : w3.path.length - 1 = P.length := by rw [hp3']; simp
    simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
    rw [g6, hlen3]
    have hw1t : ws1.taken = w.taken := by rw [g3, hr03.2.2.1]
    have hw1v : ws1.vals = w.vals := by rw [g4, hr03.2.2.2.1]
    have hw1top : ws1.top = w.top := by rw [g5, hr03.2.1]
    have hmwf := hwfG _ _ hn
    have hmt := htimesG _ _ hn
    have hwnext : wNode c.p base w w.next = none := hfreshN _ (Nat.le_refl _)
    have hc0 : ∀ z, (c0, z) ∉ n.liveAt c.i := by
      intro z hz
      have hl := KNode.searchEq_live n c.i hmwf hmt c0
      rw [hnone] at hl
      rw [KNode.liveAt_of_times n c.i hmt] at hz
      have := lookup_some_of_mem (KNode.live_keys_nodup n) hz
      rw [← hl] at this
      cases this
    have hxv : w.next ∉ w.vals.map (·.1) := by
      intro hm
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      have := hidvals q hq
      omega
    -- the virtual tree reaches the new segment leaf
    have hJV := j2NE_start (wNode c.p base w)
      (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next))) c.i
      w.top.rootKey B (w.vals.map (·.1)) L w.next n c0 hpos (by unfold TakeJ2 at hJ; exact hJ) hn hLreach hmwf hmt hc0 hwnext hBn hxv
      (updN_self _ _ _) (by rw [updN_ne _ _ _ _ (by omega)]; exact updN_self _ _ _)
      (fun z h1 h2 => by rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2])
    have hordAll : ∀ i, 0 < i → i ≤ P.length → ChainOrd c (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) i :=
      fun i hi h2 hnr hql hsp c' z hz => hOrdG _ _ _ _ _ (hreachX (i - 1) (by omega))
        (hXN (i - 1) (by omega)) hql (hKP i hi h2).2 (hXN i h2) hnr hsp c' z hz
    have hTV : TreeOK (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
        (n.add c.i (.key c0 w.next))) c.i w.top.rootKey :=
      treeOK_newSeg (wNode c.p base w) _ c.i w.top.rootKey L w.next (w.next + 1) n ⟨true, []⟩ c0 0
        hT hLreach hn (hwfG _ _ hn) (htimesG _ _ hn) (updN_self _ _ _)
        (by rw [updN_ne _ _ _ _ (by omega)]; exact updN_self _ _ _)
        (fun c' z hc => absurd hc (KNode.empty_liveAt c.i c' z))
        (fun z h1 h2 => by rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2])
        (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (by omega)
        (fun z hz u c' _ hl => by
          have := hlinksAll u c' z hl
          rcases hz with hz | hz <;> omega)
    have hchain := writerWP_appendKlongs_chainGRV c base w3.path 0 P.length
      (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i _ h2 => hpX i h2)
      (fun i h1 h2 => hpK i h1 h2)
      (fun i h1 h2 => (hKP i h1 h2).2)
      (fun i h1 h2 hnr hql c' z hz hc => hrangeG _ _ _ _ _ (hreachX (i - 1) (by omega))
        (hXN (i - 1) (by omega)) hql (hKP i h1 h2).2 (hXN i h2) hnr c' z hz hc)
      (fun i _ h2 hnr hsp => hlenG _ _ (hreachX i h2) (hXN i h2) hnr hsp)
      (fun i _ h2 => hwfG _ _ (hXN i h2))
      (fun i _ h2 => htimesG _ _ (hXN i h2))
      (Or.inr rfl)
      (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
      (fun i _ h2 hnr hsp => by
        rcases Nat.eq_zero_or_pos i with h0 | hi
        · exact Or.inl h0
        · refine Or.inr ⟨hi, ?_⟩
          rcases hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _ (hreachX (i - 1) (by omega))
            (hXN (i - 1) (by omega)) (hKP i hi h2).2 with h | hord
          · exact Or.inl h
          · refine Or.inr (fun _ i' h1' h2' hnr' hql' hsp' c' z hz => ?_)
            exact hord _ _ _ _ _ (hreachX (i' - 1) (by omega)) (hXN (i' - 1) (by omega)) hql'
              (hKP i' (by omega) (by omega)).2 (hXN i' (by omega)) hnr' hsp' c' z hz)
      P.length (by omega) ws1 [(c0, w.next)] (Or.inl ⟨c0, w.next, rfl⟩)
      (by intro q hq; simp at hq; rw [hq, g2]; simp)
      g6
      (fun i _ h2 => ⟨by
          rw [g1, lookup_append_single_ne _ _ _ _ (by have := hXlt i (by omega); omega)]
          exact hlkX i (by omega),
        by rw [hw1t]; exact htkN _ _ (hXN i (by omega))⟩)
      (by rw [hws1N, hw1top]; exact treeOK_updN_unreach _ c.i _ _ _ hT (hyRW _ (Nat.le_refl _)))
      (fun i _ h2 => by
        rw [hws1N, hw1top]
        obtain ⟨a, ha⟩ := (hreachX i (by omega)).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
      (by
        intro z hz
        rw [g2] at hz
        refine ⟨?_, ?_, (hbase z (by omega)).1⟩
        · rw [g1, lookup_append_single_ne _ _ _ _ (by omega)]
          cases h' : w3.nodes.lookup z with
          | none => rfl
          | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
        · rw [hw1t]; exact hntake z (by omega))
      (by
        intro u c' z hl
        rw [hws1N] at hl
        rw [g2]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          exact absurd hc (KNode.empty_liveAt c.i c' z)
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun _ _ => by show ws1.top.rootKey = nodeAt w.top.rootKey P 0; rw [hw1top, nodeAt_zero])
      (by
        intro z zn hz
        rw [hws1N] at hz
        by_cases hzn : z = w.next
        · rw [hzn, updN_self] at hz; cases hz; rfl
        · rw [updN_ne _ _ _ _ hzn] at hz; exact hwfG z zn hz)
      (by
        rw [hws1N, hw1top]
        simp only [Nat.zero_add, hXD, hn, Option.getD_some]
        exact hTV)
    have htake := writerWP_appendKlongs_take c base w3.path 0 P.length
      (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i _ h2 => hpX i h2)
      (fun i h1 h2 => hpK i h1 h2)
      (fun i h1 h2 => (hKP i h1 h2).2)
      (fun i h1 h2 hnr hql c' z hz hc => hrangeG _ _ _ _ _ (hreachX (i - 1) (by omega))
        (hXN (i - 1) (by omega)) hql (hKP i h1 h2).2 (hXN i h2) hnr c' z hz hc)
      (fun i _ h2 hnr hsp => hlenG _ _ (hreachX i h2) (hXN i h2) hnr hsp)
      (fun i _ h2 => hwfG _ _ (hXN i h2))
      (fun i _ h2 => htimesG _ _ (hXN i h2))
      (Or.inr rfl)
      (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
      (fun i _ h2 hnr hsp => by
        rcases Nat.eq_zero_or_pos i with h0 | hi
        · exact Or.inl h0
        · refine Or.inr ⟨hi, ?_⟩
          rcases hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _ (hreachX (i - 1) (by omega))
            (hXN (i - 1) (by omega)) (hKP i hi h2).2 with h | hord
          · exact Or.inl h
          · refine Or.inr (fun _ i' h1' h2' hnr' hql' hsp' c' z hz => ?_)
            exact hord _ _ _ _ _ (hreachX (i' - 1) (by omega)) (hXN (i' - 1) (by omega)) hql'
              (hKP i' (by omega) (by omega)).2 (hXN i' (by omega)) hnr' hsp' c' z hz)
      P.length (by omega) ws1 [(c0, w.next)] (Or.inl ⟨c0, w.next, rfl⟩)
      (by intro q hq; simp at hq; rw [hq, g2]; simp)
      g6
      (fun i _ h2 => ⟨by
          rw [g1, lookup_append_single_ne _ _ _ _ (by have := hXlt i (by omega); omega)]
          exact hlkX i (by omega),
        by rw [hw1t]; exact htkN _ _ (hXN i (by omega))⟩)
      (by rw [hws1N, hw1top]; exact treeOK_updN_unreach _ c.i _ _ _ hT (hyRW _ (Nat.le_refl _)))
      (fun i _ h2 => by
        rw [hws1N, hw1top]
        obtain ⟨a, ha⟩ := (hreachX i (by omega)).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
      (by
        intro z hz
        rw [g2] at hz
        refine ⟨?_, ?_, (hbase z (by omega)).1⟩
        · rw [g1, lookup_append_single_ne _ _ _ _ (by omega)]
          cases h' : w3.nodes.lookup z with
          | none => rfl
          | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
        · rw [hw1t]; exact hntake z (by omega))
      (by
        intro u c' z hl
        rw [hws1N] at hl
        rw [g2]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          exact absurd hc (KNode.empty_liveAt c.i c' z)
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun _ _ => by show ws1.top.rootKey = nodeAt w.top.rootKey P 0; rw [hw1top, nodeAt_zero])
      (by
        intro z zn hz
        rw [hws1N] at hz
        by_cases hzn : z = w.next
        · rw [hzn, updN_self] at hz; cases hz; rfl
        · rw [updN_ne _ _ _ _ hzn] at hz; exact hwfG z zn hz)
      (by
        rw [hws1N, hw1top]
        simp only [Nat.zero_add, hXD, hn, Option.getD_some]
        exact hTV)
      (by
        intro cc u hm
        simp only [Nat.zero_add, hXD, hn, Option.getD_some, List.foldl_cons, List.foldl_nil] at hm ⊢
        left
        exact ⟨cc, KNode.add_liveAt_keep n c0 w.next c.i hmwf hmt cc u hm
          (fun he => hc0 u (he ▸ hm))⟩)
      (fun i h1 h2 => hordAll i h1 (by omega)) hpos
      (by
        intro q qn hq hm
        rw [hws1N] at hq
        rw [hws1N, hw1top]
        by_cases hqx : q = w.next
        · rw [hqx, updN_self] at hq; cases hq; simp at hm
        · rw [updN_ne _ _ _ _ hqx] at hq
          obtain ⟨a, ha⟩ := (hJ.1 q qn hq hm).pathLen
          exact tReach_updN_of_short _ c.i _ _ _ a _ ha
            (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
    have hshape := writerWP_appendKlongs_chainShape c w3.path 0 P.length
      (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i _ h2 => hpX i h2)
      (fun i h1 h2 => hpK i h1 h2)
      (fun i h1 h2 => (hKP i h1 h2).2)
      (fun i h1 h2 hnr hql c' z hz hc => hrangeG _ _ _ _ _ (hreachX (i - 1) (by omega))
        (hXN (i - 1) (by omega)) hql (hKP i h1 h2).2 (hXN i h2) hnr c' z hz hc)
      (fun i _ h2 hnr hsp => hlenG _ _ (hreachX i h2) (hXN i h2) hnr hsp)
      hordAll
      (fun i _ h2 => htimesG _ _ (hXN i h2))
      (Or.inr rfl)
      (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
      P.length (by omega) ws1 [(c0, w.next)] (Or.inl ⟨c0, w.next, rfl⟩) (by simp) g6
      (fun i _ h2 => ⟨by
          rw [g1, lookup_append_single_ne _ _ _ _ (by have := hXlt i (by omega); omega)]
          exact hlkX i (by omega),
        by have := hXlt i (by omega); rw [g2]; omega⟩)
      (by
        intro z hz
        rw [g2] at hz
        rw [g1, lookup_append_single_ne _ _ _ _ (by omega)]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
    have hcached := writerWP_appendKlongs_cached P.length L [(c0, w.next)] c ws1
    simp only [Nat.zero_add, hXD, hn, Option.getD_some] at hchain htake hshape
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hchain htake) hshape) hcached) ?_
    rintro _ wf1 ⟨⟨⟨⟨hT1, ⟨hftop, hft, hfpath, hfnext, hfv⟩, hframe1, hreach1, hW1, hR1, hab1, hRK, hRN⟩,
      hTt1⟩, hSh1⟩, hca1⟩
    have hlkc : wf1.nodes.lookup w.next = some ⟨true, []⟩ := by
      rw [hframe1 w.next (by omega) (fun i _ h2 he => by have := hXlt i h2; omega), g1]
      exact lookup_append_single_self _ _ _ (by rw [← hnext3]; exact hfree0)
    have htkc : wf1.taken.contains w.next = false := by
      rw [hft, hw1t]; exact hntake _ (Nat.le_refl _)
    have hfreshc : ∀ z, wf1.next ≤ z → wf1.nodes.lookup z = none ∧ wf1.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ wf1.vals.lookup z = none := by
      intro z hz
      refine ⟨?_, by rw [hft, hw1t]; exact hntake z (by omega), (hbase z (by omega)).1,
        (hbase z (by omega)).2, by rw [hfv, hw1v]; exact hvalnone z (by omega)⟩
      rw [hab1 z hz, g1, lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    have hN1x : wNode c.p base wf1 w.next = some ⟨true, []⟩ := by
      simp only [wNode, htkc, Bool.false_eq_true, ↓reduceIte, hlkc]
    have hvf : wf1.vals = w.vals := by rw [hfv, hw1v]
    -- the cascade's node facts with the empty leaf left out
    let N1m : NodeId → Option KNode := fun z => if z = w.next then none else wNode c.p base wf1 z
    have hm : ∀ q, q ≠ w.next → N1m q = wNode c.p base wf1 q := fun q hq => by
      simp only [N1m, hq, ↓reduceIte]
    have hJw : J2N (wNode c.p base w) c.i w.top.rootKey B (w.vals.map (·.1)) := by
      unfold TakeJ2 at hJ; exact hJ
    obtain ⟨_, hD, hO, hS, hMs, hV⟩ := hJw
    have hother : ∀ z, z < ws1.next → (∀ i, 0 ≤ i → i ≤ P.length → z ≠ nodeAt w.top.rootKey P i) →
        N1m z = wNode c.p base w z := by
      intro z hz hnc
      by_cases hzx : z = w.next
      · simp only [N1m, hzx, ↓reduceIte, hwnext]
      · rw [hm z hzx]
        have : wNode c.p base wf1 z = wNode c.p base ws1 z := by
          simp only [wNode, hft, hframe1 z hz hnc]
        rw [this, hws1N, updN_ne _ _ _ _ hzx]
    have hshapeJ : ∀ z zn, N1m z = some zn →
        (ws1.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ P.length ∧ z = nodeAt w.top.rootKey P i) →
        CascadeShapeJ2 (wNode c.p base w) c.i B (w.vals.map (·.1)) (fun i => nodeAt w.top.rootKey P i)
          (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) 0 P.length z zn := by
      intro z zn hzn hz
      have hzx : z ≠ w.next := by
        intro he
        simp only [N1m, he, ↓reduceIte] at hzn
        cases hzn
      rw [hm z hzx] at hzn
      have htz : wf1.taken.contains z = false := by
        rw [hft, hw1t]
        rcases hz with hz | ⟨i, _, b, rfl⟩
        · exact hntake z (by omega)
        · exact htkN _ _ (hXN i b)
      have hlk : wf1.nodes.lookup z = some zn := by
        unfold wNode at hzn
        rw [htz] at hzn
        simp only [Bool.false_eq_true, ↓reduceIte] at hzn
        cases hl : wf1.nodes.lookup z with
        | some m => rw [hl] at hzn; exact hzn
        | none =>
          exfalso
          rw [hl] at hzn
          rcases hz with hz | ⟨i, a, b, rfl⟩
          · rw [(hbase z (by omega)).1] at hzn; cases hzn
          · have := hca1 _ (by
              rw [g1, lookup_append_single_ne _ _ _ _ (by have := hXlt i b; omega), hlkX i b]; rfl)
            rw [hl] at this; cases this
      obtain ⟨_, _, _, hsh⟩ := hSh1
      exact cascadeShapeJ2_of c (wNode c.p base w) B _ _ _ _ 0 P.length [(c0, w.next)] ws1.next hS hMs
        (fun i _ b => hXN i b) (fun i _ b => htimesG _ _ (hXN i b)) (by omega) (by simp)
        (by
          intro q hq y hy
          simp only [List.mem_singleton] at hq
          subst hq
          simp only [hXD, hn, Option.getD_some] at hy
          exact absurd hy (hc0 y))
        z zn hz (hsh z zn hlk hz)
    obtain ⟨hD1, hO1, hS1, hM1, hV1⟩ := j2rest_cascade2 (wNode c.p base w) N1m c.i w.top.rootKey B
      (w.vals.map (·.1)) (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) 0 P.length ws1.next hpos hT hD hO
      hS hMs hV (fun i _ b => hXN i b) (fun i _ b => hwfG _ _ (hXN i b))
      (fun i _ b => htimesG _ _ (hXN i b)) (fun i _ b => hreachX i b)
      (by
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        have := hidvals q hq
        omega)
      hother hshapeJ
    have hJE : J2NE (wNode c.p base wf1) c.i wf1.top.rootKey B (wf1.vals.map (·.1)) w.next := by
      rw [hvf]
      refine ⟨hTt1, ?_, ?_, ?_, ?_, ?_, hN1x, ?_, hBn⟩
      · intro q qn hq
        by_cases hqx : q = w.next
        · rw [hqx, hN1x] at hq; cases hq
          intro i cv y hi; simp at hi
        · exact hD1 q qn (by rw [hm q hqx]; exact hq)
      · intro q qn hq cv y hk
        by_cases hqx : q = w.next
        · rw [hqx, hN1x] at hq; cases hq; simp [prefixAt] at hk
        · exact hO1 q qn (by rw [hm q hqx]; exact hq) cv y hk
      · intro q qn hq hqB
        by_cases hqx : q = w.next
        · omega
        · exact hS1 q qn (by rw [hm q hqx]; exact hq) hqB
      · intro q qn hq hqB hqx
        exact hM1 q qn (by rw [hm q hqx]; exact hq) hqB
      · intro y hy
        have hyx : y ≠ w.next := fun he => hxv (he ▸ hy)
        rw [← hm y hyx]; exact hV1 y hy
      · refine hRK hordAll w.next ?_ (fun i _ h2 he => by have := hXlt i h2; omega)
        rw [hws1N, hw1top]
        simp only [List.foldl_cons, List.foldl_nil]
        exact hJV.2.2.2.2.2.2.2.1
    exact writerWP_putSegs_new_j2 c base (pre ++ c0 :: tail) h hM hfuel hpos B tail htail wf1 w.next
      hlkc htkc (by omega) hfreshc (by omega) hJE
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl rfl

/-- (3) below a full leaf keeps `J2At`, from `PutInv`, B at or below the next
id and the walk's ranges, for 2 ≤ splitAbove and runs with their links. -/
theorem opJ2Case_putNewSegFull (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    OpJ2CaseOK p R S PutNewSegFullCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre _ hS hJ hP
  obtain ⟨pre, c0, tail, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  have hG := putInvG_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ (hSR ts tx w hS) hI.times
  refine writerWP_mono (writerWP_put_newSegFull_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0
    h tail hat.1 rk0 tx.base w hM (by simp [ctxOf]) hat.2.1 (hI.pathUntaken _) hI.ids hI.fresh hI.wf
    hI.times hI.tree (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl)
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ (hSR ts tx w hS) hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd)
    (newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      ¬ m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩)
    hOrd hJ (hSB ts tx w hS)) ?_
  intro _ w' h' _
  exact h'

/-! ## The assembly with case (3) -/

end SIS.Tree
