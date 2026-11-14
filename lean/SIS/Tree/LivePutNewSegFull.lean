/-
`QLive` of a put that makes new segments below a full leaf (bergdb 024-12,
TP7, case (3c)). The leaf's klong to the new segment leaf v goes up through
the access path's cascade while v is still empty, so the tree with the klong
put meets `LiveEdges` but for the links to v, which only the leaf has
(`liveEdgesX_newSegLeaf`). The cascade keeps that (`writerWP_appendKlongs_chainGLX`
with E = {v}); putSegs then fills v and makes the leaves below it, and
`LiveEdges` holds again (`liveEdges_fillNewSegs`). The setup is
`writerWP_put_newSegFullR`'s, whose cascade (`writerWP_appendKlongs_chainGRV`)
gives that the nodes reached after it are below the next id.
-/
import SIS.Tree.GetNewSegFull
import SIS.Tree.LivePutFull
import SIS.Tree.GetOpCases
import SIS.Tree.HeightsRun
import SIS.Tree.WriterTreeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The tree of (3c) with the leaf's klong put, before the cascade: a leaf L of
a tree that meets `LiveEdges` gets a klong to a fresh empty leaf v that no
node reached names. It meets `LiveEdges` but for the links to v, which L
alone has. -/
theorem liveEdgesX_newSegLeaf (p : Params) (N : NodeId → Option KNode) (t : Time)
    (r L v : NodeId) (n : KNode) (c0 : Nat) (h : LiveEdges p N t r) (hn : N L = some n)
    (hnl : n.leaf = true) (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hv : N v = none) (hrv : r ≠ v)
    (hno : ∀ u un c, TReach N t r u → N u = some un → (c, v) ∉ un.liveAt t) :
    LiveEdgesX p (updN (updN N v ⟨true, []⟩) L (n.add t (.key c0 v))) t r (· = v) := by
  have hLv : L ≠ v := fun he => by rw [he, hv] at hn; cases hn
  have hVo : ∀ x, x ≠ L → x ≠ v →
      updN (updN N v ⟨true, []⟩) L (n.add t (.key c0 v)) x = N x :=
    fun x h1 h2 => by rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2]
  have hVv : updN (updN N v ⟨true, []⟩) L (n.add t (.key c0 v)) v = some ⟨true, []⟩ := by
    rw [updN_ne _ _ _ _ (Ne.symm hLv)]; exact updN_self _ _ _
  have hlen := KNode.add_key_liveAt_length n t c0 v hw ht
  have hl' := KNode.add_leaf n t (.key c0 v)
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · by_cases hrL : r = L
    · rw [hrL, updN_self] at hrn
      cases hrn
      refine ⟨fun _ => by rw [hl']; exact hnl, fun hl => ?_⟩
      rw [hl', hnl] at hl; cases hl
    · rw [hVo r hrL hrv] at hrn
      exact h.1 rn hrn
  · rcases tReach_newSegStepN N t r L v n c0 hn hw ht hv hLv u hu with hu' | hu'
    · by_cases huL : u = L
      · rw [huL, updN_self] at hun
        cases hun
        rw [huL] at hu'
        rcases KNode.add_key_liveAt_mem n t c0 v hw ht c y hc with ⟨_, hy⟩ | ⟨_, hc'⟩
        · exact ⟨fun hne => absurd hy hne, fun _ => by rw [hl']; exact hnl⟩
        · have hyv : y ≠ v := fun he => hno L n c hu' hn (by rw [← he]; exact hc')
          refine ⟨fun _ => ?_, fun he => absurd he hyv⟩
          by_cases hyL : y = L
          · rw [hyL, updN_self] at hyn
            cases hyn
            rw [hyL] at hc'
            exact childOK_grow p t n _ n _ (h.2 L n c L n hu' hn hc' hn) hl' hl' hlen
          · rw [hVo y hyL hyv] at hyn
            exact childOK_grow p t n _ yn yn (h.2 L n c y yn hu' hn hc' hyn) hl' rfl (Nat.le_refl _)
      · have huv : u ≠ v := by
          intro he
          rw [he, hVv] at hun
          cases hun
          exact KNode.empty_liveAt t c y hc
        rw [hVo u huL huv] at hun
        have hyv : y ≠ v := fun he => hno u un c hu' hun (by rw [← he]; exact hc)
        refine ⟨fun _ => ?_, fun he => absurd he hyv⟩
        by_cases hyL : y = L
        · rw [hyL, updN_self] at hyn
          cases hyn
          rw [hyL] at hc
          exact childOK_grow p t un un n _ (h.2 u un c L n hu' hun hc hn) rfl hl' hlen
        · rw [hVo y hyL hyv] at hyn
          exact h.2 u un c y yn hu' hun hc hyn
    · rw [hu', hVv] at hun
      cases hun
      exact absurd hc (KNode.empty_liveAt t c y)

/-- After the cascade of (3c), putSegs fills the excepted leaf v and makes new
nodes from B on: v and the new nodes are leaves with a live klong that name
new nodes only; the other nodes below B are kept, and the nodes reached
before are below B. `LiveEdges` holds. -/
theorem liveEdges_fillNewSegs (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time)
    (r v B : NodeId) (h : LiveEdgesX p N1 t r (· = v))
    (hlt : ∀ x, TReach N1 t r x → x < B) (hrv : r ≠ v) (hv1 : ∃ m, N1 v = some m)
    (hag : ∀ z, z < B → z ≠ v → N2 z = N1 z)
    (hnew : ∀ z m, (z = v ∨ B ≤ z) → N2 z = some m →
      m.leaf = true ∧ m.liveAt t ≠ [] ∧ ∀ c y, (c, y) ∈ m.liveAt t → B ≤ y) :
    LiveEdges p N2 t r := by
  have hrB := hlt r TReach.root
  have hok : ∀ un yn : KNode, un.leaf = true → yn.leaf = true → yn.liveAt t ≠ [] →
      ChildOK p t un yn :=
    fun un yn h1 h2 h3 => ⟨h3, fun _ h4 => (by rw [h2] at h4; cases h4),
      fun h4 => (by rw [h1] at h4; cases h4)⟩
  have hreach : ∀ u, TReach N2 t r u → TReach N1 t r u ∨ B ≤ u := by
    intro u hu
    induction hu with
    | root => exact Or.inl TReach.root
    | @link u c y _ hl ih =>
      obtain ⟨m, hm, hc⟩ := hl
      rcases ih with ih | ih
      · by_cases huv : u = v
        · exact Or.inr ((hnew u m (Or.inl huv) hm).2.2 c y hc)
        · rw [hag u (hlt u ih) huv] at hm
          exact Or.inl (TReach.link ih ⟨m, hm, hc⟩)
      · exact Or.inr ((hnew u m (Or.inr ih) hm).2.2 c y hc)
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · rw [hag r hrB hrv] at hrn
    exact h.1 rn hrn
  · rcases hreach u hu with hu1 | huB
    · by_cases huv : u = v
      · obtain ⟨hl, _, hy⟩ := hnew u un (Or.inl huv) hun
        obtain ⟨hyl, hyne, _⟩ := hnew y yn (Or.inr (hy c y hc)) hyn
        exact hok un yn hl hyl hyne
      · have hun1 : N1 u = some un := by rw [← hag u (hlt u hu1) huv]; exact hun
        have hyB := hlt y (TReach.link hu1 ⟨un, hun1, hc⟩)
        by_cases hyv : y = v
        · obtain ⟨m, hm⟩ := hv1
          have hul := (h.2 u un c y m hu1 hun1 hc (by rw [hyv]; exact hm)).2 hyv
          obtain ⟨hyl, hyne, _⟩ := hnew y yn (Or.inl hyv) hyn
          exact hok un yn hul hyl hyne
        · rw [hag y hyB hyv] at hyn
          exact (h.2 u un c y yn hu1 hun1 hc hyn).1 hyv
    · obtain ⟨hl, _, hy⟩ := hnew u un (Or.inr huB) hun
      obtain ⟨hyl, hyne, _⟩ := hnew y yn (Or.inr (hy c y hc)) hyn
      exact hok un yn hl hyl hyne

set_option maxHeartbeats 1600000 in
/-- The put of (3c) keeps `LiveEdges`, with the merges' thresholds: on
`writerWP_put_newSegFullR`'s premises for the tree. -/
theorem liveEdges_put_newSegFull (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hM : 2 ≤ c.p.M)
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
      n.searchEq c.i c0 = none ∧ ¬ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      MergeParamsOK c.p → LiveEdges c.p (wNode c.p base w) c.i w.top.rootKey →
      LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  -- after newKey and before appendKlongs
  have hrest : ∀ ws1 : W, ws1.nodes = w3.nodes ++ [(w3.next, (⟨true, []⟩ : KNode))] →
      ws1.next = w3.next + 2 → ws1.taken = w3.taken → ws1.vals = w3.vals → ws1.top = w3.top →
      ws1.path = w3.path →
      WriterWP pathSize c ws1 (fun a1 w' =>
        WriterWP (appendKlongs (a1 - 1) L [(c0, w3.next)]) c w' (fun _ w'' =>
          WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c w'' (fun _ w' =>
            MergeParamsOK c.p → LiveEdges c.p (wNode c.p base w) c.i w.top.rootKey →
            LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey))) := by
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
    -- the virtual tree: the leaf with the klong to the new segment leaf
    have hNL : wNode c.p base w L = some n := hn
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
    have hchainX := writerWP_appendKlongs_chainGLX c base w3.path 0 P.length
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
      (· = w.next) (fun i _ h2 (he : nodeAt w.top.rootKey P i = w.next) => by have := hXlt i h2; omega)
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
      (fun _ => by show ws1.top.rootKey = nodeAt w.top.rootKey P 0; rw [hw1top, nodeAt_zero])
      (fun z (hz : z = w.next) => by omega)
      (by
        rw [hws1N, hw1top]
        simp only [Nat.zero_add, hXD, hn, Option.getD_some]
        exact hTV)
    simp only [Nat.zero_add, hXD, hn, Option.getD_some] at hchain hchainX
    refine writerWP_mono (writerWP_and hchain hchainX) ?_
    intro _ wf1 ⟨⟨_, ⟨hftop, hft, _, hfnext, hfv⟩, hframe1, hreach1, _, _, hab1, _⟩, ⟨_, _, _, _, hLX⟩⟩
    rw [hnext3] at hfree0
    have hlkc : wf1.nodes.lookup w.next = some ⟨true, []⟩ := by
      rw [hframe1 w.next (by omega) (fun i _ h2 he => by have := hXlt i h2; omega), g1]
      exact lookup_append_single_self _ _ _ hfree0
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
    have hRw : ∀ z, TReach (wNode c.p base w) c.i w.top.rootKey z → z < w.next := by
      intro z hz
      induction hz with
      | root => exact hidr
      | link _ hl _ => exact hlinksAll _ _ _ hl
    have hRlt1 : ∀ z, TReach (wNode c.p base wf1) c.i wf1.top.rootKey z → z < wf1.next := by
      intro z hz
      rcases hreach1 z hz with h1 | ⟨_, h1⟩
      · rw [hws1N, hw1top] at h1
        simp only [List.foldl_cons, List.foldl_nil] at h1
        rcases tReach_newSegStepN (wNode c.p base w) c.i w.top.rootKey L w.next n c0 hn (hwfG _ _ hn)
          (htimesG _ _ hn) (hfreshN _ (Nat.le_refl _)) (by omega) z h1 with h2 | h2
        · have := hRw z h2; omega
        · omega
      · exact h1
    have hxr : w.next ≠ wf1.top.rootKey := by
      rcases hftop with h' | ⟨_, h'⟩
      · rw [h', hw1top]; omega
      · rw [g2] at h'; omega
    have hw1e : wNode c.p base wf1 w.next = some ⟨true, []⟩ := by
      simp only [wNode, htkc, Bool.false_eq_true, ↓reduceIte, hlkc]
    refine writerWP_mono (writerWP_and (writerWP_putSegs_new_shape c base (pre ++ c0 :: tail) h hM
      hfuel tail htail wf1 w.next hlkc htkc (by omega) hfreshc)
      (writerWP_putSegs_new_live c base (pre ++ c0 :: tail) h hM hfuel tail htail wf1 w.next hlkc
        htkc (by omega) hfreshc)) ?_
    rintro _ wf ⟨⟨k1, k2, _, k4, _, k7⟩, ⟨_, _, _, _, _, k8⟩⟩ hp hL
    have hLV := liveEdgesX_newSegLeaf c.p (wNode c.p base w) c.i w.top.rootKey L w.next n c0 hL hn
      hnl (hwfG _ _ hn) (htimesG _ _ hn) (hfreshN _ (Nat.le_refl _)) (by omega)
      (fun u un cc _ hun hcc => by have := hlinksAll u cc w.next ⟨un, hun, hcc⟩; omega)
    have hL1 := hLX hp (by
      rw [hws1N, hw1top]
      simp only [List.foldl_cons, List.foldl_nil]
      exact hLV)
    rw [k2]
    refine liveEdges_fillNewSegs c.p (wNode c.p base wf1) (wNode c.p base wf) c.i wf1.top.rootKey
      w.next wf1.next hL1 hRlt1 (Ne.symm hxr) ⟨_, hw1e⟩
      (fun z h2 h1 => by simp only [wNode, k1, k4 z h2 h1]) ?_
    intro z m hz hm
    have hzw : w.next ≤ z := by rcases hz with hz | hz <;> omega
    have hzt : wf.taken.contains z = false := by rw [k1, hft, hw1t]; exact hntake z hzw
    have hlk : wf.nodes.lookup z = some m := by
      unfold wNode at hm
      rw [hzt] at hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hm
      cases h' : wf.nodes.lookup z with
      | some m' => rw [h'] at hm; exact hm
      | none => rw [h'] at hm; simp only at hm; rw [(hbase z hzw).1] at hm; cases hm
    obtain ⟨hl, hy⟩ := k7 z m hz hlk
    exact ⟨hl, k8 z m hz hlk, hy⟩

  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl rfl

/-- (3c), `LiveCounts`, with the merges' thresholds and runs with their links:
`liveEdges_put_newSegFull` on `treeCase_putNewSegFull`'s premises, through the
equivalence of `LiveCounts` and `LiveEdges`. -/
theorem liveCase_putNewSegFull (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hp : MergeParamsOK p) :
    OpCaseOK p R (QLive p) PutNewSegFullCase := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hI hRO hP
  obtain ⟨pre, c0, tail, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  have hG := putInvG_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times
  refine writerWP_mono (liveEdges_put_newSegFull (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0
    h tail hat.1 rk0 w hM hat.2.1 (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl)
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd)
    (newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      ¬ m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩)) ?_
  intro _ w' hL _ hC
  exact liveCounts_of_edges p _ _ _ (hL hp (edges_of_liveCounts p _ _ _ hC))

end SIS.Tree
