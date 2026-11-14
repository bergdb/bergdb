import SIS.Tree.GetPutPath
import SIS.Tree.RangeChainG
import SIS.Tree.RangePut
import SIS.Tree.RangeOps
import SIS.Tree.RangeCollapse
import SIS.Tree.GetDelCascade
import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The put and the delete along the whole access path from the space root keep
the walk's ranges (bergdb 024-12, TP10; `RangeOrder`): prover latest's
rules of the put and the delete along it, with the ranges, on
`writerWP_appendKlongs_chainGRange` from 0, which also takes a space split of
the space root (no `hspaceG`). -/

set_option maxHeartbeats 1600000 in
/-- A put of a key into a full leaf, with the cascade along the whole access
path from the space root (the premises of prover latest's rule but `hkey`,
`hnoval`, `hspaceG` and `huniq`), keeps the walk's ranges. -/
theorem rangeOrder_put_accessPath (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
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
    (hfullL : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
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
  refine writerWP_putSegs_prefix_linked c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by rw [hw2p]; simp) ?_
  intro w2' hr2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, hpre3⟩⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the whole path from the space root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ cv rk steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk steps hpf
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
      have hXj : nodeAt w.top.rootKey P i = nodeAt rk steps j := by
        rw [hP, hj, nodeAt_append_right, hpse]
      have hvj : (nodeAt rk steps j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps rk steps j h0 hjl
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
  -- the leaf is full: the put goes to appendKlongs
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ _ c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) &&
      !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    have hf := hfullL L n hvisL hn hnl
    cases hd' : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hf ⟨hlt, hd'⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hlen3 : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen3]
  -- the state before appendKlongs: w3 with the new value
  generalize hws : ({ w3 with
    made := w3.made ++ [⟨w3.next, 0, true⟩]
    vals := w3.vals ++ [(w3.next, h)]
    next := w3.next + 2 } : W) = ws
  have hwsn : ws.nodes = w3.nodes := by rw [← hws]
  have hwst : ws.taken = w.taken := by rw [← hws]; exact hr03.2.2.1
  have hwsv : ws.vals = w.vals ++ [(w.next, h)] := by rw [← hws]; simp only; rw [hr03.2.2.2.1, hnext3]
  have hwsx : ws.next = w.next + 2 := by rw [← hws]; simp only; rw [hnext3]
  have hwsp : ws.path = w3.path := by rw [← hws]
  have hwstop : ws.top = w.top := by rw [← hws]; exact hr03.2.1
  have hwsN : wNode c.p base ws = wNode c.p base w := by
    rw [← hr03.1]
    funext z
    simp only [wNode, hwsn, hwst, hr03.2.2.1]
  have hchain := writerWP_appendKlongs_chainGRange c base w3.path 0 P.length
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
    P.length (by omega) ws [(cv, w3.next)] (Or.inl ⟨cv, w3.next, rfl⟩)
    (by intro q hq; simp at hq; rw [hq, hwsx, hnext3]; simp)
    hwsp
    (fun i _ h2 => ⟨by rw [hwsn]; exact hlkX i (by omega),
      by rw [hwst]; exact htkN _ _ (hXN i (by omega))⟩)
    (by rw [hwsN, hwstop]; exact hT)
    (fun i _ h2 => by rw [hwsN, hwstop]; exact hreachX i (by omega))
    (by
      intro z hz
      rw [hwsx] at hz
      refine ⟨?_, ?_, (hbase z (by omega)).1⟩
      · rw [hwsn]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
      · rw [hwst]; exact hntake z (by omega))
    (by
      intro u c' z hl
      rw [hwsN] at hl
      have := hlinksAll u c' z hl
      rw [hwsx]; omega)
    (fun _ => by show ws.top.rootKey = nodeAt w.top.rootKey P 0; rw [hwstop, nodeAt_zero])
    (by
      rw [hwsN, hwstop]
      simp only [Nat.zero_add, hXD, hn, Option.getD_some, hnext3]
      exact treeOK_addKey (wNode c.p base w) _ c.i w.top.rootKey L w.next n cv hT hLreach hn
        (hwfG _ _ hn) (htimesG _ _ hn) (updN_self _ _ _) (fun x hx => updN_ne _ _ _ _ hx)
        (by
          simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            (hbase w.next (Nat.le_refl _)).1]
          cases h' : w.nodes.lookup w.next with
          | none => rfl
          | some _ => have := hidn w.next (by rw [h']; rfl); omega)
        (fun u c' _ hl => by have := hlinksAll u c' w.next hl; omega))
    (by
      rw [hwsN, hwstop]
      simp only [Nat.zero_add, hXD, hn, Option.getD_some, hnext3]
      exact rangeOrder_leafPut (wNode c.p base w) c.i w.top.rootKey hR hT hwfG htimesG c.p.fuel pre cv
        rk L w.next n hrk hvisL hn hnl
        (by
          simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            (hbase w.next (Nat.le_refl _)).1]
          cases h' : w.nodes.lookup w.next with
          | none => rfl
          | some _ => have := hidn w.next (by rw [h']; rfl); omega))
  simp only [Nat.zero_add, hXD, hn, Option.getD_some] at hchain
  refine writerWP_mono hchain ?_
  intro _ wf ⟨_, _, _, _, hRf⟩
  exact hRf

end SIS.Tree
