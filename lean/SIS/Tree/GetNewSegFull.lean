import SIS.Tree.GetPutPath
import SIS.Tree.GetNewSegs

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put of a key whose next segment has no tree yet, into a full leaf (bergdb
024-12, TP10; `OpGetOK`'s rules): the leaf's klong to the new segment leaf goes
up through a cascade of splits (`writerWP_appendKlongs_chainGRV`), then the new
segment leaves are made below it (`writerWP_putSegs_new`). A reader reaches the
new segment leaf only through the key's prefix; its tree changes nothing else. -/

/-- Paths in N are paths in N' when N's links from the nodes it reaches are N''s. -/
theorem PathLen.of_sublinks (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ u c z, TReach N t r u → TLink N t u c z → TLink N' t u c z) :
    ∀ z k, PathLen N t r z k → PathLen N' t r z k := by
  intro z k hz
  induction hz with
  | root => exact PathLen.root
  | link hp hl ih => exact PathLen.link ih (h _ _ _ hp.reach hl)

/-- An empty segment leaf has no live klong. -/
theorem KNode.empty_liveAt (t : Time) (c : Nat) (z : NodeId) :
    (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
  intro hc
  rw [KNode.liveAt_of_times _ t (by simp)] at hc
  have := lookup_some_of_mem (KNode.live_keys_nodup _) hc
  rw [KNode.live_lookup] at this
  cases this

/-- A node map A' that differs from A only at the segment root ch, which A
reaches by the prefix P0, and at ids from b on: the keys that do not run through
ch read alike. -/
theorem getFromR_override_off (A A' : NodeId → Option KNode) (V V' : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root ch b : NodeId) (P0 : List Nat)
    (hT : TreeOK A t root) (hwf : ∀ x n, A x = some n → klongsWf n.ks = true)
    (hP0 : segRootR A t fuel P0 root = some ch)
    (hlt : ∀ x, ReachS A t root x → x < b)
    (hA' : ∀ z, z ≠ ch → z < b → A' z = A z) (hV' : ∀ a, a < b → V' a = V a) :
    ∀ key, (∀ q, q ≠ [] → key ≠ P0 ++ q) →
      getFromR A' V' t fuel key root = getFromR A V t fuel key root := by
  intro key hkey
  have hwfR : ∀ x n, ReachS A t root x → A x = some n → klongsWf n.ks = true :=
    fun x n _ h => hwf x n h
  have hchP : TPathK A t root ch P0 := by
    have := segRootR_tPathK A t root fuel hwf P0 root [] ch TPathK.root hP0
    simpa using this
  symm
  apply getFromR_frame A A' V V' t fuel hfuel key root
  · intro q hq
    have hr := fromVisits_reach A t fuel root hwfR key root q.1 q.2 ReachS.root hq
    have hne : q.1 ≠ ch := by
      intro he
      obtain ⟨j, hj, hjc⟩ := fromVisits_tPathK A t root fuel hwf key root [] TPathK.root q.1 q.2 hq
      rw [he] at hj
      simp only [List.nil_append] at hj
      have htake := tPathK_unique A t root hT ch _ hj P0 hchP
      have hjlt : j < key.length := (List.getElem?_eq_some_iff.mp hjc).1
      apply hkey (key.drop j) (by simp; omega)
      rw [← htake, List.take_append_drop]
    exact Or.inl (hA' q.1 hne (hlt q.1 hr)).symm
  · intro x c m y hx hm _ hs
    have hrx := fromVisits_reach A t fuel root hwfR key root x c ReachS.root hx
    cases hfd : m.searchEq t c with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have hry : ReachS A t root fd.y :=
        ReachS.step x m c fd.y hrx hm (KNode.searchEq_mem m t c fd (hwf x m hm) hfd)
      exact (hV' fd.y (hlt fd.y hry)).symm

/-- The keys that run through ch, by the prefix P0, read in A' from ch. -/
theorem getFromR_override_on (A A' : NodeId → Option KNode) (V' : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (root ch b : NodeId) (P0 : List Nat)
    (hT : TreeOK A t root) (hwf : ∀ x n, A x = some n → klongsWf n.ks = true)
    (hP0 : segRootR A t fuel P0 root = some ch)
    (hlt : ∀ x, ReachS A t root x → x < b)
    (hA' : ∀ z, z ≠ ch → z < b → A' z = A z) (hchA : (A ch).isSome = true)
    (hch : (A' ch).isSome = true) :
    ∀ q, q ≠ [] → getFromR A' V' t fuel (P0 ++ q) root = getFromR A' V' t fuel q ch := by
  intro q hq
  have hwfR : ∀ x n, ReachS A t root x → A x = some n → klongsWf n.ks = true :=
    fun x n _ h => hwf x n h
  have hchP : TPathK A t root ch P0 := by
    have := segRootR_tPathK A t root fuel hwf P0 root [] ch TPathK.root hP0
    simpa using this
  rw [getFromR_append_gen A' V' t fuel q hq P0 root]
  rw [← segRootR_frame_reach A A' t fuel root hwfR (by
      intro y hy
      by_cases hyc : y = ch
      · rw [hyc, hchA, hch]
      · rw [hA' y hyc (hlt y hy)]) P0 root ReachS.root (by
      intro q' hq'
      have hr := fromVisits_reach A t fuel root hwfR P0 root q'.1 q'.2 ReachS.root hq'
      have hne : q'.1 ≠ ch := by
        intro he
        obtain ⟨j, hj, hjc⟩ := fromVisits_tPathK A t root fuel hwf P0 root [] TPathK.root q'.1 q'.2 hq'
        rw [he] at hj
        simp only [List.nil_append] at hj
        have htake := tPathK_unique A t root hT ch _ hj P0 hchP
        have hjlt : j < P0.length := (List.getElem?_eq_some_iff.mp hjc).1
        have := congrArg List.length htake
        simp only [List.length_take] at this
        omega
      exact Or.inl (hA' q'.1 hne (hlt q'.1 hr)).symm), hP0]
  rfl

/-- `getFromR_newSegs` for a new segment leaf ch from which no key reads: the
leaf cur's klong at c0 to ch changes no key's reading. -/
theorem getFromR_newSegEmpty (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root rk0 cur ch b : NodeId) (n : KNode)
    (pre : List Nat) (c0 : Nat)
    (hrk : segRootR N t fuel pre root = some rk0)
    (hcurv : (cur, c0) ∈ eqVisits N t c0 fuel rk0) (hNcur : N cur = some n) (hnl : n.leaf = true)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hnone : (n.searchEq t c0).map (·.y) = none)
    (hN2cur : N2 cur = some (n.add t (.key c0 ch)))
    (hN2ch : (N2 ch).isSome = true) (hV2ch : V2 ch = none)
    (hsub : ∀ rest', rest' ≠ [] → getFromR N2 V2 t fuel rest' ch = none)
    (hN2 : ∀ x, x ≠ cur → x < b → N2 x = N x) (hV2 : ∀ a, a < b → V2 a = V a)
    (hrootb : root < b)
    (hwf : ∀ x xn, ReachS N t root x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N t root x → N x = some xn → (c, z) ∈ xn.liveAt t → z < b)
    (huniq : ∀ key', keyWf key' = true → (cur, c0) ∈ fromVisits N t fuel key' root →
      ∃ rest', key' = pre ++ c0 :: rest')
    (hpre : ∀ c', (cur, c') ∉ fromVisits N t fuel pre root) :
    ∀ key', keyWf key' = true → getFromR N2 V2 t fuel key' root = getFromR N V t fuel key' root := by
  -- nodes reached have ids below b
  have hreach_lt : ∀ x, ReachS N t root x → x < b := by
    intro x hx
    cases hx with
    | root => exact hrootb
    | step x' n' c _ hx' hn' hz => exact hfr x' n' c _ hx' hn' hz
  have hagree : ∀ x c, ReachS N t root x → (x = cur → c ≠ c0) → AgreeAt N N2 t x c := by
    intro x c hx hc
    by_cases hxc : x = cur
    · subst hxc
      right
      refine ⟨n, n.add t (.key c0 ch), hNcur, hN2cur, hnl, by rw [KNode.add_leaf]; exact hnl, ?_⟩
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c]
      have : (c0 == c) = false := by
        cases hb : (c0 == c) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb).symm (hc rfl)
      rw [this]; rfl
    · left; exact (hN2 x hxc (hreach_lt x hx)).symm
  have hsome : ∀ y, ReachS N t root y → (N y).isSome = (N2 y).isSome := by
    intro y hy
    by_cases hyc : y = cur
    · rw [hyc, hNcur, hN2cur]; rfl
    · rw [hN2 y hyc (hreach_lt y hy)]
  have hrrk : ReachS N t root rk0 := segRootR_reach N t fuel root hwf pre root rk0 ReachS.root hrk
  intro key' hkey'
  by_cases hv : (cur, c0) ∈ fromVisits N t fuel key' root
  · obtain ⟨rest', hk⟩ := huniq key' hkey' hv
    subst hk
    have hs : c0 :: rest' ≠ [] := by simp
    rw [getFromR_append_gen N2 V2 t fuel _ hs, getFromR_append_gen N V t fuel _ hs, hrk]
    rw [← segRootR_frame_reach N N2 t fuel root hwf hsome pre root ReachS.root (by
      intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf pre root q.1 q.2 ReachS.root hq)
        (fun he => absurd (he ▸ hq) (hpre q.2))), hrk]
    simp only [Option.bind_some]
    have hrchb : ∀ q ∈ eqVisits N t c0 fuel rk0, q.1 < b :=
      fun q hq => hreach_lt q.1 (eqVisits_reach N t root c0 fuel rk0 q.1 q.2 hrrk hq)
    have hg1 : getEqR N t c0 fuel rk0 = none := by
      rw [getEqR_change_leaf N N t c0 cur n hNcur hnl fuel rk0 (fun _ _ _ => rfl) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      exact hnone
    have hg2 : getEqR N2 t c0 fuel rk0 = some ch := by
      rw [getEqR_change_leaf N N2 t c0 cur _ hN2cur (by rw [KNode.add_leaf]; exact hnl) fuel rk0
        (fun q hq hqc => (hN2 q.1 hqc (hrchb q hq)).symm) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c0]
      simp
    have hN : getFromR N V t fuel (c0 :: rest') rk0 = none := by
      cases rest' with
      | nil => simp only [getFromR, hg1]; rfl
      | cons d more => simp only [getFromR, hg1]
    rw [hN]
    cases rest' with
    | nil =>
      simp only [getFromR, hg2, Option.bind_some, hV2ch]
    | cons d more =>
      simp only [getFromR, hg2, hN2ch, ↓reduceIte]
      rw [hsub (d :: more) (by simp)]
  · symm
    apply getFromR_frame N N2 V V2 t fuel hfuel key' root
    · intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf key' root q.1 q.2 ReachS.root hq)
        (fun he hc => hv (by rw [← he, ← hc]; exact hq))
    · intro x c m y hx hm _ hs
      have hrx := fromVisits_reach N t fuel root hwf key' root x c ReachS.root hx
      cases hfd : m.searchEq t c with
      | none => rw [hfd] at hs; cases hs
      | some fd =>
        rw [hfd] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact (hV2 fd.y (hfr x m c fd.y hrx hm (KNode.searchEq_mem m t c fd (hwf x m hrx hm) hfd))).symm

/-- After the leaf cur of the key's segment before got a klong at c0 to the new
segment leaf ch, the prefix pre ++ [c0] leads to ch. -/
theorem segRootR_newSegs (N N2 : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (root rk0 cur ch b : NodeId) (n : KNode) (pre : List Nat) (c0 : Nat)
    (hrk : segRootR N t fuel pre root = some rk0)
    (hcurv : (cur, c0) ∈ eqVisits N t c0 fuel rk0) (hNcur : N cur = some n) (hnl : n.leaf = true)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hN2cur : N2 cur = some (n.add t (.key c0 ch))) (hN2ch : (N2 ch).isSome = true)
    (hN2 : ∀ x, x ≠ cur → x < b → N2 x = N x) (hrootb : root < b)
    (hwf : ∀ x xn, ReachS N t root x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N t root x → N x = some xn → (c, z) ∈ xn.liveAt t → z < b)
    (hpre : ∀ c', (cur, c') ∉ fromVisits N t fuel pre root) :
    segRootR N2 t fuel (pre ++ [c0]) root = some ch := by
  have hreach_lt : ∀ x, ReachS N t root x → x < b := by
    intro x hx
    cases hx with
    | root => exact hrootb
    | step x' n' c _ hx' hn' hz => exact hfr x' n' c _ hx' hn' hz
  have hagree : ∀ x c, ReachS N t root x → (x = cur → c ≠ c0) → AgreeAt N N2 t x c := by
    intro x c hx hc
    by_cases hxc : x = cur
    · subst hxc
      right
      refine ⟨n, n.add t (.key c0 ch), hNcur, hN2cur, hnl, by rw [KNode.add_leaf]; exact hnl, ?_⟩
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c]
      have : (c0 == c) = false := by
        cases hb : (c0 == c) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb).symm (hc rfl)
      rw [this]; rfl
    · left; exact (hN2 x hxc (hreach_lt x hx)).symm
  have hsome : ∀ y, ReachS N t root y → (N y).isSome = (N2 y).isSome := by
    intro y hy
    by_cases hyc : y = cur
    · rw [hyc, hNcur, hN2cur]; rfl
    · rw [hN2 y hyc (hreach_lt y hy)]
  have hrrk : ReachS N t root rk0 := segRootR_reach N t fuel root hwf pre root rk0 ReachS.root hrk
  have hrchb : ∀ q ∈ eqVisits N t c0 fuel rk0, q.1 < b :=
    fun q hq => hreach_lt q.1 (eqVisits_reach N t root c0 fuel rk0 q.1 q.2 hrrk hq)
  have hg2 : getEqR N2 t c0 fuel rk0 = some ch := by
    rw [getEqR_change_leaf N N2 t c0 cur _ hN2cur (by rw [KNode.add_leaf]; exact hnl) fuel rk0
      (fun q hq hqc => (hN2 q.1 hqc (hrchb q hq)).symm) hcurv
      (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
    rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c0]
    simp
  rw [segRootR_snoc, ← segRootR_frame_reach N N2 t fuel root hwf hsome pre root ReachS.root (by
      intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf pre root q.1 q.2 ReachS.root hq)
        (fun he => absurd (he ▸ hq) (hpre q.2))), hrk]
  simp only [Option.bind_some, hg2, hN2ch, ↓reduceIte]

set_option maxHeartbeats 1600000 in
/-- A put of a key pre ++ c0 :: tail whose prefix pre is there, whose leaf for c0
has no klong of c0 and is full: the leaf's klong to the new segment leaf goes up
through a cascade along the whole access path (`writerWP_appendKlongs_chainGRV`
from the space root), and the new segment leaves below it hold the rest of the
key. The reading changes by the put alone, when every path inside one segment
tree of the writer's state after it is shorter than the fuel (`SegFits`) or the
space root does not space split (`RootStays`). The premises on the nodes
reached are those of `writerWP_put_accessPathR`. -/
theorem writerWP_put_newSegFullR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ ¬ n.size + 1 < c.p.M ∧
      (∀ key', keyWf key' = true →
        (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
        RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
        else wGet c.p c.i base w key') := by
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
  obtain ⟨hnone, hfull, huniq, hpre⟩ := hcur L n hvisL hn hnl
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
            (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
              RootStays c (wNode c.p base w) w.top.rootKey) →
            ∀ key', keyWf key' = true → wGet c.p c.i base w' key' =
              if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
              else wGet c.p c.i base w key'))) := by
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
    have hVw1 : wValue base ws1 = wValue base w := by
      funext a; simp only [wValue, hw1t, hw1v]
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
        · exact Or.inr ⟨hi, hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _ (hreachX (i - 1) (by omega))
            (hXN (i - 1) (by omega)) (hKP i hi h2).2⟩)
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
    simp only [Nat.zero_add, hXD, hn, Option.getD_some] at hchain
    refine writerWP_mono hchain ?_
    intro _ wf1 ⟨hT1, ⟨hftop, hft, hfpath, hfnext, hfv⟩, hframe1, hreach1, hW1, hR1, hab1, _⟩
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
    refine writerWP_mono (writerWP_putSegs_new c base (pre ++ c0 :: tail) h hM hfuel tail htail wf1
      w.next hlkc htkc (by omega) hfreshc) ?_
    rintro _ wf ⟨k1, k2, _, k4, k5, _, k7, k8⟩
    intro hq key' hkey'
    unfold wGet
    -- the trees and values involved
    have hVd_some : (wNode c.p base wf1 w.next).isSome = true := by
      simp only [wNode, htkc, Bool.false_eq_true, ↓reduceIte, hlkc]; rfl
    have hA'some : (wNode c.p base wf w.next).isSome = true := by
      have htk' : wf.taken.contains w.next = false := by rw [k1]; exact htkc
      cases hl : wf.nodes.lookup w.next with
      | none => rw [hl] at k7; cases k7
      | some m => simp only [wNode, htk', Bool.false_eq_true, ↓reduceIte, hl]; rfl
    have hVAL : (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next))) L =
        some (n.add c.i (.key c0 w.next)) := updN_self _ _ _
    have hVAch : (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next)))
        w.next = some ⟨true, []⟩ := by
      rw [updN_ne _ _ _ _ (by omega)]; exact updN_self _ _ _
    have hVAN : ∀ x, x ≠ L → x < w.next →
        (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next))) x =
          wNode c.p base w x := by
      intro x h1 h2
      rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ (by omega)]
    have hfrW : ∀ x xn c' z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
        wNode c.p base w x = some xn → (c', z) ∈ xn.liveAt c.i → z < w.next :=
      fun x xn c' z _ hxn hz => hlinksAll x c' z ⟨xn, hxn, hz⟩
    have hnwf := hwfG _ _ hn
    have hnt := htimesG _ _ hn
    -- (i) the prefix pre ++ [c0] leads to the new segment leaf, in the virtual tree and in wf1
    have hseg := segRootR_newSegs (wNode c.p base w)
      (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next))) c.i c.p.fuel
      w.top.rootKey rk0 L w.next w.next n pre c0 hrk hvisL hn hnl hnwf hnt hVAL
      (by rw [hVAch]; rfl) hVAN hidr hwfR hfrW hpre
    let Vd : NodeId → Option Nat := fun z => if z = w.next then some 1 else none
    have hadm_d : ∀ z, (ws1.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ P.length ∧ z = nodeAt w.top.rootKey P i) →
        Vd z = none := by
      intro z hz
      have hzn : z ≠ w.next := by
        rcases hz with hz | ⟨i, _, h2, h3⟩
        · omega
        · rw [h3]; have := hXlt i h2; omega
      simp only [Vd, hzn, ↓reduceIte]
    have hVA_d : getFromR (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
        (n.add c.i (.key c0 w.next))) Vd c.i c.p.fuel (pre ++ [c0]) w.top.rootKey = some 1 := by
      rw [segRootR_snoc] at hseg
      rw [getFromR_append]
      cases hs : segRootR (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
          (n.add c.i (.key c0 w.next))) c.i c.p.fuel pre w.top.rootKey with
      | none => rw [hs] at hseg; cases hseg
      | some rk' =>
        rw [hs] at hseg
        simp only [Option.bind_some] at hseg ⊢
        cases hg : getEqR (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
            (n.add c.i (.key c0 w.next))) c.i c0 c.p.fuel rk' with
        | none => rw [hg] at hseg; cases hseg
        | some y =>
          rw [hg] at hseg
          simp only at hseg
          split at hseg
          · simp only [Option.some.injEq] at hseg
            subst hseg
            simp only [getFromR, hg, Option.bind_some, Vd, ↓reduceIte]
          · cases hseg
    have hlinkVA : ∀ u c' z, TLink (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
        (n.add c.i (.key c0 w.next))) c.i u c' z → z < ws1.next := by
      intro u c' z hl
      obtain ⟨mm, hm, hc⟩ := hl
      by_cases hu : u = L
      · rw [hu, updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases KNode.add_key_liveAt_mem n c.i c0 w.next hnwf hnt c' z hc with ⟨_, h2⟩ | ⟨_, h2⟩
        · omega
        · have := hlinksAll L c' z ⟨n, hn, h2⟩; omega
      · rw [updN_ne _ _ _ _ hu] at hm
        by_cases hu2 : u = w.next
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          exact absurd hc (KNode.empty_liveAt c.i c' z)
        · rw [updN_ne _ _ _ _ hu2] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega
    have hreachVA : ∀ x, TReach (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
        (n.add c.i (.key c0 w.next))) c.i w.top.rootKey x → x < ws1.next := by
      intro x hx
      induction hx with
      | root => omega
      | link _ hl _ => exact hlinkVA _ _ _ hl
    have hlt : ∀ x, ReachS (wNode c.p base wf1) c.i wf1.top.rootKey x → x < wf1.next := by
      intro x hx
      rcases hreach1 x (reachS_tReach _ _ _ _ hx) with h' | ⟨_, h'⟩
      · rw [hws1N, hw1top] at h'
        have := hreachVA x h'; omega
      · exact h'
    have hA' : ∀ z, z ≠ w.next → z < wf1.next → wNode c.p base wf z = wNode c.p base wf1 z := by
      intro z h1 h2
      simp only [wNode, k1, k4 z h2 h1]
    have hfit1 : SegFits (wNode c.p base wf) c.i (c.p.fuel - 1) wf.top.rootKey →
        SegFits (wNode c.p base wf1) c.i (c.p.fuel - 1) wf1.top.rootKey := by
      intro hfit
      rw [k2] at hfit
      have hw1e : wNode c.p base wf1 w.next = some ⟨true, []⟩ := by
        simp only [wNode, htkc, Bool.false_eq_true, ↓reduceIte, hlkc]
      refine SegFits.of_sub _ _ c.i _ _ ?_ ?_ hfit
      · intro x hx
        induction hx with
        | root => exact ReachS.root
        | step u un c' z hu hun hc ih =>
          have hun' : u ≠ w.next := by
            intro he
            rw [he, hw1e] at hun
            simp only [Option.some.injEq] at hun
            subst hun
            exact KNode.empty_liveAt c.i c' z hc
          exact ReachS.step u un c' z ih (by rw [hA' u hun' (hlt u hu)]; exact hun) hc
      · intro y n' hy hyn
        by_cases hyw : y = w.next
        · subst hyw; rw [hw1e] at hyn; cases hyn; exact Or.inl rfl
        · exact Or.inr (by rw [hA' y hyw (hlt y hy)]; exact hyn)
    have hA_d : getFromR (wNode c.p base wf1) Vd c.i c.p.fuel (pre ++ [c0]) wf1.top.rootKey = some 1 := by
      rw [hR1 Vd hadm_d (hq.imp hfit1 (fun hs => ⟨fun ⟨_, hnr, hsp⟩ => Nat.not_le.mpr hsp (hs _ (by
        dsimp only
        have h0 := hXN 0 (Nat.zero_le _)
        rw [nodeAt_zero] at h0 ⊢
        exact h0) hnr), fun i hi h2 hnr hsp => hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _
          (hreachX (i - 1) (by omega)) (hXN (i - 1) (by omega)) (hKP i hi h2).2⟩)), hws1N, hw1top]
      exact hVA_d
    have hsegA : segRootR (wNode c.p base wf1) c.i c.p.fuel (pre ++ [c0]) wf1.top.rootKey =
        some w.next := by
      rw [getFromR_append] at hA_d
      rw [segRootR_snoc]
      cases hs : segRootR (wNode c.p base wf1) c.i c.p.fuel pre wf1.top.rootKey with
      | none => rw [hs] at hA_d; cases hA_d
      | some rk' =>
        rw [hs] at hA_d
        simp only [Option.bind_some, getFromR] at hA_d ⊢
        cases hg : getEqR (wNode c.p base wf1) c.i c0 c.p.fuel rk' with
        | none => rw [hg] at hA_d; cases hA_d
        | some y =>
          rw [hg] at hA_d
          simp only [Option.bind_some, Vd] at hA_d
          by_cases hy : y = w.next
          · subst hy; simp only [hVd_some, ↓reduceIte]
          · simp only [hy, ↓reduceIte] at hA_d; cases hA_d
    -- (ii) what wf1 reaches has ids below its next id
    have hV' : ∀ a, a < wf1.next → wValue base wf a = wValue base wf1 a := by
      intro a ha
      simp only [wValue, k1, k5 a ha]
    have hvw : wValue base wf1 = wValue base ws1 := by
      funext a; simp only [wValue, hft, hfv]
    have hadm_v : ∀ z, (ws1.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ P.length ∧ z = nodeAt w.top.rootKey P i) →
        wValue base ws1 z = none := by
      intro z hz
      rw [hVw1]
      rcases hz with hz | ⟨i, _, h2, h3⟩
      · simp only [wValue, hntake z (by omega), Bool.false_eq_true, ↓reduceIte,
          hvalnone z (by omega), (hbase z (by omega)).2]
      · rw [h3]; exact hnoval _ _ (hXN i h2)
    rw [k2]
    by_cases hthr : ∃ q, q ≠ [] ∧ key' = (pre ++ [c0]) ++ q
    · obtain ⟨q, hq, rfl⟩ := hthr
      rw [getFromR_override_on (wNode c.p base wf1) (wNode c.p base wf) (wValue base wf) c.i c.p.fuel
        wf1.top.rootKey w.next wf1.next (pre ++ [c0]) hT1 hW1 hsegA hlt hA' hVd_some hA'some q hq,
        k8 q hq]
      have hk : pre ++ [c0] ++ q = pre ++ c0 :: q := by simp
      rw [hk]
      by_cases hqt : tail = q
      · subst hqt; simp [Op.key, Op.value]
      · have hb1 : (tail == q) = false := by simpa using hqt
        have hb2 : (pre ++ c0 :: tail == pre ++ c0 :: q) = false := by simp [hqt]
        simp only [Op.key, hb1, hb2, Bool.false_eq_true, ↓reduceIte]
        -- before the put, the key reads nothing: the leaf has no klong of c0
        have hg1 : getEqR (wNode c.p base w) c.i c0 c.p.fuel rk0 = none := by
          rw [getEqR_change_leaf (wNode c.p base w) (wNode c.p base w) c.i c0 L n hn hnl c.p.fuel rk0
            (fun _ _ _ => rfl) hvisL (fun n1 h1 => by rw [hn] at h1; cases h1; exact hnl)]
          rw [hnone]; rfl
        rw [getFromR_append_gen _ _ _ _ (c0 :: q) (by simp) pre, hrk]
        simp only [Option.bind_some]
        cases q with
        | nil => exact absurd rfl hq
        | cons d more => simp only [getFromR, hg1]
    · have hoff := getFromR_override_off (wNode c.p base wf1) (wNode c.p base wf) (wValue base wf1)
        (wValue base wf) c.i c.p.fuel hfuel wf1.top.rootKey w.next wf1.next (pre ++ [c0]) hT1 hW1
        hsegA hlt hA' hV' key' (fun q hq he => hthr ⟨q, hq, he⟩)
      rw [hoff, hvw, hR1 (wValue base ws1) hadm_v (hq.imp hfit1 (fun hs => ⟨fun ⟨_, hnr, hsp⟩ => Nat.not_le.mpr hsp (hs _ (by
        dsimp only
        have h0 := hXN 0 (Nat.zero_le _)
        rw [nodeAt_zero] at h0 ⊢
        exact h0) hnr), fun i hi h2 hnr hsp => hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _
          (hreachX (i - 1) (by omega)) (hXN (i - 1) (by omega)) (hKP i hi h2).2⟩)) key', hws1N, hw1top, hVw1]
      simp only [List.foldl_cons, List.foldl_nil]
      have hempty : ∀ rest', rest' ≠ [] → getFromR (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L
          (n.add c.i (.key c0 w.next))) (wValue base w) c.i c.p.fuel rest' w.next = none := by
        intro rest' hr
        obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
        have hse : ((⟨true, []⟩ : KNode).searchEq c.i) = fun _ => none := by funext x; rfl
        cases rest' with
        | nil => exact absurd rfl hr
        | cons d more =>
          cases more with
          | nil => simp only [getFromR, hf2, getEqR, hVAch, ↓reduceIte, hse]; rfl
          | cons d' more' => simp only [getFromR, hf2, getEqR, hVAch, ↓reduceIte, hse]; rfl
      rw [getFromR_newSegEmpty (wNode c.p base w)
        (updN (updN (wNode c.p base w) w.next ⟨true, []⟩) L (n.add c.i (.key c0 w.next)))
        (wValue base w) (wValue base w) c.i c.p.fuel hfuel w.top.rootKey rk0 L w.next w.next n pre c0
        hrk hvisL hn hnl hnwf hnt (by rw [hnone]; rfl) hVAL (by rw [hVAch]; rfl)
        (by simp only [wValue, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
          hvalnone _ (Nat.le_refl _), (hbase _ (Nat.le_refl _)).2])
        hempty hVAN (fun _ _ => rfl) hidr hwfR hfrW huniq hpre key' hkey']
      have hne : (pre ++ c0 :: tail == key') = false := by
        cases hb : (pre ++ c0 :: tail == key') with
        | false => rfl
        | true =>
          exfalso
          apply hthr
          refine ⟨tail, htail, ?_⟩
          rw [← beq_iff_eq.mp hb]; simp
      simp only [Op.key, hne, Bool.false_eq_true, ↓reduceIte]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl rfl

/-- `writerWP_put_newSegFullR` when no node that space splits is the space root
(`hspaceG`): the reading needs no premise on the fuel. -/
theorem writerWP_put_newSegFull (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      x ≠ w.top.rootKey ∧ ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ ¬ n.size + 1 < c.p.M ∧
      (∀ key', keyWf key' = true →
        (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
        else wGet c.p c.i base w key') :=
  writerWP_mono (writerWP_put_newSegFullR c base hvc pre c0 h tail htail rk0 w hM hrk ht hids hbase hwfG
    htimesG hT hlinksAll hnoval hrangeG hlenG (fun x xn hx hxn hnr hsp => (hspaceG x xn hx hxn hnr hsp).2)
    hcur)
    (fun _ _ hp => hp (Or.inr (fun rn hrn hnr => Nat.le_of_not_lt (fun hsp =>
      (hspaceG _ _ TReach.root hrn hnr hsp).1 rfl))))

end SIS.Tree
