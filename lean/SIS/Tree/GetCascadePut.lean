import SIS.Tree.GetCascadeChain
import SIS.Tree.WriterTreeDelSpace
import SIS.Tree.GetCascadeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a leaf below a cascade of any depth (bergdb 024-12, TP10): the
descent's last m + 1 nodes XX 0 (with room) to XX m (the leaf), each below the
one before by klong KK j; the writer's `appendKlongs` along them
(`writerWP_appendKlongs_chainR`) and the leaf's put (`getFromR_leaf_change_seg`). -/

/-- The descent's entries of a chain: XX 1 to XX m by klongs KK 1 to KK m. -/
def chainSteps (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat) : List (Option Nat × NodeId) :=
  (List.range m).map (fun j => (some (KK (j + 1)), XX (j + 1)))

theorem chainSteps_length (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat) :
    (chainSteps m XX KK).length = m := by
  simp [chainSteps]

theorem chainSteps_get (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat) (j : Nat) (hj : j < m) :
    (chainSteps m XX KK)[j]? = some (some (KK (j + 1)), XX (j + 1)) := by
  simp [chainSteps, hj]

theorem chainSteps_mem (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat) (j : Nat) (hj : j < m) :
    (some (KK (j + 1)), XX (j + 1)) ∈ chainSteps m XX KK := by
  simp only [chainSteps, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

theorem pathEnd_chain (x : NodeId) (S0 : List (Option Nat × NodeId)) (m : Nat)
    (XX : Nat → NodeId) (KK : Nat → Nat) (h0 : pathEnd x S0 = XX 0) :
    pathEnd x (S0 ++ chainSteps m XX KK) = XX m := by
  cases m with
  | zero => simpa [chainSteps] using h0
  | succ m =>
    have : chainSteps (m + 1) XX KK = chainSteps m XX KK ++ [(some (KK (m + 1)), XX (m + 1))] := by
      simp [chainSteps, List.range_succ]
    rw [this, ← List.append_assoc, pathEnd_append]

set_option maxHeartbeats 1600000 in
/-- A put of a key whose descent from its last segment's root rk ends with the
chain XX 0 to XX m (`chainSteps`): XX m the leaf, full; XX 1 to XX m existed
before the transaction; XX 0 with room for two klongs; the order of each
node's compare values below its parent's klong (`hrange`). The splits of the
chain, time or space as their sizes say, change the reading by the put alone. -/
theorem writerWP_put_chain (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat)
    (NN : Nat → KNode)
    (hkey : keyWf (pre ++ [cv]) = true)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ chainSteps m XX KK))
    (htopX : pathEnd rk S0 = XX 0)
    (hNN : ∀ j, j ≤ m → wNode c.p base w (XX j) = some (NN j))
    (hleafm : (NN m).leaf = true)
    (hinner : ∀ j, j < m → (NN j).leaf = false)
    (hlinksK : ∀ j, j < m → (KK (j + 1), XX (j + 1)) ∈ (NN j).liveAt c.i)
    (hnew : ∀ j, 1 ≤ j → j ≤ m → (NN j).firstTime ≠ some c.i)
    (hrange : ∀ j, 1 ≤ j → j ≤ m → ∀ c' z, (c', z) ∈ (NN j).live → 0 < c' →
      KK j ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (j - 1)).live → KK j < c'' → c' < c'')
    (hlen : ∀ j, 1 ≤ j → j ≤ m → c.p.splitAbove < ((NN j).lastVersion c.i).size →
      2 ≤ (NN j).live.length)
    (htop : (NN 0).size + 2 + 1 ≤ c.p.M ∧ ∀ ins : List (Nat × NodeId), ins.length ≤ 2 →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN 0)) = false)
    (hdist : ∀ j j', j ≤ m → j' ≤ m → XX j = XX j' → j = j')
    (hfullL : ¬ ((NN m).size + 1 < c.p.M ∧
      deadOver c.p ((NN m).add c.i (.key cv w.next)) = false))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have hend : pathEnd rk (S0 ++ chainSteps m XX KK) = XX m := pathEnd_chain rk S0 m XX KK htopX
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
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
  intro L' w3 ⟨⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn' hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hsteps : steps = S0 ++ chainSteps m XX KK := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro mm hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro mm hm; rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm
    · exact ⟨NN m, by rw [hend]; exact hNN m (Nat.le_refl _)⟩
  have hLL : L' = XX m := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNN m (Nat.le_refl _)] at hn'; cases hn'
  -- the chain's nodes are visited
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun mm hm => by rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm)
    (by rw [hend]; exact hvisL)
  have hvisX : ∀ j, j ≤ m → (XX j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    intro j hj
    cases j with
    | zero =>
      rw [← htopX]
      cases hS0 : S0.getLast? with
      | none =>
        have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
        subst this; simpa [pathEnd] using hvis.1
      | some e =>
        have hmem : e ∈ S0 := List.mem_of_getLast? hS0
        have := hvis.2 e (by simp [hmem])
        simpa [pathEnd, hS0] using this
    | succ j =>
      exact hvis.2 _ (List.mem_append_right _ (chainSteps_mem m XX KK j (by omega)))
  have hreachX : ∀ j, j ≤ m → ReachS (wNode c.p base w) c.i w.top.rootKey (XX j) :=
    fun j hj => eqVisits_reach _ _ _ cv c.p.fuel rk (XX j) cv hrrk (hvisX j hj)
  have hlkX : ∀ j, j ≤ m → w3.nodes.lookup (XX j) = some (NN j) :=
    fun j hj => hcache3 (XX j) (NN j) (hvisX j hj) (hNN j hj)
  have htkX : ∀ j, j ≤ m → w.taken.contains (XX j) = false :=
    fun j hj => ht (XX j, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ (hvisX j hj))
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
  have hXlt : ∀ j, j ≤ m → XX j < w.next := fun j hj => hsrcw3 _ (by rw [hlkX j hj]; rfl)
  -- the writer's path
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some (XX 0) := by
    rw [← htopX]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hp2'
    | some e =>
      rw [List.getLast?_append, hS0]
      simp [pathEnd, hS0]
  have hneP : w2'.path ++ S0 ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'; simp at hp2'
  obtain ⟨d, hd⟩ : ∃ d, (w2'.path ++ S0).length = d + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ chainSteps m XX KK := by rw [hp3]; simp
  have hlen3 : w3.path.length - 1 = d + m := by
    rw [hp3', List.length_append, chainSteps_length, hd]; omega
  have hpX : ∀ i, d ≤ i → i ≤ d + m → (w3.path[i]?).map (·.2) = some (XX (i - d)) := by
    intro i h1 h2
    rw [hp3']
    by_cases hi : i = d
    · subst hi
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd] at hlastP
      simpa using hlastP
    · rw [List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
      simp only [Option.map_some]
      congr 2; omega
  have hpK : ∀ i, d < i → i ≤ d + m → w3.path[i]? = some (some (KK (i - d)), XX (i - d)) := by
    intro i h1 h2
    rw [hp3', List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
    have : i - (d + 1) + 1 = i - d := by omega
    rw [this]
  -- the leaf is full: the put goes to appendKlongs
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ _ c _ (by simpa using hlkX m (Nat.le_refl _))]
  have hcond : (decide ((NN m).size + 1 < c.p.M) &&
      !deadOver c.p ((NN m).add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd' : deadOver c.p ((NN m).add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ (NN m).size + 1 < c.p.M := fun hlt => hfullL ⟨hlt, hd'⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
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
  have hchain := writerWP_appendKlongs_chainR c base w3.path d (d + m) (fun i => XX (i - d))
    (fun i => KK (i - d)) (fun i => NN (i - d))
    (fun i h1 h2 => hpX i h1 h2)
    (fun i h1 h2 => hpK i h1 h2)
    (fun i h1 h2 => by
      show (NN (i - 1 - d)).leaf = false
      exact hinner (i - 1 - d) (by omega))
    (fun i h1 h2 => by
      show (KK (i - d), XX (i - d)) ∈ (NN (i - 1 - d)).liveAt c.i
      have := hlinksK (i - 1 - d) (by omega)
      have he : i - 1 - d + 1 = i - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 => hnew (i - d) (by omega) (by omega))
    (fun i h1 h2 c' z hz hc => by
      have := hrange (i - d) (by omega) (by omega) c' z hz hc
      have he : i - d - 1 = i - 1 - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hsp => hlen (i - d) (by omega) (by omega) hsp)
    (fun i h1 h2 => hwfG _ _ (hNN (i - d) (by omega)))
    (fun i h1 h2 => htimesG _ _ (hNN (i - d) (by omega)))
    (by simpa using htop)
    (fun i i' h1 h2 h3 h4 he => by
      have := hdist (i - d) (i' - d) (by omega) (by omega) he
      omega)
    m (Nat.le_refl _) ws [(cv, w3.next)] (Or.inl ⟨cv, w3.next, rfl⟩)
    (by intro q hq; simp at hq; rw [hq, hwsx, hnext3]; simp)
    hwsp
    (by
      intro i h1 h2
      refine ⟨by rw [hwsn]; exact hlkX (i - d) (by omega), ?_⟩
      show ws.taken.contains (XX (i - d)) = false
      rw [hwst]; exact htkX (i - d) (by omega))
    (by rw [hwsN, hwstop]; exact hT)
    (by
      intro i h1 h2
      rw [hwsN, hwstop]
      exact reachS_tReach _ _ _ _ (hreachX (i - d) (by omega)))
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
    (by
      intro z zn hz
      rw [hwsN] at hz
      exact hwfG z zn hz)
    (by
      intro z hz
      have hzn : z ≠ w.next := by
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [hwsx] at hz; omega
        · rw [h3]; have := hXlt (i - d) (by omega); omega
      have hval : wValue base ws z = wValue base w z := by
        simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ hzn]
      rw [hval]
      rcases hz with hz | ⟨i, h1, h2, h3⟩
      · rw [hwsx] at hz
        simp only [wValue, hntake z (by omega), Bool.false_eq_true, ↓reduceIte,
          hvalnone z (by omega), (hbase z (by omega)).2]
      · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
    (by
      rw [hwsN, hwstop]
      show TreeOK (updN (wNode c.p base w) (XX (d + m - d))
        ((NN (d + m - d)).add c.i (.key cv w3.next))) c.i w.top.rootKey
      have hdm : d + m - d = m := by omega
      rw [hdm, hnext3]
      exact treeOK_addKey (wNode c.p base w) _ c.i w.top.rootKey (XX m) w.next (NN m) cv hT
        (reachS_tReach _ _ _ _ (hreachX m (Nat.le_refl _))) (hNN m (Nat.le_refl _))
        (hwfG _ _ (hNN m (Nat.le_refl _))) (htimesG _ _ (hNN m (Nat.le_refl _)))
        (updN_self _ _ _) (fun x hx => updN_ne _ _ _ _ hx)
        (by
          simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            (hbase w.next (Nat.le_refl _)).1]
          cases h' : w.nodes.lookup w.next with
          | none => rfl
          | some _ => have := hidn w.next (by rw [h']; rfl); omega)
        (fun u c' _ hl => by have := hlinksAll u c' w.next hl; omega))
  have hdm : d + m - d = m := by omega
  simp only [hdm] at hchain
  refine writerWP_mono hchain ?_
  intro _ wf ⟨_, ⟨hftop, _, _, _, _⟩, _, _, _, hR⟩
  have hn2l : ((NN m).add c.i (.key cv w.next)).leaf = true := by rw [KNode.add_leaf]; exact hleafm
  have hmwf := hwfG _ _ (hNN m (Nat.le_refl _))
  have hmt := htimesG _ _ (hNN m (Nat.le_refl _))
  have hsearch := KNode.add_key_searchEq (NN m) c.i cv w.next hmwf hmt
  have hwsnext : ws.taken.contains w.next = false := by rw [hwst]; exact hntake _ (Nat.le_refl _)
  have hVv : wValue base ws w.next = some h := by
    simp only [wValue, hwsnext, Bool.false_eq_true, ↓reduceIte, hwsv,
      lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))]
  have hA := getFromR_leaf_change_seg (wNode c.p base w)
    (updN (wNode c.p base w) (XX m) ((NN m).add c.i (.key cv w.next))) (wValue base w)
    (wValue base ws) c.i c.p.fuel hfuel (XX m) pre cv w.top.rootKey rk (NN m)
    ((NN m).add c.i (.key cv w.next)) (fun x hx => (updN_ne _ _ _ _ hx).symm)
    (hNN m (Nat.le_refl _)) (updN_self _ _ _) hleafm hn2l
    (fun c' hc' => by
      rw [hsearch c']
      have hb : (cv == c') = false := by
        cases hcb : (cv == c') with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
      rw [hb]; rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun key' x c' m' y _ hx hm' _ hs' => by
      have hrx : ReachS (wNode c.p base w) c.i w.top.rootKey x :=
        fromVisits_reach _ _ _ _ hwfR key' _ x c' ReachS.root hx
      have hy : y < w.next := by
        cases hfd : m'.searchEq c.i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact hlinksAll x c' fd.y ⟨m', hm', KNode.searchEq_mem m' c.i c' fd (hwfG x m' hm') hfd⟩
      simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ (by omega : y ≠ w.next)])
  intro key' hkey'
  unfold wGet
  rw [hR key', hwsN, hwstop, hnext3]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hA.1, hsearch cv]
    simp [hVv]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-- `writerWP_put_chain` on cost's chain of any kind (`writerWP_appendKlongs_chainGRV`): the
nodes XX 1 to XX m split in place if the transaction made them; XX 0 with room
for two klongs. The splits of the chain change the reading by the put alone. -/
theorem writerWP_put_chainG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat)
    (NN : Nat → KNode)
    (hkey : keyWf (pre ++ [cv]) = true)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ chainSteps m XX KK))
    (htopX : pathEnd rk S0 = XX 0)
    (hNN : ∀ j, j ≤ m → wNode c.p base w (XX j) = some (NN j))
    (hleafm : (NN m).leaf = true)
    (hinner : ∀ j, j < m → (NN j).leaf = false)
    (hlinksK : ∀ j, j < m → (KK (j + 1), XX (j + 1)) ∈ (NN j).liveAt c.i)
    (hrange : ∀ j, 1 ≤ j → j ≤ m → ¬ ChainRoom c (NN j) → ∀ c' z, (c', z) ∈ (NN j).live → 0 < c' →
      KK j ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (j - 1)).live → KK j < c'' → c' < c'')
    (hlen : ∀ j, 1 ≤ j → j ≤ m → ¬ ChainRoom c (NN j) →
      c.p.splitAbove < ((NN j).lastVersion c.i).size → 2 ≤ (NN j).live.length)
    (htop : ChainRoom c (NN 0))
    (hdist : ∀ j j', j ≤ m → j' ≤ m → XX j = XX j' → j = j')
    (hfullL : ¬ ((NN m).size + 1 < c.p.M ∧
      deadOver c.p ((NN m).add c.i (.key cv w.next)) = false))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have hend : pathEnd rk (S0 ++ chainSteps m XX KK) = XX m := pathEnd_chain rk S0 m XX KK htopX
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
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
  intro L' w3 ⟨⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn' hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hsteps : steps = S0 ++ chainSteps m XX KK := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro mm hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro mm hm; rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm
    · exact ⟨NN m, by rw [hend]; exact hNN m (Nat.le_refl _)⟩
  have hLL : L' = XX m := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNN m (Nat.le_refl _)] at hn'; cases hn'
  -- the chain's nodes are visited
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun mm hm => by rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm)
    (by rw [hend]; exact hvisL)
  have hvisX : ∀ j, j ≤ m → (XX j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    intro j hj
    cases j with
    | zero =>
      rw [← htopX]
      cases hS0 : S0.getLast? with
      | none =>
        have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
        subst this; simpa [pathEnd] using hvis.1
      | some e =>
        have hmem : e ∈ S0 := List.mem_of_getLast? hS0
        have := hvis.2 e (by simp [hmem])
        simpa [pathEnd, hS0] using this
    | succ j =>
      exact hvis.2 _ (List.mem_append_right _ (chainSteps_mem m XX KK j (by omega)))
  have hreachX : ∀ j, j ≤ m → ReachS (wNode c.p base w) c.i w.top.rootKey (XX j) :=
    fun j hj => eqVisits_reach _ _ _ cv c.p.fuel rk (XX j) cv hrrk (hvisX j hj)
  have hlkX : ∀ j, j ≤ m → w3.nodes.lookup (XX j) = some (NN j) :=
    fun j hj => hcache3 (XX j) (NN j) (hvisX j hj) (hNN j hj)
  have htkX : ∀ j, j ≤ m → w.taken.contains (XX j) = false :=
    fun j hj => ht (XX j, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ (hvisX j hj))
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
  have hXlt : ∀ j, j ≤ m → XX j < w.next := fun j hj => hsrcw3 _ (by rw [hlkX j hj]; rfl)
  -- the writer's path
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some (XX 0) := by
    rw [← htopX]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hp2'
    | some e =>
      rw [List.getLast?_append, hS0]
      simp [pathEnd, hS0]
  have hneP : w2'.path ++ S0 ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'; simp at hp2'
  obtain ⟨d, hd⟩ : ∃ d, (w2'.path ++ S0).length = d + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ chainSteps m XX KK := by rw [hp3]; simp
  have hlen3 : w3.path.length - 1 = d + m := by
    rw [hp3', List.length_append, chainSteps_length, hd]; omega
  have hpX : ∀ i, d ≤ i → i ≤ d + m → (w3.path[i]?).map (·.2) = some (XX (i - d)) := by
    intro i h1 h2
    rw [hp3']
    by_cases hi : i = d
    · subst hi
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd] at hlastP
      simpa using hlastP
    · rw [List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
      simp only [Option.map_some]
      congr 2; omega
  have hpK : ∀ i, d < i → i ≤ d + m → w3.path[i]? = some (some (KK (i - d)), XX (i - d)) := by
    intro i h1 h2
    rw [hp3', List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
    have : i - (d + 1) + 1 = i - d := by omega
    rw [this]
  -- the leaf is full: the put goes to appendKlongs
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ _ c _ (by simpa using hlkX m (Nat.le_refl _))]
  have hcond : (decide ((NN m).size + 1 < c.p.M) &&
      !deadOver c.p ((NN m).add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd' : deadOver c.p ((NN m).add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ (NN m).size + 1 < c.p.M := fun hlt => hfullL ⟨hlt, hd'⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
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
  have hchain := writerWP_appendKlongs_chainGRV c base w3.path d (d + m) (fun i => XX (i - d))
    (fun i => KK (i - d)) (fun i => NN (i - d))
    (fun i h1 h2 => hpX i h1 h2)
    (fun i h1 h2 => hpK i h1 h2)
    (fun i h1 h2 => by
      show (KK (i - d), XX (i - d)) ∈ (NN (i - 1 - d)).liveAt c.i
      have := hlinksK (i - 1 - d) (by omega)
      have he : i - 1 - d + 1 = i - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr _ c' z hz hc => by
      have := hrange (i - d) (by omega) (by omega) hnr c' z hz hc
      have he : i - d - 1 = i - 1 - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr hsp => by
      by_cases hi : i = d
      · subst hi; simp only [Nat.sub_self] at hnr; exact absurd htop hnr
      · exact hlen (i - d) (by omega) (by omega) hnr hsp)
    (fun i h1 h2 => hwfG _ _ (hNN (i - d) (by omega)))
    (fun i h1 h2 => htimesG _ _ (hNN (i - d) (by omega)))
    (Or.inl (by simpa using htop))
    (fun i i' h1 h2 h3 h4 he => by
      have := hdist (i - d) (i' - d) (by omega) (by omega) he
      omega)
    (fun i h1 h2 hnr _ => by
      by_cases hi : i = d
      · subst hi; simp only [Nat.sub_self] at hnr; exact absurd htop hnr
      · refine ⟨by omega, ?_⟩
        show (NN (i - 1 - d)).leaf = false
        exact hinner (i - 1 - d) (by omega))
    m (Nat.le_refl _) ws [(cv, w3.next)] (Or.inl ⟨cv, w3.next, rfl⟩)
    (by intro q hq; simp at hq; rw [hq, hwsx, hnext3]; simp)
    hwsp
    (by
      intro i h1 h2
      refine ⟨by rw [hwsn]; exact hlkX (i - d) (by omega), ?_⟩
      show ws.taken.contains (XX (i - d)) = false
      rw [hwst]; exact htkX (i - d) (by omega))
    (by rw [hwsN, hwstop]; exact hT)
    (by
      intro i h1 h2
      rw [hwsN, hwstop]
      exact reachS_tReach _ _ _ _ (hreachX (i - d) (by omega)))
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
    (fun _ hnr => absurd (by simpa using htop) hnr)
    (by
      intro z zn hz
      rw [hwsN] at hz
      exact hwfG z zn hz)
    (by
      rw [hwsN, hwstop]
      show TreeOK (updN (wNode c.p base w) (XX (d + m - d))
        ((NN (d + m - d)).add c.i (.key cv w3.next))) c.i w.top.rootKey
      have hdm : d + m - d = m := by omega
      rw [hdm, hnext3]
      exact treeOK_addKey (wNode c.p base w) _ c.i w.top.rootKey (XX m) w.next (NN m) cv hT
        (reachS_tReach _ _ _ _ (hreachX m (Nat.le_refl _))) (hNN m (Nat.le_refl _))
        (hwfG _ _ (hNN m (Nat.le_refl _))) (htimesG _ _ (hNN m (Nat.le_refl _)))
        (updN_self _ _ _) (fun x hx => updN_ne _ _ _ _ hx)
        (by
          simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            (hbase w.next (Nat.le_refl _)).1]
          cases h' : w.nodes.lookup w.next with
          | none => rfl
          | some _ => have := hidn w.next (by rw [h']; rfl); omega)
        (fun u c' _ hl => by have := hlinksAll u c' w.next hl; omega))
  have hdm : d + m - d = m := by omega
  simp only [hdm] at hchain
  refine writerWP_mono hchain ?_
  intro _ wf ⟨_, ⟨hftop, hft, _, _, hfv⟩, _, _, _, hR⟩
  have hadm : ∀ z, (w.next + 2 ≤ z ∨ ∃ i, d ≤ i ∧ i ≤ d + m ∧ z = XX (i - d)) →
      wValue base ws z = none := by
    intro z hz
    have hzn : z ≠ w.next := by
      rcases hz with hz | ⟨i, h1, h2, h3⟩
      · omega
      · rw [h3]; have := hXlt (i - d) (by omega); omega
    have hval : wValue base ws z = wValue base w z := by
      simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ hzn]
    rw [hval]
    rcases hz with hz | ⟨i, h1, h2, h3⟩
    · simp only [wValue, hntake z (by omega), Bool.false_eq_true, ↓reduceIte,
        hvalnone z (by omega), (hbase z (by omega)).2]
    · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega))
  have hvf : wValue base wf = wValue base ws := by
    funext a; simp only [wValue, hft, hfv]
  have hn2l : ((NN m).add c.i (.key cv w.next)).leaf = true := by rw [KNode.add_leaf]; exact hleafm
  have hmwf := hwfG _ _ (hNN m (Nat.le_refl _))
  have hmt := htimesG _ _ (hNN m (Nat.le_refl _))
  have hsearch := KNode.add_key_searchEq (NN m) c.i cv w.next hmwf hmt
  have hwsnext : ws.taken.contains w.next = false := by rw [hwst]; exact hntake _ (Nat.le_refl _)
  have hVv : wValue base ws w.next = some h := by
    simp only [wValue, hwsnext, Bool.false_eq_true, ↓reduceIte, hwsv,
      lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))]
  have hA := getFromR_leaf_change_seg (wNode c.p base w)
    (updN (wNode c.p base w) (XX m) ((NN m).add c.i (.key cv w.next))) (wValue base w)
    (wValue base ws) c.i c.p.fuel hfuel (XX m) pre cv w.top.rootKey rk (NN m)
    ((NN m).add c.i (.key cv w.next)) (fun x hx => (updN_ne _ _ _ _ hx).symm)
    (hNN m (Nat.le_refl _)) (updN_self _ _ _) hleafm hn2l
    (fun c' hc' => by
      rw [hsearch c']
      have hb : (cv == c') = false := by
        cases hcb : (cv == c') with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
      rw [hb]; rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun key' x c' m' y _ hx hm' _ hs' => by
      have hrx : ReachS (wNode c.p base w) c.i w.top.rootKey x :=
        fromVisits_reach _ _ _ _ hwfR key' _ x c' ReachS.root hx
      have hy : y < w.next := by
        cases hfd : m'.searchEq c.i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact hlinksAll x c' fd.y ⟨m', hm', KNode.searchEq_mem m' c.i c' fd (hwfG x m' hm') hfd⟩
      simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ (by omega : y ≠ w.next)])
  intro key' hkey'
  unfold wGet
  rw [hvf, hR (wValue base ws) (fun z hz => hadm z (by rw [hwsx] at hz; exact hz)) key', hwsN, hwstop,
    hnext3]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hA.1, hsearch cv]
    simp [hVv]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-! ## The writer's splits of a delete's leaf with the parent's step left open -/

/-- Cost's `writerWP_handleFullWith_time_up` for a delete: nothing to insert and
the last version `last` given. -/
theorem writerWP_handleFullWith_time_up_last (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, last.ks⟩)] → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x []
      last compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup _ rfl rfl rfl rfl rfl rfl

/-- Cost's `writerWP_handleFullWith_space_up` for a delete: nothing to insert and
the last version `last` given. -/
theorem writerWP_handleFullWith_space_up_last (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i last []).1
        else if z = w.next + 2 then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next),
          ((halves n.leaf c.i last []).2.2, w.next + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x []
      last false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (hup _ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      rotate_left 6
      · intro _ w2 h
        simpa only [writerWP_bind, putNode, writerWP_modify] using h
      · intro z
        simp only [lookup_upsert, List.lookup_append]
        by_cases hz2 : z = w.next + 2
        · have hz1 : z ≠ w.next := by omega
          simp [hz2]
        · simp only [hz2, ↓reduceIte]
          by_cases hz1 : z = w.next
          · simp [hz1]
          · simp only [hz1, ↓reduceIte]
            cases h : w.nodes.lookup z with
            | some m => rfl
            | none =>
              have hb1 : (z == w.next) = false := by simpa using hz1
              have hb2 : (z == w.next + 2) = false := by simpa using hz2
              simp [List.lookup, hb1, hb2]
      all_goals rfl)

/-- The reading after a space split in place of the leaf L, which keeps the
first half of its last version without the compare value cv,
`⟨true, newKlongs i pairs⟩`, the second half S new, below its parent q with a new
klong to S: the key reads as no value, every other key as before. -/
theorem getFromR_spaceSplitInPlace_del (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q S : NodeId) (n qn : KNode)
    (k1 : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId) (pairs : List (Nat × NodeId))
    (hps : CvSorted pairs) (hpne : pairs ≠ [])
    (hpl : ∀ c, pairs.lookup c = if c == cv then none else n.live.lookup c)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hN2q : N2 q = some (qn.add i (.key (halves true i ⟨true, newKlongs i pairs⟩ []).2.2 S)))
    (hN2F : N2 L = some (halves true i ⟨true, newKlongs i pairs⟩ []).1)
    (hN2S : N2 S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ S → N2 x = N x)
    (hqL : q ≠ L) (hSL : S ≠ L) (hNS : N S = none)
    (hrootL : root ≠ L) (hrootS : root ≠ S) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ S) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  -- the leaf without cv, as a reader would see it unsplit
  let m : KNode := ⟨true, newKlongs i pairs⟩
  have hml : m.leaf = true := rfl
  have hmwf : klongsWf m.ks = true := klongsWf_newKlongs i pairs
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := newKlongs_times i pairs
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hmlook' : ∀ c, m.live.lookup c = pairs.lookup c := by
    intro c
    rw [KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c hpn]
  have hmlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c := by
    intro c; rw [hmlook', hpl]
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNmq : Nm q = some qn := by simp [Nm, hqL, hNq]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hmem : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hmlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [hL1]; exact lookup_some_mem this
  have hreach := reach_change N i root L S n m hNL (fun c z hz => Or.inl (hmem c z hz)) hNS hSL
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq (by
    rw [KNode.liveAt_of_times qn i hqt]; exact hk1)
  have hwfm : ∀ x xn, ReachS Nm i root x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNS] at hn; cases hn
  have hnotL : ∀ x xn c z, ReachS Nm i root x → x ≠ q → Nm x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ L := by
    intro x xn c z hx hxq hn hz hzL
    subst hzL
    by_cases hxL : x = z
    · subst hxL
      rw [hNmL] at hn; cases hn
      exact hxq (honlyL x n c hrL hNL (hmem c x hz)).1
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hxq (honlyL x xn c hx' hn hz).1
      · subst hxv; rw [hNS] at hn; cases hn
  have hnotFS : ∀ x xn c z, ReachS Nm i root x → Nm x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ S := by
    intro x xn c z hx hn hz
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      exact hfr x n c z hrL hNL (hmem c z hz)
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hfr x xn c z hx' hn hz
      · subst hxv; rw [hNS] at hn; cases hn
  have hnotFS' : ∀ x xn c z, ReachS Nm i root x → Nm x = some xn → (c, z) ∈ xn.liveAt i →
      (z ≠ L → z ≠ L) ∧ z ≠ S := fun x xn c z hx hn hz =>
    ⟨fun h => h, hnotFS x xn c z hx hn hz⟩
  -- the halves
  obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
    cases hd : (pairs.drop (pairs.length / 2)) with
    | nil =>
      have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
      have : pairs.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hpne
    | cons a _ => exact ⟨a, rfl⟩
  have hrmem : r ∈ pairs := List.mem_of_mem_drop (List.mem_of_head? hr)
  have hrmemN : r ∈ n.live := by
    have hl := lookup_some_of_mem hpn hrmem
    rw [hpl] at hl
    by_cases hc : r.1 = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (r.1 == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact lookup_some_mem hl
  have hshape := halves_leaf_shape i pairs [] r hr
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hshape
  have hsc : (halves true i ⟨true, newKlongs i pairs⟩ []).2.2 = r.1 := by rw [hshape]
  have hwfh := halves_newKlongs_wf true i pairs []
  generalize hout : halves true i ⟨true, newKlongs i pairs⟩ [] = out at hN2q hN2F hN2S hsc hwfh hshape
  obtain ⟨f, s, sc⟩ := out
  simp only at hN2q hN2F hN2S hsc hwfh
  subst hsc
  simp only [Prod.mk.injEq] at hshape
  obtain ⟨hf, hs', _⟩ := hshape
  have hfl : f.leaf = true := by rw [hf]
  have hsl : s.leaf = true := by rw [hs']
  have hft : ∀ t', Klong.time t' ∈ f.ks → t' ≤ i := by rw [hf]; exact newKlongs_times i _
  have hst : ∀ t', Klong.time t' ∈ s.ks → t' ≤ i := by rw [hs']; exact newKlongs_times i _
  have hlook := halves_leaf_lookup i pairs [] hps r hr (by simp)
  rw [hout] at hlook
  simp only [List.foldl_nil] at hlook
  have hleafF : ∀ c, c < r.1 → (f.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live f i hwfh.1 hft, KNode.searchEq_live m i hmwf hmt, hmlook']
    have := hlook c
    simp only [hc, ↓reduceIte] at this
    exact this
  have hleafS : ∀ c, r.1 ≤ c → (s.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live s i hwfh.2 hst, KNode.searchEq_live m i hmwf hmt, hmlook']
    have := hlook c
    simp only [show ¬ c < r.1 by omega, ↓reduceIte] at this
    exact this
  -- the parent's search
  have hqsearch : ∀ c : Nat,
      ((qn.add i (.key r.1 S)).searchLte i c).map (·.y) =
        (qn.searchLte i c).map (fun fd => if fd.y = L then (if c < r.1 then L else S) else fd.y) := by
    intro c
    have hA := KNode.splitParentInPlace_searchLte qn i k1 r.1 L S hqwf hqt hk1 (hrange r.1 r.2 hrmemN).1
      (fun c' z hz => by
        by_cases hc : c' ≤ k1
        · exact Or.inl hc
        · exact Or.inr ((hrange r.1 r.2 hrmemN).2 c' z hz (by omega))) c
    rw [hA]
    cases hs : qn.searchLte i c with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Option.some.injEq]
      have hmemfd := KNode.searchLte_mem qn i c fd hs
      rw [KNode.liveAt_of_times qn i hqt] at hmemfd
      have hyL : fd.y = L ↔ fd.c = k1 := by
        constructor
        · intro hy
          rw [hy] at hmemfd
          exact (honlyL q qn fd.c hrq hNq (by rw [KNode.liveAt_of_times qn i hqt]; exact hmemfd)).2
        · intro hc
          rw [hc] at hmemfd
          exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup qn) hmemfd).symm.trans
            (lookup_some_of_mem (KNode.live_keys_nodup qn) hk1))
      by_cases hc : fd.c = k1
      · simp only [hc, ↓reduceIte, hyL.mpr hc, Int.ofNat_lt]
      · have hy : ¬ fd.y = L := fun h => hc (hyL.mp h)
        simp only [hc, ↓reduceIte, hy]
  have hq2l : (qn.add i (.key r.1 S)).leaf = false := by
    rw [KNode.add_leaf]; exact hql
  have hsame : ∀ x, x ≠ L → x ≠ q → x ≠ L → x ≠ S → N2 x = Nm x := by
    intro x h1 h2 _ h4
    rw [hN2 x h1 h2 h4, hNm x h1]
  have hsim := getFromR_split Nm N2 V i fuel root L q L S hwfm
    (fun c x hx hxL hxF hxS => getEqR_split Nm N2 i root L q L S qn _ m f s r.1 hNmq hql hN2q hq2l
      hqsearch hNmL hml hN2F hfl hN2S hsl hleafF hleafS hsame hnotL hnotFS' c fuel x hx hxL hxF hxS)
    hsame (by rw [hN2q, hNmq]; rfl) hnotL
    (fun xn c z hxn _ hxl => by rw [hNmq] at hxn; cases hxn; rw [hql] at hxl; cases hxl) hnotFS'
  have hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (m.searchEq i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n i hnwf hnt, KNode.searchEq_live m i hmwf hmt, hmlook]
    have : (c' == cv) = false := by simpa using hc'
    rw [this]; rfl
  have hA := getFromR_leaf_change_seg N Nm V V i fuel hfuel L pre cv root rk n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs hrk hcv hvisL huniq
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  intro key' hkey'
  rw [hsim key' root ReachS.root hrootL hrootL hrootS]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-- The halves of a leaf's last version with nothing put, by the divider r:
the first half's keys are below r, the second half's from r, all of them pairs. -/
theorem halves_nil_links (t : Time) (pairs : List (Nat × NodeId)) (hps : CvSorted pairs)
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r) :
    (halves true t ⟨true, newKlongs t pairs⟩ []).2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).1.live → c < r.1 ∧ (c, z) ∈ pairs) ∧
    (∀ c z, (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).2.1.live →
      r.1 ≤ c ∧ (c, z) ∈ pairs) := by
  rw [halves_leaf_shape t pairs [] r hr]
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  refine ⟨trivial, ?_, ?_⟩
  · intro c z h
    have hm := newKlongs_live_mem true t _ c z h
    exact ⟨halves_left_lt_divider pairs _ hps r hr _ hm, List.mem_of_mem_take hm⟩
  · intro c z h
    have hm := newKlongs_live_mem true t _ c z h
    exact ⟨halves_right_ge_divider pairs _ hps r hr _ hm, List.mem_of_mem_drop hm⟩

/-- The space split in place of a delete's leaf x that the transaction made,
below the inner parent q, with the parent's step left open: x keeps the first
half of the last version `last`, a new node the second, and q gets the second's
klong. -/
theorem writerWP_handleFullWith_spaceInPlace_up_last (d' : Nat) (x q : NodeId) (n qn : KNode)
    (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hxn : x < w.next)
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = x then some (halves n.leaf c.i last []).1
        else if z = w.next then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [((halves n.leaf c.i last []).2.2, w.next)]) c w1
          (fun _ w2 => Q w2)) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x [] last false) c w
      (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hx2 : x ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_modify, writerWP_pure]
        refine writerWP_mono (hup _ ?_ rfl rfl rfl rfl rfl) ?_
        · intro z
          simp only [lookup_upsert, List.lookup_append]
          by_cases hzx : z = x
          · subst hzx
            simp [hx2]
          · by_cases hz1 : z = w.next
            · subst hz1
              simp [hzx]
            · simp only [hzx, hz1, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hz1]; rfl
        · intro _ w2 h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
          exact h

/-- TReach in a lookup whose links are among N's is TReach in N. -/
theorem tReach_of_sublinks (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hsub : ∀ x c y, TLink N' t x c y → TLink N t x c y) :
    ∀ y, TReach N' t r y → TReach N t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | link _ hl ih => exact TReach.link ih (hsub _ _ _ hl)

/-- The nodes of a chain XX 0 to XX m, each linked to the next, are reached
after XX m changes: a tree's paths to them are shorter than those to XX m. -/
theorem tReach_chain_updN (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hT : TreeOK N t r) (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat)
    (hlink : ∀ j, j < m → TLink N t (XX j) (KK (j + 1)) (XX (j + 1)))
    (j : Nat) (hj : j < m) (hr : TReach N t r (XX j)) (f : KNode) :
    TReach (updN N (XX m) f) t r (XX j) := by
  obtain ⟨a, ha⟩ := hr.pathLen
  have hpf : ∀ k, j + k ≤ m → PathFromLen N t (XX j) (XX (j + k)) k := by
    intro k
    induction k with
    | zero => intro _; exact PathFromLen.refl _
    | succ k ih => intro hk; exact PathFromLen.link (ih (by omega)) (hlink (j + k) (by omega))
  have hL := ha.append (hpf (m - j) (by omega))
  have he : j + (m - j) = m := by omega
  rw [he] at hL
  exact tReach_updN_of_short N t r (XX m) f a (XX j) ha
    (fun k hk => by have := PathLen.depth_unique hT _ _ _ hL hk; omega)

set_option maxHeartbeats 1600000 in
/-- A delete, the merges off, of a key whose descent from its last segment's
root rk ends with the chain XX 0 to XX m (`chainSteps`, m ≥ 1): XX m the leaf,
which keeps a live klong; XX 1 to XX m - 1 existed before the transaction;
XX 0 with room for two klongs. The leaf's bitmap, with room, or the leaf's time
or space split (each in place for a leaf the transaction made), and the splits
of the chain above it, time or space as their sizes say, change the reading by
the delete alone. -/
theorem writerWP_del_chain (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat)
    (NN : Nat → KNode) (hm : 1 ≤ m) (hmerges : c.p.merges = false) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf (pre ++ [cv]) = true)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ chainSteps m XX KK))
    (htopX : pathEnd rk S0 = XX 0)
    (hNN : ∀ j, j ≤ m → wNode c.p base w (XX j) = some (NN j))
    (hleafm : (NN m).leaf = true)
    (hinner : ∀ j, j < m → (NN j).leaf = false)
    (hlinksK : ∀ j, j < m → (KK (j + 1), XX (j + 1)) ∈ (NN j).liveAt c.i)
    (hnew : ∀ j, 1 ≤ j → j < m → (NN j).firstTime ≠ some c.i)
    (hrange : ∀ j, 1 ≤ j → j < m → ∀ c' z, (c', z) ∈ (NN j).live → 0 < c' →
      KK j ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (j - 1)).live → KK j < c'' → c' < c'')
    (hrangeL : ∀ c' z, (c', z) ∈ (NN m).live →
      KK m ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (m - 1)).live → KK m < c'' → c' < c'')
    (hlen : ∀ j, 1 ≤ j → j < m → c.p.splitAbove < ((NN j).lastVersion c.i).size →
      2 ≤ (NN j).live.length)
    (htop : (NN 0).size + 2 + 1 ≤ c.p.M ∧ ∀ ins : List (Nat × NodeId), ins.length ≤ 2 →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN 0)) = false)
    (hdist : ∀ j j', j ≤ m → j' ≤ m → XX j = XX j' → j = j')
    (hne : bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv) ≠ (NN m).lastBitmap)
    (hkeep : (NN m).allKeysIn (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have hend : pathEnd rk (S0 ++ chainSteps m XX KK) = XX m := pathEnd_chain rk S0 m XX KK htopX
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
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
  intro L' w3 ⟨⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn' hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hsteps : steps = S0 ++ chainSteps m XX KK := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro mm hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro mm hm; rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm
    · exact ⟨NN m, by rw [hend]; exact hNN m (Nat.le_refl _)⟩
  have hLL : L' = XX m := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNN m (Nat.le_refl _)] at hn'; cases hn'
  -- the chain's nodes are visited
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun mm hm => by rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm)
    (by rw [hend]; exact hvisL)
  have hvisX : ∀ j, j ≤ m → (XX j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    intro j hj
    cases j with
    | zero =>
      rw [← htopX]
      cases hS0 : S0.getLast? with
      | none =>
        have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
        subst this; simpa [pathEnd] using hvis.1
      | some e =>
        have hmem : e ∈ S0 := List.mem_of_getLast? hS0
        have := hvis.2 e (by simp [hmem])
        simpa [pathEnd, hS0] using this
    | succ j =>
      exact hvis.2 _ (List.mem_append_right _ (chainSteps_mem m XX KK j (by omega)))
  have hreachX : ∀ j, j ≤ m → ReachS (wNode c.p base w) c.i w.top.rootKey (XX j) :=
    fun j hj => eqVisits_reach _ _ _ cv c.p.fuel rk (XX j) cv hrrk (hvisX j hj)
  have hlkX : ∀ j, j ≤ m → w3.nodes.lookup (XX j) = some (NN j) :=
    fun j hj => hcache3 (XX j) (NN j) (hvisX j hj) (hNN j hj)
  have htkX : ∀ j, j ≤ m → w.taken.contains (XX j) = false :=
    fun j hj => ht (XX j, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ (hvisX j hj))
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
  have hXlt : ∀ j, j ≤ m → XX j < w.next := fun j hj => hsrcw3 _ (by rw [hlkX j hj]; rfl)
  -- the writer's path
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some (XX 0) := by
    rw [← htopX]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hp2'
    | some e =>
      rw [List.getLast?_append, hS0]
      simp [pathEnd, hS0]
  have hneP : w2'.path ++ S0 ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'; simp at hp2'
  obtain ⟨d, hd⟩ : ∃ d, (w2'.path ++ S0).length = d + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ chainSteps m XX KK := by rw [hp3]; simp
  have hlen3 : w3.path.length - 1 = d + m := by
    rw [hp3', List.length_append, chainSteps_length, hd]; omega
  have hpX : ∀ i, d ≤ i → i ≤ d + m → (w3.path[i]?).map (·.2) = some (XX (i - d)) := by
    intro i h1 h2
    rw [hp3']
    by_cases hi : i = d
    · subst hi
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd] at hlastP
      simpa using hlastP
    · rw [List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
      simp only [Option.map_some]
      congr 2; omega
  have hpK : ∀ i, d < i → i ≤ d + m → w3.path[i]? = some (some (KK (i - d)), XX (i - d)) := by
    intro i h1 h2
    rw [hp3', List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
    have : i - (d + 1) + 1 = i - d := by omega
    rw [this]
  -- the delete in the leaf
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen3]
  have hlkL := hlkX m (Nat.le_refl _)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c _ hlkL]
  have hnb : (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv) == (NN m).lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached _ _ c _ hlkL _ (fun gh => ?_)
  -- facts of the leaf, its parent and the delete's last version
  have hLt := htkX m (Nat.le_refl _)
  have hnL := hNN m (Nat.le_refl _)
  have hqn := hNN (m - 1) (by omega)
  have hnwf := hwfG _ _ hnL
  have hnt := htimesG _ _ hnL
  have hqwf := hwfG _ _ hqn
  have hqt := htimesG _ _ hqn
  have hql : (NN (m - 1)).leaf = false := hinner (m - 1) (by omega)
  have hmm : m - 1 + 1 = m := by omega
  have hkl : (KK m, XX m) ∈ (NN (m - 1)).liveAt c.i := by
    have := hlinksK (m - 1) (by omega); rw [hmm] at this; exact this
  have hkl' : (KK m, XX m) ∈ (NN (m - 1)).live := by
    rw [← KNode.liveAt_of_times _ c.i hqt]; exact hkl
  have hqL : XX (m - 1) ≠ XX m := fun h => by have := hdist _ _ (by omega) (Nat.le_refl _) h; omega
  have hrq := hreachX (m - 1) (by omega)
  have hrL := hreachX m (Nat.le_refl _)
  have honlyL : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', XX m) ∈ xn.liveAt c.i → x = XX (m - 1) ∧ c' = KK m :=
    fun x xn c' hx hxn hz => hT.oneLink x c' (XX (m - 1)) (KK m) (XX m)
      (reachS_tReach _ _ _ _ hx) (reachS_tReach _ _ _ _ hrq) ⟨xn, hxn, hz⟩ ⟨_, hqn, hkl⟩
  have hLroot : w.top.rootKey ≠ XX m := fun h =>
    hT.rootFree (XX (m - 1)) (KK m) (reachS_tReach _ _ _ _ hrq) ⟨_, hqn, by rw [h]; exact hkl⟩
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts (NN m) c.i cv
  have hlook0 := KNode.delete_live_lookup (NN m) c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have hnone : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnone, (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz, (hbase z hz).2]
  have hnoLinkW : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hlinksAll u c' z hl; omega
  have hyRW : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z :=
    fun z hz => not_reach_fresh _ c.i _ z hT (hfreshN z hz) (fun u c' _ => hnoLinkW z hz u c')
  have hw3N : ∀ w' : W, w'.nodes = w3.nodes → w'.taken = w3.taken →
      wNode c.p base w' = wNode c.p base w := by
    intro w' h1 h2
    rw [← hr03.1]
    funext z
    simp only [wNode, h1, h2]
  -- the chain at the parent, from a state that is w3's with the leaf's new nodes
  have hpq' : (w3.path[d + (m - 1)]?).map (·.2) = some (XX (m - 1)) := by
    have := hpX (d + (m - 1)) (by omega) (by omega)
    have he : d + (m - 1) - d = m - 1 := by omega
    rw [he] at this; exact this
  have hpk' : w3.path[d + (m - 1) + 1]? = some (some (KK m), XX m) := by
    have := hpK (d + (m - 1) + 1) (by omega) (by omega)
    have he : d + (m - 1) + 1 - d = m := by omega
    rw [he] at this; exact this
  have hdm : d + m = d + (m - 1) + 1 := by omega
  rw [hdm]
  -- the chain's premises above the leaf
  have hchainPre := fun (w1 : W) (ins : List (Nat × NodeId)) =>
    writerWP_appendKlongs_chainR c base w3.path d (d + (m - 1)) (fun i => XX (i - d))
    (fun i => KK (i - d)) (fun i => NN (i - d))
    (fun i h1 h2 => hpX i h1 (by omega))
    (fun i h1 h2 => hpK i h1 (by omega))
    (fun i h1 h2 => by
      show (NN (i - 1 - d)).leaf = false
      exact hinner (i - 1 - d) (by omega))
    (fun i h1 h2 => by
      show (KK (i - d), XX (i - d)) ∈ (NN (i - 1 - d)).liveAt c.i
      have := hlinksK (i - 1 - d) (by omega)
      have he : i - 1 - d + 1 = i - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 => hnew (i - d) (by omega) (by omega))
    (fun i h1 h2 c' z hz hc => by
      have := hrange (i - d) (by omega) (by omega) c' z hz hc
      have he : i - d - 1 = i - 1 - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hsp => hlen (i - d) (by omega) (by omega) hsp)
    (fun i h1 h2 => hwfG _ _ (hNN (i - d) (by omega)))
    (fun i h1 h2 => htimesG _ _ (hNN (i - d) (by omega)))
    (by simpa using htop)
    (fun i i' h1 h2 h3 h4 he => by
      have := hdist (i - d) (i' - d) (by omega) (by omega) he
      omega)
    (m - 1) (Nat.le_refl _) w1 ins
  have hdm1 : d + (m - 1) - d = m - 1 := by omega
  -- the post of the delete
  have hlast : ∀ s : String, ({ w3 with trail := s :: w3.trail } : W).nodes = w3.nodes ∧
      ({ w3 with trail := s :: w3.trail } : W).taken = w3.taken ∧
      ({ w3 with trail := s :: w3.trail } : W).path = w3.path ∧
      ({ w3 with trail := s :: w3.trail } : W).next = w3.next ∧
      ({ w3 with trail := s :: w3.trail } : W).top = w3.top ∧
      ({ w3 with trail := s :: w3.trail } : W).vals = w3.vals := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- a time split of the leaf, not in place
  have hcascadeT : ∀ (compact : Bool) (s : String),
      (!compact && decide (((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size > c.p.splitAbove)) = false →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact s hcs hfirst
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    generalize hLv : ((⟨(NN m).leaf, ((NN m).lastVersionGivenDel c.i
      (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).ks⟩ : KNode)) = Lv
    apply writerWP_handleFullWith_time_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ compact c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hcs (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hs4] at h1n h1next
    rw [hs1] at h1n
    rw [hLv] at h1n
    have hfree0 : w3.nodes.lookup w3.next = none := by
      cases h' : w3.nodes.lookup w3.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next Lv := by
      rw [wNode_append_updN c.p base w3 w1 Lv h1n h1t' hfree0
        (by rw [hr03.2.2.1, hnext3]; exact hntake _ (Nat.le_refl _))]
      rw [hw3N w3 rfl rfl, hnext3]
    rw [hnext3] at h1n h1next
    have hLvwf : klongsWf Lv.ks = true := by rw [← hLv]; exact hwf0
    have hLvt : ∀ s, Klong.time s ∈ Lv.ks → s ≤ c.i := by rw [← hLv]; exact hlt
    have hLvsub : ∀ c' z, (c', z) ∈ Lv.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hLvt] at h
      rw [KNode.liveAt_of_times _ c.i hnt]
      rw [← hLv, hleq] at h
      exact hlsub c' z h
    have hLvlook : ∀ c', Lv.live.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
      intro c'; rw [← hLv, hleq]; exact hlook0 c'
    -- the tree with the parent's klong put
    obtain ⟨hTA, hRA⟩ := treeOK_timeSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) Lv
      ((NN (m - 1)).add c.i (.key (KK m) w.next)) (KK m) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL
      (updN_self _ _ _)
      (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h)
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      hLvsub
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hchain := hchainPre w1 [(KK m, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by intro q hq; simp at hq; rw [hq, h1next]; simp)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n, List.lookup_append, hlkX (i - d) (by omega)]; rfl
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [hN1, h1top, hs5, hr03.2.1]
        exact treeOK_updN_unreach _ c.i _ _ _ hT (hyRW _ (Nat.le_refl _)))
      (by
        intro i h1 h2
        rw [hN1, h1top, hs5, hr03.2.1]
        obtain ⟨a, ha⟩ := (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n, List.lookup_append]
        have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
        cases h' : w3.nodes.lookup z with
        | none => simp [List.lookup, hb]
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, hLvsub c' z hc⟩; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hzy : z = w.next
        · rw [hzy, updN_self] at hz; cases hz; exact hLvwf
        · rw [updN_ne _ _ _ _ hzy] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        have hv1 : wValue base w1 = wValue base w := by
          funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    rw [hs4, hnext3]
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega),
        h1n, List.lookup_append, hlkL]
      rfl
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2 : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hres := getFromR_timeSplit_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) Lv (KK m) pre cv rk hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      (by rw [← hLv]; exact hleafm) hLvwf hLvt hLvlook
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      (updN_self _ _ _)
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hnoval _ _ hnL) (hfreshV _ (Nat.le_refl _)) hqL
      (fun h => by have := hXlt m (Nat.le_refl _); omega)
      (fun h => by have := hXlt (m - 1) (by omega); omega)
      (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by
        have := hlinksAll x c' z ⟨xn, hxn, hz⟩; omega)
    intro key' hkey'
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the delete's last version as pairs
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hlastE : (NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)) =
      ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hleafm, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  have hpairsN : ∀ c' z, (c', z) ∈ pairs → (c', z) ∈ (NN m).live := by
    intro c' z hm
    have hl := lookup_some_of_mem hpn hm
    rw [hpl] at hl
    by_cases hc : c' = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (c' == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact lookup_some_mem hl
  -- a space split of the leaf, which existed before
  have hcascadeS : ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    have hrmemN : r ∈ (NN m).live := hpairsN r.1 r.2 (List.mem_of_mem_drop (List.mem_of_head? hr))
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    apply writerWP_handleFullWith_space_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have h12 : w3'.next ≠ w3'.next + 2 := by omega
    have h12' : w.next ≠ w.next + 2 := by omega
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have htk2 : w3'.taken.contains (w3'.next + 2) = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (by omega)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next H.1) (w.next + 2) H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t h12 htk0 htk2, hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → c' < H.2.2 ∧ (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨h1, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hs : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i →
        ∃ c0, H.2.2 ≤ c0 ∧ c' = (fun c0 => c0) c0 ∧ (c0, z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨c', h1, rfl, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hqwf1 := KNode.add_key_wf (NN (m - 1)) c.i (KK m) w.next hqwf
    have hqt1 := KNode.add_times (NN (m - 1)) c.i (.key (KK m) w.next) (fun _ h => by cases h) hqt
    have hqlinks : ∀ c' z, (c', z) ∈ ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))).liveAt c.i →
        (c' = H.2.2 ∧ z = w.next + 2) ∨ (c' ≠ H.2.2 ∧ c' = KK m ∧ z = w.next) ∨
        (c' ≠ H.2.2 ∧ c' ≠ KK m ∧ (c', z) ∈ (NN (m - 1)).liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf1 hqt1 c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXq2 : XX (m - 1) ≠ w.next + 2 := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have hXL2 : XX m ≠ w.next + 2 := fun h => by have := hXlt m (Nat.le_refl _); omega
    obtain ⟨hTA, hRA⟩ := treeOK_spaceSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (w.next + 2) (NN (m - 1)) (NN m) H.1 H.2.1
      ([(KK m, w.next), (H.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (NN (m - 1)))
      (KK m) H.2.2 (fun c0 => c0) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL (updN_self _ _ _) hqlinks
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12']; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq2.symm, hN1]; exact updN_self _ _ _)
      hf hs
      (by
        intro z hz1 hz2 hz3 hz4
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) h12'
      (fun z hz u c' _ hl => by
        rcases hz with hz | hz <;> (subst hz; exact hnoLinkW _ (by omega) u c' hl))
    have hagree : ∀ x, TReach (wNode c.p base w) c.i w.top.rootKey x →
        wNode c.p base w1 x = wNode c.p base w x := by
      intro x hx
      have h1 : x ≠ w.next := fun h => by subst h; exact hyRW _ (Nat.le_refl _) hx
      have h2 : x ≠ w.next + 2 := fun h => by subst h; exact hyRW _ (by omega) hx
      rw [hN1, updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h1]
    have hins : InsOK (NN (m - 1)) [(KK m, w.next), (H.2.2, w.next + 2)] :=
      Or.inr ⟨KK m, w.next, H.2.2, w.next + 2, rfl, by rw [hscr]; exact (hrangeL r.1 r.2 hrmemN).1,
        fun c'' z'' hz hlt => by rw [hscr]; exact (hrangeL r.1 r.2 hrmemN).2 c'' z'' hz hlt⟩
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(KK m, w.next), (H.2.2, w.next + 2)] (by simp only [hdm1]; exact hins)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rw [h1next]
        rcases hq with hq | hq <;> (subst hq; dsimp only; omega))
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [show XX (i - d) ≠ w.next by omega, show XX (i - d) ≠ w.next + 2 by omega,
            ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1]
        exact treeOK_of_agree _ _ _ _ hT hagree)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n]
        simp only [show z ≠ w.next by omega, show z ≠ w.next + 2 by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next + 2
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          rw [KNode.liveAt_of_times _ c.i hHt.2] at hc
          have := hlinksAll _ _ _ ⟨_, hnL, by
            rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hsh c' z hc).2⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          by_cases hu1 : u = w.next
          · rw [hu1, updN_self] at hm
            simp only [Option.some.injEq] at hm
            subst hm
            rw [KNode.liveAt_of_times _ c.i hHt.1] at hc
            have := hlinksAll _ _ _ ⟨_, hnL, by
              rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hfh c' z hc).2⟩
            omega
          · rw [updN_ne _ _ _ _ hu1] at hm
            have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next + 2
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = w.next
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega), h1n]
      simp only [hXL1, hXL2, ↓reduceIte, hs1]
      exact hlkL
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2' : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2'
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hres := getFromR_spaceSplit_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (w.next + 2) (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      hrangeL
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12', updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq2.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3 hx4
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx4, updN_ne _ _ _ _ hx3])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by
        have := hlinksAll x c' z ⟨xn, hxn, hz⟩; exact ⟨by omega, by omega⟩)
    intro key' hkey'
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- a space split in place of the leaf, which the transaction made
  have hcascadeSIP : ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime = some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    apply writerWP_handleFullWith_spaceInPlace_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m)
      (NN (m - 1)) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hnx]; exact hXlt m (Nat.le_refl _))
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have htkL : w3'.taken.contains (XX m) = false := by rw [hs2, hr03.2.2.1]; exact hLt
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (XX m) H.1) w.next H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t (by rw [hnx]; exact hXL1) htkL htk0,
        hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf' : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ c' < H.2.2 := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    have hs' : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ H.2.2 ≤ c' := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    -- the leaf with its first half: links among the leaf's
    have hsubf : ∀ x c' y, TLink (updN (wNode c.p base w) (XX m) H.1) c.i x c' y →
        TLink (wNode c.p base w) c.i x c' y := by
      intro x c' y hl
      obtain ⟨mm, hm, hc⟩ := hl
      by_cases hx : x = XX m
      · subst hx
        rw [updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        exact ⟨_, hnL, (hf' c' y hc).1⟩
      · rw [updN_ne _ _ _ _ hx] at hm; exact ⟨mm, hm, hc⟩
    have hreachf := tReach_of_sublinks _ _ c.i w.top.rootKey hsubf
    have hTf : TreeOK (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey :=
      treeOK_of_node_shrink _ _ c.i _ (XX m) (NN m) H.1 hT hnL (updN_self _ _ _)
        (fun y hy => updN_ne _ _ _ _ hy) (fun c' z h => (hf' c' z h).1)
    have hnf : ¬ TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey w.next :=
      fun h => hyRW _ (Nat.le_refl _) (hreachf _ h)
    have hagree : ∀ x, TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey x →
        wNode c.p base w1 x = updN (wNode c.p base w) (XX m) H.1 x := by
      intro x hx
      have hxn : x ≠ w.next := fun h => by subst h; exact hnf hx
      rw [hN1, updN_ne _ _ _ _ hxn]
    have hlinkT : ∀ j, j < m → TLink (wNode c.p base w) c.i (XX j) (KK (j + 1)) (XX (j + 1)) :=
      fun j hj => ⟨NN j, hNN j (by omega), hlinksK j hj⟩
    have hTA := treeOK_spaceSplitInPlace_sub (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) H.1 H.2.1 (KK m) H.2.2
      hT (reachS_tReach _ _ _ _ hrq) hqn hkl hqwf hqt hnL (updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1]; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1]; exact updN_self _ _ _)
      hf' hs'
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(H.2.2, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        rw [h1next]; dsimp only; omega)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        have hxL : XX (i - d) ≠ XX m := fun he => by
          have := hdist (i - d) m (by omega) (Nat.le_refl _) he; omega
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [hxL, show XX (i - d) ≠ w.next by omega, ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1, hN1]
        exact treeOK_updN_unreach _ c.i _ _ _ hTf hnf)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (tReach_chain_updN _ c.i _ hT m XX KK hlinkT (i - d)
          (by omega) (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))) H.1))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        have hzL : z ≠ XX m := fun h => by have := hXlt m (Nat.le_refl _); omega
        rw [h1n]
        simp only [hzL, show z ≠ w.next by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, (hs' c' z hc).1⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          have := hlinksAll u c' z (hsubf u c' z ⟨mm, hm, hc⟩); omega)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = XX m
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, _, _, _, _, h2R⟩
    have hres := getFromR_spaceSplitInPlace_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      hrangeL
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1, updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx3, updN_ne _ _ _ _ hx1])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by have := hlinksAll x c' z ⟨xn, hxn, hz⟩; omega)
    intro key' hkey'
    unfold wGet
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the leaf's bitmap, its time split or its space split
  refine writerWP_mono (post := fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')
    ?_ ?_
  · by_cases hsp : ¬ ((∃ old, (NN m).ks.getLast? = some (.del old)) ∧ (NN m).lastTime = some c.i) ∧
        c.p.M ≤ (NN m).size + 1 ∧ c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
          (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size
    · obtain ⟨hnotTD, hfull, hbig⟩ := hsp
      exact writerWP_appendDeleteKlong_spaceGen c (XX m) (NN m) cv (d + (m - 1)) w3 _ hlkL hne hnotTD
        hfull (fun s => by
          by_cases hf : (NN m).firstTime = some c.i
          · exact hcascadeSIP s hbig hf
          · exact hcascadeS s hbig hf)
    · exact writerWP_appendDeleteKlong_timeGen c base hvc pre cv (d + (m - 1)) rk (XX m) (NN m) w w3
        hfuel hkey hrk hvisL huniq hwfG hnL hleafm hnt hLt hr03 hlkL hne
        (fun h1 h2 => Nat.le_of_not_lt (fun h3 => hsp ⟨h1, h2, h3⟩)) hcascadeT
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4


set_option maxHeartbeats 1600000 in
/-- `writerWP_del_chain` on cost's chain of any kind (`writerWP_appendKlongs_chainGR`): the
nodes of the chain above the leaf split in place if the transaction made them; XX 0
with room for two klongs. -/
theorem writerWP_del_chainG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (m : Nat) (XX : Nat → NodeId) (KK : Nat → Nat)
    (NN : Nat → KNode) (hm : 1 ≤ m) (hmerges : c.p.merges = false) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf (pre ++ [cv]) = true)
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
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ chainSteps m XX KK))
    (htopX : pathEnd rk S0 = XX 0)
    (hNN : ∀ j, j ≤ m → wNode c.p base w (XX j) = some (NN j))
    (hleafm : (NN m).leaf = true)
    (hinner : ∀ j, j < m → (NN j).leaf = false)
    (hlinksK : ∀ j, j < m → (KK (j + 1), XX (j + 1)) ∈ (NN j).liveAt c.i)
    (hrange : ∀ j, 1 ≤ j → j < m → ¬ ChainRoom c (NN j) → ∀ c' z, (c', z) ∈ (NN j).live → 0 < c' →
      KK j ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (j - 1)).live → KK j < c'' → c' < c'')
    (hrangeL : ∀ c' z, (c', z) ∈ (NN m).live →
      KK m ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (m - 1)).live → KK m < c'' → c' < c'')
    (hlen : ∀ j, 1 ≤ j → j < m → ¬ ChainRoom c (NN j) →
      c.p.splitAbove < ((NN j).lastVersion c.i).size → 2 ≤ (NN j).live.length)
    (htop : ChainRoom c (NN 0))
    (hdist : ∀ j j', j ≤ m → j' ≤ m → XX j = XX j' → j = j')
    (hne : bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv) ≠ (NN m).lastBitmap)
    (hkeep : (NN m).allKeysIn (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have hend : pathEnd rk (S0 ++ chainSteps m XX KK) = XX m := pathEnd_chain rk S0 m XX KK htopX
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
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
  intro L' w3 ⟨⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn' hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hsteps : steps = S0 ++ chainSteps m XX KK := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro mm hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro mm hm; rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm
    · exact ⟨NN m, by rw [hend]; exact hNN m (Nat.le_refl _)⟩
  have hLL : L' = XX m := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNN m (Nat.le_refl _)] at hn'; cases hn'
  -- the chain's nodes are visited
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun mm hm => by rw [hend, hNN m (Nat.le_refl _)] at hm; cases hm; exact hleafm)
    (by rw [hend]; exact hvisL)
  have hvisX : ∀ j, j ≤ m → (XX j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    intro j hj
    cases j with
    | zero =>
      rw [← htopX]
      cases hS0 : S0.getLast? with
      | none =>
        have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
        subst this; simpa [pathEnd] using hvis.1
      | some e =>
        have hmem : e ∈ S0 := List.mem_of_getLast? hS0
        have := hvis.2 e (by simp [hmem])
        simpa [pathEnd, hS0] using this
    | succ j =>
      exact hvis.2 _ (List.mem_append_right _ (chainSteps_mem m XX KK j (by omega)))
  have hreachX : ∀ j, j ≤ m → ReachS (wNode c.p base w) c.i w.top.rootKey (XX j) :=
    fun j hj => eqVisits_reach _ _ _ cv c.p.fuel rk (XX j) cv hrrk (hvisX j hj)
  have hlkX : ∀ j, j ≤ m → w3.nodes.lookup (XX j) = some (NN j) :=
    fun j hj => hcache3 (XX j) (NN j) (hvisX j hj) (hNN j hj)
  have htkX : ∀ j, j ≤ m → w.taken.contains (XX j) = false :=
    fun j hj => ht (XX j, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ (hvisX j hj))
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
  have hXlt : ∀ j, j ≤ m → XX j < w.next := fun j hj => hsrcw3 _ (by rw [hlkX j hj]; rfl)
  -- the writer's path
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some (XX 0) := by
    rw [← htopX]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hp2'
    | some e =>
      rw [List.getLast?_append, hS0]
      simp [pathEnd, hS0]
  have hneP : w2'.path ++ S0 ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'; simp at hp2'
  obtain ⟨d, hd⟩ : ∃ d, (w2'.path ++ S0).length = d + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ chainSteps m XX KK := by rw [hp3]; simp
  have hlen3 : w3.path.length - 1 = d + m := by
    rw [hp3', List.length_append, chainSteps_length, hd]; omega
  have hpX : ∀ i, d ≤ i → i ≤ d + m → (w3.path[i]?).map (·.2) = some (XX (i - d)) := by
    intro i h1 h2
    rw [hp3']
    by_cases hi : i = d
    · subst hi
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd] at hlastP
      simpa using hlastP
    · rw [List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
      simp only [Option.map_some]
      congr 2; omega
  have hpK : ∀ i, d < i → i ≤ d + m → w3.path[i]? = some (some (KK (i - d)), XX (i - d)) := by
    intro i h1 h2
    rw [hp3', List.getElem?_append_right (by omega), hd, chainSteps_get m XX KK _ (by omega)]
    have : i - (d + 1) + 1 = i - d := by omega
    rw [this]
  -- the delete in the leaf
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen3]
  have hlkL := hlkX m (Nat.le_refl _)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c _ hlkL]
  have hnb : (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv) == (NN m).lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached _ _ c _ hlkL _ (fun gh => ?_)
  -- facts of the leaf, its parent and the delete's last version
  have hLt := htkX m (Nat.le_refl _)
  have hnL := hNN m (Nat.le_refl _)
  have hqn := hNN (m - 1) (by omega)
  have hnwf := hwfG _ _ hnL
  have hnt := htimesG _ _ hnL
  have hqwf := hwfG _ _ hqn
  have hqt := htimesG _ _ hqn
  have hql : (NN (m - 1)).leaf = false := hinner (m - 1) (by omega)
  have hmm : m - 1 + 1 = m := by omega
  have hkl : (KK m, XX m) ∈ (NN (m - 1)).liveAt c.i := by
    have := hlinksK (m - 1) (by omega); rw [hmm] at this; exact this
  have hkl' : (KK m, XX m) ∈ (NN (m - 1)).live := by
    rw [← KNode.liveAt_of_times _ c.i hqt]; exact hkl
  have hqL : XX (m - 1) ≠ XX m := fun h => by have := hdist _ _ (by omega) (Nat.le_refl _) h; omega
  have hrq := hreachX (m - 1) (by omega)
  have hrL := hreachX m (Nat.le_refl _)
  have honlyL : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', XX m) ∈ xn.liveAt c.i → x = XX (m - 1) ∧ c' = KK m :=
    fun x xn c' hx hxn hz => hT.oneLink x c' (XX (m - 1)) (KK m) (XX m)
      (reachS_tReach _ _ _ _ hx) (reachS_tReach _ _ _ _ hrq) ⟨xn, hxn, hz⟩ ⟨_, hqn, hkl⟩
  have hLroot : w.top.rootKey ≠ XX m := fun h =>
    hT.rootFree (XX (m - 1)) (KK m) (reachS_tReach _ _ _ _ hrq) ⟨_, hqn, by rw [h]; exact hkl⟩
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts (NN m) c.i cv
  have hlook0 := KNode.delete_live_lookup (NN m) c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have hnone : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnone, (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz, (hbase z hz).2]
  have hnoLinkW : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hlinksAll u c' z hl; omega
  have hyRW : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z :=
    fun z hz => not_reach_fresh _ c.i _ z hT (hfreshN z hz) (fun u c' _ => hnoLinkW z hz u c')
  have hw3N : ∀ w' : W, w'.nodes = w3.nodes → w'.taken = w3.taken →
      wNode c.p base w' = wNode c.p base w := by
    intro w' h1 h2
    rw [← hr03.1]
    funext z
    simp only [wNode, h1, h2]
  -- the chain at the parent, from a state that is w3's with the leaf's new nodes
  have hpq' : (w3.path[d + (m - 1)]?).map (·.2) = some (XX (m - 1)) := by
    have := hpX (d + (m - 1)) (by omega) (by omega)
    have he : d + (m - 1) - d = m - 1 := by omega
    rw [he] at this; exact this
  have hpk' : w3.path[d + (m - 1) + 1]? = some (some (KK m), XX m) := by
    have := hpK (d + (m - 1) + 1) (by omega) (by omega)
    have he : d + (m - 1) + 1 - d = m := by omega
    rw [he] at this; exact this
  have hdm : d + m = d + (m - 1) + 1 := by omega
  rw [hdm]
  -- the chain's premises above the leaf
  have hchainPre := fun (w1 : W) (ins : List (Nat × NodeId)) =>
    writerWP_appendKlongs_chainGR c base w3.path d (d + (m - 1)) (fun i => XX (i - d))
    (fun i => KK (i - d)) (fun i => NN (i - d))
    (fun i h1 h2 => hpX i h1 (by omega))
    (fun i h1 h2 => hpK i h1 (by omega))
    (fun i h1 h2 => by
      show (KK (i - d), XX (i - d)) ∈ (NN (i - 1 - d)).liveAt c.i
      have := hlinksK (i - 1 - d) (by omega)
      have he : i - 1 - d + 1 = i - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr _ c' z hz hc => by
      have := hrange (i - d) (by omega) (by omega) hnr c' z hz hc
      have he : i - d - 1 = i - 1 - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr hsp => by
      by_cases hi : i = d
      · subst hi; simp only [Nat.sub_self] at hnr; exact absurd htop hnr
      · exact hlen (i - d) (by omega) (by omega) hnr hsp)
    (fun i h1 h2 => hwfG _ _ (hNN (i - d) (by omega)))
    (fun i h1 h2 => htimesG _ _ (hNN (i - d) (by omega)))
    (Or.inl (by simpa using htop))
    (fun i i' h1 h2 h3 h4 he => by
      have := hdist (i - d) (i' - d) (by omega) (by omega) he
      omega)
    (fun i h1 h2 hnr _ => by
      by_cases hi : i = d
      · subst hi; simp only [Nat.sub_self] at hnr; exact absurd htop hnr
      · refine ⟨by omega, ?_⟩
        show (NN (i - 1 - d)).leaf = false
        exact hinner (i - 1 - d) (by omega))
    (m - 1) (Nat.le_refl _) w1 ins
  have hdm1 : d + (m - 1) - d = m - 1 := by omega
  -- the post of the delete
  have hlast : ∀ s : String, ({ w3 with trail := s :: w3.trail } : W).nodes = w3.nodes ∧
      ({ w3 with trail := s :: w3.trail } : W).taken = w3.taken ∧
      ({ w3 with trail := s :: w3.trail } : W).path = w3.path ∧
      ({ w3 with trail := s :: w3.trail } : W).next = w3.next ∧
      ({ w3 with trail := s :: w3.trail } : W).top = w3.top ∧
      ({ w3 with trail := s :: w3.trail } : W).vals = w3.vals := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- a time split of the leaf, not in place
  have hcascadeT : ∀ (compact : Bool) (s : String),
      (!compact && decide (((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size > c.p.splitAbove)) = false →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact s hcs hfirst
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    generalize hLv : ((⟨(NN m).leaf, ((NN m).lastVersionGivenDel c.i
      (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).ks⟩ : KNode)) = Lv
    apply writerWP_handleFullWith_time_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ compact c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hcs (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hs4] at h1n h1next
    rw [hs1] at h1n
    rw [hLv] at h1n
    have hfree0 : w3.nodes.lookup w3.next = none := by
      cases h' : w3.nodes.lookup w3.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next Lv := by
      rw [wNode_append_updN c.p base w3 w1 Lv h1n h1t' hfree0
        (by rw [hr03.2.2.1, hnext3]; exact hntake _ (Nat.le_refl _))]
      rw [hw3N w3 rfl rfl, hnext3]
    rw [hnext3] at h1n h1next
    have hLvwf : klongsWf Lv.ks = true := by rw [← hLv]; exact hwf0
    have hLvt : ∀ s, Klong.time s ∈ Lv.ks → s ≤ c.i := by rw [← hLv]; exact hlt
    have hLvsub : ∀ c' z, (c', z) ∈ Lv.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hLvt] at h
      rw [KNode.liveAt_of_times _ c.i hnt]
      rw [← hLv, hleq] at h
      exact hlsub c' z h
    have hLvlook : ∀ c', Lv.live.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
      intro c'; rw [← hLv, hleq]; exact hlook0 c'
    -- the tree with the parent's klong put
    obtain ⟨hTA, hRA⟩ := treeOK_timeSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) Lv
      ((NN (m - 1)).add c.i (.key (KK m) w.next)) (KK m) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL
      (updN_self _ _ _)
      (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h)
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      hLvsub
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hchain := hchainPre w1 [(KK m, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by intro q hq; simp at hq; rw [hq, h1next]; simp)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n, List.lookup_append, hlkX (i - d) (by omega)]; rfl
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [hN1, h1top, hs5, hr03.2.1]
        exact treeOK_updN_unreach _ c.i _ _ _ hT (hyRW _ (Nat.le_refl _)))
      (by
        intro i h1 h2
        rw [hN1, h1top, hs5, hr03.2.1]
        obtain ⟨a, ha⟩ := (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n, List.lookup_append]
        have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
        cases h' : w3.nodes.lookup z with
        | none => simp [List.lookup, hb]
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, hLvsub c' z hc⟩; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun _ hnr => absurd (by simpa using htop) hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hzy : z = w.next
        · rw [hzy, updN_self] at hz; cases hz; exact hLvwf
        · rw [updN_ne _ _ _ _ hzy] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        have hv1 : wValue base w1 = wValue base w := by
          funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    rw [hs4, hnext3]
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega),
        h1n, List.lookup_append, hlkL]
      rfl
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2 : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hres := getFromR_timeSplit_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) Lv (KK m) pre cv rk hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      (by rw [← hLv]; exact hleafm) hLvwf hLvt hLvlook
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      (updN_self _ _ _)
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hnoval _ _ hnL) (hfreshV _ (Nat.le_refl _)) hqL
      (fun h => by have := hXlt m (Nat.le_refl _); omega)
      (fun h => by have := hXlt (m - 1) (by omega); omega)
      (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by
        have := hlinksAll x c' z ⟨xn, hxn, hz⟩; omega)
    intro key' hkey'
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the delete's last version as pairs
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hlastE : (NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)) =
      ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hleafm, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  have hpairsN : ∀ c' z, (c', z) ∈ pairs → (c', z) ∈ (NN m).live := by
    intro c' z hm
    have hl := lookup_some_of_mem hpn hm
    rw [hpl] at hl
    by_cases hc : c' = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (c' == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact lookup_some_mem hl
  -- a space split of the leaf, which existed before
  have hcascadeS : ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    have hrmemN : r ∈ (NN m).live := hpairsN r.1 r.2 (List.mem_of_mem_drop (List.mem_of_head? hr))
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    apply writerWP_handleFullWith_space_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have h12 : w3'.next ≠ w3'.next + 2 := by omega
    have h12' : w.next ≠ w.next + 2 := by omega
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have htk2 : w3'.taken.contains (w3'.next + 2) = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (by omega)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next H.1) (w.next + 2) H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t h12 htk0 htk2, hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → c' < H.2.2 ∧ (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨h1, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hs : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i →
        ∃ c0, H.2.2 ≤ c0 ∧ c' = (fun c0 => c0) c0 ∧ (c0, z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨c', h1, rfl, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hqwf1 := KNode.add_key_wf (NN (m - 1)) c.i (KK m) w.next hqwf
    have hqt1 := KNode.add_times (NN (m - 1)) c.i (.key (KK m) w.next) (fun _ h => by cases h) hqt
    have hqlinks : ∀ c' z, (c', z) ∈ ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))).liveAt c.i →
        (c' = H.2.2 ∧ z = w.next + 2) ∨ (c' ≠ H.2.2 ∧ c' = KK m ∧ z = w.next) ∨
        (c' ≠ H.2.2 ∧ c' ≠ KK m ∧ (c', z) ∈ (NN (m - 1)).liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf1 hqt1 c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXq2 : XX (m - 1) ≠ w.next + 2 := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have hXL2 : XX m ≠ w.next + 2 := fun h => by have := hXlt m (Nat.le_refl _); omega
    obtain ⟨hTA, hRA⟩ := treeOK_spaceSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (w.next + 2) (NN (m - 1)) (NN m) H.1 H.2.1
      ([(KK m, w.next), (H.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (NN (m - 1)))
      (KK m) H.2.2 (fun c0 => c0) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL (updN_self _ _ _) hqlinks
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12']; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq2.symm, hN1]; exact updN_self _ _ _)
      hf hs
      (by
        intro z hz1 hz2 hz3 hz4
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) h12'
      (fun z hz u c' _ hl => by
        rcases hz with hz | hz <;> (subst hz; exact hnoLinkW _ (by omega) u c' hl))
    have hagree : ∀ x, TReach (wNode c.p base w) c.i w.top.rootKey x →
        wNode c.p base w1 x = wNode c.p base w x := by
      intro x hx
      have h1 : x ≠ w.next := fun h => by subst h; exact hyRW _ (Nat.le_refl _) hx
      have h2 : x ≠ w.next + 2 := fun h => by subst h; exact hyRW _ (by omega) hx
      rw [hN1, updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h1]
    have hins : InsOK (NN (m - 1)) [(KK m, w.next), (H.2.2, w.next + 2)] :=
      Or.inr ⟨KK m, w.next, H.2.2, w.next + 2, rfl, by rw [hscr]; exact (hrangeL r.1 r.2 hrmemN).1,
        fun c'' z'' hz hlt => by rw [hscr]; exact (hrangeL r.1 r.2 hrmemN).2 c'' z'' hz hlt⟩
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(KK m, w.next), (H.2.2, w.next + 2)] (by simp only [hdm1]; exact hins)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rw [h1next]
        rcases hq with hq | hq <;> (subst hq; dsimp only; omega))
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [show XX (i - d) ≠ w.next by omega, show XX (i - d) ≠ w.next + 2 by omega,
            ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1]
        exact treeOK_of_agree _ _ _ _ hT hagree)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n]
        simp only [show z ≠ w.next by omega, show z ≠ w.next + 2 by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next + 2
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          rw [KNode.liveAt_of_times _ c.i hHt.2] at hc
          have := hlinksAll _ _ _ ⟨_, hnL, by
            rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hsh c' z hc).2⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          by_cases hu1 : u = w.next
          · rw [hu1, updN_self] at hm
            simp only [Option.some.injEq] at hm
            subst hm
            rw [KNode.liveAt_of_times _ c.i hHt.1] at hc
            have := hlinksAll _ _ _ ⟨_, hnL, by
              rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hfh c' z hc).2⟩
            omega
          · rw [updN_ne _ _ _ _ hu1] at hm
            have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun _ hnr => absurd (by simpa using htop) hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next + 2
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = w.next
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega), h1n]
      simp only [hXL1, hXL2, ↓reduceIte, hs1]
      exact hlkL
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2' : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2'
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hres := getFromR_spaceSplit_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (w.next + 2) (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      hrangeL
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12', updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq2.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3 hx4
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx4, updN_ne _ _ _ _ hx3])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by
        have := hlinksAll x c' z ⟨xn, hxn, hz⟩; exact ⟨by omega, by omega⟩)
    intro key' hkey'
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- a space split in place of the leaf, which the transaction made
  have hcascadeSIP : ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime = some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    apply writerWP_handleFullWith_spaceInPlace_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m)
      (NN (m - 1)) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hnx]; exact hXlt m (Nat.le_refl _))
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have htkL : w3'.taken.contains (XX m) = false := by rw [hs2, hr03.2.2.1]; exact hLt
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (XX m) H.1) w.next H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t (by rw [hnx]; exact hXL1) htkL htk0,
        hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf' : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ c' < H.2.2 := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    have hs' : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ H.2.2 ≤ c' := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    -- the leaf with its first half: links among the leaf's
    have hsubf : ∀ x c' y, TLink (updN (wNode c.p base w) (XX m) H.1) c.i x c' y →
        TLink (wNode c.p base w) c.i x c' y := by
      intro x c' y hl
      obtain ⟨mm, hm, hc⟩ := hl
      by_cases hx : x = XX m
      · subst hx
        rw [updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        exact ⟨_, hnL, (hf' c' y hc).1⟩
      · rw [updN_ne _ _ _ _ hx] at hm; exact ⟨mm, hm, hc⟩
    have hreachf := tReach_of_sublinks _ _ c.i w.top.rootKey hsubf
    have hTf : TreeOK (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey :=
      treeOK_of_node_shrink _ _ c.i _ (XX m) (NN m) H.1 hT hnL (updN_self _ _ _)
        (fun y hy => updN_ne _ _ _ _ hy) (fun c' z h => (hf' c' z h).1)
    have hnf : ¬ TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey w.next :=
      fun h => hyRW _ (Nat.le_refl _) (hreachf _ h)
    have hagree : ∀ x, TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey x →
        wNode c.p base w1 x = updN (wNode c.p base w) (XX m) H.1 x := by
      intro x hx
      have hxn : x ≠ w.next := fun h => by subst h; exact hnf hx
      rw [hN1, updN_ne _ _ _ _ hxn]
    have hlinkT : ∀ j, j < m → TLink (wNode c.p base w) c.i (XX j) (KK (j + 1)) (XX (j + 1)) :=
      fun j hj => ⟨NN j, hNN j (by omega), hlinksK j hj⟩
    have hTA := treeOK_spaceSplitInPlace_sub (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) H.1 H.2.1 (KK m) H.2.2
      hT (reachS_tReach _ _ _ _ hrq) hqn hkl hqwf hqt hnL (updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1]; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1]; exact updN_self _ _ _)
      hf' hs'
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(H.2.2, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        rw [h1next]; dsimp only; omega)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        have hxL : XX (i - d) ≠ XX m := fun he => by
          have := hdist (i - d) m (by omega) (Nat.le_refl _) he; omega
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [hxL, show XX (i - d) ≠ w.next by omega, ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1, hN1]
        exact treeOK_updN_unreach _ c.i _ _ _ hTf hnf)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (tReach_chain_updN _ c.i _ hT m XX KK hlinkT (i - d)
          (by omega) (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))) H.1))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        have hzL : z ≠ XX m := fun h => by have := hXlt m (Nat.le_refl _); omega
        rw [h1n]
        simp only [hzL, show z ≠ w.next by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, (hs' c' z hc).1⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          have := hlinksAll u c' z (hsubf u c' z ⟨mm, hm, hc⟩); omega)
      (fun _ hnr => absurd (by simpa using htop) hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = XX m
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, _, _, _, _, h2R⟩
    have hres := getFromR_spaceSplitInPlace_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      hrangeL
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1, updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx3, updN_ne _ _ _ _ hx1])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by have := hlinksAll x c' z ⟨xn, hxn, hz⟩; omega)
    intro key' hkey'
    unfold wGet
    rw [h2R key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the leaf's bitmap, its time split or its space split
  refine writerWP_mono (post := fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')
    ?_ ?_
  · by_cases hsp : ¬ ((∃ old, (NN m).ks.getLast? = some (.del old)) ∧ (NN m).lastTime = some c.i) ∧
        c.p.M ≤ (NN m).size + 1 ∧ c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
          (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size
    · obtain ⟨hnotTD, hfull, hbig⟩ := hsp
      exact writerWP_appendDeleteKlong_spaceGen c (XX m) (NN m) cv (d + (m - 1)) w3 _ hlkL hne hnotTD
        hfull (fun s => by
          by_cases hf : (NN m).firstTime = some c.i
          · exact hcascadeSIP s hbig hf
          · exact hcascadeS s hbig hf)
    · exact writerWP_appendDeleteKlong_timeGen c base hvc pre cv (d + (m - 1)) rk (XX m) (NN m) w w3
        hfuel hkey hrk hvisL huniq hwfG hnL hleafm hnt hLt hr03 hlkL hne
        (fun h1 h2 => Nat.le_of_not_lt (fun h3 => hsp ⟨h1, h2, h3⟩)) hcascadeT
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

end SIS.Tree
