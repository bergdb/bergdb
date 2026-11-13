import SIS.Tree.GetCascadeChain

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

end SIS.Tree
