import SIS.Tree.GetFinal

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete into a full leaf whose parent is full too (bergdb 024-12, TP10;
the cascades): the descent of a delete with its last three nodes g, q, L
(`writerWP_del_path`). -/

/-- The descent of a delete whose access path from the segment root rk ends
with g, q, L (`PathFrom`): the writer's state after it, with its path and its
cache of the three nodes, goes on with the delete in L. -/
theorem writerWP_del_path (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (post : Bool → W → Prop)
    (hk : ∀ d'' (w3 : W), ReadsAs c.p base w w3 →
      w3.nodes.lookup L = some n → w3.nodes.lookup q = some qn →
      w3.nodes.lookup (pathEnd rk S0) = some gn →
      (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
      (w3.path[d'']?).map (·.2) = some (pathEnd rk S0) →
      w3.path[d'' + 1]? = some (some kq, q) → w3.path[d'' + 1 + 1]? = some (some k1, L) →
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (pathEnd rk S0, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      WriterWP (do
        let noop ← deleteUpward L (d'' + 1 + 1) cv (pre ++ [cv])
        if !noop then do let _ ← fresh; pure noop else pure noop) c w3 post) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w post := by
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hk
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
  have hend : pathEnd rk (S0 ++ [(some kq, q), (some k1, L)]) = L := by
    rw [show S0 ++ [(some kq, q), (some k1, L)] = (S0 ++ [(some kq, q)]) ++ [(some k1, L)] by simp,
      pathEnd_append]
  have hsteps : steps = S0 ++ [(some kq, q), (some k1, L)] := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro m hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro m hm; rw [hend, hNL] at hm; cases hm; exact hnl
    · exact ⟨n, by rw [hend]; exact hNL⟩
  have hLL : L' = L := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNL] at hn'; cases hn'
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun m hm => by rw [hend, hNL] at hm; cases hm; exact hnl) (by rw [hend]; exact hvisL)
  have hqv : (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk :=
    hvis.2 (some kq, q) (by simp)
  have hgv : (g, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    rw [hgdef]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hvis.1
    | some e =>
      have hmem : e ∈ S0 := List.mem_of_getLast? hS0
      have := hvis.2 e (by simp [hmem])
      simpa [pathEnd, hS0] using this
  have hlq3 : w3.nodes.lookup q = some qn := hcache3 q qn hqv hNq
  have hlg3 : w3.nodes.lookup g = some gn := hcache3 g gn hgv hNg
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some g := by
    rw [hgdef]
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
  obtain ⟨d'', hd''⟩ : ∃ d'', (w2'.path ++ S0).length = d'' + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ [(some kq, q), (some k1, L)] := by
    rw [hp3]; simp
  have hlen : w3.path.length - 1 = d'' + 1 + 1 := by
    rw [hp3']; simp only [List.length_append, List.length_cons, List.length_nil] at hd'' ⊢; omega
  have hpg : (w3.path[d'']?).map (·.2) = some g := by
    rw [hp3', List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?, hd''] at hlastP
    simpa using hlastP
  have hpq : w3.path[d'' + 1]? = some (some kq, q) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  have hpk : w3.path[d'' + 1 + 1]? = some (some k1, L) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen]
  have := hk d'' w3 hr03 (by simpa using hlk3) hlq3 hlg3 hsrcw3 hpg hpq hpk hvisL hqv hgv
  simpa only [writerWP_bind] using this

/-! ## The writer: a delete's time split of a leaf whose parent is full and time split -/

/-- The state after a time split of the leaf L into its last version `last`
whose parent q, full, is time split too, below the grandparent g with room. -/
def DelTimeSplit2After (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) : Prop :=
  ∃ lq : KNode, lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = if k1 == q' then some w.next else qn.live.lookup q') ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2)))
      else if x = w.next then some ⟨n.leaf, last.ks⟩
      else if x = w.next + 2 then some ⟨qn.leaf, lq.ks⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_delTimeSplit2 (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hqfull : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hLn : L < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L []
      last compact) c w
      (fun _ w' => DelTimeSplit2After c w w' L q g n qn gn kq k1 last) := by
  have hpq' : (w.path[d'' + 1]?).map (·.2) = some q := by rw [hpq]; rfl
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d'' + 1]? with
  | none => rw [hp] at hpq'; cases hpq'
  | some e =>
    rw [hp] at hpq'
    simp only [Option.map_some, Option.some.injEq] at hpq'
    simp only [writerWP_pure]
    rw [hpq']
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ (lq : KNode), lq.leaf = qn.leaf → klongsWf lq.ks = true →
        (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) →
        (∀ q', lq.live.lookup q' = if k1 == q' then some w.next else qn.live.lookup q') →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        (∀ x, w2.nodes.lookup x =
          if x = q then some (qn.toPrev (c.i - 1))
          else if x = g then some (gn.add c.i (.key kq (w.next + 2)))
          else if x = w.next + 2 then some ⟨qn.leaf, lq.ks⟩
          else (w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))]).lookup x) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => DelTimeSplit2After c w w' L q g n qn gn kq k1 last) := by
      intro lq hq_leaf hq_wf hq_times hq_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n]
        simp only [show L ≠ q from fun h => hqL h.symm, show L ≠ g from fun h => hgL h.symm,
          show L ≠ w.next + 2 by omega, ↓reduceIte, List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, ?_⟩
      intro x
      show (upsert _ L _).lookup x = _
      rw [lookup_upsert, h2n]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hxg : x = g
          · simp [hxg]
          · simp only [hxg, ↓reduceIte, List.lookup_append]
            by_cases hx2 : x = w.next + 2
            · simp [hx2, show w.next + 2 ≠ w.next by omega]
            · simp only [hx2, ↓reduceIte]
              by_cases hxy : x = w.next
              · subst hxy; rw [hny]; simp [List.lookup]
              · simp only [hxy, ↓reduceIte]
                cases h : w.nodes.lookup x with
                | some m => rfl
                | none =>
                  show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := last.ks })].lookup x) = none
                  rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    have hup : ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))] →
        w1.next = w.next + 2 → w1.path = w.path → w1.taken = w.taken → w1.top = w.top →
        w1.vals = w.vals →
        WriterWP (appendKlongs (d'' + 1) q [(k1, w.next)]) c w1 (fun _ w' =>
          WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w'
            (fun _ w'' => DelTimeSplit2After c w w'' L q g n qn gn kq k1 last)) := by
      intro w1 h1n h1x h1p h1t h1top h1v
      refine writerWP_mono (writerWP_appendKlongs_timeSplit_gen d'' q g qn gn kq k1 w.next c w1
        (by rw [h1n, List.lookup_append, hlq]; rfl) (by rw [h1n, List.lookup_append, hlg]; rfl)
        hgq hgl hqfirst hqfull hqsplit (by rw [h1p]; exact hpg) (by rw [h1p]; exact hpq)
        hroomg hdeadg
        (by
          rw [h1n, h1x, List.lookup_append, hny2]
          show ([(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))].lookup (w.next + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)) ?_
      intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, h2n⟩
      refine hfinal lq hq_leaf hq_wf hq_times ?_ w2
        (by rw [h2t, h1t]) (by rw [h2top, h1top]) (by rw [h2v, h1v]) ?_
      · intro q'; rw [hq_look q']
      · intro x; rw [h2n x, h1x, h1n]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
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

/-! ## The reading after a delete's time split and its parent's -/

/-- `getFromR_timeSplit2` for a delete: the leaf's last version without cv at
Y. -/
theorem getFromR_delTimeSplit2 (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g Y Yq : NodeId)
    (n qn gn ln lqn : KNode) (k1 kq : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live)
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ c, ln.live.lookup c = if c == cv then none else n.live.lookup c)
    (hN2Yq : N2 Yq = some lqn) (hlql : lqn.leaf = qn.leaf) (hlqwf : klongsWf lqn.ks = true)
    (hlqt : ∀ s, Klong.time s ∈ lqn.ks → s ≤ i)
    (hlqlook : ∀ c, lqn.live.lookup c = if k1 == c then some Y else qn.live.lookup c)
    (hN2g : N2 g = some (gn.add i (.key kq Yq)))
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ Y → x ≠ Yq → N2 x = N x)
    (hV2L : V L = none) (hV2Y : V Y = none) (hV2q : V q = none) (hV2Yq : V Yq = none)
    (hqL : q ≠ L) (hYL : Y ≠ L) (hYq : Y ≠ q) (hgq : g ≠ q) (hgL : g ≠ L) (hgY : g ≠ Y)
    (hYqq : Yq ≠ q) (hYqg : Yq ≠ g) (hYqL : Yq ≠ L) (hYqY : Yq ≠ Y)
    (hNYq : N Yq = none) (hNY : N Y = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrootq : root ≠ q) (hrootYq : root ≠ Yq)
    (hrq : ReachS N i root q) (hrg : ReachS N i root g)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (honlyq : ∀ x xn c, ReachS N i root x → N x = some xn → (c, q) ∈ xn.liveAt i →
      x = g ∧ c = kq)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Y ∧ z ≠ Yq) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  -- the reader in between: q with the klong to Y, g as it was
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some (qn.add i (.key k1 Y)) else if x = g then some gn
    else if x = Yq then none else N2 x
  have hN1q : N1 q = some (qn.add i (.key k1 Y)) := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1Y : N1 Y = some ln := by simp [N1, hYq, hgY.symm, hYqY.symm, hN2Y]
  have hN1Yq : N1 Yq = none := by simp [N1, hYqq, hYqg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ Y → N1 x = N x := by
    intro x h1 h2 h3
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxY : x = Yq
      · subst hxY; simp [N1, h2, hxg, hNYq]
      · simp only [N1, h2, hxg, hxY, ↓reduceIte]
        exact hN2 x h1 h2 hxg h3 hxY
  -- step A: N1 reads as the put
  have hA := getFromR_timeSplit_del N N1 V i fuel hfuel root L q Y n qn ln k1 pre cv rk
    hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hlnl hlnwf hlnt hlnlook hN1Y hN1q hN1 hV2L hV2Y
    hqL hYL hYq hNY hrootL hrootY hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => (hfr x xn c z hx hn hz).1)
  -- the nodes N1 reaches: N's but L, and Y and v
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hgkq : (kq, q) ∈ gn.liveAt i := by rw [KNode.liveAt_of_times gn i hgt]; exact hkq
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hqadd : ∀ c z, (c, z) ∈ (qn.add i (.key k1 Y)).liveAt i → ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = Y := by
    intro c z hz
    have ht2 := KNode.add_times qn i (.key k1 Y) (fun s h => by cases h) hqt
    rw [KNode.liveAt_of_times _ i ht2] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [KNode.add_key_live_lookup_of_wf qn i k1 c Y hqwf] at this
    by_cases hc : k1 = c
    · subst hc; simp at this; exact Or.inr this.symm
    · have hc' : (k1 == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      left; rw [KNode.liveAt_of_times qn i hqt]
      exact ⟨lookup_some_mem this, fun h => hc h.symm⟩
  have hlnmem : ∀ c z, (c, z) ∈ ln.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [KNode.liveAt_of_times ln i hlnt] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup ln) hz
    rw [hlnlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem this
  have hreachNe : ∀ x, ReachS N i root x → x ≠ Y ∧ x ≠ Yq := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootY, hrootYq⟩
    | step x' xn c _ hx' hn hz =>
      have := hfr x' xn c _ hx' hn hz
      exact ⟨this.1, this.2⟩
  have hreach1 : ∀ x, ReachS N1 i root x → (ReachS N i root x ∧ x ≠ L) ∨ x = Y := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hqadd c z hz with ⟨hz', hck⟩ | hzY
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr hzY
        · rw [hN1 x' hx'L hxq (hreachNe x' hx').1] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · subst x'
        rw [hN1Y] at hn; cases hn
        have hz' := hlnmem c z hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
  -- step B: q renamed Yq at g
  have hqaddwf : klongsWf (qn.add i (.key k1 Y)).ks = true := KNode.add_key_wf qn i k1 Y hqwf
  have hqaddt := KNode.add_times qn i (.key k1 Y) (fun s h => by cases h) hqt
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn _ hn
    by_cases hxq : x = q
    · subst hxq; rw [hN1q] at hn; cases hn; exact hqaddwf
    · by_cases hxg : x = g
      · subst hxg; rw [hN1g] at hn; cases hn; exact hgwf
      · by_cases hxYq : x = Yq
        · subst hxYq; rw [hN1Yq] at hn; cases hn
        · have hn2 : N2 x = some xn := by
            simp only [N1, hxq, hxg, hxYq, ↓reduceIte] at hn; exact hn
          by_cases hxL : x = L
          · subst hxL; exact hN2L xn hn2
          · by_cases hxY : x = Y
            · subst hxY; rw [hN2Y] at hn2; cases hn2; exact hlnwf
            · rw [hN2 x hxL hxq hxg hxY hxYq] at hn2; exact hwfG x xn hn2
  have hnotq1 : ∀ x xn, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn hx hxg hn c z hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c x hz with ⟨hz', _⟩ | hzY
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hYq hzY.symm
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · subst hxY
      rw [hN1Y] at hn; cases hn
      exact hgL (honlyq L n c hrL hNL (hlnmem c z hz)).1.symm
  have hnotYq1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ Yq := by
    intro x xn hx hn c z hz hzY
    subst hzY
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c z hz with ⟨hz', _⟩ | hzY
        · exact (hfr x qn c z hx' hNq hz').2 rfl
        · exact hYqY hzY
      · by_cases hxg : x = g
        · subst hxg
          rw [hN1g] at hn; cases hn
          exact (hfr x gn c z hx' hNg hz).2 rfl
        · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
          exact (hfr x xn c z hx' hn hz).2 rfl
    · subst hxY
      rw [hN1Y] at hn; cases hn
      exact (hfr L n c z hrL hNL (hlnmem c z hz)).2 rfl
  have hS := renSim_timeSplitGen N1 N2 i root q g Yq gn (qn.add i (.key k1 Y)) lqn kq
    hgq hYqq hYqg hN1q hN1g hgl hgwf hgt hkq
    (fun c z hz hzq => by
      subst hzq
      exact (honlyq g gn c hrg hNg hz).2)
    hN2Yq (by rw [KNode.add_leaf]; exact hlql) hqaddwf hlqwf hqaddt hlqt
    (fun c => by rw [hlqlook c, KNode.add_key_live_lookup_of_wf qn i k1 c Y hqwf])
    hN2g
    (fun x h1 h2 h3 => by simp only [N1, h1, h2, h3, ↓reduceIte])
    hwf1 hnotq1 hnotYq1
  have hren : ∀ key', getFromR N1 V i fuel key' root = getFromR N2 V i fuel key' root := by
    intro key'
    have := getFromR_ren N1 N2 V V i fuel _ q Yq hS (fun a => by
      by_cases ha : a = q
      · subst ha; simp [hV2q, hV2Yq]
      · simp [ha]) key' root ⟨hrootYq, ReachS.root⟩
    rw [this]
    simp [hrootq]
  intro key' hkey'
  rw [← hren key']
  exact hA key' hkey'

/-! ## The bitmap of a delete whose leaf's parent is full -/

set_option linter.unusedSimpArgs false in
/-- `writerWP_appendDeleteKlong_get` with the parent q full and time split, below
the grandparent g with room. -/
theorem writerWP_appendDeleteKlong_get2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv k1 kq d'' : Nat) (rk L q g : NodeId) (n qn gn : KNode) (w w3 : W)
    (hfuel : 1 ≤ c.p.fuel) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hLt : w.taken.contains L = false) (hLval : wValue base w L = none)
    (hLroot : L ≠ w.top.rootKey)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hk1 : (k1, L) ∈ qn.live) (hqL : q ≠ L)
    (hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q)
    (hqfirst : qn.firstTime ≠ some c.i)
    (hNg : wNode c.p base w g = some gn) (hgl : gn.leaf = false)
    (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) (hkq : (kq, q) ∈ gn.live) (hgq : g ≠ q)
    (hgL : g ≠ L) (hgtk : w.taken.contains g = false)
    (hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g)
    (honlyq : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', q) ∈ xn.liveAt c.i → x = g ∧ c' = kq)
    (hqval : wValue base w q = none) (hqroot : q ≠ w.top.rootKey)
    (honlyL : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', L) ∈ xn.liveAt c.i → x = q ∧ c' = k1)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next)
    (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hlg3 : w3.nodes.lookup g = some gn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hpg : (w3.path[d'']?).map (·.2) = some g) (hpq : w3.path[d'' + 1]? = some (some kq, q))
    (hpk : w3.path[d'' + 1 + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hqfull : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (appendDeleteKlong L (d'' + 1 + 1) cv) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hnwf := hwfG L n hn
  have hqwf := hwfG q qn hqn
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  -- a state whose leaf L changed to n2, n's live klongs but cv's: the delete
  have hleafc : ∀ (n2 : KNode) (w6 : W), n2.leaf = true → w6.top = w.top →
      w6.taken = w.taken → w6.vals = w.vals →
      (∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x) → wNode c.p base w6 L = some n2 →
      (∀ c', (n2.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      ∀ key', keyWf key' = true →
        wGet c.p c.i base w6 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key' := by
    intro n2 w6 hl2 h6top h6taken h6vals hN hNL6 hs2
    have hV : ∀ y, wValue base w y = wValue base w6 y := by
      intro y; simp only [wValue, h6taken, h6vals]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n n2 hfuel h6top hN
      hn hNL6 hnl hl2 (fun c' hc' => by
        rw [hs2 c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL huniq (fun _ _ _ _ y _ _ _ _ _ => hV y)
    intro key' hkey'
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, hs2 cv]
      simp
    · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      exact hother key' hkey' (fun h => hk h.symm)
  -- the last version without cv
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlook0 hwf0
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hsplit hlook0 hwf0
  have hmwf : klongsWf (⟨n.leaf, last.ks⟩ : KNode).ks = true := hwf0
  have hmt : ∀ s, Klong.time s ∈ (⟨n.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := hlt
  have hmlook : ∀ c', (⟨n.leaf, last.ks⟩ : KNode).live.lookup c' =
      if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [hleq]; exact hlook0 c'
  have hms : ∀ c', ((⟨n.leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [KNode.searchEq_live _ c.i hmwf hmt, hmlook, KNode.searchEq_live n c.i hnwf hnt]
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact hcs s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ (d'' + 1 + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, h4v, hN4⟩
      refine hleafc ⟨n.leaf, last.ks⟩ w4 hnl (h4top.trans hr3'.2.1) (h4t.trans hr3'.2.2.1)
        (h4v.trans hr3'.2.2.2.1) ?_ (by rw [hN4]; simp) hms
      intro x hx; rw [hN4]; simp only [hx, ↓reduceIte]; rw [hr3'.1]
    · have hny : w3'.nodes.lookup w3'.next = none := by
        cases h' : w3'.nodes.lookup w3'.next with
        | none => rfl
        | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
      have hny2 : w3'.nodes.lookup (w3'.next + 2) = none := by
        cases h' : w3'.nodes.lookup (w3'.next + 2) with
        | none => rfl
        | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
      have hLlt : L < w.next := hsrc3 L (by rw [hlk3]; rfl)
      have hqlt : q < w.next := hsrc3 q (by rw [hlq3]; rfl)
      have hglt : g < w.next := hsrc3 g (by rw [hlg3]; rfl)
      refine writerWP_mono (writerWP_handleFullWith_delTimeSplit2 d'' L q g n qn gn kq k1 last
        compact c w3' hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hnew hqfirst hcs
        (by rw [hnext3']; exact hqfull) hqsplit hpg' hpq' hpk' hroomg hdeadg hny hny2
        (by rw [hnext3']; exact hLlt)) ?_
      intro _ w4 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h4t, h4top, h4v, h4nodes⟩
      rw [hnext3'] at h4nodes hq_look
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hvl : w4.vals = w.vals := h4v.trans hr3'.2.2.2.1
      have htp : w4.top = w.top := h4top.trans hr3'.2.1
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
      have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
        intro z hz
        cases h' : w.nodes.lookup z with
        | none => rfl
        | some _ => have := hidn z (by rw [h']; rfl); omega
      have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
        intro z hz
        simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnodenone z hz,
          (hbase z hz).1]
      have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
        intro z hz
        simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz,
          (hbase z hz).2]
      have hV4 : wValue base w4 = wValue base w := by
        funext a; simp only [wValue, htk, hvl]
      have hlqm : ({ leaf := qn.leaf, ks := lq.ks } : KNode) = lq := by
        cases lq; simp only at hq_leaf ⊢; rw [hq_leaf]
      have hres := getFromR_delTimeSplit2 (wNode c.p base w) (wNode c.p base w4) (wValue base w)
        c.i c.p.fuel hfuel w.top.rootKey L q g w.next (w.next + 2) n qn gn ⟨n.leaf, last.ks⟩
        ⟨qn.leaf, lq.ks⟩ k1 kq pre cv rk hwfG hn hnl hnt hqn hql hqt hk1 hNg hgl hgt hkq
        (by
          simp only [wNode, htk, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4nodes,
            show w.next ≠ L by omega, show w.next ≠ q by omega, show w.next ≠ g by omega])
        hnl hmwf hmt hmlook
        (by
          simp only [wNode, htk, hntake (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
            h4nodes, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega,
            show w.next + 2 ≠ g by omega, show w.next + 2 ≠ w.next by omega])
        rfl (by rw [hlqm]; exact hq_wf) (by rw [hlqm]; exact hq_times)
        (by intro c'; rw [hlqm, hq_look c'])
        (by simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq])
        (by
          intro m hm
          simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes,
            Option.some.injEq] at hm
          rw [← hm]; exact KNode.toPrev_wf n _ hnwf)
        (by
          intro x hxL hxq hxg hxY hxYq
          rw [← hr3'.1]
          simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxY, hxYq, ↓reduceIte])
        hLval (hfreshV _ (Nat.le_refl _)) hqval (hfreshV _ (by omega))
        hqL (by omega) (by omega) hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega)
        (hfreshN _ (by omega)) (hfreshN _ (Nat.le_refl _))
        hLroot.symm (by omega) hqroot.symm (by omega)
        hrq hrg hrk (keyWf_last_notin pre cv hkey) hvisL huniq honlyL honlyq
        (fun x xn cc z hx hxn hz => by
          have := hlinks x xn cc z hx hxn hz; exact ⟨by omega, by omega⟩)
      intro key' hkey'
      unfold wGet
      rw [htp, hV4, hres key' hkey']
  -- the bitmap in L, with room
  have hroomc : ∀ (n' : KNode) (s : String), n'.leaf = true →
      (∀ c', (n'.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
        wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro n' s hl' hs'
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine hleafc n' _ hl' hr3.2.1 hr3.2.2.1 hr3.2.2.2.1 ?_ ?_ hs'
    · intro y hy
      rw [← hr3.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
    · simp only [wNode, hr3.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c',
      (((n.setAt (n.size - 1) (.del U)).searchEq c.i c').map (·.y)) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro old hlst c'
    rw [← hU]
    have hw' := KNode.setAt_delete_wf n cv old hnwf hlst
    rw [KNode.searchEq_live _ c.i hw' (KNode.setAt_last_times n old _ c.i hlst hnt),
      KNode.setAt_delete_live_lookup n cv c' old hlst, KNode.searchEq_live n c.i hnwf hnt]
  have hadd : ∀ c', (((n.add c.i (.del U)).searchEq c.i c').map (·.y)) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [← hU]
    have hw' := KNode.add_delete_wf n c.i cv hnwf (by rw [hU]; exact hne)
    rw [KNode.searchEq_live _ c.i hw' (KNode.add_times n c.i _ (fun s h => by cases h) hnt),
      KNode.add_delete_live_lookup n c.i cv c', KNode.searchEq_live n c.i hnwf hnt]
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [] last
          pure false) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro hnTD
      by_cases hsz : n.size + 1 < c.p.M
      · simp only [hsz, decide_true, ↓reduceIte]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
        · simp only [hd, Bool.false_eq_true, ↓reduceIte]
          exact hroomc _ _ (by rw [KNode.add_leaf]; exact hnl) hadd
      · simp only [hsz, ↓reduceIte]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit hnTD h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt')
        | true =>
          simp only [hg, hlt', Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
          · simp only [hd, Bool.false_eq_true, ↓reduceIte]
            exact hroomc _ _ (by rw [KNode.setAt_leaf]; exact hnl) (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-! ## The rule: a delete into a leaf whose parent is full and time split -/

/-- A delete, the merges off, of a key whose access path from the segment root
rk ends with g, q, L (`PathFrom`), by a bitmap in the segment leaf L, which
keeps a live klong, the inner parent q full and time split if L splits, below
the grandparent g with room: with room for the bitmap, or L time split (in place
for a leaf the transaction made). The delete changes the reading by itself
alone. -/
theorem writerWP_del_timeSplit2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w q = none ∧ q ≠ w.top.rootKey)
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hnt, hne, hkeep, hsplit, hLval, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hqval, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  apply writerWP_del_path c base hvc pre cv rk w S0 kq k1 q L n qn gn hrk ht hids.1 hids.2.1 hwfG
    hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hlg3 hpg hgv
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hgtk : w.taken.contains g = false :=
    ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hqtk : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_get2 c base hvc pre cv k1 kq d'' rk L q g n qn gn
    w w3 hfuel hkey hrk hvisL huniq hwfG hids hbase hNL hnl hnt hLt hLval hLroot hNq hql hqt hk1L
    hqL hrq hqfirst hNg hgl hgt hkqg hgq hgL hgtk hrg
    (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
      (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
    hqval hqroot
    (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
    hlinks hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hne hsplit hqfull hqsplit hroomg hdeadg) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

/-! ## The bitmap of a delete, the leaf's time split given -/

set_option linter.unusedSimpArgs false in
/-- The bitmap of a delete in the leaf L, merges off: with room for it, or L
time split, in place for a leaf the transaction made, or by `hcascade` for one
that existed before: the state reads as the delete, when the state after it
meets Q, a condition that `hcascade` may need. -/
theorem writerWP_appendDeleteKlong_timeGenQ (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv d' : Nat) (rk L : NodeId) (n : KNode) (w w3 : W) (Q : W → Prop)
    (hfuel : 1 ≤ c.p.fuel) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hLt : w.taken.contains L = false)
    (hr3 : ReadsAs c.p base w w3) (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hcascade : ∀ (compact : Bool) (s : String),
      (!compact && decide ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size >
        c.p.splitAbove)) = false → n.firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  have hnwf := hwfG L n hn
  -- a state whose leaf L changed to n2, n's live klongs but cv's: the delete
  have hleafc : ∀ (n2 : KNode) (w6 : W), n2.leaf = true → w6.top = w.top →
      w6.taken = w.taken → w6.vals = w.vals →
      (∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x) → wNode c.p base w6 L = some n2 →
      (∀ c', (n2.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      ∀ key', keyWf key' = true →
        wGet c.p c.i base w6 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key' := by
    intro n2 w6 hl2 h6top h6taken h6vals hN hNL6 hs2
    have hV : ∀ y, wValue base w y = wValue base w6 y := by
      intro y; simp only [wValue, h6taken, h6vals]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n n2 hfuel h6top hN
      hn hNL6 hnl hl2 (fun c' hc' => by
        rw [hs2 c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL huniq (fun _ _ _ _ y _ _ _ _ _ => hV y)
    intro key' hkey'
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, hs2 cv]
      simp
    · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      exact hother key' hkey' (fun h => hk h.symm)
  -- the last version without cv
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlook0 hwf0 hcascade
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hsplit hlook0 hwf0 hcascade
  have hmwf : klongsWf (⟨n.leaf, last.ks⟩ : KNode).ks = true := hwf0
  have hmt : ∀ s, Klong.time s ∈ (⟨n.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := hlt
  have hmlook : ∀ c', (⟨n.leaf, last.ks⟩ : KNode).live.lookup c' =
      if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [hleq]; exact hlook0 c'
  have hms : ∀ c', ((⟨n.leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [KNode.searchEq_live _ c.i hmwf hmt, hmlook, KNode.searchEq_live n c.i hnwf hnt]
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact hcs s
    by_cases hnew : n.firstTime = some c.i
    · generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
      have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
      have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ (d' + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, h4v, hN4⟩ _
      refine hleafc ⟨n.leaf, last.ks⟩ w4 hnl (h4top.trans hr3'.2.1) (h4t.trans hr3'.2.2.1)
        (h4v.trans hr3'.2.2.2.1) ?_ (by rw [hN4]; simp) hms
      intro x hx; rw [hN4]; simp only [hx, ↓reduceIte]; rw [hr3'.1]
    · exact hcascade compact s hcs hnew
  -- the bitmap in L, with room
  have hroomc : ∀ (n' : KNode) (s : String), n'.leaf = true →
      (∀ c', (n'.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
        wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro n' s hl' hs'
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    intro _
    refine hleafc n' _ hl' hr3.2.1 hr3.2.2.1 hr3.2.2.2.1 ?_ ?_ hs'
    · intro y hy
      rw [← hr3.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
    · simp only [wNode, hr3.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c',
      (((n.setAt (n.size - 1) (.del U)).searchEq c.i c').map (·.y)) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro old hlst c'
    rw [← hU]
    have hw' := KNode.setAt_delete_wf n cv old hnwf hlst
    rw [KNode.searchEq_live _ c.i hw' (KNode.setAt_last_times n old _ c.i hlst hnt),
      KNode.setAt_delete_live_lookup n cv c' old hlst, KNode.searchEq_live n c.i hnwf hnt]
  have hadd : ∀ c', (((n.add c.i (.del U)).searchEq c.i c').map (·.y)) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [← hU]
    have hw' := KNode.add_delete_wf n c.i cv hnwf (by rw [hU]; exact hne)
    rw [KNode.searchEq_live _ c.i hw' (KNode.add_times n c.i _ (fun s h => by cases h) hnt),
      KNode.add_delete_live_lookup n c.i cv c', KNode.searchEq_live n c.i hnwf hnt]
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => Q w4 → ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro hnTD
      by_cases hsz : n.size + 1 < c.p.M
      · simp only [hsz, decide_true, ↓reduceIte]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
        · simp only [hd, Bool.false_eq_true, ↓reduceIte]
          exact hroomc _ _ (by rw [KNode.add_leaf]; exact hnl) hadd
      · simp only [hsz, ↓reduceIte]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit hnTD h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt')
        | true =>
          simp only [hg, hlt', Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
          · simp only [hd, Bool.false_eq_true, ↓reduceIte]
            exact hroomc _ _ (by rw [KNode.setAt_leaf]; exact hnl) (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- `writerWP_appendDeleteKlong_timeGenQ` with no condition on the state after. -/
theorem writerWP_appendDeleteKlong_timeGen (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv d' : Nat) (rk L : NodeId) (n : KNode) (w w3 : W)
    (hfuel : 1 ≤ c.p.fuel) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hLt : w.taken.contains L = false)
    (hr3 : ReadsAs c.p base w w3) (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hcascade : ∀ (compact : Bool) (s : String),
      (!compact && decide ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size >
        c.p.splitAbove)) = false → n.firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') :=
  writerWP_mono (writerWP_appendDeleteKlong_timeGenQ c base hvc pre cv d' rk L n w w3 (fun _ => True)
    hfuel hkey hrk hvisL huniq hwfG hn hnl hnt hLt hr3 hlk3 hne hsplit
    (fun compact s h1 h2 => writerWP_mono (hcascade compact s h1 h2) (fun _ _ h _ => h)))
    (fun _ _ h => h trivial)

/-! ## The writer: a delete's time split of a leaf whose parent is full and space split -/

/-- `TimeSpaceAfter` for a delete: L's last version `last` at the next id. -/
def DelTimeSpaceAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) : Prop :=
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some ((gn.add c.i (.key kq (w.next + 2))).add c.i
        (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2)))
      else if x = w.next then some ⟨n.leaf, last.ks⟩
      else if x = w.next + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).1
      else if x = w.next + 2 + 2 then
        some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.1
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_delTimeSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hLn : L < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L []
      last compact) c w
      (fun _ w' => DelTimeSpaceAfter c w w' L q g n qn gn kq k1 last) := by
  have hpq' : (w.path[d'' + 1]?).map (·.2) = some q := by rw [hpq]; rfl
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d'' + 1]? with
  | none => rw [hp] at hpq'; cases hpq'
  | some e =>
    rw [hp] at hpq'
    simp only [Option.map_some, Option.some.injEq] at hpq'
    simp only [writerWP_pure]
    rw [hpq']
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        (∀ x, w2.nodes.lookup x =
          if x = q then some (qn.toPrev (c.i - 1))
          else if x = g then some ((gn.add c.i (.key kq (w.next + 2))).add c.i
            (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2)))
          else if x = w.next + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).1
          else if x = w.next + 2 + 2 then
            some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.1
          else (w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))]).lookup x) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => DelTimeSpaceAfter c w w' L q g n qn gn kq k1 last) := by
      intro w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n]
        simp only [show L ≠ q from fun h => hqL h.symm, show L ≠ g from fun h => hgL h.symm,
          show L ≠ w.next + 2 by omega, show L ≠ w.next + 2 + 2 by omega, ↓reduceIte,
          List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, h2v, ?_⟩
      · intro x
        show (upsert _ L _).lookup x = _
        rw [lookup_upsert, h2n]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte]
            by_cases hxg : x = g
            · simp [hxg]
            · simp only [hxg, ↓reduceIte, List.lookup_append]
              by_cases hx3 : x = w.next + 2 + 2
              · simp [hx3, show w.next + 2 + 2 ≠ w.next by omega,
                  show w.next + 2 + 2 ≠ w.next + 2 by omega]
              · by_cases hx2 : x = w.next + 2
                · simp [hx2, show w.next + 2 ≠ w.next by omega]
                · simp only [hx2, hx3, ↓reduceIte]
                  by_cases hxy : x = w.next
                  · subst hxy; rw [hny]; simp [List.lookup]
                  · simp only [hxy, ↓reduceIte]
                    cases h : w.nodes.lookup x with
                    | some m => rfl
                    | none =>
                      show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := last.ks })].lookup x) = none
                      rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    have hup : ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))] →
        w1.next = w.next + 2 → w1.path = w.path → w1.taken = w.taken → w1.top = w.top →
        w1.vals = w.vals →
        WriterWP (appendKlongs (d'' + 1) q [(k1, w.next)]) c w1 (fun _ w' =>
          WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w'
            (fun _ w'' => DelTimeSpaceAfter c w w'' L q g n qn gn kq k1 last)) := by
      intro w1 h1n h1x h1p h1t h1top h1v
      refine writerWP_mono (writerWP_appendKlongs_spaceSplit d'' q g qn gn kq k1 w.next c w1
        (by rw [h1n, List.lookup_append, hlq]; rfl) (by rw [h1n, List.lookup_append, hlg]; rfl)
        hgq hgl hqfirst hqfull hqsplit (by rw [h1p]; exact hpg) (by rw [h1p]; exact hpq)
        hroomg (fun y1 sc y2 => hdeadg y1 sc y2)
        (by
          rw [h1n, h1x, List.lookup_append, hny2]
          show ([(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))].lookup (w.next + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)
        (by
          rw [h1n, h1x, List.lookup_append, hny3]
          show ([(w.next, ({ leaf := n.leaf, ks := last.ks } : KNode))].lookup (w.next + 2 + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)) ?_
      intro _ w2 ⟨h2t, h2top, h2v, h2n⟩
      refine hfinal w2
        (by rw [h2t, h1t]) (by rw [h2top, h1top]) (by rw [h2v, h1v]) ?_
      intro x; rw [h2n x, h1x, h1n]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
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

/-! ## The reading after a delete's time split and its parent's space split -/

/-- `getFromR_timeSpace` for a delete: the leaf's last version without cv at
Y. -/
theorem getFromR_delTimeSpace (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g Y Fq Sq : NodeId)
    (n qn gn ln : KNode) (k1 kq : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live) (hkqr : kq ≤ r.1)
    (hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c')
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ c, ln.live.lookup c = if c == cv then none else n.live.lookup c)
    (hN2g : N2 g = some ((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq)))
    (hN2F : N2 Fq = some (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).1)
    (hN2S : N2 Sq = some (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.1)
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ Y → x ≠ Fq → x ≠ Sq → N2 x = N x)
    (hV2L : V L = none) (hV2Y : V Y = none)
    (hqL : q ≠ L) (hYL : Y ≠ L) (hYq : Y ≠ q) (hgq : g ≠ q) (hgL : g ≠ L) (hgY : g ≠ Y)
    (hFL : Fq ≠ L) (hFq : Fq ≠ q) (hFg : Fq ≠ g) (hFY : Fq ≠ Y)
    (hSL : Sq ≠ L) (hSq : Sq ≠ q) (hSg : Sq ≠ g) (hSY : Sq ≠ Y) (hFS : Fq ≠ Sq)
    (hNY : N Y = none) (hNF : N Fq = none) (hNS : N Sq = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrootq : root ≠ q) (hrootF : root ≠ Fq)
    (hrootS : root ≠ Sq)
    (hrq : ReachS N i root q) (hrg : ReachS N i root g)
    (hnoq : ¬ ReachS N i q g) (hnoL : ¬ ReachS N i L g)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (honlyq : ∀ x xn c, ReachS N i root x → N x = some xn → (c, q) ∈ xn.liveAt i →
      x = g ∧ c = kq)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Y ∧ z ≠ Fq ∧ z ≠ Sq) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let q1 : KNode := qn.add i (.key k1 Y)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q1 else if x = g then some gn
    else if x = Fq then none else if x = Sq then none else N2 x
  have hN1q : N1 q = some q1 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1Y : N1 Y = some ln := by simp [N1, hYq, hgY.symm, hFY.symm, hSY.symm, hN2Y]
  have hN1F : N1 Fq = none := by simp [N1, hFq, hFg]
  have hN1S : N1 Sq = none := by simp [N1, hSq, hSg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ Y → N1 x = N x := by
    intro x h1 h2 h3
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxF : x = Fq
      · subst hxF; simp [N1, h2, hxg, hNF]
      · by_cases hxS : x = Sq
        · subst hxS; simp [N1, h2, hxg, hxF, hNS]
        · simp only [N1, h2, hxg, hxF, hxS, ↓reduceIte]
          exact hN2 x h1 h2 hxg h3 hxF hxS
  -- step A: N1 reads as the put
  have hA := getFromR_timeSplit_del N N1 V i fuel hfuel root L q Y n qn ln k1 pre cv rk
    hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hlnl hlnwf hlnt hlnlook hN1Y hN1q hN1 hV2L hV2Y
    hqL hYL hYq hNY hrootL hrootY hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => (hfr x xn c z hx hn hz).1)
  -- the nodes N1 reaches
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hqadd : ∀ c z, (c, z) ∈ q1.liveAt i → ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = Y := by
    intro c z hz
    have ht2 := KNode.add_times qn i (.key k1 Y) (fun s h => by cases h) hqt
    rw [KNode.liveAt_of_times _ i ht2] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [KNode.add_key_live_lookup_of_wf qn i k1 c Y hqwf] at this
    by_cases hc : k1 = c
    · subst hc; simp at this; exact Or.inr this.symm
    · have hc' : (k1 == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      left; rw [KNode.liveAt_of_times qn i hqt]
      exact ⟨lookup_some_mem this, fun h => hc h.symm⟩
  have hlnmem : ∀ c z, (c, z) ∈ ln.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [KNode.liveAt_of_times ln i hlnt] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup ln) hz
    rw [hlnlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem this
  have hreachNe : ∀ x, ReachS N i root x → x ≠ Y ∧ x ≠ Fq ∧ x ≠ Sq := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootY, hrootF, hrootS⟩
    | step x' xn c _ hx' hn hz =>
      exact hfr x' xn c _ hx' hn hz
  have hreach1 : ∀ x, ReachS N1 i root x → (ReachS N i root x ∧ x ≠ L) ∨ x = Y := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hqadd c z hz with ⟨hz', hck⟩ | hzY
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr hzY
        · rw [hN1 x' hx'L hxq (hreachNe x' hx').1] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · subst x'
        rw [hN1Y] at hn; cases hn
        have hz' := hlnmem c z hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
  -- step B: q split at g into Fq and Sq
  have hq1wf : klongsWf q1.ks = true := KNode.add_key_wf qn i k1 Y hqwf
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY
    · by_cases hxq : x = q
      · subst hxq; rw [hN1q] at hn; cases hn; exact hq1wf
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn; exact hwfG x xn hn
    · subst hxY; rw [hN1Y] at hn; cases hn; exact hlnwf
  have hnotq1 : ∀ x xn c z, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn c z hx hxg hn hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c x hz with ⟨hz', _⟩ | hzY
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hYq hzY.symm
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · subst hxY
      rw [hN1Y] at hn; cases hn
      exact hgL (honlyq L n c hrL hNL (hlnmem c z hz)).1.symm
  have hnotFS1 : ∀ x xn c z, ReachS N1 i root x → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Fq ∧ z ≠ Sq := by
    intro x xn c z hx hn hz
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c z hz with ⟨hz', _⟩ | hzY
        · exact (hfr x qn c z hx' hNq hz').2
        · rw [hzY]; exact ⟨hFY.symm, hSY.symm⟩
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
        exact (hfr x xn c z hx' hn hz).2
    · subst hxY
      rw [hN1Y] at hn; cases hn
      exact (hfr L n c z hrL hNL (hlnmem c z hz)).2
  -- the halves of q with the klong put
  obtain ⟨hscq, hFl, hSl, hFwf, hSwf, hFt, hSt, hsF, hsS⟩ :=
    halves_inner_searchLte qn i k1 Y hql hqwf hqt r hr hsc
  have hg2 : (((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq))).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hgl
  have hgsearch : ∀ c : Nat, ((((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq))).searchLte i c).map (·.y) =
      (gn.searchLte i c).map (fun fd => if fd.y = q then
        (if c < (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 then Fq else Sq) else fd.y) := by
    intro c
    rw [hscq]
    have hA := KNode.splitParent_searchLte gn i kq r.1 q Fq Sq hgwf hgt hkq hkqr hgap c
    rw [hA]
    cases hs : gn.searchLte i c with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Option.some.injEq]
      have hmemfd := KNode.searchLte_mem gn i c fd hs
      have hyq : fd.y = q ↔ fd.c = kq := by
        constructor
        · intro hy
          rw [hy] at hmemfd
          exact (honlyq g gn fd.c hrg hNg hmemfd).2
        · intro hc
          rw [KNode.liveAt_of_times gn i hgt, hc] at hmemfd
          exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup gn) hmemfd).symm.trans
            (lookup_some_of_mem (KNode.live_keys_nodup gn) hkq))
      by_cases hc : fd.c = kq
      · simp only [hc, ↓reduceIte, hyq.mpr hc, Int.ofNat_lt]
      · have hy : ¬ fd.y = q := fun h => hc (hyq.mp h)
        simp only [hc, ↓reduceIte, hy]
  have hrq1 : ReachS N1 i root q := by
    have htr : ∀ x, ReachS N i root x → ¬ ReachS N i q x → ¬ ReachS N i L x →
        ReachS N1 i root x := by
      intro x hx
      induction hx with
      | root => intro _ _; exact ReachS.root
      | step x' xn c z hx' hn hz ih =>
        intro hq hL
        have hq' : ¬ ReachS N i q x' := fun h => hq (ReachS.step x' xn c z h hn hz)
        have hL' : ¬ ReachS N i L x' := fun h => hL (ReachS.step x' xn c z h hn hz)
        have hx'q : x' ≠ q := by intro he; subst he; exact hq' ReachS.root
        have hx'L : x' ≠ L := by intro he; subst he; exact hL' ReachS.root
        have hn1 : N1 x' = some xn := by rw [hN1 x' hx'L hx'q (hreachNe x' hx').1]; exact hn
        exact ReachS.step x' xn c z (ih hq' hL') hn1 hz
    have hrg1 : ReachS N1 i root g := htr g hrg hnoq hnoL
    exact ReachS.step g gn kq q hrg1 hN1g (by rw [KNode.liveAt_of_times gn i hgt]; exact hkq)
  have hsame1 : ∀ x, x ≠ q → x ≠ g → x ≠ Fq → x ≠ Sq → N2 x = N1 x := by
    intro x h1 h2 h3 h4
    simp only [N1, h1, h2, h3, h4, ↓reduceIte]
  have hget := fun c => getEqR_split_inner N1 N2 i root q g Fq Sq gn _ q1 _ _ _ hN1g hgl hN2g hg2
    hgsearch hN1q (by simp only [q1, KNode.add_leaf]; exact hql) hrq1 hN2F hFl hN2S hSl
    (fun c hc => by rw [hscq] at hc; exact hsF c hc) (fun c hc => by rw [hscq] at hc; exact hsS c hc)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    hnotFS1 hgq.symm c
  have hsim := getFromR_split N1 N2 V i fuel root q g Fq Sq hwf1
    (fun c x hx hxq hxF hxS => (hget c fuel).1 x hx hxq hxF hxS)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4) (by rw [hN2g, hN1g]; rfl)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    (fun xn c z hxn _ hxl => by rw [hN1g] at hxn; cases hxn; rw [hgl] at hxl; cases hxl)
    (fun x xn c z hx hn hz => ⟨fun _ => (hnotFS1 x xn c z hx hn hz).1, (hnotFS1 x xn c z hx hn hz).2⟩)
  intro key' hkey'
  rw [hsim key' root ReachS.root hrootq hrootF hrootS]
  exact hA key' hkey'

/-! ## The rule: a delete into a leaf whose parent is full and space split -/

/-- A delete, the merges off, of a key whose access path from the segment root
rk ends with g, q, L (`PathFrom`), by a bitmap in the segment leaf L, which
keeps a live klong, the inner parent q full by its size with more than h klongs
in its last version, at least two of them live, space split if L splits, below
the grandparent g with room for two klongs: with room for the bitmap, or L time
split (in place for a leaf the transaction made). The delete changes the
reading by itself alone. -/
theorem writerWP_del_timeSpace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ c.p.M < qn.size + 1 + 1 ∧
      qn.firstTime ≠ some c.i ∧ c.p.splitAbove < (qn.lastVersion c.i).size ∧
      2 ≤ qn.live.length ∧ q ≠ w.top.rootKey)
    (hrange : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hacyc : ¬ ReachS (wNode c.p base w) c.i q (pathEnd rk S0) ∧
      ¬ ReachS (wNode c.p base w) c.i L (pathEnd rk S0))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨hnt, hne, hkeep, hsplit, hLval, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hq2, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  apply writerWP_del_path c base hvc pre cv rk w S0 kq k1 q L n qn gn hrk ht hidn hidv hwfG
    hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hlg3 hpg hgv hacyc
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hgtk : w.taken.contains g = false :=
    ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  -- the divider of q's halves
  obtain ⟨r, hr⟩ : ∃ r, (qn.live.drop (qn.live.length / 2)).head? = some r := by
    cases h' : qn.live.drop (qn.live.length / 2) with
    | nil => have := congrArg List.length h'; simp at this; omega
    | cons a _ => exact ⟨a, rfl⟩
  have hsc : 0 < r.1 := by
    obtain ⟨a, ha⟩ : ∃ a, a ∈ qn.live.take (qn.live.length / 2) := by
      cases h' : qn.live.take (qn.live.length / 2) with
      | nil =>
        have := congrArg List.length h'
        rw [List.length_take] at this; simp only [List.length_nil] at this; omega
      | cons a _ => exact ⟨a, by simp⟩
    have := halves_left_lt_divider qn.live _ qn.live_order r hr a ha
    omega
  have hrmem : r ∈ qn.live := List.mem_of_mem_drop (List.mem_of_head? hr)
  have hkqr : kq ≤ r.1 := (hrange r.1 r.2 hrmem hsc).1
  have hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c' := by
    intro c' z hcz
    by_cases hle : c' ≤ kq
    · exact Or.inl hle
    · exact Or.inr ((hrange r.1 r.2 hrmem hsc).2 c' z hcz (by omega))
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
  have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
    intro z hz
    cases h' : w.nodes.lookup z with
    | none => rfl
    | some _ => have := hidn z (by rw [h']; rfl); omega
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnodenone z hz,
      (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz,
      (hbase z hz).2]
  have hLlt : L < w.next := hsrc3 L (by rw [hlk3]; rfl)
  have hqlt : q < w.next := hsrc3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrc3 g (by rw [hlg3]; rfl)
  have hnwf := hwfG L n hNL
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_timeGen c base hvc pre cv (d'' + 1) rk L n w w3
    hfuel hkey hrk hvisL huniq hwfG hNL hnl hnt hLt hr3 hlk3 hne hsplit ?_) ?_
  · intro compact s hcs hnew
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by
      rw [← hw3']; exact hsrc3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hny : w3'.nodes.lookup w3'.next = none := by
      cases h' : w3'.nodes.lookup w3'.next with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny2 : w3'.nodes.lookup (w3'.next + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny3 : w3'.nodes.lookup (w3'.next + 2 + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2 + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_handleFullWith_delTimeSpace d'' L q g n qn gn kq k1 _ compact c w3'
      hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hnew hqfirst hcs hqfull hqsplit hpg' hpq' hpk' hroomg
      hdeadg hny hny2 hny3 (by rw [hnext3']; exact hLlt)) ?_
    intro _ w4 ⟨h4t, h4top, h4v, h4nodes⟩
    rw [hnext3'] at h4nodes
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hvl : w4.vals = w.vals := h4v.trans hr3'.2.2.2.1
    have htp : w4.top = w.top := h4top.trans hr3'.2.1
    have hV4 : wValue base w4 = wValue base w := by
      funext a; simp only [wValue, htk, hvl]
    have hres := getFromR_delTimeSpace (wNode c.p base w) (wNode c.p base w4) (wValue base w)
      c.i c.p.fuel hfuel w.top.rootKey L q g w.next (w.next + 2) (w.next + 2 + 2) n qn gn
      ⟨n.leaf, (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩
      k1 kq pre cv rk r hr hsc hwfG hNL hnl hnt hNq hql hqt hk1L hNg hgl hgt hkqg hkqr hgap
      (by
        simp only [wNode, htk, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4nodes,
          show w.next ≠ L by omega, show w.next ≠ q by omega, show w.next ≠ g by omega])
      hnl hwf0 hlt (by intro c'; rw [hleq]; exact hlook0 c')
      (by simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq])
      (by
        simp only [wNode, htk, hntake (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega,
          show w.next + 2 ≠ g by omega, show w.next + 2 ≠ w.next by omega])
      (by
        simp only [wNode, htk, hntake (w.next + 2 + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
          show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next by omega,
          show w.next + 2 + 2 ≠ w.next + 2 by omega])
      (by
        intro m hm
        simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes,
          Option.some.injEq] at hm
        rw [← hm]; exact KNode.toPrev_wf n _ hnwf)
      (by
        intro x hxL hxq hxg hxY hxF hxS
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxY, hxF, hxS, ↓reduceIte])
      hLval (hfreshV _ (Nat.le_refl _))
      hqL (by omega) (by omega) hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
      hLroot.symm (by omega) hqroot.symm (by omega) (by omega)
      hrq hrg hacyc.1 hacyc.2 hrk (keyWf_last_notin pre cv hkey) hvisL huniq
      (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
        (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
      (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
        (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
      (fun x xn cc z hx hxn hz => by
        have := hlinks x xn cc z hx hxn hz; exact ⟨by omega, by omega, by omega⟩)
    intro key' hkey'
    unfold wGet
    rw [htp, hV4, hres key' hkey']
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

/-! ## The writer: a delete's space split of a leaf whose parent is full and time split -/

/-- `SpaceSplitTimeAfter` for a delete: L's halves of `last`. -/
def DelSpaceTimeAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) : Prop :=
  ∃ lq : KNode, lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = [(k1, w.next),
      ((halves n.leaf c.i last []).2.2, w.next + 2)].foldl
      (pairLookupStep q') (qn.live.lookup q')) ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2 + 2)))
      else if x = w.next then some (halves n.leaf c.i last []).1
      else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 + 2 then some ⟨qn.leaf, lq.ks⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_delSpaceTime (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i last []).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none)
    (hn3 : w.nodes.lookup (w.next + 2 + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L []
      last false) c w
      (fun _ w' => DelSpaceTimeAfter c w w' L q g n qn gn kq k1 last) := by
  have hpq' : (w.path[d'' + 1]?).map (·.2) = some q := by rw [hpq]; rfl
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d'' + 1]? with
  | none => rw [hp] at hpq'; cases hpq'
  | some e =>
    rw [hp] at hpq'
    simp only [Option.map_some, Option.some.injEq] at hpq'
    simp only [writerWP_pure]
    rw [hpq']
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    have hq1 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
    have hq2 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
    have hq3 : q ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlq; cases hlq
    have hg1 : g ≠ w.next := fun h => by rw [h, hn1] at hlg; cases hlg
    have hg2 : g ≠ w.next + 2 := fun h => by rw [h, hn2] at hlg; cases hlg
    have hg3 : g ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlg; cases hlg
    have hL1 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
    have hL2 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
    have hL3 : L ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlk; cases hlk
    have hb31 : (w.next + 2 + 2 == w.next) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb32 : (w.next + 2 + 2 == w.next + 2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_timeSplitIns d'' q g qn gn kq
        [(k1, w.next), ((halves n.leaf c.i last []).2.2, w.next + 2)] c _
        (by simp [lookup_upsert, hq1, hq2, List.lookup_append, hlq])
        (by simp [lookup_upsert, hg1, hg2, List.lookup_append, hlg])
        hgq hgl hqfirst (by simpa using hqfull) (by simpa using hqsplit) hpg hpq hroomg hdeadg
        (by
          simp only [lookup_upsert, show w.next + 2 + 2 ≠ w.next + 2 by omega,
            show w.next + 2 + 2 ≠ w.next by omega, ↓reduceIte, List.lookup_append, hn3]
          simp [List.lookup, hb31, hb32])) ?_
      intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, h2n⟩
      rw [writerWP_getNode_known L n c _ (by
        rw [h2n]
        simp [hqL.symm, hgL.symm, hL1, hL2, hL3, lookup_upsert, List.lookup_append, hlk])]
      try simp only [putNode, writerWP_modify]
      refine ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, ?_⟩
      intro x
      show (upsert _ L _).lookup x = _
      rw [lookup_upsert, h2n]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hxg : x = g
          · simp [hxg]
          · simp only [hxg, ↓reduceIte]
            by_cases hx3 : x = w.next + 2 + 2
            · simp [hx3, show w.next + 2 + 2 ≠ w.next by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega]
            · simp only [hx3, ↓reduceIte, lookup_upsert, List.lookup_append]
              by_cases hx2 : x = w.next + 2
              · have hx1 : x ≠ w.next := by omega
                simp [hx2]
              · simp only [hx2, ↓reduceIte]
                by_cases hx1 : x = w.next
                · simp [hx1]
                · simp only [hx1, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    have hb1 : (x == w.next) = false := by simpa using hx1
                    have hb2 : (x == w.next + 2) = false := by simpa using hx2
                    simp [List.lookup, hb1, hb2])

/-! ## The writer: a delete's space split of a leaf whose parent is full and space split -/

/-- `SpaceSpaceAfter` for a delete: L's halves of `last`. -/
def DelSpaceSpaceAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some ((gn.add c.i (.key kq (w.next + 2 + 2))).add c.i
        (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next),
          ((halves n.leaf c.i last []).2.2, w.next + 2)]).2.2
          (w.next + 2 + 2 + 2)))
      else if x = w.next then some (halves n.leaf c.i last []).1
      else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next),
          ((halves n.leaf c.i last []).2.2, w.next + 2)]).1
      else if x = w.next + 2 + 2 + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i)
          [(k1, w.next), ((halves n.leaf c.i last []).2.2, w.next + 2)]).2.1
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_delSpaceSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 : Nat) (last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hqfull : c.p.M < qn.size + 2 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none)
    (hn3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hn4 : w.nodes.lookup (w.next + 2 + 2 + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L []
      last false) c w
      (fun _ w' => DelSpaceSpaceAfter c w w' L q g n qn gn kq k1 last) := by
  have hpq' : (w.path[d'' + 1]?).map (·.2) = some q := by rw [hpq]; rfl
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d'' + 1]? with
  | none => rw [hp] at hpq'; cases hpq'
  | some e =>
    rw [hp] at hpq'
    simp only [Option.map_some, Option.some.injEq] at hpq'
    simp only [writerWP_pure]
    rw [hpq']
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    have hq1 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
    have hq2 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
    have hq3 : q ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlq; cases hlq
    have hg1 : g ≠ w.next := fun h => by rw [h, hn1] at hlg; cases hlg
    have hg2 : g ≠ w.next + 2 := fun h => by rw [h, hn2] at hlg; cases hlg
    have hg3 : g ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlg; cases hlg
    have hL1 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
    have hL2 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
    have hL3 : L ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlk; cases hlk
    have hq4 : q ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlq; cases hlq
    have hg4 : g ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlg; cases hlg
    have hL4 : L ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlk; cases hlk
    have hb41 : (w.next + 2 + 2 + 2 == w.next) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb42 : (w.next + 2 + 2 + 2 == w.next + 2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb31 : (w.next + 2 + 2 == w.next) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb32 : (w.next + 2 + 2 == w.next + 2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_spaceSplitIns d'' q g qn gn kq
        [(k1, w.next), ((halves n.leaf c.i last []).2.2, w.next + 2)] c _
        (by simp [lookup_upsert, hq1, hq2, List.lookup_append, hlq])
        (by simp [lookup_upsert, hg1, hg2, List.lookup_append, hlg])
        hgq hgl hqfirst (by simpa using hqfull) hqsplit hpg hpq hroomg hdeadg
        (by
          simp only [lookup_upsert, show w.next + 2 + 2 ≠ w.next + 2 by omega,
            show w.next + 2 + 2 ≠ w.next by omega, ↓reduceIte, List.lookup_append, hn3]
          simp [List.lookup, hb31, hb32])
        (by
          simp only [lookup_upsert, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
            show w.next + 2 + 2 + 2 ≠ w.next by omega, ↓reduceIte, List.lookup_append, hn4]
          simp [List.lookup, hb41, hb42])) ?_
      intro _ w2 ⟨h2t, h2top, h2v, h2n⟩
      rw [writerWP_getNode_known L n c _ (by
        rw [h2n]
        simp [hqL.symm, hgL.symm, hL1, hL2, hL3, hL4, lookup_upsert, List.lookup_append, hlk])]
      try simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, h2v, ?_⟩
      intro x
      show (upsert _ L _).lookup x = _
      rw [lookup_upsert, h2n]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hxg : x = g
          · simp [hxg]
          · simp only [hxg, ↓reduceIte]
            by_cases hx4 : x = w.next + 2 + 2 + 2
            · simp [hx4, show w.next + 2 + 2 + 2 ≠ w.next by omega,
                show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
                show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega,
                show w.next + 2 + 2 ≠ w.next by omega]
            · simp only [hx4, ↓reduceIte]
              by_cases hx3 : x = w.next + 2 + 2
              · simp [hx3, show w.next + 2 + 2 ≠ w.next by omega,
                  show w.next + 2 + 2 ≠ w.next + 2 by omega]
              · simp only [hx3, ↓reduceIte, lookup_upsert, List.lookup_append]
                by_cases hx2 : x = w.next + 2
                · have hx1 : x ≠ w.next := by omega
                  simp [hx2]
                · simp only [hx2, ↓reduceIte]
                  by_cases hx1 : x = w.next
                  · simp [hx1]
                  · simp only [hx1, ↓reduceIte]
                    cases h : w.nodes.lookup x with
                    | some m => rfl
                    | none =>
                      have hb1 : (x == w.next) = false := by simpa using hx1
                      have hb2 : (x == w.next + 2) = false := by simpa using hx2
                      simp [List.lookup, hb1, hb2])

/-- The live klongs of the halves of a leaf's last version `⟨true, newKlongs t
pairs⟩` with nothing put are pairs'. -/
theorem halves_nil_live_mem (t : Time) (pairs : List (Nat × NodeId)) (hpne : pairs ≠ [])
    (c : Nat) (z : NodeId)
    (h : (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).1.live ∨
      (c, z) ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).2.1.live) : (c, z) ∈ pairs := by
  obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
    cases hd : (pairs.drop (pairs.length / 2)) with
    | nil =>
      have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
      have : pairs.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hpne
    | cons a _ => exact ⟨a, rfl⟩
  rw [halves_leaf_shape t pairs [] r hr] at h
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil] at h
  rcases h with h | h
  · exact List.mem_of_mem_take (newKlongs_live_mem true t _ c z h)
  · exact List.mem_of_mem_drop (newKlongs_live_mem true t _ c z h)

/-- The halves of a last version with nothing put have klongs of no later
time. -/
theorem halves_nil_times (t : Time) (pairs : List (Nat × NodeId)) :
    (∀ s, Klong.time s ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).1.ks → s ≤ t) ∧
    (∀ s, Klong.time s ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).2.1.ks → s ≤ t) := by
  obtain ⟨first, hfirst⟩ := halves_first_shape true t pairs []
  obtain ⟨extra, hsecond⟩ := halves_second_shape true t pairs []
  rw [hfirst, hsecond]
  exact ⟨newKlongs_times t _, newKlongs_times t _⟩

/-! ## The reading after a delete's space split and its parent's time split -/

/-- `getFromR_spaceSplitTime` for a delete: the halves of the leaf's last version
without cv, `⟨true, newKlongs i pairs⟩`. -/
theorem getFromR_delSpaceTime (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g F S Yq : NodeId)
    (n qn gn lqn : KNode) (k1 kq : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (pairs : List (Nat × NodeId)) (hps : CvSorted pairs) (hpne : pairs ≠ [])
    (hpl : ∀ c, pairs.lookup c = if c == cv then none else n.live.lookup c)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live)
    (hN2F : N2 F = some (halves true i ⟨true, newKlongs i pairs⟩ []).1)
    (hN2S : N2 S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1)
    (hN2Yq : N2 Yq = some lqn) (hlql : lqn.leaf = qn.leaf) (hlqwf : klongsWf lqn.ks = true)
    (hlqt : ∀ s, Klong.time s ∈ lqn.ks → s ≤ i)
    (hlqlook : ∀ c, lqn.live.lookup c = [(k1, F),
      ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)].foldl (pairLookupStep c)
      (qn.live.lookup c))
    (hN2g : N2 g = some (gn.add i (.key kq Yq)))
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ Yq → N2 x = N x)
    (hV2q : V q = none) (hV2Yq : V Yq = none)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hgF : g ≠ F) (hgS : g ≠ S)
    (hFL : F ≠ L) (hSL : S ≠ L) (hFq : F ≠ q) (hSq : S ≠ q) (hFS : F ≠ S)
    (hYqq : Yq ≠ q) (hYqg : Yq ≠ g) (hYqL : Yq ≠ L) (hYqF : Yq ≠ F) (hYqS : Yq ≠ S)
    (hNYq : N Yq = none) (hNF : N F = none) (hNS : N S = none)
    (hrootL : root ≠ L) (hrootF : root ≠ F) (hrootS : root ≠ S) (hrootq : root ≠ q)
    (hrootYq : root ≠ Yq)
    (hrq : ReachS N i root q) (hrg : ReachS N i root g)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (honlyq : ∀ x xn c, ReachS N i root x → N x = some xn → (c, q) ∈ xn.liveAt i →
      x = g ∧ c = kq)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ F ∧ z ≠ S ∧ z ≠ Yq) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let sc := (halves true i ⟨true, newKlongs i pairs⟩ []).2.2
  let q2 : KNode := (qn.add i (.key k1 F)).add i (.key sc S)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q2 else if x = g then some gn
    else if x = Yq then none else N2 x
  have hN1q : N1 q = some q2 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1F : N1 F = some (halves true i ⟨true, newKlongs i pairs⟩ []).1 := by
    simp [N1, hFq, hgF.symm, hYqF.symm, hN2F]
  have hN1S : N1 S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1 := by
    simp [N1, hSq, hgS.symm, hYqS.symm, hN2S]
  have hN1Yq : N1 Yq = none := by simp [N1, hYqq, hYqg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N1 x = N x := by
    intro x h1 h2 h3 h4
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxY : x = Yq
      · subst hxY; simp [N1, h2, hxg, hNYq]
      · simp only [N1, h2, hxg, hxY, ↓reduceIte]
        exact hN2 x h1 h2 hxg h3 h4 hxY
  -- step A: N1 reads as the put
  have hA := getFromR_spaceSplit_del N N1 V i fuel hfuel root L q F S n qn k1 pre cv rk pairs hps
    hpne hpl hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hrange hN1q hN1F hN1S hN1 hqL hFL hNF
    hrootL hrootF hrootS hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1⟩)
  -- the nodes N1 reaches: N's but L, and F and S
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hq2wf : klongsWf q2.ks = true :=
    KNode.add_key_wf _ i sc S (KNode.add_key_wf qn i k1 F hqwf)
  have hq2t : ∀ s, Klong.time s ∈ q2.ks → s ≤ i :=
    KNode.add_times _ i (.key sc S) (fun s h => by cases h)
      (KNode.add_times qn i (.key k1 F) (fun s h => by cases h) hqt)
  have hq2look : ∀ c, q2.live.lookup c =
      if sc == c then some S else if k1 == c then some F else qn.live.lookup c := by
    intro c
    rw [KNode.add_key_live_lookup_of_wf _ i sc c S (KNode.add_key_wf qn i k1 F hqwf),
      KNode.add_key_live_lookup_of_wf qn i k1 c F hqwf]
  have hq2mem : ∀ c z, (c, z) ∈ q2.liveAt i →
      ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = F ∨ z = S := by
    intro c z hz
    rw [KNode.liveAt_of_times _ i hq2t] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [hq2look] at this
    by_cases h1 : sc = c
    · subst h1; simp at this; exact Or.inr (Or.inr this.symm)
    · have h1' : (sc == c) = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte] at this
      by_cases h2 : k1 = c
      · subst h2; simp at this; exact Or.inr (Or.inl this.symm)
      · have h2' : (k1 == c) = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte] at this
        left; rw [KNode.liveAt_of_times qn i hqt]
        exact ⟨lookup_some_mem this, fun h => h2 h.symm⟩
  have hhalf : ∀ x xn c z, (x = F ∨ x = S) → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      (c, z) ∈ n.liveAt i := by
    intro x xn c z hx hn hz
    have hpn : (pairs.map Prod.fst).Nodup :=
      List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
    have hmemp : (c, z) ∈ pairs := by
      rcases hx with hx | hx
      · subst hx; rw [hN1F] at hn; cases hn
        rw [KNode.liveAt_of_times _ i (halves_nil_times i pairs).1] at hz
        exact halves_nil_live_mem i pairs hpne c z (Or.inl hz)
      · subst hx; rw [hN1S] at hn; cases hn
        rw [KNode.liveAt_of_times _ i (halves_nil_times i pairs).2] at hz
        exact halves_nil_live_mem i pairs hpne c z (Or.inr hz)
    have hl := lookup_some_of_mem hpn hmemp
    rw [hpl] at hl
    by_cases hc : c = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem hl
  have hreachNe : ∀ x, ReachS N i root x → x ≠ F ∧ x ≠ S ∧ x ≠ Yq := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootF, hrootS, hrootYq⟩
    | step x' xn c _ hx' hn hz => exact hfr x' xn c _ hx' hn hz
  have hreach1 : ∀ x, ReachS N1 i root x →
      (ReachS N i root x ∧ x ≠ L) ∨ x = F ∨ x = S := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hq2mem c z hz with ⟨hz', hck⟩ | hzF | hzS
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzF)
          · exact Or.inr (Or.inr hzS)
        · obtain ⟨hxF, hxS, _⟩ := hreachNe x' hx'
          rw [hN1 x' hx'L hxq hxF hxS] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · have hz' := hhalf x' xn c z (Or.inl hx') hn hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
      · have hz' := hhalf x' xn c z (Or.inr hx') hn hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
  -- step B: q renamed Yq at g
  have hwfh := halves_newKlongs_wf true i pairs []
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn _ hn
    by_cases hxq : x = q
    · subst hxq; rw [hN1q] at hn; cases hn; exact hq2wf
    · by_cases hxg : x = g
      · subst hxg; rw [hN1g] at hn; cases hn; exact hgwf
      · by_cases hxYq : x = Yq
        · subst hxYq; rw [hN1Yq] at hn; cases hn
        · by_cases hxF : x = F
          · subst hxF; rw [hN1F] at hn; cases hn; exact hwfh.1
          · by_cases hxS : x = S
            · subst hxS; rw [hN1S] at hn; cases hn; exact hwfh.2
            · have hn2 : N2 x = some xn := by
                simp only [N1, hxq, hxg, hxYq, ↓reduceIte] at hn; exact hn
              by_cases hxL : x = L
              · subst hxL; exact hN2L xn hn2
              · rw [hN2 x hxL hxq hxg hxF hxS hxYq] at hn2; exact hwfG x xn hn2
  have hnotq1 : ∀ x xn, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn hx hxg hn c z hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c x hz with ⟨hz', _⟩ | hzF | hzS
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hFq hzF.symm
        · exact hSq hzS.symm
      · obtain ⟨hxF, hxS, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · exact hgL (honlyq L n c hrL hNL (hhalf x xn c z (Or.inl hxF) hn hz)).1.symm
    · exact hgL (honlyq L n c hrL hNL (hhalf x xn c z (Or.inr hxS) hn hz)).1.symm
  have hnotYq1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ Yq := by
    intro x xn hx hn c z hz hzY
    subst hzY
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c z hz with ⟨hz', _⟩ | hzF | hzS
        · exact (hfr x qn c z hx' hNq hz').2.2 rfl
        · exact hYqF hzF
        · exact hYqS hzS
      · by_cases hxg : x = g
        · subst hxg
          rw [hN1g] at hn; cases hn
          exact (hfr x gn c z hx' hNg hz).2.2 rfl
        · obtain ⟨hxF, hxS, _⟩ := hreachNe x hx'
          rw [hN1 x hxL hxq hxF hxS] at hn
          exact (hfr x xn c z hx' hn hz).2.2 rfl
    · exact (hfr L n c z hrL hNL (hhalf x xn c z (Or.inl hxF) hn hz)).2.2 rfl
    · exact (hfr L n c z hrL hNL (hhalf x xn c z (Or.inr hxS) hn hz)).2.2 rfl
  have hS := renSim_timeSplitGen N1 N2 i root q g Yq gn q2 lqn kq
    hgq hYqq hYqg hN1q hN1g hgl hgwf hgt hkq
    (fun c z hz hzq => by
      subst hzq
      exact (honlyq g gn c hrg hNg hz).2)
    hN2Yq (by simp only [q2, KNode.add_leaf]; exact hlql) hq2wf hlqwf hq2t hlqt
    (fun c => by rw [hlqlook c, hq2look c]; simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]; rfl)
    hN2g
    (fun x h1 h2 h3 => by simp only [N1, h1, h2, h3, ↓reduceIte])
    hwf1 hnotq1 hnotYq1
  have hren : ∀ key', getFromR N1 V i fuel key' root = getFromR N2 V i fuel key' root := by
    intro key'
    have := getFromR_ren N1 N2 V V i fuel _ q Yq hS (fun a => by
      by_cases ha : a = q
      · subst ha; simp [hV2q, hV2Yq]
      · simp [ha]) key' root ⟨hrootYq, ReachS.root⟩
    rw [this]
    simp [hrootq]
  intro key' hkey'
  rw [← hren key']
  exact hA key' hkey'

/-! ## The bitmap of a delete, the leaf's space split given -/

set_option linter.unusedSimpArgs false in
/-- The bitmap of a delete in the full leaf L with no bitmap of the transaction
last, full by its size, whose last version without the key has more than h
klongs: the writer space splits L, here by `hcascade`. -/
theorem writerWP_appendDeleteKlong_spaceGen (c : Ctx) (L : NodeId) (n : KNode) (cv d' : Nat)
    (w3 : W) (post : Bool → W → Prop)
    (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hnotTD : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i))
    (hfull : c.p.M ≤ n.size + 1)
    (hcascade : ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more)
      (d' + 1) L [] (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c
      ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => post false w4)) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 post := by
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hcascade
  generalize hlast : n.lastVersionGivenDel c.i U = last at hcascade
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have hsz : ¬ n.size + 1 < c.p.M := by omega
    have hspace : ∀ (s : String), WriterWP (do
          note s
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false)
        c w3 post := by
      intro s
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (hcascade s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsz]
      exact hspace _
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte, hsz]
          exact hspace _
        | true =>
          exact absurd ⟨⟨old, hg⟩, by simpa using hlt'⟩ hnotTD
      | _ =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsz]
        exact hspace _

/-! ## The rule: a delete's space split of a leaf whose parent is full and time split -/

/-- A delete, the merges off, of a key whose access path from the segment root
rk ends with g, q, L, by a bitmap in the segment leaf L, which existed before
the transaction, keeps a live klong, is full by its size, has no bitmap of the
transaction last, and whose last version without the key has more than h
klongs: L is space split, its parent q, full with the two klongs to L's halves,
time split, below the grandparent g with room. The delete changes the reading
by itself alone. -/
theorem writerWP_del_spaceTime (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hsa : 1 ≤ c.p.splitAbove) (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1 ∧
      c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
      n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)))
          []).2.2 (w.next + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w q = none ∧ q ≠ w.top.rootKey)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨hnt, hne, hkeep, hnotTD, hfull, hbig, hfirst, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hqval, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  apply writerWP_del_path c base hvc pre cv rk w S0 kq k1 q L n qn gn hrk ht hidn hidv hwfG
    hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hlg3 hpg hgv
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hgtk : w.taken.contains g = false :=
    ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
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
  have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
    intro z hz
    cases h' : w.nodes.lookup z with
    | none => rfl
    | some _ => have := hidn z (by rw [h']; rfl); omega
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnodenone z hz,
      (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz,
      (hbase z hz).2]
  have hLlt : L < w.next := hsrc3 L (by rw [hlk3]; rfl)
  have hqlt : q < w.next := hsrc3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrc3 g (by rw [hlg3]; rfl)
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  obtain ⟨hleq, _, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  have hlastE : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) =
      ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hnl, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  have hpne : pairs ≠ [] := by
    intro he
    rw [hlastE, he] at hbig
    simp [KNode.size, newKlongs] at hbig
    omega
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_spaceGen c L n cv (d'' + 1) w3
    (fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')
    hlk3 hne hnotTD hfull ?_) ?_
  · intro s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by
      rw [← hw3']; exact hsrc3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hny : w3'.nodes.lookup w3'.next = none := by
      cases h' : w3'.nodes.lookup w3'.next with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny2 : w3'.nodes.lookup (w3'.next + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny3 : w3'.nodes.lookup (w3'.next + 2 + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2 + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_handleFullWith_delSpaceTime d'' L q g n qn gn kq k1 _ c w3'
      hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hfirst hqfirst hbig (by rw [hnext3']; exact hqfull)
      hqsplit hpg' hpq' hpk' hroomg hdeadg hny hny2 hny3) ?_
    intro _ w4 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h4t, h4top, h4v, h4nodes⟩
    rw [hnext3'] at h4nodes hq_look
    rw [hnl, hlastE] at h4nodes hq_look
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hvl : w4.vals = w.vals := h4v.trans hr3'.2.2.2.1
    have htp : w4.top = w.top := h4top.trans hr3'.2.1
    have hV4 : wValue base w4 = wValue base w := by
      funext a; simp only [wValue, htk, hvl]
    have hlqm : ({ leaf := qn.leaf, ks := lq.ks } : KNode) = lq := by
      cases lq; simp only at hq_leaf ⊢; rw [hq_leaf]
    have hres := getFromR_delSpaceTime (wNode c.p base w) (wNode c.p base w4) (wValue base w)
      c.i c.p.fuel hfuel w.top.rootKey L q g w.next (w.next + 2) (w.next + 2 + 2) n qn gn
      ⟨qn.leaf, lq.ks⟩ k1 kq pre cv rk pairs hps hpne hpl hwfG hNL hnl hnt hNq hql hqt hk1L hrange
      hNg hgl hgt hkqg
      (by
        simp only [wNode, htk, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4nodes,
          show w.next ≠ L by omega, show w.next ≠ q by omega, show w.next ≠ g by omega])
      (by
        simp only [wNode, htk, hntake (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega,
          show w.next + 2 ≠ g by omega, show w.next + 2 ≠ w.next by omega])
      (by
        simp only [wNode, htk, hntake (w.next + 2 + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
          show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next by omega,
          show w.next + 2 + 2 ≠ w.next + 2 by omega])
      rfl (by rw [hlqm]; exact hq_wf) (by rw [hlqm]; exact hq_times)
      (by intro c'; rw [hlqm, hq_look c'])
      (by simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq])
      (by
        intro m hm
        simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes,
          Option.some.injEq] at hm
        rw [← hm]; exact KNode.toPrev_wf n _ hnwf)
      (by
        intro x hxL hxq hxg hxF hxS hxYq
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxF, hxS, hxYq, ↓reduceIte])
      hqval (hfreshV _ (by omega))
      hqL hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (hfreshN _ (by omega)) (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega))
      hLroot.symm (by omega) (by omega) hqroot.symm (by omega)
      hrq hrg hrk (keyWf_last_notin pre cv hkey) hvisL huniq
      (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
        (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
      (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
        (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
      (fun x xn cc z hx hxn hz => by
        have := hlinks x xn cc z hx hxn hz; exact ⟨by omega, by omega, by omega⟩)
    intro key' hkey'
    unfold wGet
    rw [htp, hV4, hres key' hkey']
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

/-! ## The reading after a delete's space split and its parent's space split -/

/-- `getFromR_spaceSpace` for a delete: the halves of the leaf's last version
without cv, `⟨true, newKlongs i pairs⟩`. -/
theorem getFromR_delSpaceSpace (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g F S Fq Sq : NodeId)
    (n qn gn : KNode) (k1 kq : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (pairs : List (Nat × NodeId)) (hps : CvSorted pairs) (hpne : pairs ≠ [])
    (hpl : ∀ c, pairs.lookup c = if c == cv then none else n.live.lookup c)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live) (hkqr : kq ≤ r.1)
    (hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c')
    (hside : (∀ a ∈ [(k1, F), ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)], r.1 ≤ a.1) ∨
      (∀ a ∈ [(k1, F), ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)], a.1 < r.1))
    (hN2F : N2 F = some (halves true i ⟨true, newKlongs i pairs⟩ []).1)
    (hN2S : N2 S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1)
    (hN2g : N2 g = some ((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i)
        [(k1, F), ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)]).2.2 Sq)))
    (hN2Fq : N2 Fq = some (halves qn.leaf i (qn.lastVersion i)
      [(k1, F), ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)]).1)
    (hN2Sq : N2 Sq = some (halves qn.leaf i (qn.lastVersion i)
      [(k1, F), ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ Fq → x ≠ Sq → N2 x = N x)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hgF : g ≠ F) (hgS : g ≠ S)
    (hFL : F ≠ L) (hSL : S ≠ L) (hFq : F ≠ q) (hSq : S ≠ q) (hFS : F ≠ S)
    (hFqq : Fq ≠ q) (hFqg : Fq ≠ g) (hFqF : Fq ≠ F) (hFqS : Fq ≠ S)
    (hSqq : Sq ≠ q) (hSqg : Sq ≠ g) (hSqF : Sq ≠ F) (hSqS : Sq ≠ S) (hFqSq : Fq ≠ Sq)
    (hNF : N F = none) (hNS : N S = none) (hNFq : N Fq = none)
    (hNSq : N Sq = none)
    (hrootL : root ≠ L) (hrootF : root ≠ F) (hrootS : root ≠ S) (hrootq : root ≠ q)
    (hrootFq : root ≠ Fq) (hrootSq : root ≠ Sq)
    (hrq : ReachS N i root q) (hrg : ReachS N i root g)
    (hnoq : ¬ ReachS N i q g) (hnoL : ¬ ReachS N i L g)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (honlyq : ∀ x xn c, ReachS N i root x → N x = some xn → (c, q) ∈ xn.liveAt i →
      x = g ∧ c = kq)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ F ∧ z ≠ S ∧ z ≠ Fq ∧ z ≠ Sq) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let sc := (halves true i ⟨true, newKlongs i pairs⟩ []).2.2
  let q2 : KNode := (qn.add i (.key k1 F)).add i (.key sc S)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q2 else if x = g then some gn
    else if x = Fq then none else if x = Sq then none else N2 x
  have hN1q : N1 q = some q2 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1F : N1 F = some (halves true i ⟨true, newKlongs i pairs⟩ []).1 := by
    simp [N1, hFq, hgF.symm, hFqF.symm, hSqF.symm, hN2F]
  have hN1S : N1 S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1 := by
    simp [N1, hSq, hgS.symm, hFqS.symm, hSqS.symm, hN2S]
  have hN1Fq : N1 Fq = none := by simp [N1, hFqq, hFqg]
  have hN1Sq : N1 Sq = none := by simp [N1, hSqq, hSqg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N1 x = N x := by
    intro x h1 h2 h3 h4
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxF : x = Fq
      · subst hxF; simp [N1, h2, hxg, hNFq]
      · by_cases hxS : x = Sq
        · subst hxS; simp [N1, h2, hxg, hxF, hNSq]
        · simp only [N1, h2, hxg, hxF, hxS, ↓reduceIte]
          exact hN2 x h1 h2 hxg h3 h4 hxF hxS
  -- step A: N1 reads as the put
  have hA := getFromR_spaceSplit_del N N1 V i fuel hfuel root L q F S n qn k1 pre cv rk pairs hps
    hpne hpl hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hrange hN1q hN1F hN1S hN1 hqL hFL hNF
    hrootL hrootF hrootS hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1⟩)
  -- the nodes N1 reaches: N's but L, and F and S
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hq2wf : klongsWf q2.ks = true :=
    KNode.add_key_wf _ i sc S (KNode.add_key_wf qn i k1 F hqwf)
  have hq2t : ∀ s, Klong.time s ∈ q2.ks → s ≤ i :=
    KNode.add_times _ i (.key sc S) (fun s h => by cases h)
      (KNode.add_times qn i (.key k1 F) (fun s h => by cases h) hqt)
  have hq2look : ∀ c, q2.live.lookup c =
      if sc == c then some S else if k1 == c then some F else qn.live.lookup c := by
    intro c
    rw [KNode.add_key_live_lookup_of_wf _ i sc c S (KNode.add_key_wf qn i k1 F hqwf),
      KNode.add_key_live_lookup_of_wf qn i k1 c F hqwf]
  have hq2mem : ∀ c z, (c, z) ∈ q2.liveAt i →
      ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = F ∨ z = S := by
    intro c z hz
    rw [KNode.liveAt_of_times _ i hq2t] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [hq2look] at this
    by_cases h1 : sc = c
    · subst h1; simp at this; exact Or.inr (Or.inr this.symm)
    · have h1' : (sc == c) = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte] at this
      by_cases h2 : k1 = c
      · subst h2; simp at this; exact Or.inr (Or.inl this.symm)
      · have h2' : (k1 == c) = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte] at this
        left; rw [KNode.liveAt_of_times qn i hqt]
        exact ⟨lookup_some_mem this, fun h => h2 h.symm⟩
  have hhalf : ∀ x xn c z, (x = F ∨ x = S) → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      (c, z) ∈ n.liveAt i := by
    intro x xn c z hx hn hz
    have hpn : (pairs.map Prod.fst).Nodup :=
      List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
    have hmemp : (c, z) ∈ pairs := by
      rcases hx with hx | hx
      · subst hx; rw [hN1F] at hn; cases hn
        rw [KNode.liveAt_of_times _ i (halves_nil_times i pairs).1] at hz
        exact halves_nil_live_mem i pairs hpne c z (Or.inl hz)
      · subst hx; rw [hN1S] at hn; cases hn
        rw [KNode.liveAt_of_times _ i (halves_nil_times i pairs).2] at hz
        exact halves_nil_live_mem i pairs hpne c z (Or.inr hz)
    have hl := lookup_some_of_mem hpn hmemp
    rw [hpl] at hl
    by_cases hc : c = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem hl
  have hreachNe : ∀ x, ReachS N i root x → x ≠ F ∧ x ≠ S ∧ x ≠ Fq ∧ x ≠ Sq := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootF, hrootS, hrootFq, hrootSq⟩
    | step x' xn c _ hx' hn hz => exact hfr x' xn c _ hx' hn hz
  have hreach1 : ∀ x, ReachS N1 i root x →
      (ReachS N i root x ∧ x ≠ L) ∨ x = F ∨ x = S := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hq2mem c z hz with ⟨hz', hck⟩ | hzF | hzS
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzF)
          · exact Or.inr (Or.inr hzS)
        · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x' hx'
          rw [hN1 x' hx'L hxq hxF hxS] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · have hz' := hhalf x' xn c z (Or.inl hx') hn hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
      · have hz' := hhalf x' xn c z (Or.inr hx') hn hz
        left
        refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
        subst hzL
        exact hqL (honlyL _ n c hrL hNL hz').1.symm
  -- step B: q split at g into Fq and Sq
  have hwfh := halves_newKlongs_wf true i pairs []
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS
    · by_cases hxq : x = q
      · subst hxq; rw [hN1q] at hn; cases hn; exact hq2wf
      · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn; exact hwfG x xn hn
    · subst hxF; rw [hN1F] at hn; cases hn; exact hwfh.1
    · subst hxS; rw [hN1S] at hn; cases hn; exact hwfh.2
  have hnotq1 : ∀ x xn c z, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn c z hx hxg hn hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c x hz with ⟨hz', _⟩ | hzF | hzS
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hFq hzF.symm
        · exact hSq hzS.symm
      · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · exact hgL (honlyq L n c hrL hNL (hhalf x xn c z (Or.inl hxF) hn hz)).1.symm
    · exact hgL (honlyq L n c hrL hNL (hhalf x xn c z (Or.inr hxS) hn hz)).1.symm
  have hnotFS1 : ∀ x xn c z, ReachS N1 i root x → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Fq ∧ z ≠ Sq := by
    intro x xn c z hx hn hz
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c z hz with ⟨hz', _⟩ | hzF | hzS
        · exact (hfr x qn c z hx' hNq hz').2.2
        · rw [hzF]; exact ⟨hFqF.symm, hSqF.symm⟩
        · rw [hzS]; exact ⟨hFqS.symm, hSqS.symm⟩
      · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn
        exact (hfr x xn c z hx' hn hz).2.2
    · exact (hfr L n c z hrL hNL (hhalf x xn c z (Or.inl hxF) hn hz)).2.2
    · exact (hfr L n c z hrL hNL (hhalf x xn c z (Or.inr hxS) hn hz)).2.2
  -- the halves of q with the klongs put
  have hq2look' : ∀ c, q2.live.lookup c =
      [(k1, F), (sc, S)].foldl (pairLookupStep c) (qn.live.lookup c) := by
    intro c
    rw [hq2look c]
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
  obtain ⟨hscq, hFl, hSl, hFwf, hSwf, hFt, hSt, hsF, hsS⟩ :=
    halves_inner_searchLte_ins qn q2 i [(k1, F), (sc, S)] hql r hr hsc hside hq2t hq2look'
  have hg2 : (((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 Sq))).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hgl
  have hgsearch : ∀ c : Nat, ((((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 Sq))).searchLte i c).map
        (·.y) =
      (gn.searchLte i c).map (fun fd => if fd.y = q then
        (if c < (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 then Fq else Sq)
        else fd.y) := by
    intro c
    rw [hscq]
    have hA := KNode.splitParent_searchLte gn i kq r.1 q Fq Sq hgwf hgt hkq hkqr hgap c
    rw [hA]
    cases hs : gn.searchLte i c with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Option.some.injEq]
      have hmemfd := KNode.searchLte_mem gn i c fd hs
      have hyq : fd.y = q ↔ fd.c = kq := by
        constructor
        · intro hy
          rw [hy] at hmemfd
          exact (honlyq g gn fd.c hrg hNg hmemfd).2
        · intro hc
          rw [KNode.liveAt_of_times gn i hgt, hc] at hmemfd
          exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup gn) hmemfd).symm.trans
            (lookup_some_of_mem (KNode.live_keys_nodup gn) hkq))
      by_cases hc : fd.c = kq
      · simp only [hc, ↓reduceIte, hyq.mpr hc, Int.ofNat_lt]
      · have hy : ¬ fd.y = q := fun h => hc (hyq.mp h)
        simp only [hc, ↓reduceIte, hy]
  have hrq1 : ReachS N1 i root q := by
    have htr : ∀ x, ReachS N i root x → ¬ ReachS N i q x → ¬ ReachS N i L x →
        ReachS N1 i root x := by
      intro x hx
      induction hx with
      | root => intro _ _; exact ReachS.root
      | step x' xn c z hx' hn hz ih =>
        intro hq hL
        have hq' : ¬ ReachS N i q x' := fun h => hq (ReachS.step x' xn c z h hn hz)
        have hL' : ¬ ReachS N i L x' := fun h => hL (ReachS.step x' xn c z h hn hz)
        have hx'q : x' ≠ q := by intro he; subst he; exact hq' ReachS.root
        have hx'L : x' ≠ L := by intro he; subst he; exact hL' ReachS.root
        obtain ⟨hxF, hxS, _, _⟩ := hreachNe x' hx'
        have hn1 : N1 x' = some xn := by rw [hN1 x' hx'L hx'q hxF hxS]; exact hn
        exact ReachS.step x' xn c z (ih hq' hL') hn1 hz
    have hrg1 : ReachS N1 i root g := htr g hrg hnoq hnoL
    exact ReachS.step g gn kq q hrg1 hN1g (by rw [KNode.liveAt_of_times gn i hgt]; exact hkq)
  have hsame1 : ∀ x, x ≠ q → x ≠ g → x ≠ Fq → x ≠ Sq → N2 x = N1 x := by
    intro x h1 h2 h3 h4
    simp only [N1, h1, h2, h3, h4, ↓reduceIte]
  have hget := fun c => getEqR_split_inner N1 N2 i root q g Fq Sq gn _ q2 _ _ _ hN1g hgl hN2g hg2
    hgsearch hN1q (by simp only [q2, KNode.add_leaf]; exact hql) hrq1 hN2Fq hFl hN2Sq hSl
    (fun c hc => by rw [hscq] at hc; exact hsF c hc) (fun c hc => by rw [hscq] at hc; exact hsS c hc)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    hnotFS1 hgq.symm c
  have hsim := getFromR_split N1 N2 V i fuel root q g Fq Sq hwf1
    (fun c x hx hxq hxF hxS => (hget c fuel).1 x hx hxq hxF hxS)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4) (by rw [hN2g, hN1g]; rfl)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    (fun xn c z hxn _ hxl => by rw [hN1g] at hxn; cases hxn; rw [hgl] at hxl; cases hxl)
    (fun x xn c z hx hn hz => ⟨fun _ => (hnotFS1 x xn c z hx hn hz).1, (hnotFS1 x xn c z hx hn hz).2⟩)
  intro key' hkey'
  rw [hsim key' root ReachS.root hrootq hrootFq hrootSq]
  exact hA key' hkey'

/-! ## The rule: a delete's space split of a leaf whose parent is full and space split -/

/-- `writerWP_del_spaceTime` with the parent q full by its size with more than h
klongs in its last version, at least two of them live, space split, below the
grandparent g with room for two klongs; the keys of q's live klongs but the
empty key's lie between g's klong kq and its next one, and neither q nor L
reaches g. -/
theorem writerWP_del_spaceSpace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hsa : 1 ≤ c.p.splitAbove) (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1 ∧
      c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
      n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ c.p.M < qn.size + 2 + 1 ∧
      qn.firstTime ≠ some c.i ∧ c.p.splitAbove < (qn.lastVersion c.i).size ∧
      2 ≤ qn.live.length ∧ q ≠ w.top.rootKey)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hacyc : ¬ ReachS (wNode c.p base w) c.i q (pathEnd rk S0) ∧
      ¬ ReachS (wNode c.p base w) c.i L (pathEnd rk S0))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨hnt, hne, hkeep, hnotTD, hfull, hbig, hfirst, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hq2, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  apply writerWP_del_path c base hvc pre cv rk w S0 kq k1 q L n qn gn hrk ht hidn hidv hwfG
    hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hlg3 hpg hgv hacyc
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hgtk : w.taken.contains g = false :=
    ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
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
  have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
    intro z hz
    cases h' : w.nodes.lookup z with
    | none => rfl
    | some _ => have := hidn z (by rw [h']; rfl); omega
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnodenone z hz,
      (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz,
      (hbase z hz).2]
  have hLlt : L < w.next := hsrc3 L (by rw [hlk3]; rfl)
  have hqlt : q < w.next := hsrc3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrc3 g (by rw [hlg3]; rfl)
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  obtain ⟨hleq, _, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  have hlastE : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) =
      ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hnl, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  have hpne : pairs ≠ [] := by
    intro he
    rw [hlastE, he] at hbig
    simp [KNode.size, newKlongs] at hbig
    omega
  -- the divider of q's halves
  obtain ⟨r, hr⟩ : ∃ r, (qn.live.drop (qn.live.length / 2)).head? = some r := by
    cases h' : qn.live.drop (qn.live.length / 2) with
    | nil => have := congrArg List.length h'; simp at this; omega
    | cons a _ => exact ⟨a, rfl⟩
  have hsc : 0 < r.1 := by
    obtain ⟨a, ha⟩ : ∃ a, a ∈ qn.live.take (qn.live.length / 2) := by
      cases h' : qn.live.take (qn.live.length / 2) with
      | nil =>
        have := congrArg List.length h'
        rw [List.length_take] at this; simp only [List.length_nil] at this; omega
      | cons a _ => exact ⟨a, by simp⟩
    have := halves_left_lt_divider qn.live _ qn.live_order r hr a ha
    omega
  have hrmem : r ∈ qn.live := List.mem_of_mem_drop (List.mem_of_head? hr)
  have hkqr : kq ≤ r.1 := (hrangeq r.1 r.2 hrmem hsc).1
  have hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c' := by
    intro c' z hcz
    by_cases hle : c' ≤ kq
    · exact Or.inl hle
    · exact Or.inr ((hrangeq r.1 r.2 hrmem hsc).2 c' z hcz (by omega))
  -- the divider of L's halves, between k1 and q's next key
  obtain ⟨rL, hrL⟩ : ∃ rL, (pairs.drop (pairs.length / 2)).head? = some rL := by
    cases hd : (pairs.drop (pairs.length / 2)) with
    | nil =>
      have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
      have : pairs.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hpne
    | cons a _ => exact ⟨a, rfl⟩
  have hscL : (halves true c.i ⟨true, newKlongs c.i pairs⟩ []).2.2 = rL.1 := by
    rw [halves_leaf_shape c.i pairs [] rL hrL]
    simp
  have hrLmem : rL ∈ n.live := by
    have hm := List.mem_of_mem_drop (List.mem_of_head? hrL)
    have hl := lookup_some_of_mem hpn hm
    rw [hpl] at hl
    by_cases hc : rL.1 = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (rL.1 == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact lookup_some_mem hl
  have hside : (∀ a ∈ [(k1, w.next), ((halves true c.i ⟨true, newKlongs c.i pairs⟩ []).2.2,
        w.next + 2)], r.1 ≤ a.1) ∨
      (∀ a ∈ [(k1, w.next), ((halves true c.i ⟨true, newKlongs c.i pairs⟩ []).2.2,
        w.next + 2)], a.1 < r.1) := by
    rw [hscL]
    have hL1 := (hrange rL.1 rL.2 hrLmem).1
    by_cases hrk1 : r.1 ≤ k1
    · left
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | ha <;> (subst ha; simp only; omega)
    · right
      have hL2 := (hrange rL.1 rL.2 hrLmem).2 r.1 r.2 hrmem (by omega)
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | ha <;> (subst ha; simp only; omega)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_spaceGen c L n cv (d'' + 1) w3
    (fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')
    hlk3 hne hnotTD hfull ?_) ?_
  · intro s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by
      rw [← hw3']; exact hsrc3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hny : w3'.nodes.lookup w3'.next = none := by
      cases h' : w3'.nodes.lookup w3'.next with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny2 : w3'.nodes.lookup (w3'.next + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny3 : w3'.nodes.lookup (w3'.next + 2 + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2 + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny4 : w3'.nodes.lookup (w3'.next + 2 + 2 + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2 + 2 + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_handleFullWith_delSpaceSpace d'' L q g n qn gn kq k1 _ c w3'
      hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hfirst hqfirst hbig hqfull
      hqsplit hpg' hpq' hpk' hroomg hdeadg hny hny2 hny3 hny4) ?_
    intro _ w4 ⟨h4t, h4top, h4v, h4nodes⟩
    rw [hnext3'] at h4nodes
    rw [hnl, hlastE] at h4nodes
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hvl : w4.vals = w.vals := h4v.trans hr3'.2.2.2.1
    have htp : w4.top = w.top := h4top.trans hr3'.2.1
    have hV4 : wValue base w4 = wValue base w := by
      funext a; simp only [wValue, htk, hvl]
    have hres := getFromR_delSpaceSpace (wNode c.p base w) (wNode c.p base w4) (wValue base w)
      c.i c.p.fuel hfuel w.top.rootKey L q g w.next (w.next + 2) (w.next + 2 + 2)
      (w.next + 2 + 2 + 2) n qn gn k1 kq pre cv rk pairs hps hpne hpl r hr hsc hwfG hNL hnl hnt
      hNq hql hqt hk1L hrange hNg hgl hgt hkqg hkqr hgap hside
      (by
        simp only [wNode, htk, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4nodes,
          show w.next ≠ L by omega, show w.next ≠ q by omega, show w.next ≠ g by omega])
      (by
        simp only [wNode, htk, hntake (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega,
          show w.next + 2 ≠ g by omega, show w.next + 2 ≠ w.next by omega])
      (by simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq])
      (by
        simp only [wNode, htk, hntake (w.next + 2 + 2) (by omega), Bool.false_eq_true, ↓reduceIte,
          h4nodes, show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
          show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next by omega,
          show w.next + 2 + 2 ≠ w.next + 2 by omega])
      (by
        simp only [wNode, htk, hntake (w.next + 2 + 2 + 2) (by omega), Bool.false_eq_true,
          ↓reduceIte, h4nodes, show w.next + 2 + 2 + 2 ≠ L by omega,
          show w.next + 2 + 2 + 2 ≠ q by omega, show w.next + 2 + 2 + 2 ≠ g by omega,
          show w.next + 2 + 2 + 2 ≠ w.next by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
          show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega])
      (by
        intro x hxL hxq hxg hxF hxS hxFq hxSq
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxF, hxS, hxFq, hxSq, ↓reduceIte])
      hqL hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
      (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
      hLroot.symm (by omega) (by omega) hqroot.symm (by omega) (by omega)
      hrq hrg hacyc.1 hacyc.2 hrk (keyWf_last_notin pre cv hkey) hvisL huniq
      (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
        (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
      (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
        (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
      (fun x xn cc z hx hxn hz => by
        have := hlinks x xn cc z hx hxn hz; exact ⟨by omega, by omega, by omega, by omega⟩)
    intro key' hkey'
    unfold wGet
    rw [htp, hV4, hres key' hkey']
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

end SIS.Tree
