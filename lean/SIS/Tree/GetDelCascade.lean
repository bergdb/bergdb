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

end SIS.Tree
