import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the cascades of a put (bergdb 024-12, TP10; prover
latest's `writerWP_put_timeSplit2`, `writerWP_put_spaceSplitTime`): a leaf L
split whose inner parent q, full, is split too, below a grandparent g with
room. The descent to the append (`writerWP_put_seg_append2`), then the state
after the writer's split (latest's `TimeSplit2After`, `SpaceSplitTimeAfter`),
then the parts about the tree. -/

/-- A put of a key whose descent below the segment root rk ends with the
grandparent g, the parent q and the leaf L, full: after the descent and the
new value the writer appends the klong to L from a state that reads as w,
with the value at w's next id and the access path ending at g, q and L. -/
theorem writerWP_put_seg_append2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (post : Bool → W → Prop)
    (hk : ∀ d'' (w4 : W), (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (pathEnd rk S0, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      qn.leaf = false → gn.leaf = false →
      (k1, L) ∈ qn.liveAt c.i → (kq, q) ∈ gn.liveAt c.i →
      q ≠ L → pathEnd rk S0 ≠ q → pathEnd rk S0 ≠ L →
      w4.taken = w.taken → w4.top = w.top → w4.next = w.next + 2 →
      w4.nodes.lookup L = some n → w4.nodes.lookup q = some qn →
      w4.nodes.lookup (pathEnd rk S0) = some gn →
      (∀ z, (w4.nodes.lookup z).isSome = true → z < w.next) →
      wNode c.p base w4 = wNode c.p base w →
      (w4.path[d'']?).map (·.2) = some (pathEnd rk S0) → w4.path[d'' + 1]? = some (some kq, q) →
      w4.path[d'' + 1 + 1]? = some (some k1, L) →
      WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, w.next)]) c w4 (fun _ w' => post false w')) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w post := by
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hk
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
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
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
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
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.liveAt c.i := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [hkqc, hgy] at this; exact this
  rw [hlen, hnext3]
  refine hk d'' _ hqv hgv hvisL hql hgl hk1L hkqg hqL hgq hgL ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hr03.2.2.1
  · exact hr03.2.1
  · rfl
  · simpa using hlk3
  · simpa using hlq3
  · simpa using hlg3
  · exact hsrcw3
  · rw [← hr03.1]; rfl
  · simpa using hpg
  · simpa using hpq
  · simpa using hpk

/-- `live_of_lookup` with the other compare values apart. -/
theorem live_of_lookup' (l n : KNode) (cv : Nat) (v : NodeId)
    (h : ∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') :
    ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c' ≠ cv ∧ (c', z) ∈ n.live) := by
  intro c' z hz
  by_cases hc : c' = cv
  · subst hc
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup l) c' z hz
    rw [h c'] at hl
    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
    exact Or.inl ⟨rfl, hl.symm⟩
  · rcases live_of_lookup l n cv v h c' z hz with h1 | h1
    · exact absurd h1.1 hc
    · exact Or.inr ⟨hc, h1⟩

/-- The parts about the tree after a time split of a leaf L whose inner parent
q, full, is time split too, below the grandparent g: g's klong kq names a new
inner node yq with q's live klongs and k1 to a new leaf yL, which holds L's
live klongs and the put's (cv, v). -/
theorem putInvT_timeSplit2 (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv k1 kq : Nat) (v yL yq L q g : NodeId) (n qn gn l lq : KNode)
    (hv : w.next ≤ v) (hyL : w.next ≤ yL) (hyq : w.next ≤ yq)
    (hvyL : v ≠ yL) (hvyq : v ≠ yq) (hyLq : yL ≠ yq)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hgn : wNode c.p base w g = some gn) (hgl : gn.leaf = false)
    (hg : ReachS (wNode c.p base w) c.i w.top.rootKey g)
    (hkq : (kq, q) ∈ gn.live) (hk1 : (k1, L) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'g : wNode c.p base w' g = some (gn.add c.i (.key kq yq)))
    (hN'yq : wNode c.p base w' yq = some lq) (hlql : lq.leaf = false)
    (hlqt : ∀ s, Klong.time s ∈ lq.ks → s ≤ c.i)
    (hlqlive : ∀ c' z, (c', z) ∈ lq.live → (c' = k1 ∧ z = yL) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live))
    (hN'yL : wNode c.p base w' yL = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ yL → x ≠ yq →
      wNode c.p base w' x = wNode c.p base w x)
    (hpar : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hgnext := hI.lt_next g gn hgn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hgt := hI.times g gn hgn
  have hgwf := hI.wf g gn hgn
  have hkq' : (kq, q) ∈ gn.liveAt c.i := by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkq
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q := ReachS.step g gn kq q hg hgn hkq'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L := ReachS.step q qn k1 L hrq hqn hk1'
  have hqnext := hI.reach_lt q hrq
  have hLnext := hI.reach_lt L hrL
  have honlyq : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, q) ∈ xn.liveAt c.i → x = g ∧ cc = kq :=
    fun x xn cc hx hxn hc => hT x xn cc q hx hxn hc g gn kq hg hgn hkq'
  have honlyL : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hrq hqn hk1'
  have hqL : q ≠ L := by intro he; subst he; rw [hn] at hqn; cases hqn; rw [hnl] at hql; cases hql
  have hgq : g ≠ q := by
    intro he; subst he
    exact hI.tree.no_self_link g kq (reachS_tReach _ _ _ _ hg) ⟨gn, hgn, hkq'⟩
  have hgL : g ≠ L := by intro he; subst he; rw [hn] at hgn; cases hgn; rw [hnl] at hgl; cases hgl
  have hrootq : w.top.rootKey ≠ q := by
    intro he; exact hI.rootFree' g gn kq hg hgn (he ▸ hkq')
  have hrootL : w.top.rootKey ≠ L := by
    intro he; exact hI.rootFree' q qn k1 hrq hqn (he ▸ hk1')
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) (by omega) hvyL hvyq]; exact hvN
  have hgwf' := KNode.add_key_wf gn c.i kq yq hgwf
  have hg't := KNode.add_times gn c.i (.key kq yq) (fun s h => by cases h) hgt
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧ x ≠ q) ∨ x = yL ∨ x = yq ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧
      x ≠ q) ∨ x = yL ∨ x = yq ∨ x = v) (Or.inl ⟨ReachS.root, hrootL, hrootq⟩)
    intro x xn cc z hx hxn hz
    rcases hx with ⟨hx, hxL, hxq⟩ | hx | hx | hx
    · have hxnext := hI.reach_lt x hx
      by_cases hxg : x = g
      · subst hxg
        rw [hN'g] at hxn
        cases hxn
        rcases KNode.add_key_liveAt_mem gn c.i kq yq hgwf hgt cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inl h2))
        · refine Or.inl ⟨ReachS.step x gn cc z hx hgn h2, ?_, ?_⟩
          · intro hzL; subst hzL; exact hgq (honlyL x gn cc hx hgn h2).1
          · intro hzq; subst hzq; exact hne (honlyq x gn cc hx hgn h2).2
      · rw [hother x hxL hxq hxg (by omega) (by omega)] at hxn
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_, ?_⟩
        · intro hzL; subst hzL; exact hxq (honlyL x xn cc hx hxn hz).1
        · intro hzq; subst hzq; exact hxg (honlyq x xn cc hx hxn hz).1
    · subst hx
      rw [hN'yL] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlt] at hz
      rcases hlive cc z hz with ⟨_, h2⟩ | h2
      · exact Or.inr (Or.inr (Or.inr h2))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h2
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h2, ?_, ?_⟩
        · intro hzL; subst hzL
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h2⟩
        · intro hzq; subst hzq; exact hgL (honlyq L n cc hrL hn h2).1.symm
    · subst hx
      rw [hN'yq] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlqt] at hz
      rcases hlqlive cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
      · exact Or.inr (Or.inl h2)
      · rw [← KNode.liveAt_of_times qn c.i hqt] at h2
        refine Or.inl ⟨ReachS.step q qn cc z hrq hqn h2, ?_, ?_⟩
        · intro hzL; subst hzL; exact hne (honlyL q qn cc hrq hqn h2).2
        · intro hzq; subst hzq
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, h2⟩
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hyL
    · subst hx; exact hI.untaken_of_ge _ hyq
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    -- a leaf child after is not g, which stays inner
    have hL'g : L' ≠ g := by
      intro he; subst he; rw [hN'g] at hn'; cases hn'; rw [KNode.add_leaf, hgl] at hnl'; cases hnl'
    have hL'yq : L' ≠ yq := by
      intro he; subst he; rw [hN'yq] at hn'; cases hn'; rw [hlql] at hnl'; cases hnl'
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'q⟩ | hq'yL | hq'yq | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      by_cases hq'g : q' = g
      · subst hq'g
        rw [hN'g] at hq'n
        cases hq'n
        rw [← KNode.liveAt_of_times _ c.i hg't] at hk'
        rcases KNode.add_key_liveAt_mem gn c.i kq yq hgwf hgt k1' L' hk' with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact absurd h2 hL'yq
        · have hL'L : L' ≠ L := by
            intro he; subst he; exact hgq (honlyL q' gn k1' hg hgn h2).1
          have hL'q : L' ≠ q := by
            intro he; subst he; exact hne (honlyq q' gn k1' hg hgn h2).2
          have hL'yL : L' ≠ yL := by have := hI.links q' gn k1' L' hg hgn h2; omega
          rw [hother L' hL'L hL'q hL'g hL'yL hL'yq] at hn'
          rw [KNode.liveAt_of_times gn c.i hgt] at h2
          exact leafOrderAt_parent_add gn n' k1' kq yq q c.i hgwf hgt hkq
            (hI.order q' gn L' n' k1' hg hgn hgl hn' hnl' h2)
      · rw [hother q' hq'L hq'q hq'g (by omega) (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honlyL q' q'n k1' hq'r hq'n hk'').1
        have hL'q : L' ≠ q := by
          intro he; subst he; exact hq'g (honlyq q' q'n k1' hq'r hq'n hk'').1
        have hL'yL : L' ≠ yL := by have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
        rw [hother L' hL'L hL'q hL'g hL'yL hL'yq] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'yL; rw [hN'yL] at hq'n; cases hq'n; rw [hll] at hq'l; cases hq'l
    · subst hq'yq
      rw [hN'yq] at hq'n
      cases hq'n
      have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hrq hqn hql hn hnl hk1
      rcases hlqlive k1' L' hk' with ⟨h1, h2⟩ | ⟨hne, h2⟩
      · subst h1 h2
        rw [hN'yL] at hn'
        cases hn'
        intro c' z hz
        have hb : k1' ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1' < c'' → c' < c'' := by
          rcases hlive c' z hz with ⟨h1, _⟩ | h1
          · subst h1; exact hpar
          · exact hold c' z h1
        refine ⟨hb.1, ?_⟩
        intro c'' z'' hz'' hlt
        rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨_, h3⟩
        · omega
        · exact hb.2 c'' z'' h3 hlt
      · have hk'' : (k1', L') ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact h2
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hne (honlyL q qn k1' hrq hqn hk'').2
        have hL'q : L' ≠ q := by
          intro he; subst he
          exact hI.tree.no_self_link L' k1' (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, hk''⟩
        have hL'yL : L' ≠ yL := by have := hI.links q qn k1' L' hrq hqn hk''; omega
        rw [hother L' hL'L hL'q hL'g hL'yL hL'yq] at hn'
        have ho := hI.order q qn L' n' k1' hrq hqn hql hn' hnl' h2
        intro c' z hz
        refine ⟨(ho c' z hz).1, ?_⟩
        intro c'' z'' hz'' hlt
        rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨_, h3⟩
        · subst h3; exact (ho c' z hz).2 c'' L hk1 hlt
        · exact (ho c' z hz).2 c'' z'' h3 hlt
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-- A put into a full leaf that existed before the transaction, time split,
whose inner parent, full and existing before the transaction, is time split
too, below a grandparent with room, keeps `PutInv` (the writer's tree after it
given; the rule of `writerWP_put_timeSplit2`). -/
theorem putInv_put_timeSplit2 (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hfull, hfirst, hsplit⟩ := hleaf
  obtain ⟨hqfull, hqfirst, hqsplit⟩ := hparent
  obtain ⟨hroomg, hdeadg⟩ := hgp
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  apply writerWP_put_seg_append2 c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk ht
    hI.ids.1 hI.ids.2.1 hpath hNL hnl hNq hNg hfull
  intro d'' w4 hqv hgv hvisL hql hgl hk1 hkq hqL hgq hgL h4t h4top h4next hlk4 hlq4 hlg4 hsrc4 hW4
    hpg hpq hpk
  generalize hgdef : pathEnd rk S0 = g at *
  have hLn := hI.lt_next L n hNL
  have hny : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  have hny2 : w4.nodes.lookup (w4.next + 2) = none := by
    cases h' : w4.nodes.lookup (w4.next + 2) with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_timeSplit2 d'' L q g n qn gn kq k1 cv w.next c w4
    hlk4 hlq4 hlg4 hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit (by rw [h4next]; exact hqfull)
    hqsplit hpg hpq hpk hroomg hdeadg hny hny2 (by omega)) ?_
  intro _ w' ⟨l, lq, hll, _, hlt, hlk, hlql, _, hlqt, hlqk, h't, h'top, _, h'nodes⟩
  rw [h4next] at h'nodes hlqk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hNq).1
  have hgt : w.taken.contains g = false := (wNode_cases _ _ _ _ _ hNg).1
  have hyLt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hyqt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hl_eq : (⟨n.leaf, l.ks⟩ : KNode) = l := by
    cases l with
    | mk lf ks => simp only at hll; rw [hll]
  have hlq_eq : (⟨qn.leaf, lq.ks⟩ : KNode) = lq := by
    cases lq with
    | mk lf ks => simp only at hlql; rw [hlql]
  have hqn' := hI.lt_next q qn hNq
  have hgn' := hI.lt_next g gn hNg
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hNq)]; exact hk1
  have hkql : (kq, q) ∈ gn.live := by
    rw [← KNode.liveAt_of_times gn c.i (hI.times g gn hNg)]; exact hkq
  have e1 : w.next + 2 ≠ L := by omega
  have e2 : w.next + 2 ≠ q := by omega
  have e3 : w.next + 2 ≠ g := by omega
  have e4 : w.next + 2 + 2 ≠ L := by omega
  have e5 : w.next + 2 + 2 ≠ q := by omega
  have e6 : w.next + 2 + 2 ≠ g := by omega
  have e7 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  refine putInvT_timeSplit2 c base w w' hI cv k1 kq w.next (w.next + 2) (w.next + 2 + 2) L q g n qn gn
    l lq (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) (by omega) hNL hnl hNq hql hNg hgl
    hrg hkql hk1l htk (h'top.trans h4top) ?_ ?_ (by rw [hlql]; exact hql) hlqt
    (live_of_lookup' lq qn k1 (w.next + 2) hlqk) ?_ (by rw [hll]; exact hnl) hlt
    (live_of_lookup l n cv w.next hlk) ?_
    (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1l)
  · simp only [wNode, htk, hgt, Bool.false_eq_true, ↓reduceIte, h'nodes, hgL, hgq]
  · simp only [wNode, htk, hyqt, Bool.false_eq_true, ↓reduceIte, h'nodes, e4, e5, e6, e7, hlq_eq]
  · simp only [wNode, htk, hyLt, Bool.false_eq_true, ↓reduceIte, h'nodes, e1, e2, e3, hl_eq]
  · intro x hxL hxq hxg hxyL hxyq
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, hxg, hxyL, hxyq, ↓reduceIte]

/-- The parts about the tree after a space split of a leaf L whose inner parent
q, full, is time split, below the grandparent g: g's klong kq names a new inner
node yq with q's live klongs, k1 to the first half F and the divider sc to the
second half S of L's last version with the put's (cv, v). -/
theorem putInvT_spaceSplitTime (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv sc k1 kq : Nat) (v F S yq L q g : NodeId) (n qn gn f s lq : KNode)
    (hv : w.next ≤ v) (hF : w.next ≤ F) (hS : w.next ≤ S) (hyq : w.next ≤ yq)
    (hvF : v ≠ F) (hvS : v ≠ S) (hvyq : v ≠ yq) (hFS : F ≠ S) (hFyq : F ≠ yq) (hSyq : S ≠ yq)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hgn : wNode c.p base w g = some gn) (hgl : gn.leaf = false)
    (hg : ReachS (wNode c.p base w) c.i w.top.rootKey g)
    (hkq : (kq, q) ∈ gn.live) (hk1 : (k1, L) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'g : wNode c.p base w' g = some (gn.add c.i (.key kq yq)))
    (hN'yq : wNode c.p base w' yq = some lq) (hlql : lq.leaf = false)
    (hlqt : ∀ s, Klong.time s ∈ lq.ks → s ≤ c.i)
    (hlqlive : ∀ c' z, (c', z) ∈ lq.live →
      (c' = sc ∧ z = S) ∨ (c' = k1 ∧ z = F) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live))
    (hN'F : wNode c.p base w' F = some f) (hN'S : wNode c.p base w' S = some s)
    (hfl : f.leaf = true) (hsl : s.leaf = true)
    (hft : ∀ t, Klong.time t ∈ f.ks → t ≤ c.i) (hst : ∀ t, Klong.time t ∈ s.ks → t ≤ c.i)
    (hf : ∀ c' z, (c', z) ∈ f.liveAt c.i → ((c', z) = (cv, v) ∧ cv < sc) ∨ ((c', z) ∈ n.live ∧ c' < sc))
    (hs : ∀ c' z, (c', z) ∈ s.liveAt c.i →
      ((c', z) = (cv, v) ∧ sc ≤ cv) ∨ ((c', z) ∈ n.live ∧ sc ≤ c'))
    (hsc : ∃ zs, (sc, zs) ∈ n.live)
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ yq →
      wNode c.p base w' x = wNode c.p base w x)
    (hpar : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hgnext := hI.lt_next g gn hgn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hgt := hI.times g gn hgn
  have hgwf := hI.wf g gn hgn
  have hkq' : (kq, q) ∈ gn.liveAt c.i := by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkq
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q := ReachS.step g gn kq q hg hgn hkq'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L := ReachS.step q qn k1 L hrq hqn hk1'
  have hqnext := hI.reach_lt q hrq
  have hLnext := hI.reach_lt L hrL
  have honlyq : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, q) ∈ xn.liveAt c.i → x = g ∧ cc = kq :=
    fun x xn cc hx hxn hc => hT x xn cc q hx hxn hc g gn kq hg hgn hkq'
  have honlyL : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hrq hqn hk1'
  have hqL : q ≠ L := by intro he; subst he; rw [hn] at hqn; cases hqn; rw [hnl] at hql; cases hql
  have hgq : g ≠ q := by
    intro he; subst he
    exact hI.tree.no_self_link g kq (reachS_tReach _ _ _ _ hg) ⟨gn, hgn, hkq'⟩
  have hgL : g ≠ L := by intro he; subst he; rw [hn] at hgn; cases hgn; rw [hnl] at hgl; cases hgl
  have hrootq : w.top.rootKey ≠ q := by
    intro he; exact hI.rootFree' g gn kq hg hgn (he ▸ hkq')
  have hrootL : w.top.rootKey ≠ L := by
    intro he; exact hI.rootFree' q qn k1 hrq hqn (he ▸ hk1')
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) (by omega) hvF hvS hvyq]; exact hvN
  have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hrq hqn hql hn hnl hk1
  have hscb : k1 ≤ sc ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → sc < c'' := by
    obtain ⟨zs, hzs⟩ := hsc
    exact hold sc zs hzs
  have hg't := KNode.add_times gn c.i (.key kq yq) (fun s h => by cases h) hgt
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧ x ≠ q) ∨
        x = F ∨ x = S ∨ x = yq ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧
      x ≠ q) ∨ x = F ∨ x = S ∨ x = yq ∨ x = v) (Or.inl ⟨ReachS.root, hrootL, hrootq⟩)
    intro x xn cc z hx hxn hz
    have hhalf : ∀ (m : KNode), (∀ t, Klong.time t ∈ m.ks → t ≤ c.i) →
        (∀ c' z, (c', z) ∈ m.liveAt c.i → (c', z) = (cv, v) ∨ (c', z) ∈ n.live) →
        (cc, z) ∈ m.liveAt c.i →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ q) ∨
          z = F ∨ z = S ∨ z = yq ∨ z = v := by
      intro m _ hm hzm
      rcases hm cc z hzm with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        exact Or.inr (Or.inr (Or.inr (Or.inr h1.2)))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h1
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h1, ?_, ?_⟩
        · intro hzL; subst hzL
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h1⟩
        · intro hzq; subst hzq; exact hgL (honlyq L n cc hrL hn h1).1.symm
    rcases hx with ⟨hx, hxL, hxq⟩ | hx | hx | hx | hx
    · have hxnext := hI.reach_lt x hx
      by_cases hxg : x = g
      · subst hxg
        rw [hN'g] at hxn
        cases hxn
        rcases KNode.add_key_liveAt_mem gn c.i kq yq hgwf hgt cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · refine Or.inl ⟨ReachS.step x gn cc z hx hgn h2, ?_, ?_⟩
          · intro hzL; subst hzL; exact hgq (honlyL x gn cc hx hgn h2).1
          · intro hzq; subst hzq; exact hne (honlyq x gn cc hx hgn h2).2
      · rw [hother x hxL hxq hxg (by omega) (by omega) (by omega)] at hxn
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_, ?_⟩
        · intro hzL; subst hzL; exact hxq (honlyL x xn cc hx hxn hz).1
        · intro hzq; subst hzq; exact hxg (honlyq x xn cc hx hxn hz).1
    · subst hx
      rw [hN'F] at hxn
      cases hxn
      exact hhalf _ hft (fun c' z h => by
        rcases hf c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'S] at hxn
      cases hxn
      exact hhalf _ hst (fun c' z h => by
        rcases hs c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'yq] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlqt] at hz
      rcases hlqlive cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, h2⟩
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inl h2)
      · rw [← KNode.liveAt_of_times qn c.i hqt] at h2
        refine Or.inl ⟨ReachS.step q qn cc z hrq hqn h2, ?_, ?_⟩
        · intro hzL; subst hzL; exact hne (honlyL q qn cc hrq hqn h2).2
        · intro hzq; subst hzq
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, h2⟩
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hF
    · subst hx; exact hI.untaken_of_ge _ hS
    · subst hx; exact hI.untaken_of_ge _ hyq
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    have hL'g : L' ≠ g := by
      intro he; subst he; rw [hN'g] at hn'; cases hn'; rw [KNode.add_leaf, hgl] at hnl'; cases hnl'
    have hL'yq : L' ≠ yq := by
      intro he; subst he; rw [hN'yq] at hn'; cases hn'; rw [hlql] at hnl'; cases hnl'
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'q⟩ | hq'F | hq'S | hq'yq | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      by_cases hq'g : q' = g
      · subst hq'g
        rw [hN'g] at hq'n
        cases hq'n
        rw [← KNode.liveAt_of_times _ c.i hg't] at hk'
        rcases KNode.add_key_liveAt_mem gn c.i kq yq hgwf hgt k1' L' hk' with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact absurd h2 hL'yq
        · have hL'L : L' ≠ L := by
            intro he; subst he; exact hgq (honlyL q' gn k1' hg hgn h2).1
          have hL'q : L' ≠ q := by
            intro he; subst he; exact hne (honlyq q' gn k1' hg hgn h2).2
          have hlt := hI.links q' gn k1' L' hg hgn h2
          rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'yq] at hn'
          rw [KNode.liveAt_of_times gn c.i hgt] at h2
          exact leafOrderAt_parent_add gn n' k1' kq yq q c.i hgwf hgt hkq
            (hI.order q' gn L' n' k1' hg hgn hgl hn' hnl' h2)
      · rw [hother q' hq'L hq'q hq'g (by omega) (by omega) (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honlyL q' q'n k1' hq'r hq'n hk'').1
        have hL'q : L' ≠ q := by
          intro he; subst he; exact hq'g (honlyq q' q'n k1' hq'r hq'n hk'').1
        have hlt := hI.links q' q'n k1' L' hq'r hq'n hk''
        rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'yq] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'F; rw [hN'F] at hq'n; cases hq'n; rw [hfl] at hq'l; cases hq'l
    · subst hq'S; rw [hN'S] at hq'n; cases hq'n; rw [hsl] at hq'l; cases hq'l
    · subst hq'yq
      rw [hN'yq] at hq'n
      cases hq'n
      rcases hlqlive k1' L' hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hne, h2⟩
      · -- the second half, under the divider
        subst h1 h2
        rw [hN'S] at hn'
        cases hn'
        intro c' z hz
        rw [← KNode.liveAt_of_times _ c.i hst] at hz
        have hb : (k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'') ∧ k1' ≤ c' := by
          rcases hs c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
          · exact ⟨hold c' z h1, h2⟩
        refine ⟨hb.2, ?_⟩
        intro c'' z'' hz'' hlt
        rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩
        · omega
        · omega
        · exact hb.1.2 c'' z'' h3 (by omega)
      · -- the first half, under k1
        subst h1 h2
        rw [hN'F] at hn'
        cases hn'
        intro c' z hz
        rw [← KNode.liveAt_of_times _ c.i hft] at hz
        have hb : (k1' ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1' < c'' → c' < c'') ∧ c' < sc := by
          rcases hf c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
          · exact ⟨hold c' z h1, h2⟩
        refine ⟨hb.1.1, ?_⟩
        intro c'' z'' hz'' hlt
        rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩
        · rw [h3]; exact hb.2
        · omega
        · exact hb.1.2 c'' z'' h3 hlt
      · -- an old child of q
        have hk'' : (k1', L') ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact h2
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hne (honlyL q qn k1' hrq hqn hk'').2
        have hL'q : L' ≠ q := by
          intro he; subst he
          exact hI.tree.no_self_link L' k1' (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, hk''⟩
        have hlt := hI.links q qn k1' L' hrq hqn hk''
        rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'yq] at hn'
        have ho := hI.order q qn L' n' k1' hrq hqn hql hn' hnl' h2
        intro c' z hz
        refine ⟨(ho c' z hz).1, ?_⟩
        intro c'' z'' hz'' hlt'
        rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩
        · subst h3
          by_cases hk : k1' < k1
          · have := (ho c' z hz).2 k1 L hk1 hk; omega
          · have hk' : k1 < k1' := by omega
            have := hscb.2 k1' L' h2 hk'; omega
        · subst h3; exact (ho c' z hz).2 _ L hk1 hlt'
        · exact (ho c' z hz).2 c'' z'' h3 hlt'
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-- A put into a full leaf that existed before the transaction, space split,
whose inner parent, full with the two klongs and existing before the
transaction, is time split, below a grandparent with room, keeps `PutInv` (the
writer's tree after it given; the rule of `writerWP_put_spaceSplitTime`). -/
theorem putInv_put_spaceSplitTime (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧
      c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 (w.next + 2))).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 (w.next + 2 + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hfull, hfirst, hsplit, hlive⟩ := hleaf
  obtain ⟨hqfull, hqfirst, hqsplit⟩ := hparent
  obtain ⟨hroomg, hdeadg⟩ := hgp
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  apply writerWP_put_seg_append2 c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk ht
    hI.ids.1 hI.ids.2.1 hpath hNL hnl hNq hNg (fun h' => by omega)
  intro d'' w4 hqv hgv hvisL hql hgl hk1 hkq hqL hgq hgL h4t h4top h4next hlk4 hlq4 hlg4 hsrc4 hW4
    hpg hpq hpk
  generalize hgdef : pathEnd rk S0 = g at *
  have hLn := hI.lt_next L n hNL
  have hfree : ∀ z, w4.next ≤ z → w4.nodes.lookup z = none := by
    intro z hz
    cases h' : w4.nodes.lookup z with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitTime d'' L q g n qn gn kq k1 cv w.next c w4
    hlk4 hlq4 hlg4 hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit (by rw [h4next]; exact hqfull)
    hqsplit hpg hpq hpk hroomg hdeadg (hfree _ (Nat.le_refl _)) (hfree _ (by omega))
    (hfree _ (by omega))) ?_
  intro _ w' ⟨lq, hlql, _, hlqt, hlqk, h't, h'top, _, h'nodes⟩
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht hlqk
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h4next] at h'nodes hlqk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hgt : w.taken.contains g = false := (wNode_cases _ _ _ _ _ hNg).1
  have hFt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hSt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hyt : w.taken.contains (w.next + 2 + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hlq_eq : (⟨qn.leaf, lq.ks⟩ : KNode) = lq := by
    cases lq with
    | mk lf ks => simp only at hlql; rw [hlql]
  have hqn' := hI.lt_next q qn hNq
  have hgn' := hI.lt_next g gn hNg
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hNq)]; exact hk1
  have hkql : (kq, q) ∈ gn.live := by
    rw [← KNode.liveAt_of_times gn c.i (hI.times g gn hNg)]; exact hkq
  have e1 : w.next + 2 ≠ L := by omega
  have e2 : w.next + 2 ≠ q := by omega
  have e3 : w.next + 2 ≠ g := by omega
  have e4 : w.next + 2 + 2 ≠ L := by omega
  have e5 : w.next + 2 + 2 ≠ q := by omega
  have e6 : w.next + 2 + 2 ≠ g := by omega
  have e7 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  have e8 : w.next + 2 + 2 + 2 ≠ L := by omega
  have e9 : w.next + 2 + 2 + 2 ≠ q := by omega
  have e10 : w.next + 2 + 2 + 2 ≠ g := by omega
  have e11 : w.next + 2 + 2 + 2 ≠ w.next + 2 := by omega
  have e12 : w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 := by omega
  -- the time split parent's live klongs
  have hlqlive : ∀ c' z, (c', z) ∈ lq.live → (c' = out.2.2 ∧ z = w.next + 2 + 2) ∨
      (c' = k1 ∧ z = w.next + 2) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live) := by
    intro c' z hz
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup lq) c' z hz
    rw [hlqk c'] at hl
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hl
    by_cases h1 : out.2.2 = c'
    · simp only [h1, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
      exact Or.inl ⟨h1.symm, hl.symm⟩
    · have hb1 : (out.2.2 == c') = false := by simpa using h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hl
      by_cases h2 : k1 = c'
      · simp only [h2, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
        exact Or.inr (Or.inl ⟨h2.symm, hl.symm⟩)
      · have hb2 : (k1 == c') = false := by simpa using h2
        simp only [hb2, Bool.false_eq_true, ↓reduceIte] at hl
        exact Or.inr (Or.inr ⟨fun h => h2 h.symm, lookup_some_mem hl⟩)
  refine putInvT_spaceSplitTime c base w w' hI cv out.2.2 k1 kq w.next (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) L q g n qn gn out.1 out.2.1 lq (Nat.le_refl _) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hNL hnl hNq hql
    hNg hgl hrg hkql hk1l htk (h'top.trans h4top) ?_ ?_ (by rw [hlql]; exact hql) hlqt hlqlive ?_ ?_
    hfl.1 hfl.2 hht.1 hht.2 (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh)
    (by rw [hsc]; exact divider_mem n r0 hr0) ?_
    (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1l)
  · simp only [wNode, htk, hgt, Bool.false_eq_true, ↓reduceIte, h'nodes, hgL, hgq]
  · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h'nodes, e8, e9, e10, e11, e12,
      hlq_eq]
  · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h'nodes, e1, e2, e3]
  · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, e4, e5, e6, e7]
  · intro x hxL hxq hxg hxF hxS hxyq
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, hxg, hxF, hxS, hxyq, ↓reduceIte]

end SIS.Tree
