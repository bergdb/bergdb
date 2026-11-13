/-
Whole puts with a cascade of splits keep the writer's tree (bergdb 024-22,
`OpTreeOK`), as prover latest's `writerWP_put_timeSplit2` and
`writerWP_put_spaceSplitTime` (GetChain.lean): the descent to the append below
the grandparent (`writerWP_put_seg_append2`), then the cascade's tree lemma
(`writerWP_put_timeSplit2_tree`, `writerWP_put_spaceSplitTime_tree`).
-/
import SIS.Tree.WriterTreeCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A put of a key whose descent below the segment root rk ends with g, q and
the leaf L, L without room: the writer appends the klong to L at depth d'' + 2
from a state that reads as w, the value at w's next id, the path ending at g,
q, L. -/
theorem writerWP_put_seg_append2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hnoroom : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (post : Bool → W → Prop)
    (hk : ∀ qn gn d'' (w5 : W), wNode c.p base w q = some qn →
      wNode c.p base w (pathEnd rk S0) = some gn →
      (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (pathEnd rk S0, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      (∃ fdg fdq, gn.searchLte c.i cv = some fdg ∧ fdg.c = kq ∧ fdg.y = q ∧
        qn.searchLte c.i cv = some fdq ∧ fdq.c = k1 ∧ fdq.y = L) →
      gn.leaf = false → qn.leaf = false →
      w5.taken = w.taken → w5.top = w.top → w5.next = w.next + 2 →
      w5.nodes.lookup L = some n → w5.nodes.lookup q = some qn →
      w5.nodes.lookup (pathEnd rk S0) = some gn →
      (∀ z, (w5.nodes.lookup z).isSome = true → z < w.next) →
      wNode c.p base w5 = wNode c.p base w →
      (w5.path[d'']?).map (·.2) = some (pathEnd rk S0) → w5.path[d'' + 1]? = some (some kq, q) →
      w5.path[d'' + 1 + 1]? = some (some k1, L) →
      WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, w.next)]) c w5 (fun _ w' => post false w')) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w post := by
  obtain ⟨gn, qn, fdg, fdq, hNg, hgl, hgs, hkq, hgy, hNq, hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
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
  have hgv : (pathEnd rk S0, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hvis.1
    | some e =>
      have hmem : e ∈ S0 := List.mem_of_getLast? hS0
      have := hvis.2 e (by simp [hmem])
      simpa [pathEnd, hS0] using this
  have hlq3 : w3.nodes.lookup q = some qn := hcache3 q qn hqv hNq
  have hlg3 : w3.nodes.lookup (pathEnd rk S0) = some gn := hcache3 _ gn hgv hNg
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hnoroom ⟨hlt, hd⟩
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
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some (pathEnd rk S0) := by
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
  have hpg : (w3.path[d'']?).map (·.2) = some (pathEnd rk S0) := by
    rw [hp3', List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?, hd''] at hlastP
    simpa using hlastP
  have hpq : w3.path[d'' + 1]? = some (some kq, q) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  have hpk : w3.path[d'' + 1 + 1]? = some (some k1, L) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  rw [hlen, hnext3]
  apply hk qn gn d'' _ hNq hNg hqv hgv (hvis.2 (some k1, L) (by simp))
    ⟨fdg, fdq, hgs, hkqc, hgy, hqs, hk1c, hqy⟩ hgl hql
  · exact hr03.2.2.1
  · exact hr03.2.1
  · simp
  · simpa using hlk3
  · simpa using hlq3
  · simpa using hlg3
  · exact hsrcw3
  · rw [← hr03.1]; rfl
  · exact hpg
  · exact hpq
  · exact hpk

/-- `writerWP_put_timeSplit2` keeps the writer's tree: the leaf and its full
parent split in time, the grandparent with room. -/
theorem writerWP_put_timeSplit2_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  apply writerWP_put_seg_append2 c base hvc pre cv h rk w S0 kq k1 q L n hrk ht hidn hidv hpath hNL hnl
    hfull
  intro qn' gn' d'' w5 hNq' hNg' hqv hgv hLv ⟨fdg, fdq, hgs, hkqc, hgy, hqs, hk1c, hqy⟩ hgl hql
    h5t h5top h5next h5L h5q h5g h5src hW5 hpg hpq hpk
  rw [hNq] at hNq'; cases hNq'
  rw [hNg] at hNg'; cases hNg'
  have hgR : ReachS (wNode c.p base w) c.i w.top.rootKey (pathEnd rk S0) :=
    eqVisits_reach _ _ _ cv c.p.fuel rk _ cv hrrk hgv
  have hgk : (kq, q) ∈ gn.liveAt c.i := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs; rw [hkqc, hgy] at this; exact this
  have hqk : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs; rw [hk1c, hqy] at this; exact this
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hLv)
  have hqt' : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgt' : w.taken.contains (pathEnd rk S0) = false :=
    ht (_, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hLn : L < w5.next := by have := h5src L (by rw [h5L]; rfl); omega
  apply writerWP_appendKlongs_timeSplit2_tree base d'' L q (pathEnd rk S0) n qn gn kq k1 cv w.next c w5
  · rw [hW5, h5top]; exact hT
  · rw [hW5, h5top]; exact reachS_tReach _ _ _ _ hgR
  · exact h5L
  · exact h5q
  · exact h5g
  · rw [h5t]; exact hLt
  · rw [h5t]; exact hqt'
  · rw [h5t]; exact hgt'
  · exact hgk
  · exact hqk
  · exact hwf _ gn hgR hNg
  · exact hgt
  · exact hqt
  · exact htimes
  · exact hql
  · exact hgl
  · exact hfirst
  · exact hqfirst
  · exact hfull
  · exact hsplit
  · rw [h5next]; exact hqfull
  · exact hqsplit
  · exact hpg
  · exact hpq
  · exact hpk
  · exact hroomg
  · exact hdeadg
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [hW5]; exact hfree _ (Nat.le_refl _)
  · rw [h5next]; omega
  · rw [h5next]; omega
  · exact hLn
  · intro z hz u c' hu
    rw [hW5, h5top] at *
    rw [h5next] at hz
    exact hfreshT z (by omega) u c' hu

/-- `writerWP_put_spaceSplitTime` keeps the writer's tree: the leaf split in
space, its full parent in time, the grandparent with room. -/
theorem writerWP_put_spaceSplitTime_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 (w.next + 2))).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 (w.next + 2 + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
  apply writerWP_put_seg_append2 c base hvc pre cv h rk w S0 kq k1 q L n hrk ht hidn hidv hpath hNL hnl
    (fun hh => by omega)
  intro qn' gn' d'' w5 hNq' hNg' hqv hgv hLv ⟨fdg, fdq, hgs, hkqc, hgy, hqs, hk1c, hqy⟩ hgl hql
    h5t h5top h5next h5L h5q h5g h5src hW5 hpg hpq hpk
  rw [hNq] at hNq'; cases hNq'
  rw [hNg] at hNg'; cases hNg'
  have hgR : ReachS (wNode c.p base w) c.i w.top.rootKey (pathEnd rk S0) :=
    eqVisits_reach _ _ _ cv c.p.fuel rk _ cv hrrk hgv
  have hgk : (kq, q) ∈ gn.liveAt c.i := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs; rw [hkqc, hgy] at this; exact this
  have hqk : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs; rw [hk1c, hqy] at this; exact this
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hLv)
  have hqt' : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgt' : w.taken.contains (pathEnd rk S0) = false :=
    ht (_, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  apply writerWP_appendKlongs_spaceSplitTime_tree base d'' L q (pathEnd rk S0) n qn gn kq k1 cv w.next
    c w5 r0
  · rw [hW5, h5top]; exact hT
  · rw [hW5, h5top]; exact reachS_tReach _ _ _ _ hgR
  · exact h5L
  · exact h5q
  · exact h5g
  · rw [h5t]; exact hLt
  · rw [h5t]; exact hqt'
  · rw [h5t]; exact hgt'
  · exact hgk
  · exact hqk
  · exact hwf _ gn hgR hNg
  · exact hgt
  · exact hqt
  · exact htimes
  · exact hnl
  · exact hr0'
  · exact hql
  · exact hgl
  · exact hfirst
  · exact hqfirst
  · exact hfull
  · exact hsplit
  · rw [h5next]; exact hqfull
  · exact hqsplit
  · exact hpg
  · exact hpq
  · exact hpk
  · exact hroomg
  · exact hdeadg
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [hW5]; exact hfree _ (Nat.le_refl _)
  · rw [h5next]; omega
  · rw [h5next]; omega
  · rw [h5next]; omega
  · intro z hz u c' hu
    rw [hW5, h5top] at *
    rw [h5next] at hz
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
