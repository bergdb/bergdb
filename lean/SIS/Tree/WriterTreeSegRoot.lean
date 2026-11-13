/-
The writer's tree kept by a put into a segment root that is a leaf below the
segment leaf of the segment above (bergdb 024-22, `OpTreeOK`), on prover
latest's writer states (GetSegRoot.lean): the descent to the append
(`writerWP_put_segRoot_append`), and the time split of the segment root
(`writerWP_put_segTimeSplit_tree`, from `treeOK_timeSplitAfter`).
-/
import SIS.Tree.WriterTreePutInv
import SIS.Tree.GetSegLeaf

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A put of a key pre0 ++ [k1, cv] whose segment root L for k1 is a leaf with
no room: after the descents and the new value the writer appends the klong to
L from a state that reads as w, with the value at w's next id and the access
path ending at the segment leaf q above and L. -/
theorem writerWP_put_segRoot_append (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hnoroom : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hqwf : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → klongsWf qn.ks = true)
    (post : Bool → W → Prop)
    (hk : ∀ q qn d' (w5 : W), (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true → (k1, L) ∈ qn.liveAt c.i →
      w5.taken = w.taken → w5.top = w.top → w5.next = w.next + 2 →
      w5.nodes.lookup L = some n → w5.nodes.lookup q = some qn →
      (∀ z, (w5.nodes.lookup z).isSome = true → z < w.next) →
      wNode c.p base w5 = wNode c.p base w →
      (w5.path[d']?).map (·.2) = some q → w5.path[d' + 1]? = some (some k1, L) →
      WriterWP (appendKlongs (d' + 1) L [(cv, w.next)]) c w5 (fun _ w' => post false w')) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w post := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  have hvk1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ k1 [cv] pre0 _ rq hrq
  have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
    rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  have hvcv : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey := by
    rw [hkey']; exact fromVisits_append _ _ _ (pre0 ++ [k1]) cv _ L hsegL
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre0 ++ [k1, cv]) (some h) [k1, cv] (by simp) _ pre0
    w.top.rootKey rq w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrq)
    (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rq k1 [cv] (by simp)]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i k1 c.p.fuel rq,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk1 q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path k1 c base hvc c.p.fuel rq w2' ht1 hp2')
    (writerWP_descendLte_cache k1 c base hvc c.p.fuel rq w2' ht1)) ?_
  intro q w3 ⟨⟨hr23, qn, hq, hql, hlkq3, hvisq, hgetq, hdpq⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hq hvisq hgetq hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  rw [writerWP_getNode_known q qn c _ (by simpa using hlkq3)]
  rw [hL] at hgetq
  cases hfd : qn.searchEq c.i k1 with
  | none => rw [hfd] at hgetq; cases hgetq
  | some fd =>
    rw [hfd] at hgetq
    simp only [Option.map_some, Option.some.injEq] at hgetq
    have hfdc : fd.c = k1 := KNode.searchEq_c qn c.i k1 fd hfd
    simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
    rw [← hgetq, putSegs.eq_2]
    generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, L)] } : W) = w4
    have hr34 : ReadsAs c.p base w3 w4 := by subst hw4; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hr04 := ReadsAs.trans _ _ _ _ _ hr03 hr34
    have hp4 : w4.path.getLast?.map (·.2) = some L := by subst hw4; simp
    unfold setValue
    wpSimplify
    have ht2 : ∀ q ∈ eqVisits (wNode c.p base w4) c.i cv c.p.fuel L,
        w4.taken.contains q.1 = false := by
      rw [hr04.1, hr04.2.2.1]
      exact fun q hq => ht q (hvcv q hq)
    refine writerWP_mono (writerWP_and
      (writerWP_descendLte_path cv c base hvc c.p.fuel L w4 ht2 hp4)
      (writerWP_descendLte_cache cv c base hvc c.p.fuel L w4 ht2)) ?_
    intro L' w5 ⟨⟨hr45, n', hn', _, hlk5, _, _, hdp⟩, ⟨_, hsrc5, hpre5⟩⟩
    rw [hr04.1] at hn'
    have hr05 := ReadsAs.trans _ _ _ _ _ hr04 hr45
    have hnext5 : w5.next = w.next := hr05.2.2.2.2
    have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
      obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
      rw [hf2]
      simp [eqVisits, hNL, hnl]
    obtain ⟨hLL, hp5⟩ : L' = L ∧ w5.path = w4.path := by
      rcases hdp with hd | ⟨pre', q', k1', qn', fd', _, _, hq', hql', _, _, _, hqv'⟩
      · exact hd
      · rw [hr04.1, hevL] at hqv'
        simp only [List.mem_singleton, Prod.mk.injEq] at hqv'
        rw [hr04.1, hqv'.1, hNL] at hq'
        cases hq'
        rw [hnl] at hql'
        cases hql'
    subst L'
    rw [hNL] at hn'
    cases hn'
    unfold newValue fresh
    wpSimplify
    rw [writerWP_getNode_known _ n c _ (by simpa using hlk5)]
    have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w5.next))) = false := by
      rw [hnext5]
      cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
      | true => simp
      | false =>
        have : ¬ n.size + 1 < c.p.M := fun hlt => hnoroom ⟨hlt, hd⟩
        simp [this]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
      writerWP_pure]
    have hlast3 : w3.path.getLast?.map (·.2) = some q := by
      rcases hdpq with ⟨hqr, hp3⟩ | ⟨pre', q', k1', qn', fd', hp3, _, _, _, _, _, _, _⟩
      · rw [hp3, hp2', hqr]
      · rw [hp3]; simp
    have hne3 : w3.path ≠ [] := by intro he; rw [he] at hlast3; simp at hlast3
    obtain ⟨d', hd'⟩ : ∃ d', w3.path.length = d' + 1 := by
      cases h' : w3.path.length with
      | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne3
      | succ k => exact ⟨k, rfl⟩
    have hlen : w5.path.length - 1 = d' + 1 := by
      rw [hp5, ← hw4]; simp only [List.length_append, List.length_singleton]; omega
    have hpq : (w5.path[d']?).map (·.2) = some q := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd'] at hlast3
      simpa using hlast3
    have hpk : w5.path[d' + 1]? = some (some fd.c, L) := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_right (by omega), hd']
      simp
    have hlq5 : w5.nodes.lookup q = some qn := by
      have h3 := hcache3 q qn hvisq hq
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      obtain ⟨tl, htl⟩ := hpre5
      rw [← htl, List.lookup_append, h4, h3]; rfl
    have hsrcw5 : ∀ z, (w5.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      rcases hsrc5 z hz with h1 | h1
      · rw [h4] at h1
        rcases hsrc3 z h1 with h2 | h2
        · rcases hsrc2' z h2 with h3 | h3
          · rw [hw2n] at h3; exact hidn z h3
          · exact hidv z h3
        · exact hidv z h2
      · exact hidv z h1
    have hk1 : (k1, L) ∈ qn.liveAt c.i := by
      have := KNode.searchEq_mem qn c.i k1 fd (hqwf q qn hvisq hq) hfd
      rw [← hgetq] at this
      exact this
    rw [hlen, hnext5]
    rw [hfdc] at hpk
    apply hk q qn d' _ hvisq hq hql hk1
    · exact hr05.2.2.1
    · exact hr05.2.1
    · simp [hnext5]
    · simpa using hlk5
    · simpa using hlq5
    · exact hsrcw5
    · rw [← hr05.1]; rfl
    · simpa using hpq
    · simpa using hpk

/-- `writerWP_put_segTimeSplit` keeps the writer's tree: the time split of a
segment root, a leaf that existed before the transaction, below the segment
leaf of the segment above with room. -/
theorem writerWP_put_segTimeSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf
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
  have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
    segRootR_reach _ _ _ _ hwf pre0 _ rq ReachS.root hrq
  have hvk1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ k1 [cv] pre0 _ rq hrq
  have hqR : ∀ q, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    fun q hq => eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hq
  apply writerWP_put_segRoot_append c base hvc pre0 k1 cv h rq L n w hrq ht hidn hidv hL hNL hnl
    hfull (fun q qn hq hqn => hwf q qn (hqR q hq) hqn)
  intro q qn d' w5 hvisq hq hql hk1 h5t h5top h5next h5L h5q h5src hW5 hpq hpk
  obtain ⟨hqt, hroomq, hdeadq⟩ := hseg q qn hvisq hq hql
  have hqTR : TReach (wNode c.p base w) c.i w.top.rootKey q := reachS_tReach _ _ _ _ (hqR q hvisq)
  have hqL : q ≠ L := by
    intro he
    have hl : TLink (wNode c.p base w) c.i q k1 L := ⟨qn, hq, hk1⟩
    rw [← he] at hl
    exact hT.no_self_link q k1 hqTR hl
  have hny : w5.nodes.lookup w5.next = none := by
    cases h' : w5.nodes.lookup w5.next with
    | none => rfl
    | some _ => have := h5src _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_timeSplitLeafParent d' L q n qn k1 cv w.next c w5
    h5L h5q hqL hql hfirst hfull hsplit hpq hpk hroomq hdeadq hny) ?_
  intro _ wf hA
  have hLt : w.taken.contains L = false := by
    have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
      rw [segRootR_snoc, hrq]
      simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
    have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
      have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
      obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
      rw [hf2]
      simp [eqVisits, hNL, hnl]
    have : (L, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey := by
      have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
      rw [hkey']; exact fromVisits_append _ _ _ (pre0 ++ [k1]) cv _ L hsegL _ (by rw [hevL]; simp)
    exact ht _ this
  have hqt' : w.taken.contains q = false := ht (q, k1) (hvk1 _ hvisq)
  have hW5' : ∀ y, wNode c.p base w5 y = wNode c.p base w y := fun y => by rw [hW5]
  apply treeOK_timeSplitAfter c.p base c w5 wf L q n qn k1 cv w.next rfl
    (by rw [hW5, h5top]; exact hT) hA (by rw [hW5]; exact hNL) (by rw [hW5]; exact hq) hqL hk1
    (by rw [hW5, h5top]; exact hqTR) htimes hqt (hwf q qn (hqR q hvisq) hq)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · intro u c' hu; rw [hW5, h5top] at *; rw [h5next]; exact hfreshT _ (by omega) u c' hu
  · rw [hW5]; exact hfree _ (Nat.le_refl _)
  · rw [h5next]; omega
  · intro u c' hu; rw [hW5, h5top] at *; exact hfreshT _ (Nat.le_refl _) u c' hu

end SIS.Tree
