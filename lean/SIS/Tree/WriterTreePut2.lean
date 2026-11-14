/-
The writer's tree kept by whole operations (bergdb 024-22, `OpTreeOK`), more
of `OpGetOK`'s cases: the time split in place of a segment leaf that the
transaction made (`writerWP_put_timeInPlace_seg_tree`, from
`treeOK_nodeUpdate`).
-/
import SIS.Tree.WriterTreeRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A reached node L replaced by a version whose live klongs are L's with the
klong (cv, v) of a fresh v put: the tree is kept. -/
theorem treeOK_nodeUpdate (N N' : NodeId → Option KNode) (t : Time) (r L v : NodeId)
    (n l : KNode) (cv : Nat) (hT : TreeOK N t r) (hLR : TReach N t r L) (hn : N L = some n)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hl_times : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hl_look : ∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q'))
    (hNL : N' L = some l) (hother : ∀ z, z ≠ L → N' z = N z)
    (hvN : N v = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' v) : TreeOK N' t r := by
  have hLv : L ≠ v := fun h => by rw [h, hvN] at hn; cases hn
  have hvN' : N' v = none := by rw [hother v (Ne.symm hLv)]; exact hvN
  have hvR : ¬ TReach N t r v := not_reach_fresh N t r v hT hvN hfresh
  have hy_live : ∀ c' v', (c', v') ∈ l.liveAt t → (c' = cv ∧ v' = v) ∨ (c', v') ∈ n.liveAt t := by
    intro c' v' h
    rw [KNode.liveAt_of_times l t hl_times] at h
    have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' v' h
    rw [hl_look c'] at hlk'
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hlk'
    by_cases hcc : cv = c'
    · subst hcc; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
    · have hb : (cv == c') = false := by simpa using hcc
      rw [hb] at hlk'
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
      right
      rw [KNode.liveAt_of_times n t hnt]
      exact mem_of_lookup_nodup _ c' v' hlk'
  apply treeOK_transfer_gone N N' t r r (fun z => z = v) (fun _ => False) (fun u c' => (u, c')) hT
  · intro z hz; rw [hz]; exact hvR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' z hu _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases huL : u = L
    · rw [huL, hNL] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases hy_live c' z hc with ⟨_, h⟩ | hmem
      · exact Or.inl h
      · exact Or.inr ⟨id, L, c', hLR, ⟨n, hn, hmem⟩, by rw [huL]⟩
    · have huR : TReach N t r u := by
        rcases hu with h | h
        · exact h
        · rw [h, hvN'] at hm; cases hm
      rw [hother u huL] at hm
      exact Or.inr ⟨id, u, c', huR, ⟨m, hm, hc⟩, rfl⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl hl'
    rw [hz] at hl hl'
    have hone : ∀ y d, (TReach N t r y ∨ y = v) → TLink N' t y d v → y = L ∧ d = cv := by
      intro y d hy hl0
      obtain ⟨m, hm, hc⟩ := hl0
      by_cases hyL : y = L
      · rw [hyL, hNL] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases hy_live d v hc with ⟨hd, _⟩ | hmem
        · exact ⟨hyL, hd⟩
        · exact absurd ⟨n, hn, hmem⟩ (hfresh L d hLR)
      · have hyR : TReach N t r y := by
          rcases hy with h | h
          · exact h
          · rw [h, hvN'] at hm; cases hm
        rw [hother y hyL] at hm
        exact absurd ⟨m, hm, hc⟩ (hfresh y d hyR)
    obtain ⟨h1, h2⟩ := hone u c' hu hl
    obtain ⟨h3, h4⟩ := hone u' c'' hu' hl'
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro _ _ h; exact h
  · by_cases hr : r = L
    · rw [hr, hNL]; exact ⟨_, rfl⟩
    · rw [hother _ hr]; exact hT.rootKey

/-- `writerWP_put_timeInPlace_seg` keeps the writer's tree: the time split in
place of a full segment leaf that the transaction made. -/
theorem writerWP_put_timeInPlace_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime = some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hnext : wNode c.p base w w.next = none)
    (hfresh : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  have hLR : TReach (wNode c.p base w) c.i w.top.rootKey L :=
    reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ cv c.p.fuel rk L cv hrrk hvisL)
  refine writerWP_mono (writerWP_appendKlongs_timeInPlace _ L n cv w3.next c base hvc _
    (by simpa using hlk3) (by rw [hr03.2.2.1]; simpa using hLt) hfirst (by rw [hnext3]; exact hfull)
    hsplit) ?_
  intro _ wf ⟨l, _, _, hl_times, hl_look, _, hftop, _, _, hfN⟩
  simp only at hftop
  rw [hftop, hr03.2.1]
  rw [hnext3] at hl_look
  have hN' : ∀ y, wNode c.p base wf y = if y = L then some l else wNode c.p base w y := by
    intro y
    rw [hfN y, ← hr03.1]
    rfl
  apply treeOK_nodeUpdate (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey L w.next n l cv
    hT hLR hn htimes hl_times hl_look
  · rw [hN' L]; simp
  · intro z hz; rw [hN' z]; simp only [hz, ↓reduceIte]
  · exact hnext
  · exact hfresh

/-- A put of a key whose last segment's leaf L, below an inner parent q, has no
room: after the descent and the new value the writer appends the klong to L
(`appendKlongs` at L's depth) from a state that reads as w, with the value at
w's next id and the access path ending at q and L. -/
theorem writerWP_put_seg_append (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hnoroom : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (post : Bool → W → Prop)
    (hk : ∀ L n q qn k1 d' (w4 : W), (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.liveAt c.i → q ≠ L →
      w4.taken = w.taken → w4.top = w.top → w4.next = w.next + 2 →
      w4.nodes.lookup L = some n → w4.nodes.lookup q = some qn →
      (∀ z, (w4.nodes.lookup z).isSome = true → z < w.next) →
      wNode c.p base w4 = wNode c.p base w →
      (w4.path[d']?).map (·.2) = some q → w4.path[d' + 1]? = some (some k1, L) →
      WriterWP (appendKlongs (d' + 1) L [(cv, w.next)]) c w4 (fun _ w' => post false w')) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w post := by
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
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel rk w2' ht2 hp2')
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _, hdp⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  rcases hdp with ⟨hLrk, _⟩ | ⟨pre', q, k1, qn, fd, hp3, hlast, hq, hql, hqs, hc, hy, hqv⟩
  · subst hLrk
    rw [hinner n hn] at hnl
    cases hnl
  rw [hr0.1] at hq hqv
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hnoroom L n hvisL hn hnl ⟨hlt, hd⟩
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
  have hne : w2'.path ++ pre' ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'
    simp at hp2'
  obtain ⟨d', hd'⟩ : ∃ d', (w2'.path ++ pre').length = d' + 1 := by
    cases h' : (w2'.path ++ pre').length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne
    | succ k => exact ⟨k, rfl⟩
  have hlen : w3.path.length - 1 = d' + 1 := by
    rw [hp3]; simp only [List.append_assoc, List.length_append, List.length_singleton] at hd' ⊢
    omega
  have hpq : (w3.path[d']?).map (·.2) = some q := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hd'] at hlast
    simpa using hlast
  have hpk : w3.path[d' + 1]? = some (some k1, L) := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_right (by omega), hd']
    simp
  have hlq : w3.nodes.lookup q = some qn := hcache3 q qn hqv hq
  have hqL : q ≠ L := by
    intro hqL'
    rw [hqL'] at hq
    rw [hn] at hq
    cases hq
    rw [hnl] at hql
    cases hql
  have hk1 : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fd hqs
    rw [hc, hy] at this
    exact this
  rw [hlen, hnext3]
  apply hk L n q qn k1 d' _ hvisL hn hnl hqv hq hql hk1 hqL
  · exact hr03.2.2.1
  · exact hr03.2.1
  · simp
  · simpa using hlk3
  · simpa using hlq
  · exact hsrcw3
  · rw [← hr03.1]; rfl
  · exact hpq
  · exact hpk

/-- `writerWP_put_timeSplit_seg` keeps the writer's tree: a put into a full
segment leaf that existed before the transaction, split in time below an inner
parent with room. -/
theorem writerWP_put_timeSplit_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
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
  apply writerWP_put_seg_append c base hvc pre cv h rk w hrk ht hidn hidv hinner
    (fun L n hv hn hl => (hleaf L n hv hn hl).2.1)
  intro L n q qn k1 d' w4 hvisL hn hnl hqv hq hql hk1 hqL h4t h4top h4next h4L h4q _ hW4 hpq hpk
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf L n hvisL hn hnl
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hq hql
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt' : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  apply writerWP_appendKlongs_timeSplit_tree base d' L q n qn k1 cv w.next c w4
  · rw [hW4, h4top]; exact hT
  · exact h4L
  · exact h4q
  · rw [h4t]; exact hLt
  · rw [h4t]; exact hqt'
  · exact hqL
  · exact hql
  · exact hfirst
  · exact hfull
  · exact hsplit
  · exact hpq
  · exact hpk
  · exact hroomq
  · exact hdeadq k1
  · exact hk1
  · rw [hW4, h4top]; exact reachS_tReach _ _ _ _ hrq
  · exact htimes
  · exact hqt
  · exact hwf q qn hrq hq
  · rw [hW4, h4next]; exact hfree _ (by omega)
  · rw [h4next, h4t]; exact htn _ (by omega)
  · rw [hW4]; exact hfree _ (Nat.le_refl _)
  · rw [h4next]; omega
  · intro u c' hu; rw [hW4, h4top] at *; rw [h4next]; exact hfreshT _ (by omega) u c' hu
  · intro u c' hu; rw [hW4, h4top] at *; exact hfreshT _ (Nat.le_refl _) u c' hu

/-- `writerWP_put_spaceSplitInPlace_key` keeps the writer's tree: a put into a
full segment leaf that the transaction made, split in space in place below an
inner parent with room. -/
theorem writerWP_put_spaceSplitInPlace_seg_tree (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime = some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
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
  apply writerWP_put_seg_append c base hvc pre cv h rk w hrk ht hidn hidv hinner
    (fun L n hv hn hl hh => by have := (hleaf L n hv hn hl).2.1; omega)
  intro L n q qn k1 d' w4 hvisL hn hnl hqv hq hql hk1 hqL h4t h4top h4next h4L h4q h4src hW4 hpq _
  obtain ⟨htimes, hfull, hmade, hsplit, hlive⟩ := hleaf L n hvisL hn hnl
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hq hql
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt' : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
  have hLn : L < w.next := h4src L (by rw [h4L]; rfl)
  have hqn : q < w.next := h4src q (by rw [h4q]; rfl)
  apply writerWP_appendKlongs_spaceSplitInPlace_tree base d' L q n qn k1 cv w.next c w4 r0
  · rw [hW4, h4top]; exact hT
  · exact h4L
  · exact h4q
  · rw [h4t]; exact hLt
  · rw [h4t]; exact hqt'
  · exact hqL
  · exact hql
  · exact hmade
  · exact hfull
  · exact hsplit
  · exact hpq
  · exact hroomq
  · exact hdeadq
  · rw [h4next]; omega
  · rw [h4next]; omega
  · exact hk1
  · rw [hW4, h4top]; exact reachS_tReach _ _ _ _ hrq
  · exact hnl
  · exact hr0'
  · exact htimes
  · exact hqt
  · exact hwf q qn hrq hq
  · rw [hW4, h4next]; exact hfree _ (by omega)
  · rw [hW4]; exact hfree _ (Nat.le_refl _)
  · rw [h4next, h4t]; exact htn _ (by omega)
  · rw [h4next]; omega
  · intro z hz u c' hu
    rw [hW4, h4top] at *
    rw [h4next] at hz
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
