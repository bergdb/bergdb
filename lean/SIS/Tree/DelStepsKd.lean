/-
Case (4)'s delete steps with the kinds' books (bergdb 024-12, TP7 and TP10,
latest's route): the delete's walk to its leaf with an invariant J whose steps
know where the path ends (`KdPathLast`), as the kinds' lemmas ask
(`kd_descendLte`, `kd_pathAdd`).
-/
import SIS.Tree.DelStepsFull
import SIS.Tree.DelMergeCaseKd

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem kdPathLast_of_getLast (v : W) (r : NodeId) (hp : v.path.getLast?.map (·.2) = some r) :
    KdPathLast v r := by
  cases hl : v.path.getLast? with
  | none => rw [hl] at hp; cases hp
  | some e =>
    rw [hl] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    refine ⟨e.1, ?_⟩
    rw [← List.getLast?_eq_getElem?, hl, ← hp]

theorem kdPathLast_steps (v : W) (p0 steps : List (Option Nat × NodeId)) (r : NodeId)
    (hv : v.path = p0 ++ steps) (hp : p0.getLast?.map (·.2) = some r) :
    KdPathLast v (pathEnd r steps) := by
  apply kdPathLast_of_getLast
  rw [hv, List.getLast?_append]
  cases hs : steps.getLast? with
  | none =>
    simp only [pathEnd, hs, Option.map_none, Option.getD_none, Option.none_or]
    exact hp
  | some e =>
    simp [pathEnd, hs]

theorem writerWP_putSegs_prefix_linkedSJK (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (sfx : List Nat) (hsfx : sfx ≠ []) (post : Bool → W → Prop)
    (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Nat) (x L : NodeId) (n : KNode) (v : W), J v → KdPathLast v L →
      v.nodes.lookup L = some n → Klong.key s x ∈ n.ks → J { v with path := v.path ++ [(some s, x)] }) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W), J w →
      (∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true) →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ sfx) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → J w' → w.nodes.IsPrefix w'.nodes →
        (∀ z, (w'.nodes.lookup z).isSome = true →
          (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) →
        (∃ ps, w'.path = w.path ++ ps ∧ LinkedFrom (wNode c.p base w) c.i r ps ∧ pathEnd r ps = rk ∧
          ∀ z ∈ (r :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w z = some zn →
            w'.nodes.lookup z = some zn) →
        WriterWP (putSegs key value sfx rk) c w' post) →
      WriterWP (putSegs key value (pre ++ sfx) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w hJ _ _ hrk _ hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append]
    exact hcont w (ReadsAs.refl _ _ _) hJ (List.prefix_refl _) (fun z hz => Or.inl hz)
      ⟨[], by simp, LinkedFrom.nil r, rfl, by simp⟩
  | cons s rest ih =>
    intro r rk w hJ hwf ht hrk hp hcont
    have hne : rest ++ sfx ≠ [] := by simp [hsfx]
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ sfx) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ sfx = d :: rest' := by
          cases h' : rest ++ sfx with
          | nil => exact absurd h' hne
          | cons d rest' => exact ⟨d, rest', rfl⟩
        have hvis : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (s :: d :: rest') r,
            w.taken.contains q.1 = false := by
          intro q hq; apply ht q; rw [List.cons_append, he]; exact hq
        simp only [fromVisits] at hvis
        have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
            w.taken.contains q.1 = false := fun q hq => hvis q (List.mem_append_left _ hq)
        unfold setNode
        wpSimplify
        refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
          (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (writerWP_descendLte_steps s c base hvc c.p.fuel r w ht1))
          (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) (hJd s c.p.fuel r w hJ (kdPathLast_of_getLast w r hp))) ?_
        intro L w3 ⟨⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, hget⟩, ⟨steps1, hpf, hp3, hLe⟩⟩,
          ⟨hcache3, hsrc3, hpre3⟩⟩, hJ3⟩
        rw [writerWP_getNode_known L n c _ hlk3]
        rw [hg] at hget
        cases hfd : n.searchEq c.i s with
        | none => rw [hfd] at hget; cases hget
        | some fd =>
          rw [hfd] at hget
          simp only [Option.map_some, Option.some.injEq] at hget
          simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
          rw [← hget]
          generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, y)] } : W) = w4
          have hr04 : ReadsAs c.p base w w4 := by
            subst hw4
            exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
          have h4n : w4.nodes = w3.nodes := by rw [← hw4]
          have h4p : w4.path = w.path ++ steps1 ++ [(some fd.c, y)] := by rw [← hw4]; simp [hp3]
          have hvisAll := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps1 hpf
            (fun m hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
          have hlink : (fd.c, y) ∈ n.liveAt c.i := by
            have hm := KNode.searchEq_mem n c.i s fd (hwf L n hn) hfd
            rw [KNode.searchEq_c n c.i s fd hfd, hget]
            exact hm
          have hPL3 : KdPathLast w3 L := by
            have := kdPathLast_steps w3 w.path steps1 r hp3 hp
            rwa [← hLe] at this
          have hkm : Klong.key fd.c y ∈ n.ks := by rw [hget]; exact kd_searchEq_mem n c.i s fd hfd
          refine ih y rk w4 (by rw [← hw4]; exact hJp fd.c y L n w3 hJ3 hPL3 hlk3 hkm)
            (by rw [hr04.1]; exact hwf) ?_ ?_
            (by rw [h4p]; simp) ?_
          · intro q hq
            rw [hr04.2.2.1]
            rw [hr04.1] at hq
            apply hvis q
            apply List.mem_append_right
            rw [hg]
            simp only
            rw [← he]
            exact hq
          · rw [hr04.1]; exact hrk
          · intro w' hr' hJ' hpre' hsrc' ⟨ps', hp', hl', he', hc'⟩
            rw [hr04.1] at hl' hc'
            refine hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') hJ' ?_ (fun z hz => ?_) ?_
            · rw [h4n] at hpre'; exact hpre3.trans hpre'
            · rcases hsrc' z hz with h1 | h1
              · rw [h4n] at h1
                exact hsrc3 z h1
              · exact Or.inr h1
            · refine ⟨steps1 ++ (some fd.c, y) :: ps', by rw [hp', h4p]; simp, ?_, ?_, ?_⟩
              · refine LinkedFrom.append _ _ r steps1 _ (LinkedFrom.of_pathFrom _ _ s r steps1 hpf) ?_
                rw [← hLe]
                exact LinkedFrom.cons L n fd.c y ps' hn hlink hl'
              · rw [pathEnd_cons_append]; exact he'
              · intro z hz zn hzn
                have hsplit : (r :: (steps1 ++ (some fd.c, y) :: ps').map (·.2)) =
                    (r :: steps1.map (·.2)) ++ (y :: ps'.map (·.2)) := by simp
                rw [hsplit, List.dropLast_append_of_ne_nil (by simp)] at hz
                rcases List.mem_append.mp hz with hz | hz
                · have hzv : (z, s) ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r := by
                    rcases List.mem_cons.mp hz with hz | hz
                    · rw [hz]; exact hvisAll.1
                    · obtain ⟨e, he1, he2⟩ := List.mem_map.mp hz
                      rw [← he2]; exact hvisAll.2 e he1
                  have h3 := hcache3 z zn hzv hzn
                  rw [← h4n] at h3
                  exact lookup_of_isPrefix _ _ hpre' z zn h3
                · exact hc' z hz zn hzn
      · cases hrk

theorem writerWP_del_toLeafMK (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (J : W → Prop) (hJ0 : J w)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → KdPathLast v x →
      WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Nat) (x L : NodeId) (n : KNode) (v : W), J v → KdPathLast v L →
      v.nodes.lookup L = some n → Klong.key s x ∈ n.ks → J { v with path := v.path ++ [(some s, x)] })
    (hJ2 : J ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W))
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hcont : ∀ (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W),
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w L = some n →
      n.leaf = true → ReadsAs c.p base w w3 → J w3 → w3.nodes.lookup L = some n →
      w3.path = (none, w.top.rootKey) :: P →
      LinkedFrom (wNode c.p base w) c.i w.top.rootKey P →
      nodeAt w.top.rootKey P P.length = L →
      (∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
        some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)) →
      WriterWP (deleteUpward L P.length cv (pre ++ [cv])) c w3 (fun _ v => Post v)) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hw2p : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  have hJ2' : J w2 := by rw [← hw2]; exact hJ2
  refine writerWP_putSegs_prefix_linkedSJK c base hvc (pre ++ [cv]) none [cv] (by simp) _ J hJd hJp pre
    w.top.rootKey rk w2 hJ2' (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht)
    (by rw [hr02.1]; exact hrk) (by rw [hw2p]; simp) ?_
  intro w2' hr2' hJ2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2))
    (hJd cv c.p.fuel rk w2' hJ2' (by have := kdPathLast_steps w2' w2.path ps w.top.rootKey hp2' (by rw [hw2p]; rfl); rwa [hpse] at this))) ?_
  intro L w3 ⟨⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, _, hpre3⟩⟩, hJ3⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ cv rk steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk steps hpf
    (fun mm hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
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
  have hlen3 : w3.path.length - 1 = P.length := by rw [hp3']; simp
  unfold pathSize
  wpSimplify
  rw [hlen3]
  refine writerWP_mono (hcont L n P w3 hvisL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX) ?_
  intro noop v hv
  cases noop
  · simp only [Bool.not_false, ↓reduceIte, writerWP_bind]
    exact writerWP_mono (hfresh v hv) (fun _ _ h => by simp only [writerWP_pure]; exact h)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    exact hv

/-! ## The books and the kinds as the walk's invariant -/

/-- The walk's invariant: the put's books and the kinds' books. -/
def KdJ (c : Ctx) (B : NodeId) (top0 : Top) (KO : KindOracle) (BK : NodeId) (v : W) : Prop :=
  PutBook c B top0 v ∧ Book BK c v ∧ KdInv KO BK v

theorem kdJ_descendLte (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (s f : Nat) (x : NodeId) (v : W) (hJ : KdJ c B top0 KO BK v) (hx : KdPathLast v x) :
    WriterWP (descendLte s f x) c v (fun _ v' => KdJ c B top0 KO BK v') :=
  writerWP_mono (writerWP_and (putBook_descendLte s f x c base B top0 hB v hJ.1)
    (kd_descendLte KO BK s f x c v hv hk hJ.2.1 hJ.2.2 (Or.inl hx)))
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

theorem kdJ_pathAdd (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (s : Nat) (x L : NodeId) (n : KNode) (v : W) (hJ : KdJ c B top0 KO BK v) (hL : KdPathLast v L)
    (hlk : v.nodes.lookup L = some n) (hkm : Klong.key s x ∈ n.ks) :
    KdJ c B top0 KO BK { v with path := v.path ++ [(some s, x)] } := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hJ.2.1 hlk
  have hkd := kd_pathAdd KO BK s x c v hv hJ.2.1 hJ.2.2 a L g h ha hgh (kd_cache_node hJ.2.2 hlk hgh _ _ hkm)
  simp only [pathAdd, writerWP_modify] at hkd
  exact ⟨putBook_pathAdd (some s) x c base B top0 hB v hJ.1, hkd.1, hkd.2.1⟩

theorem kdJ_start (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (w : W) (hJ : KdJ c B top0 KO BK w) :
    KdJ c B top0 KO BK ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) := by
  have h1 := kd_pathClear KO BK c w hv hJ.2.1 hJ.2.2
  simp only [pathClear, writerWP_modify] at h1
  have h2 := kd_findRoot KO BK c { w with path := [] } hv h1.1 h1.2.1 rfl
  simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure] at h2
  exact ⟨putBook_pathAdd none w.top.rootKey c base B top0 hB _ (putBook_pathClear c base B top0 hB w hJ.1),
    h2.1, h2.2.1⟩

end SIS.Tree
