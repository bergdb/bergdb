import SIS.Tree.GetSegLeaf

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The access path that a descent builds, all of it (bergdb 024-12, TP10; for
the splits whose parent is full): each entry after the start names the node
that the node before it finds for the compare value (`PathFrom`). -/

/-- The entries a descent from x for cv adds to the access path: each names the
node that the node before it (x first) finds by `searchLte`, with that klong's
compare value. -/
inductive PathFrom (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    NodeId → List (Option Nat × NodeId) → Prop
  | nil (x : NodeId) : PathFrom N t cv x []
  | cons (x : NodeId) (n : KNode) (fd : Found) (rest : List (Option Nat × NodeId)) :
      N x = some n → n.leaf = false → n.searchLte t cv = some fd →
      PathFrom N t cv fd.y rest → PathFrom N t cv x ((some fd.c, fd.y) :: rest)

/-- The end of a descent's entries from x. -/
def pathEnd (x : NodeId) (steps : List (Option Nat × NodeId)) : NodeId :=
  (steps.getLast?.map (·.2)).getD x

theorem writerWP_descendLte_steps (cv : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W),
    (∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false) →
    WriterWP (descendLte cv f x) c w (fun L v => ∃ steps,
      PathFrom (wNode c.p base w) c.i cv x steps ∧ v.path = w.path ++ steps ∧
      L = pathEnd x steps) := by
  intro f
  induction f with
  | zero => intro x w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w ht
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c w base hvc)
      (writerWP_getNode_cache x c w)) ?_
    intro n v ⟨⟨hrv, hlk, hwn⟩, ⟨_, _, hvpath⟩⟩
    have hx := hwn (ht (x, cv) (by simp [eqVisits]))
    split
    · simp only [writerWP_pure]
      exact ⟨[], PathFrom.nil x, by rw [hvpath]; simp, rfl⟩
    · rename_i hleaf
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        simp only [pathAdd, writerWP_bind, writerWP_modify]
        have hr01 : ReadsAs c.p base w { v with path := v.path ++ [(some fd.c, fd.y)] } :=
          ReadsAs.trans _ _ _ _ _ hrv ⟨by funext y; rfl, rfl, rfl, rfl, rfl⟩
        have hvis : ∀ q ∈ eqVisits (wNode c.p base { v with path := v.path ++ [(some fd.c, fd.y)] })
            c.i cv f fd.y,
            ({ v with path := v.path ++ [(some fd.c, fd.y)] } : W).taken.contains q.1 = false := by
          intro q hq
          rw [hr01.1] at hq
          rw [hr01.2.2.1]
          apply ht q
          simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
          exact Or.inr hq
        refine writerWP_mono (ih fd.y _ hvis) ?_
        intro L v2 ⟨steps, hpf, hp2, hL⟩
        rw [hr01.1] at hpf
        refine ⟨(some fd.c, fd.y) :: steps, PathFrom.cons x n fd steps hx (by simpa using hleaf) hfd hpf,
          ?_, ?_⟩
        · rw [hp2, hvpath]; simp
        · rw [hL]
          unfold pathEnd
          cases steps with
          | nil => rfl
          | cons s ss => simp [List.getLast?_cons]

/-- The last two entries of a descent: the grandparent g (the start, or the
entry before them) finds q by kq, and q finds L by k1. -/
theorem PathFrom.last_two (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (s0 : List (Option Nat × NodeId)) (x : NodeId) (kq k1 : Option Nat) (q L : NodeId),
      PathFrom N t cv x (s0 ++ [(kq, q), (k1, L)]) →
      ∃ gn qn fdg fdq, N (pathEnd x s0) = some gn ∧ gn.leaf = false ∧
        gn.searchLte t cv = some fdg ∧ kq = some fdg.c ∧ fdg.y = q ∧
        N q = some qn ∧ qn.leaf = false ∧ qn.searchLte t cv = some fdq ∧ k1 = some fdq.c ∧
        fdq.y = L := by
  intro s0
  induction s0 with
  | nil =>
    intro x kq k1 q L h
    cases h with
    | cons _ gn fdg _ hg hgl hgs h2 =>
      cases h2 with
      | cons _ qn fdq _ hq hql hqs _ =>
        exact ⟨gn, qn, fdg, fdq, hg, hgl, hgs, rfl, rfl, hq, hql, hqs, rfl, rfl⟩
  | cons s ss ih =>
    intro x kq k1 q L h
    cases h with
    | cons _ n fd _ hn hnl hns h2 =>
      obtain ⟨gn, qn, fdg, fdq, h1, h2', h3, h4, h5, h6, h7, h8, h9, h10⟩ := ih fd.y kq k1 q L h2
      refine ⟨gn, qn, fdg, fdq, ?_, h2', h3, h4, h5, h6, h7, h8, h9, h10⟩
      unfold pathEnd at h1 ⊢
      cases ss with
      | nil => simpa using h1
      | cons s' ss' => simpa [List.getLast?_cons] using h1

/-- `renSim_timeSplit` with the new node holding a node of the same live
klongs. -/
theorem renSim_timeSplitGen (N M2 : NodeId → Option KNode) (t : Time) (r L q y : NodeId)
    (qn m m2 : KNode) (k1 : Nat)
    (hqL : q ≠ L) (hyL : y ≠ L) (hyq : y ≠ q)
    (hNL : N L = some m) (hNq : N q = some qn) (hql : qn.leaf = false)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hk1 : (k1, L) ∈ qn.live) (honly : ∀ c z, (c, z) ∈ qn.liveAt t → z = L → c = k1)
    (hM2y : M2 y = some m2) (hml2 : m2.leaf = m.leaf)
    (hmwf : klongsWf m.ks = true) (hm2wf : klongsWf m2.ks = true)
    (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ t) (hm2t : ∀ s, Klong.time s ∈ m2.ks → s ≤ t)
    (hlook : ∀ c, m2.live.lookup c = m.live.lookup c) (hM2q : M2 q = some (qn.add t (.key k1 y)))
    (hM2 : ∀ x, x ≠ L → x ≠ q → x ≠ y → M2 x = N x)
    (hwf : ∀ x xn, ReachS N t r x → N x = some xn → klongsWf xn.ks = true)
    (hnotL : ∀ x xn, ReachS N t r x → x ≠ q → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnoty : ∀ x xn, ReachS N t r x → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t → z ≠ y) :
    RenSim N M2 t (fun x => x ≠ y ∧ ReachS N t r x) L y := by
  -- the targets of a reachable node's searches, renamed
  have hclos : ∀ x xn, ReachS N t r x → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t →
      z ≠ y ∧ ReachS N t r z :=
    fun x xn hx hn c z hz => ⟨hnoty x xn hx hn c z hz, ReachS.step x xn c z hx hn hz⟩
  have hsame : ∀ x xn, ReachS N t r x → x ≠ q → N x = some xn → ∀ c,
      (xn.leaf = true → ((xn.searchEq t c).map (·.y)).map (fun z => if z = L then y else z) =
          (xn.searchEq t c).map (·.y) ∧
          ∀ fd, xn.searchEq t c = some fd → fd.y ≠ y ∧ ReachS N t r fd.y) ∧
      (xn.leaf = false → ((xn.searchLte t c).map (·.y)).map (fun z => if z = L then y else z) =
          (xn.searchLte t c).map (·.y) ∧
          ∀ fd, xn.searchLte t c = some fd → fd.y ≠ y ∧ ReachS N t r fd.y) := by
    intro x xn hx hxq hn c
    have hw := hwf x xn hx hn
    constructor
    · intro _
      refine ⟨?_, fun fd hfd => hclos x xn hx hn c fd.y (KNode.searchEq_mem xn t c fd hw hfd)⟩
      cases hfd : xn.searchEq t c with
      | none => rfl
      | some fd =>
        have := hnotL x xn hx hxq hn c fd.y (KNode.searchEq_mem xn t c fd hw hfd)
        simp [this]
    · intro _
      refine ⟨?_, fun fd hfd => hclos x xn hx hn fd.c fd.y (KNode.searchLte_mem xn t c fd hfd)⟩
      cases hfd : xn.searchLte t c with
      | none => rfl
      | some fd =>
        have := hnotL x xn hx hxq hn fd.c fd.y (KNode.searchLte_mem xn t c fd hfd)
        simp [this]
  intro x ⟨hxy, hx⟩
  by_cases hxL : x = L
  · subst hxL
    simp only [↓reduceIte]
    rw [hNL, hM2y]
    refine ⟨rfl, ?_⟩
    intro n1 n2 h1 h2
    cases h1; cases h2
    refine ⟨hml2.symm, fun c => ?_⟩
    have := hsame x m hx (fun h => hqL h.symm) hNL c
    have hEq : (m2.searchEq t c).map (·.y) = (m.searchEq t c).map (·.y) := by
      rw [KNode.searchEq_live m2 t hm2wf hm2t, KNode.searchEq_live m t hmwf hmt, hlook]
    have hLte : (m2.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y) :=
      KNode.searchLte_congr m2 m t hm2t hmt hlook c
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · rw [hEq]; exact this.1 hl
    · rw [hLte]; exact this.2 hl
  · simp only [hxL, ↓reduceIte]
    by_cases hxq : x = q
    · subst hxq
      rw [hNq, hM2q]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      have e1 : n1 = qn := (Option.some.inj h1).symm
      have e2 : n2 = qn.add t (.key k1 y) := (Option.some.inj h2).symm
      subst e1 e2
      have hleaf : (n1.add t (.key k1 y)).leaf = n1.leaf := KNode.add_leaf _ _ _
      refine ⟨hleaf.symm, fun c => ⟨fun hl => absurd (hql ▸ hl) (by simp), fun _ => ?_⟩⟩
      have hL1 := KNode.liveAt_of_times n1 t hqt
      have hadd := KNode.add_key_searchLte n1 t k1 y hqwf hqt ⟨L, hk1⟩ c
      refine ⟨?_, fun fd hfd => hclos x n1 hx hNq fd.c fd.y (KNode.searchLte_mem n1 t c fd hfd)⟩
      cases hfd : n1.searchLte t c with
      | none =>
        rw [hfd] at hadd
        cases h2 : (n1.add t (.key k1 y)).searchLte t c with
        | none => rfl
        | some f2 => rw [h2] at hadd; cases hadd
      | some fd =>
        rw [hfd] at hadd
        cases h2 : (n1.add t (.key k1 y)).searchLte t c with
        | none => rw [h2] at hadd; cases hadd
        | some f2 =>
          rw [h2] at hadd
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hadd
          simp only [Option.map_some, Option.some.injEq]
          rw [hadd.2]
          have hmem := KNode.searchLte_mem n1 t c fd hfd
          by_cases hc : fd.c = k1
          · have hy : fd.y = L := by
              rw [hL1] at hmem
              rw [hc] at hmem
              exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup n1) hmem).symm.trans
                (lookup_some_of_mem (KNode.live_keys_nodup n1) hk1))
            simp [hc, hy]
          · have hy : fd.y ≠ L := fun h => hc (honly fd.c fd.y hmem h)
            simp [hc, hy]
    · rw [hM2 x hxL hxq hxy]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      rw [h1] at h2
      cases h2
      refine ⟨rfl, fun c => ?_⟩
      have := hsame x n1 hx hxq h1 c
      exact ⟨fun hl => this.1 hl, fun hl => this.2 hl⟩

/-! ## The writer: a time split of a leaf whose inner parent is full, time split
too -/

/-- The state after a time split of the leaf L whose parent q, full, is time
split as well, below the grandparent g with room: L's last version with the put
at the next id, q's last version with the klong to it at the id after, g's
klong kq names that; L and q keep their klongs before the transaction. -/
def TimeSplit2After (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) : Prop :=
  ∃ l lq : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
    (∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') ∧
    lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = if k1 == q' then some w.next else qn.live.lookup q') ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2)))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else if x = w.next + 2 then some ⟨qn.leaf, lq.ks⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_timeSplit2 (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hqfull : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hLn : L < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [(cv, v)]
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSplit2After c w w' L q g n qn gn kq k1 cv v) := by
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
    have hfinal : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ (lq : KNode), lq.leaf = qn.leaf → klongsWf lq.ks = true →
        (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) →
        (∀ q', lq.live.lookup q' = if k1 == q' then some w.next else qn.live.lookup q') →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        (∀ x, w2.nodes.lookup x =
          if x = q then some (qn.toPrev (c.i - 1))
          else if x = g then some (gn.add c.i (.key kq (w.next + 2)))
          else if x = w.next + 2 then some ⟨qn.leaf, lq.ks⟩
          else (w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))]).lookup x) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => TimeSplit2After c w w' L q g n qn gn kq k1 cv v) := by
      intro l hl_leaf hl_wf hl_times hl_look lq hq_leaf hq_wf hq_times hq_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n]
        simp only [show L ≠ q from fun h => hqL h.symm, show L ≠ g from fun h => hgL h.symm,
          show L ≠ w.next + 2 by omega, ↓reduceIte, List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, lq, hl_leaf, hl_wf, hl_times, ?_, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top,
        h2v, ?_⟩
      · intro q'
        rw [hl_look q']
        simp [pairLookupStep]
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
              by_cases hx2 : x = w.next + 2
              · simp [hx2, show w.next + 2 ≠ w.next by omega]
              · simp only [hx2, ↓reduceIte]
                by_cases hxy : x = w.next
                · subst hxy; rw [hny]; simp [List.lookup]
                · simp only [hxy, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                    rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    have hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))] →
        w1.next = w.next + 2 → w1.path = w.path → w1.taken = w.taken → w1.top = w.top →
        w1.vals = w.vals →
        WriterWP (appendKlongs (d'' + 1) q [(k1, w.next)]) c w1 (fun _ w' =>
          WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w'
            (fun _ w'' => TimeSplit2After c w w'' L q g n qn gn kq k1 cv v)) := by
      intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1x h1p h1t h1top h1v
      refine writerWP_mono (writerWP_appendKlongs_timeSplit_gen d'' q g qn gn kq k1 w.next c w1
        (by rw [h1n, List.lookup_append, hlq]; rfl) (by rw [h1n, List.lookup_append, hlg]; rfl)
        hgq hgl hqfirst hqfull hqsplit (by rw [h1p]; exact hpg) (by rw [h1p]; exact hpq)
        hroomg hdeadg
        (by
          rw [h1n, h1x, List.lookup_append, hny2]
          show ([(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))].lookup (w.next + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)) ?_
      intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, h2n⟩
      refine hfinal l hl_leaf hl_wf hl_times hl_look lq hq_leaf hq_wf hq_times ?_ w2
        (by rw [h2t, h1t]) (by rw [h2top, h1top]) (by rw [h2v, h1v]) ?_
      · intro q'; rw [hq_look q']
      · intro x; rw [h2n x, h1x, h1n]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl

/-! ## The reading after the two time splits -/

/-- After a time split of the leaf L of a key's last segment and of its full
parent q (L's last version with the put at Y, q's last version with k1 to Y at
Yq, the grandparent g's klong kq to q names Yq), every key reads what it read
but the key, which reads the put's value. -/
theorem getFromR_timeSplit2 (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g Y Yq v : NodeId)
    (n qn gn ln lqn : KNode) (k1 kq : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live)
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ c, ln.live.lookup c = if cv == c then some v else n.live.lookup c)
    (hN2Yq : N2 Yq = some lqn) (hlql : lqn.leaf = qn.leaf) (hlqwf : klongsWf lqn.ks = true)
    (hlqt : ∀ s, Klong.time s ∈ lqn.ks → s ≤ i)
    (hlqlook : ∀ c, lqn.live.lookup c = if k1 == c then some Y else qn.live.lookup c)
    (hN2g : N2 g = some (gn.add i (.key kq Yq)))
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ Y → x ≠ Yq → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2L : V2 L = none)
    (hV2Y : V2 Y = none) (hV2q : V2 q = none) (hV2Yq : V2 Yq = none)
    (hqL : q ≠ L) (hYL : Y ≠ L) (hYq : Y ≠ q) (hgq : g ≠ q) (hgL : g ≠ L) (hgY : g ≠ Y)
    (hYqq : Yq ≠ q) (hYqg : Yq ≠ g) (hYqL : Yq ≠ L) (hYqY : Yq ≠ Y)
    (hvL : v ≠ L) (hvY : v ≠ Y) (hvq : v ≠ q) (hvg : v ≠ g) (hvYq : v ≠ Yq)
    (hNv : N v = none) (hNYq : N Yq = none) (hNY : N Y = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrootq : root ≠ q) (hrootYq : root ≠ Yq)
    (hrootv : root ≠ v)
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
      z ≠ v ∧ z ≠ Y ∧ z ≠ Yq) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
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
  have hA := getFromR_timeSplit_only N N1 V V2 i fuel hfuel root L q Y v n qn ln k1 pre cv h rk
    hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hlnl hlnwf hlnt hlnlook hN1Y hN1q hN1 hV2v hV2 hV2L hV2Y
    hqL hYL hYq hvL hvY hNv hrootL hrootY hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1⟩)
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
  have hlnmem : ∀ c z, (c, z) ∈ ln.liveAt i → (c, z) ∈ n.liveAt i ∨ z = v := by
    intro c z hz
    rw [KNode.liveAt_of_times ln i hlnt] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup ln) hz
    rw [hlnlook] at this
    by_cases hc : cv = c
    · subst hc; simp at this; exact Or.inr this.symm
    · have hc' : (cv == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      left; rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem this
  have hreachNe : ∀ x, ReachS N i root x → x ≠ Y ∧ x ≠ Yq ∧ x ≠ v := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootY, hrootYq, hrootv⟩
    | step x' xn c _ hx' hn hz =>
      have := hfr x' xn c _ hx' hn hz
      exact ⟨this.2.1, this.2.2, this.1⟩
  have hreach1 : ∀ x, ReachS N1 i root x → (ReachS N i root x ∧ x ≠ L) ∨ x = Y ∨ x = v := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hqadd c z hz with ⟨hz', hck⟩ | hzY
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzY)
        · rw [hN1 x' hx'L hxq (hreachNe x' hx').1] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · subst x'
        rw [hN1Y] at hn; cases hn
        rcases hlnmem c z hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr hzv)
      · subst x'
        have : N1 v = none := by
          rw [hN1 v hvL hvq hvY, hNv]
        rw [this] at hn; cases hn
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
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY | hxv
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
      rcases hlnmem c z hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvY, hNv] at hn; cases hn
  have hnotYq1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ Yq := by
    intro x xn hx hn c z hz hzY
    subst hzY
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY | hxv
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c z hz with ⟨hz', _⟩ | hzY
        · exact (hfr x qn c z hx' hNq hz').2.2 rfl
        · exact hYqY hzY
      · by_cases hxg : x = g
        · subst hxg
          rw [hN1g] at hn; cases hn
          exact (hfr x gn c z hx' hNg hz).2.2 rfl
        · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
          exact (hfr x xn c z hx' hn hz).2.2 rfl
    · subst hxY
      rw [hN1Y] at hn; cases hn
      rcases hlnmem c z hz with hz' | hzv
      · exact (hfr L n c z hrL hNL hz').2.2 rfl
      · exact hvYq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvY, hNv] at hn; cases hn
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
  have hren : ∀ key', getFromR N1 V2 i fuel key' root = getFromR N2 V2 i fuel key' root := by
    intro key'
    have := getFromR_ren N1 N2 V2 V2 i fuel _ q Yq hS (fun a => by
      by_cases ha : a = q
      · subst ha; simp [hV2q, hV2Yq]
      · simp [ha]) key' root ⟨hrootYq, ReachS.root⟩
    rw [this]
    simp [hrootq]
  intro key' hkey'
  rw [← hren key']
  exact hA key' hkey'

theorem writerWP_appendKlongs_timeSplit2 (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hqfull : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hLn : L < w.next) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => TimeSplit2After c w w' L q g n qn gn kq k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact hcs => writerWP_handleFullWith_timeSplit2 d'' L q g n qn gn kq k1 cv v
    compact c w hlk hlq hlg hqL hgq hgL hql hgl hfirst hqfirst hcs hqfull hqsplit hpg hpq hpk hroomg
    hdeadg hny hny2 hLn
  split
  · rename_i hsize
    apply hts false
    have h1 : c.p.M ≤ n.size + 1 := by simp at hsize; omega
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
    exact hsplit h1
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact hts true (by simp)

/-- Two descents' entries that both end at a leaf are the same. -/
theorem PathFrom.unique_leaf (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (s1 : List (Option Nat × NodeId)) (x : NodeId) (s2 : List (Option Nat × NodeId)),
      PathFrom N t cv x s1 → PathFrom N t cv x s2 →
      (∀ m, N (pathEnd x s1) = some m → m.leaf = true) → (∃ m, N (pathEnd x s1) = some m) →
      (∀ m, N (pathEnd x s2) = some m → m.leaf = true) → (∃ m, N (pathEnd x s2) = some m) →
      s1 = s2 := by
  intro s1
  induction s1 with
  | nil =>
    intro x s2 _ h2 hl1 he1 _ _
    cases h2 with
    | nil => rfl
    | cons _ n fd rest hn hnl _ _ =>
      obtain ⟨m, hm⟩ := he1
      have := hl1 m hm
      simp only [pathEnd, List.getLast?_nil, Option.map_none, Option.getD_none] at hm
      rw [hn] at hm; cases hm; rw [hnl] at this; cases this
  | cons st rest ih =>
    intro x s2 h1 h2 hl1 he1 hl2 he2
    cases h1 with
    | cons _ n fd _ hn hnl hs hrest =>
      cases h2 with
      | nil =>
        obtain ⟨m, hm⟩ := he2
        have := hl2 m hm
        simp only [pathEnd, List.getLast?_nil, Option.map_none, Option.getD_none] at hm
        rw [hn] at hm; cases hm; rw [hnl] at this; cases this
      | cons _ n' fd' rest' hn' _ hs' hrest' =>
        rw [hn] at hn'; cases hn'
        rw [hs] at hs'; cases hs'
        have hpe : ∀ (r : List (Option Nat × NodeId)), pathEnd x ((some fd.c, fd.y) :: r) = pathEnd fd.y r := by
          intro r
          unfold pathEnd
          cases r with
          | nil => rfl
          | cons a b => simp [List.getLast?_cons]
        rw [ih fd.y rest' hrest hrest' (by rw [← hpe]; exact hl1) (by rw [← hpe]; exact he1)
          (by rw [← hpe]; exact hl2) (by rw [← hpe]; exact he2)]

/-- The nodes of a descent's entries that end at a leaf are visited by it. -/
theorem PathFrom.mem_eqVisits (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x : NodeId) (steps : List (Option Nat × NodeId)),
      PathFrom N t cv x steps → (∀ m, N (pathEnd x steps) = some m → m.leaf = true) →
      (pathEnd x steps, cv) ∈ eqVisits N t cv f x →
      (x, cv) ∈ eqVisits N t cv f x ∧ ∀ e ∈ steps, (e.2, cv) ∈ eqVisits N t cv f x := by
  intro f
  induction f with
  | zero => intro x steps _ _ h; simp [eqVisits] at h
  | succ f ih =>
    intro x steps hp hl hv
    refine ⟨by simp [eqVisits], ?_⟩
    cases hp with
    | nil => intro e he; cases he
    | cons _ n fd rest hn hnl hs hrest =>
      have hpe : pathEnd x ((some fd.c, fd.y) :: rest) = pathEnd fd.y rest := by
        unfold pathEnd
        cases rest with
        | nil => rfl
        | cons a b => simp [List.getLast?_cons]
      rw [hpe] at hl hv
      have hne : pathEnd fd.y rest ≠ x := by
        intro he
        rw [he] at hl
        have := hl n hn
        rw [hnl] at this; cases this
      simp only [eqVisits, hn, hnl, Bool.false_eq_true, ↓reduceIte, hs, List.mem_cons,
        Prod.mk.injEq, and_true] at hv
      rcases hv with hv | hv
      · exact absurd hv hne
      obtain ⟨h1, h2⟩ := ih fd.y rest hrest hl hv
      intro e he
      simp only [eqVisits, hn, hnl, Bool.false_eq_true, ↓reduceIte, hs, List.mem_cons]
      rcases List.mem_cons.mp he with he | he
      · subst he; exact Or.inr h1
      · exact Or.inr (h2 e he)

theorem pathEnd_append (x : NodeId) (s0 : List (Option Nat × NodeId)) (e : Option Nat × NodeId) :
    pathEnd x (s0 ++ [e]) = e.2 := by
  simp [pathEnd]

/-! ## The rule: time splits of a leaf and of its full parent -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full, with at most h klongs in its last version or full by dead klongs
only, below the parent q, an inner node that existed before the transaction and
is full the same way with the klong to L's new node, below the grandparent g
with room: the two time splits change the reading by the put alone. The descent
from the segment root rk ends with g, q, L (`PathFrom`). -/
theorem writerWP_put_timeSplit2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hkey : keyWf (pre ++ [cv]) = true)
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
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false) ∧
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
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hLval, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hqval, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  -- the path's last two steps
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
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
  -- the descent is the path g, q, L
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
  -- q and g are visited
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
  -- ids in the writer's nodes are below the next id
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  -- the access path: ..., g, q, L
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
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hny : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hny2 : w3.nodes.lookup (w3.next + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_timeSplit2 d'' L q g n qn gn kq k1 cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq3) (by simpa using hlg3) hqL hgq hgL hql hgl hfirst
    hqfirst (by rw [hnext3]; exact hfull) hsplit (by simp only; rw [hnext3]; exact hqfull) hqsplit
    (by simpa using hpg) (by simpa using hpq) (by simpa using hpk) hroomg hdeadg
    (by simpa using hny) (by simpa using hny2) (by simp only; omega)) ?_
  intro _ wf hTS
  obtain ⟨l, lq, hl_leaf, hl_wf, hl_times, hl_look, hq_leaf, hq_wf, hq_times, hq_look,
    hft, hftop, hfv, hfn⟩ := hTS
  simp only at hft hftop hfv hfn hq_look
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn hl_look hq_look
  -- facts on ids
  have hqlt : q < w.next := hsrcw3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrcw3 g (by rw [hlg3]; rfl)
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
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : wf.taken.contains L = false := by
    rw [hft]; exact ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqtk : wf.taken.contains q = false := by
    rw [hft]; exact ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgtk : wf.taken.contains g = false := by
    rw [hft]; exact ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hlm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
    cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
  have hlqm : ({ leaf := qn.leaf, ks := lq.ks } : KNode) = lq := by
    cases lq; simp only at hq_leaf ⊢; rw [hq_leaf]
  have hres := getFromR_timeSplit2 (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q g (w.next + 2) (w.next + 2 + 2) w.next
    n qn gn ⟨n.leaf, l.ks⟩ ⟨qn.leaf, lq.ks⟩ k1 kq pre cv h rk hwfG hNL hnl htimes hNq hql hqt hk1L
    hNg hgl hgt hkqg
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega, show w.next + 2 ≠ g by omega])
    hnl (by rw [hlm]; exact hl_wf) (by rw [hlm]; exact hl_times)
    (by intro c'; rw [hlm, hl_look c'])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega])
    rfl (by rw [hlqm]; exact hq_wf) (by rw [hlqm]; exact hq_times)
    (by intro c'; rw [hlqm, hq_look c'])
    (by simp only [wNode, hgtk, Bool.false_eq_true, ↓reduceIte, hfn, hgL, hgq])
    (by
      intro m hm
      simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hfn, Option.some.injEq] at hm
      rw [← hm]; exact KNode.toPrev_wf n _ (hwfG L n hNL))
    (by
      intro x hxL hxq hxg hxY hxYq
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxg, hxY, hxYq, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    (by
      rw [← hLval]
      have hl' : (w.vals ++ [(w.next, h)]).lookup L = w.vals.lookup L :=
        lookup_append_single_ne _ _ _ _ (by omega)
      simp only [wValue, hft, hfv, hl'])
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 ≠ w.next),
        hvalnone _ (by omega : w.next ≤ w.next + 2), (hbase (w.next + 2) (by omega)).2])
    (by
      rw [← hqval]
      have hl' : (w.vals ++ [(w.next, h)]).lookup q = w.vals.lookup q :=
        lookup_append_single_ne _ _ _ _ (by omega)
      simp only [wValue, hft, hfv, hl'])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 + 2 ≠ w.next),
        hvalnone _ (by omega : w.next ≤ w.next + 2 + 2), (hbase (w.next + 2 + 2) (by omega)).2])
    hqL (by omega) (by omega) hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
    hLroot.symm (by omega) hqroot.symm (by omega) (by omega)
    hrq hrg hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
    (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
      (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
    (fun x xn cc z hx hxn hz => by
      have := hlinks x xn cc z hx hxn hz
      exact ⟨by omega, by omega, by omega⟩)
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

/-! ## The writer: a time split with any klongs to put -/

/-- `TimeSplitAfter` for any klongs to put. -/
def TimeSplitAfterIns (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) : Prop :=
  ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
    (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.add c.i (.key k1 w.next))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_timeSplitIns (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L ins
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSplitAfterIns c w w' L q n qn k1 ins) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
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
    have hfinal : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := l.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => TimeSplitAfterIns c w w' L q n qn k1 ins) := by
      intro l hl_leaf hl_wf hl_times hl_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert]
        simp only [show L ≠ q from fun h => hqL h.symm, ↓reduceIte, List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, ?_, h2t, h2top, h2v, ?_⟩
      · intro q'
        rw [hl_look q']
      · intro x
        simp only
        rw [lookup_upsert, h2n, lookup_upsert]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl

theorem writerWP_appendKlongs_timeSplitIns (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + ins.length + 1 ≤ c.p.M ∧
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = false))
    (hsplit : c.p.M < n.size + ins.length + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (appendKlongs (d' + 1) L ins) c w
      (fun _ w' => TimeSplitAfterIns c w w' L q n qn k1 ins) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact hcs => writerWP_handleFullWith_timeSplitIns d' L q n qn k1 ins compact c w
    hlk hlq hqL hql hfirst hcs hpq hpk hroomq hdeadq hny
  split
  · rename_i hsize
    apply hts false
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
    exact hsplit (by simpa using hsize)
  · rename_i hsize
    have hle : n.size + ins.length + 1 ≤ c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = true := by
      cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) with
      | true => rfl
      | false => exact absurd ⟨hle, h⟩ hfull
    simp only [hd, ↓reduceIte]
    exact hts true (by simp)

/-! ## The writer: a space split of a leaf whose inner parent is full and time split -/

/-- The state after a space split of the leaf L whose parent q, full, is time
split, below the grandparent g with room: the halves at the next two ids, q's
last version with the klongs to them at the id after, g's klong kq names that;
L and q keep their klongs before the transaction. -/
def SpaceSplitTimeAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) : Prop :=
  ∃ lq : KNode, lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = [(k1, w.next),
      ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)].foldl
      (pairLookupStep q') (qn.live.lookup q')) ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2 + 2)))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else if x = w.next + 2 + 2 then some ⟨qn.leaf, lq.ks⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_spaceSplitTime (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none)
    (hn3 : w.nodes.lookup (w.next + 2 + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitTimeAfter c w w' L q g n qn gn kq k1 cv v) := by
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
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
        [(k1, w.next), ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)] c _
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

/-! ## The reading after a leaf's space split and its parent's time split -/

theorem pairLookupFold_some_mem (c : Nat) :
    ∀ (l : List (Nat × NodeId)) (acc : Option NodeId) (z : NodeId),
      l.foldl (pairLookupStep c) acc = some z → (c, z) ∈ l ∨ acc = some z := by
  intro l
  induction l with
  | nil => intro acc z h; exact Or.inr h
  | cons a rest ih =>
    intro acc z h
    rw [List.foldl_cons] at h
    rcases ih _ z h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · unfold pairLookupStep at h1
      split at h1
      · rename_i ha
        simp only [Option.some.injEq] at h1
        subst h1
        left
        have : a.1 = c := by simpa using ha
        rw [← this]; exact List.mem_cons_self
      · exact Or.inr h1

theorem newKlongs_live_mem (leaf : Bool) (t : Time) (l : List (Nat × NodeId)) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ (⟨leaf, newKlongs t l⟩ : KNode).live) : (c, z) ∈ l := by
  have hl := lookup_some_of_mem (KNode.live_keys_nodup _) h
  rw [KNode.newKlongs_live_lookup_fold] at hl
  rcases pairLookupFold_some_mem c l none z hl with h1 | h1
  · exact h1
  · cases h1

/-- A leaf's live klongs after its space split: the leaf's or the put's. -/
theorem halves_leaf_live_mem (t : Time) (n : KNode) (cv : Nat) (v : NodeId) (hnl : n.leaf = true)
    (hlv0 : n.live ≠ []) (c : Nat) (z : NodeId) :
    ((c, z) ∈ (halves n.leaf t (n.lastVersion t) [(cv, v)]).1.liveAt t ∨
      (c, z) ∈ (halves n.leaf t (n.lastVersion t) [(cv, v)]).2.1.liveAt t) →
    (c, z) ∈ n.live ∨ z = v := by
  intro h
  have hlv := KNode.lastVersion_eq_newKlongs n t
  rw [hnl] at hlv
  rw [hnl, hlv] at h
  have hlive : ∀ l : List (Nat × NodeId), (∀ q ∈ l, q ∈ n.live ∨ q.2 = v) →
      (c, z) ∈ (⟨true, newKlongs t l⟩ : KNode).liveAt t → (c, z) ∈ n.live ∨ z = v := by
    intro l hl hz
    rw [KNode.liveAt_of_times _ t (newKlongs_times t l)] at hz
    exact hl (c, z) (newKlongs_live_mem true t l c z hz)
  cases hd : n.live.drop (n.live.length / 2) with
  | nil =>
    have : n.live.length ≤ n.live.length / 2 := List.drop_eq_nil_iff.mp hd
    have : n.live.length = 0 := by omega
    exact absurd (List.eq_nil_of_length_eq_zero this) hlv0
  | cons r rest =>
    have hr : (n.live.drop (n.live.length / 2)).head? = some r := by rw [hd]; rfl
    rw [halves_leaf_shape t n.live [(cv, v)] r hr] at h
    simp only [List.head?_cons] at h
    have hsub : ∀ q ∈ n.live.take (n.live.length / 2), q ∈ n.live := fun q hq => List.mem_of_mem_take hq
    have hsub2 : ∀ q ∈ n.live.drop (n.live.length / 2), q ∈ n.live := fun q hq => List.mem_of_mem_drop hq
    by_cases hc : r.1 ≤ cv
    · simp only [hc, decide_true, ↓reduceIte] at h
      rcases h with h | h
      · exact hlive _ (fun q hq => Or.inl (hsub q hq)) h
      · exact hlive _ (fun q hq => by
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (hsub2 q hq)
          · simp at hq; exact Or.inr (by rw [hq]))
          h
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at h
      rcases h with h | h
      · exact hlive _ (fun q hq => by
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (hsub q hq)
          · simp at hq; exact Or.inr (by rw [hq]))
          h
      · exact hlive _ (fun q hq => Or.inl (hsub2 q hq)) h

/-- After a space split of the leaf L of a key's last segment (halves at F and
S) and a time split of its full parent q (q's last version with the klongs k1
to F and sc to S at Yq, the grandparent g's klong kq names Yq), every key reads
what it read but the key, which reads the put's value. -/
theorem getFromR_spaceSplitTime (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g F S Yq v : NodeId)
    (n qn gn lqn : KNode) (k1 kq : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hlive : n.live ≠ [])
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live)
    (hN2F : N2 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2Yq : N2 Yq = some lqn) (hlql : lqn.leaf = qn.leaf) (hlqwf : klongsWf lqn.ks = true)
    (hlqt : ∀ s, Klong.time s ∈ lqn.ks → s ≤ i)
    (hlqlook : ∀ c, lqn.live.lookup c = [(k1, F),
      ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)].foldl (pairLookupStep c)
      (qn.live.lookup c))
    (hN2g : N2 g = some (gn.add i (.key kq Yq)))
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ Yq → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hV2q : V2 q = none) (hV2Yq : V2 Yq = none)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hgF : g ≠ F) (hgS : g ≠ S)
    (hFL : F ≠ L) (hSL : S ≠ L) (hFq : F ≠ q) (hSq : S ≠ q) (hFS : F ≠ S)
    (hYqq : Yq ≠ q) (hYqg : Yq ≠ g) (hYqL : Yq ≠ L) (hYqF : Yq ≠ F) (hYqS : Yq ≠ S)
    (hvL : v ≠ L) (hvq : v ≠ q) (hvg : v ≠ g) (hvF : v ≠ F) (hvS : v ≠ S) (hvYq : v ≠ Yq)
    (hNv : N v = none) (hNYq : N Yq = none) (hNF : N F = none) (hNS : N S = none)
    (hrootL : root ≠ L) (hrootF : root ≠ F) (hrootS : root ≠ S) (hrootq : root ≠ q)
    (hrootYq : root ≠ Yq) (hrootv : root ≠ v)
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
      z ≠ v ∧ z ≠ F ∧ z ≠ S ∧ z ≠ Yq) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let sc := (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2
  let q2 : KNode := (qn.add i (.key k1 F)).add i (.key sc S)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q2 else if x = g then some gn
    else if x = Yq then none else N2 x
  have hN1q : N1 q = some q2 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1F : N1 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1 := by
    simp [N1, hFq, hgF.symm, hYqF.symm, hN2F]
  have hN1S : N1 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1 := by
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
  have hA := getFromR_spaceSplit N N1 V V2 i fuel hfuel root L q F S v n qn k1 pre cv h rk
    hNL hnl hnwf hnt hlive hNq hql hqwf hqt hk1 hrange hN1q hN1F hN1S hN1 hV2v hV2
    hqL hvL hvF hvS hNv hrootL hrootF hrootS hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1,
      (hfr x xn c z hx hn hz).2.2.1⟩)
  -- the nodes N1 reaches: N's but L, and F, S and v
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
      (c, z) ∈ n.liveAt i ∨ z = v := by
    intro x xn c z hx hn hz
    rw [KNode.liveAt_of_times n i hnt]
    rcases hx with hx | hx
    · subst hx; rw [hN1F] at hn; cases hn
      exact halves_leaf_live_mem i n cv v hnl hlive c z (Or.inl hz)
    · subst hx; rw [hN1S] at hn; cases hn
      exact halves_leaf_live_mem i n cv v hnl hlive c z (Or.inr hz)
  have hreachNe : ∀ x, ReachS N i root x → x ≠ F ∧ x ≠ S ∧ x ≠ Yq ∧ x ≠ v := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootF, hrootS, hrootYq, hrootv⟩
    | step x' xn c _ hx' hn hz =>
      have := hfr x' xn c _ hx' hn hz
      exact ⟨this.2.1, this.2.2.1, this.2.2.2, this.1⟩
  have hreach1 : ∀ x, ReachS N1 i root x →
      (ReachS N i root x ∧ x ≠ L) ∨ x = F ∨ x = S ∨ x = v := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hq2mem c z hz with ⟨hz', hck⟩ | hzF | hzS
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzF)
          · exact Or.inr (Or.inr (Or.inl hzS))
        · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x' hx'
          rw [hN1 x' hx'L hxq hxF hxS] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · rcases hhalf x' xn c z (Or.inl hx') hn hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr (Or.inr hzv))
      · rcases hhalf x' xn c z (Or.inr hx') hn hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr (Or.inr hzv))
      · subst x'
        have : N1 v = none := by rw [hN1 v hvL hvq hvF hvS, hNv]
        rw [this] at hn; cases hn
  -- step B: q renamed Yq at g
  have hwfh := halves_newKlongs_wf true i n.live [(cv, v)]
  have hlvq := KNode.lastVersion_eq_newKlongs n i
  rw [hnl] at hlvq
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn _ hn
    by_cases hxq : x = q
    · subst hxq; rw [hN1q] at hn; cases hn; exact hq2wf
    · by_cases hxg : x = g
      · subst hxg; rw [hN1g] at hn; cases hn; exact hgwf
      · by_cases hxYq : x = Yq
        · subst hxYq; rw [hN1Yq] at hn; cases hn
        · by_cases hxF : x = F
          · subst hxF; rw [hN1F] at hn; cases hn; rw [hnl, hlvq]; exact hwfh.1
          · by_cases hxS : x = S
            · subst hxS; rw [hN1S] at hn; cases hn; rw [hnl, hlvq]; exact hwfh.2
            · have hn2 : N2 x = some xn := by
                simp only [N1, hxq, hxg, hxYq, ↓reduceIte] at hn; exact hn
              by_cases hxL : x = L
              · subst hxL; exact hN2L xn hn2
              · rw [hN2 x hxL hxq hxg hxF hxS hxYq] at hn2; exact hwfG x xn hn2
  have hnotq1 : ∀ x xn, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn hx hxg hn c z hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS | hxv
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
    · rcases hhalf x xn c z (Or.inl hxF) hn hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · rcases hhalf x xn c z (Or.inr hxS) hn hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvF hvS, hNv] at hn; cases hn
  have hnotYq1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ Yq := by
    intro x xn hx hn c z hz hzY
    subst hzY
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS | hxv
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c z hz with ⟨hz', _⟩ | hzF | hzS
        · exact (hfr x qn c z hx' hNq hz').2.2.2 rfl
        · exact hYqF hzF
        · exact hYqS hzS
      · by_cases hxg : x = g
        · subst hxg
          rw [hN1g] at hn; cases hn
          exact (hfr x gn c z hx' hNg hz).2.2.2 rfl
        · obtain ⟨hxF, hxS, _, _⟩ := hreachNe x hx'
          rw [hN1 x hxL hxq hxF hxS] at hn
          exact (hfr x xn c z hx' hn hz).2.2.2 rfl
    · rcases hhalf x xn c z (Or.inl hxF) hn hz with hz' | hzv
      · exact (hfr L n c z hrL hNL hz').2.2.2 rfl
      · exact hvYq hzv.symm
    · rcases hhalf x xn c z (Or.inr hxS) hn hz with hz' | hzv
      · exact (hfr L n c z hrL hNL hz').2.2.2 rfl
      · exact hvYq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvF hvS, hNv] at hn; cases hn
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
  have hren : ∀ key', getFromR N1 V2 i fuel key' root = getFromR N2 V2 i fuel key' root := by
    intro key'
    have := getFromR_ren N1 N2 V2 V2 i fuel _ q Yq hS (fun a => by
      by_cases ha : a = q
      · subst ha; simp [hV2q, hV2Yq]
      · simp [ha]) key' root ⟨hrootYq, ReachS.root⟩
    rw [this]
    simp [hrootq]
  intro key' hkey'
  rw [← hren key']
  exact hA key' hkey'

theorem writerWP_appendKlongs_spaceSplitTime (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny3 : w.nodes.lookup (w.next + 2 + 2) = none) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitTimeAfter c w w' L q g n qn gn kq k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplitTime d'' L q g n qn gn kq k1 cv v c w hlk hlq hlg hqL hgq
    hgL hql hgl hfirst hqfirst hsplit hqfull hqsplit hpg hpq hpk hroomg hdeadg hny hny2 hny3

/-! ## The rule: a space split of a leaf and a time split of its full parent -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full by its size, with more than h klongs in its last version, below the
parent q, an inner node that existed before the transaction and is full with the
two klongs to L's halves, with at most h klongs in its last version, below the
grandparent g with room: the space split of L and the time split of q change
the reading by the put alone. -/
theorem writerWP_put_spaceSplitTime (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hkey : keyWf (pre ++ [cv]) = true)
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
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [] ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧
      ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 (w.next + 2))).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 (w.next + 2 + 2))) = false) ∧
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
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive, hLval, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hqval, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  -- the path's last two steps
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
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
  -- the descent is the path g, q, L
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
  -- q and g are visited
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
    have : ¬ n.size + 1 < c.p.M := by omega
    simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  -- ids in the writer's nodes are below the next id
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  -- the access path: ..., g, q, L
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
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hny : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hny2 : w3.nodes.lookup (w3.next + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hny3 : w3.nodes.lookup (w3.next + 2 + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitTime d'' L q g n qn gn kq k1 cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq3) (by simpa using hlg3) hqL hgq hgL hql hgl hfirst
    hqfirst hfull hsplit (by simp only; rw [hnext3]; exact hqfull) (by simpa using hqsplit)
    (by simpa using hpg) (by simpa using hpq) (by simpa using hpk) hroomg hdeadg
    (by simpa using hny) (by simpa using hny2) (by simpa using hny3)) ?_
  intro _ wf hTS
  obtain ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, hft, hftop, hfv, hfn⟩ := hTS
  simp only at hft hftop hfv hfn hq_look
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn hq_look
  -- facts on ids
  have hqlt : q < w.next := hsrcw3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrcw3 g (by rw [hlg3]; rfl)
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
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : wf.taken.contains L = false := by
    rw [hft]; exact ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqtk : wf.taken.contains q = false := by
    rw [hft]; exact ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgtk : wf.taken.contains g = false := by
    rw [hft]; exact ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hlqm : ({ leaf := qn.leaf, ks := lq.ks } : KNode) = lq := by
    cases lq; simp only at hq_leaf ⊢; rw [hq_leaf]
  have hres := getFromR_spaceSplitTime (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q g (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) w.next n qn gn ⟨qn.leaf, lq.ks⟩ k1 kq pre cv h rk hwfG hNL hnl htimes
    hlive hNq hql hqt hk1L hrange hNg hgl hgt hkqg
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega, show w.next + 2 ≠ g by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 + 2 ≠ L by omega, show w.next + 2 + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 + 2 ≠ g by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
        show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega])
    rfl (by rw [hlqm]; exact hq_wf) (by rw [hlqm]; exact hq_times)
    (by intro c'; rw [hlqm, hq_look c'])
    (by simp only [wNode, hgtk, Bool.false_eq_true, ↓reduceIte, hfn, hgL, hgq])
    (by
      intro m hm
      simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hfn, Option.some.injEq] at hm
      rw [← hm]; exact KNode.toPrev_wf n _ (hwfG L n hNL))
    (by
      intro x hxL hxq hxg hxF hxS hxYq
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxg, hxF, hxS, hxYq, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    (by
      rw [← hqval]
      have hl' : (w.vals ++ [(w.next, h)]).lookup q = w.vals.lookup q :=
        lookup_append_single_ne _ _ _ _ (by omega)
      simp only [wValue, hft, hfv, hl'])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 + 2 + 2 ≠ w.next),
        hvalnone _ (by omega : w.next ≤ w.next + 2 + 2 + 2),
        (hbase (w.next + 2 + 2 + 2) (by omega)).2])
    hqL hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
    hLroot.symm (by omega) (by omega) hqroot.symm (by omega) (by omega)
    hrq hrg hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
    (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
      (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
    (fun x xn cc z hx hxn hz => by
      have := hlinks x xn cc z hx hxn hz
      exact ⟨by omega, by omega, by omega, by omega⟩)
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
