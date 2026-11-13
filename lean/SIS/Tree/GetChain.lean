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

end SIS.Tree
