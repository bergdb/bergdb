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

end SIS.Tree
