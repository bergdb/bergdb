/-
The take-back's (B), (C) and their node facts through the new segments of a put
(bergdb 024-12, TP7, case (3); `J2N`). A new segment leaf is empty between its
making and the next step, so it does not start at t yet: `J2NE` is `J2N` but for
one empty leaf x, reached, which may be no node of the transaction's time.
Each step gives x a klong of t to the next new leaf (`j2NE_step`), the last
step a klong to the put's value (`j2N_last`); the first comes from the leaf of
the prefix with room (`j2NE_start`).
-/
import SIS.Tree.TakeDeadAssembly
import SIS.Tree.GetNewSegs

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `J2N` with one empty leaf x, reached, exempt from `MadeStartN`. -/
def J2NE (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId) (x : NodeId) : Prop :=
  TtReachedN N t r ∧ DeadLiveN N t B vals ∧ OldBelowN N t B ∧ OldStartN N t B ∧
    (∀ q qn, N q = some qn → B ≤ q → q ≠ x → qn.firstTime = some t) ∧ ValsNoNodeN N vals ∧
    N x = some ⟨true, []⟩ ∧ TReach N t r x ∧ B ≤ x

theorem single_facts (t : Time) (a : Nat) (y : NodeId) (hpos : 0 < t) (B : NodeId)
    (vals : List NodeId) :
    DeadLiveK ⟨true, [.time t, .key a y]⟩ t B vals ∧
    prefixAt [.time t, .key a y] (t - 1) = [] ∧ (⟨true, [.time t, .key a y]⟩ : KNode).firstTime = some t ∧
    (a, y) ∈ (⟨true, [.time t, .key a y]⟩ : KNode).liveAt t := by
  have hls : LastShaped t ⟨true, [.time t, .key a y]⟩ := ⟨[(a, y)], rfl, by simp⟩
  obtain ⟨hD, hp, hf⟩ := lastShaped_facts t _ hls hpos B vals
  refine ⟨hD, hp, hf, ?_⟩
  have := (mrg_newKlongs_liveAt_iff true t [(a, y)] (by simp) a y).mpr (by simp)
  exact this

/-- A step: the empty leaf x gets a klong of t to a new empty leaf x'. -/
theorem j2NE_step (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (x x' : NodeId) (a : Nat) (hpos : 0 < t) (hJ : J2NE N t r B vals x) (hx'N : N x' = none)
    (hx'B : B ≤ x') (hx'v : x' ∉ vals)
    (hN'x : N' x = some ⟨true, [.time t, .key a x']⟩) (hN'x' : N' x' = some ⟨true, []⟩)
    (hother : ∀ z, z ≠ x → z ≠ x' → N' z = N z) : J2NE N' t r B vals x' := by
  obtain ⟨hTt, hD, hO, hS, hM, hV, hNx, hxR, hxB⟩ := hJ
  obtain ⟨hDx, hpx, hfx, hlx⟩ := single_facts t a x' hpos B vals
  -- what N reaches N' reaches, but through x, which has no live klong in N
  have hxlive : ∀ c z, (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
    intro c z h
    exact absurd (KNode.liveAt_key_mem _ t c z h) (by simp)
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = x
      · rw [hax, hNx] at han; cases han; exact absurd hau (hxlive c u)
      · have hax' : a0 ≠ x' := fun he => by rw [he, hx'N] at han; cases han
        exact TReach.link ih ⟨an, by rw [hother a0 hax hax']; exact han, hau⟩
  have hxR' : TReach N' t r x := hreach x hxR
  have hx'R : TReach N' t r x' := TReach.link hxR' ⟨_, hN'x, hlx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hN'x', hx'R, hx'B⟩
  · intro u un hu hm
    by_cases hux : u = x
    · rw [hux]; exact hxR'
    · by_cases hux' : u = x'
      · rw [hux'] at hu ⊢; rw [hN'x'] at hu; cases hu; simp at hm
      · rw [hother u hux hux'] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hDx
    · by_cases hux' : u = x'
      · rw [hux', hN'x'] at hu; cases hu
        intro i cv y hi; simp at hi
      · rw [hother u hux hux'] at hu; exact hD u un hu
  · intro u un hu cv y hk
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; simp only at hk; rw [hpx] at hk; cases hk
    · by_cases hux' : u = x'
      · rw [hux', hN'x'] at hu; cases hu; simp [prefixAt] at hk
      · rw [hother u hux hux'] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux] at huB; omega
    · by_cases hux' : u = x'
      · rw [hux'] at huB; omega
      · rw [hother u hux hux'] at hu; exact hS u un hu huB
  · intro u un hu huB hux'
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hfx
    · rw [hother u hux hux'] at hu; exact hM u un hu huB hux
  · intro y hy
    by_cases hyx : y = x
    · rw [hyx] at hy; rw [hV x hy] at hNx; cases hNx
    · by_cases hyx' : y = x'
      · rw [hyx'] at hy; exact absurd hy hx'v
      · rw [hother y hyx hyx']; exact hV y hy

/-- The last step: the empty leaf x gets a klong of t to the put's value v. -/
theorem j2N_last (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (x v : NodeId) (a : Nat) (hpos : 0 < t) (hJ : J2NE N t r B vals x) (hvN : N' v = none)
    (hN'x : N' x = some ⟨true, [.time t, .key a v]⟩)
    (hother : ∀ z, z ≠ x → N' z = N z) : J2N N' t r B (vals ++ [v]) := by
  obtain ⟨hTt, hD, hO, hS, hM, hV, hNx, hxR, hxB⟩ := hJ
  obtain ⟨hDx, hpx, hfx, _⟩ := single_facts t a v hpos B (vals ++ [v])
  have hxlive : ∀ c z, (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
    intro c z h
    exact absurd (KNode.liveAt_key_mem _ t c z h) (by simp)
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = x
      · rw [hax, hNx] at han; cases han; exact absurd hau (hxlive c u)
      · exact TReach.link ih ⟨an, by rw [hother a0 hax]; exact han, hau⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u un hu hm
    by_cases hux : u = x
    · rw [hux]; exact hreach x hxR
    · rw [hother u hux] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hDx
    · rw [hother u hux] at hu
      intro i cv y hi hB hv
      exact hD u un hu i cv y hi hB (fun h => hv (List.mem_append_left _ h))
  · intro u un hu cv y hk
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; simp only at hk; rw [hpx] at hk; cases hk
    · rw [hother u hux] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux] at huB; omega
    · rw [hother u hux] at hu; exact hS u un hu huB
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hfx
    · rw [hother u hux] at hu; exact hM u un hu huB hux
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · by_cases hyx : y = x
      · rw [hyx] at h; rw [hV x h] at hNx; cases hNx
      · rw [hother y hyx]; exact hV y h
    · rw [List.mem_singleton.mp h]; exact hvN

/-- The first step: the leaf cur of the prefix, reached, with no live klong of
c0, gets a klong of t to a new empty leaf child. -/
theorem j2NE_start (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (cur child : NodeId) (cn : KNode) (c0 : Nat) (hpos : 0 < t) (hJ : J2N N t r B vals)
    (hcur : N cur = some cn) (hcR : TReach N t r cur) (hw : klongsWf cn.ks = true)
    (ht : ∀ s, Klong.time s ∈ cn.ks → s ≤ t) (hc0 : ∀ z, (c0, z) ∉ cn.liveAt t)
    (hchN : N child = none) (hchB : B ≤ child) (hchv : child ∉ vals)
    (hN'c : N' cur = some (cn.add t (.key c0 child))) (hN'ch : N' child = some ⟨true, []⟩)
    (hother : ∀ z, z ≠ cur → z ≠ child → N' z = N z) : J2NE N' t r B vals child := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ
  have hcc : cur ≠ child := fun he => by rw [he, hchN] at hcur; cases hcur
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = cur
      · rw [hax, hcur] at han; cases han
        have hcne : c ≠ c0 := fun he => hc0 u (he ▸ hau)
        rw [hax] at ih
        exact TReach.link ih ⟨_, hN'c, KNode.add_liveAt_keep cn c0 child t hw ht c u hau hcne⟩
      · have hax' : a0 ≠ child := fun he => by rw [he, hchN] at han; cases han
        exact TReach.link ih ⟨an, by rw [hother a0 hax hax']; exact han, hau⟩
  have hcR' := hreach cur hcR
  have hchR : TReach N' t r child := TReach.link hcR' ⟨_, hN'c, KNode.add_liveAt_new cn c0 child t hw ht⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hN'ch, hchR, hchB⟩
  · intro u un hu hm
    by_cases huc : u = cur
    · rw [huc]; exact hcR'
    · by_cases huch : u = child
      · rw [huch] at hu; rw [hN'ch] at hu; cases hu; simp at hm
      · rw [hother u huc huch] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      exact deadLiveK_addKey cn t B vals c0 child hw ht (deadLiveK_of_N N t B vals hD cur cn hcur)
        (fun z hz => absurd hz (hc0 z))
    · by_cases huch : u = child
      · rw [huch, hN'ch] at hu; cases hu
        intro i cv y hi; simp at hi
      · rw [hother u huc huch] at hu; exact hD u un hu
  · intro u un hu cv y hk
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      rw [KNode.prefixAt_add cn t _ hpos] at hk; exact hO cur cn hcur cv y hk
    · by_cases huch : u = child
      · rw [huch, hN'ch] at hu; cases hu; simp [prefixAt] at hk
      · rw [hother u huc huch] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      obtain ⟨s, hs, hf⟩ := hS cur cn hcur (by rw [← huc]; exact huB)
      exact ⟨s, hs, KNode.firstTime_add_some cn t _ s hf⟩
    · by_cases huch : u = child
      · rw [huch] at huB; omega
      · rw [hother u huc huch] at hu; exact hS u un hu huB
  · intro u un hu huB huch
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      exact KNode.firstTime_add_some cn t _ t (hM cur cn hcur (by rw [← huc]; exact huB))
    · rw [hother u huc huch] at hu; exact hM u un hu huB
  · intro y hy
    by_cases hyc : y = cur
    · rw [hyc] at hy; rw [hV cur hy] at hcur; cases hcur
    · by_cases hych : y = child
      · rw [hych] at hy; exact absurd hy hchv
      · rw [hother y hyc hych]; exact hV y hy

/-! ## The new segments at the writer's level -/

/-- `writerWP_putSegs_new` with the take-back's (B), (C) and node facts: from an
empty new leaf x with `J2NE`, the new segment leaves, the last with the put's
klong, give `TakeJ2`. -/
theorem writerWP_putSegs_new_j2 (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i) (B : NodeId) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      B ≤ ws.next →
      J2NE (wNode c.p base ws) c.i ws.top.rootKey B (ws.vals.map (·.1)) x →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf => TakeJ2 c base B wf) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr hBn hJ
    have hv := hfr ws.next (Nat.le_refl _)
    have hnv : ws.next ∉ ws.vals.map (·.1) := by
      intro hm
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      have : ws.vals.lookup ws.next ≠ none := by
        rw [← hqe]
        intro hl
        rw [List.lookup_eq_none_iff] at hl
        have := hl q hq
        simp at this
      exact this hv.2.2.2.2
    have hwv : wNode c.p base ws ws.next = none := by
      simp only [wNode, hv.2.1, Bool.false_eq_true, ↓reduceIte, hv.1, hv.2.2.1]
    cases tail' with
    | nil =>
      have hpost : ∀ wf : W, wf.nodes = upsert ws.nodes x ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) →
          wf.vals = ws.vals ++ [(ws.next, h)] → wf.taken = ws.taken → wf.top = ws.top →
          wf.next = ws.next + 2 → TakeJ2 c base B wf := by
        intro wf g1 g2 g3 g4 _
        unfold TakeJ2
        rw [g4, g2, List.map_append]
        refine j2N_last (wNode c.p base ws) (wNode c.p base wf) c.i ws.top.rootKey B _ x ws.next a hpos hJ
          ?_ ?_ ?_
        · simp only [wNode, g3, hv.2.1, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert,
            show ws.next ≠ x by omega, hv.1, hv.2.2.1]
        · simp only [wNode, g3, htx, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert]; rfl
        · intro z hz
          simp only [wNode, g3, g1, lookup_upsert, hz, ↓reduceIte]
      rw [putSegs.eq_2]
      refine writerWP_mono (post := fun _ wf => wf.nodes = upsert ws.nodes x
          ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) ∧ wf.vals = ws.vals ++ [(ws.next, h)] ∧
          wf.taken = ws.taken ∧ wf.top = ws.top ∧ wf.next = ws.next + 2) ?_
        (fun _ wf hw => hpost wf hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2)
      unfold setValue
      simp only [writerWP_bind, writerWP_read]
      rw [hf2]
      unfold descendLte
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c ws hx]
      simp only [↓reduceIte, writerWP_pure]
      unfold newValue fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
      rw [writerWP_getNode_known _ _ c _ (by simpa using hx)]
      have hcond : (decide ((⟨true, []⟩ : KNode).size + 1 < c.p.M) &&
          !deadOver c.p ((⟨true, []⟩ : KNode).add c.i (.key a ws.next))) = true := by
        simp only [KNode.size, List.length_nil, deadOver_empty_add]
        simp; omega
      simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      all_goals (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
    | cons a' tail'' =>
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf => TakeJ2 c base B wf) := by
        intro ws1 g1 g2 g3 g4 g5
        have hch : ws1.nodes.lookup ws.next = some ⟨true, []⟩ := by
          rw [g1, lookup_upsert]
          simp only [show ws.next ≠ x by omega, ↓reduceIte]
          exact lookup_append_single_self _ _ _ hv.1
        refine ih (by simp) ws1 ws.next hch (by rw [g3]; exact hv.2.1) (by omega) ?_ (by omega) ?_
        · intro z hz
          rw [g2] at hz
          have hz' := hfr z (by omega)
          refine ⟨?_, by rw [g3]; exact hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, by rw [g4]; exact hz'.2.2.2.2⟩
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          rw [lookup_append_single_ne _ _ _ _ (by omega)]; exact hz'.1
        · rw [g5, g4]
          refine j2NE_step (wNode c.p base ws) (wNode c.p base ws1) c.i ws.top.rootKey B _ x ws.next a hpos
            hJ hwv hBn hnv ?_ ?_ ?_
          · simp only [wNode, g3, htx, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert]; rfl
          · simp only [wNode, g3, hv.2.1, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert,
              show ws.next ≠ x by omega]
            rw [lookup_append_single_self _ _ _ hv.1]
          · intro z hzx hzn
            simp only [wNode, g3, g1, lookup_upsert, hzx, ↓reduceIte]
            rw [lookup_append_single_ne _ _ _ _ hzn]
      rw [putSegs.eq_3 _ _ x a (a' :: tail'') (by simp)]
      unfold setNode
      simp only [writerWP_bind, writerWP_read]
      rw [hf2]
      unfold descendLte
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c ws hx]
      simp only [↓reduceIte, writerWP_pure]
      rw [writerWP_getNode_known _ _ c ws hx]
      have hse : ((⟨true, []⟩ : KNode).searchEq c.i a) = none := rfl
      simp only [hse, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      refine writerWP_ghOf_cached x _ c ws hx _ (fun gh => ?_)
      have hroom : (⟨true, []⟩ : KNode).size + 1 < c.p.M := by simp [KNode.size]; omega
      simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        exact writerWP_mono (hstep _ rfl rfl rfl rfl rfl) (fun _ _ hh => hh)

/-- (3) below a leaf with room, with the take-back's (B), (C) and node facts:
`writerWP_put_newSegs`'s premises with `TakeJ2` before, the leaf reached, and B
at or below the next id. -/
theorem writerWP_put_newSegs_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 B : NodeId) (w : W)
    (hM : 2 ≤ c.p.M) (hpos : 0 < c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ n.searchEq c.i c0 = none ∧
      n.size + 1 < c.p.M)
    (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hLR : ∀ L, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      TReach (wNode c.p base w) c.i w.top.rootKey L) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' => TakeJ2 c base B w') := by
  obtain ⟨hidn, hidv, hidt, hidvals, _⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ c0 :: tail) (some h) (c0 :: tail) (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 tail htail]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht1)
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht1)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnwf, hnt, hnone, hroom⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
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
  have hLt : w.taken.contains L = false := ht (L, c0) (hvk _ hvisL)
  have hc0 : ∀ z, (c0, z) ∉ n.liveAt c.i := by
    intro z hz
    have hl := KNode.searchEq_live n c.i hnwf hnt c0
    rw [hnone] at hl
    rw [KNode.liveAt_of_times n c.i hnt] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup n) hz
    rw [← hl] at this
    cases this
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.vals = w3.vals → ws.top = w3.top →
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        TakeJ2 c base B w') := by
    intro ws h1 h2 h3 h4 h5
    rw [hnext3] at h1 h2
    rw [hnext3]
    have hw3n : w3.nodes.lookup w.next = none := by
      cases h' : w3.nodes.lookup w.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have hLne : L ≠ w.next := by omega
    have hlkc : ws.nodes.lookup w.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w.next ≠ L by omega, ↓reduceIte]
      exact lookup_append_single_self _ _ _ hw3n
    have htk : ∀ z, ws.taken.contains z = w.taken.contains z := by intro z; rw [h3, hr03.2.2.1]
    have hwnN : wNode c.p base w w.next = none := by
      have hl : w.nodes.lookup w.next = none := by
        cases h' : w.nodes.lookup w.next with
        | none => rfl
        | some _ => have := hidn _ (by rw [h']; rfl); omega
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, hl,
        (hbase w.next (Nat.le_refl _)).1]
    have hnv : w.next ∉ w.vals.map (·.1) := by
      intro hm
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      have := hidvals q hq
      rw [hqe] at this
      omega
    have hJE : J2NE (wNode c.p base ws) c.i ws.top.rootKey B (ws.vals.map (·.1)) w.next := by
      rw [h5, h4, hr03.2.1, hr03.2.2.2.1]
      refine j2NE_start (wNode c.p base w) (wNode c.p base ws) c.i w.top.rootKey B _ L w.next n c0 hpos
        hJ hn (hLR L hvisL) hnwf hnt hc0 hwnN hBn hnv ?_ ?_ ?_
      · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h1, lookup_upsert]
      · simp only [wNode, htk, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, hlkc]; rfl
      · intro z hzL hzn
        rw [← hr03.1]
        simp only [wNode, htk, hr03.2.2.1, h1, lookup_upsert, hzL, ↓reduceIte]
        rw [lookup_append_single_ne _ _ _ _ hzn]
    refine writerWP_putSegs_new_j2 c base (pre ++ c0 :: tail) h hM hfuel hpos B tail htail ws w.next hlkc
      (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) ?_ (by omega) hJE
    intro z hz
    rw [h2] at hz
    refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hbase z (by omega)).1,
      (hbase z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
    rw [h1, lookup_upsert]
    simp only [show z ≠ L by omega, ↓reduceIte]
    rw [lookup_append_single_ne _ _ _ _ (by omega)]
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl

end SIS.Tree
