import SIS.Tree.GetNewSegs
import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put that makes several new segments keeps the walk's ranges (bergdb
024-12, TP10; `RangeOrder`): the leaf L of the key's last segment that is there
gets a klong to a new segment leaf, each new segment leaf a klong to the next
one or to the value; every new node is a leaf, which the whole range of a
segment takes (`rangeOrder_leafAddNewSet`, `writerWP_putSegs_new_shape`,
`rangeOrder_put_newSegs`). -/

/-- The walk's ranges after the leaf L gets a klong (cv, y) to a new node y, cv
in L's range: the new nodes (`New`: none before, the root not one, none linked
from a node reached) are leaves, and their live klongs name new nodes or no
node. -/
theorem rangeOrder_leafAddNewSet (N N' : NodeId → Option KNode) (t : Time) (r L y : NodeId)
    (n m : KNode) (cv : Nat) (New : NodeId → Prop) (hR : RangeOrder N t r) (hn : N L = some n)
    (hnl : n.leaf = true) (hN'L : N' L = some m) (hml : m.leaf = true)
    (hmlive : ∀ c z, (c, z) ∈ m.liveAt t → (c = cv ∧ z = y) ∨ (c, z) ∈ n.liveAt t)
    (hcv : ∀ lo hi, ReachR N t r L lo hi → lo ≤ cv ∧ UpperBound hi cv)
    (hy : New y)
    (hnew : ∀ z, New z → N z = none ∧ z ≠ r ∧ ∀ u c, TReach N t r u → ¬ TLink N t u c z)
    (hNl : ∀ z m', New z → N' z = some m' → m'.leaf = true)
    (hNk : ∀ z m' c z', New z → N' z = some m' → (c, z') ∈ m'.liveAt t → New z' ∨ N' z' = none)
    (hN' : ∀ z, z ≠ L → ¬ New z → N' z = N z) : RangeOrder N' t r := by
  have hLnew : ¬ New L := fun h => by rw [(hnew L h).1] at hn; cases hn
  have hold : ∀ z m', N' z = some m' → z ≠ L → ¬ New z → N z = some m' := by
    intro z m' h h1 h2; rw [← hN' z h1 h2]; exact h
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (¬ New z ∧ ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    (New z ∧ lo = 0 ∧ hi = none) ∨ N' z = none
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨fun h => (hnew r h).2.1 rfl, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m' c z' b _ hG hm hml' hb
    rcases hG with ⟨hzn, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzn, _, _⟩ | hG
    · have hzL : z ≠ L := by intro h; rw [h, hN'L] at hm; cases hm; rw [hml] at hml'; cases hml'
      have hm0 := hold z m' hm hzL hzn
      have hcz := childBounds_fst _ _ _ _ hb
      have hz'n : ¬ New z' := fun h =>
        (hnew z' h).2.2 z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, hcz⟩
      obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N t r hR z m' lo0 lo hi0 hi hz0 hm0 hml' hlo hhi
        _ (KNode.liveAt_order m' t) c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
      exact Or.inl ⟨hz'n, lo1, hi1, h3, h4, h5⟩
    · rw [hNl z m' hzn hm] at hml'; cases hml'
    · rw [hG] at hm; cases hm
  · intro z lo hi m' c z' _ hG hm hml' hcz
    rcases hG with ⟨hzn, lo0, hi0, hz0, _, _⟩ | ⟨hzn, _, _⟩ | hG
    · by_cases hzL : z = L
      · rw [hzL, hN'L] at hm; cases hm
        rw [hzL] at hz0
        rcases hmlive c z' hcz with ⟨_, h2⟩ | h2
        · rw [h2]; exact Or.inr (Or.inl ⟨hy, rfl, rfl⟩)
        · have hz'n : ¬ New z' := fun h =>
            (hnew z' h).2.2 L c (reachR_tReach N t r L lo0 hi0 hz0) ⟨n, hn, h2⟩
          exact Or.inl ⟨hz'n, 0, none, ReachR.seg L n lo0 hi0 c z' hz0 hn hnl h2, Nat.le_refl _,
            HiLE.refl _⟩
      · have hm0 := hold z m' hm hzL hzn
        have hz'n : ¬ New z' := fun h =>
          (hnew z' h).2.2 z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, hcz⟩
        exact Or.inl ⟨hz'n, 0, none, ReachR.seg z m' lo0 hi0 c z' hz0 hm0 hml' hcz, Nat.le_refl _,
          HiLE.refl _⟩
    · rcases hNk z m' c z' hzn hm hcz with h | h
      · exact Or.inr (Or.inl ⟨h, rfl, rfl⟩)
      · exact Or.inr (Or.inr h)
    · rw [hG] at hm; cases hm
  · intro z lo hi m' _ hG hm
    rcases hG with ⟨hzn, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzn, hlo, hhi⟩ | hG
    · by_cases hzL : z = L
      · rw [hzL, hN'L] at hm; cases hm
        rw [hzL] at hz0
        obtain ⟨hcl, hcu⟩ := hcv lo0 hi0 hz0
        intro q hq
        simp only [hml, ↓reduceIte]
        rcases hmlive q.1 q.2 hq with ⟨h1, _⟩ | h1
        · rw [h1]; exact ⟨by omega, upperBound_of_hiLE hi0 hi cv hhi hcu⟩
        · obtain ⟨h3, h4⟩ := hR L lo0 hi0 n hz0 hn q h1
          simp only [hnl, ↓reduceIte] at h3
          exact ⟨by omega, upperBound_of_hiLE hi0 hi q.1 hhi h4⟩
      · exact nodeRange_wider m' t lo0 lo hi0 hi (hR z lo0 hi0 m' hz0 (hold z m' hm hzL hzn)) hlo hhi
    · rw [hhi]
      intro q _
      simp only [hNl z m' hzn hm, ↓reduceIte]
      exact ⟨by omega, trivial⟩
    · rw [hG] at hm; cases hm

/-- The shape of `putSegs` of new segments from an empty leaf x (prover latest's
`writerWP_putSegs_new`): x and the nodes with ids from the next id on are leaves
whose live klongs name ids from the next id on; the nodes below the next id but
x are kept. -/
theorem writerWP_putSegs_new_shape (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
        wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
        (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
        (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
        ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
          m.leaf = true ∧ ∀ c' y, (c', y) ∈ m.liveAt c.i → ws.next ≤ y) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  have hone : ∀ (a : Nat) (y : NodeId) (c' : Nat) (z : NodeId),
      (c', z) ∈ ((⟨true, []⟩ : KNode).add c.i (.key a y)).liveAt c.i → z = y := by
    intro a y c' z hm
    have he : (⟨true, []⟩ : KNode).add c.i (.key a y) = ⟨true, newKlongs c.i [(a, y)]⟩ := rfl
    rw [he] at hm
    have := liveAt_newKlongs_mem true c.i c.i _ c' z hm
    simp only [List.mem_singleton, Prod.mk.injEq] at this
    exact this.2
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr
    cases tail' with
    | nil =>
      rw [putSegs.eq_2]
      refine writerWP_mono (post := fun _ wf => wf.nodes = upsert ws.nodes x
          ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) ∧ wf.vals = ws.vals ++ [(ws.next, h)] ∧
          wf.taken = ws.taken ∧ wf.top = ws.top ∧ wf.next = ws.next + 2) ?_ ?_
      · unfold setValue
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
      · intro _ wf ⟨g1, _, g3, g4, g5⟩
        refine ⟨g3, g4, by omega, ?_, ?_, ?_⟩
        · intro z _ hzx; rw [g1, lookup_upsert]; simp [hzx]
        · intro z hz
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          exact (hfr z (by omega)).1
        · intro z m hz hm
          rw [g1, lookup_upsert] at hm
          by_cases hzx : z = x
          · simp only [hzx, ↓reduceIte, Option.some.injEq] at hm
            subst hm
            refine ⟨by rw [KNode.add_leaf], fun c' y hy => ?_⟩
            rw [hone a ws.next c' y hy]; exact Nat.le_refl _
          · simp only [hzx, ↓reduceIte] at hm
            rcases hz with hz | hz
            · exact absurd hz hzx
            · rw [(hfr z hz).1] at hm; cases hm
    | cons a' tail'' =>
      have hv := hfr ws.next (Nat.le_refl _)
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf =>
            wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
            (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
            (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
            ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
              m.leaf = true ∧ ∀ c' y, (c', y) ∈ m.liveAt c.i → ws.next ≤ y) := by
        intro ws1 g1 g2 g3 g4 g5
        have hch : ws1.nodes.lookup ws.next = some ⟨true, []⟩ := by
          rw [g1, lookup_upsert]
          simp only [show ws.next ≠ x by omega, ↓reduceIte]
          exact lookup_append_single_self _ _ _ hv.1
        refine writerWP_mono (ih (by simp) ws1 ws.next hch (by rw [g3]; exact hv.2.1) (by omega) ?_) ?_
        · intro z hz
          rw [g2] at hz
          have hz' := hfr z (by omega)
          refine ⟨?_, by rw [g3]; exact hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, by rw [g4]; exact hz'.2.2.2.2⟩
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          rw [lookup_append_single_ne _ _ _ _ (by omega)]; exact hz'.1
        · rintro _ wf ⟨k1, k2, k3, k4, k6, k7⟩
          have hxf : wf.nodes.lookup x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
            rw [k4 x (by omega) (by omega), g1, lookup_upsert]; simp
          refine ⟨by rw [k1, g3], by rw [k2, g5], by omega, ?_, k6, ?_⟩
          · intro z hz hzx
            rw [k4 z (by omega) (by omega), g1, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact lookup_append_single_ne _ _ _ _ (by omega)
          · intro z m hz hm
            by_cases hzx : z = x
            · rw [hzx, hxf] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              refine ⟨by rw [KNode.add_leaf], fun c' y hy => ?_⟩
              rw [hone a ws.next c' y hy]; exact Nat.le_refl _
            · have hz2 : ws.next ≤ z := by rcases hz with hz | hz; exact absurd hz hzx; exact hz
              by_cases hz0 : z = ws.next
              · obtain ⟨h1, h2⟩ := k7 z m (Or.inl hz0) hm
                exact ⟨h1, fun c' y hy => by have := h2 c' y hy; omega⟩
              · by_cases hz1 : z < ws.next + 2
                · rw [k4 z (by omega) hz0, g1, lookup_upsert] at hm
                  simp only [hzx, ↓reduceIte] at hm
                  rw [lookup_append_single_ne _ _ _ _ hz0, (hfr z hz2).1] at hm
                  cases hm
                · obtain ⟨h1, h2⟩ := k7 z m (Or.inr (by omega)) hm
                  exact ⟨h1, fun c' y hy => by have := h2 c' y hy; omega⟩
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
        exact hstep _ rfl rfl rfl rfl rfl

set_option maxHeartbeats 800000 in
/-- A put of a key pre ++ c0 :: tail whose prefix pre is there and whose leaf
for c0 in the tree of pre has no klong of c0 and has room, with tail of one
segment or more (prover latest's `writerWP_put_newSegs`, its premises and the
tree), keeps the walk's ranges. -/
theorem rangeOrder_put_newSegs (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hM : 2 ≤ c.p.M)
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
      n.size + 1 < c.p.M ∧
      (∀ key', keyWf key' = true →
        (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
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
  obtain ⟨hnwf, hnt, hnone, hroom, huniq, hpre⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  -- ids
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
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.vals = w3.vals → ws.top = w3.top →
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
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
    refine writerWP_mono (writerWP_putSegs_new_shape c base (pre ++ c0 :: tail) h hM hfuel tail htail ws
      w.next hlkc (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) ?_) ?_
    · intro z hz
      rw [h2] at hz
      refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hbase z (by omega)).1,
        (hbase z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
      rw [h1, lookup_upsert]
      simp only [show z ≠ L by omega, ↓reduceIte]
      rw [lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    rintro _ wf ⟨k1, k2, k3, k4, k6, k7⟩
    have htkf : ∀ z, wf.taken.contains z = w.taken.contains z := by intro z; rw [k1, htk]
    have hLf : wf.nodes.lookup L = some (n.add c.i (.key c0 w.next)) := by
      rw [k4 L (by omega) hLne, h1, lookup_upsert]; simp
    have hnewshape : ∀ z m, w.next ≤ z → wf.nodes.lookup z = some m →
        m.leaf = true ∧ ∀ c' y, (c', y) ∈ m.liveAt c.i → w.next ≤ y := by
      intro z m hz hm
      by_cases hz0 : z = w.next
      · obtain ⟨h1', h2'⟩ := k7 z m (Or.inl hz0) hm
        exact ⟨h1', fun c' y hy => by have := h2' c' y hy; omega⟩
      · by_cases hz1 : z < w.next + 2
        · rw [k4 z (by omega) hz0, h1, lookup_upsert] at hm
          simp only [show z ≠ L by omega, ↓reduceIte] at hm
          rw [lookup_append_single_ne _ _ _ _ hz0] at hm
          cases h' : w3.nodes.lookup z with
          | none => rw [h'] at hm; cases hm
          | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
        · obtain ⟨h1', h2'⟩ := k7 z m (Or.inr (by omega)) hm
          exact ⟨h1', fun c' y hy => by have := h2' c' y hy; omega⟩
    have hwfz : ∀ z, w.next ≤ z → ∀ m, wNode c.p base wf z = some m → wf.nodes.lookup z = some m := by
      intro z hz m hm
      unfold wNode at hm
      rw [htkf, hntake z hz] at hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hm
      cases h' : wf.nodes.lookup z with
      | some m' => rw [h'] at hm; exact hm
      | none => rw [h'] at hm; simp only at hm; rw [(hbase z hz).1] at hm; cases hm
    rw [k2, h5, hr03.2.1]
    refine rangeOrder_leafAddNewSet (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey L w.next n
      (n.add c.i (.key c0 w.next)) c0 (fun z => w.next ≤ z) hR hn hnl
      (by simp only [wNode, htkf, hLt, Bool.false_eq_true, ↓reduceIte, hLf])
      (by rw [KNode.add_leaf]; exact hnl) ?_
      (leaf_range _ c.i _ hT hwfG c.p.fuel pre c0 rk0 L hrk hvisL) (Nat.le_refl _) ?_ ?_ ?_ ?_
    · intro c' z hz
      rcases KNode.add_key_liveAt_mem n c.i c0 w.next hnwf hnt c' z hz with h1' | ⟨_, h1'⟩
      · exact Or.inl h1'
      · exact Or.inr h1'
    · intro z hz
      refine ⟨?_, by omega, ?_⟩
      · simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, (hbase z hz).1]
        cases h' : w.nodes.lookup z with
        | none => rfl
        | some _ => have := hidn z (by rw [h']; rfl); omega
      · intro u c' hu hl
        obtain ⟨un, hun, hc⟩ := hl
        have := hlinks u un c' z (tReach_reachS _ _ _ _ hu) hun hc
        omega
    · intro z m' hz hm
      exact (hnewshape z m' hz (hwfz z hz m' hm)).1
    · intro z m' c' z' hz hm hc
      exact Or.inl ((hnewshape z m' hz (hwfz z hz m' hm)).2 c' z' hc)
    · intro z hzL hzb
      have hzb' : z < w.next := by simpa using hzb
      rw [← hr03.1]
      have hx := k4 z (by omega) (by omega)
      rw [h1, lookup_upsert] at hx
      simp only [hzL, ↓reduceIte] at hx
      rw [lookup_append_single_ne _ _ _ _ (by omega)] at hx
      simp only [wNode, htkf, hr03.2.2.1, hx]
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl

end SIS.Tree
