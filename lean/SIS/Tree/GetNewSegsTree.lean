import SIS.Tree.GetNewSegs
import SIS.Tree.WriterTreeNewSeg
import SIS.Tree.GetPutPath
import SIS.Tree.RangeNewSegs
import SIS.Tree.ChainShape
import SIS.Tree.TakeCachedKeep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The writer's tree after new segment leaves (bergdb 024-12, TP10; the tree
of the operation case (3), `GetOpCases.lean`): the new segment leaves that
`putSegs` makes below an empty segment leaf x keep the writer's tree, and every
node reached after is reached before or new (`writerWP_putSegs_new_treeR` for a
reached x, `writerWP_putSegs_new_tree` for any x). -/

theorem KNode.empty_liveAt' (t : Time) (c : Nat) (z : NodeId) :
    (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
  intro hc
  rw [KNode.liveAt_of_times _ t (by simp)] at hc
  have := lookup_some_of_mem (KNode.live_keys_nodup _) hc
  rw [KNode.live_lookup] at this
  cases this

/-- The nodes reached after an empty leaf x gets a klong to a new empty leaf y:
those reached before, and y. -/
theorem tReach_newSegStep (N : NodeId → Option KNode) (t : Time) (r x y : NodeId) (a : Nat)
    (hy : N y = none) (hxy : x ≠ y) :
    ∀ z, TReach (updN (updN N y ⟨true, []⟩) x ((⟨true, []⟩ : KNode).add t (.key a y))) t r z →
      TReach N t r z ∨ z = y := by
  intro z hz
  induction hz with
  | root => exact Or.inl TReach.root
  | @link u c z _ hl ih =>
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hux : u = x
    · subst hux
      rw [updN_self] at hm
      cases hm
      rcases KNode.add_key_liveAt_mem _ t a y (by rfl) (by simp) c z hc with ⟨_, hzy⟩ | ⟨_, hc'⟩
      · exact Or.inr hzy
      · exact absurd hc' (KNode.empty_liveAt' t c z)
    · rw [updN_ne _ _ _ _ hux] at hm
      by_cases huy : u = y
      · subst huy
        rw [updN_self] at hm
        cases hm
        exact absurd hc (KNode.empty_liveAt' t c z)
      · rw [updN_ne _ _ _ _ huy] at hm
        rcases ih with h | h
        · exact Or.inl (TReach.link h ⟨m, hm, hc⟩)
        · exact absurd h huy

theorem wNode_newSeg_updN (p : Params) (base : View BVal) (ws ws1 : W) (x : NodeId) (m : KNode)
    (h1 : ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x m)
    (h2 : ws1.taken = ws.taken) (hfree : ws.nodes.lookup ws.next = none)
    (htk : ws.taken.contains ws.next = false) (htx : ws.taken.contains x = false) :
    wNode p base ws1 = updN (updN (wNode p base ws) ws.next ⟨true, []⟩) x m := by
  have ha := wNode_append_updN p base ws { ws with nodes := ws.nodes ++ [(ws.next, ⟨true, []⟩)] }
    ⟨true, []⟩ rfl rfl hfree htk
  rw [← ha]
  exact wNode_upsert_updN p base { ws with nodes := ws.nodes ++ [(ws.next, ⟨true, []⟩)] } ws1 x m h1
    h2 htx

/-- The new segment leaves below a reached empty segment leaf x keep the
writer's tree; every node reached after is reached before or new. -/
theorem writerWP_putSegs_new_treeR (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      TreeOK (wNode c.p base ws) c.i ws.top.rootKey →
      TReach (wNode c.p base ws) c.i ws.top.rootKey x →
      (∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z → z < ws.next) →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
        TreeOK (wNode c.p base wf) c.i wf.top.rootKey ∧ wf.taken = ws.taken ∧ wf.top = ws.top ∧
        ∀ z, TReach (wNode c.p base wf) c.i wf.top.rootKey z →
          TReach (wNode c.p base ws) c.i ws.top.rootKey z ∨ ws.next ≤ z) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr hT hxR hRlt
    have hwx : wNode c.p base ws x = some ⟨true, []⟩ := by
      simp only [wNode, htx, Bool.false_eq_true, ↓reduceIte, hx]
    have hwnext : wNode c.p base ws ws.next = none := by
      obtain ⟨a1, a2, a3, _, _⟩ := hfr ws.next (Nat.le_refl _)
      simp only [wNode, a2, Bool.false_eq_true, ↓reduceIte, a1, a3]
    have hwnext1 : wNode c.p base ws (ws.next + 1) = none := by
      obtain ⟨a1, a2, a3, _, _⟩ := hfr (ws.next + 1) (by omega)
      simp only [wNode, a2, Bool.false_eq_true, ↓reduceIte, a1, a3]
    have hnoLink : ∀ z, ws.next ≤ z → ∀ u c', TReach (wNode c.p base ws) c.i ws.top.rootKey u →
        ¬ TLink (wNode c.p base ws) c.i u c' z := by
      intro z hz u c' hu hl
      have := hRlt z (TReach.link hu hl); omega
    cases tail' with
    | nil =>
      have hpost : ∀ wf : W, wf.nodes = upsert ws.nodes x ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) →
          wf.vals = ws.vals ++ [(ws.next, h)] → wf.taken = ws.taken → wf.top = ws.top →
          wf.next = ws.next + 2 →
          (TreeOK (wNode c.p base wf) c.i wf.top.rootKey ∧ wf.taken = ws.taken ∧ wf.top = ws.top ∧
            ∀ z, TReach (wNode c.p base wf) c.i wf.top.rootKey z →
              TReach (wNode c.p base ws) c.i ws.top.rootKey z ∨ ws.next ≤ z) := by
        intro wf g1 _ g3 g4 _
        have hN := wNode_upsert_updN c.p base ws wf x _ g1 g3 htx
        rw [hN, g4]
        refine ⟨treeOK_addKey (wNode c.p base ws) _ c.i ws.top.rootKey x ws.next ⟨true, []⟩ a hT hxR hwx
          (by rfl) (by simp) (updN_self _ _ _) (fun z hz => updN_ne _ _ _ _ hz) hwnext
          (fun u c' hu => hnoLink ws.next (Nat.le_refl _) u c' hu), g3, rfl, ?_⟩
        intro z hz
        rcases tReach_updN_addKey (wNode c.p base ws) c.i ws.top.rootKey x ws.next ⟨true, []⟩ a hwx
          (by rfl) (by simp) hwnext z hz with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by omega)
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
      have hv := hfr ws.next (Nat.le_refl _)
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf =>
            TreeOK (wNode c.p base wf) c.i wf.top.rootKey ∧ wf.taken = ws.taken ∧ wf.top = ws.top ∧
            ∀ z, TReach (wNode c.p base wf) c.i wf.top.rootKey z →
              TReach (wNode c.p base ws) c.i ws.top.rootKey z ∨ ws.next ≤ z) := by
        intro ws1 g1 g2 g3 g4 g5
        have hch : ws1.nodes.lookup ws.next = some ⟨true, []⟩ := by
          rw [g1, lookup_upsert]
          simp only [show ws.next ≠ x by omega, ↓reduceIte]
          exact lookup_append_single_self _ _ _ hv.1
        have hN1 := wNode_newSeg_updN c.p base ws ws1 x _ g1 g3 hv.1 hv.2.1 htx
        have hxy : x ≠ ws.next := by omega
        have hT1 : TreeOK (wNode c.p base ws1) c.i ws1.top.rootKey := by
          rw [hN1, g5]
          refine treeOK_newSeg (wNode c.p base ws) _ c.i ws.top.rootKey x ws.next (ws.next + 1)
            ⟨true, []⟩ ⟨true, []⟩ a 0 hT hxR hwx (by rfl) (by simp) ?_ ?_
            (fun c' z hc => absurd hc (KNode.empty_liveAt' c.i c' z)) ?_ hwnext hwnext1 (by omega) ?_
          · exact updN_self _ _ _
          · rw [updN_ne _ _ _ _ (Ne.symm hxy)]; exact updN_self _ _ _
          · intro z h1 h2; rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2]
          · intro z hz u c' hu
            rcases hz with hz | hz <;> (subst hz; exact hnoLink _ (by omega) u c' hu)
        have hagree : ∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z →
            updN (wNode c.p base ws) ws.next ⟨true, []⟩ z = wNode c.p base ws z := by
          intro z hz
          have := hRlt z hz
          rw [updN_ne _ _ _ _ (by omega)]
        have hTa := treeOK_of_agree _ _ _ _ hT hagree
        have hxR1 : TReach (updN (wNode c.p base ws) ws.next ⟨true, []⟩) c.i ws.top.rootKey x :=
          tReach_to_agree _ _ _ _ hagree _ hxR
        have hxR2 := tReach_updN_self _ c.i _ _ ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) hTa hxR1
        have hchR : TReach (wNode c.p base ws1) c.i ws1.top.rootKey ws.next := by
          rw [hN1, g5]
          exact TReach.link hxR2 ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ (by rfl)
            (by simp)⟩
        have hR1 : ∀ z, TReach (wNode c.p base ws1) c.i ws1.top.rootKey z →
            TReach (wNode c.p base ws) c.i ws.top.rootKey z ∨ z = ws.next := by
          intro z hz
          rw [hN1, g5] at hz
          exact tReach_newSegStep _ c.i _ x ws.next a hwnext hxy z hz
        refine writerWP_mono (ih (by simp) ws1 ws.next hch (by rw [g3]; exact hv.2.1) (by omega) ?_
          hT1 hchR ?_) ?_
        · intro z hz
          rw [g2] at hz
          have hz' := hfr z (by omega)
          refine ⟨?_, by rw [g3]; exact hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, by rw [g4]; exact hz'.2.2.2.2⟩
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          rw [lookup_append_single_ne _ _ _ _ (by omega)]; exact hz'.1
        · intro z hz
          rcases hR1 z hz with h' | h'
          · have := hRlt z h'; omega
          · omega
        · rintro _ wf ⟨k1, k2, k3, k4⟩
          refine ⟨k1, by rw [k2, g3], by rw [k3, g5], ?_⟩
          intro z hz
          rcases k4 z hz with h' | h'
          · rcases hR1 z h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (by omega)
          · exact Or.inr (by omega)
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

/-- `writerWP_putSegs_new_treeR` for any x: an x the tree does not reach takes
the new segment leaves with it, and the tree is kept. -/
theorem writerWP_putSegs_new_tree (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) (tail : List Nat) (htail : tail ≠ []) (ws : W)
    (x : NodeId) (hx : ws.nodes.lookup x = some ⟨true, []⟩) (htx : ws.taken.contains x = false)
    (hxn : x < ws.next)
    (hfr : ∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
      knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none)
    (hT : TreeOK (wNode c.p base ws) c.i ws.top.rootKey)
    (hRlt : ∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z → z < ws.next) :
    WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
      TreeOK (wNode c.p base wf) c.i wf.top.rootKey ∧ wf.taken = ws.taken ∧ wf.top = ws.top ∧
      ∀ z, TReach (wNode c.p base wf) c.i wf.top.rootKey z →
        TReach (wNode c.p base ws) c.i ws.top.rootKey z ∨ ws.next ≤ z) := by
  by_cases hxR : TReach (wNode c.p base ws) c.i ws.top.rootKey x
  · exact writerWP_putSegs_new_treeR c base key h hM hfuel tail htail ws x hx htx hxn hfr hT hxR hRlt
  · refine writerWP_mono (writerWP_putSegs_new c base key h hM hfuel tail htail ws x hx htx hxn hfr) ?_
    rintro _ wf ⟨k1, k2, _, k4, _, _, _, _⟩
    have hagree : ∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z →
        wNode c.p base wf z = wNode c.p base ws z := by
      intro z hz
      have hzlt := hRlt z hz
      have hzx : z ≠ x := fun he => hxR (he ▸ hz)
      unfold wNode
      rw [k1, k4 z hzlt hzx]
    rw [k2]
    exact ⟨treeOK_of_agree _ _ _ _ hT hagree, k1, rfl,
      fun z hz => Or.inl (tReach_of_agree _ _ _ _ hagree z hz)⟩

/-- The nodes reached after a node x gets a klong to a new empty leaf y: those
reached before, and y. -/
theorem tReach_newSegStepN (N : NodeId → Option KNode) (t : Time) (r x y : NodeId) (n : KNode)
    (a : Nat) (hn : N x = some n) (hwf : klongsWf n.ks = true)
    (htimes : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hy : N y = none) (hxy : x ≠ y) :
    ∀ z, TReach (updN (updN N y ⟨true, []⟩) x (n.add t (.key a y))) t r z →
      TReach N t r z ∨ z = y := by
  intro z hz
  induction hz with
  | root => exact Or.inl TReach.root
  | @link u c z _ hl ih =>
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hux : u = x
    · subst hux
      rw [updN_self] at hm
      cases hm
      rcases KNode.add_key_liveAt_mem n t a y hwf htimes c z hc with ⟨_, hzy⟩ | ⟨_, hc'⟩
      · exact Or.inr hzy
      · rcases ih with h | h
        · exact Or.inl (TReach.link h ⟨n, hn, hc'⟩)
        · exact absurd h hxy
    · rw [updN_ne _ _ _ _ hux] at hm
      by_cases huy : u = y
      · subst huy
        rw [updN_self] at hm
        cases hm
        exact absurd hc (KNode.empty_liveAt' t c z)
      · rw [updN_ne _ _ _ _ huy] at hm
        rcases ih with h | h
        · exact Or.inl (TReach.link h ⟨m, hm, hc⟩)
        · exact absurd h huy

/-- A put of a key pre ++ c0 :: tail whose leaf for c0 has no klong of c0 and
has room (`writerWP_put_newSegs_inv`'s case) keeps the writer's tree; the taken
ids are kept, and every node reached after is reached before or new. -/
theorem writerWP_put_newSegs_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hI : PutInv c base w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ w'.taken = w.taken ∧
      ∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
        TReach (wNode c.p base w) c.i w.top.rootKey z ∨ w.next ≤ z) := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hI.ids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ hwfR _ _ q.1 q.2 ReachS.root hq)
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk0 :=
    segRootR_reach _ _ _ _ hwfR pre _ rk0 ReachS.root hrk
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
  obtain ⟨hnone, hroom⟩ := hcur L n hvisL hn hnl
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
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hLR : TReach (wNode c.p base w) c.i w.top.rootKey L :=
    reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ c0 c.p.fuel rk0 L c0 hrrk hvisL)
  have hRlt : ∀ z, TReach (wNode c.p base w) c.i w.top.rootKey z → z < w.next :=
    fun z hz => hI.reach_lt z (tReach_reachS _ _ _ _ hz)
  have hwnext : wNode c.p base w w.next = none := hI.none_of_ge w.next (Nat.le_refl _)
  have hwnext1 : wNode c.p base w (w.next + 1) = none := hI.none_of_ge (w.next + 1) (by omega)
  have hnoLink : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hu hl
    have := hRlt z (TReach.link hu hl); omega
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.vals = w3.vals → ws.top = w3.top →
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ w'.taken = w.taken ∧
        ∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (wNode c.p base w) c.i w.top.rootKey z ∨ w.next ≤ z) := by
    intro ws h1 h2 h3 h4 h5
    rw [hnext3] at h1 h2
    rw [hnext3]
    have hw3n : w3.nodes.lookup w.next = none := by
      cases h' : w3.nodes.lookup w.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have hLne : L ≠ w.next := by
      have := hsrcw3 L (by rw [hlk3]; rfl); omega
    have hlkc : ws.nodes.lookup w.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w.next ≠ L by omega, ↓reduceIte]
      exact lookup_append_single_self _ _ _ hw3n
    have htk : ∀ z, ws.taken.contains z = w.taken.contains z := by intro z; rw [h3, hr03.2.2.1]
    have htk3 : w3.taken.contains w.next = false := by rw [hr03.2.2.1]; exact hntake _ (Nat.le_refl _)
    have htL3 : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
    have hN1 : wNode c.p base ws = updN (updN (wNode c.p base w) w.next e) L
        (n.add c.i (.key c0 w.next)) := by
      have := wNode_newSeg_updN c.p base w3 ws L _ (by rw [hnext3]; exact h1) h3 (by rw [hnext3]; exact hw3n)
        (by rw [hnext3]; exact htk3) htL3
      rw [this, hr03.1, hnext3]
    have htop : ws.top = w.top := by rw [h5, hr03.2.1]
    have hT1 : TreeOK (wNode c.p base ws) c.i ws.top.rootKey := by
      rw [hN1, htop]
      refine treeOK_newSeg (wNode c.p base w) _ c.i w.top.rootKey L w.next (w.next + 1)
        n ⟨true, []⟩ c0 0 hI.tree hLR hn (hI.wf L n hn) (hI.times L n hn) ?_ ?_
        (fun c' z hc => absurd hc (KNode.empty_liveAt' c.i c' z)) ?_ hwnext hwnext1 (by omega) ?_
      · exact updN_self _ _ _
      · rw [updN_ne _ _ _ _ (Ne.symm hLne)]; exact updN_self _ _ _
      · intro z h1 h2; rw [updN_ne _ _ _ _ h1, updN_ne _ _ _ _ h2]
      · intro z hz u c' hu
        rcases hz with hz | hz <;> (subst hz; exact hnoLink _ (by omega) u c' hu)
    have hagree : ∀ z, TReach (wNode c.p base w) c.i w.top.rootKey z →
        updN (wNode c.p base w) w.next e z = wNode c.p base w z := by
      intro z hz
      have := hRlt z hz
      rw [updN_ne _ _ _ _ (by omega)]
    have hTa := treeOK_of_agree _ _ _ _ hI.tree hagree
    have hLR1 : TReach (updN (wNode c.p base w) w.next e) c.i w.top.rootKey L :=
      tReach_to_agree _ _ _ _ hagree _ hLR
    have hLR2 := tReach_updN_self _ c.i _ _ (n.add c.i (.key c0 w.next)) hTa hLR1
    have hchR : TReach (wNode c.p base ws) c.i ws.top.rootKey w.next := by
      rw [hN1, htop]
      exact TReach.link hLR2 ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ (hI.wf L n hn)
        (hI.times L n hn)⟩
    have hR1 : ∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z →
        TReach (wNode c.p base w) c.i w.top.rootKey z ∨ z = w.next := by
      intro z hz
      rw [hN1, htop] at hz
      exact tReach_newSegStepN _ c.i _ L w.next n c0 hn (hI.wf L n hn) (hI.times L n hn) hwnext hLne z hz
    refine writerWP_mono (writerWP_putSegs_new_treeR c base (pre ++ c0 :: tail) h hM hfuel tail htail ws
      w.next hlkc (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) ?_ hT1 hchR ?_) ?_
    · intro z hz
      rw [h2] at hz
      refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hI.fresh z (by omega)).1,
        (hI.fresh z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
      rw [h1, lookup_upsert]
      simp only [show z ≠ L by omega, ↓reduceIte]
      rw [lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    · intro z hz
      rcases hR1 z hz with h' | h'
      · have := hRlt z h'; omega
      · omega
    · rintro _ wf ⟨k1, k2, _, k4⟩
      refine ⟨k1, by rw [k2, h3, hr03.2.2.1], ?_⟩
      intro z hz
      rcases k4 z hz with h' | h'
      · rcases hR1 z h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (by omega)
      · rw [h2] at h'; exact Or.inr (by omega)
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl

/-! ## The walk's ranges after new segment leaves below an empty leaf -/

/-- The walk's ranges after an empty leaf x, whose parents are all leaves, gets
new segment leaves below it: x and the new nodes (`New`: none before, the root
not one, none linked from a node reached) are leaves whose live klongs name new
nodes or no node. -/
theorem rangeOrder_newChain (N N' : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (New : NodeId → Prop) (hR : RangeOrder N t r) (hxr : x ≠ r) (hxnew : ¬ New x)
    (hxpar : ∀ u un c, N u = some un → (c, x) ∈ un.liveAt t → un.leaf = true)
    (hnew : ∀ z, New z → N z = none ∧ z ≠ r ∧ ∀ u c, TReach N t r u → ¬ TLink N t u c z)
    (hNl : ∀ z m', (New z ∨ z = x) → N' z = some m' → m'.leaf = true)
    (hNk : ∀ z m' c z', (New z ∨ z = x) → N' z = some m' → (c, z') ∈ m'.liveAt t →
      New z' ∨ N' z' = none)
    (hN' : ∀ z, z ≠ x → ¬ New z → N' z = N z) : RangeOrder N' t r := by
  have hold : ∀ z m', N' z = some m' → z ≠ x → ¬ New z → N z = some m' := by
    intro z m' h h1 h2; rw [← hN' z h1 h2]; exact h
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (¬ New z ∧ z ≠ x ∧ ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    ((New z ∨ z = x) ∧ lo = 0 ∧ hi = none) ∨ N' z = none
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨fun h => (hnew r h).2.1 rfl, fun h => hxr h.symm, 0, none, ReachR.root,
      Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m' c z' b _ hG hm hml' hb
    rcases hG with ⟨hzn, hzx, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzn, _, _⟩ | hG
    · have hm0 := hold z m' hm hzx hzn
      have hcz := childBounds_fst _ _ _ _ hb
      have hz'n : ¬ New z' := fun h =>
        (hnew z' h).2.2 z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, hcz⟩
      have hz'x : z' ≠ x := by
        intro h; subst h
        have := hxpar z m' c hm0 hcz
        rw [hml'] at this; cases this
      obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N t r hR z m' lo0 lo hi0 hi hz0 hm0 hml' hlo hhi
        _ (KNode.liveAt_order m' t) c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
      exact Or.inl ⟨hz'n, hz'x, lo1, hi1, h3, h4, h5⟩
    · rw [hNl z m' hzn hm] at hml'; cases hml'
    · rw [hG] at hm; cases hm
  · intro z lo hi m' c z' _ hG hm hml' hcz
    rcases hG with ⟨hzn, hzx, lo0, hi0, hz0, _, _⟩ | ⟨hzn, _, _⟩ | hG
    · have hm0 := hold z m' hm hzx hzn
      have hz'n : ¬ New z' := fun h =>
        (hnew z' h).2.2 z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, hcz⟩
      by_cases hz'x : z' = x
      · exact Or.inr (Or.inl ⟨Or.inr hz'x, rfl, rfl⟩)
      · exact Or.inl ⟨hz'n, hz'x, 0, none, ReachR.seg z m' lo0 hi0 c z' hz0 hm0 hml' hcz,
          Nat.le_refl _, HiLE.refl _⟩
    · rcases hNk z m' c z' hzn hm hcz with h | h
      · exact Or.inr (Or.inl ⟨Or.inl h, rfl, rfl⟩)
      · exact Or.inr (Or.inr h)
    · rw [hG] at hm; cases hm
  · intro z lo hi m' _ hG hm
    rcases hG with ⟨hzn, hzx, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzn, hlo, hhi⟩ | hG
    · exact nodeRange_wider m' t lo0 lo hi0 hi (hR z lo0 hi0 m' hz0 (hold z m' hm hzx hzn)) hlo hhi
    · rw [hhi]
      intro q _
      simp only [hNl z m' hzn hm, ↓reduceIte]
      exact ⟨by omega, trivial⟩
    · rw [hG] at hm; cases hm

/-- The new segment leaves below an empty segment leaf x, whose parents are all
leaves, keep the walk's ranges. -/
theorem writerWP_putSegs_new_range (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) (tail : List Nat) (htail : tail ≠ []) (ws : W)
    (x : NodeId) (hx : ws.nodes.lookup x = some ⟨true, []⟩) (htx : ws.taken.contains x = false)
    (hxn : x < ws.next)
    (hfr : ∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
      knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none)
    (hR : RangeOrder (wNode c.p base ws) c.i ws.top.rootKey) (hxr : x ≠ ws.top.rootKey)
    (hxpar : ∀ u un cc, wNode c.p base ws u = some un → (cc, x) ∈ un.liveAt c.i → un.leaf = true)
    (hRlt : ∀ z, TReach (wNode c.p base ws) c.i ws.top.rootKey z → z < ws.next) :
    WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
      RangeOrder (wNode c.p base wf) c.i wf.top.rootKey) := by
  refine writerWP_mono (writerWP_and (writerWP_putSegs_new_shape c base key h hM hfuel tail htail ws x
    hx htx hxn hfr) (writerWP_putSegs_new c base key h hM hfuel tail htail ws x hx htx hxn hfr)) ?_
  rintro _ wf ⟨⟨k1, k2, k3, k4, k5, k6⟩, ⟨_, _, _, _, _, _, k7, _⟩⟩
  have hwf : ∀ z m', (z = x ∨ ws.next ≤ z) → wNode c.p base wf z = some m' →
      wf.nodes.lookup z = some m' := by
    intro z m' hz hm
    unfold wNode at hm
    rw [k1] at hm
    have htz : ws.taken.contains z = false := by
      rcases hz with hz | hz
      · rw [hz]; exact htx
      · exact (hfr z hz).2.1
    rw [htz] at hm
    simp only [Bool.false_eq_true, ↓reduceIte] at hm
    cases h' : wf.nodes.lookup z with
    | some m'' => rw [h'] at hm; exact hm
    | none =>
      exfalso
      rcases hz with hz | hz
      · subst hz; rw [h'] at k7; cases k7
      · rw [h'] at hm
        simp only at hm
        rw [(hfr z hz).2.2.1] at hm; cases hm
  have hRlt' : ws.top.rootKey < ws.next := hRlt _ TReach.root
  rw [k2]
  refine rangeOrder_newChain (wNode c.p base ws) (wNode c.p base wf) c.i ws.top.rootKey x
    (fun z => ws.next ≤ z) hR hxr (by omega) hxpar ?_ ?_ ?_ ?_
  · intro z hz
    refine ⟨?_, by omega, fun u c' hu hl => ?_⟩
    · obtain ⟨a1, a2, a3, _, _⟩ := hfr z hz
      simp only [wNode, a2, Bool.false_eq_true, ↓reduceIte, a1, a3]
    · have := hRlt z (TReach.link hu hl); omega
  · intro z m' hz hm
    have hz' : z = x ∨ ws.next ≤ z := hz.elim (fun h => Or.inr h) (fun h => Or.inl h)
    exact (k6 z m' hz' (hwf z m' hz' hm)).1
  · intro z m' c' z' hz hm hc
    exact Or.inl ((k6 z m' (hz.elim (fun h => Or.inr h) (fun h => Or.inl h))
      (hwf z m' (hz.elim (fun h => Or.inr h) (fun h => Or.inl h)) hm)).2 c' z' hc)
  · intro z hzx hzn
    have hzlt : z < ws.next := by omega
    unfold wNode
    rw [k1, k4 z hzlt hzx]

/-- Every klong of every node that N reads names an id below b. -/
def KlongsBelow (N : NodeId → Option KNode) (b : NodeId) : Prop :=
  ∀ x xn, N x = some xn → ∀ cv y, Klong.key cv y ∈ xn.ks → y < b

end SIS.Tree
