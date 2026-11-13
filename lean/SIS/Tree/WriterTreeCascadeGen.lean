/-
Cascades of time splits of any depth keep the writer's tree (bergdb 024-22,
`OpTreeOK`). The writer's time split of a node below an inner parent, with
what the parent's `appendKlongs` does left open (`writerWP_handleFullWith_time_up`);
the tree before the klong to the new node is put in the parent, as the tree with
the node's klongs put (`treeOK_up_time`).
-/
import SIS.Tree.WriterTreeDepth

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's time split of x, which existed before the transaction, with
klongs ins and the last version `n.lastVersion`, below an inner parent q (the
access path's d' and d' + 1): the new node at the next id holds the last version
with ins, then q gets the klong k1 to it (`appendKlongs d'`, whatever it does),
then x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_time_up (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true → (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
      (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) →
      ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, l.ks⟩)] → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
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
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl

theorem wNode_upsert_updN (p : Params) (base : View BVal) (w w' : W) (x : NodeId) (m : KNode)
    (hn : w'.nodes = upsert w.nodes x m) (ht : w'.taken = w.taken) (hx : w.taken.contains x = false) :
    wNode p base w' = updN (wNode p base w) x m := by
  funext z
  unfold wNode updN
  rw [ht, hn, lookup_upsert]
  by_cases hz : z = x
  · subst hz; simp only [hx, Bool.false_eq_true, ↓reduceIte]
  · simp only [hz, ↓reduceIte]

theorem wNode_append_updN (p : Params) (base : View BVal) (w w' : W) (m : KNode)
    (hn : w'.nodes = w.nodes ++ [(w.next, m)]) (ht : w'.taken = w.taken)
    (hfree : w.nodes.lookup w.next = none) (htk : w.taken.contains w.next = false) :
    wNode p base w' = updN (wNode p base w) w.next m := by
  funext z
  unfold wNode updN
  rw [ht, hn]
  by_cases hz : z = w.next
  · subst hz
    simp only [htk, Bool.false_eq_true, ↓reduceIte, List.lookup_append, hfree]
    simp [List.lookup]
  · simp only [hz, ↓reduceIte, List.lookup_append]
    cases h : w.nodes.lookup z with
    | some _ => rfl
    | none =>
      have hb : (z == w.next) = false := by simpa using hz
      simp [List.lookup, hb]

/-- The live klongs of a node with a key klong put: those of the node but the
compare value's, and the klong's. -/
theorem KNode.add_key_liveAt_iff_fold (n m : KNode) (t : Time) (k : Nat) (y : NodeId)
    (hw : klongsWf n.ks = true) (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hm : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (hl : ∀ q', m.live.lookup q' = [(k, y)].foldl (pairLookupStep q') (n.live.lookup q')) :
    ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ (n.add t (.key k y)).liveAt t := by
  intro c z h
  have hat := KNode.add_times n t (.key k y) (fun s h => by cases h) hn
  rw [KNode.liveAt_of_times m t hm] at h
  rw [KNode.liveAt_of_times _ t hat]
  have h1 := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
  rw [hl c] at h1
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t k c y hw]
  simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at h1
  exact h1

/-- A cascade of time splits of any depth (bergdb 024-22, `OpTreeOK`): the
access path's nodes X s (with room for a klong) to X D, each below the one
before by klong K i, each of the transaction's time, inner but X D, existed
before the transaction, and full nodes time split. From a state whose tree
with the klong (k, y) put in X j is a tree, `appendKlongs j (X j) [(k, y)]`
keeps the writer's tree; it changes no node outside X s .. X j below the next
id, and reaches nodes that the tree with the klong put reaches, or new ones. -/
theorem writerWP_appendKlongs_timeChain (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hinner : ∀ i, s < i → i ≤ D → (Nn (i - 1)).leaf = false)
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnew : ∀ i, s < i → i ≤ D → (Nn i).firstTime ≠ some c.i)
    (hsplit : ∀ i, s < i → i ≤ D → c.p.M < (Nn i).size + 1 + 1 →
      ((Nn i).lastVersion c.i).size ≤ c.p.splitAbove)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : (Nn s).size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p ((Nn s).add c.i (.key k y)) = false)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i') :
    ∀ e, s + e ≤ D → ∀ (w : W) (k : Nat) (y : NodeId),
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      y < w.next →
      TreeOK (updN (wNode c.p base w) (X (s + e)) ((Nn (s + e)).add c.i (.key k y))) c.i
        w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) [(k, y)]) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e)) ((Nn (s + e)).add c.i (.key k y))) c.i
            w.top.rootKey z ∨ w.next ≤ z)) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (k : Nat) (y : NodeId),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + 1 + 1 ≤ c.p.M →
      deadOver c.p ((Nn (s + e)).add c.i (.key k y)) = false →
      TreeOK (updN (wNode c.p base w) (X (s + e)) ((Nn (s + e)).add c.i (.key k y))) c.i
        w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) [(k, y)]) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e)) ((Nn (s + e)).add c.i (.key k y))) c.i
            w.top.rootKey z ∨ w.next ≤ z)) := by
    intro e _ w k y hlk htk hroom hdead hV
    refine writerWP_mono (writerWP_appendKlongs_room (s + e) (X (s + e)) (Nn (s + e)) k y c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    have hN : wNode c.p base { w with nodes := upsert w.nodes (X (s + e)) ((Nn (s + e)).add c.i
        (.key k y)) } = updN (wNode c.p base w) (X (s + e)) ((Nn (s + e)).add c.i (.key k y)) :=
      wNode_upsert_updN c.p base w _ _ _ rfl rfl htk
    refine ⟨?_, ⟨rfl, rfl, rfl, Nat.le_refl _⟩, ?_, ?_⟩
    · rw [hN]; exact hV
    · intro z _ hz
      show (upsert w.nodes _ _).lookup z = _
      rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hz (s + e) (Nat.le_add_right _ _) (Nat.le_refl _)))]
    · intro z hz
      rw [hN] at hz
      exact Or.inl hz
  intro e
  induction e with
  | zero =>
    intro hD w k y _ hS2 _ _ _ _ _ hV
    obtain ⟨hlk, htk⟩ := hS2 s (Nat.le_refl _) (by omega)
    exact hroomCase 0 hD w k y hlk htk htop.1 (htop.2 k y) hV
  | succ e ih =>
    intro hD w k y hS1 hS2 hS3 hS4 hS5 hS6 hS7 hV
    have hj : s < s + (e + 1) := by omega
    obtain ⟨hlk, htk⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, htq⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + 1 + 1 ≤ c.p.M ∧
        deadOver c.p ((Nn (s + (e + 1))).add c.i (.key k y)) = false
    · exact hroomCase (e + 1) hD w k y hlk htk hroom.1 hroom.2 hV
    · -- the full node: a time split, and the klong to the new node put in the parent
      have hql : (Nn (s + e)).leaf = false := by
        have := hinner (s + (e + 1)) hj hD; simpa using this
      have hfirst := hnew (s + (e + 1)) hj hD
      have hpq : (w.path[s + e]?).map (·.2) = some (X (s + e)) := by
        rw [hS1]; exact hX (s + e) (by omega) (by omega)
      have hpk : w.path[s + e + 1]? = some (some (K (s + (e + 1))), X (s + (e + 1))) := by
        rw [hS1]; exact hK (s + (e + 1)) hj hD
      have hkl : (K (s + (e + 1)), X (s + (e + 1))) ∈ (Nn (s + e)).liveAt c.i := by
        have := hlinkK (s + (e + 1)) hj hD; simpa using this
      -- the rest of the step, for either flag
      have hstep : ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) [(k, y)] ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                ((Nn (s + (e + 1))).add c.i (.key k y))) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
        intro compact hcs
        apply writerWP_handleFullWith_time_up (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) [(k, y)] compact c w hlk hlq hql hfirst hcs hpq hpk
        intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1t h1top h1path h1next _
        -- facts of the state before the parent's step
        obtain ⟨hfree0, htk0, _⟩ := hS5 w.next (Nat.le_refl _)
        have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ :=
          wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
        have hwnext : wNode c.p base w w.next = none := by
          simp only [wNode, htk0, Bool.false_eq_true, ↓reduceIte, hfree0, (hS5 w.next (Nat.le_refl _)).2.2]
        have hnoLink : ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' w.next := by
          intro u c' hl; have := hS6 u c' w.next hl; omega
        have hyR : ¬ TReach (wNode c.p base w) c.i w.top.rootKey w.next :=
          not_reach_fresh _ c.i _ w.next hS3 hwnext (fun u c' _ => hnoLink u c')
        have hXlt : ∀ i, s ≤ i → i ≤ s + (e + 1) → X i < w.next := by
          intro i h1 h2
          obtain ⟨hl, _⟩ := hS2 i h1 h2
          rcases Nat.lt_or_ge (X i) w.next with hlt | hge
          · exact hlt
          · have := (hS5 (X i) hge).1
            rw [hl] at this; cases this
        -- the tree with the parent's klong put
        have hqx : X (s + e) ≠ X (s + (e + 1)) := by
          intro h; have := hdist _ _ (by omega) (by omega) (by omega) hD h; omega
        have hwq : wNode c.p base w (X (s + e)) = some (Nn (s + e)) := by
          simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
        have hwx : wNode c.p base w (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
          simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
        have hqR : TReach (updN (wNode c.p base w) (X (s + (e + 1))) ((Nn (s + (e + 1))).add c.i (.key k y))) c.i w.top.rootKey (X (s + e)) :=
          tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 (s + e) (by omega) (by omega))
            ⟨Nn (s + e), hwq, hkl⟩
        have hqtimes := htimes (s + e) (by omega) (by omega)
        have hqwf := hwf (s + e) (by omega) (by omega)
        have hxtimes := htimes (s + (e + 1)) (by omega) hD
        have hxwf := hwf (s + (e + 1)) (by omega) hD
        have hsplitT := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (s + (e + 1))) ((Nn (s + (e + 1))).add c.i (.key k y))) (updN (wNode c.p base w1) (X (s + e))
            ((Nn (s + e)).add c.i (.key (K (s + (e + 1))) w.next))) c.i w.top.rootKey (X (s + e))
          (X (s + (e + 1))) w.next (Nn (s + e)) ((Nn (s + (e + 1))).add c.i (.key k y))
          ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ ((Nn (s + e)).add c.i (.key (K (s + (e + 1))) w.next))
          (K (s + (e + 1))) hV hqR (by show updN _ _ _ _ = _; rw [updN_ne _ _ _ _ hqx]; exact hwq)
          hkl (updN_self _ _ _)
          (updN_self _ _ _)
          (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + e) (by omega) (by omega); omega), hN1]
            exact updN_self _ _ _)
          (KNode.add_key_liveAt_iff_fold _ _ c.i k y hxwf hxtimes hl_times hl_look)
          (by
            intro z hz1 hz2 hz3
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)]; exact hwnext)
          (by
            intro u c' _ hl
            obtain ⟨m, hm, hc⟩ := hl
            by_cases hu : u = X (s + (e + 1))
            · rw [hu, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              rcases KNode.add_key_liveAt_mem _ c.i _ _ hxwf hxtimes c' w.next hc with ⟨_, h⟩ | ⟨_, h⟩
              · omega
              · exact hnoLink _ _ ⟨_, hwx, h⟩
            · rw [updN_ne _ _ _ _ hu] at hm
              exact hnoLink u c' ⟨m, hm, hc⟩)
        obtain ⟨hT1V, hR1V⟩ := hsplitT
        -- the parent's step, by the induction
        have hpar := ih (by omega) w1 (K (s + (e + 1))) w.next (by rw [h1path, hS1])
          (by
            intro i h1 h2
            obtain ⟨a, b⟩ := hS2 i h1 (by omega)
            refine ⟨?_, by rw [h1t]; exact b⟩
            rw [h1n, List.lookup_append, a]; rfl)
          (by
            rw [hN1, h1top]
            exact treeOK_updN_unreach _ c.i _ _ _ hS3 hyR)
          (by
            intro i h1 h2
            rw [hN1, h1top]
            obtain ⟨a, ha⟩ := (hS4 i h1 (by omega)).pathLen
            exact tReach_updN_of_short _ c.i _ _ _ a _ ha (fun b hb => absurd hb.reach hyR))
          (by
            intro z hz
            rw [h1next] at hz
            obtain ⟨a, b, d⟩ := hS5 z (by omega)
            refine ⟨?_, by rw [h1t]; exact b, d⟩
            rw [h1n, List.lookup_append, a]
            have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
            simp [List.lookup, hb])
          (by
            intro u c' z hl
            rw [hN1] at hl
            rw [h1next]
            obtain ⟨m, hm, hc⟩ := hl
            by_cases hu : u = w.next
            · rw [hu, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              have h2 := KNode.add_key_liveAt_iff_fold _ _ c.i k y hxwf hxtimes hl_times hl_look c' z hc
              rcases KNode.add_key_liveAt_mem _ c.i _ _ hxwf hxtimes c' z h2 with ⟨_, h⟩ | ⟨_, h⟩
              · omega
              · have := hS6 _ _ _ ⟨_, hwx, h⟩; omega
            · rw [updN_ne _ _ _ _ hu] at hm
              have := hS6 u c' z ⟨m, hm, hc⟩; omega)
          (by rw [h1next]; omega)
          (by rw [h1top]; exact hT1V)
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next⟩, h2frame, h2reach⟩
        -- the node keeps its klongs before the transaction; it is reached no more
        have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
          rw [h2frame _ (by rw [h1next]; have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)
            (fun i h1 h2 he => by have := hdist _ _ (by omega) hD h1 (by omega) he; omega), h1n,
            List.lookup_append, hlk]
          rfl
        simp only [writerWP_bind]
        rw [writerWP_getNode_known _ _ c w2 hlk2]
        simp only [putNode, writerWP_modify]
        have htk2 : w2.taken.contains (X (s + (e + 1))) = false := by rw [h2t, h1t]; exact htk
        generalize hw3 : ({ w2 with nodes := upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) } : W) = w3
        have h3n : w3.nodes = upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) := by
          rw [← hw3]
        have h3t : w3.taken = w2.taken := by rw [← hw3]
        have hN3 := wNode_upsert_updN c.p base w2 w3 (X (s + (e + 1))) _ h3n h3t htk2
        have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (s + (e + 1))) := by
          intro h
          rcases h2reach _ h with h' | h'
          · rw [h1top] at h'
            exact (hR1V _ h').2 rfl
          · rw [h1next] at h'; have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [hN3]
          exact treeOK_updN_unreach _ c.i _ _ _ hT2 hxR2
        · rw [h2top, h1top]
        · rw [h2t, h1t]
        · rw [h2path, h1path]
        · rw [h1next] at h2next; omega
        · intro z hz hzX
          rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _))),
            h2frame z (by rw [h1next]; omega) (fun i h1 h2 => hzX i h1 (by omega)), h1n,
            List.lookup_append]
          cases h : w.nodes.lookup z with
          | some _ => rfl
          | none =>
            have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
            simp [List.lookup, hb]
        · intro z hz
          rw [hN3] at hz
          have hz2 := tReach_updN_unreach _ c.i _ _ _ hxR2 z hz
          rcases h2reach z hz2 with h' | h'
          · rw [h1top] at h'
            rcases (hR1V z h').1 with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (by omega)
          · rw [h1next] at h'; exact Or.inr (by omega)
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn (s + (e + 1))).size + [(k, y)].length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        apply hstep false
        have := hsplit (s + (e + 1)) hj hD (by simp at hsz; omega)
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact this
      · have hd : deadOver c.p ([(k, y)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) = true := by
          simp only [List.foldl_cons, List.foldl_nil]
          cases h : deadOver c.p ((Nn (s + (e + 1))).add c.i (.key k y)) with
          | true => rfl
          | false => exact absurd ⟨by simp at hsz; omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hstep true (by simp)

/-- The writer's space split of x, which existed before the transaction, with
klongs ins, below an inner parent q: the halves at the next two ids, then q
gets the klongs to them (`appendKlongs d'`, whatever it does), then x keeps
its klongs before the transaction. -/
theorem writerWP_handleFullWith_space_up (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 →
        WriterWP (appendKlongs d' q [(k1, w.next),
          ((halves n.leaf c.i (n.lastVersion c.i) ins).2.2, w.next + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (hup _ ?_ ?_ ?_ ?_ ?_) ?_
      rotate_left 5
      · intro _ w2 h
        simpa only [writerWP_bind, putNode, writerWP_modify] using h
      · intro z
        simp only [lookup_upsert, List.lookup_append]
        by_cases hz2 : z = w.next + 2
        · have hz1 : z ≠ w.next := by omega
          simp [hz2]
        · simp only [hz2, ↓reduceIte]
          by_cases hz1 : z = w.next
          · simp [hz1]
          · simp only [hz1, ↓reduceIte]
            cases h : w.nodes.lookup z with
            | some m => rfl
            | none =>
              have hb1 : (z == w.next) = false := by simpa using hz1
              have hb2 : (z == w.next + 2) = false := by simpa using hz2
              simp [List.lookup, hb1, hb2]
      all_goals rfl)

end SIS.Tree
