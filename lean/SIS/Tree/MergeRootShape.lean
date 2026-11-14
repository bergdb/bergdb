/-
The merge's full parent at the space root with the take-back's facts (bergdb
024-12, for prover putinv's `TakeJ2` through a merge at depth 1):
`writerWP_handleFull_rootVF` with the reach back (the nodes reached before, but
the root, are reached after; the root is reached after or left as its previous
version; the new nodes are reached), and the shapes of the nodes the root's
split makes or changes (`ShapePost` for the one-node chain of the root), as
`writerWP_handleFull_lastVF2` and `writerWP_handleFull_lastShape` give them one
level down.
-/
import SIS.Tree.GetMergeRoot
import SIS.Tree.LevelShape

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The next id and the path after the root's splits -/

/-- The space split of the space root, which existed before the transaction:
the next id grows past the halves and the new root; the path is kept. -/
theorem writerWP_handleFullWith_rootSpaceSplit_next (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => w.next + 2 + 2 + 2 ≤ w'.next ∧ w'.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  have hL3 : L ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        exact ⟨by simp only; omega, rfl⟩

/-- The time split of the space root, which existed before the transaction:
the next id grows past the new root; the path is kept. -/
theorem writerWP_handleFullWith_rootTimeSplit_next (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up 0 L [] last compact) c w
      (fun _ w' => w.next + 2 ≤ w'.next ∧ w'.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          exact ⟨by simp only; omega, rfl⟩

set_option linter.unusedSimpArgs false in
/-- The space split in place of the space root, which the transaction made:
the next id grows past the second half and the new root; the path is kept. -/
theorem writerWP_handleFullWith_rootSpaceSplitInPlace_next
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => w.next + 2 + 2 ≤ w'.next ∧ w'.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            first
            | exact ⟨by simp only; omega, rfl⟩
            | exact ⟨by omega, trivial⟩
            | (refine ⟨?_, ?_⟩ <;> first | trivial | rfl | omega | (simp only; omega) | simp)

/-- The time split in place of the space root, which the transaction made: the
root holds its last version; the next id and the path are kept. -/
theorem writerWP_handleFullWith_rootTimeInPlace_nodes (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      w'.next = w.next ∧ w'.path = w.path ∧ w'.nodes = upsert w.nodes L ⟨n.leaf, last.ks⟩) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  cases compact with
  | true =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial
  | false =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

/-! ## The reach back -/

set_option maxHeartbeats 4000000 in
/-- `handleFull` at the space root L with the last version `last`, on
`writerWP_handleFull_rootVF`'s premises: the nodes the tree with L's last version
reaches, but L, are reached after; L is reached after, or holds its klongs before
the transaction (a root that existed before it); every node cached from the next
id on is reached after; the root after is the root before or a new node. -/
theorem writerWP_handleFull_rootReach (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (up : NodeId → List (Nat × NodeId) → M Unit) (L : NodeId) (n last : KNode) (compact : Bool)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (w : W) (hlk : w.nodes.lookup L = some n) (htk : w.taken.contains L = false)
    (hrk : w.top.rootKey = L)
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      (∀ z, TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey z → z ≠ L →
        TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
      (TReach (wNode c.p base w') c.i w'.top.rootKey L ∨
        (w'.nodes.lookup L = some (n.toPrev (c.i - 1)) ∧
          wNode c.p base w' L = some (n.toPrev (c.i - 1)) ∧ n.firstTime ≠ some c.i)) ∧
      (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
        TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
      (w'.top.rootKey = w.top.rootKey ∨ w.next ≤ w'.top.rootKey)) := by
  have hLn : L < w.next := by
    rcases Nat.lt_or_ge L w.next with hlt' | hge
    · exact hlt'
    · have := (hS5 L hge).1
      rw [hlk] at this; cases this
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  obtain ⟨hfree0, htk0, _⟩ := hS5 w.next (Nat.le_refl _)
  obtain ⟨hfree2, htk2', _⟩ := hS5 (w.next + 2) (by omega)
  obtain ⟨_, htk4, _⟩ := hS5 (w.next + 2 + 2) (by omega)
  have hwfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    obtain ⟨a, b, d⟩ := hS5 z hz
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
  -- a node with a link in the tree with L's last version, but L, is below the next id
  have hVu : ∀ u m, u ≠ L → updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩ u = some m →
      wNode c.p base w u = some m ∧ u < w.next := by
    intro u m hu h
    rw [updN_ne _ _ _ _ hu] at h
    refine ⟨h, ?_⟩
    rcases Nat.lt_or_ge u w.next with h' | h'
    · exact h'
    · rw [hwfree u h'] at h; cases h
  -- a node cached after and not taken is the writer's node
  have hcached : ∀ (w' : W), w'.taken = w.taken → ∀ z m, w.next ≤ z → w'.nodes.lookup z = some m →
      wNode c.p base w' z = some m := by
    intro w' ht z m hz hm
    simp only [wNode, ht, (hS5 z hz).2.1, Bool.false_eq_true, ↓reduceIte, hm]
  by_cases hsp : c.p.splitAbove < last.size ∧ compact = false
  · obtain ⟨hsp, hc⟩ := hsp
    subst hc
    have h2l := hlen2 hsp
    obtain ⟨r, hdiv0, hsc, _, _, _⟩ := halves_facts_nil c.i (⟨n.leaf, last.ks⟩ : KNode) h2l hlt
    have hcov0 := halves_cover_nil c.i (⟨n.leaf, last.ks⟩ : KNode) h2l hlt hlwf
    rw [hlastV] at hdiv0 hcov0
    have hdiv : (halves n.leaf c.i last []).2.2 = r.1 := hdiv0
    have hcov : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i →
        (c' < (halves n.leaf c.i last []).2.2 →
          ∃ c'', (c'', z) ∈ (halves n.leaf c.i last []).1.liveAt c.i) ∧
        ((halves n.leaf c.i last []).2.2 ≤ c' →
          ∃ c'', (c'', z) ∈ (halves n.leaf c.i last []).2.1.liveAt c.i) := hcov0
    by_cases hmade : n.firstTime = some c.i
    · -- the root space split in place: the second half and a new root
      refine writerWP_mono (writerWP_handleFullWith_rootSpaceSplitInPlace_nilV up L n last c w
        hlk hmade hsp hLn hfree2) ?_
      rintro _ w' ⟨⟨h't, h'root, h'n⟩, _⟩
      obtain ⟨out, hout⟩ : ∃ o, halves n.leaf c.i last [] = o := ⟨_, rfl⟩
      rw [hout] at h'n hdiv hcov
      rw [hdiv] at h'n hcov
      have hFx : ¬ w.next = L := by omega
      have hRx : ¬ w.next + 2 = L := by omega
      have hRF : ¬ w.next + 2 = w.next := by omega
      have hw' : ∀ z, wNode c.p base w' z =
          if z = L then some out.1
          else if z = w.next then some out.2.1
          else if z = w.next + 2 then some ⟨false, [.time c.i, .key 0 L, .key r.1 w.next]⟩
          else wNode c.p base w z := by
        intro z
        by_cases h1 : z = L
        · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
        · by_cases h2 : z = w.next
          · subst h2; simp only [wNode, h't, htk0, h'n, h1, Bool.false_eq_true, ↓reduceIte]
          · by_cases h3 : z = w.next + 2
            · subst h3
              simp only [wNode, h't, htk2', h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
            · simp only [wNode, h't, h'n, h1, h2, h3, ↓reduceIte]
      have hnd : ([(0, L), (r.1, w.next)].map Prod.fst).Nodup := by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
        omega
      have hR : wNode c.p base w' (w.next + 2) =
          some ⟨false, newKlongs c.i [(0, L), (r.1, w.next)]⟩ := by
        rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl
      have hRR : TReach (wNode c.p base w') c.i w'.top.rootKey (w.next + 2) := by
        rw [h'root]; exact TReach.root
      have hRL : TReach (wNode c.p base w') c.i w'.top.rootKey L :=
        TReach.link hRR ⟨_, hR, (mrg_newKlongs_liveAt_iff false c.i _ hnd 0 L).mpr (by simp)⟩
      have hRS : TReach (wNode c.p base w') c.i w'.top.rootKey w.next :=
        TReach.link hRR ⟨_, hR, (mrg_newKlongs_liveAt_iff false c.i _ hnd r.1 w.next).mpr (by simp)⟩
      refine ⟨?_, Or.inl hRL, ?_, Or.inr (by rw [h'root]; omega)⟩
      · intro z hz hzL
        refine tReach_transport _ _ c.i w.top.rootKey w'.top.rootKey L _ (updN_self _ _ _)
          (fun h => absurd hrk h) ?_ ?_ z hz hzL
        · intro u c' z' _ hux _ hl _
          obtain ⟨m, hm, hc⟩ := hl
          obtain ⟨hm', hu⟩ := hVu u m hux hm
          have hu1 : u ≠ w.next := by omega
          have hu2 : u ≠ w.next + 2 := by omega
          refine ⟨m, ?_, hc⟩
          rw [hw']
          simp only [hux, hu1, hu2, ↓reduceIte]
          exact hm'
        · intro c' z' hc
          obtain ⟨hFc, hSc⟩ := hcov c' z' hc
          by_cases hlt' : c' < r.1
          · obtain ⟨c'', h''⟩ := hFc hlt'
            exact TReach.link hRL ⟨out.1, by rw [hw']; simp only [↓reduceIte], h''⟩
          · obtain ⟨c'', h''⟩ := hSc (by omega)
            exact TReach.link hRS ⟨out.2.1, by rw [hw']; simp only [hFx, ↓reduceIte], h''⟩
      · intro z hz hs
        have hzL : z ≠ L := by omega
        rw [h'n] at hs
        by_cases h1 : z = w.next
        · subst h1; exact hRS
        · by_cases h2 : z = w.next + 2
          · subst h2; exact hRR
          · simp only [hzL, h1, h2, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
              Bool.false_eq_true] at hs
    · -- the root space split: the halves and a new root
      refine writerWP_mono (writerWP_handleFullWith_rootSpaceSplit_nilV up L n last c w
        hlk hmade hsp hLn) ?_
      rintro _ w' ⟨⟨h't, h'root, h'n⟩, _⟩
      obtain ⟨out, hout⟩ : ∃ o, halves n.leaf c.i last [] = o := ⟨_, rfl⟩
      rw [hout] at h'n hdiv hcov
      rw [hdiv] at h'n hcov
      have hFx : ¬ w.next = L := by omega
      have hSx : ¬ w.next + 2 = L := by omega
      have hRx : ¬ w.next + 2 + 2 = L := by omega
      have hSF : ¬ w.next + 2 = w.next := by omega
      have hRF : ¬ w.next + 2 + 2 = w.next := by omega
      have hRS' : ¬ w.next + 2 + 2 = w.next + 2 := by omega
      have hw' : ∀ z, wNode c.p base w' z =
          if z = L then some (n.toPrev (c.i - 1))
          else if z = w.next then some out.1
          else if z = w.next + 2 then some out.2.1
          else if z = w.next + 2 + 2 then
            some ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩
          else wNode c.p base w z := by
        intro z
        by_cases h1 : z = L
        · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
        · by_cases h2 : z = w.next
          · subst h2; simp only [wNode, h't, htk0, h'n, h1, Bool.false_eq_true, ↓reduceIte]
          · by_cases h3 : z = w.next + 2
            · subst h3
              simp only [wNode, h't, htk2', h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
            · by_cases h4 : z = w.next + 2 + 2
              · subst h4
                simp only [wNode, h't, htk4, h'n, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
              · simp only [wNode, h't, h'n, h1, h2, h3, h4, ↓reduceIte]
      have hnd : ([(0, w.next), (r.1, w.next + 2)].map Prod.fst).Nodup := by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
        omega
      have hR : wNode c.p base w' (w.next + 2 + 2) =
          some ⟨false, newKlongs c.i [(0, w.next), (r.1, w.next + 2)]⟩ := by
        rw [hw']; simp only [hRx, hRF, hRS', ↓reduceIte]; rfl
      have hRR : TReach (wNode c.p base w') c.i w'.top.rootKey (w.next + 2 + 2) := by
        rw [h'root]; exact TReach.root
      have hRF1 : TReach (wNode c.p base w') c.i w'.top.rootKey w.next :=
        TReach.link hRR ⟨_, hR, (mrg_newKlongs_liveAt_iff false c.i _ hnd 0 w.next).mpr (by simp)⟩
      have hRS : TReach (wNode c.p base w') c.i w'.top.rootKey (w.next + 2) :=
        TReach.link hRR ⟨_, hR,
          (mrg_newKlongs_liveAt_iff false c.i _ hnd r.1 (w.next + 2)).mpr (by simp)⟩
      refine ⟨?_, Or.inr ⟨?_, ?_, hmade⟩, ?_, Or.inr (by rw [h'root]; omega)⟩
      · intro z hz hzL
        refine tReach_transport _ _ c.i w.top.rootKey w'.top.rootKey L _ (updN_self _ _ _)
          (fun h => absurd hrk h) ?_ ?_ z hz hzL
        · intro u c' z' _ hux _ hl _
          obtain ⟨m, hm, hc⟩ := hl
          obtain ⟨hm', hu⟩ := hVu u m hux hm
          have hu1 : u ≠ w.next := by omega
          have hu2 : u ≠ w.next + 2 := by omega
          have hu3 : u ≠ w.next + 2 + 2 := by omega
          refine ⟨m, ?_, hc⟩
          rw [hw']
          simp only [hux, hu1, hu2, hu3, ↓reduceIte]
          exact hm'
        · intro c' z' hc
          obtain ⟨hFc, hSc⟩ := hcov c' z' hc
          by_cases hlt' : c' < r.1
          · obtain ⟨c'', h''⟩ := hFc hlt'
            exact TReach.link hRF1 ⟨out.1, by rw [hw']; simp only [hFx, ↓reduceIte], h''⟩
          · obtain ⟨c'', h''⟩ := hSc (by omega)
            exact TReach.link hRS ⟨out.2.1, by rw [hw']; simp only [hSx, hSF, ↓reduceIte], h''⟩
      · rw [h'n]; simp only [↓reduceIte]
      · rw [hw']; simp only [↓reduceIte]
      · intro z hz hs
        have hzL : z ≠ L := by omega
        rw [h'n] at hs
        by_cases h1 : z = w.next
        · subst h1; exact hRF1
        · by_cases h2 : z = w.next + 2
          · subst h2; exact hRS
          · by_cases h3 : z = w.next + 2 + 2
            · subst h3; exact hRR
            · simp only [hzL, h1, h2, h3, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                Bool.false_eq_true] at hs
  · have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
      cases compact with
      | true => simp
      | false =>
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
        exact fun h => hsp ⟨h, rfl⟩
    by_cases hmade : n.firstTime = some c.i
    · -- the root time split in place
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV up 0 L n last compact c base hvc
        w hlk htk hmade hcs) ?_
      rintro _ w' ⟨h't, h'top, _, hN'⟩
      have hN'' : wNode c.p base w' = updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩ := by
        funext y; rw [hN' y]; rfl
      have hroot : w'.top.rootKey = w.top.rootKey := by rw [h'top]
      refine ⟨?_, Or.inl ?_, ?_, Or.inl hroot⟩
      · intro z hz _
        rw [hN'', hroot]; exact hz
      · rw [hroot, hrk]; exact TReach.root
      · intro z hz hs
        exfalso
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
        have h1 := hcached w' h't z m hz hm
        have hzL : z ≠ L := by omega
        rw [hN'] at h1
        simp only [hzL, ↓reduceIte, hwfree z hz] at h1
        cases h1
    · -- the root time split: a new root
      refine writerWP_mono (writerWP_handleFullWith_rootTimeSplit_nilV up L n last compact c w
        hlk hmade hcs hLn hfree0) ?_
      rintro _ w' ⟨⟨h't, h'root, h'n⟩, _⟩
      have hN' : wNode c.p base w' = updN (updN (wNode c.p base w) L
          (n.toPrev (c.i - 1))) w.next ⟨n.leaf, last.ks⟩ :=
        wNode_two_updN c.p base w w' _ _ _ _ h'n h't (by omega) htk htk0
      have hRR : TReach (wNode c.p base w') c.i w'.top.rootKey w.next := by
        rw [h'root]; exact TReach.root
      refine ⟨?_, Or.inr ⟨?_, ?_, hmade⟩, ?_, Or.inr (by rw [h'root]; exact Nat.le_refl _)⟩
      · intro z hz hzL
        refine tReach_transport _ _ c.i w.top.rootKey w'.top.rootKey L _ (updN_self _ _ _)
          (fun h => absurd hrk h) ?_ ?_ z hz hzL
        · intro u c' z' _ hux _ hl _
          obtain ⟨m, hm, hc⟩ := hl
          obtain ⟨hm', hu⟩ := hVu u m hux hm
          have hu1 : u ≠ w.next := by omega
          refine ⟨m, ?_, hc⟩
          rw [hN', updN_ne _ _ _ _ hu1, updN_ne _ _ _ _ hux]
          exact hm'
        · intro c' z' hc
          exact TReach.link hRR ⟨_, by rw [hN']; exact updN_self _ _ _, hc⟩
      · rw [h'n]; simp only [↓reduceIte]
      · rw [hN', updN_ne _ _ _ _ (by omega), updN_self]
      · intro z hz hs
        rw [h'n] at hs
        by_cases h1 : z = w.next
        · subst h1; exact hRR
        · have hzL : z ≠ L := by omega
          simp only [hzL, h1, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
            Bool.false_eq_true] at hs

/-- `writerWP_handleFull_rootVF` with the reach back (`writerWP_handleFull_rootReach`):
(8r) the nodes the tree with L's last version reaches, but L, are reached after;
(9r) L is reached after, or holds its klongs before the transaction; (10r) every
node cached from the next id on is reached after; and the root after is the root
before or a new node. -/
theorem writerWP_handleFull_rootVF2 (f : Nat) (hf2 : 2 ≤ f) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base)
    (up : NodeId → List (Nat × NodeId) → M Unit) (L : NodeId) (n last : KNode) (compact : Bool)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (w : W) (hlk : w.nodes.lookup L = some n) (htk : w.taken.contains L = false)
    (hrk : w.top.rootKey = L)
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hV : TreeOK (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ w'.taken = w.taken ∧ w'.vals = w.vals ∧
      (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
        TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey z ∨ w.next ≤ z) ∧
      (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
      (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ z = L) → Val z = none) →
        (SegFits (wNode c.p base w') c.i (f - 1) w'.top.rootKey ∨
          (!compact && decide (last.size > c.p.splitAbove)) = false) →
        ∀ key, getFromR (wNode c.p base w') Val c.i f key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) Val c.i f key w.top.rootKey) ∧
      (TReach (wNode c.p base w') c.i w'.top.rootKey L →
        ∀ m, wNode c.p base w' L = some m → ∀ cv y, Klong.key cv y ∈ m.ks → Klong.key cv y ∈ last.ks) ∧
      (∀ z, TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey z → z ≠ L →
        TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
      (TReach (wNode c.p base w') c.i w'.top.rootKey L ∨
        (w'.nodes.lookup L = some (n.toPrev (c.i - 1)) ∧
          wNode c.p base w' L = some (n.toPrev (c.i - 1)) ∧ n.firstTime ≠ some c.i)) ∧
      (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
        TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
      (w'.top.rootKey = w.top.rootKey ∨ w.next ≤ w'.top.rootKey)) := by
  refine writerWP_mono (writerWP_and
    (writerWP_handleFull_rootVF f hf2 c base hvc up L n last compact hlwf hlt hlastV hlen2 w hlk htk
      hrk hS5 hS6 hW hV hvx)
    (writerWP_handleFull_rootReach c base hvc up L n last compact hlwf hlt hlastV hlen2 w hlk htk
      hrk hS5)) ?_
  rintro _ w' ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## The shapes -/

set_option maxHeartbeats 4000000 in
/-- After `handleFull` at the space root L with the last version `last` (a time
klong and key klongs of distinct compare values), for the one-node chain X 0 = L,
Nn 0 = n: the next id grows, the nodes below it but L are kept, the ids from it
on are free, and every node from the next id on or at L has a cascade node's
shape (`ShapePost` from 0 with nothing put); the path is kept. With a property
`Bnd` of every node written, which each kind of node written has (the dead
klongs' bound, `writerWP_handleFull_rootDead`). -/
theorem writerWP_handleFull_rootShapeG (c : Ctx) (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hX0 : X 0 = L) (hN0 : Nn 0 = n)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (w : W) (hlk : w.nodes.lookup L = some n) (hLn : L < w.next)
    (hfr : ∀ z, w.next ≤ z → w.nodes.lookup z = none)
    (Bnd : KNode → Prop) (hBr : ∀ (a b : NodeId) (sc : Nat), 0 < sc →
      Bnd ⟨false, [Klong.time c.i, .key 0 a, .key sc b]⟩)
    (hBp0 : n.firstTime ≠ some c.i → Bnd (n.toPrev (c.i - 1)))
    (hBlast : ∀ lf, Bnd ⟨lf, last.ks⟩)
    (hBlh : Bnd (halves n.leaf c.i last []).1 ∧ Bnd (halves n.leaf c.i last []).2.1) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      ShapePostG Bnd c X K Nn 0 0 [] w w' ∧ w'.path = w.path) := by
  obtain ⟨pairs, hks, hnd⟩ := hpairs
  have hlt : ∀ t, Klong.time t ∈ last.ks → t ≤ c.i := by rw [hks]; exact newKlongs_times c.i pairs
  have hlsh : ∀ (lf : Bool) (P : NodeId → Prop), ShadowOK c.i ⟨lf, last.ks⟩ P := by
    intro lf P; rw [hks]; exact shadowOK_newKlongs c.i lf pairs hnd P
  have hzX : ∀ z, (∀ i, 0 ≤ i → i ≤ 0 → z ≠ X i) ↔ z ≠ L := by
    intro z
    constructor
    · intro h; have := h 0 (Nat.le_refl _) (Nat.le_refl _); rw [hX0] at this; exact this
    · intro h i _ hi
      have : i = 0 := by omega
      subst this; rw [hX0]; exact h
  have hzX' : ∀ z, (w.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ 0 ∧ z = X i) → w.next ≤ z ∨ z = L := by
    intro z h
    rcases h with h | ⟨i, _, hi, h⟩
    · exact Or.inl h
    · have : i = 0 := by omega
      subst this; rw [hX0] at h; exact Or.inr h
  -- a node made by the transaction, not on the chain
  have hnew : ∀ z zn, z ≠ L → ShadowOK c.i zn (ChainShadow c X Nn 0 0 []) →
      CascadeNodeShape c X K Nn 0 0 [] z zn := by
    intro z zn hzL hsh
    refine Or.inr (Or.inr (Or.inl ⟨hsh, fun i _ hi h => ?_⟩))
    have : i = 0 := by omega
    subst this; rw [hX0] at h; exact absurd h hzL
  -- the root L left as its klongs before the transaction
  have hprev : n.firstTime ≠ some c.i →
      CascadeNodeShape c X K Nn 0 0 [] L (n.toPrev (c.i - 1)) := by
    intro hf
    exact Or.inr (Or.inl ⟨0, Nat.le_refl _, Nat.le_refl _, hX0.symm, by rw [hN0], by rw [hN0]; exact hf⟩)
  -- the root L made by the transaction, with new klongs
  have hmadeL : n.firstTime = some c.i → ∀ zn, ShadowOK c.i zn (ChainShadow c X Nn 0 0 []) →
      CascadeNodeShape c X K Nn 0 0 [] L zn := by
    intro hf zn hsh
    refine Or.inr (Or.inr (Or.inl ⟨hsh, fun i _ hi _ => ?_⟩))
    have : i = 0 := by omega
    subst this; rw [hN0]; exact hf
  have hmono : ∀ (P : NodeId → Prop) zn, (∀ y, P y → False) → ShadowOK c.i zn P →
      ShadowOK c.i zn (ChainShadow c X Nn 0 0 []) :=
    fun P zn hP h => h.mono (fun y hy => absurd hy (fun h' => hP y h'))
  by_cases hsp : c.p.splitAbove < last.size ∧ compact = false
  · obtain ⟨hsp, hc⟩ := hsp
    subst hc
    have h2l := hlen2 hsp
    obtain ⟨hF0, hS0, hscpos0, _, _⟩ :=
      halves_node (⟨n.leaf, last.ks⟩ : KNode) c.i [] hlt h2l List.Pairwise.nil
    rw [hlastV] at hF0 hS0 hscpos0
    have hF : ShadowOK c.i (halves n.leaf c.i last []).1 (ChainShadow c X Nn 0 0 []) :=
      hmono _ _ (fun y hy => by obtain ⟨_, _, hc⟩ := hy; simp at hc) hF0
    have hS : ShadowOK c.i (halves n.leaf c.i last []).2.1 (ChainShadow c X Nn 0 0 []) :=
      hmono _ _ (fun y hy => by obtain ⟨_, _, hc⟩ := hy; simp at hc) hS0
    have hscpos : 0 < (halves n.leaf c.i last []).2.2 := hscpos0
    by_cases hmade : n.firstTime = some c.i
    · -- the root space split in place: the second half and a new root
      refine writerWP_mono (writerWP_and (writerWP_handleFullWith_rootSpaceSplitInPlace_nilV up L n
        last c w hlk hmade hsp hLn (hfr _ (by omega)))
        (writerWP_handleFullWith_rootSpaceSplitInPlace_next up L n last c w hlk hmade hsp)) ?_
      rintro _ w' ⟨⟨⟨_, _, h'n⟩, _⟩, h'next, h'path⟩
      refine ⟨⟨by omega, ?_, ?_, ?_⟩, h'path⟩
      · intro z hz hzx
        have hzL := (hzX z).mp hzx
        rw [h'n]
        have hne0 : z ≠ w.next := by omega
        have hne1 : z ≠ w.next + 2 := by omega
        simp only [hzL, hne0, hne1, ↓reduceIte]
      · intro z hz
        rw [h'n]
        have hne0 : z ≠ L := by omega
        have hne1 : z ≠ w.next := by omega
        have hne2 : z ≠ w.next + 2 := by omega
        simp only [hne0, hne1, hne2, ↓reduceIte]
        exact hfr z (by omega)
      · intro z zn h hz
        rw [h'n] at h
        by_cases h1 : z = L
        · subst h1
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨?_, hBlh.1⟩
          exact hmadeL hmade _ hF
        · by_cases h2 : z = w.next
          · subst h2
            simp only [h1, ↓reduceIte, Option.some.injEq] at h
            subst h
            refine ⟨?_, hBlh.2⟩
            exact hnew _ _ h1 hS
          · by_cases h3 : z = w.next + 2
            · subst h3
              simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBr _ _ _ hscpos⟩
              exact hnew _ _ h1 (shadowOK_root c.i _ _ _ hscpos _)
            · simp only [h1, h2, h3, ↓reduceIte] at h
              rcases hzX' z hz with hz' | hz'
              · rw [hfr z hz'] at h; cases h
              · exact absurd hz' h1
    · -- the root space split: the halves and a new root
      refine writerWP_mono (writerWP_and (writerWP_handleFullWith_rootSpaceSplit_nilV up L n
        last c w hlk hmade hsp hLn)
        (writerWP_handleFullWith_rootSpaceSplit_next up L n last c w hlk hmade hsp hLn)) ?_
      rintro _ w' ⟨⟨⟨_, _, h'n⟩, _⟩, h'next, h'path⟩
      refine ⟨⟨by omega, ?_, ?_, ?_⟩, h'path⟩
      · intro z hz hzx
        have hzL := (hzX z).mp hzx
        rw [h'n]
        have hne0 : z ≠ w.next := by omega
        have hne1 : z ≠ w.next + 2 := by omega
        have hne2 : z ≠ w.next + 2 + 2 := by omega
        simp only [hzL, hne0, hne1, hne2, ↓reduceIte]
      · intro z hz
        rw [h'n]
        have hne0 : z ≠ L := by omega
        have hne1 : z ≠ w.next := by omega
        have hne2 : z ≠ w.next + 2 := by omega
        have hne3 : z ≠ w.next + 2 + 2 := by omega
        simp only [hne0, hne1, hne2, hne3, ↓reduceIte]
        exact hfr z (by omega)
      · intro z zn h hz
        rw [h'n] at h
        by_cases h1 : z = L
        · subst h1
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨?_, hBp0 hmade⟩
          exact hprev hmade
        · by_cases h2 : z = w.next
          · subst h2
            simp only [h1, ↓reduceIte, Option.some.injEq] at h
            subst h
            refine ⟨?_, hBlh.1⟩
            exact hnew _ _ h1 hF
          · by_cases h3 : z = w.next + 2
            · subst h3
              simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBlh.2⟩
              exact hnew _ _ h1 hS
            · by_cases h4 : z = w.next + 2 + 2
              · subst h4
                simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, hBr _ _ _ hscpos⟩
                exact hnew _ _ h1 (shadowOK_root c.i _ _ _ hscpos _)
              · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                rcases hzX' z hz with hz' | hz'
                · rw [hfr z hz'] at h; cases h
                · exact absurd hz' h1
  · have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
      cases compact with
      | true => simp
      | false =>
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
        exact fun h => hsp ⟨h, rfl⟩
    by_cases hmade : n.firstTime = some c.i
    · -- the root time split in place
      refine writerWP_mono (writerWP_handleFullWith_rootTimeInPlace_nodes up L n last compact c w
        hlk hmade hcs) ?_
      rintro _ w' ⟨h'next, h'path, h'n⟩
      refine ⟨⟨by omega, ?_, ?_, ?_⟩, h'path⟩
      · intro z _ hzx
        have hzL := (hzX z).mp hzx
        rw [h'n, lookup_upsert]
        simp only [hzL, ↓reduceIte]
      · intro z hz
        rw [h'next] at hz
        rw [h'n, lookup_upsert]
        have hne0 : z ≠ L := by omega
        simp only [hne0, ↓reduceIte]
        exact hfr z hz
      · intro z zn h hz
        rw [h'n, lookup_upsert] at h
        by_cases h1 : z = L
        · subst h1
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨?_, hBlast _⟩
          exact hmadeL hmade _ (hlsh _ _)
        · simp only [h1, ↓reduceIte] at h
          rcases hzX' z hz with hz' | hz'
          · rw [hfr z hz'] at h; cases h
          · exact absurd hz' h1
    · -- the root time split: a new root
      refine writerWP_mono (writerWP_and (writerWP_handleFullWith_rootTimeSplit_nilV up L n last
        compact c w hlk hmade hcs hLn (hfr _ (Nat.le_refl _)))
        (writerWP_handleFullWith_rootTimeSplit_next up L n last compact c w hlk hmade hcs)) ?_
      rintro _ w' ⟨⟨⟨_, _, h'n⟩, _⟩, h'next, h'path⟩
      refine ⟨⟨by omega, ?_, ?_, ?_⟩, h'path⟩
      · intro z hz hzx
        have hzL := (hzX z).mp hzx
        rw [h'n]
        have hne0 : z ≠ w.next := by omega
        simp only [hzL, hne0, ↓reduceIte]
      · intro z hz
        rw [h'n]
        have hne0 : z ≠ L := by omega
        have hne1 : z ≠ w.next := by omega
        simp only [hne0, hne1, ↓reduceIte]
        exact hfr z (by omega)
      · intro z zn h hz
        rw [h'n] at h
        by_cases h1 : z = L
        · subst h1
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨?_, hBp0 hmade⟩
          exact hprev hmade
        · by_cases h2 : z = w.next
          · subst h2
            simp only [h1, ↓reduceIte, Option.some.injEq] at h
            subst h
            refine ⟨?_, hBlast _⟩
            exact hnew _ _ h1 (hlsh _ _)
          · simp only [h1, h2, ↓reduceIte] at h
            rcases hzX' z hz with hz' | hz'
            · rw [hfr z hz'] at h; cases h
            · exact absurd hz' h1

set_option maxHeartbeats 4000000 in
/-- After `handleFull` at the space root L with the last version `last` (a time
klong and key klongs of distinct compare values), for the one-node chain X 0 = L,
Nn 0 = n: the next id grows, the nodes below it but L are kept, the ids from it
on are free, and every node from the next id on or at L has a cascade node's
shape (`ShapePost` from 0 with nothing put); the path is kept. -/
theorem writerWP_handleFull_rootShape (c : Ctx) (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hX0 : X 0 = L) (hN0 : Nn 0 = n)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (w : W) (hlk : w.nodes.lookup L = some n) (hLn : L < w.next)
    (hfr : ∀ z, w.next ≤ z → w.nodes.lookup z = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      ShapePost c X K Nn 0 0 [] w w' ∧ w'.path = w.path) := by
  refine writerWP_mono (writerWP_handleFull_rootShapeG c up L n last compact X K Nn hX0 hN0 hpairs
    hlastV hlen2 w hlk hLn hfr (fun _ => True) (fun _ _ _ _ => trivial) (fun _ => trivial)
    (fun _ => trivial) ⟨trivial, trivial⟩) ?_
  intro _ _ ⟨⟨a, b, d, f⟩, hp⟩
  exact ⟨⟨a, b, d, fun z zn h hz => (f z zn h hz).1⟩, hp⟩

/-- The dead klongs' bound of the space root's split with a last version given
(bergdb 024-12, `QDead` of (4)): with theta 0 or at least 2, every node written
holds at most theta dead klongs when the root does. -/
theorem writerWP_handleFull_rootDead (c : Ctx) (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hX0 : X 0 = L) (hN0 : Nn 0 = n)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (w : W) (hlk : w.nodes.lookup L = some n) (hLn : L < w.next)
    (hfr : ∀ z, w.next ≤ z → w.nodes.lookup z = none)
    (hdn : c.p.theta ≠ 0 → n.deadCount ≤ c.p.theta) (hwn : klongsWf n.ks = true) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      ShapePostG (fun m => c.p.theta ≠ 0 → m.deadCount ≤ c.p.theta) c X K Nn 0 0 [] w w' ∧
        w'.path = w.path) := by
  obtain ⟨pairs, hks, hnd⟩ := hpairs
  have hlv : (⟨n.leaf, last.ks⟩ : KNode).lastVersionGivenDel c.i
      (⟨n.leaf, last.ks⟩ : KNode).lastBitmap = last := hlastV
  have hh := halves_normalized_deadCount_le (⟨n.leaf, last.ks⟩ : KNode) c.i
    (⟨n.leaf, last.ks⟩ : KNode).lastBitmap []
  rw [hlv] at hh
  exact writerWP_handleFull_rootShapeG c up L n last compact X K Nn hX0 hN0 ⟨pairs, hks, hnd⟩
    hlastV hlen2 w hlk hLn hfr (fun m => c.p.theta ≠ 0 → m.deadCount ≤ c.p.theta)
    (fun a b sc hsc _ => by rw [KNode.deadCount_newRoot c.i a b sc hsc]; exact Nat.zero_le _)
    (fun _ h0 => Nat.le_trans (KNode.deadCount_toPrev_le n _ hwn) (hdn h0))
    (fun lf _ => by
      have h1 := KNode.newKlongs_deadCount lf c.i pairs hnd
      have h2 : (⟨lf, last.ks⟩ : KNode).deadCount = 0 := by rw [hks]; exact h1
      omega)
    ⟨fun _ => by have := hh.1; simp at this; omega, fun _ => by have := hh.2; simp at this; omega⟩

end SIS.Tree
