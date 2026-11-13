/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsMerge.lean:
the merges after a delete, the delete (`deleteUpward`), a put, and a
transaction (`execW_kinds`).
-/
import SIS.Tree.RootWalkMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The merges after a delete -/

theorem kr_mergeUp (K : KindOracle) (B : NodeId) (key : Key) (g fuel : Nat) :
    ∀ (h : Nat) (merged : Bool) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c →
      Book B c w → KrInv K B w →
      WriterWP (mergeUp key g fuel h merged) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  induction fuel with
  | zero => intro h merged c w _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged c w hv hk hb hi
    unfold mergeUp
    krSimp
    refine writerWP_mono (kr_descendToHeight K B key g h c w hv hk hb hi) ?_
    rintro d w1 ⟨hb1, hi1, hle1⟩
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
    · rename_i hd0
      have hd : d ≠ 0 := by intro h0; subst h0; exact hd0 rfl
      krSimp
      refine writerWP_mono (kr_pathNode d c w1) ?_
      rintro x w2 ⟨hw, ax, hpx⟩
      rw [hw]
      refine writerWP_mono (kr_pathNode (d - 1) c w1) ?_
      rintro q w3 ⟨hw3, aq, hpq⟩
      rw [hw3]
      refine writerWP_mono (kr_getNode K B q c w1 hv hk hb1 hi1) ?_
      rintro nq w4 ⟨hb4, hi4, hle4, hl4, hp4, -⟩
      split
      · rw [writerWP_pure]; exact ⟨hb4, hi4, hle1.trans hle4⟩
      · rename_i hql
        krSimp
        refine writerWP_mono (kr_getNode K B x c w4 hv hk hb4 hi4) ?_
        rintro nx w5 ⟨hb5, hi5, hle5, hl5, hp5, -⟩
        split
        · rw [writerWP_pure]; exact ⟨hb5, hi5, hle1.trans (hle4.trans hle5)⟩
        · krSimp
          have hpw : w5.path = w1.path := hp5.trans hp4
          refine writerWP_mono (kr_merge K B x d c w5 hv hk hb5 hi5 hd ax
            (by rw [hpw]; exact hpx) ?_) ?_
          · intro a q' hq'
            rw [hpw, hpq] at hq'
            simp only [Option.some.injEq, Prod.mk.injEq] at hq'
            obtain ⟨-, rfl⟩ := hq'
            obtain ⟨n', hn', hl'⟩ := hle5.1.lookup hl4
            refine ⟨n', hn', ?_⟩
            rw [hl']
            cases hnl : nq.leaf
            · rfl
            · exact absurd hnl hql
          · rintro r w6 ⟨hb6, hi6, hle6, -⟩
            have hle := hle1.trans (hle4.trans (hle5.trans hle6))
            split
            · rw [writerWP_pure]; exact ⟨hb6, hi6, hle⟩
            · exact writerWP_mono (ih (h + 1) true c w6 hv hk hb6 hi6)
                (fun _ u hu => ⟨hu.1, hu.2.1, hle.trans hu.2.2⟩)

theorem kr_afterDelete (K : KindOracle) (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KrInv K B w) :
    WriterWP (afterDelete key g h) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  unfold afterDelete
  krSimp
  split
  · krSimp
    refine writerWP_mono (kr_mergeUp K B key g c.p.fuel h false c w hv hk hb hi) ?_
    rintro r w1 ⟨hb1, hi1, hle1⟩
    split
    · exact writerWP_mono (kr_collapseRoot K B key g c.p.fuel c w1 hv hk hb1 hi1)
        (fun _ u hu => ⟨hu.1, hu.2.1, hle1.trans hu.2.2⟩)
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
  · rw [writerWP_pure]; exact ⟨hb, hi, KrLe.refl w⟩

/-! ## The delete -/

theorem kr_foldlM4 (K : KindOracle) (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β)
    (hf : ∀ b a, KrKeepsP K B (f b a)) : ∀ init, KrKeepsP K B (xs.foldlM f init) := by
  induction xs with
  | nil =>
    intro init c w _ _ hb hi
    simp only [List.foldlM_nil, writerWP_pure]
    exact ⟨hb, hi, KrLe.refl w, by trivial⟩
  | cons a xs ih =>
    intro init c w hv hk hb hi
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a c w hv hk hb hi) ?_
    rintro b v ⟨h1, h2, h3, h4⟩
    exact writerWP_mono (ih b c v hv hk h1 h2)
      (fun _ u h => ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2.trans h4⟩)

theorem kr_forIn (K : KindOracle) (B : NodeId) {α β : Type} (xs : List α)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KrKeepsP K B (f a b)) :
    ∀ init, KrKeepsP K B (forIn xs init f) := by
  induction xs with
  | nil =>
    intro init c w _ _ hb hi
    simp only [List.forIn_nil, writerWP_pure]
    exact ⟨hb, hi, KrLe.refl w, by trivial⟩
  | cons a xs ih =>
    intro init c w hv hk hb hi
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hk hb hi) ?_
    rintro step v ⟨h1, h2, h3, h4⟩
    cases step with
    | done b => simp only [writerWP_pure]; exact ⟨h1, h2, h3, h4⟩
    | yield b =>
      exact writerWP_mono (ih b c v hv hk h1 h2)
        (fun _ u h => ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2.trans h4⟩)

macro "krPN" : tactic => `(tactic| first
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (kr_pathNode _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
     refine writerWP_mono (kr_klongAt _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _, _⟩
     subst hkdEq))

macro "krTB" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takeBack _ _ _) _ _ _)
  (refine writerWP_mono (kr_takeBack ?krK ?krB _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ _ (by krTag)) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

macro "krADK" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (appendDeleteKlong _ _ _) _ _ _)
  (refine writerWP_mono (kr_appendDeleteKlong ?krK ?krB _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ (kr_path_at (by assumption) (by krPathEq))) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

theorem kr_h_ne2 {v1 v2 : W} {s : NodeId} {sn n : KNode} {h : Nat} (hn : n.leaf = (h == 0))
    (hl2 : v2.nodes.lookup s = some n) (hf : ¬ sn.leaf = true) (hl1 : v1.nodes.lookup s = some sn)
    (hk : KrLe v1 v2) : h ≠ 0 := by
  obtain ⟨n', hn', hl'⟩ := hk.1.lookup hl1
  rw [hl2] at hn'
  cases hn'
  intro h0
  subst h0
  simp at hn
  rw [hl'] at hn
  exact hf hn

macro "krLEB" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (emptyKeyNext _ _) _ _ _)
  (refine writerWP_mono (kr_emptyKeyNext ?krK ?krB _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ (kr_path_at (by assumption) (by krPathEq)) _ _ (by krTag) (kr_h_ne2 (by assumption) (by assumption) (by assumption) (by assumption) (by krChain))) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

/-- A step whose path may change. -/
macro "krUse3 " h:term : tactic => `(tactic| (
  (refine' writerWP_mono ($h _ _ ?krView ?krKinds ?krBook ?krInv) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _⟩))

/-- The end of a walk whose path may change. -/
macro "krDone3" : tactic => `(tactic| (
  (with_unfolding_none guard_target = Book _ _ _ ∧ KrInv _ _ _ ∧ KrLe _ _)
  exact ⟨by krState, by assumption, by krChain⟩))

macro "krFold" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (List.foldlM _ _ _) _ _ _)
  (refine krP_writerWP (kr_foldlM4 ?krK ?krB _ _ ?krHf _) _ _ _ ?krView ?krKinds ?krBook ?krInv ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krHf => (intro _ _ c w hv hk hb hi; repeat' first | krSimp | krCore | wpSplit | split | contradiction)
  intro _ _ _ _ _ _))

macro "krFor" : tactic => `(tactic| (
  (refine krP_writerWP (kr_forIn ?krK ?krB _ _ ?krHf _) _ _ _ ?krView ?krKinds ?krBook ?krInv ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krHf => (intro _ _ c w hv hk hb hi; repeat' first | krSimp | krPN | krTB | krUseP (kr_unlink _ _ _) | krCore | wpSplit | split | contradiction)
  intro _ _ _ _ _ _))

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 20000 in
/-- The delete in the segment leaf `leaf`, the path's node at `depth`. -/
theorem kr_deleteUpward (K : KindOracle) (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, leaf)) :
    WriterWP (deleteUpward leaf depth cv key) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  unfold deleteUpward
  repeat' first
    | krSimp
    | krDone3
    | krPN
    | krTB
    | krADK
    | krLEB
    | krUse3 (kr_afterDelete _ _ _ _ _)
    | krUse3 (kr_mergeUp _ _ _ _ _ _ _)
    | krUse3 (kr_collapseRoot _ _ _ _ _)
    | krUseP (kr_climb _ _ _)
    | krUseP (kr_unlink _ _ _)
    | krFold
    | krFor
    | krCore
    | wpSplit
    | split
    | contradiction

/-! ## A put -/

theorem kr_newValue_nodes (h : Nat) (c : Ctx) (w : W) :
    WriterWP (newValue h) c w (fun _ v => v.nodes = w.nodes ∧ v.path = w.path) := by
  unfold newValue fresh
  simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
  exact ⟨trivial, trivial⟩

theorem kr_putNode_other (x : NodeId) (n' n0 : KNode) (c : Ctx) (w : W)
    (hl : w.nodes.lookup x = some n0) :
    WriterWP (putNode x n') c w (fun _ v => ∀ y, y ≠ x → v.nodes.lookup y = w.nodes.lookup y) := by
  simp only [putNode, writerWP_modify]
  intro y hy
  show (upsert w.nodes x n').lookup y = _
  rw [bk_lookup_upsert _ x y n' n0 hl]
  simp [hy]

theorem kr_empty_ok (p : Params) (hM : 2 ≤ p.M) (t : Time) (cv : Nat) (y : NodeId) :
    ((⟨true, []⟩ : KNode).size + 1 < p.M && !deadOver p ((⟨true, []⟩ : KNode).add t (.key cv y))) = true := by
  have h1 := nex_run_deadOver_nil p ⟨true, []⟩ t cv y rfl
  have h2 : (⟨true, []⟩ : KNode).size + 1 < p.M := by show 0 + 1 < p.M; omega
  rw [h1, Bool.not_false, Bool.and_true]
  exact decide_eq_true h2

theorem kr_empty_lt (p : Params) (hM : 2 ≤ p.M) : (⟨true, []⟩ : KNode).size + 1 < p.M := by
  show 0 + 1 < p.M; omega

/-- The value's klong in the segment leaf: a value, of a last segment. -/
theorem kr_leaf_val {K : KindOracle} {w : W} {g h cv : Nat} {v : NodeId} (hh : h = 0)
    (hcv : segLen cv ≠ 7) (hv : IsValId K w v) : KindKlong K w g h cv v :=
  ⟨fun h0 => absurd hh h0, fun _ => ⟨fun h7 => absurd h7 hcv, fun _ => hv⟩⟩

/-- The new segment leaf's klong: a key node of the next segment, of a segment
before the last. -/
theorem kr_leaf_child {K : KindOracle} {w : W} {g h cv : Nat} {y : NodeId} (hh : h = 0)
    (hcv : segLen cv = 7) (hy : IsKeySeg K w y (g + 1)) : KindKlong K w g h cv y :=
  ⟨fun h0 => absurd hh h0, fun _ => ⟨fun _ => hy, fun h7 => absurd hcv h7⟩⟩

theorem kr_h0 {B : NodeId} {c : Ctx} {w : W} {x : NodeId} {n : KNode} {g h : Nat}
    (hb : Book B c w) (hl : w.nodes.lookup x = some n) (hm : (x, g, h) ∈ w.gh)
    (hleaf : n.leaf = true) : h = 0 := by
  have := kr_leaf hb hl hm
  rw [hleaf] at this
  cases h with
  | zero => rfl
  | succ k => exact absurd this (by simp)

set_option maxHeartbeats 1600000 in
/-- `setValue` from segRoot, the path's last node, or (a put) an empty segment
leaf off the path. -/
theorem kr_setValue (K : KindOracle) (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key)
    (value : Option Nat) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KrInv K B w) (hM : 2 ≤ c.p.M)
    (hr : KrPathLast w segRoot ∨ (value.isSome = true ∧ w.nodes.lookup segRoot = some ⟨true, []⟩))
    (hcv : value.isSome = true → segLen cv ≠ 7) :
    WriterWP (setValue segRoot cv key value) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  unfold setValue
  krSimp
  refine writerWP_mono (kr_descendLte K B cv c.p.fuel segRoot c w hv hk hb hi
    (hr.imp id (fun h => h.2))) ?_
  rintro leaf w1 ⟨hb1, hi1, hle1, hlast, n0, hl0, hleaf0⟩
  obtain ⟨g, hh, hm⟩ := kr_tag_of_lookup hb1 hl0
  have hh0 : hh = 0 := kr_h0 hb1 hl0 hm hleaf0
  subst hh0
  cases value with
  | none =>
    have hl1 : KrPathLast w1 leaf := by
      rcases hlast with h1 | ⟨rfl, hp, -⟩
      · exact h1
      · rcases hr with ⟨a, ha⟩ | ⟨hf, -⟩
        · exact ⟨a, by rw [hp]; exact ha⟩
        · cases hf
    obtain ⟨a, ha⟩ := hl1
    krSimp
    refine writerWP_mono (kr_pathSize c w1) ?_
    rintro sz w2 ⟨hw, hsz⟩
    rw [hw, hsz]
    refine writerWP_mono (kr_deleteUpward K B leaf _ cv key c w1 hv hk hb1 hi1 a ha) ?_
    rintro noop w3 ⟨hb3, hi3, hle3⟩
    split
    · krSimp
      refine writerWP_mono (kr_fresh K B c w3 hv hk hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle3.trans hle4)⟩
    · rw [writerWP_pure]
      exact ⟨hb3, hi3, hle1.trans hle3⟩
  | some h =>
    have hcv' := hcv rfl
    krSimp
    refine writerWP_mono (writerWP_and (kr_newValue K B h c w1 hv hb1 hi1)
      (kr_newValue_nodes h c w1)) ?_
    rintro y w2 ⟨⟨hb2, hi2, hle2, hp2, -, hval⟩, hn2, -⟩
    have hkl2 : KindKlong K w2 g 0 cv y := kr_leaf_val rfl hcv' hval
    have hm2 := KrLe.gh' hm hle2
    rcases hlast with ⟨a, ha⟩ | ⟨rfl, hp1, he⟩
    · refine writerWP_mono (kr_getNode K B leaf c w2 hv hk hb2 hi2) ?_
      rintro n w3 ⟨hb3, hi3, hle3, hl3, hp3, -⟩
      have hm3 := KrLe.gh' hm2 hle3
      have hkl : KindKlong K w3 g 0 cv y := hkl2.krMono hle3
      split
      · krSimp
        refine writerWP_mono (kr_putNode K B leaf _ c w3 hb3 hi3 n hl3 (KNode.add_leaf _ _ _) g 0 hm3
          (krKs_add_key _ (kr_cache_node hi3 hl3 hm3) hkl)) ?_
        rintro _ w4 ⟨hb4, hi4, hle4, -⟩
        exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4))⟩
      · krSimp
        refine writerWP_mono (kr_pathSize c w3) ?_
        rintro sz w4 ⟨hw, hsz⟩
        rw [hw, hsz]
        refine writerWP_mono (kr_appendKlongs K B _ leaf [(cv, y)] c w3 hv hk hb3 hi3
          ⟨g, 0, hm3, krPairs_cons hkl krPairs_nil'⟩ ⟨a, by rw [hp3, hp2]; exact ha⟩) ?_
        rintro _ w5 ⟨hb5, hi5, hle5, -⟩
        exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle3.trans hle5))⟩
    · have he2 : w2.nodes.lookup leaf = some ⟨true, []⟩ := by rw [hn2]; exact he
      refine writerWP_mono (kr_getNode_hit leaf _ c w2 he2) ?_
      rintro n w3 ⟨hn3, hw3⟩
      rw [hn3, hw3]
      split
      · krSimp
        refine writerWP_mono (kr_putNode K B leaf _ c w2 hb2 hi2 _ he2 (KNode.add_leaf _ _ _) g 0 hm2
          (krKs_add_key _ (kr_cache_node hi2 he2 hm2) hkl2)) ?_
        rintro _ w4 ⟨hb4, hi4, hle4, -⟩
        exact ⟨hb4, hi4, hle1.trans (hle2.trans hle4)⟩
      · rename_i hfull
        exact absurd (kr_empty_ok c.p hM c.i cv y) hfull

/-- Every node of the key access path is a key node of the overlay when its
last node is. -/
theorem kr_path_in_gh {K : KindOracle} {B : NodeId} {w : W} (hi : KrInv K B w) {x : NodeId}
    (hpl : KrPathLast w x) (hx : x ∈ w.gh.map (·.1)) : ∀ e ∈ w.path, e.2 ∈ w.gh.map (·.1) := by
  intro e he
  obtain ⟨d, hd⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨a, ha⟩ := hpl
  have hlt := (List.getElem?_eq_some_iff.mp hd).1
  by_cases hd1 : d + 1 < w.path.length
  · obtain ⟨a', q⟩ := e
    exact hi.pathGh d a' q hd hd1
  · have : d = w.path.length - 1 := by omega
    subst this
    rw [ha] at hd
    cases hd
    exact hx

set_option maxHeartbeats 1600000 in
/-- `setNode` from segRoot, the path's last node, or (a put) an empty segment
leaf off the path: the tree of the next segment, the path's last node, or a new
empty segment leaf off the path. -/
theorem kr_setNode (K : KindOracle) (B : NodeId) (hframe : AppendFrameOK B) (segRoot : NodeId)
    (cv : Nat) (create : Bool) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds K B c) (hb : Book B c w) (hi : KrInv K B w) (hM : 2 ≤ c.p.M)
    (hr : KrPathLast w segRoot ∨ (create = true ∧ w.nodes.lookup segRoot = some ⟨true, []⟩))
    (hcv : create = true → segLen cv = 7) :
    WriterWP (setNode segRoot cv create) c w (fun r v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧
      ∀ y, r = some y → KrPathLast v y ∨ (create = true ∧ v.nodes.lookup y = some ⟨true, []⟩)) := by
  unfold setNode
  krSimp
  refine writerWP_mono (kr_descendLte K B cv c.p.fuel segRoot c w hv hk hb hi
    (hr.imp id (fun h => h.2))) ?_
  rintro cur w1 ⟨hb1, hi1, hle1, hlast, n0, hl0, hleaf0⟩
  obtain ⟨g, hh, hm⟩ := kr_tag_of_lookup hb1 hl0
  have hh0 : hh = 0 := kr_h0 hb1 hl0 hm hleaf0
  subst hh0
  have hcase : KrPathLast w1 cur ∨ (create = true ∧ n0 = ⟨true, []⟩) := by
    rcases hlast with h1 | ⟨hcr, hp, he⟩
    · exact Or.inl h1
    · subst hcr
      rcases hr with ⟨a, ha⟩ | ⟨hc, -⟩
      · exact Or.inl ⟨a, by rw [hp]; exact ha⟩
      · right
        refine ⟨hc, ?_⟩
        rw [hl0] at he
        exact Option.some.inj he
  refine writerWP_mono (kr_getNode_hit cur n0 c w1 hl0) ?_
  rintro n w2 ⟨hn, hw⟩
  rw [hn, hw]
  split
  · rename_i fd hfd
    rcases hcase with ⟨a, ha⟩ | ⟨-, hn0⟩
    · krSimp
      refine writerWP_mono (kr_pathAdd K B fd.c fd.y c w1 hv hb1 hi1 a cur g 0 ha hm
        (kr_cache_node hi1 hl0 hm _ _ (kr_searchEq_mem n0 c.i cv fd hfd))) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3, -⟩
      refine ⟨hb3, hi3, hle1.trans hle3, ?_⟩
      intro y hy
      cases hy
      left
      exact ⟨some fd.c, by rw [hp3]; exact kr_pathLast_append _ _⟩
    · subst hn0
      rw [nex_run_searchEq_nil _ _ _ rfl] at hfd
      cases hfd
  · split
    · rw [writerWP_pure]
      exact ⟨hb1, hi1, hle1, fun y hy => by cases hy⟩
    · rename_i hcr
      have hc : create = true := by cases create <;> simp_all
      have h7 := hcv hc
      krSimp
      refine writerWP_mono (kr_ghOf K B cur c w1 hv hk hb1 hi1) ?_
      rintro ⟨g', h'⟩ w3 ⟨hb3, hi3, hle3, hp3, -, hm3, -⟩
      obtain ⟨hg', hh'⟩ := kr_tag_eq hb3 (KrLe.gh' hm hle3) hm3
      subst hg'
      subst hh'
      krSimp
      refine writerWP_mono (kr_note K B _ c w3 hv hk hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
      have hcg4 : cur ∈ w4.gh.map (·.1) := kr_mem_ids (KrLe.gh' hm (hle3.trans hle4))
      refine writerWP_mono (kr_newKey K B (g + 1) 0 true [] c w4 hb4 hi4 rfl (krKs_nil _)) ?_
      rintro child w5 ⟨hb5, hi5, hle5, hp5, -, hlc, hmc, hcx⟩
      have hnot : ∀ q ∈ w4.gh.map (·.1), q ≠ child := by
        intro q hq hqc
        rw [hqc, hcx] at hq
        exact kr_next_not hb4 hq
      have hcur : cur ≠ child := hnot cur hcg4
      have hkl : KindKlong K w5 g 0 cv child := kr_leaf_child rfl h7 (kr_isKey hmc)
      have hle15 : KrLe w1 w5 := hle3.trans (hle4.trans hle5)
      obtain ⟨n5, hl5, hlf5⟩ := hle15.1.lookup hl0
      have hm5 := KrLe.gh' hm hle15
      have hks : krKs (KindKlong K w5 g 0) (n0.add c.i (.key cv child)).ks :=
        krKs_add_key _ (kr_cache_at hl0 hi1 hm hle15) hkl
      split
      · krSimp
        refine writerWP_mono (writerWP_and (kr_putNode K B cur _ c w5 hb5 hi5 n5 hl5
          ((KNode.add_leaf _ _ _).trans hlf5.symm) g 0 hm5 hks) (kr_putNode_other cur _ n5 c w5 hl5)) ?_
        rintro _ w6 ⟨⟨hb6, hi6, hle6, -⟩, hoth⟩
        refine ⟨hb6, hi6, hle15.trans hle6 |> hle1.trans, ?_⟩
        intro y hy
        cases hy
        right
        exact ⟨hc, by rw [hoth child (Ne.symm hcur)]; exact hlc⟩
      · rename_i hfull
        have hpl : KrPathLast w1 cur := by
          rcases hcase with h1 | ⟨-, hn0⟩
          · exact h1
          · subst hn0
            exact absurd (kr_empty_lt c.p hM) hfull
        obtain ⟨a, ha⟩ := hpl
        have hpw : w5.path = w1.path := hp5.trans (hp4.trans hp3)
        have hpath : ∀ e ∈ w5.path, e.2 ≠ child := by
          intro e he
          rw [hpw] at he
          have := kr_path_in_gh hi1 ⟨a, ha⟩ (kr_mem_ids hm) e he
          exact hnot _ (by
            obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
            exact List.mem_map.mpr ⟨q, KrLe.gh' hq (hle3.trans hle4), hqe⟩)
        krSimp
        refine writerWP_mono (kr_pathSize c w5) ?_
        rintro sz w6 ⟨hw6, hsz⟩
        rw [hw6, hsz]
        refine writerWP_mono (writerWP_and (kr_appendKlongs K B _ cur [(cv, child)] c w5 hv hk hb5 hi5
          ⟨g, 0, hm5, krPairs_cons hkl krPairs_nil'⟩ ⟨a, by rw [hpw]; exact ha⟩)
          (hframe _ cur [(cv, child)] c w5 child hv hb5 hlc (Ne.symm hcur) hpath)) ?_
        rintro _ w7 ⟨⟨hb7, hi7, hle7, -⟩, hlc7⟩
        exact ⟨hb7, hi7, hle1.trans (hle15.trans hle7), fun y hy => by
          cases hy; exact Or.inr ⟨hc, hlc7⟩⟩

/-- The segments of a key as `Keys.toSegments` makes them: every segment but
the last has 7 bytes, the last has fewer. -/
def KrSegs : List Nat → Prop
  | [] => False
  | [c] => segLen c ≠ 7
  | c :: r => segLen c = 7 ∧ KrSegs r

theorem kr_segs_of_keyWf : ∀ key, keyWf key = true → KrSegs key
  | [], h => by simp [keyWf] at h
  | [c], h => by
    simp only [keyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact h.2
  | c :: d :: r, h => by
    simp only [keyWf, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.2, kr_segs_of_keyWf (d :: r) h.2⟩

/-- The loop of a put or a delete over the key's segments. -/
theorem kr_putSegs (K : KindOracle) (B : NodeId) (hframe : AppendFrameOK B) (key : Key)
    (value : Option Nat) (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w →
      KrInv K B w → 2 ≤ c.p.M → KrSegs segs →
      (KrPathLast w r ∨ (value.isSome = true ∧ w.nodes.lookup r = some ⟨true, []⟩)) →
      WriterWP (putSegs key value segs r) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  induction segs with
  | nil => intro r c w _ _ _ _ _ hs _; cases hs
  | cons cv rest ih =>
    intro r c w hv hk hb hi hM hs hr
    cases rest with
    | nil =>
      unfold putSegs
      exact kr_setValue K B r cv key value c w hv hk hb hi hM hr (fun _ => hs)
    | cons d rest' =>
      unfold putSegs
      krSimp
      refine writerWP_mono (kr_setNode K B hframe r cv value.isSome c w hv hk hb hi hM hr
        (fun _ => hs.1)) ?_
      rintro res w1 ⟨hb1, hi1, hle1, hres⟩
      split
      · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
      · rename_i next
        exact writerWP_mono (ih next c w1 hv hk hb1 hi1 hM hs.2 (hres next rfl))
          (fun _ u hu => ⟨hu.1, hu.2.1, hle1.trans hu.2.2⟩)

/-- One operation. -/
theorem kr_putKv (K : KindOracle) (B : NodeId) (hframe : AppendFrameOK B) (op : Op) (c : Ctx)
    (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (hM : 2 ≤ c.p.M) (hkey : keyWf op.key = true) :
    WriterWP (putKv op) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  unfold putKv
  krSimp
  refine writerWP_mono (kr_pathClear K B c w hv hb hi) ?_
  rintro _ w1 ⟨hb1, hi1, hle1, hp1, -⟩
  refine writerWP_mono (kr_findRoot K B c w1 hv hb1 hi1 hp1) ?_
  rintro root w2 ⟨hb2, hi2, hle2, hp2, -⟩
  have hl : KrPathLast w2 root := ⟨none, by rw [hp2]; rfl⟩
  cases op with
  | put key h =>
    exact writerWP_mono (kr_putSegs K B hframe key (some h) key root c w2 hv hk hb2 hi2 hM
      (kr_segs_of_keyWf key hkey) (Or.inl hl))
      (fun _ u hu => ⟨hu.1, hu.2.1, hle1.trans (hle2.trans hu.2.2)⟩)
  | del key =>
    exact writerWP_mono (kr_putSegs K B hframe key none key root c w2 hv hk hb2 hi2 hM
      (kr_segs_of_keyWf key hkey) (Or.inl hl))
      (fun _ u hu => ⟨hu.1, hu.2.1, hle1.trans (hle2.trans hu.2.2)⟩)

/-- The operations of a transaction. -/
theorem kr_ops (K : KindOracle) (B : NodeId) (hframe : AppendFrameOK B) (ops : List Op) :
    ∀ (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KrInv K B w →
      2 ≤ c.p.M → (∀ op ∈ ops, keyWf op.key = true) →
      WriterWP (ops.mapM putKv) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  induction ops with
  | nil =>
    intro c w _ _ hb hi _ _
    simp only [List.mapM_nil, writerWP_pure]
    exact ⟨hb, hi, KrLe.refl w⟩
  | cons op ops ih =>
    intro c w hv hk hb hi hM hkeys
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (kr_putKv K B hframe op c w hv hk hb hi hM
      (hkeys op List.mem_cons_self)) ?_
    rintro noop v ⟨hbv, hiv, hlev⟩
    simp only [writerWP_bind, writerWP_pure]
    exact writerWP_mono (ih c v hv hk hbv hiv hM (fun o ho => hkeys o (List.mem_cons_of_mem _ ho)))
      (fun _ u h => ⟨h.1, h.2.1, hlev.trans h.2.2⟩)

/-- The first state of a transaction. -/
theorem krInv_start (K : KindOracle) (B : NodeId) (top : Top)
    (hroot : ∃ g, K.key top.rootKey g) :
    KrInv K B { next := B, top := top } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n g h hn; cases hn
  · intro d a q cv y h1; simp at h1
  · intro q hq; cases hq
  · intro q hq; cases hq
  · intro d a q h1; simp at h1
  · intro q hq; cases hq
  · intro d a q h1; simp at h1
  · obtain ⟨g, hg⟩ := hroot
    exact ⟨g, Or.inr hg⟩

/-- A successful transaction of the writer ends with a space root that is a key
node (`RootK`: of the overlay's `gh`, or of the oracle), given an oracle that the
view meets, the frame of `appendKlongs`, and a space root of the view that the
oracle knows as a key node. -/
theorem execW_rootWalk (K : KindOracle) (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hM : 2 ≤ p.M) (hwf : tx.wf = true)
    (hframe : AppendFrameOK tx.base)
    (hv : ViewIdsBelow tx.base v)
    (hk : ViewKinds K tx.base { p := p, i := i, view := rootless v })
    (hroot : ∀ z top, lastTop v = some z → topOf p (rootless v) z = .ok top →
      ∃ g, K.key top.rootKey g)
    (he : execW p tx i v = .ok (bs, w)) : RootK K w := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      have hkeys : ∀ op ∈ tx.ops, keyWf op.key = true := by
        intro op hop
        unfold Tx.wf at hwf
        exact List.all_eq_true.mp hwf op hop
      exact (kr_ops K tx.base hframe tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } (viewIdsBelow_rootless tx.base v hv) hk
        (book_start _ _ top) (krInv_start K tx.base top (hroot z top hz ht)) hM hkeys bs w hr).2.1.root

end SIS.Tree
