/-
The contract package (bergdb 030-10): `handleFullWith` when it does a space
split, for a key of any number of segments: WriterSpaceSplit.lean's
`handleFull_space` without `PathInner`. New: the parent is a segment leaf and
the node split is the root of the next segment's tree: a new root names the
two halves, and the segment leaf's klong names the new root, by a klong given
to the leaf (`space-split-2`), or in place if the node split was made by the
transaction (`space-split-2.inplace`).
-/
import Contract.Proof.WriterSpaceSplit
import Contract.Proof.WriterCascadeDefsG
import Contract.Proof.TreeRulesSeg
import Contract.Proof.NodeAlg4

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 0. The steps of the writer remove no node from `outside` -/

/-- The step f from w removes no node from `outside`. -/
abbrev SsKeep {α : Type} (f : SIS.Tree.M α) (c : SIS.Tree.Ctx) (w : MW) : Prop :=
  WP f c w (fun _ w' => w'.outside = [] → w.outside = [])

theorem ssk_bind {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w : MW} (hf : SsKeep f c w) (hg : ∀ a (w1 : MW), SsKeep (g a) c w1) :
    SsKeep (f >>= g) c w := by
  unfold SsKeep
  rw [wp_bind]
  exact WP.mono hf (fun a w1 h1 => WP.mono (hg a w1) (fun _ w2 h2 hout => h1 (h2 hout)))

theorem ssk_same {α : Type} {f : SIS.Tree.M α} {c : SIS.Tree.Ctx} {w : MW}
    (h : WP f c w (fun _ w' => w'.outside = w.outside)) : SsKeep f c w :=
  WP.mono h (fun _ _ e hout => e ▸ hout)

theorem ssk_pure {α : Type} (a : α) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (pure a) c w :=
  (wp_pure _ _ _ _).mpr id

theorem ssk_throw {α : Type} (e : String) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (throw e : SIS.Tree.M α) c w :=
  wp_throw _ _ _ _

theorem ssk_read (c : SIS.Tree.Ctx) (w : MW) : SsKeep (read : SIS.Tree.M SIS.Tree.Ctx) c w :=
  (wp_read _ _ _).mpr id

theorem ssk_get (c : SIS.Tree.Ctx) (w : MW) : SsKeep (MonadState.get : SIS.Tree.M MW) c w :=
  (wp_get _ _ _).mpr id

theorem ssk_eq {α : Type} {f : SIS.Tree.M α} {c : SIS.Tree.Ctx} {w w1 : MW} {a : α}
    (h : f c w = .ok (a, w1)) (ho : w1.outside = [] → w.outside = []) : SsKeep f c w := by
  intro r w' hr
  rw [h] at hr
  cases hr
  exact ho

theorem ssk_getNode (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (SIS.Tree.getNode x) c w :=
  ssk_same (ss_getNode_outside c w x)

theorem ssk_putNode (x : NodeId) (m : MNode) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.putNode x m) c w :=
  ssk_eq (putNode_eq c w x m) id

theorem ssk_note (t : String) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (SIS.Tree.note t) c w :=
  ssk_eq (ss_note c w t) id

theorem ssk_modify (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (modify (fun w : MW => { w with spaceSplits := w.spaceSplits + 1 })) c w :=
  ssk_eq (ss_modify c w) id

theorem ssk_setMadeFor (m : NodeId) (o : Option NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.setMadeFor m o) c w :=
  ssk_eq (ss_setMadeFor c w m o) id

theorem ssk_replacedBy (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.replacedBy x) c w :=
  ssk_eq (replacedBy_eq c w x) id

theorem ssk_newKey (g h : Nat) (leaf : Bool) (ks : List MKlong) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.newKey g h leaf ks) c w := by
  refine ssk_eq (newKey_eq c w g h leaf ks) ?_
  intro hout
  simp only [MW.afterNewKey] at hout
  split at hout
  · cases hout
  · exact hout

theorem ssk_ghOf (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (SIS.Tree.ghOf x) c w := by
  unfold SIS.Tree.ghOf
  refine ssk_bind (ssk_getNode x c w) (fun _ w1 => ?_)
  refine ssk_bind (ssk_get c w1) (fun w2 w3 => ?_)
  split
  · exact ssk_pure _ _ _
  · exact ssk_throw _ _ _

theorem ssk_parentAt (d : Nat) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (SIS.Tree.parentAt d) c w := by
  unfold SIS.Tree.parentAt
  split
  · exact ssk_pure _ _ _
  · refine ssk_bind ?_ (fun _ _ => ssk_pure _ _ _)
    unfold SIS.Tree.pathNode
    refine ssk_bind (ssk_get c w) (fun w2 w3 => ?_)
    split
    · exact ssk_pure _ _ _
    · exact ssk_throw _ _ _

theorem ssk_klongAt (d : Nat) (c : SIS.Tree.Ctx) (w : MW) : SsKeep (SIS.Tree.klongAt d) c w := by
  unfold SIS.Tree.klongAt
  refine ssk_bind (ssk_get c w) (fun w2 w3 => ?_)
  split
  · exact ssk_pure _ _ _
  · exact ssk_throw _ _ _

theorem ssk_newSuperRoot (y : NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.newSuperRoot y) c w := by
  by_cases e : c.i = w.top.time
  · exact ssk_eq (newSuperRoot_inPlace_eq c w y e) id
  · exact ssk_eq (newSuperRoot_new_eq c w y e) id

theorem ssk_foldlM (F : MNode → Nat × NodeId → SIS.Tree.M MNode) (c : SIS.Tree.Ctx)
    (hF : ∀ r cy (w : MW), WP (F r cy) c w (fun _ w' => w' = w)) :
    ∀ (ins : List (Nat × NodeId)) (r0 : MNode) (w : MW),
      WP (List.foldlM F r0 ins) c w (fun _ w' => w' = w)
  | [], r0, w => (wp_pure _ _ _ _).mpr rfl
  | cy :: ins, r0, w => by
    rw [List.foldlM_cons, wp_bind]
    exact WP.mono (hF r0 cy w) (fun r1 w1 e => by
      rw [e]; exact ssk_foldlM F c hF ins r1 w)

theorem ssk_replaceOrAdd (last : MNode) (ins : List (Nat × NodeId)) (c : SIS.Tree.Ctx) (w : MW) :
    SsKeep (SIS.Tree.replaceOrAdd last ins) c w := by
  unfold SIS.Tree.replaceOrAdd
  rw [SsKeep, wp_bind]
  refine (wp_read _ _ _).mpr ?_
  refine WP.mono (ssk_foldlM _ c (fun r cy w1 => ?_) ins last w) (fun _ _ e => by rw [e]; exact id)
  dsimp only
  split
  · exact wp_throw _ _ _ _
  · exact (wp_pure _ _ _ _).mpr rfl
  · exact (wp_pure _ _ _ _).mpr rfl

/-- `handleFullWith` removes no node from `outside` if `up` removes none. -/
theorem handleFullWith_outside {c : SIS.Tree.Ctx}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hup : ∀ q ins (w : MW), WP (up q ins) c w (fun _ w' => w'.outside = [] → w.outside = []))
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : MNode) (compact : Bool)
    (w : MW) :
    WP (SIS.Tree.handleFullWith up depth x ins last compact) c w
      (fun _ w' => w'.outside = [] → w.outside = []) := by
  show SsKeep _ c w
  unfold SIS.Tree.handleFullWith
  repeat' (first
    | with_reducible exact hup _ _ _
    | with_reducible exact ssk_pure _ _ _
    | with_reducible exact ssk_throw _ _ _
    | with_reducible exact ssk_read _ _
    | with_reducible exact ssk_getNode _ _ _
    | with_reducible exact ssk_putNode _ _ _ _
    | with_reducible exact ssk_note _ _ _
    | with_reducible exact ssk_modify _ _
    | with_reducible exact ssk_setMadeFor _ _ _ _
    | with_reducible exact ssk_replacedBy _ _ _
    | with_reducible exact ssk_newKey _ _ _ _ _ _
    | with_reducible exact ssk_ghOf _ _ _
    | with_reducible exact ssk_parentAt _ _ _
    | with_reducible exact ssk_klongAt _ _ _
    | with_reducible exact ssk_newSuperRoot _ _ _
    | with_reducible exact ssk_replaceOrAdd _ _ _ _
    | with_reducible refine ssk_bind ?_ (fun _ _ => ?_)
    | split)

/-! ## 1. The state before the step, with `CasPreG` -/

/-- At depth 0 `CasPreG` is `CasPre`: no node is above x. -/
theorem ssg_casPre0 {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreG p i base s tp w 0 x n ins C) : CasPre p i base s tp w 0 x n ins C :=
  ⟨h.look, h.on, h.path, h.nodup, fun _ _ _ _ hd => absurd hd (Nat.not_lt_zero _), h.books,
    h.wf, h.size, h.len, h.two, h.hyp⟩

/-- The state before the step keeps what the steps keep, and its map is that
of the state with the klongs added (the "if" state), but at x. -/
theorem ssg_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreG p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false) :
    SsOk p i base s tp (fun _ => False) w ∧
      (treeOf i s (w.withNode x (addAll i n ins))).obj x =
        some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) ∧
      ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z = (treeOf i s w).obj z := by
  have hI := h.hyp
  have hA : treeOf i s (w.withNode x (addAll i n ins)) = (treeOf i s w).set x
      (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hAx : (treeOf i s (w.withNode x (addAll i n ins))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [hA]; simp [Tree.set]
  have hAz : ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z =
      (treeOf i s w).obj z := by
    intro z hz; rw [hA]; simp [Tree.set, hz]
  have hW : treeOf i s w = (treeOf i s (w.withNode x (addAll i n ins))).set x
      (.key ⟨wLevel s w x, n.leaf, ksOf n⟩) := by
    apply prim_tree_ext
    · intro z
      by_cases hz : z = x
      · subst hz
        rw [treeOf_obj_overlay i s h.look htx]
        simp [Tree.set, ksOf]
      · simp only [Tree.set, hz, ite_false]
        rw [hAz z hz]
    · rfl
  refine ⟨⟨?_, h.books.toE, hI.top, ?_⟩, hAx, hAz⟩
  · rw [hW]
    have hD := dirtyOf_withNode (n' := addAll i n ins) h.look
    refine hI.frame.set (fun y hy => by rw [hD] at hy; exact hy) (mem_dirtyOf_of_lookup h.look)
      (fun o0 ho0 => ?_)
    obtain ⟨o', ho', he, -⟩ := hI.frame.1 x o0 ho0
    rw [hAx] at ho'
    cases ho'
    cases o0 with
    | val v => exact absurd he (by simp [Ext])
    | key n0 =>
      obtain ⟨he1, he2, he3⟩ := he
      refine ⟨he1, he2, (ss_ext_of_addAll (prim_timesBefore (hb.times x n0 ho0))
        (hb.first x n0 ho0) (ss_timesLe (h.books.times x n h.look)) he3).2⟩
  · intro y m hy hty he
    obtain ⟨t, rest, hr⟩ := h.books.timeFirst y m hy hty
    rw [hr] at he
    cases he

/-- A node that a key klong of x with the klongs added names exists in the
"if" state's map, if x is reached there. -/
theorem ssg_named_some {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp) (h : CasPreG p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false)
    (hx : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    {y : NodeId} (hy : ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) :
    ((treeOf i s (w.withNode x (addAll i n ins))).obj y).isSome = true := by
  obtain ⟨-, hAx, -⟩ := ssg_start hb h htx
  obtain ⟨c', hc'⟩ := hy
  exact ss_nodeOk_names (h.hyp.sound.nodes x hx _ hAx) hc'

/-- x cut back to before the transaction: its klongs of s. -/
theorem ssg_toPrev {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreG p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false) {n0 : KNode} (hs : s.obj x = some (.key n0)) :
    ksOf (n.toPrev (i - 1)) = n0.ks := by
  obtain ⟨-, hAx, -⟩ := ssg_start hb h htx
  obtain ⟨o', ho', he, -⟩ := h.hyp.frame.1 x _ hs
  rw [hAx] at ho'
  cases ho'
  exact (ss_ext_of_addAll (prim_timesBefore (hb.times x n0 hs)) (hb.first x n0 hs)
    (ss_timesLe (h.books.times x n h.look)) he.2.2).1

/-! ## 2. The key access path above x -/

/-- Above x the path is in the "if" state's map A a chain from the space root:
x is not on it (`nodup`), its parent q is reached in A with a live klong
(k1, x) to x, x is on a lower level, one lower if q is an inner node. -/
theorem ssg_path {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    {c0 : Option Nat} (hon : w.path[d + 1]? = some (c0, x)) (htx : w.taken.contains x = false) :
    ∃ k1 cq q nq, w.path[d]? = some (cq, q) ∧ w.path[d + 1]? = some (some k1, x) ∧
      w.nodes.lookup q = some nq ∧ w.taken.contains q = false ∧ q ≠ x ∧
      (k1, x) ∈ live (ksOf nq) ∧
      q ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey ∧
      wLevel s w x < wLevel s w q ∧ (nq.leaf = false → wLevel s w x + 1 = wLevel s w q) ∧
      (∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) := by
  obtain ⟨-, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    rw [hux] at hu
    exact h.nodup e (d + 1) c c0 x (by omega) le_rfl hu hon
  have hreach : ∀ e, e ≤ d + 1 → ∀ c u, w.path[e]? = some (c, u) →
      u ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey := by
    intro e
    induction e with
    | zero =>
      intro _ c u hu
      rw [h.path.root] at hu
      cases hu
      exact tc_self _ _ _
    | succ e ih =>
      intro he c u hu
      obtain ⟨c0', u', c', y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      rw [h2] at hu
      cases hu
      have hq := ih (by omega) _ _ h1
      have hux := hnx e c0' u' (by omega) h1
      rw [← hAz u' hux] at h3
      have hz := tc_kid h3 h4 (tc_self _ nu.level u)
      exact hI.sound.good.tr_closed hq (g := nu.level + 1) hz
  obtain ⟨c0', q, k1, y, nq', h1, h2, h3, h4⟩ := h.path.links d (by omega)
  rw [hon] at h2
  cases h2
  obtain ⟨_, u2, nq, h5, h6, h7⟩ := h.path.nodes d (by omega)
  rw [h1] at h5
  cases h5
  rw [treeOf_obj_overlay i s h6 h7] at h3
  cases h3
  have hqx := hnx d c0' q le_rfl h1
  have hqr := hreach d (by omega) _ _ h1
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s h6 h7]
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq
  have hlt : wLevel s w x < wLevel s w q := by
    rcases hgq.kind hAq h4 with ⟨_, _, v, hv⟩ | ⟨_, m, _, _, hm1, hm2, _, _⟩
    · rw [hAx] at hv; cases hv
    · rw [hAx] at hm1; cases hm1; exact hm2
  refine ⟨k1, c0', q, nq, h1, hon, h6, h7, hqx, h4, hqr, hlt, fun hl => ?_, hnx⟩
  obtain ⟨-, -, hb3⟩ := hI.balanced q (by rw [reach_of_root hI.root]; exact hqr) _ hAq
  obtain ⟨m', hm1, hm2⟩ := hb3 hl k1 x h4
  rw [hAx] at hm1
  cases hm1
  exact hm2

/-! ## 3. Under an inner parent -/

/-- `ss_parent_pre` with `CasPreG`, the parent q an inner node: the state
before the parent's step `up`, if it holds the halves (first and second) and
is otherwise the state before x's step, meets the parent's `CasPreG`, and the
parent's "if" state reaches what A reaches and the halves, and not x if x was
replaced. -/
theorem ssg_parent_pre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode}
    (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = false)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    (hlq : wLevel s w x + 1 = wLevel s w q)
    (hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x)
    {f s2 : MNode} {sc : Nat} {L1 rest : List (Nat × NodeId)} {y0 : NodeId}
    (hsplit : live (ksOf (addAll i n ins)) = L1 ++ (sc, y0) :: rest) (hL1 : L1 ≠ [])
    (hfl : f.leaf = n.leaf) (hsl : s2.leaf = n.leaf) (hlf : live (ksOf f) = L1)
    (hls : live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest)
    (hwff : klongsWf (ksOf f) = true) (hwfs : klongsWf (ksOf s2) = true)
    (hszf : f.size ≤ p.M) (hszs : s2.size ≤ p.M)
    (hkf : ∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    (hks : ∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    {first second : NodeId} {insU : List (Nat × NodeId)} {wU : MW}
    (hOU : SsOk p i base s tp (fun _ => False) wU)
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hntU : wU.newTop = w.newTop)
    (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hwlU : ∀ y, y < w.next → wLevel s wU y = wLevel s w y)
    (hobjU : ∀ z, z ≠ first → z ≠ second → (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hfU : (treeOf i s wU).obj first = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩))
    (hsU : (treeOf i s wU).obj second = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩))
    (hfirst : first = x ∨ w.next ≤ first) (hsecond : w.next ≤ second) (hfs : first ≠ second)
    (hins : (insU = [(sc, second)] ∧ first = x) ∨ insU = [(k1, first), (sc, second)]) :
    CasPreG p i base s tp wU d q nq insU C ∧
      (first ≠ x → x ∉ reachOf i s (wU.withNode q (addAll i nq insU))) ∧
      (∀ z ∈ reachOf i s (wU.withNode q (addAll i nq insU)),
        z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ z = first ∨ z = second) ∧
      x ∈ reachOf i s (w.withNode x (addAll i n ins)) := by
  obtain ⟨-, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  -- q's node: well formed, of size M at most
  have hnq := hI.sound.nodes q hqr _ hAq
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  have hnq' := hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq'
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq'
  rw [ksOf_length] at hnqs
  -- x is reached in A, and a kid of q there
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, -, hpp⟩ := live_split he
  have hkx := (hgq.tr_kids hAq _ (bounds_mem hiq he)).2.2.2 (by simp [hql])
  obtain ⟨mx, hmx, -, -, hgx⟩ := hkx
  simp only [hql, Bool.false_eq_true, ite_false] at hgx
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey :=
    hI.sound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq hk1 (tc_self _ _ x))
  have hsc1 : max loq k1 < sc := Good.tr_split_lo hgx hAx hsplit hL1
  have hscpost : ∀ b ∈ post, sc < b.1 :=
    tr_lt_post hpp (Good.tr_hi hgx hAx (y := y0) (by rw [hsplit]; simp))
  -- the klongs for the parent
  have hlenU : insU.length = 1 ∨ insU.length = 2 := by
    rcases hins with ⟨rfl, -⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmemU : ∀ c y, (c, y) ∈ insU → y = first ∨ y = second := by
    intro c y hm
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      exact Or.inr hm.2
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · exact Or.inl hm.2
      · exact Or.inr hm.2
  have hliveU : insU.foldl (fun m cy => insertCv cy.1 cy.2 m) (live (ksOf nq)) =
      insertCv sc second (insertCv k1 first (live (ksOf nq))) := by
    rcases hins with ⟨rfl, rfl⟩ | rfl
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [ss_insertCv_mem (live_sorted _) hk1]
    · rfl
  -- the state at q
  have hkq : wU.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq : wU.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  have hwq : wLevel s wU q = wLevel s w q := hwlU q hqlt
  have hqf : q ≠ first := by
    rcases hfirst with e | e
    · rw [e]; exact hqx
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt e)
  have hqs : q ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt hsecond)
  obtain ⟨tq, rq, hrq⟩ := (hOU.toBooks (fun _ h => h)).timeFirst q nq hlkq hkq
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq insU
  have hOq := ssOk_withNode (E' := fun _ => False) hOU hlkq hkq (addAll_leaf i nq insU)
    (Or.inl (by rw [hrq', hrq]; rfl))
    (fun t ht => addAll_timesLe (ss_timesLe (hOU.books.times q nq hlkq)) insU t (ss_time_ksOf ht))
    (fun n0 hs0 => addAll_ext (prim_timesBefore (hb.times q n0 hs0))
      (frame_overlay_ext hOU.frame hlkq hkq hs0).2.2 insU)
    (by rw [hrq']; simp) (fun _ _ h => h)
  -- the parent's "if" state's map B
  have hBq : (treeOf i s (wU.withNode q (addAll i nq insU))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq insU)⟩) := by
    rw [hOq.2, ss_ite_pos rfl, addAll_leaf, hwq]
  have hBo : ∀ z, z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hBx : ((treeOf i s (wU.withNode q (addAll i nq insU))).obj x).isSome = true := by
    rw [hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
      rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z h0 h1 h2 h3
    rw [hBo z h3, hobjU z h1 h2, hAz z h0]
  have hBA : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBo _ hqf.symm, hfU]; rfl
    by_cases h2 : z = second
    · rw [h2, hBo _ hqs.symm, hsU]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (ssg_named_some hb h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) first (wLevel s w x) n.leaf
      L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs (by rw [hBo _ hqf.symm]; exact hfU) hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) second (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs (by rw [hBo _ hqs.symm]; exact hsU) ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNq : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) q (wLevel s w q) false
      (insertCv sc second (insertCv k1 first (live (ksOf nq)))) (bnd p.M (some q) q) := by
    rw [← hql, ← addAll_leaf i nq insU, ← hliveU, ← addAll_live hnqwf]
    refine ss_nodeIs (by rw [hBq, addAll_leaf]) rfl (addAll_wf hnqwf insU) ?_ ?_
    · simp only [bnd, ite_true]
      have := addAll_size i nq insU
      rcases hlenU with e | e <;> rw [e] at this <;> omega
    · intro c y hy
      rcases (addAll_key_mem insU nq).mp (ss_key_ksOf hy) with h1 | h1
      · exact hBA y (ss_nodeOk_names hnq h1)
      · rcases hmemU c y h1 with e | e
        · rw [e, hBo _ hqf.symm, hfU]; rfl
        · rw [e, hBo _ hqs.symm, hsU]; rfl
  have hfirstA : first = x ∨ (treeOf i s (w.withNode x (addAll i n ins))).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (treeOf_fresh hb hI.books e).1
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplit (ex' := some q) hI.sound hqr hAq hql hk1 hAx hsplit
    hL1 hfirstA (treeOf_fresh hb hI.books hsecond).1 hfs hNf hNs hNq hBx hsame
  have hrkq : (wU.withNode q (addAll i nq insU)).top.rootKey = w.top.rootKey := by
    show wU.top.rootKey = _
    rw [htopU]
  refine ⟨⟨hlkq, ⟨cq, by rw [hpU]; exact hq1⟩, ?_, ?_, hOU.toBooks (fun _ h => h), hnqwf, hnqs,
    hlenU, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the path
    refine ⟨by rw [hpU, htopU]; exact h.path.root, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨c, u, n', h1, h2, h3⟩ := h.path.nodes e (by omega)
      have hux := hnx e c u he h1
      have hult : u < w.next := h.books.ids.1 u n' h2
      exact ⟨c, u, n', by rw [hpU]; exact h1, by rw [hlkU u hux hult]; exact h2,
        by rw [hkU]; exact h3⟩
    · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      have hux := hnx e c0 u (by omega) h1
      obtain ⟨n', hn', -⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
      have hult : u < w.next := h.books.ids.1 u n' hn'
      have huf : u ≠ first := by
        rcases hfirst with e' | e'
        · rw [e']; exact hux
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hult e')
      have hus : u ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hult hsecond)
      exact ⟨c0, u, c, y, nu, by rw [hpU]; exact h1, by rw [hpU]; exact h2,
        by rw [hobjU u huf hus]; exact h3, h4⟩
  · -- no node twice on the path
    intro e e' c c' u he he' h1 h2
    rw [hpU] at h1 h2
    exact h.nodup e e' c c' u he (by omega) h1 h2
  · -- two klongs: the halves of x
    intro a y1 b y2 heq
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp at heq
    · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at heq
      obtain ⟨⟨rfl, -⟩, rfl, -⟩ := heq
      refine ⟨by omega, ⟨x, hk1⟩, fun c' y' hm hlt => ?_⟩
      rw [he] at hm
      rcases List.mem_append.mp hm with hm | hm
      · have := hpre _ hm
        simp only at this
        omega
      · rcases List.mem_cons.mp hm with hm | hm
        · cases hm
          omega
        · exact hscpost _ hm
  · -- the parent's "if" state
    have hrootQ : (treeOf i s (wU.withNode q (addAll i nq insU))).root = some w.top.rootKey := by
      rw [treeOf_withNode i s _ hkq]
      have e1 : (treeOf i s wU).root = (treeOf i s (w.withNode x (addAll i n ins))).root := by
        simp only [Tree.root, treeOf, hntU, htopU]
        rfl
      exact e1.trans hI.root
    have hxR : x ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
      rw [reach_of_root hI.root]; exact hxreach
    have hqR : q ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
      rw [reach_of_root hI.root]; exact hqr
    have hHL := ss_halves_live hsplit hlf hls
    have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
    have hBf' : (treeOf i s (wU.withNode q (addAll i nq insU))).obj first =
        some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by rw [hBo _ hqf.symm, hfU]
    have hBs' : (treeOf i s (wU.withNode q (addAll i nq insU))).obj second =
        some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by rw [hBo _ hqs.symm, hsU]
    have hBx' : ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj x = some (.key m') ∧
        m'.level = wLevel s w x := by
      rw [hBo x hqx.symm]
      by_cases hxf : x = first
      · have e := hfU
        rw [← hxf] at e
        rw [e]; exact ⟨_, rfl, rfl⟩
      · rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; exact ⟨_, rfl, rfl⟩
    have hold : ∀ z, z ∉ [x, first, second, q] →
        (treeOf i s (wU.withNode q (addAll i nq insU))).obj z =
          (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      exact hsame z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have hlevB := ss_lev_of hold (by
      intro z hz m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hxcase : ∀ m, (treeOf i s (w.withNode x (addAll i n ins))).obj x = some (.key m) →
          ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj x = some (.key m') ∧
            m'.level = m.level := by
        intro m hm
        rw [hAx] at hm
        cases hm
        exact hBx'
      rcases hz with e | e | e | e
      · rw [e] at hm ⊢; exact hxcase m hm
      · rcases hfirst with ef | ef
        · rw [e, ef] at hm ⊢; exact hxcase m hm
        · rw [e, (treeOf_fresh hb hI.books ef).1] at hm; cases hm
      · rw [e, (treeOf_fresh hb hI.books hsecond).1] at hm; cases hm
      · rw [e] at hm ⊢
        rw [hAq] at hm
        cases hm
        exact ⟨_, hBq, rfl⟩)
    have hBal : Balanced p (treeOf i s (wU.withNode q (addAll i nq insU))) := by
      refine ss_bal_of hI.balanced hI.root hrootQ (fun z hz => ?_) hold hlevB
        (fun z hz hzR m hm => ?_)
      · rcases hRB z hz with h1 | h1 | h1
        · exact Or.inl h1
        · right; simp [h1]
        · right; simp [h1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        have hfr : ∀ m, (treeOf i s (wU.withNode q (addAll i nq insU))).obj first =
            some (.key m) → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
            (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks →
              ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj y = some (.key m') ∧
                m'.level + 1 = m.level) := by
          intro m hm
          rw [hBf'] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx hlevB hfl rfl
            (fun c y hy => Or.inl (hHL.1 c y hy))
        rcases hz with e | e | e | e
        · rw [e] at hzR hm
          by_cases hxf : x = first
          · rw [hxf] at hm; exact hfr m hm
          · exact absurd hzR (hxB (Ne.symm hxf))
        · rw [e] at hm; exact hfr m hm
        · rw [e, hBs'] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx hlevB hsl rfl
            (fun c y hy => Or.inl (hHL.2 c y hy))
        · rw [e, hBq] at hm
          cases hm
          refine ss_rule_node hI.balanced hqR hAq hlevB rfl rfl (fun c y hy => ?_)
          rw [addAll_live hnqwf] at hy
          rcases mem_foldl_insertCv_src insU _ hy with h1 | h1
          · exact Or.inl ⟨c, h1⟩
          · rcases hmemU c y h1 with e' | e'
            · rw [e']; exact Or.inr ⟨_, hBf', hlq⟩
            · rw [e']; exact Or.inr ⟨_, hBs', hlq⟩
    exact ⟨by rw [hrkq]; exact hrootQ, by rw [hrkq]; exact hSB, hOq.1.frame, hOq.1.top, hBal,
      hOq.1.toBooks (fun _ h => h)⟩
  · intro hfx
    unfold reachOf
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz
  · exact hxreach

theorem ssg_parent_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = false)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = ssNote w4 "split.space1.inplace") :
    WP (up q [(sc, w.next)] >>= fun _ => pure ()) { p := p, i := i, view := v } w5
      (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1, cq', q', nq', hq1', hon', hq3', hq4, hqx, hk1, hqr, -, hlq0, hnx⟩ :=
    ssg_path hb h hon htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  have hlq := hlq0 hql
  obtain ⟨hO, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  -- the states
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0)
      (by rw [hf1]; simp) (fun z _ hz => hz)
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
  have hO5 : SsOk p i base s tp (fun _ => False) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hn5 : w5.next = w.next + 2 := by rw [e5, e4, e3, e2, e1]; rfl
  obtain ⟨hpre, -, hreach, hxr⟩ := ssg_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := x) (second := w.next)
    (insU := [(sc, w.next)]) hO5
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by
      intro y hyx hy
      rw [e5, e4]
      show (w3.withNode w.next s2).nodes.lookup y = _
      rw [ss_lookup_withNode (Nat.ne_of_lt hy), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hy)])
    (by
      intro y hy
      rw [show wLevel s w5 = wLevel s w1 by rw [e5, e4, ← hwl3]; rfl]
      exact hwl1 y (Nat.ne_of_lt hy))
    (by
      intro z h1 h2
      rw [hT5, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h1, hT2, hO1.2, ss_ite_neg h2])
    (by rw [hT5, hO4.2, ss_ite_neg (Nat.ne_of_lt hxlt), hO3.2, ss_ite_pos rfl])
    (by rw [hT5, hO4.2, ss_ite_pos rfl, hlev])
    (Or.inl rfl) (Nat.le_refl _) (Nat.ne_of_lt hxlt) (Or.inl ⟨rfl, rfl⟩)
  rw [wp_bind]
  refine WP.mono (hup q _ w5 nq C hpre) (fun _ w' hpost => (wp_pure _ _ _ _).mpr ?_)
  intro hout
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hpU : w5.path = w.path := by rw [e5, e4, e3, e2, e1]; rfl
  refine ⟨hPI, hCP.path.trans hpU, ?_, ?_, ?_⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    refine hCP.off y ny ?_ (fun d' c hd' => by rw [hpU]; exact hnot d' c (by omega))
    rw [e5, e4]
    show (w3.withNode w.next s2).nodes.lookup y = _
    rw [ss_lookup_withNode (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · exact Nat.le_trans (ss_le_add hn5) hCP.next
  · intro z hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inl hxr
      · rw [h2]; exact Or.inr (Nat.le_refl _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn5) h1)

theorem ssg_parent_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} {k1 : Nat} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = false)
    (hon' : w.path[d + 1]? = some (some k1, x))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = ssNote w3 "split.space1")
    (e5 : w5 = w4.withNode w.next f) (e6 : w6 = w5.withNode (w.next + 2) s2) :
    WP (up q [(k1, w.next), (sc, w.next + 2)] >>= fun _ =>
        SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w6 (CasPost p i base s tp w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, -, hlq0, hnx⟩ :=
    ssg_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  have hlq := hlq0 hql
  obtain ⟨hO, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w4 := by
    rw [e4, e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT4 : treeOf i s w4 = treeOf i s w2 := by rw [e4, e3]; rfl
  have hk4 : w4.taken = w.taken := by rw [e4, e3, e2, e1]; rfl
  have hN4 : w4.nodes = w2.nodes := by rw [e4, e3]; rfl
  have hM4 : w4.made = w2.made := by rw [e4, e3]; rfl
  have hwl4 : wLevel s w4 = wLevel s w2 := by unfold wLevel; rw [hM4]
  have hwl0 : wLevel s w4 w.next = p.keyLevel g hh := by
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w4 (w.next + 2) = p.keyLevel g hh := by
    rw [hwl4, e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwlo : ∀ y, y < w.next → wLevel s w4 y = wLevel s w y := by
    intro y hy
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_of_lt_add hy), e1]
    exact prim_wLevel_afterNewKey (Nat.ne_of_lt hy)
  have hlk4 : ∀ y, y ≠ w.next → y ≠ w.next + 2 → w4.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2
    rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hold4 : ∀ y, y < w.next → (treeOf i s w4).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT4, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy), hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 2) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w4).obj z := by
    rw [e5, ← hwl0]
    refine ssOk_withNode hO4 (m := ⟨n.leaf, []⟩)
      (by rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
          exact prim_lookup_append_self _ _ hn0)
      (by rw [hk4]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO6 : SsOk p i base s tp (fun _ => False) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w5).obj z := by
    have hwl5 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by rw [e5]; exact hwl2
    rw [e6, ← hwl5]
    refine ssOk_withNode hO5.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e5]; show w4.taken.contains _ = false
        rw [hk4, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0')
      (by rw [hs1]; simp) (fun _ hz h => hz h)
    · rw [e5, ss_lookup_withNode hne20, hN4, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hn2')
  have hpU : w6.path = w.path := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hn6 : w6.next = w.next + 4 := by rw [e6, e5, e4, e3, e2]; show w1.next + 2 = _; rw [hn1]
  have hlk6 : ∀ y, y ≠ x → y < w.next → w6.nodes.lookup y = w.nodes.lookup y := by
    intro y _ hy
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hy), e5, ss_lookup_withNode (Nat.ne_of_lt hy),
      hlk4 y (Nat.ne_of_lt hy) (ss_ne_of_lt_add hy)]
  obtain ⟨hpre, hxnot, hreach, -⟩ := ssg_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := w.next)
    (second := w.next + 2) (insU := [(k1, w.next), (sc, w.next + 2)]) hO6.1 hpU
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) (by rw [e6, e5, e4, e3, e2, e1]; rfl)
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) hlk6
    (by
      intro y hy
      rw [show wLevel s w6 = wLevel s w4 by rw [e6, e5]; rfl]
      exact hwlo y hy)
    (by
      intro z h1 h2
      rw [hO6.2, ss_ite_neg h2, hO5.2, ss_ite_neg h1, hT4, hO2.2, ss_ite_neg h2, hO1.2,
        ss_ite_neg h1])
    (by rw [hO6.2, ss_ite_neg hne20.symm, hO5.2, ss_ite_pos rfl, hlev])
    (by rw [hO6.2, ss_ite_pos rfl, hlev])
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) hne20.symm (Or.inr rfl)
  rw [wp_bind]
  refine WP.mono (hup q _ w6 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine ss_wp_getPut (n := n) (fun hout => ?_)
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hlk6x : w6.nodes.lookup x = some n := by
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hxlt), e5, ss_lookup_withNode (Nat.ne_of_lt hxlt),
      hlk4 x (Nat.ne_of_lt hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  have hlkx : w'.nodes.lookup x = some n := by
    refine hCP.off x n hlk6x ?_
    intro d' c hd' e
    rw [hpU] at e
    exact hnx d' c x hd' e rfl
  have hsx : (s.obj x).isSome = true := (h.books.first x n hlook htx).mpr hin
  have htx' : w'.taken.contains x = false := by
    cases e : w'.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hPI.books.taken x e)
      have := (hPI.books.ids.2.2.1 m hm).2
      rw [hmx] at this
      rw [(hb.ids x this).1] at hsx
      cases hsx
  have hxnr : x ∉ reachOf i s w' := by
    intro hx
    rcases hCP.reach x hx with h1 | h1
    · exact hxnot hxlt.ne' h1
    · rw [hn6] at h1
      exact absurd (Nat.lt_of_lt_of_le hxlt (Nat.le_trans (Nat.le_add_right _ 4) h1))
        (Nat.lt_irrefl _)
  have hO' : SsOk p i base s tp (fun _ => False) w' :=
    ⟨hPI.frame, hPI.books.toE, hPI.top, fun y m hy ht he => by
      obtain ⟨t, r, hr⟩ := hPI.books.timeFirst y m hy ht
      rw [hr] at he
      cases he⟩
  have hO'' := ssOk_withNode (E' := fun _ => False) hO' hlkx htx' rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (ssg_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  have ha : ∀ z ∈ reachOf i s w', (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s w').obj z := by
    intro z hz
    have hzx : z ≠ x := fun e => hxnr (e ▸ hz)
    rw [hO''.2, ss_ite_neg hzx]
  have hrx : w'.top.rootKey ≠ x := fun e => hxnr (by unfold reachOf; rw [e]; exact tc_self _ _ _)
  have hfuel : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey =
      (treeOf i s w').fuel w'.top.rootKey := by
    simp only [Tree.fuel, hO''.2, ss_ite_neg hrx]
  have hreach' : reachOf i s (w'.withNode x (n.toPrev (i - 1))) = reachOf i s w' := by
    unfold reachOf
    show reachAt _ ((treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey)
      w'.top.rootKey = _
    rw [hfuel]
    exact reachAt_agree _ _ ha
  have hSB : Sound p.M none (treeOf i s (w'.withNode x (n.toPrev (i - 1))))
      (w'.withNode x (n.toPrev (i - 1))).top.rootKey C := by
    refine Sound.agree hPI.sound ha (fun z hz => ?_)
    by_cases hzx : z = x
    · rw [hzx, hO''.2, ss_ite_pos rfl]; rfl
    · rw [hO''.2, ss_ite_neg hzx]; exact hz
  have hroot : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root =
      some (w'.withNode x (n.toPrev (i - 1))).top.rootKey := by
    rw [treeOf_withNode i s _ htx']
    exact hPI.root
  have hBal3 : Balanced p (treeOf i s (w'.withNode x (n.toPrev (i - 1)))) := by
    have hrB : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root = some w'.top.rootKey := by
      rw [treeOf_withNode i s _ htx']; exact hPI.root
    refine Balanced.of_reach (N := [x]) hPI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
      (levels_kept_withNode i s _ hlkx htx') (fun z hz hzR => ?_)
    · left
      rw [reach_of_root hrB] at hz
      rw [reach_of_root hPI.root]
      have hz' : z ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hz
      rw [hreach'] at hz'
      exact hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hO''.2, ss_ite_neg hz]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz, reach_of_root hrB] at hzR
      have hz' : x ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hzR
      rw [hreach'] at hz'
      exact absurd hz' hxnr
  refine ⟨hlkx, ss_pinv hO''.1 hroot hSB hBal3, ⟨hCP.path.trans hpU, ?_, ?_, ?_⟩⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) (some k1) le_rfl (by rw [e]; exact hon')
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx]
    refine hCP.off y ny (by rw [hlk6 y hyx hylt]; exact hy) ?_
    intro d' c hd'
    rw [hpU]
    exact hnot d' c (by omega)
  · exact Nat.le_trans (ss_le_add hn6) hCP.next
  · intro z hz
    rw [hreach'] at hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inr (Nat.le_refl _)
      · rw [h2]; exact Or.inr (Nat.le_add_right _ _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn6) h1)

theorem ssg_parent_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hq3 : w.nodes.lookup q = some nq) (hql : nq.leaf = false) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true, hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ssg_parent_inPlace_post hp hb h hup hcase hin hgh hq1 hq3 hql hH rfl rfl rfl rfl rfl


theorem ssg_parent_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = false) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin', hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_klongAt rfl hon') ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact ssg_parent_new_post hp hb h hup hcase hin hgh hq1 hq3 hql hon' hH rfl rfl rfl rfl rfl rfl


/-! ## 4. Under a segment leaf: the tree rule -/

/-- x the root of the next segment's tree under the segment leaf q: the state
wU holds the halves (first and second) and a new root r that names them, and
q gets the node mq whose live klongs are q's with (k1, r) set. Then the state
with q set keeps what the steps keep, its map is sound with q allowed over its
size by `ex'`, and it reaches what A reaches, the halves and r, and not x if
x was replaced. -/
theorem ssg_seg_core {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {q : NodeId} {nq : MNode} (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = true)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    (hlev : wLevel s w x + 1 < wLevel s w q) (hhr : p.heightOf (wLevel s w x + 1) ≠ 0)
    {f s2 : MNode} {sc : Nat} {L1 rest : List (Nat × NodeId)} {y0 : NodeId}
    (hsplit : live (ksOf (addAll i n ins)) = L1 ++ (sc, y0) :: rest) (hL1 : L1 ≠ [])
    (hfl : f.leaf = n.leaf) (hsl : s2.leaf = n.leaf) (hlf : live (ksOf f) = L1)
    (hls : live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest)
    (hwff : klongsWf (ksOf f) = true) (hwfs : klongsWf (ksOf s2) = true)
    (hszf : f.size ≤ p.M) (hszs : s2.size ≤ p.M)
    (hkf : ∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    (hks : ∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    {first second r : NodeId} {wU : MW}
    (hOU : SsOk p i base s tp (fun _ => False) wU)
    (htopU : wU.top = w.top) (hntU : wU.newTop = w.newTop) (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hwlU : ∀ y, y < w.next → wLevel s wU y = wLevel s w y)
    (hobjU : ∀ z, z ≠ first → z ≠ second → z ≠ r →
      (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hfU : (treeOf i s wU).obj first = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩))
    (hsU : (treeOf i s wU).obj second = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩))
    (hrU : (treeOf i s wU).obj r = some (.key ⟨wLevel s w x + 1, false,
      ([.time i, .key 0 first, .key sc second] : List MKlong).map kOf⟩))
    (hfirst : first = x ∨ w.next ≤ first) (hsecond : w.next ≤ second) (hr : w.next ≤ r)
    (hfs : first ≠ second) (hrf : r ≠ first) (hrs : r ≠ second)
    {mq : MNode} {ex' : Option NodeId}
    (hmlive : live (ksOf mq) = insertCv k1 r (live (ksOf nq)))
    (hmwf : klongsWf (ksOf mq) = true) (hmsz : mq.size ≤ bnd p.M ex' q)
    (hmleaf : mq.leaf = nq.leaf)
    (hmkey : ∀ c y, SIS.Tree.Klong.key c y ∈ mq.ks → Klong.key c y ∈ ksOf nq ∨ y = r)
    (hmfst : mq.ks.head? = nq.ks.head?)
    (hmtimes : ∀ t, SIS.Tree.Klong.time t ∈ mq.ks → t ≤ i)
    (hmext : ∀ n0, s.obj q = some (.key n0) →
      ksOf mq = n0.ks ∨ ∃ more, ksOf mq = n0.ks ++ Klong.time i :: more)
    (hmne : mq.ks ≠ []) :
    SsOk p i base s tp (fun _ => False) (wU.withNode q mq) ∧
      Sound p.M ex' (treeOf i s (wU.withNode q mq)) (wU.withNode q mq).top.rootKey C ∧
      (treeOf i s (wU.withNode q mq)).root = some (wU.withNode q mq).top.rootKey ∧
      (first ≠ x → x ∉ reachOf i s (wU.withNode q mq)) ∧
      (∀ z ∈ reachOf i s (wU.withNode q mq),
        z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ z = first ∨ z = second ∨ z = r) ∧
      x ∈ reachOf i s (w.withNode x (addAll i n ins)) ∧
      Balanced p (treeOf i s (wU.withNode q mq)) := by
  obtain ⟨-, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  have hnq := hI.sound.nodes q hqr _ hAq
  -- x is reached in A, and sound there
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq
  obtain ⟨lox, hix, hgx⟩ : ∃ lo hi, Good (treeOf i s (w.withNode x (addAll i n ins))) x lo hi := by
    rcases hgq.kind hAq hk1 with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', _, _, _, hg⟩
    · rw [hAx] at hv; cases hv
    · exact ⟨lo', hi', hg⟩
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey :=
    hI.sound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq hk1 (tc_self _ _ x))
  have hsc0 : 0 < sc := Nat.lt_of_le_of_lt (Nat.zero_le _) (Good.tr_split_lo hgx hAx hsplit hL1)
  -- the state at q
  have hkq : wU.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq : wU.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  have hwq : wLevel s wU q = wLevel s w q := hwlU q hqlt
  have hqf : q ≠ first := by
    rcases hfirst with e | e
    · rw [e]; exact hqx
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt e)
  have hqs : q ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt hsecond)
  have hqr' : q ≠ r := Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt hr)
  have hOq := ssOk_withNode (E' := fun _ => False) hOU hlkq hkq hmleaf (Or.inl hmfst) hmtimes
    hmext hmne (fun _ _ h => h)
  -- the map B
  have hBq : (treeOf i s (wU.withNode q mq)).obj q =
      some (.key ⟨wLevel s w q, mq.leaf, ksOf mq⟩) := by
    rw [hOq.2, ss_ite_pos rfl, hwq]
  have hBo : ∀ z, z ≠ q → (treeOf i s (wU.withNode q mq)).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
  have hxr : x ≠ r := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hr)
  have hBx : ((treeOf i s (wU.withNode q mq)).obj x).isSome = true := by
    rw [hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · rw [hobjU x hxf hxs hxr, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ r → z ≠ q →
      (treeOf i s (wU.withNode q mq)).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z h0 h1 h2 h4 h3
    rw [hBo z h3, hobjU z h1 h2 h4, hAz z h0]
  have hBA : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (wU.withNode q mq)).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBo _ hqf.symm, hfU]; rfl
    by_cases h2 : z = second
    · rw [h2, hBo _ hqs.symm, hsU]; rfl
    by_cases h4 : z = r
    · rw [h4, hBo _ hqr'.symm, hrU]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h4 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (wU.withNode q mq)).obj y).isSome = true :=
    fun m hm c y hy => hBA y (ssg_named_some hb h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (wU.withNode q mq)) first (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs (by rw [hBo _ hqf.symm]; exact hfU) hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (wU.withNode q mq)) second (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs (by rw [hBo _ hqs.symm]; exact hsU) ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (treeOf i s (wU.withNode q mq)) r (wLevel s w x + 1) false
      [(0, first), (sc, second)] p.M :=
    ss_nodeIs_root hsc0 (by have := hp.size; omega) (by rw [hBo _ hqr'.symm]; exact hrU)
      (by rw [hBo _ hqf.symm, hfU]; rfl) (by rw [hBo _ hqs.symm, hsU]; rfl)
  have hNq : NodeIs (treeOf i s (wU.withNode q mq)) q (wLevel s w q) true
      (insertCv k1 r (live (ksOf nq))) (bnd p.M ex' q) := by
    rw [← hql, ← hmleaf, ← hmlive]
    refine ss_nodeIs hBq rfl hmwf hmsz ?_
    intro c y hy
    rcases hmkey c y hy with h1 | h1
    · exact hBA y (ss_nodeOk_names hnq h1)
    · rw [h1, hBo _ hqr'.symm, hrU]; rfl
  have hfirstA : first = x ∨ (treeOf i s (w.withNode x (addAll i n ins))).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (treeOf_fresh hb hI.books e).1
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplitSeg (ex' := ex') hI.sound hqr hAq hql hk1 hAx hsplit
    hL1 hfirstA (treeOf_fresh hb hI.books hsecond).1 hfs (treeOf_fresh hb hI.books hr).1
    ⟨hrf, hrs⟩ hlev hNf hNs hNr hNq hBx hsame
  have hrkq : (wU.withNode q mq).top.rootKey = w.top.rootKey := by
    show wU.top.rootKey = _
    rw [htopU]
  have hrootQ : (treeOf i s (wU.withNode q mq)).root = some w.top.rootKey := by
    rw [treeOf_withNode i s _ hkq]
    have e1 : (treeOf i s wU).root = (treeOf i s (w.withNode x (addAll i n ins))).root := by
      simp only [Tree.root, treeOf, hntU, htopU]
      rfl
    exact e1.trans hI.root
  -- the balance rule in B
  have hxR : x ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
    rw [reach_of_root hI.root]; exact hxreach
  have hqR : q ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
    rw [reach_of_root hI.root]; exact hqr
  have hHL := ss_halves_live hsplit hlf hls
  have hBf' : (treeOf i s (wU.withNode q mq)).obj first =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by rw [hBo _ hqf.symm, hfU]
  have hBs' : (treeOf i s (wU.withNode q mq)).obj second =
      some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by rw [hBo _ hqs.symm, hsU]
  have hBr' : (treeOf i s (wU.withNode q mq)).obj r = some (.key ⟨wLevel s w x + 1, false,
      ([.time i, .key 0 first, .key sc second] : List MKlong).map kOf⟩) := by
    rw [hBo _ hqr'.symm, hrU]
  have hBx' : ∃ m', (treeOf i s (wU.withNode q mq)).obj x = some (.key m') ∧
      m'.level = wLevel s w x := by
    rw [hBo x hqx.symm]
    by_cases hxf : x = first
    · have e := hfU
      rw [← hxf] at e
      rw [e]; exact ⟨_, rfl, rfl⟩
    · rw [hobjU x hxf hxs hxr, treeOf_obj_overlay i s hlook htx]; exact ⟨_, rfl, rfl⟩
  have hold : ∀ z, z ∉ [x, first, second, r, q] →
      (treeOf i s (wU.withNode q mq)).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact hsame z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    have hxcase : ∀ m, (treeOf i s (w.withNode x (addAll i n ins))).obj x = some (.key m) →
        ∃ m', (treeOf i s (wU.withNode q mq)).obj x = some (.key m') ∧
          m'.level = m.level := by
      intro m hm
      rw [hAx] at hm
      cases hm
      exact hBx'
    rcases hz with e | e | e | e | e
    · rw [e] at hm ⊢; exact hxcase m hm
    · rcases hfirst with ef | ef
      · rw [e, ef] at hm ⊢; exact hxcase m hm
      · rw [e, (treeOf_fresh hb hI.books ef).1] at hm; cases hm
    · rw [e, (treeOf_fresh hb hI.books hsecond).1] at hm; cases hm
    · rw [e, (treeOf_fresh hb hI.books hr).1] at hm; cases hm
    · rw [e] at hm ⊢
      rw [hAq] at hm
      cases hm
      exact ⟨_, hBq, rfl⟩)
  have hBal : Balanced p (treeOf i s (wU.withNode q mq)) := by
    refine ss_bal_of hI.balanced hI.root hrootQ (fun z hz => ?_) hold hlevB
      (fun z hz hzR m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hfr : ∀ m, (treeOf i s (wU.withNode q mq)).obj first =
          some (.key m) → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
          (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks →
            ∃ m', (treeOf i s (wU.withNode q mq)).obj y = some (.key m') ∧
              m'.level + 1 = m.level) := by
        intro m hm
        rw [hBf'] at hm
        cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hfl rfl
          (fun c y hy => Or.inl (hHL.1 c y hy))
      rcases hz with e | e | e | e | e
      · rw [e] at hzR hm
        by_cases hxf : x = first
        · rw [hxf] at hm; exact hfr m hm
        · exact absurd hzR (hxB (Ne.symm hxf))
      · rw [e] at hm; exact hfr m hm
      · rw [e, hBs'] at hm
        cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hsl rfl
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [e, hBr'] at hm
        cases hm
        exact ss_rule_root (Nat.succ_pos _) hhr ⟨_, hBf', rfl⟩ ⟨_, hBs', rfl⟩
      · rw [e, hBq] at hm
        cases hm
        obtain ⟨h1, h2, -⟩ := hI.balanced q hqR _ hAq
        refine ⟨h1, by rw [hmleaf]; exact h2, fun hl => ?_⟩
        rw [hmleaf, hql] at hl
        cases hl
  refine ⟨hOq.1, by rw [hrkq]; exact hSB, by rw [hrkq]; exact hrootQ, ?_, ?_, hxreach, hBal⟩
  · intro hfx
    unfold reachOf
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz

/-! ## 5. x cut back after the parent's step -/

/-- After the parent's step from the state wU, x (from before the transaction,
not on the path above its depth, not reached in the parent's "if" state) is
cut back to its klongs of s: the step meets `CasPost`. -/
theorem ssg_cutBack {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hin : ¬ n.firstTime = some i) {k1 : Nat} (hon' : w.path[d + 1]? = some (some k1, x))
    {q : NodeId} {nq : MNode} {insU : List (Nat × NodeId)} {wU w' : MW}
    (hpU : wU.path = w.path) (hnU : w.next ≤ wU.next)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hlkUx : wU.nodes.lookup x = some n)
    (hxnot : x ∉ reachOf i s (wU.withNode q (addAll i nq insU)))
    (hreach : ∀ z ∈ reachOf i s (wU.withNode q (addAll i nq insU)),
      z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ w.next ≤ z)
    (hpost : CasPost p i base s tp wU d q nq insU C () w') :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w' (CasPost p i base s tp w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    rw [hux] at hu
    exact h.nodup e (d + 1) c (some k1) x (by omega) le_rfl hu hon'
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  refine ss_wp_getPut (n := n) (fun hout => ?_)
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hlkx : w'.nodes.lookup x = some n := by
    refine hCP.off x n hlkUx ?_
    intro d' c hd' e
    rw [hpU] at e
    exact hnx d' c x hd' e rfl
  have hsx : (s.obj x).isSome = true := (h.books.first x n hlook htx).mpr hin
  have htx' : w'.taken.contains x = false := by
    cases e : w'.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hPI.books.taken x e)
      have := (hPI.books.ids.2.2.1 m hm).2
      rw [hmx] at this
      rw [(hb.ids x this).1] at hsx
      cases hsx
  have hxnr : x ∉ reachOf i s w' := by
    intro hx
    rcases hCP.reach x hx with h1 | h1
    · exact hxnot h1
    · exact absurd (Nat.lt_of_lt_of_le hxlt (Nat.le_trans hnU h1)) (Nat.lt_irrefl _)
  have hO' : SsOk p i base s tp (fun _ => False) w' :=
    ⟨hPI.frame, hPI.books.toE, hPI.top, fun y m hy ht he => by
      obtain ⟨t, r, hr⟩ := hPI.books.timeFirst y m hy ht
      rw [hr] at he
      cases he⟩
  have hO'' := ssOk_withNode (E' := fun _ => False) hO' hlkx htx' rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (ssg_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  have ha : ∀ z ∈ reachOf i s w', (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s w').obj z := by
    intro z hz
    have hzx : z ≠ x := fun e => hxnr (e ▸ hz)
    rw [hO''.2, ss_ite_neg hzx]
  have hrx : w'.top.rootKey ≠ x := fun e => hxnr (by unfold reachOf; rw [e]; exact tc_self _ _ _)
  have hfuel : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey =
      (treeOf i s w').fuel w'.top.rootKey := by
    simp only [Tree.fuel, hO''.2, ss_ite_neg hrx]
  have hreach' : reachOf i s (w'.withNode x (n.toPrev (i - 1))) = reachOf i s w' := by
    unfold reachOf
    show reachAt _ ((treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey)
      w'.top.rootKey = _
    rw [hfuel]
    exact reachAt_agree _ _ ha
  have hSB : Sound p.M none (treeOf i s (w'.withNode x (n.toPrev (i - 1))))
      (w'.withNode x (n.toPrev (i - 1))).top.rootKey C := by
    refine Sound.agree hPI.sound ha (fun z hz => ?_)
    by_cases hzx : z = x
    · rw [hzx, hO''.2, ss_ite_pos rfl]; rfl
    · rw [hO''.2, ss_ite_neg hzx]; exact hz
  have hroot : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root =
      some (w'.withNode x (n.toPrev (i - 1))).top.rootKey := by
    rw [treeOf_withNode i s _ htx']
    exact hPI.root
  have hBal3 : Balanced p (treeOf i s (w'.withNode x (n.toPrev (i - 1)))) := by
    have hrB : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root = some w'.top.rootKey := by
      rw [treeOf_withNode i s _ htx']; exact hPI.root
    refine Balanced.of_reach (N := [x]) hPI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
      (levels_kept_withNode i s _ hlkx htx') (fun z hz hzR => ?_)
    · left
      rw [reach_of_root hrB] at hz
      rw [reach_of_root hPI.root]
      have hz' : z ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hz
      rw [hreach'] at hz'
      exact hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hO''.2, ss_ite_neg hz]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz, reach_of_root hrB] at hzR
      have hz' : x ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hzR
      rw [hreach'] at hz'
      exact absurd hz' hxnr
  refine ⟨hlkx, ss_pinv hO''.1 hroot hSB hBal3, ⟨hCP.path.trans hpU, ?_, ?_, ?_⟩⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) (some k1) le_rfl (by rw [e]; exact hon')
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx]
    refine hCP.off y ny (by rw [hlkU y hyx hylt]; exact hy) ?_
    intro d' c hd'
    rw [hpU]
    exact hnot d' c (by omega)
  · exact Nat.le_trans hnU hCP.next
  · intro z hz
    rw [hreach'] at hz
    rcases hCP.reach z hz with h1 | h1
    · exact hreach z h1
    · exact Or.inr (Nat.le_trans hnU h1)

/-- `getNode` and `putNode` of x leave `outside` as it is. -/
theorem ss_getPut_outside (c : SIS.Tree.Ctx) (w : MW) (x : NodeId) (t : Time) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev t)) c w
      (fun _ w' => w'.outside = w.outside) := by
  rw [wp_bind]
  intro n' w1 hg
  exact ss_wp_putNode (ss_getNode_outside c w x n' w1 hg)

/-- Above x (CasPreG, x not on the path above its depth), a state with the
path, the top, the nodes taken back and the nodes of the path as before, and
the map as before on the nodes of before but x, keeps the path. -/
theorem ssg_path_keep {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) {wU : MW}
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hobjU : ∀ z, z ≠ x → z < w.next → (treeOf i s wU).obj z = (treeOf i s w).obj z) :
    PathOk i s wU d ∧ ∀ e e' c c' u, e < e' → e' ≤ d → wU.path[e]? = some (c, u) →
      wU.path[e']? = some (c', u) → False := by
  refine ⟨⟨by rw [hpU, htopU]; exact h.path.root, fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · obtain ⟨c, u, n', h1, h2, h3⟩ := h.path.nodes e (by omega)
    have hux := hnx e c u he h1
    have hult : u < w.next := h.books.ids.1 u n' h2
    exact ⟨c, u, n', by rw [hpU]; exact h1, by rw [hlkU u hux hult]; exact h2,
      by rw [hkU]; exact h3⟩
  · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
    have hux := hnx e c0 u (by omega) h1
    obtain ⟨n', hn', -⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
    have hult : u < w.next := h.books.ids.1 u n' hn'
    exact ⟨c0, u, c, y, nu, by rw [hpU]; exact h1, by rw [hpU]; exact h2,
      by rw [hobjU u hux hult]; exact h3, h4⟩
  · intro e e' c c' u he he' h1 h2
    rw [hpU] at h1 h2
    exact h.nodup e e' c c' u he (by omega) h1 h2

/-- A new root at height h + 1 ≤ H of a segment below a segment leaf is on a
level below the leaf's. -/
theorem ssg_level_seg (p : MParams) {g h gq : Nat} (hhH : h + 1 ≤ p.H)
    (hlt : p.keyLevel g h < p.keyLevel gq 0) : p.keyLevel g h + 1 < p.keyLevel gq 0 := by
  unfold SIS.Tree.Params.keyLevel at *
  have hab : p.G - g < p.G - gq := by
    rcases Nat.lt_or_ge (p.G - g) (p.G - gq) with hc | hc
    · exact hc
    · have := Nat.mul_le_mul_right (p.H + 1) hc
      omega
  have := Nat.mul_le_mul_right (p.H + 1) (Nat.succ_le_of_lt hab)
  rw [Nat.succ_mul] at this
  omega

/-! ## 6. Under a segment leaf: x from before the transaction (`split.space2`) -/

theorem ssg_seg_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hupo : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → w.outside = []))
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} {k1 : Nat} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) (hon' : w.path[d + 1]? = some (some k1, x))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 w7 w8 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = (ssNote w3 "split.space2").afterNewKey p g (hh + 1) false [])
    (e5 : w5 = ssMF w4 (w.next + 4) (some x))
    (e6 : w6 = w5.withNode w.next f) (e7 : w7 = w6.withNode (w.next + 2) s2)
    (e8 : w8 = w7.withNode (w.next + 4) ⟨false, [.time i, .key 0 w.next, .key sc (w.next + 2)]⟩) :
    WP (up q [(k1, w.next + 4)] >>= fun _ =>
        SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w8 (CasPost p i base s tp w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hn2 : w2.next = w.next + 4 := by rw [e2]; show w1.next + 2 = _; rw [hn1]
  have hn3 : w3.next = w.next + 4 := by rw [e3]; exact hn2
  rw [wp_bind]
  by_cases ho : w8.outside = []
  swap
  · refine WP.mono (hupo q _ w8) (fun _ (w' : MW) hw' => ?_)
    intro r w'' hrun hout
    exact absurd (hw' (by rw [← ss_getPut_outside _ w' x (i - 1) r w'' hrun]; exact hout)) ho
  have hout4 : w4.outside = [] := by
    rw [← ho, e8, e7, e6, e5]
    rfl
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e4] at hout4
      simp [MW.afterNewKey, hc] at hout4
    · exact hc
  have hlk : ∀ y, y ≠ w.next → y ≠ w.next + 2 → y ≠ w.next + 4 →
      w8.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2 h4
    rw [e8, ss_lookup_withNode h4, e7, ss_lookup_withNode h2, e6, ss_lookup_withNode h1,
      show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space2") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space2").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, hlt, -, hnx⟩ :=
    ssg_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO3 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w3 := by
    rw [e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT3 : treeOf i s w3 = treeOf i s w2 := by rw [e3]; rfl
  have hfr3 := treeOf_freshE hb hO3.books (Nat.le_refl w3.next)
  rw [hn3] at hfr3
  obtain ⟨-, hs4, hn4', -, ht4, hm4⟩ := hfr3
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false, []⟩) else (treeOf i s w3).obj z := by
    rw [e4, ← hn3]
    exact ssOk_newKey hb (hO3.congr (w' := ssNote w3 "split.space2") rfl rfl rfl rfl rfl rfl rfl rfl
      rfl) hgG hH1 (by simp) (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hk5 : w5.taken = w.taken := by rw [e5, e4, e3, e2, e1]; rfl
  have hM5 : wLevel s w5 = wLevel s w4 := by rw [e5]; rfl
  have hw4n : ∀ y, y ≠ w.next + 4 → wLevel s w5 y = wLevel s w2 y := by
    intro y hy
    rw [hM5, e4, prim_wLevel_afterNewKey (w := ssNote w3 "split.space2")
      (by show y ≠ w3.next; rw [hn3]; exact hy)]
    rw [e3]
    rfl
  have hwl0 : wLevel s w5 w.next = p.keyLevel g hh := by
    rw [hw4n _ (ss_ne_add (by decide)), e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_add (by decide)), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by
    rw [hw4n _ (by
      have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
      rw [Nat.add_assoc] at this
      exact this), e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwl4 : wLevel s w5 (w.next + 4) = p.keyLevel g (hh + 1) := by
    rw [hM5, e4, ← hn3]
    exact ss_wLevel_newKey (w := ssNote w3 "split.space2") p g (hh + 1) false []
      (by show s.obj w3.next = none; rw [hn3]; exact hs4)
      (by show ∀ m ∈ w3.made, m.id ≠ w3.next; rw [hn3]; exact hm4)
  have hN5 : ∀ y, y ≠ w.next + 4 → y ≠ w.next + 2 → w5.nodes.lookup y = w1.nodes.lookup y := by
    intro y h4 h2
    rw [show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space2") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space2").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2)]
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hold5 : ∀ y, y < w.next → (treeOf i s w5).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT5, hO4.2, ss_ite_neg (ss_ne_of_lt_add hy), hT3, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy),
      hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO6 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w5).obj z := by
    rw [e6, ← hwl0]
    refine ssOk_withNode hO5 (m := ⟨n.leaf, []⟩)
      (by rw [hN5 _ (ss_ne_add (by decide)) (ss_ne_add (by decide)), hlk1n])
      (by rw [hk5]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne40 : w.next + 4 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne42 : w.next + 4 ≠ w.next + 2 := by
    have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
    rw [Nat.add_assoc] at this
    exact this.symm
  have hlk1 : w1.nodes.lookup (w.next + 2) = none := by rw [← hn1]; rw [hn1]; exact hn2'
  have hO7 : SsOk p i base s tp (fun z => z = w.next + 4) w7 ∧
      ∀ z, (treeOf i s w7).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w6).obj z := by
    have hwl6 : wLevel s w6 (w.next + 2) = p.keyLevel g hh := by rw [e6]; exact hwl2
    rw [e7, ← hwl6]
    refine ssOk_withNode hO6.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0')
      (by rw [hs1]; simp) ?_
    · rw [e6, ss_lookup_withNode hne20, show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
        ss_lookup_newKey (w := ssNote w3 "split.space2")
          (by show _ ≠ w3.next; rw [hn3]; exact hne42.symm),
        show (ssNote w3 "split.space2").nodes = w2.nodes by rw [e3]; rfl, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hlk1)
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO8 : SsOk p i base s tp (fun _ => False) w8 ∧
      ∀ z, (treeOf i s w8).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩)
        else (treeOf i s w7).obj z := by
    have hwl7 : wLevel s w7 (w.next + 4) = p.keyLevel g (hh + 1) := by rw [e7, e6]; exact hwl4
    rw [e8, ← hwl7]
    refine ssOk_withNode hO7.1 (m := ⟨false, []⟩) ?_
      (by
        rw [e7, e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w3.taken by rw [e3, e2, e1]; rfl]; exact ht4) rfl
      (Or.inr ⟨rfl, _, rfl⟩) (by simp) (fun n0 hn0' => by rw [hs4] at hn0'; cases hn0')
      (by simp) (fun _ hz h => hz h)
    · rw [e7, ss_lookup_withNode hne42, e6, ss_lookup_withNode hne40,
        show w5.nodes = w4.nodes by rw [e5]; rfl, e4, ← hn3]
      exact prim_lookup_append_self (l := (ssNote w3 "split.space2").nodes) _
        (by show w3.nodes.lookup w3.next = none; rw [hn3]; exact hn4')
  -- the state before the parent's step
  have hxn : x ≠ w.next := Nat.ne_of_lt hxlt
  have hxn2 : x ≠ w.next + 2 := ss_ne_of_lt_add hxlt
  have hxn4 : x ≠ w.next + 4 := ss_ne_of_lt_add hxlt
  have hpU : w8.path = w.path := by rw [e8, e7, e6, e5, e4, e3, e2, e1]; rfl
  have htopU : w8.top = w.top := by rw [e8, e7, e6, e5, e4, e3, e2, e1]; rfl
  have hntU : w8.newTop = w.newTop := by rw [e8, e7, e6, e5, e4, e3, e2, e1]; rfl
  have hkU : w8.taken = w.taken := by rw [e8, e7, e6, e5, e4, e3, e2, e1]; rfl
  have hn8 : w8.next = w.next + 6 := by
    rw [e8, e7, e6, e5, e4]
    show w3.next + 2 = _
    rw [hn3]
  have hlkU : ∀ y, y ≠ x → y < w.next → w8.nodes.lookup y = w.nodes.lookup y :=
    fun y _ hy => hlk y (Nat.ne_of_lt hy) (ss_ne_of_lt_add hy) (ss_ne_of_lt_add hy)
  have hlkUx : w8.nodes.lookup x = some n := by rw [hlk x hxn hxn2 hxn4]; exact hlook
  have hwlU : ∀ y, y < w.next → wLevel s w8 y = wLevel s w y := by
    intro y hy
    rw [show wLevel s w8 = wLevel s w5 by rw [e8, e7, e6]; rfl, hw4n y (ss_ne_of_lt_add hy), e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_of_lt_add hy), e1]
    exact prim_wLevel_afterNewKey (Nat.ne_of_lt hy)
  have hobjU : ∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 4 →
      (treeOf i s w8).obj z = (treeOf i s w).obj z := by
    intro z h1 h2 h4
    rw [hO8.2, ss_ite_neg h4, hO7.2, ss_ite_neg h2, hO6.2, ss_ite_neg h1, hT5, hO4.2,
      ss_ite_neg h4, hT3, hO2.2, ss_ite_neg h2, hO1.2, ss_ite_neg h1]
  have hfU : (treeOf i s w8).obj w.next = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [hO8.2, ss_ite_neg hne40.symm, hO7.2, ss_ite_neg hne20.symm, hO6.2, ss_ite_pos rfl, hlev]
  have hsU : (treeOf i s w8).obj (w.next + 2) =
      some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by
    rw [hO8.2, ss_ite_neg hne42.symm, hO7.2, ss_ite_pos rfl, hlev]
  have hrU : (treeOf i s w8).obj (w.next + 4) = some (.key ⟨wLevel s w x + 1, false,
      ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩) := by
    rw [hO8.2, ss_ite_pos rfl, hlev, keyLevel_succ]
  -- the levels: the new root is below q
  obtain ⟨gq, hq', -, -, -, hlq, hleafq⟩ := h.books.levels q nq hq3 hq4
  have hq0 : hq' = 0 := by
    rw [hql] at hleafq
    exact (beq_iff_eq.mp hleafq.symm)
  have hlevq : wLevel s w x + 1 < wLevel s w q := by
    rw [hlev, hlq, hq0] at hlt ⊢
    exact ssg_level_seg p hH1 hlt
  -- q's node
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  have hnq := hI.sound.nodes q hqr _ hAq
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq
  rw [ksOf_length] at hnqs
  have hkq8 : w8.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq8 : w8.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  obtain ⟨tq, rq, hrq⟩ := h.books.timeFirst q nq hq3 hq4
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq [(k1, w.next + 4)]
  obtain ⟨hOQ, hSQ, hrootQ, hxB, hRB, -, hBQ⟩ := ssg_seg_core hp hb h htx hq3 hq4 hqx hql hk1
    hqr hlevq (by rw [hlev, ← keyLevel_succ, heightOf_keyLevel p hH1]; simp) hsplit hL1 hfl
    hsl hlf hls hwff hwfs hszf hszs hkf hks (first := w.next)
    (second := w.next + 2) (r := w.next + 4) hO8.1 htopU hntU hkU hlkU hwlU hobjU hfU hsU hrU
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) (Nat.le_add_right _ _) hne20.symm hne40
    hne42 (mq := addAll i nq [(k1, w.next + 4)]) (ex' := some q)
    (by rw [addAll_live hnqwf]; rfl) (addAll_wf hnqwf _)
    (by
      simp only [bnd, ite_true]
      have := addAll_size i nq [(k1, w.next + 4)]
      simp only [List.length_singleton] at this
      omega)
    (addAll_leaf i nq _)
    (fun c y hy => by
      rcases (addAll_key_mem _ nq).mp (ss_key_ksOf hy) with h1 | h1
      · exact Or.inl h1
      · simp only [List.mem_singleton, Prod.mk.injEq] at h1
        exact Or.inr h1.2)
    (by rw [hrq', hrq]; rfl)
    (fun t ht => addAll_timesLe (ss_timesLe (h.books.times q nq hq3)) _ t (ss_time_ksOf ht))
    (fun n0 hs0' => addAll_ext (prim_timesBefore (hb.times q n0 hs0'))
      (frame_overlay_ext hO8.1.frame hlkq8 hkq8 hs0').2.2 _)
    (by rw [hrq']; simp)
  obtain ⟨hP8, hnd8⟩ := ssg_path_keep h hnx hpU htopU hkU hlkU
    (fun z _ hz => hobjU z (Nat.ne_of_lt hz) (ss_ne_of_lt_add hz) (ss_ne_of_lt_add hz))
  have hpre : CasPreG p i base s tp w8 d q nq [(k1, w.next + 4)] C :=
    ⟨hlkq8, ⟨cq, by rw [hpU]; exact hq1⟩, hP8, hnd8, hO8.1.toBooks (fun _ h => h), hnqwf, hnqs,
      Or.inl rfl, fun a y1 b y2 e => by simp at e,
      ⟨hrootQ, hSQ, hOQ.frame, hOQ.top, hBQ, hOQ.toBooks (fun _ h => h)⟩⟩
  refine WP.mono (hup q _ w8 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine ssg_cutBack hb h hin hon' hpU (by rw [hn8]; exact Nat.le_add_right _ _) hlkU hlkUx
    (hxB hxn.symm) (fun z hz => ?_) hpost
  rcases hRB z hz with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1]; exact Or.inr (Nat.le_refl _)
  · rw [h1]; exact Or.inr (Nat.le_add_right _ _)
  · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

theorem ssg_seg_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hup : UpOkG p i base s tp v up d)
    (hupo : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → w.outside = []))
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin', hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_klongAt rfl hon') ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact ssg_seg_new_post hp hb h hup hupo hcase hin hgh hq1 hq3 hql hon' hH rfl rfl rfl rfl rfl rfl
    rfl rfl

/-! ## 7. Under a segment leaf: x made by the transaction (`split.space2.inplace`) -/

theorem ssg_seg_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} {k1 j : Nat} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) (hon' : w.path[d + 1]? = some (some k1, x))
    (hj : nq.linkIndex x k1 = some j)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = (ssNote w4 "split.space2.inplace").afterNewKey p g (hh + 1) false
      [.time i, .key 0 x, .key sc w.next])
    (e6 : w6 = ssMF w5 (w.next + 2) (w5.madeFor.lookup x)) :
    CasPost p i base s tp w (d + 1) x n ins C () (w6.withNode q (nq.repoint j (w.next + 2))) := by
  intro hout
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, hlt, -, hnx⟩ :=
    ssg_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := ssg_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  -- the bound of the new root
  have hout6 : w6.outside = [] := hout
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e6, e5] at hout6
      simp [ssMF, MW.afterNewKey, hc] at hout6
    · exact hc
  -- the states
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl)
      (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0)
      (by rw [hf1]; simp) (fun z _ hz => hz)
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2]; exact hn1
  have hO5 : SsOk p i base s tp (fun _ => False) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩)
        else (treeOf i s w4).obj z := by
    rw [e5, ← hn4]
    refine ssOk_newKey hb (hO4.1.congr (w' := ssNote w4 "split.space2.inplace") rfl rfl rfl rfl
      rfl rfl rfl rfl rfl) hgG hH1 (by simp)
      (Or.inr ⟨_, rfl⟩) (by simp) (by simp)
  have hO6 : SsOk p i base s tp (fun _ => False) w6 := by
    rw [e6]
    exact hO5.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT6 : treeOf i s w6 = treeOf i s w5 := by rw [e6]; rfl
  -- the state before q's klong is pointed
  have hxn : x ≠ w.next := Nat.ne_of_lt hxlt
  have hxn2 : x ≠ w.next + 2 := ss_ne_of_lt_add hxlt
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hpU : w6.path = w.path := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have htopU : w6.top = w.top := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hntU : w6.newTop = w.newTop := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hkU : w6.taken = w.taken := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hn6 : w6.next = w.next + 4 := by
    rw [e6, e5]
    show w4.next + 2 = _
    rw [hn4]
  have hlkU : ∀ y, y ≠ x → y < w.next → w6.nodes.lookup y = w.nodes.lookup y := by
    intro y hyx hy
    rw [show w6.nodes = w5.nodes by rw [e6]; rfl, e5,
      ss_lookup_newKey (w := ssNote w4 "split.space2.inplace")
        (by show y ≠ w4.next; rw [hn4]; exact ss_ne_of_lt_add hy),
      show (ssNote w4 "split.space2.inplace").nodes = w4.nodes from rfl, e4,
      ss_lookup_withNode (Nat.ne_of_lt hy), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hy)]
  have hwlU : ∀ y, y < w.next → wLevel s w6 y = wLevel s w y := by
    intro y hy
    rw [show wLevel s w6 = wLevel s w5 by rw [e6]; rfl, e5,
      prim_wLevel_afterNewKey (w := ssNote w4 "split.space2.inplace")
        (by show y ≠ w4.next; rw [hn4]; exact ss_ne_of_lt_add hy)]
    show wLevel s w4 y = _
    rw [show wLevel s w4 = wLevel s w3 by rw [e4]; rfl, hwl3, hwl1 y (Nat.ne_of_lt hy)]
  have hobjU : ∀ z, z ≠ x → z ≠ w.next → z ≠ w.next + 2 →
      (treeOf i s w6).obj z = (treeOf i s w).obj z := by
    intro z h1 h2 h4
    rw [hT6, hO5.2, ss_ite_neg h4, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h1, hT2, hO1.2,
      ss_ite_neg h2]
  have hfU : (treeOf i s w6).obj x = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [hT6, hO5.2, ss_ite_neg hxn2, hO4.2, ss_ite_neg hxn, hO3.2, ss_ite_pos rfl]
  have hsU : (treeOf i s w6).obj w.next = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by
    rw [hT6, hO5.2, ss_ite_neg hne20.symm, hO4.2, ss_ite_pos rfl, hlev]
  have hrU : (treeOf i s w6).obj (w.next + 2) = some (.key ⟨wLevel s w x + 1, false,
      ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩) := by
    rw [hT6, hO5.2, ss_ite_pos rfl, hlev, keyLevel_succ]
  -- the levels: the new root is below q
  obtain ⟨gq, hq', -, -, -, hlq, hleafq⟩ := h.books.levels q nq hq3 hq4
  have hq0 : hq' = 0 := by
    rw [hql] at hleafq
    exact (beq_iff_eq.mp hleafq.symm)
  have hlevq : wLevel s w x + 1 < wLevel s w q := by
    rw [hlev, hlq, hq0] at hlt ⊢
    exact ssg_level_seg p hH1 hlt
  -- q's node
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  have hnq := hI.sound.nodes q hqr _ hAq
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq
  rw [ksOf_length] at hnqs
  have hkq6 : w6.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq6 : w6.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  obtain ⟨tq, rq, hrq⟩ := h.books.timeFirst q nq hq3 hq4
  obtain ⟨rq', hrq'⟩ := repoint_first hrq j (w.next + 2)
  obtain ⟨hOQ, hSQ, hrootQ, -, hRB, hxW0, hBQ⟩ := ssg_seg_core hp hb h htx hq3 hq4 hqx hql hk1
    hqr hlevq (by rw [hlev, ← keyLevel_succ, heightOf_keyLevel p hH1]; simp) hsplit hL1 hfl
    hsl hlf hls hwff hwfs hszf hszs hkf hks (first := x)
    (second := w.next) (r := w.next + 2) hO6 htopU hntU hkU hlkU hwlU hobjU hfU hsU hrU
    (Or.inl rfl) (Nat.le_refl _) (Nat.le_add_right _ _) hxn hxn2.symm hne20
    (mq := nq.repoint j (w.next + 2)) (ex' := none) (repoint_live hnqwf hj _)
    (repoint_wf hnqwf hj _)
    (by simp only [bnd, reduceCtorEq, ite_false]; rw [repoint_size]; exact hnqs)
    (repoint_leaf nq j _)
    (fun c y hy => by
      rcases repoint_key_mem hj (ss_key_ksOf hy) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1.2)
    (by rw [hrq', hrq]; rfl)
    (fun t ht => repoint_timesLe (ss_timesLe (h.books.times q nq hq3)) j _ t (ss_time_ksOf ht))
    (fun n0 hs0' => Or.inr (repoint_ext hj
      (fun c' hc' => by
        have := hn q n0 hs0' c' x hc'
        rw [hsx] at this
        cases this)
      (frame_overlay_ext hO6.frame hlkq6 hkq6 hs0').2.2 _))
    (by rw [hrq']; simp)
  refine ⟨ss_pinv hOQ hrootQ hSQ hBQ, ⟨hpU, ?_, ?_, ?_⟩⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) (some k1) le_rfl (by rw [e]; exact hon')
    have hyq : y ≠ q := fun e => hnot d cq (by omega) (by rw [e]; exact hq1)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyq, hlkU y hyx hylt]
    exact hy
  · show w.next ≤ w6.next
    rw [hn6]
    exact Nat.le_add_right _ _
  · intro z hz
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]; exact Or.inl hxW0
    · rw [h1]; exact Or.inr (Nat.le_refl _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

/-- q's node through the steps of `split.space2.inplace`. -/
theorem ssg_lookup6 {p : MParams} {g hh : Nat} {leaf : Bool} {f s2 : MNode}
    {x q r : NodeId} {o : Option NodeId} {t : String} {ks : List MKlong} {w w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = (ssNote w4 t).afterNewKey p g (hh + 1) false ks)
    (e6 : w6 = ssMF w5 r o) (hqx : q ≠ x) (hqlt : q < w.next) :
    w6.nodes.lookup q = w.nodes.lookup q := by
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2, e1]; rfl
  rw [e6]
  show w5.nodes.lookup q = _
  rw [e5, ss_lookup_newKey (w := ssNote w4 t)
    (by show q ≠ w4.next; rw [hn4]; exact ss_ne_of_lt_add hqlt)]
  show w4.nodes.lookup q = _
  rw [e4, ss_lookup_withNode (Nat.ne_of_lt hqlt), e3, ss_lookup_withNode hqx, e2]
  show w1.nodes.lookup q = _
  rw [e1]
  exact ss_lookup_newKey (w := ssSp w) (Nat.ne_of_lt hqlt)

theorem ssg_seg_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (h : CasPreG p i base s tp w (d + 1) x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true, hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_klongAt rfl hon') ?_
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  obtain ⟨_, _, q', _, hq1', -, -, -, hqx, -⟩ := ssg_path hb h hon htx
  rw [hq1] at hq1'
  cases hq1'
  refine ss_wp_step (getNode_hit _ ((ssg_lookup6 rfl rfl rfl rfl rfl rfl hqx hqlt).trans hq3)) ?_
  cases hj : nq.linkIndex x k1 with
  | none =>
    simp only
    rw [wp_bind]
    exact wp_throw _ _ _ _
  | some j =>
    simp only
    by_cases hlt : (nq.lastTime != some i) = true
    · rw [ss_ite_pos hlt, wp_bind]
      exact wp_throw _ _ _ _
    · rw [ss_ite_neg hlt]
      refine ss_wp_step (putNode_eq _ _ _ _) ?_
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine (wp_pure _ _ _ _).mpr ?_
      exact ssg_seg_inPlace_post hp hb hn h hcase hin hgh hq1 hq3 hql hon' hj hH rfl rfl rfl rfl
        rfl rfl

/-! ## 8. The step

The six cases of `handleFullWith`'s space split: at the space root (x made by
the transaction or not), under an inner parent (the same), and under a segment
leaf (`split.space2.inplace`, `split.space2`). -/

theorem handleFull_space_g {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s) {depth : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (h : CasPreG p i base s tp w depth x n ins C)
    (hup : ∀ d, depth = d + 1 → UpOkG p i base s tp v up d)
    (hupo : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP (up q ins) { p := p, i := i, view := v } w (fun _ w' => w'.outside = [] → w.outside = []))
    (hcase : p.splitAbove < (n.lastVersion i).size) :
    WP (SIS.Tree.handleFullWith up depth x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w depth x n ins C) := by
  cases depth with
  | zero =>
    by_cases hin : n.firstTime = some i
    · exact ss_root_inPlace hp hb (ssg_casPre0 h) hcase hin
    · exact ss_root_new hp hb (ssg_casPre0 h) hcase hin
  | succ d =>
    obtain ⟨c0, hon⟩ := h.on
    have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
    obtain ⟨k1, cq, q, nq, hq1, hon', hq3, -⟩ := ssg_path hb h hon htx
    cases hql : nq.leaf with
    | false =>
      by_cases hin : n.firstTime = some i
      · exact ssg_parent_inPlace hp hb h (hup d rfl) hcase hin hq1 hq3 hql
      · exact ssg_parent_new hp hb h (hup d rfl) hcase hin hq1 hon' hq3 hql
    | true =>
      by_cases hin : n.firstTime = some i
      · exact ssg_seg_inPlace hp hb hn h hcase hin hq1 hon' hq3 hql
      · exact ssg_seg_new hp hb h (hup d rfl) (hupo d rfl) hcase hin hq1 hon' hq3 hql

end Contract
