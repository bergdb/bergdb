/-
The contract package (bergdb 030-10): `handleFullWith` when it does a space
split, while a new segment leaf has no klong yet (`CasPreO`,
WriterCascadeDefsO.lean).
-/
import Contract.Proof.WriterSpaceSplitG
import Contract.Proof.WriterCascadeDefsO

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. The map with the nodes of fs set -/

theorem sso_ov_cons (a : NodeId × Obj) (fs : List (NodeId × Obj)) (T : Tree) :
    ovSet (a :: fs) T = ovSet fs (T.set a.1 a.2) := rfl

theorem sso_ov_out : ∀ (fs : List (NodeId × Obj)) (T : Tree) {z : NodeId},
    z ∉ fs.map (·.1) → (ovSet fs T).obj z = T.obj z
  | [], _, _, _ => rfl
  | a :: fs, T, z, hz => by
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    rw [sso_ov_cons, sso_ov_out fs _ hz.2]
    simp [Tree.set, hz.1]

theorem sso_ov_in : ∀ (fs : List (NodeId × Obj)) (T T' : Tree) {z : NodeId},
    z ∈ fs.map (·.1) → (ovSet fs T).obj z = (ovSet fs T').obj z
  | [], _, _, _, hz => by simp at hz
  | a :: fs, T, T', z, hz => by
    rw [sso_ov_cons, sso_ov_cons]
    by_cases h : z ∈ fs.map (·.1)
    · exact sso_ov_in fs _ _ h
    · rw [sso_ov_out fs _ h, sso_ov_out fs _ h]
      simp only [List.map_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · simp [Tree.set, hz]
      · exact absurd hz h

theorem sso_ov_some : ∀ (fs : List (NodeId × Obj)) (T : Tree) {z : NodeId},
    z ∈ fs.map (·.1) → ((ovSet fs T).obj z).isSome = true
  | [], _, _, hz => by simp at hz
  | a :: fs, T, z, hz => by
    rw [sso_ov_cons]
    by_cases h : z ∈ fs.map (·.1)
    · exact sso_ov_some fs _ h
    · rw [sso_ov_out fs _ h]
      simp only [List.map_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · simp [Tree.set, hz]
      · exact absurd hz h

theorem sso_ov_roots : ∀ (fs : List (NodeId × Obj)) (T : Tree), (ovSet fs T).roots = T.roots
  | [], _ => rfl
  | a :: fs, T => by rw [sso_ov_cons, sso_ov_roots fs]; rfl

theorem sso_ov_root (fs : List (NodeId × Obj)) (T : Tree) : (ovSet fs T).root = T.root := by
  unfold Tree.root
  rw [sso_ov_roots]

/-- Two maps that agree off the nodes of fs agree with fs set. -/
theorem sso_ov_agree {fs : List (NodeId × Obj)} {T T' : Tree} {z : NodeId}
    (h : z ∉ fs.map (·.1) → T'.obj z = T.obj z) : (ovSet fs T').obj z = (ovSet fs T).obj z := by
  by_cases hz : z ∈ fs.map (·.1)
  · exact sso_ov_in fs _ _ hz
  · rw [sso_ov_out fs _ hz, sso_ov_out fs _ hz]
    exact h hz

/-! ## 2. The books over `newSuperRoot`, with nodes without klongs -/

theorem sso_putBooksE_afterSuperRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree}
    (y : NodeId) {w : MW} (hk : PutBooksE p i base s w) :
    PutBooksE p i base s (MW.afterSuperRoot w p i y) := by
  obtain ⟨-, -, h1, h2, h3, h4, -, -, h7⟩ := afterSuperRoot_fields w p i y
  have hlev : ∀ x n, w.nodes.lookup x = some n →
      wLevel s (MW.afterSuperRoot w p i y) x = wLevel s w x :=
    fun x n hl => wLevel_afterSuperRoot s p i y (Nat.ne_of_lt (hk.ids.1 x n hl))
  have hmade : ∀ x, x ∈ w.made.map (·.id) →
      x ∈ (MW.afterSuperRoot w p i y).made.map (·.id) := by
    intro x hx
    cases hnt : w.newTop
    · rw [(afterSuperRoot_new hnt p i y).1, List.map_append]
      exact List.mem_append_left _ hx
    · rw [(afterSuperRoot_inPlace hnt p i y).1]
      exact hx
  have hids : ((∀ x n, (MW.afterSuperRoot w p i y).nodes.lookup x = some n →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ x h, (MW.afterSuperRoot w p i y).vals.lookup x = some h →
        x < (MW.afterSuperRoot w p i y).next) ∧
      (∀ m ∈ (MW.afterSuperRoot w p i y).made, m.id < (MW.afterSuperRoot w p i y).next ∧
        base ≤ m.id) ∧
      base ≤ (MW.afterSuperRoot w p i y).next ∧
      ((MW.afterSuperRoot w p i y).newTop = true →
        (MW.afterSuperRoot w p i y).top.id < (MW.afterSuperRoot w p i y).next)) := by
    obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hk.ids
    cases hnt : w.newTop
    · rw [afterSuperRoot_of_false hnt]
      refine ⟨fun x n hl => Nat.lt_add_right 2 (hi1 x n hl),
        fun x h hl => Nat.lt_add_right 2 (hi2 x h hl), fun m hm => ?_, by
          show base ≤ w.next + 2; omega, fun _ => by show w.next < w.next + 2; omega⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨Nat.lt_add_right 2 (hi3 m hm).1, (hi3 m hm).2⟩
      · simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨by show w.next < w.next + 2; omega, hi4⟩
    · rw [afterSuperRoot_of_true hnt]
      exact ⟨hi1, hi2, hi3, hi4, hi5⟩
  refine ⟨?_, ?_, ?_, hids, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h3]
    exact hk.first
  · rw [h1]
    exact hk.times
  · intro x n hl ht
    rw [h1] at hl
    rw [h3] at ht
    obtain ⟨g, h, hg, hG, hH, hL, hleaf⟩ := hk.levels x n hl ht
    exact ⟨g, h, by rw [h4]; exact hg, hG, hH, by rw [hlev x n hl]; exact hL, hleaf⟩
  · rw [h3]
    exact fun x hx => hmade x (hk.taken x hx)
  · rw [h1]
    intro x n hl
    rcases hk.overlay x n hl with h | h
    · exact Or.inl h
    · exact Or.inr (hmade x h)
  · rw [h7]
    exact hk.within
  · rw [h1, h3]
    exact hk.timeFirst
  · rw [h1, h3]
    exact hk.empty

/-- `newSuperRoot r` keeps what the steps keep. -/
theorem ssoOk_superRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {E : NodeId → Prop} (hb : Books i base s tp) (hO : SsOk p i base s tp E w) (r : NodeId) :
    SsOk p i base s tp E (MW.afterSuperRoot w p i r) ∧
      (treeOf i s (MW.afterSuperRoot w p i r)).obj = (treeOf i s w).obj ∧
      (treeOf i s (MW.afterSuperRoot w p i r)).root = some r ∧
      (MW.afterSuperRoot w p i r).top.rootKey = r := by
  obtain ⟨hobjF, hrootF, hdirtyF⟩ := treeOf_afterSuperRoot i s p r hO.books.ids.1
  obtain ⟨hrk, -, hnodes, -, htaken, -⟩ := afterSuperRoot_fields w p i r
  refine ⟨⟨?_, sso_putBooksE_afterSuperRoot r hO.books,
    topInv_afterSuperRoot r hO.top hb hO.books.ids.2.2.2.1, ?_⟩, hobjF, hrootF, hrk⟩
  · obtain ⟨f1, f2, -⟩ := hO.frame
    refine ⟨fun y o hy => ?_, fun y m hy hsy => ?_,
      ⟨[(i, r)], treeOf_afterSuperRoot_roots i s p r w, by simp⟩⟩
    · obtain ⟨o', h1, h2, h3⟩ := f1 y o hy
      exact ⟨o', by rw [hobjF]; exact h1, h2, by rw [hdirtyF]; exact h3⟩
    · rw [hdirtyF]
      rw [hobjF] at hy
      exact f2 y m hy hsy
  · intro y m hy hty he
    rw [hnodes] at hy
    rw [htaken] at hty
    exact hO.empty y m hy hty he

/-- `PInvO` of a state that keeps what the steps keep, with only the nodes of
fs without klongs, and its map with fs set sound from its root. -/
theorem sso_pinv {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {fs : List (NodeId × Obj)} {ex : Option NodeId} {C : List (Key × Nat)} {w : MW}
    (hO : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w)
    (hr : (treeOf i s w).root = some w.top.rootKey)
    (hS : Sound p.M ex (ovSet fs (treeOf i s w)) w.top.rootKey C)
    (hB : Balanced p (ovSet fs (treeOf i s w))) :
    PInvO p i base s tp fs ex C w :=
  ⟨hr, hS, hO.frame, hO.top, hB, hO.books, hO.empty⟩

/-! ## 3. The state before the step -/

/-- The state before the step keeps what the steps keep, and its map is that
of the state with the klongs added (the "if" state), but at x. -/
theorem sso_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreO p i base s tp fs w depth x n ins C)
    (htx : w.taken.contains x = false) :
    SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w ∧
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
  refine ⟨⟨?_, h.books, hI.top, ?_⟩, hAx, hAz⟩
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
    by_cases hyx : y = x
    · rw [hyx, h.look] at hy
      cases hy
      obtain ⟨t, rest, hr⟩ := h.first
      rw [hr] at he
      cases he
    · refine hI.empties y m ?_ hty he
      rw [MW.withNode, lookup_upsert_ne _ _ hyx]
      exact hy

/-- x cut back to before the transaction: its klongs of s. -/
theorem sso_toPrev {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreO p i base s tp fs w depth x n ins C)
    (htx : w.taken.contains x = false) {n0 : KNode} (hs : s.obj x = some (.key n0)) :
    ksOf (n.toPrev (i - 1)) = n0.ks := by
  obtain ⟨-, hAx, -⟩ := sso_start hb h htx
  obtain ⟨o', ho', he, -⟩ := h.hyp.frame.1 x _ hs
  rw [hAx] at ho'
  cases ho'
  exact (ss_ext_of_addAll (prim_timesBefore (hb.times x n0 hs)) (hb.first x n0 hs)
    (ss_timesLe (h.books.times x n h.look)) he.2.2).1

/-- A node that a key klong of x with the klongs added names exists in the
"if" state's map with fs set, if x is reached there. -/
theorem sso_named_some {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w depth x n ins C) (htx : w.taken.contains x = false)
    (hxF : x ∉ fs.map (·.1))
    (hx : x ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey)
    {y : NodeId} (hy : ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) :
    ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj y).isSome = true := by
  obtain ⟨-, hAx, -⟩ := sso_start hb h htx
  obtain ⟨c', hc'⟩ := hy
  exact ss_nodeOk_names (h.hyp.sound.nodes x hx _ (by rw [sso_ov_out fs _ hxF]; exact hAx)) hc'

/-! ## 4. The key access path above x -/

/-- Above x the path is in the "if" state's map with fs set (A') a chain from
the space root: x is not on it (`nodup`), its parent q is reached in A' with a
live klong (k1, x) to x, x is on a lower level, one lower if q is an inner
node. No node of the path is a node of fs. -/
theorem sso_path {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    {c0 : Option Nat} (hon : w.path[d + 1]? = some (c0, x)) (htx : w.taken.contains x = false) :
    ∃ k1 cq q nq, w.path[d]? = some (cq, q) ∧ w.path[d + 1]? = some (some k1, x) ∧
      w.nodes.lookup q = some nq ∧ w.taken.contains q = false ∧ q ≠ x ∧
      (k1, x) ∈ live (ksOf nq) ∧
      q ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
        ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
        w.top.rootKey ∧
      wLevel s w x < wLevel s w q ∧ (nq.leaf = false → wLevel s w x + 1 = wLevel s w q) ∧
      (∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) ∧
      q ∉ fs.map (·.1) ∧ x ∉ fs.map (·.1) := by
  obtain ⟨-, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  have hxF : x ∉ fs.map (·.1) := h.away (d + 1) c0 x le_rfl hon
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    rw [hux] at hu
    exact h.nodup e (d + 1) c c0 x (by omega) le_rfl hu hon
  have hreach : ∀ e, e ≤ d + 1 → ∀ c u, w.path[e]? = some (c, u) →
      u ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
        ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
        w.top.rootKey := by
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
      rw [← hAz u' hux, ← sso_ov_out fs _ (h.away e c0' u' (by omega) h1)] at h3
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
  have hqF : q ∉ fs.map (·.1) := h.away d c0' q (by omega) h1
  have hqr := hreach d (by omega) _ _ h1
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s h6 h7]
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _
    (by rw [sso_ov_out fs _ hqF]; exact hAq)
  have hlt : wLevel s w x < wLevel s w q := by
    rcases hgq.kind (by rw [sso_ov_out fs _ hqF]; exact hAq) h4 with
      ⟨_, _, v, hv⟩ | ⟨_, m, _, _, hm1, hm2, _, _⟩
    · rw [sso_ov_out fs _ hxF, hAx] at hv; cases hv
    · rw [sso_ov_out fs _ hxF, hAx] at hm1; cases hm1; exact hm2
  refine ⟨k1, c0', q, nq, h1, hon, h6, h7, hqx, h4, hqr, hlt, fun hl => ?_, hnx, hqF, hxF⟩
  obtain ⟨-, -, hb3⟩ := hI.balanced q
    (by rw [reach_of_root (by rw [sso_ov_root]; exact hI.root)]; exact hqr) _
    (by rw [sso_ov_out fs _ hqF]; exact hAq)
  obtain ⟨m', hm1, hm2⟩ := hb3 hl k1 x h4
  rw [sso_ov_out fs _ hxF, hAx] at hm1
  cases hm1
  exact hm2

/-- Above x, a state with the path, the top, the nodes taken back and the
nodes of the path as before, and the map as before on the nodes of before but
x, keeps the path. -/
theorem sso_path_keep {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) {wU : MW}
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hobjU : ∀ z, z ≠ x → z < w.next → (treeOf i s wU).obj z = (treeOf i s w).obj z) :
    PathOk i s wU d ∧ (∀ e e' c c' u, e < e' → e' ≤ d → wU.path[e]? = some (c, u) →
      wU.path[e']? = some (c', u) → False) ∧
      ∀ e c u, e ≤ d → wU.path[e]? = some (c, u) → u ∉ fs.map (·.1) := by
  refine ⟨⟨by rw [hpU, htopU]; exact h.path.root, fun e he => ?_, fun e he => ?_⟩, ?_, ?_⟩
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
  · intro e c u he h1
    rw [hpU] at h1
    exact h.away e c u (by omega) h1

/-! ## 5. At the space root -/

theorem sso_notF {fs : List (NodeId × Obj)} {a b e : Nat}
    (hav : ∀ e ∈ fs.map (·.1), e < a ∨ b ≤ e) (h1 : a ≤ e) (h2 : e < b) : e ∉ fs.map (·.1) :=
  fun he => by rcases hav e he with h | h <;> omega

theorem sso_lt4 {a b : Nat} (h : a + 4 ≤ b) : a < b ∧ a + 2 < b := by omega

theorem sso_root_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = (ssNote w4 "split.space3.inplace").afterNewKey p g (hh + 1) false
      [.time i, .key 0 x, .key sc w.next])
    (e6 : w6 = ssMF w5 (w.next + 2) (w5.madeFor.lookup x)) :
    CasPostO p i base s tp fs w 0 x n ins C () (MW.afterSuperRoot w6 p i (w.next + 2)) := by
  intro hout hav
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx (by obtain ⟨t, r, hr⟩ := h.first; rw [hr]; simp)
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  have hA0 := (treeOf_freshE hb hI.books (Nat.le_refl w.next)).1
  have hA2 := (treeOf_freshE hb hI.books (Nat.le_add_right w.next 2)).1
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hxreach : x ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  -- the bound of the new root
  have hout6 : w6.outside = [] := by
    rw [← hout]
    exact ((afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.2).symm
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
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl)
      (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.first
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO3 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w3 ∧
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
  have hO4 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz'.resolve_right hz)
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2]; exact hn1
  have hO5 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩)
        else (treeOf i s w4).obj z := by
    rw [e5, ← hn4]
    refine ssOk_newKey hb (hO4.1.congr (w' := ssNote w4 "split.space3.inplace") rfl rfl rfl rfl
      rfl rfl rfl rfl rfl) hgG hH1 (by simp)
      (Or.inr ⟨_, rfl⟩) (by simp) (fun z hz => hz.resolve_left (fun h => by cases h.2))
  have hO6 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w6 := by
    rw [e6]
    exact hO5.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT6 : treeOf i s w6 = treeOf i s w5 := by rw [e6]; rfl
  -- the map after the step, and with fs set
  obtain ⟨hOF, hobjF, hrootF, hrkF⟩ := ssoOk_superRoot hb hO6 (w.next + 2)
  have h6 : w6.next = w.next + 4 := by rw [e6, e5]; show w4.next + 2 = _; rw [hn4]
  have hFn : w.next + 4 ≤ (MW.afterSuperRoot w6 p i (w.next + 2)).next := by
    rw [← h6]; exact ss_afterSuperRoot_next w6 p i _
  have hxF : x ∉ fs.map (·.1) := h.away 0 c0 x le_rfl hon
  have hF0 : w.next ∉ fs.map (·.1) := sso_notF hav (Nat.le_refl _) (sso_lt4 hFn).1
  have hF2 : w.next + 2 ∉ fs.map (·.1) :=
    sso_notF hav (Nat.le_add_right _ _) (sso_lt4 hFn).2
  have hBr : (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj (w.next + 2) =
      some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩) := by
    rw [sso_ov_out fs _ hF2, hobjF, hT6, hO5.2, ss_ite_pos rfl]
  have hBs : (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj w.next =
      some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [sso_ov_out fs _ hF0, hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_add (by decide)), hO4.2,
      ss_ite_pos rfl]
  have hBx : (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj x =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [sso_ov_out fs _ hxF, hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_of_lt_add hxlt), hO4.2,
      ss_ite_neg (Nat.ne_of_lt hxlt), hO3.2, ss_ite_pos rfl]
  have hBo : ∀ z, z ≠ w.next + 2 → z ≠ w.next → z ≠ x →
      (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z h1 h2 h3
    refine sso_ov_agree (fun _ => ?_)
    rw [hobjF, hT6, hO5.2, ss_ite_neg h1, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h3, hT2, hO1.2,
      ss_ite_neg h2, hAz z h3]
  have hBA : ∀ z, ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z).isSome = true →
      ((ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj z).isSome = true := by
    intro z hz
    by_cases h1 : z = w.next + 2
    · rw [h1, hBr]; rfl
    by_cases h2 : z = w.next
    · rw [h2, hBs]; rfl
    by_cases h3 : z = x
    · rw [h3, hBx]; rfl
    rw [hBo z h1 h2 h3]
    exact hz
  have hS : Sound p.M (some x) (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      w.top.rootKey C := hI.sound
  rw [← hxr] at hS
  have hAx' : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [sso_ov_out fs _ hxF]; exact hAx
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx' hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (sso_named_some hb h htx hxF hxreach (hm c y hy))
  have hNf : NodeIs (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))) x
      (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs hBx hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))) w.next
      (wLevel s w x) n.leaf (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))) (w.next + 2)
      (wLevel s w x + 1) false [(0, x), (sc, w.next)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBx]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, -, hRB⟩ := Sound.spaceSplitRoot hS hAx' hsplit hL1 (Or.inl rfl)
    (by rw [sso_ov_out fs _ hF0]; exact hA0) (Nat.ne_of_lt hxlt)
    (by rw [sso_ov_out fs _ hF2]; exact hA2)
    ⟨(ss_ne_of_lt_add hxlt).symm, (ss_ne_add (by decide)).symm⟩ hNf hNs
    hNr (by rw [hBx]; rfl) (fun z h1 _ h3 h4 => hBo z h4 h3 h1)
  -- the balance rule in the map after the step, with fs set
  have hrA : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).root = some x := by
    rw [sso_ov_root, hxr]; exact hI.root
  have hxR : x ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
    rw [reach_of_root hrA]; exact tc_self _ _ _
  have hold : ∀ z, z ∉ [x, w.next, w.next + 2] →
      (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact hBo z hz.2.2 hz.2.1 hz.1
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · rw [hAx'] at hm; cases hm; exact ⟨_, hBx, rfl⟩
    · rw [sso_ov_out fs _ hF0, hA0] at hm; cases hm
    · rw [sso_ov_out fs _ hF2, hA2] at hm; cases hm)
  have hHL := ss_halves_live hsplit hlf hls
  have hBal : Balanced p (ovSet fs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2)))) := by
    refine ss_bal_of hI.balanced hrA (by rw [sso_ov_root]; exact hrootF) (fun z hz => ?_) hold
      hlevB (fun z hz _ m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · rw [hBx] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hfl rfl
          (fun c y hy => Or.inl (hHL.1 c y hy))
      · rw [hBs] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hsl hlev.symm
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [hBr] at hm; cases hm
        refine ss_rule_root (keyLevel_pos p g (hh + 1)) (by rw [heightOf_keyLevel p hH1]; simp)
          ⟨_, hBx, by rw [hlev, keyLevel_succ]⟩ ⟨_, hBs, by rw [keyLevel_succ]⟩
  refine ⟨sso_pinv hOF (by rw [hrkF]; exact hrootF) (by rw [hrkF]; exact hSB) hBal,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.1, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.1,
      show w6.nodes = w5.nodes by rw [e6]; rfl]
    have e5n : w5.nodes = w4.nodes ++ [(w4.next, ⟨false, [.time i, .key 0 x, .key sc w.next]⟩)] :=
      by rw [e5]; rfl
    rw [e5n, prim_lookup_append_ne _ _ (by rw [hn4]; exact ss_ne_of_lt_add hylt), e4, MW.withNode,
      lookup_upsert_ne _ _ (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · exact Nat.le_trans (ss_le_add h6) (ss_afterSuperRoot_next w6 p i (w.next + 2))
  · intro z hz
    unfold reachOfO at hz ⊢
    rw [hrkF] at hz
    have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]
      exact Or.inl (tc_self _ _ _)
    · rw [h1]
      exact Or.inr (Nat.le_refl _)
    · rw [h1]
      exact Or.inr (Nat.le_add_right _ _)

theorem sso_root_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w 0 x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true]
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
  refine ss_wp_step (newSuperRoot_eq v _ h.hyp.top) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine (wp_pure _ _ _ _).mpr ?_
  exact sso_root_inPlace_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl

theorem sso_lt6 {a b : Nat} (h : a + 6 ≤ b) : a < b ∧ a + 2 < b ∧ a + 4 < b := by omega

theorem sso_root_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 w7 w8 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = (ssNote w3 "split.space3").afterNewKey p g (hh + 1) false [])
    (e5 : w5 = ssMF w4 (w.next + 4) (some x))
    (e6 : w6 = w5.withNode w.next f) (e7 : w7 = w6.withNode (w.next + 2) s2)
    (e8 : w8 = w7.withNode (w.next + 4) ⟨false, [.time i, .key 0 w.next, .key sc (w.next + 2)]⟩) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } (MW.afterSuperRoot w8 p i (w.next + 4))
      (CasPostO p i base s tp fs w 0 x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hn2 : w2.next = w.next + 4 := by rw [e2]; show w1.next + 2 = _; rw [hn1]
  have hn3 : w3.next = w.next + 4 := by rw [e3]; exact hn2
  -- the node lookups through the steps
  have hlk : ∀ y, y ≠ w.next → y ≠ w.next + 2 → y ≠ w.next + 4 →
      w8.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2 h4
    rw [e8, ss_lookup_withNode h4, e7, ss_lookup_withNode h2, e6, ss_lookup_withNode h1,
      show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hlk9 : (MW.afterSuperRoot w8 p i (w.next + 4)).nodes.lookup x = some n := by
    rw [(afterSuperRoot_fields w8 p i _).2.2.1, hlk x (Nat.ne_of_lt hxlt)
      (ss_ne_of_lt_add hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  refine ss_wp_step (getNode_hit _ hlk9) ?_
  refine ss_wp_putNode ?_
  intro hout hav
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.first
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  have hA0 := (treeOf_freshE hb hI.books (Nat.le_refl w.next)).1
  have hA2 := (treeOf_freshE hb hI.books (Nat.le_add_right w.next 2)).1
  have hA4 := (treeOf_freshE hb hI.books (Nat.le_add_right w.next 4)).1
  have hxreach : x ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  -- the bound of the new root
  have hout4 : w4.outside = [] := by
    rw [← hout]
    show w4.outside = (MW.afterSuperRoot w8 p i (w.next + 4)).outside
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.2, e8, e7, e6, e5]
    rfl
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e4] at hout4
      simp [MW.afterNewKey, hc] at hout4
    · exact hc
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
  have hO3 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w3 := by
    rw [e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT3 : treeOf i s w3 = treeOf i s w2 := by rw [e3]; rfl
  have hfr3 := treeOf_freshE hb hO3.books (Nat.le_refl w3.next)
  rw [hn3] at hfr3
  obtain ⟨-, hs4, hn4', -, ht4, hm4⟩ := hfr3
  have hO4 : SsOk p i base s tp
      (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false, []⟩) else (treeOf i s w3).obj z := by
    rw [e4, ← hn3]
    exact ssOk_newKey hb (hO3.congr (w' := ssNote w3 "split.space3") rfl rfl rfl rfl rfl rfl rfl rfl
      rfl) hgG hH1 (by simp) (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
  have hO5 : SsOk p i base s tp
      (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hk5 : w5.taken = w.taken := by rw [e5, e4, e3, e2, e1]; rfl
  have hM5 : wLevel s w5 = wLevel s w4 := by rw [e5]; rfl
  have hw4n : ∀ y, y ≠ w.next + 4 → wLevel s w5 y = wLevel s w2 y := by
    intro y hy
    rw [hM5, e4, prim_wLevel_afterNewKey (w := ssNote w3 "split.space3")
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
    exact ss_wLevel_newKey (w := ssNote w3 "split.space3") p g (hh + 1) false []
      (by show s.obj w3.next = none; rw [hn3]; exact hs4)
      (by show ∀ m ∈ w3.made, m.id ≠ w3.next; rw [hn3]; exact hm4)
  have hN5 : ∀ y, y ≠ w.next + 4 → y ≠ w.next + 2 → w5.nodes.lookup y = w1.nodes.lookup y := by
    intro y h4 h2
    rw [show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2)]
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hold5 : ∀ y, y < w.next → (treeOf i s w5).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT5, hO4.2, ss_ite_neg (ss_ne_of_lt_add hy), hT3, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy),
      hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO6 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w5).obj z := by
    rw [e6, ← hwl0]
    refine ssOk_withNode hO5 (m := ⟨n.leaf, []⟩)
      (by rw [hN5 _ (ss_ne_add (by decide)) (ss_ne_add (by decide)), hlk1n])
      (by rw [hk5]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr (Or.inl hz')
      · exact Or.inr (Or.inr hz')
      · exact absurd hz' hz
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne40 : w.next + 4 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne42 : w.next + 4 ≠ w.next + 2 := by
    have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
    rw [Nat.add_assoc] at this
    exact this.symm
  have hlk1 : w1.nodes.lookup (w.next + 2) = none := by rw [← hn1]; rw [hn1]; exact hn2'
  have hO7 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4) w7 ∧
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
        ss_lookup_newKey (w := ssNote w3 "split.space3")
          (by show _ ≠ w3.next; rw [hn3]; exact hne42.symm),
        show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hlk1)
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hO8 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w8 ∧
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
      (by simp) (fun _ hz h => h.resolve_right hz)
    · rw [e7, ss_lookup_withNode hne42, e6, ss_lookup_withNode hne40,
        show w5.nodes = w4.nodes by rw [e5]; rfl, e4, ← hn3]
      exact prim_lookup_append_self (l := (ssNote w3 "split.space3").nodes) _
        (by show w3.nodes.lookup w3.next = none; rw [hn3]; exact hn4')
  obtain ⟨hO9, hobj9, hroot9, hrk9⟩ := ssoOk_superRoot hb hO8.1 (w.next + 4)
  have htx9 : (MW.afterSuperRoot w8 p i (w.next + 4)).taken.contains x = false := by
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.1, e8, e7, e6]
    show w5.taken.contains x = false
    rw [hk5]; exact htx
  have hO10 := ssOk_withNode (E' := fun z => z ∈ fs.map (·.1)) hO9 hlk9 htx9 rfl
    (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (sso_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  -- the map after the step, and with fs set
  have hxn : x ≠ w.next := Nat.ne_of_lt hxlt
  have hxn2 : x ≠ w.next + 2 := ss_ne_of_lt_add hxlt
  have hxn4 : x ≠ w.next + 4 := ss_ne_of_lt_add hxlt
  have h8 : w8.next = w.next + 6 := by
    rw [e8, e7, e6, e5, e4]
    show w3.next + 2 = _
    rw [hn3]
  have hFn : w.next + 6 ≤ ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))).next := by
    rw [← h8]; exact ss_afterSuperRoot_next w8 p i _
  have hxF : x ∉ fs.map (·.1) := h.away 0 c0 x le_rfl hon
  have hF0 : w.next ∉ fs.map (·.1) := sso_notF hav (Nat.le_refl _) (sso_lt6 hFn).1
  have hF2 : w.next + 2 ∉ fs.map (·.1) :=
    sso_notF hav (Nat.le_add_right _ _) (sso_lt6 hFn).2.1
  have hF4 : w.next + 4 ∉ fs.map (·.1) :=
    sso_notF hav (Nat.le_add_right _ _) (sso_lt6 hFn).2.2
  have hB : ∀ z, z ≠ x → (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj z = (treeOf i s w8).obj z := by
    intro z hz
    rw [hO10.2, ss_ite_neg hz, hobj9]
  have hBr : (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))).obj (w.next + 4) = some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩) := by
    rw [sso_ov_out fs _ hF4, hB _ hxn4.symm, hO8.2, ss_ite_pos rfl]
  have hBs : (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))).obj (w.next + 2) =
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [sso_ov_out fs _ hF2, hB _ hxn2.symm, hO8.2, ss_ite_neg hne42.symm, hO7.2, ss_ite_pos rfl]
  have hBf : (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))).obj w.next = some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) := by
    rw [sso_ov_out fs _ hF0, hB _ hxn.symm, hO8.2, ss_ite_neg hne40.symm, hO7.2,
      ss_ite_neg hne20.symm, hO6.2, ss_ite_pos rfl]
  have hBx : ((ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))).obj x).isSome = true := by
    rw [sso_ov_out fs _ hxF, hO10.2, ss_ite_pos rfl]; rfl
  have hBo : ∀ z, z ≠ x → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 4 →
      (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1))))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z h0 h1 h2 h4
    refine sso_ov_agree (fun _ => ?_)
    rw [hB z h0, hO8.2, ss_ite_neg h4, hO7.2, ss_ite_neg h2, hO6.2, ss_ite_neg h1, hT5, hO4.2,
      ss_ite_neg h4, hT3, hO2.2, ss_ite_neg h2, hO1.2, ss_ite_neg h1, hAz z h0]
  have hBA : ∀ z, ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z).isSome = true →
      ((ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1))))).obj z).isSome = true := by
    intro z hz
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    by_cases h1 : z = w.next
    · rw [h1, hBf]; rfl
    by_cases h2 : z = w.next + 2
    · rw [h2, hBs]; rfl
    by_cases h4 : z = w.next + 4
    · rw [h4, hBr]; rfl
    rw [hBo z h0 h1 h2 h4]
    exact hz
  have hS : Sound p.M (some x) (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      w.top.rootKey C := hI.sound
  rw [← hxr] at hS
  have hAx' : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [sso_ov_out fs _ hxF]; exact hAx
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx' hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1))))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (sso_named_some hb h htx hxF hxreach (hm c y hy))
  have hNf : NodeIs (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))) w.next (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl, hlev]
    exact ss_nodeIs hBf hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))) (w.next + 2) (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))) (w.next + 4) (wLevel s w x + 1) false
      [(0, w.next), (sc, w.next + 2)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBf]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplitRoot hS hAx' hsplit hL1
    (Or.inr (by rw [sso_ov_out fs _ hF0]; exact hA0)) (by rw [sso_ov_out fs _ hF2]; exact hA2)
    hne20.symm (by rw [sso_ov_out fs _ hF4]; exact hA4)
    ⟨hne40, hne42⟩ hNf hNs hNr hBx (fun z h0 h1 h2 h4 => hBo z h0 h1 h2 h4)
  have hrk10 : ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))).top.rootKey = w.next + 4 := hrk9
  have hroot10 : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).root = some (w.next + 4) := by
    rw [treeOf_withNode i s _ htx9]
    exact hroot9
  -- the balance rule in the map after the step, with fs set
  have hrA : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).root = some x := by
    rw [sso_ov_root, hxr]; exact hI.root
  have hxR : x ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
    rw [reach_of_root hrA]; exact tc_self _ _ _
  have hwx9 : wLevel s (MW.afterSuperRoot w8 p i (w.next + 4)) x = wLevel s w x := by
    rw [wLevel_afterSuperRoot s p i _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt
      (by rw [h8]; exact Nat.le_add_right _ _))),
      show wLevel s w8 = wLevel s w5 by rw [e8, e7, e6]; rfl, hw4n x hxn4, e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact hxn2), e1]
    exact prim_wLevel_afterNewKey hxn
  have hold : ∀ z, z ∉ [x, w.next, w.next + 2, w.next + 4] →
      (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1))))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact hBo z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hAx'] at hm; cases hm
      exact ⟨_, by rw [sso_ov_out fs _ hxF, hO10.2, ss_ite_pos rfl], hwx9⟩
    · rw [sso_ov_out fs _ hF0, hA0] at hm; cases hm
    · rw [sso_ov_out fs _ hF2, hA2] at hm; cases hm
    · rw [sso_ov_out fs _ hF4, hA4] at hm; cases hm)
  have hHL := ss_halves_live hsplit hlf hls
  have hBal : Balanced p (ovSet fs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))))) := by
    refine ss_bal_of hI.balanced hrA (r' := w.next + 4)
      (by rw [sso_ov_root]; exact hroot10) (fun z hz => ?_) hold hlevB
      (fun z hz hzR m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact absurd hzR (hxB hxn.symm)
      · rw [hBf] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hfl hlev.symm
          (fun c y hy => Or.inl (hHL.1 c y hy))
      · rw [hBs] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hsl hlev.symm
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [hBr] at hm; cases hm
        refine ss_rule_root (keyLevel_pos p g (hh + 1)) (by rw [heightOf_keyLevel p hH1]; simp)
          ⟨_, hBf, by rw [keyLevel_succ]⟩ ⟨_, hBs, by rw [keyLevel_succ]⟩
  refine ⟨sso_pinv hO10.1 (by rw [hrk10]; exact hroot10) (by rw [hrk10]; exact hSB) hBal,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · show (MW.afterSuperRoot w8 p i (w.next + 4)).path = w.path
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.1, e8, e7, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx, (afterSuperRoot_fields w8 p i (w.next + 4)).2.2.1,
      hlk y (Nat.ne_of_lt hylt) (ss_ne_of_lt_add hylt) (ss_ne_of_lt_add hylt)]
    exact hy
  · exact Nat.le_trans (Nat.le_add_right _ 6) hFn
  · intro z hz
    unfold reachOfO at hz ⊢
    rw [hrk10] at hz
    have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]; exact Or.inr (Nat.le_refl _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

theorem sso_root_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w 0 x n ins C) := by
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
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin']
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
  refine ss_wp_step (newSuperRoot_eq v _ h.hyp.top) ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact sso_root_new_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## 6. x cut back after the parent's step -/

/-- `getNode` changes neither the next id nor `outside`. -/
theorem sso_getNode_next (c : SIS.Tree.Ctx) (w : MW) (x : NodeId) :
    WP (SIS.Tree.getNode x) c w (fun _ w1 => w1.next = w.next ∧ w1.outside = w.outside) := by
  unfold SIS.Tree.getNode
  rw [wp_bind]
  refine (wp_get _ _ _).mpr ?_
  cases hl : w.nodes.lookup x with
  | some n => exact (wp_pure _ _ _ _).mpr ⟨rfl, rfl⟩
  | none =>
    dsimp only
    rw [wp_bind]
    refine (wp_read _ _ _).mpr ?_
    cases hv : c.view x with
    | none => exact wp_throw _ _ _ _
    | some nd =>
      dsimp only
      split
      · exact wp_throw _ _ _ _
      · rw [wp_bind]
        refine (wp_set _ _ _ _).mpr ?_
        exact (wp_pure _ _ _ _).mpr ⟨rfl, rfl⟩

/-- x cut back: under the bounds and with the ids of fs away, x is the node n
then. -/
theorem sso_wp_getPut {c : SIS.Tree.Ctx} {w : MW} {x : NodeId} {t : Time} {n : MNode}
    {fs : List (NodeId × Obj)} {a : Nat} {Q : MW → Prop}
    (h : w.outside = [] → (∀ e ∈ fs.map (·.1), e < a ∨ w.next ≤ e) →
      w.nodes.lookup x = some n ∧ Q (w.withNode x (n.toPrev t))) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev t)) c w
      (fun _ w' => w'.outside = [] → (∀ e ∈ fs.map (·.1), e < a ∨ w'.next ≤ e) → Q w') := by
  rw [wp_bind]
  intro n' w1 hg
  obtain ⟨hn, ho⟩ := sso_getNode_next c w x n' w1 hg
  refine ss_wp_putNode (fun hout hav => ?_)
  have hout' : w.outside = [] := by rw [← ho]; exact hout
  have hav' : ∀ e ∈ fs.map (·.1), e < a ∨ w.next ≤ e := by
    intro e he
    rw [← hn]
    exact hav e he
  obtain ⟨hlk, hQ⟩ := h hout' hav'
  rw [getNode_hit c hlk] at hg
  simp only [Except.ok.injEq, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  exact hQ

/-- The step `up` and what follows when a node of fs got its id among those
the step made before `up`: the conclusion holds vacuously. -/
theorem sso_vac {c : SIS.Tree.Ctx} {f : SIS.Tree.M Unit} {k : Unit → SIS.Tree.M Unit}
    {w wU : MW} {fs : List (NodeId × Obj)} {P : MW → Prop}
    (hf : WP f c wU (fun _ w' => wU.next ≤ w'.next))
    (hk : ∀ w1 : MW, WP (k ()) c w1 (fun _ w' => w1.next ≤ w'.next))
    (he : ∃ e ∈ fs.map (·.1), w.next ≤ e ∧ e < wU.next) :
    WP (f >>= k) c wU
      (fun _ w' => w'.outside = [] → (∀ e ∈ fs.map (·.1), e < w.next ∨ w'.next ≤ e) → P w') := by
  rw [wp_bind]
  refine WP.mono hf (fun u w1 h1 => WP.mono (hk w1) (fun _ w2 h2 _ hav => ?_))
  obtain ⟨e, hmem, he1, he2⟩ := he
  cases u
  rcases hav e hmem with h | h
  · exact absurd he1 (Nat.not_le.mpr h)
  · exact absurd (Nat.lt_of_lt_of_le he2 (Nat.le_trans h1 h2)) (Nat.not_lt.mpr h)

theorem sso_getPut_next (c : SIS.Tree.Ctx) (w : MW) (x : NodeId) (t : Time) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev t)) c w
      (fun _ w' => w.next ≤ w'.next) := by
  rw [wp_bind]
  intro n' w1 hg
  refine ss_wp_putNode ?_
  show w.next ≤ w1.next
  rw [(sso_getNode_next c w x n' w1 hg).1]

theorem sso_cutBack {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hin : ¬ n.firstTime = some i) {k1 : Nat} (hon' : w.path[d + 1]? = some (some k1, x))
    {q : NodeId} {nq : MNode} {insU : List (Nat × NodeId)} {wU w' : MW}
    (hpU : wU.path = w.path) (hnU : w.next ≤ wU.next)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hlkUx : wU.nodes.lookup x = some n)
    (hxnot : x ∉ reachOfO i s fs (wU.withNode q (addAll i nq insU)))
    (hreach : ∀ z ∈ reachOfO i s fs (wU.withNode q (addAll i nq insU)),
      z ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∨ w.next ≤ z)
    (hpost : CasPostO p i base s tp fs wU d q nq insU C () w') :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w' (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    rw [hux] at hu
    exact h.nodup e (d + 1) c (some k1) x (by omega) le_rfl hu hon'
  obtain ⟨t0, r0, hr0⟩ := h.first
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  refine sso_wp_getPut (n := n) (fun hout hav => ?_)
  obtain ⟨hPI, hCP⟩ := hpost hout (fun e he => by
    rcases hav e he with h1 | h1
    · exact Or.inl (Nat.lt_of_lt_of_le h1 hnU)
    · exact Or.inr h1)
  have hlkx : w'.nodes.lookup x = some n := by
    refine hCP.off x n hlkUx ?_
    intro d' c hd' e
    rw [hpU] at e
    exact hnx d' c x hd' e rfl
  have hsx : (s.obj x).isSome = true := (h.books.first x n hlook htx (by
    obtain ⟨t, r, hr⟩ := h.first; rw [hr]; simp)).mpr hin
  have htx' : w'.taken.contains x = false := by
    cases e : w'.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hPI.books.taken x e)
      have := (hPI.books.ids.2.2.1 m hm).2
      rw [hmx] at this
      rw [(hb.ids x this).1] at hsx
      cases hsx
  have hxnr : x ∉ reachOfO i s fs w' := by
    intro hx
    rcases hCP.reach x hx with h1 | h1
    · exact hxnot h1
    · exact absurd (Nat.lt_of_lt_of_le hxlt (Nat.le_trans hnU h1)) (Nat.lt_irrefl _)
  have hO' : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w' :=
    ⟨hPI.frame, hPI.books, hPI.top, hPI.empties⟩
  have hxF : x ∉ fs.map (·.1) := h.away (d + 1) (some k1) x le_rfl hon'
  have hO'' := ssOk_withNode (E' := fun z => z ∈ fs.map (·.1)) hO' hlkx htx' rfl
    (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (sso_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  have hob : ∀ z, z ≠ x → (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))).obj z =
      (ovSet fs (treeOf i s w')).obj z := by
    intro z hzx
    exact sso_ov_agree (fun _ => by rw [hO''.2, ss_ite_neg hzx])
  have ha : ∀ z ∈ reachOfO i s fs w',
      (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))).obj z =
        (ovSet fs (treeOf i s w')).obj z := by
    intro z hz
    exact hob z (fun e => hxnr (e ▸ hz))
  have hrx : w'.top.rootKey ≠ x := fun e => hxnr (by unfold reachOfO; rw [e]; exact tc_self _ _ _)
  have hfuel : (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))).fuel w'.top.rootKey =
      (ovSet fs (treeOf i s w')).fuel w'.top.rootKey := by
    simp only [Tree.fuel, hob _ hrx]
  have hreach' : reachOfO i s fs (w'.withNode x (n.toPrev (i - 1))) = reachOfO i s fs w' := by
    unfold reachOfO
    show reachAt _ ((ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))).fuel
      w'.top.rootKey) w'.top.rootKey = _
    rw [hfuel]
    exact reachAt_agree _ _ ha
  have hSB : Sound p.M none (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1)))))
      (w'.withNode x (n.toPrev (i - 1))).top.rootKey C := by
    refine Sound.agree hPI.sound ha (fun z hz => ?_)
    by_cases hzx : z = x
    · rw [hzx, sso_ov_out fs _ hxF, hO''.2, ss_ite_pos rfl]; rfl
    · rw [hob z hzx]; exact hz
  have hroot : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root =
      some (w'.withNode x (n.toPrev (i - 1))).top.rootKey := by
    rw [treeOf_withNode i s _ htx']
    exact hPI.root
  have hrA : (ovSet fs (treeOf i s w')).root = some w'.top.rootKey := by
    rw [sso_ov_root]; exact hPI.root
  have hrB : (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))).root =
      some w'.top.rootKey := by
    rw [sso_ov_root, treeOf_withNode i s _ htx']; exact hPI.root
  have hBal3 : Balanced p (ovSet fs (treeOf i s (w'.withNode x (n.toPrev (i - 1))))) := by
    refine Balanced.of_reach (N := [x]) hPI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
      (fun y m hm => ?_) (fun z hz hzR => ?_)
    · left
      rw [reach_of_root hrB] at hz
      rw [reach_of_root hrA]
      have hz' : z ∈ reachOfO i s fs (w'.withNode x (n.toPrev (i - 1))) := hz
      rw [hreach'] at hz'
      exact hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      exact hob z hz
    · by_cases hyx : y = x
      · rw [hyx, sso_ov_out fs _ hxF] at hm ⊢
        exact levels_kept_withNode i s _ hlkx htx' x m hm
      · exact ⟨m, by rw [hob y hyx]; exact hm, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz, reach_of_root hrB] at hzR
      have hz' : x ∈ reachOfO i s fs (w'.withNode x (n.toPrev (i - 1))) := hzR
      rw [hreach'] at hz'
      exact absurd hz' hxnr
  refine ⟨hlkx, sso_pinv hO''.1 hroot hSB hBal3, ⟨hCP.path.trans hpU, ?_, ?_, ?_⟩⟩
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

/-! ## 7. Under an inner parent -/

theorem sso_parent_pre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode}
    (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = false)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey) (hqF : q ∉ fs.map (·.1)) (hxF : x ∉ fs.map (·.1))
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
    (hOU : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) wU)
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hntU : wU.newTop = w.newTop)
    (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hwlU : ∀ y, y < w.next → wLevel s wU y = wLevel s w y)
    (hobjU : ∀ z, z ≠ first → z ≠ second → (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hfU : (treeOf i s wU).obj first = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩))
    (hsU : (treeOf i s wU).obj second = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩))
    (hfirst : first = x ∨ w.next ≤ first) (hsecond : w.next ≤ second) (hfs : first ≠ second)
    (hfF : first ∉ fs.map (·.1)) (hsF : second ∉ fs.map (·.1))
    (hins : (insU = [(sc, second)] ∧ first = x) ∨ insU = [(k1, first), (sc, second)]) :
    CasPreO p i base s tp fs wU d q nq insU C ∧
      (first ≠ x → x ∉ reachOfO i s fs (wU.withNode q (addAll i nq insU))) ∧
      (∀ z ∈ reachOfO i s fs (wU.withNode q (addAll i nq insU)),
        z ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∨ z = first ∨ z = second) ∧
      x ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) := by
  obtain ⟨-, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  have hAq' : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [sso_ov_out fs _ hqF, hAq]
  have hAx' : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [sso_ov_out fs _ hxF, hAx]
  -- q's node: well formed, of size M at most
  have hnq := hI.sound.nodes q hqr _ hAq'
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  have hnq' := hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq'
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq'
  rw [ksOf_length] at hnqs
  -- x is reached in A, and a kid of q there
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq'
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, -, hpp⟩ := live_split he
  have hkx := (hgq.tr_kids hAq' _ (bounds_mem hiq he)).2.2.2 (by simp [hql])
  obtain ⟨mx, hmx, -, -, hgx⟩ := hkx
  simp only [hql, Bool.false_eq_true, ite_false] at hgx
  have hxreach : x ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey :=
    hI.sound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq' hk1 (tc_self _ _ x))
  have hsc1 : max loq k1 < sc := Good.tr_split_lo hgx hAx' hsplit hL1
  have hscpost : ∀ b ∈ post, sc < b.1 :=
    tr_lt_post hpp (Good.tr_hi hgx hAx' (y := y0) (by rw [hsplit]; simp))
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
  obtain ⟨tq, rq, hrq⟩ := hOU.books.timeFirst q nq hlkq hkq (fun he => by
    have := ss_live_mem hk1
    rw [ksOf, he] at this
    simp at this)
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq insU
  have hOq := ssOk_withNode (E' := fun z => z ∈ fs.map (·.1)) hOU hlkq hkq (addAll_leaf i nq insU)
    (Or.inl (by rw [hrq', hrq]; rfl))
    (fun t ht => addAll_timesLe (ss_timesLe (hOU.books.times q nq hlkq)) insU t (ss_time_ksOf ht))
    (fun n0 hs0 => addAll_ext (prim_timesBefore (hb.times q n0 hs0))
      (frame_overlay_ext hOU.frame hlkq hkq hs0).2.2 insU)
    (by rw [hrq']; simp) (fun _ _ h => h)
  -- the parent's "if" state's map B, and with fs set
  have hBq : (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq insU)⟩) := by
    rw [sso_ov_out fs _ hqF, hOq.2, ss_ite_pos rfl, addAll_leaf, hwq]
  have hBo : ∀ z, z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hBf : (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj first =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [sso_ov_out fs _ hfF, hBo _ hqf.symm, hfU]
  have hBs : (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj second =
      some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by
    rw [sso_ov_out fs _ hsF, hBo _ hqs.symm, hsU]
  have hBx : ((ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj x).isSome = true := by
    rw [sso_ov_out fs _ hxF, hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
      rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ q →
      (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z h0 h1 h2 h3
    exact sso_ov_agree (fun _ => by rw [hBo z h3, hobjU z h1 h2, hAz z h0])
  have hBA : ∀ z, ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z).isSome = true →
      ((ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBf]; rfl
    by_cases h2 : z = second
    · rw [h2, hBs]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (sso_named_some hb h htx hxF hxreach (hm c y hy))
  have hNf : NodeIs (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))) first
      (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs hBf hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))) second
      (wLevel s w x) n.leaf (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNq : NodeIs (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))) q (wLevel s w q)
      false (insertCv sc second (insertCv k1 first (live (ksOf nq)))) (bnd p.M (some q) q) := by
    rw [← hql, ← addAll_leaf i nq insU, ← hliveU, ← addAll_live hnqwf]
    refine ss_nodeIs (by rw [hBq, addAll_leaf]) rfl (addAll_wf hnqwf insU) ?_ ?_
    · simp only [bnd, ite_true]
      have := addAll_size i nq insU
      rcases hlenU with e | e <;> rw [e] at this <;> omega
    · intro c y hy
      rcases (addAll_key_mem insU nq).mp (ss_key_ksOf hy) with h1 | h1
      · exact hBA y (ss_nodeOk_names hnq h1)
      · rcases hmemU c y h1 with e | e
        · rw [e, hBf]; rfl
        · rw [e, hBs]; rfl
  have hfirstA : first = x ∨
      (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (by rw [sso_ov_out fs _ hfF]; exact (treeOf_freshE hb hI.books e).1)
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplit (ex' := some q) hI.sound hqr hAq' hql hk1 hAx'
    hsplit hL1 hfirstA (by rw [sso_ov_out fs _ hsF]; exact (treeOf_freshE hb hI.books hsecond).1)
    hfs hNf hNs hNq hBx hsame
  have hrkq : (wU.withNode q (addAll i nq insU)).top.rootKey = w.top.rootKey := by
    show wU.top.rootKey = _
    rw [htopU]
  refine ⟨⟨hlkq, ⟨cq, by rw [hpU]; exact hq1⟩, ?_, ?_, ?_, hOU.books, ⟨tq, rq, hrq⟩, hnqwf,
    hnqs, hlenU, ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · -- no node of fs on the path
    intro e c u he h1
    rw [hpU] at h1
    exact h.away e c u (by omega) h1
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
    have hrA : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).root =
        some w.top.rootKey := by
      rw [sso_ov_root]; exact hI.root
    have hxR : x ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
      rw [reach_of_root hrA]; exact hxreach
    have hqR : q ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
      rw [reach_of_root hrA]; exact hqr
    have hHL := ss_halves_live hsplit hlf hls
    have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
    have hBx' : ∃ m', (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj x =
        some (.key m') ∧
        m'.level = wLevel s w x := by
      rw [sso_ov_out fs _ hxF, hBo x hqx.symm]
      by_cases hxf : x = first
      · have e := hfU
        rw [← hxf] at e
        rw [e]; exact ⟨_, rfl, rfl⟩
      · rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; exact ⟨_, rfl, rfl⟩
    have hold : ∀ z, z ∉ [x, first, second, q] →
        (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj z =
          (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      exact hsame z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have hlevB := ss_lev_of hold (by
      intro z hz m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hxcase : ∀ m, (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
          some (.key m) → ∃ m', (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj x =
            some (.key m') ∧ m'.level = m.level := by
        intro m hm
        rw [hAx'] at hm
        cases hm
        exact hBx'
      rcases hz with e | e | e | e
      · rw [e] at hm ⊢; exact hxcase m hm
      · rcases hfirst with ef | ef
        · rw [e, ef] at hm ⊢; exact hxcase m hm
        · rw [e, sso_ov_out fs _ hfF, (treeOf_freshE hb hI.books ef).1] at hm; cases hm
      · rw [e, sso_ov_out fs _ hsF, (treeOf_freshE hb hI.books hsecond).1] at hm; cases hm
      · rw [e] at hm ⊢
        rw [hAq'] at hm
        cases hm
        exact ⟨_, hBq, rfl⟩)
    have hBal : Balanced p (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))) := by
      refine ss_bal_of hI.balanced hrA (by rw [sso_ov_root]; exact hrootQ) (fun z hz => ?_) hold
        hlevB (fun z hz hzR m hm => ?_)
      · rcases hRB z hz with h1 | h1 | h1
        · exact Or.inl h1
        · right; simp [h1]
        · right; simp [h1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        have hfr : ∀ m, (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj first =
            some (.key m) →
            0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
            (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks →
              ∃ m', (ovSet fs (treeOf i s (wU.withNode q (addAll i nq insU)))).obj y =
                some (.key m') ∧
                m'.level + 1 = m.level) := by
          intro m hm
          rw [hBf] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx' hlevB hfl rfl
            (fun c y hy => Or.inl (hHL.1 c y hy))
        rcases hz with e | e | e | e
        · rw [e] at hzR hm
          by_cases hxf : x = first
          · rw [hxf] at hm; exact hfr m hm
          · exact absurd hzR (hxB (Ne.symm hxf))
        · rw [e] at hm; exact hfr m hm
        · rw [e, hBs] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx' hlevB hsl rfl
            (fun c y hy => Or.inl (hHL.2 c y hy))
        · rw [e, hBq] at hm
          cases hm
          refine ss_rule_node hI.balanced hqR hAq' hlevB rfl rfl (fun c y hy => ?_)
          rw [addAll_live hnqwf] at hy
          rcases mem_foldl_insertCv_src insU _ hy with h1 | h1
          · exact Or.inl ⟨c, h1⟩
          · rcases hmemU c y h1 with e' | e'
            · rw [e']; exact Or.inr ⟨_, hBf, hlq⟩
            · rw [e']; exact Or.inr ⟨_, hBs, hlq⟩
    exact sso_pinv hOq.1 (by rw [hrkq]; exact hrootQ) (by rw [hrkq]; exact hSB) hBal
  · intro hfx
    unfold reachOfO
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOfO at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz
  · exact hxreach


theorem sso_parent_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
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
      (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1, cq', q', nq', hq1', hon', hq3', hq4, hqx, hk1, hqr, -, hlq0, hnx, hqF, hxF⟩ :=
    sso_path hb h hon htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  have hlq := hlq0 hql
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx (by obtain ⟨t, r, hr⟩ := h.first; rw [hr]; simp)
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
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
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.first
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
  have hO3 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w3 ∧
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
  have hO4 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz'.resolve_right hz)
  have hO5 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hn5 : w5.next = w.next + 2 := by rw [e5, e4, e3, e2, e1]; rfl
  rw [wp_bind]
  by_cases hav0 : ∃ e ∈ fs.map (·.1), w.next ≤ e ∧ e < w5.next
  · rw [← wp_bind]
    exact sso_vac (hupn q _ w5) (fun w1 => (wp_pure _ _ _ _).mpr (Nat.le_refl _)) hav0
  have hsF : w.next ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_refl _,
    by rw [hn5]; exact Nat.lt_add_of_pos_right (by decide)⟩
  obtain ⟨hpre, -, hreach, hxr⟩ := sso_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hqF hxF
    hlq hnx
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
    (Or.inl rfl) (Nat.le_refl _) (Nat.ne_of_lt hxlt) hxF hsF (Or.inl ⟨rfl, rfl⟩)
  refine WP.mono (hup q _ w5 nq C hpre) (fun _ w' hpost => (wp_pure _ _ _ _).mpr ?_)
  intro hout hav
  obtain ⟨hPI, hCP⟩ := hpost hout (fun e he => by
    rcases hav e he with h1 | h1
    · exact Or.inl (Nat.lt_of_lt_of_le h1 (ss_le_add hn5))
    · exact Or.inr h1)
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


theorem sso_parent_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
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
      { p := p, i := i, view := v } w6 (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, -, hlq0, hnx, hqF, hxF⟩ :=
    sso_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  have hlq := hlq0 hql
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.first
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
  have hO4 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w4 := by
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
  have hO5 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w4).obj z := by
    rw [e5, ← hwl0]
    refine ssOk_withNode hO4 (m := ⟨n.leaf, []⟩)
      (by rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
          exact prim_lookup_append_self _ _ hn0)
      (by rw [hk4]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hO6 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w5).obj z := by
    have hwl5 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by rw [e5]; exact hwl2
    rw [e6, ← hwl5]
    refine ssOk_withNode hO5.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e5]; show w4.taken.contains _ = false
        rw [hk4, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0')
      (by rw [hs1]; simp) (fun _ hz h => h.resolve_right hz)
    · rw [e5, ss_lookup_withNode hne20, hN4, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hn2')
  have hpU : w6.path = w.path := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hn6 : w6.next = w.next + 4 := by rw [e6, e5, e4, e3, e2]; show w1.next + 2 = _; rw [hn1]
  have hlk6 : ∀ y, y ≠ x → y < w.next → w6.nodes.lookup y = w.nodes.lookup y := by
    intro y _ hy
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hy), e5, ss_lookup_withNode (Nat.ne_of_lt hy),
      hlk4 y (Nat.ne_of_lt hy) (ss_ne_of_lt_add hy)]
  have hlk6x : w6.nodes.lookup x = some n := by
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hxlt), e5, ss_lookup_withNode (Nat.ne_of_lt hxlt),
      hlk4 x (Nat.ne_of_lt hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  rw [wp_bind]
  by_cases hav0 : ∃ e ∈ fs.map (·.1), w.next ≤ e ∧ e < w6.next
  · rw [← wp_bind]
    exact sso_vac (hupn q _ w6) (fun w1 => sso_getPut_next _ w1 x (i - 1)) hav0
  have hfF : w.next ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_refl _,
    by rw [hn6]; exact Nat.lt_add_of_pos_right (by decide)⟩
  have hsF : w.next + 2 ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_add_right _ _,
    by rw [hn6]; exact Nat.add_lt_add_left (by decide) _⟩
  obtain ⟨hpre, hxnot, hreach, -⟩ := sso_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hqF hxF
    hlq hnx
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
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) hne20.symm hfF hsF (Or.inr rfl)
  refine WP.mono (hup q _ w6 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine sso_cutBack hb h hin hon' hpU (by rw [hn6]; exact Nat.le_add_right _ _) hlk6 hlk6x
    (hxnot (Nat.ne_of_lt hxlt).symm) (fun z hz => ?_) hpost
  rcases hreach z hz with h2 | h2 | h2
  · exact Or.inl h2
  · rw [h2]; exact Or.inr (Nat.le_refl _)
  · rw [h2]; exact Or.inr (Nat.le_add_right _ _)

theorem sso_parent_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hq3 : w.nodes.lookup q = some nq) (hql : nq.leaf = false) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
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
  exact sso_parent_inPlace_post hp hb h hup hupn hcase hin hgh hq1 hq3 hql hH rfl rfl rfl rfl rfl


theorem sso_parent_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = false) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
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
  exact sso_parent_new_post hp hb h hup hupn hcase hin hgh hq1 hq3 hql hon' hH rfl rfl rfl rfl rfl
    rfl


/-! ## 8. Under a segment leaf -/

theorem sso_seg_core {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {q : NodeId} {nq : MNode} (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = true)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey) (hqF : q ∉ fs.map (·.1)) (hxF : x ∉ fs.map (·.1))
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
    (hOU : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) wU)
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
    (hfF : first ∉ fs.map (·.1)) (hsF : second ∉ fs.map (·.1)) (hrF : r ∉ fs.map (·.1))
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
    SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) (wU.withNode q mq) ∧
      Sound p.M ex' (ovSet fs (treeOf i s (wU.withNode q mq))) (wU.withNode q mq).top.rootKey C ∧
      (treeOf i s (wU.withNode q mq)).root = some (wU.withNode q mq).top.rootKey ∧
      (first ≠ x → x ∉ reachOfO i s fs (wU.withNode q mq)) ∧
      (∀ z ∈ reachOfO i s fs (wU.withNode q mq),
        z ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∨ z = first ∨ z = second ∨ z = r) ∧
      x ∈ reachOfO i s fs (w.withNode x (addAll i n ins)) ∧
      Balanced p (ovSet fs (treeOf i s (wU.withNode q mq))) := by
  obtain ⟨-, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [sso_ov_out fs _ hqF, hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  have hAx' : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [sso_ov_out fs _ hxF, hAx]
  have hnq := hI.sound.nodes q hqr _ hAq
  -- x is reached in A', and sound there
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq
  obtain ⟨lox, hix, hgx⟩ : ∃ lo hi,
      Good (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) x lo hi := by
    rcases hgq.kind hAq hk1 with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', _, _, _, hg⟩
    · rw [hAx'] at hv; cases hv
    · exact ⟨lo', hi', hg⟩
  have hxreach : x ∈ reachAt (ovSet fs (treeOf i s (w.withNode x (addAll i n ins))))
      ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).fuel w.top.rootKey)
      w.top.rootKey :=
    hI.sound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq hk1 (tc_self _ _ x))
  have hsc0 : 0 < sc :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Good.tr_split_lo hgx hAx' hsplit hL1)
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
  have hOq := ssOk_withNode (E' := fun z => z ∈ fs.map (·.1)) hOU hlkq hkq hmleaf (Or.inl hmfst)
    hmtimes hmext hmne (fun _ _ h => h)
  -- the map B, with fs set
  have hBq : (ovSet fs (treeOf i s (wU.withNode q mq))).obj q =
      some (.key ⟨wLevel s w q, mq.leaf, ksOf mq⟩) := by
    rw [sso_ov_out fs _ hqF, hOq.2, ss_ite_pos rfl, hwq]
  have hBo : ∀ z, z ≠ q → (treeOf i s (wU.withNode q mq)).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hBf : (ovSet fs (treeOf i s (wU.withNode q mq))).obj first =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [sso_ov_out fs _ hfF, hBo _ hqf.symm, hfU]
  have hBs : (ovSet fs (treeOf i s (wU.withNode q mq))).obj second =
      some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by
    rw [sso_ov_out fs _ hsF, hBo _ hqs.symm, hsU]
  have hBr : (ovSet fs (treeOf i s (wU.withNode q mq))).obj r = some (.key ⟨wLevel s w x + 1,
      false, ([.time i, .key 0 first, .key sc second] : List MKlong).map kOf⟩) := by
    rw [sso_ov_out fs _ hrF, hBo _ hqr'.symm, hrU]
  have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
  have hxr : x ≠ r := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hr)
  have hBx : ((ovSet fs (treeOf i s (wU.withNode q mq))).obj x).isSome = true := by
    rw [sso_ov_out fs _ hxF, hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · rw [hobjU x hxf hxs hxr, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ r → z ≠ q →
      (ovSet fs (treeOf i s (wU.withNode q mq))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z h0 h1 h2 h4 h3
    exact sso_ov_agree (fun _ => by rw [hBo z h3, hobjU z h1 h2 h4, hAz z h0])
  have hBA : ∀ z, ((ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z).isSome = true →
      ((ovSet fs (treeOf i s (wU.withNode q mq))).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBf]; rfl
    by_cases h2 : z = second
    · rw [h2, hBs]; rfl
    by_cases h4 : z = r
    · rw [h4, hBr]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h4 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((ovSet fs (treeOf i s (wU.withNode q mq))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (sso_named_some hb h htx hxF hxreach (hm c y hy))
  have hNf : NodeIs (ovSet fs (treeOf i s (wU.withNode q mq))) first (wLevel s w x) n.leaf L1
      p.M := by
    rw [← hfl]
    exact ss_nodeIs hBf hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (ovSet fs (treeOf i s (wU.withNode q mq))) second (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (ovSet fs (treeOf i s (wU.withNode q mq))) r (wLevel s w x + 1) false
      [(0, first), (sc, second)] p.M :=
    ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBf]; rfl) (by rw [hBs]; rfl)
  have hNq : NodeIs (ovSet fs (treeOf i s (wU.withNode q mq))) q (wLevel s w q) true
      (insertCv k1 r (live (ksOf nq))) (bnd p.M ex' q) := by
    rw [← hql, ← hmleaf, ← hmlive]
    refine ss_nodeIs hBq rfl hmwf hmsz ?_
    intro c y hy
    rcases hmkey c y hy with h1 | h1
    · exact hBA y (ss_nodeOk_names hnq h1)
    · rw [h1, hBr]; rfl
  have hfirstA : first = x ∨
      (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (by rw [sso_ov_out fs _ hfF]; exact (treeOf_freshE hb hI.books e).1)
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplitSeg (ex' := ex') hI.sound hqr hAq hql hk1 hAx' hsplit
    hL1 hfirstA (by rw [sso_ov_out fs _ hsF]; exact (treeOf_freshE hb hI.books hsecond).1) hfs
    (by rw [sso_ov_out fs _ hrF]; exact (treeOf_freshE hb hI.books hr).1)
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
  -- the balance rule in B, with fs set
  have hrA : (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).root = some w.top.rootKey := by
    rw [sso_ov_root]; exact hI.root
  have hxR : x ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
    rw [reach_of_root hrA]; exact hxreach
  have hqR : q ∈ reach (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))) := by
    rw [reach_of_root hrA]; exact hqr
  have hHL := ss_halves_live hsplit hlf hls
  have hBx' : ∃ m', (ovSet fs (treeOf i s (wU.withNode q mq))).obj x = some (.key m') ∧
      m'.level = wLevel s w x := by
    rw [sso_ov_out fs _ hxF, hBo x hqx.symm]
    by_cases hxf : x = first
    · have e := hfU
      rw [← hxf] at e
      rw [e]; exact ⟨_, rfl, rfl⟩
    · rw [hobjU x hxf hxs hxr, treeOf_obj_overlay i s hlook htx]; exact ⟨_, rfl, rfl⟩
  have hold : ∀ z, z ∉ [x, first, second, r, q] →
      (ovSet fs (treeOf i s (wU.withNode q mq))).obj z =
        (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact hsame z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    have hxcase : ∀ m, (ovSet fs (treeOf i s (w.withNode x (addAll i n ins)))).obj x =
        some (.key m) →
        ∃ m', (ovSet fs (treeOf i s (wU.withNode q mq))).obj x = some (.key m') ∧
          m'.level = m.level := by
      intro m hm
      rw [hAx'] at hm
      cases hm
      exact hBx'
    rcases hz with e | e | e | e | e
    · rw [e] at hm ⊢; exact hxcase m hm
    · rcases hfirst with ef | ef
      · rw [e, ef] at hm ⊢; exact hxcase m hm
      · rw [e, sso_ov_out fs _ hfF, (treeOf_freshE hb hI.books ef).1] at hm; cases hm
    · rw [e, sso_ov_out fs _ hsF, (treeOf_freshE hb hI.books hsecond).1] at hm; cases hm
    · rw [e, sso_ov_out fs _ hrF, (treeOf_freshE hb hI.books hr).1] at hm; cases hm
    · rw [e] at hm ⊢
      rw [hAq] at hm
      cases hm
      exact ⟨_, hBq, rfl⟩)
  have hBal : Balanced p (ovSet fs (treeOf i s (wU.withNode q mq))) := by
    refine ss_bal_of hI.balanced hrA (by rw [sso_ov_root]; exact hrootQ) (fun z hz => ?_) hold
      hlevB (fun z hz hzR m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hfr : ∀ m, (ovSet fs (treeOf i s (wU.withNode q mq))).obj first = some (.key m) →
          0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
          (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks →
            ∃ m', (ovSet fs (treeOf i s (wU.withNode q mq))).obj y = some (.key m') ∧
              m'.level + 1 = m.level) := by
        intro m hm
        rw [hBf] at hm
        cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hfl rfl
          (fun c y hy => Or.inl (hHL.1 c y hy))
      rcases hz with e | e | e | e | e
      · rw [e] at hzR hm
        by_cases hxf : x = first
        · rw [hxf] at hm; exact hfr m hm
        · exact absurd hzR (hxB (Ne.symm hxf))
      · rw [e] at hm; exact hfr m hm
      · rw [e, hBs] at hm
        cases hm
        exact ss_rule_node hI.balanced hxR hAx' hlevB hsl rfl
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [e, hBr] at hm
        cases hm
        exact ss_rule_root (Nat.succ_pos _) hhr ⟨_, hBf, rfl⟩ ⟨_, hBs, rfl⟩
      · rw [e, hBq] at hm
        cases hm
        obtain ⟨h1, h2, -⟩ := hI.balanced q hqR _ hAq
        refine ⟨h1, by rw [hmleaf]; exact h2, fun hl => ?_⟩
        rw [hmleaf, hql] at hl
        cases hl
  refine ⟨hOq.1, by rw [hrkq]; exact hSB, by rw [hrkq]; exact hrootQ, ?_, ?_, hxreach, hBal⟩
  · intro hfx
    unfold reachOfO
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOfO at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz

theorem sso_seg_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupo : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → w.outside = []))
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
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
      { p := p, i := i, view := v } w8 (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
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
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, hlt, -, hnx, hqF, hxF⟩ :=
    sso_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
  have hO3 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 2 ∨ z = w.next) w3 := by
    rw [e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT3 : treeOf i s w3 = treeOf i s w2 := by rw [e3]; rfl
  have hfr3 := treeOf_freshE hb hO3.books (Nat.le_refl w3.next)
  rw [hn3] at hfr3
  obtain ⟨-, hs4, hn4', -, ht4, hm4⟩ := hfr3
  have hO4 : SsOk p i base s tp
      (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false, []⟩) else (treeOf i s w3).obj z := by
    rw [e4, ← hn3]
    exact ssOk_newKey hb (hO3.congr (w' := ssNote w3 "split.space2") rfl rfl rfl rfl rfl rfl rfl rfl
      rfl) hgG hH1 (by simp) (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
  have hO5 : SsOk p i base s tp
      (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w5 := by
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
  have hO6 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4 ∨ z = w.next + 2) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w5).obj z := by
    rw [e6, ← hwl0]
    refine ssOk_withNode hO5 (m := ⟨n.leaf, []⟩)
      (by rw [hN5 _ (ss_ne_add (by decide)) (ss_ne_add (by decide)), hlk1n])
      (by rw [hk5]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr (Or.inl hz')
      · exact Or.inr (Or.inr hz')
      · exact absurd hz' hz
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne40 : w.next + 4 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne42 : w.next + 4 ≠ w.next + 2 := by
    have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
    rw [Nat.add_assoc] at this
    exact this.symm
  have hlk1 : w1.nodes.lookup (w.next + 2) = none := by rw [← hn1]; rw [hn1]; exact hn2'
  have hO7 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next + 4) w7 ∧
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
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hO8 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w8 ∧
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
      (by simp) (fun _ hz h => h.resolve_right hz)
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
  have hnq := hI.sound.nodes q hqr _ (by rw [sso_ov_out fs _ hqF]; exact hAq)
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq
  rw [ksOf_length] at hnqs
  have hkq8 : w8.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq8 : w8.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  by_cases hav0 : ∃ e ∈ fs.map (·.1), w.next ≤ e ∧ e < w8.next
  · rw [← wp_bind]
    exact sso_vac (hupn q _ w8) (fun w1 => sso_getPut_next _ w1 x (i - 1)) hav0
  have hfF : w.next ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_refl _,
    by rw [hn8]; exact Nat.lt_add_of_pos_right (by decide)⟩
  have hsF : w.next + 2 ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_add_right _ _,
    by rw [hn8]; exact Nat.add_lt_add_left (by decide) _⟩
  have hrF : w.next + 4 ∉ fs.map (·.1) := fun he => hav0 ⟨_, he, Nat.le_add_right _ _,
    by rw [hn8]; exact Nat.add_lt_add_left (by decide) _⟩
  obtain ⟨tq, rq, hrq⟩ := h.books.timeFirst q nq hq3 hq4 (fun he => by
    have := ss_live_mem hk1
    rw [ksOf, he] at this
    simp at this)
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq [(k1, w.next + 4)]
  obtain ⟨hOQ, hSQ, hrootQ, hxB, hRB, -, hBQ⟩ := sso_seg_core hp hb h htx hq3 hq4 hqx hql hk1
    hqr hqF hxF hlevq (by rw [hlev, ← keyLevel_succ, heightOf_keyLevel p hH1]; simp) hsplit
    hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := w.next)
    (second := w.next + 2) (r := w.next + 4) hO8.1 htopU hntU hkU hlkU hwlU hobjU hfU hsU hrU
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) (Nat.le_add_right _ _) hne20.symm hne40
    hne42 hfF hsF hrF (mq := addAll i nq [(k1, w.next + 4)]) (ex' := some q)
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
  obtain ⟨hP8, hnd8, haw8⟩ := sso_path_keep h hnx hpU htopU hkU hlkU
    (fun z _ hz => hobjU z (Nat.ne_of_lt hz) (ss_ne_of_lt_add hz) (ss_ne_of_lt_add hz))
  have hpre : CasPreO p i base s tp fs w8 d q nq [(k1, w.next + 4)] C :=
    ⟨hlkq8, ⟨cq, by rw [hpU]; exact hq1⟩, hP8, hnd8, haw8, hO8.1.books, ⟨tq, rq, hrq⟩, hnqwf,
      hnqs, Or.inl rfl, fun a y1 b y2 e => by simp at e, sso_pinv hOQ hrootQ hSQ hBQ⟩
  refine WP.mono (hup q _ w8 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine sso_cutBack hb h hin hon' hpU (by rw [hn8]; exact Nat.le_add_right _ _) hlkU hlkUx
    (hxB hxn.symm) (fun z hz => ?_) hpost
  rcases hRB z hz with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1]; exact Or.inr (Nat.le_refl _)
  · rw [h1]; exact Or.inr (Nat.le_add_right _ _)
  · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

theorem sso_seg_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hup : UpOkO p i base s tp v fs up d)
    (hupo : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → w.outside = []))
    (hupn : ∀ q ins (w : MW), WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => w.next ≤ w'.next))
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
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
  exact sso_seg_new_post hp hb h hup hupo hupn hcase hin hgh hq1 hq3 hql hon' hH rfl rfl rfl rfl
    rfl rfl
    rfl rfl

theorem sso_seg_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
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
    CasPostO p i base s tp fs w (d + 1) x n ins C ()
      (w6.withNode q (nq.repoint j (w.next + 2))) := by
  intro hout hav
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hk1, hqr, hlt, -, hnx, hqF, hxF⟩ :=
    sso_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := sso_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size h.first h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx (by obtain ⟨t, r, hr⟩ := h.first; rw [hr]; simp)
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_freshE hb h.books (Nat.le_refl w.next)
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
  have hO1 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl)
      (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inr hz
        · exact Or.inl hz)
  have hO2 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.first
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO3 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1) ∨ z = w.next) w3 ∧
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
  have hO4 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz'.resolve_right hz)
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2]; exact hn1
  have hO5 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩)
        else (treeOf i s w4).obj z := by
    rw [e5, ← hn4]
    refine ssOk_newKey hb (hO4.1.congr (w' := ssNote w4 "split.space2.inplace") rfl rfl rfl rfl
      rfl rfl rfl rfl rfl) hgG hH1 (by simp)
      (Or.inr ⟨_, rfl⟩) (by simp)
      (fun z hz => hz.resolve_left (fun h => by cases h.2))
  have hO6 : SsOk p i base s tp (fun z => z ∈ fs.map (·.1)) w6 := by
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
  have hnq := hI.sound.nodes q hqr _ (by rw [sso_ov_out fs _ hqF]; exact hAq)
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq
  rw [ksOf_length] at hnqs
  have hkq6 : w6.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq6 : w6.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  obtain ⟨tq, rq, hrq⟩ := h.books.timeFirst q nq hq3 hq4 (fun he => by
    have := ss_live_mem hk1
    rw [ksOf, he] at this
    simp at this)
  have hFn : w.next + 4 ≤ (w6.withNode q (nq.repoint j (w.next + 2))).next := by
    show w.next + 4 ≤ w6.next
    rw [hn6]
  have hsF : w.next ∉ fs.map (·.1) := sso_notF hav (Nat.le_refl _) (sso_lt4 hFn).1
  have hrF : w.next + 2 ∉ fs.map (·.1) := sso_notF hav (Nat.le_add_right _ _) (sso_lt4 hFn).2
  obtain ⟨rq', hrq'⟩ := repoint_first hrq j (w.next + 2)
  obtain ⟨hOQ, hSQ, hrootQ, -, hRB, hxW0, hBQ⟩ := sso_seg_core hp hb h htx hq3 hq4 hqx hql hk1
    hqr hqF hxF hlevq (by rw [hlev, ← keyLevel_succ, heightOf_keyLevel p hH1]; simp) hsplit
    hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := x)
    (second := w.next) (r := w.next + 2) hO6 htopU hntU hkU hlkU hwlU hobjU hfU hsU hrU
    (Or.inl rfl) (Nat.le_refl _) (Nat.le_add_right _ _) hxn hxn2.symm hne20 hxF hsF hrF
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
  refine ⟨sso_pinv hOQ hrootQ hSQ hBQ, ⟨hpU, ?_, ?_, ?_⟩⟩
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

theorem sso_seg_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {fs : List (NodeId × Obj)} {x : NodeId} {ins : List (Nat × NodeId)}
    {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    (h : CasPreO p i base s tp fs w (d + 1) x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode} (hq1 : w.path[d]? = some (cq, q))
    (hon' : w.path[d + 1]? = some (some k1, x)) (hq3 : w.nodes.lookup q = some nq)
    (hql : nq.leaf = true) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w (d + 1) x n ins C) := by
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
  obtain ⟨_, _, q', _, hq1', -, -, -, hqx, -⟩ := sso_path hb h hon htx
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
      exact sso_seg_inPlace_post hp hb hn h hcase hin hgh hq1 hq3 hql hon' hj hH rfl rfl rfl rfl
        rfl rfl

/-! ## 9. The step

The six cases of `handleFullWith`'s space split, as in WriterSpaceSplitG.lean,
with soundness read on the map with fs set. -/

theorem handleFull_space_o {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s)
    {fs : List (NodeId × Obj)} {depth : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW}
    {n : MNode} {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (h : CasPreO p i base s tp fs w depth x n ins C)
    (hup : ∀ d, depth = d + 1 → UpOkO p i base s tp v fs up d)
    (hupo : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP (up q ins) { p := p, i := i, view := v } w (fun _ w' => w'.outside = [] → w.outside = []))
    (hupn : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP (up q ins) { p := p, i := i, view := v } w (fun _ w' => w.next ≤ w'.next))
    (hcase : p.splitAbove < (n.lastVersion i).size) :
    WP (SIS.Tree.handleFullWith up depth x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPostO p i base s tp fs w depth x n ins C) := by
  cases depth with
  | zero =>
    by_cases hin : n.firstTime = some i
    · exact sso_root_inPlace hp hb h hcase hin
    · exact sso_root_new hp hb h hcase hin
  | succ d =>
    obtain ⟨c0, hon⟩ := h.on
    have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
    obtain ⟨k1, cq, q, nq, hq1, hon', hq3, -⟩ := sso_path hb h hon htx
    cases hql : nq.leaf with
    | false =>
      by_cases hin : n.firstTime = some i
      · exact sso_parent_inPlace hp hb h (hup d rfl) (hupn d rfl) hcase hin hq1 hq3 hql
      · exact sso_parent_new hp hb h (hup d rfl) (hupn d rfl) hcase hin hq1 hon' hq3 hql
    | true =>
      by_cases hin : n.firstTime = some i
      · exact sso_seg_inPlace hp hb hn h hcase hin hq1 hon' hq3 hql
      · exact sso_seg_new hp hb h (hup d rfl) (hupo d rfl) (hupn d rfl) hcase hin hq1 hon' hq3 hql

/-! ## 10. The steps of the writer do not lower the next id -/

/-- The step f from w does not lower the next id. -/
abbrev SsNext {α : Type} (f : SIS.Tree.M α) (c : SIS.Tree.Ctx) (w : MW) : Prop :=
  WP f c w (fun _ w' => w.next ≤ w'.next)

theorem ssn_bind {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w : MW} (hf : SsNext f c w) (hg : ∀ a (w1 : MW), SsNext (g a) c w1) :
    SsNext (f >>= g) c w := by
  unfold SsNext
  rw [wp_bind]
  exact WP.mono hf (fun a w1 h1 => WP.mono (hg a w1) (fun _ w2 h2 => Nat.le_trans h1 h2))

theorem ssn_eq {α : Type} {f : SIS.Tree.M α} {c : SIS.Tree.Ctx} {w w1 : MW} {a : α}
    (h : f c w = .ok (a, w1)) (ho : w.next ≤ w1.next) : SsNext f c w := by
  intro r w' hr
  rw [h] at hr
  cases hr
  exact ho

theorem ssn_pure {α : Type} (a : α) (c : SIS.Tree.Ctx) (w : MW) : SsNext (pure a) c w :=
  (wp_pure _ _ _ _).mpr (Nat.le_refl _)

theorem ssn_throw {α : Type} (e : String) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (throw e : SIS.Tree.M α) c w :=
  wp_throw _ _ _ _

theorem ssn_read (c : SIS.Tree.Ctx) (w : MW) : SsNext (read : SIS.Tree.M SIS.Tree.Ctx) c w :=
  (wp_read _ _ _).mpr (Nat.le_refl _)

theorem ssn_get (c : SIS.Tree.Ctx) (w : MW) : SsNext (MonadState.get : SIS.Tree.M MW) c w :=
  (wp_get _ _ _).mpr (Nat.le_refl _)

theorem ssn_getNode (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.getNode x) c w :=
  WP.mono (sso_getNode_next c w x) (fun _ _ h => Nat.le_of_eq h.1.symm)

theorem ssn_putNode (x : NodeId) (m : MNode) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.putNode x m) c w :=
  ssn_eq (putNode_eq c w x m) (Nat.le_refl _)

theorem ssn_note (t : String) (c : SIS.Tree.Ctx) (w : MW) : SsNext (SIS.Tree.note t) c w :=
  ssn_eq (ss_note c w t) (Nat.le_refl _)

theorem ssn_modify (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (modify (fun w : MW => { w with spaceSplits := w.spaceSplits + 1 })) c w :=
  ssn_eq (ss_modify c w) (Nat.le_refl _)

theorem ssn_setMadeFor (m : NodeId) (o : Option NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.setMadeFor m o) c w :=
  ssn_eq (ss_setMadeFor c w m o) (Nat.le_refl _)

theorem ssn_replacedBy (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.replacedBy x) c w :=
  ssn_eq (replacedBy_eq c w x) (Nat.le_refl _)

theorem ssn_newKey (g h : Nat) (leaf : Bool) (ks : List MKlong) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.newKey g h leaf ks) c w :=
  ssn_eq (newKey_eq c w g h leaf ks) (Nat.le_add_right _ _)

theorem ssn_ghOf (x : NodeId) (c : SIS.Tree.Ctx) (w : MW) : SsNext (SIS.Tree.ghOf x) c w := by
  unfold SIS.Tree.ghOf
  refine ssn_bind (ssn_getNode x c w) (fun _ w1 => ?_)
  refine ssn_bind (ssn_get c w1) (fun w2 w3 => ?_)
  split
  · exact ssn_pure _ _ _
  · exact ssn_throw _ _ _

theorem ssn_parentAt (d : Nat) (c : SIS.Tree.Ctx) (w : MW) : SsNext (SIS.Tree.parentAt d) c w := by
  unfold SIS.Tree.parentAt
  split
  · exact ssn_pure _ _ _
  · refine ssn_bind ?_ (fun _ _ => ssn_pure _ _ _)
    unfold SIS.Tree.pathNode
    refine ssn_bind (ssn_get c w) (fun w2 w3 => ?_)
    split
    · exact ssn_pure _ _ _
    · exact ssn_throw _ _ _

theorem ssn_klongAt (d : Nat) (c : SIS.Tree.Ctx) (w : MW) : SsNext (SIS.Tree.klongAt d) c w := by
  unfold SIS.Tree.klongAt
  refine ssn_bind (ssn_get c w) (fun w2 w3 => ?_)
  split
  · exact ssn_pure _ _ _
  · exact ssn_throw _ _ _

theorem ssn_newSuperRoot (y : NodeId) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.newSuperRoot y) c w := by
  by_cases e : c.i = w.top.time
  · exact ssn_eq (newSuperRoot_inPlace_eq c w y e) (Nat.le_refl _)
  · exact ssn_eq (newSuperRoot_new_eq c w y e) (Nat.le_add_right _ _)

theorem ssn_replaceOrAdd (last : MNode) (ins : List (Nat × NodeId)) (c : SIS.Tree.Ctx) (w : MW) :
    SsNext (SIS.Tree.replaceOrAdd last ins) c w := by
  unfold SIS.Tree.replaceOrAdd
  rw [SsNext, wp_bind]
  refine (wp_read _ _ _).mpr ?_
  refine WP.mono (ssk_foldlM _ c (fun r cy w1 => ?_) ins last w)
    (fun _ _ e => by rw [e])
  dsimp only
  split
  · exact wp_throw _ _ _ _
  · exact (wp_pure _ _ _ _).mpr rfl
  · exact (wp_pure _ _ _ _).mpr rfl

/-- `handleFullWith` does not lower the next id if `up` does not. -/
theorem sso_handleFullWith_next {c : SIS.Tree.Ctx}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hup : ∀ q ins (w : MW), WP (up q ins) c w (fun _ w' => w.next ≤ w'.next))
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : MNode) (compact : Bool)
    (w : MW) :
    WP (SIS.Tree.handleFullWith up depth x ins last compact) c w
      (fun _ w' => w.next ≤ w'.next) := by
  show SsNext _ c w
  unfold SIS.Tree.handleFullWith
  repeat' (first
    | with_reducible exact hup _ _ _
    | with_reducible exact ssn_pure _ _ _
    | with_reducible exact ssn_throw _ _ _
    | with_reducible exact ssn_read _ _
    | with_reducible exact ssn_getNode _ _ _
    | with_reducible exact ssn_putNode _ _ _ _
    | with_reducible exact ssn_note _ _ _
    | with_reducible exact ssn_modify _ _
    | with_reducible exact ssn_setMadeFor _ _ _ _
    | with_reducible exact ssn_replacedBy _ _ _
    | with_reducible exact ssn_newKey _ _ _ _ _ _
    | with_reducible exact ssn_ghOf _ _ _
    | with_reducible exact ssn_parentAt _ _ _
    | with_reducible exact ssn_klongAt _ _ _
    | with_reducible exact ssn_newSuperRoot _ _ _
    | with_reducible exact ssn_replaceOrAdd _ _ _ _
    | with_reducible refine ssn_bind ?_ (fun _ _ => ?_)
    | split)

end Contract
