/-
Root collapse at a segment root (bergdb 024-22, `OpTreeOK`; `replaceRoot` and
`takeBackRoot` below the segment leaf of the segment above): the leaf's klong
k names the root's only child instead of the root, which is left behind or
taken back (`writerWP_replaceRoot_seg_tree`, with room in the leaf;
`writerWP_takeBackRoot_seg_tree`).
-/
import SIS.Tree.WriterTreeLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_pathNode_known (d : Nat) (y : NodeId) (c : Ctx) (w : W)
    (h : (w.path[d]?).map (·.2) = some y) (post : NodeId → W → Prop) (hp : post y w) :
    WriterWP (pathNode d) c w post := by
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  cases he : w.path[d]? with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    simp only [writerWP_pure]
    rw [h]; exact hp

theorem writerWP_klongAt_known (d k : Nat) (y : NodeId) (c : Ctx) (w : W)
    (h : w.path[d]? = some (some k, y)) (post : Nat → W → Prop) (hp : post k w) :
    WriterWP (klongAt d) c w post := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]
  exact hp

/-- `replaceRoot` at a segment root x below the segment leaf `leaf` with room:
the tree is kept. -/
theorem writerWP_replaceRoot_seg_tree (x : NodeId) (d only : Nat) (n : KNode) (child leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlf : TReach (wNode c.p base w) c.i w.top.rootKey leaf)
    (hlkL : w.nodes.lookup leaf = some ln) (hLt : w.taken.contains leaf = false)
    (hlnwf : klongsWf ln.ks = true) (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i)
    (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hpd : (w.path[d]?).map (·.2) = some leaf) (hpk : w.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child' =>
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_frame x c _) ?_
    intro _ w1 ⟨h1t, h1top, _, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child' c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    simp only
    rw [h1top]
    obtain ⟨cc, hcc⟩ := onlyLiveKlong_link n c.i only child' hnt honly hp
    apply treeOK_collapseSegment (wNode c.p base w) _ c.i w.top.rootKey leaf x child' k cc ln
      (ln.add c.i (.key k child')) n hT hlf hwL hk hwx hcc
    · simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro c' z hm
      rcases KNode.add_key_liveAt_mem ln c.i k child' hlnwf hlnt c' z hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
    · intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]

/-- `takeBackRoot` at a segment root x that the transaction made by a split,
below the segment leaf `leaf`: the leaf's klong k is pointed in place to the
child, x is taken back. -/
theorem writerWP_takeBackRoot_seg_tree (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlf : TReach (wNode c.p base w) c.i w.top.rootKey leaf)
    (hlkL : w.nodes.lookup leaf = some ln) (hLt : w.taken.contains leaf = false)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i)
    (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hpd : (w.path[d]?).map (·.2) = some leaf) (hpk : w.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    rw [writerWP_getNode_known leaf ln c _ (by simpa using hlkL)]
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    split
    · rename_i j hj
      split
      · exact writerWP_throw _ _ _ _
      · simp only [putNode, writerWP_bind, writerWP_modify]
        refine (writerWP_takenBack_iff x c _ _).mpr ?_
        simp only
        obtain ⟨cc, hcc⟩ := onlyLiveKlong_link n c.i only child hnt honly hp
        apply treeOK_collapseSegment (wNode c.p base w) _ c.i w.top.rootKey leaf x child k cc ln
          (ln.repoint j child) n hT hlf hwL hk hwx hcc
        · have hLt' : (x :: w.taken).contains leaf = false := by
            rw [List.contains_cons]
            have : (leaf == x) = false := by simpa using hlx
            rw [this, Bool.false_or]; exact hLt
          simp only [wNode, hLt', Bool.false_eq_true, ↓reduceIte, lookup_upsert]
        · intro c' z hm
          rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times ln j child c.i hlnt)] at hm
          have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hm
          rw [KNode.repoint_live_lookup ln x child k j hj c'] at hlk
          by_cases hck : k = c'
          · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
          · have hb : (k == c') = false := by simpa using hck
            rw [hb] at hlk
            simp only [Bool.false_eq_true, ↓reduceIte] at hlk
            refine Or.inr ⟨?_, Ne.symm hck⟩
            rw [KNode.liveAt_of_times ln c.i hlnt]
            exact mem_of_lookup_nodup _ c' z hlk
        · intro y hyl hyx
          have hyt : (x :: w.taken).contains y = w.taken.contains y := by
            rw [List.contains_cons]
            have : (y == x) = false := by simpa using hyx
            simp [this]
          simp only [wNode, hyt, lookup_upsert, hyl, ↓reduceIte]
    · exact writerWP_throw _ _ _ _

end SIS.Tree
