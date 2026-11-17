/-
The contract package (bergdb 030-16): the bitmap, `Dag.appendDeleteKlong`, in
every form: the bits set in the transaction's own bitmap (`setAt`), or a new
bitmap klong (`add`); and when the node then holds more than theta dead
klongs (`deadOver`, a compaction) or has no room (`bitmap.full`), the node is
replaced by its last version with the delete (`handleFull`, a time split or a
space split, WriterDelTime.lean, WriterDelSpace.lean).

The statement: node x of the key access path at `depth`, with a live klong of
compare value cv; the caller says what the state is with x set to a node V
that has x's live klongs but cv's (`DelVirt`): it meets `PInv` with x maybe
over its size and holds the keys C. Then the step, where it gives no error and
leaves no key node outside G and H, ends in a state that meets `PInv` and holds
C. Used for a segment leaf (the delete's own klong) and for the stop node of
the upward unlink (the klong of the emptied child).
-/
import Contract.Proof.WriterDelTime
import Contract.Proof.WriterDelSpace

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. Helpers: the last version of the node with the bitmap -/

/-- A fold over indexed klongs that skips every klong but a key klong leaves
its value as it is over klongs with no key klong. -/
theorem wdb_fold_id {β : Type} (f : β → MKlong × Nat → β)
    (hf : ∀ b k i, (∀ c y, k ≠ SIS.Tree.Klong.key c y) → f b (k, i) = b) :
    ∀ (e : List MKlong) (k : Nat) (b : β), (∀ c y, SIS.Tree.Klong.key c y ∉ e) →
      (e.zipIdx k).foldl f b = b
  | [], _, _, _ => rfl
  | a :: e, k, b, h => by
    rw [List.zipIdx_cons, List.foldl_cons, hf b a k (fun c y he => h c y (he ▸ by simp)),
      wdb_fold_id f hf e (k + 1) b (fun c y he => h c y (List.mem_cons_of_mem _ he))]

/-- Two nodes of the same kind whose klongs are the same but for a tail of no
key klongs: the first's last version given V's last bitmap is V's. -/
theorem wdb_lvgd_of {n V : MNode} {ks0 e1 e2 : List MKlong} (t : Time) (u : List Nat)
    (h1 : n.ks = ks0 ++ e1) (h2 : V.ks = ks0 ++ e2)
    (he1 : ∀ c y, SIS.Tree.Klong.key c y ∉ e1) (he2 : ∀ c y, SIS.Tree.Klong.key c y ∉ e2)
    (hu : V.lastBitmap = u) (hl : V.leaf = n.leaf) :
    n.lastVersionGivenDel t u = V.lastVersion t := by
  unfold SIS.Tree.KNode.lastVersion
  rw [hu]
  unfold SIS.Tree.KNode.lastVersionGivenDel
  have hf : ∀ (b : List (Nat × NodeId)) (k : MKlong) (i : Nat),
      (∀ c y, k ≠ SIS.Tree.Klong.key c y) →
      (match (k, i) with
        | (k, i) => match k with
          | .key c y => if u.contains i then b else SIS.Tree.setCv b c y
          | _ => b) = b := by
    intro b k i hk
    cases k with
    | key c y => exact absurd rfl (hk c y)
    | time _ => rfl
    | del _ => rfl
  rw [h1, h2, hl, List.zipIdx_append, List.zipIdx_append, List.foldl_append, List.foldl_append,
    wdb_fold_id _ hf e1 _ _ he1, wdb_fold_id _ hf e2 _ _ he2]

/-- `lastVersionGivenDel` of a new bitmap klong's union is the last version of
the node with the bitmap added. -/
theorem wdb_lv_add (n : MNode) (t t' : Time) (u : List Nat) :
    n.lastVersionGivenDel t u = (n.add t' (.del u)).lastVersion t := by
  have hu : (n.add t' (.del u)).lastBitmap = u := by
    rcases add_ks n t' (.del u) with ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp [SIS.Tree.KNode.lastBitmap, SIS.Tree.lastBitmapOf, h, List.foldl_append]
  rcases add_ks n t' (.del u) with ⟨h, -⟩ | ⟨h, -⟩
  · exact wdb_lvgd_of (e1 := []) t u (by simp) h (by simp) (by simp) hu (add_leaf _ _ _)
  · exact wdb_lvgd_of (e1 := []) t u (by simp) h (by simp) (by simp) hu (add_leaf _ _ _)

/-- So for the transaction's own bitmap set in place. -/
theorem wdb_lv_set {n : MNode} {t' : Time} (ht : hasTransDel n t' = true) (t : Time)
    (u : List Nat) :
    n.lastVersionGivenDel t u = (n.setAt (n.size - 1) (.del u)).lastVersion t := by
  obtain ⟨ks0, B, hks, -⟩ := hasTransDel_ks ht
  have h2 := setAt_last hks (.del u)
  have hu : (n.setAt (n.size - 1) (.del u)).lastBitmap = u := by
    simp [SIS.Tree.KNode.lastBitmap, SIS.Tree.lastBitmapOf, h2, List.foldl_append]
  exact wdb_lvgd_of t u hks h2 (by simp) (by simp) hu rfl

/-- A node set to one with no live klong but the old node's, on its level,
reaches no node that was not reached before. -/
theorem wdb_reach_sub {T : Tree} {x : NodeId} {m m' : KNode} (hx : T.obj x = some (.key m))
    (hsub : ∀ a ∈ live m'.ks, a ∈ live m.ks) :
    ∀ (f : Nat) (r z : NodeId), z ∈ reachAt (T.set x (.key m')) f r → z ∈ reachAt T f r
  | 0, r, z, h => by
    simp only [reachAt, List.mem_singleton] at h ⊢
    exact h
  | f + 1, r, z, h => by
    rcases tc_mem_succ.mp h with rfl | ⟨n, hn, cy, hcy, hz⟩
    · exact tc_self _ _ _
    · have ih := wdb_reach_sub hx hsub f cy.2 z hz
      by_cases e : r = x
      · subst e
        rw [prim_set_obj_self] at hn
        cases hn
        exact tc_kid hx (hsub cy hcy) ih
      · rw [prim_set_obj_ne _ _ e] at hn
        exact tc_kid hn hcy ih

/-- `OldReach` of the state with node x of the overlay set to a node with no
live klong but x's: it reaches no node that the state did not. -/
theorem wdb_old_withNode {i : Time} {s : Tree} {w : MW} {x : NodeId} {n V : MNode}
    (ho : OldReach i s w) (hlk : w.nodes.lookup x = some n) (ht : w.taken.contains x = false)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hsub : ∀ a ∈ live (ksOf V), a ∈ live (ksOf n)) : OldReach i s (w.withNode x V) := by
  intro z hz hsz
  have hAx := treeOf_obj_overlay i s hlk ht
  have hTW := treeOf_withNode i s V ht
  have hrootW : (treeOf i s (w.withNode x V)).root = some w.top.rootKey := hroot
  rw [reach_of_root hrootW, hTW] at hz
  have hf : ((treeOf i s w).set x (.key ⟨wLevel s w x, V.leaf, ksOf V⟩)).fuel w.top.rootKey =
      (treeOf i s w).fuel w.top.rootKey := by
    unfold Tree.fuel
    by_cases e : w.top.rootKey = x
    · rw [e, prim_set_obj_self, hAx]
    · rw [prim_set_obj_ne _ _ e]
  rw [hf] at hz
  refine ho z ?_ hsz
  rw [reach_of_root hroot]
  exact wdb_reach_sub hAx hsub _ _ _ hz

/-- The live klongs but cv's are among the live klongs. -/
theorem wdb_drop_sub {V n : MNode} {cv : Nat} (h : live (ksOf V) = dropCv cv (live (ksOf n))) :
    ∀ a ∈ live (ksOf V), a ∈ live (ksOf n) := by
  intro a ha
  rw [h] at ha
  exact List.mem_of_mem_filter ha

/-! ## 2. The bitmap -/

/-- Before `handleFull` of the bitmap, from the state after its `note`: the
node x would be V, and the last version is V's. -/
theorem wdb_pre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {x : NodeId} {w : MW} {n V : MNode} {C : List (Key × Nat)}
    (hlk : w.nodes.lookup x = some n) (hon : ∃ c0, w.path[depth]? = some (c0, x))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf n) = true) (hsize : n.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : Balanced p (treeOf i s w))
    (hVI : PInv p i base s tp (some x) C (w.withNode x V)) (hVl : V.leaf = n.leaf)
    (t : String) :
    CasPreD p i base s tp { w with trail := t :: w.trail } depth x n V (V.lastVersion i) C :=
  ⟨hlk, hon, hpath.congr rfl rfl rfl rfl (treeOf_congr i s rfl rfl rfl rfl rfl rfl), hin,
    putBooks_congr hbooks rfl rfl rfl rfl rfl rfl rfl rfl rfl, hwf, hsize, hroot, hframe, htop,
    hbal, hVl,
    (lastVersion_leaf V i).trans hVl, lastVersion_ks i,
    hVI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- The bitmap, for a compare value whose bits are not all in the node's last
bitmap already (`isNoop` false); `appendDeleteKlong_spec` is its case of a
live klong of cv. -/
theorem wdb_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {w : MW} {n : MNode} {cv : Nat} {C : List (Key × Nat)}
    (hlk : w.nodes.lookup x = some n) (hon : ∃ c0, w.path[depth]? = some (c0, x))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf n) = true) (hsize : n.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : Balanced p (treeOf i s w)) (ho : OldReach i s w)
    (hnoop : (delUnion n cv == n.lastBitmap) = false)
    (hV : DelVirt p i base s tp w x n cv C) :
    WP (SIS.Tree.appendDeleteKlong x depth cv) { p := p, i := i, view := v } w
      (fun r w' => r = false ∧ (w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧
          OldReach i s w')) := by
  have ht : w.taken.contains x = false := by
    obtain ⟨c0, hc0⟩ := hon
    exact (hpath.lookup (Nat.le_refl _) hc0).choose_spec.2
  obtain ⟨t0, rest, hr0⟩ := hbooks.timeFirst x n hlk ht
  have hT0 := wput_timesLe hbooks hlk
  have hlive : (live (ksOf n)).length + 1 ≤ p.M := by
    have := live_length_le (ks := ksOf n) ⟨t0, rest.map kOf, by simp [ksOf, hr0, kOf]⟩
    rw [ksOf_length] at this
    omega
  have hdrop : (dropCv cv (live (ksOf n))).length ≤ (live (ksOf n)).length :=
    List.length_filter_le _ _
  -- the post of the four steps that change the node
  have hput : ∀ (V : MNode) (t : String), PInv p i base s tp (some x) C (w.withNode x V) →
      OldReach i s (w.withNode x V) → V.size ≤ p.M →
      WP (do SIS.Tree.note t; SIS.Tree.putNode x V; pure false)
        { p := p, i := i, view := v } w
        (fun r w' => r = false ∧ (w'.outside = [] →
          PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧
          OldReach i s w')) := by
    intro V t hVI hVo hVs
    refine wput_ok (note_eq _ _ _) (wput_ok (putNode_eq _ _ _ _) ?_)
    rw [wp_pure]
    exact ⟨rfl, fun _ => ⟨wput_pinv_fit (hVI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl)
      (lookup_upsert_self _ _ _) hVs, rfl, Nat.le_refl _, wput_old_congr hVo rfl⟩⟩
  have hfull : ∀ (V : MNode) (t : String) (compact : Bool),
      PInv p i base s tp (some x) C (w.withNode x V) → OldReach i s (w.withNode x V) →
      V.leaf = n.leaf → ((compact = true ∧ (live (ksOf V)).length + 1 ≤ p.M) ∨
        (compact = false ∧ (V.lastVersion i).size ≤ p.splitAbove) ∨
        (compact = false ∧ p.splitAbove < (V.lastVersion i).size)) →
      WP (do SIS.Tree.note t; SIS.Tree.handleFull depth x (V.lastVersion i) compact; pure false)
        { p := p, i := i, view := v } w
        (fun r w' => r = false ∧ (w'.outside = [] →
          PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧
          OldReach i s w')) := by
    intro V t compact hVI hVo hVl hcase
    refine wput_ok (note_eq _ _ _) ?_
    rw [wp_bind]
    have hpre := wdb_pre hlk hon hpath hin hbooks hwf hsize hroot hframe htop hbal hVI hVl t
    have hpost : ∀ (u : Unit) (w' : MW),
        CasPostD p i base s tp { w with trail := t :: w.trail } depth x V C u w' →
        WP (pure false) { p := p, i := i, view := v } w'
          (fun r w' => r = false ∧ (w'.outside = [] →
            PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧
          OldReach i s w')) := by
      intro u w' h
      rw [wp_pure]
      refine ⟨rfl, fun ho => ?_⟩
      obtain ⟨h1, h2⟩ := h ho
      refine ⟨h1, h2.path, h2.next, fun z hz hsz => ?_⟩
      rw [reach_of_root h1.root] at hz
      rcases h2.reach z hz with h3 | h3
      · exact hVo z (by rw [reach_of_root hVI.root]; exact h3) hsz
      · rw [(hb.ids z (Nat.le_trans hbooks.ids.2.2.2.1 h3)).1] at hsz
        cases hsz
    rcases hcase with hc | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · exact (handleFullD_time hp hb hpre (Or.inl hc)).mono hpost
    · exact (handleFullD_time hp hb hpre (Or.inr ⟨rfl, hc⟩)).mono hpost
    · exact (handleFullD_space hp hb hpre hc).mono hpost
  have hext : ∀ n0, s.obj x = some (.key n0) →
      (∀ t, Klong.time t ∈ n0.ks → t < i) ∧
        (ksOf n = n0.ks ∨ ∃ more, ksOf n = n0.ks ++ Klong.time i :: more) := by
    intro n0 hs0
    obtain ⟨-, -, he⟩ := frame_overlay_ext hframe hlk ht hs0
    exact ⟨prim_timesBefore (hb.times x n0 hs0), he⟩
  unfold SIS.Tree.appendDeleteKlong
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk) ?_
  dsimp only
  split
  · rw [wp_bind]
    exact wp_throw _ _ _ _
  · have hdu : SIS.Tree.bitsUnion n.lastBitmap (n.bitsOf cv) = delUnion n cv := rfl
    simp only [hdu, hnoop, Bool.not_false, ↓reduceIte]
    refine wp_ite _ _ _ _ _ _ (fun htd => ?_) (fun _ => ?_)
    · -- the transaction's own bitmap, in place
      have htd' : hasTransDel n i = true := htd
      have hVI := hV _ (setDel_leaf _ _) (setDel_live hwf htd' cv) (setDel_wf hwf htd' cv)
        (by rw [setDel_size]; omega) (fun c y h => (setDel_key_mem htd').mp h)
        (by obtain ⟨rest', hr1⟩ := setDel_first htd' hr0 (delUnion n cv); rw [hr1, hr0]; rfl)
        (setDel_timesLe hT0 _)
        (fun n0 hs0 => Or.inr (setDel_ext (hext n0 hs0).1 htd' (hext n0 hs0).2 _))
      have hVo := wdb_old_withNode ho hlk ht hroot (wdb_drop_sub (setDel_live hwf htd' cv))
      rw [wdb_lv_set htd' i (delUnion n cv)]
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · refine hfull _ _ true hVI hVo (setDel_leaf _ _) (Or.inl ⟨rfl, ?_⟩)
        rw [setDel_live hwf htd' cv]
        omega
      · exact hput _ _ hVI hVo (by rw [setDel_size]; exact hsize)
    · rw [wdb_lv_add n i i (delUnion n cv)]
      have hsz := add_size n i (.del (delUnion n cv))
      have hVI := hV _ (add_leaf _ _ _) (addDel_live hwf cv) (addDel_wf hwf cv) hsz
        (fun c y h => addDel_key_mem.mp h)
        (by
          obtain ⟨rest', hr1⟩ := add_first (t := i) (.del (delUnion n cv)) hr0
          rw [hr1, hr0]
          rfl)
        (add_timesLe hT0 _ (fun t' e => by cases e))
        (fun n0 hs0 => add_ext (hext n0 hs0).1 (hext n0 hs0).2 _)
      have hVo := wdb_old_withNode ho hlk ht hroot (wdb_drop_sub (addDel_live (t := i) hwf cv))
      refine wp_ite _ _ _ _ _ _ (fun hroom => ?_) (fun _ => ?_)
      · refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
        · refine hfull _ _ true hVI hVo (add_leaf _ _ _) (Or.inl ⟨rfl, ?_⟩)
          rw [addDel_live hwf cv]
          omega
        · exact hput _ _ hVI hVo (by omega)
      · by_cases hh : ((n.add i (.del (delUnion n cv))).lastVersion i).size ≤ p.splitAbove
        · exact hfull _ _ false hVI hVo (add_leaf _ _ _) (Or.inr (Or.inl ⟨rfl, hh⟩))
        · exact hfull _ _ false hVI hVo (add_leaf _ _ _) (Or.inr (Or.inr ⟨rfl, by omega⟩))

theorem appendDeleteKlong_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {w : MW} {n : MNode} {cv : Nat} {C : List (Key × Nat)}
    (hlk : w.nodes.lookup x = some n) (hon : ∃ c0, w.path[depth]? = some (c0, x))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf n) = true) (hsize : n.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : Balanced p (treeOf i s w)) (ho : OldReach i s w)
    (hcv : ∃ y, (cv, y) ∈ live (ksOf n))
    (hV : DelVirt p i base s tp w x n cv C) :
    WP (SIS.Tree.appendDeleteKlong x depth cv) { p := p, i := i, view := v } w
      (fun r w' => r = false ∧ (w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧
          OldReach i s w')) := by
  refine wdb_spec hp hb hlk hon hpath hin hbooks hwf hsize hroot hframe htop hbal ho ?_ hV
  cases h : (delUnion n cv == n.lastBitmap)
  · rfl
  · exfalso
    obtain ⟨y, hy⟩ := hcv
    rw [← delUnion_noop hwf h] at hy
    simp [dropCv] at hy

end Contract
