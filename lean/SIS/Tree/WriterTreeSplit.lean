/-
The writer's tree kept by the splits (bergdb 024-22, `OpTreeOK`). First, the
time split of `GetSplit.lean` (`TimeSplitAfter`): a segment leaf L that existed
before the transaction, below an inner parent q with room, is replaced by a new
node that holds its last version and the klong put; q's klong of L names the new
node; L keeps its klongs before the transaction and is reached no more
(`treeOK_timeSplitAfter`, by `treeOK_transfer_gone`).
-/
import SIS.Tree.WriterTreeVisits
import SIS.Tree.GetSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A key klong added at time t: the live klongs at t are the new one and the
others of the node. -/
theorem KNode.add_key_liveAt_mem (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (h : (c, y) ∈ (n.add t (.key cv v)).liveAt t) :
    (c = cv ∧ y = v) ∨ (c ≠ cv ∧ (c, y) ∈ n.liveAt t) := by
  by_cases hc : c = cv
  · subst hc
    left
    refine ⟨rfl, ?_⟩
    have ht' := KNode.add_times n t (.key c v) (fun s h => by cases h) ht
    rw [KNode.liveAt_of_times _ t ht'] at h
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c y h
    rw [KNode.add_key_live_lookup_of_wf n t c c v hw] at hl
    simp at hl
    exact hl.symm
  · exact Or.inr ⟨hc, KNode.add_key_liveAt_other n t cv v hw ht c y hc h⟩

/-- The tree after a time split of a segment leaf below an inner parent with
room (`TimeSplitAfter`). The premises: the tree before; L and q the writer's
nodes, q inner and naming L by k1 at the time, L a leaf; the klong put of a
short segment; the klongs of L and q of no later time, q's well formed; the next
id no node of the writer's and named by no link of the tree. -/
theorem treeOK_timeSplitAfter (p : Params) (base : View BVal) (c : Ctx) (w w' : W)
    (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) (hcp : c.p = p)
    (hT : TreeOK (wNode p base w) c.i w.top.rootKey)
    (hA : TimeSplitAfter c w w' L q n qn k1 cv v)
    (hLn : wNode p base w L = some n) (hqn : wNode p base w q = some qn) (hqL : q ≠ L)
    (hqleaf : qn.leaf = false) (hnleaf : n.leaf = true) (hseg : segLen cv ≠ 7)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode p base w) c.i w.top.rootKey q)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hnext : wNode p base w w.next = none) (hntk : w.taken.contains w.next = false)
    (hfresh : ∀ u c', TReach (wNode p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode p base w) c.i u c' w.next) :
    TreeOK (wNode p base w') c.i w'.top.rootKey := by
  subst hcp
  obtain ⟨l, hl_leaf, _, hl_times, hl_look, h'taken, h'top, _, h'nodes⟩ := hA
  generalize hN : wNode c.p base w = N at *
  generalize hr : w.top.rootKey = r at *
  rw [h'top, hr]
  have hLt : w.taken.contains L = false := by
    rw [← hN] at hLn; unfold wNode at hLn; split at hLn
    · cases hLn
    · rename_i h; simpa using h
  have hqt' : w.taken.contains q = false := by
    rw [← hN] at hqn; unfold wNode at hqn; split at hqn
    · cases hqn
    · rename_i h; simpa using h
  have hLy : L ≠ w.next := fun h => by rw [h, hnext] at hLn; cases hLn
  have hqy : q ≠ w.next := fun h => by rw [h, hnext] at hqn; cases hqn
  -- the writer's nodes after
  have hN' : ∀ x, wNode c.p base w' x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.add c.i (.key k1 w.next))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else N x := by
    intro x
    rw [← hN]
    unfold wNode
    rw [h'taken, h'nodes x]
    by_cases hxL : x = L
    · subst hxL; simp only [hLt, Bool.false_eq_true, ↓reduceIte]
    · by_cases hxq : x = q
      · subst hxq; simp only [hqt', hxL, Bool.false_eq_true, ↓reduceIte]
      · by_cases hxy : x = w.next
        · subst hxy; simp only [hntk, hxL, hxq, Bool.false_eq_true, ↓reduceIte]
        · simp only [hxL, hxq, hxy, ↓reduceIte]
  -- facts of the tree before
  have hLreach : TReach N c.i r L := TReach.link hq ⟨qn, hqn, hqk, fun h => by rw [hqleaf] at h; cases h⟩
  have hqLlink : TLink N c.i q k1 L := ⟨qn, hqn, hqk, fun h => by rw [hqleaf] at h; cases h⟩
  have hLparent : ∀ u c', TReach N c.i r u → TLink N c.i u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqLlink
  have hyNotReach : ¬ TReach N c.i r w.next := by
    intro h
    cases h with
    | root =>
      obtain ⟨m, hm⟩ := hT.rootKey
      rw [hm] at hnext
      cases hnext
    | link hu hl => exact hfresh _ _ hu hl
  -- the live klongs of the new node
  have hy_live : ∀ c' v', (c', v') ∈ ({ leaf := n.leaf, ks := l.ks } : KNode).liveAt c.i →
      (c' = cv ∧ v' = v) ∨ (c', v') ∈ n.liveAt c.i := by
    intro c' v' h
    rw [KNode.liveAt_of_times ({ leaf := n.leaf, ks := l.ks } : KNode) c.i hl_times] at h
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' v' h
    have hlk' : l.live.lookup c' = some v' := by
      rw [← KNode.live_with_leaf l n.leaf]; exact hlk
    rw [hl_look c'] at hlk'
    by_cases hcc : cv = c'
    · subst hcc; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
    · have hb : (cv == c') = false := by simpa using hcc
      rw [hb] at hlk'
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
      right
      rw [KNode.liveAt_of_times n c.i hnt]
      exact mem_of_lookup_nodup _ c' v' hlk'
  apply treeOK_transfer_gone N (wNode c.p base w') c.i r r (fun z => z = w.next) (fun z => z = L)
    (fun u c' => if u = L then (w.next, c') else (u, c')) hT
  · intro z hz; rw [hz]; exact hyNotReach
  · refine Or.inl ⟨rfl, fun h => ?_⟩
    exact hT.rootFree q k1 hq (by rw [h]; exact hqLlink)
  · intro u c' v' hu hug hl
    obtain ⟨m, hm, hc, hs⟩ := hl
    rw [hN' u] at hm
    by_cases huL : u = L
    · exact absurd huL hug
    simp only [huL, ↓reduceIte] at hm
    by_cases huq : u = q
    · subst huq
      simp only [↓reduceIte, Option.some.injEq] at hm
      subst hm
      rcases KNode.add_key_liveAt_mem qn c.i k1 w.next hqwf hqt c' v' hc with ⟨_, hv⟩ | ⟨hck, hmem⟩
      · exact Or.inl hv
      · right
        have hlink : TLink N c.i u c' v' := ⟨qn, hqn, hmem, fun h => by rw [hqleaf] at h; cases h⟩
        refine ⟨fun hvL => ?_, u, c', hq, hlink, by simp [hqL]⟩
        rw [hvL] at hlink
        exact hck (hLparent u c' hq hlink).2
    · simp only [huq, ↓reduceIte] at hm
      by_cases huy : u = w.next
      · simp only [huy, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        have hleafy : ({ leaf := n.leaf, ks := l.ks } : KNode).leaf = true := hnleaf
        have h7 := hs hleafy
        rcases hy_live c' v' hc with ⟨hcv, _⟩ | hmem
        · exact absurd (hcv ▸ h7) hseg
        · right
          have hlink : TLink N c.i L c' v' := ⟨n, hLn, hmem, fun _ => h7⟩
          refine ⟨fun hvL => ?_, L, c', hLreach, hlink, by simp [huy]⟩
          rw [hvL] at hlink
          exact hqL (hLparent L c' hLreach hlink).1.symm
      · simp only [huy, ↓reduceIte] at hm
        have hlink : TLink N c.i u c' v' := ⟨m, hm, hc, hs⟩
        have huR : TReach N c.i r u := by
          rcases hu with h | h
          · exact h
          · exact absurd h huy
        right
        refine ⟨fun hvL => ?_, u, c', huR, hlink, by simp [huL]⟩
        rw [hvL] at hlink
        exact huq (hLparent u c' huR hlink).1
  · intro u c' u' c'' z hu hug hu' hug' hz hl hl'
    rw [hz] at hl hl'
    -- the one link to the new node is q's k1
    have hone : ∀ x d, (TReach N c.i r x ∨ x = w.next) → x ≠ L →
        TLink (wNode c.p base w') c.i x d w.next → x = q ∧ d = k1 := by
      intro x d hx hxL hl0
      obtain ⟨m, hm, hc, hs⟩ := hl0
      rw [hN' x] at hm
      simp only [hxL, ↓reduceIte] at hm
      by_cases hxq : x = q
      · subst hxq
        simp only [↓reduceIte, Option.some.injEq] at hm
        subst hm
        rcases KNode.add_key_liveAt_mem qn c.i k1 w.next hqwf hqt d w.next hc with
          ⟨hd, _⟩ | ⟨_, hmem⟩
        · exact ⟨rfl, hd⟩
        · exact absurd ⟨qn, hqn, hmem, fun h => by rw [hqleaf] at h; cases h⟩ (hfresh x d hq)
      · simp only [hxq, ↓reduceIte] at hm
        by_cases hxy : x = w.next
        · simp only [hxy, ↓reduceIte, Option.some.injEq] at hm
          subst hm
          have h7 := hs hnleaf
          rcases hy_live d w.next hc with ⟨hcv, _⟩ | hmem
          · exact absurd (hcv ▸ h7) hseg
          · exact absurd ⟨n, hLn, hmem, fun _ => h7⟩ (hfresh L d hLreach)
        · simp only [hxy, ↓reduceIte] at hm
          have hxR : TReach N c.i r x := by
            rcases hx with h | h
            · exact h
            · exact absurd h hxy
          exact absurd ⟨m, hm, hc, hs⟩ (hfresh x d hxR)
    obtain ⟨h1, h2⟩ := hone u c' hu hug hl
    obtain ⟨h3, h4⟩ := hone u' c'' hu' hug' hl'
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro z hz hzL; rw [hz] at hzL; exact hLy hzL.symm
  · by_cases hrL : r = L
    · exact absurd (by rw [hrL]; exact hqLlink) (hT.rootFree q k1 hq)
    · rw [hN' r]
      simp only [hrL, ↓reduceIte]
      by_cases hrq : r = q
      · simp [hrq]
      · simp only [hrq, ↓reduceIte]
        by_cases hry : r = w.next
        · simp [hry]
        · simp only [hry, ↓reduceIte]
          exact hT.rootKey

end SIS.Tree
