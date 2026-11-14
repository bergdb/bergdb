import SIS.Tree.PutInvRoot
import SIS.Tree.WriterTreeSegRoot
import SIS.Tree.GetSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a put into a segment root that is a leaf below the segment
leaf q of the key's segment before (bergdb 024-12, TP10; the rules of prover
latest's `writerWP_put_segLeaf_inv`): with room, the time split in place, the
time split (q's klong names the new node), the space split into a new segment
root and the space split in place (q's klong names the new root). No inner node
links the segment root, so the order at its leaf needs no bound; q, a leaf
child of an inner node itself, keeps its compare values. -/

/-- A leaf child whose live compare values are among the old child's keeps the
order below its parent. -/
theorem leafOrderAt_child (qn m m' : KNode) (k1 : Nat) (h : LeafOrderAt qn k1 m)
    (hc : ∀ c' z, (c', z) ∈ m'.live → ∃ z', (c', z') ∈ m.live) : LeafOrderAt qn k1 m' :=
  fun c' z hz => let ⟨z', hz'⟩ := hc c' z hz; h c' z' hz'

theorem repoint_time_mem (n : KNode) (e : Nat) (y : NodeId) (s : Time)
    (h : Klong.time s ∈ (n.repoint e y).ks) : Klong.time s ∈ n.ks := by
  unfold KNode.repoint at h
  split at h
  · rcases List.mem_or_eq_of_mem_set h with h1 | h1
    · exact h1
    · cases h1
  · exact h

/-- The parts about the tree after a time split of a leaf L below a segment
leaf q: q's klong k1 names a new node y holding L's live klongs and (cv, v). -/
theorem putInvT_timeSplitLeaf (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv k1 : Nat) (v y L q : NodeId) (n qn l : KNode) (hv : w.next ≤ v) (hy : w.next ≤ y)
    (hvy : v ≠ y)
    (hn : wNode c.p base w L = some n) (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = true)
    (hq : ReachS (wNode c.p base w) c.i w.top.rootKey q) (hk1 : (k1, L) ∈ qn.live) (hqL : q ≠ L)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'q : wNode c.p base w' q = some (qn.add c.i (.key k1 y)))
    (hN'y : wNode c.p base w' y = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ y → wNode c.p base w' x = wNode c.p base w x) :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hqnext := hI.lt_next q qn hqn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) hvy]; exact hvN
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hqwf := hI.wf q qn hqn
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  have honly : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hq hqn hk1'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    ReachS.step q qn k1 L hq hqn hk1'
  have hroot : w.top.rootKey ≠ L := by
    intro he
    exact hI.tree.rootFree q k1 (reachS_tReach _ _ _ q hq) ⟨qn, hqn, he ▸ hk1'⟩
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L) ∨ x = y ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L) ∨
      x = y ∨ x = v) (Or.inl ⟨ReachS.root, hroot⟩)
    intro x xn cc z hx hxn hz
    rcases hx with ⟨hx, hxL⟩ | hx | hx
    · have hxn' := hI.reach_lt x hx
      by_cases hxq : x = q
      · subst hxq
        rw [hN'q] at hxn
        cases hxn
        rcases KNode.add_key_liveAt_mem qn c.i k1 y hqwf hqt cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inl h2)
        · refine Or.inl ⟨ReachS.step x qn cc z hx hqn h2, ?_⟩
          intro hzL; subst hzL
          exact hne (honly x qn cc hx hqn h2).2
      · rw [hother x hxL hxq (by omega)] at hxn
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_⟩
        intro hzL; subst hzL
        exact hxq (honly x xn cc hx hxn hz).1
    · subst hx
      rw [hN'y] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlt] at hz
      rcases hlive cc z hz with ⟨_, h2⟩ | h2
      · exact Or.inr (Or.inr h2)
      · rw [← KNode.liveAt_of_times n c.i hnt] at h2
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h2, ?_⟩
        intro hzL; subst hzL
        exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h2⟩
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hy
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    rcases hsub q' hq' with ⟨hq'r, hq'L⟩ | hq'y | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      have hq'q : q' ≠ q := by
        intro he; subst he; rw [hN'q] at hq'n; cases hq'n
        rw [KNode.add_leaf, hql] at hq'l; cases hq'l
      rw [hother q' hq'L hq'q (by omega)] at hq'n
      have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
        rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
      have hL'L : L' ≠ L := by
        intro he; subst he; exact hq'q (honly q' q'n k1' hq'r hq'n hk'').1
      have hL'y : L' ≠ y := by
        have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
      by_cases hL'q : L' = q
      · subst hL'q
        rw [hN'q] at hn'
        cases hn'
        have hold := hI.order q' q'n L' qn k1' hq'r hq'n hq'l hqn hql hk'
        refine leafOrderAt_child q'n qn _ k1' hold ?_
        intro c' z hz
        have ht' := KNode.add_times qn c.i (.key k1 y) (fun s h => by cases h) hqt
        rw [← KNode.liveAt_of_times _ c.i ht'] at hz
        rcases KNode.add_key_liveAt_mem qn c.i k1 y hqwf hqt c' z hz with ⟨h1, _⟩ | ⟨_, h2⟩
        · subst h1; exact ⟨L, hk1⟩
        · rw [KNode.liveAt_of_times qn c.i hqt] at h2; exact ⟨z, h2⟩
      · rw [hother L' hL'L hL'q hL'y] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'y; rw [hN'y] at hq'n; cases hq'n; rw [hll] at hq'l; cases hq'l
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-- The parts about the tree after a space split of a segment root L, a leaf
below the segment leaf q: a new segment root R over the halves F (a fresh id,
or L itself in place) and S; q's klong k1 names R. -/
theorem putInvT_segSpaceSplit (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv sc k1 : Nat) (v F S R L q : NodeId) (n qn qn' f s : KNode)
    (hv : w.next ≤ v) (hS : w.next ≤ S) (hR : w.next ≤ R) (hF : w.next ≤ F ∨ F = L)
    (hvS : v ≠ S) (hvR : v ≠ R) (hvF : v ≠ F) (hSR : S ≠ R) (hFS : F ≠ S) (hFR : F ≠ R)
    (hn : wNode c.p base w L = some n) (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = true)
    (hq : ReachS (wNode c.p base w) c.i w.top.rootKey q) (hk1 : (k1, L) ∈ qn.live) (hqL : q ≠ L)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'q : wNode c.p base w' q = some qn') (hqn'l : qn'.leaf = true)
    (hq't : ∀ s, Klong.time s ∈ qn'.ks → s ≤ c.i)
    (hqlive : ∀ c' z, (c', z) ∈ qn'.liveAt c.i →
      (c' = k1 ∧ z = R) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt c.i))
    (hN'R : wNode c.p base w' R = some ⟨false, newKlongs c.i [(0, F), (sc, S)]⟩)
    (hN'F : wNode c.p base w' F = some f) (hN'S : wNode c.p base w' S = some s)
    (hfl : f.leaf = true) (hsl : s.leaf = true)
    (hft : ∀ t, Klong.time t ∈ f.ks → t ≤ c.i) (hst : ∀ t, Klong.time t ∈ s.ks → t ≤ c.i)
    (hf : ∀ c' z, (c', z) ∈ f.liveAt c.i → ((c', z) = (cv, v) ∧ cv < sc) ∨ ((c', z) ∈ n.live ∧ c' < sc))
    (hs : ∀ c' z, (c', z) ∈ s.liveAt c.i →
      ((c', z) = (cv, v) ∧ sc ≤ cv) ∨ ((c', z) ∈ n.live ∧ sc ≤ c'))
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → x ≠ R →
      wNode c.p base w' x = wNode c.p base w x) :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hqnext := hI.lt_next q qn hqn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) hvF hvS hvR]; exact hvN
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  have honly : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hq hqn hk1'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    ReachS.step q qn k1 L hq hqn hk1'
  have hroot : w.top.rootKey ≠ L := by
    intro he
    exact hI.tree.rootFree q k1 (reachS_tReach _ _ _ q hq) ⟨qn, hqn, he ▸ hk1'⟩
  have hrootF : w.top.rootKey ≠ F := by
    rcases hF with h | h
    · have := hI.ids.2.2.2.2; omega
    · rw [h]; exact hroot
  -- a link of a reachable node to F is q's k1 (F = L) or none (F fresh)
  have hFfresh : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, F) ∈ xn.liveAt c.i → x = q ∧ cc = k1 := by
    intro x xn cc hx hxn hc
    rcases hF with h | h
    · have := hI.links x xn cc F hx hxn hc; omega
    · rw [h] at hc; exact honly x xn cc hx hxn hc
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧ x ≠ F) ∨
        x = F ∨ x = S ∨ x = R ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧
      x ≠ L ∧ x ≠ F) ∨ x = F ∨ x = S ∨ x = R ∨ x = v) (Or.inl ⟨ReachS.root, hroot, hrootF⟩)
    intro x xn cc z hx hxn hz
    have hhalf : ∀ (m : KNode), (∀ t, Klong.time t ∈ m.ks → t ≤ c.i) →
        (∀ c' z, (c', z) ∈ m.liveAt c.i → (c', z) = (cv, v) ∨ (c', z) ∈ n.live) →
        (cc, z) ∈ m.liveAt c.i →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ F) ∨
          z = F ∨ z = S ∨ z = R ∨ z = v := by
      intro m _ hm hzm
      rcases hm cc z hzm with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        exact Or.inr (Or.inr (Or.inr (Or.inr h1.2)))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h1
        by_cases hzF : z = F
        · exact Or.inr (Or.inl hzF)
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h1, ?_, hzF⟩
        intro hzL; subst hzL
        exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h1⟩
    rcases hx with ⟨hx, hxL, hxF⟩ | hx | hx | hx | hx
    · have hxn' := hI.reach_lt x hx
      by_cases hxq : x = q
      · subst hxq
        rw [hN'q] at hxn
        cases hxn
        rcases hqlive cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · by_cases hzF : z = F
          · exact absurd (hFfresh x qn cc hx hqn (hzF ▸ h2)).2 hne
          refine Or.inl ⟨ReachS.step x qn cc z hx hqn h2, ?_, hzF⟩
          intro hzL; subst hzL
          exact hne (honly x qn cc hx hqn h2).2
      · rw [hother x hxL hxq hxF (by omega) (by omega)] at hxn
        by_cases hzF : z = F
        · subst hzF; exact absurd (hFfresh x xn cc hx hxn hz).1 hxq
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_, hzF⟩
        intro hzL; subst hzL
        exact hxq (honly x xn cc hx hxn hz).1
    · subst hx
      rw [hN'F] at hxn
      cases hxn
      exact hhalf _ hft (fun c' z h => by
        rcases hf c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'S] at hxn
      cases hxn
      exact hhalf _ hst (fun c' z h => by
        rcases hs c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'R] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i (rootPair_times c.i F S sc)] at hz
      rcases rootPair_live_mem c.i F S sc cc z hz with ⟨_, h2⟩ | ⟨_, _, h2⟩
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inl h2)
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx
      rcases hF with h | h
      · exact hI.untaken_of_ge _ h
      · rw [h]; exact hI.untaken L hrL
    · subst hx; exact hI.untaken_of_ge _ hS
    · subst hx; exact hI.untaken_of_ge _ hR
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'F⟩ | hq'F | hq'S | hq'R | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      have hq'q : q' ≠ q := by
        intro he; subst he; rw [hN'q] at hq'n; cases hq'n; rw [hqn'l] at hq'l; cases hq'l
      rw [hother q' hq'L hq'q hq'F (by omega) (by omega)] at hq'n
      have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
        rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
      have hL'L : L' ≠ L := by
        intro he; subst he; exact hq'q (honly q' q'n k1' hq'r hq'n hk'').1
      have hL'F : L' ≠ F := by
        intro he; subst he; exact hq'q (hFfresh q' q'n k1' hq'r hq'n hk'').1
      have hL'S : L' ≠ S := by
        have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
      have hL'R : L' ≠ R := by
        have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
      by_cases hL'q : L' = q
      · subst hL'q
        rw [hN'q] at hn'
        cases hn'
        have hold := hI.order q' q'n L' qn k1' hq'r hq'n hq'l hqn hql hk'
        refine leafOrderAt_child q'n qn _ k1' hold ?_
        intro c' z hz
        rw [← KNode.liveAt_of_times _ c.i hq't] at hz
        rcases hqlive c' z hz with ⟨h1, _⟩ | ⟨_, h2⟩
        · subst h1; exact ⟨L, hk1⟩
        · rw [KNode.liveAt_of_times qn c.i hqt] at h2; exact ⟨z, h2⟩
      · rw [hother L' hL'L hL'q hL'F hL'S hL'R] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'F; rw [hN'F] at hq'n; cases hq'n; rw [hfl] at hq'l; cases hq'l
    · subst hq'S; rw [hN'S] at hq'n; cases hq'n; rw [hsl] at hq'l; cases hq'l
    · rw [hq'R, hN'R] at hq'n
      cases hq'n
      rcases rootPair_live_mem c.i F S sc k1' L' hk' with ⟨h1, h2⟩ | ⟨h1, _, h2⟩
      · rw [h2, hN'S] at hn'
        cases hn'
        intro c' z hz
        rw [← KNode.liveAt_of_times _ c.i hst] at hz
        have hb : sc ≤ c' := by
          rcases hs c' z hz with ⟨h1, h2⟩ | ⟨_, h2⟩
          · simp only [Prod.mk.injEq] at h1; omega
          · exact h2
        refine ⟨by omega, ?_⟩
        intro c'' z'' hz'' hlt
        rcases rootPair_live_mem c.i F S sc c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _, _⟩ <;> omega
      · rw [h2, hN'F] at hn'
        cases hn'
        intro c' z hz
        rw [← KNode.liveAt_of_times _ c.i hft] at hz
        have hb : c' < sc := by
          rcases hf c' z hz with ⟨h1, h2⟩ | ⟨_, h2⟩
          · simp only [Prod.mk.injEq] at h1; omega
          · exact h2
        refine ⟨by omega, ?_⟩
        intro c'' z'' hz'' hlt
        rcases rootPair_live_mem c.i F S sc c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _, _⟩ <;> omega
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-! ## The rules -/

/-- The segment root L of a key's segment, a key node, is named by a segment
leaf x of the segment before, reachable, and by no other reachable node. -/
theorem segRoot_parent (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 : Nat) (rq L : NodeId)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L) :
    ∃ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ wNode c.p base w x = some xn ∧
      xn.leaf = true ∧ (k1, L) ∈ xn.liveAt c.i := by
  have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre0 _ rq ReachS.root hrq
  obtain ⟨x, xn, hx, hxn, hxl, hs⟩ := getEqR_some_visit _ _ k1 c.p.fuel rq L hL
  have hrx := eqVisits_reach _ _ _ k1 c.p.fuel rq x k1 hrrq hx
  cases hfd : xn.searchEq c.i k1 with
  | none => rw [hfd] at hs; cases hs
  | some fd =>
    rw [hfd] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    have hm := KNode.searchEq_mem xn c.i k1 fd (hI.wf x xn hxn) hfd
    rw [hs] at hm
    exact ⟨x, xn, hrx, hxn, hxl, hm⟩

/-- No reachable inner node links a segment root. -/
theorem segRoot_noInner (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 : Nat) (rq L : NodeId)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L) :
    ∀ q qn k1', ReachS (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      qn.leaf = false → (k1', L) ∈ qn.live → False := by
  intro q qn k1' hq hqn hql hk
  obtain ⟨x, xn, hrx, hxn, hxl, hm⟩ := segRoot_parent c base w hI pre0 k1 rq L hrq hL
  have hk' : (k1', L) ∈ qn.liveAt c.i := by
    rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk
  obtain ⟨he, _⟩ := htree_of_treeOK _ _ _ hI.tree q qn k1' L hq hqn hk' x xn k1 hrx hxn hm
  subst he
  rw [hqn] at hxn; cases hxn
  rw [hxl] at hql; cases hql

theorem segRoot_facts (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true) :
    segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L ∧
    eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] ∧
    (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false) ∧
    ReachS (wNode c.p base w) c.i w.top.rootKey rq := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  · obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hNL, hnl]
  · exact fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      _ _ q.1 q.2 ReachS.root hq)
  · exact segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre0 _ rq ReachS.root hrq

/-- A put into a segment root, a leaf with room, keeps `PutInv`. -/
theorem putInv_put_room_segRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hsegL, hevL, ht, _⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  rw [hkey'] at ht ⊢
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  refine writerWP_mono (writerWP_put_room_after c base hB.coherent (pre0 ++ [k1]) cv h L w hsegL ht
    (fun L' n' hL' hn' _ => by
      rw [hevL] at hL'
      have : L' = L := by simpa using hL'
      subst this; rw [hNL] at hn'; cases hn'; exact hroom)) ?_
  intro _ w' ⟨L', n', hL', hn', hnl', htk, htop, hL'', hother⟩
  rw [hevL] at hL'
  have : L' = L := by simpa using hL'
  subst this
  exact putInvT_room c base w w' hI cv L' n' hn' hnl' htk htop hL'' hother
    (fun q qn k1' hq hqn hql hk => absurd (segRoot_noInner c base w hI pre0 k1 rq L' hrq hL q qn
      k1' hq hqn hql hk) id)

/-- A put into a segment root, a full leaf that the transaction made, by a time
split in place, keeps `PutInv`. -/
theorem putInv_put_timeInPlace_segRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨_, _, ht, _⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_put_segRoot_append c base hB.coherent pre0 k1 cv h rq L n w hrq ht hI.ids.1
    hI.ids.2.1 hL hNL hnl hfull (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 _ _ _ _ h5t h5top _ hlk5 _ _ hW5 _ _
  refine writerWP_mono (writerWP_appendKlongs_timeInPlace (d' + 1) L n cv w.next c base hB.coherent
    w5 hlk5 (by rw [h5t]; exact (wNode_cases _ _ _ _ _ hNL).1) hfirst hfull hsplit) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, _, hN'⟩
  refine putInvT_leaf c base w w' hI cv w.next L n l (Nat.le_refl _) hNL hnl (h't.trans h5t)
    (h'top.trans h5top) (by rw [hN']; simp) (by rw [hll]; exact hnl) hlt
    (live_of_lookup l n cv w.next (lookup_foldl_single l n cv w.next hlk))
    (fun x hx => by rw [hN']; simp only [hx, ↓reduceIte, hW5]) ?_
  exact fun q qn k1' hq hqn hql hk => absurd (segRoot_noInner c base w hI pre0 k1 rq L hrq hL q qn
    k1' hq hqn hql hk) id

/-- A put into a segment root, a full leaf that existed before the transaction,
below the segment leaf q with room, by a time split, keeps `PutInv`. -/
theorem putInv_put_segTimeSplit (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_put_segRoot_append c base hB.coherent pre0 k1 cv h rq L n w hrq ht hI.ids.1
    hI.ids.2.1 hL hNL hnl hfull (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 h5t h5top h5next hlk5 hlq5 hsrc5 hW5 hpq hpk
  obtain ⟨hroomq, hdeadq⟩ := hseg q qn hqv hqn hql
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  have hny : w5.nodes.lookup w5.next = none := by
    cases h' : w5.nodes.lookup w5.next with
    | none => rfl
    | some _ => have := hsrc5 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_timeSplitLeafParent d' L q n qn k1 cv w.next c w5
    hlk5 hlq5 hqL hql hfirst hfull hsplit hpq hpk hroomq hdeadq hny) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, h'nodes⟩
  rw [h5next] at h'nodes
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hyt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have htk : w'.taken = w.taken := h't.trans h5t
  have hl_eq : (⟨n.leaf, l.ks⟩ : KNode) = l := by
    cases l with
    | mk lf ks => simp only at hll; rw [hll]
  have hLy : L ≠ w.next + 2 := by have := hI.lt_next L n hNL; omega
  have hqy : q ≠ w.next + 2 := by have := hI.lt_next q qn hqn; omega
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  refine putInvT_timeSplitLeaf c base w w' hI cv k1 w.next (w.next + 2) L q n qn l (Nat.le_refl _)
    (by omega) (by omega) hNL hqn hql hrq' hk1l hqL htk (h'top.trans h5top) ?_ ?_
    (by rw [hll]; exact hnl) hlt (live_of_lookup l n cv w.next hlk) ?_
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL]
  · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h'nodes, hLy.symm, hqy.symm,
      hl_eq]
  · intro x hxL hxq hxy
    rw [← hW5]
    simp only [wNode, htk, h5t, h'nodes, hxL, hxq, hxy, ↓reduceIte]

/-- A put into a segment root, a leaf that existed before the transaction,
full by its size, with more than h klongs in its last version, below the
segment leaf q with room, by a space split into a new segment root, keeps
`PutInv`. -/
theorem putInv_put_segSpaceSplit (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hfull : c.p.M ≤ n.size + 1) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hlive : n.live ≠ [])
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_put_segRoot_append c base hB.coherent pre0 k1 cv h rq L n w hrq ht hI.ids.1
    hI.ids.2.1 hL hNL hnl (fun h' => by omega) (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 h5t h5top h5next hlk5 hlq5 hsrc5 hW5 hpq hpk
  obtain ⟨hroomq, hdeadq⟩ := hseg q qn hqv hqn hql
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  have hLn := hI.lt_next L n hNL
  have hqn' := hI.lt_next q qn hqn
  refine writerWP_mono (writerWP_appendKlongs_segSpaceSplit d' L q n qn k1 cv w.next c w5 hlk5 hlq5
    hqL hql hfirst hfull hsplit hpq hpk hroomq hdeadq (by omega) (by omega)) ?_
  intro _ w' hA
  obtain ⟨h't, h'top, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h5next] at h'nodes
  have htk : w'.taken = w.taken := h't.trans h5t
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hFt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hSt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hRt : w.taken.contains (w.next + 2 + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hqt' := hI.times q qn hqn
  have hqwf := hI.wf q qn hqn
  have e1 : w.next + 2 ≠ L := by omega
  have e2 : w.next + 2 ≠ q := by omega
  have e3 : w.next + 2 + 2 ≠ L := by omega
  have e4 : w.next + 2 + 2 ≠ q := by omega
  have e5 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  have e6 : w.next + 2 + 2 + 2 ≠ L := by omega
  have e7 : w.next + 2 + 2 + 2 ≠ q := by omega
  have e8 : w.next + 2 + 2 + 2 ≠ w.next + 2 := by omega
  have e9 : w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 := by omega
  refine putInvT_segSpaceSplit c base w w' hI cv out.2.2 k1 w.next (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) L q n qn (qn.add c.i (.key k1 (w.next + 2 + 2 + 2))) out.1 out.2.1
    (Nat.le_refl _) (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hNL hqn hql hrq' hk1l hqL htk (h'top.trans h5top) ?_
    (by rw [KNode.add_leaf]; exact hql) (KNode.add_times _ c.i _ (fun s h => by cases h) hqt') ?_ ?_
    ?_ ?_ hfl.1 hfl.2 hht.1 hht.2 (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) ?_
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL]
  · intro c' z hz
    rcases KNode.add_key_liveAt_mem qn c.i k1 _ hqwf hqt' c' z hz with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h'nodes, e6, e7, e8, e9, newKlongs,
      List.map]
  · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h'nodes, e1, e2]
  · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, e3, e4, e5]
  · intro x hxL hxq hxF hxS hxR
    rw [← hW5]
    simp only [wNode, htk, h5t, h'nodes, hxL, hxq, hxF, hxS, hxR, ↓reduceIte]

/-- A put into a segment root, a leaf that the transaction made, full by its
size, with more than h klongs in its last version, below the segment leaf q, by
a space split in place into a new segment root (q's klong repointed), keeps
`PutInv`. -/
theorem putInv_put_segSpaceSplitInPlace (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hfull : c.p.M ≤ n.size + 1) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hlive : n.live ≠ []) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_put_segRoot_append c base hB.coherent pre0 k1 cv h rq L n w hrq ht hI.ids.1
    hI.ids.2.1 hL hNL hnl (fun h' => by omega) (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 h5t h5top h5next hlk5 hlq5 hsrc5 hW5 hpq hpk
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  have hLn := hI.lt_next L n hNL
  have hqn' := hI.lt_next q qn hqn
  have hny : w5.nodes.lookup (w5.next + 2) = none := by
    cases h' : w5.nodes.lookup (w5.next + 2) with
    | none => rfl
    | some _ => have := hsrc5 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_segSpaceSplitInPlace d' L q n qn k1 cv w.next c w5
    hlk5 hlq5 hqL hql hfirst hfull hsplit hpq hpk (by omega) (by omega) hny) ?_
  intro _ w' hA
  obtain ⟨j, hj, h't, h'top, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h5next] at h'nodes
  have htk : w'.taken = w.taken := h't.trans h5t
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hRt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hqt' := hI.times q qn hqn
  have hrt : ∀ s, Klong.time s ∈ (qn.repoint j (w.next + 2 + 2)).ks → s ≤ c.i :=
    fun s hs => hqt' s (repoint_time_mem qn j _ s hs)
  have hrl : (qn.repoint j (w.next + 2 + 2)).leaf = qn.leaf := by
    unfold KNode.repoint; split <;> rfl
  have e1 : w.next + 2 ≠ L := by omega
  have e2 : w.next + 2 ≠ q := by omega
  have e3 : w.next + 2 + 2 ≠ L := by omega
  have e4 : w.next + 2 + 2 ≠ q := by omega
  have e5 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  refine putInvT_segSpaceSplit c base w w' hI cv out.2.2 k1 w.next L (w.next + 2) (w.next + 2 + 2)
    L q n qn (qn.repoint j (w.next + 2 + 2)) out.1 out.2.1
    (Nat.le_refl _) (by omega) (by omega) (Or.inr rfl) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hNL hqn hql hrq' hk1l hqL htk (h'top.trans h5top) ?_
    (by rw [hrl]; exact hql) hrt ?_ ?_ ?_ ?_ hfl.1 hfl.2 hht.1 hht.2 (by rw [hsc]; exact hfh)
    (by rw [hsc]; exact hsh) ?_
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL]
  · intro c' z hz
    rw [KNode.liveAt_of_times _ c.i hrt] at hz
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hz
    rw [KNode.repoint_live_lookup qn L _ k1 j hj c'] at hl
    by_cases hc : k1 = c'
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
      exact Or.inl ⟨rfl, hl.symm⟩
    · have hb : (k1 == c') = false := by simpa using hc
      rw [hb] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      refine Or.inr ⟨fun he => hc he.symm, ?_⟩
      rw [KNode.liveAt_of_times qn c.i hqt']
      exact lookup_some_mem hl
  · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h'nodes, e3, e4, e5, newKlongs,
      List.map]
  · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h'nodes]
  · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, e1, e2]
  · intro x hxL hxq _ hxS hxR
    rw [← hW5]
    simp only [wNode, htk, h5t, h'nodes, hxL, hxq, hxS, hxR, ↓reduceIte]

/-- Every put into a segment root that is a leaf below the segment leaf of the
key's segment before, with room for a klong there, keeps `PutInv` (the writer's
tree after it given; the rules of `writerWP_put_segLeaf_inv`). -/
theorem putInv_put_segLeaf (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · exact putInv_put_room_segRoot c base B top0 hB pre0 k1 cv h rq L n w hI hw hrq hL hNL hnl hroom
  · by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact putInv_put_segSpaceSplitInPlace c base B top0 hB pre0 k1 cv h rq L n w hI hw hrq hL
          hNL hnl hsp.1 hnew hsp.2 (hlive hsp.2)
      · exact putInv_put_timeInPlace_segRoot c base B top0 hB pre0 k1 cv h rq L n w hI hw hrq hL
          hNL hnl hroom hnew (fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩))
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact putInv_put_segSpaceSplit c base B top0 hB pre0 k1 cv h rq L n w hI hw hrq hL hNL hnl
          hsp.1 hnew hsp.2 (hlive hsp.2) hseg
      · exact putInv_put_segTimeSplit c base B top0 hB pre0 k1 cv h rq L n w hI hw hrq hL hNL hnl
          hroom hnew (fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)) hseg

end SIS.Tree
