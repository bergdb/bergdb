import SIS.Tree.PutInvSplit
import SIS.Tree.WriterTreeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the space splits of a put below an inner parent with room
(bergdb 024-12, TP10): of a leaf that existed before the transaction (two new
halves, `putInv_put_spaceSplit_below`) and in place (the leaf keeps the first
half, `putInv_put_spaceSplitInPlace_below`). The halves' compare values lie on
either side of the divider sc, the second half's first compare value, a live
compare value of the leaf (`halves_leaf_live`); the parent's klong k1 names the
first half and a klong sc the second. -/

/-- The parts about the tree after a space split of a leaf L below its inner
parent q: q's klong k1 names the first half F (or L itself, in place), a klong
of the divider sc the second half S; their live klongs are L's and the put's
(cv, v), below sc in F and at or above it in S. -/
theorem putInvT_spaceSplit (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv k1 sc : Nat) (v F S L q : NodeId) (n qn f s : KNode)
    (hv : w.next ≤ v) (hS : w.next ≤ S) (hvS : v ≠ S)
    (hF : w.next ≤ F ∨ F = L) (hvF : v ≠ F) (hFS : F ≠ S)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hq : ReachS (wNode c.p base w) c.i w.top.rootKey q) (hk1 : (k1, L) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (qn' : KNode) (hN'q : wNode c.p base w' q = some qn') (hq2l : qn'.leaf = false)
    (hq2t : ∀ t, Klong.time t ∈ qn'.ks → t ≤ c.i)
    (hqlive : ∀ c' z, (c', z) ∈ qn'.liveAt c.i →
      (c' = sc ∧ z = S) ∨ (c' = k1 ∧ z = F) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt c.i))
    (hN'F : wNode c.p base w' F = some f) (hN'S : wNode c.p base w' S = some s)
    (hfl : f.leaf = true) (hsl : s.leaf = true)
    (hft : ∀ t, Klong.time t ∈ f.ks → t ≤ c.i) (hst : ∀ t, Klong.time t ∈ s.ks → t ≤ c.i)
    (hf : ∀ c' z, (c', z) ∈ f.liveAt c.i → ((c', z) = (cv, v) ∧ cv < sc) ∨ ((c', z) ∈ n.live ∧ c' < sc))
    (hs : ∀ c' z, (c', z) ∈ s.liveAt c.i →
      ((c', z) = (cv, v) ∧ sc ≤ cv) ∨ ((c', z) ∈ n.live ∧ sc ≤ c'))
    (hsc : ∃ zs, (sc, zs) ∈ n.live)
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → wNode c.p base w' x = wNode c.p base w x)
    (hpar : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hqnext := hI.lt_next q qn hqn
  have hqL : q ≠ L := by intro he; subst he; rw [hn] at hqn; cases hqn; rw [hnl] at hql; cases hql
  have hqF : q ≠ F := by
    rcases hF with h | h
    · omega
    · rw [h]; exact hqL
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvL : v ≠ L := by omega
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v hvL (by omega) hvF hvS]; exact hvN
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
  have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hq hqn hql hn hnl hk1
  have hscb : k1 ≤ sc ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → sc < c'' := by
    obtain ⟨zs, hzs⟩ := hsc
    exact hold sc zs hzs
  have hfree : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z ≠ S ∧ z ≠ v :=
    fun x xn cc z hx hxn hz => by
      have := hI.links x xn cc z hx hxn hz; exact ⟨by omega, by omega⟩
  -- F after: L in place, or a fresh id
  have hFfresh : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, F) ∈ xn.liveAt c.i → x = q ∧ cc = k1 := by
    intro x xn cc hx hxn hc
    rcases hF with h | h
    · have := hI.links x xn cc F hx hxn hc; omega
    · rw [h] at hc; exact honly x xn cc hx hxn hc
  -- reachable after: reachable before but L, or F, S, v
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧ x ≠ F) ∨ x = F ∨ x = S ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧
      x ≠ F) ∨ x = F ∨ x = S ∨ x = v)
    · by_cases hrF : w.top.rootKey = F
      · exact Or.inr (Or.inl hrF)
      · exact Or.inl ⟨ReachS.root, hroot, hrF⟩
    intro x xn cc z hx hxn hz
    -- the links of the halves
    have hhalf : ∀ (m : KNode), (∀ t, Klong.time t ∈ m.ks → t ≤ c.i) →
        (∀ c' z, (c', z) ∈ m.liveAt c.i → (c', z) = (cv, v) ∨ (c', z) ∈ n.live) →
        (cc, z) ∈ m.liveAt c.i →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ F) ∨ z = F ∨ z = S ∨ z = v := by
      intro m _ hm hzm
      rcases hm cc z hzm with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        exact Or.inr (Or.inr (Or.inr h1.2))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h1
        by_cases hzF : z = F
        · exact Or.inr (Or.inl hzF)
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h1, ?_, hzF⟩
        intro hzL; subst hzL
        exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h1⟩
    rcases hx with ⟨hx, hxL, hxF⟩ | hx | hx | hx
    · have hxn' := hI.reach_lt x hx
      by_cases hxq : x = q
      · subst hxq
        rw [hN'q] at hxn
        cases hxn
        rcases hqlive cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inl h2)
        · by_cases hzF : z = F
          · exact Or.inr (Or.inl hzF)
          refine Or.inl ⟨ReachS.step x qn cc z hx hqn h2, ?_, hzF⟩
          intro hzL; subst hzL
          exact hne (honly x qn cc hx hqn h2).2
      · rw [hother x hxL hxq hxF (by omega)] at hxn
        have hzS := hfree x xn cc z hx hxn hz
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
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx
      rcases hF with h | h
      · exact hI.untaken_of_ge _ h
      · rw [h]; exact hI.untaken L hrL
    · subst hx; exact hI.untaken_of_ge _ hS
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    -- the order below the new parent
    have hfo : LeafOrderAt qn' k1 f := by
      intro c' z hz
      rw [← KNode.liveAt_of_times f c.i hft] at hz
      have hb : (k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'') ∧ c' < sc := by
        rcases hf c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
        · exact ⟨hold c' z h1, h2⟩
      refine ⟨hb.1.1, ?_⟩
      intro c'' z'' hz'' hlt
      rw [← KNode.liveAt_of_times _ c.i hq2t] at hz''
      rcases hqlive c'' z'' hz'' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1]; exact hb.2
      · omega
      · rw [KNode.liveAt_of_times qn c.i hqt] at h2
        exact hb.1.2 c'' z'' h2 hlt
    have hso : LeafOrderAt qn' sc s := by
      intro c' z hz
      rw [← KNode.liveAt_of_times s c.i hst] at hz
      have hb : (k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'') ∧ sc ≤ c' := by
        rcases hs c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
        · exact ⟨hold c' z h1, h2⟩
      refine ⟨hb.2, ?_⟩
      intro c'' z'' hz'' hlt
      rw [← KNode.liveAt_of_times _ c.i hq2t] at hz''
      rcases hqlive c'' z'' hz'' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
      · omega
      · omega
      · rw [KNode.liveAt_of_times qn c.i hqt] at h2
        exact hb.1.2 c'' z'' h2 (by omega)
    have hoo : ∀ k1' L' n', (k1', L') ∈ qn.live → k1' ≠ k1 → LeafOrderAt qn k1' n' →
        LeafOrderAt qn' k1' n' := by
      intro k1' L' n' hkL' hne ho c' z hz
      refine ⟨(ho c' z hz).1, ?_⟩
      intro c'' z'' hz'' hlt
      rw [← KNode.liveAt_of_times _ c.i hq2t] at hz''
      rcases hqlive c'' z'' hz'' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
      · subst h1
        by_cases hk : k1' < k1
        · have := (ho c' z hz).2 k1 L hk1 hk; omega
        · have hk' : k1 < k1' := by omega
          have := hscb.2 k1' L' hkL' hk'; omega
      · subst h1; exact (ho c' z hz).2 _ L hk1 hlt
      · rw [KNode.liveAt_of_times qn c.i hqt] at h2
        exact (ho c' z hz).2 c'' z'' h2 hlt
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'F⟩ | hq'F | hq'S | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      have hL'q : L' ≠ q := by
        intro he; subst he; rw [hN'q] at hn'; cases hn'; rw [hq2l] at hnl'; cases hnl'
      by_cases hq'q : q' = q
      · subst hq'q
        rw [hN'q] at hq'n
        cases hq'n
        rw [← KNode.liveAt_of_times _ c.i hq2t] at hk'
        rcases hqlive k1' L' hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hne, h2⟩
        · subst h1 h2; rw [hN'S] at hn'; cases hn'; exact hso
        · subst h1 h2; rw [hN'F] at hn'; cases hn'; exact hfo
        · have hL'L : L' ≠ L := by
            intro he; subst he; exact hne (honly q' qn k1' hq hqn h2).2
          have hL'F : L' ≠ F := by
            intro he; subst he; exact hne (hFfresh q' qn k1' hq hqn h2).2
          have hL'S : L' ≠ S := (hfree q' qn k1' L' hq hqn h2).1
          rw [hother L' hL'L hL'q hL'F hL'S] at hn'
          rw [KNode.liveAt_of_times qn c.i hqt] at h2
          exact hoo k1' L' n' h2 hne (hI.order q' qn L' n' k1' hq hqn hql hn' hnl' h2)
      · rw [hother q' hq'L hq'q hq'F (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honly q' q'n k1' hq'r hq'n hk'').1
        have hL'F : L' ≠ F := by
          intro he; subst he; exact hq'q (hFfresh q' q'n k1' hq'r hq'n hk'').1
        have hL'S : L' ≠ S := (hfree q' q'n k1' L' hq'r hq'n hk'').1
        rw [hother L' hL'L hL'q hL'F hL'S] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'F; rw [hN'F] at hq'n; cases hq'n; rw [hfl] at hq'l; cases hq'l
    · subst hq'S; rw [hN'S] at hq'n; cases hq'n; rw [hsl] at hq'l; cases hq'l
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-! ## The rules -/

theorem flatAt_times (i : Time) (ks : List Klong) (h : FlatAt i ks) :
    ∀ s, Klong.time s ∈ ks → s ≤ i := by
  obtain ⟨r, rfl, hr⟩ := h
  intro s hs
  rcases List.mem_cons.mp hs with h1 | h1
  · cases h1; exact Nat.le_refl _
  · obtain ⟨cv, y, he⟩ := hr _ h1; cases he

theorem halves_leaf_flags (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.leaf = leaf ∧ (halves leaf t last ins).2.1.leaf = leaf := by
  unfold halves
  simp only []
  constructor <;> (split <;> (try split) <;> (try split) <;> simp_all)

theorem halves_times (leaf : Bool) (n : KNode) (t : Time) (ins : List (Nat × NodeId)) :
    (∀ s, Klong.time s ∈ (halves leaf t (n.lastVersion t) ins).1.ks → s ≤ t) ∧
    (∀ s, Klong.time s ∈ (halves leaf t (n.lastVersion t) ins).2.1.ks → s ≤ t) := by
  have h := halves_flatAt leaf t (n.lastVersion t) ins (KNode.lastVersion_flat n t)
  exact ⟨flatAt_times t _ h.1, flatAt_times t _ h.2⟩

theorem divider_mem (n : KNode) (r0 : Nat × NodeId)
    (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0) : ∃ zs, (r0.1, zs) ∈ n.live :=
  ⟨r0.2, List.mem_of_mem_drop (List.mem_of_mem_head? hr0)⟩

theorem live_ne_nil_head (n : KNode) (h : n.live ≠ []) :
    ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
  cases hd : (n.live.drop (n.live.length / 2)).head? with
  | some r0 => exact ⟨r0, rfl⟩
  | none =>
    exfalso
    rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
    have : n.live.length ≠ 0 := fun h0 => h (List.eq_nil_of_length_eq_zero h0)
    omega

/-- A put of a key whose prefix is there into a full segment leaf that existed
before the transaction, below an inner segment root and an inner parent with
room for two klongs, by a space split, keeps `PutInv` (the writer's tree after
it given). -/
theorem putInv_put_spaceSplit_below (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧
      c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      (pre ++ [cv]) _ q.1 q.2 ReachS.root hq)
  apply writerWP_put_seg_append c base hB.coherent pre cv h rk w hrk ht hI.ids.1 hI.ids.2.1 hinner
    (fun L n hL hn hnl hroom => by
      have := (hleaf L n hL hn hnl).1; omega)
  intro L n q qn k1 d' w4 hL hn hnl hqv hqn hql hk1 hqL h4t h4top h4next hlk4 hlq4 hsrc4 hW4
    hpq hpk
  obtain ⟨hfull, hfirst, hsplit, hlive⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hn1 : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  have hn2 : w4.nodes.lookup (w4.next + 2) = none := by
    cases h' : w4.nodes.lookup (w4.next + 2) with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_spaceSplit d' L q n qn k1 cv w.next c w4 hlk4 hlq4
    hqL hql hfirst (by omega) hsplit hpq hpk hroomq (fun y1 sc y2 => hdeadq k1 y1 sc y2) hn1 hn2) ?_
  intro _ w' hA
  obtain ⟨h't, h'top, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have htk : w'.taken = w.taken := h't.trans h4t
  have hLn := hI.lt_next L n hn
  have hqn' := hI.lt_next q qn hqn
  have hFt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hSt : w.taken.contains (w.next + 4) = false := hI.untaken_of_ge _ (by omega)
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  have hqt' := hI.times q qn hqn
  have hqwf := hI.wf q qn hqn
  have hq1wf := KNode.add_key_wf qn c.i k1 (w.next + 2) hqwf
  have hq1t := KNode.add_times qn c.i (.key k1 (w.next + 2)) (fun s h => by cases h) hqt'
  rw [h4next] at h'nodes
  refine putInvT_spaceSplit c base w w' hI cv k1 out.2.2 w.next (w.next + 2) (w.next + 4) L q n qn
    out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
    hn hnl hqn hql hrq hk1l htk (h'top.trans h4top)
    ((qn.add c.i (.key k1 (w.next + 2))).add c.i (.key out.2.2 (w.next + 2 + 2))) ?_
    (by rw [KNode.add_leaf, KNode.add_leaf]; exact hql)
    (KNode.add_times _ c.i _ (fun s h => by cases h) hq1t) ?_ ?_ ?_ hfl.1 hfl.2 hht.1 hht.2
    (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) (by rw [hsc]; exact divider_mem n r0 hr0) ?_
    (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL]
  · intro c' z h
    rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with h1 | ⟨_, h1⟩
    · left; exact ⟨h1.1, by rw [h1.2]⟩
    · rcases KNode.add_key_liveAt_mem qn c.i k1 _ hqwf hqt' c' z h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  · have h1 : w.next + 2 ≠ L := by omega
    have h2 : w.next + 2 ≠ q := by omega
    simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h'nodes, h1, h2]
  · have h1 : w.next + 4 ≠ L := by omega
    have h2 : w.next + 4 ≠ q := by omega
    have h3 : w.next + 4 ≠ w.next + 2 := by omega
    have h4 : w.next + 2 + 2 = w.next + 4 := by omega
    simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, h1, h2, h3, h4]
  · intro x hxL hxq hxF hxS
    rw [← hW4]
    have h4 : w.next + 2 + 2 = w.next + 4 := by omega
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, hxF, h4, hxS, ↓reduceIte]

/-- A put of a key whose prefix is there into a full segment leaf that the
transaction made, below an inner segment root and an inner parent with room, by
a space split in place, keeps `PutInv` (the writer's tree after it given). -/
theorem putInv_put_spaceSplitInPlace_below (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      c.p.M ≤ n.size + 1 ∧ n.firstTime = some c.i ∧
      c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      (pre ++ [cv]) _ q.1 q.2 ReachS.root hq)
  apply writerWP_put_seg_append c base hB.coherent pre cv h rk w hrk ht hI.ids.1 hI.ids.2.1 hinner
    (fun L n hL hn hnl hroom => by
      have := (hleaf L n hL hn hnl).1; omega)
  intro L n q qn k1 d' w4 hL hn hnl hqv hqn hql hk1 hqL h4t h4top h4next hlk4 hlq4 hsrc4 hW4
    hpq hpk
  obtain ⟨hfull, hfirst, hsplit, hlive⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hLn := hI.lt_next L n hn
  have hqn' := hI.lt_next q qn hqn
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitInPlace d' L q n qn cv w.next c w4 hlk4 hlq4
    hqL hql hfirst hfull hsplit hpq hroomq hdeadq (by omega) (by omega)) ?_
  intro _ w' hA
  obtain ⟨h't, h'top, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have htk : w'.taken = w.taken := h't.trans h4t
  have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  have hqt' := hI.times q qn hqn
  have hqwf := hI.wf q qn hqn
  rw [h4next] at h'nodes
  refine putInvT_spaceSplit c base w w' hI cv k1 out.2.2 w.next L (w.next + 2) L q n qn
    out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega) (Or.inr rfl) (by omega) (by omega)
    hn hnl hqn hql hrq hk1l htk (h'top.trans h4top)
    (qn.add c.i (.key out.2.2 (w.next + 2))) ?_
    (by rw [KNode.add_leaf]; exact hql)
    (KNode.add_times _ c.i _ (fun s h => by cases h) hqt') ?_ ?_ ?_ hfl.1 hfl.2 hht.1 hht.2
    (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) (by rw [hsc]; exact divider_mem n r0 hr0) ?_
    (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL]
  · intro c' z h
    rcases KNode.add_key_liveAt_mem qn c.i _ _ hqwf hqt' c' z h with h1 | ⟨hne, h1⟩
    · exact Or.inl h1
    · by_cases hck : c' = k1
      · subst hck
        have hn := KNode.live_keys_nodup qn
        rw [KNode.liveAt_of_times qn c.i hqt'] at h1
        have h2 := lookup_of_mem_nodup _ hn _ _ h1
        rw [lookup_of_mem_nodup _ hn _ _ hk1l] at h2
        cases h2
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨hck, h1⟩)
  · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h'nodes]
  · have h1 : w.next + 2 ≠ L := by omega
    have h2 : w.next + 2 ≠ q := by omega
    simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, h1, h2]
  · intro x hxL hxq _ hxS
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, hxS, ↓reduceIte]

end SIS.Tree
