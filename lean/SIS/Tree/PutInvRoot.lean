import SIS.Tree.PutInvLeaf
import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the splits of the space root, a leaf (bergdb 024-12,
TP10): the time split (a new root holds the last version with the put), the
space split (two halves under a new inner root), and the space split in place
of a root the transaction made (the root keeps the first half). Together with
the rules of `PutInvRoom.lean` and `PutInvSplit.lean`: every put of a key of
one segment into a space whose root is a leaf keeps `PutInv`
(`putInv_put_leafRoot`, the rules of `writerWP_put_leafRoot`). -/

/-- No reachable node links to the space root. -/
theorem PutInv.rootFree' {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (xn : KNode) (cc : Nat) (hx : ReachS (wNode c.p base w) c.i w.top.rootKey x)
    (hxn : wNode c.p base w x = some xn) (hc : (cc, w.top.rootKey) ∈ xn.liveAt c.i) : False :=
  hI.tree.rootFree x cc (reachS_tReach _ _ _ x hx) ⟨xn, hxn, hc⟩

/-- The parts about the tree after a time split of the space root L: a new
root y holds L's live klongs and the put's (cv, v). -/
theorem putInvT_rootTimeSplit (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv : Nat) (v y : NodeId) (n l : KNode) (hv : w.next ≤ v) (hy : w.next ≤ y) (hvy : v ≠ y)
    (hn : wNode c.p base w w.top.rootKey = some n)
    (htk : w'.taken = w.taken) (hrk' : w'.top.rootKey = y)
    (hN'y : wNode c.p base w' y = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hother : ∀ x, x ≠ w.top.rootKey → x ≠ y → wNode c.p base w' x = wNode c.p base w x) :
    PutInvT c base w' := by
  have hLnext := hI.lt_next _ n hn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) hvy]; exact hvN
  have hnt := hI.times _ n hn
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ w.top.rootKey) ∨ x = y ∨ x = v := by
    rw [hrk']
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧
      x ≠ w.top.rootKey) ∨ x = y ∨ x = v) (Or.inr (Or.inl rfl))
    intro x xn cc z hx hxn hz
    rcases hx with ⟨hx, hxL⟩ | hx | hx
    · have := hI.reach_lt x hx
      rw [hother x hxL (by omega)] at hxn
      refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_⟩
      intro hzL; rw [hzL] at hz; exact hI.rootFree' x xn cc hx hxn hz
    · subst hx
      rw [hN'y] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlt] at hz
      rcases hlive cc z hz with ⟨_, h2⟩ | h2
      · exact Or.inr (Or.inr h2)
      · rw [← KNode.liveAt_of_times n c.i hnt] at h2
        refine Or.inl ⟨ReachS.step _ n cc z ReachS.root hn h2, ?_⟩
        intro hzL; rw [hzL] at h2; exact hI.rootFree' _ n cc ReachS.root hn h2
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
    · have := hI.reach_lt q' hq'r
      rw [hother q' hq'L (by omega)] at hq'n
      have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
        rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
      have hL'L : L' ≠ w.top.rootKey := by
        intro he; rw [he] at hk''; exact hI.rootFree' q' q'n k1' hq'r hq'n hk''
      have hL'y : L' ≠ y := by
        have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
      rw [hother L' hL'L hL'y] at hn'
      exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'y; rw [hN'y] at hq'n; cases hq'n; rw [hll] at hq'l; cases hq'l
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-- The live klongs of a new inner root over two halves. -/
theorem rootPair_live_mem (t : Time) (F S : NodeId) (sc c' : Nat) (z : NodeId)
    (h : (c', z) ∈ (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).live) :
    (c' = sc ∧ z = S) ∨ (c' = 0 ∧ c' ≠ sc ∧ z = F) := by
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h
  rw [KNode.rootPair_live_lookup] at hl
  by_cases h1 : sc = c'
  · simp only [h1, ↓reduceIte, Option.some.injEq] at hl
    exact Or.inl ⟨h1.symm, hl.symm⟩
  · by_cases h2 : 0 = c'
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hl
      exact Or.inr ⟨h2.symm, fun h => h1 h.symm, hl.symm⟩
    · simp [h1, h2] at hl

theorem rootPair_times (t : Time) (F S : NodeId) (sc : Nat) :
    ∀ s, Klong.time s ∈ (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).ks → s ≤ t := by
  intro s hs
  simp [newKlongs] at hs
  omega

/-- The parts about the tree after a space split of the space root L: a new
inner root R names the first half F (a fresh id, or L itself in place) by the
empty key and the second half S by the divider sc. -/
theorem putInvT_rootSpaceSplit (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv sc : Nat) (v F S R : NodeId) (n f s : KNode)
    (hv : w.next ≤ v) (hS : w.next ≤ S) (hR : w.next ≤ R) (hF : w.next ≤ F ∨ F = w.top.rootKey)
    (hvS : v ≠ S) (hvR : v ≠ R) (hvF : v ≠ F) (hSR : S ≠ R) (hFS : F ≠ S) (hFR : F ≠ R)
    (hn : wNode c.p base w w.top.rootKey = some n)
    (htk : w'.taken = w.taken) (hrk' : w'.top.rootKey = R)
    (hN'R : wNode c.p base w' R = some ⟨false, newKlongs c.i [(0, F), (sc, S)]⟩)
    (hN'F : wNode c.p base w' F = some f) (hN'S : wNode c.p base w' S = some s)
    (hfl : f.leaf = true) (hsl : s.leaf = true)
    (hft : ∀ t, Klong.time t ∈ f.ks → t ≤ c.i) (hst : ∀ t, Klong.time t ∈ s.ks → t ≤ c.i)
    (hf : ∀ c' z, (c', z) ∈ f.liveAt c.i → ((c', z) = (cv, v) ∧ cv < sc) ∨ ((c', z) ∈ n.live ∧ c' < sc))
    (hs : ∀ c' z, (c', z) ∈ s.liveAt c.i →
      ((c', z) = (cv, v) ∧ sc ≤ cv) ∨ ((c', z) ∈ n.live ∧ sc ≤ c'))
    (hother : ∀ x, x ≠ w.top.rootKey → x ≠ F → x ≠ S → x ≠ R →
      wNode c.p base w' x = wNode c.p base w x) :
    PutInvT c base w' := by
  have hLnext := hI.lt_next _ n hn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvL : v ≠ w.top.rootKey := by omega
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v hvL hvF hvS hvR]; exact hvN
  have hnt := hI.times _ n hn
  -- links of reachable nodes avoid the root and the fresh ids
  have hfree : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
      z ≠ w.top.rootKey ∧ z ≠ F ∧ z ≠ S ∧ z ≠ R := by
    intro x xn cc z hx hxn hz
    have hlt := hI.links x xn cc z hx hxn hz
    have hzL : z ≠ w.top.rootKey := by
      intro he; rw [he] at hz; exact hI.rootFree' x xn cc hx hxn hz
    refine ⟨hzL, ?_, by omega, by omega⟩
    rcases hF with h | h
    · omega
    · rw [h]; exact hzL
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ w.top.rootKey ∧ x ≠ F) ∨
        x = F ∨ x = S ∨ x = R ∨ x = v := by
    rw [hrk']
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧
      x ≠ w.top.rootKey ∧ x ≠ F) ∨ x = F ∨ x = S ∨ x = R ∨ x = v) (Or.inr (Or.inr (Or.inr
      (Or.inl rfl))))
    intro x xn cc z hx hxn hz
    have hhalf : ∀ (m : KNode), (∀ t, Klong.time t ∈ m.ks → t ≤ c.i) →
        (∀ c' z, (c', z) ∈ m.liveAt c.i → (c', z) = (cv, v) ∨ (c', z) ∈ n.live) →
        (cc, z) ∈ m.liveAt c.i →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ w.top.rootKey ∧ z ≠ F) ∨
          z = F ∨ z = S ∨ z = R ∨ z = v := by
      intro m _ hm hzm
      rcases hm cc z hzm with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        exact Or.inr (Or.inr (Or.inr (Or.inr h1.2)))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h1
        obtain ⟨h2, h3, _, _⟩ := hfree _ n cc z ReachS.root hn h1
        exact Or.inl ⟨ReachS.step _ n cc z ReachS.root hn h1, h2, h3⟩
    rcases hx with ⟨hx, hxL, hxF⟩ | hx | hx | hx | hx
    · have := hI.reach_lt x hx
      rw [hother x hxL hxF (by omega) (by omega)] at hxn
      obtain ⟨h2, h3, _, _⟩ := hfree x xn cc z hx hxn hz
      exact Or.inl ⟨ReachS.step x xn cc z hx hxn hz, h2, h3⟩
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
      · rw [h]; exact hI.untaken _ ReachS.root
    · subst hx; exact hI.untaken_of_ge _ hS
    · subst hx; exact hI.untaken_of_ge _ hR
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'F⟩ | hq'F | hq'S | hq'R | hq'v
    · have := hI.reach_lt q' hq'r
      rw [hother q' hq'L hq'F (by omega) (by omega)] at hq'n
      have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
        rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
      obtain ⟨h1, h2, h3, h4⟩ := hfree q' q'n k1' L' hq'r hq'n hk''
      rw [hother L' h1 h2 h3 h4] at hn'
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

/-- A put of a key of one segment into the space root, a full leaf that existed
before the transaction, by a time split (also of a root full by its dead klongs
only), keeps `PutInv` (the writer's tree after it given). -/
theorem putInv_put_rootTimeSplit (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  have hLn := hI.lt_next _ n hroot
  apply writerWP_put_root_append c base hB.coherent cv h w n hroot hnl hrt hfull hI.ids.1
    hI.ids.2.1
  intro w4 h4t h4top h4next _ hlk4 hsrc4 hW4
  have hny : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_rootTimeSplit w.top.rootKey n cv w.next c w4
    hlk4 hfirst hfull hsplit (by omega) hny) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'rk, _, h'nodes⟩
  rw [h4next] at h'nodes
  rw [h4next] at h'rk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hyt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hl_eq : (⟨n.leaf, l.ks⟩ : KNode) = l := by
    cases l with
    | mk lf ks => simp only at hll; rw [hll]
  have hyL : w.next + 2 ≠ w.top.rootKey := by omega
  refine putInvT_rootTimeSplit c base w w' hI cv w.next (w.next + 2) n l (Nat.le_refl _) (by omega)
    (by omega) hroot htk h'rk ?_ (by rw [hll]; exact hnl) hlt
    (live_of_lookup l n cv w.next (lookup_foldl_single l n cv w.next hlk)) ?_
  · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h'nodes, hyL, hl_eq]
  · intro x hxL hxy
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxy, ↓reduceIte]

/-- A put of a key of one segment into the space root, a leaf that existed
before the transaction, full by its size, with more than h klongs in its last
version, by a space split under a new root, keeps `PutInv` (the writer's tree
after it given). -/
theorem putInv_put_rootSpaceSplit (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hfull : c.p.M ≤ n.size + 1) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hlive : n.live ≠ []) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  have hLn := hI.lt_next _ n hroot
  apply writerWP_put_root_append c base hB.coherent cv h w n hroot hnl hrt
    (fun h' => by omega) hI.ids.1 hI.ids.2.1
  intro w4 h4t h4top h4next _ hlk4 hsrc4 hW4
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceSplit w.top.rootKey n cv w.next c w4
    hlk4 hfirst hfull hsplit (by omega)) ?_
  intro _ w' hA
  obtain ⟨h't, h'rk, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h4next] at h'nodes
  rw [h4next] at h'rk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hFt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hSt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hRt : w.taken.contains (w.next + 2 + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have h1 : w.next + 2 ≠ w.top.rootKey := by omega
  have h2 : w.next + 2 + 2 ≠ w.top.rootKey := by omega
  have h3 : w.next + 2 + 2 + 2 ≠ w.top.rootKey := by omega
  have h4 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  have h5 : w.next + 2 + 2 + 2 ≠ w.next + 2 := by omega
  have h6 : w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 := by omega
  refine putInvT_rootSpaceSplit c base w w' hI cv out.2.2 w.next (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) n out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega) (Or.inl (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hroot htk h'rk ?_ ?_ ?_
    hfl.1 hfl.2 hht.1 hht.2 (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) ?_
  · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h'nodes, h3, h5, h6, newKlongs,
      List.map]
  · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h'nodes, h1]
  · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, h2, h4]
  · intro x hxL hxF hxS hxR
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxF, hxS, hxR, ↓reduceIte]

/-- A put of a key of one segment into the space root, a leaf that the
transaction made, full by its size, with more than h klongs in its last
version, by a space split in place under a new root, keeps `PutInv` (the
writer's tree after it given). -/
theorem putInv_put_rootSpaceSplitInPlace (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hfull : c.p.M ≤ n.size + 1) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hlive : n.live ≠ []) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  have hLn := hI.lt_next _ n hroot
  apply writerWP_put_root_append c base hB.coherent cv h w n hroot hnl hrt
    (fun h' => by omega) hI.ids.1 hI.ids.2.1
  intro w4 h4t h4top h4next _ hlk4 hsrc4 hW4
  have hny : w4.nodes.lookup (w4.next + 2) = none := by
    cases h' : w4.nodes.lookup (w4.next + 2) with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceSplitInPlace w.top.rootKey n cv w.next c w4
    hlk4 hfirst hfull hsplit (by omega) hny) ?_
  intro _ w' hA
  obtain ⟨h't, h'rk, _, h'nodes⟩ := hA
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'nodes hfl hht
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h4next] at h'nodes
  rw [h4next] at h'rk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hLt : w.taken.contains w.top.rootKey = false := hrt
  have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hRt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have h2 : w.next + 2 ≠ w.top.rootKey := by omega
  have h3 : w.next + 2 + 2 ≠ w.top.rootKey := by omega
  have h4 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  refine putInvT_rootSpaceSplit c base w w' hI cv out.2.2 w.next w.top.rootKey (w.next + 2)
    (w.next + 2 + 2) n out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega) (Or.inr rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hroot htk h'rk ?_ ?_ ?_
    hfl.1 hfl.2 hht.1 hht.2 (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) ?_
  · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h'nodes, h3, h4, newKlongs,
      List.map]
  · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h'nodes]
  · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h'nodes, h2]
  · intro x hxL _ hxS hxR
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxS, hxR, ↓reduceIte]

/-- Every put of a key of one segment into a space whose root is a leaf keeps
`PutInv` (the writer's tree after it given): with room, by a time split or a
space split, in place for a root the transaction made. -/
theorem putInv_put_leafRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · exact putInv_put_room_root c base B top0 hB cv h w n hI hw hroot hnl hroom
  · by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact putInv_put_rootSpaceSplitInPlace c base B top0 hB cv h w n hI hw hroot hnl hsp.1 hnew
          hsp.2 (hlive hsp.2)
      · exact putInv_put_timeInPlace_root c base B top0 hB cv h w n hI hw hroot hnl hroom hnew
          (fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩))
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact putInv_put_rootSpaceSplit c base B top0 hB cv h w n hI hw hroot hnl hsp.1 hnew
          hsp.2 (hlive hsp.2)
      · exact putInv_put_rootTimeSplit c base B top0 hB cv h w n hI hw hroot hnl hroom hnew
          (fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩))

end SIS.Tree
