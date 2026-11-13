import SIS.Tree.GetInPlaceCascade
import SIS.Tree.PutInvCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the cascades into a parent the transaction made (bergdb
024-12, TP10; latest's `writerWP_put_timeSplitQIP` and
`writerWP_put_spaceSplitQIP`): the leaf L, which existed before the
transaction, is time split or space split, and its parent q, made by the
transaction and full, is time split in place: q keeps its id, with its live
klongs and the klongs to L's new nodes. No node above q changes. -/

/-- `putInvT_timeSplit` with q's node after it given by its live klongs: q's
live klongs and k1 to the new leaf y, which holds L's live klongs and the put's
(cv, v). -/
theorem putInvT_timeSplitG (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv k1 : Nat) (v y L q : NodeId) (n qn l lq : KNode) (hv : w.next ≤ v) (hy : w.next ≤ y)
    (hvy : v ≠ y)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hq : ReachS (wNode c.p base w) c.i w.top.rootKey q) (hk1 : (k1, L) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'L : wNode c.p base w' L = some (n.toPrev (c.i - 1)))
    (hN'q : wNode c.p base w' q = some lq) (hlql : lq.leaf = false)
    (hlqt : ∀ s, Klong.time s ∈ lq.ks → s ≤ c.i)
    (hlqlive : ∀ c' z, (c', z) ∈ lq.live → (c' = k1 ∧ z = y) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live))
    (hN'y : wNode c.p base w' y = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ y → wNode c.p base w' x = wNode c.p base w x)
    (hpar : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hqnext := hI.lt_next q qn hqn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) hvy]; exact hvN
  have hqL : q ≠ L := by intro he; subst he; rw [hn] at hqn; cases hqn; rw [hnl] at hql; cases hql
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  -- the one link to L is q's k1
  have honly : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hq hqn hk1'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    ReachS.step q qn k1 L hq hqn hk1'
  have hroot : w.top.rootKey ≠ L := by
    intro he
    exact hI.tree.rootFree q k1 (reachS_tReach _ _ _ q hq) ⟨qn, hqn, he ▸ hk1'⟩
  -- reachable after: reachable before but L, or y, or v
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
        rw [KNode.liveAt_of_times _ c.i hlqt] at hz
        rcases hlqlive cc z hz with ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inl h2)
        · rw [← KNode.liveAt_of_times qn c.i hqt] at h2
          refine Or.inl ⟨ReachS.step x qn cc z hx hqn h2, ?_⟩
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
      -- a leaf child of q' after: not q
      have hL'q : L' ≠ q := by
        intro he; subst he; rw [hN'q] at hn'; cases hn'
        rw [hlql] at hnl'; cases hnl'
      by_cases hq'q : q' = q
      · subst hq'q
        rw [hN'q] at hq'n
        cases hq'n
        have hold : LeafOrderAt qn k1 n := hI.order q' qn L n k1 hq hqn hql hn hnl hk1
        rcases hlqlive k1' L' hk' with ⟨h1, h2⟩ | ⟨hne, h2⟩
        · subst h1 h2
          rw [hN'y] at hn'
          cases hn'
          intro c' z hz
          have hb : k1' ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1' < c'' → c' < c'' := by
            rcases hlive c' z hz with ⟨h1, _⟩ | h1
            · subst h1; exact hpar
            · exact hold c' z h1
          refine ⟨hb.1, ?_⟩
          intro c'' z'' hz'' hlt
          rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨_, h3⟩
          · omega
          · exact hb.2 c'' z'' h3 hlt
        · have hk'' : (k1', L') ∈ qn.liveAt c.i := by
            rw [KNode.liveAt_of_times qn c.i hqt]; exact h2
          have hL'L : L' ≠ L := by
            intro he; subst he; exact hne (honly q' qn k1' hq hqn hk'').2
          have hL'y : L' ≠ y := by
            have := hI.links q' qn k1' L' hq hqn hk''; omega
          rw [hother L' hL'L hL'q hL'y] at hn'
          have ho := hI.order q' qn L' n' k1' hq hqn hql hn' hnl' h2
          intro c' z hz
          refine ⟨(ho c' z hz).1, ?_⟩
          intro c'' z'' hz'' hlt
          rcases hlqlive c'' z'' hz'' with ⟨h3, _⟩ | ⟨_, h3⟩
          · subst h3; exact (ho c' z hz).2 c'' L hk1 hlt
          · exact (ho c' z hz).2 c'' z'' h3 hlt
      · rw [hother q' hq'L hq'q (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honly q' q'n k1' hq'r hq'n hk'').1
        have hL'y : L' ≠ y := by
          have := hI.links q' q'n k1' L' hq'r hq'n hk''; omega
        rw [hother L' hL'L hL'q hL'y] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'y; rw [hN'y] at hq'n; cases hq'n; rw [hll] at hq'l; cases hq'l
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

/-- A put of a key whose prefix is there into a full segment leaf that existed
before the transaction, below an inner segment root and an inner parent that
the transaction made, by a time split, the parent full with the klong to the
leaf's new node and time split in place, keeps `PutInv` (the writer's tree after
it given; the rule of latest's `writerWP_put_timeSplitQIP`). -/
theorem putInv_put_timeSplitQIP (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.firstTime = some c.i ∧
      (∀ k1, ¬ (qn.size + 1 + 1 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false)) ∧
      (c.p.M < qn.size + 1 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)) :
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
    (fun L n hL hn hnl => (hleaf L n hL hn hnl).1)
  intro L n q qn k1 d' w4 hL hn hnl hqv hqn hql hk1 hqL h4t h4top h4next hlk4 hlq4 hsrc4 hW4
    hpq hpk
  obtain ⟨hfull, hfirst, hsplit⟩ := hleaf L n hL hn hnl
  obtain ⟨hqfirst, hqfull, hqsplit⟩ := hparent q qn hqv hqn hql
  have hny : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hyt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  refine writerWP_mono (writerWP_appendKlongs_timeSplitQIP d' L q n qn k1 cv w.next c base
    hB.coherent w4 hlk4 hlq4 (by rw [h4t]; exact hLt) (by rw [h4t]; exact hqt)
    (by rw [h4t, h4next]; exact hyt) hqL hql hfirst hqfirst hfull hsplit hpq hpk
    (by rw [h4next]; exact hqfull k1) hqsplit hny) ?_
  intro _ w' ⟨l, lq, hll, _, hlt, hlk, hlql, _, hlqt, hlqk, h't, h'top, _, h'N⟩
  rw [h4next] at h'N hlqk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hl_eq : (⟨n.leaf, l.ks⟩ : KNode) = l := by
    cases l with
    | mk lf ks => simp only at hll; rw [hll]
  have hLy : L ≠ w.next + 2 := by have := hI.lt_next L n hn; omega
  have hqy : q ≠ w.next + 2 := by have := hI.lt_next q qn hqn; omega
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  refine putInvT_timeSplitG c base w w' hI cv k1 w.next (w.next + 2) L q n qn l lq (Nat.le_refl _)
    (by omega) (by omega) hn hnl hqn hql hrq hk1l htk (h'top.trans h4top) ?_ ?_
    (by rw [hlql]; exact hql) hlqt (live_of_lookup' lq qn k1 (w.next + 2) hlqk) ?_
    (by rw [hll]; exact hnl) hlt (live_of_lookup l n cv w.next hlk) ?_
    (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
  · rw [h'N]; simp
  · rw [h'N]; simp [hqL]
  · rw [h'N]; simp [hLy.symm, hqy.symm, hl_eq]
  · intro x hxL hxq hxy
    rw [h'N]
    simp only [hxL, hxq, hxy, ↓reduceIte]
    rw [hW4]

/-- A put of a key whose prefix is there into a full segment leaf that existed
before the transaction, below an inner segment root and an inner parent that
the transaction made, by a space split, the parent full by its size with the
two klongs to the halves and time split in place, keeps `PutInv` (the writer's
tree after it given; the rule of latest's `writerWP_put_spaceSplitQIP`). -/
theorem putInv_put_spaceSplitQIP (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
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
      qn.firstTime = some c.i ∧ c.p.M < qn.size + 2 + 1 ∧
      (qn.lastVersion c.i).size ≤ c.p.splitAbove) :
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
  obtain ⟨hqfirst, hqfull, hqsplit⟩ := hparent q qn hqv hqn hql
  have hn1 : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  have hn2 : w4.nodes.lookup (w4.next + 2) = none := by
    cases h' : w4.nodes.lookup (w4.next + 2) with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hFt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hSt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitQIP d' L q n qn k1 cv w.next c base
    hB.coherent w4 hlk4 hlq4 (by rw [h4t]; exact hLt) (by rw [h4t]; exact hqt)
    (by rw [h4t, h4next]; exact hFt) (by rw [h4t, h4next]; exact hSt) hqL hql hfirst hqfirst
    (by omega) hsplit hpq hpk (fun h' => by omega) (fun _ => hqsplit) hn1 hn2) ?_
  intro _ w' ⟨lq, hlql, _, hlqt, hlqk, h't, h'top, _, h'N⟩
  obtain ⟨r0, hr0⟩ := live_ne_nil_head n hlive
  obtain ⟨hsc, hfh, hsh⟩ := halves_leaf_live n c.i hnl cv w.next r0 hr0
  have hfl := halves_leaf_flags n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]
  have hht := halves_times n.leaf n c.i [(cv, w.next)]
  rw [hnl] at h'N hfl hht hlqk
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, w.next)] = out at *
  rw [h4next] at h'N hlqk
  have htk : w'.taken = w.taken := h't.trans h4t
  have hLn := hI.lt_next L n hn
  have hqn' := hI.lt_next q qn hqn
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  have hqt' := hI.times q qn hqn
  -- the parent's live klongs after its time split in place
  have hlqlive : ∀ c' z, (c', z) ∈ lq.live → (c' = out.2.2 ∧ z = w.next + 2 + 2) ∨
      (c' = k1 ∧ z = w.next + 2) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live) := by
    intro c' z hz
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup lq) c' z hz
    rw [hlqk c'] at hl
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hl
    by_cases h1 : out.2.2 = c'
    · simp only [h1, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
      exact Or.inl ⟨h1.symm, hl.symm⟩
    · have hb1 : (out.2.2 == c') = false := by simpa using h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hl
      by_cases h2 : k1 = c'
      · simp only [h2, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
        exact Or.inr (Or.inl ⟨h2.symm, hl.symm⟩)
      · have hb2 : (k1 == c') = false := by simpa using h2
        simp only [hb2, Bool.false_eq_true, ↓reduceIte] at hl
        exact Or.inr (Or.inr ⟨fun h => h2 h.symm, lookup_some_mem hl⟩)
  have h4 : w.next + 2 + 2 = w.next + 4 := by omega
  refine putInvT_spaceSplit c base w w' hI cv k1 out.2.2 w.next (w.next + 2) (w.next + 4) L q n qn
    out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega)
    hn hnl hqn hql hrq hk1l htk (h'top.trans h4top) lq ?_ (by rw [hlql]; exact hql) hlqt ?_ ?_ ?_
    hfl.1 hfl.2 hht.1 hht.2
    (by rw [hsc]; exact hfh) (by rw [hsc]; exact hsh) (by rw [hsc]; exact divider_mem n r0 hr0) ?_
    (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
  · rw [h'N]; simp [hqL]
  · intro c' z h
    rw [KNode.liveAt_of_times _ c.i hlqt] at h
    rw [KNode.liveAt_of_times _ c.i hqt']
    rcases hlqlive c' z h with h1 | h1 | h1
    · left; exact ⟨h1.1, by rw [h1.2, h4]⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · have h1 : w.next + 2 ≠ L := by omega
    have h2 : w.next + 2 ≠ q := by omega
    rw [h'N]; simp [h1, h2]
  · have h1 : w.next + 4 ≠ L := by omega
    have h2 : w.next + 4 ≠ q := by omega
    rw [h'N]; simp [h1, h2, h4]
  · intro x hxL hxq hxF hxS
    rw [h'N]
    simp only [hxL, hxq, hxF, h4, hxS, ↓reduceIte]
    rw [hW4]

end SIS.Tree
