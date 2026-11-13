import SIS.Tree.PutInvRoom
import SIS.Tree.GetInPlace
import SIS.Tree.WriterTreePut2
import SIS.Tree.WriterTreeRoot
import SIS.Tree.WriterTreeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the time splits of a put (bergdb 024-12, TP10): in place
(a leaf the transaction made becomes its last version with the put's klong:
`putInv_put_timeInPlace_below`, `putInv_put_timeInPlace_root`), and of a leaf
that existed before the transaction below an inner parent with room (a new
node holds the last version, the parent's klong names it:
`putInv_put_timeSplit_below`). -/

/-- Live klongs given by lookup: a node whose live lookup is n's with the
klong (cv, v) has the live klongs of n and (cv, v). -/
theorem live_of_lookup (l n : KNode) (cv : Nat) (v : NodeId)
    (h : ∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') :
    ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live := by
  intro c' z hz
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup l) c' z hz
  rw [h c'] at hl
  by_cases hc : cv = c'
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
    exact Or.inl ⟨rfl, hl.symm⟩
  · have hb : (cv == c') = false := by simpa using hc
    rw [hb] at hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hl
    exact Or.inr (lookup_some_mem hl)

theorem PutInv.lt_next {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (xn : KNode) (h : wNode c.p base w x = some xn) : x < w.next := by
  rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hk⟩
  · exact hI.ids.1 x (by rw [hl]; rfl)
  · cases Nat.lt_or_ge x w.next with
    | inl h => exact h
    | inr h => rw [(hI.fresh x h).1] at hk; cases hk

theorem PutInv.none_of_ge {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (z : NodeId) (hz : w.next ≤ z) : wNode c.p base w z = none := by
  cases h : wNode c.p base w z with
  | none => rfl
  | some xn => have := hI.lt_next z xn h; omega

theorem PutInv.untaken_of_ge {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (z : NodeId) (hz : w.next ≤ z) : w.taken.contains z = false := by
  cases h' : w.taken.contains z with
  | false => rfl
  | true => have := hI.ids.2.2.1 _ h'; omega

/-- A property of the start that every live link keeps holds of every node
reachable. -/
theorem reachS_closed (N' : NodeId → Option KNode) (t : Time) (r' : NodeId) (P : NodeId → Prop)
    (hr : P r') (hstep : ∀ x xn c z, P x → N' x = some xn → (c, z) ∈ xn.liveAt t → P z) :
    ∀ x, ReachS N' t r' x → P x := by
  intro x hx
  induction hx with
  | root => exact hr
  | step x n c z _ hn hc ih => exact hstep x n c z ih hn hc

/-- Every node reachable in the writer's tree has an id below the next one. -/
theorem PutInv.reach_lt {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (hx : ReachS (wNode c.p base w) c.i w.top.rootKey x) : x < w.next := by
  induction hx with
  | root => exact hI.ids.2.2.2.2
  | step x n cc z hx hn hc _ => exact hI.links x n cc z hx hn hc

/-- The parts about the tree after a change of a leaf L alone: its new
content l, a leaf, has the live klongs of L and a klong (cv, v) of a fresh id,
between the bounds of L's parents. -/
theorem putInvT_leaf (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv : Nat) (v L : NodeId) (n l : KNode) (hv : w.next ≤ v)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hL' : wNode c.p base w' L = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hother : ∀ x, x ≠ L → wNode c.p base w' x = wNode c.p base w x)
    (hpar : ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.live →
      k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega)]; exact hvN
  have hnt := hI.times L n hn
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      ReachS (wNode c.p base w) c.i w.top.rootKey x ∨ x = v := by
    rw [htop]
    apply reachS_sub _ _ _ _ _ _ (Or.inl ReachS.root)
    intro x xn cc z hx hxn hz
    rcases hx with hx | hx
    · by_cases hxL : x = L
      · subst hxL
        rw [hL'] at hxn
        cases hxn
        rw [KNode.liveAt_of_times _ c.i hlt] at hz
        rcases hlive cc z hz with ⟨_, h2⟩ | h2
        · exact Or.inr h2
        · rw [← KNode.liveAt_of_times n c.i hnt] at h2
          exact Or.inl (ReachS.step x n cc z hx hn h2)
      · rw [hother x hxL] at hxn
        exact Or.inl (ReachS.step x xn cc z hx hxn hz)
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q qn L2 n2 k1 hq hqn hql hn2 hnl2 hk
    have hqL : q ≠ L := by
      intro he; subst he; rw [hL'] at hqn; cases hqn
      rw [hll] at hql; cases hql
    rw [hother q hqL] at hqn
    have hq' : ReachS (wNode c.p base w) c.i w.top.rootKey q := by
      rcases hsub q hq with h | h
      · exact h
      · subst h; rw [hvN] at hqn; cases hqn
    by_cases hL2 : L2 = L
    · subst hL2
      rw [hL'] at hn2
      cases hn2
      have hold := hI.order q qn L2 n k1 hq' hqn hql hn hnl hk
      have hb := hpar q qn k1 hq' hqn hql hk
      intro c' z hz
      rcases hlive c' z hz with ⟨h1, _⟩ | h2
      · subst h1; exact hb
      · exact hold c' z h2
    · rw [hother L2 hL2] at hn2
      exact hI.order q qn L2 n2 k1 hq' hqn hql hn2 hnl2 hk

/-! ## The time split in place -/

theorem lookup_foldl_single (l n : KNode) (cv : Nat) (v : NodeId)
    (h : ∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) :
    ∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q' := by
  intro q'
  rw [h q']
  simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]

/-- A put of a key whose prefix is there into a full segment leaf that the
transaction made, below an inner segment root, by a time split in place, keeps
`PutInv` (the writer's tree after it given). -/
theorem putInv_put_timeInPlace_below (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime = some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)) :
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
  intro L n q qn k1 d' w4 hL hn hnl _ _ _ _ _ h4t h4top _ hlk4 _ _ hW4 _ _
  obtain ⟨hfull, hfirst, hsplit⟩ := hleaf L n hL hn hnl
  have hLt4 : w4.taken.contains L = false := by
    rw [h4t]; exact (wNode_cases _ _ _ _ _ hn).1
  refine writerWP_mono (writerWP_appendKlongs_timeInPlace (d' + 1) L n cv w.next c base hB.coherent
    w4 hlk4 hLt4 hfirst hfull hsplit) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, _, hN'⟩
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  refine putInvT_leaf c base w w' hI cv w.next L n l (Nat.le_refl _) hn hnl (h't.trans h4t)
    (h'top.trans h4top) (by rw [hN']; simp) (by rw [hll]; exact hnl) hlt
    (live_of_lookup l n cv w.next (lookup_foldl_single l n cv w.next hlk))
    (fun x hx => by rw [hN']; simp only [hx, ↓reduceIte, hW4]) ?_
  exact fun q qn k1 hq hqn _ hk => parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1
    hq hqn hk

/-- A put of a key of one segment into the space root, a full leaf that the
transaction made, by a time split in place, keeps `PutInv` (the writer's tree
after it given). -/
theorem putInv_put_timeInPlace_root (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  apply writerWP_put_root_append c base hB.coherent cv h w n hroot hnl hrt hfull hI.ids.1
    hI.ids.2.1
  intro w4 h4t h4top _ _ hlk4 _ hW4
  refine writerWP_mono (writerWP_appendKlongs_timeInPlace 0 w.top.rootKey n cv w.next c base
    hB.coherent w4 hlk4 (by rw [h4t]; exact hrt) hfirst hfull hsplit) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, _, hN'⟩
  refine putInvT_leaf c base w w' hI cv w.next w.top.rootKey n l (Nat.le_refl _) hroot hnl
    (h't.trans h4t) (h'top.trans h4top) (by rw [hN']; simp) (by rw [hll]; exact hnl) hlt
    (live_of_lookup l n cv w.next (lookup_foldl_single l n cv w.next hlk))
    (fun x hx => by rw [hN']; simp only [hx, ↓reduceIte, hW4]) ?_
  exact fun q qn k1 hq hqn _ hk => absurd ⟨qn, hqn, by
      rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)] at hk; exact hk⟩
      (hI.tree.rootFree q k1 (reachS_tReach _ _ _ q hq))

/-! ## The time split below an inner parent -/

/-- A parent that gets a key klong (k1, y) of the compare value of its live
klong to L keeps the order at its other leaf children. -/
theorem leafOrderAt_parent_add (qn n' : KNode) (k1' k1 : Nat) (y L : NodeId) (t : Time)
    (hwf : klongsWf qn.ks = true) (ht : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hL : (k1, L) ∈ qn.live) (hold : LeafOrderAt qn k1' n') :
    LeafOrderAt (qn.add t (.key k1 y)) k1' n' := by
  intro c' z hz
  refine ⟨(hold c' z hz).1, ?_⟩
  intro c'' z'' hz'' hlt
  have ht' := KNode.add_times qn t (.key k1 y) (fun s h => by cases h) ht
  rw [← KNode.liveAt_of_times _ t ht'] at hz''
  rcases KNode.add_key_liveAt_mem qn t k1 y hwf ht c'' z'' hz'' with ⟨h1, _⟩ | ⟨_, h2⟩
  · subst h1; exact (hold c' z hz).2 c'' L hL hlt
  · rw [KNode.liveAt_of_times qn t ht] at h2
    exact (hold c' z hz).2 c'' z'' h2 hlt

/-- The new child of a parent's klong (k1, y): its live klongs are those of
the old child L under k1 and (cv, v), between the parent's bounds. -/
theorem leafOrderAt_parent_new (qn n l : KNode) (k1 cv : Nat) (y v : NodeId) (t : Time)
    (hwf : klongsWf qn.ks = true) (ht : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hold : LeafOrderAt qn k1 n)
    (hb : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'')
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live) :
    LeafOrderAt (qn.add t (.key k1 y)) k1 l := by
  intro c' z hz
  have hfirst : k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'' := by
    rcases hlive c' z hz with ⟨h1, _⟩ | h2
    · subst h1; exact hb
    · exact hold c' z h2
  refine ⟨hfirst.1, ?_⟩
  intro c'' z'' hz'' hlt
  have ht' := KNode.add_times qn t (.key k1 y) (fun s h => by cases h) ht
  rw [← KNode.liveAt_of_times _ t ht'] at hz''
  rcases KNode.add_key_liveAt_mem qn t k1 y hwf ht c'' z'' hz'' with ⟨h1, _⟩ | ⟨_, h2⟩
  · subst h1; omega
  · rw [KNode.liveAt_of_times qn t ht] at h2
    exact hfirst.2 c'' z'' h2 hlt

/-- The parts about the tree after a time split of a leaf L below its inner
parent q: q's klong k1 names a new node y holding L's live klongs and the
put's (cv, v); L keeps only klongs of earlier times and is reached no more. -/
theorem putInvT_timeSplit (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv k1 : Nat) (v y L q : NodeId) (n qn l : KNode) (hv : w.next ≤ v) (hy : w.next ≤ y)
    (hvy : v ≠ y)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hq : ReachS (wNode c.p base w) c.i w.top.rootKey q) (hk1 : (k1, L) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'L : wNode c.p base w' L = some (n.toPrev (c.i - 1)))
    (hN'q : wNode c.p base w' q = some (qn.add c.i (.key k1 y)))
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
  have hqwf := hI.wf q qn hqn
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
      -- a leaf child of q' after: not L, not q
      have hL'q : L' ≠ q := by
        intro he; subst he; rw [hN'q] at hn'; cases hn'
        rw [KNode.add_leaf, hql] at hnl'; cases hnl'
      by_cases hq'q : q' = q
      · subst hq'q
        rw [hN'q] at hq'n
        cases hq'n
        have ht' := KNode.add_times qn c.i (.key k1 y) (fun s h => by cases h) hqt
        rw [← KNode.liveAt_of_times _ c.i ht'] at hk'
        rcases KNode.add_key_liveAt_mem qn c.i k1 y hqwf hqt k1' L' hk' with ⟨h1, h2⟩ | ⟨hne, h2⟩
        · subst h1 h2
          rw [hN'y] at hn'
          cases hn'
          exact leafOrderAt_parent_new qn n l k1' cv L' v c.i hqwf hqt
            (hI.order q' qn L n k1' hq hqn hql hn hnl hk1) hpar hlive
        · have hL'L : L' ≠ L := by
            intro he; subst he; exact hne (honly q' qn k1' hq hqn h2).2
          have hL'y : L' ≠ y := by
            have := hI.links q' qn k1' L' hq hqn h2; omega
          rw [hother L' hL'L hL'q hL'y] at hn'
          rw [KNode.liveAt_of_times qn c.i hqt] at h2
          exact leafOrderAt_parent_add qn n' k1' k1 y L c.i hqwf hqt hk1
            (hI.order q' qn L' n' k1' hq hqn hql hn' hnl' h2)
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
before the transaction, below an inner segment root and an inner parent with
room, by a time split (also of a leaf full by its dead klongs only), keeps
`PutInv` (the writer's tree after it given). -/
theorem putInv_put_timeSplit_below (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (n.lastVersion c.i).size ≤ c.p.splitAbove)
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
    (fun L n hL hn hnl => (hleaf L n hL hn hnl).1)
  intro L n q qn k1 d' w4 hL hn hnl hqv hqn hql hk1 hqL h4t h4top h4next hlk4 hlq4 hsrc4 hW4
    hpq hpk
  obtain ⟨hfull, hfirst, hsplit⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hny : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_timeSplit d' L q n qn k1 cv w.next c w4 hlk4 hlq4
    hqL hql hfirst hfull hsplit hpq hpk hroomq (fun y => hdeadq k1 y) hny) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, h'nodes⟩
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hyt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
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
  refine putInvT_timeSplit c base w w' hI cv k1 w.next (w.next + 2) L q n qn l (Nat.le_refl _)
    (by omega) (by omega) hn hnl hqn hql hrq hk1l htk (h'top.trans h4top) ?_ ?_ ?_
    (by rw [hll]; exact hnl) hlt (live_of_lookup l n cv w.next hlk) ?_
    (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
  · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h'nodes]
  · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h'nodes, hqL, h4next]
  · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h'nodes, h4next, hLy.symm, hqy.symm,
      hl_eq]
  · intro x hxL hxq hxy
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, h4next, hxy, ↓reduceIte]

end SIS.Tree
