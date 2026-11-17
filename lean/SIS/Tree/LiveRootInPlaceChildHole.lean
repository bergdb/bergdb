/-
The split step's R1 for the one of l4f's 69 whose segment leaf q, made by the transaction,
is the space root and splits in time in place (bergdb 030-01, R4's open part): p's whole
split with the heights' cache, then the merges' descent one height up finds p's copy
(`descendToHeight_topSeg_leafRoot`, the space root kept).
-/
import SIS.Tree.LiveInPlaceSpaceChildHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's time split in place of the space root x, made by the
transaction: x holds its last version with ins. -/
theorem writerWP_handleFullWith_timeInPlace_term0N_gh (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩ ∧ w'.gh = w.gh) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew, parentAt, writerWP_bind, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true]
  cases compact with
  | true =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  | false =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-! ## The shapes of a cascade's nodes -/

/-- The same at the space root q (depth 0), made by the transaction. -/
theorem writerWP_appendKlongs_rootInPlaceHoleGh (q : NodeId) (n : KNode)
    (k1 : Nat) (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hfirst : n.firstTime = some c.i)
    (hfull : n.size + 2 ≤ c.p.M → deadOver c.p (n.add c.i (.key k1 y)) = true)
    (htime : c.p.M < n.size + 2 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs 0 q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧ w'.gh = w.gh ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  have hsplit : ∀ compact : Bool,
      (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 q
        [(k1, y)] (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧ w'.gh = w.gh ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
    intro compact hcs
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0N_gh _ q n [(k1, y)]
      compact c w hlk hfirst hcs) ?_
    rintro _ w' ⟨l, hl1, hl2, hl3, hl4, -, ht, htop, -, -, hp, hn, hgh⟩
    exact ⟨ht, htop, hp, hgh, inPlaceHole_post c w w' q n k1 y l hl1 hl2 hl3 hl4 hn⟩
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + [(k1, y)].length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime (by simpa using hsz)
    exact hsplit false
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
  · have hd := hfull (by simp at hsz; omega)
    simp only [List.foldl_cons, List.foldl_nil] at hsz ⊢
    simp only [hsz, hd, ↓reduceIte]
    exact hsplit true (by simp)

set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth 1, not made) split in time below the space root q (made,
without room or compacting, within a split's bound when no room), which splits in time in
place: q's node is a leaf whose search of k1 names p's copy (the next id), which holds p's
last version and p's cached segment and height; the rest kept but p, q and the copy. -/
theorem writerWP_handleFull_rootInPlaceChildHole (p q : NodeId) (pn qn last : KNode)
    (k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqmade : qn.firstTime = some c.i) (hpq' : p ≠ q)
    (hplt : p < w.next) (hqlt : q < w.next) (hny : w.nodes.lookup w.next = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = qn.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
  have hpn : p ≠ w.next := by omega
  have hqn : q ≠ w.next := by omega
  unfold handleFull
  refine writerWP_handleFullWith_time_up_last_gh 0 p q pn qn k1 last compact c w hlk hlq hfirst
    hcs hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1p h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqn]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_rootInPlaceHoleGh q qn k1 w.next c w1 hlq1 hqmade hqfull
    hqtime) ?_
  rintro _ w2 ⟨h2t, h2top, h2p, h2gh, h2rest, qn', hq2, hql', hfd'⟩
  have hlp2 : w2.nodes.lookup p = some pn := by
    rw [h2rest p hpq', h1n, lookup_append_single_ne _ _ _ _ hpn]
    exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known p pn c w2 hlp2]
  rw [putNode, writerWP_modify]
  have hy3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup w.next = some ⟨pn.leaf, last.ks⟩ := by
    rw [lookup_upsert]
    simp only [Ne.symm hpn, ↓reduceIte]
    rw [h2rest w.next (Ne.symm hqn), h1n]
    exact lookup_append_single_self _ _ _ hny
  refine ⟨by rw [h2t, h1t], by rw [h2top, h1top], ?_, rdN_of_lookup _ _ _ _ hy3, ?_, qn', ?_, hql', hfd'⟩
  · intro z h1 h2 h3
    show (upsert w2.nodes p _).lookup z = _
    rw [lookup_upsert]
    simp only [h1, ↓reduceIte]
    rw [h2rest z h2, h1n, lookup_append_single_ne _ _ _ _ h3]
  · show rdG c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w.next = _
    unfold rdG
    simp only [hy3]
    show w2.gh.lookup w.next = _
    rw [h2gh, h1gh, hgh]
    simp [List.lookup]
  · rw [← hq2]
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup q = _
    rw [lookup_upsert]
    simp only [Ne.symm hpq', ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- R1 after that split (`descendToHeight_topSeg_leafRoot`, q the space root kept). -/
theorem writerWP_handleFull_rootInPlaceChildHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W)
    (d : Nat) (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q : NodeId) (pnS qnS pn qn last : KNode) (k1 : Nat) (compact : Bool) (w : W)
    (hpkS : S1.path[d - 1]? = some (some k1, p)) (hpnS : rdN c S p = some pnS) (hplS : pnS.leaf = false)
    (hqS : (S1.path[d - 2]?).map (·.2) = some q) (hqnS : rdN c S q = some qnS) (hqlS : qnS.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hR0 : w.top.rootKey = q)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn) (hqnl : qn.leaf = true)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqmade : qn.firstTime = some c.i) (hpq' : p ≠ q)
    (hplt : p < w.next) (hqlt : q < w.next) (hny : w.nodes.lookup w.next = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_rootInPlaceChildHole p q pn qn last k1 compact c w hlk hlq
    hfirst hcs hpq hpk hqmade hpq' hplt hqlt hny hqfull hqtime) ?_
  rintro _ T ⟨-, htop, -, hy, hgy, qn', hqr, hql', hs1⟩
  obtain ⟨g', hg'⟩ := hghp
  have hTr : T.top.rootKey = q := by rw [htop, hR0]
  exact descendToHeight_topSeg_leafRoot key g h c S S1 T d hS hd p q w.next pnS qnS qn' k1 hpkS hpnS
    hplS hqS hqnS hqlS habove (by rw [hTr]; exact hqr) (by rw [hql']; exact hqnl) hs1 ⟨_, hy⟩
    ⟨g', by rw [hgy]; exact hg'⟩

end SIS.Tree
