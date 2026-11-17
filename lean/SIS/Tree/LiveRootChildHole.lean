/-
The space root's time split with p's copy put, with the heights' cache (bergdb 030-01, R4's
open part, the 25 of l4f's 69 at the space root): `writerWP_appendKlongs_rootTime` keeping the
cache but at the new root, and the whole split of the merge's parent p (depth 1, not made,
split in time) below the space root q (a leaf, not made, without room): after it the new
space root is a leaf whose search of p's klong names p's copy, the copy holds p's last
version and p's cached segment and height (what `descendToHeight_topSeg_leafRoot` takes).
-/
import SIS.Tree.LiveInPlaceSpaceHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- The time split of the space root L, not made by the transaction, with klongs ins to
put and its last version: the next id holds the last version with ins (`out`), the new
space root; L its klongs before the transaction; the rest kept. -/
theorem writerWP_handleFullWith_rootTimeSplit_insGh (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧
      (∀ z, z ≠ w.next → w'.gh.lookup z = w.gh.lookup z) ∧ ∃ out : KNode,
        out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, out.ks⟩ else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w1 ⟨hw1, hl1, hl2, hl3, hl4, -⟩
    subst w1
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨rfl, rfl, fun z hz => ?_, l, hl1, hl2, hl3, hl4, ?_⟩
          · have hb : (z == w.next) = false := by simp [hz]
            simp [List.lookup, hb]
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

/-- `appendKlongs` at the space root L (depth 0), not made by the transaction, without room
for ins or compacting, with its last version within a split's bound when it has no room:
the time split of `writerWP_handleFullWith_rootTimeSplit_ins`. -/
theorem writerWP_appendKlongs_rootTimeGh (L : NodeId) (n : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none)
    (hfull : n.size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = true)
    (htime : c.p.M < n.size + ins.length + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs 0 L ins) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧
      (∀ z, z ≠ w.next → w'.gh.lookup z = w.gh.lookup z) ∧ ∃ out : KNode,
        out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, out.ks⟩ else w.nodes.lookup x) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + ins.length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime hsz
    exact writerWP_handleFullWith_rootTimeSplit_insGh _ L n ins false c w hlk hfirst
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
      hLn hny
  · have hd := hfull (by omega)
    simp only [hsz, hd, ↓reduceIte]
    exact writerWP_handleFullWith_rootTimeSplit_insGh _ L n ins true c w hlk hfirst
      (by simp) hLn hny

set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth 1), not made by the transaction, split in time with its last
version `last` below the space root q (a leaf of the first segment, not made), which gets
p's copy by p's klong k1 without room (or compacting), within a split's bound when no room,
and splits in time: the new space root is a leaf whose search of k1 names p's copy (the
next id), the copy holds `last` and p's cached segment and height; the rest kept but p, q
and the two new nodes. -/
theorem writerWP_handleFull_rootChildTimeHole (p q : NodeId) (pn qn last : KNode) (k1 : Nat)
    (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqfirst : qn.firstTime ≠ some c.i) (hpq' : p ≠ q)
    (hqlt : q < w.next) (hplt : p < w.next) (hny : w.nodes.lookup w.next = none)
    (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ w.next → z ≠ w.next + 2 → w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ qn', rdN c w' w'.top.rootKey = some qn' ∧ qn'.leaf = qn.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
  have hqn : q ≠ w.next := by omega
  have hpn : p ≠ w.next := by omega
  unfold handleFull
  refine writerWP_handleFullWith_time_up_last_gh 0 p q pn qn k1 last compact c w hlk hlq hfirst hcs
    hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1p h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqn]; exact hlq
  have hny1 : w1.nodes.lookup w1.next = none := by
    rw [h1next, h1n, lookup_append_single_ne _ _ _ _ (by omega)]; exact hny2
  refine writerWP_mono (writerWP_appendKlongs_rootTimeGh q qn [(k1, w.next)] c w1 hlq1 hqfirst
    (by rw [h1next]; omega) hny1 (fun h => hqfull (by simpa using h))
    (fun h => hqtime (by simpa using h))) ?_
  rintro _ w2 ⟨h2t, h2r, h2gh, out, ho1, ho2, ho3, ho4, h2n⟩
  have hlp2 : w2.nodes.lookup p = some pn := by
    rw [h2n p, h1next, h1n, lookup_append_single_ne _ _ _ _ hpn]
    have e : p ≠ w.next + 2 := by omega
    simp only [hpq', e, ↓reduceIte]; exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known p pn c w2 hlp2]
  rw [putNode, writerWP_modify]
  have hy3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup w.next = some ⟨pn.leaf, last.ks⟩ := by
    rw [lookup_upsert, h2n, h1next, h1n]
    have e : w.next ≠ w.next + 2 := by omega
    simp only [Ne.symm hpn, Ne.symm hqn, e, ↓reduceIte]
    exact lookup_append_single_self _ _ _ hny
  have hq : (⟨qn.leaf, out.ks⟩ : KNode) = out := by rw [← ho1]
  have hr3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup (w.next + 2) = some out := by
    rw [lookup_upsert, h2n, h1next]
    have e : w.next + 2 ≠ p := by omega
    have e2 : w.next + 2 ≠ q := by omega
    simp only [e, e2, ↓reduceIte, hq]
  refine ⟨by rw [h2t, h1t], by rw [h2r, h1next], ?_, rdN_of_lookup _ _ _ _ hy3, ?_, out, ?_, ho1, ?_⟩
  · intro z h1 h2 h3 h4
    show (upsert w2.nodes p _).lookup z = _
    rw [lookup_upsert, h2n, h1next, h1n, lookup_append_single_ne _ _ _ _ h3]
    simp only [h1, h2, h4, ↓reduceIte]
  · show rdG c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w.next = _
    unfold rdG
    simp only [hy3]
    show w2.gh.lookup w.next = _
    rw [h2gh _ (by rw [h1next]; omega), h1gh, hgh]
    simp [List.lookup]
  · show rdN c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w2.top.rootKey = some out
    rw [h2r, h1next]
    exact rdN_of_lookup _ _ _ _ hr3
  · have hs := KNode.searchEq_live out c.i ho2 ho3 k1
    rw [ho4 k1] at hs
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep, beq_self_eq_true, ↓reduceIte] at hs
    obtain ⟨fd', hfd', hfy⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨fd', hfd', hfy⟩

set_option maxHeartbeats 4000000 in
/-- R1 after that split: the merges' descent one height up finds p's copy, from the
descent at (g, h) on a state S that found the merged node below p (at depth 1), p below the
space root q (a segment leaf): `descendToHeight_topSeg_leafRoot` with
`writerWP_handleFull_rootChildTimeHole`, p's cached height h + 1. -/
theorem writerWP_handleFull_rootChildTimeHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q : NodeId) (pnS qnS pn qn last : KNode) (k1 : Nat) (compact : Bool) (w : W)
    (hpkS : S1.path[d - 1]? = some (some k1, p)) (hpnS : rdN c S p = some pnS) (hplS : pnS.leaf = false)
    (hqS : (S1.path[d - 2]?).map (·.2) = some q) (hqnS : rdN c S q = some qnS) (hqlS : qnS.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn) (hqnl : qn.leaf = true)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqfirst : qn.firstTime ≠ some c.i) (hpq' : p ≠ q)
    (hqlt : q < w.next) (hplt : p < w.next) (hny : w.nodes.lookup w.next = none)
    (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_rootChildTimeHole p q pn qn last k1 compact c w hlk hlq
    hfirst hcs hpq hpk hqfirst hpq' hqlt hplt hny hny2 hqfull hqtime) ?_
  rintro _ T ⟨-, -, -, hy, hgy, qn', hr, hl, hfd⟩
  obtain ⟨g', hg'⟩ := hghp
  exact descendToHeight_topSeg_leafRoot key g h c S S1 T d hS hd p q w.next pnS qnS qn' k1 hpkS hpnS
    hplS hqS hqnS hqlS habove hr (by rw [hl]; exact hqnl) hfd ⟨_, hy⟩ ⟨g', by rw [hgy]; exact hg'⟩

end SIS.Tree
