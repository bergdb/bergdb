/-
The split step's R1 for the one of l4f's 69 whose segment leaf q is the space root, not
made, and splits in space (`split.space3`; bergdb 030-01, R4's open part): p's whole split
with the heights' cache, then the merges' descent one height up finds p's copy
(`descendToHeight_topSeg_innerRoot`).
-/
import SIS.Tree.LiveRootInPlaceChildHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option linter.unusedSimpArgs false in
/-- The writer's space split of the space root x, which existed before the
transaction: the halves and a new space root over them at the next three ids;
x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_rootSpace_term_gh (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hxn : x < w.next) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) false) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w.next + 2 + 2 + 2 ≤ w'.next ∧
      (∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 → w'.gh.lookup z = w.gh.lookup z) ∧
      ∀ z, w'.nodes.lookup z =
        if z = x then some (n.toPrev (c.i - 1))
        else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else if z = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
          .key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 (w.next + 2)]⟩
        else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hx1 : x ≠ w.next := by omega
  have hx2 : x ≠ w.next + 2 := by omega
  have hx3 : x ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known x n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hx1, hx2, hx3, ↓reduceIte, hlk]
          rfl
        refine ⟨?_, ?_, ?_, ?_, ?_, fun z h1 h2 h3 => ?_, fun z => ?_⟩
        all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
        · have hb1 : (z == w.next) = false := by simpa using h1
          have hb2 : (z == w.next + 2) = false := by simpa using h2
          have hb3 : (z == w.next + 2 + 2) = false := by simpa using h3
          simp [List.lookup, hb1, hb2, hb3]
        simp only [lookup_upsert, List.lookup_append]
        by_cases hzx : z = x
        · subst hzx; simp
        · simp only [hzx, ↓reduceIte]
          by_cases h3 : z = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : z = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : z = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup z with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup z) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into the space root q, a leaf not made by the transaction, without
room, its last version over the split's bound: q's halves and a new inner space root over
them; the new root's search at k1 names the half on k1's side, a leaf whose search of k1
names y; the nodes but q and the three new ones kept. -/
theorem writerWP_appendKlongs_rootSpaceHoleGh (q : NodeId) (n : KNode) (k1 : Nat) (y : NodeId)
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hnl : n.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hnwf : klongsWf n.ks = true) (hntm : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hqn : q < w.next)
    (hsz : c.p.M < n.size + 2) (hsp : c.p.splitAbove < (n.lastVersion c.i).size)
    (h2 : 2 ≤ n.live.length) :
    WriterWP (appendKlongs 0 q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧
      (∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 → w'.gh.lookup z = w.gh.lookup z) ∧
      (∀ z, z ≠ q → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
        w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ (rn : KNode) (fr : Found) (z' : NodeId) (zn : KNode),
        rdN c w' w'.top.rootKey = some rn ∧ rn.leaf = false ∧
        rn.searchLte c.i k1 = some fr ∧ fr.y = z' ∧
        rdN c w' z' = some zn ∧ zn.leaf = true ∧
        ∃ fd', zn.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  obtain ⟨r, hr⟩ : ∃ r, (n.live.drop (n.live.length / 2)).head? = some r := by
    cases h : n.live.drop (n.live.length / 2) with
    | nil =>
      have := congrArg List.length h
      simp at this
      omega
    | cons e _ => exact ⟨e, rfl⟩
  have hQwf := KNode.add_key_wf n c.i k1 y hnwf
  have hQt := KNode.add_times n c.i (.key k1 y) (fun s h => by cases h) hntm
  have hQlook : ∀ cc, (n.add c.i (.key k1 y)).live.lookup cc =
      [(k1, y)].foldl (pairLookupStep cc) (n.live.lookup cc) := by
    intro cc
    rw [KNode.add_key_live_lookup_of_wf n c.i k1 cc y hnwf]
    simp [pairLookupStep]
  have hside : (∀ q ∈ [(k1, y)], r.1 ≤ q.1) ∨ (∀ q ∈ [(k1, y)], q.1 < r.1) := by
    by_cases h : r.1 ≤ k1
    · left; intro q hq; simp at hq; rw [hq]; exact h
    · right; intro q hq; simp at hq; rw [hq]; simp only; omega
  have hH := halves_leaf_searchEq_ins n (n.add c.i (.key k1 y)) c.i [(k1, y)] hnl r hr hside hQwf hQt hQlook
  simp only at hH
  obtain ⟨hsc, hfl, hsl, -, -, -, -, hfs, hss⟩ := hH
  have hQs : ((n.add c.i (.key k1 y)).searchEq c.i k1).map (·.y) = some y := by
    rw [KNode.searchEq_live _ c.i hQwf hQt k1, KNode.add_key_live_lookup_of_wf n c.i k1 k1 y hnwf]
    simp
  obtain ⟨e, he, her⟩ := divider_gt_first n r h2 hr
  have hsc0 : 0 < (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 := by rw [hsc]; omega
  -- the writer
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  have hgt : n.size + [(k1, y)].length + 1 > c.p.M := by simp; omega
  simp only [hgt, ↓reduceIte]
  refine writerWP_mono (writerWP_handleFullWith_rootSpace_term_gh _ q n [(k1, y)] c w hlk hfirst hsp hqn) ?_
  rintro _ w' ⟨ht, hroot, -, -, -, hgh, hlook⟩
  have hq1 : q ≠ w.next := by omega
  have hq2 : q ≠ w.next + 2 := by omega
  have hq3 : q ≠ w.next + 2 + 2 := by omega
  refine ⟨ht, hroot, hgh, fun z h1 h2 h3 h4 => by rw [hlook z]; simp [h1, h2, h3, h4], ?_⟩
  obtain ⟨fr, hfr, hfry⟩ := searchLte_twoRoot c.i w.next (w.next + 2)
    (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 k1 hsc0
  have hrR : rdN c w' w'.top.rootKey = some ⟨false, [.time c.i, .key 0 w.next,
      .key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2)]⟩ := by
    rw [hroot]; apply rdN_of_lookup; rw [hlook]
    have e1 : w.next + 2 + 2 ≠ w.next := by omega
    have e2 : w.next + 2 + 2 ≠ w.next + 2 := by omega
    simp only [Ne.symm hq3, e1, e2, ↓reduceIte]
  by_cases hsk : (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 ≤ k1
  · have hy2 := hss k1 (by rw [← hsc]; exact hsk)
    rw [hQs] at hy2
    obtain ⟨fd', h1, h2⟩ := Option.map_eq_some_iff.mp hy2
    refine ⟨_, fr, w.next + 2, _, hrR, rfl, hfr, by rw [hfry]; simp [hsk], ?_, hsl, fd', h1, h2⟩
    apply rdN_of_lookup; rw [hlook]
    have e1 : w.next + 2 ≠ w.next := by omega
    simp only [Ne.symm hq2, e1, ↓reduceIte]
  · have hy1 := hfs k1 (by rw [← hsc]; omega)
    rw [hQs] at hy1
    obtain ⟨fd', h1, h2⟩ := Option.map_eq_some_iff.mp hy1
    refine ⟨_, fr, w.next, _, hrR, rfl, hfr, by rw [hfry]; simp [hsk], ?_, hfl, fd', h1, h2⟩
    apply rdN_of_lookup; rw [hlook]
    simp only [Ne.symm hq1, ↓reduceIte]


set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth 1, inner, not made) split in time below the space root q (a
leaf, not made, without room, over the split's bound), which splits in space under a new
space root: its search at k1 names the half on k1's side, a leaf whose search of k1 names
p's copy (the next id), which holds p's last version and p's cached segment and height. -/
theorem writerWP_handleFull_rootSpaceChildHole (p q : NodeId) (pn qn last : KNode)
    (k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hpnl : pn.leaf = false) (hlq : w.nodes.lookup q = some qn)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqnl : qn.leaf = true) (hqfirst : qn.firstTime ≠ some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hpq' : p ≠ q)
    (hplt : p < w.next) (hqlt : q < w.next) (hny : w.nodes.lookup w.next = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 + 2 ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
        z ≠ w.next + 2 + 2 + 2 → w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ (rn : KNode) (fr : Found) (z' : NodeId) (zn : KNode),
        rdN c w' w'.top.rootKey = some rn ∧ rn.leaf = false ∧
        rn.searchLte c.i k1 = some fr ∧ fr.y = z' ∧
        rdN c w' z' = some zn ∧ zn.leaf = true ∧
        ∃ fd', zn.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
  have hpn : p ≠ w.next := by omega
  have hqn : q ≠ w.next := by omega
  unfold handleFull
  refine writerWP_handleFullWith_time_up_last_gh 0 p q pn qn k1 last compact c w hlk hlq hfirst
    hcs hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1p h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqn]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceHoleGh q qn k1 w.next c w1 hlq1 hqnl hqfirst hqwf
    hqtm (by rw [h1next]; omega) hsz hsp h2) ?_
  rintro _ w2 ⟨h2t, h2r, h2gh, h2rest, rn, fr, z', zn, hrr, hrl, hfr, hfry, hzr, hzl, hs1⟩
  have hlp2 : w2.nodes.lookup p = some pn := by
    rw [h2rest p hpq' (by rw [h1next]; omega) (by rw [h1next]; omega) (by rw [h1next]; omega), h1n,
      lookup_append_single_ne _ _ _ _ hpn]
    exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known p pn c w2 hlp2]
  rw [putNode, writerWP_modify]
  have hy3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup w.next = some ⟨pn.leaf, last.ks⟩ := by
    rw [lookup_upsert]
    simp only [Ne.symm hpn, ↓reduceIte]
    rw [h2rest w.next (Ne.symm hqn) (by rw [h1next]; omega) (by rw [h1next]; omega)
      (by rw [h1next]; omega), h1n]
    exact lookup_append_single_self _ _ _ hny
  have hzp : z' ≠ p := by
    intro he
    rw [he, rdN_of_lookup _ _ _ _ hlp2] at hzr
    cases hzr
    rw [hpnl] at hzl
    cases hzl
  have hroot : w2.top.rootKey = w.next + 2 + 2 + 2 := by rw [h2r, h1next]
  refine ⟨by rw [h2t, h1t], hroot, ?_, rdN_of_lookup _ _ _ _ hy3, ?_, rn, fr, z', zn, ?_, hrl, hfr, hfry,
    ?_, hzl, hs1⟩
  · intro z h1 h2 h3 h4 h5 h6
    show (upsert w2.nodes p _).lookup z = _
    rw [lookup_upsert]
    simp only [h1, ↓reduceIte]
    rw [h2rest z h2 (by rw [h1next]; exact h4) (by rw [h1next]; exact h5) (by rw [h1next]; exact h6), h1n,
      lookup_append_single_ne _ _ _ _ h3]
  · show rdG c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w.next = _
    unfold rdG
    simp only [hy3]
    show w2.gh.lookup w.next = _
    rw [h2gh _ (by rw [h1next]; omega) (by rw [h1next]; omega) (by rw [h1next]; omega), h1gh, hgh]
    simp [List.lookup]
  · rw [← hrr]
    show rdN c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w2.top.rootKey = _
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup w2.top.rootKey = _
    rw [lookup_upsert, hroot]
    have e : w.next + 2 + 2 + 2 ≠ p := by omega
    simp only [e, ↓reduceIte]
  · rw [← hzr]
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup z' = _
    rw [lookup_upsert]
    simp only [hzp, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- R1 after that split (`descendToHeight_topSeg_innerRoot`). -/
theorem writerWP_handleFull_rootSpaceChildHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W)
    (d : Nat) (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q : NodeId) (pnS qnS pn qn last : KNode) (k1 : Nat) (compact : Bool) (w : W)
    (hpkS : S1.path[d - 1]? = some (some k1, p)) (hpnS : rdN c S p = some pnS) (hplS : pnS.leaf = false)
    (hqS : (S1.path[d - 2]?).map (·.2) = some q) (hqnS : rdN c S q = some qnS) (hqlS : qnS.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hlk : w.nodes.lookup p = some pn) (hpnl : pn.leaf = false) (hlq : w.nodes.lookup q = some qn)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0]?).map (·.2) = some q) (hpk : w.path[0 + 1]? = some (some k1, p))
    (hqnl : qn.leaf = true) (hqfirst : qn.firstTime ≠ some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hpq' : p ≠ q)
    (hplt : p < w.next) (hqlt : q < w.next) (hny : w.nodes.lookup w.next = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (0 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_rootSpaceChildHole p q pn qn last k1 compact c w hlk hpnl hlq
    hfirst hcs hpq hpk hqnl hqfirst hqwf hqtm hpq' hplt hqlt hny hsz hsp h2) ?_
  rintro _ T ⟨-, -, -, hy, hgy, rn, fr, z', zn, hrr, hrl, hfr, hfry, hzr, hzl, hs1⟩
  obtain ⟨g', hg'⟩ := hghp
  exact descendToHeight_topSeg_innerRoot key g h c S S1 T d hS hd p q z' w.next pnS qnS rn zn k1 fr
    hpkS hpnS hplS hqS hqnS hqlS habove hrr hrl hfr hfry hzr hzl hs1 ⟨_, hy⟩ ⟨g', by rw [hgy]; exact hg'⟩

end SIS.Tree
