/-
The split step's R1 for the 6 of l4f's 69 whose segment leaf q, made, splits in space in
place below the space root q0, which splits in time (bergdb 030-01, R4's open part): p's
whole split with the heights' cache, then the merges' descent one height up finds p's copy
(`descendToHeight_topSeg_innerRoot`).
-/
import SIS.Tree.LiveSpaceRoomChildHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's space split in place of x, made by the transaction, below an
inner parent q: x keeps the first half, the second at the next id, then q gets
the klong to it (`appendKlongs d'`, whatever it does). -/
theorem writerWP_handleFullWith_spaceInPlace_up_gh (d' : Nat) (x q : NodeId) (n qn : KNode)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hxn : x < w.next)
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = x then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 → w1.vals = w.vals →
        (∀ z, z ≠ w.next → w1.gh.lookup z = w.gh.lookup z) →
        WriterWP (appendKlongs d' q [((halves n.leaf c.i (n.lastVersion c.i) ins).2.2, w.next)]) c w1
          (fun _ w2 => Q w2)) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hx2 : x ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_modify, writerWP_pure]
        refine writerWP_mono (hup _ ?_ rfl rfl rfl rfl rfl ?_) ?_
        · intro z
          simp only [lookup_upsert, List.lookup_append]
          by_cases hz1 : z = w.next
          · subst hz1; simp [Ne.symm hx2]
          · by_cases hzx : z = x
            · subst hzx; simp [hz1]
            · simp only [hz1, hzx, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hz1]; rfl
        · intro z hz
          have hb : (z == w.next) = false := by simpa using hz
          simp [List.lookup, hb]
        · intro _ w2 h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
          exact h

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into q (depth 1), a leaf the transaction made, without room, over
the split's bound, below the space root q0 (by kq), inner, not made, without room for the
second half's klong (or compacting) and within a split's bound when no room: q keeps the
first half, the second at the next id, q0's copy with its klong the new space root; the new
root's search at k1 names the half on k1's side, a leaf whose search of k1 names y. -/
theorem writerWP_appendKlongs_inPlaceSpaceRootHoleGh (q q0 : NodeId) (n q0n : KNode) (kq k1 : Nat)
    (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hlq0 : w.nodes.lookup q0 = some q0n)
    (hnl : n.leaf = true) (hmade : n.firstTime = some c.i)
    (hnwf : klongsWf n.ks = true) (hntm : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hqlt : q < w.next) (hq0lt : q0 < w.next) (hqq0 : q ≠ q0)
    (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hsz : c.p.M < n.size + 2) (hsp : c.p.splitAbove < (n.lastVersion c.i).size)
    (h2 : 2 ≤ n.live.length) (hrange : ∀ c' z, (c', z) ∈ n.live → kq ≤ c')
    (hpq : (w.path[0]?).map (·.2) = some q0)
    (hq0l : q0n.leaf = false) (hq0first : q0n.firstTime ≠ some c.i)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hq0full : q0n.size + 1 + 1 ≤ c.p.M → deadOver c.p ([((halves n.leaf c.i (n.lastVersion c.i)
      [(k1, y)]).2.2, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) q0n) = true)
    (hq0time : c.p.M < q0n.size + 1 + 1 → (q0n.lastVersion c.i).size ≤ c.p.splitAbove)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) (hfdy : fd.y = q) :
    WriterWP (appendKlongs 1 q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 ∧
      (∀ z, z ≠ w.next → z ≠ w.next + 2 → w'.gh.lookup z = w.gh.lookup z) ∧
      (∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → z ≠ w.next + 2 → w'.nodes.lookup z = w.nodes.lookup z) ∧
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
  have hkqsc : kq < (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 := by
    rw [hsc]; have := hrange e.1 e.2 he; omega
  have hq0n1 : q0 ≠ w.next := by omega
  have hq0n2 : q0 ≠ w.next + 2 := by omega
  have hqn1 : q ≠ w.next := by omega
  have hqn2 : q ≠ w.next + 2 := by omega
  -- the writer
  show WriterWP (appendKlongs (0 + 1) q [(k1, y)]) c w _
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  have hgt : n.size + [(k1, y)].length + 1 > c.p.M := by simp; omega
  simp only [hgt, ↓reduceIte]
  refine writerWP_handleFullWith_spaceInPlace_up_gh 0 q q0 n q0n [(k1, y)] c w hlk hlq0 hq0l hmade hsp
    hpq hqlt _ ?_
  intro w1 h1n h1t h1top h1p h1next h1v h1gh
  have hlq01 : w1.nodes.lookup q0 = some q0n := by
    rw [h1n q0]; simp only [Ne.symm hqq0, hq0n1, ↓reduceIte]; exact hlq0
  have hny1 : w1.nodes.lookup w1.next = none := by
    rw [h1next, h1n]
    have e1 : w.next + 2 ≠ q := by omega
    have e2 : w.next + 2 ≠ w.next := by omega
    simp only [e1, e2, ↓reduceIte]; exact hny2
  refine writerWP_mono (writerWP_appendKlongs_rootTimeGh q0 q0n _ c w1 hlq01 hq0first
    (by rw [h1next]; omega) hny1 (fun h => hq0full (by simpa using h))
    (fun h => hq0time (by simpa using h))) ?_
  rintro _ w2 ⟨h2t, h2r, h2gh, out, ho1, -, ho3, ho4, h2n⟩
  have hroot : w2.top.rootKey = w.next + 2 := by rw [h2r, h1next]
  have hfin : ∀ z, z ≠ q0 → z ≠ w.next + 2 → w2.nodes.lookup z = w1.nodes.lookup z := by
    intro z h1 h2
    rw [h2n z, h1next]
    simp only [h1, h2, ↓reduceIte]
  refine ⟨by rw [h2t, h1t], hroot, fun z h1 h2 => by
    rw [h2gh z (by rw [h1next]; exact h2), h1gh z h1], fun z h1 h2 h3 h4 => by
    rw [hfin z h2 h4, h1n z]; simp only [h1, h3, ↓reduceIte], ?_⟩
  have hq : (⟨q0n.leaf, out.ks⟩ : KNode) = out := by rw [← ho1]
  have hrR : rdN c w2 w2.top.rootKey = some out := by
    rw [hroot]; apply rdN_of_lookup
    rw [h2n, h1next]
    simp only [Ne.symm hq0n2, ↓reduceIte, hq]
  have hlk' : ∀ cc, out.live.lookup cc =
      if (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 == cc then some w.next
      else q0n.live.lookup cc := by
    intro cc; rw [ho4 cc]; simp [pairLookupStep]
  obtain ⟨fr, hfr, hfry⟩ := searchLte_lookup_addNew q0n out c.i k1 kq _ w.next fd hq0tm ho3 hlk' hfd hfdc
    hkqsc
  by_cases hsk : (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 ≤ k1
  · have hy2 := hss k1 (by rw [← hsc]; exact hsk)
    rw [hQs] at hy2
    obtain ⟨fd', e1, e2⟩ := Option.map_eq_some_iff.mp hy2
    refine ⟨out, fr, w.next, _, hrR, by rw [ho1]; exact hq0l, hfr, by rw [hfry]; simp [hsk], ?_, hsl,
      fd', e1, e2⟩
    apply rdN_of_lookup
    rw [hfin _ (Ne.symm hq0n1) (by omega), h1n]
    simp only [Ne.symm hqn1, ↓reduceIte]
  · have hy1 := hfs k1 (by rw [← hsc]; omega)
    rw [hQs] at hy1
    obtain ⟨fd', e1, e2⟩ := Option.map_eq_some_iff.mp hy1
    refine ⟨out, fr, q, _, hrR, by rw [ho1]; exact hq0l, hfr, by rw [hfry]; simp [hsk, hfdy], ?_,
      hfl, fd', e1, e2⟩
    apply rdN_of_lookup
    rw [hfin _ hqq0 hqn2, h1n]
    simp only [↓reduceIte]


set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth 2, inner, not made), split in time below its segment leaf q
(depth 1, made, without room, over the split's bound), which splits in space in place below
the space root q0 (not made, without room for the second half's klong or compacting), which
splits in time: the new space root's search at k1 names the half on k1's side, a leaf whose
search of k1 names p's copy (the next id), which holds p's last version and p's cached
segment and height. -/
theorem writerWP_handleFull_inPlaceSpaceChildHole (p q q0 : NodeId) (pn qn q0n last : KNode)
    (kq k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hpnl : pn.leaf = false) (hlq : w.nodes.lookup q = some qn)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0 + 1]?).map (·.2) = some q) (hpk : w.path[0 + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[0]?).map (·.2) = some q0)
    (hqnl : qn.leaf = true) (hqmade : qn.firstTime = some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny4 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length) (hrange : ∀ c' z, (c', z) ∈ qn.live → kq ≤ c')
    (hq0l : q0n.leaf = false) (hq0first : q0n.firstTime ≠ some c.i)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hq0full : q0n.size + 1 + 1 ≤ c.p.M → deadOver c.p ([((halves qn.leaf c.i (qn.lastVersion c.i)
      [(k1, w.next)]).2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) q0n) = true)
    (hq0time : c.p.M < q0n.size + 1 + 1 → (q0n.lastVersion c.i).size ≤ c.p.splitAbove)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) (hfdy : fd.y = q) :
    WriterWP (handleFull (0 + 1 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ q0 → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
        w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ (rn : KNode) (fr : Found) (z' : NodeId) (zn : KNode),
        rdN c w' w'.top.rootKey = some rn ∧ rn.leaf = false ∧
        rn.searchLte c.i k1 = some fr ∧ fr.y = z' ∧
        rdN c w' z' = some zn ∧ zn.leaf = true ∧
        ∃ fd', zn.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
  have hpn : p ≠ w.next := by omega
  have hqn : q ≠ w.next := by omega
  have hq0n : q0 ≠ w.next := by omega
  unfold handleFull
  refine writerWP_handleFullWith_time_up_last_gh (0 + 1) p q pn qn k1 last compact c w hlk hlq hfirst
    hcs hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1p h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqn]; exact hlq
  have hlq01 : w1.nodes.lookup q0 = some q0n := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hq0n]; exact hlq0
  have hny21 : w1.nodes.lookup (w1.next + 2) = none := by
    rw [h1next, h1n, lookup_append_single_ne _ _ _ _ (by omega)]; exact hny4
  refine writerWP_mono (writerWP_appendKlongs_inPlaceSpaceRootHoleGh q q0 qn q0n kq k1 w.next c w1 hlq1
    hlq01 hqnl hqmade hqwf hqtm (by rw [h1next]; omega) (by rw [h1next]; omega) hqq0 hny21 hsz hsp h2
    hrange (by rw [h1p]; exact hpq0) hq0l hq0first hq0tm (by rw [h1next]; exact hq0full) hq0time fd hfd
    hfdc hfdy) ?_
  rintro _ w2 ⟨h2t, h2r, h2gh, h2rest, rn, fr, z', zn, hrr, hrl, hfr, hfry, hzr, hzl, hs1⟩
  have hlp2 : w2.nodes.lookup p = some pn := by
    rw [h2rest p hpq' hpq0' (by rw [h1next]; omega) (by rw [h1next]; omega), h1n,
      lookup_append_single_ne _ _ _ _ hpn]
    exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known p pn c w2 hlp2]
  rw [putNode, writerWP_modify]
  have hy3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup w.next = some ⟨pn.leaf, last.ks⟩ := by
    rw [lookup_upsert]
    simp only [Ne.symm hpn, ↓reduceIte]
    rw [h2rest w.next (Ne.symm hqn) (Ne.symm hq0n) (by rw [h1next]; omega) (by rw [h1next]; omega), h1n]
    exact lookup_append_single_self _ _ _ hny
  have hzp : z' ≠ p := by
    intro he
    rw [he, rdN_of_lookup _ _ _ _ hlp2] at hzr
    cases hzr
    rw [hpnl] at hzl
    cases hzl
  have hroot : w2.top.rootKey = w.next + 2 + 2 := by rw [h2r, h1next]
  refine ⟨by rw [h2t, h1t], hroot, ?_, rdN_of_lookup _ _ _ _ hy3, ?_, rn, fr, z', zn, ?_, hrl, hfr, hfry,
    ?_, hzl, hs1⟩
  · intro z h1 h2 h3 h4 h5 h6
    show (upsert w2.nodes p _).lookup z = _
    rw [lookup_upsert]
    simp only [h1, ↓reduceIte]
    rw [h2rest z h2 h3 (by rw [h1next]; exact h5) (by rw [h1next]; exact h6), h1n,
      lookup_append_single_ne _ _ _ _ h4]
  · show rdG c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w.next = _
    unfold rdG
    simp only [hy3]
    show w2.gh.lookup w.next = _
    rw [h2gh _ (by rw [h1next]; omega) (by rw [h1next]; omega), h1gh, hgh]
    simp [List.lookup]
  · rw [← hrr]
    show rdN c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w2.top.rootKey = _
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup w2.top.rootKey = _
    rw [lookup_upsert, hroot]
    have e : w.next + 2 + 2 ≠ p := by omega
    simp only [e, ↓reduceIte]
  · rw [← hzr]
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup z' = _
    rw [lookup_upsert]
    simp only [hzp, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- R1 after that split (`descendToHeight_topSeg_innerRoot`; every node above q inner at S). -/
theorem writerWP_handleFull_inPlaceSpaceChildHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W)
    (d : Nat) (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q q0 : NodeId) (pnS qnS pn qn q0n last : KNode)
    (kq k1 : Nat) (compact : Bool) (w : W)
    (hpkS : S1.path[d - 1]? = some (some k1, p)) (hpnS : rdN c S p = some pnS) (hplS : pnS.leaf = false)
    (hqS : (S1.path[d - 2]?).map (·.2) = some q) (hqnS : rdN c S q = some qnS) (hqlS : qnS.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hlk : w.nodes.lookup p = some pn) (hpnl : pn.leaf = false) (hlq : w.nodes.lookup q = some qn)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[0 + 1]?).map (·.2) = some q) (hpk : w.path[0 + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[0]?).map (·.2) = some q0)
    (hqnl : qn.leaf = true) (hqmade : qn.firstTime = some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny4 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length) (hrange : ∀ c' z, (c', z) ∈ qn.live → kq ≤ c')
    (hq0l : q0n.leaf = false) (hq0first : q0n.firstTime ≠ some c.i)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hq0full : q0n.size + 1 + 1 ≤ c.p.M → deadOver c.p ([((halves qn.leaf c.i (qn.lastVersion c.i)
      [(k1, w.next)]).2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) q0n) = true)
    (hq0time : c.p.M < q0n.size + 1 + 1 → (q0n.lastVersion c.i).size ≤ c.p.splitAbove)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) (hfdy : fd.y = q)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (0 + 1 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_inPlaceSpaceChildHole p q q0 pn qn q0n last kq k1 compact c w
    hlk hpnl hlq hlq0 hfirst hcs hpq hpk hpq0 hqnl hqmade hqwf hqtm hpq' hpq0' hqq0 hplt hqlt hq0lt hny
    hny4 hsz hsp h2 hrange hq0l hq0first hq0tm hq0full hq0time fd hfd hfdc hfdy) ?_
  rintro _ T ⟨-, -, -, hy, hgy, rn, fr, z', zn, hrr, hrl, hfr, hfry, hzr, hzl, hs1⟩
  obtain ⟨g', hg'⟩ := hghp
  exact descendToHeight_topSeg_innerRoot key g h c S S1 T d hS hd p q z' w.next pnS qnS rn zn k1 fr
    hpkS hpnS hplS hqS hqnS hqlS habove hrr hrl hfr hfry hzr hzl hs1 ⟨_, hy⟩ ⟨g', by rw [hgy]; exact hg'⟩

end SIS.Tree
