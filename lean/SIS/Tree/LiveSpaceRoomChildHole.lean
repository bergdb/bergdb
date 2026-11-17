/-
The split step's R1 for the 15 of l4f's 69 whose segment leaf q, not made, splits in space
below an inner q0 with room (bergdb 030-01, R4's open part): p's whole split with the
heights' cache, then the merges' descent one height up finds p's copy
(`descendToHeight_redirectSeg2`, q's half for q').
-/
import SIS.Tree.LiveInPlaceChildHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's space split of x, which existed before the transaction, with
klongs ins, below an inner parent q: the halves at the next two ids, then q
gets the klongs to them (`appendKlongs d'`, whatever it does), then x keeps
its klongs before the transaction; the cache but at the halves kept. -/
theorem writerWP_handleFullWith_space_up_gh (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 → w1.vals = w.vals →
        (∀ z, z ≠ w.next → z ≠ w.next + 2 → w1.gh.lookup z = w.gh.lookup z) →
        WriterWP (appendKlongs d' q [(k1, w.next),
          ((halves n.leaf c.i (n.lastVersion c.i) ins).2.2, w.next + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
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
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (hup _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      rotate_left 7
      · intro _ w2 h
        simpa only [writerWP_bind, putNode, writerWP_modify] using h
      · intro z
        simp only [lookup_upsert, List.lookup_append]
        by_cases hz2 : z = w.next + 2
        · have hz1 : z ≠ w.next := by omega
          simp [hz2]
        · simp only [hz2, ↓reduceIte]
          by_cases hz1 : z = w.next
          · simp [hz1]
          · simp only [hz1, ↓reduceIte]
            cases h : w.nodes.lookup z with
            | some m => rfl
            | none =>
              have hb1 : (z == w.next) = false := by simpa using hz1
              have hb2 : (z == w.next + 2) = false := by simpa using hz2
              simp [List.lookup, hb1, hb2]
      all_goals first
        | rfl
        | (intro z h1 h2
           have hb1 : (z == w.next) = false := by simpa using h1
           have hb2 : (z == w.next + 2) = false := by simpa using h2
           simp [List.lookup, hb1, hb2]))

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into q (depth d'' + 1), a leaf not made by the transaction,
without room, its last version over the split's bound: q splits in space, its halves at
the next two ids, named by q0 (inner, with room for two klongs) by q's klong kq and the
divider; q0's search at k1 (where it named q) names the half on k1's side, a leaf whose
search of k1 names y; the nodes but q, q0 and the halves kept. -/
theorem writerWP_appendKlongs_spaceRoomHoleGh (d'' : Nat) (q q0 : NodeId) (n q0n : KNode)
    (kq k1 : Nat) (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hlq0 : w.nodes.lookup q0 = some q0n)
    (hnl : n.leaf = true) (hfirst : n.firstTime ≠ some c.i) (hnwf : klongsWf n.ks = true)
    (hntm : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hqq0 : q ≠ q0)
    (hsz : c.p.M < n.size + 2) (hsp : c.p.splitAbove < (n.lastVersion c.i).size)
    (h2 : 2 ≤ n.live.length) (hrange : ∀ c' z, (c', z) ∈ n.live → kq ≤ c')
    (hpq : (w.path[d'']?).map (·.2) = some q0) (hpk : w.path[d'' + 1]? = some (some kq, q))
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hroom : q0n.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((q0n.add c.i (.key kq w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2))) = false)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) :
    WriterWP (appendKlongs (d'' + 1) q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ w.next → z ≠ w.next + 2 → w'.gh.lookup z = w.gh.lookup z) ∧
      (∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → z ≠ w.next + 2 → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ (q0n' : KNode) (z' : NodeId) (zn : KNode), rdN c w' q0 = some q0n' ∧ q0n'.leaf = false ∧
        (∃ fd0, q0n'.searchLte c.i k1 = some fd0 ∧ fd0.y = z') ∧
        (z' = w.next ∨ z' = w.next + 2) ∧
        rdN c w' z' = some zn ∧ zn.leaf = true ∧
        ∃ fd', zn.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  -- the halves' facts
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
  have hq0n1 : q0 ≠ w.next := by intro he; rw [he, hny] at hlq0; cases hlq0
  have hq0n2 : q0 ≠ w.next + 2 := by intro he; rw [he, hny2] at hlq0; cases hlq0
  have hqn1 : q ≠ w.next := by intro he; rw [he, hny] at hlk; cases hlk
  have hqn2 : q ≠ w.next + 2 := by intro he; rw [he, hny2] at hlk; cases hlk
  -- the writer
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  have hgt : n.size + [(k1, y)].length + 1 > c.p.M := by simp; omega
  simp only [hgt, ↓reduceIte]
  refine writerWP_handleFullWith_space_up_gh d'' q q0 n q0n kq [(k1, y)] c w hlk hlq0 hq0l hfirst hsp
    hpq hpk _ ?_
  intro w1 h1n h1t h1top h1p h1next h1v h1gh
  have hlq01 : w1.nodes.lookup q0 = some q0n := by
    rw [h1n q0]; simp only [hq0n1, hq0n2, ↓reduceIte]; exact hlq0
  refine writerWP_mono (writerWP_appendKlongs_room2 d'' q0 q0n kq _ w.next (w.next + 2) c w1 hlq01
    hroom hdead) ?_
  rintro _ w2 rfl
  have hlq2 : (upsert w1.nodes q0 ((q0n.add c.i (.key kq w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2)))).lookup q = some n := by
    rw [lookup_upsert, h1n q]
    simp only [hqq0, hqn1, hqn2, ↓reduceIte]
    exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known q n c _ hlq2]
  rw [putNode, writerWP_modify]
  have hfin : ∀ z, z ≠ q → z ≠ q0 →
      (upsert (upsert w1.nodes q0 ((q0n.add c.i (.key kq w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2)))) q
        (n.toPrev (c.i - 1))).lookup z = w1.nodes.lookup z := by
    intro z h1 h2
    rw [lookup_upsert, lookup_upsert]
    simp only [h1, h2, ↓reduceIte]
  have hfinq0 : (upsert (upsert w1.nodes q0 ((q0n.add c.i (.key kq w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2)))) q
        (n.toPrev (c.i - 1))).lookup q0 = some ((q0n.add c.i (.key kq w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2))) := by
    rw [lookup_upsert, lookup_upsert]
    simp only [Ne.symm hqq0, ↓reduceIte]
  refine ⟨h1t, h1top, h1p, h1gh, ?_, ?_⟩
  · intro z hzq hzq0 hzn hzn2
    show (upsert (upsert w1.nodes q0 _) q _).lookup z = _
    rw [hfin z hzq hzq0, h1n z]
    simp only [hzn, hzn2, ↓reduceIte]
  · obtain ⟨fd0, hfd0, hfy0⟩ := searchLte_add_two q0n c.i k1 kq _ w.next (w.next + 2) fd hq0wf hq0tm hfd
      hfdc hkqsc
    have hq0l' : ((q0n.add c.i (.key kq w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 (w.next + 2))).leaf = false := by
      rw [KNode.add_leaf, KNode.add_leaf]; exact hq0l
    by_cases hsk : (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.2 ≤ k1
    · have hy2 := hss k1 (by rw [← hsc]; exact hsk)
      rw [hQs] at hy2
      obtain ⟨fd', h1, h2⟩ := Option.map_eq_some_iff.mp hy2
      refine ⟨_, w.next + 2, (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).2.1,
        rdN_of_lookup _ _ _ _ hfinq0, hq0l',
        ⟨fd0, hfd0, by rw [hfy0]; simp [hsk]⟩, Or.inr rfl, ?_, hsl, fd', h1, h2⟩
      apply rdN_of_lookup
      show (upsert (upsert w1.nodes q0 _) q _).lookup (w.next + 2) = _
      rw [hfin _ (Ne.symm hqn2) (Ne.symm hq0n2), h1n]
      simp
    · have hy1 := hfs k1 (by rw [← hsc]; omega)
      rw [hQs] at hy1
      obtain ⟨fd', h1, h2⟩ := Option.map_eq_some_iff.mp hy1
      refine ⟨_, w.next, (halves n.leaf c.i (n.lastVersion c.i) [(k1, y)]).1,
        rdN_of_lookup _ _ _ _ hfinq0, hq0l',
        ⟨fd0, hfd0, by rw [hfy0]; simp [hsk]⟩, Or.inl rfl, ?_, hfl, fd', h1, h2⟩
      apply rdN_of_lookup
      show (upsert (upsert w1.nodes q0 _) q _).lookup w.next = _
      rw [hfin _ (Ne.symm hqn1) (Ne.symm hq0n1), h1n]
      simp


set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth d'' + 2), not made, split in time below its segment leaf q (a
leaf not made, without room, over the split's bound), which splits in space below q0 (inner,
with room for two klongs): q0's search at k1 names the half on k1's side, a leaf whose
search of k1 names p's copy (the next id), which holds p's last version and p's cached
segment and height; the rest kept but p, q, q0, the copy and the halves. -/
theorem writerWP_handleFull_spaceRoomChildHole (d'' : Nat) (p q q0 : NodeId) (pn qn q0n last : KNode)
    (kq k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d'' + 1]?).map (·.2) = some q) (hpk : w.path[d'' + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[d'']?).map (·.2) = some q0) (hpkq : w.path[d'' + 1]? = some (some kq, q))
    (hqnl : qn.leaf = true) (hqfirst : qn.firstTime ≠ some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny4 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length) (hrange : ∀ c' z, (c', z) ∈ qn.live → kq ≤ c')
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hroom : q0n.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((q0n.add c.i (.key kq (w.next + 2))).add c.i
      (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2))) = false)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) :
    WriterWP (handleFull (d'' + 1 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ q0 → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
        w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ (q0n' : KNode) (z' : NodeId) (zn : KNode), rdN c w' q0 = some q0n' ∧ q0n'.leaf = false ∧
        (∃ fd0, q0n'.searchLte c.i k1 = some fd0 ∧ fd0.y = z') ∧
        (z' = w.next + 2 ∨ z' = w.next + 2 + 2) ∧
        rdN c w' z' = some zn ∧ zn.leaf = true ∧
        ∃ fd', zn.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
  have hpn : p ≠ w.next := by omega
  have hqn : q ≠ w.next := by omega
  have hq0n : q0 ≠ w.next := by omega
  unfold handleFull
  refine writerWP_handleFullWith_time_up_last_gh (d'' + 1) p q pn qn k1 last compact c w hlk hlq hfirst
    hcs hpq hpk _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1p h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqn]; exact hlq
  have hlq01 : w1.nodes.lookup q0 = some q0n := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hq0n]; exact hlq0
  have hny1 : w1.nodes.lookup w1.next = none := by
    rw [h1next, h1n, lookup_append_single_ne _ _ _ _ (by omega)]; exact hny2
  have hny21 : w1.nodes.lookup (w1.next + 2) = none := by
    rw [h1next, h1n, lookup_append_single_ne _ _ _ _ (by omega)]; exact hny4
  refine writerWP_mono (writerWP_appendKlongs_spaceRoomHoleGh d'' q q0 qn q0n kq k1 w.next c w1 hlq1
    hlq01 hqnl hqfirst hqwf hqtm hny1 hny21 hqq0 hsz hsp h2 hrange (by rw [h1p]; exact hpq0)
    (by rw [h1p]; exact hpkq) hq0l hq0wf hq0tm hroom (by rw [h1next]; exact hdead) fd hfd hfdc) ?_
  rintro _ w2 ⟨h2t, h2top, h2p, h2gh, h2rest, q0n', z', zn, hq0r, hq0l', hs0, hz', hzr, hzl, hs1⟩
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
  have hzp : z' ≠ p := by rw [h1next] at hz'; omega
  refine ⟨by rw [h2t, h1t], by rw [h2top, h1top], ?_, rdN_of_lookup _ _ _ _ hy3, ?_, q0n', z', zn, ?_,
    hq0l', hs0, by rw [h1next] at hz'; exact hz', ?_, hzl, hs1⟩
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
  · rw [← hq0r]
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup q0 = _
    rw [lookup_upsert]
    simp only [Ne.symm hpq0', ↓reduceIte]
  · rw [← hzr]
    apply rdN_congr_lookup
    show (upsert w2.nodes p _).lookup z' = _
    rw [lookup_upsert]
    simp only [hzp, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- R1 after that split (`descendToHeight_redirectSeg2` with the half for q'). -/
theorem writerWP_handleFull_spaceRoomChildHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 3 ≤ d)
    (d'' : Nat) (p q q0 : NodeId) (pnS qnS q0nS pn qn q0n last : KNode)
    (kq k1 : Nat) (compact : Bool) (w : W)
    (hpkS : S1.path[d - 1]? = some (some k1, p)) (hpnS : rdN c S p = some pnS) (hplS : pnS.leaf = false)
    (hqS : (S1.path[d - 2]?).map (·.2) = some q) (hqnS : rdN c S q = some qnS) (hqlS : qnS.leaf = true)
    (hq0S : (S1.path[d - 3]?).map (·.2) = some q0) (hq0nS : rdN c S q0 = some q0nS)
    (hq0lS : q0nS.leaf = false)
    (hroot : w.top.rootKey = S.top.rootKey)
    (hagS : ∀ u ∈ (S1.path.map (·.2)).dropLast.dropLast.dropLast.dropLast,
      rdN c w u = rdN c S u ∧ u ≠ p ∧ u ≠ q ∧ u ≠ q0 ∧ u < w.next)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d'' + 1]?).map (·.2) = some q) (hpk : w.path[d'' + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[d'']?).map (·.2) = some q0) (hpkq : w.path[d'' + 1]? = some (some kq, q))
    (hqnl : qn.leaf = true) (hqfirst : qn.firstTime ≠ some c.i) (hqwf : klongsWf qn.ks = true)
    (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny4 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hsz : c.p.M < qn.size + 2) (hsp : c.p.splitAbove < (qn.lastVersion c.i).size)
    (h2 : 2 ≤ qn.live.length) (hrange : ∀ c' z, (c', z) ∈ qn.live → kq ≤ c')
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (hroom : q0n.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((q0n.add c.i (.key kq (w.next + 2))).add c.i
      (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2))) = false)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (d'' + 1 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_spaceRoomChildHole d'' p q q0 pn qn q0n last kq k1 compact c w
    hlk hlq hlq0 hfirst hcs hpq hpk hpq0 hpkq hqnl hqfirst hqwf hqtm hpq' hpq0' hqq0 hplt hqlt hq0lt hny
    hny2 hny4 hsz hsp h2 hrange hq0l hq0wf hq0tm hroom hdead fd hfd hfdc) ?_
  rintro _ T ⟨-, htop, hfr, hy, hgy, q0n', z', zn, hq0r, hq0l', hs0, hz', hzr, hzl, hs1⟩
  obtain ⟨g', hg'⟩ := hghp
  refine descendToHeight_redirectSeg2 key g h c S S1 T d hS hd p q q0 z' w.next pnS qnS q0nS
    q0n' zn k1 hpkS hpnS hplS hqS hqnS hqlS hq0S hq0nS hq0lS (by rw [htop]; exact hroot) ?_ hq0r hq0l'
    hs0 hzr hzl hs1 ⟨_, hy⟩ ⟨g', by rw [hgy]; exact hg'⟩
  intro u hu
  obtain ⟨h1, h2, h3, h4, h5⟩ := hagS u hu
  rw [← h1]
  apply rdN_congr_lookup
  exact hfr u h2 h3 h4 (by omega) (by omega) (by omega)

end SIS.Tree
