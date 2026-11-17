/-
The split step's R1 for the 15 of l4f's 69 where the segment leaf q, not made, splits in
time below an inner q0 with room (bergdb 030-01, R4's open part): p's whole split with the
heights' cache, then the merges' descent one height up finds p's copy
(`descendToHeight_redirectSeg2`).
-/
import SIS.Tree.LiveRootChildHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- The writer's time split of a node that existed before the transaction, with
klongs ins and its last version, below a parent of either kind, with the copy's entry in the cache: x's. -/
theorem writerWP_handleFullWith_time_upN_gh (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ (gh : Nat × Nat), w.gh.lookup x = some gh → ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true → (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
      (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) →
      (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) →
      ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, l.ks⟩)] →
        w1.gh = (w.next, gh.1, gh.2) :: w.gh → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cachedL x n c w hlk _ (fun gh hgh => ?_)
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup gh hgh l hl_leaf hl_wf hl_times hl_look hl_nd _ rfl rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup gh hgh l hl_leaf hl_wf hl_times hl_look hl_nd _ rfl rfl rfl rfl rfl rfl rfl

set_option maxHeartbeats 4000000 in
/-- `appendKlongs` at q (depth d'' + 1), not made by the transaction, without room for
ins or compacting, its last version within a split's bound when it has no room, below
q0 (by q's klong kq) with room for one klong: q's copy, its last version with ins, is
the next id, named by q0 by kq; q its klongs before the transaction; the rest kept. -/
theorem writerWP_appendKlongs_timeRoomGh (d'' : Nat) (q q0 : NodeId) (n q0n : KNode) (kq : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : n.firstTime ≠ some c.i) (hny : w.nodes.lookup w.next = none) (hqq0 : q ≠ q0)
    (hfull : n.size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = true)
    (htime : c.p.M < n.size + ins.length + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d'']?).map (·.2) = some q0) (hpk : w.path[d'' + 1]? = some (some kq, q))
    (hroom : q0n.size + 1 + 1 ≤ c.p.M) (hdead : deadOver c.p (q0n.add c.i (.key kq w.next)) = false) :
    WriterWP (appendKlongs (d'' + 1) q ins) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ w.next → w'.gh.lookup z = w.gh.lookup z) ∧
      w'.nodes.lookup q0 = some (q0n.add c.i (.key kq w.next)) ∧
      w'.nodes.lookup q = some (n.toPrev (c.i - 1)) ∧
      (∃ out : KNode, out.leaf = n.leaf ∧ klongsWf out.ks = true ∧
        (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ cc, out.live.lookup cc = ins.foldl (pairLookupStep cc) (n.live.lookup cc)) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, out.ks⟩) ∧
      ∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) := by
  have hq0n : q0 ≠ w.next := by intro he; rw [he, hny] at hlq0; cases hlq0
  have hqn : q ≠ w.next := by intro he; rw [he, hny] at hlk; cases hlk
  -- the split, given its continuation
  have hsplit : ∀ compact : Bool,
      (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs d'' q more) (d'' + 1) q ins
        (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ w.next → w'.gh.lookup z = w.gh.lookup z) ∧
      w'.nodes.lookup q0 = some (q0n.add c.i (.key kq w.next)) ∧
      w'.nodes.lookup q = some (n.toPrev (c.i - 1)) ∧
      (∃ out : KNode, out.leaf = n.leaf ∧ klongsWf out.ks = true ∧
        (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ cc, out.live.lookup cc = ins.foldl (pairLookupStep cc) (n.live.lookup cc)) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, out.ks⟩) ∧
      ∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) := by
    intro compact hcs
    refine writerWP_handleFullWith_time_upN_gh d'' q q0 n q0n kq ins compact c w hlk hlq0 hfirst hcs
      hpq hpk _ ?_
    intro gh _ l hl1 hl2 hl3 hl4 _ w1 h1n h1gh h1t h1top h1p h1next h1v
    have hlq01 : w1.nodes.lookup q0 = some q0n := by
      rw [h1n, lookup_append_single_ne _ _ _ _ hq0n]; exact hlq0
    refine writerWP_mono (writerWP_appendKlongs_room d'' q0 q0n kq w.next c w1 hlq01 hroom hdead) ?_
    rintro _ w2 rfl
    have hlq2 : (upsert w1.nodes q0 (q0n.add c.i (.key kq w.next))).lookup q = some n := by
      rw [lookup_upsert, h1n, lookup_append_single_ne _ _ _ _ hqn]
      simp only [hqq0, ↓reduceIte]; exact hlk
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q n c _ hlq2]
    rw [putNode, writerWP_modify]
    refine ⟨h1t, h1top, h1p, fun z hz => ?_, ?_, ?_, ⟨l, hl1, hl2, hl3, hl4, ?_⟩, ?_⟩
    · show w1.gh.lookup z = _
      rw [h1gh]
      have hb : (z == w.next) = false := by simp [hz]
      simp [List.lookup, hb]
    · show (upsert (upsert w1.nodes q0 _) q _).lookup q0 = _
      rw [lookup_upsert, lookup_upsert]
      simp only [Ne.symm hqq0, ↓reduceIte]
    · show (upsert (upsert w1.nodes q0 _) q _).lookup q = _
      rw [lookup_upsert]
      simp only [↓reduceIte]
    · show (upsert (upsert w1.nodes q0 _) q _).lookup w.next = _
      rw [lookup_upsert, lookup_upsert, h1n, List.lookup_append, hny]
      simp only [Ne.symm hqn, Ne.symm hq0n, ↓reduceIte]
      simp [List.lookup]
    · intro z hzq hzq0 hzn
      show (upsert (upsert w1.nodes q0 _) q _).lookup z = _
      rw [lookup_upsert, lookup_upsert, h1n, lookup_append_single_ne _ _ _ _ hzn]
      simp only [hzq, hzq0, ↓reduceIte]
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + ins.length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime hsz
    exact hsplit false
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
  · have hd := hfull (by omega)
    simp only [hsz, hd, ↓reduceIte]
    exact hsplit true (by simp)

set_option maxHeartbeats 4000000 in
/-- The merge's parent p (depth d'' + 2), not made, split in time below its segment leaf q
(not made, without room or compacting, within a split's bound when no room), which splits
in time below q0 (inner, with room): after it q0's search at k1 (where it named q) names q's
copy (the id after p's copy), a leaf whose search of k1 names p's copy, which holds p's last
version and p's cached segment and height; the rest kept but p, q, q0 and the two new ones. -/
theorem writerWP_handleFull_timeRoomChildHole (d'' : Nat) (p q q0 : NodeId) (pn qn q0n last : KNode)
    (kq k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d'' + 1]?).map (·.2) = some q) (hpk : w.path[d'' + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[d'']?).map (·.2) = some q0) (hpkq : w.path[d'' + 1]? = some (some kq, q))
    (hqfirst : qn.firstTime ≠ some c.i) (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hroom : q0n.size + 1 + 1 ≤ c.p.M) (hdead : deadOver c.p (q0n.add c.i (.key kq (w.next + 2))) = false)
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) :
    WriterWP (handleFull (d'' + 1 + 1) p last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧
      (∀ z, z ≠ p → z ≠ q → z ≠ q0 → z ≠ w.next → z ≠ w.next + 2 →
        w'.nodes.lookup z = w.nodes.lookup z) ∧
      rdN c w' w.next = some ⟨pn.leaf, last.ks⟩ ∧ rdG c w' w.next = w.gh.lookup p ∧
      ∃ q0n' qn', rdN c w' q0 = some q0n' ∧ q0n'.leaf = false ∧
        (∃ fd0, q0n'.searchLte c.i k1 = some fd0 ∧ fd0.y = w.next + 2) ∧
        rdN c w' (w.next + 2) = some qn' ∧ qn'.leaf = qn.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = w.next) := by
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
  refine writerWP_mono (writerWP_appendKlongs_timeRoomGh d'' q q0 qn q0n kq [(k1, w.next)] c w1 hlq1
    hlq01 hqfirst hny1 hqq0 (fun h => hqfull (by simpa using h)) (fun h => hqtime (by simpa using h))
    (by rw [h1p]; exact hpq0) (by rw [h1p]; exact hpkq) hroom (by rw [h1next]; exact hdead)) ?_
  rintro _ w2 ⟨h2t, h2top, h2p, h2gh, h2q0, -, ⟨out, ho1, ho2, ho3, ho4, h2nx⟩, h2rest⟩
  have hlp2 : w2.nodes.lookup p = some pn := by
    rw [h2rest p hpq' hpq0' (by rw [h1next]; omega), h1n, lookup_append_single_ne _ _ _ _ hpn]
    exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known p pn c w2 hlp2]
  rw [putNode, writerWP_modify]
  have hy3 : (upsert w2.nodes p (pn.toPrev (c.i - 1))).lookup w.next = some ⟨pn.leaf, last.ks⟩ := by
    rw [lookup_upsert]
    simp only [Ne.symm hpn, ↓reduceIte]
    rw [h2rest w.next (Ne.symm hqn) (Ne.symm hq0n) (by rw [h1next]; omega), h1n]
    exact lookup_append_single_self _ _ _ hny
  have hq : (⟨qn.leaf, out.ks⟩ : KNode) = out := by rw [← ho1]
  refine ⟨by rw [h2t, h1t], by rw [h2top, h1top], ?_, rdN_of_lookup _ _ _ _ hy3, ?_,
    q0n.add c.i (.key kq (w.next + 2)), out, ?_, by rw [KNode.add_leaf]; exact hq0l,
    searchLte_add_key q0n c.i k1 kq (w.next + 2) fd hq0wf hq0tm hfd hfdc, ?_, ho1, ?_⟩
  · intro z h1 h2 h3 h4 h5
    show (upsert w2.nodes p _).lookup z = _
    rw [lookup_upsert]
    simp only [h1, ↓reduceIte]
    rw [h2rest z h2 h3 (by rw [h1next]; exact h5), h1n, lookup_append_single_ne _ _ _ _ h4]
  · show rdG c { w2 with nodes := upsert w2.nodes p (pn.toPrev (c.i - 1)) } w.next = _
    unfold rdG
    simp only [hy3]
    show w2.gh.lookup w.next = _
    rw [h2gh _ (by rw [h1next]; omega), h1gh, hgh]
    simp [List.lookup]
  · apply rdN_of_lookup
    show (upsert w2.nodes p _).lookup q0 = _
    rw [lookup_upsert]
    simp only [Ne.symm hpq0', ↓reduceIte]
    rw [h2q0, h1next]
  · apply rdN_of_lookup
    show (upsert w2.nodes p _).lookup (w.next + 2) = _
    rw [lookup_upsert]
    have e : w.next + 2 ≠ p := by omega
    simp only [e, ↓reduceIte]
    rw [← h1next, h2nx, hq]
  · have hs := KNode.searchEq_live out c.i ho2 ho3 k1
    rw [ho4 k1] at hs
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep, beq_self_eq_true, ↓reduceIte] at hs
    obtain ⟨fd', hfd', hfy⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨fd', hfd', hfy⟩

set_option maxHeartbeats 4000000 in
/-- R1 after that split: with the round's descent at (g, h) on S (p at depth d - 1 below the
segment leaf q, q below an inner q0), the reads of w as S's above q0 (those nodes old, none
of p, q, q0), the space roots alike and p's cached height h + 1, the descent at (g, h + 1) on
the state after the split finds p's copy (`descendToHeight_redirectSeg2`). -/
theorem writerWP_handleFull_timeRoomChildHole_R1 (key : Key) (g h : Nat) (c : Ctx) (S S1 : W) (d : Nat)
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
    (hlk : w.nodes.lookup p = some pn) (hlq : w.nodes.lookup q = some qn) (hqnl : qn.leaf = true)
    (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : pn.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d'' + 1]?).map (·.2) = some q) (hpk : w.path[d'' + 1 + 1]? = some (some k1, p))
    (hpq0 : (w.path[d'']?).map (·.2) = some q0) (hpkq : w.path[d'' + 1]? = some (some kq, q))
    (hqfirst : qn.firstTime ≠ some c.i) (hpq' : p ≠ q) (hpq0' : p ≠ q0) (hqq0 : q ≠ q0)
    (hplt : p < w.next) (hqlt : q < w.next) (hq0lt : q0 < w.next)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hqfull : qn.size + 2 ≤ c.p.M → deadOver c.p (qn.add c.i (.key k1 w.next)) = true)
    (hqtime : c.p.M < qn.size + 2 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hroom : q0n.size + 1 + 1 ≤ c.p.M) (hdead : deadOver c.p (q0n.add c.i (.key kq (w.next + 2))) = false)
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq)
    (hghp : ∃ g', w.gh.lookup p = some (g', h + 1)) :
    WriterWP (handleFull (d'' + 1 + 1) p last compact) c w (fun _ T =>
      WriterWP (descendToHeight key g (h + 1)) c T
        (fun d' T1 => (T1.path[d']?).map (·.2) = some w.next)) := by
  refine writerWP_mono (writerWP_handleFull_timeRoomChildHole d'' p q q0 pn qn q0n last kq k1 compact c w
    hlk hlq hlq0 hfirst hcs hpq hpk hpq0 hpkq hqfirst hpq' hpq0' hqq0 hplt hqlt hq0lt hny hny2 hqfull
    hqtime hroom hdead hq0l hq0wf hq0tm fd hfd hfdc) ?_
  rintro _ T ⟨-, htop, hfr, hy, hgy, q0n', qn', hq0r, hq0l', hs0, hqr, hql', hs1⟩
  obtain ⟨g', hg'⟩ := hghp
  refine descendToHeight_redirectSeg2 key g h c S S1 T d hS hd p q q0 (w.next + 2) w.next pnS qnS q0nS
    q0n' qn' k1 hpkS hpnS hplS hqS hqnS hqlS hq0S hq0nS hq0lS (by rw [htop]; exact hroot) ?_ hq0r hq0l'
    hs0 hqr (by rw [hql']; exact hqnl) hs1 ⟨_, hy⟩ ⟨g', by rw [hgy]; exact hg'⟩
  intro u hu
  obtain ⟨h1, h2, h3, h4, h5⟩ := hagS u hu
  rw [← h1]
  apply rdN_congr_lookup
  exact hfr u h2 h3 h4 (by omega) (by omega)

end SIS.Tree
