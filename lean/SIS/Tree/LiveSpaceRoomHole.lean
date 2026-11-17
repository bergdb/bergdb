/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the group of l4f's 69 thin-copy cascades whose segment leaf q, not made by the
transaction, splits in space below an inner parent q0 with room (15 on the runs): p's
copy y put by `appendKlongs` into q, without room, with a last version over the split's
bound: q's halves at the next two ids (`split.space1`), y's klong in the half on its side
of the divider, and q0 names them. What `descendToHeight_redirectSeg2` takes: q0's search
at p's klong names the half that holds it, a leaf whose search of p's klong names y.
-/
import SIS.Tree.LiveInPlaceHole
import SIS.Tree.WriterTreeCascadeGen

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Two klongs added to an inner node q: kq's, the klong that q's `searchLte` finds at
k1, now naming a, and a new one sc above kq naming b: the search at k1 finds b from sc
on, else a. -/
theorem searchLte_add_two (qn : KNode) (t : Time) (k1 kq sc : Nat) (a b : NodeId) (fd : Found)
    (hwf : klongsWf qn.ks = true) (htm : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hfd : qn.searchLte t k1 = some fd) (hc : fd.c = kq) (hlt : kq < sc) :
    ∃ fd', ((qn.add t (.key kq a)).add t (.key sc b)).searchLte t k1 = some fd' ∧
      fd'.y = if sc ≤ k1 then b else a := by
  have hwf1 := KNode.add_key_wf qn t kq a hwf
  have hat1 := KNode.add_times qn t (.key kq a) (fun s h => by cases h) htm
  have hat2 := KNode.add_times _ t (.key sc b) (fun s h => by cases h) hat1
  have hmem2 : ∀ c' z, (c', z) ∈ ((qn.add t (.key kq a)).add t (.key sc b)).liveAt t →
      (c' = sc ∧ z = b) ∨ (c' = kq ∧ z = a) ∨ (c' ≠ kq ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z h
    rcases KNode.add_key_liveAt_mem _ t sc b hwf1 hat1 c' z h with h1 | ⟨_, h2⟩
    · exact Or.inl h1
    · rcases KNode.add_key_liveAt_mem _ t kq a hwf htm c' z h2 with h3 | h3
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h3)
  have hb : (sc, b) ∈ ((qn.add t (.key kq a)).add t (.key sc b)).liveAt t := by
    rw [KNode.liveAt_of_times _ t hat2]
    apply bk_mem_of_lookup
    rw [KNode.add_key_live_lookup_of_wf _ t sc sc b hwf1]
    simp
  have ha : (kq, a) ∈ ((qn.add t (.key kq a)).add t (.key sc b)).liveAt t := by
    rw [KNode.liveAt_of_times _ t hat2]
    apply bk_mem_of_lookup
    rw [KNode.add_key_live_lookup_of_wf _ t sc kq b hwf1, KNode.add_key_live_lookup_of_wf qn t kq kq a hwf]
    have : (sc == kq) = false := by simp; omega
    simp [this]
  obtain ⟨hs1, _⟩ := KNode.searchLte_spec qn t k1
  obtain ⟨hmemq, hle, hmax⟩ := hs1 fd hfd
  simp only [decide_eq_true_eq] at hle hmax
  obtain ⟨hs1', hs2'⟩ := KNode.searchLte_spec ((qn.add t (.key kq a)).add t (.key sc b)) t k1
  cases hr : ((qn.add t (.key kq a)).add t (.key sc b)).searchLte t k1 with
  | none =>
    exfalso
    have := (hs2'.mp hr) (kq, a) ha
    simp only [decide_eq_false_iff_not] at this
    rw [← hc] at this
    exact this hle
  | some f' =>
    refine ⟨f', rfl, ?_⟩
    obtain ⟨hmem', hle', hmax'⟩ := hs1' f' hr
    simp only [decide_eq_true_eq] at hle' hmax'
    rcases hmem2 f'.c f'.y hmem' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hne, hold⟩
    · have : sc ≤ k1 := by rw [← h1]; omega
      simp [this, h2]
    · by_cases hsk : sc ≤ k1
      · exfalso
        have := hmax' (sc, b) hb (by simp only; omega)
        simp only at this
        omega
      · simp [hsk, h2]
    · exfalso
      have h1 := hmax (f'.c, f'.y) hold hle'
      have h2 := hmax' (kq, a) ha (by rw [← hc]; exact hle)
      simp only at h1 h2
      rw [hc] at h1
      exact hne (by omega)

/-- A klong pair added to a node with room: the node gets both, nothing else changes but
the cache of the node. -/
theorem writerWP_appendKlongs_room2 (d : Nat) (q : NodeId) (qn : KNode) (k1 k2 : Nat) (y1 y2 : NodeId)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup q = some qn) (hroom : qn.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) = false) :
    WriterWP (appendKlongs d q [(k1, y1), (k2, y2)]) c w (fun _ w' =>
      w' = { w with nodes := upsert w.nodes q ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) }) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  have h1 : ¬ (qn.size + [(k1, y1), (k2, y2)].length + 1 > c.p.M) := by simp; omega
  simp only [h1, ↓reduceIte, List.foldl_cons, List.foldl_nil, hdead, Bool.false_eq_true]
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  simp only [putNode, List.foldl_cons, List.foldl_nil, writerWP_modify]

/-- The divider of a node's halves is above the node's first live compare value. -/
theorem divider_gt_first (n : KNode) (r : Nat × NodeId) (h2 : 2 ≤ n.live.length)
    (hr : (n.live.drop (n.live.length / 2)).head? = some r) :
    ∃ e ∈ n.live, e.1 < r.1 := by
  have hpw := n.live_order
  have hsplit : n.live = n.live.take (n.live.length / 2) ++ n.live.drop (n.live.length / 2) :=
    (List.take_append_drop _ _).symm
  obtain ⟨e, he⟩ : ∃ e, (n.live.take (n.live.length / 2)).head? = some e := by
    cases h : n.live.take (n.live.length / 2) with
    | nil =>
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · rw [h] at h2; simp at h2
    | cons e _ => exact ⟨e, rfl⟩
  have heT : e ∈ n.live.take (n.live.length / 2) := List.mem_of_mem_head? he
  have hrD : r ∈ n.live.drop (n.live.length / 2) := List.mem_of_mem_head? hr
  rw [hsplit, List.pairwise_append] at hpw
  exact ⟨e, List.mem_of_mem_take heT, hpw.2.2 e heT r hrD⟩

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into q (depth d'' + 1), a leaf not made by the transaction,
without room, its last version over the split's bound: q splits in space, its halves at
the next two ids, named by q0 (inner, with room for two klongs) by q's klong kq and the
divider; q0's search at k1 (where it named q) names the half on k1's side, a leaf whose
search of k1 names y; the nodes but q, q0 and the halves kept. -/
theorem writerWP_appendKlongs_spaceRoomHole (d'' : Nat) (q q0 : NodeId) (n q0n : KNode)
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
  refine writerWP_handleFullWith_space_up d'' q q0 n q0n kq [(k1, y)] c w hlk hlq0 hq0l hfirst hsp
    hpq hpk _ ?_
  intro w1 h1n h1t h1top h1p h1next h1v
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
  refine ⟨h1t, h1top, h1p, ?_, ?_⟩
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

end SIS.Tree
