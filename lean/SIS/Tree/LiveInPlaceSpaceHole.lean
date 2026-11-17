/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the last group of l4f's 69 thin-copy cascades (6 on the runs): p's copy y put by
k1 into its segment leaf q, made by the transaction, without room and over the split's
bound: q splits in space in place (`split.space1.inplace`: q keeps the first half, the
second at the next id), q's parent q0, the space root, not made, gets the second half's
klong without room and splits in time (`split.time2`): q0's copy, its last version with
that klong, is the new space root. Its search at k1 names the half on k1's side (q or the
second), a leaf whose search of k1 names y: what `descendToHeight_topSeg_innerRoot` takes.
-/
import SIS.Tree.LiveRootSpaceHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node m whose live klongs are n's and a new klong sc naming b, above the klong kq
that n's `searchLte` finds at k1: m's search at k1 names b from sc on, else what n's
named. -/
theorem searchLte_lookup_addNew (n m : KNode) (t : Time) (k1 kq sc : Nat) (b : NodeId) (fd : Found)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (ht2 : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (hlk : ∀ cc, m.live.lookup cc = if sc == cc then some b else n.live.lookup cc)
    (hfd : n.searchLte t k1 = some fd) (hc : fd.c = kq) (hlt : kq < sc) :
    ∃ fd', m.searchLte t k1 = some fd' ∧ fd'.y = if sc ≤ k1 then b else fd.y := by
  have hL1 := KNode.liveAt_of_times n t ht
  have hL2 := KNode.liveAt_of_times m t ht2
  have hnd1 := KNode.live_keys_nodup n
  have hnd2 := KNode.live_keys_nodup m
  have hmem2 : ∀ c' z, (c', z) ∈ m.live ↔ if sc = c' then z = b else (c', z) ∈ n.live := by
    intro c' z
    rw [mem_iff_lookup _ hnd2, hlk]
    by_cases h : sc = c'
    · subst h; simp [eq_comm]
    · have : (sc == c') = false := by simpa using h
      simp only [this, Bool.false_eq_true, ↓reduceIte, h]
      rw [mem_iff_lookup _ hnd1]
  obtain ⟨hs1, _⟩ := KNode.searchLte_spec n t k1
  obtain ⟨hmemq, hle, hmax⟩ := hs1 fd hfd
  rw [hL1] at hmemq hmax
  simp only [decide_eq_true_eq] at hle hmax
  have hkqm : (kq, fd.y) ∈ m.live := by
    rw [hmem2]
    have : ¬ sc = kq := by omega
    simp only [this, ↓reduceIte]
    rw [← hc]; exact hmemq
  have hscm : (sc, b) ∈ m.live := by rw [hmem2]; simp
  obtain ⟨hs1', hs2'⟩ := KNode.searchLte_spec m t k1
  cases hr : m.searchLte t k1 with
  | none =>
    exfalso
    have := (hs2'.mp hr) (kq, fd.y) (by rw [hL2]; exact hkqm)
    simp only [decide_eq_false_iff_not] at this
    rw [← hc] at this
    exact this hle
  | some f' =>
    refine ⟨f', rfl, ?_⟩
    obtain ⟨hmem', hle', hmax'⟩ := hs1' f' hr
    rw [hL2] at hmem' hmax'
    simp only [decide_eq_true_eq] at hle' hmax'
    rw [hmem2] at hmem'
    by_cases hs : sc = f'.c
    · simp only [hs, ↓reduceIte] at hmem'
      have : sc ≤ k1 := by omega
      simp [this, hmem']
    · simp only [hs, ↓reduceIte] at hmem'
      -- f' is an old klong: by n's max it is at most kq, by m's max at least kq
      have h1 := hmax (f'.c, f'.y) hmem' hle'
      have h2 := hmax' (kq, fd.y) hkqm (by rw [← hc]; exact hle)
      simp only at h1 h2
      rw [hc] at h1
      have hfk : f'.c = kq := by omega
      have hsk : ¬ sc ≤ k1 := by
        intro hsk
        have := hmax' (sc, b) hscm (by simp only; omega)
        simp only at this
        omega
      simp only [hsk, ↓reduceIte]
      -- the same compare value, so the same pointee
      have e1 := lookup_some_of_mem hnd1 hmem'
      have e2 := lookup_some_of_mem hnd1 hmemq
      rw [hfk, ← hc] at e1
      rw [e1] at e2
      exact Option.some.inj e2

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into q (depth 1), a leaf the transaction made, without room, over
the split's bound, below the space root q0 (by kq), inner, not made, without room for the
second half's klong (or compacting) and within a split's bound when no room: q keeps the
first half, the second at the next id, q0's copy with its klong the new space root; the new
root's search at k1 names the half on k1's side, a leaf whose search of k1 names y. -/
theorem writerWP_appendKlongs_inPlaceSpaceRootHole (q q0 : NodeId) (n q0n : KNode) (kq k1 : Nat)
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
  refine writerWP_handleFullWith_spaceInPlace_up 0 q q0 n q0n [(k1, y)] c w hlk hlq0 hq0l hmade hsp
    hpq hqlt _ ?_
  intro w1 h1n h1t h1top h1p h1next h1v
  have hlq01 : w1.nodes.lookup q0 = some q0n := by
    rw [h1n q0]; simp only [Ne.symm hqq0, hq0n1, ↓reduceIte]; exact hlq0
  have hny1 : w1.nodes.lookup w1.next = none := by
    rw [h1next, h1n]
    have e1 : w.next + 2 ≠ q := by omega
    have e2 : w.next + 2 ≠ w.next := by omega
    simp only [e1, e2, ↓reduceIte]; exact hny2
  refine writerWP_mono (writerWP_appendKlongs_rootTime q0 q0n _ c w1 hlq01 hq0first
    (by rw [h1next]; omega) hny1 (fun h => hq0full (by simpa using h))
    (fun h => hq0time (by simpa using h))) ?_
  rintro _ w2 ⟨h2t, h2r, out, ho1, -, ho3, ho4, h2n⟩
  have hroot : w2.top.rootKey = w.next + 2 := by rw [h2r, h1next]
  have hfin : ∀ z, z ≠ q0 → z ≠ w.next + 2 → w2.nodes.lookup z = w1.nodes.lookup z := by
    intro z h1 h2
    rw [h2n z, h1next]
    simp only [h1, h2, ↓reduceIte]
  refine ⟨by rw [h2t, h1t], hroot, fun z h1 h2 h3 h4 => by
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

end SIS.Tree
