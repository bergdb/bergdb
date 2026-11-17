/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the one of l4f's 69 thin-copy cascades whose segment leaf q is the space root,
not made by the transaction, split in space (`split.space3`): p's copy y put by k1 into q
makes q's halves and a new inner space root over them; the new root's search at k1 names
the half that holds y's klong. What `descendToHeight_topSeg_innerRoot` takes.
-/
import SIS.Tree.LiveSpaceRoomHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The new space root over two halves: its search at k1 names the second half from the
divider on, else the first. -/
theorem searchLte_twoRoot (t : Time) (a b : NodeId) (sc k1 : Nat) (hsc : 0 < sc) :
    ∃ fd, (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode).searchLte t k1 = some fd ∧
      fd.y = if sc ≤ k1 then b else a := by
  have hks : ([.time t, .key 0 a, .key sc b] : List Klong) = newKlongs t [(0, a), (sc, b)] := rfl
  have hsrt : CvSorted [(0, a), (sc, b)] := by
    simp [CvSorted]; omega
  have hlive : (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode).live = [(0, a), (sc, b)] := by
    rw [hks]; exact KNode.live_newKlongs_sorted false t _ hsrt
  have htm : ∀ s, Klong.time s ∈ (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode).ks → s ≤ t := by
    show ∀ s, Klong.time s ∈ ([.time t, .key 0 a, .key sc b] : List Klong) → s ≤ t
    rw [hks]; exact newKlongs_times t _
  have hla := KNode.liveAt_of_times (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode) t htm
  rw [hlive] at hla
  obtain ⟨hs1, hs2⟩ := KNode.searchLte_spec (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode) t k1
  cases hr : (⟨false, [.time t, .key 0 a, .key sc b]⟩ : KNode).searchLte t k1 with
  | none =>
    exfalso
    have := (hs2.mp hr) (0, a) (by rw [hla]; simp)
    simp at this
  | some f =>
    refine ⟨f, rfl, ?_⟩
    obtain ⟨hmem, hle, hmax⟩ := hs1 f hr
    rw [hla] at hmem hmax
    simp only [decide_eq_true_eq] at hle hmax
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    · -- f is (0, a)
      have hfc : f.c = 0 := (Prod.mk.inj h).1
      have hfy : f.y = a := (Prod.mk.inj h).2
      by_cases hsk : sc ≤ k1
      · exfalso
        have := hmax (sc, b) (by simp) (by simp only; omega)
        simp only at this
        omega
      · simp [hsk, hfy]
    · have hfc : f.c = sc := (Prod.mk.inj h).1
      have hfy : f.y = b := (Prod.mk.inj h).2
      have : sc ≤ k1 := by omega
      simp [this, hfy]

set_option maxHeartbeats 4000000 in
/-- p's copy y put by k1 into the space root q, a leaf not made by the transaction, without
room, its last version over the split's bound: q's halves and a new inner space root over
them; the new root's search at k1 names the half on k1's side, a leaf whose search of k1
names y; the nodes but q and the three new ones kept. -/
theorem writerWP_appendKlongs_rootSpaceHole (q : NodeId) (n : KNode) (k1 : Nat) (y : NodeId)
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hnl : n.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hnwf : klongsWf n.ks = true) (hntm : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hqn : q < w.next)
    (hsz : c.p.M < n.size + 2) (hsp : c.p.splitAbove < (n.lastVersion c.i).size)
    (h2 : 2 ≤ n.live.length) :
    WriterWP (appendKlongs 0 q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧
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
  refine writerWP_mono (writerWP_handleFullWith_rootSpace_term _ q n [(k1, y)] c w hlk hfirst hsp hqn) ?_
  rintro _ w' ⟨ht, hroot, -, -, -, hlook⟩
  have hq1 : q ≠ w.next := by omega
  have hq2 : q ≠ w.next + 2 := by omega
  have hq3 : q ≠ w.next + 2 + 2 := by omega
  refine ⟨ht, hroot, fun z h1 h2 h3 h4 => by rw [hlook z]; simp [h1, h2, h3, h4], ?_⟩
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

end SIS.Tree
