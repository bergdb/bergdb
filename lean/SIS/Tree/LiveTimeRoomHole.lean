/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the second group of l4f's 69 thin-copy cascades (15 on the runs): p's copy y
is put by `appendKlongs` into its segment leaf q, not made by the transaction, without
room (or compacting), which splits in time (`split.time1`): q's copy q', its last version
with p's klong naming y, is put into q's parent q0, inner, with room. Its shape gives what
`descendToHeight_redirectSeg2` takes: q0's search of p's compare value names q', a leaf
whose search of p's klong names y.
-/
import SIS.Tree.LiveRootTimeHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- `appendKlongs` at q (depth d'' + 1), not made by the transaction, without room for
ins or compacting, its last version within a split's bound when it has no room, below
q0 (by q's klong kq) with room for one klong: q's copy, its last version with ins, is
the next id, named by q0 by kq; q its klongs before the transaction; the rest kept. -/
theorem writerWP_appendKlongs_timeRoom (d'' : Nat) (q q0 : NodeId) (n q0n : KNode) (kq : Nat)
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
      w'.nodes.lookup q0 = some (q0n.add c.i (.key kq w.next)) ∧
      w'.nodes.lookup q = some (n.toPrev (c.i - 1)) ∧
      (∃ out : KNode, out.leaf = n.leaf ∧ klongsWf out.ks = true ∧
        (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ cc, out.live.lookup cc = ins.foldl (pairLookupStep cc) (n.live.lookup cc)) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, out.ks⟩) ∧
      ∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) := by
    intro compact hcs
    refine writerWP_handleFullWith_time_upN d'' q q0 n q0n kq ins compact c w hlk hlq0 hfirst hcs
      hpq hpk _ ?_
    intro l hl1 hl2 hl3 hl4 _ w1 h1n h1t h1top h1p h1next h1v
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
    refine ⟨h1t, h1top, h1p, ?_, ?_, ⟨l, hl1, hl2, hl3, hl4, ?_⟩, ?_⟩
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

/-- p's copy y put by p's klong k1 into its segment leaf q, not made by the transaction,
which splits in time below an inner q0 with room: q0's search at k1 (where it named q)
names q's copy q' (the next id), a leaf whose search of k1 names y; the nodes but q, q0
and q' kept. What `descendToHeight_redirectSeg2` takes but y's node and height. -/
theorem writerWP_appendKlongs_timeRoomHole (d'' : Nat) (q q0 : NodeId) (n q0n : KNode)
    (kq k1 : Nat) (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hlq0 : w.nodes.lookup q0 = some q0n)
    (hfirst : n.firstTime ≠ some c.i) (hny : w.nodes.lookup w.next = none) (hqq0 : q ≠ q0)
    (hfull : n.size + 2 ≤ c.p.M → deadOver c.p (n.add c.i (.key k1 y)) = true)
    (htime : c.p.M < n.size + 2 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d'']?).map (·.2) = some q0) (hpk : w.path[d'' + 1]? = some (some kq, q))
    (hroom : q0n.size + 1 + 1 ≤ c.p.M) (hdead : deadOver c.p (q0n.add c.i (.key kq w.next)) = false)
    (hq0l : q0n.leaf = false) (hq0wf : klongsWf q0n.ks = true)
    (hq0tm : ∀ s, Klong.time s ∈ q0n.ks → s ≤ c.i)
    (fd : Found) (hfd : q0n.searchLte c.i k1 = some fd) (hfdc : fd.c = kq) :
    WriterWP (appendKlongs (d'' + 1) q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ q → z ≠ q0 → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ q0n' qn', rdN c w' q0 = some q0n' ∧ q0n'.leaf = false ∧
        (∃ fd0, q0n'.searchLte c.i k1 = some fd0 ∧ fd0.y = w.next) ∧
        rdN c w' w.next = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  refine writerWP_mono (writerWP_appendKlongs_timeRoom d'' q q0 n q0n kq [(k1, y)] c w hlk hlq0
    hfirst hny hqq0 (fun h => hfull (by simpa using h)) (fun h => htime (by simpa using h)) hpq hpk
    hroom hdead) ?_
  rintro _ w' ⟨ht, htop, hp, h0, -, ⟨out, hl1, hl2, hl3, hl4, hnx⟩, hrest⟩
  have hq : (⟨n.leaf, out.ks⟩ : KNode) = out := by rw [← hl1]
  refine ⟨ht, htop, hp, hrest, q0n.add c.i (.key kq w.next), out, rdN_of_lookup _ _ _ _ h0, ?_,
    searchLte_add_key q0n c.i k1 kq w.next fd hq0wf hq0tm hfd hfdc,
    rdN_of_lookup _ _ _ _ (by rw [hnx, hq]), hl1, ?_⟩
  · rw [KNode.add_leaf]; exact hq0l
  · have hs := KNode.searchEq_live out c.i hl2 hl3 k1
    rw [hl4 k1] at hs
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep, beq_self_eq_true, ↓reduceIte] at hs
    obtain ⟨fd', hfd', hfy⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨fd', hfd', hfy⟩

end SIS.Tree
