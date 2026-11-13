import SIS.Tree.GetDelCascade
import SIS.Tree.PutInvTimeSpace
import SIS.Tree.PutInvDelFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete into a full segment leaf whose full inner parent
splits too (bergdb 024-12, TP10; the delete cascades of latest's
`writerWP_del_timeSplit2` and `writerWP_del_timeSpace`): the leaf, which keeps
a live klong, is time split into its last version without the key's klong, and
its parent is time split or space split below a grandparent with room. The
parts about the tree follow from the put cascades' `putInvT_timeSplit2` and
`putInvT_timeSpace`, with an unused fresh id for the put's value: the new leaf
holds only live klongs of the old one. -/

set_option linter.unusedSimpArgs false in
/-- A delete's bitmap in the segment leaf L, which keeps a live klong: by the
bitmap with room, or, full, by a time split of L's last version without the
key, in place for a leaf the transaction made, or by `hcascade` for one that
existed before; the parts about the tree are kept. -/
theorem writerWP_appendDeleteKlong_putInvTGen (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w w3 : W) (hI : PutInv c base w) (cv d' : Nat) (L : NodeId) (n : KNode)
    (hn : wNode c.p base w L = some n) (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hcascade : ∀ (compact : Bool) (s : String),
      (!compact && decide ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size >
        c.p.splitAbove)) = false → n.firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => PutInvT c base w4)) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => PutInvT c base w4) := by
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hnt := hI.times L n hn
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlsub hcascade
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hlsub hsplit hcascade
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => PutInvT c base w4) := by
    intro compact hcs s
    by_cases hnew : n.firstTime = some c.i
    · generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
      have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
      have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ (d' + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, hN4⟩
      rw [hleq] at hN4
      refine putInvT_shrink c base w w4 hI L n last hn (by rw [← hleq]) hlt hlsub
        (h4t.trans hr3'.2.2.1) (h4top.trans hr3'.2.1) (by rw [hN4]; simp) ?_
      intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rw [hr3'.1]
    · exact hcascade compact s hcs hnew
  -- the bitmap in L: a node that loses live klongs only
  have hshrink : ∀ (n' : KNode) (s : String), n'.leaf = n.leaf →
      (∀ t, Klong.time t ∈ n'.ks → t ≤ c.i) → (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 => PutInvT c base w4) := by
    intro n' s hl' ht' hsub
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine putInvT_shrink c base w _ hI L n n' hn hl' ht' ?_ hr3.2.2.1 hr3.2.1 ?_ ?_
    · intro c' z hz
      have h1 : (c', z) ∈ n'.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i ht']; exact hz
      have := hsub c' z h1
      rwa [KNode.liveAt_of_times _ c.i hnt] at this
    · simp only [wNode, hr3.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hy
      rw [← hr3.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro old hold c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z, (c', z) ∈ (n.add c.i (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  have haddt := KNode.add_times n c.i (.del U) (fun s h => by cases h) hnt
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => PutInvT c base w4) := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => PutInvT c base w4) := by
      intro hnTD
      by_cases hsz : n.size + 1 < c.p.M
      · rw [if_pos hsz]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · rw [if_pos hd]; exact htime true _ (by simp)
        · rw [if_neg hd]; exact hshrink _ _ (KNode.add_leaf _ _ _) haddt hadd
      · rw [if_neg hsz]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit hnTD h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt')
        | true =>
          simp only [hg, hlt', Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · rw [if_pos hd]; exact htime true _ (by simp)
          · rw [if_neg hd]
            exact hshrink _ _ (KNode.setAt_leaf _ _ _) (KNode.setAt_last_del_times n c.i old _ hg hnt)
              (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- A delete of a key whose access path from the segment root rk ends with g,
q, L (`PathFrom`), by a bitmap in the segment leaf L, which keeps a live klong,
the merges off, keeps `PutInv` (the writer's tree after it given): with room
for the bitmap, or L time split, in place for a leaf the transaction made, else
its inner parent q, full, time split too, below the grandparent g with room
(the rule of latest's `writerWP_del_timeSplit2`). -/
theorem putInv_del_timeSplit2 (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hne, hkeep, hsplit⟩ := hleaf
  obtain ⟨hqfull, hqfirst, hqsplit⟩ := hparent
  obtain ⟨hroomg, hdeadg⟩ := hgp
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqt := hI.times q qn hNq
  have hgt := hI.times _ gn hNg
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  apply writerWP_del_path c base hB.coherent pre cv rk w S0 kq k1 q L n qn gn hrk ht hI.ids.1
    hI.ids.2.1 hI.wf hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  generalize hgdef : pathEnd rk S0 = g at *
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqtk : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hNq).1
  have hgtk : w.taken.contains g = false := (wNode_cases _ _ _ _ _ hNg).1
  have hLlt := hI.lt_next L n hNL
  have hqlt := hI.lt_next q qn hNq
  have hglt := hI.lt_next g gn hNg
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_putInvTGen c base hB.coherent w w3 hI cv (d'' + 1)
    L n hNL hr3 hlk3 hne hsplit ?_) ?_
  · intro compact s hcs hnew
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hny : w3'.nodes.lookup w3'.next = none := by
      cases h' : w3'.nodes.lookup w3'.next with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hny2 : w3'.nodes.lookup (w3'.next + 2) = none := by
      cases h' : w3'.nodes.lookup (w3'.next + 2) with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
    generalize hlast : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
      at hcs hleq hlt hlsub
    refine writerWP_mono (writerWP_handleFullWith_delTimeSplit2 d'' L q g n qn gn kq k1 last
      compact c w3' hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hnew hqfirst hcs
      (by rw [hnext3']; exact hqfull) hqsplit hpg' hpq' hpk' hroomg hdeadg hny hny2
      (by rw [hnext3']; exact hLlt)) ?_
    intro _ w4 ⟨lq, hq_leaf, _, hq_times, hq_look, h4t, h4top, _, h4nodes⟩
    rw [hnext3', hleq] at h4nodes
    rw [hnext3'] at hq_look
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hyLt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
    have hyqt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
    have hlq_eq : (⟨qn.leaf, lq.ks⟩ : KNode) = lq := by
      cases lq with
      | mk lf ks => simp only at hq_leaf; rw [hq_leaf]
    have e1 : w.next ≠ L := by omega
    have e2 : w.next ≠ q := by omega
    have e3 : w.next ≠ g := by omega
    have e4 : w.next + 2 ≠ L := by omega
    have e5 : w.next + 2 ≠ q := by omega
    have e6 : w.next + 2 ≠ g := by omega
    have e7 : w.next + 2 ≠ w.next := by omega
    refine putInvT_timeSplit2 c base w w4 hI cv k1 kq (w.next + 2 + 2) w.next (w.next + 2) L q g
      n qn gn last lq (by omega) (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) hNL hnl
      hNq hql hNg hgl hrg hkqg hk1L htk (h4top.trans hr3'.2.1) ?_ ?_ (by rw [hq_leaf]; exact hql)
      hq_times (live_of_lookup' lq qn k1 w.next hq_look) ?_ (by rw [← hleq]; exact hnl) hlt
      (fun c' z h => Or.inr (hlsub c' z h)) ?_
      (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1L)
    · simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq]
    · simp only [wNode, htk, hyqt, Bool.false_eq_true, ↓reduceIte, h4nodes, e4, e5, e6, e7, hlq_eq]
    · simp only [wNode, htk, hyLt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2, e3]
    · intro x hxL hxq hxg hxyL hxyq
      rw [← hr3'.1]
      simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxyL, hxyq, ↓reduceIte]
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

/-- A delete of a key whose access path from the segment root rk ends with g,
q, L (`PathFrom`), by a bitmap in the segment leaf L, which keeps a live klong,
the merges off, keeps `PutInv` (the writer's tree after it given): with room
for the bitmap, or L time split, in place for a leaf the transaction made, else
its inner parent q, full by its size with more than h klongs in its last
version and at least two live, space split, below the grandparent g with room
for two klongs (the rule of latest's `writerWP_del_timeSpace`, with its
premise on the range of q's compare values in g). -/
theorem putInv_del_timeSpace (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : c.p.M < qn.size + 1 + 1 ∧ qn.firstTime ≠ some c.i ∧
      c.p.splitAbove < (qn.lastVersion c.i).size ∧ 2 ≤ qn.live.length)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hne, hkeep, hsplit⟩ := hleaf
  obtain ⟨hqfull, hqfirst, hqsplit, hq2⟩ := hparent
  obtain ⟨hroomg, hdeadg⟩ := hgp
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  have hqt := hI.times q qn hNq
  have hgt := hI.times _ gn hNg
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  apply writerWP_del_path c base hB.coherent pre cv rk w S0 kq k1 q L n qn gn hrk ht hI.ids.1
    hI.ids.2.1 hI.wf hpath hNL hnl hNq hNg
  intro d'' w3 hr3 hlk3 hlq3 hlg3 hsrc3 hpg hpq hpk hvisL hqv hgv
  generalize hgdef : pathEnd rk S0 = g at *
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hgtk : w.taken.contains g = false := (wNode_cases _ _ _ _ _ hNg).1
  have hLlt := hI.lt_next L n hNL
  have hqlt := hI.lt_next q qn hNq
  have hglt := hI.lt_next g gn hNg
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_putInvTGen c base hB.coherent w w3 hI cv (d'' + 1)
    L n hNL hr3 hlk3 hne hsplit ?_) ?_
  · intro compact s hcs hnew
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hlg3' : w3'.nodes.lookup g = some gn := by rw [← hw3']; exact hlg3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpg' : (w3'.path[d'']?).map (·.2) = some g := by rw [← hw3']; exact hpg
    have hpq' : w3'.path[d'' + 1]? = some (some kq, q) := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d'' + 1 + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hfree : ∀ z, w3'.next ≤ z → w3'.nodes.lookup z = none := by
      intro z hz
      cases h' : w3'.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
    generalize hlast : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
      at hcs hleq hlt hlsub
    refine writerWP_mono (writerWP_handleFullWith_delTimeSpace d'' L q g n qn gn kq k1 last
      compact c w3' hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hnew hqfirst hcs hqfull hqsplit hpg' hpq'
      hpk' hroomg hdeadg (hfree _ (Nat.le_refl _)) (hfree _ (by omega)) (hfree _ (by omega))
      (by rw [hnext3']; exact hLlt)) ?_
    intro _ w4 ⟨h4t, h4top, _, h4nodes⟩
    rw [hnext3', hleq] at h4nodes
    have hqlive : qn.live ≠ [] := by intro he; rw [he] at hq2; simp at hq2
    obtain ⟨r0, hr0⟩ := live_ne_nil_head qn hqlive
    have hsc0 := divider_pos qn.live (KNode.live_order qn) hq2 r0 hr0
    obtain ⟨hsc, hf1, hf2⟩ := halves_inner_live qn c.i k1 w.next hql r0 hr0 hsc0
    have hfl := halves_leaf_flags qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]
    have hht := halves_times qn.leaf qn c.i [(k1, w.next)]
    generalize hout : halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)] = out at *
    rw [hql] at hfl
    rw [hsc] at h4nodes
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hyLt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
    have hQ1t : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
    have hQ2t : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
    have e1 : w.next ≠ L := by omega
    have e2 : w.next ≠ q := by omega
    have e3 : w.next ≠ g := by omega
    have e4 : w.next + 2 ≠ L := by omega
    have e5 : w.next + 2 ≠ q := by omega
    have e6 : w.next + 2 ≠ g := by omega
    have e7 : w.next + 2 ≠ w.next := by omega
    have e8 : w.next + 2 + 2 ≠ L := by omega
    have e9 : w.next + 2 + 2 ≠ q := by omega
    have e10 : w.next + 2 + 2 ≠ g := by omega
    have e11 : w.next + 2 + 2 ≠ w.next := by omega
    have e12 : w.next + 2 + 2 ≠ w.next + 2 := by omega
    refine putInvT_timeSpace c base w w4 hI cv r0.1 k1 kq (w.next + 2 + 2 + 2) w.next (w.next + 2)
      (w.next + 2 + 2) L q g n qn gn last out.1 out.2.1 (by omega) (Nat.le_refl _) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hNL hnl hNq hql
      hNg hgl hrg hkqg hk1L hrangeq (divider_mem qn r0 hr0) hsc0 htk (h4top.trans hr3'.2.1) ?_ ?_
      (by rw [← hleq]; exact hnl) hlt (fun c' z h => Or.inr (hlsub c' z h)) ?_ hfl.1
      hht.1 hf1 ?_ hfl.2 hht.2 hf2 ?_
      (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1L)
    · simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq]
    · simp only [wNode, htk, hyLt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2, e3]
    · simp only [wNode, htk, hQ1t, Bool.false_eq_true, ↓reduceIte, h4nodes, e4, e5, e6, e7]
    · simp only [wNode, htk, hQ2t, Bool.false_eq_true, ↓reduceIte, h4nodes, e8, e9, e10, e11, e12]
    · intro x hxL hxq hxg hxyL hxQ1 hxQ2
      rw [← hr3'.1]
      simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxyL, hxQ1, hxQ2, ↓reduceIte]
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

end SIS.Tree
