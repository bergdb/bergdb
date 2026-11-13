import SIS.Tree.PutInvDelCascade
import SIS.Tree.PutInvSpaceSpace
import SIS.Tree.PutInvDelSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete whose full leaf is space split and whose full
inner parent splits too (bergdb 024-12, TP10; latest's `writerWP_del_spaceTime`
and `writerWP_del_spaceSpace`): the leaf, full by its size, which existed before
the transaction, is replaced by the two halves of its last version without the
key's klong, and its parent is time split or space split below a grandparent
with room. The parts about the tree follow from the put cascades'
`putInvT_spaceSplitTime` and `putInvT_spaceSpace`, with an unused fresh id for
the put's value: the halves hold only live klongs of the old leaf. -/

set_option linter.unusedSimpArgs false in
/-- A delete's bitmap in the leaf L, full by its size, with no bitmap of the
transaction last: the state after it is one that the leaf's split from a state
that reads as w3 reaches (`hspace`, for any note). -/
theorem writerWP_appendDeleteKlong_spaceGenP (c : Ctx) (w3 : W) (P : W → Prop) (cv d' : Nat)
    (L : NodeId) (n : KNode) (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hnTD : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i))
    (hfull : c.p.M ≤ n.size + 1)
    (hspace : ∀ s : String, WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => P w4)) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => P w4) := by
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hspace
  generalize hlast : n.lastVersionGivenDel c.i U = last at hspace
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have hrest : WriterWP (if n.size + 1 < c.p.M then
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
          pure false) c w3 (fun _ w4 => P w4) := by
      have hsz : ¬ n.size + 1 < c.p.M := by omega
      simp only [hsz, ↓reduceIte, note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (hspace _) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    cases hg : n.ks.getLast? with
    | none =>
      simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest
        | true =>
          exact absurd ⟨⟨old, hg⟩, by simpa using hlt'⟩ hnTD
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest

/-- A delete of a key whose access path from the segment root rk ends with g,
q, L (`PathFrom`), by a bitmap in the segment leaf L, which keeps a live klong,
full by its size, with no bitmap of the transaction last, existing before the
transaction, whose last version without the key has more than h klongs, the
merges off, keeps `PutInv` (the writer's tree after it given): L is space split
and its inner parent q, full with the two klongs, is time split, below the
grandparent g with room (the rule of latest's `writerWP_del_spaceTime`). -/
theorem putInv_del_spaceTime (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1 ∧
      c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
      n.firstTime ≠ some c.i)
    (hparent : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)))
          []).2.2 (w.next + 2))) = false) ∧
      qn.firstTime ≠ some c.i ∧
      (c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
    (hgp : gn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hne, hkeep, hnTD, hfull, hsp, hfirst⟩ := hleaf
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
  refine writerWP_mono (writerWP_appendDeleteKlong_spaceGenP c w3 (fun w4 => PutInvT c base w4) cv
    (d'' + 1) L n hlk3 hne hnTD hfull ?_) ?_
  · intro s
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
    refine writerWP_mono (writerWP_handleFullWith_delSpaceTime d'' L q g n qn gn kq k1 _ c w3'
      hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hfirst hqfirst hsp (by rw [hnext3']; exact hqfull) hqsplit
      hpg' hpq' hpk' hroomg hdeadg (hfree _ (Nat.le_refl _)) (hfree _ (by omega))
      (hfree _ (by omega))) ?_
    intro _ w4 ⟨lq, hlql, _, hlqt, hlqk, h4t, h4top, _, h4nodes⟩
    rw [hnext3'] at h4nodes hlqk
    obtain ⟨sc, hsc, hscm, hfh, hsh⟩ := halves_del_live n c.i cv hnl (by omega)
    have hflat := KNode.lastVersionGivenDel_flatAt n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
    have hfl := halves_leaf_flags n.leaf c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
    have hhf := halves_flatAt n.leaf c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] (FlatAt.flat c.i _ hflat)
    rw [hnl] at hfl hhf hfh hsh hsc h4nodes hlqk
    generalize hout : halves true c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] = out at *
    have hft := flatAt_times c.i _ hhf.1
    have hst := flatAt_times c.i _ hhf.2
    rw [hsc] at hlqk
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hFt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
    have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
    have hyt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
    have hlq_eq : (⟨qn.leaf, lq.ks⟩ : KNode) = lq := by
      cases lq with
      | mk lf ks => simp only at hlql; rw [hlql]
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
    -- the time split parent's live klongs
    have hlqlive : ∀ c' z, (c', z) ∈ lq.live → (c' = sc ∧ z = w.next + 2) ∨
        (c' = k1 ∧ z = w.next) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live) := by
      intro c' z hz
      have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup lq) c' z hz
      rw [hlqk c'] at hl
      simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hl
      by_cases h1 : sc = c'
      · simp only [h1, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
        exact Or.inl ⟨h1.symm, hl.symm⟩
      · have hb1 : (sc == c') = false := by simpa using h1
        simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hl
        by_cases h2 : k1 = c'
        · simp only [h2, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
          exact Or.inr (Or.inl ⟨h2.symm, hl.symm⟩)
        · have hb2 : (k1 == c') = false := by simpa using h2
          simp only [hb2, Bool.false_eq_true, ↓reduceIte] at hl
          exact Or.inr (Or.inr ⟨fun h => h2 h.symm, lookup_some_mem hl⟩)
    refine putInvT_spaceSplitTime c base w w4 hI cv sc k1 kq (w.next + 2 + 2 + 2) w.next (w.next + 2)
      (w.next + 2 + 2) L q g n qn gn out.1 out.2.1 lq (by omega) (Nat.le_refl _) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hNL hnl hNq hql
      hNg hgl hrg hkqg hk1L htk (h4top.trans hr3'.2.1) ?_ ?_ (by rw [hlql]; exact hql) hlqt hlqlive
      ?_ ?_ hfl.1 hfl.2 hft hst (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h))
      hscm ?_ (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1L)
    · simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq]
    · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h4nodes, e8, e9, e10, e11, e12,
        hlq_eq]
    · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2, e3]
    · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e4, e5, e6, e7]
    · intro x hxL hxq hxg hxF hxS hxyq
      rw [← hr3'.1]
      simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxF, hxS, hxyq, ↓reduceIte]
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

/-- A delete of a key whose access path from the segment root rk ends with g,
q, L (`PathFrom`), by a bitmap in the segment leaf L, which keeps a live klong,
full by its size, with no bitmap of the transaction last, existing before the
transaction, whose last version without the key has more than h klongs, the
merges off, keeps `PutInv` (the writer's tree after it given): L is space split
and its inner parent q, full by its size with the two klongs, existing before
the transaction, with more than h klongs in its last version and at least two
live, is space split too, below the grandparent g with room for two klongs (the
rule of latest's `writerWP_del_spaceSpace`, with its premise on the range of
q's compare values in g). -/
theorem putInv_del_spaceSpace (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1 ∧
      c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
      n.firstTime ≠ some c.i)
    (hparent : c.p.M < qn.size + 2 + 1 ∧ qn.firstTime ≠ some c.i ∧
      c.p.splitAbove < (qn.lastVersion c.i).size ∧ 2 ≤ qn.live.length)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hne, hkeep, hnTD, hfull, hsp, hfirst⟩ := hleaf
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
  refine writerWP_mono (writerWP_appendDeleteKlong_spaceGenP c w3 (fun w4 => PutInvT c base w4) cv
    (d'' + 1) L n hlk3 hne hnTD hfull ?_) ?_
  · intro s
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
    refine writerWP_mono (writerWP_handleFullWith_delSpaceSpace d'' L q g n qn gn kq k1 _ c w3'
      hlk3' hlq3' hlg3' hqL hgq hgL hql hgl hfirst hqfirst hsp hqfull hqsplit hpg' hpq' hpk' hroomg
      hdeadg (hfree _ (Nat.le_refl _)) (hfree _ (by omega)) (hfree _ (by omega))
      (hfree _ (by omega))) ?_
    intro _ w4 ⟨h4t, h4top, _, h4nodes⟩
    rw [hnext3'] at h4nodes
    have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hrq hNq hql hNL hnl hk1L
    -- the leaf's halves
    obtain ⟨sc, hsc, hscm, hfh, hsh⟩ := halves_del_live n c.i cv hnl (by omega)
    have hflat := KNode.lastVersionGivenDel_flatAt n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
    have hfl := halves_leaf_flags n.leaf c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
    have hhf := halves_flatAt n.leaf c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] (FlatAt.flat c.i _ hflat)
    rw [hnl] at hfl hhf hfh hsh hsc h4nodes
    generalize hout : halves true c.i
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] = out at *
    have hft := flatAt_times c.i _ hhf.1
    have hst := flatAt_times c.i _ hhf.2
    rw [hsc] at h4nodes
    have hks : k1 ≤ sc := by obtain ⟨zs, hzs⟩ := hscm; exact (hold sc zs hzs).1
    -- the parent's halves
    have hqlive : qn.live ≠ [] := by intro he; rw [he] at hq2; simp at hq2
    obtain ⟨rq, hrq0⟩ := live_ne_nil_head qn hqlive
    have hsq0 := divider_pos qn.live (KNode.live_order qn) hq2 rq hrq0
    have hside : decide (rq.1 ≤ sc) = decide (rq.1 ≤ k1) := by
      by_cases h1 : rq.1 ≤ k1
      · have h2 : rq.1 ≤ sc := by omega
        simp [h1, h2]
      · have hrqm : (rq.1, rq.2) ∈ qn.live := List.mem_of_mem_drop (List.mem_of_mem_head? hrq0)
        obtain ⟨zs, hzs⟩ := hscm
        have := (hold sc zs hzs).2 rq.1 rq.2 hrqm (by omega)
        have h2 : ¬ rq.1 ≤ sc := by omega
        simp [h1, h2]
    obtain ⟨hscq, hf1, hf2⟩ := halves_inner_live2 qn c.i k1 sc w.next (w.next + 2) hql hks
      rq hrq0 hsq0 hside
    have hfl2 := halves_leaf_flags qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next), (sc, w.next + 2)]
    have hht2 := halves_times qn.leaf qn c.i [(k1, w.next), (sc, w.next + 2)]
    generalize hout2 : halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next), (sc, w.next + 2)]
      = out2 at *
    rw [hql] at hfl2
    rw [hscq] at h4nodes
    have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
    have hFt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
    have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
    have hQ1t : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
    have hQ2t : w.taken.contains (w.next + 2 + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
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
    have e13 : w.next + 2 + 2 + 2 ≠ L := by omega
    have e14 : w.next + 2 + 2 + 2 ≠ q := by omega
    have e15 : w.next + 2 + 2 + 2 ≠ g := by omega
    have e16 : w.next + 2 + 2 + 2 ≠ w.next := by omega
    have e17 : w.next + 2 + 2 + 2 ≠ w.next + 2 := by omega
    have e18 : w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 := by omega
    refine putInvT_spaceSpace c base w w4 hI cv sc k1 kq rq.1 (w.next + 2 + 2 + 2 + 2) w.next
      (w.next + 2) (w.next + 2 + 2) (w.next + 2 + 2 + 2) L q g n qn gn out.1 out.2.1 out2.1 out2.2.1
      (by omega) (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hNL hnl hNq hql hNg hgl hrg hkqg hk1L hrangeq (divider_mem qn rq hrq0) hsq0 htk
      (h4top.trans hr3'.2.1) ?_ ?_ ?_ hfl.1 hfl.2 hft hst (fun c' z h => Or.inr (hfh c' z h))
      (fun c' z h => Or.inr (hsh c' z h)) hscm ?_ hfl2.1 hht2.1 hf1 ?_ hfl2.2 hht2.2 hf2 ?_
      (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1L)
    · simp only [wNode, htk, hgtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hgL, hgq]
    · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2, e3]
    · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e4, e5, e6, e7]
    · simp only [wNode, htk, hQ1t, Bool.false_eq_true, ↓reduceIte, h4nodes, e8, e9, e10, e11, e12]
    · simp only [wNode, htk, hQ2t, Bool.false_eq_true, ↓reduceIte, h4nodes, e13, e14, e15, e16, e17,
        e18]
    · intro x hxL hxq hxg hxF hxS hxQ1 hxQ2
      rw [← hr3'.1]
      simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxg, hxF, hxS, hxQ1, hxQ2, ↓reduceIte]
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

end SIS.Tree
