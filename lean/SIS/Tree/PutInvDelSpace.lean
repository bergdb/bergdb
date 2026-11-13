import SIS.Tree.PutInvTimeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete into a full segment leaf whose last version
without the key has more than h klongs (bergdb 024-12, TP10): the space split
of the leaf, with nothing to insert (in place for a leaf the transaction made),
below an inner parent with room for two klongs, the merges off. With
`putInv_del_leafBelow`'s time splits: every delete by a bitmap into a segment
leaf that keeps a live klong, below an inner parent with room
(`putInv_del_leafBelow2`). -/

theorem writerWP_handleFullWith_spaceSplit_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last false) c w
      (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧ ∀ x, w'.nodes.lookup x =
        if x = L then some (n.toPrev (c.i - 1))
        else if x = q then some ((qn.add c.i (.key k1 w.next)).add c.i
          (.key (halves n.leaf c.i last []).2.2 (w.next + 2)))
        else if x = w.next then some (halves n.leaf c.i last []).1
        else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_room2 d' q qn k1 w.next _ (w.next + 2) c _
        (by
          simp only [lookup_upsert]
          have h1 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
          have h2 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
          simp [h1, h2, List.lookup_append, hlq]) hroomq (hdeadq _ _ _)) ?_
      intro _ w2 hw2
      subst hw2
      rw [writerWP_getNode_known L n c _ (by
        simp only [lookup_upsert]
        have h1 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
        have h2 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
        simp [hqL.symm, h1, h2, List.lookup_append, hlk])]
      simp only [putNode, writerWP_modify]
      refine ⟨trivial, trivial, ?_⟩
      intro x
      simp only [lookup_upsert, List.lookup_append]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hx2 : x = w.next + 2
          · have hx1 : x ≠ w.next := by omega
            simp [hx2]
          · simp only [hx2, ↓reduceIte]
            by_cases hx1 : x = w.next
            · simp [hx1]
            · simp only [hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                have hb1 : (x == w.next) = false := by simpa using hx1
                have hb2 : (x == w.next + 2) = false := by simpa using hx2
                simp [List.lookup, hb1, hb2])

theorem writerWP_handleFullWith_spaceSplitInPlace_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M)
    (hdeadq : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last false) c w
      (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧ ∀ x, w'.nodes.lookup x =
        if x = L then some (halves n.leaf c.i last []).1
        else if x = q then some (qn.add c.i (.key (halves n.leaf c.i last []).2.2 w.next))
        else if x = w.next then some (halves n.leaf c.i last []).2.1
        else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hq2 : q ≠ w.next := by omega
    have hL2 : L ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_modify, writerWP_pure]
        refine writerWP_mono (writerWP_appendKlongs_room d' q qn _ w.next c _ ?_ hroomq
          (hdeadq _ _)) ?_
        · simp only [lookup_upsert, List.lookup_append, hq2, hqL, ↓reduceIte, hlq]
          rfl
        intro _ w2 hw2
        subst hw2
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
        refine ⟨trivial, trivial, ?_⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL
          simp [hqL.symm, hL2]
        · by_cases hxq : x = q
          · subst hxq
            simp [hxL]
          · by_cases hx1 : x = w.next
            · subst hx1
              simp [hxL, hxq]
            · simp only [hxL, hxq, hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hx1]; rfl


/-- The halves of a leaf's last version without the key's klong: the first
holds live klongs of the leaf below the divider sc, a live compare value of the
leaf, the second those at or above it. -/
theorem halves_del_live (n : KNode) (t : Time) (cv : Nat) (hl : n.leaf = true)
    (hpos : 0 < (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).size - 1) :
    ∃ sc, (halves n.leaf t (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.2 = sc ∧
      (∃ zs, (sc, zs) ∈ n.live) ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t
        (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).1.liveAt t →
        (c, z) ∈ n.live ∧ c < sc) ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t
        (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.1.liveAt t →
        (c, z) ∈ n.live ∧ sc ≤ c) := by
  obtain ⟨_, _, hlsub⟩ := delLast_facts n t cv
  generalize hlast : n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv)) = last at hlsub hpos ⊢
  obtain ⟨pairs, hks, hs⟩ := n.lastVersionGivenDel_order t (bitsUnion n.lastBitmap (n.bitsOf cv))
  rw [hlast] at hks
  have hlleaf : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlast' : last = ⟨true, newKlongs t pairs⟩ := by
    cases last with
    | mk lf ks => simp only at hks hlleaf; rw [hks, hlleaf, hl]; rfl
  have hn : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr (hs.imp (by intro a b hab; omega))
  have hlen : 0 < pairs.length := by
    rw [hlast'] at hpos; simp [KNode.size, newKlongs] at hpos; omega
  obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
    cases hd : (pairs.drop (pairs.length / 2)).head? with
    | some r => exact ⟨r, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      omega
  have hmemlive : ∀ c z, (c, z) ∈ pairs → (c, z) ∈ n.live := by
    intro c z hm
    apply hlsub
    have h1 := lookup_of_mem_nodup _ hn c z hm
    have h2 : last.live.lookup c = some z := by
      rw [hlast', KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c hn, h1]
    exact lookup_some_mem h2
  have hshape := halves_shape true t pairs [] r hr
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hshape
  rw [hl, hlast', hshape]
  have hleft := halves_left_lt_divider pairs (pairs.length / 2) hs r hr
  have hright := halves_right_ge_divider pairs (pairs.length / 2) hs r hr
  refine ⟨r.1, rfl, ⟨r.2, hmemlive r.1 r.2 (List.mem_of_mem_drop (List.mem_of_mem_head? hr))⟩, ?_, ?_⟩
  · intro c z hm
    have hm' := liveAt_newKlongs_mem true t t _ c z hm
    exact ⟨hmemlive c z (List.mem_of_mem_take hm'), hleft (c, z) hm'⟩
  · intro c z hm
    have hm' := liveAt_newKlongs_mem true t t _ c z hm
    simp only [secondSplitPairs, ↓reduceIte] at hm'
    exact ⟨hmemlive c z (List.mem_of_mem_drop hm'), hright (c, z) hm'⟩

theorem writerWP_appendDeleteKlong_putInvT2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w w3 : W) (hI : PutInv c base w) (cv k1 d' : Nat) (rk L q : NodeId) (n qn : KNode)
    (hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hLrk : L ≠ rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqv : (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false) (hk1 : (k1, L) ∈ qn.liveAt c.i)
    (hqL : q ≠ L) (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsa : 1 ≤ c.p.splitAbove)
    (hroomq2 : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq2 : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hdeadq1 : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => PutInvT c base w4) := by
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hnt := hI.times L n hn
  have hnwf := hI.wf L n hn
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hroomq : qn.size + 1 + 1 ≤ c.p.M := by omega
  have hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false := fun y => hdeadq1 k1 y
  have hLn := hI.lt_next L n hn
  have hqnx := hI.lt_next q qn hqn
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hpar := parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l
  have hqtm := hI.times q qn hqn
  have hqwf := hI.wf q qn hqn
  have hLt0 : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt0 : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hflat := KNode.lastVersionGivenDel_flatAt n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  -- the space split of the full leaf, from a state that reads as w3 but for the trail
  have hspace0 : c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => PutInvT c base w4) := by
    intro hsp s
    obtain ⟨sc, hsc, hscm, hfh, hsh⟩ := halves_del_live n c.i cv hnl (by omega)
    have hfl := halves_leaf_flags n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
    have hhf := halves_flatAt n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
      (FlatAt.flat c.i _ hflat)
    rw [hnl] at hfl hhf hfh hsh hsc
    generalize hout : halves true c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] = out at *
    have hft := flatAt_times c.i _ hhf.1
    have hst := flatAt_times c.i _ hhf.2
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpq' : (w3'.path[d']?).map (·.2) = some q := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d' + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    have hfree : ∀ z, w3'.next ≤ z → w3'.nodes.lookup z = none := by
      intro z hz
      cases h' : w3'.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
    have hFt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
    have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
    by_cases hnew : n.firstTime = some c.i
    · have hsp' : c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size := hsp
      have h := writerWP_handleFullWith_spaceSplitInPlace_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) c w3' hlk3' hlq3' hqL hql
        hnew hsp' hpq' hroomq (fun k y => hdeadq1 k y) (by omega) (by omega)
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hsc] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have e1 : w.next ≠ L := by omega
      have e2 : w.next ≠ q := by omega
      refine putInvT_spaceSplit c base w w4 hI cv k1 sc (w.next + 2) L w.next L q n qn out.1 out.2.1
        (by omega) (Nat.le_refl _) (by omega) (Or.inr rfl) (by omega) (by omega) hn hnl hqn hql hrq
        hk1l htk (h4top.trans hr3'.2.1) (qn.add c.i (.key sc w.next)) ?_ (by rw [KNode.add_leaf]; exact hql)
        (KNode.add_times _ c.i _ (fun s h => by cases h) hqtm) ?_ ?_ ?_ hfl.1 hfl.2 hft hst
        (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h)) hscm ?_ hpar
      · simp only [wNode, htk, hqt0, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · intro c' z h
        rcases KNode.add_key_liveAt_mem qn c.i _ _ hqwf hqtm c' z h with h1 | ⟨hne, h1⟩
        · exact Or.inl h1
        · by_cases hck : c' = k1
          · subst hck
            have hnd := KNode.live_keys_nodup qn
            rw [KNode.liveAt_of_times qn c.i hqtm] at h1
            have h2 := lookup_of_mem_nodup _ hnd _ _ h1
            rw [lookup_of_mem_nodup _ hnd _ _ hk1l] at h2
            cases h2
            exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨hck, h1⟩)
      · simp only [wNode, htk, hLt0, Bool.false_eq_true, ↓reduceIte, h4nodes]
      · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2]
      · intro x hxL hxq _ hxS
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxS, ↓reduceIte]
    · have h := writerWP_handleFullWith_spaceSplit_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) k1 c w3' hlk3' hlq3' hqL hql
        hnew hsp hpq' hpk' hroomq2 (fun y1 sc y2 => hdeadq2 y1 sc y2) (hfree _ (Nat.le_refl _))
        (hfree _ (by omega))
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hsc] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have e1 : w.next ≠ L := by omega
      have e2 : w.next ≠ q := by omega
      have e3 : w.next + 2 ≠ L := by omega
      have e4 : w.next + 2 ≠ q := by omega
      have e5 : w.next + 2 ≠ w.next := by omega
      have hq1wf := KNode.add_key_wf qn c.i k1 w.next hqwf
      have hq1t := KNode.add_times qn c.i (.key k1 w.next) (fun s h => by cases h) hqtm
      refine putInvT_spaceSplit c base w w4 hI cv k1 sc (w.next + 4) w.next (w.next + 2) L q n qn
        out.1 out.2.1 (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _)) (by omega) (by omega)
        hn hnl hqn hql hrq hk1l htk (h4top.trans hr3'.2.1)
        ((qn.add c.i (.key k1 w.next)).add c.i (.key sc (w.next + 2))) ?_
        (by rw [KNode.add_leaf, KNode.add_leaf]; exact hql)
        (KNode.add_times _ c.i _ (fun s h => by cases h) hq1t) ?_ ?_ ?_ hfl.1 hfl.2 hft hst
        (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h)) hscm ?_ hpar
      · simp only [wNode, htk, hqt0, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · intro c' z h
        rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with h1 | ⟨_, h1⟩
        · exact Or.inl h1
        · rcases KNode.add_key_liveAt_mem qn c.i k1 _ hqwf hqtm c' z h1 with h2 | h2
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr h2)
      · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2]
      · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e3, e4, e5]
      · intro x hxL hxq hxF hxS
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxF, hxS, ↓reduceIte]
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hleq hlt hlsub hspace0
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hlsub hspace0
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => PutInvT c base w4) := by
    intro compact hcs s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpq' : (w3'.path[d']?).map (·.2) = some q := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d' + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ (d' + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, hN4⟩
      rw [hleq] at hN4
      refine putInvT_shrink c base w w4 hI L n last hn (by rw [← hleq]) hlt hlsub
        (h4t.trans hr3'.2.2.1) (h4top.trans hr3'.2.1) (by rw [hN4]; simp) ?_
      intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rw [hr3'.1]
    · have hny : w3'.nodes.lookup w3'.next = none := by
        cases h' : w3'.nodes.lookup w3'.next with
        | none => rfl
        | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
      refine writerWP_mono (writerWP_handleFullWith_timeSplit_nil d' L q n qn last k1 compact c w3'
        hlk3' hlq3' hqL hql hnew hcs hpq' hpk' hroomq hdeadq hny) ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hleq] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hyt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
      have hLy : L ≠ w.next := by have := hI.lt_next L n hn; omega
      have hqy : q ≠ w.next := by have := hI.lt_next q qn hqn; omega
      refine putInvT_timeSplit c base w w4 hI cv k1 (w.next + 2) w.next L q n qn last (by omega)
        (Nat.le_refl _) (by omega) hn hnl hqn hql hrq hk1l htk (h4top.trans hr3'.2.1) ?_ ?_ ?_
        (by rw [← hleq]; exact hnl) hlt (fun c' z h => Or.inr (hlsub c' z h)) ?_
        (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
      · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes]
      · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm, hqy.symm]
      · intro x hxL hxq hxy
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxy, ↓reduceIte]
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
      intro _
      by_cases hsz : n.size + 1 < c.p.M
      · rw [if_pos hsz]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · rw [if_pos hd]; exact htime true _ (by simp)
        · rw [if_neg hd]; exact hshrink _ _ (KNode.add_leaf _ _ _) haddt hadd
      · rw [if_neg hsz]
        by_cases hsp : c.p.splitAbove < last.size
        · simp only [note, writerWP_bind, writerWP_modify]
          exact writerWP_mono (hspace0 hsp _) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
        · apply htime false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
          omega
    cases hg : n.ks.getLast? with
    | none =>
      simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt)
        | true =>
          simp only [hg, hlt, Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · rw [if_pos hd]; exact htime true _ (by simp)
          · rw [if_neg hd]
            exact hshrink _ _ (KNode.setAt_leaf _ _ _) (KNode.setAt_last_del_times n c.i old _ hg hnt)
              (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)


/-- Every delete of a key whose prefix is there, below an inner segment root
and inner nodes with room for two klongs, by a bitmap in its segment leaf,
which keeps a live klong, the merges off, keeps `PutInv` (the writer's tree
after it given): with room for the bitmap, or the leaf full by its size or by
its dead klongs, time split or space split, in place for a leaf the
transaction made. -/
theorem putInv_del_leafBelow2 (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  apply writerWP_del_seg_leaf c base hB.coherent pre cv rk w hrk ht hI.ids.1 hI.ids.2.1 hinner
  intro L n q qn k1 d' w3 hL hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk _
  obtain ⟨hne, hkeep⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq2, hdeadq2, hdeadq1⟩ := hparent q qn hqv hqn hql
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_putInvT2 c base hB.coherent w w3 hI cv k1 d' rk L
    q n qn hrrk hL hLrk hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk hne hsa hroomq2
    (fun y1 sc y2 => hdeadq2 k1 y1 sc y2) hdeadq1) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

end SIS.Tree
