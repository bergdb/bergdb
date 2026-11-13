import SIS.Tree.PutInvUp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete into a segment root that is a leaf below the
segment leaf of the segment before, which keeps a live klong (bergdb 024-12,
TP10), the merges off: the bitmap with room, or the root full by its size or by
its dead klongs, split in time or into a new segment root in space, in place
for a root the transaction made (`putInv_del_segRoot`). -/

/-! ## A segment root's splits with nothing to insert (a delete) -/

/-- `SegSpaceSplitAfter` with nothing to insert and the last version `last`. -/
def SegSpaceSplitNilAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn last : KNode) (k1 : Nat) :
    Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.add c.i (.key k1 (w.next + 2 + 2)))
      else if x = w.next then some (halves n.leaf c.i last []).1
      else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
        .key (halves n.leaf c.i last []).2.2 (w.next + 2)]⟩
      else w.nodes.lookup x

/-- `SegSpaceSplitInPlaceAfter` with nothing to insert and the last version
`last`. -/
def SegSpaceSplitInPlaceNilAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn last : KNode) (k1 : Nat) :
    Prop :=
  ∃ j, qn.linkIndex L k1 = some j ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (halves n.leaf c.i last []).1
      else if x = q then some (qn.repoint j (w.next + 2))
      else if x = w.next then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 then some ⟨false, [.time c.i, .key 0 L,
        .key (halves n.leaf c.i last []).2.2 w.next]⟩
      else w.nodes.lookup x

theorem writerWP_handleFullWith_timeSplitLeafParent_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact) c w
      (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = q then some (qn.add c.i (.key k1 w.next))
          else if x = w.next then some ⟨n.leaf, last.ks⟩
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
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ w2 : W, w2.taken = w.taken → w2.top = w.top →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := last.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
            ∀ x, w'.nodes.lookup x =
              if x = L then some (n.toPrev (c.i - 1))
              else if x = q then some (qn.add c.i (.key k1 w.next))
              else if x = w.next then some ⟨n.leaf, last.ks⟩
              else w.nodes.lookup x) := by
      intro w2 h2t h2top h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert, if_neg (fun h => hqL h.symm), List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, ?_⟩
      intro x
      rw [lookup_upsert, h2n, lookup_upsert]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte, List.lookup_append]
          by_cases hxy : x = w.next
          · subst hxy; rw [hny]; simp [List.lookup]
          · simp only [hxy, ↓reduceIte]
            cases h : w.nodes.lookup x with
            | some m => rfl
            | none =>
              show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := last.ks })].lookup x) = none
              rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl

theorem writerWP_handleFullWith_segSpaceSplit_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M)
    (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last false) c w
      (fun _ w' => SegSpaceSplitNilAfter c w w' L q n qn last k1) := by
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
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hq1 : q ≠ w.next := by omega
    have hq2 : q ≠ w.next + 2 := by omega
    have hq3 : q ≠ w.next + 2 + 2 := by omega
    have hL1 : L ≠ w.next := by omega
    have hL2 : L ≠ w.next + 2 := by omega
    have hL3 : L ≠ w.next + 2 + 2 := by omega
    simp only [newKey, fresh, setMadeFor, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_klongAt (d' + 1) k1 L c _ ?_ _).mpr ?_
        · exact hpk
        refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 (w.next + 2 + 2) c _
          ?_ hroomq (hdeadq _)) ?_
        · simp only [lookup_upsert, List.lookup_append, hq1, hq2, hq3, ↓reduceIte, hlq]
          rfl
        intro _ w2 hw2
        subst hw2
        simp only [Bool.not_false, ↓reduceIte, writerWP_bind]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hqL.symm, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        refine ⟨rfl, rfl, ?_⟩
        intro x
        show (upsert _ L _).lookup x = _
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · subst hxq; simp [hxL]
          · simp only [hxq, ↓reduceIte]
            by_cases h3 : x = w.next + 2 + 2
            · subst h3
              simp [show w.next + 2 + 2 ≠ w.next by omega]
            · simp only [h3, ↓reduceIte]
              by_cases h2 : x = w.next + 2
              · subst h2; simp
              · simp only [h2, ↓reduceIte]
                by_cases h1 : x = w.next
                · subst h1; simp
                · simp only [h1, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                      ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup x)).or
                      ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup x) = none
                    rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl

/-! ## The rule: a space split of a segment root below a segment leaf -/

theorem writerWP_handleFullWith_segSpaceSplitInPlace_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hLn : L < w.next) (hqn : q < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last false) c w
      (fun _ w' => SegSpaceSplitInPlaceNilAfter c w w' L q n qn last k1) := by
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
    have hq1 : q ≠ w.next := by omega
    have hq2 : q ≠ w.next + 2 := by omega
    have hL1 : L ≠ w.next := by omega
    have hL2 : L ≠ w.next + 2 := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
            refine (writerWP_klongAt (d' + 1) k1 L c _ ?_ _).mpr ?_
            · exact hpk
            refine (writerWP_getNode_known q qn c _ ?_ _).mpr ?_
            · simp only [lookup_upsert, List.lookup_append, hq1, hq2, hqL, ↓reduceIte, hlq]
              rfl
            split
            · rename_i j hj
              split
              · simp only [writerWP_bind]
                exact writerWP_throw _ _ _ _
              · simp only [writerWP_bind, writerWP_modify, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, writerWP_pure]
                refine ⟨j, hj, rfl, rfl, ?_⟩
                intro x
                simp only [lookup_upsert, List.lookup_append]
                by_cases hxL : x = L
                · subst hxL; simp [hqL.symm, hL1, hL2]
                · simp only [hxL, ↓reduceIte]
                  by_cases hxq : x = q
                  · simp [hxq]
                  · simp only [hxq, ↓reduceIte]
                    by_cases h1 : x = w.next
                    · subst h1; simp
                    · simp only [h1, ↓reduceIte]
                      by_cases h2 : x = w.next + 2
                      · subst h2
                        rw [hny]
                        have hb : (w.next + 2 == w.next) = false := by simp
                        simp [List.lookup, hb]
                      · simp only [h2, ↓reduceIte]
                        cases h : w.nodes.lookup x with
                        | some m => rfl
                        | none =>
                          show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                            ([(w.next + 2, _)].lookup x)) = none
                          rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl
            · exact writerWP_throw _ _ _ _

theorem writerWP_appendDeleteKlong_seg_putInvT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w w3 : W) (hI : PutInv c base w) (cv k1 d' : Nat) (L q : NodeId) (n qn : KNode)
    (hrq0 : ReachS (wNode c.p base w) c.i w.top.rootKey q)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = true) (hk1 : (k1, L) ∈ qn.liveAt c.i)
    (hqL : q ≠ L) (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsa : 1 ≤ c.p.splitAbove)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => PutInvT c base w4) := by
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hnt := hI.times L n hn
  have hnwf := hI.wf L n hn
  have hrq := hrq0
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hLn := hI.lt_next L n hn
  have hqnx := hI.lt_next q qn hqn
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
    · have hny : w3'.nodes.lookup (w3'.next + 2) = none := hfree _ (by omega)
      have h := writerWP_handleFullWith_segSpaceSplitInPlace_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) k1 c w3' hlk3' hlq3' hqL hql
        hnew hsp hpq' hpk' (by omega) (by omega) hny
      unfold SegSpaceSplitInPlaceNilAfter at h
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨j, hj, h4t, h4top, h4nodes⟩
      rw [hnext3', hsc] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hRt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
      have e1 : w.next ≠ L := by omega
      have e2 : w.next ≠ q := by omega
      have e3 : w.next + 2 ≠ L := by omega
      have e4 : w.next + 2 ≠ q := by omega
      have e5 : w.next + 2 ≠ w.next := by omega
      have hrt : ∀ s, Klong.time s ∈ (qn.repoint j (w.next + 2)).ks → s ≤ c.i :=
        fun s hs => hqtm s (repoint_time_mem qn j _ s hs)
      have hrl : (qn.repoint j (w.next + 2)).leaf = qn.leaf := by
        unfold KNode.repoint; split <;> rfl
      refine putInvT_segSpaceSplit c base w w4 hI cv sc k1 (w.next + 4) L w.next (w.next + 2) L q n qn
        (qn.repoint j (w.next + 2)) out.1 out.2.1 (by omega) (Nat.le_refl _) (by omega) (Or.inr rfl)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hn hqn hql hrq hk1l hqL htk
        (h4top.trans hr3'.2.1) ?_ (by rw [hrl]; exact hql) hrt ?_ ?_ ?_ ?_ hfl.1 hfl.2 hft hst
        (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h)) ?_
      · simp only [wNode, htk, hqt0, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · intro c' z hz
        rw [KNode.liveAt_of_times _ c.i hrt] at hz
        have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hz
        rw [KNode.repoint_live_lookup qn L _ k1 j hj c'] at hl
        by_cases hc : k1 = c'
        · subst hc
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl
          exact Or.inl ⟨rfl, hl.symm⟩
        · have hb : (k1 == c') = false := by simpa using hc
          rw [hb] at hl
          simp only [Bool.false_eq_true, ↓reduceIte] at hl
          refine Or.inr ⟨fun he => hc he.symm, ?_⟩
          rw [KNode.liveAt_of_times qn c.i hqtm]
          exact lookup_some_mem hl
      · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h4nodes, e3, e4, e5, newKlongs,
          List.map]
      · simp only [wNode, htk, hLt0, Bool.false_eq_true, ↓reduceIte, h4nodes]
      · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2]
      · intro x hxL hxq _ hxS hxR
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxS, hxR, ↓reduceIte]
    · have h := writerWP_handleFullWith_segSpaceSplit_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) k1 c w3' hlk3' hlq3' hqL hql
        hnew hsp hpq' hpk' hroomq hdeadq (by omega) (by omega)
      unfold SegSpaceSplitNilAfter at h
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hsc] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hRt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
      have e1 : w.next ≠ L := by omega
      have e2 : w.next ≠ q := by omega
      have e3 : w.next + 2 ≠ L := by omega
      have e4 : w.next + 2 ≠ q := by omega
      have e5 : w.next + 2 ≠ w.next := by omega
      have e6 : w.next + 2 + 2 ≠ L := by omega
      have e7 : w.next + 2 + 2 ≠ q := by omega
      have e8 : w.next + 2 + 2 ≠ w.next := by omega
      have e9 : w.next + 2 + 2 ≠ w.next + 2 := by omega
      refine putInvT_segSpaceSplit c base w w4 hI cv sc k1 (w.next + 6) w.next (w.next + 2)
        (w.next + 2 + 2) L q n qn (qn.add c.i (.key k1 (w.next + 2 + 2))) out.1 out.2.1 (by omega)
        (by omega) (by omega) (Or.inl (Nat.le_refl _)) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hn hqn hql hrq hk1l hqL htk (h4top.trans hr3'.2.1) ?_
        (by rw [KNode.add_leaf]; exact hql) (KNode.add_times _ c.i _ (fun s h => by cases h) hqtm)
        ?_ ?_ ?_ ?_ hfl.1 hfl.2 hft hst (fun c' z h => Or.inr (hfh c' z h))
        (fun c' z h => Or.inr (hsh c' z h)) ?_
      · simp only [wNode, htk, hqt0, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · intro c' z h
        exact KNode.add_key_liveAt_mem qn c.i k1 _ hqwf hqtm c' z h
      · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h4nodes, e6, e7, e8, e9, newKlongs,
          List.map]
      · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1, e2]
      · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e3, e4, e5]
      · intro x hxL hxq hxF hxS hxR
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxF, hxS, hxR, ↓reduceIte]
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
      refine writerWP_mono (writerWP_handleFullWith_timeSplitLeafParent_nil d' L q n qn last k1 compact c
        w3' hlk3' hlq3' hqL hql hnew hcs hpq' hpk' hroomq hdeadq hny) ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hleq] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hyt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
      have hLy : L ≠ w.next := by have := hI.lt_next L n hn; omega
      have hqy : q ≠ w.next := by have := hI.lt_next q qn hqn; omega
      refine putInvT_timeSplitLeaf c base w w4 hI cv k1 (w.next + 2) w.next L q n qn last (by omega)
        (Nat.le_refl _) (by omega) hn hqn hql hrq hk1l hqL htk (h4top.trans hr3'.2.1) ?_ ?_
        (by rw [← hleq]; exact hnl) hlt (fun c' z h => Or.inr (hlsub c' z h)) ?_
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



/-- Every delete of a key whose last segment's tree is one leaf L below the
segment leaf of the segment before, with room for a klong there, L keeping a
live klong, the merges off, keeps `PutInv` (the writer's tree after it given):
no value, a bitmap with room, or L full by its size or by its dead klongs split
in time or into a new segment root in space, in place for a root the
transaction made. -/
theorem putInv_del_segRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.del (pre0 ++ [k1, cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  have hvc := hB.coherent
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_del_segRoot_leaf c base hvc pre0 k1 cv rq L n w hrq ht hI.ids.1 hI.ids.2.1 hL hNL hnl
    (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 hlk5 hlq5 hsrc5 hr5 hpq hpk _
  obtain ⟨hroomq, hdeadq⟩ := hseg q qn hqv hqn hql
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  simp only [writerWP_bind]
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w5 hlk5]
  by_cases hnoop : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
  · have hb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by rw [hnoop]; simp
    simp only [hb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
    exact putInvT_of_readsAs c base w w5 hI hr5
  · have hb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hnoop
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false, writerWP_bind]
    refine writerWP_ghOf_cached L n c w5 hlk5 _ (fun gh => ?_)
    refine writerWP_mono (writerWP_appendDeleteKlong_seg_putInvT c base hvc w w5 hI cv k1 d' L q n qn
      hrq' hNL hnl hqn hql hk1 hqL hr5 hlk5 hlq5 hsrc5 hpq hpk hnoop hsa hroomq hdeadq) ?_
    intro _ w4 h4
    unfold afterDelete fresh
    simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure,
      Bool.not_false, writerWP_get, writerWP_set]
    exact h4

end SIS.Tree
