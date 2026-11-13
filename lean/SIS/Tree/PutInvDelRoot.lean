import SIS.Tree.PutInvSpaceSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by every delete of a key of one segment in a space whose root
is a leaf (bergdb 024-12, TP10), the merges off: no value, a bitmap with room,
the root kept empty (the upward delete's first case), the root full by its
size or its dead klongs split in time or in space, in place for a root the
transaction made (`putInv_del_leafRoot`). -/

/-! ## The space root's splits with nothing to insert (a delete) -/

/-- The state after a space split of the space root L with nothing to insert
and the last version `last`: the halves at the next two ids under a new root
at the id after them, which the super root names; L keeps its klongs before. -/
def RootSpaceSplitNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = w.next then some (halves n.leaf c.i last []).1
      else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
        .key (halves n.leaf c.i last []).2.2 (w.next + 2)]⟩
      else w.nodes.lookup x

/-- The state after a time split of the space root L with the last version
`last`: a new root at the next id holds it. -/
def RootTimeSplitNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = w.next then some ⟨n.leaf, last.ks⟩ else w.nodes.lookup x

/-- The state after a space split in place of the space root L with nothing to
insert: L the first half, the next id the second, the id after the new root. -/
def RootSpaceSplitInPlaceNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (halves n.leaf c.i last []).1
      else if x = w.next then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 then some ⟨false, [.time c.i, .key 0 L,
        .key (halves n.leaf c.i last []).2.2 w.next]⟩
      else w.nodes.lookup x

theorem writerWP_handleFullWith_rootSpaceSplit_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitNilAfter c w w' L n last) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  have hL3 : L ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        refine ⟨rfl, rfl, ?_⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL; simp
        · simp only [hxL, ↓reduceIte]
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

theorem writerWP_handleFullWith_rootTimeSplit_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      RootTimeSplitNilAfter c w w' L n last) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨rfl, rfl, ?_⟩
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

theorem writerWP_handleFullWith_rootSpaceSplitInPlace_nil
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitInPlaceNilAfter c w w' L n last) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine ⟨rfl, rfl, ?_⟩
            intro x
            simp only [lookup_upsert, List.lookup_append]
            by_cases hxL : x = L
            · subst hxL; simp [hL1, hL2]
            · simp only [hxL, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                by_cases h2 : x = w.next + 2
                · subst h2
                  rw [show w.nodes.lookup (w.next + 2) = none from hny]
                  have hb : (w.next + 2 == w.next) = false := by simp
                  simp [List.lookup, hb]
                · simp only [h2, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                      ([(w.next + 2, _)].lookup x)) = none
                    rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl

/-- A delete's bitmap in the space root L, a leaf: with room, the root loses
live klongs; full by its size or by its dead klongs, it is split, in time or
in space, in place for a root the transaction made; the parts about the tree
are kept. -/
theorem writerWP_appendDeleteKlong_root_putInvT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w w3 : W) (hI : PutInv c base w) (cv : Nat) (n : KNode)
    (hn : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hr3 : ReadsAs c.p base w w3) (hlk3 : w3.nodes.lookup w.top.rootKey = some n)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) (hsa : 1 ≤ c.p.splitAbove) :
    WriterWP (appendDeleteKlong w.top.rootKey 0 cv) c w3 (fun _ w4 => PutInvT c base w4) := by
  generalize hLdef : w.top.rootKey = L at hn hlk3 ⊢
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hnt := hI.times L n hn
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hLn := hI.lt_next L n hn
  have hflat := KNode.lastVersionGivenDel_flatAt n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  have hfree : ∀ z, w3.next ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := hsrc3 _ (by rw [h']; rfl); omega
  -- the outcomes on any state that reads as w3, its trail aside
  have hout : ∀ (w5 : W), w5.nodes = w3.nodes → w5.taken = w3.taken → w5.top = w3.top →
      w5.next = w3.next → ReadsAs c.p base w w5 →
      (∀ (compact : Bool), (!compact && decide
          ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size > c.p.splitAbove)) = false →
        WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L []
          (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact) c w5
          (fun _ w4 => PutInvT c base w4)) ∧
      (c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size →
        WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L []
          (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c w5
          (fun _ w4 => PutInvT c base w4)) := by
    intro w5 h5n h5t h5top h5next hr5
    have hlk5 : w5.nodes.lookup L = some n := by rw [h5n]; exact hlk3
    have hfree5 : ∀ z, w5.next ≤ z → w5.nodes.lookup z = none := by
      intro z hz; rw [h5n]; exact hfree z (by omega)
    have hL5t : w5.taken.contains L = false := by rw [hr5.2.2.1]; exact hLt
    obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
    have hrk : w.top.rootKey = L := hLdef
    refine ⟨?_, ?_⟩
    · intro compact hcs
      by_cases hnew : n.firstTime = some c.i
      · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ 0 L n _ compact c base hvc w5
          hlk5 hL5t hnew hcs) ?_
        intro _ w4 ⟨h4t, h4top, hN4⟩
        rw [hleq] at hN4
        refine putInvT_shrink c base w w4 hI L n _ hn (by rw [← hleq]) hlt hlsub
          (h4t.trans hr5.2.2.1) (h4top.trans hr5.2.1) (by rw [hN4]; simp) ?_
        intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rw [hr5.1]
      · refine writerWP_mono (writerWP_handleFullWith_rootTimeSplit_nil _ L n _ compact c w5 hlk5 hnew
          hcs (by omega) (hfree5 _ (Nat.le_refl _))) ?_
        intro _ w4 ⟨h4t, h4rk, h4nodes⟩
        rw [h5next, hnext3, hleq] at h4nodes
        rw [h5next, hnext3] at h4rk
        have htk : w4.taken = w.taken := h4t.trans hr5.2.2.1
        have hyt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
        have hLy : L ≠ w.next := by omega
        rw [← hrk] at hn
        refine putInvT_rootTimeSplit c base w w4 hI cv (w.next + 2) w.next n _ (by omega)
          (Nat.le_refl _) (by omega) hn htk h4rk ?_ (by rw [← hleq]; exact hnl) hlt
          (fun c' z h => Or.inr (hlsub c' z h)) ?_
        · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm]
        · intro x hxL hxy
          rw [hrk] at hxL
          rw [← hr5.1]
          simp only [wNode, htk, hr5.2.2.1, h4nodes, hxL, hxy, ↓reduceIte]
    · intro hsp
      obtain ⟨sc, hsc, hscm, hfh, hsh⟩ := halves_del_live n c.i cv hnl (by omega)
      have hfl := halves_leaf_flags n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
      have hhf := halves_flatAt n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []
        (FlatAt.flat c.i _ hflat)
      have hft := flatAt_times c.i _ hhf.1
      have hst := flatAt_times c.i _ hhf.2
      have hfl1 : (halves n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []).1.leaf
          = true := by rw [hfl.1]; exact hnl
      have hfl2 : (halves n.leaf c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.1.leaf
          = true := by rw [hfl.2]; exact hnl
      have hrk : w.top.rootKey = L := hLdef
      rw [← hrk] at hn
      by_cases hnew : n.firstTime = some c.i
      · have h := writerWP_handleFullWith_rootSpaceSplitInPlace_nil
          (fun _ _ => throw "corrupt: a split's parent above depth 0") L n _ c w5 hlk5 hnew hsp (by omega)
          (hfree5 _ (by omega))
        refine writerWP_mono h ?_
        intro _ w4 ⟨h4t, h4rk, h4nodes⟩
        rw [h5next, hnext3, hsc] at h4nodes
        rw [h5next, hnext3] at h4rk
        have htk : w4.taken = w.taken := h4t.trans hr5.2.2.1
        have hSt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
        have hRt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
        have e1 : w.next ≠ L := by omega
        have e2 : w.next + 2 ≠ L := by omega
        have e3 : w.next + 2 ≠ w.next := by omega
        refine putInvT_rootSpaceSplit c base w w4 hI cv sc (w.next + 4) w.top.rootKey w.next (w.next + 2)
          n _ _ (by omega) (Nat.le_refl _) (by omega) (Or.inr rfl) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) hn htk h4rk ?_ ?_ ?_ hfl1 hfl2 hft hst
          (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h)) ?_
        · rw [hrk]
          simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h4nodes, e2, e3, newKlongs,
            List.map]
        · rw [hrk]
          simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes]
        · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1]
        · intro x hxL _ hxS hxR
          rw [hrk] at hxL
          rw [← hr5.1]
          simp only [wNode, htk, hr5.2.2.1, h4nodes, hxL, hxS, hxR, ↓reduceIte]
      · have h := writerWP_handleFullWith_rootSpaceSplit_nil
          (fun _ _ => throw "corrupt: a split's parent above depth 0") L n _ c w5 hlk5 hnew hsp (by omega)
        refine writerWP_mono h ?_
        intro _ w4 ⟨h4t, h4rk, h4nodes⟩
        rw [h5next, hnext3, hsc] at h4nodes
        rw [h5next, hnext3] at h4rk
        have htk : w4.taken = w.taken := h4t.trans hr5.2.2.1
        have hFt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
        have hSt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
        have hRt : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
        have e1 : w.next ≠ L := by omega
        have e2 : w.next + 2 ≠ L := by omega
        have e3 : w.next + 2 + 2 ≠ L := by omega
        have e4 : w.next + 2 ≠ w.next := by omega
        have e5 : w.next + 2 + 2 ≠ w.next := by omega
        have e6 : w.next + 2 + 2 ≠ w.next + 2 := by omega
        refine putInvT_rootSpaceSplit c base w w4 hI cv sc (w.next + 6) w.next (w.next + 2)
          (w.next + 2 + 2) n _ _ (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hn htk h4rk ?_ ?_ ?_
          hfl1 hfl2 hft hst (fun c' z h => Or.inr (hfh c' z h)) (fun c' z h => Or.inr (hsh c' z h)) ?_
        · simp only [wNode, htk, hRt, Bool.false_eq_true, ↓reduceIte, h4nodes, e3, e5, e6, newKlongs,
            List.map]
        · simp only [wNode, htk, hFt, Bool.false_eq_true, ↓reduceIte, h4nodes, e1]
        · simp only [wNode, htk, hSt, Bool.false_eq_true, ↓reduceIte, h4nodes, e2, e4]
        · intro x hxL hxF hxS hxR
          rw [hrk] at hxL
          rw [← hr5.1]
          simp only [wNode, htk, hr5.2.2.1, h4nodes, hxL, hxF, hxS, hxR, ↓reduceIte]
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
  have hw5 : ∀ s : String, ({ w3 with trail := s :: w3.trail } : W).nodes = w3.nodes ∧
      ({ w3 with trail := s :: w3.trail } : W).taken = w3.taken ∧
      ({ w3 with trail := s :: w3.trail } : W).top = w3.top ∧
      ({ w3 with trail := s :: w3.trail } : W).next = w3.next ∧
      ReadsAs c.p base w ({ w3 with trail := s :: w3.trail } : W) :=
    fun s => ⟨rfl, rfl, rfl, rfl, hr3⟩
  have htime : ∀ (compact : Bool) (s : String), (!compact && decide
      ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size > c.p.splitAbove)) = false →
      WriterWP (do note s; handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L [] (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) compact; pure false)
        c w3 (fun _ w4 => PutInvT c base w4) := by
    intro compact s hcs
    simp only [note, writerWP_bind, writerWP_modify]
    obtain ⟨a1, a2, a3, a4, a5⟩ := hw5 s
    exact writerWP_mono ((hout _ a1 a2 a3 a4 a5).1 compact hcs)
      (fun _ w4 h => by simp only [writerWP_pure]; exact h)
  have hspace : ∀ (s : String),
      c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size →
      WriterWP (do note s; handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L [] (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false; pure false)
        c w3 (fun _ w4 => PutInvT c base w4) := by
    intro s hsp
    simp only [note, writerWP_bind, writerWP_modify]
    obtain ⟨a1, a2, a3, a4, a5⟩ := hw5 s
    exact writerWP_mono ((hout _ a1 a2 a3 a4 a5).2 hsp)
      (fun _ w4 h => by simp only [writerWP_pure]; exact h)
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun old hold c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z,
      (c', z) ∈ (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  have haddt := KNode.add_times n c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))
    (fun s h => by cases h) hnt
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have hrest : WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = true then do
            note "bitmap.dead"
            handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L [] (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv))))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 L [] (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)))
          pure false) c w3 (fun _ w4 => PutInvT c base w4) := by
      by_cases hsz : n.size + 1 < c.p.M
      · rw [if_pos hsz]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = true
        · rw [if_pos hd]; exact htime true _ (by simp)
        · rw [if_neg hd]; exact hshrink _ _ (KNode.add_leaf _ _ _) haddt hadd
      · rw [if_neg hsz]
        by_cases hsp : c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size
        · exact hspace _ hsp
        · apply htime false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
          omega
    cases hg : n.ks.getLast? with
    | none =>
      simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest
        | true =>
          simp only [hg, hlt, Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = true
          · rw [if_pos hd]; exact htime true _ (by simp)
          · rw [if_neg hd]
            exact hshrink _ _ (KNode.setAt_leaf _ _ _) (KNode.setAt_last_del_times n c.i old _ hg hnt)
              (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest

/-- Every delete of a key of one segment in a space whose root is a leaf, the
merges off, keeps `PutInv` (the writer's tree after it given): a key without a
value; a bitmap with room; the root emptied and kept (the upward delete's
first case); the root full by its size or by its dead klongs, split in time or
in space, in place for a root the transaction made. -/
theorem putInv_del_leafRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true) :
    WriterWP (putKv (.del [cv])) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hvc := hB.coherent
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn' hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  have hlk3' : w3.nodes.lookup w.top.rootKey = some n := by simpa using hlk3
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rw [hw2n] at h1; exact hI.ids.1 z h1
    · exact hI.ids.2.1 z h1
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen]
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c _ hlk3']
  by_cases hnoop : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
  · have hb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by rw [hnoop]; simp
    simp only [hb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
    exact putInvT_of_readsAs c base w w3 hI hr03
  · have hb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hnoop
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    -- the continuation after the bitmap: the merges off, the marker's id
    have hcont : ∀ (w4 : W), PutInvT c base w4 →
        WriterWP fresh c w4 (fun _ w5 => PutInvT c base w5) := by
      intro w4 h4
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact h4
    cases hk : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, writerWP_bind]
      refine writerWP_ghOf_cached _ n c _ hlk3' _ (fun gh => ?_)
      refine writerWP_mono (writerWP_appendDeleteKlong_root_putInvT c base hvc w w3 hI cv n hroot hnl
        hr03 hlk3' hsrcw3 hnoop hsa) ?_
      intro _ w4 h4
      unfold afterDelete
      simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte,
        writerWP_pure, Bool.not_false]
      exact hcont w4 h4
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      unfold climb pathNode
      simp only [writerWP_bind, writerWP_read, writerWP_get]
      rw [show w3.path[0]? = some (none, w.top.rootKey) by rw [hp3, hp2]; rfl]
      simp only [writerWP_pure]
      rw [writerWP_getNode_known _ n c _ hlk3']
      simp only [hnl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure, beq_self_eq_true,
        note, writerWP_modify, writerWP_bind]
      refine writerWP_mono (writerWP_appendDeleteKlong_root_putInvT c base hvc w _ hI cv n hroot hnl
        hr03 hlk3' hsrcw3 hnoop hsa) ?_
      intro _ w4 h4
      simp only [writerWP_pure, Bool.not_false, ↓reduceIte, writerWP_bind]
      exact hcont w4 h4

end SIS.Tree
