/-
The contract package (bergdb 030-16): a merge's parent, `Dag.mergeParent`
(bergdb 024-11, M4). The parent q, at `depth` of the key access path, has the
live klongs (cL, l) (klong il) and (cR, r) (klong ir), adjacent; the merge made
m1, and maybe m2 with its first compare value g. Then cL's klong names m1;
cR's is deleted, or names m2 (g = cR), or m2 gets a klong of g and cR is
deleted (`mergeTarget`). A bitmap comes before any new klong; the
transaction's own bitmap gets the bits in place; a klong of the transaction is
pointed in place. A full node, or one with more than theta dead klongs, is
replaced by its last version with the pointers set (`handleFull`, a time or a
space split: WriterDelTime.lean, WriterDelSpace.lean).

The statement, as the bitmap's (WriterDelBitmap.lean): the caller says that the
map with q set to any node V of q's kind with the live klongs `mergeTarget`, at
most M + 3 klongs, well formed, whose key klongs name nodes that q's klongs
name or m1 or m2, is sound with q over its size, holds the keys C and meets
BalancedOK (`MergeVirt`); then the step, where it gives no error and leaves no
key node outside G and H, ends in a state that meets `PInv` and holds C.
-/
import Contract.Proof.WriterDelBitmap
import Contract.Proof.NodeAlg5

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-- The live klongs that a merge leaves in its parent, from the parent's live
klongs L. -/
def mergeTarget (L : List (Nat × NodeId)) (cL cR : Nat) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) : List (Nat × NodeId) :=
  match m2 with
  | none => insertCv cL m1 (dropCv cR L)
  | some (y, g) =>
    if g = cR then insertCv cR y (insertCv cL m1 L)
    else insertCv g y (insertCv cL m1 (dropCv cR L))

/-- What a caller of `mergeParent` gives: the map with q set to V is sound,
with q over its size, holds the keys C, and meets BalancedOK, for every V of
q's kind with the live klongs `mergeTarget`. -/
def MergeVirt (p : MParams) (i : Time) (s : Tree) (w : MW) (q : NodeId) (nq : MNode)
    (cL cR : Nat) (m1 : NodeId) (m2 : Option (NodeId × Nat)) (C : List (Key × Nat)) : Prop :=
  ∀ V : MNode, V.leaf = nq.leaf → live (ksOf V) = mergeTarget (live (ksOf nq)) cL cR m1 m2 →
    klongsWf (ksOf V) = true → V.size ≤ p.M + 3 →
    (∀ c y, Klong.key c y ∈ ksOf V →
      (∃ c', Klong.key c' y ∈ ksOf nq) ∨ y = m1 ∨ ∃ g, m2 = some (y, g)) →
    (∃ t rest, V.ks = SIS.Tree.Klong.time t :: rest) → TimesLe V i →
    Sound p.M (some q) (treeOf i s (w.withNode q V)) w.top.rootKey C ∧
      BalancedAll p (treeOf i s (w.withNode q V))

/-- Klong j of node n is the live klong of compare value c, naming y: the
last key klong of c, not deleted by the last bitmap. -/
def LiveAt (n : MNode) (j c : Nat) (y : NodeId) : Prop :=
  (ksOf n)[j]? = some (Klong.key c y) ∧ j ∉ lastBitmap (ksOf n) ∧
    ∀ j', j < j' → cvAt (ksOf n) j' ≠ some c

/-! ## 1. `mergeParent` in parts -/

/-- `deleteR`: the right child's compare value is deleted. -/
def wmp_delR (cR : Nat) (m2 : Option (NodeId × Nat)) : Bool :=
  match m2 with
  | some (_, g) => g != cR
  | none => true

/-- `after j`: klong j is after the node's last time klong. -/
def wmp_after (pn : MNode) (j : Nat) : Bool :=
  match pn.lastTimeIndex with
  | some ti => decide (ti < j)
  | none => false

/-- The bitmap of the parent: the bits of cR added if it is deleted. -/
def wmp_union (pn : MNode) (cR : Nat) (m2 : Option (NodeId × Nat)) : List Nat :=
  if wmp_delR cR m2 then SIS.Tree.bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap

/-- The parent with its bitmap. -/
def wmp_n1 (tt : Time) (pn : MNode) (cR : Nat) (m2 : Option (NodeId × Nat)) : MNode :=
  if !wmp_delR cR m2 then pn
  else if hasTransDel pn tt then pn.setAt (pn.size - 1) (.del (wmp_union pn cR m2))
  else pn.add tt (.del (wmp_union pn cR m2))

/-- Then cL's klong naming m1. -/
def wmp_n2 (tt : Time) (pn : MNode) (il cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) : MNode :=
  if (pn.lastTime == some tt && wmp_after pn il) = true then (wmp_n1 tt pn cR m2).repoint il m1
  else (wmp_n1 tt pn cR m2).add tt (.key cL m1)

/-- Then m2's klong. -/
def wmp_n3 (tt : Time) (pn : MNode) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : MNode :=
  match m2 with
  | some (y, g) =>
    if (!wmp_delR cR m2 && pn.lastTime == some tt && wmp_after pn ir) = true then
      (wmp_n2 tt pn il cL m1 cR m2).repoint ir y
    else (wmp_n2 tt pn il cL m1 cR m2).add tt (.key (if wmp_delR cR m2 then g else cR) y)
  | none => wmp_n2 tt pn il cL m1 cR m2

/-- The klongs the parent needs room for. -/
def wmp_need (tt : Time) (pn : MNode) (il ir cR : Nat) (m2 : Option (NodeId × Nat)) : Nat :=
  (if (wmp_delR cR m2 && !hasTransDel pn tt) = true then 1 else 0) +
    (if (pn.lastTime == some tt && wmp_after pn il) = true then 0 else 1) +
    (if (m2.isNone || (!wmp_delR cR m2 && pn.lastTime == some tt && wmp_after pn ir)) = true
      then 0 else 1) +
    (if (pn.lastTime == some tt) = true then 0 else 1)

/-- A full parent: its last version with the pointers set, by a split. -/
def wmp_full (q depth : Nat) (tt : Time) (pn : MNode) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (compact : Bool) : SIS.Tree.M Unit := do
  SIS.Tree.note (if compact then "merge.parent.dead" else "merge.parent.full")
  let last := pn.lastVersionGivenDel tt (wmp_union pn cR m2)
  let last ← match SIS.Tree.replaceKlong last.ks tt cL m1 with
    | .ok (some ks) => pure { last with ks := ks }
    | .ok none => throw s!"Bug: merge at {tt}: no klong of the left child in the last version \
        of {q}"
    | .error e => throw e
  let last ← match m2 with
    | some (y, g) =>
      if wmp_delR cR m2 then pure { last with ks := SIS.Tree.insertSorted last.ks g y }
      else match SIS.Tree.replaceKlong last.ks tt cR y with
        | .ok (some ks) => pure { last with ks := ks }
        | .ok none => throw s!"Bug: merge at {tt}: no klong of the right child in the last \
            version of {q}"
        | .error e => throw e
    | none => pure last
  SIS.Tree.handleFull depth q last compact

theorem wmp_eq (q depth il cL : Nat) (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    SIS.Tree.mergeParent q depth il cL m1 ir cR m2 = (do
      let c ← read
      let pn ← SIS.Tree.getNode q
      if pn.size + wmp_need c.i pn il ir cR m2 ≤ c.p.M then
        if SIS.Tree.deadOver c.p (wmp_n3 c.i pn il cL m1 ir cR m2) then
          wmp_full q depth c.i pn cL m1 cR m2 true
        else do
          SIS.Tree.note (if wmp_delR cR m2 then "merge.parent.delete" else "merge.parent.repoint")
          SIS.Tree.putNode q (wmp_n3 c.i pn il cL m1 ir cR m2)
      else wmp_full q depth c.i pn cL m1 cR m2 false) := by
  rfl


/-! ## 2. Helpers: a last version with pointers set -/

/-- The model's klongs of a node whose klongs are a time klong and key klongs. -/
theorem wmp_ks_keys {r : MNode} {t : Time} {L : List (Nat × NodeId)}
    (h : ksOf r = .time t :: L.map (fun p => Klong.key p.1 p.2)) :
    r.ks = .time t :: L.map (fun p => SIS.Tree.Klong.key p.1 p.2) := by
  apply List.map_injective_iff.mpr kOf_injective
  rw [show r.ks.map kOf = ksOf r from rfl, h]
  simp [kOf]

/-- `insertCv` of a compare value the list has: where its klong was. -/
theorem wmp_insertCv_at {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {c : Nat} {y0 : NodeId}
    (hm : (c, y0) ∈ L) (y : NodeId) :
    ∃ pre post y1, (∀ a ∈ pre, a.1 < c) ∧ (∀ b ∈ post, c < b.1) ∧
      L = pre ++ (c, y1) :: post ∧ insertCv c y L = pre ++ (c, y) :: post := by
  obtain ⟨pre, post, hpre, hpost, he, hl⟩ := insertCv_split hs c y
  rcases hl with hl | ⟨y1, hl⟩
  · exfalso
    rw [hl] at hm
    rcases List.mem_append.mp hm with h1 | h1
    · exact Nat.lt_irrefl _ (hpre _ h1)
    · exact Nat.lt_irrefl _ (hpost _ h1)
  · exact ⟨pre, post, y1, hpre, hpost, hl, he⟩

/-- `replaceKlong` in a last version of time t that has a klong of c. -/
theorem wmp_replace {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {t : Time} {c : Nat}
    {y0 : NodeId} (hm : (c, y0) ∈ L) (y : NodeId) :
    SIS.Tree.replaceKlong (.time t :: L.map (fun p => SIS.Tree.Klong.key p.1 p.2)) t c y =
      .ok (some (.time t :: (insertCv c y L).map (fun p => SIS.Tree.Klong.key p.1 p.2))) := by
  obtain ⟨pre, post, y1, hpre, -, hL, hI⟩ := wmp_insertCv_at hs hm y
  unfold SIS.Tree.replaceKlong
  rw [SIS.Tree.replaceKlong.go, hI, hL,
    go_some t c y y1 post pre _ (fun a ha => Nat.ne_of_lt (hpre a ha))]
  rfl

theorem wmp_insertSorted_keys {g : Nat} (y : NodeId) : ∀ (L : List (Nat × NodeId)),
    (∀ a ∈ L, a.1 ≠ g) →
    SIS.Tree.insertSorted (L.map (fun p => SIS.Tree.Klong.key p.1 p.2)) g y =
      (insertCv g y L).map (fun p => SIS.Tree.Klong.key p.1 p.2)
  | [], _ => rfl
  | (c', y') :: r, hg => by
    have hne : g ≠ c' := fun e => hg (c', y') List.mem_cons_self e.symm
    have ih := wmp_insertSorted_keys y r (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    by_cases hlt : g < c'
    · simp [SIS.Tree.insertSorted, insertCv, hlt]
    · simp [SIS.Tree.insertSorted, insertCv, hlt, hne, ih]

/-- `insertSorted` in a last version of a compare value it has not. -/
theorem wmp_insertSorted {L : List (Nat × NodeId)} {t : Time} {g : Nat}
    (hg : ∀ a ∈ L, a.1 ≠ g) (y : NodeId) :
    SIS.Tree.insertSorted (.time t :: L.map (fun p => SIS.Tree.Klong.key p.1 p.2)) g y =
      .time t :: (insertCv g y L).map (fun p => SIS.Tree.Klong.key p.1 p.2) := by
  rw [← wmp_insertSorted_keys y L hg]
  rfl

/-! ## 3. The parent's live klongs -/

/-- `LiveAt` in the model's klongs. -/
theorem wmp_liveAt_model {n : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y) :
    n.ks[j]? = some (.key c y) ∧ j ∉ n.lastBitmap ∧
      ∀ j' y', j < j' → n.ks[j']? ≠ some (.key c y') := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun j' y' hlt he => h3 j' hlt ?_⟩
  · rw [ksOf_getElem?] at h1
    obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp h1
    cases k with
    | key c' y' =>
      simp only [kOf, Klong.key.injEq] at hkk
      rw [hk, hkk.1, hkk.2]
    | time _ => simp [kOf] at hkk
    | del _ => simp [kOf] at hkk
  · rw [lastBitmap_ksOf] at h2
    exact h2
  · unfold cvAt
    rw [ksOf_getElem?, he]
    rfl

/-- `LiveAt` is what `linkIndex` finds. -/
theorem wmp_linkIndex {n : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y) :
    n.linkIndex y c = some j := by
  obtain ⟨hj, hD, hlast⟩ := wmp_liveAt_model h
  have hlt : j < n.ks.length := (List.getElem?_eq_some_iff.mp hj).1
  have hsplit : n.ks = n.ks.take j ++ SIS.Tree.Klong.key c y :: n.ks.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j n.ks]
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    exact (List.getElem?_eq_some_iff.mp hj).2
  have hlen : (n.ks.take j).length = j := by simp; omega
  have hfind : ∀ P : MKlong × Nat → Bool, (∀ k i, P (k, i) = match k with
      | .key c' _ => c' == c
      | _ => false) →
      n.ks.zipIdx.reverse.find? P = some (SIS.Tree.Klong.key c y, j) := by
    intro P hP
    rw [List.find?_eq_some_iff_append]
    refine ⟨by simp [hP], ((n.ks.drop (j + 1)).zipIdx (j + 1)).reverse,
      (n.ks.take j).zipIdx.reverse, ?_, ?_⟩
    · conv_lhs => rw [hsplit]
      rw [List.zipIdx_append, List.zipIdx_cons, hlen, List.reverse_append, List.reverse_cons]
      simp
    · rintro ⟨k, i⟩ ha
      rw [List.mem_reverse] at ha
      have h3 := List.mem_zipIdx ha
      rw [hP]
      cases k with
      | key c' y' =>
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
        intro hc
        subst hc
        obtain ⟨h31, h32, h33⟩ := h3
        refine hlast i y' (by omega) ?_
        have h5 : (n.ks.drop (j + 1))[i - (j + 1)]? = some (SIS.Tree.Klong.key c' y') := by
          rw [List.getElem?_eq_getElem (by omega), ← h33]
        rw [List.getElem?_drop, show j + 1 + (i - (j + 1)) = i by omega] at h5
        exact h5
      | time _ => rfl
      | del _ => rfl
  unfold SIS.Tree.KNode.linkIndex
  rw [hfind _ (fun k i => by cases k <;> rfl)]
  simp [hD]

/-- `insertCv` of a compare value the list has keeps its length. -/
theorem wmp_insertCv_length {X : List (Nat × NodeId)} (hs : X.Pairwise CvLt) {c : Nat}
    {y0 : NodeId} (hm : (c, y0) ∈ X) (y : NodeId) : (insertCv c y X).length = X.length := by
  obtain ⟨pre, post, y1, -, -, hX, hI⟩ := wmp_insertCv_at hs hm y
  rw [hI, hX]
  simp

/-- The merge's target: sorted, no longer than the parent's live klongs, of
the parent's live klongs, m1 and m2. -/
theorem wmp_target {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {cL cR : Nat}
    {l r m1 : NodeId} {m2 : Option (NodeId × Nat)} (hmL : (cL, l) ∈ L) (hmR : (cR, r) ∈ L)
    (hlr : cL < cR) :
    (mergeTarget L cL cR m1 m2).Pairwise CvLt ∧
      (mergeTarget L cL cR m1 m2).length ≤ L.length ∧
      ∀ c z, (c, z) ∈ mergeTarget L cL cR m1 m2 →
        (c, z) ∈ L ∨ z = m1 ∨ ∃ g, m2 = some (z, g) := by
  have hD := dropCv_sorted cR hs
  have hLD : (cL, l) ∈ dropCv cR L := mem_dropCv.mpr ⟨hmL, Nat.ne_of_lt hlr⟩
  have hDlen : (dropCv cR L).length + 1 ≤ L.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨(cR, r), hmR, by simp⟩
  have hmem : ∀ {c z} {X : List (Nat × NodeId)} {c' : Nat} {y' : NodeId},
      (c, z) ∈ insertCv c' y' X → (c, z) = (c', y') ∨ (c, z) ∈ X := fun h => mem_insertCv h
  cases m2 with
  | none =>
    refine ⟨insertCv_sorted _ _ hD, ?_, fun c z h => ?_⟩
    · show (insertCv cL m1 (dropCv cR L)).length ≤ L.length
      rw [wmp_insertCv_length hD hLD]
      omega
    · rcases hmem h with h1 | h1
      · exact Or.inr (Or.inl (Prod.mk.inj h1).2)
      · exact Or.inl (mem_dropCv.mp h1).1
  | some yg =>
    obtain ⟨y, g⟩ := yg
    have hsI := insertCv_sorted cL m1 hs
    have hsID := insertCv_sorted cL m1 hD
    by_cases hgc : g = cR
    · subst hgc
      have hRI : (g, r) ∈ insertCv cL m1 L :=
        (mem_insertCv_iff hs).mpr (Or.inr ⟨hmR, Nat.ne_of_gt hlr⟩)
      simp only [mergeTarget, ite_true]
      refine ⟨insertCv_sorted _ _ hsI, ?_, fun c z h => ?_⟩
      · rw [wmp_insertCv_length hsI hRI, wmp_insertCv_length hs hmL]
      · rcases hmem h with h1 | h1
        · exact Or.inr (Or.inr ⟨g, by rw [(Prod.mk.inj h1).2]⟩)
        · rcases hmem h1 with h2 | h2
          · exact Or.inr (Or.inl (Prod.mk.inj h2).2)
          · exact Or.inl h2
    · simp only [mergeTarget, hgc, ite_false]
      refine ⟨insertCv_sorted _ _ hsID, ?_, fun c z h => ?_⟩
      · have := length_insertCv g y (insertCv cL m1 (dropCv cR L))
        rw [wmp_insertCv_length hD hLD] at this
        omega
      · rcases hmem h with h1 | h1
        · exact Or.inr (Or.inr ⟨g, by rw [(Prod.mk.inj h1).2]⟩)
        · rcases hmem h1 with h2 | h2
          · exact Or.inr (Or.inl (Prod.mk.inj h2).2)
          · exact Or.inl (mem_dropCv.mp h2).1

/-! ## 4. A full parent: its last version with the pointers set -/

/-- `handleFull` of the parent's last version with the pointers set, from the
state after its `note`. -/
theorem wmp_hf {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {q : NodeId}
    {w : MW} {nq : MNode} {il cL ir cR : Nat} {l r m1 : NodeId} {m2 : Option (NodeId × Nat)}
    {C : List (Key × Nat)}
    (hlk : w.nodes.lookup q = some nq) (hon : ∃ c0, w.path[depth]? = some (c0, q))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf nq) = true) (hsize : nq.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : BalancedAll p (treeOf i s w))
    (hil : LiveAt nq il cL l) (hir : LiveAt nq ir cR r) (hlr : cL < cR)
    (hV : MergeVirt p i s w q nq cL cR m1 m2 C)
    {V : MNode} (hVl : V.leaf = nq.leaf)
    (hVks : V.ks = .time i :: (mergeTarget (live (ksOf nq)) cL cR m1 m2).map
      (fun p => SIS.Tree.Klong.key p.1 p.2)) (t : String) (compact : Bool) :
    WP (SIS.Tree.handleFull depth q V compact) { p := p, i := i, view := v }
      { w with trail := t :: w.trail }
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next) := by
  have hmL := (linkIndex_some hwf (wmp_linkIndex hil)).2.1
  have hmR := (linkIndex_some hwf (wmp_linkIndex hir)).2.1
  obtain ⟨hsT, hlenT, hmemT⟩ := wmp_target (m1 := m1) (m2 := m2) (live_sorted (ksOf nq)) hmL hmR
    hlr
  have hksV := ksOf_keys hVks
  have hliveV : live (ksOf V) = mergeTarget (live (ksOf nq)) cL cR m1 m2 := by
    rw [hksV]
    exact live_version hsT i
  have ht : w.taken.contains q = false := by
    obtain ⟨c0, hc0⟩ := hon
    exact (hpath.lookup (Nat.le_refl _) hc0).choose_spec.2
  obtain ⟨t0, rest, hr0⟩ := hbooks.timeFirst q nq hlk ht
  have hLs := live_length_size hr0
  have hVs : V.size = (mergeTarget (live (ksOf nq)) cL cR m1 m2).length + 1 := by
    rw [← ksOf_length, hksV]
    simp
  have hVt : TimesLe V i := by
    intro t' ht'
    rw [hksV] at ht'
    rcases List.mem_cons.mp ht' with h1 | h1
    · cases h1
      exact Nat.le_refl _
    · obtain ⟨_, _, h2⟩ := List.mem_map.mp h1
      cases h2
  obtain ⟨hVS, hVB⟩ := hV V hVl hliveV (by rw [hksV]; exact klongsWf_version _ _) (by omega)
    (fun c z hz => by
      rw [hksV] at hz
      simp only [List.mem_cons, reduceCtorEq, List.mem_map, false_or] at hz
      obtain ⟨⟨c1, z1⟩, hm1, he⟩ := hz
      simp only [Klong.key.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases hmemT _ _ hm1 with h1 | h1 | h1
      · exact Or.inl ⟨_, ts_live_mem_key h1⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1))
    ⟨i, _, hVks⟩ hVt
  have hpre : CasPreD p i base s tp { w with trail := t :: w.trail } depth q nq V V C :=
    ⟨hlk, hon, hpath.congr rfl rfl rfl rfl (treeOf_congr i s rfl rfl rfl rfl rfl rfl), hin,
      putBooks_congr hbooks rfl rfl rfl rfl rfl rfl rfl rfl rfl, hwf, hsize, hroot, hframe, htop,
      hbal, hVl, hVl, by rw [hliveV]; exact hksV, hVS, hVB, ⟨i, _, hVks⟩, hVt⟩
  have hpost : ∀ (u : Unit) (w' : MW),
      CasPostD p i base s tp { w with trail := t :: w.trail } depth q V C u w' →
      w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next := by
    intro u w' h ho
    obtain ⟨h1, h2⟩ := h ho
    exact ⟨h1, h2.path, h2.next⟩
  cases compact with
  | true =>
    exact (handleFullD_time hp hb hpre (Or.inl ⟨rfl, by rw [hliveV]; omega⟩)).mono hpost
  | false =>
    by_cases hh : V.size ≤ p.splitAbove
    · exact (handleFullD_time hp hb hpre (Or.inr ⟨rfl, hh⟩)).mono hpost
    · exact (handleFullD_space hp hb hpre (by omega)).mono hpost

/-- A full parent (`full`): its last version with the pointers set, by a
split. -/
theorem wmp_full_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {q : NodeId}
    {w : MW} {nq : MNode} {il cL ir cR : Nat} {l r m1 : NodeId} {m2 : Option (NodeId × Nat)}
    {C : List (Key × Nat)}
    (hlk : w.nodes.lookup q = some nq) (hon : ∃ c0, w.path[depth]? = some (c0, q))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf nq) = true) (hsize : nq.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : BalancedAll p (treeOf i s w))
    (hil : LiveAt nq il cL l) (hir : LiveAt nq ir cR r) (hlr : cL < cR)
    (hV : MergeVirt p i s w q nq cL cR m1 m2 C)
    (hadj : ∀ c y, (c, y) ∈ live (ksOf nq) → c ≤ cL ∨ cR ≤ c)
    (hg : ∀ y g, m2 = some (y, g) → cL < g ∧
      ∀ c z, (c, z) ∈ live (ksOf nq) → cR < c → g < c) (compact : Bool) :
    WP (wmp_full q depth i nq cL m1 cR m2 compact) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next) := by
  have hmL := (linkIndex_some hwf (wmp_linkIndex hil)).2.1
  have hmR := (linkIndex_some hwf (wmp_linkIndex hir)).2.1
  have hL := live_sorted (ksOf nq)
  have hLD : (cL, l) ∈ dropCv cR (live (ksOf nq)) := mem_dropCv.mpr ⟨hmL, Nat.ne_of_lt hlr⟩
  unfold wmp_full
  refine wput_ok (note_eq _ _ _) ?_
  cases m2 with
  | none =>
    have h0 : (nq.lastVersionGivenDel i (wmp_union nq cR none)).ks =
        .time i :: (dropCv cR (live (ksOf nq))).map (fun p => SIS.Tree.Klong.key p.1 p.2) :=
      wmp_ks_keys (lastVersionGivenDel_union nq i cR)
    dsimp only
    rw [h0, wmp_replace (dropCv_sorted cR hL) hLD m1]
    dsimp only
    refine wput_ok rfl (wput_ok rfl ?_)
    refine wmp_hf (v := v) hp hb hlk hon hpath hin hbooks hwf hsize hroot hframe htop hbal hil hir
      hlr hV ?_ ?_ _ compact
    · rfl
    · rfl
  | some yg =>
    obtain ⟨y, g⟩ := yg
    by_cases hgc : g = cR
    · subst hgc
      have h0 : (nq.lastVersionGivenDel i (wmp_union nq g (some (y, g)))).ks =
          .time i :: (live (ksOf nq)).map (fun p => SIS.Tree.Klong.key p.1 p.2) :=
        wmp_ks_keys (by
          rw [show wmp_union nq g (some (y, g)) = nq.lastBitmap by simp [wmp_union, wmp_delR]]
          exact lastVersion_ks i)
      have hRI : (g, r) ∈ insertCv cL m1 (live (ksOf nq)) :=
        (mem_insertCv_iff hL).mpr (Or.inr ⟨hmR, Nat.ne_of_gt hlr⟩)
      dsimp only
      rw [h0, wmp_replace hL hmL m1]
      dsimp only
      refine wput_ok rfl ?_
      simp only [wmp_delR, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [wmp_replace (insertCv_sorted cL m1 hL) hRI y]
      dsimp only
      refine wput_ok rfl ?_
      refine wmp_hf (v := v) hp hb hlk hon hpath hin hbooks hwf hsize hroot hframe htop hbal hil
        hir hlr hV ?_ ?_ _ compact
      · rfl
      · simp [mergeTarget]
    · have h0 : (nq.lastVersionGivenDel i (wmp_union nq cR (some (y, g)))).ks =
          .time i :: (dropCv cR (live (ksOf nq))).map (fun p => SIS.Tree.Klong.key p.1 p.2) := by
        refine wmp_ks_keys ?_
        rw [show wmp_union nq cR (some (y, g)) = delUnion nq cR by
          simp [wmp_union, wmp_delR, hgc, delUnion]]
        exact lastVersionGivenDel_union nq i cR
      obtain ⟨hgl, hgr⟩ := hg y g rfl
      have hnot : ∀ a ∈ insertCv cL m1 (dropCv cR (live (ksOf nq))), a.1 ≠ g := by
        intro a ha
        rcases mem_insertCv ha with h1 | h1
        · rw [h1]
          exact Nat.ne_of_lt hgl
        · obtain ⟨h2, h3⟩ := mem_dropCv.mp h1
          rcases hadj a.1 a.2 h2 with h4 | h4
          · omega
          · have := hgr a.1 a.2 h2 (by omega)
            omega
      dsimp only
      rw [h0, wmp_replace (dropCv_sorted cR hL) hLD m1]
      dsimp only
      refine wput_ok rfl ?_
      simp only [wmp_delR, hgc, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [wmp_insertSorted hnot y]
      refine wput_ok rfl ?_
      refine wmp_hf (v := v) hp hb hlk hon hpath hin hbooks hwf hsize hroot hframe htop hbal hil
        hir hlr hV ?_ ?_ _ compact
      · rfl
      · simp [mergeTarget, hgc]

/-! ## 5. The parent's node, step by step -/

/-- `add` at time i of a klong that is no time klong: the last time is i; one
klong more if the last time was i, else two. -/
theorem wmp_add_last {n : MNode} {i : Time} (ht : TimesLe n i) {k : MKlong}
    (hk : ∀ t, k ≠ .time t) :
    (n.add i k).lastTime = some i ∧
      (n.add i k).size = n.size + (if n.lastTime = some i then 1 else 2) := by
  have hk' : ∀ t', kOf k ≠ Klong.time t' := fun t' e => hk t' (kOf_eq_time e)
  rcases add_ks n i k with ⟨h, hl⟩ | ⟨h, lt, hl, hle⟩
  · have hne : n.lastTime ≠ some i := fun e => Nat.lt_irrefl _ (hl i e)
    refine ⟨?_, ?_⟩
    · rw [← lastT_ksOf, show ksOf (n.add i k) = ksOf n ++ [.time i, kOf k] by
        simp [ksOf, h, kOf]]
      exact lastT_append_time _ _ _ hk'
    · simp [SIS.Tree.KNode.size, h, hne]
  · have hlt : lt ≤ i := ht lt (by rw [← lastT_ksOf] at hl; exact lastT_mem hl)
    have he : lt = i := Nat.le_antisymm hlt hle
    subst he
    refine ⟨?_, ?_⟩
    · rw [← lastT_ksOf, show ksOf (n.add lt k) = ksOf n ++ [kOf k] by simp [ksOf, h],
        ← hl, ← lastT_ksOf]
      unfold lastT
      rw [List.foldl_append]
      cases k with
      | time t => exact absurd rfl (hk t)
      | key c y => rfl
      | del b => rfl
    · simp [SIS.Tree.KNode.size, h, hl]

/-- The last time over a key klong set to another pointee. -/
theorem wmp_lastT_set {ks : List Klong} {j c : Nat} {y y' : NodeId}
    (hj : ks[j]? = some (Klong.key c y)) : lastT (ks.set j (Klong.key c y')) = lastT ks := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
  have hs : ks = ks.take j ++ Klong.key c y :: ks.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j ks]
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hlen : (ks.take j).length = j := by simp; omega
  rw [hs, List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero]
  unfold lastT
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  rfl

theorem wmp_repoint_last {n : MNode} {j c : Nat} {y : NodeId} (hj : n.ks[j]? = some (.key c y))
    (y' : NodeId) : (n.repoint j y').lastTime = n.lastTime := by
  have hj' : (ksOf n)[j]? = some (Klong.key c y) := by
    rw [ksOf_getElem?, hj]
    rfl
  rw [← lastT_ksOf, ← lastT_ksOf, ksOf_repoint_set hj, wmp_lastT_set hj']

theorem wmp_setDel_last {n : MNode} {t : Time} (ht : hasTransDel n t = true) (b : List Nat) :
    (n.setAt (n.size - 1) (.del b)).lastTime = n.lastTime := by
  obtain ⟨ks0, B, hks, -⟩ := hasTransDel_ks ht
  rw [← lastT_ksOf, ← lastT_ksOf]
  have h1 : ksOf (n.setAt (n.size - 1) (.del b)) = ks0.map kOf ++ [Klong.del b] := by
    simp [ksOf, setAt_last hks, kOf]
  have h2 : ksOf n = ks0.map kOf ++ [Klong.del B] := by simp [ksOf, hks, kOf]
  rw [h1, h2]
  unfold lastT
  rw [List.foldl_append, List.foldl_append]
  rfl

/-- A fold that notes the index of each time klong ends at an index at or
after one it started from. -/
theorem wmp_lti_fold (F : Option Nat → MKlong × Nat → Option Nat)
    (hF : ∀ acc k i, F acc (k, i) = match k with
      | .time _ => some i
      | _ => acc) (l : List MKlong) : ∀ (s j : Nat), j ≤ s →
    ∃ ti, (l.zipIdx s).foldl F (some j) = some ti ∧ j ≤ ti := by
  induction l with
  | nil => intro s j _; exact ⟨j, rfl, Nat.le_refl _⟩
  | cons a l ih =>
    intro s j hj
    rw [List.zipIdx_cons, List.foldl_cons, hF]
    cases a with
    | time t =>
      obtain ⟨ti, h1, h2⟩ := ih (s + 1) s (by omega)
      exact ⟨ti, h1, by omega⟩
    | key c y =>
      obtain ⟨ti, h1, h2⟩ := ih (s + 1) j (by omega)
      exact ⟨ti, h1, h2⟩
    | del b =>
      obtain ⟨ti, h1, h2⟩ := ih (s + 1) j (by omega)
      exact ⟨ti, h1, h2⟩

theorem wmp_lti_fold2 (F : Option Nat → MKlong × Nat → Option Nat)
    (hF : ∀ acc k i, F acc (k, i) = match k with
      | .time _ => some i
      | _ => acc) {t : Time} (l : List MKlong) : ∀ (s : Nat) (acc : Option Nat) (k : Nat),
    l[k]? = some (.time t) → ∃ ti, (l.zipIdx s).foldl F acc = some ti ∧ s + k ≤ ti := by
  induction l with
  | nil => intro s acc k h; simp at h
  | cons a l ih =>
    intro s acc k h
    rw [List.zipIdx_cons, List.foldl_cons]
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [hF]
      obtain ⟨ti, h1, h2⟩ := wmp_lti_fold F hF l (s + 1) s (by omega)
      exact ⟨ti, h1, by omega⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨ti, h1, h2⟩ := ih (s + 1) _ k h
      exact ⟨ti, h1, by omega⟩

/-- The index of the last time klong is at or after every time klong's. -/
theorem wmp_lti_ge {n : MNode} {k : Nat} {t : Time} (h : (ksOf n)[k]? = some (Klong.time t)) :
    ∃ ti, n.lastTimeIndex = some ti ∧ k ≤ ti := by
  have h' : n.ks[k]? = some (.time t) := by
    rw [ksOf_getElem?] at h
    obtain ⟨k', hk, hkk⟩ := Option.map_eq_some_iff.mp h
    rw [hk, kOf_eq_time hkk]
  unfold SIS.Tree.KNode.lastTimeIndex
  refine Exists.imp (fun ti h => ⟨h.1, by have := h.2; omega⟩)
    (wmp_lti_fold2 _ ?_ n.ks 0 none k h')
  intro acc k i
  cases k <;> rfl

/-- A klong set after the time klong of i keeps the klongs up to it. -/
theorem wmp_set_ext {ks ks0 more : List Klong} {i : Time} (h : ks = ks0 ++ Klong.time i :: more)
    {j : Nat} (hj : ks0.length < j) (k : Klong) :
    ∃ more', ks.set j k = ks0 ++ Klong.time i :: more' := by
  rw [h, List.set_append_right _ _ (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, j - ks0.length = m + 1 := ⟨j - ks0.length - 1, by omega⟩
  rw [hm, List.set_cons_succ]
  exact ⟨_, rfl⟩

/-- The live klong of a compare value stays so after klongs appended that are
no key klong of it and no bitmap that deletes it. -/
theorem wmp_liveAt_app {n n' : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y)
    {E : List Klong} (he : ksOf n' = ksOf n ++ E) (hE : ∀ y', Klong.key c y' ∉ E)
    (hD : j ∉ lastBitmap (ksOf n')) : LiveAt n' j c y := by
  obtain ⟨h1, -, h3⟩ := h
  have hlt : j < (ksOf n).length := (List.getElem?_eq_some_iff.mp h1).1
  refine ⟨by rw [he, List.getElem?_append_left hlt]; exact h1, hD, fun j' hj' => ?_⟩
  rw [he]
  by_cases hl : j' < (ksOf n).length
  · rw [cvAt_append hl]
    exact h3 j' hj'
  · unfold cvAt
    rw [List.getElem?_append_right (Nat.le_of_not_lt hl)]
    intro hc
    split at hc
    · rename_i c' y' hk
      simp only [Option.some.injEq] at hc
      subst hc
      exact hE y' (List.mem_of_getElem? hk)
    · simp at hc

theorem wmp_liveAt_add {n : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y) (t : Time)
    {k : MKlong} (hk : ∀ y', k ≠ .key c y') (hb : ∀ b, k = .del b → j ∉ b) :
    LiveAt (n.add t k) j c y := by
  have hk' : ∀ y', kOf k ≠ Klong.key c y' := by
    intro y' e
    cases k with
    | key c1 y1 =>
      simp only [kOf, Klong.key.injEq] at e
      exact hk y' (by rw [e.1, e.2])
    | time _ => simp [kOf] at e
    | del _ => simp [kOf] at e
  have hD0 := h.2.1
  have hlast : ∀ E : List Klong, lastBitmap (ksOf n ++ E ++ [kOf k]) = match k with
      | .del b => b
      | _ => lastBitmap (ksOf n ++ E) := by
    intro E
    rw [lastBitmap_snoc]
    cases k <;> rfl
  rcases ksOf_add n t k with ⟨he, _⟩ | ⟨he, _⟩
  · refine wmp_liveAt_app h he (fun y' hm => ?_) ?_
    · simp only [List.mem_cons, reduceCtorEq, false_or, List.not_mem_nil, or_false] at hm
      exact hk' y' hm.symm
    · rw [he, show ksOf n ++ [Klong.time t, kOf k] = ksOf n ++ [Klong.time t] ++ [kOf k] by simp,
        hlast]
      cases k with
      | del b => exact hb b rfl
      | key _ _ => rw [lastBitmap_snoc]; exact hD0
      | time _ => rw [lastBitmap_snoc]; exact hD0
  · refine wmp_liveAt_app h he (fun y' hm => ?_) ?_
    · simp only [List.mem_singleton] at hm
      exact hk' y' hm.symm
    · rw [he, show ksOf n ++ [kOf k] = ksOf n ++ [] ++ [kOf k] by simp, hlast]
      cases k with
      | del b => exact hb b rfl
      | key _ _ => simpa using hD0
      | time _ => simpa using hD0

theorem wmp_liveAt_setDel {n : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y) {t : Time}
    (ht : hasTransDel n t = true) {b : List Nat} (hb : j ∉ b) :
    LiveAt (n.setAt (n.size - 1) (.del b)) j c y := by
  obtain ⟨ks0, B, hks, -⟩ := hasTransDel_ks ht
  have hn : ksOf n = ks0.map kOf ++ [Klong.del B] := by simp [ksOf, hks, kOf]
  have hs : ksOf (n.setAt (n.size - 1) (.del b)) = ks0.map kOf ++ [Klong.del b] := by
    simp [ksOf, setAt_last hks, kOf]
  obtain ⟨h1, -, h3⟩ := h
  have hlt : j < (ks0.map kOf).length := by
    have := (List.getElem?_eq_some_iff.mp h1).1
    rw [hn] at h1 this
    simp only [List.length_append, List.length_singleton] at this
    rcases Nat.lt_or_ge j (ks0.map kOf).length with h2 | h2
    · exact h2
    · rw [List.getElem?_append_right h2, show j - (ks0.map kOf).length = 0 by omega] at h1
      simp at h1
  refine ⟨?_, ?_, fun j' hj' => ?_⟩
  · rw [hs, List.getElem?_append_left hlt]
    rw [hn, List.getElem?_append_left hlt] at h1
    exact h1
  · rw [hs, lastBitmap_snoc]
    exact hb
  · have := h3 j' hj'
    rw [hn] at this
    rw [hs]
    unfold cvAt at this ⊢
    by_cases hl : j' < (ks0.map kOf).length
    · rw [List.getElem?_append_left hl] at this ⊢
      exact this
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hl)]
      cases j' - (ks0.map kOf).length <;> simp

theorem wmp_liveAt_repoint {n : MNode} {j c : Nat} {y : NodeId} (h : LiveAt n j c y)
    {j2 c2 : Nat} {y2 : NodeId} (hj2 : n.ks[j2]? = some (.key c2 y2)) (hc : c2 ≠ c)
    (y' : NodeId) : LiveAt (n.repoint j2 y') j c y := by
  obtain ⟨h1, h2, h3⟩ := h
  have hj2' : (ksOf n)[j2]? = some (Klong.key c2 y2) := by
    rw [ksOf_getElem?, hj2]
    rfl
  have hne : j ≠ j2 := by
    intro e
    rw [e, hj2'] at h1
    simp only [Option.some.injEq, Klong.key.injEq] at h1
    exact hc h1.1
  obtain ⟨hsplit, hlen⟩ := ksOf_split hj2
  unfold LiveAt
  rw [ksOf_repoint_set hj2]
  refine ⟨?_, ?_, fun j' hj' => ?_⟩
  · rw [List.getElem?_set_ne (Ne.symm hne)]
    exact h1
  · rw [hsplit, List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.set_cons_zero,
      ← lastBitmap_keyswap _ _ c2 y2 y', ← hsplit]
    exact h2
  · have := h3 j' hj'
    unfold cvAt at this ⊢
    by_cases hjj : j' = j2
    · subst hjj
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hj2').1]
      simp [hc]
    · rw [List.getElem?_set_ne (Ne.symm hjj)]
      exact this

/-- What each step of `mergeParent` keeps of the parent's node n, on its way
from q's node nq: its kind and first klong, the live klongs L', well formed,
no time after i, the key klongs of nq or m1 or m2, the frame, and its size
(counting a time klong of i still to come). -/
structure WmpNode (i : Time) (s : Tree) (q : NodeId) (nq : MNode) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) (n : MNode) (L' : List (Nat × NodeId)) (sz : Nat) : Prop where
  leaf : n.leaf = nq.leaf
  live : live (ksOf n) = L'
  wf : klongsWf (ksOf n) = true
  head : n.ks.head? = nq.ks.head?
  first : ∃ t rest, n.ks = .time t :: rest
  times : TimesLe n i
  keys : ∀ c z, Klong.key c z ∈ ksOf n →
    (∃ c', Klong.key c' z ∈ ksOf nq) ∨ z = m1 ∨ ∃ g, m2 = some (z, g)
  ext : ∀ n0, s.obj q = some (.key n0) →
    ksOf n = n0.ks ∨ ∃ more, ksOf n = n0.ks ++ Klong.time i :: more
  size : n.size + (if n.lastTime = some i then 0 else 1) = sz
  last : nq.lastTime = some i → n.lastTime = some i

theorem wmp_node_add {i : Time} {s : Tree} {q : NodeId} {nq : MNode} {m1 : NodeId}
    {m2 : Option (NodeId × Nat)} {n : MNode} {L' : List (Nat × NodeId)} {sz : Nat}
    (h : WmpNode i s q nq m1 m2 n L' sz)
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i)
    {c : Nat} {z : NodeId} (hz : z = m1 ∨ ∃ g, m2 = some (z, g)) :
    WmpNode i s q nq m1 m2 (n.add i (.key c z)) (insertCv c z L') (sz + 1) := by
  obtain ⟨t0, rest, hr⟩ := h.first
  obtain ⟨hlt, hsz⟩ := wmp_add_last h.times (k := .key c z) (fun t e => by cases e)
  refine ⟨by rw [add_leaf]; exact h.leaf, by rw [add_key_live h.wf, h.live], add_key_wf h.wf c z,
    by rw [add_head hr, h.head], ⟨t0, add_first _ hr⟩,
    add_timesLe h.times _ (fun t e => by cases e), fun c' z' hm => ?_,
    fun n0 hs0 => add_ext (h0 n0 hs0) (h.ext n0 hs0) _, ?_,
    fun _ => hlt⟩
  · rcases add_key_mem.mp hm with h1 | ⟨-, rfl⟩
    · exact h.keys c' z' h1
    · exact Or.inr hz
  · rw [← h.size, hsz, hlt]
    split <;> simp

theorem wmp_node_addDel {i : Time} {s : Tree} {q : NodeId} {nq : MNode} {m1 : NodeId}
    {m2 : Option (NodeId × Nat)} {n : MNode} {L' : List (Nat × NodeId)} {sz : Nat}
    (h : WmpNode i s q nq m1 m2 n L' sz)
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i) (cR : Nat) :
    WmpNode i s q nq m1 m2 (n.add i (.del (delUnion n cR))) (dropCv cR L') (sz + 1) := by
  obtain ⟨t0, rest, hr⟩ := h.first
  obtain ⟨hlt, hsz⟩ := wmp_add_last h.times (k := .del (delUnion n cR)) (fun t e => by cases e)
  refine ⟨by rw [add_leaf]; exact h.leaf, by rw [addDel_live h.wf, h.live], addDel_wf h.wf cR,
    by rw [add_head hr, h.head], ⟨t0, add_first _ hr⟩,
    add_timesLe h.times _ (fun t e => by cases e),
    fun c' z' hm => h.keys c' z' (addDel_key_mem.mp hm),
    fun n0 hs0 => add_ext (h0 n0 hs0) (h.ext n0 hs0) _, ?_, fun _ => hlt⟩
  rw [← h.size, hsz, hlt]
  split <;> simp

theorem wmp_node_setDel {i : Time} {s : Tree} {q : NodeId} {nq : MNode} {m1 : NodeId}
    {m2 : Option (NodeId × Nat)} {n : MNode} {L' : List (Nat × NodeId)} {sz : Nat}
    (h : WmpNode i s q nq m1 m2 n L' sz) (ht : hasTransDel n i = true)
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i) (cR : Nat) :
    WmpNode i s q nq m1 m2 (n.setAt (n.size - 1) (.del (delUnion n cR))) (dropCv cR L') sz := by
  obtain ⟨t0, rest, hr⟩ := h.first
  have hl := wmp_setDel_last ht (delUnion n cR)
  refine ⟨by rw [setDel_leaf]; exact h.leaf, by rw [setDel_live h.wf ht, h.live],
    setDel_wf h.wf ht cR, by rw [setDel_head ht hr, h.head], ⟨t0, setDel_first ht hr _⟩,
    setDel_timesLe h.times _, fun c' z' hm => h.keys c' z' ((setDel_key_mem ht).mp hm),
    fun n0 hs0 => Or.inr (setDel_ext (h0 n0 hs0) ht (h.ext n0 hs0) _), ?_,
    fun e => by rw [hl]; exact h.last e⟩
  rw [setDel_size, hl]
  exact h.size

theorem wmp_node_repoint {i : Time} {s : Tree} {q : NodeId} {nq : MNode} {m1 : NodeId}
    {m2 : Option (NodeId × Nat)} {n : MNode} {L' : List (Nat × NodeId)} {sz : Nat}
    (h : WmpNode i s q nq m1 m2 n L' sz)
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i)
    {j c : Nat} {y0 : NodeId} (hj : LiveAt n j c y0) (hti : n.lastTime = some i)
    (hpos : ∀ n0, s.obj q = some (.key n0) → n0.ks.length < j)
    {z : NodeId} (hz : z = m1 ∨ ∃ g, m2 = some (z, g)) :
    WmpNode i s q nq m1 m2 (n.repoint j z) (insertCv c z L') sz := by
  obtain ⟨t0, rest, hr⟩ := h.first
  have hli := wmp_linkIndex hj
  obtain ⟨hjm, -, -⟩ := wmp_liveAt_model hj
  have hl := wmp_repoint_last hjm z
  obtain ⟨rest', hr'⟩ := repoint_first hr j z
  refine ⟨by rw [repoint_leaf]; exact h.leaf, by rw [repoint_live h.wf hli, h.live],
    repoint_wf h.wf hli z, by rw [hr', ← h.head, hr]; rfl, ⟨t0, rest', hr'⟩,
    repoint_timesLe h.times _ _, fun c' z' hm => ?_, fun n0 hs0 => ?_, ?_,
    fun _ => by rw [hl]; exact hti⟩
  · rcases repoint_key_mem hli hm with h1 | ⟨-, rfl⟩
    · exact h.keys c' z' h1
    · exact Or.inr hz
  · right
    rw [ksOf_repoint_set hjm]
    rcases h.ext n0 hs0 with he | ⟨more, he⟩
    · exfalso
      have := lastT_mem (show lastT (ksOf n) = some i by rw [lastT_ksOf]; exact hti)
      rw [he] at this
      exact Nat.lt_irrefl _ (h0 n0 hs0 i this)
    · exact wmp_set_ext he (hpos n0 hs0) _
  · rw [repoint_size, hl]
    exact h.size

/-- Klong j after the parent's last time klong is after its klongs of before
the transaction (and their time klong of i). -/
theorem wmp_hpos {i : Time} {s : Tree} {q : NodeId} {nq : MNode}
    (hext : ∀ n0, s.obj q = some (.key n0) →
      ksOf nq = n0.ks ∨ ∃ more, ksOf nq = n0.ks ++ Klong.time i :: more)
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i)
    (hoT : nq.lastTime = some i) {j : Nat} (haft : wmp_after nq j = true) :
    ∀ n0, s.obj q = some (.key n0) → n0.ks.length < j := by
  intro n0 hs0
  have hti := lastT_mem (show lastT (ksOf nq) = some i by rw [lastT_ksOf]; exact hoT)
  rcases hext n0 hs0 with he | ⟨more, he⟩
  · rw [he] at hti
    exact absurd (h0 n0 hs0 i hti) (Nat.lt_irrefl _)
  · have hk : (ksOf nq)[n0.ks.length]? = some (Klong.time i) := by
      rw [he, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    obtain ⟨ti, h1, h2⟩ := wmp_lti_ge hk
    unfold wmp_after at haft
    rw [h1] at haft
    simp only [decide_eq_true_eq] at haft
    omega

/-- The parent's node with the pointers set, in place (`putNode`): its live
klongs are the merge's target, and its size counts the klongs `need` says. -/
theorem wmp_n3_node {i : Time} {s : Tree} {q : NodeId} {nq : MNode} {il cL ir cR : Nat}
    {l r m1 : NodeId} {m2 : Option (NodeId × Nat)}
    (hN0 : WmpNode i s q nq m1 m2 nq (live (ksOf nq))
      (nq.size + if nq.lastTime = some i then 0 else 1))
    (h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i)
    (hil : LiveAt nq il cL l) (hir : LiveAt nq ir cR r) (hlr : cL < cR) :
    WmpNode i s q nq m1 m2 (wmp_n3 i nq il cL m1 ir cR m2)
      (mergeTarget (live (ksOf nq)) cL cR m1 m2) (nq.size + wmp_need i nq il ir cR m2) := by
  have hcLR : cL ≠ cR := Nat.ne_of_lt hlr
  obtain ⟨hilm, -, -⟩ := wmp_liveAt_model hil
  have hnotin : il ∉ delUnion nq cR := by
    rw [mem_delUnion]
    rintro (h1 | h1)
    · exact hil.2.1 h1
    · unfold cvAt at h1
      rw [hil.1] at h1
      simp only [Option.some.injEq] at h1
      exact hcLR h1
  have hN1 : WmpNode i s q nq m1 m2 (wmp_n1 i nq cR m2)
      (if wmp_delR cR m2 then dropCv cR (live (ksOf nq)) else live (ksOf nq))
      ((nq.size + if nq.lastTime = some i then 0 else 1) +
        if (wmp_delR cR m2 && !hasTransDel nq i) = true then 1 else 0) := by
    unfold wmp_n1 wmp_union
    cases hd : wmp_delR cR m2
    · simpa using hN0
    · cases hT : hasTransDel nq i
      · simpa [hT, delUnion] using wmp_node_addDel hN0 h0 cR
      · simpa [hT, delUnion] using wmp_node_setDel hN0 hT h0 cR
  have hL1 : LiveAt (wmp_n1 i nq cR m2) il cL l := by
    unfold wmp_n1 wmp_union
    cases hd : wmp_delR cR m2
    · simpa using hil
    · cases hT : hasTransDel nq i
      · simpa [hT, delUnion] using
          wmp_liveAt_add hil i (k := .del (delUnion nq cR)) (fun y' e => by cases e)
          (fun b e => by cases e; exact hnotin)
      · simpa [hT, delUnion] using wmp_liveAt_setDel hil hT hnotin
  have hN2 : WmpNode i s q nq m1 m2 (wmp_n2 i nq il cL m1 cR m2)
      (insertCv cL m1 (if wmp_delR cR m2 then dropCv cR (live (ksOf nq)) else live (ksOf nq)))
      (((nq.size + if nq.lastTime = some i then 0 else 1) +
        if (wmp_delR cR m2 && !hasTransDel nq i) = true then 1 else 0) +
        if (nq.lastTime == some i && wmp_after nq il) = true then 0 else 1) := by
    unfold wmp_n2
    by_cases hc : (nq.lastTime == some i && wmp_after nq il) = true
    · simp only [hc, ↓reduceIte, Nat.add_zero]
      obtain ⟨hoT, haL⟩ := Bool.and_eq_true_iff.mp hc
      have hoT' : nq.lastTime = some i := beq_iff_eq.mp hoT
      exact wmp_node_repoint hN1 h0 hL1 (hN1.last hoT') (wmp_hpos hN0.ext h0 hoT' haL)
        (Or.inl rfl)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact wmp_node_add hN1 h0 (Or.inl rfl)
  have hR2 : wmp_delR cR m2 = false → LiveAt (wmp_n2 i nq il cL m1 cR m2) ir cR r := by
    intro hd
    have e : wmp_n1 i nq cR m2 = nq := by simp [wmp_n1, hd]
    unfold wmp_n2
    rw [e]
    split
    · exact wmp_liveAt_repoint hir hilm hcLR m1
    · exact wmp_liveAt_add hir i (k := .key cL m1) (fun y' e => hcLR (by cases e; rfl))
        (fun b e => by cases e)
  cases m2 with
  | none =>
    have eT : mergeTarget (live (ksOf nq)) cL cR m1 none =
        insertCv cL m1 (if wmp_delR cR none then dropCv cR (live (ksOf nq))
          else live (ksOf nq)) := by
      simp [mergeTarget, wmp_delR]
    have es : (((nq.size + if nq.lastTime = some i then 0 else 1) +
        if (wmp_delR cR none && !hasTransDel nq i) = true then 1 else 0) +
        if (nq.lastTime == some i && wmp_after nq il) = true then 0 else 1) =
        nq.size + wmp_need i nq il ir cR none := by
      unfold wmp_need
      simp only [wmp_delR, Option.isNone_none, Bool.true_or, beq_iff_eq]
      split_ifs <;> omega
    rw [eT, ← es]
    exact hN2
  | some yg =>
    obtain ⟨y, g⟩ := yg
    unfold wmp_n3
    by_cases hgc : g = cR
    · subst hgc
      have hd : wmp_delR g (some (y, g)) = false := by simp [wmp_delR]
      have eT : mergeTarget (live (ksOf nq)) cL g m1 (some (y, g)) =
          insertCv g y (insertCv cL m1 (live (ksOf nq))) := by
        simp [mergeTarget]
      rw [eT]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hN2 ⊢
      by_cases hc : (nq.lastTime == some i && wmp_after nq ir) = true
      · simp only [Bool.not_false, Bool.true_and, hc, ↓reduceIte]
        obtain ⟨hoT, haR⟩ := Bool.and_eq_true_iff.mp hc
        have hoT' : nq.lastTime = some i := beq_iff_eq.mp hoT
        have h3 := wmp_node_repoint hN2 h0 (hR2 hd) (hN2.last hoT') (wmp_hpos hN0.ext h0 hoT' haR)
          (Or.inr ⟨g, rfl⟩)
        convert h3 using 1
        unfold wmp_need
        clear h3 hN2 hR2 hN1 hL1 hN0 eT
        by_cases h1 : nq.lastTime = some i <;> by_cases h2 : wmp_after nq il = true <;>
          by_cases h3 : wmp_after nq ir = true <;> by_cases h4 : hasTransDel nq i = true <;>
          simp_all
      · simp only [Bool.not_false, Bool.true_and, hc, Bool.false_eq_true, ↓reduceIte]
        have h3 := wmp_node_add hN2 h0 (c := g) (Or.inr ⟨g, rfl⟩)
        convert h3 using 1
        unfold wmp_need
        clear h3 hN2 hR2 hN1 hL1 hN0 eT
        by_cases h1 : nq.lastTime = some i <;> by_cases h2 : wmp_after nq il = true <;>
          by_cases h3 : wmp_after nq ir = true <;> by_cases h4 : hasTransDel nq i = true <;>
          simp_all
    · have hd : wmp_delR cR (some (y, g)) = true := by simp [wmp_delR, hgc]
      have eT : mergeTarget (live (ksOf nq)) cL cR m1 (some (y, g)) =
          insertCv g y (insertCv cL m1 (dropCv cR (live (ksOf nq)))) := by
        simp [mergeTarget, hgc]
      rw [eT]
      simp only [hd, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true] at hN2 ⊢
      have h3 := wmp_node_add hN2 h0 (c := g) (Or.inr ⟨g, rfl⟩)
      convert h3 using 1
      unfold wmp_need
      clear h3 hN2 hR2 hN1 hL1 hN0 eT
      by_cases h1 : nq.lastTime = some i <;> by_cases h2 : wmp_after nq il = true <;>
        by_cases h3 : wmp_after nq ir = true <;> by_cases h4 : hasTransDel nq i = true <;>
        simp_all

/-! ## 6. The merge's parent -/

theorem mergeParent_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {q : NodeId}
    {w : MW} {nq : MNode} {il cL ir cR : Nat} {l r m1 : NodeId} {m2 : Option (NodeId × Nat)}
    {C : List (Key × Nat)}
    (hlk : w.nodes.lookup q = some nq) (hon : ∃ c0, w.path[depth]? = some (c0, q))
    (hpath : PathOk i s w depth) (hin : PathInner w depth)
    (hbooks : PutBooks p i base s w) (hwf : klongsWf (ksOf nq) = true) (hsize : nq.size ≤ p.M)
    (hroot : (treeOf i s w).root = some w.top.rootKey)
    (hframe : Frame i s (dirtyOf w) (treeOf i s w)) (htop : WTopInv i s tp w.top w.newTop)
    (hbal : BalancedAll p (treeOf i s w))
    (hil : LiveAt nq il cL l) (hir : LiveAt nq ir cR r) (hlr : cL < cR)
    (hadj : ∀ c y, (c, y) ∈ live (ksOf nq) → c ≤ cL ∨ cR ≤ c)
    (hg : ∀ y g, m2 = some (y, g) → cL < g ∧
      ∀ c z, (c, z) ∈ live (ksOf nq) → cR < c → g < c)
    (hV : MergeVirt p i s w q nq cL cR m1 m2 C) :
    WP (SIS.Tree.mergeParent q depth il cL m1 ir cR m2) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ w'.path = w.path ∧ w.next ≤ w'.next) := by
  have ht : w.taken.contains q = false := by
    obtain ⟨c0, hc0⟩ := hon
    exact (hpath.lookup (Nat.le_refl _) hc0).choose_spec.2
  obtain ⟨t0, rest, hr0⟩ := hbooks.timeFirst q nq hlk ht
  have h0 : ∀ n0, s.obj q = some (.key n0) → ∀ t, Klong.time t ∈ n0.ks → t < i :=
    fun n0 hs0 => prim_timesBefore (hb.times q n0 hs0)
  have hN0 : WmpNode i s q nq m1 m2 nq (live (ksOf nq))
      (nq.size + if nq.lastTime = some i then 0 else 1) :=
    ⟨rfl, rfl, hwf, rfl, ⟨t0, rest, hr0⟩, wput_timesLe hbooks hlk,
      fun c z h => Or.inl ⟨c, h⟩, fun n0 hs0 => (frame_overlay_ext hframe hlk ht hs0).2.2, rfl,
      id⟩
  have hfull := fun compact => wmp_full_spec (v := v) hp hb hlk hon hpath hin hbooks hwf hsize
    hroot hframe htop hbal hil hir hlr hV hadj hg compact
  rw [wmp_eq]
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk) ?_
  refine wp_ite _ _ _ _ _ _ (fun hfit => ?_) (fun _ => hfull false)
  refine wp_ite _ _ _ _ _ _ (fun _ => hfull true) (fun _ => ?_)
  refine wput_ok (note_eq _ _ _) ?_
  intro u w' hr
  rw [putNode_eq] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  intro _
  have hN3 := wmp_n3_node (m1 := m1) hN0 h0 hil hir hlr
  have hsz3 : (wmp_n3 i nq il cL m1 ir cR m2).size ≤ p.M := by
    have := hN3.size
    have hfit' : nq.size + wmp_need i nq il ir cR m2 ≤ p.M := hfit
    omega
  obtain ⟨hS, hB⟩ := hV _ hN3.leaf hN3.live hN3.wf (by omega) hN3.keys hN3.first hN3.times
  have hI : PInv p i base s tp (some q) C (w.withNode q (wmp_n3 i nq il cL m1 ir cR m2)) :=
    ⟨hroot, hS, frame_withNode hframe hlk ht hN3.leaf hN3.ext, htop, hB,
      putBooks_withNode hbooks hlk ht hN3.leaf hN3.head (timesLe_model hN3.times)⟩
  exact ⟨(wput_pinv_fit hI (lookup_upsert_self _ _ _) hsz3).congr rfl rfl rfl rfl rfl rfl rfl rfl
    rfl, rfl, Nat.le_refl _⟩

end Contract
