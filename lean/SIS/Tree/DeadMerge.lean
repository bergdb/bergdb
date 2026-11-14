/-
The merge's parent keeps the dead klongs' bound (bergdb 024-12, a piece for
`QDead` of (4)): `mergeParent` puts the parent in place only when `deadOver`
lets it through (`writerWP_mergeParent_casesD`, `writerWP_mergeParent_cases`
with that fact), and a full parent, or one with too many dead klongs, goes to
`handleFull` (`writerWP_handleFull_lastDead`, `writerWP_handleFull_rootDead`).
-/
import SIS.Tree.DeadSteps
import SIS.Tree.WriterTreeMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option linter.unusedSimpArgs false in
/-- `mergeParent` by its two ways, as `writerWP_mergeParent_cases`, with the
fact that the parent in place does not hold too many dead klongs. -/
theorem writerWP_mergeParent_casesD (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn)
    (hroomP : ∀ s : String, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false →
      post () ({ ({ w with trail := s :: w.trail } : W) with
        nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W))
    (hfullP : ∀ (last : KNode) (compact : Bool) (s : String),
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull depth p last compact) c ({ w with trail := s :: w.trail } : W) post) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_if
    · intro _
      apply writerWP_if
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          apply hfullP
          simp only [mergeFullLast] at hks ⊢
          simp only [hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hnd
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _ (Bool.eq_false_iff.mpr hnd)
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        apply hfullP
        simp only [mergeFullLast] at hks ⊢
        simp only [hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
  | some yg =>
    obtain ⟨y, g⟩ := yg
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_if
    · intro _
      apply writerWP_if
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          by_cases hg : g = cR
          · have hgb : (g != cR) = false := by simp [hg]
            simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
            split
            · rename_i ks2 hks2
              apply hfullP
              simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
            · exact writerWP_throw _ _ _ _
            · exact writerWP_throw _ _ _ _
          · have hgb : (g != cR) = true := by simp [hg]
            simp only [hgb, ↓reduceIte] at hks ⊢
            apply hfullP
            simp only [mergeFullLast, hgb, ↓reduceIte, hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hnd
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _ (Bool.eq_false_iff.mpr hnd)
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        by_cases hg : g = cR
        · have hgb : (g != cR) = false := by simp [hg]
          simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
          split
          · rename_i ks2 hks2
            apply hfullP
            simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
          · exact writerWP_throw _ _ _ _
          · exact writerWP_throw _ _ _ _
        · have hgb : (g != cR) = true := by simp [hg]
          simp only [hgb, ↓reduceIte] at hks ⊢
          apply hfullP
          simp only [mergeFullLast, hgb, ↓reduceIte, hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _

/-- The merge's parent keeps the bound: in place only when `deadOver` lets it
through; a full parent, or one with too many dead klongs, goes to `handleFull`
(`hfull`, the split and its cascade: `writerWP_handleFull_lastDead`,
`writerWP_handleFull_rootDead`), with the last version `mergeFullLast`. -/
theorem writerWP_mergeParent_dead (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup p = some pn) (htk : w.taken.contains p = false)
    (hW : WDeadN c.p (wNode c.p base w))
    (hfull : ∀ (last : KNode) (compact : Bool) (w0 : W), w0.nodes = w.nodes → w0.taken = w.taken →
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull depth p last compact) c w0 (fun _ w' => WDeadN c.p (wNode c.p base w'))) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w
      (fun _ w' => WDeadN c.p (wNode c.p base w')) := by
  refine writerWP_mergeParent_casesD p pn depth il cL m1 ir cR m2 c w
    (fun _ w' => WDeadN c.p (wNode c.p base w')) hlk ?_ ?_
  · intro s hd
    have hN := wNode_upsert_updN c.p base w
      ({ ({ w with trail := s :: w.trail } : W) with
        nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W) p
      (mergeParentNode pn c.i il cL m1 ir cR m2) rfl rfl htk
    rw [hN]
    exact wDeadN_updN c.p _ p _ hW (fun h0 => deadOver_false c.p _ hd h0)
  · intro last compact s hm
    exact hfull last compact _ rfl rfl hm

/-- Retargeting a node's klongs keeps its dead count. -/
theorem KNode.deadCount_retarget (n : KNode) (ti : Nat) (src dst : NodeId) :
    ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).deadCount = n.deadCount := by
  have e1 := KNode.deadCount_map_shape n.leaf (retargetKlongs n.ks ti src dst)
  have e2 := KNode.deadCount_map_shape n.leaf n.ks
  rw [retargetKlongs_shape] at e1
  show (⟨n.leaf, retargetKlongs n.ks ti src dst⟩ : KNode).deadCount = (⟨n.leaf, n.ks⟩ : KNode).deadCount
  rw [← e1, e2]

/-- What the merge's last loop keeps: every node the writer reads at or below
theta, with well-formed klongs, and the parent p not taken back. -/
def DeadWf (c : Ctx) (base : View BVal) (p : NodeId) (w : W) : Prop :=
  WDeadN c.p (wNode c.p base w) ∧ (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) ∧
    w.taken.contains p = false

/-- `retarget` keeps `DeadWf`: the node changes to itself or retargeted, which
has the same dead count and well-formedness. -/
theorem writerWP_retarget_deadWf (p src dst : NodeId) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) (hI : DeadWf c base p w) :
    WriterWP (retarget p src dst) c w (fun _ w' => DeadWf c base p w') := by
  obtain ⟨hW, hwf, hpt⟩ := hI
  refine writerWP_mono (writerWP_retarget_wNode p src dst c base hvc w hpt) ?_
  rintro _ w' ⟨ht, _, _, _, hoth, _, hp⟩
  have key : ∀ y n, wNode c.p base w' y = some n → ∃ n0, wNode c.p base w y = some n0 ∧
      n.deadCount = n0.deadCount ∧ klongsWf n.ks = klongsWf n0.ks := by
    intro y n hy
    by_cases hyp : y = p
    · subst hyp
      obtain ⟨n0, hn0, hor⟩ := hp n hy
      rcases hor with e | ⟨ti, e⟩
      · subst e; exact ⟨_, hn0, rfl, rfl⟩
      · subst e
        exact ⟨n0, hn0, KNode.deadCount_retarget n0 ti src dst, klongsWf_retargetKlongs _ _ _ _⟩
    · rw [hoth y hyp] at hy
      exact ⟨n, hy, rfl, rfl⟩
  refine ⟨fun h0 y n hy => ?_, fun y n hy => ?_, by rw [ht]; exact hpt⟩
  · obtain ⟨n0, hn0, hd, _⟩ := key y n hy
    rw [hd]; exact hW h0 y n0 hn0
  · obtain ⟨n0, hn0, _, hk⟩ := key y n hy
    rw [hk]; exact hwf y n0 hn0

/-- A take-back keeps `DeadWf` but of the node taken back: the writer reads
fewer nodes. -/
theorem writerWP_takenBack_deadWf (p x : NodeId) (c : Ctx) (base : View BVal) (w : W)
    (hxp : x ≠ p) (hI : DeadWf c base p w) :
    WriterWP (takenBack x) c w (fun _ w' => DeadWf c base p w') := by
  obtain ⟨hW, hwf, hpt⟩ := hI
  rw [writerWP_takenBack_iff]
  have hsub : ∀ y n, wNode c.p base ({ w with taken := x :: w.taken } : W) y = some n →
      wNode c.p base w y = some n := by
    intro y n hy
    unfold wNode at hy ⊢
    cases hty : w.taken.contains y with
    | true =>
      have : (x :: w.taken).contains y = true := by
        rw [List.contains_cons, hty, Bool.or_true]
      simp only [this, ↓reduceIte] at hy
      cases hy
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hxy : (x :: w.taken).contains y = true
      · simp only [hxy, ↓reduceIte] at hy; cases hy
      · simp only [hxy, Bool.false_eq_true, ↓reduceIte] at hy
        exact hy
  refine ⟨fun h0 y n hy => hW h0 y n (hsub y n hy), fun y n hy => hwf y n (hsub y n hy), ?_⟩
  show (x :: w.taken).contains p = false
  rw [List.contains_cons, hpt, Bool.or_false]
  simpa using Ne.symm hxp

/-- `unlink` keeps `DeadWf`: the node, if it changes, becomes its previous
version, with no more dead klongs (`KNode.deadCount_toPrev_le`) and well-formed
klongs. -/
theorem writerWP_unlink_deadWf (p o : NodeId) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) (hI : DeadWf c base p w) :
    WriterWP (unlink o) c w (fun _ w' => DeadWf c base p w') := by
  obtain ⟨hW, hwf, hpt⟩ := hI
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_reads o c w base hvc) ?_
  intro n w1 ⟨hr1, _, hw1⟩
  have hN1 : wNode c.p base w1 = wNode c.p base w := hr1.1
  have h1pt : w1.taken.contains p = false := by rw [hr1.2.2.1]; exact hpt
  split
  · unfold putNode
    refine (writerWP_modify _ c w1 _).mpr ?_
    by_cases ht : w.taken.contains o = true
    · have e : wNode c.p base ({ w1 with nodes := upsert w1.nodes o (n.toPrev (c.i - 1)) } : W) =
          wNode c.p base w1 := by
        funext z
        by_cases hz : z = o
        · subst hz
          have h1t : w1.taken.contains z = true := by rw [hr1.2.2.1]; exact ht
          simp only [wNode, h1t, ↓reduceIte]
        · simp only [wNode, lookup_upsert, hz, ↓reduceIte]
      refine ⟨?_, ?_, h1pt⟩
      · rw [e, hN1]; exact hW
      · rw [e, hN1]; exact hwf
    · have ht' : w.taken.contains o = false := by simpa using ht
      have hn := hw1 ht'
      have h1t : w1.taken.contains o = false := by rw [hr1.2.2.1]; exact ht'
      have hwn : klongsWf n.ks = true := hwf o n hn
      have hNe : wNode c.p base ({ w1 with nodes := upsert w1.nodes o (n.toPrev (c.i - 1)) } : W) =
          updN (wNode c.p base w) o (n.toPrev (c.i - 1)) := by
        rw [wNode_upsert_updN c.p base w1
          ({ w1 with nodes := upsert w1.nodes o (n.toPrev (c.i - 1)) } : W) o (n.toPrev (c.i - 1))
          rfl rfl h1t, hN1]
      refine ⟨?_, fun z zn hz => ?_, h1pt⟩
      · rw [hNe]
        exact wDeadN_updN c.p _ o _ hW (fun h0 =>
          Nat.le_trans (KNode.deadCount_toPrev_le n _ hwn) (hW h0 o n hn))
      rw [hNe] at hz
      by_cases hzo : z = o
      · subst hzo
        rw [updN_self] at hz
        cases hz
        exact KNode.toPrev_wf n _ hwn
      · rw [updN_ne _ _ _ _ hzo] at hz
        exact hwf z zn hz
  · refine (writerWP_pure _ c w1 _).mpr ?_
    refine ⟨?_, ?_, h1pt⟩
    · rw [hN1]; exact hW
    · rw [hN1]; exact hwf

/-- The merge's last loop keeps `DeadWf`: each node is taken back (its parent
retargeted) or unlinked. -/
theorem writerWP_mergeCleanup_deadWf (p m1 : NodeId) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, q.1 ≠ p) → DeadWf c base p w →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => DeadWf c base p w') := by
  intro xs
  induction xs with
  | nil =>
    intro w _ hI
    rw [List.forIn_nil]
    exact (writerWP_pure _ c w _).mpr hI
  | cons q qs ih =>
    intro w hne hI
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hne' : ∀ q' ∈ qs, q'.1 ≠ p := fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_deadWf p q.1 m1 c base hvc w hI) ?_
      intro _ w1 h1
      refine writerWP_mono (writerWP_takenBack_deadWf p q.1 c base w1 hqp h1) ?_
      intro _ w2 h2
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      exact ih _ hne' ⟨h2.1, h2.2.1, h2.2.2⟩
    · simp only [writerWP_bind, hq2, Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_deadWf p q.1 c base hvc w hI) ?_
      intro _ w1 h1
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      exact ih _ hne' h1

end SIS.Tree
