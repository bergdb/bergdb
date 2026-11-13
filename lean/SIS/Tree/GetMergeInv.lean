/-
The writer's merge from the invariants of the state before it (bergdb 024-22,
case 4 of 024-12's assembly): the premises of `writerWP_merge_any_get` and
`writerWP_merge_root_get` from `PutInv`, its global parts `PutInvG`, the walk's
ranges `RangeOrder` and the key access path down to the merged node (`PathOK`).
What they do not give is named: no space split in place below a segment leaf on
the path (`hNoSSIP`, `hNoSSIPp`), and the range of the full parent's last
version in its link (`hrangeL`).
-/
import SIS.Tree.GetMergeRoot
import SIS.Tree.GetCaseBridge
import SIS.Tree.ChildrenExist
import SIS.Tree.DelMergeBook

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The key access path of the writer's state down to depth d: its nodes X i
(the space root first), each named by the one above it by its klong K i, held
in the overlay and not taken back. -/
def PathOK (c : Ctx) (w : W) (d : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) :
    Prop :=
  (∀ i, i ≤ d → (w.path[i]?).map (·.2) = some (X i)) ∧
  (∀ i, 0 < i → i ≤ d → w.path[i]? = some (some (K i), X i)) ∧
  (∀ i, i ≤ d → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) ∧
  (∀ i, 0 < i → i ≤ d → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) ∧
  X 0 = w.top.rootKey

/-- The path's nodes are at their depths in the writer's tree, so reached and
distinct. -/
theorem pathOK_depth (c : Ctx) (base : View BVal) (w : W) (d : Nat) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn) :
    ∀ i, i ≤ d → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
  obtain ⟨_, _, hS2, hlink, h0⟩ := hP
  intro i
  induction i with
  | zero => intro _; rw [h0]; exact PathLen.root
  | succ i ih =>
    intro hi
    have hw : wNode c.p base w (X i) = some (Nn i) := by
      obtain ⟨a, b⟩ := hS2 i (by omega)
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
    exact PathLen.link (ih (by omega)) ⟨Nn i, hw, by simpa using hlink (i + 1) (by omega) hi⟩

theorem pathOK_reach (c : Ctx) (base : View BVal) (w : W) (d : Nat) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn) :
    ∀ i, i ≤ d → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
  fun i hi => (pathOK_depth c base w d X K Nn hP i hi).reach

theorem pathOK_dist (c : Ctx) (base : View BVal) (w : W) (d : Nat) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey) :
    ∀ i i', i ≤ d → i' ≤ d → X i = X i' → i = i' := by
  intro i i' hi hi' he
  have h1 := pathOK_depth c base w d X K Nn hP i hi
  have h2 := pathOK_depth c base w d X K Nn hP i' hi'
  rw [he] at h1
  exact PathLen.depth_unique hT _ _ _ h1 h2

/-- `ChainOrd` of a path node from the walk's order (`OrdG`). -/
theorem chainOrd_of_ordG (c : Ctx) (base : View BVal) (w : W) (d : Nat) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (hO : OrdG c (wNode c.p base w) w.top.rootKey) :
    ∀ i, 0 < i → i ≤ d → ChainOrd c K Nn i := by
  intro i hi0 hi hNR hql hsp c' z hz
  obtain ⟨_, _, hS2, hlink, _⟩ := hP
  have hw : ∀ j, j ≤ d → wNode c.p base w (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  exact hO (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
    (pathOK_reach c base w d X K Nn ⟨‹_›, ‹_›, hS2, hlink, ‹_›⟩ (i - 1) (by omega))
    (hw (i - 1) (by omega)) hql (hlink i hi0 hi) (hw i hi) hNR hsp c' z hz

/-- The writer's merge of the node x at depth d of the key access path keeps the
reading of every key when the state after fits the fuel, from the state's
invariants: `PutInv`, its global parts `PutInvG`, the walk's ranges and the path
down to x (`PathOK`), the parent X (d - 1) inner. Named premises: no space split
in place below a segment leaf on the path above the parent (`hNoSSIP`) or at the
parent (`hNoSSIPp`), and the full parent's last version in the range of its link
(`hrangeL`). -/
theorem writerWP_merge_get_inv (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (hd0 : 0 < d) (hx : X d = x) (hql : (Nn (d - 1)).leaf = false)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hNoSSIP : ∀ i, 0 < i → i + 2 ≤ d → (Nn (i - 1)).leaf = true → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → (Nn i).firstTime ≠ some c.i)
    (hNoSSIPp : 2 ≤ d → (Nn (d - 2)).leaf = true → ∀ cL cR m1 m2 last,
      mergeFullLast (Nn (d - 1)) c.i cL m1 cR m2 = some last → c.p.splitAbove < last.size →
      (Nn (d - 1)).firstTime ≠ some c.i)
    (hrangeL : 2 ≤ d → ∀ cL cR m1 m2 last, mergeFullLast (Nn (d - 1)) c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → (Nn (d - 2)).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨(Nn (d - 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (d - 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (d - 2)).live → K (d - 1) < c'' → c' < c'') :
    WriterWP (merge x d) c w (fun _ w' =>
      SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey →
      ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
  have hP' := hP
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := hP'
  have hT := hI.tree
  have hreach := pathOK_reach c base w d X K Nn hP
  have hdist := pathOK_dist c base w d X K Nn hP hT
  have hw : ∀ j, j ≤ d → wNode c.p base w (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hO := ordG_of_rangeOrder c _ _ hRO hI.times
  have hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i := by
    intro p hp
    have hpX : p = X (d - 1) := by
      rw [hX (d - 1) (by omega)] at hp; exact (Option.some.inj hp).symm
    subst hpX
    exact ⟨hreach (d - 1) (by omega), Nn (d - 1), hw (d - 1) (by omega), hql,
      hI.wf _ _ (hw (d - 1) (by omega)), hI.times _ _ (hw (d - 1) (by omega)),
      fun cc z zn _ hz => hI.times z zn hz⟩
  have hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false :=
    fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) :=
    ⟨hI.ids.1, hI.ids.2.1, hI.ids.2.2.1⟩
  have hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none := fun z hz => (hI.fresh z hz).1
  have hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next :=
    fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl
  have hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' _ hl; have := hlinksAll u c' z hl; omega
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    have hvz : w.vals.lookup z = none := by
      cases h' : w.vals.lookup z with
      | none => rfl
      | some _ =>
        have hm := lookup_some_mem h'
        have := hI.ids.2.2.2.1 _ hm
        simp only at this; omega
    simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz, (hI.fresh z hz).2]
  by_cases hd1 : d = 1
  · subst hd1
    refine writerWP_mono (writerWP_merge_root_get x 1 c base hvc w hT hpar hRt hids hbaseF hfreshT hRO
      hcap hI.times hI.wf hI.keyNoValue hlinksAll hfreshV rfl
      (by rw [hX 0 (by omega), h0]) hsa2) ?_
    intro _ w' h hf key
    exact h (Or.inl hf) key
  · have hd2 : 2 ≤ d := by omega
    refine writerWP_mono (writerWP_merge_any_get x d c base hvc w hT hpar hRt hids hbaseF hfreshT hRO
      hcap hI.times hI.wf hI.keyNoValue hlinksAll hfreshV 0 (d - 2) X K Nn (Nat.zero_le _)
      (by omega)
      (fun i _ hi => hX i (by omega))
      (fun i h1 hi => hK i h1 (by omega))
      (fun i h1 hi => hlink i h1 (by omega))
      (fun i h1 hi hNR hql' c' z hz hpos =>
        rangeG_of_rangeOrder c _ _ hRO hI.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
          (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
          (hw i (by omega)) hNR c' z hz hpos)
      (fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
        (hw i (by omega)) hNR hsp)
      (fun i _ hi => hI.wf _ _ (hw i (by omega)))
      (fun i _ hi => hI.times _ _ (hw i (by omega)))
      (Or.inr rfl)
      (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
      (by
        intro i _ hi hNR hsp
        rcases Nat.eq_zero_or_pos i with h | h
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_⟩
          cases hpl : (Nn (i - 1)).leaf with
          | false => exact Or.inl rfl
          | true =>
            exact Or.inr ⟨hNoSSIP i h (by omega) hpl hNR hsp, fun i' h1 h2 =>
              chainOrd_of_ordG c base w d X K Nn hP hO i' h1 (by omega)⟩)
      (fun i _ hi => hS2 i (by omega))
      (fun i _ hi => hreach i (by omega))
      (fun _ => by rw [h0])
      (fun i _ hi he => by
        have := hdist i d (by omega) (Nat.le_refl _) (by rw [he, hx]); omega)
      hsa2
      (by
        have he : d - 2 + 1 = d - 1 := by omega
        rw [he]
        exact hrangeL hd2)
      (by
        have he : d - 2 + 1 = d - 1 := by omega
        rw [he]
        intro cL cR m1 m2 last hl hsp
        cases hpl : (Nn (d - 2)).leaf with
        | false => exact Or.inl rfl
        | true =>
          exact Or.inr ⟨hNoSSIPp hd2 hpl cL cR m1 m2 last hl hsp, fun i' h1 h2 =>
            chainOrd_of_ordG c base w d X K Nn hP hO i' h1 (by omega)⟩)) ?_
    intro _ w' h hf key
    exact h (Or.inl hf) key

/-! ## The delete's inner invariant -/

/-- `PutInv` is read alike: a state that reads as w has w's invariant. -/
theorem putInv_of_readsAs (c : Ctx) (base : View BVal) (w v : W) (hI : PutInv c base w)
    (hr : ReadsAs c.p base w v) : PutInv c base v := by
  obtain ⟨hN, htop, ht, hvals, hnext⟩ := hr
  have hV : wValue base v = wValue base w := wValue_congr' base v w ht hvals
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, htop]; exact hI.tree
  · rw [hN]; exact hI.wf
  · rw [hN]; exact hI.times
  · intro z hz
    rw [hnext]
    rcases Nat.lt_or_ge z w.next with h | h
    · exact h
    · exfalso
      have htz : v.taken.contains z = false := by
        rw [ht]
        cases h' : w.taken.contains z with
        | false => rfl
        | true => have := hI.ids.2.2.1 z h'; omega
      have hwz : wNode c.p base v z ≠ none := by
        simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte]
        cases hl : v.nodes.lookup z with
        | none => rw [hl] at hz; cases hz
        | some _ => simp
      rw [hN] at hwz
      apply hwz
      have hnz : w.nodes.lookup z = none := by
        cases h' : w.nodes.lookup z with
        | none => rfl
        | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
      simp only [wNode, ← ht, htz, Bool.false_eq_true, ↓reduceIte, hnz, (hI.fresh z h).1]
  · rw [hnext]; exact hI.ids.2.1
  · rw [hnext, ht]; exact hI.ids.2.2.1
  · rw [hnext, hvals]; exact hI.ids.2.2.2.1
  · rw [hnext, htop]; exact hI.ids.2.2.2.2
  · rw [hnext]; exact hI.fresh
  · rw [hN, htop, hnext]; exact hI.links
  · rw [hN, htop, ht]; exact hI.untaken
  · rw [hN, hV]; exact hI.keyNoValue
  · rw [hN, htop]; exact hI.order

/-- `PutInvG` is read alike. -/
theorem putInvG_of_readsAs (c : Ctx) (base : View BVal) (w v : W) (hI : PutInvG c base w)
    (hr : ReadsAs c.p base w v) : PutInvG c base v := by
  obtain ⟨hN, htop, ht, hvals, hnext⟩ := hr
  have hV : wValue base v = wValue base w := wValue_congr' base v w ht hvals
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hN]; exact hI.wf
  · rw [hN]; exact hI.times
  · intro z hz
    rw [hnext]
    rcases Nat.lt_or_ge z w.next with h | h
    · exact h
    · exfalso
      have htz : v.taken.contains z = false := by
        rw [ht]
        cases h' : w.taken.contains z with
        | false => rfl
        | true => have := hI.ids.2.2.1 z h'; omega
      have hwz : wNode c.p base v z ≠ none := by
        simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte]
        cases hl : v.nodes.lookup z with
        | none => rw [hl] at hz; cases hz
        | some _ => simp
      rw [hN] at hwz
      apply hwz
      have hnz : w.nodes.lookup z = none := by
        cases h' : w.nodes.lookup z with
        | none => rfl
        | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
      simp only [wNode, ← ht, htz, Bool.false_eq_true, ↓reduceIte, hnz, (hI.fresh z h).1]
  · rw [hnext]; exact hI.ids.2.1
  · rw [hnext, ht]; exact hI.ids.2.2.1
  · rw [hnext, hvals]; exact hI.ids.2.2.2
  · rw [hnext]; exact hI.fresh
  · rw [hN, hnext]; exact hI.links
  · rw [hN, hV]; exact hI.keyNoValue

/-- The delete's inner invariant, at a state v inside the delete of `key` from
the state w0 between operations: `PutInv`, its global parts, the walk's ranges,
inner children there, the fuel premise, and the reading of w0 with the key
deleted. -/
def DelInv (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (v : W) : Prop :=
  PutInv c base v ∧ PutInvG c base v ∧ RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
  InnerChildrenExist (wNode c.p base v) c.i v.top.rootKey ∧
  SegFits (wNode c.p base v) c.i (c.p.fuel - 1) v.top.rootKey ∧
  (∀ key', keyWf key' = true →
    wGet c.p c.i base v key' = if key == key' then none else wGet c.p c.i base w0 key') ∧
  ∃ B top0, PutBase c base B ∧ PutBook c B top0 v

theorem delInv_of_readsAs (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (w v : W)
    (h : DelInv c base w0 key w) (hr : ReadsAs c.p base w v)
    (hb : ∃ B top0, PutBase c base B ∧ PutBook c B top0 v) : DelInv c base w0 key v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
  have hV : wValue base v = wValue base w := wValue_congr' base v w hr.2.2.1 hr.2.2.2.1
  refine ⟨putInv_of_readsAs c base w v h1 hr, putInvG_of_readsAs c base w v h2 hr, ?_, ?_, ?_, ?_, hb⟩
  · rw [hr.1, hr.2.1]; exact h3
  · rw [hr.1, hr.2.1]; exact h4
  · rw [hr.1, hr.2.1]; exact h5
  · intro key' hk
    rw [← h6 key' hk]
    unfold wGet
    rw [hr.1, hr.2.1, hV]

end SIS.Tree
