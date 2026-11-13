/-
The writer's tree kept by every put at leaf level without an inner split
(bergdb 024-22, `OpTreeOK`), under prover latest's writer invariant `PutInv`
(GetPutInv.lean): a put into a space whose root is a leaf
(`writerWP_put_leafRoot_tree`), and a put into a leaf below inner nodes with
room for two klongs (`writerWP_put_leafBelow_tree`), each case by the rule
that the leaf's state chooses, as in `writerWP_put_leafRoot` and
`writerWP_put_leafBelow`.
-/
import SIS.Tree.WriterTreeMergeOp
import SIS.Tree.GetPutInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `writerWP_appendKlongs_timeSplit_tree` with the split's size premise only
for a node full by its size (`writerWP_appendKlongs_timeSplit_gen`). -/
theorem writerWP_appendKlongs_timeSplit_gen_tree (base : View BVal) (d' : Nat) (L q : NodeId)
    (n qn : KNode) (k1 cv v : Nat) (c : Ctx) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode c.p base w w.next = none) (ht1 : w.taken.contains w.next = false)
    (hvN : wNode c.p base w v = none) (hv1 : v ≠ w.next)
    (hfresh1 : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' w.next)
    (hfreshv : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' v) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hn1 : w.nodes.lookup w.next = none := by
    unfold wNode at hf1; simp only [ht1, Bool.false_eq_true, ↓reduceIte] at hf1
    split at hf1
    · cases hf1
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_timeSplit_gen d' L q n qn k1 cv v c w hlk hlq hqL hql
    hfirst hfull hsplit hpq hpk hroomq hdeadq hn1) ?_
  intro _ w' hA
  exact treeOK_timeSplitAfter c.p base c w w' L q n qn k1 cv v rfl hT hA hwL hwq hqL hqk hq hnt hqt
    hqwf hf1 ht1 hfresh1 hvN hv1 hfreshv

/-- `writerWP_put_timeSplit_seg_tree` with the split's size premise only for a
leaf full by its size. -/
theorem writerWP_put_timeSplit_seg_gen_tree (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  apply writerWP_put_seg_append c base hvc pre cv h rk w hrk ht hidn hidv hinner
    (fun L n hv hn hl => (hleaf L n hv hn hl).2.1)
  intro L n q qn k1 d' w4 hvisL hn hnl hqv hq hql hk1 hqL h4t h4top h4next h4L h4q _ hW4 hpq hpk
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf L n hvisL hn hnl
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hq hql
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt' : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  apply writerWP_appendKlongs_timeSplit_gen_tree base d' L q n qn k1 cv w.next c w4
  · rw [hW4, h4top]; exact hT
  · exact h4L
  · exact h4q
  · rw [h4t]; exact hLt
  · rw [h4t]; exact hqt'
  · exact hqL
  · exact hql
  · exact hfirst
  · exact hfull
  · exact hsplit
  · exact hpq
  · exact hpk
  · exact hroomq
  · exact hdeadq k1
  · exact hk1
  · rw [hW4, h4top]; exact reachS_tReach _ _ _ _ hrq
  · exact htimes
  · exact hqt
  · exact hwf q qn hrq hq
  · rw [hW4, h4next]; exact hfree _ (by omega)
  · rw [h4next, h4t]; exact htn _ (by omega)
  · rw [hW4]; exact hfree _ (Nat.le_refl _)
  · rw [h4next]; omega
  · intro u c' hu; rw [hW4, h4top] at *; rw [h4next]; exact hfreshT _ (by omega) u c' hu
  · intro u c' hu; rw [hW4, h4top] at *; exact hfreshT _ (Nat.le_refl _) u c' hu

/-- The facts of `PutInv` that the tree's put rules take. -/
theorem PutInv.facts (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w) :
    (∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true) ∧
    (∀ z, w.next ≤ z → knodeOf c.p base z = none) ∧
    (∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) ∧
    (∀ z, w.next ≤ z → wNode c.p base w z = none) ∧
    (∀ (key : List Nat), ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key w.top.rootKey,
      w.taken.contains q.1 = false) := by
  obtain ⟨hidn, _, hidt, _, _⟩ := hI.ids
  have hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  refine ⟨hwf, fun z hz => (hI.fresh z hz).1, ?_, ?_, ?_⟩
  · intro z hz u c' hu hl
    obtain ⟨m, hm, hc⟩ := hl
    have := hI.links u m c' z (tReach_reachS _ _ _ _ hu) hm hc
    omega
  · intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, (hI.fresh z hz).1]
  · intro key q hq
    exact hI.untaken q.1 (fromVisits_reach _ _ _ _ hwf key _ q.1 q.2 ReachS.root hq)

/-- Every put into a leaf below inner nodes with room for two klongs keeps the
writer's tree, under `PutInv` (the cases of `writerWP_put_leafBelow`). -/
theorem writerWP_put_leafBelow_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hI : PutInv c base w)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hwf, hbaseF, hfreshT, hfree, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  have ht := htk (pre ++ [cv])
  have hlive : ∀ n : KNode, c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro n hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  have hparent' : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false := by
    intro q qn hq hqn hql
    obtain ⟨a2, a3, a4⟩ := hparent q qn hq hqn hql
    exact ⟨hI.times q qn hqn, a2, a3, a4⟩
  by_cases hex : ∃ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk ∧
      wNode c.p base w L = some n ∧ n.leaf = true
  · obtain ⟨L, n, hL, hn, hnl⟩ := hex
    have hone : ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
        wNode c.p base w L' = some n' → n'.leaf = true → L' = L ∧ n' = n := by
      intro L' n' hL' hn' hnl'
      have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
      subst he
      rw [hn] at hn'
      exact ⟨rfl, (Option.some.inj hn').symm⟩
    have hnwf := hI.wf L n hn
    have htimes := hI.times L n hn
    by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
    · exact writerWP_put_room_seg_tree c base hvc pre cv h rk w hrk ht
        (fun L' n' hL' hn' hnl' => by
          obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
          subst he1 he2
          exact ⟨hnwf, htimes, hroom.1, hroom.2⟩)
        hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
    · by_cases hnew : n.firstTime = some c.i
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact writerWP_put_spaceSplitInPlace_seg_tree c base hvc pre cv h rk w hrk ht
            ⟨hidn, hidv, hidt⟩ hbaseF hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hsp.1, hnew, hsp.2, hlive _ hsp.2⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, _, a4⟩ := hparent' q qn hq hqn hql
              exact ⟨a1, by omega, a4⟩)
            hwf hI.tree hfreshT
        · exact writerWP_put_timeInPlace_seg_tree c base hvc pre cv h rk w hrk ht
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
            hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact writerWP_put_spaceSplit_seg_tree c base hvc pre cv h rk w hrk ht
            ⟨hidn, hidv, hidt⟩ hbaseF hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hsp.1, hnew, hsp.2, hlive _ hsp.2⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, a3, _⟩ := hparent' q qn hq hqn hql
              exact ⟨a1, a2, a3⟩)
            hwf hI.tree hfreshT
        · exact writerWP_put_timeSplit_seg_gen_tree c base hvc pre cv h rk w hrk ht
            ⟨hidn, hidv, hidt⟩ hbaseF hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, _, a4⟩ := hparent' q qn hq hqn hql
              exact ⟨a1, by omega, a4⟩)
            hwf hI.tree hfreshT
  · exact writerWP_put_room_seg_tree c base hvc pre cv h rk w hrk ht
      (fun L' n' hL' hn' hnl' => absurd ⟨L', n', hL', hn', hnl'⟩ hex)
      hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))

/-- Every put into a space whose root is a leaf keeps the writer's tree, under
`PutInv` (the cases of `writerWP_put_leafRoot`). -/
theorem writerWP_put_leafRoot_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode) (hI : PutInv c base w) (hsa : 1 ≤ c.p.splitAbove)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hwf, hbaseF, hfreshT, hfree, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, hidr⟩ := hI.ids
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hev : eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hroot, hnl]
  have hleafAt : ∀ L n', (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w L = some n' → L = w.top.rootKey ∧ n' = n := by
    intro L n' hL hn'
    rw [hev] at hL
    have hL' : L = w.top.rootKey := by simpa using hL
    subst hL'
    rw [hroot] at hn'
    exact ⟨rfl, (Option.some.inj hn').symm⟩
  have hnwf := hI.wf _ _ hroot
  have htimes := hI.times _ _ hroot
  have hrt : w.taken.contains w.top.rootKey = false := hI.untaken _ ReachS.root
  have ht := htk ([] ++ [cv])
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · exact writerWP_put_room_seg_tree c base hvc [] cv h w.top.rootKey w rfl ht
      (fun L n' hL hn' _ => by
        obtain ⟨_, he⟩ := hleafAt L n' hL hn'
        subst he
        exact ⟨hnwf, htimes, hroom.1, hroom.2⟩)
      hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
  · have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
      intro hlt he
      have := KNode.lastVersion_size n c.i
      simp only [KNode.cnt, he, List.length_nil] at this
      omega
    by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_rootSpaceSplitInPlace_tree c base hvc cv h w n hroot hnl hrt
          ⟨htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩ ⟨hidn, hidv, hidt, hidr⟩ hbaseF hI.tree hfreshT
      · exact writerWP_put_timeInPlace_seg_tree c base hvc [] cv h w.top.rootKey w rfl ht
          (fun L n' hL hn' _ => by
            obtain ⟨_, he⟩ := hleafAt L n' hL hn'
            subst he
            exact ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
          hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_rootSpaceSplit_tree c base hvc cv h w n hroot hnl hrt
          ⟨htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩ ⟨hidn, hidv, hidt, hidr⟩ hbaseF hI.tree hfreshT
      · exact writerWP_put_rootTimeSplit_tree c base hvc cv h w n hroot hnl hrt
          ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩
          ⟨hidn, hidv, hidt, hidr⟩ hbaseF hI.tree hfreshT

end SIS.Tree
