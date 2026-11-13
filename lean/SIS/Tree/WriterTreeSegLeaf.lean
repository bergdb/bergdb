/-
Every put into a segment root that is a leaf below the segment leaf of the
segment above keeps the writer's tree under `PutInv` (bergdb 024-22,
`OpTreeOK`; the cases of prover latest's `writerWP_put_segLeaf_inv`):
`writerWP_put_segLeaf_tree`.
-/
import SIS.Tree.WriterTreeSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_put_segLeaf_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W) (hI : PutInv c base w)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hwf, hbaseF, hfreshT, hfree, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
    rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  have ht := htk (pre0 ++ [k1, cv])
  have ht' : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel ((pre0 ++ [k1]) ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := htk _
  have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hNL, hnl]
  have hat : ∀ (P : KNode → Prop), P n → ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv
      c.p.fuel L → wNode c.p base w L' = some n' → n'.leaf = true → P n' := by
    intro P hP L' n' hL' hn' _
    rw [hevL] at hL'
    have : L' = L := by simpa using hL'
    subst this
    rw [hNL] at hn'
    cases hn'
    exact hP
  have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  have hsegT : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true → ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i :=
    fun q qn _ hqn _ => hI.times q qn hqn
  have hnwf := hI.wf L n hNL
  have htimes := hI.times L n hNL
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · rw [hkey']
    exact writerWP_put_room_seg_tree c base hvc (pre0 ++ [k1]) cv h L w hsegL ht'
      (fun L' n' hL' hn' hnl' => hat (fun m => klongsWf m.ks = true ∧
        (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧ m.size + 1 < c.p.M ∧
        deadOver c.p (m.add c.i (.key cv w.next)) = false)
        ⟨hnwf, htimes, hroom.1, hroom.2⟩ L' n' hL' hn' hnl')
      hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
  · by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_segSpaceSplitInPlace_tree c base hvc pre0 k1 cv h rq L n w hrq ht
          ⟨hidn, hidv, hidt⟩ hbaseF hL hNL hnl ⟨htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩ hsegT
          hwf hI.tree hfreshT
      · rw [hkey']
        exact writerWP_put_timeInPlace_seg_tree c base hvc (pre0 ++ [k1]) cv h L w hsegL ht'
          (fun L' n' hL' hn' hnl' => hat (fun m =>
            (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧
            ¬ (m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) ∧
            m.firstTime = some c.i ∧ (c.p.M ≤ m.size + 1 → (m.lastVersion c.i).size ≤ c.p.splitAbove))
            ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩
            L' n' hL' hn' hnl')
          hwf hI.tree (hfree _ (Nat.le_refl _)) (hfreshT _ (Nat.le_refl _))
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_segSpaceSplit_tree c base hvc pre0 k1 cv h rq L n w hrq ht
          ⟨hidn, hidv, hidt⟩ hbaseF hL hNL hnl ⟨htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩
          (fun q qn hq hqn hql => ⟨hI.times q qn hqn, (hseg q qn hq hqn hql).1,
            (hseg q qn hq hqn hql).2⟩)
          hwf hI.tree hfreshT
      · exact writerWP_put_segTimeSplit_tree c base hvc pre0 k1 cv h rq L n w hrq ht
          ⟨hidn, hidv, hidt⟩ hbaseF hL hNL hnl
          ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩
          (fun q qn hq hqn hql => ⟨hI.times q qn hqn, (hseg q qn hq hqn hql).1,
            (hseg q qn hq hqn hql).2⟩)
          hwf hI.tree hfreshT

end SIS.Tree
