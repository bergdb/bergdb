import SIS.Tree.PutInvSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The put rules together (bergdb 024-12, TP10): every put of a key whose
prefix is there into a leaf below inner nodes with room for two klongs keeps
`PutInv` (`putInv_put_leafBelow`, the rules of `writerWP_put_leafBelow`): with
room, by a time split or a space split, in place for a leaf the transaction
made. The writer's tree after it is given (cost's `OpTreeOK`). -/

theorem putInv_put_leafBelow (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  have hlive : ∀ n : KNode, c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro n hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  by_cases hex : ∃ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk ∧
      wNode c.p base w L = some n ∧ n.leaf = true
  · obtain ⟨L, n, hL, hn, hnl⟩ := hex
    have hat : ∀ (P : KNode → Prop), P n → ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv
        c.p.fuel rk → wNode c.p base w L' = some n' → n'.leaf = true → P n' := by
      intro P hP L' n' hL' hn' hnl'
      have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
      subst he
      rw [hn] at hn'
      cases hn'
      exact hP
    by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
    · exact putInv_put_room_below c base B top0 hB pre cv h rk w hI hw hrk hinner
        (hat (fun m => m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) hroom)
    · by_cases hnew : n.firstTime = some c.i
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact putInv_put_spaceSplitInPlace_below c base B top0 hB pre cv h rk w hI hw hrk hinner
            (hat (fun m => c.p.M ≤ m.size + 1 ∧ m.firstTime = some c.i ∧
              c.p.splitAbove < (m.lastVersion c.i).size ∧ m.live ≠ [])
              ⟨hsp.1, hnew, hsp.2, hlive n hsp.2⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, _, a3⟩ := hparent q qn hq hqn hql
              exact ⟨by omega, a3⟩)
        · exact putInv_put_timeInPlace_below c base B top0 hB pre cv h rk w hI hw hrk hinner
            (hat (fun m => ¬ (m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) ∧
              m.firstTime = some c.i ∧ (c.p.M ≤ m.size + 1 → (m.lastVersion c.i).size ≤ c.p.splitAbove))
              ⟨hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact putInv_put_spaceSplit_below c base B top0 hB pre cv h rk w hI hw hrk hinner
            (hat (fun m => c.p.M ≤ m.size + 1 ∧ m.firstTime ≠ some c.i ∧
              c.p.splitAbove < (m.lastVersion c.i).size ∧ m.live ≠ [])
              ⟨hsp.1, hnew, hsp.2, hlive n hsp.2⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, _⟩ := hparent q qn hq hqn hql
              exact ⟨a1, a2⟩)
        · exact putInv_put_timeSplit_below c base B top0 hB pre cv h rk w hI hw hrk hinner
            (hat (fun m => ¬ (m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) ∧
              m.firstTime ≠ some c.i ∧ (c.p.M ≤ m.size + 1 → (m.lastVersion c.i).size ≤ c.p.splitAbove))
              ⟨hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, _, a3⟩ := hparent q qn hq hqn hql
              exact ⟨by omega, a3⟩)
  · exact putInv_put_room_below c base B top0 hB pre cv h rk w hI hw hrk hinner
      (fun L' n' hL' hn' hnl' => absurd ⟨L', n', hL', hn', hnl'⟩ hex)

end SIS.Tree
