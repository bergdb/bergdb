/-
The merge under a parent with room keeps the take-back's (B) (bergdb 024-12,
TP4; `TtReachedN`, TakeInvTree.lean): the two nodes merged, l and r, give way
to the new nodes, which the parent names; every node reached before but l and r
is reached after (`reach_merge`), and l and r, unlinked, keep no klong of the
transaction's time.
-/
import SIS.Tree.TakeInvUp
import SIS.Tree.WriterGetMergeTail
import SIS.Tree.RangeMerge
import SIS.Tree.RangeMergeMade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A merge at node-map level: under the reached parent p, its children l and rr
(by klongs cL and cR) give way to new nodes ms that p names; the live children
of l and rr are children of the new nodes; p keeps its other live klongs.
Every node reached before is reached after, or is l or rr, and then p is. -/
theorem reach_merge (N N' : NodeId → Option KNode) (t : Time) (r p l rr : NodeId) (ms : List NodeId)
    (pn ln rn pn' : KNode) (cL cR : Nat) (hT : TreeOK N t r) (hp : TReach N t r p)
    (hpn : N p = some pn) (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hmsN : ∀ m ∈ ms, N m = none)
    (hN'p : N' p = some pn')
    (hpkeep : ∀ c z, (c, z) ∈ pn.liveAt t → c ≠ cL → c ≠ cR → (c, z) ∈ pn'.liveAt t)
    (hpnew : ∀ m ∈ ms, ∃ c, (c, m) ∈ pn'.liveAt t)
    (hcover : ∀ c z, ((c, z) ∈ ln.liveAt t ∨ (c, z) ∈ rn.liveAt t) →
      ∃ m ∈ ms, ∃ mn c', N' m = some mn ∧ (c', z) ∈ mn.liveAt t)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ∉ ms → N' y = N y) :
    ∀ u, TReach N t r u →
      ((u ≠ l ∧ u ≠ rr) ∧ TReach N' t r u) ∨ ((u = l ∨ u = rr) ∧ TReach N' t r p) := by
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hrootl : r ≠ l := fun h => hT.rootFree p cL hp (h ▸ hlink_l)
  have hrootr : r ≠ rr := fun h => hT.rootFree p cR hp (h ▸ hlink_r)
  -- a reached node linking l or rr is p
  have honlyP : ∀ a c, TReach N t r a → (TLink N t a c l → a = p ∧ c = cL) ∧
      (TLink N t a c rr → a = p ∧ c = cR) :=
    fun a c ha => ⟨fun h => hT.oneLink a c p cL l ha hp h hlink_l,
      fun h => hT.oneLink a c p cR rr ha hp h hlink_r⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  intro u hu
  induction hu with
  | root => exact Or.inl ⟨⟨hrootl, hrootr⟩, TReach.root⟩
  | @link a c u ha hlk ih =>
    obtain ⟨an, han, hau⟩ := hlk
    have hlk' : TLink N t a c u := ⟨an, han, hau⟩
    by_cases hal : a = l ∨ a = rr
    · -- a child of l or rr: a child of a new node
      have hpR' : TReach N' t r p := by
        rcases ih with ⟨⟨h1, h2⟩, _⟩ | ⟨_, h⟩
        · rcases hal with h | h
          · exact absurd h h1
          · exact absurd h h2
        · exact h
      have hmem : (c, u) ∈ ln.liveAt t ∨ (c, u) ∈ rn.liveAt t := by
        rcases hal with h | h
        · rw [h, hln] at han; cases han; exact Or.inl hau
        · rw [h, hrn] at han; cases han; exact Or.inr hau
      obtain ⟨m, hm, mn, c', hmn, hmu⟩ := hcover c u hmem
      obtain ⟨cm, hcm⟩ := hpnew m hm
      have hmR : TReach N' t r m := TReach.link hpR' ⟨pn', hN'p, hcm⟩
      refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩, TReach.link hmR ⟨mn, hmn, hmu⟩⟩
      · have := ((honlyP a c ha).1 (hul ▸ hlk')).1
        rcases hal with h | h
        · rw [h] at this; exact hpl this.symm
        · rw [h] at this; exact hpr this.symm
      · have := ((honlyP a c ha).2 (hur ▸ hlk')).1
        rcases hal with h | h
        · rw [h] at this; exact hpl this.symm
        · rw [h] at this; exact hpr this.symm
    · have haR' : TReach N' t r a := by
        rcases ih with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hal
      have hal' : a ≠ l ∧ a ≠ rr := ⟨fun h => hal (Or.inl h), fun h => hal (Or.inr h)⟩
      by_cases hap : a = p
      · rw [hap, hpn] at han
        cases han
        rw [hap] at haR' ha
        by_cases hcl : c = cL
        · rw [hcl] at hau
          exact Or.inr ⟨Or.inl (KNode.liveAt_fun pn t cL l u hl hau).symm, haR'⟩
        · by_cases hcr : c = cR
          · rw [hcr] at hau
            exact Or.inr ⟨Or.inr (KNode.liveAt_fun pn t cR rr u hrr hau).symm, haR'⟩
          · refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩,
              TReach.link haR' ⟨pn', hN'p, hpkeep c u hau hcl hcr⟩⟩
            · rw [hul] at hau
              exact hcl ((honlyP p c hp).1 ⟨pn, hpn, hau⟩).2
            · rw [hur] at hau
              exact hcr ((honlyP p c hp).2 ⟨pn, hpn, hau⟩).2
      · have ham : a ∉ ms := fun h => by rw [hmsN a h] at han; cases han
        have hl2 : TLink N' t a c u := ⟨an, by rw [hother a hap hal'.1 hal'.2 ham]; exact han, hau⟩
        refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩, TReach.link haR' hl2⟩
        · exact hap ((honlyP a c ha).1 (hul ▸ hlk')).1
        · exact hap ((honlyP a c ha).2 (hur ▸ hlk')).1

/-- (B) after a merge: l and rr without a klong of time t after. -/
theorem ttReachedN_merge (N N' : NodeId → Option KNode) (t : Time) (r p l rr : NodeId)
    (ms : List NodeId) (pn ln rn pn' : KNode) (cL cR : Nat) (hT : TreeOK N t r) (hp : TReach N t r p)
    (hpn : N p = some pn) (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hmsN : ∀ m ∈ ms, N m = none)
    (hN'p : N' p = some pn')
    (hpkeep : ∀ c z, (c, z) ∈ pn.liveAt t → c ≠ cL → c ≠ cR → (c, z) ∈ pn'.liveAt t)
    (hpnew : ∀ m ∈ ms, ∃ c, (c, m) ∈ pn'.liveAt t)
    (hcover : ∀ c z, ((c, z) ∈ ln.liveAt t ∨ (c, z) ∈ rn.liveAt t) →
      ∃ m ∈ ms, ∃ mn c', N' m = some mn ∧ (c', z) ∈ mn.liveAt t)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ∉ ms → N' y = N y)
    (hfate : ∀ y yn, (y = l ∨ y = rr) → N' y = some yn → Klong.time t ∉ yn.ks)
    (hL : TtReachedN N t r) : TtReachedN N' t r := by
  have hR := reach_merge N N' t r p l rr ms pn ln rn pn' cL cR hT hp hpn hl hrr hln hrn hmsN hN'p
    hpkeep hpnew hcover hother
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpR' : TReach N' t r p := by
    rcases hR p hp with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · rcases h with h | h
      · exact absurd h hpl
      · exact absurd h hpr
  intro u un hu hm
  by_cases hulr : u = l ∨ u = rr
  · exact absurd hm (hfate u un hulr hu)
  · by_cases hums : u ∈ ms
    · obtain ⟨cm, hcm⟩ := hpnew u hums
      exact TReach.link hpR' ⟨pn', hN'p, hcm⟩
    · by_cases hup : u = p
      · rw [hup]; exact hpR'
      · rw [hother u hup (fun h => hulr (Or.inl h)) (fun h => hulr (Or.inr h)) hums] at hu
        rcases hR u (hL u un hu hm) with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hulr

end SIS.Tree
