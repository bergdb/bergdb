/-
The walk of a delete with the merges on to its leaf's upward delete (bergdb
024-12, case (4)'s delete steps, `DelEmptyM`): the key's access path from the
space root across its segments (the path premises of the upward delete), with
an invariant J carried along (the books).
-/
import SIS.Tree.DelStepsBook
import SIS.Tree.DelStepsRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `DelInvF` at a state w' inside a delete of key from w0 (between operations,
with `PutInv` and the fuel premise), from `CollGetInv` at w', the walk's ranges
at w', the books at w', and the reading of w' as the delete of key from a state
v that reads as w0. -/
theorem delInvF_of_collGetInv (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w0 v w' : W) (key : Key)
    (hI0 : PutInv c base w0) (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (hrv : ReadsAs c.p base w0 v)
    (hCG : CollGetInv c base w' w') (hRO : RangeOrder (wNode c.p base w') c.i w'.top.rootKey)
    (hbook : PutBook c B top0 w')
    (hread : ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' = if key == key' then none else wGet c.p c.i base v key') :
    DelInvF c base w0 key (c.p.fuel + 1) w' := by
  have hG := putInvG_of_book c base B top0 w' hB hbook
  have hT := hCG.1.1
  have hPI : PutInv c base w' := putInv_of_parts c base w' hG hT
    (fun y hy => hCG.1.2.1 y (reachS_tReach _ _ _ _ hy))
    (leafOrder_of_rangeOrder _ _ _ hRO hG.times)
  refine ⟨hPI, hG, hRO, fun y yn cc z hy hyn hl hz => hCG.1.2.2.2 y yn cc z hy hyn hl hz, ?_, ?_,
    B, top0, hB, hbook⟩
  · simp only [Nat.add_sub_cancel]
    exact segFits_mono _ _ _ _ _ hCG.2.2.1 (by omega)
  · intro key' hk'
    have hwfv : ∀ x xn, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
        wNode c.p base w' x = some xn → klongsWf xn.ks = true := fun x xn _ h => hPI.wf x xn h
    have hwfw : ∀ x xn, ReachS (wNode c.p base w0) c.i w0.top.rootKey x →
        wNode c.p base w0 x = some xn → klongsWf xn.ks = true := fun x xn _ h => hI0.wf x xn h
    rw [wGetAt_eq_wGet c base w' _ (by omega) hwfv hCG.2.2.1, wGetAt_eq_wGet c base w0 _ (by omega) hwfw hF0,
      hread key' hk']
    have hsame : wGet c.p c.i base v key' = wGet c.p c.i base w0 key' := by
      unfold wGet
      rw [hrv.1, hrv.2.1, ReadsAs.value _ _ _ _ hrv]
    rw [hsame]

end SIS.Tree
