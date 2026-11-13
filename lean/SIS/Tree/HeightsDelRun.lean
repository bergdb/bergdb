/-
The delete side of the heights' walk at the run level (bergdb 024-22, step 4;
TP7's (b)): `OpHtDelOK` from the holder family (`HtDelFamily`), and TP7's
`HeightLiveOK` after every run from it (`treeRun_heightLiveOK_family`).

The named premises, for each transaction tx after a run ts: an invariant
J ts tx of the take-back's that holds at every state that tx's earlier
operations reach (`hJ0`), and the family `HtDelFamily` for it: J kept by the
steps between the take-backs, the merge's holder (`MergeTailHoldOK`), the
root's holder (`rootHold`), and the upward delete that empties its leaf
(`upEmpty`).
-/
import SIS.Tree.HeightsRun
import SIS.Tree.WriterHeightsDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- J at every state that a transaction's earlier operations reach, before a
delete. -/
def HtJStart (p : Params) (J : List Tx → Tx → Ctx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    J ts tx (ctxOf p ts) w

/-- The delete side of the walk from the holder family. -/
theorem opHtDelOK_of_family (p : Params) (J : List Tx → Tx → Ctx → W → Prop)
    (hF : ∀ ts tx, Within p (ts ++ [tx]) →
      HtDelFamily tx.base (htOracleOf p (treeRun p ts)) (J ts tx))
    (hJ0 : HtJStart p J) : OpHtDelOK p := by
  intro ts tx hw z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi
  refine writerWP_mono (ht_putKv_del tx.base (J ts tx) (hF ts tx hw) key (ctxOf p ts) w hvo
    (by simp [ctxOf]) hkw hb hi hwf (hJ0 ts tx hw z top hz htop pre key post hsplit r w hpre)) ?_
  rintro _ v ⟨_, hiv, _, _⟩
  exact hiv

/-- TP7's (b) after every run within reach, given the holder family. -/
theorem treeRun_heightLiveOK_family (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (J : List Tx → Tx → Ctx → W → Prop)
    (hF : ∀ ts tx, Within p (ts ++ [tx]) →
      HtDelFamily tx.base (htOracleOf p (treeRun p ts)) (J ts tx))
    (hJ0 : HtJStart p J) (ts : List Tx) (hw : Within p ts) :
    HeightLiveOK p (treeRun p ts) ts.length :=
  treeRun_heightLiveOK p hM hP (opHtDelOK_of_family p J hF hJ0) ts hw

end SIS.Tree
