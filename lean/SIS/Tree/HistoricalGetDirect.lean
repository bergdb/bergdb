import SIS.Tree.HistoricalGet

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.searchBy_eq_of_prefix (a b : KNode) (t : Nat)
    (better : Nat → Option Nat → Bool) (he : prefixAt a.ks t = prefixAt b.ks t) :
    a.searchBy t better = b.searchBy t better := by
  simp only [KNode.searchBy, he]

end SIS.Tree
