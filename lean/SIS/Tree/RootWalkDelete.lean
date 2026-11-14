/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsSplit.lean:
the descents, which follow klongs of the overlay onto the key access path, and
the delete: the bitmaps, LE-b, the take-back, root collapse and the merges.
-/
import SIS.Tree.RootWalkSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The merges -/

/-- An inner node's klong names a node of its segment. -/
theorem kr_inner_kl {K : KindOracle} {w : W} {g h c : Nat} {y : NodeId} (hh : h ≠ 0)
    (hy : IsKeySeg K w y g) : KindKlong K w g h c y :=
  ⟨fun _ => hy, fun h0 => absurd h0 hh⟩

/-- Klongs of an inner node that name nodes of its segment. -/
syntax "krKsMP " term:max term:max : tactic
macro_rules
  | `(tactic| krKsMP $hm1 $hm2) => `(tactic| first
    | krKsTac
    | exact krKs_repoint _ (by krKsMP $hm1 $hm2) (fun _ _ _ => kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_repoint _ (by krKsMP $hm1 $hm2) (fun _ _ _ => kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_add_key _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_add_key _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_insertSorted _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_replaceKlong (by assumption) (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_replaceKlong (by assumption) (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | (split <;> krKsMP $hm1 $hm2))

end SIS.Tree
