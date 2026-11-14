/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsRules.lean:
the tactics of the walk, a full node's replacement (`handleFullWith`) and
`appendKlongs`.
-/
import SIS.Tree.RootWalkRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Helpers -/

theorem KrLe.gh' {w v : W} {e : NodeId × Nat × Nat} (h : e ∈ w.gh) (hk : KrLe w v) : e ∈ v.gh :=
  hk.1.2 e h

/-- A new root above x and y of segment g. -/
theorem kr_root3 {K : KindOracle} {w : W} {x y : NodeId} {g h h' : Nat} (t : Time) (sc : Nat)
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) (h'' : Nat) :
    krKs (KindKlong K w g (h'' + 1)) [.time t, .key 0 x, .key sc y] := by
  refine krKs_cons_time t (krKs_cons_key ?_ (krKs_cons_key ?_ (krKs_nil _)))
  · exact ⟨fun _ => kr_isKey hx, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · exact ⟨fun _ => kr_isKey hy, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩

/-- The klongs of a node read at an earlier state, for its entry in `gh`. -/
theorem kr_cache_at {K : KindOracle} {B : NodeId} {vr v : W} {x : NodeId} {n : KNode} {g h : Nat}
    (hl : vr.nodes.lookup x = some n) (hi : KrInv K B vr) (hm : (x, g, h) ∈ vr.gh)
    (hk : KrLe vr v) : krKs (KindKlong K v g h) n.ks :=
  krKs_mono (kr_cache_node hi hl hm) hk

/-! ## The tactics of the walk -/

/-- `KrLe a b` along the chain of the steps' hypotheses `KrLe v1 v2`. -/
syntax "krChain" : tactic
macro_rules
  | `(tactic| krChain) => `(tactic| first
    | exact KrLe.refl _
    | assumption
    | (refine KrLe.trans ?krL (by assumption); krChain))

/-- `v.path = w.path` along the chain of the steps' hypotheses. -/
syntax "krPathEq" : tactic
macro_rules
  | `(tactic| krPathEq) => `(tactic| first
    | rfl
    | assumption
    | (refine Eq.trans (by assumption) ?krP; krPathEq))

/-- An entry of `gh` at an earlier state. -/
macro "krTag" : tactic => `(tactic| first
  | assumption
  | exact KrLe.gh' (by assumption) (by krChain))

/-- Klongs of the right kind for a node's entry. -/
syntax "krKsTac" : tactic
macro_rules
  | `(tactic| krKsTac) => `(tactic| first
    | exact krKs_nil _
    | exact krKs_mono (by assumption) (by krChain)
    | exact (krKs_halves _ _ (kr_free_of_leaf (by assumption)) (krKs_mono (by assumption) (by krChain))
        (krPairs_mono (by assumption) (by krChain))).1
    | exact (krKs_halves _ _ (kr_free_of_leaf (by assumption)) (krKs_mono (by assumption) (by krChain))
        (krPairs_mono (by assumption) (by krChain))).2
    | exact kr_root3 _ _ (by krTag) (by krTag) _
    | exact kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain)
    | exact krKs_toPrev _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_setAt_del _ _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_add_del _ _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_lastVersionGivenDel _ _
        (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_renameKey _ (kr_free (by assumption)) (by assumption)
        (krKs_lastVersionGivenDel _ _
          (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain)))
    | (split <;> krKsTac))

/-! ## A full node's replacement -/

/-! ## `appendKlongs` -/

end SIS.Tree
