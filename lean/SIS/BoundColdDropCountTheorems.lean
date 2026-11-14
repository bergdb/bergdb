/-
Self-indexed streams in Lean: the count k of `DropStepJ` with TREE, and
bounded startup for 024-12's tree model with it (bergdb item 007;
SIS/BoundColdDropJ.lean, SIS/BoundStartupTheorems.lean). Trusted part: the
statements. The definitions they are about are in SIS/BoundColdDropJ.lean
(`DropStepJ`, `DropRunOKJ`, `lostTo`, `bvalW`), SIS/BoundCold.lean (`removedAt`)
and those of `bounded_startup`; the proofs in SIS/Proof/BoundColdDropCount.lean.
Added 2026-11-13. No new definition.

In plain words: the pointers that the nodes a change makes unreachable lose to
each other go to nodes made unreachable too, and with TREE each of those had
one parent. So k, the count that `DropStepJ` assumes, is at most the number of
nodes the change makes unreachable (`removedAt`): for BergDB the values its
deletes and puts replace, the nodes its splits replace, the nodes its merges
and its upward unlink leave out, a replaced root and the old top node. In the
tree model `DropRunOKJ` then holds with that count and nothing else assumed
beyond TREE (`DropRunOKJ_tree_removed`), and bounded startup needs, in place
of `DropRunOKJ` and k, a bound on the nodes each transaction makes
unreachable (`bounded_startup_tree`). That bound is not (H + 1) per operation
(SIS/BoundColdCascadeExample.lean: 11 nodes for one delete at H = 7); about
2 (H + 1) per operation is the conjecture.
-/
import SIS.Proof.BoundColdDropCount
import SIS.BoundStartupTheorems
import SIS.BoundColdDropJTreeTheorems

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- `DropStepJ.dropped` with TREE: for any change c at time j, with `SpecOK`'s
live pointers among the pointers (`LiveSub`), P's pointers to nodes of P on
lower levels (`PtrsOK`, true after every transaction of a run with `RunOK`)
and TREE at j - 1, the nodes c makes unreachable lose to each other at most as
many pointers as they are. -/
theorem DropStepJ_dropped_removed (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (hls : LiveSub sp) (hptr : PtrsOK sp P) (htr : treeAt sp P (j - 1)) :
    ((removedAt sp P c j).map (fun z => (lostTo sp P (P.apply j c) j z).length)).sum ≤
      (removedAt sp P c j).length :=
  dropped_le_removed sp P j c hls hptr htr

/-- `DropRunOKJ` in BergDB's tree model with BergDB's weights and, for each
transaction T(τ), k(τ) the number of nodes it makes unreachable: with `RunOK`,
BergDB's still-dirty test and TREE in R(0) and after every transaction, and
nothing else. -/
theorem DropRunOKJ_tree_removed (p : Tree.Params) (al : Algo Check.BVal Tree.Tx)
    (ts : List Tree.Tx) (hok : RunOK (Tree.treeSpec p) al ts)
    (hj : al.stillDirty = javaTest (Tree.treeSpec p))
    (htree0 : treeAt (Tree.treeSpec p) (run (Tree.treeSpec p) al []).P 0)
    (htree : TreeRunOK (Tree.treeSpec p) al ts) :
    DropRunOKJ (Tree.treeSpec p) al bvalW (fun τ =>
      (removedAt (Tree.treeSpec p) (run (Tree.treeSpec p) al (ts.take (τ - 1))).P
        (changeAt (Tree.treeSpec p) al ts τ) τ).length) ts := by
  apply DropRunOKJ_tree p al ts hok (Or.inl hj)
  intro j hj'
  dsimp only
  rw [Nat.add_sub_cancel, changeAt_succ_exec (Tree.treeSpec p) al ts hj']
  apply dropped_le_removed
  · exact hok.1.liveSub
  · exact (inv_st _ al ts hok (algOK_of _ al (Or.inl hj)) j (by omega)).ptrs
  · rw [Nat.add_sub_cancel]
    cases j with
    | zero => simpa using htree0
    | succ i => exact htree i (by omega)

/-- **Bounded startup for BergDB's tree model** (`bounded_startup` with
`treeSpec`, BergDB's weights `bvalW` and `DropRunOKJ_tree_removed`): the
assumptions of `bounded_startup` without `DropRunOKJ` and k, and with K a
bound on the nodes each transaction makes unreachable (`removedAt`). A cold
start then reads at most

  (N + 1) (V0 + A + Dm) + 2 + N ((H + 1) A + Dm) Pt + 2 N (H + 1) (A + K) + 2 N B

times, N = 2 M / m + 2, Dm = (1 + Q + ... + Q^Hp) (Hp + 1) N (H + 1) A. Of the
assumptions, `LiveAppend` is proved (TP15, `liveAppendTree`); the others are
open for the tree model, as `bounded_startup` says. -/
theorem bounded_startup_tree (p : Tree.Params) (al : Algo Check.BVal Tree.Tx) (ts : List Tree.Tx)
    -- the run
    (hok : RunOK (Tree.treeSpec p) al ts) (hla : LiveAppend (Tree.treeSpec p))
    (hj : al.stillDirty = javaTest (Tree.treeSpec p))
    (htree0 : treeAt (Tree.treeSpec p) (run (Tree.treeSpec p) al []).P 0)
    (htree : TreeRunOK (Tree.treeSpec p) al ts)
    -- T3: Java's take with its byte limit
    (size : Record Check.BVal Tree.Tx → Nat) (sd : Time → Nat) (pace : Pace Check.BVal Tree.Tx)
    (nodeB maxB : Nat) (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M m : Nat) (hm0 : 0 < m) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run (Tree.treeSpec p) al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run (Tree.treeSpec p) al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB)
    -- heights
    (H : Nat)
    (hH : ∀ t ≤ ts.length, LiveHeightLe (Tree.treeSpec p) (run (Tree.treeSpec p) al (ts.take t)).P t H root)
    (Hp Q : Nat)
    (hHp : ∀ t ≤ ts.length, ∀ e ∈ (run (Tree.treeSpec p) al (ts.take t)).D,
      PtrHeightLe (Tree.treeSpec p) (run (Tree.treeSpec p) al (ts.take t)).P Hp e.1)
    (hQ : ∀ t ≤ ts.length, ∀ z,
      (ptrParents (Tree.treeSpec p) (run (Tree.treeSpec p) al (ts.take t)).P z).length ≤ Q)
    -- sizes
    (sib : Tree.Tx → Nat) (A K B Pt V0 : Nat)
    (hA : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt (Tree.treeSpec p) al ts τ).new.length + (changeAt (Tree.treeSpec p) al ts τ).adds.length +
        (changeAt (Tree.treeSpec p) al ts τ).touch.length +
        ((changeAt (Tree.treeSpec p) al ts τ).adds.map (fun a => bvalW a.2)).sum ≤ A)
    (hK : ∀ τ, 0 < τ → τ ≤ ts.length →
      (removedAt (Tree.treeSpec p) (run (Tree.treeSpec p) al (ts.take (τ - 1))).P
        (changeAt (Tree.treeSpec p) al ts τ) τ).length ≤ K)
    (hB : ∀ tr ∈ ts, sib tr ≤ B)
    (hPt : ∀ R ∈ (run (Tree.treeSpec p) al ts).S, ∀ v ∈ R.vers, v.node ≠ root →
      (Tree.treeSpec p).topLevel ≤ v.level → (pointees (Tree.treeSpec p) v.hist).length ≤ Pt)
    (hV0 : ∀ R ∈ (run (Tree.treeSpec p) al []).S, R.vers.length ≤ V0) :
    let N := 2 * M / m + 2
    let Dm := geomSum Q Hp * ((Hp + 1) * N * ((H + 1) * A))
    lazyReads (Tree.treeSpec p) sib (run (Tree.treeSpec p) al ts).S ≤
      (N + 1) * (V0 + A + Dm) + 2 + N * (((H + 1) * A + Dm) * Pt) +
        2 * (N * ((H + 1) * (A + K))) + 2 * (N * B) :=
  bounded_startup (Tree.treeSpec p) al ts hok hla hj htree0 htree size sd pace nodeB maxB hp M m
    hm0 hM hm hfit H hH Hp Q hHp hQ bvalW _ (DropRunOKJ_tree_removed p al ts hok hj htree0 htree)
    sib A K B Pt V0 hA hK hB hPt hV0

end SIS
