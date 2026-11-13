/-
Self-indexed streams in Lean: bounded startup in one statement (bergdb item
007; 007-01, 007-03). T3 as a count of transactions (`T3_takeB_count`), T4's
records and debt (`T4_record_gd_height`, `T4_debt_java_tree_height`) and a
cold start's reads (`coldReadsJ_height_noD`) joined. Trusted part: the
statement. The definitions it is about are those of the theorems it joins
(SIS/BoundColdReads.lean, SIS/BoundTakeBytes.lean, SIS/BoundT4.lean,
SIS/BoundT4Java.lean, SIS/BoundHeight.lean, SIS/BoundColdDropJ.lean); the proof
in SIS/Proof/BoundStartup.lean. Added 2026-11-13. No new definition.
-/
import SIS.Proof.BoundStartup

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- **Bounded startup** (007-01, as argued in prose since October 2026): after
any run that meets the assumptions below, a cold start reads at most

  F = (N + 1) (V0 + A + Dm) + 2 + N ((H + 1) A + Dm) Pt + 2 N (H + 1) (A + K) + 2 N B

times, where N = 2 M / m + 2 (the most transactions of a startup section) and
Dm = (1 + Q + ... + Q^Hp) (Hp + 1) N (H + 1) A (the most nodes of D). A read
is a version the start parses, a header read, or a follow of the rerun
(`lazyReads`). F does not grow with the database's size or its age: only with
the setting M, the node height H, the transactions' sizes and the constants of
the tree.

In plain words, for BergDB: the start parses the startup section, which T3
keeps below N transactions (with the take's byte limit, 005-31); each record
of it is a transaction plus the debt D (T4's record), and D holds only nodes
on the access paths of the last Hp + 1 sections (T4's debt), so at most Dm;
the rerun of each of the section's transactions follows at most (H + 1) nodes
per node, entry or touch of its change and per pointer that its removals lose
(the read bound). No term counts the database's keys.

The assumptions, each one explicit:

* the run: `RunOK`, `LiveAppend`, BergDB's still-dirty test (`javaTest`),
  TREE in R(0) and after every transaction;
* T3: the take is Java's with its byte limit (`takePolicyB`), settings at most
  M, every record costing at least m > 0 (its own bytes), and each
  transaction's got-dirty nodes fitting in the limit (`hfit`, 005-31);
* heights: the root's live height at most H after every transaction; the nodes
  of D at most Hp along all pointers, and every node with at most Q pointer
  parents, after every transaction (T4's debt);
* removals: `DropRunOKJ` with weights w and counts k;
* sizes, per transaction T(τ): its change's new nodes, entries, touched nodes
  and the weights of its entries at most A in all; k(τ) at most K; its
  merges' sibling follows `sib` at most B; every version of a top node in
  the stream points to at most Pt nodes (rule 4's top-node header reads);
  R(0) has at most V0 versions.

For 024-12's tree model (`treeSpec`): proved are `LiveAppend` (TP15,
`liveAppendTree`), the take's count (T3 holds for any run), and the kept part
of `DropRunOKJ` with BergDB's weights (`DropRunOKJ_tree`), which leaves the
count k. Open there: `RunOK` (TP14), TREE (TP16, TP7), the height H (the
writer keeps key trees within G and H, but no theorem gives `LiveHeightLe`),
Hp and Q (no uniform Q is known for Java: 007-09's second review), Pt (a top
node has a root pointer and a skip pointer for each set bit of its ordinal,
below 2^48, so about 49 in Java; not proved in the model), A (TP20's `MadeBound` is
the like statement in operations, open), and two that are new:

* K: k is not at most (H + 1) per operation: a merge cascade loses two
  pointers per height (SIS/BoundColdCascadeExample.lean: k = 10 for one delete
  with H = 7). About 2 (H + 1) per operation is the conjecture.
* B: each merge follows at most two siblings (`Dag.merge`: the left one, read
  and possibly rejected, then the right one), so B is twice a transaction's
  merges; the merges of an operation at most the tree's height and one is
  TP32 (CB1), open on main, so B stays a premise. -/
theorem bounded_startup (sp : Spec V T) (al : Algo V T) (ts : List T)
    -- the run
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    -- T3: Java's take with its byte limit
    (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T) (nodeB maxB : Nat)
    (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M m : Nat) (hm0 : 0 < m) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run sp al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB)
    -- heights
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root)
    (Hp Q : Nat)
    (hHp : ∀ t ≤ ts.length, ∀ e ∈ (run sp al (ts.take t)).D,
      PtrHeightLe sp (run sp al (ts.take t)).P Hp e.1)
    (hQ : ∀ t ≤ ts.length, ∀ z, (ptrParents sp (run sp al (ts.take t)).P z).length ≤ Q)
    -- removals
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    -- sizes
    (sib : T → Nat) (A K B Pt V0 : Nat)
    (hA : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
        (changeAt sp al ts τ).touch.length + ((changeAt sp al ts τ).adds.map (fun a => w a.2)).sum ≤ A)
    (hK : ∀ τ, 0 < τ → τ ≤ ts.length → k τ ≤ K)
    (hB : ∀ tr ∈ ts, sib tr ≤ B)
    (hPt : ∀ R ∈ (run sp al ts).S, ∀ v ∈ R.vers, v.node ≠ root → sp.topLevel ≤ v.level →
      (pointees sp v.hist).length ≤ Pt)
    (hV0 : ∀ R ∈ (run sp al []).S, R.vers.length ≤ V0) :
    let N := 2 * M / m + 2
    let Dm := geomSum Q Hp * ((Hp + 1) * N * ((H + 1) * A))
    lazyReads sp sib (run sp al ts).S ≤
      (N + 1) * (V0 + A + Dm) + 2 + N * (((H + 1) * A + Dm) * Pt) +
        2 * (N * ((H + 1) * (A + K))) + 2 * (N * B) := by
  intro N Dm
  have h := bounded_startup_of sp al ts hok hla hj htree0 htree size sd pace nodeB maxB hp M m hm0
    hM hm hfit H hH Hp Q hHp hQ w k hdrop sib A K B Pt V0 hA hK hB hPt hV0
  have hN : 2 * M / m + 3 = N + 1 := rfl
  rw [hN] at h
  exact h

end SIS
