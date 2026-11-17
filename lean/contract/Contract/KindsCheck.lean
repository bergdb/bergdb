/-
The contract package (bergdb 030-17): K-LEVEL in the contract checker
(ContractCheck.lean), as 030-14 put it in the bridge checker (KIND,
RecoverCheck.lean).

K-LEVEL (bergdb 030-14, Recover.lean): a key node's kind, segment leaf or
inner node, is a function of its level. The kind function of a trace is the
TREE line's: `kindOfHeight h`, a segment leaf if its height in its segment
tree is 0 (`traceKind`). In the contract's words (`KindsAll kind s`): every
key node of the tree s has the kind of its level.

The checker computes it as the bridge checker does: every key node of the
start heap that `TX 0` makes (`startKindsB`), and every key node of D after
each transaction (`kindsOk`, Recover.lean). A key node not in D is as it was
(the frame, clause 3 of the contract), so with the contract that gives
K-LEVEL for every key node of every tree of the history
(`checkVerdict_sound`).

The checker's verdict (`checkVerdict`): 030-15's `contractVerdict` and
K-LEVEL on the trace's history. `checkVerdict_sound` proves that a trace with
that verdict is whole, readable, a history that meets the contract with TREE
and the top (`MeetsTop`, as `contractVerdict_sound`), and that the start tree
and the tree after each of its transactions meet K-LEVEL with the TREE line's
h. To read and to trust, with Verdict.lean and Recover.lean.
Nothing here needs Mathlib.
-/
import Contract.Verdict
import Contract.Recover

namespace Contract

/-- K-LEVEL for a tree, in the contract's words: every key node of s has the
kind of its level. -/
def KindsAll (kind : Nat → Bool) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → n.leaf = kind n.level

/-- The kind function of a trace: its TREE line's h. -/
def traceKind (tr : Trace) : Nat → Bool := kindOfHeight tr.shape.H

/-- K-LEVEL for every key node of a heap, computed (as RecoverCheck.lean's
`startKindsOk`). -/
def startKindsB (kind : Nat → Bool) (h0 : Heap) : Bool :=
  h0.objs.toList.all (fun xo => match xo.2 with
    | .key n => n.leaf == kind n.level
    | _ => true)

/-- K-LEVEL on a trace read, computed: every key node of the start that
`TX 0` makes, and every key node of D after each transaction after it. -/
def traceKindsOk (tr : Trace) : Bool :=
  match tr.txs.toList with
  | [] => false
  | tx0 :: rest =>
    startKindsB (traceKind tr) (traceStart tx0).1 &&
      (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty rest).all
        (fun st => kindsOk (traceKind tr) st.2.2.1.tree st.2.1)

/-- The contract checker's verdict on a trace's lines (bergdb 030-17): 030-15's
`contractVerdict`, and K-LEVEL on its history. -/
def checkVerdict (lines : Array String) : Bool :=
  contractVerdict lines &&
    match readTrace lines with
    | .ok tr => traceKindsOk tr
    | .error _ => false

/-! ## The verdict is sound -/

theorem startKindsB_sound {kind : Nat → Bool} {h0 : Heap} (hc : startKindsB kind h0 = true) :
    KindsAll kind h0.tree := by
  intro x n hx
  have hm : (x, Obj.key n) ∈ h0.objs.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx
  have := List.all_eq_true.mp hc _ hm
  simpa using this

/-- One transaction keeps K-LEVEL: a key node not in D is as it was (the
frame), one in D is checked. -/
theorem kinds_frame {kind : Nat → Bool} {i : Time} {s s' : Tree} {D : List NodeId}
    (hk : KindsAll kind s) (hf : Frame i s D s') (hd : kindsOk kind s' D = true) :
    KindsAll kind s' := by
  intro x n hx
  by_cases hxD : x ∈ D
  · have := List.all_eq_true.mp hd x hxD
    rw [hx] at this
    simpa using this
  · cases hs : s.obj x with
    | none => exact absurd (hf.2.1 x n hx hs) hxD
    | some o =>
      obtain ⟨o', ho', _, heq⟩ := hf.1 x o hs
      rw [heq hxD] at ho'
      rw [hx] at ho'
      cases ho'
      exact hk x n hs

/-- Along a traced history that passes `historyTopOk`, from a tree that meets
K-LEVEL, each step whose D is checked keeps it. -/
theorem kinds_steps (p : Params) (kind : Nat → Bool) :
    ∀ (steps : List (List Op × List NodeId × Heap × Top)) (i : Time) (h : Heap) (tp : Top),
      KindsAll kind h.tree → historyTopOk p i h tp steps = true →
      steps.all (fun st => kindsOk kind st.2.2.1.tree st.2.1) = true →
      ∀ st ∈ steps, KindsAll kind st.2.2.1.tree
  | [], _, _, _, _, _, _ => by simp
  | (ops, D, h', tp') :: rest, i, h, tp, hk, hc, ha => by
    simp only [historyTopOk, Bool.and_eq_true] at hc
    simp only [List.all_cons, Bool.and_eq_true] at ha
    obtain ⟨⟨_, hfr⟩, _, _, _⟩ := checkTopTx_sound p i h tp ops D h' tp' hc.1
    have hk' : KindsAll kind h'.tree := kinds_frame hk hfr ha.1
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact hk'
    · exact kinds_steps p kind rest (i + 1) h' tp' hk' hc.2 ha.2 st hst

/-- The contract checker's verdict (`checkVerdict`, what `contractcheck` passes
a trace on since bergdb 030-17) is sound: the trace is whole and readable, its
history meets the contract with TREE and the top (`MeetsTop`), and the start
tree and the tree after each of its transactions meet K-LEVEL with the kinds
that the TREE line's h gives. -/
theorem checkVerdict_sound (lines : Array String) (hv : checkVerdict lines = true) :
    completeFault lines = none ∧ ∃ tr, readTrace lines = .ok tr ∧ readsOk tr = true ∧
      ∃ tx0 rest, tr.txs.toList = tx0 :: rest ∧
        MeetsTop { M := tr.M } (rest.map (·.ops))
          (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
            rest)).1.tree
          (lastTop (traceStart tx0) (traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty
            rest)).2 ∧
        KindsAll (traceKind tr) (traceStart tx0).1.tree ∧
        ∀ st ∈ traceSteps (traceStart tx0).1 (traceStart tx0).2 tx0.dirty rest,
          KindsAll (traceKind tr) st.2.2.1.tree := by
  unfold checkVerdict at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨hc, hk⟩ := hv
  obtain ⟨hf, tr, hr, hreads, tx0, rest, htx, hmt⟩ := contractVerdict_sound lines hc
  refine ⟨hf, tr, hr, hreads, tx0, rest, htx, hmt, ?_⟩
  rw [hr] at hk
  simp only at hk
  have htop : traceTopOk tr = true := by
    unfold contractVerdict at hc
    simp only [Bool.and_eq_true, hr] at hc
    exact hc.2.1
  unfold traceKindsOk at hk
  unfold traceTopOk at htop
  rw [htx] at hk htop
  simp only [Bool.and_eq_true] at hk htop
  have h0 := startKindsB_sound hk.1
  exact ⟨h0, kinds_steps { M := tr.M } (traceKind tr) _ 1 _ _ h0 htop.2 hk.2⟩

end Contract
