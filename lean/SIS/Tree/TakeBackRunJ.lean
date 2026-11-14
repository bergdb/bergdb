/-
The take-back's joint induction with (B), (C) and their node facts kept
together by every operation (bergdb 024-12, TP7; `TakeInvJ`): the form in which
the rule lemmas give them (`TakeJ2`, `J2N`), with a state predicate S that the
assembly gives at every state between operations (latest's `PutInv`, the walk's
ranges, the books, the kinds). The first state's node facts but one hold of P;
that P's key nodes start before the transaction (`BaseStartOK`) is a premise.
-/
import SIS.Tree.TakeBackRunU
import SIS.Tree.TakeDeadCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (A), and (B), (C) with their node facts. -/
def TakeInvJ (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Prop :=
  ReachedFree p P t w ∧ J2N (wNode p (viewOf P) w) t w.top.rootKey B (w.vals.map (·.1))

/-- S at every state that a prefix of a transaction's operations reaches. -/
def StateOK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
    (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → S ts tx w

/-- P's key nodes start before the next transaction. -/
def BaseStartOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ q qn,
    knodeOf p (viewOf (treeRun p ts)) q = some qn → ∃ s, s < ts.length + 1 ∧ qn.firstTime = some s

/-- `TakeInvJ` at a transaction's first state. -/
theorem takeInvJ_init (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (top : Top)
    (hB : ∀ q qn, knodeOf p (viewOf (treeRun p ts)) q = some qn →
      ∃ s, s < ts.length + 1 ∧ qn.firstTime = some s) :
    TakeInvJ p (treeRun p ts) (ts.length + 1) tx.base (wInit tx top) := by
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  have hT := takeInvT_init p ts tx hw top
  -- the base's nodes and their klongs are below B
  have hid : ∀ q qn, knodeOf p (viewOf (treeRun p ts)) q = some qn → q < tx.base := by
    intro q qn hq
    unfold knodeOf viewOf at hq
    cases hg : (treeRun p ts).get? q with
    | none => simp [hg] at hq
    | some nd => exact hfresh _ (mem_of_get? hg)
  have hptr : ∀ q qn, knodeOf p (viewOf (treeRun p ts)) q = some qn →
      ∀ cv y, Klong.key cv y ∈ qn.ks → y < tx.base := by
    intro q qn hq cv y hk
    unfold knodeOf viewOf at hq
    cases hg : (treeRun p ts).get? q with
    | none => simp [hg] at hq
    | some nd =>
      simp only [hg] at hq
      split at hq
      · cases hq
      · simp only [Option.some.injEq] at hq
        subst hq
        obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist cv y hk
        have hy := hR.1 _ (mem_of_get? hg) e he y (by rw [hv]; simp [bptrs])
        obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hy
        exact hfresh _ (mem_of_get? hny)
  refine ⟨hT.1, hT.2, deadLive_init p ts tx hw hR top, ?_, ?_, ?_, ?_⟩
  · intro q qn hq cv y hk
    rw [hlook] at hq
    apply hptr q qn hq cv y
    obtain ⟨rest, hrest⟩ : ∃ rest, prefixAt qn.ks (ts.length + 1 - 1) ++ rest = qn.ks :=
      List.takeWhile_prefix _
    rw [← hrest]; exact List.mem_append_left _ hk
  · intro q qn hq _
    rw [hlook] at hq
    obtain ⟨s, hs, hf⟩ := hB q qn hq
    exact ⟨s, hs, hf⟩
  · intro q qn hq hqB
    rw [hlook] at hq
    have := hid q qn hq
    omega
  · intro y hy
    simp [wInit] at hy

end SIS.Tree
