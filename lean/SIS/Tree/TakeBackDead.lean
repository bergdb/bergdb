/-
The take-back's (C) (bergdb 024-12, TP4; `DeadTakenLive`, TakeBackRun.lean) in
the form every operation keeps: `DeadLive`, a klong of a kept node to a node at
or above B that is no value comes with a live klong of the same node to it, and
in a segment leaf is the last live one of its compare value. A node taken back
is at or above B and no value (`TakenAbove`, `TakenNotValOK`), so `DeadLive`
gives (C) (`deadTakenLive_of_deadLive`).

Per operation (`OpDeadLiveOK`), with the writer's tree, (A) and (B), and the
walk's ranges before it: why it holds, rule by rule. A klong to a node of the
transaction dies only where the writer kills it after retargeting it from a
node taken back (the upward delete's stop node), moves it (LE-b), or deletes a
merged node's klong that the merge then retargets to the first new node; a
klong added never shadows a live one to a node of the transaction (the walk's
ranges: a split's divider is no live compare value of the parent); new nodes and
nodes split in place hold last versions, live klongs only; `unlink` keeps the
klongs before the transaction only. Not proved yet; checked on two runs in
TakeBackRunExample.lean.
-/
import SIS.Tree.TakeBackRunT
import SIS.Tree.WriterKindsRun
import SIS.Tree.WriterFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (C) in the form every operation keeps, at node-map level: a klong of a node
to a node at or above B that is no value of the transaction comes with a live
klong of the same node to it; in a segment leaf it is itself the last live
klong of its compare value, so `takeBackRoot`'s one repoint leaves no klong to
the root taken back. With the writer's nodes, the values and the taken nodes
as they are read (`ReadsAs`), it is kept by every read. -/
def DeadLiveN (N : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId) : Prop :=
  ∀ q qn, N q = some qn → ∀ i cv y, qn.ks[i]? = some (Klong.key cv y) → B ≤ y → y ∉ vals →
    (∃ c, (c, y) ∈ qn.liveAt t) ∧ (qn.leaf = true → LastLive qn.ks qn.lastBitmap i cv)

/-- `DeadLiveN` of the writer's state w over the base P. -/
def DeadLive (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Prop :=
  DeadLiveN (wNode p (viewOf P) w) t B (w.vals.map (·.1))

/-- (C) from `DeadLive`: a node taken back is at or above B and no value. -/
theorem deadTakenLive_of_deadLive (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W)
    (hD : DeadLive p P t B w) (hU : (w.nodes.map (·.1)).Nodup)
    (hA : ∀ x ∈ w.taken, B ≤ x) (hTV : ∀ x ∈ w.taken, x ∉ w.vals.map (·.1)) :
    DeadTakenLive t w := by
  intro q hq hqk cv y hk hy
  have hy' : y ∈ w.taken := by simpa using hy
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hk
  have hlk : w.nodes.lookup q.1 = some q.2 := nex_run_lookup_of_mem w.nodes q.1 q.2 hU hq
  have hqk' : q.1 ∉ w.taken := by simpa using hqk
  have hN : wNode p (viewOf P) w q.1 = some q.2 := by simp [wNode, hqk', hlk]
  exact (hD q.1 q.2 hN i cv y hi (hA y hy') (hTV y hy')).1

/-- `DeadLive` at a transaction's first state: no overlay node. -/
theorem deadLive_init (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (top : Top) :
    DeadLive p (treeRun p ts) (ts.length + 1) tx.base (wInit tx top) := by
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  intro q qn hq i cv y hi hB _
  rw [hlook] at hq
  exfalso
  have hk : Klong.key cv y ∈ qn.ks := List.mem_of_getElem? hi
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
      have := hfresh _ (mem_of_get? hny)
      simp only at this
      omega

/-- At every transaction's end no node taken back is a value of the
transaction (taken nodes are key nodes of the books, values are not: the walk
of the kinds' `KdInv.vals`). Not proved here. -/
def TakenNotValOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → ∀ x ∈ w.taken, x ∉ w.vals.map (·.1)

/-- At a transaction's end no node taken back is a value: taken nodes are key
nodes of the books (`Book.taken`), values are not (the walk of the kinds'
`KdInv.vals`). -/
theorem execW_takenNotVal (K : KindOracle) (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hM : 2 ≤ p.M) (hwf : tx.wf = true)
    (hv : ViewIdsBelow tx.base v)
    (hk : ViewKinds K tx.base { p := p, i := i, view := rootless v })
    (he : execW p tx i v = .ok (bs, w)) : ∀ x ∈ w.taken, x ∉ w.vals.map (·.1) := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      have hkeys : ∀ op ∈ tx.ops, keyWf op.key = true := by
        intro op hop
        unfold Tx.wf at hwf
        exact List.all_eq_true.mp hwf op hop
      obtain ⟨hbook, hkd, _⟩ := kd_ops K tx.base (appendFrameOK tx.base) tx.ops
        { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } (viewIdsBelow_rootless tx.base v hv) hk
        (book_start _ _ top) (kdInv_start K tx.base top) hM hkeys bs w hr
      intro x hx hxv
      obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxv
      have h1 := (hkd.vals q hq).2.2
      rw [hqx] at h1
      exact h1 (hbook.taken x hx)

end SIS.Tree
