/-
The take-back's (C) (bergdb 024-12, TP4; `DeadTakenLive`, TakeBackRun.lean) in
the form every operation keeps: `DeadLive`, a klong of a kept overlay node to
a key node of the transaction (at or above B, in the books' list) comes with a
live klong of the same node to it. A node taken back is such a key node
(`Book.taken`, `TakenAbove`), so `DeadLive` gives (C) (`deadTakenLive_of_deadLive`).

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

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (C) in the form every operation keeps. -/
def DeadLive (B : NodeId) (t : Time) (w : W) : Prop :=
  ∀ q ∈ w.nodes, w.taken.contains q.1 = false → ∀ cv y, Klong.key cv y ∈ q.2.ks →
    y ∈ w.gh.map (·.1) → B ≤ y → ∃ c, (c, y) ∈ q.2.liveAt t

/-- (C) from `DeadLive`: a node taken back is a key node of the books, at or
above B. -/
theorem deadTakenLive_of_deadLive (B : NodeId) (t : Time) (w : W) (hD : DeadLive B t w)
    (htk : ∀ x ∈ w.taken, x ∈ w.gh.map (·.1)) (hA : ∀ x ∈ w.taken, B ≤ x) :
    DeadTakenLive t w := by
  intro q hq hqk cv y hk hy
  have hy' : y ∈ w.taken := by simpa using hy
  exact hD q hq hqk cv y hk (htk y hy') (hA y hy')

/-- `DeadLive` at a transaction's first state: no overlay node. -/
theorem deadLive_init (B : NodeId) (t : Time) (tx : Tx) (top : Top) :
    DeadLive B t (wInit tx top) := by
  intro q hq
  simp [wInit] at hq

/-- Every operation of a transaction within reach, from a state that its
earlier operations reach, with the writer's tree, (A) and (B), the walk's
ranges and `DeadLive`, keeps `DeadLive`. Not proved. -/
def OpDeadLiveOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    TakeInvT p (treeRun p ts) (ts.length + 1) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    DeadLive tx.base (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => DeadLive tx.base (ts.length + 1) w')

/-- `DeadLive` at every state that a prefix of a transaction's operations
reaches, from `OpDeadLiveOK`, given the walk's ranges at every such state. -/
theorem deadLive_reached (p : Params) (R : Struct BVal → Time → Prop) (hOT : OpTakeTOK p R) (hO : OpDeadLiveOK p R)
    (ho : OpTreeOK p) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hRange : ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      DeadLive tx.base (ts.length + 1) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      DeadLive tx.base (ts.length + 1) w
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact deadLive_init tx.base (ts.length + 1) tx top
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      have h0 := h
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT1 := writerTreeOK_reached p ho ts tx hw z top hz htop hT pre' (op :: post)
            hsplit' r1 w1 h1
          have hT2 := writerTreeOK_reached p ho ts tx hw z top hz htop hT (pre' ++ [op]) post
            (by rw [hsplit]) r w h0
          rw [← h.2] at hT2 ⊢
          have hTI := takeInvT_reached p R hOT ho ts tx hw hr hT z top hz htop pre' (op :: post) hsplit'
            r1 w1 h1
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hTI
            (hRange pre' (op :: post) hsplit' r1 w1 h1) hI1 a w2 h2

/-- (C) at every transaction's end from `OpDeadLiveOK`, given the walk's ranges
at every state between operations. -/
theorem deadTakenLiveOK_of_ops (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOK p) (hOT : OpTakeTOK p R) (hO : OpDeadLiveOK p R)
    (hRange : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    DeadTakenLiveOK p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hD := deadLive_reached p R hOT hO ho ts tx hw hr (hRT _ _ hr) z top hz htop
    (hRange ts tx hw hr z top hz htop) tx.ops [] (by simp) noops w hops
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (noops, w) := hrun
  have hbook := execW_book p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  exact deadTakenLive_of_deadLive tx.base (ts.length + 1) w hD hbook.taken hl.2.1

end SIS.Tree
