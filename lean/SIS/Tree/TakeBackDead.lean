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
    DeadLive p (treeRun p ts) (ts.length + 1) tx.base w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => DeadLive p (treeRun p ts) (ts.length + 1) tx.base w')

/-- `DeadLive` at every state that a prefix of a transaction's operations
reaches, from `OpDeadLiveOK`, given the walk's ranges at every such state. -/
theorem deadLive_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hOT : OpTakeTOK p R) (hO : OpDeadLiveOK p R)
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
      DeadLive p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      DeadLive p (treeRun p ts) (ts.length + 1) tx.base w
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
    exact deadLive_init p ts tx hw (hRL _ _ hr) top
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

/-- At every transaction's end no node taken back is a value of the
transaction (taken nodes are key nodes of the books, values are not: the walk
of the kinds' `KdInv.vals`). Not proved here. -/
def TakenNotValOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → ∀ x ∈ w.taken, x ∉ w.vals.map (·.1)

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
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hTV : TakenNotValOK p R) :
    DeadTakenLiveOK p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hD := deadLive_reached p R hRL hOT hO ho ts tx hw hr (hRT _ _ hr) z top hz htop
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
  have hU : (w.nodes.map (·.1)).Nodup := execW_cacheUnique p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hrun
  exact deadTakenLive_of_deadLive p (treeRun p ts) (ts.length + 1) tx.base w hD hU hl.2.1
    (hTV ts tx hw hr noops w hrun)

end SIS.Tree
