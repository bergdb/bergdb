/-
The tree model (bergdb 024-12, TP4 and TP7): the take-back discipline
(`TakeBackOKUnder`, PointersRun.lean) and P's tree (`TreeAt`, WriterTree.lean)
at every run within reach, as one induction over the runs. The circle
TP4 → the lift of the writer's overlay → P's tree → TP4 closes as an
induction (`runTree_joint`): each transaction's take-back needs P's tree before
it, and P's tree after it needs the lift, which needs TP4 before it.

The take-back at a transaction's end (`takeBackEnd_of_inv`) follows from three
facts of its last state, besides the books (the nodes taken back are made by
the transaction; one overlay entry per node):

* (A) a node reached from the space root is not taken back (`ReachedFree`);
* (B) a kept node with a live klong to a node of the transaction is reached
  (`LiveReached`);
* (C) a klong of a kept node to a node taken back comes with a live klong of
  the same node to it (`DeadTakenLive`).

(A) and (B) are tree-level and kept by every operation (`OpTakeOK`, with the
writer's tree before and after: prover cost's `OpTreeOK`); (C) holds at a
transaction's end (`DeadTakenLiveOK`). The induction carries a further
statement Q about the runs, with its own first state and step, for what the
proofs of these premises need of P (for example TP7's invariant).

Premises here: `OpTreeOK`, `OpTakeOK`, `DeadTakenLiveOK`, Q's first state and
step. None is void: TakeBackRunExample.lean computes (A) and (B) and the
writer's tree at every state between operations, and (C) and the take-back at
the last, on two runs whose transactions take nodes back by the upward delete,
by a merge and by root collapse, at the space root and at a segment's.
-/
import SIS.Tree.PointersRun
import SIS.Tree.WriterTree
import SIS.Tree.WriterCacheUnique

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The lift of one transaction -/

/-- The lift of the writer's last state for one transaction: P after it reads
as the writer's nodes (`CommitLiftOK` at one step). -/
def CommitLiftAt (p : Params) (ts : List Tx) (tx : Tx) : Prop :=
  ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x, knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = wNode p (viewOf (treeRun p ts)) w x) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

/-- `commitLiftOK_of_overlay` at one transaction, from TP4, the klongs that give
the histories and a history for every key node before it. -/
theorem commitLiftAt_of_links (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) : CommitLiftAt p ts tx := by
  intro noops w hrun
  obtain ⟨hov, htaken, htopt⟩ := overlayLiftOKUnder_links p ts tx hw hR noops w hrun
  refine ⟨?_, htaken, htopt⟩
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  have hmn := madeNodes_of_runOps p ts tx noops w hrun
  obtain ⟨z, top0, _, _, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, _, hnt, hvm, _, _⟩ := hinv
  have hroot := treeRun_root p ts
  intro x
  have hov' := hov x
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hov' ⊢
  generalize hP : treeRun p ts = P at hov' hbase hroot ⊢
  generalize hi : ts.length + 1 = i at hov' ⊢
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  by_cases hty : w.taken.contains x = true
  · have hge := htaken x (by simpa using hty)
    have hPx := get?_none_of_ge P tx.base x hbase hge
    have hNx := newNodeOf_changesOf_none i w x (fun m _ hid => by rw [← hid] at hty ⊢; exact hty)
    have hty2 : x ∈ w.taken := by simpa using hty
    simp [knodeOf, viewOf, get?_apply, hPx, hNx, wNode, hty2]
  · have hty' : w.taken.contains x = false := by simpa using hty
    have hty3 : x ∉ w.taken := by simpa using hty
    cases hl : w.nodes.lookup x with
    | some n =>
      rw [hov' n hl hty']
      simp [wNode, hty3, hl]
    | none =>
      have hwn : wNode p (viewOf P) w x = knodeOf p (viewOf P) x := by
        simp [wNode, hty3, hl]
      rw [hwn]
      have hnokey : ∀ q ∈ w.nodes, q.1 ≠ x := by
        intro q hq hqx
        have := List.lookup_eq_none_iff.mp hl q hq
        simp [hqx] at this
      cases hPx : P.get? x with
      | some nd =>
        have hlt : x < tx.base := hbase _ (get?_mem P x nd hPx)
        by_cases hxr : x = root
        · subst hxr
          rw [hndr] at hPx
          cases hPx
          have := rootLevel_gt p
          simp [knodeOf, viewOf, get?_apply_of_get? hndr, hndr, hlr, hdr, this]
        · have hA : addsFor (changesOf i w) i x = [] :=
            List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
              obtain ⟨_, hm⟩ := mem_addsFor.mp he
              rcases mem_changesOf_adds i w x e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
                  ⟨hnt', hr⟩
              · exact hnokey q hq hqy
              · have := madeGe _ (hvm _ hh')
                simp only at this
                omega
              · rcases hr with ⟨hxr', _⟩ | ⟨hxt, _⟩
                · exact hxr hxr'
                · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
                  have := madeGe m hm
                  rw [hmid, ← hxt] at this
                  omega)
          simp [knodeOf, viewOf, get?_apply_of_get? hPx, hPx, hA]
      | none =>
        have hk0 : knodeOf p (viewOf P) x = none := by simp [knodeOf, viewOf, hPx]
        rw [hk0]
        cases hNx : newNodeOf (changesOf i w) x with
        | none => simp [knodeOf, viewOf, get?_apply, hPx, hNx]
        | some nd =>
          obtain ⟨m, hm, hid, _, hnd⟩ := newNodeOf_changesOf_some i w x nd hNx
          subst hnd
          cases hmd : m.isData with
          | true => simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd]
          | false =>
            rcases hmn m hm hmd with hs | hlv
            · rw [hid, hl] at hs
              cases hs
            · have hlv' : p.keyMax < m.level := hlv
              simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd, hlv']

/-- P's tree after one transaction, from P's tree before it, `OpTreeOK` and the
lift of that transaction (`treeAt_commit_of_lift` at one step). -/
theorem treeAt_step (p : Params) (ho : OpTreeOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hT : TreeAt p (treeRun p ts) ts.length)
    (hl : CommitLiftAt p ts tx) : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hW := writerTreeOK_reached p ho ts tx hw z top hz htop hT tx.ops [] (by simp) noops w hops
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  exact ⟨w.top.rootKey, hR, treeOK_congr_look _ _ _ _ (funext hK).symm hW⟩

/-! ## The take-back from three facts of the last state -/

/-- (A) No node reached from the space root is taken back. -/
def ReachedFree (p : Params) (P : Struct BVal) (t : Time) (w : W) : Prop :=
  ∀ y, TReach (wNode p (viewOf P) w) t w.top.rootKey y → w.taken.contains y = false

/-- (B) A kept node with a live klong to a node at or above B (the
transaction's first id) is reached from the space root. -/
def LiveReached (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Prop :=
  ∀ q qn c y, wNode p (viewOf P) w q = some qn → (c, y) ∈ qn.liveAt t → B ≤ y →
    TReach (wNode p (viewOf P) w) t w.top.rootKey q

/-- (A) and (B): what every operation keeps. -/
def TakeInv (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Prop :=
  ReachedFree p P t w ∧ LiveReached p P t B w

/-- (C) A klong of a kept overlay node that names a node taken back comes with
a live klong of the same node to it. -/
def DeadTakenLive (t : Time) (w : W) : Prop :=
  ∀ q ∈ w.nodes, w.taken.contains q.1 = false → ∀ cv y, Klong.key cv y ∈ q.2.ks →
    w.taken.contains y = true → ∃ c, (c, y) ∈ q.2.liveAt t

/-- The take-back at a state from (A), (B), (C), the nodes taken back at or
above B, and one overlay entry per node. -/
theorem takeBackEnd_of_inv (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W)
    (hI : TakeInv p P t B w) (hD : DeadTakenLive t w) (hA : ∀ x ∈ w.taken, B ≤ x)
    (hU : (w.nodes.map (·.1)).Nodup) : TakeBackEnd w := by
  obtain ⟨hF, hL⟩ := hI
  refine ⟨?_, hF _ TReach.root⟩
  intro q hq hqk cv y hk
  cases hy : w.taken.contains y with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨c, hc⟩ := hD q hq hqk cv y hk hy
    have hlk : w.nodes.lookup q.1 = some q.2 := nex_run_lookup_of_mem w.nodes q.1 q.2 hU hq
    have hqk' : q.1 ∉ w.taken := by simpa using hqk
    have hN : wNode p (viewOf P) w q.1 = some q.2 := by simp [wNode, hqk', hlk]
    have hB : B ≤ y := hA y (by simpa using hy)
    have hr := hL q.1 q.2 c y hN hc hB
    have hry : TReach (wNode p (viewOf P) w) t w.top.rootKey y := TReach.link hr ⟨q.2, hN, hc⟩
    have := hF y hry
    rw [hy] at this
    cases this

/-! ## The premises about the writer -/

/-- Every operation of a transaction within reach, from a state that its
earlier operations reach, with the writer's tree and (A) and (B), keeps (A) and
(B) (the writer's tree after it given). R: what is known of P before the
transaction. -/
def OpTakeOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    TakeInv p (treeRun p ts) (ts.length + 1) tx.base w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      TakeInv p (treeRun p ts) (ts.length + 1) tx.base w')

/-- (C) at the last state of every transaction within reach. -/
def DeadTakenLiveOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → DeadTakenLive (ts.length + 1) w

/-! ## (A) and (B) at every state of a transaction -/

/-- (A) and (B) at a transaction's first state: nothing is taken back, and a
node of P names only nodes of P, which are below the transaction's first id. -/
theorem takeInv_init (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (top : Top) :
    TakeInv p (treeRun p ts) (ts.length + 1) tx.base (wInit tx top) := by
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  refine ⟨fun y _ => by simp [wInit], ?_⟩
  intro q qn c y hq hl hB
  rw [hlook] at hq
  exfalso
  have hk := KNode.liveAt_key_mem qn _ c y hl
  unfold knodeOf viewOf at hq
  cases hg : (treeRun p ts).get? q with
  | none => simp [hg] at hq
  | some nd =>
    simp only [hg] at hq
    split at hq
    · cases hq
    · simp only [Option.some.injEq] at hq
      subst hq
      obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist c y hk
      have hy := hR.1 _ (mem_of_get? hg) e he y (by rw [hv]; simp [bptrs])
      obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hy
      have := hfresh _ (mem_of_get? hny)
      simp only at this
      omega

/-- (A) and (B) at every state that a prefix of a transaction's operations
reaches, from the first state, `OpTakeOK` and the writer's tree at every such
state (cost's `OpTreeOK`, `writerTreeOK_reached`). -/
theorem takeInv_reached (p : Params) (R : Struct BVal → Time → Prop) (hO : OpTakeOK p R)
    (ho : OpTreeOK p) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length) (hRL : RunLinksOK p (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInv p (treeRun p ts) (ts.length + 1) tx.base w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      TakeInv p (treeRun p ts) (ts.length + 1) tx.base w
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
    exact takeInv_init p ts tx hw hRL top
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
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hT1 hI1 a w2 h2 hT2

/-- The take-back discipline under R, from the writer's tree (`OpTreeOK`), (A)
and (B) kept by every operation and (C) at the end, if R has TP4 and P's tree. -/
theorem takeBackOKUnder_of_ops (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (ho : OpTreeOK p) (hO : OpTakeOK p R) (hD : DeadTakenLiveOK p R) : TakeBackOKUnder p R := by
  intro ts tx hw hr noops w hrun
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hI := takeInv_reached p R hO ho ts tx hw hr (hRL _ _ hr) (hRT _ _ hr) z top hz htop tx.ops []
    (by simp) noops w hops
  have hl := commitLiftAt_of_links p ts tx hw (hRL _ _ hr) noops w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have hU : (w.nodes.map (·.1)).Nodup := execW_cacheUnique p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh) hrun
  exact takeBackEnd_of_inv p (treeRun p ts) (ts.length + 1) tx.base w hI
    (hD ts tx hw hr noops w hrun) hl.2.1 hU

/-! ## The induction over the runs -/

/-- What travels together from one run to the next: TP4 with the klongs that
give the histories and a history for every key node, P's tree, and Q. -/
def RunTreeQ (p : Params) (Q : Struct BVal → Time → Prop) (P : Struct BVal) (t : Time) : Prop :=
  RunLinksOK p P t ∧ TreeAt p P t ∧ Q P t

/-- The induction: TP4 (with the histories), P's tree and Q at every run
within reach, from Q's first state and step, cost's `OpTreeOK`, and the two
statements about the writer (`OpTakeOK`, `DeadTakenLiveOK`) under what the
induction carries. -/
theorem runTree_joint (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOK p) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hTB : TakeBackOKUnder p (RunTreeQ p Q) :=
    takeBackOKUnder_of_ops p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD
  intro ts hw
  have hk : ∀ n, n ≤ ts.length → RunTreeQ p Q (treeRun p (ts.take n)) n := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact ⟨runLinksOK_init p, treeAt_init p, hQ0⟩
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hlen : (ts.take n).length = n := by
        simp only [List.length_take]; omega
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hr : RunTreeQ p Q (treeRun p (ts.take n)) (ts.take n).length := by
        rw [hlen]; exact ih (by omega)
      have hL := runLinksOK_step p hM (ts.take n) ts[n] hwn hr.1
        (fun noops w hrun => hTB (ts.take n) ts[n] hwn hr noops w hrun)
      have hT := treeAt_step p ho (ts.take n) ts[n] hwn hr.2.1
        (commitLiftAt_of_links p (ts.take n) ts[n] hwn hr.1)
      have hQ := hQs (ts.take n) ts[n] hwn hr hL hT
      rw [htake]
      rw [hlen] at hL hT hQ
      exact ⟨hL, hT, hQ⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- TP7's take-back statement, from the induction's premises. -/
theorem takeBackOK_of_joint (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOK p) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    TakeBackOKUnder p (RunLinksOK p) := by
  intro ts tx hw _
  have hj := runTree_joint p hM Q hQ0 hQs ho hO hD ts (within_snoc_prefix p ts tx hw)
  exact takeBackOKUnder_of_ops p _ (fun _ _ h => h.1) (fun _ _ h => h.2.1) ho hO hD ts tx hw hj

/-- P's tree at every run within reach, with no premise on the lift
(`treeAt_run` takes `CommitLiftOK`). -/
theorem treeAt_of_joint (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (ho : OpTreeOK p) (hO : OpTakeOK p (RunTreeQ p Q)) (hD : DeadTakenLiveOK p (RunTreeQ p Q)) :
    ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length :=
  fun ts hw => (runTree_joint p hM Q hQ0 hQs ho hO hD ts hw).2.1

end SIS.Tree
