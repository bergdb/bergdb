/-
`DeadAllOK` (the top theorem's premise `hD`, bergdb 024-12; option 2's bound,
024-23) reduced to the operations: every key node the writer's state reads
holds at most theta dead klongs (`WDeadOK`). It holds at a transaction's first
state when P meets `DeadAllOK` (`wDeadOK_init`); an operation that keeps it
(`QDead`) keeps it along the transaction (`dead_reached`); at the last state
it is `DeadAllOK` of the structure after the transaction, by the commit's lift
(`deadAllOK_commit`). So `DeadAllOK` holds at every run from `QDead` of each
operation (`deadAllOK_snoc`, one transaction's step). Case (1), a put into
its leaf with room, keeps it: the writer puts the klong only when `deadOver`
lets it through (`deadCase_putLeafRoom`).
-/
import SIS.Tree.LatestJoint
import SIS.Tree.DeadProps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every key node the writer's state reads holds at most theta dead klongs
(with theta on). -/
def WDeadOK (p : Params) (P : Struct BVal) (w : W) : Prop :=
  p.theta ≠ 0 → ∀ x n, wNode p (viewOf P) w x = some n → n.deadCount ≤ p.theta

/-- `WDeadOK` kept by an operation. -/
def QDead (p : Params) : List Tx → Op → W → W → Prop :=
  fun ts _ w w' => WDeadOK p (treeRun p ts) w → WDeadOK p (treeRun p ts) w'

/-- At a transaction's first state the writer reads P's key nodes. -/
theorem wDeadOK_init (p : Params) (ts : List Tx) (tx : Tx) (top : Top)
    (hD : DeadAllOK p (treeRun p ts)) : WDeadOK p (treeRun p ts) (wInit tx top) := by
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  intro h0 x n hn
  rw [hlook] at hn
  exact hD x n (by rw [keyNodeAt_eq_knodeOf]; exact hn) h0

/-- `WDeadOK` at every state that a prefix of a transaction's operations
reaches, from P's `DeadAllOK` and `QDead` at every operation, with `PutInv` and
the walk's ranges there from `joint_reached`. -/
theorem dead_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hDd : OpCaseOK p R (QDead p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (hD : DeadAllOK p (treeRun p ts))
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WDeadOK p (treeRun p ts) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WDeadOK p (treeRun p ts) w
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
    exact wDeadOK_init p ts tx top hD
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
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
          obtain ⟨hI1, hR1⟩ := joint_reached p R hRL hT hP hO ts tx hw hr hTA hI z top hz htop
            pre' (op :: post) hsplit' r1 w1 h1
          have hD1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hD2 := hDd ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a
            w2 h2 hD1
          rw [← h.2]
          exact hD2

/-- `WDeadOK` at the transaction's last state is `DeadAllOK` of the structure
after it, by the commit's lift. -/
theorem deadAllOK_commit (p : Params) (ts : List Tx) (tx : Tx)
    (hl : CommitLiftAt p ts tx) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w))
    (hW : WDeadOK p (treeRun p ts) w) : DeadAllOK p (treeRun p (ts ++ [tx])) := by
  obtain ⟨hK, _, _⟩ := hl noops w hrun
  intro x n hx h0
  rw [keyNodeAt_eq_knodeOf, hK] at hx
  exact hW h0 x n hx

/-- One transaction's step of `DeadAllOK`: from `RunOK` and `DeadAllOK` before
it, TP10's three posts and `QDead` for every operation. -/
theorem deadAllOK_snoc (p : Params)
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hDd : OpCaseOK p (RunOK p) (QDead p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : RunOK p (treeRun p ts) ts.length)
    (hD : DeadAllOK p (treeRun p ts)) : DeadAllOK p (treeRun p (ts ++ [tx])) := by
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hcl : CommitLiftAt p ts tx := commitLiftAt_of_links p ts tx hw hr.1
  exact deadAllOK_commit p ts tx hcl noops w hrun
    (dead_reached p (RunOK p) hRL hT hPI hO hDd ts tx hw hr hr.2.1 hr.2.2 hD z top hz htop tx.ops []
      (by simp) noops w hops)

/-! ## The operation cases -/

/-- (1), `QDead`: the leaf's klong is put only when `deadOver` lets it through. -/
theorem deadCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpCaseOK p R (QDead p) PutLeafRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have ht : ∀ q ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      (ctxOf p ts).p.fuel (pre ++ [cv]) w.top.rootKey, w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  have hall := keyLeaf_all hK hrk (fun m => m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false) hroom
  refine writerWP_mono (writerWP_put_room_after (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk
    w hrk ht hall) ?_
  intro _ w' ⟨L', n', hvis, hn', hnl', _, _, hN'L, hN'⟩ hW h0 x m hx
  by_cases hxL : x = L'
  · subst hxL
    have hN'L2 : wNode p (viewOf (treeRun p ts)) w' x =
        some (n'.add (ts.length + 1) (.key cv w.next)) := hN'L
    rw [hN'L2] at hx
    cases hx
    exact deadOver_false p _ (hall x n' hvis hn' hnl').2 h0
  · have hN'2 : wNode p (viewOf (treeRun p ts)) w' x = wNode p (viewOf (treeRun p ts)) w x :=
      hN' x hxL
    rw [hN'2] at hx
    exact hW h0 x m hx

/-! ## In the run induction -/

theorem deadAllOK_init (p : Params) : DeadAllOK p (initStruct p) := by
  intro x n hx _
  unfold keyNodeAt at hx
  cases hg : (initStruct p).get? x with
  | none => rw [hg] at hx; cases hx
  | some nd =>
    rw [hg] at hx
    rcases mem_init p (x, nd) (mem_of_get? hg) with h | h | h <;> cases h
    · have := rootLevel_gt p
      simp [Nat.not_le.mpr this] at hx
    · have hk := initial_key_level_le p
      simp only [Bool.not_false, Bool.true_and, hk, decide_true, ↓reduceIte,
        Option.some.injEq] at hx
      have h0 : ∀ b, (⟨b, klongsOf [(⟨0, marker⟩ : Entry BVal)]⟩ : KNode).deadCount = 0 := by
        intro b; cases b <;> decide
      rw [← hx, h0]
      exact Nat.zero_le _
    · simp [Params.topLevel] at hx
      exact absurd (of_decide_eq_true hx.1) (by omega)

/-- `LatestQ` with `DeadAllOK`: the run induction's Q when the bound on dead
klongs comes from the operations. -/
def LatestQD (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  LatestQ p P t ∧ DeadAllOK p P

theorem latestQD_init (p : Params) (hM : 2 ≤ p.M) : LatestQD p (initStruct p) 0 :=
  ⟨latestQ_init p hM, deadAllOK_init p⟩

/-- The step of `LatestQD`, with `QDead` for every operation in place of
`DeadAllOK` at every run. -/
theorem latestQD_snoc (p : Params) (hp : MergeParamsOK p) (hdel : OpHtDelOK p)
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hLv : OpCaseOK p (RunOK p) (QLive p) AnyOp)
    (hDd : OpCaseOK p (RunOK p) (QDead p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQD p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  intro ts tx hw hr hL' hT'
  have hM := mergeParamsOK_M p hp
  obtain ⟨hL, hTA, ⟨hI, _, hK, hA, hS, hLA⟩, hD⟩ := hr
  have hD' := deadAllOK_snoc p hT hPI hO hDd ts tx hw ⟨hL, hTA, hI⟩ hD
  have hK' := kindsAllOK_snoc p (by omega) ts tx hw hL hK
  have hA' := heightAllOK_snoc p (by omega) hdel ts tx hw hL hK hA
  have hS' := sizeOK_snoc p hp ts tx hw hL hS
  have hLA' := leftAllOK_snoc p hp ts tx hw hL hLA
  exact ⟨⟨invOK_snoc p hT hPI hO hLv ts tx hw ⟨hL, hTA, hI⟩ hL' hT' hK' hA' hS' hLA' hD',
    hL'.1, hK', hA', hS', hLA'⟩, hD'⟩

theorem runOK_of_runTreeQD (p : Params) (P : Struct BVal) (t : Time)
    (h : RunTreeQ p (LatestQD p) P t) : RunOK p P t :=
  ⟨h.1, h.2.1, h.2.2.1.1⟩

end SIS.Tree
