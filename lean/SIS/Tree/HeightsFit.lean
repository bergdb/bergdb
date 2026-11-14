/-
The fuel premise between operations from the heights (bergdb 024-22, step 4
(C); 024-12's TP10 premise `TxSegFitsOK`): `txSegFitsOK_of_takeBelowR`. Its one
new named premise is `TakeBelowFuelOK`: every node an operation takes back has
a height below the fuel. The argument, the doomed transaction:

* at a state between operations the heights' walk holds (`ht_reached`, given
  `OpDelChkOK`), so SegFits (fuel - 1) follows when every node not taken back
  has a height below fuel (`segFits_of_heights`);
* a node of height fuel or more is above H, so it is in `outside`
  (`HeightMarkedPred`), and stays there to the transaction's end;
* `boundsOK` at the end asks it taken back, by some later operation, which
  `TakeBelowFuelOK` excludes.

`TakeBelowFuelOK`'s reason is (C)'s part 1 (`ht_descendLte_height`): every node
an operation finds and takes back is in a segment tree the operation descended
through, and such a descent passes heights below the fuel only.
-/
import SIS.Tree.HeightsChkRun
import SIS.Tree.HeightsFuelDescent
import SIS.Tree.MergeHeightOrigins
import SIS.Tree.GetAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Fields that only grow -/

/-- An entry of `outside` stays. -/
@[instance_reducible]
def outsideHasFields (q : NodeId × Nat × Nat) : WriterFieldsInvariant where
  pred := fun _ _ out => q ∈ out
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]; exact hw
      · exact writerWP_throw _ _ _ _
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    · exact List.mem_cons_of_mem _ hw
    · exact hw

/-- An entry of `gh` stays. -/
@[instance_reducible]
def ghHasFields (q : NodeId × Nat × Nat) : WriterFieldsInvariant where
  pred := fun _ gh _ => q ∈ gh
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact List.mem_cons_of_mem _ hw
      · exact writerWP_throw _ _ _ _
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    all_goals exact List.mem_cons_of_mem _ hw

/-! ## The operations after a state -/

/-- The run of a transaction's operations split at a state its prefix reaches. -/
theorem mapM_split_run (c : Ctx) (w0 : W) (pre post : List Op) (r : List Bool) (w : W)
    (bs : List Bool) (wEnd : W)
    (hpre : (pre.mapM putKv) c w0 = .ok (r, w))
    (hall : ((pre ++ post).mapM putKv) c w0 = .ok (bs, wEnd)) :
    ∃ r2, (post.mapM putKv) c w = .ok (r2, wEnd) := by
  rw [List.mapM_append] at hall
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind] at hall
  rw [hpre] at hall
  simp only at hall
  cases h2 : (post.mapM putKv) c w with
  | error e => rw [h2] at hall; cases hall
  | ok rw2 =>
    rcases rw2 with ⟨r2, w2⟩
    rw [h2] at hall
    simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hall
    exact ⟨r2, by rw [hall.2]⟩

/-- A node not taken back at a state and taken back at the end: some operation
after the state takes it back. -/
theorem taken_by_op (c : Ctx) (w0 : W) (ops : List Op) (x : NodeId) :
    ∀ (post pre : List Op), ops = pre ++ post → ∀ r w r2 wEnd,
      (pre.mapM putKv) c w0 = .ok (r, w) → (post.mapM putKv) c w = .ok (r2, wEnd) →
      w.taken.contains x = false → wEnd.taken.contains x = true →
      ∃ pre' op post' r' u a v, ops = pre' ++ op :: post' ∧
        (pre'.mapM putKv) c w0 = .ok (r', u) ∧ putKv op c u = .ok (a, v) ∧
        u.taken.contains x = false ∧ v.taken.contains x = true ∧
        ∃ (rest : List Op) (r3 : List Bool), (rest.mapM putKv) c w = .ok (r3, u) := by
  intro post
  induction post with
  | nil =>
    intro pre _ r w r2 wEnd _ hpost hx hend
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hpost
    rw [← hpost.2, hx] at hend
    cases hend
  | cons op post ih =>
    intro pre hsplit r w r2 wEnd hpre hpost hx hend
    rw [List.mapM_cons] at hpost
    simp only [bind, ReaderT.bind, StateT.bind, Except.bind] at hpost
    cases h1 : putKv op c w with
    | error e => rw [h1] at hpost; cases hpost
    | ok aw =>
      rcases aw with ⟨a, w1⟩
      rw [h1] at hpost
      simp only at hpost
      cases h2 : (post.mapM putKv) c w1 with
      | error e => rw [h2] at hpost; cases hpost
      | ok rw2 =>
        rcases rw2 with ⟨r3, w3⟩
        rw [h2] at hpost
        simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at hpost
        cases hx1 : w1.taken.contains x with
        | true =>
          exact ⟨pre, op, post, r, w, a, w1, hsplit, hpre, h1, hx, hx1, [], [], rfl⟩
        | false =>
          have hpre' : ((pre ++ [op]).mapM putKv) c w0 = .ok (r ++ [a], w1) := by
            rw [List.mapM_append]
            simp only [bind, ReaderT.bind, StateT.bind, Except.bind]
            rw [hpre]
            simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind,
              Except.bind]
            rw [h1]
            rfl
          obtain ⟨pre', op', post', r', u, a', v, hs', hp', ho', hu, hv, rest, r4, hrest⟩ :=
            ih (pre ++ [op]) (by rw [hsplit]; simp) (r ++ [a]) w1 r3 wEnd hpre'
              (by rw [h2, hpost.2]) hx1 hend
          refine ⟨pre', op', post', r', u, a', v, hs', hp', ho', hu, hv, op :: rest, a :: r4, ?_⟩
          rw [List.mapM_cons]
          simp only [bind, ReaderT.bind, StateT.bind, Except.bind]
          rw [h1]
          simp only
          rw [hrest]
          rfl

/-! ## The fuel between operations -/

/-- `segFits_of_heights` asking the bound of the nodes not taken back only. -/
theorem segFits_of_heightsU {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W}
    (hb : Book B c w) (hc : HtCache c H w) (hvh : ViewHeights H B c) (base : View BVal)
    (hbase : BaseHeights c H base) (bound : Nat) (r : NodeId)
    (hr : ∀ x n, wNode c.p base w x = some n → ∀ h, HasHt H w x h → h ≤ bound) :
    SegFits (wNode c.p base w) c.i bound r := by
  intro x _
  cases hn : wNode c.p base w x with
  | none =>
    cases bound with
    | zero => intro n h; rw [hn] at h; cases h
    | succ b => intro n h; rw [hn] at h; cases h
  | some n =>
    obtain ⟨h, hh, _⟩ := hasHt_of_wNode hb base hbase hn
    have he := segDepthEq_of_hasHt hb hc hvh base hbase h x hh
    exact SegDepthLe.mono _ _ h x (he.le h x) bound (hr x n hn h hh)

theorem fuel_gt_H (p : Params) : p.H + 2 < p.fuel := by
  unfold Params.fuel
  have : p.H + 2 ≤ (p.G + 1) * (p.H + 2) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

/-- `TakeBelowFuelOK` for the deletes: a put takes nothing back. -/
def TakeBelowFuelDelOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    ∀ a v, putKv (.del key) (ctxOf p ts) w = .ok (a, v) →
    ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → v.taken.contains x = true →
      h < p.fuel

end SIS.Tree
