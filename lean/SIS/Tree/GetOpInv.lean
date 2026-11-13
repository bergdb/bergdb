import SIS.Tree.GetCommit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `OpGetOK` (bergdb 024-12, TP10) from an invariant of the writer's state
inside a transaction: one that the writer's first state meets, and that each
operation keeps while it changes what the state reads by itself alone. The
invariant is the prover's choice; TP7's invariant does not serve
(`sharedSegment_changes_other_key`): it must exclude, at least, two klongs
live at the transaction's time that name one key node. -/

/-- An invariant of the writer's state inside a transaction (a predicate of
the run before it, the transaction and the state) under which each operation
of the transaction changes what the state reads by itself alone. -/
def OpInvariant (p : Params) (I : List Tx → Tx → W → Prop) : Prop :=
  (∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top → I ts tx (wInit tx top)) ∧
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ op ∈ tx.ops, ∀ w, I ts tx w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => I ts tx w' ∧ ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

theorem opInvariant_prefix (p : Params) (I : List Tx → Tx → W → Prop) (hI : OpInvariant p I)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre, (∃ post, tx.ops = pre ++ post) → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → I ts tx w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → (∃ post, tx.ops = pre ++ post) → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → I ts tx w from
    hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact hI.1 ts tx hw z top hz htop
  | succ k ih =>
    intro pre hl hpost r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      obtain ⟨post, hsplit⟩ := hpost
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
          have hI1 := ih pre' hl' ⟨op :: post, by rw [hsplit]; simp⟩ r1 w1 h1
          have hop : op ∈ tx.ops := by rw [hsplit]; simp
          have := (hI.2 ts tx hw op hop w1 hI1 a w2 h2).1
          rw [← h.2]
          exact this

/-- `OpGetOK` from an invariant of the writer's state inside a transaction. -/
theorem opGetOK_of_invariant (p : Params) (I : List Tx → Tx → W → Prop)
    (hI : OpInvariant p I) : OpGetOK p := by
  intro ts tx hw z top hz htop pre op post hsplit r w hpre
  have hIw := opInvariant_prefix p I hI ts tx hw z top hz htop pre ⟨op :: post, hsplit⟩ r w hpre
  have hop : op ∈ tx.ops := by rw [hsplit]; simp
  exact writerWP_mono (hI.2 ts tx hw op hop w hIw) (fun _ _ h => h.2)

end SIS.Tree
