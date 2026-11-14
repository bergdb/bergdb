import SIS.Tree.PutInvRange

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `OpPutInvOK` from the parts about the tree alone, and `PutInv` at every
state of a transaction (bergdb 024-12, TP10). The global parts of `PutInv`
hold after every operation (`putInvG_of_book`), so `OpPutInvOK` reduces to
`OpPutInvTOK`: each operation keeps no reachable node taken back and the order
at the leaves (`opPutInvOK_of_T`). With cost's `OpTreeOK`, `PutInv` holds at
every state that a prefix of a transaction's operations reaches
(`putInv_reached`): the invariant that `OpGetOK`'s rules take. -/

/-- `PutInv` at every state that a prefix of a transaction's operations
reaches: from its first state (`putInv_init`), `OpPutInvOK` and cost's
`OpTreeOK`. -/
theorem putInv_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (ho : OpTreeOK p) (hP : OpPutInvOK p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact putInv_init p ts tx hw (hR _ _ hr) hT hI z top hz htop
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
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 := ho ts tx hw z top hz htop pre' op post hsplit' r1 w1 h1
            (writerTreeOK_reached p ho ts tx hw z top hz htop hT pre' (op :: post) hsplit' r1 w1 h1)
            a w2 h2
          have := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 a w2 h2 hT2
          rw [← h.2]
          exact this

end SIS.Tree
