/-
The tree model (bergdb 024-12, section 6): TP13 for the primordial structure.
`initStruct` (the root, the first top node, the primordial key node) meets
`SpecOK` with `VirtInit`: distinct ids, entries at time 0, pointers to lower
levels, every node reachable at time 0, the root's history the entry for its
one top node. Proved but for `SpecOK.liveSub`, a property of `blive` alone,
which is a hypothesis here: bergdb 024-09's branch proves it
(Check/Live.lean). And `RunPSame` (with TP19): the structure of the model's
`run` on the tree is `treeRun`. Proofs; not needed for reading the statements.
-/
import SIS.Tree.Props

namespace SIS.Tree

open SIS SIS.Check

theorem lvl_top_root (p : Params) : p.topLevel 0 < p.rootLevel := by
  unfold Params.topLevel Params.rootLevel
  omega

theorem lvl_key_top (p : Params) : p.keyLevel 0 0 < p.topLevel 0 := by
  unfold Params.keyLevel Params.topLevel Params.keyMax
  simp only [Nat.sub_zero]
  omega

theorem init_get_root (p : Params) :
    (initStruct p).get? root = some { level := p.rootLevel, isData := false, hist := [⟨0, .top 2⟩] } := by
  rfl

theorem init_get_top (p : Params) :
    (initStruct p).get? 2 = some { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] } := by
  rfl

theorem init_get_key (p : Params) :
    (initStruct p).get? 1 = some { level := p.keyLevel 0 0, isData := false, hist := [⟨0, marker⟩] } := by
  rfl

theorem init_reach (p : Params) : reachList (treeSpec p) (initStruct p) 0 = [0, 2, 1] := by
  unfold reachList
  rw [init_get_root]
  simp only
  rw [reachFrom]
  have h1 : (treeSpec p).live (History.upTo [(⟨0, BVal.top 2⟩ : Entry BVal)] 0) = [2] := by
    show blive _ = _
    decide
  simp only [h1, List.flatMap_cons, List.flatMap_nil, init_get_top, lvl_top_root, ↓reduceIte, List.append_nil]
  rw [reachFrom]
  have h2 : (treeSpec p).live (History.upTo [(⟨0, BVal.rootKey 1⟩ : Entry BVal)] 0) = [1] := by
    show blive _ = _
    decide
  simp only [h2, List.flatMap_cons, List.flatMap_nil, init_get_key, lvl_key_top, ↓reduceIte, List.append_nil]
  rw [reachFrom]
  have h3 : (treeSpec p).live (History.upTo [(⟨0, marker⟩ : Entry BVal)] 0) = [] := by
    show blive _ = _
    decide
  simp [h3, root]

theorem mem_init (p : Params) (q : NodeId × Node BVal) (hq : q ∈ initStruct p) :
    q = (root, { level := p.rootLevel, isData := false, hist := [⟨0, .top 2⟩] }) ∨
    q = (1, { level := p.keyLevel 0 0, isData := false, hist := [⟨0, marker⟩] }) ∨
    q = (2, { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] }) := by
  simpa [initStruct] using hq

theorem virtInitTree (p : Params) : VirtInit (treeSpec p) where
  rootPtrs := fun _ => rfl
  rootIndex := by
    intro n hn
    have h := init_get_root p
    rw [show (treeSpec p).init = initStruct p from rfl, h] at hn
    cases hn
    rfl
  initTop := by
    intro q hq hne hlv
    have h12 := lvl_key_top p
    rcases mem_init p q hq with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact absurd hlv (by show ¬ (p.topLevel 0 ≤ p.keyLevel 0 0); omega)
    · refine ⟨rfl, by simp, ?_⟩
      intro q' hq' hne' hlv'
      rcases mem_init p q' hq' with rfl | rfl | rfl
      · exact absurd rfl hne'
      · exact absurd hlv' (by show ¬ (p.topLevel 0 ≤ p.keyLevel 0 0); omega)
      · rfl
  initRootHist := by
    intro n hn
    have h := init_get_root p
    rw [show (treeSpec p).init = initStruct p from rfl, h] at hn
    cases hn
    have h12 := lvl_key_top p
    have h23 := lvl_top_root p
    simp [treeSpec, initStruct, root, Nat.not_le.mpr h12, Nat.le_of_lt h23]

/-- TP13, proved but for `liveSub`, a property of `blive` that 024-09's branch
proves (Check/Live.lean): the primordial structure meets `SpecOK` and
`VirtInit`. -/
theorem specOKTree_of_liveSub (p : Params)
    (hl : ∀ (h : History BVal) (y : NodeId), y ∈ blive h → ∃ e ∈ h, y ∈ bptrs e.val) :
    SpecOKTree p where
  liveSub := hl
  initDistinct := by
    show ((initStruct p).map (·.1)).Nodup
    simp [initStruct, root]
  initRoot := by
    show ((initStruct p).get? root).isSome = true
    rw [init_get_root]
    rfl
  initTime := by
    intro q hq e he
    rcases mem_init p q hq with rfl | rfl | rfl <;> simp at he <;> rw [he]
  initData := by
    intro q hq hd
    rcases mem_init p q hq with rfl | rfl | rfl <;> simp at hd
  initLevels := by
    intro q hq e he y hy
    have h12 := lvl_key_top p
    have h23 := lvl_top_root p
    rcases mem_init p q hq with rfl | rfl | rfl
    · simp at he
      subst he
      have : y = 2 := by simpa [treeSpec, bptrs] using hy
      subst this
      exact ⟨_, init_get_top p, h23⟩
    · simp at he
      subst he
      simp [treeSpec, bptrs, marker] at hy
    · simp at he
      subst he
      have : y = 1 := by simpa [treeSpec, bptrs] using hy
      subst this
      exact ⟨_, init_get_key p, h12⟩
  initReachable := by
    intro q hq
    show (reachList (treeSpec p) (initStruct p) 0).contains q.1 = true
    rw [init_reach]
    rcases mem_init p q hq with rfl | rfl | rfl <;> simp [root]
  virtInit := fun _ => virtInitTree p

/-! ## The model's run on the tree -/

theorem step_P (sp : Spec BVal Tx) (al : Algo BVal Tx) (db : DB BVal Tx) (tr : Tx) :
    (step sp al db tr).P =
      db.P.apply db.S.length (sp.exec tr db.S.length (view sp db.P (db.S.length - 1))) := rfl

theorem step_S_length (sp : Spec BVal Tx) (al : Algo BVal Tx) (db : DB BVal Tx) (tr : Tx) :
    (step sp al db tr).S.length = db.S.length + 1 := by
  simp [step]

theorem run_from (p : Params) (al : Algo BVal Tx) (ts : List Tx) :
    ∀ (db : DB BVal Tx) (k : Nat), db.S.length = k + 1 →
      (ts.foldl (step (treeSpec p) al) db).P =
        (ts.zipIdx k).foldl (fun P (q : Tx × Nat) =>
          P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) db.P := by
  induction ts with
  | nil => intro db k _; rfl
  | cons tr t ih =>
    intro db k hk
    rw [List.foldl_cons, List.zipIdx_cons, List.foldl_cons]
    have h1 := ih (step (treeSpec p) al db tr) (k + 1) (by rw [step_S_length, hk])
    rw [h1, step_P, hk]
    rfl

/-- `RunPSame`, proved (with TP19): the structure of the model's `run` on the
tree is `treeRun`, whatever the algorithm's choices. -/
theorem runPSame (p : Params) : RunPSame p := by
  intro al ts
  have h := run_from p al ts (init (treeSpec p)) 0 (by simp [init])
  unfold run treeRun
  rw [h]
  rfl

end SIS.Tree
