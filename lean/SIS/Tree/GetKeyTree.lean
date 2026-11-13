import SIS.Tree.GetUnder
import SIS.Tree.WriterTree
import SIS.Tree.InvConsequences

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! TREE for key nodes (`KeyTreeOK`, a part of `RunReadOK`) from the tree of P
(`TreeAt`, SIS/Tree/WriterTree.lean): the key nodes reachable at t are reached
from the space root by links, and the tree names each node by one link at
most. So TP10 and TP11 need, of the runs, TP7, `KeyNodesOK` and `TreeAt`
(`getOK_of_treeAt`, `scanOK_of_treeAt`). -/

theorem nodesAt_tReach (p : Params) (view : View BVal) (t : Time) (r : NodeId) :
    ∀ (f : Nat) (x y : NodeId), TReach (knodeOf p view) t r x → y ∈ nodesAt p view t f x →
      TReach (knodeOf p view) t r y := by
  intro f
  induction f with
  | zero => intro x y _ h; simp [nodesAt] at h
  | succ f ih =>
    intro x y hx hy
    simp only [nodesAt] at hy
    cases hn : knodeOf p view x with
    | none => rw [hn] at hy; cases hy
    | some n =>
      rw [hn] at hy
      simp only [List.mem_cons, List.mem_flatMap] at hy
      rcases hy with rfl | ⟨⟨c, z⟩, hz, hyz⟩
      · exact hx
      · split at hyz
        · cases hyz
        · exact ih z y (TReach.link hx ⟨n, hn, hz⟩) hyz

theorem keyTreeOK_of_treeAt (p : Params) (P : Struct BVal) (t : Time) (hT : TreeAt p P t) :
    KeyTreeOK p P t := by
  obtain ⟨r, hr, ht⟩ := hT
  have hreach : ∀ x ∈ keyNodesAt p P t, TReach (knodeOf p (viewOf P)) t r x := by
    intro x hx
    simp only [keyNodesAt, hr] at hx
    exact nodesAt_tReach p (viewOf P) t r p.fuel r x TReach.root hx
  intro x1 hx1 x2 hx2 n1 n2 h1 h2 q1 hq1 q2 hq2 hq
  rw [keyNodeAt_eq_knodeOf] at h1 h2
  have l1 : TLink (knodeOf p (viewOf P)) t x1 q1.1 q1.2 := ⟨n1, h1, hq1⟩
  have l2 : TLink (knodeOf p (viewOf P)) t x2 q2.1 q1.2 := ⟨n2, h2, by rw [hq]; exact hq2⟩
  exact ht.oneLink x1 q1.1 x2 q2.1 q1.2 (hreach x1 hx1) (hreach x2 hx2) l1 l2

/-- TP10 from TP7, the key nodes sound as they are and P's tree after every run
within reach, and the two statements about the writer under `RunReadOK`. -/
theorem getOK_of_treeAt (p : Params) (hinv : InvPreserved p)
    (hK : ∀ ts, Within p ts → KeyNodesOK p (treeRun p ts))
    (hT : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpGetOKUnder p (RunReadOK p)) (hl : OverlayLiftOKUnder p (RunReadOK p)) : GetOK p :=
  getOK_of_runRead p hinv
    (fun ts hw => ⟨hK ts hw, keyTreeOK_of_treeAt p _ _ (hT ts hw)⟩) ho hl

/-- TP11 from TP7, the key nodes sound as they are and P's tree after every run
within reach, and the two statements about the writer under `RunReadOK`. -/
theorem scanOK_of_treeAt (p : Params) (hinv : InvPreserved p)
    (hK : ∀ ts, Within p ts → KeyNodesOK p (treeRun p ts))
    (hT : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpGetOKUnder p (RunReadOK p)) (hl : OverlayLiftOKUnder p (RunReadOK p)) : ScanOK p :=
  scanOK_of_runRead p hinv
    (fun ts hw => ⟨hK ts hw, keyTreeOK_of_treeAt p _ _ (hT ts hw)⟩) ho hl

end SIS.Tree
