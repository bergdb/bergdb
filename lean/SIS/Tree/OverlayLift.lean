/-
The tree model (bergdb 024-12, TP7; 024-22): the lift of the writer's
overlay, in the shape of `OverlayLiftOK` (SIS/Tree/GetCommit.lean). After a
transaction of a run within reach, every node of the writer's last state
that it did not take back is, as a key node of the structure after the
transaction, that node: its klongs (SIS/Tree/ApplyBridge.lean) and its leaf
flag (`Book`: the level of a node of P, or of a made node within the level
bounds); the nodes taken back are the transaction's; its own top node is not
taken back.

`overlayLiftOKUnder_links` is the lift for every transaction after a run
whose structure has pointers to nodes of P (TP4), a history for every key
node, and klongs of every key node that are well formed and give its
history (`OverlayLiftOKUnder`, SIS/Tree/GetUnder.lean). With the three for
every run within reach it is `OverlayLiftOK` (`overlayLiftOK_of_links`).
-/
import SIS.Tree.OverlayBook
import SIS.Tree.KeyHistRun
import SIS.Tree.GetCommit
import SIS.Tree.GetUnder
import SIS.Tree.WriterBookMerge
import SIS.Tree.WriterTakenOps
import SIS.Tree.KeyLevels
import SIS.Tree.SizeStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem execW_outside_taken (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs, w)) :
    ∀ q ∈ w.outside, w.taken.contains q.1 = true := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      exact boundsOK_outside_taken p _ bs w he

/-- The lift of the overlay for one transaction, from the books of the
writer's last state (`Book`, `TakenAbove`) and the structure before it. -/
theorem overlayLift_of_book (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool)
    (w : W) (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (htaken : TakenAbove tx.base w) :
    (∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
      knodeOf p (viewOf (P.apply i (changesOf i w))) x = some n) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false) := by
  refine ⟨?_, htaken, ?_⟩
  · intro x n hlook hnt
    have hmem := mem_ids_of_lookup w.nodes x n hlook
    have hxg : x ∈ (w.gh.map (·.1)).reverse := by
      rw [← hbook.ids]
      exact List.mem_map.mpr ⟨(x, n), hmem, rfl⟩
    obtain ⟨⟨x', g, h⟩, hgh, hx'⟩ := List.mem_map.mp (List.mem_reverse.mp hxg)
    simp only at hx'
    subst hx'
    have hleaf := hbook.leaf x' n g h hmem hgh
    -- The node of the structure after the transaction, of a key level.
    have hnode : ∃ nd', (P.apply i (changesOf i w)).get? x' = some nd' ∧ nd'.isData = false ∧
        nd'.level ≤ p.keyMax ∧ p.heightOf nd'.level = h := by
      rcases hbook.tag x' g h hgh with ⟨nd, hv, hd, hlv, _, hh⟩ | ⟨hB, hmade, hout⟩
      · have hg := view_eq_get? p P (i - 1) htimes x' nd (rootless_some_eq _ x' nd hv)
        exact ⟨_, get?_apply_of_get? hg, hd, hlv, hh.symm⟩
      · have hin : ¬ (p.G < g ∨ p.H < h) := by
          intro hc
          have := execW_outside_taken p tx i _ bs w he _ (hout hc)
          simp only at this
          rw [hnt] at this
          cases this
        have hhH : h ≤ p.H := by omega
        have halloc := execW_allocatedIds p tx i _ bs w he
        have hnew := newNodeOf_changesOf_made tx.base i w halloc _ hmade hnt
        have hPx := get?_none_of_ge P tx.base x' hfresh hB
        have hnew' : newNodeOf (changesOf i w) x' =
            some { level := p.keyLevel g h, isData := false, hist := [] } := hnew
        have hget : (P.apply i (changesOf i w)).get? x' = some (Node.mk (p.keyLevel g h) false
            ([] ++ addsFor (changesOf i w) i x')) := by
          rw [get?_apply, hPx, Option.none_or, hnew']
          rfl
        exact ⟨_, hget, rfl, keyLevel_le_keyMax p g h hhH, Params.heightOf_keyLevel p g h hhH⟩
    obtain ⟨nd', hget, hd, hlv, hh⟩ := hnode
    rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x' nd' hget hd hlv with
      ⟨n1, hl1, _, _, hk, _⟩ | ⟨_, hno | htk⟩
    · rw [hlook] at hl1
      have hn1 : n = n1 := by simpa using hl1
      subst hn1
      have hlv' : ¬ p.keyMax < nd'.level := by omega
      simp only [knodeOf, viewOf, hget, hd, hlv', Bool.false_or, decide_false, Bool.false_eq_true,
        ↓reduceIte, hh, hk, Option.some.injEq]
      cases n
      simp only [KNode.mk.injEq, and_true]
      exact hleaf.symm
    · rw [hlook] at hno
      cases hno
    · rw [hnt] at htk
      cases htk
  · intro hnt
    obtain ⟨_, _, hnot⟩ := hbook.top hnt
    cases hc : w.taken.contains w.top.id with
    | false => rfl
    | true =>
      have hm : w.top.id ∈ w.taken := by simpa using hc
      exact (hnot (hbook.taken _ hm)).elim

/-- The lift of the writer's overlay, after a run whose structure has TP4, a
history for every key node, and klongs that give the histories. -/
theorem overlayLiftOKUnder_links (p : Params) :
    OverlayLiftOKUnder p (fun P _ => PointersOK P ∧ KeyHistOK p P ∧ KeyNonempty p P) := by
  intro ts tx hw hR noops w hrun
  obtain ⟨hP, hH, hN⟩ := hR
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl : ViewLinksOK tx.base p (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) :=
    viewLinksOK_of p _ _ tx.base hfresh htimes hP hN
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (noops, w) := hrun
  have hbook := execW_book p tx (ts.length + 1) _ noops w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have htaken := execW_takenAbove p tx (ts.length + 1) _ noops w
    (viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl) he
  rw [treeRun_snoc_changes p ts tx noops w hrun]
  exact overlayLift_of_book p (treeRun p ts) (ts.length + 1) tx noops w (by omega) hfresh htimes
    (treeRun_root_level p ts) hH hl he hbook htaken

end SIS.Tree
