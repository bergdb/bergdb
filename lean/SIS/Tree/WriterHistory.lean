import SIS.Tree.WriterKlongOps
import SIS.Tree.InvInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every cached history of a successful writer now meets TP1's premise,
so conversion to entries and back loses no klong, including bitmaps and
time markers. This concerns whole cached nodes, before export filtering. -/
theorem execW_cached_roundTrip (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewKlongsWf p v)
    (he : execW p tx i v = .ok (bs, w)) :
    ∀ q ∈ w.nodes, klongsOf (entriesOf q.2.ks) = q.2.ks := by
  intro q hq
  exact klongsRoundTrip q.2.ks (execW_klongsWf p tx i v bs w hv he q hq)

/-- TP9 applies to every cached node after a successful writer, including
nodes changed by splits, merges and upward cleanup. -/
theorem execW_cached_searchEq (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewKlongsWf p v)
    (he : execW p tx i v = .ok (bs, w)) :
    ∀ q ∈ w.nodes, ∀ t cv,
      (q.2.searchEq t cv).map (·.y) = (q.2.liveAt t).lookup cv := by
  intro q hq t cv
  exact searchEqSpec q.2 t cv (execW_klongsWf p tx i v bs w hv he q hq)

theorem initial_upTo_klongsWf (p : Params) (t : Time) (q : NodeId × Node BVal)
    (hq : q ∈ initStruct p) : klongsWf (klongsOf (q.2.hist.upTo t)) = true := by
  rcases mem_init p q hq with rfl | rfl | rfl <;>
    simp [History.upTo, klongsOf, marker, klongsWf]

/-- The primordial reader view meets the writer's physical-history
premise at every time and for all parameters. -/
theorem viewKlongsWf_initial (p : Params) (t : Time) :
    ViewKlongsWf p (view (treeSpec p) (initStruct p) t) := by
  intro x n hn _ _
  unfold view at hn
  split at hn
  · cases hx : (initStruct p).get? x with
    | none => simp [hx] at hn
    | some old =>
      have he : {old with hist := old.hist.upTo t} = n := by simpa [hx] using hn
      subst n
      exact initial_upTo_klongsWf p t (x, old) (mem_of_get? hx)
  · cases hn

theorem execW_initial_klongsWf (p : Params) (tx : Tx) (i : Time)
    (bs : List Bool) (w : W)
    (he : execW p tx i (view (treeSpec p) (initStruct p) 0) = .ok (bs, w)) :
    WriterKlongsWf w :=
  execW_klongsWf p tx i _ bs w (viewKlongsWf_initial p 0) he

end SIS.Tree
