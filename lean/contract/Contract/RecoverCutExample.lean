/-
The contract package (bergdb 030-17): Java's search and reads with a top that
lacks a top node, for one history that meets the premises
(`BridgeExample4.h4`, bergdb 030-11: four transactions; top node 5 of time 0,
and top node 7 of time 2 with its skip pointer to top node 5).

A top that holds the history's top from time 2 needs only top node 7: top
node 5 (time 0) is not the top node of time 2, so it may be gone (a cut whose
first available time is 2) or evicted (`topFrom_cut`). From time 2 on Java's
search finds the right space root without it, and Java's reads under eviction
are right (`evict_java_get16`, `evict_java_get8`); at time 1, before the
first available time, the search needs top node 5, and without it finds no
space root (`search_before`), where the whole top finds top node 5's
(`search_whole`). The statements are closed: no premise is left.
-/
import Contract.RecoverCutTheorems
import Contract.RecoverExample

namespace Contract.RecoverCutExample

open Contract Contract.Example3 Contract.BridgeExample3 Contract.BridgeExample4
  Contract.RecoverExample

/-- The top without top node 5: only top node 7, the super root. -/
def tpCut : Top := [(7, { time := 2, root := 4, skips := [(0, 5, 0)] })]

/-- It holds the history's top after the fourth transaction from time 2. -/
theorem topFrom_cut : TopFrom 2 (top4 4) tpCut := by
  refine ⟨by decide, ?_, ?_⟩
  · intro zn hzn hf
    simp only [top4, tp2, tp0, show ¬ (4 < 2) from by decide, ite_false, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hzn
    rcases hzn with rfl | rfl
    · simp at hf
    · decide
  · intro zn hz
    have : topAt (top4 4) 2 = some (7, { time := 2, root := 4, skips := [(0, 5, 0)] }) := by
      decide
    rw [this] at hz
    cases hz
    decide

/-- The history's top is built by the clauses. -/
theorem topGood4 : TopGood (top4 4) :=
  (BridgeExample4.meetsFull.meetsBridgeTop.inv 4 (by decide)).2.good

/-- Under eviction with handles (`ts4`), after the fourth transaction, with
top node 5 out of Java's top: at time 3 the get of [16] gives 6. -/
theorem evict_java_get16 : jget (h4.tree 4) tpCut 3 false [16] = some 6 := by
  rw [(evict_java_tree BridgeExample4.meetsFull (by decide) kinds4 alm rfl rfl ts4 ts4_map
    (j := 4) (t := 3) (by decide) (by decide) false tpCut
    (topFrom_cut.mono topGood4 (by decide))).1 [16]]
  decide

/-- At time 2, between the records 2 and 3, the get of [8] gives 5 (the
delete is at 3). -/
theorem evict_java_get8 : jget (h4.tree 4) tpCut 2 true [8] = some 5 := by
  rw [(evict_java_tree BridgeExample4.meetsFull (by decide) kinds4 alm rfl rfl ts4 ts4_map
    (j := 4) (t := 2) (by decide) (by decide) true tpCut topFrom_cut).1 [8]]
  decide

/-- Before the first available time the search needs the gone top node: at
time 1, between the records 1 and 2, it finds no space root without top node
5; on the whole top it finds top node 5's, the leaf 1. -/
theorem search_before : findRoot tpCut 1 true = none := by decide

theorem search_whole : findRoot (top4 4) 1 true = some 1 := by decide

end Contract.RecoverCutExample
