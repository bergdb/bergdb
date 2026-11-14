/-
The take-back's induction (TakeBackRun.lean) with (B) in the form that every
rule of the writer keeps (bergdb 024-12, TP4): `TtReachedN`, a node with a klong
of the transaction's time is reached from the space root. With the overlay's
klongs before the transaction those of the view (`CacheGood`, `execW_good`),
whose pointers are below the transaction's first id (`ViewGood`), it gives the
take-back at the end (`takeBackEnd_of_invT`): a live klong to a node of the
transaction is a klong of the transaction's time. The rest is as in
TakeBackRun.lean; the induction that uses it is `runTree_jointJ2`
(TakeBackRunJ2.lean).
-/
import SIS.Tree.TakeInvTree
import SIS.Tree.WriterGoodOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (A) and (B) in the form every rule keeps. -/
def TakeInvT (p : Params) (P : Struct BVal) (t : Time) (w : W) : Prop :=
  ReachedFree p P t w ∧ TtReachedN (wNode p (viewOf P) w) t w.top.rootKey

/-- A live klong of an overlay node to a node at or above B is a klong of the
transaction's time: the node has a time klong of it. -/
theorem time_of_live_new (B : NodeId) (c : Ctx) (hv : ViewGood B c) (x : NodeId) (n : KNode)
    (hg : Good B c x n) (cv : Nat) (y : NodeId) (hk : Klong.key cv y ∈ n.ks) (hB : B ≤ y) :
    Klong.time c.i ∈ n.ks := by
  have hnot : Klong.key cv y ∉ prefixAt n.ks (c.i - 1) := by
    intro hm
    rw [hg.old] at hm
    unfold baseKlongs at hm
    cases hx : c.view x with
    | none => rw [hx] at hm; cases hm
    | some nd =>
      rw [hx] at hm
      have := hv.ptrs x nd hx cv y hm
      omega
  obtain ⟨s, hs, hts⟩ := later_time_of_not_mem_prefixAt n.ks (c.i - 1) _ hk hnot
  have hle := hg.times s hs
  have hpos := hv.pos
  have : s = c.i := by omega
  rw [← this]
  exact hs

/-- The take-back at a state from (A), (B) in `TtReachedN`'s form, (C), the
overlay's klongs before the transaction those of the view, the nodes taken
back at or above B, and one overlay entry per node. -/
theorem takeBackEnd_of_invT (p : Params) (P : Struct BVal) (B : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hG : CacheGood B c w) (hI : TakeInvT p P c.i w) (hD : DeadTakenLive c.i w)
    (hA : ∀ x ∈ w.taken, B ≤ x) (hU : (w.nodes.map (·.1)).Nodup) : TakeBackEnd w := by
  obtain ⟨hF, hL⟩ := hI
  refine ⟨?_, hF _ TReach.root⟩
  intro q hq hqk cv y hk
  cases hy : w.taken.contains y with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨c', hc⟩ := hD q hq hqk cv y hk hy
    have hlk : w.nodes.lookup q.1 = some q.2 := nex_run_lookup_of_mem w.nodes q.1 q.2 hU hq
    have hqk' : q.1 ∉ w.taken := by simpa using hqk
    have hN : wNode p (viewOf P) w q.1 = some q.2 := by simp [wNode, hqk', hlk]
    have hB : B ≤ y := hA y (by simpa using hy)
    have htm := time_of_live_new B c hv q.1 q.2 (hG.2 q hq) c' y
      (KNode.liveAt_key_mem _ _ c' y hc) hB
    have hr := hL q.1 q.2 hN htm
    have hry : TReach (wNode p (viewOf P) w) c.i w.top.rootKey y := TReach.link hr ⟨q.2, hN, hc⟩
    have := hF y hry
    rw [hy] at this
    cases this

/-- (A) and (B) at a transaction's first state: nothing taken back, and P's
nodes have no klong of the transaction's time. -/
theorem takeInvT_init (p : Params) (ts : List Tx) (tx : Tx) (_hw : Within p (ts ++ [tx]))
    (top : Top) : TakeInvT p (treeRun p ts) (ts.length + 1) (wInit tx top) := by
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  refine ⟨fun y _ => by simp [wInit], ?_⟩
  intro q qn hq hm
  rw [hlook] at hq
  exfalso
  unfold knodeOf viewOf at hq
  cases hg : (treeRun p ts).get? q with
  | none => simp [hg] at hq
  | some nd =>
    simp only [hg] at hq
    split at hq
    · cases hq
    · simp only [Option.some.injEq] at hq
      subst hq
      obtain ⟨e, he, het⟩ := klongsOf_time_mem nd.hist _ hm
      have := treeRun_timesLE p ts _ (mem_of_get? hg) e he
      omega

end SIS.Tree
