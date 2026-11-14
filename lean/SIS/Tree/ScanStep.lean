import SIS.Tree.WalkEdges
import SIS.Tree.RunEncoding

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The four searches used by a scan's next step. -/
def scanChoice (n : KNode) (t : Time) (req : ScanReq) (first eqMatch : Bool)
    (lc : Int) : Option Found :=
  if first && req.inclusive && eqMatch then
    (if req.forward then n.searchGte t lc else n.searchLte t lc)
  else (if req.forward then n.searchGt t lc else n.searchLt t lc)

theorem scanChoice_mem (n : KNode) (t : Time) (req : ScanReq)
    (first eqMatch : Bool) (lc : Int) (fd : Found)
    (hf : scanChoice n t req first eqMatch lc = some fd) :
    (fd.c, fd.y) ∈ n.liveAt t := by
  unfold scanChoice at hf
  split at hf
  · split at hf
    · exact ((n.searchGte_spec t lc).1 fd hf).1
    · exact ((n.searchLte_spec t lc).1 fd hf).1
  · split at hf
    · exact ((n.searchGt_spec t lc).1 fd hf).1
    · exact ((n.searchLt_spec t lc).1 fd hf).1

theorem scanChoice_sentinel (n : KNode) (t : Time) (req : ScanReq) (eqMatch : Bool)
    (hn : n.liveAt t ≠ [])
    (hb : ∀ q ∈ n.liveAt t, cvLo < (q.1 : Int) ∧ (q.1 : Int) < cvHi) :
    scanChoice n t req false eqMatch (if req.forward then cvLo else cvHi) ≠ none := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hn
  intro he
  cases hf : req.forward with
  | true =>
    have hh := (n.searchGt_spec t cvLo).2.mp (by simpa [scanChoice, hf] using he) q hq
    have hp := (hb q hq).1
    simp only [decide_eq_false_iff_not] at hh
    exact hh hp
  | false =>
    have hh := (n.searchLt_spec t cvHi).2.mp (by simpa [scanChoice, hf] using he) q hq
    have hp := (hb q hq).2
    simp only [decide_eq_false_iff_not] at hh
    exact hh hp

/-- Pop the current key node, removing a segment precisely at a segment edge. -/
def scanPop (p : Params) (v : View BVal) (ch : Chain) (rest : List (NodeId × Int)) : Chain :=
  { ch with first := false, links := rest, segs := match rest with
      | (q, _) :: _ =>
        if ((knodeOf p v q).map (·.leaf)) == some true then ch.segs.dropLast else ch.segs
      | [] => ch.segs }

/-- Enter a child at the first cursor in the scan's direction. -/
def scanPush (req : ScanReq) (ch : Chain) (n : KNode) (x : NodeId)
    (rest : List (NodeId × Int)) (fd : Found) : Chain :=
  { ch with first := false
            links := (fd.y, if req.forward then cvLo else cvHi) :: (x, (fd.c : Int)) :: rest,
            segs := if n.leaf then ch.segs ++ [fd.c] else ch.segs,
            seen := fd.y :: ch.seen }

/-- The end-key test shared by the one-step proof equations. -/
def scanPast (req : ScanReq) (ch : Chain) (fd : Found) : Bool :=
  match req.endKey with
  | some e => pastEnd ch.segs fd.c e req.endInclusive
  | none => false

/-- An equation exposing just one step of the unchanged next-step algorithm. -/
theorem nextGo_step (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (f : Nat) (ch : Chain) (x : NodeId) (lc : Int) (rest : List (NodeId × Int))
    (hl : ch.links = (x,lc) :: rest) (n : KNode) (hn : knodeOf p v x = some n) :
    nextGo p v t req (f+1) ch =
      match scanChoice n t req ch.first ch.eqMatch lc with
      | none => nextGo p v t req f (scanPop p v ch rest)
      | some fd =>
        if scanPast req ch fd then (none, {ch with first := false}.done)
        else match v fd.y with
        | none => (none, {ch with first := false}.done)
        | some nd =>
          if nd.isData then
            match valueOf v fd.y with
            | some h => (some ⟨ch.segs ++ [fd.c], h, fd.time⟩,
                { ch with first := false, links := (x, (fd.c : Int)) :: rest })
            | none => (none, {ch with first := false}.done)
          else nextGo p v t req f (scanPush req ch n x rest fd) := by
  simp only [nextGo, hl, hn]
  rfl

end SIS.Tree
