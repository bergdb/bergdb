/-
Self-indexed streams in Lean: bounds, part 1, the length of the startup
section (bergdb item 007; docs/sis-model.md, section 10, the planned T3).

Trusted part: the definitions that T3 is about. The statements are in
SIS/BoundTheorems.lean. Added 2026-10-23.
-/
import SIS.Algorithm

namespace SIS

variable {V T : Type}

/-- The cost of the records R(a), ..., R(b-1) of S, for a cost `size` of each
record (bergdb item 007). The model has records, not bytes (10); `size` is the
cost model. For BergDB's startup distance it is the bytes of the record in the
stream; it may as well count transactions, or estimate the time to read a
record and rerun its transaction. T3 holds for every `size`. -/
def Stream.cost (size : Record V T → Nat) (S : Stream V T) (a b : Nat) : Nat :=
  (((S.drop a).take (b - a)).map size).sum

/-- The startup pos that a startup distance of d asks for in transaction
i = S.length, where S is the stream before R(i) (6.1, step 4): the last
transaction j < i whose record begins at least d before the end of the stream,
that is, R(j), ..., R(i-1) cost at least d; 0 if there is none. BergDB's
`TransSeq.take` takes the transactions with tpos <= stream length − startup
distance, where the stream length is before R(i), as here. -/
def sdTarget (size : Record V T → Nat) (d : Nat) (S : Stream V T) : Nat :=
  ((List.range S.length).filter (fun j => decide (d ≤ S.cost size j S.length))).foldl max 0

/-- A startup pos policy keeps up with a startup distance of d if it never
asks for a startup pos before `sdTarget` (bergdb item 007). The algorithm
clamps the policy (`startupPos`); T3 needs nothing else of it. BergDB's take
(`TransSeq.take`) does not keep up: after two transactions it stops at a limit
on the nodes taken (docs/problem.md, Q4). -/
def KeepsUp (size : Record V T → Nat) (d : Nat) (al : Algo V T) : Prop :=
  ∀ S D i tr, sdTarget size d S ≤ al.policy S D i tr

/-- The startup distance policy: the startup pos that a startup distance of d
asks for (`sdTarget`), with no limit on the nodes taken. -/
def sdPolicy (size : Record V T → Nat) (d : Nat) : Stream V T → Dirty → Time → T → Nat :=
  fun S _ _ _ => sdTarget size d S

end SIS
