/-
Self-indexed streams in Lean: bounds, part 1, the length of the startup
section (bergdb item 007; docs/sis-model.md, section 10, the planned T3).

Trusted part: the definitions that T3 is about. The statements are in
SIS/BoundTheorems.lean. Added 2026-10-23. Since 2026-10-28 (bergdb 007-08,
step 4 of 007-03) also BergDB's take, `TransSeq.take` as step 3 and D4:B left
it (bergdb 007-07): `Stream.span`, `Pace`, `takeLoop`, `takePolicy`, and
BergDB's pace with its share and rounding, `share`, `dither`, `javaPace` and
`javaTake`.
-/
import SIS.Algorithm
import SIS.Startup

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
that is, R(j), ..., R(i-1) cost at least d; 0 if there is none. The stream
length is before R(i), as in BergDB's `TransSeq.take`, whose deadline takes
the transactions with tpos <= stream length − d, for d the larger of twice the
setting and the span of the section (`takePolicy`, since bergdb 007-07). -/
def sdTarget (size : Record V T → Nat) (d : Nat) (S : Stream V T) : Nat :=
  ((List.range S.length).filter (fun j => decide (d ≤ S.cost size j S.length))).foldl max 0

/-- A startup pos policy keeps up with a startup distance of d if it never
asks for a startup pos before `sdTarget` (bergdb item 007). The algorithm
clamps the policy (`startupPos`); T3 needs nothing else of it. BergDB's take
before bergdb 007-07 did not keep up: after two transactions it stopped at a
limit on the nodes taken (bergdb 011-01, Q4). Its take since then, `takePolicy`,
keeps up with the larger of twice the setting and the span of the section,
which depends on the stream; it does not keep up with a d of its own, and T3
for it is stated over runs (`T3_take`, bergdb 007-08). -/
def KeepsUp (size : Record V T → Nat) (d : Nat) (al : Algo V T) : Prop :=
  ∀ S D i tr, sdTarget size d S ≤ al.policy S D i tr

/-- The startup distance policy: the startup pos that a startup distance of d
asks for (`sdTarget`), with no limit on the nodes taken. -/
def sdPolicy (size : Record V T → Nat) (d : Nat) : Stream V T → Dirty → Time → T → Nat :=
  fun S _ _ _ => sdTarget size d S

/-! ## BergDB's take (bergdb 007-08)

`TransSeq.take` as step 3 of 007-03 and D4:B left it (bergdb 007-07, `f89846d`;
005-49's report, section 6). A commit takes whole transactions of D, oldest
first: as many as its share asks for, and every one that begins the deadline's
distance or more before the end of the stream. The share is the pace: any rule
that decides, transaction by transaction, whether to take the next one
(`Pace`); the theorems hold for every pace, and BergDB's is `javaPace`. Left
out of the model, as 007-03's step 4 says: the record limit (`take`'s
`maxBytes`), which stops the take before a transaction whose nodes would not
fit in the record, also past the deadline (since 005-31 the nodes of one
transaction fit in a record whose own part is below 1/16 of the limit); and
the meta blocks, 128 bytes every 200 kB, which Java's positions count and the
model's cost of a record does not (bergdb 007-08, section 1). -/

/-- The span of the startup section's transactions: the cost of R(s+1), ...,
R(k-1), from the beginning of R(s+1) to that of R(k), where R(k) is the last
record of S and s its startup pos; 0 if s + 1 ≥ k. It is the startup section
without its last record, which T3 bounds. In the stream before R(i), it is
Java's `TransSeq.span()`, from the tpos of the oldest transaction whose
got-dirty nodes are in D, T(s+1), to that of the newest, T(i-1) (bergdb
007-07). -/
def Stream.span (size : Record V T → Nat) (S : Stream V T) : Nat :=
  S.cost size (lastSp S + 1) (S.length - 1)

/-- A pace (bergdb 005-49): whether the take of transaction i, which has taken
`taken` got-dirty nodes so far, also takes the next transaction, which has
`count` of them, where the deadline does not ask for it. A function of the
stream S before R(i), D, i and T(i), as a policy is (6.1, step 4; 005-49's
report, 7.5: "For T3 the pace can be any predicate on the stream and T(i)").
BergDB's pace is `javaPace`; `fun _ _ _ _ _ _ => false` is the deadline alone. -/
abbrev Pace (V T : Type) := Stream V T → Dirty → Time → T → Nat → Nat → Bool

/-- The take's loop (`TransSeq.take`'s `while`), over the transactions js,
oldest first, with `taken` got-dirty nodes taken so far and acc the last
transaction taken: a transaction j is taken if it begins at least d before the
end of the stream S, or if the pace takes it; the first that neither takes
ends the take. The got-dirty nodes of T(j) are D's entries with d(x) = j, the
`gotDirtyNodes` of its `TransInfo`. Returns the last transaction taken, or acc
if none. -/
def takeLoop (size : Record V T → Nat) (d : Nat) (pace : Nat → Nat → Bool) (S : Stream V T)
    (D : Dirty) : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | j :: js, taken, acc =>
    let count := (D.filter (fun e => e.2 == j)).length
    if d ≤ S.cost size j S.length ∨ pace taken count = true then
      takeLoop size d pace S D js (taken + count) j
    else acc

/-- BergDB's take (`TransSeq.take`, bergdb 005-49 and 007-07) as a startup pos
policy, with sd i the startup distance's setting in transaction i and a pace.
In transaction i, with S the stream before R(i) and s = s(i-1) its last
startup pos, it runs the take's loop over T(s+1), ..., T(i-1), Java's
`TransSeq` (`sectionIdx`, the transactions that a start reruns), from s on,
with the deadline at the larger of twice the setting, d_h = 2 sd i, and the
span of these transactions (`Stream.span`): `hardSp = streamLength - max(2 *
sd, span())`. While the span is below d_h the deadline is at d_h; after a
decrease of the setting it is at the span, which shrinks with every
transaction (D4:B). The setting is any function of i: in Java it changes only
by `Db.setStartupDistance`, whose own transaction already uses the new one. -/
def takePolicy (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T) :
    Stream V T → Dirty → Time → T → Nat :=
  fun S D i tr =>
    takeLoop size (max (2 * sd i) (S.span size)) (pace S D i tr) S D
      (sectionIdx S (lastSp S)) 0 (lastSp S)

/-- The share of a record (`TransSeq.take`, bergdb 005-49): D × o / O × L / sd,
where D (`dirty`) is the number of got-dirty nodes of the section's
transactions, o (`own`) the record's own bytes, O (`ownSec`) those of the
section's records, L (`len`) the length of the section, from the startup pos
to the end of the stream, and sd the setting. In Java's double arithmetic and
order: Lean's `Float` is the same IEEE 754 binary64, with the same rounding
(SIS/BoundExample.lean compares bits with Java's). -/
def share (dirty own ownSec len sd : Nat) : Float :=
  dirty.toFloat * own.toFloat / ownSec.toFloat * len.toFloat / sd.toFloat

/-- `TransSeq.dither`: a number in [0, 1) hashed from a stream position, the
finalizer of SplitMix64, as Java computes it on a `long` (multiplications mod
2^64, logical shifts). -/
def dither (pos : Nat) : Float :=
  let z : UInt64 := UInt64.ofNat pos * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  ((z ^^^ (z >>> 31)) >>> 11).toFloat * Float.scaleB 1 (-53)

/-- BergDB's pace (`TransSeq.take`, bergdb 005-49): the record of T(i) has the
share `share` of D, and takes the transactions that fit in it; the next one,
of which only a part fits, if that part is larger than the dither of the
stream's length. Java stops where `taken + count > share && share - taken <= u
* count` (and the deadline does not ask for the transaction); this pace takes
the transaction where Java does not stop. D counts the got-dirty nodes of
T(s+1), ..., T(i-1), Java's `dirtyCount`, without those of T(i), which Java
adds to its `TransSeq` after the take. `own t` is the own bytes of the record
of transaction t (`TransSeq.ownBytes`: its value nodes and 48), a function of
the transaction here; in Java it is that of the value nodes the transaction
writes. -/
def javaPace (size : Record V T → Nat) (own : T → Nat) (sd : Time → Nat) : Pace V T :=
  fun S D i tr taken count =>
    let s := lastSp S
    let dirty := (D.filter (fun e => decide (s < e.2 ∧ e.2 < i))).length
    let ownSec := S.cost (fun R => (R.trans.map own).getD 0) (s + 1) S.length
    let sh := share dirty (own tr) ownSec (S.cost size s S.length) (sd i)
    let u := dither (S.cost size 0 S.length)
    !(decide (sh < (taken + count).toFloat) && decide (sh - taken.toFloat ≤ u * count.toFloat))

/-- BergDB's take, `TransSeq.take` as bergdb 007-07 left it: `takePolicy` with
BergDB's pace. -/
def javaTake (size : Record V T → Nat) (own : T → Nat) (sd : Time → Nat) :
    Stream V T → Dirty → Time → T → Nat :=
  takePolicy size sd (javaPace size own sd)

end SIS
