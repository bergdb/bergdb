007-08. Step 4: BergDB's take in Lean, and T3 for it
====================================================

Created 2026-10-28 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, as
006-10's W4.1, at his go (006-10, question 3, 09:36: "yes, as recommended:
W4.1 at max effort once 007-07 is in `main`"). Status: done. 007-03's step
4: `TransSeq.take` as step 3 and D4:B left it (007-07, `f89846d`) is a
startup pos policy of the Lean model, and T3 is proved for runs with it.

The answer. With a constant setting sd of the startup distance, the startup
section without its last record, R(s+1), ..., R(k-1), costs less than d_h =
2 sd after every transaction, with or without restarts: the plan's T3 for
the take holds. After a decrease of the setting to sd', it does not hold
against the new d_h at once. What holds is the deadline in force: after
each transaction the section is shorter than the larger of 2 sd and what it
was before the transaction. So after a decrease it never grows, it shrinks
with every transaction while it is at 2 sd' or more, by at least one byte
each time, and once below 2 sd' it stays below. The plan's way to the proof,
that the take keeps up with d_h (`KeepsUp`), is false for the take with
D4:B; the proof goes by induction over the run instead. All of it holds for
every pace, so for BergDB's share, and for every cost of a record, with no
other assumption. The model's take gives the same startup pos as Java's
`TransSeq.take` on 300 generated cases.


1 The take as a policy (the trusted part)
-----------------------------------------

`lean/SIS/Bound.lean` gets eight definitions; they are what a reader must
check against `TransSeq.take` to trust the theorems. In the order of the
file:

* `Stream.span size S`: the cost of R(s+1), ..., R(k-1), where R(k) is the
  last record of S and s its startup pos; 0 if there are none. It is the
  quantity T3 bounds, the startup section without its last record
  (`T3_section` writes it out), and, for the stream before R(i), Java's
  `TransSeq.span()`: from the tpos of the oldest transaction in D, T(s+1),
  to that of the newest, T(i-1).
* `Pace V T`: a pace, any rule that decides whether the take of T(i), having
  taken `taken` got-dirty nodes, also takes the next transaction, of `count`
  nodes, where the deadline does not ask for it; a function of the stream
  before R(i), D, i and T(i), as the model's policies are (011-11, M10), and
  of `taken` and `count`.
* `takeLoop`: the take's loop over the transactions, oldest first: a
  transaction j is taken if it begins at least d before the end of the
  stream (`d ≤ S.cost size j S.length`), or if the pace takes it; the first
  that neither takes ends the take; the result is the last transaction
  taken. The got-dirty nodes of T(j) are D's entries with d(x) = j, the
  `gotDirtyNodes` of its `TransInfo`.
* `takePolicy size sd pace`: the policy. In T(i), the loop over T(s+1), ...,
  T(i-1) (`sectionIdx S s`, the transactions a start reruns and puts in its
  `TransSeq`), from s on, with the deadline at `max (2 * sd i) (S.span
  size)`: Java's `hardSp = streamLength - max(2 * sd, span())`. sd i is the
  setting in force in T(i), any function of i.
* `share`: D × o / O × L / sd, the share of `TransSeq.take`, in Lean's
  `Float`, which is IEEE 754 binary64 as Java's double, with the operations
  in Java's order, so the same bits (checked, section 4).
* `dither`: `TransSeq.dither`, SplitMix64's finalizer, on `UInt64` as Java
  computes it on a long.
* `javaPace size own sd`: BergDB's pace. The share of the record of T(i),
  with D the got-dirty nodes of T(s+1), ..., T(i-1) (not those of T(i),
  which Java adds after the take), o = `own` of T(i), O the own bytes of
  R(s+1), ..., R(i-1), L the cost from R(s) to the end, and the setting;
  the pace takes the next transaction where Java does not stop: Java stops
  where `taken + count > share && share - taken <= u * count`, with u the
  dither of the stream's length.
* `javaTake size own sd = takePolicy size sd (javaPace size own sd)`.

Also changed in the trusted part: `Bound.lean` imports `SIS.Startup` (for
`sectionIdx`); the comments of `sdTarget` and `KeepsUp`, which described the
take before 007-07; no definition that was there changed.

What the model leaves out or abstracts, and why the theorems still hold for
Java's take:

* The record limit (`take`'s `maxBytes`): Java stops before a transaction
  whose nodes would not fit in the record, also past the deadline. Left
  out, as 007-03's step 4 planned. Since 005-31 the nodes of one transaction
  fit in a record whose own part is below 1/16 of the limit, so the record
  limit stops the take only for records near the limit (005-17).
* The meta blocks: Java's positions count them, 128 bytes at the start of
  every 200 kB, and the model's cost of a record does not (007-01, section
  3). Taken into the cost of the record they fall in, the model's positions
  and span are Java's but in one case: when the stream's length before
  R(i) is inside the meta block at the start of a 200 kB block, R(i) begins
  after it (`RecoverableStream.getNextSpos`), up to 128 bytes later, and
  Java's deadline and share, measured from the stream's length, can leave a
  transaction that the model's take takes. The first transaction Java
  leaves then begins less than d + 128 bytes before R(i), so the section
  exceeds the model's bound by less than 128 bytes in that record. Not
  proved.
  (2026-10-28, 005-68: this case does not arise when `Db.store` calls
  `take`. `RecoverableStream.append` writes a meta block together with the
  record that ends at its position, and recovery fills out one that a
  crash cut, so the stream's length is never inside a meta block then, and
  `getLength()` equals `getNextSpos()`, where R(i) begins: Java's argument
  is the model's. Checked by running: 0 of 5,524,901 calls differ, 229 of them
  after a record that ended exactly on a boundary.)
* The own bytes as a function of the transaction (`own : T → Nat`); Java's
  are those of the value nodes the transaction writes, which a value
  transformation decides as it runs. The theorems hold for every pace, so
  they do not depend on it.
* The setting as any function of the transaction's index: Java changes it
  only by `Db.setStartupDistance`, whose own transaction already uses the
  new one, and keeps it in the stream's meta blocks.
* The share's arithmetic is Java's (`Float`), but no theorem uses it: T3
  holds for every pace, so it is a statement of what Java does, checked by
  running, not something the proofs rest on.


2 The theorems
--------------

In `lean/SIS/BoundTheorems.lean`, for a run whose policy is `takePolicy
size sd pace` (so `javaTake size own sd` too), any cost `size` of a record,
and nothing else assumed: not A1 to A5, nor anything of the structure, the
transactions, the pace or the still-dirty test. The transactions of a run
ts are T(1), ..., T(k), k = ts.length; after T(i) the stream is R(0), ...,
R(i). "The section" below is `S.span size`, the startup section without
its last record.

    theorem T3_take_step ... (hp : al.policy = takePolicy size sd pace)
        (db : DB V T) (tr : T) (hsd : 0 < sd db.S.length) :
        (step sp al db tr).S.span size < max (2 * sd db.S.length) (db.S.span size)

On any database, not only after a run: the section after T(i) costs less
than the larger of 2 sd i and the section before T(i), the deadline's
distance in T(i). (Java's setting is at least 10, so 0 < sd i.)

    theorem T3_take ... (M : Nat) (hM0 : 0 < M) (ts : List T)
        (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M) :
        (run sp al ts).S.span size < 2 * M

If the setting is at most M in T(1), ..., T(k), the section after T(k) costs
less than 2 M. With a constant setting sd: less than d_h = 2 sd, the plan's
T3. `T3_take_restarts` is the same for runs with restarts after any
transactions (`runRestarts`).

    theorem T3_take_decrease ... (ts us : List T) (sd' : Nat) (hsd' : 0 < sd')
        (hset : ∀ i, ts.length < i → i ≤ ts.length + us.length → sd i = sd') :
        (run sp al (ts ++ us)).S.span size < 2 * sd' ∨
          (run sp al (ts ++ us)).S.span size + us.length ≤ (run sp al ts).S.span size

D4:B. Let the setting be sd' in T(m+1), ..., T(m+n), m = ts.length and n =
us.length (after a decrease, `setStartupDistance`'s transaction is T(m+1)).
After T(m+n) the section costs less than 2 sd', or at least n less than
after T(m). So it never costs more than the larger of its cost after T(m),
which `T3_take` bounds by twice the largest setting before, and 2 sd' - 1
(corrected after the review, point 2: not more than after T(m) only if that
is 2 sd' or more; a section below 2 sd' may grow, but stays below); it
shrinks with every transaction while it costs 2 sd' or more; it costs less than 2 sd' after at most (its
cost after T(m)) - 2 sd' + 1 transactions, and from then on.
`T3_take_decrease_restarts` is the same with restarts. Raising the setting
needs nothing: `T3_take` with the new setting as M.

    theorem T3_take_rerun ... (M m : Nat) (hM0 : 0 < M) (ts : List T)
        (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
        (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R) :
        let S := (run sp al ts).S
        ((sectionIdx S (lastSp S)).length - 1) * m < 2 * M ∧
          S.cost size (lastSp S + 1) S.length < 2 * M + S.cost size (S.length - 1) S.length

What startup reruns (6.2, step 6), the plan's goal statement: T(s+1), ...,
T(k), whose records cost less than 2 M plus the last record; if every record
costs at least m (48 bytes in Java), there are fewer than 2 M / m + 1 of
them. `T3_take_reads`, with the same hypotheses: what startup reads, R(s),
..., R(k), costs less than 2 M plus the costs of R(s) and R(k).

`#print axioms` of the seven: `[propext, Classical.choice, Quot.sound]`.

And T2, restart invariance (`T2_restart`), holds for runs with the take as
it is: it is proved for every policy that sees only S, D, i and T(i), as
`takePolicy` does, so the stream does not depend on restarts (010, P2;
Java's `testSameStreamAfterDecreaseWithRestartsF`). By running, the runs of
section 4 with restarts give the same stream as without.


3 What is true and what is not
------------------------------

Against the statements of 007-03 and 007-07:

1. **The plan's T3 for the take, with d = d_h: true** for a constant
   setting (`T3_take`), with and without restarts, and for any settings
   below a bound M with 2 M in place of d_h.
2. **"The policy keeps up with d_h (`KeepsUp`)": false** for the take with
   D4:B. `KeepsUp` is over all streams, and on a stream whose span is
   longer than 2 sd the deadline is at the span. Counterexample (a `#guard`
   in `BoundExample.lean`): the run of example 2 with the deadline alone,
   the setting 400 and then 100 from T(31) on; before T(31) the span is 672,
   longer than d_h = 200, and the take asks for an earlier startup pos than
   a startup distance of 200 does. So the proof does not go through
   `KeepsUp` with a constant d. What holds for every stream is that the
   take keeps up with its own deadline's distance, max(2 sd i, span)
   (`takePolicy_keepsUp`), and the theorems follow by induction over the
   run.
3. **"Below the new d_h" right after a decrease: false**, as D4:B intends:
   in example 2 with BergDB's pace and the setting from 2000 to 400 after
   T(40), the section is 1016 and 816 after T(41) and T(42), above the new
   d_h of 800, and 680 after T(43); with the deadline alone, from 400 to
   100, it is above 200 for five transactions (616, 608, 456, 328, 280). The
   precise form is `T3_take_decrease` ("the deadline in force", 007-07,
   10.1).
4. **"The span shrinks with every record" (007-07, 10.1): true, by at least
   one unit of cost, and no more in general.** A record takes every
   transaction that begins within the last record's length of the oldest,
   so the section loses the records taken and gains the last one; when the
   last record is one unit smaller than the oldest, the take takes the
   oldest alone and the section shrinks by one. In a run with the deadline
   alone and a cost carried by the transaction (`slowSpans` in
   `BoundExample.lean`), after a decrease from 50 to 5 the section shrinks
   by exactly 1 with each of 16 transactions in a row while every record
   costs 8 to 10. So a bound on the time to come down, in records or in
   stream written, needs more than the theorems assume: a property of the
   pace, whose share brings it down much faster in Java's runs (after 81 to
   86 records at 200 to 50 MB, 587 to 669 at 1000 to 100 MB; 007-07, 10.4),
   or of the records' sizes.
5. **"Startup reruns the transactions of less than 2 × sd of records, and
   the last transaction" (007-03, the goal): true**, `T3_take_rerun` with M
   = sd, the last record counted whole. **With the last transaction
   counted by its own bytes: false.** A record holds the versions of the
   nodes it takes, in whole transactions, so a small transaction's record
   can hold a large one's got-dirty nodes (007-07, 7.1 and 7.2: single puts
   wrote records of up to 209 kB where their mean was 576 bytes). The
   records at the ends of the section, R(s) and R(k), are bounded only by
   a bound on D (T4, 007-01, section 6). In the model too (a `#guard` in
   `BoundExample.lean` since 2026-10-29, from the review's point 3): with
   the deadline alone at a setting of 200, after T(6) R(s+1), ..., R(6)
   cost 552, at least 2 · 200 + 72, the last transaction's own bytes, and
   less than 2 · 200 + 232, its record's cost. The same holds for what startup
   reads, R(s), ..., R(k): less than the costs of R(s) and R(k) plus 2 M
   (`T3_take_reads`).


4 Checked by running
--------------------

`lean/SIS/BoundExample.lean` (not trusted), all `#guard`s, so `lake build`
runs them:

* **Java's arithmetic, bit for bit.** `dither` at seven positions and
  `share` on three sets of numbers give the bits that `TransSeq.dither` and
  the share's expression of `TransSeq.take` give on JDK 27
  (`Double.doubleToLongBits`, printed by `TakeCheck bits`), among them the
  share 25 and the dithers of 1300 and 1200 (0.41 and 0.99) of
  `TransSeq.testShare`, whose decisions the pace's test reproduces: two
  transactions of 10 nodes and the third if the dither is below 0.5; and a
  transaction with no got-dirty nodes is taken while the share is not used
  up (007-07, 2.4).
* **Against `TransSeq.take` on generated cases.**
  [08-step4-take-in-lean/TakeCheck.java](08-step4-take-in-lean/TakeCheck.java)
  runs `TransSeq.take` of `f89846d` (its source compiled against the main
  tree's jar of 2026-10-27, which predates it) on 300 cases that SplitMix64
  makes from the case number: 1 to 4 records up to the startup pos, a
  `TransSeq` of 0 to 12 transactions with 0 to 29 got-dirty nodes, own bytes
  of 48 to 447 and sizes of their own bytes and 0 to 2,999 more, a setting
  of 10 to 16,009 and the record's own bytes, and prints the number of
  transactions taken in each. `takeCase` makes the same cases as streams of
  the model, with the same generator, D holding also 0 to 4 got-dirty nodes
  of T(i), and runs `javaTake`: the same result in all 300. In the cases the deadline takes a
  transaction in 107, the span is longer than twice the setting in 95, the
  share takes more than the deadline in 213 and stops the take before its
  last transaction in 163. The check tells the take from near misses: the
  deadline alone gives another result in 213 cases, a dither fixed at 0.5
  in 52, and counting T(i)'s got-dirty nodes in D in 11.
* **Runs of example 2** (four leaves, a cost like bytes, `bytes2`; own bytes
  72 a transaction): with `javaTake` at a constant setting of 1000, the
  section stays below 2000 after every transaction on two seeds (at most
  848 on the first) and every step meets `T3_take_step`; with restarts the
  stream is the run's (T2) and the bound holds; with decreases from 2000 to
  400 after T(40) (BergDB's pace, with and without restarts) and from 400 to
  100 after T(30) (the deadline alone), every step meets `T3_take_step` and
  every state `T3_take_decrease`, with the sections of section 3; and the
  counterexamples of section 3, all four. The take before 007-07, with its node limit
  (`oldTake`, the old sketch `javaTake` renamed), does not keep up, as
  before.

Example 2 is small (seven nodes at the start, a few got-dirty nodes a
transaction), so its share is coarse; the generated cases exercise the
share's arithmetic, and Java's own runs (007-06, 007-07) its behavior at
scale.


5 The proof
-----------

`lean/SIS/Proof/BoundTake.lean`, 244 lines, on top of 007's
`Proof/Bound.lean`:

1. The target of a distance d, `sdTarget size d S`, is 0 or a transaction
   that begins at least d before the end (`sdTarget_spec`).
2. The loop: it never returns a startup pos before the one it starts from
   (`takeLoop_ge`); and if every transaction from a to J begins at least d
   before the end, it takes them all, whatever the pace says
   (`takeLoop_reaches`): the deadline's test comes first in each step, and
   the cost to the end only shrinks along the stream (`cost_le_of_le`).
3. So the take keeps up with its own deadline's distance on every stream,
   D, i and T(i): `sdTarget size (max (2 * sd i) (S.span size)) S ≤
   takePolicy size sd pace S D i tr` (`takePolicy_keepsUp`).
4. One transaction of any policy that keeps up with a distance dd in that
   transaction leaves a section shorter than dd, or empty
   (`section_step_of`, the argument of `section_step` with dd for d): if
   R(s+1), ..., R(i-1) cost dd or more, R(s+1) begins dd or more before the
   end, and the target would be s+1 or later. With 3, the section after
   T(i) is shorter than max(2 sd i, the section before) (`take_step`). The
   section before T(i) is the span of the stream before R(i): the
   transactions T(s+1), ..., T(i-1) and the section R(s+1), ..., R(i-2) are
   the same stretch of stream.
5. Runs, with or without restarts, are folds of steps, each followed by a
   startup or not, which keeps the stream (`fold_length`): the bound under
   settings at most M by induction (`fold_bound`; a section shorter than
   2 M before is shorter after, as max(2 sd i, it) < 2 M), and the decrease
   (`fold_decrease`): a section below 2 sd' stays below, and a section at
   2 sd' or more is shorter after the step, by the step bound with max(2
   sd', it) = it.

Nothing else is used; the share, the dither and D's contents never enter.


6 Not covered
-------------

* The record limit (section 1). The meta blocks are left out too, but
  they make no difference to the take (005-68; section 1).
* The trace checker does not compare Java's startup pos with this policy on
  Java's runs (007-03, step 4, "Later"): it would need each record's length
  in bytes in the traces. The generated cases check the take as a function;
  Java's runs are checked against the model's step with Java's startup pos
  as given.
* How fast the section comes down after a decrease, beyond one unit of
  cost per transaction (section 3, point 4): Java's share does it, the
  theorems do not.
* The records at the ends of the section, R(s) and R(k): T4.
* The share's properties: that a record takes its share on average, that
  the section stays near sd. Measured (005-49, 007-06, 007-07), not modeled.


7 Questions for Frans
---------------------

1. The share in the trusted part. `share`, `dither` and `javaPace` state
   what Java does, in `Float`, but no theorem depends on them, since T3
   holds for every pace. Keep them in `Bound.lean`, as the statement of
   BergDB's take with its check against Java, or move them to the examples
   and keep only `takePolicy` trusted? Recommended: keep them; they are 30
   lines, and they say what "BergDB's take" means in the theorems' comments.
2. The trace checker's comparison of the startup pos (007-03, step 4,
   "Later"): now that the model has the policy, add record lengths to the
   trace format, so that C-S can check Java's startup pos against
   `javaTake` on every record? It is a format change in the exporter and in
   `Check/`. Recommended: later, with the next trace format change; the
   generated cases cover the take's arithmetic.
3. A bound on the time to come down after a decrease needs a property of
   the pace (section 3, point 4). Java's runs answer it at scale. Model it?
   Recommended: no.

Frans's answers, 2026-10-28, 13:09 ("as recommended", after the review):

1. Keep `share`, `dither` and `javaPace` in `Bound.lean`, in the trusted
   part, with a note that no theorem uses them and that they are kept to
   check the model against Java's arithmetic (the `#guard`s, TakeCheck).
   Done: the note is in Bound.lean's header and the three definitions'
   comments, and in lean/README.md's table.
2. Record lengths in the traces: later, with the next trace format change.
   As the review notes (its "For Frans", 2), a trace check of the startup
   pos would be the only check that `Db.store` gives `take` the model's
   arguments (the stream length, the setting, the startup pos), on which
   the theorems' meaning for Java rests by reading today, and with each
   record's tpos it would check the meta blocks at scale too.
3. No model of how fast the section comes down after a decrease.


Files
-----

* `lean/SIS/Bound.lean`: the definitions (section 1).
* `lean/SIS/BoundTheorems.lean`: the statements (section 2).
* `lean/SIS/Proof/BoundTake.lean`: the proofs (section 5).
* `lean/SIS/BoundExample.lean`: the checks by running (section 4).
* [08-step4-take-in-lean/TakeCheck.java](08-step4-take-in-lean/TakeCheck.java):
  the probe that runs `TransSeq.take` on the generated cases; how to run it
  is in its comment.


Review, 2026-10-28
------------------

2026-10-28, 13:05, by Claude (Opus 5.5, Claude Code): an independent
review at max effort of `db1eca8`, `a0e47c3`, `63471fc`, `8e71ffb` and
`8b6669f`, from the Lean and the Java, not from the account above. In my
clone `/Users/f/fl/bench/006-10/rev8/` at `8b6669f`; my checks are in its
`review/` folder (not committed; run from lean/ with `lake env lean
../review/<file>`).

**1. Faithfulness.** `takePolicy` is `TransSeq.take` of `f89846d`
(unchanged since) as `Db.store` calls it, but for the record limit and the
meta blocks. The loop's list, T(s+1), ..., T(i-1), is the `TransSeq`:
`store` adds every transaction after its take, and `DbStarter` adds
T(s+1), ..., T(k) again at a start. The test `d ≤ S.cost size j S.length`
is Java's `first.tpos <= hardSp`; `max (2 * sd i) (S.span size)` is
`Math.max(2L * startupDistance, span())`, `Stream.span` of the stream
before R(i) being `last.tpos - first.tpos`; both, and the share, are
computed once before the loop; the pace sees what Java's break test sees;
the result is the last transaction taken, or s. `javaPace` takes D, o, O,
L and the dither as `take` does. The Float model is sound: `Nat.toFloat`
rounds to nearest below 2^64, as Java's long to double does; `*` and `/`
are binary64 and left-associative, in Java's order; comparisons with NaN
are false in both. TakeCheck runs the real `TransSeq.take` (I built it
from the clone's sources, JDK 27): its 300 results are `javaTakes`, and
`TakeCheck bits` prints the `#guard`s' bits. Two limits of these checks:
the share's bits come from a copy of the expression in TakeCheck, not from
TransSeq (`a0e47c3`'s message says both come from TransSeq itself); and
neither the three share checks nor the 300 cases tell Java's order of the
share's operations from two other orders, or the deadline's `≤` from `<`
(review/Variants.lean: 0 of 300 cases differ, where a dither of 0.5
changes 52, the deadline alone 213, T(i)'s nodes in D 11, the deadline
without the span 40). On three inputs where the order changes the bits,
`share` gives Java's (review/Order3.lean, ShareBits.java); the `≤` I
confirm by reading.

The meta blocks: section 1's account holds for one record, not for runs.
After a record that ends exactly on a 200,000-byte boundary, `take` gets
`getLength()`, 128 bytes before where R(i) begins (`getNextSpos`), so
Java's deadline is 128 bytes stricter than the model's. This recurs at
every such record, and the theorems are inductions over records. With
records that each fill a block (199,872 bytes) and a pace that takes
nothing more, Java's section after a decrease stays at m × 200,000 bytes,
where the model's loses a record each time, and at a constant setting it
can stay up to 127 bytes above 2 sd. So "for every pace" does not carry
over to Java there. With Java's share, about L/sd' ≥ 2 transactions'
worth of nodes a record while the section is above 2 sd', it should not
matter, and 007-07's runs shrank at every record. Passing
`nodeStream.getNextPos()` instead of `getLength()` to `take` in
`Db.store` would make the model exact here.

**2. The statements**, read in full (review/Stmts.lean), say what section
2 says. `T3_take` with M = sd is 007-03's T3 with d = d_h, `T3_take_rerun`
with M = sd the goal's sentence with the last record whole, and
`T3_take_decrease` the honest form under D4:B. The hypotheses are only the
policy, M > 0 and the settings, and they are met: review/NonVacuous.lean
applies `T3_take` to example 2's run with `javaTake` at a setting of 1000,
and `T3_take_decrease` to the decrease from 2000 to 400 after T(40), where
the second disjunct is the one that holds. The section without its last
record is the right quantity: the take chooses s(k) before R(k) exists, so
R(s+1), ..., R(k-1) is what it can bound, and the theorems add R(s) and
R(k) for the reads and the rerun. `T3_take_reads` is what startup reads in
full (6.2, step 3; `readTransactions` from the startup pos), not all that
it reads: the reads through references into older records (step 5; rule 4
and the index at s from a cold disk, the plan's N) are outside it, as for
`T3_reads`. One comment is wrong: "So it never costs more than after
T(m)" (`T3_take_decrease`, and section 2) holds only if the section after
T(m) costs at least 2 sd'; in general it never costs more than the larger
of that and 2 sd' - 1. The statement itself is right.

**3. The counterexamples** are correct. Three are `#guard`s that the
build runs: `KeepsUp` with 2 sd (transaction 31 of the run from 400 to
100), above the new d_h right after a decrease (1016 and 816; 616 to
280), and one unit a transaction (`slowSpans`). `KeepsUp` fails since it
is over all streams; at a constant setting the take keeps up with d_h on
every stream a run reaches (by `T3_take`). The fourth, R(s+1), ..., R(k)
below 2 sd plus the last transaction's own bytes, is argued from 007-07's
Java data, not checked; it is false in the model too
(review/NonVacuous.lean, `viol`: with the deadline alone at sd 200, after
T(6) they cost 552 ≥ 2 · 200 + 72).

**4. The trusted part.** The theorems need `Stream.span`, `Pace`,
`takeLoop` and `takePolicy` (with `sectionIdx`, trusted before): minimal.
`share`, `dither`, `javaPace` and `javaTake` enter no theorem, so they
cannot make one wrong; keeping them is harmless, but Bound.lean's header
and lean/README.md's table list them with the trusted definitions without
saying so. No definition changed: `Stream.cost`, `sdTarget`, `KeepsUp` and
`sdPolicy` are as before, with accurate new comments; no other trusted
file and no earlier statement changed.

**5. The checks.** In the fresh clone, `nice -n 10 lake build`: "Build
completed successfully (148 jobs)", no warnings, 67 s (review/build.log).
`#print axioms` of the seven and of `takePolicy_keepsUp`
(review/Axioms.lean): `[propext, Classical.choice, Quot.sound]`. `sh
test-traces/run.sh`: "TRACE TESTS OK". No `sorry`, `admit`,
`native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`,
`ofReduceBool`, `maxHeartbeats` or `by decide` anywhere in lean/; `decide`
only as Bool tests in definitions.

**6. Docs.** docs/sis-model.md, docs/levels.md and lean/README.md claim
what is proved, and name the record limit and the meta blocks as left out.
README.md's "Bounded startup is proved for BergDB's own startup pos
policy" says more than T3, which leaves the records at the ends (T4) and a
cold start's random reads open (levels.md already used the phrase for
T3); what follows its colon is exact. "Comes down with every commit" holds
for the model; for Java it rests on the share (point 1).

**Changes made.** None to the Lean, the Java or the docs; only this
section.

**Verdict.** Faithful to `TransSeq.take` without the record limit and the
meta blocks, not vacuous, the proofs sound. No error in a definition, a
statement or a proof; one wrong comment (point 2) and an understated
caveat (point 1).

**For Frans.**

1. The subitem's question 1: keep `share`, `dither` and `javaPace` in
   Bound.lean, as recommended, with a line there and in lean/README.md
   that no theorem uses them.
2. Question 2: later, as recommended. But a trace check of the startup pos
   is the only check that `Db.store` gives `take` the model's arguments
   (the stream length, the setting, the startup pos), which the theorems'
   meaning for Java now rests on by reading; with each record's tpos it
   would cover the meta blocks too.
3. Question 3: no, as recommended.
4. The meta blocks (point 1): keep them out, as documented, with section 1
   saying that the 128 bytes can recur; or pass `getNextPos()` to `take`,
   which changes a stream only after a record that ends on a block
   boundary.
5. For the author: the comment of point 2, a `#guard` for the fourth
   counterexample, and README.md's first words (point 6).

**Follow-up, 2026-10-28** (006-10, at Frans's word, 13:09: "as
recommended"): the comment of point 2 corrected, in `T3_take_decrease` and
section 2; README.md's sentence now says that T3, the startup section's
bound, is proved, and that T4 and a cold start's reads through references
are open, and docs/levels.md's limit says the same; the note of point 4 on
`share`, `dither` and `javaPace`; Frans's answers to section 7's questions
are under them. Comments and documents only; `lake build` clean. The
fourth counterexample's `#guard` is not made. The meta blocks (point 4 for
Frans): a fix was decided, as 005-68, which found that point 1's case does
not arise: when `take` is called the stream's length is where R(i) begins,
as `RecoverableStream.append` writes a meta block with the record that ends
at its position; so the gap is not there, and 005-68 was dropped with no
change.

**Follow-up, 2026-10-29** (006-10's decision 9; Frans, 10:09: "Yes, as
recommended for 5 to 9"), by Claude (Opus 5.5, Claude Code): the fourth
counterexample is a `#guard` at the end of `BoundExample.lean`: with the
deadline alone at a setting of 200, after T(6) R(s+1), ..., R(6) cost 552,
at least 2 · 200 + 72 (`own2`) = 472, and less than 2 · 200 + 232, R(6)'s
cost, as `T3_take_rerun` says (section 3, point 5; the review's `viol`).
README.md, docs/levels.md, docs/sis-model.md and lean/README.md no longer
say only that the meta blocks are not modelled: they still are not, but
005-68 showed that they make no difference to the take (`getLength()`
equals `getNextPos()` whenever `take` runs), while the record limit is
still left out. `nice -n 10 lake build`: "Build completed successfully (148
jobs)", no warnings, no `sorry`; `sh test-traces/run.sh`: "TRACE TESTS OK".
