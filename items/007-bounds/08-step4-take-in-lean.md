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
after T(m). So it never costs more than after T(m), which `T3_take` bounds
by twice the largest setting before; it shrinks with every transaction
while it costs 2 sd' or more; it costs less than 2 sd' after at most (its
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
   a bound on D (T4, 007-01, section 6). The same holds for what startup
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
  counterexamples of section 3. The take before 007-07, with its node limit
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

* The record limit and the meta blocks (section 1).
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


Files
-----

* `lean/SIS/Bound.lean`: the definitions (section 1).
* `lean/SIS/BoundTheorems.lean`: the statements (section 2).
* `lean/SIS/Proof/BoundTake.lean`: the proofs (section 5).
* `lean/SIS/BoundExample.lean`: the checks by running (section 4).
* [08-step4-take-in-lean/TakeCheck.java](08-step4-take-in-lean/TakeCheck.java):
  the probe that runs `TransSeq.take` on the generated cases; how to run it
  is in its comment.
