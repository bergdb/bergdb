007-03. Plan: bounded startup for BergDB itself
================================================

Created 2026-10-24 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request ("Do: write this plan into item 007."), from Claude's proposal
of 2026-10-23, which followed 007-01 and 007-02.

**Status: step 1 done (005-31, 2026-10-24); steps 2 to 5 not started, and
after release 2026.1 (Frans, 2026-10-25: "After the release").**
Step 1, 005-31, had Frans's go for its option A (2026-10-24: "005-31, it
has my 'go'. But don't start the implementation now."), and then his
request to fix it ("fix all todo items of type Fix"). Step 3, the deadline,
is decided too (D1, Frans, 2026-10-24: "As you propose."): d_h = 2 × sd, a
constant factor.


The goal
--------

T3 bounds the startup section for a policy that keeps up with the startup
distance (007-01, section 3). BergDB's take does not keep up (007-01, 4.1),
and one large transaction can stop it for good (005-31). The goal: bounded
startup that holds for BergDB itself, proved for BergDB's own policy. In
the words a user should be able to rely on:

    Startup reruns the transactions of less than 2 × sd of records, and
    the last transaction, whatever the size and the age of the database,
    where sd is the startup distance. At the default of 50 MB, that is
    about X s on F53.

X comes from step 5. Not in this plan: T4, a bound on D (007-01, section
6), which bounds the two records at the ends of the section and the memory
that D pins; and the startup distance as an estimated time instead of bytes
(007-01, D3).


The steps
---------

### Step 1. Fix 005-31 (option A, decided)

Refuse, before the go point, a transaction whose got-dirty index nodes
could not be written in one record: a cheap test for every transaction, and
the precise count, under the write lock, only for the rare large ones
([005-31](../005-todo/31-fix-take-blocked.md), "The fix, options", A).

* Why first: with it, the nodes of every transaction fit in one record,
  which the deadline of step 3 needs. Without it, no policy can bound
  startup.
* First: 005-31's first step, comparing the precise count with the bytes
  the nodes take when written, on 007-02's probe and on a large load of new
  keys.
* Done when: as 005-31 says (a unit test with the record limit lowered,
  `before-commit.sh`, StreamDigest identical, the docs).
* Size: S.
* Done 2026-10-24, by Claude (Opus 5.5, Claude Code); see 005-31's
  outcome. The bound is at 15/16 of the record limit, so a transaction's
  nodes fit in the record of a later transaction whose own part is below
  1/16 of the limit. For step 3: "one transaction always fits in a record"
  holds for such records; a record whose values take nearly 7/8 of the
  limit (005-17) leaves less, and the take then waits for a smaller one. A
  dirty limit of 1/8 of the record limit would make it hold for every
  record, at the price of refusing eight times smaller updates; for Frans
  to decide if step 3 or 4 needs it.

### Step 2. A test that drives the debt up

A stress test, in `java/stress/` with LoadTest's setup, that makes the debt
of D large compared with the startup distance (007-01, 4.2), run on
today's take first. Three workloads:

* A load of n keys, then single puts spread uniformly over them, for
  several n and startup distances. The measured 10M keys at 20 MB (2.21 d)
  is such a run, and likely overshoots for this reason: the first updates'
  records have many got-dirty ids and few index nodes, as the take is
  still writing the load's nodes, which are cheap; so the debt piles up
  until the take reaches them.
* The startup distance lowered at runtime (`Db.setStartupDistance`, for
  example from 50 MB to 5 MB), which leaves the take a long section's debt
  to pay.
* Deletes of existing keys spread over the keys: small records, each with
  a key path's worth of got-dirty ids.

After every transaction, it records the section without its last record,
the record's size, D in nodes, and the debt: the stream size of D's nodes
plus 16 bytes each, as `TransSeq.recordBytes` counts them.

* Done when: for each workload, the largest section over d, the largest
  record, and the debt over d, on today's take; 007-01's hypothesis (the
  section reaches the larger of d and the debt, plus at most 0.25 d)
  confirmed or rejected; the outputs in this item's directory. The same
  runs again after step 3.
* Size: S, and runs in the background. They count bytes and nodes, not
  time, so a busy machine does not matter.

### Step 3. The deadline in `TransSeq.take` (D1, decided)

The take ignores its node limit for transactions that begin more than d_h
before the end of the stream; d_h is 2 × the startup distance, a constant
factor, so no new setting. In `take()`'s loop, one more way to go on:

    first.tpos <= maxSp
        && (nodeCount < nodeCountLimit || transCount < 2 || first.tpos <= hardSp)

where `hardSp` is the stream length minus d_h. The record limit stays: after
step 1 one transaction always fits in a record, so a take that lags passes
at least one transaction per record.

* Streams change only where the take lagged more than d_h: tests with small
  startup distances, runs like the 10M one. StreamDigest on the standard
  sets says which, and each change needs its reason.
* The price, to measure with step 2: the largest record the deadline makes,
  which writes the debt beyond d_h, and that commit's latency.
* `Db.setStartupDistance`'s Javadoc warns that a large decrease "can cause
  a large transaction to run". Today the node limit spreads the work; with
  the deadline, the next transaction writes the debt beyond d_h at once.
  Update the Javadoc.
* `take()`'s comment: its "TODO D." of 2015, which asks for a factor on the
  node limit when the startup pos falls behind by more than 2 × sd (D1's
  origin), goes with the change, and so does the claim that the startup
  pos "should never fall exceedingly behind" (007-01, 4.1). Noted
  2026-10-25 (006-05, T7).
* Done when: in step 2's runs, the section without its last record stays
  below d_h; `before-commit.sh`; `level2.sh`, since the take is Level 2's
  mechanism; `level3.sh` and `level4.sh` if their streams change; the quick
  performance suite unchanged; docs/levels.md, Level 2, "Bounds", updated.
* Size: S for the code, M with the gates and runs.

### Step 4. BergDB's take in Lean

BergDB's take becomes a policy of the model, in the trusted part
(`lean/SIS/Bound.lean`): from s(i-1) + 1 on, whole transactions while they
begin at least sd before the end of the stream, and fewer than two have
been taken, or their got-dirty ids are below the limit, or they begin at
least d_h before the end. The limit is a function of T(i), which the
policy may see (M10 of docs/level2-alignment.md). BoundExample.lean's
sketch, `javaTake`, becomes this definition.

* The proof: every transaction up to the target of d_h passes the loop's
  test, since the cost to the end only shrinks along the stream and
  d_h ≥ sd. So the policy keeps up with d_h (`KeepsUp`), and T3 holds for
  runs with BergDB's take, with d = d_h.
* The record limit is left out of the model. Java's take is the model's as
  long as the record limit does not stop it, which after step 1 takes the
  transactions due at once to need more than one record, about 2 GB of
  index nodes. The theorem's comment says so.
* Done when: the theorem (`T3_take`, say) proved, with `#guard`s on
  example 2: the take with the deadline keeps the section below d_h, and
  with a tight limit and no deadline it does not; `lake build` with no
  warnings and no `sorry`; lean/README.md and docs/sis-model.md, section
  10, updated.
* Size: S to M.

Later, not in this plan: the trace checker compares Java's startup pos
with this policy on every record. It needs each record's length in bytes
in the traces (a trace format change, in Java's exporter and in `Check/`),
and Java's positions also count the meta blocks, 128 bytes every 200 kB,
which the model's cost of a record does not.

### Step 5. Startup time

Startup time against the section on F53: sections of 5 to 100 MB, values of
10 bytes to 10 kB, a warm OS file cache; and a cold one on s1, where root
can drop the caches (F53 has no passwordless sudo). Besides the time, count
what startup does: the bytes it reads in order, the transactions it reruns,
its first touches (random reads); fit time ≈ a × bytes + b × transactions
+ c × touches.

* Done when: the table, the fitted constants, and the numbers for the
  promise: the default (50 MB, so d_h = 100 MB) with small and large values,
  warm and cold.
* Size: S, in the background with the session idle, and not while another
  timing run is on.


Order
-----

1, 2 and 3 in that order: the deadline needs 005-31, and step 2 shows the
take before and after it. Step 4 can go beside 2 and 3, once D1 has fixed
the deadline's rule, which it must match. Step 5 after 3, as it measures
the startup that the deadline bounds.

D1 is decided (the deadline at 2 × sd), so all five steps stand.


Decisions
---------

* 005-31, option A: decided, go (Frans, 2026-10-24); done (2026-10-24).
* D1 of 007-01: the deadline, with d_h = 2 × sd as a constant factor:
  decided (Frans, 2026-10-24, "As you propose."); not started.
* D3 of 007-01, bytes or estimated time: not needed for this plan.
* Steps 2 to 5 before or after release 2026.1 (item 008): after (Frans,
  2026-10-25, "After the release"). The release ships with the take as it
  is, and says so: README.md, and docs/levels.md, "Bounds, measured".


After the plan
--------------

* T4 (007-01, section 6): a bound on D, for the exact still-dirty test
  first. It bounds the records at the ends of the section and the memory
  that D pins.
* The trace checker's comparison of the startup pos (after step 4).
* The promise in the user documentation: the Pub API's startup distance,
  and docs/levels.md.


How to work
-----------

Several sessions work in the bergdb tree at once: Java and Lean changes are
made and gated in a scratch clone, and copied into the main tree last, with
the gates run again on the combined tree. Frans commits, or the session he
asks to; no session commits on its own.
