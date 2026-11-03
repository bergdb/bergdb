005-79. Implement: integers instead of doubles in the Core's decisions
====================================================================

Status: open, planned for release 2026.2 (016-01, section 4.1, item 2;
"Plan for 2026.2" below); nothing implemented yet. Kind: implement.
Created 2026-10-29.

Registered at Frans's request (2026-10-29, 15:38, in 012's conductor
session), after his question at 15:30, "Do we really need doubles in
BergDB Java? Would using integers help portability significantly?": "Yes,
add an 005 item for removing the use of doubles. It seems the right way
forward. To ensure things are deterministic for all potential programming
languages and targets. Integer operations are well-defined on all
targets." So the direction is decided: no double decides the stream's
bytes or the memory. Frans's decisions on the questions follow below
(section Decision, 15:48): option B for the take, an integer for the
internal fraction's setter, and this entry on its own. Registered only;
nothing changed; not to be implemented until Frans says so. Code cited at
`82626eb`.


The issue
---------

The stream's bytes are a function of the transactions and the settings
(010-01, P2), and a port must give the same bytes (item 012). Four
computations in the Core use `double`; three decide the bytes (012-01,
3.2, point 4), one the memory:

| Where | Expression | Decides |
|---|---|---|
| `TransSeq.take` (005-49, 007-03 step 3, 007-07: `f89846d`) | `share = (double) dirtyCount * recordOwnBytes / ownBytes * (streamLength - currentSp) / startupDistance`; `u = dither(streamLength)`, SplitMix64's finalizer, its top 53 bits times 2^-53; a transaction before the deadline stops the take if `taken + count > share && share - taken <= u * count` | which transactions' dirty nodes a record takes: the bytes |
| `Reclaim.transactionCompleted` | `t.tt - lastTStart() >= (long) (ITERATION_SPACING * retainDuration)`, `ITERATION_SPACING = 0.25` | when an iteration starts: the bytes |
| `Reclaim.transactionCompleted` | `allowed = (long) (internalFraction * (streamSize - current.pStart)) - rewritten`; `internalFraction` 0.25 by default, set by `Db.setReclaimInternalFraction(double)` and JMX (0.001 to 0.90; NaN passes the check, 005-73) | how much a step may rewrite: the bytes |
| `Eviction.setBudget` and its constructor | `low = (long) (budget * LOW)`, `LOW = 0.75` | the low watermark: what stays in memory |

The other doubles in `java/src` decide nothing that is stored or kept:
statistics and their getters (`Db.getDirtyFraction100` and `1000`, JMX's
getters, `StorageManager`'s progress percentage, `StartupInfo`'s
duration), the Pub API's `Duration.seconds(double)` (a user's input,
turned into a long once), and the Pub API's indexes on double values (the
user's data, stored as their bits).

**What doubles cost a port.** The C clone gives Java's results with IEEE
binary64, the operations in Java's order, no fused multiply-add
(`-ffp-contract=off`, and a unit test, `jsem_no_fma`, that fails if one is
made), and Java's saturating conversion to long (`j_d2l`, 012-01, 6.2);
012-17 had to show that link-time optimization keeps all of it. No
difference was met, but each new language or target has its own traps:
Go fuses `x*y+z` on arm64 unless told not to; old 32-bit x86 compilers
compute in 80-bit registers; on some microcontroller compilers, such as
avr-gcc, `double` is 32 bits by default; `-ffast-math` reorders; a
Cortex-M0+ has no FPU and a Cortex-M4F only single precision, so doubles
come from a software library (exact for `+ - * /`, slower, a few kB). With
integers, a port needs only 64-bit integer arithmetic with wrapping, which
the Core needs anyway (klongs, hashes) and every target has.

**The Lean model.** `SIS/Bound.lean` has the take's share and dither as
Lean's `Float` (`share`, `dither`, `javaPace`, `javaTake`), checked
against Java bit for bit by `#guard`s and TakeCheck; no theorem uses them,
since T3 holds for any pace (`lean/README.md`). With integers the pace
itself could be reasoned about, for example how far a record can exceed
its share (up to 30 percent with 005-49's first dither, 007-03 step 3).


Options for the take
--------------------

The other three are simple (Proposal). The take's rule compares ratios
of longs; three ways to make it integers:

**A. The same rule, exact.** With `N = dirtyCount * recordOwnBytes *
(streamLength - currentSp)` and `M = ownBytes * startupDistance`, the
share is N / M; `taken + count > share` is `(taken + count) * M > N`, and
with the dither as an integer h of k bits, `share - taken <= u * count`
is `(N - taken * M) * 2^k <= h * count * M`. The products need more than
64 bits: N alone can pass 2^100 within the format's limits (a record
below 2 GB, a distance of terabytes), and the dither's test adds k
bits, so k = 53 is out of reach of 128 bits; it needs k of about 16 and a
128-bit multiply and compare (Java: `Math.multiplyHigh`, Java 9; the
unsigned one is Java 18, beyond BergDB's `--release 17`; C:
`unsigned __int128`, or a 64 by 64 to 128 helper on 32-bit targets).
The decisions are those of exact arithmetic; they differ from today's
only where today's rounding decided, plus the dither's fewer bits.

**B. Fixed point.** The share computed once per take in units of 2^-16
of a dirty node, `shareFp = floor(N * 2^16 / M)`, with one 128-bit
product and a 128 by 64 division (written out; Java has none built in),
the dither's top 16 bits as `uFp`; then the loop in 64-bit integers:
`((taken + count) << 16) > shareFp && shareFp - (taken << 16) <= uFp *
count`. Cheaper in the loop than A, one rounding (at the share), and its
bounds are simpler to state.

**C. A new pace, defined in integers.** The share's factors reordered
or bounded so that every product stays below 2^63 without 128 bits (for
example the share in dirty nodes, `dirtyCount * recordOwnBytes / ownBytes`
first, then scaled by `distance / sd` capped, which 005-77's cap of S/sd
would give), with the dither as an integer threshold. The simplest code,
but a new rule: 007-03's and 007-07's measurements of the pace (records
within their share, the catch-up after a decrease) are to be made again.

All three change the take's choices in some records, so the stream's
bytes for the same transactions differ from today's: a one-time change,
like 005-49's and 007-07's. The format stays; every existing database
opens and continues, since the take's state is not stored (a start
rebuilds the startup section). Recommended: B, as the smallest change
with bounds that can be written beside the code; C if 005-77 changes the
share anyway (see Order).


Decision
--------

Frans, 2026-10-29, 15:48: "B for the take. setReclaimInternalFraction()
should take an integer. Not together, create a new entry. But make a note
about the others that you mention. Do not implement this now, just create
the entry." So:

1. **The take: option B**, fixed point. The number of bits (16 proposed,
   for the share's fraction and for the dither) is for the first step,
   with question 2's bounds.
2. **`setReclaimInternalFraction` takes an integer**: an API change, in
   `Db`, JMX and the C clone's `bergdb_set_reclaim_internal_fraction`,
   noted in `releases/next.md`; the unit (parts of 2^16, or per mille) is
   for the first step. The NaN that the double setter accepts (005-73)
   goes with it.
3. **Not together** with 005-77 and 005-78: this entry changes the bytes
   on its own, and so do they. Notes in both (and in 005-73) point here,
   so that whichever comes later builds on the one before.
4. **Not now**: registered only.


Proposal
--------

* **The take**: option B (Decision).
* **The iteration spacing**: `retainDuration / 4` (with `Long.MAX_VALUE`,
  forever, as today handled before). The same as `(long) (0.25 *
  retainDuration)` for every duration below 2^53 time units (about 28
  years at 10^7 units a second), since below that the conversion and the
  multiplication by a power of two are exact.
* **The internal fraction**: an integer in parts of 2^16 (or per mille),
  `allowed = growth * f >> 16` with a bound on growth or a 128-bit
  product. The default 0.25 is 16,384 exactly, so the default's bytes stay
  the same; other values may round by one byte. The setter takes the
  integer (Decision, 2), its range the same as today's 0.001 to 0.90.
* **The low watermark**: floor(3 * budget / 4) without overflow, `budget
  / 4 * 3 + budget % 4 * 3 / 4`, the same as `(long) (budget * 0.75)` for
  every budget below 2^53 bytes.
* **A rule and its check**: 010-01, P2 (or a principle of its own) says
  that every decision that changes the stream's bytes or the memory is
  made with integers; a step of `java/before-commit.sh` refuses `double`
  and `float` in the Core Layer's packages (`java/deps.py --layer core`'s
  list) outside a list of allowed statistics methods, and C's `rules`
  step the same in `src/`.


Questions
---------

1. The take is option B (Decision). With how many bits of dither and of
   fraction?
2. The bounds: what limits `dirtyCount`, `recordOwnBytes`, `ownBytes`,
   the distance and sd today (the record limit, 2 GB in Java; the
   distance's largest setting), and does the chosen form hold for all of
   them, or does the code clamp?
3. The internal fraction's setter takes an integer (Decision). Its unit,
   parts of 2^16 or per mille?
4. Decided: on its own, not with 005-77 or 005-78.


Done when
---------

1. No double or float decides the stream's bytes or the memory in Java's
   Core: the four places use integers, with the bounds that keep them
   from overflowing written beside them.
2. The check of the rule passes in `java/before-commit.sh` and in C's
   gate, and fails on a planted double.
3. StreamDigest: identical for the spacing, the default fraction and the
   watermark (shown, not assumed); for the take, the records whose take
   differs counted on its workloads, and the pace measured as in 007-03
   step 3 (records within their share).
4. The C clone follows (`transseq.c`, `reclaim.c`, `evict.c`; 012's code,
   by hand, as C is a separate project): `cross.sh full
   C=build/release` passes; `jsem.h`'s double helpers kept only where
   the API converts.
5. Lean: `share`, `dither` and `javaPace` in `Nat` or `Int`, the
   `#guard`s and TakeCheck against Java's new take.
6. The four gates; `releases/next.md` if the API changes; 010-01's P2.


First step
----------

Question 2's bounds, from the code and the limits it enforces; then
option B prototyped in `TransSeq.take` in a clone, against today's on
StreamDigest's workloads and 007-03's pace runs: how many records take
differently, and whether records stay within their share.


Size and order
--------------

M: reclaim and eviction a few lines each; the take a day with its tests
and measurements; C in hours; Lean an hour or two. Related: 005-77 (a cap
of the pace's factor S/sd, the same expression), 005-78 (the retain
duration into the stream, the same iteration rule), 005-73 (the fraction
setter accepts NaN). Each changes the bytes of the take or of reclaim,
and each is done on its own (Decision, 3): the StreamDigest and the C
clone change with each. If 005-77 caps S/sd first, B's share is computed
from the capped factor; if this entry comes first, 005-77's cap is
written in B's integers.


Decisions of 2026-11-03
-----------------------

* **D3 of 016-01** (Frans, 2026-11-03, 15:01): "005-79, yes implement this
  internally. The Pub API can use doubles at the interface, then
  immediately convert to integers (int, long) internally."
  * This replaces decision 2 of 2026-10-29 (an integer setter).
    `Db.setReclaimInternalFraction(double)` and JMX's
    `setReclaimInternalFraction(double)` keep their double, convert it to
    an `int` at once, and keep 005-73's checks: NaN, and values outside
    0.001 to 0.90, are refused, and the setting stays as it was.
  * No double decides the stream's bytes or the memory (016-01, section 3).
* **Java only** (Frans, 15:31): "The C code does not need to be updated
  for 2026.2 in this work. Only Java code will be included in the release.
  It is not a requirement to update the Lean code either. If this is
  needed to develop Java or to ensure it works well, then do it. See it as
  a tool, not an output artifact for the release."
  * This replaces "Done when" 4 (the C clone) and 5 (Lean) for 2026.2.
  * C follows after the release (the plan, step 9). Lean is a tool here
    (step 8, optional).
* **Tonight** (Frans, 15:40): "try your best to finish this work by 07:00
  tomorrow in the morning ... instead of in three days or so. Note, you
  only need before-commit.sh to be successful to commit your work."
  * One agent does steps 1 to 5 from about 16:50, in four to five hours
    with the tests. Another agent reviews (about 30 minutes). The
    coordinator commits before about 01:30.
  * The commit gate is `java/before-commit.sh`. The level scripts of the
    mechanisms run if they fit.
* **The format stays** (016-01, section 3): the take writes other bytes
  within the format, once. This is recorded: StreamDigest's new digests in
  this entry, and the notes (step 5).


Plan for 2026.2
---------------

### 1. Settled by reading the code

At `6d81050` (`java/` as at `df6ad50`).

**The bounds (question 2).** The take's inputs, and what bounds them:

| Value | Type | Bound | Where |
|---|---|---|---|
| sd, the setting | int | 10 to 2^31 - 1; 5 to 1000 MB in the Pub API | `DbBuilder.startupDistance` |
| o, the record's own bytes | long | 48 to 48 + `valueLimit()`, below 2^31 | `TransSeq.ownBytes`, `StoredTrans` |
| O, the section's own bytes | long | above 0 when D has a transaction (an assert); at most S | `TransSeq.add` |
| D, the section's got-dirty nodes | long | none in the code | `TransSeq.add` |
| S, `streamLength - currentSp` | long | none in the code; the deadline keeps it near max(2 sd, span) | `take` |
| count, one transaction's nodes | int | below 2^31 | `TransInfo.gotDirtyNodes` |
| taken | long | at most D | `take` |

So the code clamps where nothing bounds: the take checks D < 2^32 and
S < 2^47 (128 TB) itself. Beyond them the share is all of D, so the pace
takes every transaction before the deadline, as the deadline does after it.
Neither limit is reached with sd below 2^31 unless the record limit holds
transactions back for a very long time. `T3_take` holds for every pace
(007-08), so the clamp cannot break the bound.

**The take, option B, with 16 bits (question 1).** The share in units of
2^-16 of a node, computed once per take:

    p       = D * o                      below 2^63, as D < 2^32 and o < 2^31
    q       = S << 16                    below 2^63, as S < 2^47
    X       = p * q                      128 bits: Math.multiplyHigh and the low product
    Q       = floor(floor(X / O) / sd)   two divisions of 128 by 64 bits
    shareFp = min(Q, D << 16)            D << 16 if D >= 2^32 or S >= 2^47
    uFp     = h >>> 48                   h: SplitMix64's finalizer, as dither() has it

Before the deadline, the loop stops at a transaction if
`((taken + count) << 16) > shareFp && shareFp - (taken << 16) <= uFp * count`.

* One rounding, as B asks: floor(floor(X / O) / sd) is floor(X / (O sd))
  for positive integers, so shareFp = floor(D o S 2^16 / (O sd)).
* uFp is floor(u 2^16) exactly, since today's u is (h >>> 11) 2^-53.
* The min changes no decision: taken + count is at most D, so the first
  test is false at D << 16 as at any larger Q.
* No overflow in the loop: taken << 16 is below 2^48, (taken + count) << 16
  below 2^49, and uFp * count below 2^47.
* `Math.multiplyHigh` (Java 9) gives the unsigned high part for operands
  that are not negative. The division of 128 by 64 bits is written out:
  first the high word by the divisor, then Hacker's Delight's `divlu`
  (2nd edition, section 9-4) on the remainder and the low word, with
  `Long.divideUnsigned`. A 64-step shift and subtract is the plainer
  alternative, if the review prefers it.
* Why 16 bits:
  * the pace takes its share on average up to 2^-16 of a transaction per
    record, which is nothing next to one transaction;
  * 32 bits do not fit this scheme: q = S << 32 needs S < 2^31, and S
    reaches 2 sd, up to 2^32;
  * the internal fraction uses the same unit, so the Core has one fixed
    point, 2^-16.
* `TransSeq.testShare`'s dithers become `ditherFp(1300) = 26583` and
  `ditherFp(1200) = 65167` (0.4056 and 0.9944 today). With a share of 25
  nodes the test's decisions stay the same.

**The internal fraction's unit: parts of 2^16 (question 3).**

* The default 0.25 is 16,384 exactly, so the default's bytes stay.
* The conversion at the API is exact up to one rounding:
  `(int) Math.round(f * 65536)`. A product with a power of two is exact in
  binary64, so only `Math.round` (half up) rounds, as in every language.
  Per mille's `f * 1000` rounds in the product first.
* 005-73's range 0.001 to 0.90 becomes 66 to 58,982 (65.536 and 58,982.4
  rounded). Every value in it is within the range. At the low end, 2^-16
  is finer than per mille, whose 1, 2 and 3 are steps of 100 and 50
  percent.
* The getter returns `units / 65536.0`, which is exact.
* The allowance: `allowed = (g >>> 16) * f + (((g & 0xFFFF) * f) >>> 16) -
  rewritten`, with g = `streamSize - pStart`. This is floor(g f / 2^16),
  exact for every g below 2^63, since f < 2^16.
* A fraction that is set gives the nearest multiple of 2^-16: 0.1 becomes
  6,554 (0.100006). A step's allowance then differs by a few bytes per MB
  of growth. Only JMX, `Db`, and ReclaimCost's property set it;
  StreamDigest does not.
* For 005-78's question 9: kept in the stream, it is 2 bytes or a short
  field.

**The iteration spacing.** `retainDuration / 4`, after the test for
forever, as today. It is the same as `(long) (0.25 * retainDuration)` for
every duration below 2^53 time units (28.5 years at 10^7 units a second):
there the conversion to double is exact, and so is the product by 0.25.

**The low watermark.** `budget / 4 * 3 + budget % 4 * 3 / 4`, which is
floor(3 budget / 4), without overflow; `Long.MAX_VALUE` stays
`Long.MAX_VALUE`.

* It is the same as `(long) (budget * 0.75)` for every budget below
  2^53 / 3, about 3 * 10^15 bytes, where budget and 3 budget / 4 are exact
  doubles.
* A correction to the Proposal, which said "below 2^53": between 2^53 / 3
  and 2^53, the double product can round up past the next integer.

**The other doubles in the Core.** The attachment
[doubles-scan.txt](79-integers-not-doubles/doubles-scan.txt) lists every
one in the production code of the Core Layer's packages.

* Three more decide memory: the growth of `KeyAccessPath`'s arrays,
  `(int) (size * 1.6)`, and two buffers of `StoredTrans`,
  `(int) (keyCount * 1.20)` and `(long) (totalSize * 1.20)`. These are
  array sizes, not bytes.
  * They become `size + size * 3 / 5`, `keyCount + keyCount / 5` and
    `totalSize + totalSize / 5`: the exact floors, which the doubles give,
    or miss by one where 1.20's double, a little below 1.2, puts the
    product just below an integer.
* The rest are the API, statistics, formatting, the users' values as their
  bits, randomness, test data and the test framework. They go into the
  check's allowed list (step 4).

### 2. The steps

| Step | What | Who | Size | Gate or check |
|---|---|---|---|---|
| 0 | The clone, the status | coordinator | 5 min | the base commit recorded |
| 1 | The baseline: digests and pace | agent | 20 min | the files below exist |
| 2 | Part A: spacing, fraction, watermark, buffers | agent | 1 h | `before-commit.sh`; digests identical |
| 3 | Part B: the take in fixed point | agent | 2.5 h | `before-commit.sh`; tests; digests explained |
| 4 | The check against doubles | agent | 1 h | `before-commit.sh` fails on a planted double |
| 5 | The words: notes, P2, Javadoc | agent | 30 min | read by the reviewer |
| 6 | The review (016-01, H5) | another agent | 30 min | findings answered here |
| 7 | Gates and commits | coordinator | 30 min | `BEFORE COMMIT OK` on the combined tree |
| 8 | Lean as a tool (optional) | agent | 1 to 2 h | `lake build`, no `sorry`, no new axiom |
| 9 | C follows (after 2026.2) | later | hours | C's gate and `cross.sh full` |

Steps 1 to 5 run in one clone, in order, by one agent. Steps 2 and 3 are
two parts, so that A can be committed without B (section 3).

**Step 0. The coordinator.**

* `git clone /Users/f/fl/repos/bergdb /Users/f/fl/bench/016/005-79`, and
  the base commit into this entry's State.
* 005-79's row in 005's table: "in progress".
* At most one heavy run at a time (013-02). StreamDigest and the probes
  are deterministic, and are not timed.

**Step 1. The baseline** (the agent; 20 minutes; files: this directory).

* `java/build.sh` in the clone. Copy `java/build/bergdb.jar` and
  `java/build/stress/` to `/Users/f/fl/bench/016/005-79-base/`: the
  preserved build, whose compiled StreamDigest runs against every jar
  (StreamDigest's header).
* `java -cp $BASE/bergdb.jar:$BASE/stress bergdb.core.StreamDigest all >
  digest-base.txt`, in the background, with the output in this directory.
* 007-07's ShareProbe
  (`items/007-bounds/07-step3-paced-take/ShareProbe.java`), compiled
  against the base jar, at `-Dsd=800000` and `-Dsd=2000000`, with
  `-Dkeys=2000 -Dvsize=1000`, as in 007-07, section 2: `share-base.txt`.

**Step 2. Part A: the bytes stay** (the agent; 1 hour).

* Files:
  * `java/src/bergdb/core/Reclaim.java`:
    * the spacing, `retainDuration / ITERATION_DIVISOR`, with
      `ITERATION_DIVISOR = 4` in place of `ITERATION_SPACING`;
    * the fraction, an `int` in units of 2^-16:
      `DEFAULT_INTERNAL_FRACTION = 16384`, and `setInternalFraction(int)`,
      which refuses values outside 66 to 58,982;
      `getInternalFraction()` returns the units;
    * the allowance through a helper, `fractionOf(g, f)`.
  * `java/src/bergdb/core/Db.java`: `setReclaimInternalFraction(double)`
    checks as today, then calls `reclaim.setInternalFraction((int)
    Math.round(f * 65536))`; `getInternalFraction()` returns
    `units / 65536.0`. `Jmx.java` goes through `Db`, unchanged.
  * `java/src/bergdb/core/Eviction.java`: `lowOf(budget)` in the
    constructor and in `setBudget`; `LOW` goes.
  * `java/src/bergdb/dag/KeyAccessPath.java` and
    `java/src/bergdb/core/StoredTrans.java`: the three sizes in integers.
* Tests:
  * `DbTester.testReclaimInternalFractionValidation`: 0.001, 0.90 and 0.25
    give the units 66, 58,982 and 16,384, and the getter gives the units
    over 65,536.0. The refused values stay as they are.
  * New: `fractionOf` and `lowOf` against `BigInteger`'s floor, on the
    edges (0, 2^16 - 1, 2^47, 2^53 / 3, 2^63 - 2) and on random values.
* "Shown, not assumed" (Done when 3): `Equiv.java` in this directory,
  package `bergdb.core`, against the clone's jar. It compares the old
  double expressions with the new methods, on the edges and on 10^8
  random values, for:
  * the spacing below 2^53;
  * the watermark below 2^53 / 3;
  * the default fraction below 2^53;
  * and it prints the first differences above those bounds.

  The output goes to `equiv.txt`.
* The gate:
  * `java/before-commit.sh` prints `BEFORE COMMIT OK`;
  * StreamDigest all, the base's compiled copy against the new jar, and
    `compare digest-base.txt digest-a.txt` prints `DIGESTS IDENTICAL`;
  * if it fits: `java/stress/level3.sh` (reclaim, 5 minutes).
    `level4.sh` (16 minutes) only if the night has room, as `equiv.txt`
    shows the watermark the same.
* The handover: a note "Part A" in this entry, with the files and the
  results, and a message to the coordinator with the file list.

**Step 3. Part B: the take** (the agent; 2.5 hours).

* Files: `java/src/bergdb/core/TransSeq.java`:
  * `take()` as in section 1;
  * `ditherFp(long pos)`, an `int` from 0 to 65,535, in place of
    `dither`;
  * `shareFp(D, o, O, S, sd)`, package-private and static;
  * the 128-bit helpers, private and static in `TransSeq`, its only user;
  * the Javadoc of `take()`: the share's paragraph in integers, with the
    bounds of section 1 (Done when 1).
* Tests (`@Nano`, the unit group):
  * `testShareFpExact`: `shareFp` against `BigInteger`'s floor, clamped at
    D << 16, on 10^5 cases from SplitMix64 spread over the bit lengths (D
    to 2^32 - 1, o to 2^31 - 1, S to 2^47 - 1, O from 1 to S + 1, sd from
    10 to 2^31 - 1), and on the edges: each bound at its largest, O = 1,
    sd = 10, o = 0, D = 0;
  * `testShareFpClamp`: D = 2^32, or S = 2^47, gives D << 16;
  * `testShare`: the dithers as integers (26,583 and 65,167), and the same
    decisions;
  * the other take tests, in `TransSeq` and `DbTester` (some calibrated
    with 007-07's TakeProbe), unchanged. A number that changes is
    explained by the comparison below: which decision differs, and why.
* The comparison (in the clone only; not handed over):
  `compare-take.diff` in this directory. It computes the double decision
  beside the integer one at each test of the loop, counts the takes where
  any test differs, and prints the counts at the end of each StreamDigest
  configuration. Its output is `compare.txt`.
* StreamDigest all on the new jar: `digest-b.txt`, and a summary as
  007-07's `digest-summary.txt` (`digest-summary.txt`). It gives each
  configuration's lengths, whether its digest differs from the base, and
  whether its three modes agree.
* ShareProbe on the new jar, as in step 1: `share-b.txt`.
* The gate:
  * `java/before-commit.sh` prints `BEFORE COMMIT OK`;
  * in every configuration, plain, reads and restarts give the same
    stream (P2);
  * a configuration differs from the base exactly when `compare.txt`
    counts a differing take in it;
  * ShareProbe's written nodes per commit, share and section over sd are
    the base's, to two decimals;
  * if it fits: `java/stress/level2.sh`, the take's level (17 minutes).
    Its RestartInvariance and its conformance with the model (steps 4 and
    7) run the new take.

**Step 4. The check** (the agent; 1 hour; written while StreamDigest runs).

* Files:
  * `java/doubles.py`, new;
  * `java/deps.py`: its last line becomes
    `if __name__ == "__main__": sys.exit(main())`, so that `doubles.py`
    can import it, and `test_regions` gets a parameter `helpers=True`;
  * `java/before-commit.sh`: a step after deps.py, `python3 -I doubles.py >
    $LOG/doubles.txt`, failing as "doubles in the Core's production code
    outside the allowed list"; a line `Doubles: ...`; its header comment.
* `doubles.py` calls `test_regions` with `helpers=False`. deps.py's helper
  rule counts `TransSeq.take` and `dither` as test code, since in their own
  file only tests call them. That is found by this plan's scan; for deps.py
  it does no harm, as its lists cover test code too.
* What it refuses, in the production code of the packages that
  `deps.py --layer core --list` prints (computed at each run, not written
  in):
  * the words `double`, `float`, `Double` and `Float`;
  * floating literals: a decimal number with a point, an exponent or a
    `d` or `f` suffix, and a hexadecimal one with a `p` exponent;
  * calls that take or return floating point with no such word: the
    methods of `Math` and `StrictMath` on doubles (`sqrt`, `pow`, `log`,
    `exp`, `floor`, `ceil`, `rint`, `round`, `random`, `signum` and the
    rest, listed in the script), and `nextDouble`, `nextFloat`,
    `nextGaussian`, `doubleValue`, `floatValue`, `parseDouble`,
    `parseFloat`;
  * the names of the allowed list's methods used outside it, so that an
    allowed getter cannot feed a decision.
* The allowed list, in the script, with a reason for each entry:

  | File | Where | Why |
  |---|---|---|
  | `core/Db.java` | `setReclaimInternalFraction`, `getInternalFraction` | the API, converts at once |
  | `core/Jmx.java` | the file | JMX: setters through `Db`, statistics |
  | `common/Bytes.java` | float and double to and from bytes | the users' values, as bits |
  | `common/StringUtil.java` | `oneDecimal`, `twoDecimals`, `wholeNumber` | text of statistics |
  | `common/SeedGenerator.java` | `addRandomOffset` | randomness for ids and keys |
  | `core/KeyFactory.java` | the file | keys for tests and src-dev's programs |
  | `core/NodeCollection.java` | the `LinkedHashMap`'s load factor | a JDK parameter |
  | `storage/StorageManager.java` | the progress percentage | statistics of a copy |
  | `nanotest/` | the package | the test framework |

* Its self-test, at every run, before the scan. It checks itself on
  snippets that it carries, and fails if one is judged wrong:
  * a double in a production method is found;
  * one in a `@Nano` method is not;
  * `Math.sqrt(n)` is found;
  * `0x7f` is not;
  * `1e-9` and `0.75f` are found;
  * a production use of an allowed method's name is found.
* By hand, once:
  * on the base, before steps 2 and 3 (`git stash` in the clone), it lists
    exactly the four decisions and the three sizes;
  * a planted `double x = 0.5;` in `TransSeq.take` makes
    `before-commit.sh` print `BEFORE COMMIT FAILED` with the line.

  Both go into this entry (Done when 2).

**Step 5. The words** (the agent; 30 minutes).

* `releases/next.md`:
  * The take and reclaim decide with integers (005-79, the date).
  * The take's choices differ in some records from the double rule of
    2026-10-28. So the same transactions give other bytes, once, and the
    format is the same.
  * StreamDigest's digests change in N of 12 configurations, named. The
    digests of 2026.2 are the new reference (016-01, W7).
  * The fraction's setter keeps its double and uses the nearest multiple
    of 2^-16 (0.25 exactly).
  * The spacing and the watermark give what they gave, for retain
    durations below 28 years and budgets below 3 PB.
* 010-01, P2, "Where BergDB stands": a point that the Core decides in
  integers since 005-79, that `java/doubles.py` checks it in
  `before-commit.sh`, and Frans's words of D3.
* `docs/levels.md`, section 5: the names `ITERATION_SPACING` and
  `internalFraction` as the code now has them.
* `lean/README.md`, if step 8 is not done: one sentence where it says that
  `javaTake` gives the result of Java's take. It now gives the double rule
  of 2026-10-28, which Java used until 005-79.
* The Javadoc of `Db.setReclaimInternalFraction` and of JMX's setter: the
  unit and the rounding.

**Step 6. The review** (another agent, xhigh as Q3 says; 30 minutes per
part).

* It gets this entry (Decisions, Proposal, the plan), the diff, the tests,
  and `equiv.txt`, `compare.txt` and `digest-summary.txt`.
* What it checks:
  * the bounds and the clamp;
  * the 128-bit arithmetic, against the `BigInteger` tests;
  * the loop's overflow;
  * the conversion's rounding and range;
  * the check's patterns and its allowed list;
  * whether the tests would fail on a wrong rule.
* Its findings are answered in this entry.

**Step 7. The commits** (the coordinator).

* Commit A after its review: "Integers for reclaim's spacing and fraction
  and eviction's watermark (005-79)".
* Commit B: "Integers in the take's share and dither, and a check against
  doubles in the Core (005-79)".
* Each one:
  * `java/before-commit.sh` on the combined tree prints
    `BEFORE COMMIT OK`;
  * `java/` and `lean/` in `main` are what was gated (016-01, section 3);
  * staged by path list, in Frans's name.
* `level2.sh` on B if it fits before 01:30.
* 005's table: done when B is committed, with step 9 registered in 015 as
  its own entry. That closing is the coordinator's choice.

**Step 8. Lean as a tool** (optional; an agent who is free; 1 to 2 hours).

* `SIS/Bound.lean`'s `share`, `dither` and `javaPace` in `Nat`, as
  section 1 has them.
* A new TakeCheck in this directory, from 007-08's, which prints `shareFp`
  and `ditherFp` and the 300 cases' takes from the new jar.
* `SIS/BoundExample.lean`'s `#guard`s from its output.
* The gate: `lake build` with no `sorry`, and lean/README.md's
  `#print axioms` with no new axiom.
* Why: it is a second implementation of the take, in integers without
  bounds, checked against Java on 300 cases. That is the check the C clone
  would have given.
* A Lean gotcha: in `Nat`, `sh - taken * 65536` stops at 0. The test keeps
  its truth value, since its right side is never negative.
* Not a gate of the release.

**Step 9. C follows** (after 2026.2; a 015 entry; D6 and Frans's 15:31).

* `transseq.c`: `ts_share`, `ts_dither` and the loop as Java's. It uses
  `unsigned __int128` on 64-bit targets, and a helper for 64 by 64 to 128
  bits elsewhere.
* `reclaim.c`: the spacing, and the fraction in units of 2^-16.
* `evict.c`: `EV_LOW`.
* `api.c` and `db.c`: the setter keeps its double and converts.
* `jsem.h`'s double helpers stay only for that and for the users' values
  (`bytes.c`).
* C's `rules` step refuses double in `src/` outside a list of the same
  kind.
* `cross.sh full C=build/release` passes again. Until then it fails
  wherever the take differs, as C keeps the double rule.

### 3. Order, parallel work, the night

* One agent does steps 1 to 5. Another reviews. Step 8 is optional, and
  step 9 comes later.
* 005-78's study and probe run beside it, in their own clone. They read
  `Reclaim` and do not depend on these changes; the fraction's unit is
  settled above.
* The night, after 016-02:

  | Time | What |
  |---|---|
  | 16:50 | steps 0 and 1 |
  | 17:10 | step 2 |
  | 18:10 | A handed over; its review; commit A |
  | 18:15 | step 3 |
  | 20:45 | step 4 |
  | 21:30 | step 5; B handed over at about 21:50 |
  | 22:20 | B's review; the gate; commit B, about 23:00 |
  | 01:30 | the latest commit of the release |

* **The fallback.** If B is not reviewed and gated by 00:30, A alone goes
  into the release.
  * The take keeps its doubles, and the notes say so.
  * B is finished after the release, and its bytes change in 2026.3.
  * A does not depend on B.

### 4. What the byte change moves

* **StreamDigest**: `digest-base.txt`, `digest-a.txt` (identical to the
  base) and `digest-b.txt`, with `digest-summary.txt`, in this directory.
  The reference of the release is W7's: 2026.2's digests in its
  `baseline.zip`.
* **Unit tests with exact numbers**: changed only with an explanation
  (step 3).
* **Lean**: TakeCheck's 300 numbers and `BoundExample.lean`'s bits are of
  the double rule.
  * They stay true of Lean's `Float` functions, but no longer of Java's
    take.
  * Step 8 brings them back, or step 5's sentence says so.
* **The trace conformance of level2.sh to level4.sh** follows by itself.
  The checker takes each record's sp from the trace (`REC` lines,
  docs/trace-format.md), and T3 holds for every pace. So the traces of
  the new take need no change in Lean. Level 2's step 7 shows it when it
  runs.
* **The C clone's cross tests** fail until step 9.
* **007-07's measurements** are history; ShareProbe's rerun shows the
  pace as it was.

### 5. State

* **Done** (2026-11-03, before 16:50):
  * this plan;
  * the scan of the doubles,
    [doubles-scan.txt](79-integers-not-doubles/doubles-scan.txt).
* **The base** for the work is `main` at the start (`6d81050`, with
  `java/` and `lean/` as at `df6ad50`).
* **Progress** (the implementer, in the clone `/Users/f/fl/bench/016/005-79`):
  * 15:54. Step 0 done (the clone at `6d81050`). Step 1 done: the base
    build preserved in `/Users/f/fl/bench/016/005-79-base/` (`bergdb.jar`,
    `stress/`, `probe/` with ShareProbe); `digest-base.txt` (StreamDigest
    all, 7 s) and `share-base.txt` (sd 800 kB: E[w] 0.92, E[share] 0.92,
    S/sd 1.001; sd 2 MB: 0.52, 0.52, 1.008) in this directory.
* **Next**: step 2, Part A.
* **For the implementer**:
  * The Java files have trailing whitespace, which the Edit and Write
    tools drop. Edit them with exact strings, and compare with `diff -w`.
  * Every test stops its databases (try-with-resources, `testSetup()`).
  * A probe in `bergdb.core` goes before `build/bergdb.jar` on `-cp`.
  * `before-commit.sh` must not be edited while it runs; edit the clone's
    copy.
  * Record the outcome of each step in this State, with the times, so
    that a fresh agent can resume.


Log
---

2026-10-29. Registered, with Frans's decisions of 15:48 (above).

2026-11-03.
* Frans decided D3 of 016-01: before the release, with doubles at the API
  only.
* The plan for 2026.2 added, with
  [doubles-scan.txt](79-integers-not-doubles/doubles-scan.txt).
* Frans's changes of 15:31 (Java only; Lean as a tool) and 15:40 (tonight;
  `before-commit.sh` the only gate) are in "Decisions of 2026-11-03".
