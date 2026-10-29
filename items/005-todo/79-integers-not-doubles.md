005-79. Implement: integers instead of doubles in the Core's decisions
====================================================================

Status: open. Kind: implement. Created 2026-10-29.

Registered at Frans's request (2026-10-29, 15:38, in 012's conductor
session), after his question at 15:30, "Do we really need doubles in
BergDB Java? Would using integers help portability significantly?": "Yes,
add an 005 item for removing the use of doubles. It seems the right way
forward. To ensure things are deterministic for all potential programming
languages and targets. Integer operations are well-defined on all
targets." So the direction is decided: no double decides the stream's
bytes or the memory; how the take's rule becomes integers is to be chosen
(section Options). Registered only; nothing changed. Code cited at
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


Proposal
--------

* **The take**: an option above.
* **The iteration spacing**: `retainDuration / 4` (with `Long.MAX_VALUE`,
  forever, as today handled before). The same as `(long) (0.25 *
  retainDuration)` for every duration below 2^53 time units (about 28
  years at 10^7 units a second), since below that the conversion and the
  multiplication by a power of two are exact.
* **The internal fraction**: an integer in parts of 2^16 (or per mille),
  `allowed = growth * f >> 16` with a bound on growth or a 128-bit
  product. The default 0.25 is 16,384 exactly, so the default's bytes stay
  the same; other values may round by one byte. The setting at the API:
  either `setReclaimInternalFraction(double)` stays and converts once (NaN
  and values outside 0.001 to 0.90 refused, 005-73), or it takes the
  integer (an API change, in `releases/next.md`). For Frans.
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

1. Which option for the take, A, B or C, and with how many bits of
   dither and of fraction?
2. The bounds: what limits `dirtyCount`, `recordOwnBytes`, `ownBytes`,
   the distance and sd today (the record limit, 2 GB in Java; the
   distance's largest setting), and does the chosen form hold for all of
   them, or does the code clamp?
3. The internal fraction at the API: a double converted once, or an
   integer?
4. With 005-77 and 005-78 (Order below): one change of the take's and
   reclaim's bytes, or three?


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
setter accepts NaN). Each changes the bytes of the take or of reclaim;
doing 005-77's decision first, or the three together, changes the
StreamDigest and the C clone once.
