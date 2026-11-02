005-75. Fix: dead checks and comments that differ from the code in the Core
===========================================================================

Status: done. Kind: fix. Created 2026-10-28. Closed 2026-11-02.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
the C clone's work (012-02's review, its section 15; 012-04; 012-06,
section 7; 012-09; 012-10), as 012-01's decision D5 says. The fixes leave
valid stream bytes unchanged; some change the refusal of corrupt input.
Each finding misleads a reader of the code, and the C clone was written
from that code.


The findings
------------

* **`KeyNode.checkIncreasingTime` checks nothing**: it never updates its
  `time`, so each TIME klong is compared with `Long.MIN_VALUE` (012-02, section
  15, finding 4; `KeyNode.java:1569-1583` at `404d2ee`).
* **`StoredTopNode.parse`'s "TopNode ID too large" cannot fire**: the
  ordinal, `bytesToLongLE(...) >>> 16`, is at most 2^48 − 1, which is
  `MAX_TOP_NODE_ID_VALUE` (012-06, F4; 012-02, finding 5).
* **`NodeStream.recover`'s length check is unreachable from a start**: a
  stream shorter than a meta block that is not an incomplete creation is
  refused by the first read of a meta block before it (012-02, finding
  21).
* **`RecoverableStream.append` checks the size field at the buffer's
  start, not at `offset`** (`Bytes.bytesToIntLE(buffer, 0)`,
  `RecoverableStream.java:490` at `fd8f513`; 012-09, section 6.3, F2).
  Every caller passes offset 0, so nothing differs today; with another
  offset the check refuses a right record and passes a wrong one (a probe
  showed both). Added 2026-10-28, 22:17.
* **`DbStarter.validateTransactions` checks nothing**: it never updates
  its `tpos` and `tt`, so its "non-increasing" checks compare against −1
  only (012-10, section 6.4, F1). Probe `TimesProbe` (012-10's scratch,
  outside the repository): the last record's time set back in a copy of a
  stream; without `-ea` Java starts and then reads `/k2` as null, with
  `-ea` it fails in a `KeyNode` assert. C does as Java. Added 2026-10-28,
  23:26. 012-14's corrupt-input runs (2026-10-29) found the consequence:
  one flipped bit in a record header's time field, which no checksum
  covers, makes Java's start fail with an `AssertionError` (with `-ea`) or
  another `Error` (without), and C's process abort, in 50 distinct
  variants; a two-line fix of the check, with a check that a time is at
  most `Klong.MAX_TIME`, refuses all 50 as a format error (a prototype in
  C, not applied; probes `crash-703-flip-3/` and `crash-902-flip-8/` in
  `/Users/f/fl/bench/012/14-out/probes/`).
* **`Klong`'s comments**: the format comment gives a TIME klong 58 bits,
  the code 56 (`MAX_TIME` 0x00ffffffffffffff; 012-04); `getIntType`'s
  comment says it returns 0, 1 or 2, and it returns 3 for a delete bitmap
  (012-04); the bits of the first key byte, and three more comments,
  differ from the code (012-02, finding 18).


What to do
----------

Recommended: `checkIncreasingTime` made to check (it is called on parsed
nodes, so a fix makes a corrupt node's times refused: run the gates and
StreamDigest), the two dead checks removed or kept as documentation, and
the comments corrected. The C clone keeps Java's behaviour meanwhile.


Done when
---------

Each fixed or accepted; a code change with `before-commit.sh`.


Decision and outcome
--------------------

2026-11-02. Frans requested the fix: make `checkIncreasingTime` check,
remove the two dead checks, correct the comments, run `before-commit.sh`
and StreamDigest, and commit after the gate succeeds. The remaining
findings are fixed too. By Codex:

* `KeyNode.checkIncreasingTime` advances its previous time after each
  TIME klong. Equal and decreasing times are refused by the node check,
  including startup's validation of parsed key nodes, which translates
  the failure to `StreamFormatException`.
* `DbStarter.validateTransactions` advances both the previous position
  and time, and checks every record time against `Klong.MIN_TIME` and
  `Klong.MAX_TIME`. Startup seeds the STM coverage boundary after this
  validation: before, a corrupt negative time could reach
  `KeyModSet.setFirstTime`'s assertion first. These checks run before
  replay, with assertions enabled or disabled.
* `StoredTopNode.parse`'s impossible ordinal upper-bound check and
  `NodeStream.recover`'s redundant length check are removed. The unsigned
  48-bit extraction bounds the ordinal; incomplete-creation and meta-block
  validation already handle a short stream at startup.
* `RecoverableStream.append` checks the size at the supplied offset.
  Its regression checks a valid slice with a misleading prefix, the bytes
  written, and refusal of a bad slice whose prefix holds the expected size.
* The comments now describe the 56-bit time, key-byte positions, key
  length and type values, compare-value layout, reserved node bytes,
  checksums, four-byte value-node alignment and recovery's legacy minimum
  record size. The old 58-bit design note is labelled historical.

Four regressions cover transaction position/time order, parsed key-node
times, actual restarts with eight corrupt record times, and nonzero append
offsets. All four fail with the previous production behavior and pass with
the fix, with and without `-ea` (five checks per focused run, including the
stopped-database check). Valid time-order controls pass too.

Validation uses an isolated snapshot of `c229ab2` plus this change, so it
includes the separately committed 005-74 fix. `before-commit.sh` prints
`BEFORE COMMIT OK (96 s)`: 1,086 unit tests and 78 f-tests. One compiled
StreamDigest class, run against the preserved `7f3dab4` jar and the fixed
jar, gives `DIGESTS IDENTICAL (36 of 36)`; the three modes also agree in
each of the twelve configurations. The format is unchanged. No checksum
was added to transaction times: these are range and order checks.
`level2.sh quick` also prints `LEVEL 2 OK`, including restart and crash
checks and 14 successful Lean conformance traces.

The C clone is unchanged; this entry fixes the Java Core, and no C checks
were run. Evidence is in
[75-core-checks-and-comments/](75-core-checks-and-comments/).
