005-75. Fix: dead checks and comments that differ from the code in the Core
===========================================================================

Status: open. Kind: fix. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
the C clone's work (012-02's review, its section 15; 012-04; 012-06,
section 7; 012-09; 012-10), as 012-01's decision D5 says. None changes a byte or a
result; each misleads a reader of the code, and the C clone was written
from that code.


The findings
------------

* **`KeyNode.checkIncreasingTime` checks nothing**: it never updates its
  `time`, so each klong is compared with the first only (012-02, section
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
