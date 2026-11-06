019-33. Decide: a node byte changed between 0x00 and 0xff passes the node checksum
==================================================================================

Status: waiting. Kind: Decide. Frans: decision.
Created 2026-11-06 by Frans Lundberg.

What: `NodeChecksum` is Fletcher-16, its sums modulo 255, so a byte of
0x00 and one of 0xff add the same: a node byte changed from one to the
other leaves the checksum right, and the node is taken. Where the byte is
a value's, a read returns another value with no error; where it is a
field, the node may mean something else.

Found by harness 6.1 (018-07), in the night 006-12, a byte flipped (xor
0xff) in a node, sample seed 2:

```text
all, flip, xor 255 at 2564 (record at 2216, offset 348: node at offset 176 of size 180,
  its byte 172): undetected: at time 90, /k6 is null, not 142 bytes
take, flip, xor 255 at 17141 (record at 16888, offset 253: node at offset 120 of size
  448, its byte 133): undetected: the counter at time 310 is null, not 31
```

Why: damage other than a cut tail is outside the crash contract, and its
detection is best effort (018-01, section 6.1; 014-01, section 7). This
one is the checksum's own blind spot, a property of Fletcher-16 modulo
255 (all bits of a byte set or cleared at once, as a torn or zeroed
sector may do), not a missing check.

Frans: a decision.

* **(a) Outside the fault model for 2026.3**, as 015-73: the harness
  counts such a copy as known to pass undetected. Nothing changes.
* **(b) A stronger node checksum** (Fletcher-16 modulo 256, or a CRC) at
  the next change of the node format, with 019-07's header checksum: a
  change of the stream format, which needs Frans's approval (018-01,
  section 2), and the C clone (012) with it.

Recommendation: (a) for 2026.3, and (b) considered with 019-07 when the
format next changes.

Done when: Frans has chosen; for (a), the harness's skip list line
"019-33" becomes a `KNOWN` line (018-07, section 4).

First step: Frans's decision.


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-33" in `CorruptStreamTester.SKIP`.
