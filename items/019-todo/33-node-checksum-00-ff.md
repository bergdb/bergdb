019-33. Decide: a node byte changed between 0x00 and 0xff passes the node checksum
==================================================================================

Status: done (decided 2026-11-06: outside the fault model for 2026.3,
option (a)). Kind: Decide. Frans: decision.
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

Frans: a decision; he chose (a), 2026-11-06, 10:42 (the log).

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

2026-11-06, 10:42. Frans decided 019-30, 019-31 and 019-33 together, to
coord-1106, which asked for each as recommended: "Yes, as recommended.
BergDB assumes correct storage. Which makes sense. Ensure this is
documented in the relevant Javadoc comments. However, use of checksums
in the stream is also a reasonable design. Going in that direction is
definitely not for 2026.3. Remember the target: bug-free Core. Move the
possibility of checksums in the stream to a new item in 017. This may or
may not be added in some future release." Option (a): a node byte
changed between 0x00 and 0xff is outside the fault model for 2026.3, as
015-73. Option (b), a stronger node checksum, is part 3 of 017-08,
checksums in the stream: not for 2026.3, and it may or may not come in a
future release.

2026-11-06. Done by agent d4 of coord-1106, option (a); nothing in the
Core changed. Harness 6.1 (018-07): a node byte flipped by 0xff is
marked known ("019-33") when the copy is made, and an undetected one is
counted as "known 019-33: undetected" (1,016 in the full set of seed
20398, 1,132 in seed 20399's); its line left `CorruptStreamTester.SKIP`.
`releases/next.md`'s known limit names the kind. BEFORE COMMIT OK; the
runs are in 019-30's log.
