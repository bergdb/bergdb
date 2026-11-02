005-83. Investigate: recovery can write before refusing a corrupt size
=====================================================================

Status: open. Kind: investigate. Created 2026-11-02.

Split from 005-74 when Frans selected its option A, the size checks.
Found in 012-14, section 6.6, which records the probe and its result.


The issue
---------

A flipped record-size field can make a complete record look torn and
longer. Recovery zero-fills it, and startup then refuses the stream with
`Bad lastByte`. The recorded probe added about 1 MB before refusing. Java
and C behave alike. 005-40 prevents writes when the meta blocks are
unreadable; it does not cover this case.

The size checks of 005-74's option A run after recovery. They cannot by
themselves prevent recovery's writes. A genuine torn record also names
bytes beyond the current stream; simply rejecting every such size would
break crash recovery.


First step
----------

Reproduce 012-14's refused-start-writes case and identify which invalid
framing can be recognized before zero fill, using only the bounded tail
read by recovery. Establish which damaged-size cases cannot be told from
a genuine torn write with the current format. Propose the resulting
recovery contract and its tests before choosing a change.


Done when
---------

The distinction and its limits are established, a remedy or explicit
contract is decided, and any implementation has corrupt-input regressions
plus the crash and restart checks of Level 2. Java and C are considered
together where recovery behavior changes.


Log
---

2026-11-02. Split from 005-74 during its option A implementation. Open;
neither recovery policy nor the stream format changes in 005-74.
