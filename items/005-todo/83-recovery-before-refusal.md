005-83. Investigate: recovery can write before refusing a corrupt size
=====================================================================

Status: moved to 014-01 on 2026-11-03. Kind: investigate. Created 2026-11-02.

The correction/format investigation now belongs to
[014-01, Stream correction at startup](../014-stream/01-correction.md).
The bug is not fixed. This file and 83-power-loss-tail retain the original
experiment, evidence and design history so existing references and the
reproducible runner continue to work.

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

Completed as an experiment on 2026-11-02; see "Power-loss tail experiment"
below. An initial design proposed truncation; Frans requested a strictly
append-only reconsideration. See "Recovery design". The replacement
protocol, implementation and release scope remain open.


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

2026-11-02. At Frans's request after discussing 005-82, ran the hole
experiment with normal forces enabled. The report and reproducible probe
are linked below. Investigation step complete; item stays open for the
recovery contract and design. No production code changes or commit.


Power-loss tail experiment
--------------------------

[Report, code and evidence](83-power-loss-tail/readme.md), sections 1 to
5. Full run on `3ad171d`, with the same structured results on `0e61856`:
56 controls recover and remain usable; all 56 hole images fail the
readable-prefix oracle (112 checks, two reading orders). Every admissible
image preserves all already-forced bytes and names. Of the 112 checks,
68 refuse at startup and 44 open but fail later reads or history checks.
Eight deliberately lost-acknowledgement controls are detected.

The larger case opens with a damaged value before an intact later meta
block. An ordinary read fails the instance; `getTrans` leaves it active
and another write is accepted. This supplies crash-generated evidence
for 005-82, while showing why its small error-handler fix is not a
recovery fix. The original 012-14 refused-start fixture also reproduces:
1,057,153 bytes appended before `Bad lastByte` refuses startup.

The report's section 4 recommended designing bounded suffix validation.
That design is now proposed below; no production format has changed.


Recovery design
---------------

2026-11-02, reconsideration at Frans's request: [strictly append-only
recovery](83-power-loss-tail/append-only-reconsideration.md), sections 1–5.
Truncation is not fundamentally necessary. Leave rejected bytes in place,
append a recovery checkpoint selecting the validated state, then continue
at new physical positions. The truncation preference below is withdrawn.
Checkpoint discovery/publication, accepted-history iteration, repeated
recovery crashes and bounded startup/reclaim need a replacement design;
the initial checks do not establish that protocol. No production change.

[Proposal](83-power-loss-tail/design.md), sections 1–9. At Frans's request,
designed whole-record and meta integrity, an enforced 8 MB physical write
window, a forced scan anchor protected through reclaim, consecutive prefix
validation and exclusive startup suffix removal. The anchor protection
uses the complete durable transaction frontier, not partially forced
bytes of an unfinished record. Startup reconstructs a read-only prefix
before modifying storage or exposing the database.

The proposed new format is 155 / record 6, with SHA-256 integrity. This
is a proposal, not an adopted or implemented format. Initial scope is
plaintext main file storage. Legacy failed slots need separate handling;
existing Salsa20 encryption cannot safely reuse trimmed positions, and
replica reconciliation remains separate. These limits and the required
Java/C implementation, crash, conformance and performance checks are
explicit in sections 7–8.

The item-local model checks the proposed framing, prefix rule, anchor
inequalities and file-removal order: 84,560 conditions pass, including
negative controls. It does not implement production recovery, filesystem
persistence or the existing Lean model. See section 9 and its recorded
output. No production code changed and no commit was made for this design.

2026-11-02. Design step complete. Item remains open for the recovery
contract, format/scope decision and implementation; 005-82 remains a
separate live-read fix.
