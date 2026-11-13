028-12. Investigate: can the take's byte limit stop the startup section's bound?
================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: `TransSeq.take` stops at the first transaction whose taken nodes
do not fit in `maxBytes`, the room left in the record, also after the
deadline (its Javadoc: "It matters for records near the record limit
only"). Today's Lean (prover "t44", 007, `SIS/BoundTakeBytes.lean`,
checkpoint 183c2ec7) proves T3's bound for this take when the debt's
nodes always fit (`T3_takeB`: nodeB·|D| ≤ maxB before every
transaction), and refutes it without that, by two runs checked by
running (`BoundTakeBytesExample`): a transaction whose nodes never fit
is never taken, so the span grows by a record each time; and even when
each fits, a costly record leaves cheap ones queued behind the limit,
and the span reaches 103 against 2M = 6.

Why: bounded startup (007, Frans's top priority since 2026-10-23) rests
on T3: the startup section stays below 2 sd. If the byte limit can hold
the take back in Java, the section is not bounded. 005-31 (007-02) fixed
the case of a single transaction that never fits; the second case is
new.

Frans: none; the answer is: whether Java's runs can reach it (the room
left in a record against the bytes of D's nodes, at 1M to 100M keys and
the record limit), and if they can, a proposal.

Done when: a measurement or an argument from the code that says whether
`bytes + cost > maxBytes` stops a take past the deadline in Java's runs
(007-06's debt test drives the debt up; its runs or a probe give the
numbers), written here with the numbers; if it can, a proposal (for
example: past the deadline, take at least one transaction, or bound D's
bytes) for Frans.

First step: read `TransSeq.take`, where `maxBytes` comes from
(`StoredTrans.recordLimit`, the record's own bytes), and 007-06's
largest debt in bytes.


Log
---

2026-11-13. Registered by coord-1113, from prover t44's target D (007).
