005-83. Recovery with strictly append-only storage
=================================================

2026-11-02. Reconsideration requested by Frans. This supersedes the
recommendation to truncate the tail in 005-83, initial recovery design,
sections 5–8. It establishes an append-only direction and its requirements,
not a completed replacement protocol. No production change or commit.


1. Answer and correction
-------------------------

Truncation is not fundamentally necessary. A damaged suffix can be
excluded from the logical database while its physical bytes remain.
Append new recovery metadata selecting the validated earlier state,
then append future transactions at fresh positions beyond the physical
EOF. The storage operations remain reads, appends and durability barriers.
No old byte is overwritten or removed; no position is reused.

The original proposal's exclusive startup trim was an explicit exception
to AppendOnlyStream, not a solution within that interface. Preferring it
for simplicity gave insufficient weight to BergDB's storage abstraction.
Withdraw that preference. Investigate an append-only recovery checkpoint
before adding a special truncation capability.

The distinction is between a consecutive prefix of accepted transactions
selected during recovery and a contiguous range of all physical bytes.
The former is necessary for transaction consistency. The latter need not
remain true after a crash and append-only repair.


2. Concrete shape
------------------

Suppose A and B are good, C is damaged, and D survives but may depend on C.
The physical stream after repair and a new transaction N can be:

    A | B | damaged C | D | recovery checkpoint R | N

The logical history is A, B, N. R selects the state after B, excludes the
physical interval after B up to R, and establishes where normal records
resume. It never accepts D merely because D's own checksum is valid.

A recovery checkpoint needs integrity over at least its type/version,
stream identity, own position, last accepted transaction position/time,
accepted prefix end, restart/root information, excluded interval and
resumption position. It also needs a reference to earlier recovery state
when previous repairs exist. These are design fields, not a frozen layout.
A recovery epoch or explicit predecessor links can express the same idea.

First validate/reconstruct the accepted state read-only. Establish the
durability of that state and any recovery-index dependencies, append the
checkpoint, and force it before accepting new user writes. A crash before
completion leaves the old data available and an incomplete repair attempt;
a crash after completion leaves a durable description of the selected
state. Repeat recovery must be idempotent in logical effect, even though
failed attempts consume additional physical space.

A valid checkpoint must have a trustworthy publication protocol. An intact
marker after a hole is not sufficient evidence that its dependencies are
valid: that was precisely the experiment's counterexample. Checksums,
validation and force ordering must work together. Nor does forcing the
abandoned bytes turn them into valid transactions.


3. Required format and reader changes
--------------------------------------

Merely appending a normal record after garbage is insufficient. Current
forward iteration still encounters the broken framing first. The new
format must make recovery checkpoints discoverable without trusting the
size of the damaged record, for example at reserved fixed block positions.
Do not resynchronize by accepting arbitrary plausible bytes in a value.

Startup replay, transaction iteration, historical lookups, direct getTrans
and reclaim must agree about the accepted record chain and excluded ranges.
Discarded transactions must not reappear through an iterator or stale meta
block. A known recovery gap is different from an unexplained corrupt record
in the accepted history; ordinary read corruption still fails the instance.

Meta blocks or an append-only checkpoint/index structure must carry enough
recovery state for later startups. A list of every past gap reconstructed
from the beginning would lose bounded startup. Keeping the right checkpoint,
its dependencies and accepted-history references through reclaim needs a
new argument. In particular, the initial design's inference from forced
bytes to ordinary valid framing no longer holds inside sealed gaps.

Repeated crashes while writing padding, a checkpoint or its index are
mandatory cases. An unbounded succession of partial repair attempts cannot
simply be assumed to fit inside the original 8 MB window. The replacement
must establish its discovery/work bound, or explicitly state its limit;
the initial truncation model and its 84,560 checks do not establish it.


4. Tradeoffs and scope
----------------------

Append-only recovery preserves existing positions and avoids the specific
Salsa20 keystream-reuse problem caused by truncating and reusing offsets.
This is not an encryption correctness result: encrypted framing, checkpoint
discovery, partial blocks and durability ordering still require checks.
Similarly, it does not resolve replica winner selection.

Abandoned bytes consume space. If front reclaim is supported, they can
leave with a later safe prefix cut once no accepted history or recovery
metadata needs them. With storage that never permits deletion at all,
those bytes remain permanently, like every other obsolete byte.

Clean restarts should still append nothing. Recovery after actual damage
can append control records, and future physical positions then depend on
the abandoned region. Do not promise the byte identity of a truncation
approach for that case, or relabel accepted-but-lost transactions as refused.
Any extension of P2 to damaged-stream recovery needs an explicit contract.

Truncation remains an alternative if the format must keep the invariant
that all physical record bytes belong to one continuous valid history.
It would require a startup storage exception, supported providers and a
separate encryption solution. That is an engineering choice, not a
fundamental requirement of crash recovery.


5. Next design work and external comparison
--------------------------------------------

Replace the trim step with an append-only recovery checkpoint. Specify its
location, publication, accepted-chain semantics and retained checkpoint
state; then model crashes before and inside every repair write/force,
including repeated interruptions and reclaim. Keep full record integrity
and validation of a consistent transaction prefix from the initial design.
Do not carry over its storage/work bounds without proving them again.

For an example of the broader design family, Couchstore documents an
append-only file with newly appended headers, root pointers and headers
located on fixed block boundaries; opening searches for a valid header.
See its [primary format description](https://github.com/couchbase/couchstore/blob/master/file_format.md),
“How A File Is Written” and “File Header”. That is evidence that appended
state-selection metadata is a practical format technique, not a proof
that its header rule alone handles BergDB's tested hole images or meets
BergDB's startup bound.
