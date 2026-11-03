005-82. Fix: parsing corrupt transaction data must fail the database
==================================================================

Status: open. Kind: fix. Created 2026-11-02.

Split from 005-74 when Frans selected its option A, the size checks.
Found in 012-14, section 6.7; the finding and its probe remain there.


The issue
---------

`Db.getTrans` catches storage and format errors from `TransIterator.next`,
but calls `getStoredTrans` outside that `try`. A node checksum failure in
the latter escapes as `StreamChecksumException` and leaves the database
active. A parser bounds exception can escape too. This contradicts the
read-failure contract of levels.md, section 3, and 005-34.

005-74's option A checks sizes before allocations and bounds parsing by
the declared record. It does not move the parse into the failure handler.
The C API already fails the database on a parsing error (012-03).


Proposed fix
------------

Parse inside `getTrans`'s storage-failure handling. Refuse malformed
records with a format error, retaining its cause when the database fails.
Keep invalid caller positions and expired reads as their existing errors.


Done when
---------

Regressions corrupt a node checksum in an otherwise readable transaction
and exercise a malformed record. Each read fails the database; later reads
and writes are refused with the first failure as cause. Valid, expired and
invalid-position cases retain their behavior. `before-commit.sh` passes.


Log
---

2026-11-02. Split from 005-74 during its option A implementation. The
checksum finding remains open; no production change for it in 005-74.

2026-11-02. Frans asked to distinguish expected incomplete crash tails
from unexpected corruption before implementing this change. 005-83,
"Power-loss tail experiment", now supplies the evidence: the `lazy`
case opens with damaged unforced data before an intact later meta block.
An ordinary read fails the instance; `getTrans` reports the parsing
error, stays active and accepts another write. Its section 4 recommends
deciding the startup recovery contract first. Making live-read error
handling consistent would not by itself make the damaged tail recover.
This item remains open; its implementation and that policy decision have
not been carried out.
