015-07. Fix: a node's inner fields are not checked, and a read that meets one does not fail the database
========================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2 (016-01, section 6, the rule for findings: verified,
no format or API change).

What: the node parsers do not check their inner fields against the node's
size: `StoredKeyNode`'s key count, `StoredValueNode`'s value and key
sizes, and `StoredTopNode`'s pointer count (only by an assert). A node
whose Fletcher-16 checksum is right but whose field is wrong (a corrupt
stream, or a fault in a writer) gives an `ArrayIndexOutOfBoundsException`
or a `NegativeArraySizeException` in a load (`NodeStream.readNode`).
`Db.getOneInternal`, `getMany` and the reads before a transaction's go
point catch only `StreamException`, so the exception escapes to the
caller and the database stays active.

Why: docs/levels.md, section 3: a read that fails fails the database. A
database that goes on after such a read may write on a wrong view.

Verified: a probe in 005-82's work (its Log, 2026-11-03), on the clone's
jar: `getOne`, `getMany` and a put each threw
`ArrayIndexOutOfBoundsException`, and a later put was taken.

Done when: each parser checks its fields against the node's size and
throws `StreamFormatException` (as 005-74 did for the record and node
sizes), and the reads fail the database with that cause; a test per
parser that fails before the fix; `BEFORE COMMIT OK`.

First step: 005-82's probe as tests in `DbTesterFailure`.

Found 2026-11-03 by the work on 005-82 (016-05).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
