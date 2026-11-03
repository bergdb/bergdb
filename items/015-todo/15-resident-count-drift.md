015-15. Fix: a batch subtracts values never counted, and a count driven to 0 stays 0
====================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2. Found by review R1 (016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F4, with a probe.

What: a value that the writer puts into a key node is not counted.
A capacity controller's batch (`Eviction.unswizzleValues`) takes every
written value of a pinned key node and `Residents.valueOut` subtracts
each, the uncounted ones too, down to 0; `grown` and `valueIn` skip a
count of 0 (the sign of "not counted"), so the node stays counted 0 while
it is resident. The resident bytes stay below the real ones, and the
database uses more memory than its budget: in the probe, `resident bytes
1033517, exact 1299038`; with a startup distance of 50 MB, 968 against
72,726 after 50 transactions. The object counter drifts too. New since
2026.1 (whose sweeps made the count exact by walks).

Done when: "counted" is kept apart from the size, so that an object whose
count reached 0 is counted again at its write and by `valueIn`; a value
the writer puts into a counted object is counted, or `valueOut` stops at
the holder's own size; the object counter does not drift; a unit test of
the probe's steps (the leaf's count equals `bytesOf` after its write, the
resident bytes equal an exact walk); `BEFORE COMMIT OK`. Whether D's dirty
nodes are counted between their writes stays as Residents' design says,
and docs/levels.md, section 7 says it, if "exact" is not kept.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
