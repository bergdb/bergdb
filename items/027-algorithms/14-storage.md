# 027-14. Storage and durability

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 10 of 027's outline (027-04, section 2.3; levels: all). Below the
Core: the append-only stream's contract; `FileStream`'s files and forces;
`BufferedStream`'s chunks and group commit; the meta blocks; what
`sync()`, `stop()` and `close()` promise; the physical cut's deletes; the
crash contract (a prefix of what was appended); per-append forcing turned
off; no replication, copies left to the OS.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
