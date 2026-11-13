028-07. Investigate: one start's sync blocks every start of the JVM
===================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: a Pub start holds the lock of the class `DatabaseImp` through
`Db.syncCreation`.

Why: a sync that waits (after an `OutOfMemoryError`, or on a slow disk)
blocks every other start and open in the JVM (`tools/jstack2.txt`).

Frans: none.

Done when: the lock is not held across the sync, or
`DatabaseBuilder.start()`'s Javadoc says that starts wait for each other.

First step: why the start holds the class lock.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-3).
