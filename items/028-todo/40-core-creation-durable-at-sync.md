028-40. Fix: the Core API's creation is durable only at its first sync, not said in its Javadoc
================================================================================================

Status: done. Kind: Fix. Frans: decided (2026-11-20).
Created 2026-11-20 by Frans Lundberg.

What: a database made by the Core API's creating start (`Db.start()` on a
new stream) is durable only at its first sync: the start does not sync
its records (`Db.startInner`'s comment; only the Pub API's path, with
`created.txt`, syncs both). A crash after `start()` returned, before a
sync, can leave the first record alone, and the next start throws
`DatabaseNotCreatedException`. The Javadoc of `Db.start()` (its `@throws
DatabaseNotCreatedException`) and of `DatabaseNotCreatedException` speak
of "a creation that did not complete", which a reader takes to mean a
crash inside the start. Found by 028-35 (KillEmpty, a halt of the JVM
right after a creating `start()` left no stream file at all).

Why: the Javadoc must say what the code does (027-04); a user of the Core
API who relies on a returned `start()` as durable loses the database. If
release 2026.5 behaves the same and its Javadoc says the same, it is a
released bug by 033's definition.

Frans: none.

Done when: the Javadoc of `Db.start()`, `DatabaseNotCreatedException` and,
if it names the case, `DbBuilder` say that the Core's creation is durable
at the first sync, and what a user does (sync after the start, or use the
Pub API); release 2026.5's behaviour and Javadoc checked at its tag, and
an RB entry in 033 if it is a released bug (or the reason it is not);
`java/before-commit.sh` BEFORE COMMIT OK.

First step: `Db.startInner`'s comment on the creation's sync and 028-35's
findings.


Result
------

Frans decided (2026-11-20): the Javadoc only; it is to say clearly that a
Core user calls sync after start() for a new database to survive a
restart; a minor released bug, the unclear API documentation.

* `Db.start()`'s Javadoc: a paragraph on the creation's durability (the
  first sync after the start; `sync(SyncLevel.ORDINARY)` after `start()`;
  with `DbBuilder.createdTxt(File)` the start syncs it itself), and its
  `@throws DatabaseNotCreatedException` names the crash after the start
  returned.
* `DatabaseNotCreatedException`'s Javadoc: the Pub API against the Core
  API, and what a Core user does.
* Release 2026.5: the same behaviour (its start syncs the creation only
  with `created.txt`, `syncCreation`) and the same Javadoc: RB-003 in 033,
  S4.


Log
---

2026-11-20. Registered by coord-1120, from 028-35's report.
2026-11-20. Done by coord-1120: the Javadoc; RB-003. Moved to Closed.
