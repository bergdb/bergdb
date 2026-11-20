028-40. Fix: the Core API's creation is durable only at its first sync, not said in its Javadoc
================================================================================================

Status: open. Kind: Fix. Frans: none.
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


Log
---

2026-11-20. Registered by coord-1120, from 028-35's report.
