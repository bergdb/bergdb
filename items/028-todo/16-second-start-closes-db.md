028-16. Fix: a refused second start of one Db closes the database the first started
==================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-16 by Frans Lundberg.

What: `DatabaseImp.createAndStart(Db)` (package-private) closes the `Db`
in its catch when `db.start()` refuses it. If it is called twice on one
`Db`, `Db.start()` refuses the second call (`IllegalDbStateException`),
and that call's catch closes the database that the first call started,
against `Db.start()`'s Javadoc ("nothing is closed then"). Since 028-07
the close can also come while the first call's index manager starts.

Why: only BergDB's own tests can make the two calls; the Pub API builds a
new `Db` for each start (`DatabaseBuilderImp`). Low priority, but the code
and the Javadoc disagree.

Done when: a refused call closes nothing that another call started (for
example, the catch closes the `Db` only when this call's `db.start()`
began the start), with a test of two calls on one `Db`; or the Javadoc
says what happens. `java/before-commit.sh` prints BEFORE COMMIT OK.

Source: 028-07, section "what the lock guarded" (two `createAndStart()`
calls on one `Db`).


Log
---

2026-11-16. Registered by coord-1116, from 028-07.
