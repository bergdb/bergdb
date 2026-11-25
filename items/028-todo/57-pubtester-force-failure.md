028-57. Investigate: PubTester.testNoCreatedTxtWithoutForce fails in Codex's sandbox
====================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: in Codex's review of 028-55 (2026-11-25), the first run of
`java/before-commit.sh` failed only `PubTester.testNoCreatedTxtWithoutForce`:
the force failure that the test injects came out as a
`DbFailedException`, where the test expects a `StreamIoException`. The
test alone failed so on `main` with and without 028-55's fix; a second
run of the whole gate passed. On F53 the gate passes.

Why: either the test depends on its environment (Codex's sandbox, its
file system or its order of tests), or the database wraps a failed
force differently on some path, which would be a fault of the error
handling (a caller's exception changed).

Frans: none.

Done when: the cause named, with the environment that gives it; a fix
of the test or of the database, with `java/before-commit.sh` printing
`BEFORE COMMIT OK`; an RB entry drafted if a release has a fault.

First step: `PubTester.testNoCreatedTxtWithoutForce` and the code that
injects the force failure; run the test alone, many times, and in the
gate's order.


Log
---

2026-11-25. Registered by lead-1125, from Codex's review of 028-55.
