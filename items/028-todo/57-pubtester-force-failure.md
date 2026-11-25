028-57. Investigate: PubTester.testNoCreatedTxtWithoutForce fails in Codex's sandbox
====================================================================================

Status: done: a fault of the test, not of the database; the test
fixed. Kind: Investigate. Frans: none.
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


Result
------

Investigated 2026-11-25 by Codex (GPT-6.1 Sol, reasoning effort max) on
F53, at `c041ac79`, at lead-1125's request.

* **Cause: the test's timing.** The test arms a force failure before
  `start()` of a new database with `testSetup`'s 100,000-byte buffer
  and its 10 ms timer. The storage's consumer may flush the primordial
  record while the start goes on (`BufferedStream.flushToStream`,
  `FileStream`'s new file, its force): the failure is then recorded by
  the storage manager, and the start's later steps, after it has set
  the database `ACTIVE` (the startup distance's KV read and put,
  reclaim's reads), find failed storage and throw `DbFailedException`.
  When the creation's own sync meets the failure first, it throws
  `StreamIoException`. Both close the failed start and leave no
  `created.txt`; both are allowed by 010-01, P7 and the Javadoc of
  `Db`'s errors and `start()`.
* **Evidence.** The test alone in 100 fresh JVMs: 27 passed, 73
  failed (16 in the startup's reads, 16 in `execute`'s state check, 41
  in the creation's transaction); in the gate's order, after the JVM
  has warmed up, it passes (a loop of 1,000 in one JVM: 996 passed).
  A probe forcing each order gave each exception, `created.txt` absent
  and the database closed in both. Release 2026.6 has the same test and
  paths, and the same two outcomes: no released bug (033's rules leave
  out tests).
* **Fix.** The test takes either exception and checks that the cause
  at the bottom is its injected force failure (`BufferedStream.read`
  may copy the message without the cause, so the message is compared).
  Alone in 100 fresh JVMs, 100 passed; 1,000 in one JVM, all passed.
  `java/before-commit.sh` on `main` (`09a814f0`) with the fix: `BEFORE
  COMMIT OK (203 s)`, 1,752 unit tests, 89 f-tests.


Log
---

2026-11-25. Registered by lead-1125, from Codex's review of 028-55.

2026-11-25. Investigated by Codex at lead-1125's request: the test's
timing, not a fault of the database; the test fixed to take either
exception. Done.
