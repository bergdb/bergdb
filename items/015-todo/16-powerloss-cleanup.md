015-16. Investigate: PowerLossTest failed once in its cleanup, "cannot delete test file"
========================================================================================

Status: open. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

For release 2026.2, if it is a fault of BergDB.

What: in 016-08's F3 (the stress programs with fresh seeds, on F53, main
at `323a54a`), `PowerLossTest 111010062 2 1500 3` failed after 1 s:
`java.io.IOException: cannot delete test file
/var/folders/.../bergdb-power-recovery-.../00000000000024.bergdb` at
`FileStreamPowerLossTester.remove` (679), from `verify` (558) and
`runTrace` (638). Rerun three times by the coordinator at 16:52: POWERLOSS
OK each time. F3 ran five JVMs beside other agents' gates.

Questions: did a thread of BergDB (the cut's delete thread, a
BufferedStream) still run after the database's close and delete or hold
the file, against "close() waits" (005-35); or did the tester's cleanup
race with something of its own? `File.delete()` returns false also when
the file is already gone.

Done when: the cause is known; a fault of BergDB is fixed with a test, a
fault of the tester is fixed or noted.

First step: read `remove` and what `verify` closed before it, and the
threads a FileStream database starts and how close() waits for them.

Found 2026-11-03 by 016-08's F3 (`/Users/f/fl/bench/016/h4-stress/f3/`).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
