015-16. Investigate: PowerLossTest failed once in its cleanup, "cannot delete test file"
========================================================================================

Status: done. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

For release 2026.2, if it is a fault of BergDB.

What: in 016-08's F3 (the stress programs with fresh seeds, on F53, main
at `c8e2f1e`), `PowerLossTest 111010062 2 1500 3` failed after 1 s:
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


State
-----

2026-11-03, 19:45: done. Not a fault of BergDB: the tester removed its
directory right after `stop()`, while the close, and the cut's deletes,
still ran in the background (005-35). The tester now calls `close()`,
which waits. Committed after the combined gate.

Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:07 to 17:26, by agent J (016-05), in
`/Users/f/fl/bench/016/015-16/repo` from `c12af6e`: the cause, the
interleaving and the probes, as follows.

1. `db.stop()` in `verify()`'s finally returns at once; `Db-close-N`
   waits in `FileStream.close`'s `awaitCutThread`.
2. `remove` lists a file F, and `F.exists()` is true.
3. The cut's thread (`FileStream-cut`, a cut that the first database
   decided and the second start made) unlinks F.
4. `F.delete()` returns false: "cannot delete test file F".

Probes in `/Users/f/fl/bench/016/015-16/probe/`: `PowerCleanupProbe`
(seeds 111010062 and 63, 110 verifies): with `stop()`, `Db-close` alive
at `remove` 98 times, `FileStream-cut` once; with `close()`, 0 and 0.
`PowerCleanupForce` holds the cut's first delete on a latch: `stop()`
gives `remove`'s exact `IOException`; `close()` returns after the
delete, in 312 ms, and `remove` works. The images depend on the flush
timing, so a rerun of the seed need not repeat it.

2026-11-03, 19:45, by the coordinator: the fix, J's next step:
`close()` in place of `stop()` in `FileStreamPowerLossTester`'s
`verify()` (its finally) and `runTrace` (the trace's database before its
images are verified, and its finally); `remove()` stays strict. Not
changed, a doubt: `manager.stop()` before `remove(dir)` in two other
tests of the same tester (`StorageManager.stop()` also closes in the
background); no failure of them is on record. Gated with 015-09 on
`main` at `b1651a5`.
