015-17. Investigate: a read during close fails with "File closed", and close reports it
=======================================================================================

Status: open. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

For release 2026.2, if it is a fault.

What: in 016-08's F3 (F53, main at `323a54a`), `InterruptStress` failed
after 485 s of a 600 s run: "a worker failed", `StreamIoException: File
closed, .../00000000022200.bergdb` at `Db.close` (1307), from a worker's
close (`InterruptStress$1.once`, 167); its cause, the `IOException` "File
closed" at `FileStream$DbFile.reopenChannel` (1254), from a read of
another worker's get (`InterruptStress$2.once`, 186: `DbUtil.get`,
`Db.getOne`, `NodeCollection.followValuePointer`, `NodeStream.readNode`,
`RecoverableStream.read`, `StorageManager.read`, `BufferedStream.read`,
`FileStream.read`). So a get that ran while the database closed read a
file that the close had closed; the read failed as an I/O failure, and
the close reported it. InterruptStress takes no seed (its interleavings
come from timing), so a rerun need not repeat it.

Questions: what does BergDB promise for a get that runs while another
thread closes the database (Db.close's and the Pub API's Javadoc;
005-46, 005-55, 005-63)? Should the get get a "closed" refusal, and the
close not fail? Is the read's failure recorded as the database's
failure, and does a later start see anything of it (it should not)?

Done when: the interleaving is written out against the code and checked;
a fault is fixed with a test that forces it, or the behaviour is shown to
be the promised one and InterruptStress's check is corrected.

First step: the interleaving, from the stack traces in
`/Users/f/fl/bench/016/h4-stress/f3/interrupt-111110000.txt`.

Found 2026-11-03 by 016-08's F3.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
