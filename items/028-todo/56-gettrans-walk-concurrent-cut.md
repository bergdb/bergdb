028-56. Fix: getTrans's walk refuses a kept transaction when a cut comes during it
===================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `Db.getTrans(tpos)` of a transaction of over 1 MiB walks the
records' sizes from a record's start that a meta block names
(`RecoverableStream.getRecordStartBefore`, `NodeStream.recordHolding`;
021-27, Q27-1; 028-55). The stream's first position is read before the
meta block; a cut made by another thread during the walk can remove the
named record, which is below reclaim's cut though `tpos` is not, and
the walk's read below the first position makes `getTrans` throw
`LookupTimeNotAvailableException` for a transaction that is kept. A
retry succeeds. Found by Codex's review of 028-55 (2026-11-25), with a
probe that holds the cut with latches (`DbCutRaceProbe`: a get gave
`tpos` 1,102,264, the cut stayed at 1,101,912, the first position
became 1,000,000, the walk's named start was 512); the same on `main`
before 028-55, so since 2026.5 (`2858ed36`).

Why: a call refused wrongly (033: S3, a race), in the Core API only;
`Connection.transactionInfo()` does not walk.

Frans: none.

Done when: the race reproduced on `main` with a probe or a unit test
that fails before the fix; the fix (Codex's lead: no named start below
the cut read at the walk's start, and a new start when a cut removes
what the walk reads while `tpos` is still kept); `java/before-commit.sh`
printing `BEFORE COMMIT OK`; whether 2026.5 and 2026.6 have it, and if
so an RB entry drafted for 033.

First step: 028-55's entry and fix; `RecoverableStream.getRecordStartBefore`
and `NodeStream.recordHolding`; Reclaim's cut and BufferedStream's
first position.


Log
---

2026-11-25. Registered by lead-1125, from Codex's review of 028-55.
