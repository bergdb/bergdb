028-55. Investigate: getTrans fails in week.sh's Churn soak, seed 2078207, node size 30
=====================================================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `week.sh` on `main` at `09bf9efb` (2026-11-25, step apps-soak-cc):
the app Churn (a2, 024-26), `Churn 2078207 30 30 300 DIR 1000 500 0.25
0 400000 big`, failed after 50 transactions with no restart. Its
`verifyChains` called `Db.getTrans(167171320)`, a position that
`getOne` had given in `GetData.tpos`, and got "Not a position of a
transaction, 167171320: the bytes there are not a committed
transaction's record", caused by `StreamFormatException: Bad
transaction size, -1594286241, transPos=160000128, stream size:
340100968` (`NodeStream.readRecordHeader`, from `recordHolding` and
`TransIterator.next`). The stream is in files of 20,000,000 bytes; the
first kept file begins at 160,000,000, and the walk began at
160,000,128. The other 20 apps of the soak passed, and the same app
passed in earlier week runs with other seeds.

Why: a read of a committed transaction refused, or the walk to it
misreading the stream; through the Pub API, `Connection.transactionInfo()`
reads with the same walk, and a record that is not a committed
transaction fails the database there (021-27). A wrong refusal is S3, a
failed database S2 (033's rules); in 2026.6 too, a released bug.

Frans: none.

Done when: the failure reproduced from the seed (and from the kept
data, if it helps); its cause named; release 2026.6 checked; a fix with
a unit test that fails before it, `java/before-commit.sh` printing
`BEFORE COMMIT OK`, and the RB entry in 033 if 2026.6 has it.

First step: run the command above on `main`'s release jar; read
`NodeStream.recordHolding`, `TransIterator` and where the walk begins
for a position in the first kept file of a split file stream.


Log
---

2026-11-25. Registered by lead-1125, from `week.sh`'s report
(2026-11-25-1409).
