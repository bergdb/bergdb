015-62. Fix: transactionInfo() after a get() that found no entry throws IllegalArgumentException
================================================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F7 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F7: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes for the code path; 2026.1's `getTrans` may have read position 0 instead of

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies and fixes it, with
015-42, 48, 59 and 62 as one group.

2026-11-05. Done by session bergdb-e8's agent. Verified:
`transactionInfo()` checked only `actualLookupTime == -1` and
`tpos == Spos.NULL`; a get that finds no entry does not set
`GetData.tpos`, so on a connection whose gets had found nothing it was 0,
and `Db.getTrans(0)` threw `IllegalArgumentException: Not a position of a
transaction, 0.`.

* Test (`PubTester`, unit): `testTransactionInfoAfterGetOfMissingKey`, R8's
  probe made a test: `IllegalStateException` whose message says "found no
  entry", then a get that finds a value gives its info. Before the fix:
  "IllegalArgumentException: Not a position of a transaction, 0.".
* Fix: `transactionInfo()` throws `IllegalStateException` when `tpos` is 0
  (no read of the connection has found a value). Javadoc of
  `Connection.transactionInfo()`: the `IllegalStateException` is also for
  "no get() has retrieved a value: ... each found no entry".
* Not changed, a question for Frans: after a get that found a value, a get
  that finds none leaves `transactionInfo()` describing the value found
  before (`tpos` is kept), as the Javadoc's "the last value retrieved with
  the get() method" reads literally. R8-F7's proposed fix would throw then
  too. Also, `exists()` sets what `transactionInfo()` describes, though the
  Javadoc names only `get()`. Both are as in 2026.2.
* Checked against 010-01's P1 to P12: no new work, wait, setting, public
  method or global state; the Core Layer and the stream are unchanged.
* A line in `releases/next.md` (Reliability).
* Gate, with 015-42, 48, 59 and 62: `before-commit.sh`: `BEFORE COMMIT OK
  (103 s)`, unit 1155, f 81.

2026-11-05, 12:24. Frans decided the open question. The options as given
to him, for a get that finds no entry after a get that found a value
(written by transaction T1), where `transactionInfo()` still describes T1:
(a) keep it; (b) throw `IllegalStateException` after a get that found
nothing (R8-F7's proposal); (c) keep it and say it in the Javadoc. His
answer: "as recommended", (c). Changed: the Javadoc of
`Connection.transactionInfo()` now says "A get() that finds no entry does
not change the value this method describes: after one, it describes the
value retrieved by an earlier get()."; no code change. A clause in
`releases/next.md`'s line.

2026-11-05, 12:27. Frans decided the second question: `exists()` sets
what `transactionInfo()` describes, though the Javadoc named only `get()`.
In `ConnectionImp`, `exists()` reads through `getBytesAtLookupTime()`, with
the connection's `GetData`: one that finds the key sets `tpos` as a get
does; one that does not sets the actual lookup time and keeps `tpos`, as a
get that finds no entry. An `exists()` of an rw-transaction reads with the
transaction's own `GetData` (015-42) and changes neither. The options as
given to him: (a) keep it and document it; (b) make `exists()` leave
`transactionInfo()` alone. His answer: "as recommended", (a). Changed, the
Javadoc only, no code change: `Connection.exists()` now says that it is a
read like `get()` (the lookup time, the frozen time of 015-48) and that,
when it finds the key, `transactionInfo()` then describes the transaction
that wrote the value; when it does not, it leaves `transactionInfo()` as a
get that finds no entry does. `Connection.transactionInfo()` says "An
exists() of this connection counts as a get() here: one that finds the key
as a get() that retrieved its value, one that does not as a get() that
found no entry." `ReadInterface.exists`, `RwEnvironment` and the class
comment of `TransactionInfo` are unchanged. A clause in `releases/next.md`'s
line.
