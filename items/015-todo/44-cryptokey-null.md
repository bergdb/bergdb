015-44. Fix: databaseBuilder.cryptoKey(CryptoKey.NULL) after a key keeps the key
================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F5 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F5: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`0b739f3`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F5, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
2026-11-05. In progress: taken by session bergdb-e8 (its agent, in a clone).

2026-11-05. Done by session bergdb-e8's agent. Verified: `DatabaseBuilderImp.cryptoKey`
set the key only when it was not `CryptoKey.NULL`, so NULL after a key kept the key, and
the database was encrypted, against the Javadoc ("CryptoKey.NULL to not use any
encryption"); `cryptoKey(null)` threw a `NullPointerException`.

* Test: `DatabaseBuilderImp.testCryptoKeyNullAfterKey`, a builder on a
  `MemoryStream` with `cryptoKey(CryptoKey.generate()).cryptoKey(CryptoKey.NULL)`;
  before the fix: "the stream's first bytes, plain without encryption, expected
  'berg', got 'Æ-Ë'" (encrypted). And `testCryptoKeyNullRefused`; before the fix,
  a `NullPointerException`.
* Fix: `DatabaseBuilderImp.cryptoKey` sets `this.cryptoKey` to null for NULL, the
  last call counts, and throws `IllegalArgumentException` for null, as `dir(null)`
  does (S1-F5's fix). `DatabaseBuilder.cryptoKey`'s Javadoc says both.
* 010-01: no new setting or method (P10, P12); a database started with NULL is not
  encrypted, as documented: no change of the format, and no workload in StreamDigest
  sets a key (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (104 s)`, unit 1154, f 81.

2026-11-05, 12:20. Frans, to session bergdb-e8, on what
`cryptoKey(null)` should do: (a) `IllegalArgumentException`, as this
morning's fix made it, with a message pointing to `CryptoKey.NULL`, as
`create(null)` and `open(null)` throw; (b) treat `null` as
`CryptoKey.NULL`; or (c) a documented `NullPointerException` at once.
His answer: "As recommended", (a): an accidental null must never
quietly mean no encryption. Nothing in `java/` changes.
