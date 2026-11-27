028-69. Implement: remove the internal crypto code
==================================================

Status: in progress. Kind: Implement. Frans: none (decided).
Created 2026-11-27 by Frans Lundberg.

What: encryption left the API in release 2026.4 (020-28), and its code
was kept internal for a later design (017-10): `bergdb.stream.SalsaStream`,
`bergdb.pubimp.CryptoKey`, the package-private
`DatabaseBuilderImp.cryptoKey()`, and what only they use in the stream
contract, the storage, the Core's builder and the tests. This entry
removes that code, its tests and its mentions in the Javadoc. The
refusal of a database that a release before 2026.4 encrypted stays, if
it needs none of the removed code; if it does, the entry's log says what
was done about it.

Why: Frans decided on 2026-11-27 to remove it.

* The key is a setting outside the stream that changes the stream's
  bytes, against the rule of the day for P2's wording (no setting
  outside the stream is to affect the bytes; 028-68 is the other such
  setting).
* 028-60's part 2 (the repair of a tail of zeros, branch `028-60b`,
  gated and reviewed twice by Codex) waits only on a choice about
  encrypted streams, which exist only through this code.
* The study of A1's option (d) and Codex's review of it (2026-11-27,
  006-37) both met it: the keystream at a byte written again, and the
  cipher's cursor after a cut of the tail.

For the later design: the record of the removal goes into 017-10's log,
so that the design finds the code: the last commit that has it, the
commit that removes it, and the files. When encryption comes back, the
key is the one exception to "no setting outside the stream affects the
bytes": the stored bytes depend on it, and it cannot be in the stream
(Frans, 2026-11-27).

Frans: none; decided 2026-11-27.

Done when: the code is gone; `java/before-commit.sh` prints
`BEFORE COMMIT OK`; 017-10's log has the record of the removal; 028-60's
part 2 is rebased on it without its opt-out for encrypted streams.

First step: list every use of `SalsaStream`, `CryptoKey` and
`cryptoKey` in `java/` (on 2026-11-27: `DatabaseBuilderImp`,
`CryptoKey`, `PubTester`, `PubTesterJavadocRest` and `Pack` in
`bergdb.pubimp`; `DbBuilder` and `Db` in `bergdb.core`; `SalsaStream`,
`StreamContract`, `StreamContractTester` and `Pack` in `bergdb.stream`;
`RecoverableStream` in `bergdb.storage`; `bergdb.pub`'s package.html),
and the scripts and items that name them.


Log
---

2026-11-27. Registered by lead-1127 after Frans's decision; in progress,
by an agent of lead-1127 in a clone.
