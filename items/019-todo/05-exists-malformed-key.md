019-05. Fix: Connection.exists() answers false for a malformed key, where get() throws
=====================================================================================

Status: done. Kind: Fix. Frans: decision.
Created 2026-11-05 by Frans Lundberg.

What: `ConnectionImp.exists(ukey)` catches the `IllegalArgumentException`
of `PubKeys.u2i` and returns `false` for a key that does not follow the
allowed format (empty, without the leading `/`, `/` alone, ending with
`/`, or containing `//`). It returns before the read, so it neither
freezes the lookup time (015-48) nor changes what `transactionInfo()`
describes (015-62). For the same key:

* `ConnectionImp.get()` throws `IllegalArgumentException` (its own
  Javadoc: "if 'ukey' has an invalid format").
* `RwEnvironmentImp.exists()`, the `exists()` of an rw-transaction, is
  `get(ukey, byte[].class) != null`, and `RwEnvironmentImp.get()` calls
  `PubKeys.u2i` first, so it throws `IllegalArgumentException` too
  (found by reading the code). The exception leaves the action, and
  `RwTransaction.executeRw` catches only `RerunException`, so `c.rw(...)`
  throws it and the transaction is not run.

So `exists()` answers differently in a connection and in an
rw-transaction, through the same `ReadInterface.exists`, which lets a
read method be used in both. `Connection.exists()`'s Javadoc names
`IllegalArgumentException` only for a null key, and says that it is "a
read like get()". The method's comment in `ConnectionImp` says that it
throws for a key "not of a valid format", which the code does not do.

Why: found 2026-11-05 by the agent that wrote 015-62's Javadoc of
`exists()` (commit a46d2b2). A fault of the Pub API, in release 2026.3's
goal (018-01, D4). No test or code in `java/` calls `exists()` with a
malformed key.

Frans: decision. The options:

* (a) **`exists()` throws `IllegalArgumentException` for a malformed
  key**, as `get()` does, in a connection and in an rw-transaction alike.
  `ConnectionImp.exists()` drops its catch and lets `PubKeys.u2i` throw;
  the rw-transaction's `exists()` is unchanged. `Connection.exists()`'s
  `@throws IllegalArgumentException` says "if 'key' is null or not of a
  valid format", as `get()` does, and `ReadInterface.exists` follows. A
  caller that passes a malformed key to a connection's `exists()` gets an
  exception where it got `false`: a change of behaviour, for a call that
  is a programming error. Recommended: a malformed key is a programming
  error, as a null key already is, and the two reads, and the two places
  `exists()` is called from, then agree.
* (b) **`exists()` answers `false` for a key that cannot exist**, in a
  connection and in an rw-transaction alike. The connection keeps its
  catch; `RwEnvironmentImp.exists()` checks the key itself (catches the
  `IllegalArgumentException` of `PubKeys.u2i` and returns `false`, before
  the read, so it adds no read hash). The Javadoc of `Connection.exists()`
  and `ReadInterface.exists` says that `exists()` answers `false` for a key
  that is not of a valid format, without reading: it then neither freezes
  the lookup time nor changes `transactionInfo()`, and `get()` throws for
  the same key. No caller's behaviour changes in a connection; in an
  rw-transaction, a call that threw returns `false`. `exists()` and
  `get()` then disagree on a malformed key, by design.

Done when: Frans has chosen; a test that fails before the fix passes (for
(a): `exists()` of a connection and of an rw-transaction throw
`IllegalArgumentException` for each malformed form above; for (b): both
return `false`); the Javadoc says so; `before-commit.sh` prints BEFORE
COMMIT OK.

First step: Frans's choice.


Log
---

2026-11-05. Registered by session bergdb-e8 at Frans's word (12:35: "OK,
register it as 019-05."). Status waiting, for Frans's choice between (a)
and (b).

2026-11-05, 12:56. Frans chose option (a): "as recommended". Status in
progress, taken by session bergdb-e8's agent.

2026-11-05. Done by session bergdb-e8's agent. The test,
`PubTester.testExistsOfMalformedKeyThrows`, calls `get()` and `exists()`
of a connection, and of an rw-transaction (through `c.rw()`), with each
malformed form above (`""`, `"a/b"`, `"/"`, `"/a/"`, `"/a//b"`), and
expects `IllegalArgumentException` from each; then `exists("/a/b")` is
true. Before the fix it failed at the first connection `exists()` ("key
'', connection exists(): expected IllegalArgumentException"); the
rw-transaction's calls threw already, and the test pins them. The fix:
`ConnectionImp.exists()` drops its catch and lets `PubKeys.u2i` throw,
and its comment says so. The Javadoc of `Connection.exists` and
`ReadInterface.exists`: `@throws IllegalArgumentException` "If key does
not follow the allowed format, or is null", as `get()`'s. No other code
in `java/` (src, src-dev, stress, bench) calls `exists()` with a
malformed key. `releases/next.md` notes the change under Pub API. 010-01's
P1 to P12: a check of the argument before the read; no write, no
setting, no global state, the stream and the Core API unchanged (P2,
P12); a refused call, not a failure: the database goes on (P7); simpler
code (P11). JAVADOC PUB OK; BEFORE COMMIT OK (105 s; unit 1168, f 81).
