015-47. Fix: a byte[] value is shared with the caller: a change of the array changes the value in memory
========================================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F8 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F8: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`0b739f3`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F8, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
2026-11-05. In progress: taken by session bergdb-e8 (its agent, in a clone).

2026-11-05. Done by session bergdb-e8's agent. Verified: `RwEnvironmentImp.put` passed the
caller's array to `Trans.Builder.put`, which keeps it as the value in memory, and
`KvToObjectImp.createObject` returned the value's own array for `byte[].class` (and for
`Object.class` at a key that holds bytes). Every put (`Connection.put`, `WBuilder.put`,
`RwEnvironment.put`) and every get (`Connection.get`, `RwEnvironment.get`) goes through
these two places.

* Test: `PubTester.testByteArrayValueIsNotShared`: byte[] puts by `Connection.put`,
  `WBuilder.put` and `RwEnvironment.put`, the caller's arrays changed after them, and
  a change of an array returned by `Connection.get(key, byte[].class)`, by
  `get(key, Object.class)` and by `RwEnvironment.get`; each value must still be
  `[1, 2, 3]`. Before the fix: "the value at /b1.bin, expected '[1, 2, 3]', got
  '[9, 9, 3]'" (both changes seen).
* The choice: the value is safe only if neither the caller's put array nor an array
  handed out by a get is the value in memory, so the fix copies at both, once each,
  at the Pub API's edge: `RwEnvironmentImp.put` stores `clone()` of a byte[], and
  `KvToObjectImp.createObject` returns `clone()` for byte[] (S1-F8's fix). The other
  option, a Javadoc that makes the arrays the database's, leaves the stored value open
  to a reused buffer, and a get's copy can be skipped only where the Core can tell
  that the array is not in memory (a large value read from the stream): a new output
  of `GetData`, more Core code for a case that costs least, so not done (P11, P12).
  The Core API keeps its arrays as they are; `Trans.Builder`'s and `Db.getOne`'s
  Javadoc says that they are the database's. A String put or get copies already (its
  UTF-8 conversion), and a DbObject copies its bytes.
* Cost, measured on F53 with a probe (a memory database, 20,000 keys, 1,000,000 gets of
  random keys, two runs each, before and after): gets of 16 and 100 bytes, 420 to 490
  ns, no difference beyond the noise; 4 KB, 430 to 480 ns before, 870 to 880 after
  (+0.4 µs); 64 KB, 350 to 360 ns before, 3.1 µs after (+2.8 µs, the copy's memory
  traffic). Puts: no difference (7.2 to 7.5 µs at 16 bytes, 26 µs at 4 KB, 370 µs at
  64 KB, the commit's). The heap kept per value is the same (the copy replaces the
  caller's array as the value). `RwEnvironment.exists` copies too, as it is a get.
* 010-01: no new setting or method; the stream's bytes are unchanged (the record
  was serialized at the commit already, P2); the work is per call and proportional to
  the value (P1); the cache's accounting is unchanged (P8).
* Javadoc: `Connection.get` (byte[].class: a new array that the caller may change),
  `Connection.put` and `WBuilder.put` (a byte[] is copied), which `RwEnvironment` and
  `ReadInterface` refer to.
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (104 s)`, unit 1154, f 81.

2026-11-05. Frans decided (12:00) on option (c), copy at the put only: "Option (c). I
want the zero copy gets. Performance is significantly better (more than x2) for some
cases. Javadoc should be clear." Changed by session bergdb-e8's agent; the status stays
done: the put side is fixed, the get side is documented behaviour by his decision.

* Removed: the get's two copies in `KvToObjectImp.createObject` (byte[].class, and
  Object.class at a value of bytes), so `RwEnvironment.exists` no longer copies either.
  `KvToObjectImp.testByteArray` again expects the very same array, as before 015-47.
  The put's copy in `RwEnvironmentImp.put` is kept.
* Javadoc: `Connection.get`, `ReadInterface.get` and `RwEnvironment.get`: a byte[]
  returned is the database's own array, not a copy, and must not be changed; a change
  changes what later reads return, in every connection, until the value leaves memory
  or the database restarts, while the stream keeps the committed bytes; to change the
  bytes, copy them first, with clone(). `Connection.useIndex` and `usePrimary` (their
  objects come from the same conversion): with byte[].class or Object.class, an array
  is the database's own. `Connection.put`, `WBuilder.put` and `RwEnvironment.put`: a
  byte[] is copied at the put, so the caller may change or reuse its array. `Db.getOne`
  now says that the Pub API returns the database's array too; `Trans.Builder` unchanged.
* Test: `PubTester.testByteArrayValueIsNotShared` renamed
  `testByteArrayCopiedAtPutNotAtGet`: the put-side checks kept (the three puts, the
  caller's arrays changed after them, each value still `[1, 2, 3]`), the get-side checks
  dropped, and one line added as a statement of the decided behaviour: two gets of a
  value in memory return the same array.
* 010-01: P1, less work per get; P2, the stream's bytes are unchanged; P8, a caller
  that changes a returned array makes later reads depend on whether the value is still
  in memory, which the Javadoc forbids; P10, no setting; P11, the simplest code, as
  before 015-47; P12, the Core Layer unchanged.
* Gate: `java/javadoc-pub.sh` passes; `before-commit.sh`: `BEFORE COMMIT OK (105 s)`, unit 1167, f 81.
