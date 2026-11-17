019-04. Implement: remove seekFirstPos() from AppendOnlyStream
==============================================================

Status: done. Kind: Implement. Frans: none (decided).
Created 2026-11-05 by Frans Lundberg.

What: `AppendOnlyStream.seekFirstPos(position)` makes an empty stream
start at a later position. Remove it from the interface and from every
implementation and wrapper in `java/src`, `java/src-dev`, `java/stress`
and `java/bench`, with the two checks of it in harness 6.3 (018-02);
`FileStream` keeps a package-private method of the same kind for its own
tests' large positions.

Why: its Javadoc says that it was added for replication, which was removed
on 2026-11-04 (005-11). No production code calls it. Only pass-through
wrappers (`CutStream`, `ReadOnlyStream`, `SalsaStream`, `BufferedStream`'s
inner class), test wrappers (`DbTester`, `DbTesterFailure`, `PubTester`),
harness 6.3 (`StreamContract`, `StreamContractTester`, `StrictStream`;
018-02) and `FileStream`'s own tests (5 calls, for large positions) use
it. `MemoryStream`, `DummyStream`, `OneFileStream` and `StorageManager`
throw `UnsupportedOperationException`, which the Javadoc does not allow
(018-02, section 2.4). A storage interface smaller by one method keeps
the Core Layer small (010-01, P12).

Frans: the options, as put to him on 2026-11-05:

* (a) Remove it from the interface and from every implementation and
  wrapper, with harness 6.3's two checks of it; `FileStream` keeps a
  package-private method of the same kind for its own tests' large
  positions. The storage interface gets one method smaller (P12), and the
  Javadoc's gap (five implementations throw
  `UnsupportedOperationException`, which the Javadoc does not allow) is
  gone. Recommended.
* (b) Keep it and document it as optional.
* (c) Leave it as it is.

Frans, 2026-11-05, 12:30: "Yes, do it now", option (a), as recommended.

Done when: no `seekFirstPos` in `AppendOnlyStream` or in any class of
`java/src`, `java/src-dev`, `java/stress` and `java/bench` but
`FileStream`'s package-private method and its tests; harness 6.3 without
its checks of it, and 018-02 saying so; `releases/next.md` with a line;
`before-commit.sh` prints BEFORE COMMIT OK, the Core builds alone
(`stress/core-build.sh unit`), and the level script that covers the
stream and the storage passes.

First step: `grep -rn seekFirstPos java/` and remove each method; then
`FileStream`'s method package-private, without `@Override`.


Done
----

* `AppendOnlyStream`: the method and its Javadoc gone; a line in its log.
* Gone from `MemoryStream`, `OneFileStream`, `DummyStream`, `CutStream`,
  `ReadOnlyStream`, `SalsaStream`, `StorageManager`, `BufferedStream`
  (also its field `appendHasBeenCalled`, set by every append and read
  only by the method, and its test stream's pass-through), `DbTester`,
  `DbTesterFailure` (three test streams) and `PubTester`; `stress/Perf.java`
  no longer passes it on (below). `java/src-dev` and `java/bench` had none.
* `FileStream`: `seekFirstPos(long)` stays, package-private, with a
  Javadoc that says it is for this class's tests' large positions (bergdb
  019-04); its four tests (`testSeekFirstPos0`, `testSeekFirstPos1`,
  `testReopenPast214TB`, `testLockFile`) run unchanged.
* Harness 6.3: `StreamContract`'s checks "seekFirstPos()" and
  "seekFirstPos() after an append" and `Impl.seekUnit()`;
  `StrictStream`'s `seekFirstPos()`, its call SEEK_FIRST_POS, its kind
  SEEK_AFTER_APPEND and its field `appended`, used only there;
  `StreamContractTester`'s check of the kind (its breach counts 7 and 10
  are now 6 and 9). 018-02, sections 1, 2.1, 2.2 and 2.4, and its log,
  say so.
* `stress/Perf.java`: its `CountingStream` keeps a `seekFirstPos(long)`
  without `@Override` that throws `UnsupportedOperationException`, so that
  the harness of `performance.sh` (`PerfUtil.java`, `Perf.java`,
  `PerfTool.java`), compiled against each build's jar, still compiles
  against older jars, whose interface has the method (the coordinator,
  2026-11-05). `PerfUtil.java` and `PerfTool.java` implement no stream.
  Found on the way: the harness already fails to compile against 2026.2's
  jar since 005-47 (`9b67a82`), at `new FileStream(dir, !noForce)`, a
  constructor that 2026.2 lacks; with that line changed in a copy, it
  compiles against 2026.2's jar, and without the kept method it does not.
* `releases/next.md`: a section Internal with the change; the Core API,
  the Pub API, the stream format and the stream's bytes are unchanged.
* `docs/` (levels.md, trace-format.md, sis-model.md) and `lean/` never
  name it: the Lean model has no such step, and the docs describe no
  stream method list. Nothing changed there.
* Not changed, as told: the copies in other items' tools and reviews
  (005, 006-11, 007, 016-06, 004-02, and 012's `StreamScan`, built
  against 2026.2). Those that call it on an `AppendOnlyStream` (the
  timing wrappers of 005-57, 005-64, 005-81, 007-05, 004-02 and others)
  no longer compile against `main`; those that only have the method
  still do.

010-01's principles: P2 and P8 hold, since no write path called it and
the stream's bytes are unchanged (level 3's RestartInvariance: the
streams identical); P1, P3 to P7, P9 and P10 are not touched
(`BufferedStream.append` writes one volatile less); P11 and P12 gain: the
storage interface under `Db` is one method smaller, and no implementation
throws `UnsupportedOperationException` for a method of the interface.


Log
---

2026-11-05. Registered by session bergdb-e8, at Frans's decision (12:30);
taken by the session's agent, in a clone of `main` at b16e715.

2026-11-05. Done by session bergdb-e8's agent: `seekFirstPos()` removed
from `AppendOnlyStream` and every stream and wrapper, with harness 6.3's
checks of it; `FileStream` keeps a package-private method for its tests.
Gates in the clone: `before-commit.sh` BEFORE COMMIT OK (105 s; unit
1,167, f 81), `stress/core-build.sh unit` CORE BUILD OK (747 unit tests),
and `stress/level3.sh` (full) LEVEL 3 OK, chosen because it runs the
stream and the storage hardest: the unit and f-tests, cuts through
`CutStream`, `FileStream` and `StorageManager`, LoadTest on a strict
stream, PowerLossTest on `FileStream` and InterruptStress on a
`FileStream`.

2026-11-05. At the coordinator's request, `Perf.java` keeps a
`seekFirstPos` without `@Override` (Done, above); the harness compiles
against the clone's jar, and against 2026.2's but for 005-47's
constructor; 015-19's log lists the item tools that no longer compile.
