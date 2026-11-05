015-02. Implement: the C clone follows 2026.2's Java changes
============================================================

Status: done (2026-11-05). Kind: Implement. Created 2026-11-03 by Frans Lundberg.

After release 2026.2. Frans, 2026-11-03, 15:31 (016-01, D7): "The C code
does not need to be updated for 2026.2 in this work. Only Java code will be
included in the release." So the C clone (012) does not follow the
release's changes, and its cross tests against Java differ where Java's
bytes changed.

What: port to the C clone the Java changes of 2026.2 that C has a
counterpart for:

* 005-79's integer take (Part B changes the take's bytes, so C's
  `cross.sh` fails until C follows; 005-79, "Plan for 2026.2", step 9);
* 005-69's `SystemClock` promise;
* 005-78's retain duration in the stream, if Frans chooses a form.

Why: the C clone is a second implementation of the Core, compared byte for
byte with Java (012); it only checks Java while it writes the same bytes.

Done when: C's own tests and its cross tests against Java pass against
release 2026.2's Java (`release-2026.2`), and `c/readme.md` says that C
matches that release (Frans, 2026-11-05: a release, not the Java of the
day).

First step: list the Java commits since `release-2026.1` that change the
Core's bytes or its promises, against 012's last cross run.

Found 2026-11-03 in the plans of 005-79 and 005-69 (016-05).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:35, by the coordinator: C's cross-test generator
`c/test/cross/java/Vectors.java` calls `TransSeq.dither`, which 005-79
removed, so it no longer compiles against `main` (015-19).

2026-11-05, 07:30, by Claude (Opus 5.5, Claude Code), at Frans's question
what it takes to make C match release 2026.2. The Java commits from 012's
last cross run (`ae4aaf9`) to `release-2026.2` (31 touch `java/`),
sorted by what C has a counterpart for:

* Bytes: 005-79 part B, the take in fixed point (`f04cefe`; one take of
  2,158 differs, at a tie in StreamDigest's `l3-node14`).
* Same bytes at the defaults, but C's answers or decisions: 005-79 part A
  (reclaim's spacing and fraction in units of 2^-16, eviction's low
  watermark; `dde82e8`), 005-73's F1 (the start's startup distance) and
  F4 (NaN refused), 005-69 (`SystemClock`), 005-75 (record times and key
  node times checked before replay; C aborts on a flipped time today).
* Nothing in C: 005-70 (C changed with Java, `7d967d7`), 005-74 and
  005-82 (C did so already), 015-40 (the Core's `Trans` unchanged), and the
  Java-only fixes: threads and the memory model, the eviction thread, the
  resident count, the lock, the Pub API.

C as it is, against the release's source zip in a scratch folder
(`Vectors.java`'s dither line patched): `cross.sh quick` gave 276
differences, all one line, the start's `startupDistance=-1` (005-73, F1);
no stream byte differed (22 workloads, 82 crash cuts, 44 budget runs), and
the 85 corrupt variants agreed.

2026-11-05, 07:34. Frans: "Yes" to recording this and starting the port.
His answers before he left (07:34): commit when green, in his name; the
cross harness compares with release 2026.2 by default (the release's
source zip), the repo's `java/` on request; `cross.sh full` and the scale
set not before 08:45, the code and the quick tests before. "Done when"
is now against `release-2026.2`, not the Java of the day. The work runs in
a scratch clone of `main` at `9d37877`.

2026-11-05, 09:40. Done, by Claude (Opus 5.5, Claude Code). The C clone
(`items/012-bergdb-c/c/`) matches release 2026.2; `c/readme.md` says so,
under "Which Java".

What C follows, each as Java does it, with Java's tests ported:

* 005-79, part B: the take's share and dither in units of 2^-16
  (`ts_share_fp` with `j_mulhi64` and `ts_divlu`, Java's 128-bit product
  and Hacker's Delight division, so a 32-bit target needs no `__int128`;
  `ts_dither_fp`), against `unsigned __int128` on 10^5 cases each, and the
  tie of `l3-node14`.
* 005-79, part A: reclaim's fraction as an integer in units of 2^-16
  (`rc_fraction_of`; the API's double checked and converted at once with
  `j_round`, Java's `Math.round`; the getter gives the units over 65,536,
  0.1 as 0.100006), its spacing `retainDuration / 4`, eviction's
  `ev_low_of`, and the key access path's growth in integers.
* The doubles check of 005-79 in C's gate: `test/doubles.py`, in the rules
  step, refuses floating point in `src/` outside 11 allowed places, with a
  self-test; a planted double fails it.
* 005-73: the start's startup distance is the one in force (F1; also in
  `bergdb-dump`'s start line), and NaN is refused (F4).
* 005-69: the system clock is strictly increasing.
* 005-74: the record parser's sizes against the record's size, and
  `NodeStream.checkReadSize` (a size beyond the stream is a
  `StreamFormatException`, not the read's `EOFException`).
* 005-75: record times in the 56-bit range and increasing, and key nodes'
  times increasing, checked before replay; a corrupt record time is
  refused where C aborted before (`sdb_refusals`, which aborts without the
  fix). Its dead check of a stream shorter than a meta block is gone, as in
  Java.
* 015-07: the node parsers check their sizes against the node's.
* The cross harness: `test/cross/java-build.sh` compiles the Java of
  `JAVA_REF`, by default release 2026.2's source zip (checked against its
  `SHA256SUMS`, extracted into `build/java-src/`), `tree` for the
  repository's `java/`; `examples/compare.sh` takes CoreDemo from the
  same tree. `Vectors.java` writes the integer take (015-19's part for
  012); Java's vectors written again from the release. Its key-node runs
  now set a previous state before the next change's time, as a database
  does: a previous state at that same time made two equal times in a node,
  which 005-75's check refuses.

Nothing in C for: 005-70 (done with Java, `7d967d7`), 005-82 (C failed
the database already), 015-40 (the Core's `Trans` unchanged), 015-01 (the
Pub API's `created.txt`), and the Java-only fixes (threads, the memory
model, the eviction thread, the resident count, the lock, the Pub API).

Tests, on F53, in the scratch clone, against release 2026.2's Java:

* `C BEFORE COMMIT OK (179 s)`: 353 unit tests, 26 functional tests, the
  doubles check, `cross.sh quick`, `writecheck.sh`, the allocation
  failures, the examples.
* `cross.sh full C=build/test` (08:45 to 09:23): CROSS full OK, 446
  workloads all run by C (181 with reclaim), 1,357 crash cuts, 498 corrupt
  variants, 6 in turns, 1,784 budget runs, 0 differences (2,262 s). A
  negative control: on StreamDigest's `l3-node14` workloads the C before
  this work wrote other bytes than the release (the files that reclaim's
  cut leaves differ); this C writes the release's.
* `cross.sh scale C=build/release`: CROSS scale OK, the 10M-key database
  byte for byte (238 s).
* `corrupt.sh HEADERS=4` (its four bases, 656 variants;
  `/Users/f/fl/bench/015-02/corrupt/`): the same exit status and text in
  every variant. Its 12 "differences" are its own rule that C never writes
  into a database it refuses: 12 starts that both refuse after recovery's
  fill, Java's and C's directories byte for byte equal (012-14's known
  class; 014-01's damaged tail). 012-14's other classes are gone here: no
  abort on a flipped record time (005-75), no getTrans difference (005-82).

Before the long runs, at 07:28 to 07:55, this work's builds and a quick
cross run added load while the 005 session's quiet block waited, which
then skipped its runs; it ran them in a second block, 08:02 to 08:31,
while this work held. Later work checks for a QUIET-BLOCK file first.

C stays a separate project (012): Java's changes after 2026.2 (on `main`:
005-47's forcing at every append, 005-52's option B, replication removed)
are not in C, and the harness does not compare with them unless
`JAVA_REF=tree`.
