# 020-23 Independent reviews of the fixes of 9 November

Created 2026-11-09 by Frans Lundberg. Status: open.

Independent reviews of the fixes that today's bug hunts (020-13 to
020-22, 021-11) brought to `main`, about 50 commits in `java/src` from
`a9e5488` to `94a1520`, before the release candidate. Frans, 11:57 (to
the coordinator's proposal of a Codex review and two reviewers of its own,
one for the Pub layer and one for the Core): "Both as recommended."


## 1. Codex, round 2

Codex CLI, model GPT-6.1-Sol, effort max, in
`/Users/f/fl/bench/2026-11-09/clone-codex2` at `94a1520`, 11:58 to
12:14; the brief in `/Users/f/fl/bench/2026-11-09/codex2/prompt.md`.
Its report, verbatim:

<!-- CODEX REPORT START -->
Reviewed `a9e5488..94a1520`. **Two confirmed defects**, both in the strict `Time` parsing fix. Build and targeted unit tests passed. Only `probes/` was added; tracked files are unchanged.

**1. Findings**

**Y1 — medium — Relative time parsing loses clock units and rejects a valid boundary**

Commit: `648527f`. Location: [TimeResolver.java:269](/Users/f/fl/bench/2026-11-09/clone-codex2/java/src/bergdb/pubimp/TimeResolver.java:269), also line 261.

Minus-time parsing still converts the decimal through `double`, then truncates the product. Even an offset exactly representable in clock units can produce the wrong time. At the range boundary, rounding makes a legal call throw.

This leaves 020-21, section 3.1 incomplete and contradicts `Time.resolve()`’s resolution, rounding and range promises.

Reproduction: [TimeContractProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex2/probes/TimeContractProbe.java), run with `sh probes/run.sh` after building. Output includes:

```text
-0.0000021 s => delta=20 units; expected half-up delta=21
-900719925.4740993 s => delta=9007199254740992 units; expected half-up delta=9007199254740993
```

Also:

```java
Time.resolve(UTC, Time.MAX, "-7205759403.7927935 s")
```

throws `BadFormatException: Time out of range (negative: -1)`. Subtracting exactly `Time.MAX.units()` should return epoch zero.

**Confidence:** confirmed by execution.

**Y2 — low — The strict parser rejects a date form its grammar permits**

Commit: `648527f`. Location: [TimeResolver.java:150](/Users/f/fl/bench/2026-11-09/clone-codex2/java/src/bergdb/pubimp/TimeResolver.java:150).

The [Time.resolve grammar](/Users/f/fl/bench/2026-11-09/clone-codex2/java/src/bergdb/pub/Time.java:162) permits `year-month` followed by a time. The implementation instead requires a day whenever the string extends beyond `YYYY-MM`.

The same probe confirms that all three entry points—`utc()` and both `resolve()` overloads—reject these legal strings:

```text
2020-06 12:34
2020-06T12:34:56.1234567
```

Each throws `BadFormatException`. This is another remaining mismatch in 020-21’s promise to follow the published grammar.

**Confidence:** confirmed by execution.

**2. Fixes checked and found sound**

Within the reviewed cases and stated contracts:

- `4b520f9`: BufferedStream’s close-wait condition prevents the reported lost wake-up.
- `da6c5b0`: pointee checks cover canonical linking, assertion-time ID checking and writer linking.
- `1eb6390`: tracking only values whose entries the build writes preserves conflict detection.
- `bac75ce`: the value-byte limit stops steps without prematurely ending the build.
- `e2941c2`: the fixed end key works with concurrent appends and writer maintenance.
- `4e3bae2`: cleanup advances only after successful deletion and checks the prefix before finishing.
- `c950612`: the first successful raw read fixes the RW snapshot before conversion can throw.
- `a03111e` / `3f61a74`: directory replacement refusals and preservation of literal-key entries.
- `987e734` / `42201c2`: initializer errors become conversion failures; VM errors pass through.
- `ef6a3cf`: inherited-field module access and generic metadata failures.
- `87a1f83`: malformed entry K bytes receive the required internal-data refusal.
- `2fcc546`: prefix keys no longer hide definitions or markers during startup.
- `d2f86f4`: builds skip Core-written keys containing slashes in the filename.
- `3f102f2`: WBuilder is spent even when execution throws.
- `656decb`: null retain duration, String index type, negative joins and CryptoKey.NULL handling.
- `2e4c77d`: Duration refuses NaN.
- `a3bb07b`: CryptoKey returns independent key-data arrays.
- `6db1ac3`: unlistable directories report storage I/O errors.
- Deleted-build status notes correctly omit the restart promise.

Targeted unit runs all passed. [PointerTypeProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex2/probes/bergdb/core/PointerTypeProbe.java) additionally checked **192** sampled wrong-type pointer cases, with assertions on/off and writes before reads, without an unexpected failure.

**3. What I did not get to**

- Full audits of the new fuzzing, kill/restart and expanded randomized harnesses.
- Exhaustive corruption/interleaving campaigns, multi-gigabyte boundaries or extremely long keys.
- A fresh review of unchanged production code outside the requested fixes.

No before-commit, nightly or stress scripts were run.

<!-- CODEX REPORT END -->

Y1 and Y2 went to the fixer of 020-21 (12:15).


## 2. The Pub layer's fixes

Reviewer v1 (coord-1109's agent), clone `/Users/f/fl/bench/2026-11-09/clone-v1`
at `94a1520`; probes in `/Users/f/fl/bench/2026-11-09/v1/probe/` (`ProbeV1`) and
`/Users/f/fl/bench/2026-11-09/v1/c18copy/`. Nothing critical, high or medium; four
low findings, all about documents. Its report, as given (12:18):

### 2.1. Findings

| ID   | Sev. | Where                                    | Commit    | What                                      |
|------|------|------------------------------------------|-----------|-------------------------------------------|
| V1-1 | low  | Time.java:162-163, TimeResolver.java:145 | `648527f` | the ABNF gives "2013-08 14:29"; refused   |
| V1-2 | low  | Connection.java:261, WBuilder.java:71    | `60f824e` | put/delete/execute: interrupt not listed  |
| V1-3 | low  | 020-10, sections 6.1 and 6.2             | (none)    | the spec describes the build before F1-F5 |
| V1-4 | low  | releases/next.md                         | `c950612` | no line for 020-13's bug 1                |

* **V1-1** (020-21, 1): today's ABNF in `Time.resolve` gives `absolute = date [(SPACE /
  "T") time-of-day]` with `date = year "-" month ["-" day]`, and the new text says a
  string is taken only as that format gives it; but `reallyResolveAbsolute` refuses
  "2013-08 14:29" (line 145: a string longer than 7 characters must have a day). The
  same as Codex's Y2.
* **V1-2** (020-19, J8): since 2026.4 (020-10, I1) a put(), delete() or w() at a key
  without a suffix runs again after a conflict, as an rw() does
  (`RwTransaction.executeRwInner`, lines 143 to 151); an interrupt during the wait throws
  DbException ("The transaction was not run: the thread was interrupted while it waited
  to run it again after a conflict."), the flag set. J8 documented it for rw() only;
  `Connection.put`, `delete` and `WBuilder.execute` do not list it. Shown by `ProbeV1
  interrupt`. Fix: rw()'s line in all three.
* **V1-3**: 020-10, sections 6.1 and 6.2, still describe the build and the cleanup
  before F1, F3, F4 and F5 (`1eb6390`, `bac75ce`, `e2941c2`, `4e3bae2`); F16-3's skip and
  020-16's O16-2 wording also missing there. The Javadoc of `IndexBuilderImp.startBuild`
  and `IndexManager.startCleanup` is right. Cosmetic: IndexBuilderImp.java:327, a Javadoc
  line of 142 characters (F4).
* **V1-4**: 020-13's bug 1 was also in 2026.3 (an rw() that caught a get's conversion
  failure could commit after reading two states); it fixes released behaviour but has no
  line in releases/next.md, while today's other such fixes do.

### 2.2. Fixes checked and found sound

X1 (`a03111e`) and bug 3 (`3f61a74`); X2 and bug 2 (`987e734`, `42201c2`: the catch
order, `newInstance` the only call into user code); X3 (`ef6a3cf`); bug 1 (`c950612`);
020-18's F1 (`1eb6390`), F3 (`bac75ce`), F4 (`e2941c2`), F5 (`4e3bae2`), F2 and 020-19's
F1 (`2d409c9`, `55da329`); F16-1 to F16-3 (`87a1f83`, `2fcc546`, `d2f86f4`); 020-19's J1
to J8 (J7 superseded by 020-21's ABNF, J8's gap is V1-2); 020-20's T1 (`6db1ac3`) and N1
(`a3bb07b`); 020-21's 1 to 4 and Q1 (`648527f`, `3f102f2`, `656decb`, `28a6085`,
`2e4c77d`); releases/next.md's 14 Pub API entries. Combined runs on main's head, 0
findings each: c18's ProbeIndexStress with key-replace writers at
`/s/r${transactionTime}`, 60 s on a memory database (1.57 M writes, 961 index changes)
and 60 s on a file database (2 MB cache, reclaim at 2 s); ProbeIndexRestart in crash
mode, 40 rounds.

### 2.3. Not done

PubTesterJavadoc's 44 tests one by one; the new Time parse against the old for every
valid string (read only); a local time in a DST gap; the harnesses of 020-15 and 020-17
and FormatFuzzer (out of scope); no gate run.

What follows: V1-1 goes with Y2 to 020-21's fixer; V1-2, V1-3 and V1-4 to the day's
document update.


## 3. The Core's fixes

Reviewer v2 (coord-1109's agent), clone `/Users/f/fl/bench/2026-11-09/clone-v2` at
`94a1520`; probes and a proposed test in `/Users/f/fl/bench/2026-11-09/v2/`. Three
commits are below the Pub layer: `4b520f9` (020-13, bug 4, `BufferedStream`), `da6c5b0`
(021-11, `NodeCollection`) and `6db1ac3` (020-20, T1, `FileStream`). All three sound; two
low findings. Its report, as given (12:20):

### 3.1. Findings

* **V2-1, low, a test gap in `da6c5b0`.** No gate test pins the check in
  `linkToCanonical` (`NodeCollection.java:782`), which without `-ea` is rule 4's only
  type check. Every test runs with `-ea`, where `checkLinkById` (line 804) refuses the
  same pointer first: with line 782 taken out, `Unit -c 'CorruptStreamTester|NodeCollection'`
  still passes. `testFound021_11` cannot cover it (under `-da`, its row 3 is refused by the
  read, not at the start). Proposed test:
  `/Users/f/fl/bench/2026-11-09/v2/proposed-test.java`
  (`NodeCollection.testLinkToCanonicalChecksTheType`: rule 4 with `check == false` on a key
  node whose pointer position the section's ids give as a top node; refused, no handle);
  passes at HEAD, fails with line 782 out. Lines 710 and 804 are pinned by
  `testResolvePointersChecksTheType` and row 3 of `testFound021_11`.
* **V2-2, low, an older `BufferedStream` gap, not reachable from `Db`.**
  `BufferedStream.java:618-650`, not new in `4b520f9`, outside `AppendOnlyStream`'s
  CONCURRENCY rule 2: an `append()` waiting for buffer room when `close()` begins does not
  check `exception`, `flushAndClose` or `stop` again after the wait, and its write wakes
  the consumer only if it is idle or the buffer crosses a quarter. (a) `close()` may wait a
  whole wait time (bug 4's symptom by another path); (b) `close()` sees the empty buffer
  first, the append returns normally, its bytes never written. Probe
  `/Users/f/fl/bench/2026-11-09/v2/probe/src/bergdb/storage/CloseProbe.java`, mode "free",
  2 minutes: at HEAD 3 closes of 15 s in 3,279 iterations and 269 appends that returned
  during `close()` with bytes never written; at `4b520f9^` closes of 15 s within 7
  iterations. Users are not affected: `Db.closeStorage` sets STOPPING and takes the write
  lock before `StorageManager.closeAndThrow`, and `StorageManager.append` needs the write
  lock. Hardening: after its room wait, `append` checks `exception` again and throws.

### 3.2. Fixes checked and found sound

* `4b520f9` (bug 4): the consumer checks `closeWaits()` under the monitor before its timed
  wait, and `close()` sets `flushAndClose` and calls `notifyAll()` under the same monitor,
  so the wake cannot be lost; no busy loop; interrupts take the existing paths. Probe mode
  "contract" (as `Db` uses it; random delays, syncs, interrupts), 150 s: 6,787 closes,
  105,315 syncs, 244 MB; no slow close (longest 42 ms against 15 s), no lost or wrong byte.
  The old code: three 15 s closes within 6 iterations.
* `da6c5b0` (021-11): no false positive (each check tests the same canonical object a
  follow's 019-32 check tests); the rule matches `TopNode`'s layout and
  `pointsToIndexNode`; ids are unique across types; a throw in `resolvePointers` fails the
  database through `fail(t, e)`; no other site links unchecked (the follows,
  `createMemoryPointers`, `updateStreamPointers`, `canonicalNode`,
  `topNodeOfLastTransaction`, eviction, reclaim, the writer's tree operations).
* `6db1ac3` (T1): an unlistable directory gives an `IOException`, and the constructor
  releases its lock; other null-returning `listFiles()` calls are in test code only.

### 3.3. Not done

The level scripts; T1 on Linux or Windows; the pending cut during a close; the Pub layer.

What follows: V2-1's test and V2-2's hardening to a fixer (12:21), with `level1.sh`.

### 3.4. Fixes

Fixer w23 (coord-1109's agent, 12:21), clone `/Users/f/fl/bench/2026-11-09/clone-w23` from
`dcfd175`; probe outputs in `/Users/f/fl/bench/2026-11-09/w23/`.

* **V2-1**, `1a36a0c`: v2's proposed test as
  `NodeCollection.testLinkToCanonicalChecksTheType`, in the tester's style. With
  `linkToCanonical`'s `checkPointeeType` (line 782) taken out it fails ("refused,
  expected true, but was false"); with it, it passes. Test only.
* **V2-2**, `958b87f`: `BufferedStream.append` checks `exception` after its wait for room
  (`close()`, `stop()` and a failed flush each set it) and throws an `IOException`, as an
  append after them does; the old check before the wait, for a stop only, moved after it.
  020-13 bug 4's protocol is unchanged (`closeWaits()` under the monitor). What an append
  put in the buffer before its wait stays there and is written by `close()` (Javadoc).
  Test `BufferedStream.testAppendWaitingForRoomWhenCloseBeginsThrows`, deterministic (a
  held flush, the writer in its room wait, then `close()`); before the fix: "the append
  returned normally after close() began".
* v2's `CloseProbe`, mode "free", seed 1, 120 s:

  | Code | Iterations | Closes over 3 s | Longest close | Lost during close() |
  |------|------------|-----------------|---------------|---------------------|
  | before, dcfd175 | 4,292 | 2 | 15,005 ms | 338 |
  | after, V2-2     | 5,484 | 0 | 30 ms     | 0   |

  Lost before close() and wrong bytes: 0 in both runs. After the fix, 1,354 closes wrote
  more than the appends that returned: the part that a thrown append had put in the buffer
  before its wait. A copy of the probe that checks every byte of the stream (seed 2, 60 s;
  `w23/probe2/`) found 2,836 iterations, 0 wrong bytes, and that extra part in 678 of them,
  at most 3,704 bytes.
* Not reachable through `Db` by its close: `closeStorage` sets STOPPING and takes the write
  lock first. One other path closes the stream beside an append: a failed read on a
  reader's thread (`StorageManager.handleStreamException`). The storage and the database
  have failed by then. So there is no `releases/next.md` line.
* Gate on the tree of the two commits, under the gate lock: BEFORE COMMIT OK (183 s;
  unit 1,503, f 86, demos); `level1.sh`: LEVEL 1 OK. On `main` as `780dc63` and `8a3d191`.


## 4. Codex, round 3

Codex CLI, GPT-6.1-Sol, effort max, on the afternoon's fixes
(`94a1520..a593b17`, 38 commits in `java/src`), in
`/Users/f/fl/bench/2026-11-09/clone-codex3`, 14:10 to 14:28; the brief in
`/Users/f/fl/bench/2026-11-09/codex3/prompt.md`. Its report, verbatim:

<!-- CODEX REPORT START -->
Reviewed `94a1520..a593b17`: 38 commits touching `java/src`. **Two confirmed wrong-result cases and one Javadoc mismatch.** The underlying code faults predate this range; the new contracts expose guarantees that the implementation does not meet.

Only `probes/` was added. Production code, existing tests, items, docs and `frans/` are unchanged.

**1. Findings**

**Z1 — high — A backward clock can invalidate a time returned by `currentTime()`**

Commit: `5fafc1f`, [Clock.java:30](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/pub/util/Clock.java:30). Implementation: [DbClock.java:107](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/core/DbClock.java:107).

The new Javadoc explicitly permits the clock to move backward. However, a subsequent `currentTime()` overwrites `lastReadTime` with the lower time. A future transaction can then precede an earlier `currentTime()` result, contradicting [Connection.java:150](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/pub/Connection.java:150). Reads using that returned time can change after later writes.

Reproduction: [ClockContractsProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex3/probes/ClockContractsProbe.java), using a thread-safe custom clock:

```text
currentTime calls: 2000, 1500
future transaction time: 1501 (must exceed 2000)
same lookup time 2000: before -> after
```

**Confidence:** confirmed by execution. The implementation fault is older than `5fafc1f`.

**Z2 — high — A raw-byte index scan returns a format-1 object under a stale query**

Commits: `fd18b6a` / `4f96446`, the guarantee in [Db.java:101](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/core/Db.java:101); scan path also touched by `dee7c66`. Fault: [UseIndexBuilderImp.java:362](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/pubimp/UseIndexBuilderImp.java:362).

When `entryLevels()` refuses a format-1 object, the scan substitutes the stale entry’s levels. It assumes conversion will subsequently refuse the object. With `byte[].class`, conversion returns the bytes directly, so a value without the queried field is returned as a match.

This violates 020-22’s detection floor and 020-10, section 3.4. It requires no write to forbidden internal keys.

Reproduction: [Format1StaleScan.java](/Users/f/fl/bench/2026-11-09/clone-codex3/probes/Format1StaleScan.java):

1. Store `/p/a` with `x=1` and build its index.
2. Close the Pub database.
3. Through a standalone Core database, replace it with an empty format-1 object.
4. Close Core, reopen Pub and scan `eq(1)` as `byte[]`.

```text
after offline Core write: eq(1) = 1
returned /p/a = 626572676f010000
same scan as DbObject: ObjectCreationException
```

**Confidence:** confirmed by execution. The bypass predates this range; the new unconditional assurance remains false.

**Z3 — low — The new clock documentation overstates startup validation**

Commit: `5fafc1f`, [Clock.java:25](/Users/f/fl/bench/2026-11-09/clone-codex3/java/src/bergdb/pub/util/Clock.java:25).

The sentence says an out-of-range clock refuses a start. Creation checks it, but reopening an existing database need not call the clock and succeeds.

The second case in [ClockContractsProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex3/probes/ClockContractsProbe.java:26) prints:

```text
existing start with clock 2^56: succeeded, value=saved
```

The sentence should distinguish creation from reopening.

**Confidence:** confirmed by execution.

**2. Fixes checked and found sound**

Within the inspected paths and exercised cases:

- `83e8e13`, 021-12: both older-key-node load paths validate before reconstruction uses them; valid histories survive bounded restarts.
- `f66bf25`, 021-13: `appendedEnd` and the write-lock wait cover records absent or partially appended, followed by the failure/state check.
- `8a3d191`, V2-2: the post-wait exception check prevents append from continuing after close, stop or flush failure.
- `780dc63`, V2-1: the added test exercises canonical-link type checking with `check=false`.
- `04b0178`: GetN/PrefixN respect zero and positive limits; PrefixN owns its prefix copy.
- `98e39d5`: a scan before the first transaction calls `eod()` once.
- `75f42c8`: invalid builder cache budgets are refused before assignment.
- `afc1c1d`, Y1: exact relative-time arithmetic, half-up rounding and the epoch boundary.
- `644c1b8`, Y2: year-month forms accept a following time through both separators.
- `6af0f51`: CryptoKey parsing requires exactly three parts and preserves the NULL round trip.
- `cb126ac`: Time’s null arguments receive the promised `IllegalArgumentException`.
- `fe6d284`: default cache sizing clamps both bounds without narrowing overflow.
- `d782915`: transaction info filters keys without an exact Pub-key round trip.
- `dee7c66`: primary/index scans exclude keys without a Pub key; Z2 is a separate value-validation bypass.
- `67b9e2b`: stop/close documentation correctly distinguishes an admitted commit from an action still running.
- `1ea097b` / `95cda1f`: key-replacement timing and lookup-time inclusion match the code.
- `b38037a`: the documented Stockholm DST examples match resolution.
- `84848e5` / `381d26a`: conversion truncation, read-modify-write losses, UTF-8 tie ordering and empty prefixes match behavior.
- `0b71892` / `4f96446`: the checked Core exception, builder and key-space qualifications hold, apart from Z2’s guarantee.

Build and focused Core/Pub unit classes passed. Independent probes passed 489 boundary checks and, in each assertion mode, 15 bounded restarts with 135 historical scans. Reproduce the probes with `sh probes/run.sh` after building.

Two rebuilds briefly overlapped accidentally; the affected checks were rerun sequentially and passed.

**3. What I did not get to**

- Exhaustive corruption/interleaving campaigns, full harness audits, multi-gigabyte boundaries or long-running reclaim/eviction validation.
- Executing every Javadoc promise across every overload and environment.
- 021-14 and 021-15: neither is present in this checkout.

No before-commit, nightly or stress scripts were run.
<!-- CODEX REPORT END -->

Z1 to Z3 went to a fixer (14:29).

### 4.1. Fixes

Fixer z23 (coord-1109's agent, 14:29), clone `/Users/f/fl/bench/2026-11-09/clone-z23` from
`a593b17`, rebased on `5efe3bd`; gate outputs in `/Users/f/fl/bench/2026-11-09/z23-*.txt`.

* **Z1**, confirmed, `45b633e`. Cause: `DbClock.currentTime()` set `lastReadTime`, the time
  that the next transaction must pass, to the clock's time at each call, also to a lower
  one after the clock went back. Since the 2017 code: in 2026.1 with the default clock when
  the system clock was set back, since 2026.2 (005-69, a strictly increasing
  `SystemClock`) only with an application's `Clock`. Fix: `lastReadTime` never decreases;
  the time is the clock's, taken at most as `LAST_USER_TIME`, or the last time given or the
  last transaction's when that is later. The cap keeps the 1024 units of 015-55: with the
  clock there or out of range, `currentTime()` gave the clock's time, which took the times
  of reclaim's internal transactions after a user's, or made `Database.currentTime()`
  throw `IllegalArgumentException` from `Time`; with the fix alone, such a time would have
  been kept until the next start, refusing every transaction. The other users of the
  clock have no such pattern: `transactionBegin()` takes the largest of the clock's time,
  the last transaction's time + 1 and `lastReadTime` + 1; `lookupTime()` and a frozen
  lookup time take `lastTransactionTime`, which only `transactionEnd()` raises; a start sets
  it from the last stored transaction. `Clock.getTime()`'s Javadoc says what
  `currentTime()` gives. Tests, each failing before: `DbClock.testClockGoesBack`,
  `testCurrentTimeLeavesTheMargin`, `PubTesterJavadocRest.testCurrentTimeWithAClockThatGoesBack`
  (Codex's probe). `releases/next.md`, Pub API.
* **Z2**, confirmed, `4ab3077`. Cause: when `entryLevels()` refused the value at an entry's
  key, an object of format 1, `UseIndexBuilderImp.Scan.hasNext()` took the entry's levels
  as the value's and left the refusal to the conversion, which a `byte[]` scan does not
  make. Since 020-08's step 3 (`38afb1a`, 2026-11-09, 00:02) and 020-10's I3 (`8be9a95`),
  never in a release. Fix: such a value has no levels, as `RwEnvironmentImp` gives a
  previous value of format 1 no entries, so its entry is stale and the key left out, for
  every type: 020-22's W6 (a Core put that changes what the index takes is left out; Q3)
  and `UseIndexBuilder`'s Javadoc (a stale entry is skipped). Not `InternalDataException`:
  the entry is well formed and the value is the user's data, and Q4's B1 adds no detection.
  A scan as `DbObject` or `Object` now leaves the key out too, where it threw
  `ObjectCreationException` naming format 1 (8be9a95's choice under Frans's delegation,
  22:17); a get and a primary scan still refuse the object. Test, failing before:
  `PubTesterCoreKeys.testCorePutOfAFormat1ObjectAtAnIndexedObjectKey`. `releases/next.md`:
  020-08 step 3's entry corrected (it said that an index scan's `next()` refuses it).
* **Z3**, confirmed, `4c3d7b2`. `Clock.getTime()`'s Javadoc: a start that creates a
  database throws the `DbException`, as it writes the first transaction; a start of an
  existing one does not read the clock and succeeds, its transactions refused while the
  clock is out of range. Javadoc only. Test `PubTesterJavadocRest.testStartWithTheClockOutOfRange`,
  which passes on the code as it is.
* Not fixed, seen on the way: an internal transaction takes the clock's time when that is
  later, so a clock that passes `LAST_USER_TIME` between a user transaction and its reclaim
  step (102 µs before 2^56 - 1, the year 2198, or a test clock) can use up the margin, and
  the step then fails the database (015-55's design).
* Gate on the tree of the three commits, under the gate lock: BEFORE COMMIT OK (200 s; unit
  1,555, f 86, demos); `javadoc-pub.sh`: JAVADOC PUB OK; `level1.sh`: LEVEL 1 OK. On
  `main` as `6ac9708`, `d794d06` and `142afa2`.


## 5. The late Core fixes: 021-20, U10-3, U10-5, U10-6

Reviewer v2 (coord-1109's agent, 17:27 to 17:36), on `2557286` to `41e4da5`, clone
`/Users/f/fl/bench/2026-11-09/clone-v2` (branch `r-u10`), probes in
`/Users/f/fl/bench/2026-11-09/v2/probe3` to `probe5`. Result: sound, no defect.

**021-20, the two lock keys and the directory check.**

* `FileStream.lockDir` checks and adds both keys under `LOCKED_DIRS` before its `try`, so a
  start refused in the same JVM never removes the keys of the stream that holds them. A
  failure after the add removes only its own keys; the system properties go with
  `remove(k, COPY)`, so another class loader's keys stay. `unlockDir` removes the path key
  stored at lock time, independent of the directory still being there; it is still
  `close()`'s last step, also when a failed stream's `close()` throws. `toRealPath()` gives
  one key for case variants on APFS, a symlink and a relative path.
* Probe `probe5/LifeProbe.java`, one JVM, "LIFEPROBE OK": 150 starts at once after
  `close()` or `stop()` and `close()`, none refused; 20 rounds of stop, delete the
  directory, `create()` again, reopen; a start failed on a damaged stream left no lock; a
  symlink, a case variant and a relative path to an open database refused as in use, and
  started after its close; 8 threads, 320 starts at one path: 19 started, 301 refused as
  in use, nothing else thrown; a directory deleted while its database ran: a new `create()`
  refused as in use, the old database failed (`DbFailedException`) at its next file and
  wrote nothing into the new directory, which then worked and reopened.
* `checkDirectory` costs one `stat` per new file, per deleted cut file and per reopen after
  an interrupt; a file switch already creates and forces a file.
* On Linux ext4 a deleted directory's inode number is reused at once (s1: `rm -rf` then
  `mkdir` gave the same inode 50 of 50 times), which would defeat a check by file key. It
  does not here: while a file in the old directory is open, the inode is not reused (0 of
  30), and the stream holds `bergdb.lock` open until `unlockDir`, after its last file step.
  **V5-1 (low, a comment)**: this invariant is not written down; a comment at
  `checkDirectory` would keep a later change from closing the lock file earlier.

**U10-3, the buffer released.** `releaseBuffer` runs only when the thread has ended or never
started, and only after `exception` is set; `read()` checks `exception` under the monitor
before it touches the buffer; `append()` checks it at entry and after each wait for room
(`958b87f`, V2-2); the consumer releases only after its own last use. Probe
`probe4/ReleaseProbe.java` (a writer waiting for room, the first flush makes room, the second
fails and ends the thread), 3,000 iterations: no `NullPointerException`; the append returned
962 times and threw `IOException` 2,038 times.

**U10-5.** `mkdirs()` returning false throws only if the path is then not a directory; the
lock refuses the losers. Correct.

**U10-6.** `closedDurable()` runs only if no failure was set when the close began and
`mainStream.close()` returned normally; that close has flushed everything and forced the last
file, and `confirmedLength` came from its thread before the join. A close that failed leaves
the durable length where it was, so a later `sync()` throws as before. Correct.

**Not done.** A JVM run on Linux or Windows (another session was timing on s1); a second
process creating a database at the path (by reading, the old process fails at its next file
switch; the in-JVM key does not apply across processes); the commits' own tests and gates.


## 6. Codex, round 4

`codex exec`, the latest Sol model at effort max, workspace-write in
`/Users/f/fl/bench/2026-11-09/clone-codex4`, on `5d45478..41e4da5` (the late fixes:
021-13, 021-16 to 021-23, 020-24's U10 and U11, 020-27, 020-28, the Android changes),
17:28 to 17:45. Prompts, logs and the report: `/Users/f/fl/bench/2026-11-09/codex4/`. The
first run stopped at 17:37 on the provider's content filter while it studied the recursion
of split propagation in the write path, already open as 021-16's Q1; it was resumed with
that question left out.

**W1 (high), confirmed by a probe**, `2557286` (021-20), `FileStream.newFile()`: it checks
the directory, then forces and closes the previous file, which can block, before it makes
the next file by path. A directory replaced during that force (the probe pauses the
`SWITCH` force through `FileStreamIo`, moves the live directory away and moves a synced,
closed database into its path) gets the old database's next stream file: the old
database's `sync()` and `close()` return without an error, and the replacement then cannot
start ("Bad size of file .../00000000000000.bergdb, should have been a multiple of 100000,
but was 424"). It contradicts `Database`'s Javadoc that the old database writes nothing into
the replacement directory. Probe: `clone-codex4/probes/DirectorySwitchProbe.java`. To fixer
d24 (17:40), as 021-24; fixed, on `main` as `c66e824`, and reviewed (section 7).

**Checked and found sound** (no defect found within the checks described): 021-21 and
021-22 (the environment's lock, conversions outside it, closing before the commit, guards
released on exceptions, same-thread re-entrancy kept); U11-5; 021-17 and R17-1; 021-13;
U10-3; U10-6; 021-23; 021-16 and 021-18; 020-28 (the refusals of an encrypted database
leave its files unchanged); the Android changes by reading; the Javadoc of 020-24 and
020-27 against the code and focused tests.

**Not done**: a run on Android; exhaustive I/O interleavings, power loss, a full disk;
heap limits of several GB; the recursion of split propagation (021-16, Q1).


## 7. The review of 021-24

Reviewer v2 (coord-1109's agent, until 18:18), on d24's fix of W1, `4ebd063` in
`clone-d24`, on `main` as `c66e824`; probes in `/Users/f/fl/bench/2026-11-09/v2/`. Result:
sound, no defect; two low points of wording, V7-1 and V7-2, done by d24 in `604841a`, on
`main` as `03ce6ec`.

* **Checks before each step.** Every step that opens, creates or deletes a file by its path
  is checked right before the call: `openForRw`, `DbFile.delete`, `reopenChannel`, and the
  writer's reopen in `force()`. `FileStreamIo` makes those calls directly, with nothing
  between the check and the call that can wait. The slow steps come before the first check
  or after the step: the `SWITCH` force, the writer's close, `close()` in `delete`, and
  `forceDirectory`. The checks after the step cover a replacement during the file's force,
  the directory's force and the read channel's open. The start's read-only opens of earlier
  files are not checked, but they create nothing.
* **Codex's probe** (`DirectorySwitchProbe`, section 6): the old database now fails at its
  `sync()` (`DbFailedException`, its cause "no longer the database's directory"), and
  nothing is made in the replacement.
* **The read channel.** A reopened read channel is published only after its second check,
  under `channelLock`, and closed if that check fails.
* **V7-1 (low, wording): the window that is left**, between the check and the step: the
  comments and `Database.stop()` said "microseconds"; it is usually microseconds, longer if
  the thread is paused, as by a GC, and no bound. Said so in `604841a` (`03ce6ec`).
* **V7-2 (low, wording): the empty file the window can leave** is refused with an exception
  that depends on what else is in the directory: `BadDirStateException` beside the
  replacement's own stream files; in a directory without others `StreamFormatException` from
  `create()` and `DatabaseMissingException` from `open()` (probe `v2/probe6`). Said so in
  `604841a` (`03ce6ec`); a clearer refusal is for Frans (020-11, section 11).
* **No case found where a legal database fails:** a symlink, a relative path, a case
  variant, a slow disk, a start. `LifeProbe`, "LIFEPROBE OK": 150 starts at once, 20 rounds
  of stop, delete and create, a failed start, 8 threads on one path, a directory deleted
  while its database ran. The 86 unit tests of the streams passed.
* **A remote risk.** Any `IOException` of the check's `stat` counts as "gone", so a
  transient error of `stat` on a network file system would fail a legal database. Not seen.

**Not done.** The full gate, a run on Linux, a stress race inside the window.


Log
===

2026-11-09. Created by coord-1109; Codex's round 2 done (12:14): Y1
(medium) and Y2 (low), both in 020-21's strict `Time` parsing.

2026-11-09. Fixer w23: V2-1's test (`1a36a0c`) and V2-2's hardening (`958b87f`) in
clone-w23, gated with `level1.sh` (section 3.4).

2026-11-09. Codex, round 3 (14:28): Z1 (high, a backward clock),
Z2 (high, a format-1 object through a byte[] index scan), Z3 (low, a
Javadoc sentence); both high faults older than today's range.

2026-11-09. Fixer z23: Z1 (`45b633e`), Z2 (`4ab3077`) and Z3 (`4c3d7b2`) in clone-z23,
gated with `level1.sh` (section 4.1).

2026-11-09, 16:20. Frans decided Z2 as recommended: a scan of an index leaves out an
object of format 1, for every type (section 4.1; on `main` as `d794d06`, with Z1 as
`6ac9708` and Z3 as `142afa2`).

2026-11-09. Reviewer v2: 021-20, U10-3, U10-5 and U10-6 sound; V5-1 (low), a comment
at `checkDirectory` (section 5).

2026-11-09. Codex, round 4 (17:45): W1 (high, a directory replaced during a file
switch's force; to 021-24); the rest of the late fixes sound (section 6).

2026-11-09. Reviewer v2: 021-24's fix (`4ebd063`, on `main` as `c66e824`) sound; V7-1
and V7-2 (low, wording), done by d24 in `604841a` (`03ce6ec` on `main`) (section 7).
Section 7 and the main hashes of sections 3.4 and 4.1 written by coord-1109's final items
pass.
