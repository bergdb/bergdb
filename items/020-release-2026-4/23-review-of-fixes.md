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


Log
===

2026-11-09. Created by coord-1109; Codex's round 2 done (12:14): Y1
(medium) and Y2 (low), both in 020-21's strict `Time` parsing.
