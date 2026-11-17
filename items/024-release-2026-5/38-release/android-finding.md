# 024-38, Android finding: testClosedDatabasesHoldLittleHeap

Created 2026-11-13 by Frans Lundberg. Status: diagnosed; the fix is
proposed, not made (nothing lands before the morning's commit B).

The release night of 2026.5 (024-38, section 3) failed its Android step,
`java/stress/android.sh` (006-18-03) on commit A `3611130c`, with one
failure among about 1,700 unit tests:
`PubTesterJavadocNewUsers.testClosedDatabasesHoldLittleHeap`, "heap grew
by 48923 KB for 10 closed databases" (the bound is 30 MB). The test came
with 020-24's U10-3 (commit `d10bcce2`, 2026-11-09). This file says why,
made by the agent "andr" of the coordinator coord-1112, during the night.


## 1. The answer

* **Not a regression, and not a leak.** The test's measurement does not
  work on Android: its `heapAfterGc()` calls `System.gc()` three times,
  and on Android (ART's libcore) `System.gc()` runs no collection unless
  `System.runFinalization()` ran just before; it only sets a flag for
  the next `runFinalization()`. So the test measures the heap with
  whatever garbage the background collector has not yet taken: the
  closed databases' released 10 MB write buffers. Whether the test
  passes depends on when ART's concurrent collector happened to run.
* **It came with `d10bcce2`** (020-24, U10-3), the commit that added the
  test, which is in release 2026.4. 2026.4's release night passed it by
  chance.
* **Android only.** On a JVM `System.gc()` calls `Runtime.gc()`, a full
  collection, and the test passes (this night: night.sh large, s1's JDK
  27 and 17).
* **The fix:** in `heapAfterGc()`, `Runtime.getRuntime().gc()` instead
  of `System.gc()`. One line in the test, no product code; the same
  change, for the same reason, that 006-18-03 made in
  `PubTester.testConnectionOfEndedThreadNotKept` (commit `58f20922`,
  whose comment says it). On a JVM nothing changes.


## 2. Evidence

All runs on the emulator of android.sh (AVD bergdb34, API 34, arm64), on
port 5592, with A's build and with release 2026.4's (`76f66f89`, the tag's commit), each
dexed as android.sh does. F53 ran the night's frac step meanwhile.

**2.1. The test alone fails at the same rate on 2026.4 and on A.** Unit
with `-c PubTesterJavadocNewUsers -m testClosedDatabasesHoldLittleHeap`:

| Build             | Runs | Failures | "heap grew by" in the failures, KB |
|-------------------|------|----------|------------------------------------|
| A `3611130c`      | 83   | 26       | about 38,600 or 48,700             |
| 2026.4 `76f66f89` | 60   | 21       | about 38,000 or 48,000             |

(Batches: A 9 of 20, 1 of 3, 7 of 30, 9 of 30; 2026.4 11 of 30, 10 of
30, and a first batch of 20 with 5 failures in the 10 runs whose lines
were kept.) The failing values come in steps of 10 MB: 4 or 5 write
buffers not yet collected. A bisect between the two is therefore
pointless and was not run.

**2.2. With a real collection the closed databases hold 0.8 MB each.** A
probe (`andrprobe.HeapProbe`, outside the repo, section 4) runs the
test's scenario and measures the heap after three of: `System.gc()` (as
the test), `Runtime.getRuntime().gc()`, or `System.gc()` followed by
`System.runFinalization()`; first while the 10 closed databases are
referenced ("kept"), then after the list is dropped ("dropped"). Ten
processes each, in KB:

| Build  | Mode    | Kept, KB                                       | Dropped, KB  |
|--------|---------|------------------------------------------------|--------------|
| A      | system  | 18,964 to 19,177 (7 runs); 29,154; 49,489 (2)  | = kept       |
| A      | runtime | 9,098 (all 10)                                 | 716          |
| A      | sysfin  | 9,098 (all 10)                                 | 716          |
| 2026.4 | system  | 18,293 to 18,476 (7 runs); 28,479 (2); 48,805  | = kept       |
| 2026.4 | runtime | 8,429 (all 10)                                 | 703          |
| 2026.4 | sysfin  | 8,429 (all 10)                                 | 703          |

With `System.gc()` alone, "dropped" equals "kept" in every run: no
collection ran at all between the two measurements, although the
`List` of 10 databases became garbage. With `Runtime.gc()`, or with
`runFinalization()` after `System.gc()`, the numbers are exact and
repeatable: the 10 closed databases hold 8.4 MB on A, 7.7 MB on 2026.4,
far under the test's 30 MB.

**2.3. The same on a JVM.** The probe with `Runtime.gc()` on JDK 25
(Homebrew openjdk 27): kept 10,285 KB, dropped 1,997 KB on A; 9,730 and
2,108 on 2026.4. So a closed database holds about 830 KB on A and 760 KB
on 2026.4, on both platforms.


## 3. A side observation: 024-33 adds 67 KB to a closed database

The 0.67 MB difference for 10 closed databases (section 2.2 and 2.3) is
024-33's `Cache3.Table`. A class histogram (`jcmd GC.class_histogram`,
JVM) of the probe holding its 10 closed databases, A minus 2026.4: 40,960
more `bergdb.core.Cache3$Table` (655 KB, 4,096 per database) and 10
`Cache3$Table[]` of 16 KB each; nothing else of size. Each closed
database also still holds its cache's 4,096 empty `HashMap`s and their
`values()` views (about 230 KB a database, as in 2026.4). So a closed
database that the application keeps referencing holds its whole
`Cache3`, about 310 KB, of its 830 KB. This is within U10-3's aim
("holds little heap") and is no part of the failure; dropping the cache
at the close would cut it, a separate decision for 2026.6 if wanted.


## 4. The proposed fix, its size, and how it is checked

`java/src/bergdb/pubimp/PubTesterJavadocNewUsers.java`, `heapAfterGc()`:

```java
for (int i = 0; i < 3; i++) {
    // Runtime.gc(), which System.gc() calls on a JVM; on Android System.gc()
    // collects only after a finalization (bergdb 024-38, android-finding).
    Runtime.getRuntime().gc();
    Thread.sleep(20);
}
```

One changed line and a two-line comment, in a test; no product code, no
expected value changed. Checked by: before-commit.sh (the JVM, where
`System.gc()` is `Runtime.gc()`, so the test is unchanged there), and on
the emulator the test alone 30 times (expected: 0 failures, kept about
9 MB, from section 2.2) and android.sh once.

Frans decides in the morning whether it goes into commit B, or into
main after the release with android.sh's failure listed as known in
releases/2026.5 (it is a test's measurement on Android, not a bug of the
database). Other uses of `System.gc()` in `src-dev` (OneGig, BigDb,
MemPerf, the night tests) measure only on a JVM, so no other unit test
has this flaw; `PubTester.testConnectionOfEndedThreadNotKept` was fixed
in 006-18-03.

Tools, outside the repo, in `/Users/f/fl/bench/2026-11-12/andr/`:
`tools/` (env.sh, boot.sh: the emulator on port 5592; build.sh TREE:
build and d8; run.sh JAR N: the test alone N times; probe.sh J N: the
probe), `probe/andrprobe/HeapProbe.java` and its outputs (`out-A.txt`,
`out-R4.txt`, `histo-A.txt`, `histo-R4.txt`), `clone/` at A, `c2/` at
release 2026.4.


## 5. State

2026-11-13 00:25. The emulator is stopped. Done: the cause, its commit, Android only, the fix
proposed (section 4). Not done: the fix itself (not allowed tonight: no
change to the test, nothing lands before commit B). No branch was made;
the clones `/Users/f/fl/bench/2026-11-12/andr/clone` (A, `3611130c`,
detached) and `.../andr/c2` (release-2026.4) are unchanged. To continue:
make a branch from main after commit B, apply section 4's change, run
before-commit.sh, then `tools/build.sh` and `tools/run.sh JAR 30` on the
emulator (`tools/boot.sh` first; stop it with `adb -s emulator-5592 emu
kill`).
