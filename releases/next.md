Notes for the next release
==========================

What the release notes of the next release after 2026.4 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.4](2026.4/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.4 (2026-11-11), whose notes hold what was there.


### Core API

* **A reclaim step makes dirty only the index nodes on the paths of its
  own puts** (bergdb 024-07, option A; on `main` in `a780b957`). The last
  step of each reclaim iteration made dirty every index node after its
  scan's last key (`Db.touchRange`, a key range with no end): with keys in
  time order (a queue, a log) the whole index, pinned in memory and then
  written in one record. At 10M keys in time order that was 772,454 nodes,
  a commit of 20.6 to 22.3 s under the write lock, 0.67 to 2.31 GB
  resident against a cache budget of 0.2 GB, and a record of 206 MB; at
  1M keys 1.6 s and 17 MB (024-07, sections 2 and 8). Two faults of 2026.4
  and before are gone with it (024-07, section 3; 2026.4's Known issues):
  * with a small heap the step ended in `OutOfMemoryError` inside a
    user's commit and failed the database (a queue of 1M keys, a heap of
    256 MB): it now runs its 40,000 transactions, the slowest commit 37
    ms;
  * from about 104M keys in time order the step's nodes passed the record
    limit, 2^31 - 9 bytes, the startup position stopped for good, no cut
    was made again, and the stream and the heap grew without end, without
    an exception (reproduced with the limit lowered,
    `Reclaim.Tester.testLastStepWithinRecordLimit`; not run at that
    size).

  Now a step follows the path of each key it puts (`Db.touchPaths`) and
  no key range. At 10M keys in time order the last step makes 5 to 15
  nodes dirty, the largest record is 29 kB, the slowest commit 78 ms, and
  a transaction writes 9.7 % fewer bytes (6 % at 100,000 to 1M keys);
  reclaim's iterations, steps and cuts are as before (024-07, section 8).
  The cut's correctness without the range: 024-07, section 4 (the Lean
  theorems T-COVER and T-LATEST; it rests on a delete's unlink, 023-07,
  section 5.1). The record format is unchanged; the stream's bytes of a
  database with reclaim on change. StreamDigest's configurations that
  change and the entry that keeps their digests before and after: not
  yet named (024-07, section 10).
* **In a transaction's builder the last call on a key wins, put or
  delete** (bergdb 024-10, R1; Frans, 2026-11-11, 07:08). Of the calls of
  `Trans.Builder` on one key as written, `build()` keeps the one made
  last, a put with its value or a delete; the earlier ones are gone. In
  2026.4 and before a put won over a delete whatever their order (015-40):
  `put(k, 1)` then `delete(k)` kept the put, and now deletes `k`. A
  transaction that names no key twice writes the bytes it wrote before
  (StreamDigest `all`, 48 of 48 digests identical; 024-10, section 8). The
  Pub API's `w()` and `rw()` already kept the last call on a key as
  written (015-40, 015-41).
* *For 024-16 to fill: KVs that key transformations make one key.*


### Known issues and limits

* **Fixed: reclaim with keys in time order** (bergdb 024-07; 2026.4's
  Known issues, its first entry): the heap that ran out in a user's commit
  and the record limit that stopped reclaim at about 104M keys (Core API,
  above).
