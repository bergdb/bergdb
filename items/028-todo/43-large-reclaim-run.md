028-43. Change: a long functional run with large reclaim
======================================================

Status: done. Kind: Change. Frans: none.
Created 2026-11-21 by Frans Lundberg.

What: `java/stress/LargeReclaimRun.java` and `java/stress/large.sh`, a
functional history at 10 million keys with reclaim, historical reads,
bounded kept bytes and recovery; a new step in `java/week.sh`.

Why: the functional checks cover small and medium databases for minutes.
Long histories at large size add coverage of reclaim's pace, whole-file
cuts, retention and recovery. 028-42 found that a first cut at 10 million
keys needs a complete iteration, its retention and the durable waits;
that timing scenario ends at its first cut.

Frans: none.

Done when: quick and full runs pass, the full run at 10 million keys
checks many physical cuts, bounded kept bytes, historical reads, two
clean restarts, a child killed during writes and full oracle scans;
`java/before-commit.sh` prints `BEFORE COMMIT OK`. Any database difference
keeps its seed and a reproduction; database code is unchanged. Changes
remain uncommitted in the task's clone (2026-11-21).

First step: read 027-13's reclaim and retention rules, 028-42 and the
existing stress runners; check free disk before creating data.


Workload and oracle
-------------------

The full run fills 10,000,000 keys, each an eight-byte key and a 64-byte
value, in batches of 100. Then 40 epochs each update every key once,
four keys per transaction: 100,000,000 history transactions. The quick
run has 1,000,000 keys and 16 epochs (4,000,000 transactions). The seeded
affine permutation visits every key once per epoch; its inverse gives
the version of any key at any transaction number. Every value contains
its key and version and deterministic check bytes. About one version in
17 is a delete, followed by reinsertion. The fresh fill has every key.

The oracle stores no value history. Its bounded length ring uses eight
bytes per retained transaction, about 2 MB in full mode. A temporary
integer array checks the arithmetic oracle against an independent small
history before the run. Planted wrong and missing values and a substituted
snapshot time must be found.

The simulated clock advances 10,000 units per user transaction; the user
transaction time is checked against that exact schedule. Retention is
one tenth of an epoch, 250,000 user transactions in full mode (250
seconds of logical time); reclaim uses its default fraction at commits.
There is no maintenance drive or wall-clock pacing. Fixed work decides
a pass; the time printed is information. Reader joins, child readiness
and process exit have generous hang guards, with a 12-hour JVM guard.
The capacity controller stays on with a 3 GB resident cache in full mode
and 300 MB in quick mode, inside the runner's 10 GB and 3 GB heaps.

Each block of at most 16,384 writes overlaps a reader's 512 point reads
and eight scan pages, forward and backward. Reads mix latest and old
times, with half targeting keys that changed near the snapshot. Every
result is checked at its actual lookup time; scan pages check gaps and
order too. Historical requests must report the requested lookup time,
which is always at or before an already completed transaction; the test
refuses a silently substituted latest snapshot. A concurrent expired
read is accepted only below the actual available frontier. Three
historical scans pause after their first row
while writing continues, then resume after a physical cut has overtaken
their snapshot. They must finish with the oracle's rows or expire with
the documented exception. At each epoch, with writing paused, checks require
successful reads at the retention boundary, halfway through retention
and at the available frontier, and refusal of both get and scan at the
frontier minus one. A latest read then checks that refusal left the
database usable. Each epoch syncs.


Space envelope
--------------

Let L0 be the filled stream's length. G3 (024-30; 027-13, section 4)
uses `logicalKept - retainedUserBytes <= 6 L0`. Here H_R is all stream
growth over the last R user transactions and one extra transaction:
it includes every retained user record and may include internal records.
Thus the same workload envelope gives the conservative check
`logicalKept <= 6 L0 + H_R`. H_R comes from a ring of stream positions,
not a time-based estimate. Every user transaction after the first
logical cut checks it, including across clean restarts.

FileStream is capped at 2 GB per file. Its physical first position can
lag the logical first position by less than one file, so
`physicalKept <= 6 L0 + H_R + 2 GB`. The harness checks that too. This
is a functional acceptance envelope derived from G3, not a proved general
bound of reclaim. Bounded sawtooth growth between cuts is expected;
monotone decrease is not required. A separate, fixed retained-growth
budget requires `H_R <= 2 L0` once the ring has a complete window. Together
these give `logicalKept <= 8 L0` and `physicalKept <= 8 L0 + 2 GB`,
absolute bounds independent of the history's length, checked after every
user transaction after the first cut, also while the ring is being filled.
The fresh fill must make that absolute bound less than 40 GB. The history
must append at least 12 L0 and observe at least half as many physical cuts
as epochs (at least six). Per-epoch lengths and peaks expose the settled
envelope over time.

The script requires 45 GB free for full mode. The harness checks actual
file sizes and free disk at every epoch and crash-child sync, and checks
the physical kept size after each user transaction, stopping
before the 40 GB cap. The output directory is new for each run; successful
data is removed by default, while a failure always keeps its data.
week.sh moves a failed run, including its data, journal and build, out
of its temporary clone before that clone is removed.


Recovery
--------

Two clean restarts at one third and two thirds of the history check the
persisted retention and nondecreasing reclaim frontier. Each scans every
key against the oracle and repeats old reads. The final history is synced
and closed before a child JVM opens it. The child journals PREPARE before
each batch and journals and forces SYNC only after database sync returned.
After a fixed number of writes and several completed syncs, the parent
kills it with SIGKILL, as the existing kill-restart harness does. An
incomplete last journal line is unacknowledged.

Recovery requires the sequence marker to name a prefix between the last
SYNC and the last PREPARE. A full scan checks every key against precisely
that prefix: missing synced batches, an extra operation and a half-applied
batch fail. This checks process loss with OS caches intact, not power loss.
Each retained transaction from the child's history is also checked at its
own snapshot: its prefix marker, its four keys and those keys just before
the transaction. Every retained SYNC snapshot's marker is checked too,
so later overwrites cannot hide a lost historical batch.
The recovered database is written again and scanned in full at the end.


Runs
----

Quick and full passed on the same harness source (2026-11-21). Its
SHA-256 is
`e1dd086d303c052635d12b7e3c28f8d9f7cca6a3c1988e64e9d15f42e830dd99`.
The database source is unchanged at `40cb9ae9`. Successful data was
deleted; logs, journals and each run's exact build remain.

Quick: seed 20261124, 1,000,000 keys,
4,000,000 main-history transactions, 39 observed main-history physical
cuts, three scans across cuts, three allowed read expiries, two clean
restarts and one SIGKILL recovery. Its final scan checked all 1,000,000
keys; 65,749 retained crash-history transactions and all 65 recorded sync
snapshots were checked. Duration 208.172 s. Fresh length 190,979,192
bytes; maximum logical kept 916,149,784 and physical kept 982,565,736;
final physical kept 790,428,576. Log:
`java/build/large/quick-20261124-20261121T103043/out.txt`.

Full: seed 20778, 10,000,000 keys, 40 epochs and 100,000,000 main-history
transactions. The run began at 10:36:10 CET and ended at 11:55:19 CET,
exit status 0; harness duration 4,748.499 s (79 minutes 8.499 seconds).
It observed 89 physical cut advances and appended 185,944,336,336 bytes
after the fresh fill of 2,106,983,240 bytes. Peak logical kept was
7,470,972,616 bytes and peak physical kept 7,931,360,504, below the
fixed bounds of 16,855,865,920 and 18,855,865,920 respectively.
The free-disk admission recorded 69,600,000 KB. The 10 GB Java heap
and 3 GB resident cache kept the full run within its memory budget.

The following are epoch-end samples; GB is decimal. The stream length
is a cumulative position, including bytes already removed from disk.

| Epoch | Transactions (M) | Cuts | Stream GB | Logical kept GB | Physical kept GB |
|---|---|---|---|---|---|
|  1 |   2.5 |  1 |   6.309 | 4.202 | 4.309 |
|  5 |  12.5 |  7 |  24.938 | 5.316 | 5.438 |
| 10 |  25.0 | 17 |  48.100 | 7.157 | 7.600 |
| 20 |  50.0 | 42 |  94.655 | 4.874 | 5.155 |
| 30 |  75.0 | 65 | 141.553 | 6.391 | 6.553 |
| 40 | 100.0 | 89 | 188.051 | 5.707 | 6.051 |

The physical peaks over successive ten-epoch blocks were 7.931, 7.725,
6.892 and 6.842 GB: the kept stream settled while cumulative length
continued to grow. The envelope was checked after every transaction,
including the peaks between these samples.

Clean restarts at prefixes 32,500,000 and 65,000,000 passed full scans,
retention checks and frontier refusals. Open times were 1.530 s and
1.277 s, with full scans in 16.954 s and 17.064 s. Three historical
scans crossed physical cuts. Across all concurrent reads, two allowed
expiries were recorded; every completed scan checked its rows. Overall,
3,671,991 point reads (2,887,080 historical) and 49,055 scan pages were
checked, in addition to the full scans.

The child was killed with exit status 137 during writing. Its journal
offered prefix 100,067,197 and acknowledged sync through 100,066,560;
recovery returned exactly 100,066,560. Open took 1.288 s and its full
scan 16.963 s. All 66,561 retained child-history snapshots and all 66
sync snapshots, including the parent's handoff, passed. Writing resumed
for 16,384 transactions. The final scan checked every key at prefix
100,082,944; logical kept was 5,867,920,224 bytes and physical kept
6,212,078,136. Log:
`java/build/large/full-20778-20261121T103604/out.txt`.

The final gate, run from `java/` as `sh before-commit.sh`, printed
`BEFORE COMMIT OK (66 s)`: 1,738 unit tests, 89 f-tests and 14 demos.
Its output is `java/build/large/before-commit-final.txt`.
Shell syntax checks and both weekly dry runs passed, with the day's
seed passed to the new step. The full weekly suite was not run.

The first full-size attempt, seed 20778, disabled eviction and ran out
of its 10 GB Java heap after 5,844,918 history transactions (420.558 s),
in `KeyNode.growCapacity` during a user write. It had two observed physical
cuts and no value mismatch. Its data and exact build are kept in
`java/build/large/full-20778-20261121T095627/`. The harness now uses the
capacity controller's bounded cache. This is a harness configuration
failure; it is not evidence of a wrong database result. Recovery of an
APFS copy with the bounded cache passed a full scan of all 10 million
keys at prefix 5,844,918 in 47.479 s. The original data was kept
unchanged; the temporary recovery copy was deleted.

A quick preflight on seed 20261124 found a harness bookkeeping fault:
the crash child's length ring had no position for its starting prefix.
After one retention window, that made H_R include the inherited kept
stream. The starting position is now installed in the ring when a child
or a recovered writer begins. The failed run is kept in
`java/build/large/quick-20261124-20261121T100646/`; no wrong database
value was found.

No wrong database result was observed in the completed runs. Neither
harness fault required a change to database code.


Log
---

2026-11-21. Registered and taken by session large-reclaim-20261121.
The test is functional and belongs only
to week.sh; the task requires Kind Change and an uncommitted clone.

2026-11-21. Done: quick and the 10-million-key full run passed on the
same harness source; 89 main-history physical cuts in the full run,
bounded kept bytes, historical reads and clean and abrupt recovery.
The final gate printed BEFORE COMMIT OK. Changes remain uncommitted.
