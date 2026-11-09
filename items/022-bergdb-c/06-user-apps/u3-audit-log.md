# 022-06-3 An audit log with retention, as a new user of the C library

Created 2026-11-09 by Frans Lundberg.

User u3 of BergDB's C library (bergdb 022-06), with the user kit only
(`/Users/f/fl/bench/022/userkit/`: `bergdb.h`, `c-readme.md`, the examples and
the two built libraries of int.git's 2026.4 at 391c3cf5). I read no
implementation or test of the library. The scenario: an append-heavy audit log
with retention, read at past times. (The session saved this text from u3's
final message; u3's own write of the file was refused by the harness.)

# 1. The findings

Most severe first. The files are in `/Users/f/fl/bench/022/apps/u3/`.

| ID   | Kind | Severity | What                                                     | Reproduction |
|------|-----|--------|----------------------------------------------------------|--------------|
| U3-1 | bug | medium | Reclaim stops cutting a log keyed by time; the dir grows | repro_fifo.c |
| U3-2 | bug | medium | One-record transactions write records of MBs, growing    | repro_fifo.c |
| U3-3 | doc | low    | get_trans reads transactions before first_available_pos  | auditlog.c   |
| U3-4 | API | low    | A range's prefix does not position the read: 0 pairs     | misc.c, 5    |
| U3-5 | doc | low    | A scan from the first key returns BergDB's own keys      | misc.c, 6    |
| U3-6 | doc | low    | reclaim_iteration_count counts since the open; not said  | misc.c, 7    |
| U3-7 | API | low    | A negative lookup time: NOT_AVAILABLE, taken, or ARG     | misc.c, 4    |
| U3-8 | API | low    | No transaction by time, and no walk of the transactions  | auditlog.c   |

No wrong value was read, nothing synced was lost, and the sanitizer builds
reported nothing (section 3).

## 1.1. U3-1: reclaim stops cutting a log keyed by time

**What.** An audit log whose records are keyed by their time, the oldest
deleted as new ones come (a FIFO of keys in time order), with a retain
duration of 5 to 40 s. Reclaim cuts for a while, then stops: the first
available position stays where it is for minutes of the clock, while the
stream grows, and the directory with it. The live data is under 1 MB.

**Expected.** `bergdb_set_retain_duration`: "reclaim removes what is older";
the readme, section 9, point 9: a cut "at most one per quarter of the retain
duration, and only when the stream has grown by twice the startup distance
since the last iteration began", "so the directory stays within what the
retention needs".

**Seen.**

- `repro_fifo.c` (one key per transaction, `/t/` and the time in 16 hex
  digits, the record 1,024 back deleted; startup distance 2 MB; retain
  duration 20 s; 300,000 transactions, about a minute): 16 cuts up to
  transaction 240,000, then none. At the end the first available time is
  129.7 s back, and the directory grew from 65 MB to 115 MB in the last 60,000
  transactions. It prints "NOT CUT" and exits 1 when the first available time
  is more than four retain durations back. The same at 60,000 transactions
  cuts as expected (so the run needs its length).
- `repro_growth.c DIR 60000 2000000 0 qo` (the same FIFO, a clock of 1 to
  2 ms per transaction, retain 20 s from 13.5 s and 5 s from 49.5 s): no cut
  at all in 90 s of the clock; the directory 70 MB. With per-source keys as
  well (`q`, 100,000 transactions): no cut in 127 s with 20 s and then 5 s;
  230 MB. With startup distance 10 MB (`q`): one cut at about 60 s, then none
  for 90 s; the first available time 120 s back with 5 s; 188 MB.
- Without the keys by time (`repro_growth.c DIR 40000 2000000 0`: 16 per-source
  FIFOs of 64 records): a cut every 4 MB, the first available time about 8 s
  back with 5 s, the directory about 10 MB. With the time hashed in the key
  (`qh`, or `KEYS=hashed repro_fifo`): cuts go on.
- The application (`auditlog.c`, startup distance 2 MB, 100,000
  transactions, a restart every 2,000 to 6,000): the first available position
  stayed at 607,800,336 from transaction 61,258 (226.8 s of the clock) to
  99,000 (364.9 s), 144.7 s back with a retain duration of 5 s and then 40 s;
  the directory reached 1.84 GB for a stream of 2.4 GB. The application's
  "not cut" check fails 18 times, and `run.sh` exits 1. Restarts do not cause
  it (the same with `NORESTART=1`), nor do reads (the same growth with
  `NOCHECK=1 NORESTART=1`). An open sometimes makes a cut that was due: the
  run's last restart brought the first available time to 44.9 s back.

No data within the retention was lost: in every check, the first available
time was within the retain duration, and every read at or after it matched the
model. The cost is the disk: a log with retention grows without a bound.

## 1.2. U3-2: one-record transactions write records of MBs

**What.** Under the same FIFO of keys in time order, now and then one
transaction of one put and one delete writes a record of MBs. These records
grow with the run, while the live data stays constant (1,024 records, 300 KB).

**Seen.** `repro_fifo.c` prints each record over 1 MB: 1.07 MB at transaction
45,614, 1.39 MB at 59,020, 2.37 MB at 99,235, 3.09 MB at 129,220, the largest
5.1 MB; one every 7,000 to 15,000 transactions. With the time hashed in the
key, the largest record of 60,000 transactions is 242 KB. In the application
with startup distance 1 MB: 250 MB of records in 1,000 transactions of 1 to 4
records, the largest 3.5 MB; with 400,000 (the setter's minimum), one of
8.5 MB. `repro_growth.c ... q` (2 MB): 17.4 MB at transaction 85,477.

The index in memory grows with every transaction as well (`probe_dag.c`, which
counts the lines of `bergdb_debug_print`; the same FIFO with 5 s): 5,485 key
nodes and 20,251 values after 20,000 transactions, and 22,134 and 80,554 after
80,000. Meanwhile 1,024 keys are live and reclaim had cut the stream before
37.9 MB; resident bytes 45 MB. After a restart: 1,309 key nodes and 2,924
values in memory. I cannot tell from outside whether this is the history that
the large records rewrite. A likely link with U3-1 is that both need keys in
time order.

For a user this means latency spikes (a transaction writes 5 to 17 MB), and a
stream that grows much faster than the data (the application: 2.4 GB of stream
for 124,000 records of 80 to 480 bytes).

## 1.3. The low findings

- **U3-3, doc.** `bergdb_get_trans` of a transaction before
  `first_available_pos` succeeds, with the right content, while its file is
  still there (41 times in the release run). The header says
  `BERGDB_NOT_AVAILABLE` when "reclaim has removed the transaction", while
  `bergdb_get_one` refuses any time before `first_available_lookup_time`.
  Say which holds: refused before `first_available_pos`, or readable until
  its file is deleted.
- **U3-4, API and doc.** `struct bergdb_range`'s `prefix` is only a stop
  condition. A range with a prefix and no start key reads from the first key
  of the database and stops at once: 0 pairs, no error (`misc.c`, 5). Say at
  the field to set `start_key` to the prefix, or make a prefix without a start
  key start there.
- **U3-5, doc.** A scan from the first key returns BergDB's own keys
  (`/#i/dreclaim/-settings.txt` after `bergdb_set_retain_duration`, and three
  such keys while reclaim runs; `misc.c`, 6). Section E names them, but
  `bergdb_get_many` does not say that a scan of all keys includes them.
- **U3-6, doc.** `bergdb_stats.reclaim_iteration_count` restarts at 0 at each
  open (`misc.c`, 7). `transaction_count` says "since the open"; this field
  does not.
- **U3-7, API.** A negative lookup time: `bergdb_get_one` and
  `bergdb_get_many` refuse it with `BERGDB_NOT_AVAILABLE`;
  `bergdb_lookup_time(db, -1)` returns `BERGDB_OK` and -1;
  `bergdb_trans_lookup_time(t, -1)` returns `BERGDB_ARG` (`misc.c`, 4). The
  header documents none of the first three. One rule (`BERGDB_ARG`) would be
  simpler.
- **U3-8, API.** The API cannot find the transaction at or before a time, step
  from a transaction to the next one, or read the versions of one key within
  the retention. The application keeps its own index by time,
  `/bytime/TIME/...`, through a key transformation that puts the
  transaction's time into the key; that works well.

# 2. The application

`auditlog.c` (about 880 lines) is an audit log of 16 sources. Each transaction
appends 0 to 4 records; for each record it puts `/log/sNN/RRRRRRRRRR`,
`/latest/sNN` and, through a key transformation, `/bytime/TIME/sNN/R...`, and
`/count` through a value transformation. Each source keeps its 64 newest
records; older ones are deleted, so the live data is bounded and the history
is what retention removes. The retention schedule changes the retain duration
(forever, 20 s, 5 s, 40 s) and the fraction (0.1, 0.5) during the run, some
just before a restart; a restart comes every 2,000 to 6,000 transactions; the
startup distance is 2 MB. The oracle is a model of every transaction (time,
position, records, deletes), checked after each restart and every 1,000
transactions at the latest state and at past times (the first available time
and the unit before it, the retention's horizon, before the first transaction,
the last transaction's time and after it, -1, random times). `misc.c` checks
the edges; `crash.c` kills the log without a close (8 rounds of `_exit` or
`SIGKILL`, a sync every 700 transactions, cuts during the run); `run.sh`
builds against both libraries and runs it all (about 4.5 minutes, up to 2 GB;
it exits 1 today, from U3-1).

# 3. What went well

- **Time travel is exact.** 8,620 checks (each 18 to 80 reads) matched the
  model across 38 restarts.
- **Retention never took data within the retain duration**, also after a
  decrease from 20 to 5 s and an increase from 5 to 40 s; every read before
  the first available time (1,630) was refused with `BERGDB_NOT_AVAILABLE` and
  a clear text with the times in UTC.
- **Settings in the stream** survive restarts; a setter of the value in force
  writes nothing.
- **Transaction times** were always later than the last one's, also with the
  clock an hour back across a restart.
- **Durability.** In `crash.c`'s 8 rounds, no synced transaction was lost, and
  what remained was a prefix.
- **Sanitizers.** No report from any sanitizer build.
- **Determinism.** With the test clock, reruns gave the same output.
- **The header** answered nearly every question.
