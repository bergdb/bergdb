# 022-06-1 A device-configuration and event store on the C library

Created 2026-11-09 by Frans Lundberg.

New user u1 of BergDB's C library (bergdb 022-06), with the user kit only
(`/Users/f/fl/bench/022/userkit/`: `bergdb.h`, `c-readme.md`, the examples,
the release and the sanitizer libraries). Nothing of the library's source or
tests was read. Function names in U1-4 come from a stack sample (`sample`) of
the running application, not from the source. The application, its build and
run scripts and the reproductions are in `/Users/f/fl/bench/022/apps/u1/`.


# 1. The application

`app.c` (about 1,800 lines of C) is the store of a small device: the
configuration of devices under ikeys such as `/dev/3/cfg/ip` (converted with
`bergdb_ikey_to_bkey`), binary keys with every byte value 0x00 to 0xff (the
empty key, runs of 0x00 and 0xff, the Pub API's key forms 01 66 and 01 2f,
random keys of 1 to 40 bytes, families with shared prefixes), long keys of
255 bytes to 16 MiB, values from empty to 1.6 MiB (one of 24 MB), and an
event log: each event's key is made at the transaction's time by a key
transformation (`fe 'e' 'v'` and the time), with a counter kept by a value
transformation (the previous value plus one, no read set).

Its oracle is a model of its own: per key the list of (time, value or
delete) of every committed transaction, with the header's rules (the last
put of a key counts, a delete does not replace a put, a delete of a key
without a value writes nothing). Every get_one and get_many is compared with
the model, at the latest state and at past times.

Its commands:

- `random`: transactions of 1 to 60 puts and deletes, executed once or
  twice; refusals part way: RERUN (a read set and an older lookup time),
  LIMIT (a clock out of range), ARG (NULL keys and values in the builder),
  NOMEM (`bergdb_mem.fail_at` at random allocations of execute and
  get_many; a FAILED database is reopened and the model checked with the
  transaction there or not); random ranges (start key, inclusive, backward,
  prefix, end key, count, a stop function) and get_one at past times;
  get_trans of a value's tpos; sync; restarts with full checks at the latest
  state and at past times; set_cache_size_indicator from 1 to 200 MB; the
  budget after each step; a retain duration of 1 s (reclaim's cuts,
  NOT_AVAILABLE before the first available time).
- `kill`: a child writes and syncs; kill -9 after 0 to 620 ms; the parent
  opens, reads the counter k of the last transaction and checks that k is
  at least the last synced one, and that the whole state, and two past
  times, equal the model after k transactions (nothing half there). Values
  over 1 MiB fill the 10 MB buffer within a record; even seeds have a
  startup distance of 10 and reclaim cutting.
- `restarts`: 100 restarts, 1 to 3 transactions between them, with or
  without a sync, each open with another budget; every key and full scans
  at the latest state and at two past times after each open.
- `bigtrans`: transactions of 30,000 puts and deletes over 12,000 keys,
  with keys given several times (put then delete, delete then put), the
  model after each, at the latest state and at the time before; a restart
  and every past time.
- `sd`: the startup distance: the open's range, the stream's value at a
  restart, the setter's clamps and refusal, a set of the value in force;
  the cache size indicator's refusals.
- `longkey`: keys of 0 to 16 MiB (all 0x00, all 0xff, random), values to
  24 MB, prefix and backward reads, a restart; lengths over INT32_MAX (a
  mapped, untouched region).
- `misc`: key conversions, IN_USE from another process, argument checks,
  an open failing at each allocation (nothing live after), an open of a
  file.

`run.sh` builds both variants (`build.sh`) and runs all of it with each
(the sanitizer variant with half the steps), about 10 minutes on the loaded
F53; it exits non-zero on a wrong result. Its last run gave RUN OK
(2026-11-09, 18:21; `run.out`). The known overshoot of U1-3 is noted, not
failed (`U1_STRICT=1` fails it). `repro/` holds the reproductions;
`sh repro/build.sh` builds each in both variants.


# 2. Findings

Most severe first. No finding of data lost or wrong (section 3).

| ID | Kind | Severity | What | Reproduction (in repro/) |
|----|------|----------|------|--------------------------|
| U1-1  | bug | high   | a long key with a long shared prefix: minutes | long_key_time.c        |
| U1-2  | bug | medium | long keys: 10 times their size, disk and RAM  | long_key_memory.c      |
| U1-3  | bug | medium | a refused transaction's loads stay resident   | budget_after_refusal.c |
| U1-4  | bug | medium | a budget under the pinned: scans quadratic    | evict_scan.c           |
| U1-5  | bug | low    | pinned_bytes counts evictable bytes           | budget_after_refusal.c |
| U1-6  | API | low    | BergDB's own keys in the user's scans         | dummy_key_in_scan.c    |
| U1-7  | doc | low    | a plain and a transformed put of one key      | transform_same_key.c   |
| U1-8  | API | low    | get_trans at a wrong position fails the db    | get_trans_fails_db.c   |
| U1-9  | doc | low    | what bergdb_one.time is; the write time       | app.c (notes)          |
| U1-10 | doc | low    | RERUN for a key that nothing changed          | app.c (notes)          |

**U1-1, a long key with a long shared prefix (bug, high: a hang to the
caller).** The header takes any bkey up to INT32_MAX bytes. A put of a key
that shares a long prefix with a stored key takes time that grows with the
square of the shared prefix or faster, all in `bergdb_execute` (release
build, in memory): random keys of 256 KiB 0.006 s, of 512 KiB 0.010 s
(sharing 256 KiB), of 1 MiB 5.6 s (sharing 512 KiB), of 2 MiB 18.4 s
(sharing 1 MiB), of 1 MiB + 1 byte 24.6 s (sharing 1 MiB). A key of 1 MiB
with no shared prefix takes 0.03 s, one of 2 MiB 0.1 s; a key of 4 MiB that
shares 2 MiB with it had not returned after 5 minutes (4.5 minutes of CPU)
when it was stopped (`long_key_4mib.c`). In the application, keys of
1 MiB + 1 of 0x00 (or 0xff) after one of 1 MiB took 19.7 s (22.5 s), a
4 MiB key of zeros had not returned after more than a minute, and keys of
0x00 and 0xff over 1 MiB were taken out of the run. A device that keys
events by a long path, or a key that grows by a byte, meets it.

**U1-2, the size of long keys (bug, medium).** 16 random keys of 1 MiB with
values of 10 bytes, a cache size indicator of 10 MB: the stream is 172.7 MB;
the index is resident 167 MB, of which bergdb_stats says 191 MB is pinned,
over the 10 MB budget; the allocator's live total is 288 MB; the open after a
restart peaks at 1,224 MB (`bergdb_mem.peak_total`). The application's long
key database (60 keys, about 22 MB of keys and 35 MB of values) is 336 MB on
disk, resident 556 MB (pinned 622 MB) over a 200 MB budget, and a get_many of
its 54 pairs takes 4 to 18 s. Neither the header nor the readme says that
long keys cost this; a reader of "any bkey up to INT32_MAX" plans for the
key's own bytes.

**U1-3, the budget after a refused transaction (bug, medium).** The header:
"The index's resident bytes are kept at most this, but for what must stay",
and eviction "runs at the end of a transaction and after loads". A
transaction refused before its go point (BERGDB_LIMIT from the clock,
BERGDB_RERUN, BERGDB_NOMEM) leaves what its warm-up loaded in memory: with a
budget of 100,000 bytes, a refused transaction of 2,000 puts over keys with
5,000-byte values leaves 10.2 MB resident, through a `bergdb_sync`, until a
`bergdb_get_one` or `bergdb_set_cache_size_indicator` brings it back to
150 KB. In the application's random runs: up to 12.4 MB resident over a
budget of 100,000 bytes, and 10.8 MB over 1,000, each after a refusal, and
lasting over later syncs. The 10.2 MB is about the 2,000 previous values of
the put keys: the warm-up seems to load every put key's previous value,
which the header does not say.

**U1-4, a budget under what must stay (bug, medium).** With the cache size
indicator at 1 (legal: "under 1" is refused), a full get_many scan takes
time growing with the square of the keys: 2,000 keys 0.013 s, 4,000 0.05 to
0.08 s, 8,000 0.30 to 0.57 s, where the default budget takes 0.001 s and a
budget of 100,000 0.017 s for 8,000 keys. A stack sample puts nearly all of
it in `ev_run` called from `db_safe_point` in `dag_get_many`, once per load:
it looks as if eviction walks the index after each load and cannot reach
the budget, where a budget of 100,000 lets it stop. The first random run,
with budgets set at random, did 400 steps in more than 3 minutes for this;
the application now notes each get_many over 0.5 s (several per run, at
budgets of 1,000 and 100,000).

**U1-5, pinned_bytes (bug, low).** `bergdb_stats.pinned_bytes` is "of the
resident bytes, those that must stay". After the refused transaction of
U1-3 it is 10.2 MB, and a get_one evicts all but 156 KB of it: they did not
have to stay. And it exceeds resident_bytes: 156,072 against 149,632 after
an open, 621,957,890 against 556,215,542 in the long key database, 191 MB
against 167 MB in U1-2. A tool that reports "pinned" as the floor of the
budget is misled.

**U1-6, BergDB's keys in the user's reads (API, low).** After
`bergdb_set_startup_distance`, a full scan gives the internal key
`/#i/-dummy` with its 200,000-byte value among the user's pairs; after
`bergdb_set_retain_duration`, reclaim's keys under `/#i/dreclaim/` (three)
come in every scan that reaches 01 25 (379 such pairs in one random run's
184 scans). They count in `max_count` and the stop function sees them, so "the
first 10 of my keys" needs a filter and a loop. Section E names these keys
as BergDB's ("Do not write them"), but not that reads return them; the
application had to filter keys that start with 01 25. Either say so at
`bergdb_get_many` and section E, or leave "/#" out of user reads.

**U1-7, a plain and a transformed put of one given key (doc, low).** In one
transaction, `bergdb_trans_put(k, "plain")` and then
`bergdb_trans_put_transformed(k, ...)` with a key transformation to k2: k
gets no value, and k2 does; in the other order k2's put is the one lost.
The dedupe at the execute ("for a key given several times the last one
counts") is by the given key, before the transformation, though the
transformed put writes another key. Not wrong by the letter of the header,
but nothing warns of it: the application lost plain puts of a key that was
also the given key of its event puts (found by the model), and now gives
its transformed puts keys that nothing else writes.

**U1-8, get_trans at a wrong position (API, low).** `bergdb_get_trans` at
`tpos + 8` of a transaction (a multiple of 8, inside the stream) returns
BERGDB_FAILED: "DbFailedException: A read failed on the storage (the cause).
... Cause: StreamFormatException: Bad item byte size, ...". The database
takes nothing more until it is closed and opened; a database in memory is
lost. The header documents it ("corrupt data, which fails it"), but a
caller's wrong argument should not fail the database, and the text blames
the storage. Positions that are no transaction's could be BERGDB_ARG, as
negative ones are.

**U1-9, the times of a read (doc, low).** `bergdb_one.time` and
`bergdb_kvt.time` are "the time of the key node's entry, not the time the
value was written": in the runs they were up to about 3 ms of database time
after the write. The header says what they are not; an application that
wants an event's or a setting's write time needs `bergdb_get_trans(tpos).tt`,
which the header could say. After reclaim copies a value forward, that tt is
reclaim's transaction's, not the write's (seen with a retain duration of
1 s): the write time is then gone, which is worth a sentence too. (The
random runs note each get_one whose time is not the model's write time.)

**U1-10, RERUN without a change (doc, low).** One transaction whose read
set held a key that no transaction had written (in a database in memory,
after its re-creation) was refused: "RerunException: key hash
4819762370856219547". The STM seems to compare key hashes, so a change of
another key can refuse a transaction. The header says "refused with
BERGDB_RERUN if a transaction after the lookup time changed the key, or the
time is outside the STM's coverage"; a word that false conflicts happen,
rarely, would keep a user from hunting a bug of their own (1 in about 70
RERUNs here; `./app random - 3 600 0 0`, step 151, notes it in every run).

Smaller remarks, no finding: the header's many item references (012-03,
015-87, 005-70) mean nothing to a user and make the rules long to read; a
transaction cannot be cleared for reuse (free and new); `bergdb_open` with a
startup distance under 10 is refused with BERGDB_ARG and leaves no
directory, as documented.


# 3. What went well

- **No wrong data.** Every get_one and get_many matched the model: in one
  run.sh, about 810,000 get_one and 3,100 get_many checks in the random,
  restart and bigtrans runs (and more in the sd and longkey runs), at the
  latest state and at past times, over 150 restarts and more within the random
  runs, with startup distances of 10, 1,000, 400,000 and 50 MB at the
  creation, budgets of 1 byte to NO_EVICT, reclaim cutting with a retain
  duration of 1 s (past times before the first available one were
  BERGDB_NOT_AVAILABLE, never wrong), transactions of 30,000 puts and
  deletes with keys given several times, and transactions executed twice
  and with transformations (the event keys and the counter right after
  every commit and every re-execution).
- **Refusals leave the database as it was.** RERUN, LIMIT (a clock of -1 to
  -100 or over 2^56), ARG in the builder and NOMEM before the go point never
  changed the model; NOMEM after the go point failed the database
  (BERGDB_FAILED with the cause, "OutOfMemoryError: a KeyModSet entry",
  "the node table"), and the reopened database held the transaction whole
  or not at all, each time.
- **kill -9.** 72 kill cycles per run.sh (48 release, 24 sanitizer) and
  about 50 more by hand, at 0 to 620 ms, also within opens, with records
  torn by a full buffer and with reclaim deleting front files: every synced
  transaction was there, the state equalled the model after exactly the
  recovered count (nothing half there), and every open succeeded.
- **Sanitizers and leaks.** No AddressSanitizer or UBSan report in any run;
  `bergdb_mem.live_total` was 0 after every close, and after every refused
  open (an open failed at each of its allocations in turn).
- **Limits.** Keys and values of 2^31 bytes are BERGDB_ARG at every call
  (put, delete, key_read, get_one, get_many's start, prefix and end key),
  without a read of the bytes; the cache size indicator 0 and -7, a sync at
  the end of the stream or at level 30, a lookup time of -1 are refused. A
  value of 1,900,000,000 bytes and one of INT32_MAX are taken by the put and
  refused at the execute with BERGDB_LIMIT, with nothing written, and the
  next transaction commits.
- **The header** is precise where it matters: ownership, the go point, what
  a failed database still does, durability, and what each call refuses.
  Every surprise above was a gap, not a contradiction, but U1-3 and U1-5.
