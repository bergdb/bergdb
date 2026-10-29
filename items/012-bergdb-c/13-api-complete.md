012-13. Task: the rest of the API, and durability
=================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done, 2026-10-29 03:17** (started 02:16):
"Done when" holds (6.6) but for item 4's second close and calls after a
close, which a C handle cannot have (Q2, recommended A, as implemented);
`C BEFORE COMMIT OK (144 s)` with the examples run; `cross.sh full` OK.
Approved with 012-01 by Frans's go (012-01, 9.1).
Phase E (012-01, section 8). Effort: high. After: 012-11, 012-12.


# 1. The goal

Every function of `bergdb.h` (012-03) implemented, tested and described,
and the durability of a C database written down and tested: what a user
of the C clone can rely on.

Done when:

1. Every function of `bergdb.h` exists and has a functional test, and the
   table of 012-03 says for each of `Db`'s public methods what C has.
2. **Settings and status**: the startup distance (with Java's clamp and
   dummy transaction, 005-53), the cache budget while running (005-52),
   the retain duration, the internal fraction, and every status value of
   012-03's table, equal to Java's on the same database where Java's is
   not a matter of timing (the stream length, the counts, the first
   available time and position, the startup distance).
3. **Durability**, written in the C directory's `readme.md` and tested:
   what is durable after `execute`, after `sync` at each level, and after
   close; the buffer's size; `F_FULLFSYNC`; the durable length; a write or
   a force that fails fails the database (P7), and what `sync` and close
   do then.
4. **Close**: writes, forces, frees everything; a second close is
   harmless; calls after close get STATE.
5. **Examples**: C's `CoreDemo`, which prints the same as Java's on each
   other's databases; and the `getMany` example of 012-03.
6. **The API's text**: the header's comments checked against the code,
   and a short guide in `readme.md` (open, write, read, close, errors,
   one caller at a time).


# 2. Read first

* 012-03 (the design and the table); 012-01, 4.3; `Db`'s Javadoc of each
  method; `docs/levels.md`, section 3; 011-07 (Java's durability) and
  005-44 (what a sync waits for).


# 3. The work

1. A list of `bergdb.h`'s functions with their state (done, tested,
   missing); finish the missing ones.
2. The durability tests: kill the process (`kill -9`) after `execute`,
   after `sync`, and during a write, and check what a restart finds
   (C alone; the power-loss side is 012-14's).
3. The examples and the guide.


# 4. Tests

The functional tests (done item 1); the durability tests; the examples in
the gate.


# 5. Notes

* Small API, as Java's (P12): no function beyond 012-03's design without a
  note in this file of why.


# 6. Progress

## 6.1 The log

* **2026-10-29 02:16, start.** In the clone `/Users/f/fl/bench/012/13-api`
  (of `main` at `ca9e583`), beside 012-12 (the memory budget, in
  `/Users/f/fl/bench/012/12-memory`), which changes eviction, the
  budget's setter and `bergdb_stats`' resident bytes; this task keeps out
  of those and tests the setter's API only. Java's reference: `main` at
  `ca9e583` (`java/` unchanged by 012).
* **02:20, the missing functions** (`fe430f1`): of `bergdb.h`'s 33
  functions, only `bergdb_debug_print` and `bergdb_debug_check` were
  missing. Both in `api.c` (functions of its own, nothing in `db.c`):
  Java's `Dag.visitMemoryNodes` by an explicit stack (a chain of top nodes
  in memory can be long; 012-01, 4.5, point 8), marks cleared at its end;
  the check is Java's `KeyNode.check` of each key node and C's recount of
  every object's holders (`db_recount`). **The examples** link and run:
  `build.sh` builds `core_demo` and `get_many_prefix` with `include/`
  only on their path; `examples/compare.sh` checks `get_many_prefix`
  against Java's output in its comment and runs `core_demo` and Java's
  `CoreDemo` on each other's databases; a gate step `examples`.
* **02:27, settings and status** (`9ecc1fe`): `test/func/f_settings.c`.
  `settings_and_status_as_java` runs `test/func/java/StatsProbe.java`'s
  sequence (150 transactions with deletes, reads, `getMany`s, reclaim
  with a retain of 1 s, `setStartupDistance(10)` clamped to 400,000 with
  its dummy, the same value again, the other three setters, a sync, a
  restart, a sync) and compares Db's thirteen getters at nine points with
  Java's lines: equal, every one (the stream length, the durable length
  after a sync and a start, the last valid meta block's transaction, the
  first available time and position, reclaim's iterations, the three
  counts, the startup distance, the cache size indicator, the retain
  duration, the internal fraction). The probe ran twice on Java with the
  same lines. Then the setters' checks and clamps, also on a failed
  database; the open's checks; the error names and texts; the key
  conversions; the test clock; sync's levels and positions; the clock's
  times; the debug calls before and after a restart and on a failed
  database; close with objects not freed; and every call of a database
  from its own callback, the close among them: `BERGDB_STATE` and nothing
  done.
* **02:31, durability** (`577504c`): `test/func/f_durable.c` (6.4).
* **02:33, the header's text** (`256b4e7`): `bergdb.h`'s comments read
  against the code; changed where they said less than the code does
  (03-c-api.md's progress lists them). One code fix: `bergdb_get_one` set
  `*out` before a `BERGDB_NOMEM` of its buffer; now on success only, as
  the header says.
* **02:36, the guide** (`05674b6`): the C directory's `readme.md`, section
  8 (the API in short) and section 9 (durability).
* **02:37, the documents left to the conductor**: 05-cross-harness.md,
  6.5 (the sets and the comparison as `cross.sh` is at 012-11's end), and
  03-c-api.md's progress (012-11's comment of
  `bergdb_set_retain_duration`, and 012-13's).
* **02:39, the gate** on `05674b6`: `C BEFORE COMMIT OK (148 s)`, with
  21 functional tests (28,006 checks) in both builds, no leaks, the quick
  cross set (22 workloads, 93 crash cuts, 85 corrupt variants, 2 in
  turns), writecheck, and `EXAMPLES OK`. The gate took 130 s at 012-11's
  end; the functional tests add about 4 s a run, three runs.
* **02:39, C on Java's databases, by hand**: C's open of the directory
  that `StatsProbe` left (Java's, after its last sync and close) reports
  Java's values (a scratch program, kept nowhere); and with
  `BERGDB_STATS_OUT`, the directory of C's run of the sequence equals
  Java's file for file, byte for byte (`cmp`).
* **02:41, 40 rounds of random kills** (`BERGDB_DURABLE_ROUNDS=40`, the
  release build, 22 s): every restart a whole prefix with every synced
  transaction; 12 rounds ended with a torn record, 13 found transactions
  beyond the last sync.
* **02:40, `cross.sh full C=build/tools-full`** started (a copy of the
  test build), as `bergdb_get_one`, which `bergdb-run` calls, changed;
  012-12's own full run in its clone at the same time.
* **03:13, `cross.sh full` OK**: `CROSS full OK: 446 workloads, 1368 crash
  cuts, 498 corrupt variants, 6 in turns, the planted difference at 1164
  was found and explained; side B: .../build/tools-full; 1991 s`; side B's
  runs all C's (181 with reclaim), its 892 dumps all C's; no difference.
* **02:45, the merge with 012-12 tried** in a scratch clone (6.7).
* **03:16, the gate** on the last code (`af4e73b`): `C BEFORE COMMIT OK
  (144 s)`: 340 unit tests, 21 functional (28,006 checks) in both builds
  and under `leaks`, the quick cross set, writecheck, `EXAMPLES OK`.
* **03:17, done.** Next: the conductor merges with 012-12 (6.7) and gates
  the merged tree; Frans answers Q2 (and 11-reclaim.md's Q1); 012-14
  takes power loss, with this task's kill tests as its start.

## 6.2 The functions of `bergdb.h`

All 33 exist, and each has a functional test (`test/func/`); every one
is also called by the examples or `bergdb-run`, but for the debug calls
and the rare setters. "Java" is what the test compares with Java's own
output (the cross sets, through `bergdb-run`; `StatsProbe`; the
examples).

| Function | State | Functional tests | Against Java |
|---|---|---|---|
| `bergdb_errmsg`, `bergdb_errname` | done | `settings_errors_and_keys`, `api_refusals`, `durable_*` | Java's exception names in the texts (cross sets' `error=`) |
| `bergdb_test_clock_time`, `_set` | done | `settings_errors_and_keys`, all | |
| `bergdb_options_init` | done | `settings_open_checks` (Java's defaults) | |
| `bergdb_open` | done | `settings_open_checks`, `start_*`, `durable_*`, `api_*` | cross sets |
| `bergdb_close` | done | `settings_close_and_callbacks`, `durable_write_fails`, all | |
| `bergdb_ikey_to_bkey`, `bergdb_bkey_to_ikey` | done | `settings_errors_and_keys` | vectors (012-04) |
| `bergdb_trans_new`, `_free`, `_put`, `_delete` | done | `api_create_and_read`, all | cross sets |
| `bergdb_trans_put_transformed` | done | `api_transformations` | |
| `bergdb_trans_key_read`, `_lookup_time` | done | `api_refusals` (RERUN) | |
| `bergdb_execute` | done | all | cross sets |
| `bergdb_read_new`, `_free` | done | all | |
| `bergdb_get_one` | done | `api_create_and_read`, `durable_*` | cross sets, examples |
| `bergdb_range_init`, `bergdb_get_many` | done | `api_create_and_read`, `api_refusals`, `settings_errors_and_keys` | cross sets, `get_many_prefix` |
| `bergdb_get_trans` | done | `api_create_and_read`, `api_refusals`, `settings_setters`, `api_reclaim_directory` (a removed transaction: `BERGDB_NOT_AVAILABLE`) | `core_demo` (C's dumper reads transactions through its own module, `sdb`) |
| `bergdb_sync` | done | `settings_sync_and_times`, `durable_*` | |
| `bergdb_current_time`, `bergdb_lookup_time` | done | `settings_sync_and_times`, `api_create_and_read` | cross sets (`now`) |
| `bergdb_set_startup_distance` | done | `settings_setters`, `settings_and_status_as_java` | `StatsProbe`, cross sets (`setsd`) |
| `bergdb_set_cache_size_indicator` | done (the API; eviction is 012-12's) | `settings_setters`, `settings_and_status_as_java` | `StatsProbe` |
| `bergdb_set_retain_duration`, `bergdb_set_reclaim_internal_fraction` | done | `settings_setters`, `f_reclaim.c` | `StatsProbe`, cross sets |
| `bergdb_stats` | done | `settings_and_status_as_java`, all | `StatsProbe`, cross sets (`status`) |
| `bergdb_debug_print`, `bergdb_debug_check` | done (012-13) | `settings_debug`, `settings_debug_after_start`, `durable_*` | |

03-c-api.md, 6.2's table says for each of `Db`'s 45 public methods what C
has; every C counterpart there is now in this list.

## 6.3 Decisions

* **D1. One open of a directory per process** (09-write-path.md, 6.4,
  its option A, as recommended there). C keeps Java's lock (an `fcntl`
  lock of `bergdb.lock`'s byte at 2^62), which refuses another process's
  open, C's or Java's (`BERGDB_IN_USE`, tested by `durable_in_use`).
  Within one process the lock does not refuse a second open, and its
  close would release the first one's lock; C does not detect it, as a
  table of open directories would be global state (P9) with a lock. The
  rule is in `bergdb.h` (section G, `BERGDB_IN_USE`) and in the readme,
  section 9, point 10. Options B and C stay open for Frans.
* **D2. The debug calls in `api.c`**, as functions of their own, so that
  `db.c` (where 012-12 works) is not touched; the walk uses `OBJ_MARK` as
  `obj_recount` does, and clears it.
* **D3. `StatsProbe.java` kept** in `test/func/java/`, with how to run it,
  as the source of `f_settings.c`'s expected lines (the vectors' way:
  Java's output kept, the test without Java). `BERGDB_STATS_OUT=FILE`
  writes C's lines for a diff with a new Java run.
* **D4. The examples' comparison in the gate** (`examples/compare.sh`, the
  step `examples`): a second or two of JVM after the cross step, which
  builds the classes. It uses `java/stress/core-build/CoreDemo.java`:
  006-08's copy in its item imports `bergdb.core.SyncLevel`, which 005-56
  moved to `bergdb.pub.util`, so it no longer compiles; the two differ in
  that import only.
* **D5. No memory stream across restarts** (012-03, D13 and 6.10): the
  functional tests restart in directories, fast enough.
* **D6. Durability as it is, written down** (readme, section 9): no
  change of when C writes or forces. In particular the creation is not
  forced by the open (Java's start does not wait for it either), and a
  full buffer is written but not forced.

## 6.4 Durability tests

`test/func/f_durable.c`, C alone; the killed process is the test
program itself (`func --child exec DIR COUNT SIZE SYNC_EVERY KILL_AT`,
its standard output a pipe), killed with `SIGKILL`:

1. **After execute**: transactions 0 to 9, a sync, 10 to 14, killed after
   14's execute: the restart finds 0 to 9, nothing after, and the files
   end where the sync left them (the rest was in the buffer).
2. **After sync**: a sync after every transaction, killed after 14's
   sync: 0 to 14 found.
3. **After the creation, no sync**: the files are empty; the restart
   creates the database again.
4. **During a write**: values of 1 MB and no sync, killed after
   transaction 12: the 10 MB buffer was written inside transaction 9's
   record; the files hold exactly 10,000,000 bytes; the restart cuts the
   torn record off and finds 0 to 8.
5. **At random moments** (6 rounds; `BERGDB_DURABLE_ROUNDS` for more):
   1 MB values, a sync every 12 (so the buffer is written inside a record
   between syncs), killed after 0 to 2 syncs and 0 to 60 ms: every
   restart finds a prefix of whole transactions with every synced one.
   In the gate's runs some rounds end with a torn record and some find
   transactions beyond the last sync (a full buffer's write).

Every restart also checks each `/k/j` (the value, or none after the
prefix), runs `bergdb_debug_check`, executes one more transaction,
closes, opens again and finds it, with the allocator's count 0. Besides:
**`durable_in_use`** (another process's open: `BERGDB_IN_USE`, then
`BERGDB_OK` after the close) and **`durable_write_fails`**: a child with
`RLIMIT_FSIZE` at 150,000 bytes (`SIGXFSZ` ignored) executes 10
transactions of 50 kB; its sync fails (`EFBIG`) and gives `BERGDB_FAILED`
("A sync failed on the storage ... File too large"); then execute,
`get_one` and sync give `BERGDB_FAILED`, `bergdb_read_new`, `bergdb_stats`
and the cache size setter work, close gives `BERGDB_IO`, the count is 0;
the restart finds transactions 0 and 1, whole. A force that fails takes
the same path (`stream_sync`'s `fail`) but is not provoked here.

## 6.5 Questions for Frans

**Q2. A closed handle.** "Done when", item 4 asks that a second close be
harmless and that calls after a close get STATE, as Java's `close()` and
its `IllegalDbStateException`. In C the close frees the handle (012-03,
D1: a handle exists from its open to its close, which removed "not
started" and "stopping" from every call), so a second close or a call
after it uses freed memory, as `fclose` twice does; the test build's
AddressSanitizer reports it, the release build does not. What holds:
`bergdb_close(NULL)` does nothing, so `bergdb_close(db); db = NULL;` makes
a second close harmless; a close or any call from a callback gets
`BERGDB_STATE` and does nothing (`settings_close_and_callbacks`).

* **A. As now**, documented (`bergdb.h`, sections C and the close; the
  readme, section 8): the handle ends at the close, as a `FILE`.
* **B. Close keeps a small shell**: `bergdb_close` frees everything but a
  few bytes that say "closed", and a new `bergdb_free(db)` frees those;
  calls between get `BERGDB_STATE`. A function beyond 012-03's design
  (P12), and a leak if the caller forgets it.
* **C. A process-wide table of live handles**, checked by every call:
  global state with a lock (P9), as D1's option B.

**Recommended: A**, as C's own convention (`fclose`, `sqlite3_close`), and
because B and C add state or a function for a caller's error that the
test build already reports.

## 6.6 Done when, as it holds

1. **Every function of `bergdb.h` exists and has a functional test** (6.2:
   33 of 33; `bergdb_debug_print` and `bergdb_debug_check` written here),
   and 03-c-api.md, 6.2's table says for each of `Db`'s 45 public methods
   what C has. Holds.
2. **Settings and status equal to Java's**: `settings_and_status_as_java`
   compares the thirteen getters with `StatsProbe`'s lines on Java at nine
   points (the startup distance with Java's clamp, its dummy and the value
   in force; the cache size indicator set while running; the retain
   duration; the internal fraction; the stream length, the counts, the
   first available time and position, reclaim's iterations, the last valid
   meta block's transaction, the durable length after a sync and a start):
   all equal, and C's files equal Java's after the sequence. By hand, C's
   open of Java's finished directory gives Java's own values after its
   restart (the same line but the length, which the last two transactions
   added). `settings_setters` checks the setters' refusals and clamps, also
   on a failed database. Holds; the eviction that the budget's setter
   starts is 012-12's.
3. **Durability written and tested**: the readme, section 9 (after
   execute, after sync at each level, after close; the 10 MB buffer;
   `F_FULLFSYNC`; the durable length; the creation; what a start finds; a
   write or a force that fails fails the database, and what sync and close
   do then; reclaim's cut; one database per directory); `f_durable.c`
   (6.4). Holds for a process that dies; power loss is 012-14's.
4. **Close**: writes, forces and frees everything (the count 0 and no
   block live after every test, also with objects not freed and after a
   failed write, where it returns `BERGDB_IO`); a close from a callback
   gets `BERGDB_STATE` and closes nothing. A second close and calls after
   the close: the handle is gone, as a `FILE` after `fclose` (Q2, 6.5,
   recommended A, as implemented); `bergdb_close(NULL)` is harmless.
5. **Examples**: `core_demo` and Java's `CoreDemo` print the same five
   lines, each on a new directory and on the other's database;
   `get_many_prefix` prints Java's output; both run in the gate
   (`examples/compare.sh`, the test build). Holds.
6. **The API's text**: `bergdb.h`'s comments read against the code and
   corrected where they said less (03-c-api.md's progress); the guide in
   the readme, section 8. Holds.

## 6.7 Notes for the conductor

* **Files** (all in `items/012-bergdb-c/`): `13-api-complete.md`;
  `03-c-api.md` (progress); `05-cross-harness.md` (6.5); `c/readme.md`
  (sections 1, 2, 8, 9); `c/include/bergdb.h` (comments only);
  `c/src/api.c`, `c/src/api.h` (its comment); `c/build.sh`;
  `c/before-commit.sh` (the step `examples`); new `c/examples/compare.sh`;
  `c/test/func/f_api.c` (`main`: the tables, `func --child`,
  `func_program`); new `c/test/func/f_settings.c`, `f_durable.c`,
  `java/StatsProbe.java`; `c/test/func/readme.md`. Nothing in `db.c`,
  `db.h`, `cross.sh`, `run.c`, `java/`, `lean/` or `docs/`.
* **The merge with 012-12**, tried at 02:45 in a scratch clone (this
  clone's `7c3d857` with 012-12's `f4db2de`): two conflicts, both small.
  `src/api.c`, the end of `bergdb_get_one`: keep `*out = one;` (this
  task's) and then 012-12's comment and `db_evict(&db->db);` in place of
  `obj_collect`. `test/func/f_api.c`, `main`: both tables' externs, and
  `settings_tests, durable_tests, budget_tests` in the list, with this
  task's `func_program` and `--child` lines. `bergdb.h` and `readme.md`
  merged by themselves. The merged tree: `build.sh` BUILD OK, `unit` 345
  tests OK, `func` 23 tests OK (the status still Java's with eviction in,
  the debug checks with eviction), `examples/compare.sh` EXAMPLES OK. After
  the merge, `api.h`'s "Not yet: eviction (012-12)" sentence is stale.
* **Questions for Frans**: Q2 here (6.5); 11-reclaim.md's Q1 stands, and
  the readme says what C does today; 09-write-path.md's question (6.4) is
  decided (D1), and that file is not changed here.
* **Findings in Java**: none. Not a finding: 006-08's `CoreDemo.java` in
  its item does not compile on `main` (005-56 moved `SyncLevel`); the
  copy in `java/stress/core-build/` does (D4).
