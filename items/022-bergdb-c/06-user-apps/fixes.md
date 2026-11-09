# 022-06 Fixes of the user apps' findings in C

Created 2026-11-09 by Frans Lundberg. Status: open.

What C changed for the findings of the new users of the C library, u1
(022-06-1, [u1-device-store.md](u1-device-store.md)), u2 (022-06-2,
[u2-error-paths.md](u2-error-paths.md)) and u3 (022-06-3,
[u3-audit-log.md](u3-audit-log.md)), finding by finding; their
reproductions are in `/Users/f/fl/bench/022/apps/`. The rule
(the session `022-bergdb-c`): C follows Java's Core; where C does what
Java does, the words change, not the behaviour; the behaviour changes
only where C alone is at fault. Java's behaviour was read in `main` at
`a2fa9df` (`Db`, `DbClock`, `Trans`, `GetMany`, `DbBuilder`).


# 1. Worker f3: the header, the readme, four small fixes

Twenty findings and worker t12's, of the close: four changes of C's
behaviour, each with a test that fails before it, one departure kept,
and words for the rest, in `c/include/bergdb.h` and
`c/readme.md`. The others are worker f1's (U3-1, U3-2:
[u3-reclaim-fifo.md](u3-reclaim-fifo.md)), worker f2's (U2-1, U2-3,
U2-4, U2-6, U2-8) and the session's other workers' (U1-1 to U1-4, U1-8).

| Finding          | Change    | Where                                          |
|------------------|-----------|------------------------------------------------|
| U2-10            | behaviour | `api.c`, `bergdb.h`; test `f_start.c`          |
| U2-13, U1-5      | behaviour | `evict.c`, `evict.h`, `bergdb.h`; `f_budget.c` |
| U2-14            | behaviour | `api.c`, `bergdb.h`; test `f_settings.c`       |
| U2-11            | words     | `bergdb.h`; test `f_start.c`                   |
| U2-5, U2-7, U2-9 | words     | `bergdb.h`, `readme.md`                        |
| U2-12, U2-16     | words     | `bergdb.h`, `readme.md`                        |
| U2-15            | words     | `readme.md`, section 9, point 6                |
| U3-3 to U3-7     | words     | `bergdb.h`                                     |
| U1-6, U1-7       | words     | `bergdb.h`                                     |
| U1-9, U1-10      | words     | `bergdb.h`                                     |
| t12's close      | departure | `bergdb.h`, `readme.md`, section 11, point 5   |

## 1.1. The changes of behaviour

* **U2-10.** An open whose startup position lies in a stream file that is
  gone (the first file deleted by hand) gave `BERGDB_NOT_AVAILABLE`, the
  code of a read at a time that reclaim removed, which the open's list of
  errors lacks. Java's start throws the `StreamIoException` ("Cannot read
  at spos 128, below the first position, 200000."), which `bergdb.h` maps
  to `BERGDB_IO`. Now `bergdb_open` gives `BERGDB_IO` for it, its text
  unchanged (C's own fault: the code of the read below the first position
  was kept for the reads after the open, where it is right). `BERGDB_IO`'s
  comment and the open's list say so. Test `f_start.c`'s
  `start_files_of_the_directory`, which failed before (`BERGDB_NOT_AVAILABLE`).
* **U2-13.** `bergdb_stats.pinned_bytes`, "of the resident bytes", was
  larger than `resident_bytes` with the smallest budget (6,552 against
  6,032). The cause: the walk of the pinned objects (`ev_pinned_bytes`)
  counted each pinned node with its handle, and each object that its
  pointers hold, but marked only the nodes; so a pinned node's handle that
  its pinned parent holds was counted twice, by the parent and by the node
  (a probe that counts each object once gave 6,032, the resident bytes
  exactly; the excess was 13 handles of 40 bytes). The count is C's own
  (Java's `Db` has no such getter): now each object is counted once, its
  handle and the values and handles that it holds marked too, and unmarked
  by a second walk. `bergdb.h` and `evict.h` say so. Test `f_budget.c`'s
  `budget_pinned_within_resident` (node sizes 8, 14 and 30, budgets 1,
  4,000 and none, 300 transactions in memory, the stats after each): before
  the fix the pinned bytes exceeded the resident bytes after up to 300 of
  the 300 transactions in each run, also once without eviction.
  `t_evict.c`'s checks with the pinned bytes pass with the true count.
* **U1-5** (U2-13's, and more). The pinned bytes also counted every value
  that a pinned key node holds, though a sweep makes a written value's
  pointer a stream pointer (`unswizzle_values`, Java's
  `Eviction.unswizzleValues`), so the value need not stay: after a refused
  transaction whose warm-up loaded 2,000 values of 5,000 bytes into the
  nodes of D, u1 saw 10.2 MB pinned, which the next read evicted down to
  156 KB. Now `pinned_of` leaves out a written value (`written_value`):
  the pinned bytes are what stays after a full sweep, the pinned nodes,
  their handles, the handles they hold, the values not written yet, and the
  node table. u1's `budget_after_refusal.c` now gives 149,632 pinned bytes
  after the open, where it gave 156,072 against 149,632 resident, and the
  same after each refusal, with 10,229,632 resident, where it gave
  10.2 MB. The test above
  checks it too: after each committed transaction, whose values are all
  written, the pinned bytes are at most the resident bytes less the
  values' (`bergdb_mem.live[BERGDB_MEM_VALUE]`); without this part of the
  fix it fails in 6 of the 9 runs. Worker f4 changed when C evicts (U1-3,
  U1-4: [u1-eviction.md](u1-eviction.md)); the meaning of the pinned
  bytes, what must stay, does not depend on it, and `cache_size_indicator`
  now names them and f4's margin over them under a budget below them (the
  gap between the watermarks, or the node table's bytes if more).
* **U2-14.** The test clock (`bergdb_test_clock_time`) with `clock_ctx`
  NULL dereferenced NULL at the creation's read of the clock. C's own:
  Java's `CoreTestClock` is one object, and `DbBuilder.clock(null)` is
  refused. Now `bergdb_open` refuses it first, with `BERGDB_ARG`,
  "IllegalArgumentException: clock_ctx == NULL not allowed with
  bergdb_test_clock_time", and nothing made; a clock function of the
  caller's still gets its ctx as given, NULL too. Test `f_settings.c`'s
  `settings_open_checks` (in a directory and in memory), which crashed
  before.

## 1.2. The words

Each where C does what Java's Core does, read in Java first:

* **U2-11.** `BERGDB_FORMAT` named "foreign files in the directory". The
  open reads only the files whose names end with ".bergdb", as Java's
  `FileStream.getSortedDbFiles`, and refuses such a file that is not a
  stream file's, a gap and a short file before the last
  (`BadDirStateException`); other files are not the database's. The
  comment says that now; `start_files_of_the_directory` checks both
  (a `notes.txt` taken, a `notes.bergdb` refused).
* **U2-12.** Section F said times run from 0 to `BERGDB_MAX_TIME`. Now it
  says that a user transaction's time is at most `BERGDB_MAX_TIME - 1024`
  (Java's `DbClock.LAST_USER_TIME`, 015-55): `bergdb_execute`'s, the
  creation's, the dummy transaction's; the last 1,024 units are for
  reclaim's transactions and the commits of reclaim's settings.
* **U2-15.** `readme.md`, section 9, point 6 said that the start cuts a
  torn record off. It fills it with zeros to the size its header gives
  (`appendZeros`), a record that is not committed, and the next
  transaction follows it; the point says so, and that the open needs room
  for the zeros (u2's U2-2).
* **U2-5.** Section G and `readme.md`, section 9, point 10: what follows
  a second open in one process. Both append to the same files; the one
  that writes second finds a file of another length ("Was it modified by
  someone else?"), fails, and loses its transactions since its last sync,
  whose execute gave `BERGDB_OK`; its sync gives `BERGDB_FAILED` with the
  text, its close `BERGDB_IO` (seen with u2's `repro_two_handles.c`).
* **U2-7.** `bergdb_close`: the close's write and force are a
  `bergdb_sync`'s, so a caller that wants the text syncs first, which
  gives `BERGDB_FAILED` and the text; after a sync that succeeded, the
  close has nothing to write or force. Also in `readme.md`, section 8.
* **U2-9.** Section G: an open writes (the lock file, the forces at the
  open, the zero fill, a pending cut), so a read-only volume gives
  `BERGDB_IO`, and the API has no read-only open (section 2).
* **U2-16.** Section A, `cache_size_indicator` and `readme.md`, section 9,
  point 1: the 10 MB write buffer is allocated at the first append and
  held until the close, outside the budget, which bounds the index only;
  the transactions, read contexts and a database in memory's stream too.
  Java's `DbBuilder.stream(stream, bufferSize, bufferTime)` sets its size;
  C's API has no such setting (section 2).
* **U3-3.** `bergdb_get_trans` gives `BERGDB_NOT_AVAILABLE` only when a
  cut has deleted the transaction's file, as Java's `getTrans`
  (`isReadBelowCut`): a transaction before `first_available_pos` is read
  while its file is there.
* **U3-4.** `bergdb_range.prefix`: a stop condition only, as Java's
  `GetMany.Prefix`; set `start_key` to the prefix (forward), or, backward,
  to the prefix with its last byte raised by one and `inclusive` false.
* **U3-5.** `bergdb_get_many`: a read of every key returns BergDB's own
  keys (01 25, "/#"); read your own range, or leave them out with a stop
  function (section E's advice, now at the function).
* **U3-6.** `reclaim_iteration_count`: the iterations completed since the
  open, 0 at each open, as Java's `getReclaimIterationCount` ("since its
  start()").
* **U3-7.** A negative lookup time, as Java: `bergdb_lookup_time` gives it
  as it is (`DbClock.lookupTime` takes any time), a read refuses it with
  `BERGDB_NOT_AVAILABLE` (`getOneInternal`: before the first available
  lookup time), and `bergdb_trans_lookup_time` with `BERGDB_ARG`
  (`Trans.Builder.lookupTime`'s `IllegalArgumentException`). Section F,
  `bergdb_lookup_time`, `bergdb_get_one` and `bergdb_trans_lookup_time`
  say so. Nothing changed: one rule (u3's proposal) would depart from
  Java.

* **U1-6** (= U3-5). Section E and `bergdb_get_many`: a range that
  reaches BergDB's keys returns them among the user's pairs, and
  `max_count` counts them; a stop function that answers `BERGDB_CONTINUE`
  for them decides before the count (`api.c`'s chain: prefix, end key,
  function, count).
* **U1-7.** `bergdb_trans_put`: the last put of a key counts by the key as
  given, before a key transformation, as Java's `Trans.Builder.build()`
  (a `TreeMap` by `kv.getKey()`); so a plain and a transformed put of one
  given key are one, and the earlier is dropped. Give a transformed put a
  key that no other put or delete of the transaction gives.
* **U1-9.** `bergdb_one.time` and `tpos` already had Java's words (021-17,
  021-19, in `cd25a24`, after the user kit's `391c3cf`): the write's time
  is `bergdb_get_trans(tpos)`'s `tt`, and for a value that reclaim copied,
  the step's, with the way back by a get at the step's time less one. Now
  `tpos` also says, as Java's `getTrans` does, that once reclaim has made
  that time unavailable the write's transaction and time are gone.
* **U1-10.** `bergdb_trans_key_read`: keys are compared by their hashes,
  Java's words (`Db`, "Optimistic transactions"): a write of another key
  with the same hash gives a rerun that was not needed, never a missed one.

* **t12's close** (no U number: worker t12, porting Java's tests).
  `bergdb_close` gives `BERGDB_IO` also after a call has reported the
  storage's failure, where Java's `close()` returns normally since 019-09
  (`testCloseOfFailedDatabaseReturnsNormally`); `bergdb.h` said that
  Java's `close()` does not report a failure at all, words from before
  005-73 and 019-09. Decided by default (the session; Frans may change
  it): C's behaviour kept, a departure, `readme.md`, section 11, point 5
  (C reports more, never less; no data at stake); `bergdb_close`'s words
  say so.

## 1.3. For Frans

Three API additions that the users asked for, none made (each would be
C's own, beyond Java's `Db`, or a port of a Java setting that 012-03 left
out):

* **A read-only open** (U2-9): for snapshots and backups on a read-only
  volume. C's stream already opens a directory read-only for the tools
  (`stream.c`, `bergdb-dump`); an open that writes nothing would also skip
  the forces, the zero fill and the cuts, and refuse transactions. Java's
  `Db` can start on a `ReadOnlyStream`; Java's `FileStream` opens for
  writing.
* **A buffer size** (U2-16): `bergdb_options.buffer_size`, as Java's
  `DbBuilder.stream(stream, bufferSize, bufferTime)`; C has it inside
  (`db_config.buffer_size`, which the API leaves 0). For small devices.
* **A close error text** (U2-7): `bergdb_close` with an error buffer, as
  `bergdb_open` has; until then, a sync before the close gives the text.
