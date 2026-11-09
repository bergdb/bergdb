# 022-06-2 A careful application that meets every error

Created 2026-11-09 by Frans Lundberg.

New user u2 of BergDB's C library, with only `/Users/f/fl/bench/022/userkit/`:
an application that meets the errors of a real deployment and checks each
against the words of `bergdb.h` (and of `c-readme.md` where the header points
there). The library's implementation and tests were not read. Two findings
name a function or file of the library (U2-3, U2-14): the names come from the
macOS profiler's stack samples of a slow run and from a UBSan report, not from
the source. (The session saved this text from u2's final message; u2's own
write of the file was refused by the harness.)


# 1. The application

`u2` (`u2.c` and the scenario files `u2_*.c`, 2,320 lines of C) runs one
scenario per call, `u2 SCENARIO [DIR]`, and prints `DIFF [scenario] ...` for
every difference between what a call did and what the header says, and
`NOTE` for an observation where the header is silent. A call that may crash
(a NULL, a length over `INT32_MAX`) runs in a forked child. `run.sh` builds
`u2` against both libraries and runs every scenario with each (about 40 s with
the sanitizer build, 30 s with the release build); it exits with the number of
scenario runs that had a difference (2 today: `clock`, U2-1 and U2-12;
`files`, U2-11). `repros.sh` builds and runs every `repro_*.c`;
`repro_full_zerofill.sh` runs apart (it attaches a disk image).

The scenarios: `args` (bad arguments to every function: NULLs, oversized
lengths, objects of another database, every setting out of range, malformed
UTF-8; 348 checks); `callbacks` (the clock, a stop condition and both
transformations call every function of their own database and others; 161
checks); `failed` (allocation failures in every call, the failed database's
behaviour, the reopen; 855 checks); `budget` (the smallest settings, reclaim,
restarts, `debug_check`); `clock` (clocks before 1970 and past the maximum, a
stuck clock, a clock that goes back, the end of time); `lock` (a second open
from another process and in the same process, the lock file deleted, read-only
or a directory); `files` (stream files deleted, truncated, made read-only while
open and between runs, foreign files, a flipped byte); `full` (a database on a
60 MB HFS+ image filled until a call fails, reopens with the disk full and after
space is freed); `reserved` (garbage under BergDB's own keys); `large` (keys of
16 KB to 256 KB, values up to 64 MB); `kill` (`SIGKILL` at six points); `rofs`
(a read-only volume); `paths` (long paths and names). Leaks: 0 live bytes after
every close; macOS `leaks` finds none.


# 2. Findings

| ID    | Kind | Severity | What                                                       | Reproduction |
|-------|------|----------|------------------------------------------------------------|---|
| U2-1  | bug  | medium   | One current_time with the clock past MAX_TIME stops all writes until a restart | repro_clock_poison.c |
| U2-2  | bug  | medium   | After a full disk, the open zero-fills the torn record: needs its size free | repro_full_zerofill.sh |
| U2-3  | bug  | medium   | Long keys sharing a prefix: an unrelated 4 MB put takes 16 s | repro_long_key.c |
| U2-4  | API  | medium   | get_trans at a position inside a record fails the database, not ARG | repro_get_trans_fails.c |
| U2-5  | API  | low      | Second open in one process: the first's later commits say OK and are lost | repro_two_handles.c |
| U2-6  | API  | low      | A stream file deleted under an open database: sync and close OK, no open after | repro_deleted_file.c |
| U2-7  | API  | low      | bergdb_close's BERGDB_IO has no text | repro_two_handles.c |
| U2-8  | API  | low      | 7 bytes under reclaim's settings key: no open ever again, no repair | repro_reserved_key.c |
| U2-9  | API  | low      | No read-only open: a database on a read-only volume does not open | run.sh (rofs) |
| U2-10 | doc  | low      | bergdb_open gives BERGDB_NOT_AVAILABLE, which its list of errors lacks | repro_open_not_available.c |
| U2-11 | doc  | low      | BERGDB_FORMAT lists foreign files; an open with notes.txt succeeds | repro_foreign_file.c |
| U2-12 | doc  | low      | User times end at MAX_TIME - 1024; section F says 0 to MAX_TIME | repro_clock_end.c |
| U2-13 | doc  | low      | stats: pinned_bytes, "of the resident bytes", exceeds resident_bytes | repro_pinned.c |
| U2-14 | doc  | low      | The test clock with clock_ctx NULL: a NULL dereference in the open | repro_test_clock_null.c |
| U2-15 | doc  | low      | readme 9.6 says a torn record is cut off; the open zero-fills it | repro_full_zerofill.sh |
| U2-16 | API  | low      | The 10 MB write buffer is outside the memory budget | u2 budget |

* **U2-1.** Section F: a clock time outside 0 to `BERGDB_MAX_TIME` "refuses
  the transaction", and `bergdb_current_time` gives "the clock's time, at most
  BERGDB_MAX_TIME - 1024", and the next transaction's time is later than what
  it gave. So one call of `bergdb_current_time` while the clock reads past the
  maximum (a clock glitch) records MAX_TIME - 1024; when the clock is right
  again, every user transaction is refused: "DbException: No database time is
  left for a user transaction: its time would be 72057594037926912, after the
  last, 72057594037926911". The setters that commit are refused the same way.
  A restart cures it. Expected: a clock out of range refuses the transactions
  while it is out of range only; `current_time` need not record a clamped time
  that no transaction can follow. Java's `DbClock` may do the same; not checked.
* **U2-2.** A 12 MB transaction on a disk with 2 MB free fails the database
  (`BERGDB_FAILED`, as documented), and the close gives `BERGDB_IO`. The next
  open writes zeros over the torn record's whole declared length: with 6 MB
  free it fails ("IOException: Write of 1000000 bytes at 0 failed: No space
  left on device"), and the database does not open, not even to read, until
  about the failed transaction's size is free (up to the value limit, about
  1.88 GB). After that open, a database that held 264 bytes has a stream of
  12,591,624 bytes. (014-01's zero fill.)
* **U2-3.** Keys of 128 KB, 512 KB and 2 MB that share all but their last
  byte, each put in its own transaction in a directory database (release
  build): the 2 MB key's execute takes 4.2 s (alone: 0.07 s); then a put of a
  1 MB value under another, 2-byte key takes 2.0 s and one of 4 MB 16.4 s
  (test build: 41.7 s). The profiler's samples are all in `bergdb_execute`,
  `db_execute`, `store`, `kn_get_pointer` and `kn_get_pointer_node`. In memory
  the same puts are fast. A key also costs about 51 bytes of memory per byte
  while it is put (53 MB for a 1 MB key, 425 MB for 8 MB). The header allows
  keys of up to `INT32_MAX` bytes and says nothing of their cost.
* **U2-4.** `bergdb_get_trans` at `tpos + 8` of a committed transaction (a
  multiple of 8, before the end, not in a meta block) gives `BERGDB_FAILED`
  ("DbFailedException: A read failed on the storage ... Cause:
  StreamFormatException: Bad transaction size"), and every later read and
  transaction fails; an in-memory database is lost. The function's comment
  says so, but section B's list for `BERGDB_ARG` has "a position that is not a
  transaction's", and the text blames the storage.
* **U2-5.** Section G says a second open in one process is not detected and
  that its close releases the first's lock. Also: the first handle's next
  `bergdb_execute` returns `BERGDB_OK`, the transaction is lost, and only the
  first handle's close says `BERGDB_IO`, with no text.
* **U2-6.** The last (or only) stream file deleted while the database is open:
  later transactions, `bergdb_sync` and `bergdb_close` all give `BERGDB_OK`,
  and the next open refuses the directory (`BERGDB_FORMAT` or
  `BERGDB_NOT_AVAILABLE`). `fstat`'s `st_nlink` at a sync would tell.
* **U2-7.** `bergdb_close` returns `BERGDB_IO` with no text; an application
  cannot log why its close failed.
* **U2-8.** A put of "garbage" under `/#i/dreclaim/-settings.txt` is taken, and
  every later open gives `BERGDB_FORMAT` ("InternalDataException: Bad value of
  /#i/dreclaim/-settings.txt"); nothing in the API can repair it. The Core
  could refuse puts and deletes under the keys it writes itself.
* **U2-9.** On a volume attached read-only, `bergdb_open` gives `BERGDB_IO`
  (the lock file); a read-only open would serve snapshots and backups.
* **U2-10.** With the first stream file deleted between runs, `bergdb_open`
  gives `BERGDB_NOT_AVAILABLE` ("StreamIoException: Cannot read at spos 128,
  below the first position, 200000."), which the open's list lacks.
* **U2-11.** `BERGDB_FORMAT`'s comment lists "foreign files in the directory";
  a `notes.txt` is taken; a foreign file named like a stream file is refused.
* **U2-12.** User transaction times end at MAX_TIME - 1024; section F says 0
  to MAX_TIME; only `bergdb_current_time`'s comment has the 1024.
* **U2-13.** `pinned_bytes` ("of the resident bytes") is larger than
  `resident_bytes` with the smallest settings (6,552 against 6,032).
* **U2-14.** `bergdb_test_clock_time` as the clock with `clock_ctx` NULL: a
  NULL dereference in the creation (UBSan; SIGSEGV in the release build); a
  NULL there could be `BERGDB_ARG` at the open.
* **U2-15.** `c-readme.md` section 9 point 6 says a torn record is cut off;
  the open fills it with zeros to its whole length.
* **U2-16.** Every database holds the fixed 10 MB write buffer, outside the
  memory budget; a setting of its size would help small devices.

Other observations, not findings: `bergdb_lookup_time(-5)` gives -5, which a
read then refuses; a lookup time of `INT64_MIN` prints as "+27259-04-19 ...";
on a failed database the argument checks come first; a single corrupt value
node makes every later read fail after it is met; a deleted `bergdb.lock`
under an open database lets another process open the directory.


# 3. What went well

* Every bad argument that the header lists is refused with `BERGDB_ARG` and
  leaves the transaction or database as it was (348 checks), without a crash or
  a sanitizer report (but U2-14).
* Callbacks: every call into the same database from a callback gives
  `BERGDB_STATE` and does nothing; transformations that move or merge keys keep
  the index sound.
* Allocation failures: every NOMEM before the go point left the database as it
  was; the failure after it gave `BERGDB_FAILED` and the failed database did
  exactly what section B lists.
* A full disk and `SIGKILL`: every synced key was there after the reopen, whole
  transactions only (but U2-2).
* Corrupt bytes were always found: no wrong value was ever returned without an
  error.
* The lock: another process gets `BERGDB_IN_USE` with a clear text.
* The smallest budget kept every key; `debug_check` passed throughout.
* The error texts name Java's exception and say what to do.
* The release and the sanitizer builds gave the same results; no leaks.
