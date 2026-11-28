Notes for the next release
==========================

What the release notes of the next release after 2026.6 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.6](2026.6/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

The release's files are on GitHub Releases, under its tag: the jar and
the Javadoc zip. `releases/VERSION/` holds the notes
(`readme.md`) and `SHA256SUMS`; there is no source zip (GitHub archives
each tag), and `baseline.zip` is not published (bergdb 034-01,
section 1; 029). The notes say so where they list the files.

Emptied at release 2026.6 (2026-11-24), whose notes hold what was there.


Released bugs fixed
-------------------

* **RB-005, S4. The count of the index nodes a transaction makes dirty
  was short for a key transformed to a longer key** (bergdb 033;
  028-50, 2026-11-24). The check of the index nodes that a transaction
  can make dirty (bergdb 005-31) counted a key with a key transformation
  by a coarse estimate with the key as given, before the transformation. It counts it now after the key transformations, with
  the key they gave, as it counts other keys. A transaction whose
  transformed keys could make too many nodes dirty is refused before its
  go point with a `DbException`, its keys as written given back, and the
  database goes on; one that the coarse count refused only because of
  its keys as given, such as 500 KVs of 111-byte keys on a small stream
  at node size 62 (review rev24, R3), can be taken now. Transactions
  without key transformations are counted as before; their stream is
  the same (StreamDigest identical).
* **RB-006, S4. `maintain()` could stop beginning reclaim iterations
  after some cuts** (bergdb 033; 028-51, 2026-11-24). After the cut of
  an iteration that began within 400 kB of its cut point, such as the
  first, calls of `maintain()` began no iteration until the application
  had written about twice the startup distance: a database written
  slowly kept up to about twice the startup distance of stream, and one
  emptied after such a cut and then not written to kept the deleted
  data's stream. A call now also begins an iteration when the stream
  written since reclaim last stored its table is 400 kB, so the calls
  begin iterations by the clock in a database written to, as the Javadoc
  says, and this rule begins none in one that is not. Streams written
  without `maintain()` are the same (StreamDigest identical).
  In part (028-58, 2026-11-25): when less than 400 kB is written after
  the cut and the stretch before it is just below 400 kB, an emptied
  database still keeps up to about 800 kB; the rest goes with RB-007's
  fix. The rest fixed by 031-06 (2026-11-27), with RB-007: a pass that
  a call of `maintain(int budget)` begins cuts at its own start, and
  031-03's case keeps 18,896 bytes of stream, from 790,264.
* **RB-007, S4. `maintain()` kept the stream written while a reclaim
  iteration waited for its cut** (bergdb 033; 028-53, 2026-11-24;
  031-06, 2026-11-27). A database written to and deleted from while an
  iteration that began within 400 kB of its cut point ran or waited for
  its cut, and then no longer written to, kept that stream under the
  calls, up to about twice the startup distance, though the Javadoc
  said that they bring an emptied database to within about 400 kB of a
  fresh one's stream. A call of `maintain(int budget)` now begins a pass
  while the stream kept holds a record of the application's, and the
  pass cuts at its own start: 028-53's case keeps 71,368 bytes, from
  4,804,384.
* **RB-010, S4. A stop or a crash during `maintain()` could leave its
  200 kB filler live** (bergdb 033; 028-59, 2026-11-25; 031-06,
  2026-11-27). A stop or a crash between the filler's put and its delete
  left `/#i/dreclaim/-fill.txt` live until a later call needed another
  filler, though the Javadoc said it is deleted at once. The filler is
  now reclaim's table padded with spaces, one record with nothing to
  delete, and no `-fill.txt` is written; a database of 2026.6, which may
  hold one, is not opened.
* **RB-008, S3. `Db.getTrans` could refuse a large transaction's
  position just after a cut** (bergdb 033; 028-55, 2026-11-25). With the
  Core API, `getTrans` of a committed transaction of over 1 MiB, just
  after a reclaim cut, threw `IllegalArgumentException` when a
  transaction ran over the start of the first kept file or 1 MB array:
  the walk to the record's start began at the stream's first position,
  inside that transaction. It begins at reclaim's cut now; a position
  before the cut with no record's start named before it expires
  (`LookupTimeNotAvailableException`). The Pub API was not affected.
* **RB-009, S3. `Db.getTrans` could expire a kept large transaction
  while reclaim cut the stream** (bergdb 033; 028-56, 2026-11-25). The
  walk to the record's start of a transaction of over 1 MiB could begin
  at, or reach, a record that a cut during the call removed, and the
  call threw `LookupTimeNotAvailableException` for a kept transaction.
  The walk now takes no record's start named before reclaim's cut and
  starts again when a cut removes what it reads while the position is
  kept; a position before the cut always expires, as
  `getFirstAvailablePos()` says. The Pub API was not affected.
* **RB-011, S4. An emptied file database kept its last stream file
  under `maintain()`** (bergdb 033; 028-62, 2026-11-26). A file
  database emptied after a large stream kept, under the calls, the
  stream file that its first position lay in, up to a quarter of the
  stream kept when that file was made (031-02's RetainChurn: 10,400 kB
  on disk for 61 kB of stream), though the Javadoc of
  `Database.maintain()` said within about 400 kB of a fresh database's
  size. The Javadoc of `maintain(int budget)` names no size: the calls
  rewrite the live data once, and the space comes back once the retain
  duration has passed since; an emptied database then keeps at most
  about 1 MB of stream: twice a fresh database's under the same calls,
  about 200 kB, and 600 kB more (bergdb 027-13, section 4, G5; in
  RetainChurn on `main`, 104 to 689 kB). `FileStream` gives a new file
  about a tenth of the stream that its files hold, not a quarter
  (RetainChurn's emptied rounds: 0.3 to 5.2 MB on disk); its Javadoc
  states that the disk can hold up to about one file more than the
  stream, and that the files, copied in the order of their names, are a
  backup. Files made by the quarter open
  beside new ones. The stream's bytes are the same; a stream has about
  three times as many files. A new file is at least 1 MB once 4 MB of
  stream are kept, as with the quarter, so a new database's first 10 MB
  are not in 200 kB files (028-73).
* **RB-012, S2. After a kill on macOS, a zeroed tail over a meta block
  stopped the start** (bergdb 033; 028-60, 2026-11-25 and 2026-11-27).
  A kill during a large append can leave the last stream file ending in
  zeros within its length (APFS); where they covered a meta block, the
  start threw "Invalid magic bytes", and where they reached past a
  record's end, it refused the database until a person cut the file. A
  meta block of zero bytes is now not valid, and at the open the file
  storage leaves a run of zero bytes of at most 8 MB at the end of the
  last stream file out of the stream, and truncates the file there at
  its first write, the same on every system: the start recovers the
  stream as a cut tail, with every transaction that a sync returned
  for. `Database`'s Javadoc, "What a crash keeps",
  says so. A longer run of zeros past a record's end, or other bytes, is
  refused, since 028-67 (2026-11-27) before the start writes anything and
  with a message that names the cause and the position to cut the stream
  at; meta blocks and records of another file or place, such as an older
  stream file's bytes that a kill can leave in the last file on APFS, are
  not taken (a meta block holds its own position and the database's ID, a
  record's header a check of them; meta version 156).
* **RB-013, S4. A stop between a transaction's record and reclaim's
  records after it changed the stream's bytes** (bergdb 033; 031-06,
  2026-11-27). After a `stop()` from another thread that came between a
  transaction's record and the records of reclaim that followed it in
  the same commit, and a restart, reclaim's interrupted work went on at
  the next commit at other positions, so the bytes differed from that
  record on from those of a run without the stop, for the same
  transactions. Every accepted action now appends one record, and a
  commit's record holds the maintenance that reclaim owes, so nothing
  lies between. No value was lost or changed.
* **RB-014, S4. A creation that a kill left as zeros was not refused
  as a creation** (bergdb 033; 028-80, 2026-11-28). After a kill during
  a new database's creation that left the file storage holding zeros
  only where the creation's first write should be, the start threw
  `StreamFormatException`, not `DatabaseNotCreatedException`, so an
  application that removes the files of a database that was not created
  did not. Such a stream, zeros only and at most 200,000 bytes from 0,
  is now refused as a creation that did not complete, and the start
  writes nothing.


Known released bugs
-------------------

Not fixed on `main`; a release with one needs Frans's exception
(bergdb 034-01).

None (2026-11-27).


The stream and the start
------------------------

* **A start compares created.txt's database ID with the stream's**
  (bergdb 028-81, 2026-11-28). A start that does not create the database
  reads the database ID that `created.txt` names, where the directory has
  one, and refuses, before it reads the rest of the stream, when the
  stream's first meta block holds another ID: another database's first
  stream file put in place of the database's own, or the stream files of
  one database beside the `created.txt` of another. The refusal names
  both IDs, says that the files are of two databases and gives the way
  out (restore the database's files from a backup, the stream files and
  `created.txt` together); the start writes and deletes nothing. Before,
  such a start was refused with a wrong cause, and its way out left a
  database with the other database's values. A directory without
  `created.txt` starts as before.


Speed
-----

* **The writer allocates and reads less** (bergdb 028-19, 2026-11-24).
  A small transaction's leaves are decided by counts from one pass over
  their klongs, a full leaf found before it, and the plan routes an inner
  node's operations and decides one appended to by counts without making
  its list of live entries. The same trees and the same stream
  (StreamDigest identical). Against the writer of record format 7 (as in
  2026.5): the set test of CORE 1.04 times its time, from 1.17; at 10M
  keys CCBench's median transaction 1.00 and the load 0.98 of its puts a
  second. `java/timing.sh` on F53, on c01ac655 against release 2026.6
  (with 028-01's and 028-48's changes of the conflict check also since
  2026.6, not timed apart): TIMING OK, no alerts; CORE 0.250 against
  0.250 (its set 0.35 to 0.36 against 0.40 and 0.41); the longest get or
  commit with ZGC 13.1 against 15.6 ms; commits a second +6.3 %
  (`w-uni-100-inf`) to +11.5 % (`r-100-fin`'s mixed phase), `w10m-fin`
  +7.8 %, `w10m-inf` +10.4 %; the reads +0.2 to +9.1 %.
