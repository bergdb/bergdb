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
  fix.
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
* **RB-012, S2, in part. After a kill on macOS, a zeroed tail over a
  meta block stopped the start** (bergdb 033; 028-60, 2026-11-25). A
  kill during a large append can leave the last stream file ending in
  zeros within its length; where they covered a meta block, the start
  threw "Invalid magic bytes". A meta block of zero bytes is now not
  valid: zeros that begin inside the last record are recovered as a cut
  tail, and zeros past a record's end get the documented refusal with
  the position P to cut at, which then starts. Whether the start cuts
  such a tail itself is open (028-60).


Known released bugs
-------------------

Not fixed on `main`; a release with one needs Frans's exception
(bergdb 034-01).

* **RB-007, S4. `maintain()` keeps the stream written while a reclaim
  iteration waited for its cut** (bergdb 033; 028-53, 2026-11-24). A
  database written to and deleted from while an iteration that began
  within 400 kB of its cut point ran or waited for its cut, and then no
  longer written to, keeps that stream under the calls, up to about
  twice the startup distance, though the Javadoc says that they bring
  an emptied database to within about 400 kB of a fresh one's stream.
  028-53's options A and B were not taken (Frans, 2026-11-25); 031-03
  looks for the fix.
* **RB-010, S4. A stop or a crash during `maintain()` can leave its
  200 kB filler live** (bergdb 033; 028-59, 2026-11-25). A stop or a
  crash between the filler's put and its delete leaves
  `/#i/dreclaim/-fill.txt` live until a later call needs another
  filler, though the Javadoc says it is deleted at once. 031-03's
  design has no filler to delete.
* **RB-011, S4. An emptied file database keeps its last stream file
  under `maintain()`** (bergdb 033; 028-61, 2026-11-25). Reclaim cuts
  the stream below 400 kB, but `FileStream` drops only whole files and
  keeps the last one, sized when the stream was large; 028-62 holds the
  options for the fix.


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
