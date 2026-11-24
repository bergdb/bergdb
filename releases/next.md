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
  028-53 holds the options for the fix.


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
