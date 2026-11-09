# 020-24-14 A multi-tenant SaaS backend: index churn in one database

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u14, for coord-1109, round 5
of the common brief of 020-24): only the release jar on the class path, built from a clone
of main at `b0eba12`, and only what a user reads (README.md, `java/src/overview-pub.html`,
the Javadoc of `bergdb.pub` and `bergdb.pub.util`, `releases/next.md`). The Core's `Db`, which
the package's "The API and its jar" names as API, was used once, after the runs, to count
the stored index entries (`CoreScan`).


## 1. The application

A SaaS backend that keeps 200 tenants in one database. All is in
`/Users/f/fl/bench/2026-11-09/app-u14/app/` (1,380 lines): `Tenants.java` the application and
its oracle, `Crash.java` crashes in the middle of builds and cleanups, `CoreScan.java` the
count of stored index entries, `Scale.java` the cost of many indexes, `Probe1.java` the
messages during a build, `PutCost.java` and `ReclaimChurn.java` the reproductions of U14-1.
`run1.txt` to `run6.txt`, `crash1.txt`, `scan*.txt`, `reclaim-*.txt`, `rc-*.txt` and
`putcost*.txt` are the outputs. Run: `javac -cp ../bergdb/java/build/bergdb-release.jar -d
classes *.java`, then `java -cp ../bergdb/java/build/bergdb-release.jar:classes Tenants
DBDIR [churnSeconds] [seed] [retainSeconds] [full|static|churn]`.

* Each tenant is a directory tree: `/ten/T/readme.txt`, `/ten/T/users/` (User objects:
  a string name, long age, double score, byte[] tag, a nested Addr with a city and a zip, a
  Long level that is often absent), `/ten/T/users/archive/`, `/ten/T/proj/p0` and `p1`
  (Project objects) with `/ten/T/proj/pN/tasks/` (Task objects). 30 to 80 keys a tenant, two
  "whale" tenants with 15,000 users. The tenant names include prefixes of each other (`t1`,
  `t10`, `t100`), `t.x47`, `tö49` and `t😀48`; the values include -0.0, NaN, infinities,
  bytes above 0x7F, names beyond the BMP and in the private use area, a String put over an
  object key, absent fields.
* Each tenant has its own indexes, named `T.iN`, of 14 definitions: every type, nested
  fields, two levels (string and long, long and string, string and double, long and double,
  bytes and string), an index of a subdirectory (`users/archive/`), one whose type does not
  match its field (no entries). 75 at the start, 50 to 100 during the churn, 450 to 470 in
  the parallel phase.
* The oracle: every write updates an in-memory map of the tenant's keys, under the tenant's
  lock, after its commit. Each check computes the index function from the oracle (the
  Javadoc's rules: kinds not converted, NaN and absent fields without an entry, -0.0 as 0.0,
  strings by code points, bytes unsigned, keys by UTF-8) and compares, in order, the keys
  and the values of a full scan, a backward scan, and four random queries (eq on 0 to all
  levels, from, to, both, prefix, backward); a listing of each of the tenant's directories;
  and a query that mixes two indexes of a tenant at one frozen lookup time, intersected by
  key. Every key outside the index's directory is reported as foreign.
* The phases, in one run: load; 75 index builds; churn for 20 to 60 s while 4 writers write
  (about 8,000 writes a second): index creations, deletions, rebuilds under the same name with
  the same or another definition, tenants deleted as a whole (indexes and keys) and made
  again under the same name, with their indexes before or after the data; scans at a lookup
  time before a rebuild under the same name with another definition (the old definition's
  result against a snapshot of the oracle); 4 admin threads that do the churn of their own
  tenants at once for 20 s; 50 races of two threads that create one name at once, then
  delete it at once; restarts right after whale indexes were deleted and created (builds of
  15,000 values running) and right after rebuilds of them (cleanups running), after whole
  whale tenants were deleted and made again, and with every index active. `Crash` halts a
  child JVM (`Runtime.halt`) 20 to 200 ms after it has deleted and created indexes of a
  tenant of 20,000 users and synced, 8 times, and checks after each start.
* Each run exits with 1 on a wrong result. Over the 9 runs of `Tenants`: about 300,000
  queries checked, 5.6 million writes, about 50,000 index creations and as many deletions,
  6,000 tenants deleted and made again; every check passed. Runs 5 and 6 and the
  `reclaim-*` runs had a retain duration of 2 s and a startup distance of 5 MB, which found
  U14-1.


## 2. The findings

No wrong result: no scan of a tenant's index gave another tenant's key or any key outside
its directory, no stale entry, no wrong order, no wrong value, also after restarts and
crashes in the middle of builds and cleanups. Every build ended. The cleanups left no
entry: after a run, the stored entries of each live index, counted with the Core's `Db`,
equal the oracle's count, each index has one generation, and no deletion marker is left.
One finding is a bug, of performance: with a retain duration, the creations and deletions of
indexes slow down every later put, also in a directory without an index, and stall reclaim
(U14-1). The others are about what a multi-tenant application needs and does not get. Most
severe first:

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U14-1 | bug | high   | with reclaim, index churn slows every later put          | PutCost   |
| U14-2 | API | medium | no listing of the indexes or of their definitions        | section 3 |
| U14-3 | API | low    | no listing of subdirectories: a tenant's tree is unknown | section 3 |
| U14-4 | API | low    | a rebuild under its name: queries throw until built      | Probe1    |
| U14-5 | doc | low    | no word on limits on the number of indexes, or cost      | Scale     |
| U14-6 | API | low    | no way to know that a deleted index's cleanup ended      | CoreScan  |


## 3. The findings in detail

### U14-1. With reclaim, index churn slows every later put, also after a restart (bug, high)

A multi-tenant service sets a retain duration, so that the data of deleted tenants and old
versions leave the disk (`Database.setRetainDuration()`). With one set, each creation and
deletion of an index makes every later put slower, also a put in a directory that has no
index, and the slowdown stays, also after a restart (not measured: whether it ends once
reclaim has cut past the deletions). Under steady index churn, reclaim also stops cutting,
and the stream grows as if no retain duration were set.

`PutCost` (startup distance 5 MB, retain 2 s): 20,000 objects in `/w/`, no index there; an
index on `/c/` (500 objects) created, joined and deleted K times; then 50,000 single puts
in `/w/`. Without a retain duration (same program, no second argument) the cycles change
nothing.

| Cycles         | Puts a second, retain 2 s | Without a retain duration |
|----------------|---------------------------|---------------------------|
| 0              | 155,027                   | 134,533                   |
| 10             | 133,113                   | 108,258                   |
| 100            | 43,165                    | 199,014                   |
| 300            | 21,669                    | 232,318                   |
| 1,000          | 8,631                     | 197,709                   |
| after restart  | 6,261                     | 223,046                   |

`ReclaimChurn DBDIR seconds MODE` (the same settings, a writer updates 20,000 objects of
`/w/`, so the live data stays at about 1 MB; every 5 s the stream on disk and the age of
the first available lookup time):

* `none` (no index): 6.5 million puts in 45 s; 86 to 115 MB on disk; the first available
  lookup time 2.1 to 2.2 s old throughout.
* `slow` (one creation and deletion a second, 29 in all): 57 to 86 MB, 2.1 to 2.6 s. Fine.
* `churn` (create, join, delete in a loop, 878 cycles in 50 s): 572,000 puts, 11 times
  fewer; 350 MB on disk and growing; the first available lookup time 3.6, 9.6, 14.6 ...
  39.6 s old: no cut for 40 s.
* `burst10` (the loop for 10 s, 261 cycles, then puts only for 50 s): the puts stay at
  15,000 to 20,000 a second for the 50 s after the burst, 7 to 10 times fewer than before;
  a cut only about every 25 s; 180 to 270 MB on disk.

In the application (`Tenants` with retain 2 s, `reclaim-static2.txt` and
`reclaim-churn.txt`, 100 s each): without index churn, 1.07 million writes left 562 MB on
disk for 54 MB of live keys and values (counted with `CoreScan`), with a cut every 10 to
20 s; with the churn, 750,000 writes left 1.5 GB for 9.7 MB of live data, and the first
available lookup time was 61 s old before the one cut, at 85 s. The Javadoc of
`setRetainDuration()` gives store efficiencies of 0.09 to 0.75; this is 0.0065.

Every result was still right: the slowdown and the stall cost time and disk, not data.
Why, from the implementation, read afterwards and not verified: the Core's `Reclaim`
(its class comment) makes a step at each external transaction, and a step scans the keys
from the last one and "touches" the key range, "also nodes that hold deleted keys only".
Each index generation leaves its entries as deleted keys (500 a cycle here) and a marker,
so each step, at each put, may walk more deleted keys the more indexes were deleted; a
restart does not remove them. Severity high: the slowdown grows with every index ever
deleted in a database with a retain duration, it hits every writer of the database, and
a multi-tenant service with tenant-defined indexes deletes indexes all the time.

### U14-2. No listing of the indexes or of their definitions (API, medium)

The Pub API has no call that lists the indexes, and none that gives an index's definition
(its directory and levels): `Database` has `indexBuilder()`, `deleteIndex()` and
`indexJob(name)`, and `indexJob()` takes a name the caller knows. A multi-tenant application
lets each tenant define indexes, so it must keep its own registry of the names and
definitions, and it cannot write that registry in the transaction that creates or deletes
the index: `IndexBuilder.start()` and `deleteIndex()` are transactions of their own. After
a crash between the two, the registry and the database disagree. An index that the registry
lost is never found again: it is kept by every write of its directory and costs at every
start, and only a guess of its name (`indexJob(name)`) or the Core API finds it. The same
holds for an application that just wants to show a tenant its indexes, or to check after
an upgrade which definitions exist. A `Database.indexNames()` (or a listing by directory)
and a getter of the definition would close it; the definitions are stored at
`/#i/didef/-NAME` (`releases/next.md`), so the data is there.

### U14-3. No listing of subdirectories: a tenant's tree is unknown (API, low)

`UsePrimaryBuilder` lists a directory's own keys, not its subdirectories, and nothing else
lists them; there is no delete of a directory tree either. "A tenant deleted as a whole"
therefore needs the application's own record of every directory it ever wrote: a
subdirectory that the record missed (an older version of the application, a bug, a write
through another path) stays, with no way to see it from the Pub API. The application here
deletes the keys its oracle knows and checks with listings of the directories it knows.
A listing of the subdirectories of a directory (as names, like a file system's), or a scan
of a key range, would let it delete a tree for sure.

### U14-4. A rebuild under its name: the tenant's queries throw until the build ends (API, low)

To change an index's definition there is only delete and create. Under the same name, the
tenant's queries throw `NoSuchIndexException` ("The index 'by-age' is building at the
lookup time.") from the deletion until the new build ends: for 15,000 values about 0.4 s,
longer for a large directory, as a build is paced. The way around it, which the Javadoc
could give as the pattern: create the new definition under a new name (`T.byAge.v2`),
switch the queries when its `join()` returns, then delete the old one; the application
keeps the mapping (U14-2). `NoSuchIndexException` for a building index is documented
(`Connection.useIndex()`), so this is no bug; the message is clear.

### U14-5. No word on limits on the number of indexes, or on their cost (doc, low)

The Javadoc says nothing on how many indexes a database may have, and nothing on what an
index costs beyond its build (`IndexBuilder`, `Database.indexBuilder()`, the package's
"Indexes"). Measured (`Scale`, one index on each of N directories of 5 objects): 20,000
indexes were created in 3.8 s, all active at once; a put in an unindexed directory was
not slower than with none (about 100,000 a second), one in an indexed directory about
42,000 to 92,000 a second; a start with 20,000 definitions took 1.6 s against 0.05 s
without, and `indexJob()` of all 20,000 took 6 ms; 20,000 deletions 3.6 s. With 100 and
2,000 indexes nothing was measurably slower. A sentence would help a multi-tenant user: no
limit but the index name's 255 bytes; an index costs at each write of its directory (one
entry deleted and one put) and its definition at each start; deletion is one transaction
and a background cleanup linear in the entries.

### U14-6. No way to know that a deleted index's cleanup has ended (API, low)

`Database.deleteIndex()`: "its entries are removed in the background", also after a
restart, and `releases/next.md` says the time is linear in the entries; no call tells when
it has ended. A tenant deleted for good (a contract ended, a request to erase its data)
leaves its index entries for that time, and the application cannot wait for it or report
it. (In the runs here every cleanup had ended when `CoreScan` looked: no marker
`/#i/didel/` left, one generation an index.) The old states stay readable anyway until
reclaim cuts them (`Database.setRetainDuration()`), which the Javadoc says; a job for the
cleanup, as `indexJob()` is for a build, would say when the entries are gone from the
latest state.


## 4. What went well

* Every index query of every run matched the oracle: about 300,000 queries over the runs,
  with every type, nested fields, two levels, Unicode beyond the BMP, -0.0, NaN, absent
  fields, Strings over objects, a subdirectory index beside its parent's, and tenants whose
  names are prefixes of each other. No foreign key ever.
* Index churn while tenants write: 6,500 creations and 6,500 deletions a minute, rebuilds
  under the same name with another definition, 1,200 tenants deleted and made again a
  minute; four admin threads at once; every build ended, the longest a few seconds.
* A name reused at once is clean: a scan at a lookup time before the rebuild gives the
  old definition's result exactly (30 checks against a snapshot), the new one the new
  data, and the old generation's entries are gone from the latest state.
* Races: two threads creating one name, 50 times: exactly one won, the other got
  `IndexAlreadyExistsException`; two deleting it: one won, the other got
  `NoSuchIndexException`.
* Restarts with `close()` right after builds of 15,000 values started, and right after
  their indexes were deleted and made again: the builds were taken again ("building: 0
  values read") and ended, the deleted names were gone (`useIndex()` and `indexJob()` threw
  `NoSuchIndexException`). Eight crashes (`Runtime.halt`) in the middle of builds and
  cleanups: the same, and the synced deletions and creations were all there.
* The stored entries equal the oracle: 107 live indexes, each with its count of entries,
  one generation, no deletion marker, after 4,000 deletions.
* Builds are fast for a paced build: 75 indexes over 40,000 values in 0.5 to 1.2 s, one of
  15,000 values in about 0.4 s. The messages of `NoSuchIndexException` and
  `IndexAlreadyExistsException` say what happened ("building at the lookup time", "exists
  already").
* The Javadoc of `IndexBuilder` and `UseIndexBuilder` was enough to write the oracle: the
  index function's rules (kinds, NaN, -0.0, the 4,096 bytes, code points, unsigned bytes,
  keys by UTF-8) were all exact.
