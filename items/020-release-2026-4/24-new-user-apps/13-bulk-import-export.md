# 020-24-13 Bulk import and export

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of release 2026.4 would write it
(020-24's brief, round 5): the release jar alone on the class path, and
only what a user reads (README.md, the Pub API's Javadoc in
`java/src/bergdb/pub`, `overview-pub.html`, `releases/next.md`). The jar
was built from `b0eba12`. Nothing in BergDB was changed.


## 1. The application

**What it does.** An ETL job: it imports millions of small records from a
CSV file, exports them back, deletes them all and imports them again, as a
nightly reload does. Each phase is a JVM of its own (`run1.sh PHASE ...`;
`run.sh N KN` runs them all and prints `APP OK`; each phase exits non-zero
at the first wrong result):

1. `gen`: a CSV of N records in key order, and a second version of each
   record for the reload. A record is a function of its id: id, sku, a name
   of 1 to 3 words (among them "kök", "日本語", an emoji, `a,b`,
   `say "hi"`, a tab), one of 50 categories with a shared prefix of 46
   chars, a price of 0 to 999 (many ties), a quantity, a note of 0 to 80
   chars with commas, quotes, "é" and "€". Quoted CSV, UTF-8.
2. `import`: reads the CSV, parses each line, and puts each record as a
   Data Object `Rec` at `/imp/<name>`, in batches of 1, 3, 10, 100, 1,000,
   5,000, 20,000, 100,000 and 300,000 records, in turn; even batches as
   `w()`, odd ones as `rw()`. The index `by-cat-price` (category, price)
   is created on the empty directory before the first import. The keys
   share a prefix of 109 chars and come in four families that differ only
   after it (`...shelf-0000000002`, `...shelf-a0000000004`,
   `...shelf-b...`, `...shelf-ö...`), so the key order is not the id
   order, and one family is not ASCII.
3. `export`: the primary scan with paging (`usePrimary().dir()`, then
   `startAt(last).inclusive(false)` for each next page, at one frozen
   lookup time), written back as CSV and compared byte for byte with the
   source; then the index scan with paging: the whole index in order
   (category, price, key), a page of 1,000 at a time, resumed by
   `eq(category).from(price, true)` and skipping the keys seen at that
   price, then `from(category, false)` when a category ends. Each entry's
   record must equal the source, each id once, in strict order, all N.
4. `delete`: every key, in transactions of 500,000, 1,000,000 and
   2,000,000 deletes (`w()` and `rw()` in turn); then the primary scan and
   the index must be empty, and gets of every 9,973rd key null.
5. `export ... past`: the whole export again at the lookup time before the
   deletes, compared byte for byte.
6. `import` of the second version, `export` of it (primary pages of 777).
7. The kill test, on a database of its own: `killer` starts the import in
   a child JVM that syncs after every third batch and logs each commit and
   each returned sync to a progress file, and kills it with `kill -9`
   after some seconds; `resume` starts the database, checks what the kill
   kept (each batch whole or absent, no batch after a missing one, every
   batch up to the last synced one there, one index entry for each record
   there), then imports from the batch after the last synced one, or
   starts another child and kills it again. Three kills, then the import
   to the end and the full export.
8. `limit`: transactions at the size limit that the Javadoc gives, "more
   than 7/8 of 2^31 - 9 bytes, about 1.88 GB, in the stream", and over it:
   19 values of about 99 MB just below it and 1 MB over it, by `w()` and
   by `rw()`; one `put()` of a single value over it; 1,000,000 values of
   about 1.8 KB whose keys and values are 10 MB below it; a restart.

**Size.** `App.java`, about 620 lines, `Probe.java` (kill -9 during a
transaction of 1.88 GB), `run.sh` and `run1.sh`, in
`/Users/f/fl/bench/2026-11-09/app-u13/app/`. Outputs in `app-u13/`:
`run1.txt` (the whole job), `limit-large.txt`, `limit-small.txt`,
`dry.txt` (a run with 100,000 records).

**The runs.** A dry run of every phase with 100,000 records and 300,000 for
the kill test printed `APP OK` (`dry.txt`). The full run (`run1.txt`):
the kill test on 1,000,000 records, three kills and the resumption, then
the import of 5,000,000 records, 705 MB of CSV, in 108 batches (258 s),
and their export, primary (88 s) and index (202 s). Each phase passed. The
run was stopped in its delete phase, after a first `w()` of 500,000
deletes (52 s), so that the probes could go first, and on the
coordinator's word it was not resumed: the deletes, the past export and
the reload of 5 million are unchecked (`run-rest.sh`); the dry run of
100,000 passed them. The probes are in section 4. The machine had a load
of 20 to 27 from other sessions, so the times are not measurements.

| What                                      | Records   | CSV      | On disk  | Stream files |
|-------------------------------------------|-----------|----------|----------|--------------|
| import, 100,000 records                   | 100,000   | 13.8 MB  | 105 MB   | 50           |
| the same, after deleting all of them      | 100,000   |          | 211 MB   | 55           |
| the same, after the reload                | 100,000   |          | 344 MB   | 62           |
| kill test: 3 kills, resumed, 1M records   | 1,000,000 | 140 MB   | 1,449 MB | 75           |
| import, 5,000,000 records                 | 5,000,000 | 706 MB   | 6,030 MB | 89           |
| the limit test: two transactions of 1.88 GB |         |          | 3,760 MB | 84           |

Starts (`getStartupDuration()`): 5 to 10 s for the database of 100,000
records, 5 to 12 s for the kill test's, 16 s for that of 5 million; 27 to
75 s after a transaction of 1.88 GB (U13-7).


## 2. The findings

No wrong result, no throw from legal use and no hang in what ran: every
count and value agreed with the source. The findings are of the
documentation and the API.

| ID    | Kind | Severity | What                                                  | Reproduction  |
|-------|------|----------|-------------------------------------------------------|---------------|
| U13-7 | doc  | medium   | after a transaction of 1.88 GB each start takes 27-75 s | 4.1, U13-7    |
| U13-1 | doc  | medium   | a long key costs ~6 times its length; Pub API silent  | 4.3, import   |
| U13-2 | doc  | low      | the size limit counts about 36 to 39 bytes a KV more  | `limit small` |
| U13-3 | doc  | low      | the crash rules of a resumable import are in 3 places | the kill test |
| U13-4 | API  | low      | no delete of a directory: list and delete each key    | `delete`      |
| U13-5 | API  | low      | paging an index of two levels needs three scan forms  | `export`      |
| U13-6 | doc  | low      | starts of 5 to 16 s for 0.1 to 5 million records      | the starts    |

### U13-1. A long key costs many times its length (doc, medium)

The brief's keys share a prefix of 109 chars, as keys made of a tenant, a
region and a path do. A record is about 140 bytes of CSV, about 126 bytes
of key and a stored object of about 150 bytes; with its index entry,
perhaps 450 bytes. The stream took 1,050 bytes a record for 100,000
records, 1,206 bytes for 5 million (6.03 GB for 706 MB of CSV, 8.5
times). Nothing in the Pub API's Javadoc says what a key costs or how
long it may be: `Connection`'s "Keys" gives only the syntax. The Core's
`Db` (020-24-09, U9-5) says it: "a key is stored as a path of key nodes, a
level for each 7 bytes, so that a key costs memory, stream bytes and time
in proportion to its length, many times what a value of that length
costs ... Keep keys short". A user of the Pub API, whom the overview
steers away from the Core, does not read that. The figure (section 4.3):
the same 100,000 records with names of 11 to 12 chars took 42.5 MB of
stream, with names of 120 to 122 chars (the shared prefix) 105.3 MB, so
110 more bytes of key cost about 630 bytes of stream a record, almost 6
times their length, and the import took about twice the time. Suggested:
the same sentences, with such a figure, at `Connection`'s "Keys" and in
the package page, and a word on the size on disk to expect for N
records.

### U13-2. The size limit counts more than the keys and values (doc, low)

`Connection.put()` and `WBuilder.execute()`: refused if "its values and
keys taking more than 7/8 of 2^31 - 9 bytes, about 1.88 GB, in the
stream". At the limit, with 19 values of 99 MB, it holds to the byte: a
`w()` and an `rw()` of 1,878,848,640 bytes of keys and values were taken,
and 1,880,048,640 refused at once, nothing written, the database going on.
But a `w()` of 1,000,000 values of 1,847 bytes, keys and values
1,869,048,184 bytes, 10 MB below the figure, was refused: "its values and
keys take 1908048184 bytes in the stream, more than 1879048178"; 39 bytes
a KV more (36 with the large values). An ETL job that sizes its batches
by bytes cannot know that. The limit in the message, 1,879,048,178, is 6
bytes below 7/8 of 2^31 - 9 (1,879,048,184). Suggested: say "keys,
values and about 40 bytes for each KV", or give the limit as the
message's number. (`limit-large.txt`, `limit-small.txt`.)

### U13-3. The rules for a resumable import are in three places (doc, low)

The resumption needed three facts: a `w()` and an `rw()` are whole or
absent after a crash (the package page's "all of them, or none", for
`w()` only); a crash keeps a prefix of the transactions, in commit order
(`Database`'s "The files": "a cut tail of the stream ... only transactions
that no sync() had returned for"); and `Connection.sync()` makes durable
"the last transaction started with this connection", so, it seems, every
earlier one. Each kill agreed (batches whole, a prefix, every synced batch
there, the index matching). Suggested: one paragraph, "What a crash
keeps", at `Database` or `Connection.sync()`, that says the three and that
an `rw()` is whole too.

### U13-4. No delete of a directory (API, low)

"Delete everything" is a listing of every key and a delete of each, in
batches; the job reads the 5 million keys from its CSV. `Database`'s "A
full disk" says that a delete writes, so a reload doubles the stream
(100,000 records: 105, 211, then 344 MB), as documented. A delete of a
directory, or of a key range, would save the listing; not needed for
2026.4.

### U13-5. Paging an index of two levels (API, low)

Known as U4-4 (no resume point). For the index (category, price), a page
resumes with `eq(category).from(price, true)`, skips the keys already
seen at that price (up to 100 here), and, when the category ends, goes on
with `from(category, false)` on level 1. It works (5,000,000 entries in
5,025 pages, in order, each once), but every user writes this loop.

### U13-6. Starts of 5 to 16 s (doc, low)

`getStartupDuration()`: 5 to 10 s for 100,000 records (105 to 344 MB of
stream), 16 s for 5 million; `DatabaseBuilder.startupDistanceInMb()`
says about 0.6 s for 100,000 keys and 3 to 5 s at 50 MB for 10 to 50
million keys. Under a load of 20 to 27, so no measurement; the same as
U4-6.


### U13-7. After a transaction of 1.88 GB every start takes 27 to 75 s (doc, medium)

A start reads the startup section, about the startup distance of stream
(50 MB by default), so the README promises that "startup time does not
grow with the size of the database". After one transaction of 1.88 GB,
the limit's size, each start read for 27 to 30 s (`bdb`, section 4.1:
after the transaction, again after a small put and a close, and again at
the first start of the probe `tailwrite`, 30.2 s); with two
such transactions, 46 and 75 s (`ldb`, the limit test). The start's time
followed the large transaction, not the database: after 150 MB of small
puts after it, the start took 0.6 s (`probe-tailwrite.txt`). So it seems
that a start rereads the last transactions whole, back to one that ends
before the startup section, and a transaction larger than the startup
distance makes the section that large until enough is written after it.
Not a wrong result, and the start ends; but a user who imports in large
transactions and then restarts, as an ETL job does, waits up to minutes,
and nothing says why or what helps. Suggested: say it at
`startupDistanceInMb()` and at the size limit of `Connection.put()`
("a transaction larger than the startup distance makes each start read
it, until about 2 to 3 times the startup distance is written after it"),
or bound the start in this case. Reproduction: `Probe bigkill DIR 45 3`
(a child writes and syncs 19 values of 99 MB in one `w()`), then `Probe
open DIR` twice, then `Probe tailwrite DIR 150`.

## 3. What went well

* Every count and every value agreed with the source, after every phase:
  the import of 1 and 5 million records through batches of 1 to 300,000
  records, the exports by both scans, byte for byte, and the three kills
  and the resumption; in the dry run of 100,000 records also the deletes
  of everything, the state at the time before them, and the reload.
* The transaction size limit is where the Javadoc says, to the byte, and
  its refusal is clean: in about a second, nothing written, the database
  goes on, and the message gives the transaction's size in the stream and
  the limit. A `w()` and an `rw()` of 1.878 GB were taken, and read back
  equal after a restart.
* The Javadoc's crash rules were enough to write the resumption: a `w()`
  is "all of them, or none", sync() makes the transaction durable, and a
  start recovers a cut tail. Each kill left whole batches, a prefix of
  them, every synced batch there, and an index that matched the data.
* `usePrimary().dir().startAt(name).inclusive(false)` pages a directory
  simply and correctly, also over keys with a shared prefix of 109 chars
  and a family whose names are not ASCII; `freezeLookupTime()` keeps the
  pages at one state; the earlier state after the deletes is a
  `setLookupTime()` away.
* The Javadoc's examples and the package page were enough for the whole
  application; the only lookups were the limits and the crash rules.


## 4. The probes

`Probe.java` and `probes.sh`, run after the main run (`probes.txt`,
`probe-tailwrite.txt` in `app-u13/`). No wrong result, no data lost after
a crash, no failed start and no hang.

### 4.1. kill -9 during a transaction of 1.88 GB

A child JVM starts the database, puts and syncs a small value, then
executes one `w()` of 19 values of 98.9 MB (1.879 GB less 300,000 bytes)
and syncs it; the parent kills it with `kill -9` after N seconds,
restarts, and checks: the small value there, the large transaction whole
or absent, there if its sync returned; then a put, a sync, a restart and
a get of it. Three rounds on one database:

| Round | Kill after | The child at the kill             | Start after | Large transaction |
|-------|------------|-----------------------------------|-------------|-------------------|
| 1     | 15 s       | in `execute()`, nothing written   | 0.1 s       | absent            |
| 2     | 27 s       | in `execute()`, 1.8 GB written    | 6.2 s       | absent            |
| 3     | 45 s       | had ended: executed and synced    | 27.3 s      | there, whole      |

Each round's put after the recovery, and its restart, worked. After
round 2 the stream kept the 1.8 GB of the cut transaction: the database
grew from 1.8 to 3.5 GB in round 3, though only one large transaction is
in it. That fits "a start ... completes a cut tail" (`DatabaseBuilder`),
but a user does not learn from it that a crash in a large transaction
leaves that much dead stream for good (with the default retain
duration). Low; not in the table.

### 4.2. Keys of up to 1,000,000 chars with shared prefixes

90 keys in `/long/`: names of `x` repeated L times, L = 1, 100, 127, 128,
255, 256, 1,000, 4,095, 4,096, 4,097, 8,192, 65,535, 65,536, 65,537 and
1,000,000, each alone and followed by "a", "b", "ö", an emoji (a
surrogate pair) and U+FFFF; put by `put()` and `w()`, with a String at a
`.txt` key of the same name in a second directory. Every get, the
scan's order (the names' UTF-8 bytes, so the emoji after U+FFFF), and
`startAt(name)` forward with `inclusive(false)` and backward from every
one of the 90 names were right, before and after a restart; the deletes
emptied the directory. A put of a key of 1,000,001 chars after one of
1,000,000 took 1.1 to 1.3 s, as the Core's `Db` says of long keys with a
long shared start.

### 4.3. Short keys against long keys

The same 100,000 records (`gen`, `import`), names of 11 to 12 chars
(`-Dshort=1`) against the main run's names of 120 to 122 chars: 42.5 MB
of stream in 41 files and 3.4 s, against 105.3 MB in 50 files and 7.2 s
(U13-1).


## 5. Fixes

By fixer x28 for coord-1109, 2026-11-09, in `/Users/f/fl/bench/2026-11-09/clone-x28`, branch
`x28-rebased` (worktree `clone-x28-rb`), on main at `b3a6b05`, all in `2508989`. These are
Javadoc changes only, with no change of behaviour, and an entry in next.md's Documentation.

* U13-1: `Connection`'s "Keys" now says that a key is stored as a path of key nodes, a level
  for each 7 bytes, and costs many times its length. The package's "Good to know" points to
  it. Its figures come from a test of 200,000 keys with values of 11 bytes, written 1,000 to
  a transaction:
  * about 70 bytes of stream for a key of 13 bytes;
  * 1,200 to 1,400 bytes for a key of 114 bytes whose first 100 differ from key to key, in
    key order or not;
  * about 190 bytes for keys of 120 bytes that share their first 109.
* U13-2: `Connection.put()` now gives the limit to the byte: 1,879,048,178
  (`StoredTrans.valueLimit()`, `(2^31 - 9) / 8 * 7` in integers). It also says what
  `Db.checkSize` counts, which is `StoredValueNode.getByteSizeLong` for each KV, the index
  entries included:
  * 28 bytes and the value's bytes for a put, 24 bytes for a delete;
  * 8 bytes for each segment of the key: its bytes / 7 + 1, the bytes being its UTF-8 and one
    for each '/';
  * each KV rounded up to 4 bytes.

  This gives 1,908 bytes a KV for the refused `w()` of values of 1,847 bytes, as its message
  said. `WBuilder.execute()` refers to it.
* U13-3: `Database`'s new "What a crash keeps" holds the rules, which the code confirms:
  * each transaction, an `rw()` too, is one record with its index entries, in commit order;
  * a crash keeps a prefix of the transactions, each whole or absent;
  * a `sync()` returns when every byte up to its transaction is durable (`Db.sync`), and so
    it covers every earlier transaction.
* U13-7: `DatabaseBuilder.startupDistanceInMb()` now says that a start reruns each
  transaction of its startup section whole. A transaction larger than the startup distance
  makes every start read all of it, until about twice the startup distance has been written
  after it. A probe on the Core, at a startup distance of 5 MB, after a transaction of
  200 MB:
  * starts took 3.1 s, and 2.7 s after a small put, with a section of 200 MB;
  * after 10 MB more of small puts, a start took 0.07 s, with a section of 4.6 MB.

  README.md is unchanged.
* U13-4, U13-5 and U13-6: not in this round. U13-4 and U13-5 are API wishes; U13-6 is not
  measured.
