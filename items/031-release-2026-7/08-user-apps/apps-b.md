# 031-08, part B. User apps: one stream, and a user's handling of the files

Created 2026-11-28 by Frans Lundberg. Status: open.

Part B of a round of "AI as the user" testing (006-20; the last rounds
024-26, 026-13, 031-02) against what `main` changed for release 2026.7:
031-06's one record an action, the new stream format and the start's new
checks (a meta block holds its own position and the database's ID, a
record's header a check of them, the tail walked before recovery writes,
a refused start that writes nothing and names the cause and the way out,
leftover files before a gap). Part A (another agent) takes the Pub API
under reclaim, `maintain(budget)`, indexes and kills with an oracle of
the contents; part B takes two fields:

1. The README's "One stream" taken at its word: "what is appended is
   decided by the stream so far and the transactions that follow, with
   their times and order, and by nothing else. A restart or a stop
   changes no byte."
2. A user's handling of the files: missing, cut, another database's, an
   older copy, read-only, a running database copied, a database of
   2026.6, a refused start and then its cause removed.

An agent of the lead played a new user: it built the release jar from a
clone of `main` (`ee8a8165`) and wrote the apps f1 to f5 from the README,
the Javadoc of the Pub API (`java/javadoc-pub.sh`), the Javadoc of the
Core's `Db`, `DbBuilder`, `FileStream` and `MemoryStream`, and
`releases/next.md`, each with an oracle of its own; the implementation
was read only to tell a product bug from a mistake of the app or the
documents after a result disagreed. Nothing in `java/src` was changed.

Made by: Claude, Anthropic's model Opus 5.5, as an agent of the lead, on
2026-11-28 from 06:16; on the branch `031-08-apps-b` of a clone.

Findings are UB-1, UB-2, ...


## 1. In short

(Written at the end; section 5 has the state.)


## 2. The applications

Each is plain Java with `main`, compiled with `javac` against
`build/bergdb-release.jar` as `java/stress/apps.sh` compiles the apps,
deterministic by its seed, functional (no result depends on the
machine's speed; the waits have limits that only a hang meets), and
prints `OK` or a `FAILED` line with the seed. Their sources are in
`java/stress/apps/f1-same-bytes/` to `f5-live-copy/`; they share
`common/Common.java` with the earlier apps, and f2 to f5 use f1's
action list and file helpers.

* **f1 SameBytes** (Core API; field 1). A list of actions from the seed:
  transactions of puts and deletes over 1,200 keys of five shapes (short
  ASCII, exactly 7, 14 and 21 bytes, 22 to 111 bytes behind a shared
  20-byte start, 1 to 12 random bytes, 111 bytes), 1 to 500 operations
  (large commits of small values, runs of keys in key order put or
  deleted), values of 0 bytes to 1 MB; `setRetainDuration()` (1 to 3 s),
  `setStartupDistance()` (20 to 400 kB, so that reclaim iterates and cuts
  every few hundred kB), `setReclaimInternalFraction()`,
  `maintain(budget)` (100 to 5,100); each action at a time of a clock that
  the app sets before it (`DbBuilder.clock()`), the same times in every
  run, with steps of 0 (the next unit) to 3.5 s (past the retain
  duration). Every run makes a new database with the same `DatabaseId`
  (`DbBuilder.id()`, which Db's Javadoc names the Pub API's; without it
  two creations differ in every meta block, UB-2) and runs the list:
  * `ref`: one start, a file stream that forces each append, a sync after
    each action;
  * `restart`: a stop (half by `stop()` then `close()`) and a start after
    one action in 25, the state checked after some;
  * `every`: a stop and a start after each of the first 400 actions;
  * `cache`: a cache budget of 1 MB (eviction all the time) and three
    reader threads that scan and get at the latest and at older times,
    each read checked against the oracle at its actual lookup time;
  * `nosync`: a file stream that does not force appends
    (`FileStream(dir, false)`), `sync()` after one action in ten, pauses
    of 0 to 120 ms after two in ten (the buffer time, 50 ms, passes or
    not);
  * `quiet` against `quietbig`: each `maintain(budget)` replaced by calls
    of `maintain(100)` at the same clock until a call writes nothing
    (Db.maintain(): "with the application idle, the calls then go quiet"),
    with a stop and a start after one call in six, against calls of
    `maintain(100000)` until quiet: the same parts in other calls (each
    part "an action of its own ... with its own time from the clock and
    one record ... planned under the write lock from the stream before the
    record");
  * `stopmid` against `quietbig`: each `maintain(budget)` a call of
    `maintain(100000)` in another thread, a `stop()` 0 to 3 ms after it
    began, a start, then calls of `maintain(100)` until quiet;
  * `copy`: at a random action the database is closed, its files copied
    in the order of their names, and the run goes on in the copy;
  * `memory`: a `MemoryStream` in place of the file stream.
  Checks: the stream length after each action equal to the ref's; every
  byte appended (read from the files after each action up to the durable
  length, and at each close, before a cut can delete it) equal to the
  ref's, and the files kept at the end equal where both runs have them;
  the first available position and time; the latest state against the
  oracle at the end and after restarts; after the last close, a start and
  a close change no stream byte and leave the files beginning with the
  file of the first available position. A difference prints the first
  differing position and the action whose record holds it (the ref's
  length after each action). Files that differ while the stream is the
  same are a NOTE (UB-1).
* **f2 KillBytes** (Core API; field 1 under kills). f1's actions for the
  seed run first in this process as the ref. Then chains of child JVMs
  run the same actions on one directory from where the stream ends, each
  child killed with SIGKILL (`destroyForcibly`): in mode `between` after
  a chosen action and its sync (the child prints and waits), `unsynced`
  the same without the sync, `random` 30 to 1,500 ms after the child's
  start, at any point of its actions, syncs and starts. After each kill:
  * K1: the files are a prefix of the ref's stream, byte for byte, but
    for zeros at the end of the last file; every action a sync returned
    for is in them; paused after an action and its sync, the files end
    exactly where the action's records end ("the database appends
    nothing by itself");
  * K2: the start (in the parent): the state is exactly that after the
    actions whose records end at or before the cut (each transaction
    whole or not at all), at least the synced ones; if the stream ended
    at an action's end the start writes nothing (every remaining file's
    bytes as before; it may delete files wholly before the first
    available position, the cut that a decided cut owes); if it ended
    inside, the bytes before the cut stay as they were; a second start
    writes nothing;
  * K3: a chain whose starts all found the stream at an action's end ends,
    after all the actions, with the ref's stream (byte for byte where the
    files are, and its length);
  * K4: after a start that completed a torn end, two copies of the files
    as the kill left them, each started and given the next 25 to 65
    actions, end with the same stream; the chain then ends.
* **f3 PubSameBytes** (Pub API; field 1 for a Pub user). The clock is a
  `TestClock` (`DatabaseBuilder.clock()`: "Use this method together with a
  TestClock to do deterministic testing"). The database is created at a
  fixed time and closed; each run starts on a copy of its files (the Pub
  API cannot give two creations one ID). The actions: puts of objects
  (long, string and bytes fields), texts and bytes, `w()` batches of 2 to
  200 puts and deletes, deletes, `rw()` counters, `setRetainDuration()`
  (1 to 3 s), `setStartupDistanceInMb()` (5 to 7), `maintain(budget)`,
  `setCacheSizeInMb()`, an index on the objects' long field created by
  `start().join()`; with the option `delete` also `deleteIndex()` and the
  index created again. Runs: `ref` (a sync after each action), `fast`,
  `slow` (pauses of 0 to 150 ms), `restart` (one action in 20), `cache`
  (4 MB, two readers that hold iterators of the listing and of the index
  across commits at frozen lookup times), `copy`. Checks: `getStreamSize()`
  after each action, every byte of the stream as in f1, the latest state
  (each directory's listing, every value, the index's scan) against the
  oracle.
* **f4 FileHandling** (Pub API; field 2). Three databases made once: A
  and B of the same shape (the same keys and value lengths, a startup
  distance of 5 MB, 500 to 700 `w()` transactions, a sync after each so
  that the app knows where each transaction's records end; every value
  begins with its database's tag and its transaction's number), and R
  with reclaim (a retain duration of 1 s on a `TestClock`), written until
  its first file begins at 1 MB or more, with a copy taken when it had
  first cut. About 65 cases a seed, each on a copy: the last file cut at
  0, 1 and 7 bytes, at record ends and one byte off them, at and near each
  200,000-byte block, at random places; a file but the last cut to a
  length that is not a multiple of 100,000, and to 100,000; the last file
  removed and the one before cut; a file missing (the first, the second,
  one in the middle, the one before the last, the last), `created.txt`
  missing, every stream file missing; B's file of the same name in place
  of A's (the last, one in the middle, the first); A's first half and B's
  second half; B's bytes, random bytes, 100 zeros and 9 MB of zeros after
  A's last record; B's stream files with A's `created.txt`; an older copy
  of a file put back, the older copy over the newer files, the older copy
  alone; every stream file read-only, the directory read-only; before a
  gap in R's files, B's first file, R's file under an earlier name, an
  empty file, R's own old files (from its earlier copy); R's second file
  missing; a database of release 2026.6 (made by the jar built from the
  tag `release-2026.6`). Each start is `open()`; the app takes the SHA-256
  of every file before and after. A refused start: its exception and
  message are printed, and no file may change; an accepted start: the
  state must be exactly that after the transactions whose records end at
  or before the cut (or a prefix where the case does not fix one), never
  a value of another database, and 25 older states read at the
  transactions' times must be the oracle's. Then the cause is removed in
  the same directory (the files put back, the permissions given back),
  and the start must take it with every transaction.
* **f5 LiveCopy** (Pub API; field 2, a running database copied). A
  writer (a startup distance of 5 MB, a retain duration of 1 s on the
  system clock, so that reclaim cuts and deletes files all the time)
  commits transactions i of a value made from (seed, i) at
  `/k/x(i mod 400).bin` and the marker `/m/last.txt` = i in one `w()`,
  syncing after one in five. A copier takes copies while it writes, by
  FileStream's procedure ("doc": list, sort by name, copy each, the last
  one last), by `cp DIR/*.bergdb COPY/` ("glob") and by `cp -R`
  ("cpr"); S is the last transaction a sync returned for before the copy
  began, C the last committed when it ended. Each copy is started with
  `open()`: it must hold the state after k transactions, S + 1 <= k <=
  C + 1, every value as written, or be refused only as FileStream's
  Javadoc allows (a listed file that a cut deleted is missing: "take the
  copy again"), with no file changed.


## 3. The runs

(Filled in as the runs end.)


## 4. Findings

No product bug that the documents do not allow was found. The findings
are about what the documents promise (UB-1, UB-2, UB-4, UB-5) and one
refusal whose diagnosis and way out are wrong (UB-3).

* **UB-1 (document). The same actions give the same stream, not the same
  files: a closed database can keep the files of a decided cut.**
  Expected: the README's "A restart or a stop changes no byte"; for the
  disk, FileStream's "The files and the disk": "the disk can hold up to
  about one file more than the stream ... and, for a while after a cut,
  the files that the cut's thread has not yet deleted", and
  `Database.getStreamSize()`: "The storage may hold a little more (a file
  storage drops whole files)". What happened: in every run the stream was
  the ref's, byte for byte; but runs without a sync after each action
  ended, after `close()`, with more files than the ref: in f1 seed 2's
  `restart` run 16 files of 200 kB (3.2 MB) wholly before the file of the
  first available position, beside 2.2 MB of stream kept; in f3 seed 1
  (the Pub API, a startup distance of 5 MB) the runs `fast`, `slow`,
  `cache` and `copy` 15 files of 1 MB (15 MB) before it, beside 11.2 MB
  of stream kept. A start and a close then deleted them (f1 checks it
  after every file run). The mechanism, read after the result: reclaim
  decides a cut (the first available position moves) and makes it, the
  storage's `pretruncate()`, only when the stream is durable past the
  decision's record, at a later commit or a `maintain()` call
  (`Reclaim.cutIfDurable()`); `close()` makes no pending cut, and a start
  makes it (`Reclaim.initFromDb()`). So after the last commits before a
  stop, the files of the last decided cut, up to the stream between two
  cut points (an iteration, at least twice the startup distance), stay on
  disk while the database is stopped and until the next start or commit;
  which commit makes it follows the write buffer's timing, so the files
  on disk differ between runs of the same actions; where both runs had
  files, they were the same files, byte for byte. Reproduction (30 s): `java PubSameBytes 1 600 DIR fast` (a
  NOTE line: "the same stream, other files"). Judgment: document; the
  README's sentence is about the stream, and FileStream's and
  `getStreamSize()`'s Javadoc could say that a closed or idle database
  keeps the files of a decided cut until the next start, commit or
  `maintain()` call. Or a small product change: `close()` makes the
  pending cut once its final flush has made the record durable, as a
  start does.
* **UB-2 (document). The README's "One stream" does not name the Pub
  API's index jobs or the creation's random ID.** Expected: "what is
  appended is decided by the stream so far and the transactions that
  follow, with their times and order, and by nothing else. A restart or
  a stop changes no byte." What happened: f3 with the option `delete`
  (the index deleted and made again): after `deleteIndex()` the stream
  depends on the speed. Seed 1, 600 actions: action 305 is
  `deleteIndex("by-n")`, action 306 a put of one key; after 306
  `getStreamSize()` is 17,019,440 in `fast`, 17,043,264 in the ref (both
  17,018,440 after 305): in the ref, which syncs after each action, the
  cleanup thread's commits came before the put. The Javadoc says it
  ("its entries are removed in the background"; `IndexBuilder.start()`:
  the build runs "in a background thread", in paced steps, and "If the
  database stops before the build ends, the next start takes it again,
  from the first key of the directory", so a stop during a build changes
  the bytes too). And the start that creates a database takes a random
  ID, which goes into every meta block and every record's check: two
  databases made by the same actions at the same times have different
  bytes, and the Pub API has no way to give the ID (f3 therefore copies
  one created database; f1 uses `DbBuilder.id()`). 031-05 named both as
  outside its goal (N9, N10) and recommended for the index jobs "(a)
  outside the goal for now, named in the wording" (Q4); the README's
  sentence names neither. With `start().join()` before the next action
  and no `deleteIndex()`, f3's runs gave the ref's bytes. Reproduction
  (40 s): `java PubSameBytes 1 600 DIR fast delete` ("FAILED seed 1:
  fast: after action 306 ... getStreamSize() is 17019440, the ref's
  17043264"). Judgment: document: the README's sentence holds for the
  Core and for the Pub API's transactions, settings and `maintain()`,
  not for its index jobs, and given the creation; it should say so
  (031-05, Q4 (a)), until Q4 (b) runs the jobs' steps inside actions.
* **UB-3 (product, a refusal's message). Another database's first file
  in place of the first: the refusal names a wrong cause, and its way out
  gives the other database's values.** Expected: Database, "What a crash
  keeps": "each meta block holds its own position and the database's ID
  ... so a start takes no meta block or record of another file or place",
  and a tail that is not the stream's own records is refused with a
  message that "names the cause and P, the position where the stream's
  own records end", with the way out: keep a copy, cut the stream at P,
  remove the later files. What happened (f4, all seeds; the probe
  `probes/ForeignFileProbe.java`, mode `first`): A and B made by the same
  puts, B's `00000000000000.bergdb` in place of A's: the start is refused
  with `BadTailException`: "The header of the record at 206200 is not one
  of this database's records at its place (bergdb 028-67, C3). The
  stream's records end at stream position 206200: from there to the
  stream's end, 23973800, it holds bytes that are not its records. A kill
  of the process during an append can leave such bytes ... To start the
  database, keep a copy of its files, then cut the stream at 206200 ...
  and remove the later stream files". Followed, the way out gives a
  database of 6 keys, every value B's; A's 24 MB, its own records, are
  what the message called not the stream's. The start takes the
  database's ID from the first meta block, B's; A's `created.txt` names
  A's ID ("database ID: fd7fc818..."), and the start does not read it
  (f4's case "B's stream files with A's created.txt" is accepted as B's
  database). Judgment: product, of low severity: the files were not
  handled "all together" as Database's "The files" asks, nothing is
  lost while the copy that the message asks for is kept, and the
  refusal writes nothing; but the diagnosis is wrong and its way out
  gives another database's values. A start could take the ID from
  `created.txt` where it has one, and refuse a first meta block of
  another ID as it refuses a file before a gap of another database
  (028-66's message: "the file and the files after the gap are of two
  databases").
* **UB-4 (document, as documented). Another database's file in the
  middle: accepted, and a read can give the other database's value.**
  Expected: never another database's value; the documents allow it:
  Database, "Errors": the checks "are a best effort, and damage that
  passes them gives wrong values with no error", and "The files": other
  damage "is refused by the start or fails a read (DbFailedException), or
  passes the checks". What happened: f4 seed 2, B's
  `00000000000066.bergdb` (the 34th of 67 files, the same name and
  length) in place of A's: the start was accepted and the latest state's
  `/k/x112.bin` was B's value, with no error; seed 3, the same case: the
  latest state was A's, and a read at an older time failed with
  `DbFailedException` (`StreamChecksumException`, a node's checksum).
  Reproduction: `probes/ForeignFileProbe.java`, mode `middle`, or
  `java FileHandling 2 DIR` (case 38). Judgment: as documented; the
  2026.7 checks of the ID and the position (meta blocks, record headers)
  guard the start's tail, not the reads of nodes and values before it. For
  031-07's review of the checksums: a node checksum seeded with the
  database's ID and the node's position would refuse such a read.
* **UB-5 (document and messages, minor). Read-only files cannot be read,
  and three refusals name no way out or no file.** (a) Every stream file
  read-only (a copy on a read-only medium, an archive): `open()`'s start
  is refused, `StreamIoException`: ".../00000000000320.bergdb (Permission
  denied)", though a start of a cleanly stopped database writes nothing;
  `DatabaseBuilder.open()` says "an application whose database must be
  there, and a tool that reads a database, use this method", and no
  sentence says that a start needs to write. (b) The directory read-only:
  "StreamIoException: Permission denied", the cause an `IOException`
  "Permission denied": no file or directory is named (it is the lock
  file, `bergdb.lock`, that cannot be made). (c) A file but the last cut,
  or an older copy of it put back: "Bad size of file
  .../00000000000072.bergdb, should have been a multiple of 100000, but
  was 199999." (`BadDirStateException`), and a file put under another
  name: "Existing files in dir ... are not in a correct state. File
  .../00000000000100.bergdb has a filename with an index value that does
  not match the previous file sizes": the file, no way out (restore the
  file from a backup, as `DatabaseMissingException`'s message says for a
  missing stream). Every refusal changed no file, and after the cause was
  removed every start was accepted with every transaction. Judgment:
  document (`open()` needs write access to the directory and the last
  file) and messages.


## 5. State

(Filled in.)
