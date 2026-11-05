005-todo
========

Created 2026-10-19 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.

Since 2026-11-03, new entries go to 015-todo, numbered from 015-01. An
entry closely related to a 005 entry may still be added here, for now.


The list
========

Two tables: what is left to do, and what is closed. A subitem's own
`Status:` line is the source. When an entry closes (done, dropped or
moved), its row moves from Open to Closed in the same edit, with the date
it closed; Closed is newest first. Files stay where they are, so links to
them keep working.


Open
----

| ID | Kind | What | Status |
|---|---|---|---|
| [005-47](47-written-not-forced.md) | Decide | A durability of "written, not forced". Decided (Frans, 2026-11-04): A, a setting of `FileStream`, per-append forcing on (the default) or off, in the core API only, no force at an interval; implemented, with forces kept at a new file, its predecessor, a cut and `close()`, and a power-loss mode without per-append forces. Sync latency on s1 (1 thread): p50 4.2 ms on, 0.1 ms off. Left: the same on F53, in a quiet block (not quiet on 2026-11-05, not run); holes in the unforced tail are 014-01's | open |
| [005-65](65-gets-with-8-readers.md) | Investigate | Gets of 27 and 36 ms with 8 readers in ScaleBench from the OS's cache at 665 MB under ZGC (`bf19075`: 2.1 ms), with 22 and 26 waits of a reader's load for the eviction thread over 10 ms (item 009's target 2, not yet met there). Measured 2026-10-28 night, quiet: only with 8 threads, on `eaec93e` (005-46) and `4f7cd60` alike; no load waited for a batch; the machine at 9.6 of 10 cores, and the loads' entries into `evictorLock` in `Eviction.wake` (78,000 a second) a fifth of the gets over 10 ms. Frans decided 2026-10-29: the fix, in `main` (`988fe1a`): a load skips that monitor when a request to the eviction thread is pending (an untimed count with 8 readers: 116,000 to 128,000 entries a second before, about 570 after); the rest accepted as a full machine. Rerun 2026-11-04: the entries a second 81,877 to 484, but the gets over 10 ms rose, 298 to 492. Frans approved an AB/BA step (2026-11-05), to close the entry if the rise is not the fix's; not run on 2026-11-05, F53 not quiet | open |
| [005-78](78-retain-duration-in-stream.md) | Investigate | The retain duration is not kept in the stream: it decides when reclaim's iterations start and where it cuts, so the stream's bytes, but a start takes the builder's value (default forever), against the rule of 005-53 and 005-52 (a setting that changes the stream's bytes is kept in the stream, 010-P2) and without a word in its Javadoc. Frans: it must be in the stream; study first. Forms: the meta blocks (as the startup distance), an internal KV, or reclaim's table | open |
| [005-81](81-overload-and-retries.md) | Investigate | Transaction retries: `executeRw()` reruns a conflict after hard-coded sleeps from 10 ms doubling to 10,240 ms, with no jitter, attempt limit, time budget or setting (over 20 s across eleven reruns on a hot key), and the same `RerunException` for a long action that outlives `KeyModSet`'s history. Left: the wait points and client contract the retries need, a diagnostic harness from 006-11's, hot-key and disjoint-key baselines, the retry variants measured, and an `executeRw()` proposal. Split 2026-11-04: overload and admission control are 017-06 | open |


Closed
------

| ID | Kind | What | Status | Closed |
|---|---|---|---|---|
| [005-52](52-cache-size-while-running.md) | Fix | Change the cache size while the database runs: `Database.setCacheSizeInMb` (`fd8f513`); after a decrease a transaction's warmup no longer waits for eviction (option B, `0c6c4be`) | done | 2026-11-05 |
| [005-72](72-file-layout-after-cut.md) | Decide | The files after a physical cut depend on timing: B dropped, A covers it | done | 2026-11-05 |
| [005-77](77-cap-pace-factor.md) | Investigate | Cap the pace's factor S/sd: moved to 015-84 | moved | 2026-11-05 |
| [005-60](60-block-storage.md) | Investigate | Block storage: moved to 017-05 | moved | 2026-11-04 |
| [005-54](54-open-bounds.md) | Investigate | The bounds still open: moved to 017-04 | moved | 2026-11-04 |
| [005-11](11-replication.md) | Decide | Replication: removed, copies left to the OS and the file system (Frans: "A with C2 now"); a future design is 017-03 | done | 2026-11-04 |
| [005-07](07-transaction-synchronization.md) | Investigate | Synchronization of transactions: obsolete since handles (009) | dropped | 2026-11-04 |
| [005-06](06-publication-literature.md) | Investigate | The literature and a publication: moved to 017-02 | moved | 2026-11-04 |
| [005-05](05-bergdb-future.md) | Decide | What to do with BergDB: moved to 017-01 | moved | 2026-11-04 |
| [005-79](79-integers-not-doubles.md) | Implement | Integers, not doubles, in the Core's decisions | done | 2026-11-03 |
| [005-82](82-gettrans-corruption.md) | Fix | getTrans fails the database on a corrupt record | done | 2026-11-03 |
| [005-69](69-system-clock-promise.md) | Fix | SystemClock keeps its promise | done | 2026-11-03 |
| [005-71](71-dbclock-read-time-after-start.md) | Fix | DbClock read time after a start: a note in P2 | done | 2026-11-03 |
| [005-80](80-setbudget-race-record.md) | Decide | setBudget's race recorded, with a test | done | 2026-11-03 |
| [005-83](83-recovery-before-refusal.md) | Investigate | Correction: 014-01 | moved | 2026-11-03 |
| [005-76](76-wake-at-a-quarter.md) | Fix | Wake at a quarter | done | 2026-11-02 |
| [005-73](73-db-api-small-findings.md) | Fix | Core API fixes | done | 2026-11-02 |
| [005-75](75-core-checks-and-comments.md) | Fix | Core checks and comments | done | 2026-11-02 |
| [005-74](74-parser-corrupt-sizes.md) | Fix | Reject corrupt sizes | done | 2026-11-02 |
| [005-70](70-keymodset-after-start.md) | Fix | STM startup boundary | done | 2026-10-30 |
| [005-64](64-buffer-time-after-group-commit.md) | Investigate | The buffer time after group commit, 20, 50 or 100 ms: since 005-48 a sync no longer waits for the timer, which now only bounds how long bytes nobody syncs on stay buffered. Runs of 2026-10-28 on F53 and s1: 50 ms saves 11 to 35 % of the forces of writers that do not sync, with the same throughput, latency and CPU; 100 ms costs 13 to 16 % of the throughput at 1 KB values (the quarter rule seen only at a wake, now 005-76); idle and trickle energy the same; twice the unsynced data at risk at 50 ms (question 5). Decided (Frans, 2026-10-29): 50 ms. `StorageManager.DEFAULT_BUFFER_TIME` 20 to 50, its comment, the docs, `releases/next.md`; StreamDigest identical; the four gates pass | done | 2026-10-29 |
| [005-68](68-fix-take-stream-length.md) | Fix | `Db.store` passes the stream's `getLength()` to `TransSeq.take`, where the Lean model's argument is where the record begins, `getNextPos()`: after a record that ends on a 200,000-byte boundary they would differ by the meta block's 128 bytes, and Java could leave T3's bound (007-08, review, point 1). Dropped: the finding does not hold. `RecoverableStream.append` writes a meta block together with the record that ends at its position, and recovery fills out one that a crash cut, so when `take` is called the two are equal: by reading, and by running an instrumented copy (0 of 5,524,901 calls differ, 229 after a record that ended exactly on a boundary). No change; the one-line change would pass the same value | dropped | 2026-10-28 |
| [005-53](53-startup-distance-on-the-fly.md) | Investigate | The startup distance on the fly: the Pub API could not change it for an existing database (against 010-P6); the core could since 2013-04, through JMX only. Investigated (the history, `Reclaim`'s fault fixed as 005-61, the decrease measured in 007-06 and 007-07) and decided after D4:B (Frans, 2026-10-28): option E, `Database.setStartupDistanceInMb` and `getStartupDistanceInMb`, kept in the stream's meta blocks as before, one call, no steps and no `Job`; a call with the value in force writes nothing, a refused call changes nothing. Implemented with 005-52 (`fd8f513`); StreamDigest identical | done | 2026-10-28 |
| [005-67](67-fix-test-add-replica2.md) | Fix | `StorageManagerTester.testAddReplica2` failed about one gate run in twelve on a busy machine, "Expected 700, got 200", since 2015 (Frans's note): the test was wrong, not the code. It asserted both streams' lengths right after an append, but an active replica only means that the sync's last bytes are in the replica's buffer, which writes them a little later, and both buffers write an append within milliseconds. Now it waits for the confirmed lengths; `testAddReplicaWhileAppending`'s writer, which appended without the write lock and could hang the test, takes it. Forced interleavings: each failure certain before, none after; 400,000 runs after the fix without a failure (4 in 40,000 before). 2015's "Expected 800, got 1200" was `BufferedStream`'s flush of nothing at a close, fixed by 005-14. Test code only | done | 2026-10-28 |
| [005-62](62-lean-t9-t12-over-handles.md) | Fix | Lean: T9 and T12 over handles, so that the design before handles can go. Both proved (`t9_handles`, `t12_handles`), reviewed at max effort. Then, as Frans decided (2026-10-28), the design before handles removed from lean/: Evict.lean and its proofs, EvictExample.lean, and the seven theorems over it with a counterpart over handles; the startup with handles proved over handles (HandleStart.lean); the assumptions of stage 2 and `Mem.sectionPos` in Phys.lean; lean/ from 144 files and 66,452 lines to 119 and 51,539. And rule 4 by position after a cut, with Java's skip of the pointers below the stream's first position, proved to link what rule 4 by node id links (`rule4PosCut_handles`, `runPosCut_handles`), so T12 holds for Java's startup; no new assumption. A theorem for a cut without a restart: not for now (Frans) | done | 2026-10-28 |
| [005-66](66-builder-opens-at-start.md) | Implement | The Pub API's builder opens the directories in `start()`: `dir()` and `replica()` opened their `FileStream`s at once, and since 005-63 a builder that was never started, the first of two `dir()` calls or a replica given before `dir()` held a directory's lock until the JVM ended (a builder has no `close()`). Now they record the directories and `start()` opens them, the database's first, and closes them if it fails (005-32); a bad or busy directory is reported by `start()`; a replica given before `dir()` is kept. Two tests that fail on the code before; `releases/next.md` | done | 2026-10-28 |
| [005-56](56-package-dependencies.md) | Investigate | Package dependencies against the `package.html` files; Frans's question. Decided 2026-10-28, as the entry's table proposed: the lists of `pub` (`common`, `nanotest` for its tests, `pubimp` for `Factory`'s designed cycle) and `pubimp` (`dag`, `pub.util`, `storage`) changed, all in one form, `Depends on: a, b, c.`; `SyncLevel` moved from `core` to `pub.util` (an API change against 2026.1, in `releases/next.md`); `Database.PRIMARY` and `TestClock`'s range in `pub`; `TimeResolver` stays in `pubimp`. `java/deps.py` checks each package's uses against its list, a step of `before-commit.sh`. Follow-ups 2026-10-28: titles, `src-dev`'s lists, the Core Layer built alone nightly (`java/stress/core-build.sh` in `night.sh`) | done | 2026-10-28 |
| [005-48](48-group-commit.md) | Investigate | Group commit: a sync that waits has the buffer written at once (`BufferedStream.flushSoon`) instead of waiting for the timer, and the force paces the groups (005-13's question 5). In `main` since 2026-10-27 (`e611709`): on s1 one thread's durable commits went from 38 to 213 a second, the sync's median from 24.8 to 3.8 ms, 64 threads' from 2,364 to 6,429; writers that do not sync and the stream's bytes unchanged. Closed by Frans with the buffer time kept at 20 ms; whether 50 or 100 ms is better now is 005-64 | done | 2026-10-28 |
| [005-63](63-one-database-per-directory.md) | Decide | One database per directory, also while one closes: `stop()` returns before the close, and since 005-46 the cut's files are deleted afterwards, so a database started on the same directory right after `stop()` could adopt files that were being deleted and fail (level2's `BryanRepro`, fixed in the test with `close()`). Decided 2026-10-28, option C: `FileStream` holds an operating-system lock on `bergdb.lock` in its directory until it is closed, and a second one on the directory, in the JVM or in another process, is refused with `DirectoryInUseException`; within the JVM a set of the locked directories refuses first, as closing a second channel of the file released the lock for other processes (macOS, Linux), a deviation from 010-P9; `stop()`'s Javadoc says to start again after `close()`; network file systems in `FileStream`'s Javadoc; tests, `releases/next.md` | done | 2026-10-28 |
| [005-59](59-autocloseable.md) | Decide | `Db` and `Database` as `AutoCloseable` (005-55's question 6). Decided 2026-10-27, option A: both implement it, `Database` gets a `close()` that waits as `Db.close()` does, so try-with-resources closes the database; Javadoc, tests, a line in `releases/next.md` | done | 2026-10-27 |
| [005-61](61-reclaim-startup-distance.md) | Fix | Reclaim spaced its iterations by the builder's startup distance, copied before `start()` read the stream's, and never saw `setStartupDistance`: reclaim ran too seldom or too often (found in 005-53, question 3; no wrong cut). Now it uses the database's live startup distance; two unit tests that fail on the code before; StreamDigest identical | done | 2026-10-27 |
| [005-49](49-smooth-index-writes.md) | Investigate | Smooth index writes: at large startup distances the index was written in bursts (records of 2.5 to 11.6 MB, up to 72 times their own bytes), and 007-03's deadline alone made records of up to 110 MB. Recommended for 007-03's step 3 (report.md): a paced take, each commit writes the waiting dirty index nodes oldest first, in whole transactions, in proportion to the stream it adds, with the deadline at 2 sd as the backstop (it never fired); the section stays at about sd; at the startup distance that gives today's peak section it writes 3 to 13 percent fewer bytes a put, with records 6 to 11 times smaller. Frans: the startup distance's setting is the section's target, the actual startup distance what a start reads from; the default stays 50 MB | done | 2026-10-27 |
| [005-58](58-lean-rule4-by-position.md) | Investigate | A Lean theorem for rule 4 by position (005-57). Proved in the model: `Rule4_positions` (a pointer that rule 4 links names a version of the startup section, the version before its node's first one there, or its canonical object's version) and `Rule4Pos_handles` (rule 4 by position links what rule 4 by node id links, at every startup of a run), with no new assumption; new trusted definitions of Java's rule 4 by position in `SIS/Handle.lean`. Frans took the trusted additions as they are, and the by-id check under assertions in `linkToCanonical` stays (2026-10-27) | done | 2026-10-27 |
| [005-46](46-stream-file-lock.md) | Fix | A read of the stream's last file waits for the writer's append and its `fsync` (`FileStream.DbFile`, one monitor for both): seconds on s1's disk, the longest waits left there with handles (009-03); and every read waits while reclaim's physical cut deletes files (`FileStream.pretruncate`, the stream's monitor): up to 171 ms in P4's soak on F53, under every collector (009-04). Investigated 2026-10-27, with probes: every read also waits while a new file is forced (`newFile`), an encrypted database's reads wait for each other, and a commit by an interrupted thread that makes a physical cut fails the database. Proposed: positional reads on a channel of each file's own, safe from interrupts; the file list without a lock; a new file made, and a cut's files deleted on a thread of their own, outside the stream's monitor. Decided 2026-10-27: as proposed; `SalsaStream` and interrupts in this entry (today an interrupt can fail the database, a commit that waits for room in the write buffer or makes a cut, or hang it, the storage thread interrupted; a rule proposed, one question open); the test reports note a writer's waits for room, which do not count against item 009's target 2. Implemented 2026-10-27, rule A for interrupts; measured the same day on s1 and F53: no read waits for a force, a new file or a cut any more, and a commit only for room in the write buffer when the disk stalls. Done 2026-10-27, at Frans's word; P4's soak and ScaleBench in 006-09's quiet block confirm it, and are item 009's evidence | done | 2026-10-27 |
| [005-03](03-sweep-cost.md) | Investigate | The sweep's cost under read churn (item 001, finding 10). Done by item 009: handles removed the sweep; the capacity controller runs batches of at most 2 ms, and in P4's soak the writer and the readers keep their paced rates (009-04) | done | 2026-10-27 |
| [005-51](51-eviction-on-calls.md) | Fix | Eviction only in response to the calls: the eviction thread woke once a second while the database was open, also when idle (`evictorLock.wait(1000)`), against 010-P3. Now it waits with no timeout, the database's close wakes it, and `close()` returns after it has ended | done | 2026-10-27 |
| [005-57](57-startup-header-reads.md) | Investigate | Startup without rule 4's header reads: a cold start at 10M keys took minutes on s1, most of it rule 4's reads of a header for each stream pointer of D's nodes (007-05). Rule 4 now finds a pointer's node by its position (the startup section's `posToId`, the canonical objects' positions), with no read but for a top node's pointer, checked against rule 4 by node id at every startup of the tests; with it, in the prototype, a cold start on s1 at 10M keys took about 46 and 51 s at 50 and 200 MB, where it took 214 and 210 s. Part 1 of the report; part 2, the writer's reads, not made (Frans: "Part 1 alone") | done | 2026-10-27 |
| [005-55](55-fix-finalize.md) | Fix | The note of deprecated API that every build printed: `finalize()` (six uses) and `Class.newInstance()` (two). `Db.finalize()` stopped a database that the application dropped without `stop()`, as the Pub API promised. Decided 2026-10-27: no safety net. Now `stop()` or `close()` is required (the Javadoc of `Db` and of `Database.stop()`), the 188 unit and f-tests that left a database running stop it, and so do two night tests and two stress programs, which ran out of memory without `finalize()`; `bergdb.dev.Unit`, `F` and `Night` fail when a test leaves one; `ValueNodeTotalMem` deleted, `newInstance()` replaced; `build.sh` prints no note (Frans: "finalize() need to go") | done | 2026-10-27 |
| [005-50](50-fix-node-size-start.md) | Fix | A start with another node size than the stream was written with failed with what looked like a corrupt stream (`StreamFormatException: startup error, node ... not found`), or started, and could then leave a stream that no start opened, with either size. Now the size is in every meta block, 2 bytes at offset 44 that were reserved (so no new version: release 2026.1 starts a new database), and a start refuses another size with a `StreamFormatException` that says what to do, and a database without one, written before, with a `VersioningStreamException`, before recovery writes (005-38) | done | 2026-10-27 |
| [005-38](38-writes-at-scale.md) | Investigate | Writes at scale: the stream grew to about 1.1 KB per key at 100M random keys (004-02); the cause was its startup distance of 10 MB. At 200 to 1000 MB a put costs 180 to 670 bytes at 10M and 50M keys; the fix is a startup distance that suits the database. Node size 30 stays. Bursts of index writes at large startup distances found | done | 2026-10-26 |
| [005-45](45-fix-two-leftovers.md) | Fix | Two faults found on the way in 005-40 and 005-41: `SalsaStream.getLength()` did not count what it appended (BergDB's own stack did not meet it), and `WTransaction.sync(SyncLevel)` waited for the database's last transaction, not for its own; now the length is the underlying stream's, and the sync waits for its own transaction, as `sync()` does | done | 2026-10-25 |
| [005-42](42-transaction-info.md) | Decide | `Connection.transactionInfo()` gave internal KVs, whose `key()` threw (an index entry, reclaim's row), and for a value that reclaim had rewritten, reclaim's transaction and its time; from a TODO of 2016 (006-05). Decided A1 and B2: the internal KVs are left out, and a value that reclaim has rewritten gives `LookupTimeNotAvailableException` | done | 2026-10-25 |
| [005-33](33-crashed-creation.md) | Decide | A database whose creation crashed (a power loss in the first write of its stream) never started: one of three `StreamFormatException`s that did not say why, after recovery had zero-filled its first transaction. Decided A, one clear error: a start refuses it with a `DatabaseNotCreatedException` that says what happened and what to do, and writes nothing (005-28) | done | 2026-10-25 |
| [005-44](44-fix-sync-commit-byte.md) | Fix | A sync returned when every byte of the transaction but its last, the commit byte, was durable, so that a crash could then lose a transaction that the sync had reported durable, with a write buffer whose size is not a multiple of 4 (through the core API); now it waits until the commit byte is durable too (005-41) | done | 2026-10-25 |
| [005-41](41-is-durable.md) | Decide | `isDurable()`, whether a transaction is durable, answered at once, beside `sync()`; Frans's idea of 2026-10-13, from comments in the Pub API (006-05): not now (option C) | done | 2026-10-25 |
| [005-43](43-fix-from-todos.md) | Fix | Two leftovers of TODO markers (006-05): `Db.getTrans` threw a `DbException` for a position at or past the end of the stream, and the Pub API's `IndexBuilder.dir` and `UsePrimaryBuilder.dir` a `BadFormatException` for a bad directory; now both throw `IllegalArgumentException`, as for the other positions that cannot start a transaction and for a bad key | done | 2026-10-25 |
| [005-40](40-fix-refused-start-writes.md) | Fix | A start wrote to the stream before it checked the crypto key and the format: after a crash that ended the stream at or just inside a meta block, a start with a wrong key, or none, left a database that the right key could not start either; a newer record format was refused as corrupt data, with format 2's message. Now recovery reads the meta blocks first, and the versions of records and nodes are refused with a `VersioningStreamException` that says which BergDB wrote the stream. The format check that `DbStarter`'s TODO asked for had been made by the parsers since 2015 | done | 2026-10-25 |
| [005-39](39-fix-trans-completed-before.md) | Fix | `RecoverableStream.getPosOfTransCompletedBefore`, where the iterators that do not start at an exact position start: its Javadoc promised the last transaction completed before the position, which it never searched for (a TODO said so), and in a stream cut by reclaim it threw `NullPointerException` or gave a transaction before the cut; now the Javadoc says what it gives, and in a cut stream it gives the first transaction after the cut that a meta block names | done | 2026-10-25 |
| [005-31](31-fix-take-blocked.md) | Fix | A transaction whose dirty index nodes did not fit in one record stopped the startup pos for good; now one whose index nodes, by a bound at the largest node size, could take more than 15/16 of the record limit is refused before its go point (007-02, 007-03 step 1) | done | 2026-10-24 |
| [005-35](35-fix-stop-and-close.md) | Fix | `stop()` lost the transactions still in the write buffer; `close()` returned at once after `stop()` or beside another `close()`; a writer that waited for room in the buffer waited for ever; now `stop()` starts one close that writes everything, in a thread that is not a daemon, and `close()` waits for it | done | 2026-10-24 |
| [005-32](32-fix-failed-start-storage.md) | Fix | A start that threw left its storage running: its threads, its open files, and writes of what it appended, also into a database started after it; `BufferedStream.close()` hung when the last flush failed; now a start that throws closes its storage before the exception leaves (005-28) | done | 2026-10-24 |
| [005-34](34-fix-transaction-info-position.md) | Fix | `Connection.transactionInfo()` read at a wrong position for a value after a meta block in its record, and, after a restart, for a value rerun at startup; now a get gives its transaction's position, `getTrans` refuses a position that cannot start one, and a format error there fails the database (005-30) | done | 2026-10-24 |
| [005-37](37-fix-memory-stream-checks.md) | Fix | `MemoryStream` took a negative length to `append` and a `pretruncate` past its length, after some of which it took no more appends; now it refuses both, and `AppendOnlyStream`'s Javadoc says what the streams do (005-29) | done | 2026-10-24 |
| [005-36](36-fix-test-crash3.md) | Fix | `DbTester.testCrash3` never tested a truncation: it truncated a copy and started on the original; now it starts on the copy, after a sync that writes the creation (005-29) | done | 2026-10-24 |
| [005-30](30-fix-read-failure.md) | Fix | A read or a sync that failed on the storage (an I/O error, corrupt data) left the database running half dead; now it fails the database, as a transaction does since 005-01 | done | 2026-10-23 |
| [005-27](27-fix-meta-block-edge.md) | Fix | A crash that ended the stream exactly at a meta block's position, after a transaction that ended there, left a database that did not start; now recovery fills out that meta block too, as one partly written (005-11, P11) | done | 2026-10-23 |
| [005-29](29-fix-memory-stream-assert.md) | Fix | `MemoryStream.copy` failed an assertion when the stream was empty or its length a multiple of 1,000,000 bytes (test code; 005-11); now its arrays are exactly those that hold bytes, also after `truncate` and an append of 0 bytes | done | 2026-10-23 |
| [005-28](28-fix-trans-iterator-loop.md) | Fix | Startup looped for ever when the transaction at its start position was a failed one (a damaged or mixed stream, 005-11's P9, or a crash in a new database's first transaction); now it throws a `StreamFormatException` that names it | done | 2026-10-23 |
| [005-01](01-fix-m49-exception-safety.md) | Fix | M49: a transaction that threw after its go point was half committed; now it fails the database, which refuses every transaction and read until it is restarted (item 003) | done | 2026-10-22 |
| [005-12](12-transaction-outputs.md) | Decide | Transaction outputs (`setOutput`, `getOutput`) stay, with a consistent API: typed, null for a missing output, the same checks; an environment refuses calls after its action (005-10) | done | 2026-10-22 |
| [005-26](26-fix-lone-surrogates.md) | Fix | A string with a lone surrogate cannot be stored in an array: `utf8Size` | done | 2026-10-21 |
| [005-25](25-fix-buffered-read-past-end.md) | Fix | A `BufferedStream` read one byte past the end returns a stale byte | done | 2026-10-21 |
| [005-24](24-fix-file-read-at-end.md) | Fix | A `FileStream` read at the end of the stream loops forever | done | 2026-10-21 |
| [005-23](23-fix-deep-objects.md) | Fix | `StackOverflowError` for a cyclic or deeply nested object at a put | done | 2026-10-21 |
| [005-22](22-fix-narrowing.md) | Fix | A stored value too large for its Java field is truncated silently | done | 2026-10-21 |
| [005-21](21-fix-small-overflows.md) | Fix | Smaller overflows: `Time.millis`, `TimeResolver` seconds, `TransSeq.take`, negative key hashes, `DbObject` shorts, corrupt counts | done | 2026-10-21 |
| [005-20](20-fix-jmx-retain-days.md) | Fix | `Jmx` `setRetainDurationInDays` in `int`: 99,999 days becomes 578.5 | done | 2026-10-21 |
| [005-19](19-fix-file-names.md) | Fix | `FileStream` cannot reopen a stream past 214.7 TB: file names parsed as `int` | done | 2026-10-21 |
| [005-18](18-fix-clock-range.md) | Fix | A clock time of 2^56 or more is not checked; the database cannot restart ("Time too large") | done | 2026-10-21 |
| [005-17](17-fix-transaction-size.md) | Fix | A transaction of 1.79 GB or more is half committed and blocks the writer: the record's sizes in `int`, no size limit (M49) | done | 2026-10-21 |
| [005-16](16-fix-memory-stream-first-pos.md) | Fix | An in-memory database with a retain duration fails after 2^31 bytes: `MemoryStream`'s first position in `int` | done | 2026-10-21 |
| [005-15](15-fix-index-scan-carry.md) | Fix | Long-index range scans skip or add entries: `plusOne` does not clear the `0xff` bytes it carries past (startAt(255) exclusive misses 256 to 510) | done | 2026-10-21 |
| [005-14](14-calm-when-idle.md) | Decide | Calm when idle: an idle database woke 163 times a second at 20 ms; now the consumer sleeps when nothing is buffered; also the wake count's overflow and a close that appended the whole buffer (005-13) | done | 2026-10-21 |
| [005-10](10-unused-code.md) | Investigate | Unused code in `java/` and `lean/`: find it and propose what to remove; nothing is removed without Frans's approval | done | 2026-10-20 |
| [005-09](09-fix-node-table-snapshot-race.md) | Fix | A race between a reader and a sweep lets the node table name a released object (INV-CAN); a unit test fails now and then (005-02) | done | 2026-10-20 |
| [005-13](13-buffer-time.md) | Investigate | The buffer time (100 ms, from the hard-drive era): sweep it on SSD, then decide the default and group commit; now 20 ms | done | 2026-10-20 |
| [005-08](08-fix-node-table-tree-bins.md) | Fix | The node table's 256 maps make every bin a tree (`Cache3.mapIndex`): 61 bytes per KV, a slower `set` (006-02) | done | 2026-10-19 |
| [005-04](04-a6-failures.md) | Decide | A6 fails in 5 Java transactions: is anything to be done? | done | 2026-10-19 |
| [005-02](02-fix-m46-ordinal-bound.md) | Fix | M46: the top node ordinal bound, 2^30 − 1 over a database's life (item 002) | done | 2026-10-19 |

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation).

Order, as proposed, of what is open: 005-03 is done by item 009, whose
handles removed the sweep; 005-05 and 005-06 beside the rest, as they are mostly reading and thinking,
and 005-06 feeds 005-05. The go point that 005-07
asks about is in `Db.executeInner` since 005-01. 005-09 is done. What is left of 005-10 waits for Frans; a removal is best made
when no other change to `java/` is under way. 005-12
is done. 005-27, 005-28 and 005-29, the fixes found in 005-11, are done.
005-30 is done, and so is 005-34, found in it. 005-31 is done, which item
007's deadline for `TransSeq.take` (007-01, D1) needed. 005-32
is done, which 005-33's change needed; 005-33 is decided, A, and done. 005-35,
005-36 and 005-37 are done, and so are 005-39, 005-40, 005-43 and 005-44.
005-41 is decided: not now. 005-42 is decided, A1 and B2, and done, and so
is 005-45. 005-11 is decided, A with C2, and done: replication is
removed. 005-55 is done; it did not
change the eviction thread, so 005-51 does not depend on it; 005-51 is
done. 005-57 is done (part 1); 005-58, its Lean theorem, is done.
005-46 is done. 005-56 is done. 005-68 is dropped: its finding did not
hold. 005-07 is dropped: obsolete since handles (009). 005-52 is done:
option B (`0c6c4be`).


Files
=====

* [01-fix-m49-exception-safety.md](01-fix-m49-exception-safety.md). 005-01,
  fix M49; done, with its probe, checks and runs in
  [01-fix-m49-exception-safety/](01-fix-m49-exception-safety/).
* [02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md). 005-02, fix
  M46.
* [03-sweep-cost.md](03-sweep-cost.md). 005-03, investigate the sweep's
  cost; done by item 009, which removed the sweep.
* [04-a6-failures.md](04-a6-failures.md). 005-04, the A6 failures: decide
  whether anything is to be done; done, with its tools and runs in
  [04-a6-failures/](04-a6-failures/).
* [05-bergdb-future.md](05-bergdb-future.md). 005-05, what to do with
  BergDB.
* [06-publication-literature.md](06-publication-literature.md). 005-06, the
  literature and the options for a publication.
* [07-transaction-synchronization.md](07-transaction-synchronization.md).
  005-07, synchronization of transactions: the design before handles, from
  the code and F1-007's notes; dropped 2026-11-04, obsolete since 009.
* [08-fix-node-table-tree-bins.md](08-fix-node-table-tree-bins.md). 005-08,
  fix the node table's tree bins, found and measured in 006-02; done, with
  its runs and tools in
  [08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/).
* [09-fix-node-table-snapshot-race.md](09-fix-node-table-snapshot-race.md).
  005-09, fix the race that lets the node table name a released object,
  found in 005-02; done, with its probe, runs and checks in
  [09-fix-node-table-snapshot-race/](09-fix-node-table-snapshot-race/).
* [10-unused-code.md](10-unused-code.md). 005-10, find unused code and
  propose what to remove, for Frans to approve; the proposal, with its
  tables, plan, tools and runs, in [10-unused-code/](10-unused-code/), and
  the removal as Frans decided it in
  [10-unused-code/applied/](10-unused-code/applied/).
* [11-replication.md](11-replication.md). 005-11, replication: the
  decision material for Frans, his decision (A with C2) and the removal;
  the study, with its probes and runs, in
  [11-replication/](11-replication/).
* [12-transaction-outputs.md](12-transaction-outputs.md). 005-12,
  transaction outputs: they stay; the API made consistent, with unit
  tests; done.
* [13-buffer-time.md](13-buffer-time.md). 005-13, the buffer time: the
  sweep, and the default changed to 20 ms; done, with its table, tools
  and runs in [13-buffer-time/](13-buffer-time/).
* [14-calm-when-idle.md](14-calm-when-idle.md). 005-14, the idle cost of
  the storage thread's timer, by buffer time, and the fix: the consumer
  sleeps when idle, with two faults of `BufferedStream` fixed; done, with
  its table, tools and runs in [14-calm-when-idle/](14-calm-when-idle/).

* [15-fix-index-scan-carry.md](15-fix-index-scan-carry.md) to
  [26-fix-lone-surrogates.md](26-fix-lone-surrogates.md). 005-15 to 005-26,
  the findings of the review of the Java code for overflow: 15
  [index scan carry](15-fix-index-scan-carry.md), 16
  [MemoryStream first position](16-fix-memory-stream-first-pos.md), 17
  [transaction size](17-fix-transaction-size.md), 18
  [clock range](18-fix-clock-range.md), 19
  [file names](19-fix-file-names.md), 20
  [Jmx retain days](20-fix-jmx-retain-days.md), 21
  [smaller overflows](21-fix-small-overflows.md), 22
  [narrowing](22-fix-narrowing.md), 23
  [deep objects](23-fix-deep-objects.md), 24
  [FileStream read at the end](24-fix-file-read-at-end.md), 25
  [BufferedStream read past the end](25-fix-buffered-read-past-end.md), 26
  [lone surrogates](26-fix-lone-surrogates.md).
* [27-fix-meta-block-edge.md](27-fix-meta-block-edge.md),
  [28-fix-trans-iterator-loop.md](28-fix-trans-iterator-loop.md),
  [29-fix-memory-stream-assert.md](29-fix-memory-stream-assert.md). 005-27
  to 005-29, faults found in 005-11 outside replication: a crash at a meta
  block's position, the startup's loop on a failed transaction, and
  `MemoryStream.copy`'s assertion. 005-28 is done, with its runs in
  [28-fix-trans-iterator-loop/](28-fix-trans-iterator-loop/); 005-29 is
  done; 005-27 is done, with its runs, gates and probe in
  [27-fix-meta-block-edge/](27-fix-meta-block-edge/).
* [30-fix-read-failure.md](30-fix-read-failure.md). 005-30, a read that
  fails on the storage fails the database (005-01's follow-up); done, with
  its checks and runs in [30-fix-read-failure/](30-fix-read-failure/).
* [31-fix-take-blocked.md](31-fix-take-blocked.md). 005-31, a transaction
  whose dirty index nodes do not fit in one record stops the startup pos
  for good; found in item 007, with the probe in
  [../007-bounds/02-take-blocked/](../007-bounds/02-take-blocked/); done;
  the measurements of the bound in
  [31-fix-take-blocked/](31-fix-take-blocked/).
* [32-fix-failed-start-storage.md](32-fix-failed-start-storage.md). 005-32,
  a start that throws leaves its storage running; found in 005-28; done;
  the probe and its runs, before and after the fix, in
  [32-fix-failed-start-storage/](32-fix-failed-start-storage/).
* [33-crashed-creation.md](33-crashed-creation.md). 005-33, a database
  whose creation crashed: the study, the options and Frans's decision, A;
  done; found in 005-28, with the probe and its runs, before and after the
  change, in [33-crashed-creation/](33-crashed-creation/).
* [34-fix-transaction-info-position.md](34-fix-transaction-info-position.md).
  005-34, `transactionInfo()`'s wrong position after a meta block, found in
  005-30; done; its probe and runs in
  [34-fix-transaction-info-position/](34-fix-transaction-info-position/).
* [35-fix-stop-and-close.md](35-fix-stop-and-close.md). 005-35, `stop()`
  and `close()` do not close the database as their Javadoc says, from
  Frans's note in `Db.close()`; done; its probes, the survey of the calls
  and their runs, before and after the fix, in
  [35-fix-stop-and-close/](35-fix-stop-and-close/).
* [36-fix-test-crash3.md](36-fix-test-crash3.md) and
  [37-fix-memory-stream-checks.md](37-fix-memory-stream-checks.md).
  005-36 and 005-37, found in 005-29: `DbTester.testCrash3`, which tests
  no truncation, and `MemoryStream`, which takes a negative length and a
  cut past its end. Both are done.
* [38-writes-at-scale.md](38-writes-at-scale.md). 005-38, investigate
  writes at scale: the stream's growth per key and loads beyond the
  budget, found in 004-02; done; the report, the tool (WriteBench), the
  node-size runs and every output in
  [38-writes-at-scale/](38-writes-at-scale/).
* [39-fix-trans-completed-before.md](39-fix-trans-completed-before.md).
  005-39, `RecoverableStream.getPosOfTransCompletedBefore`: a wrong
  Javadoc, from the TODO under it, and a cut stream; done; the probe and
  its output, before and after the fix, in
  [39-fix-trans-completed-before/](39-fix-trans-completed-before/).
* [40-fix-refused-start-writes.md](40-fix-refused-start-writes.md).
  005-40, a start writes to the stream before it checks the crypto key
  and the format; found from the TODO on the format version in
  `DbStarter`; done; the probes, their runs before and after the fix, and
  the prototype in
  [40-fix-refused-start-writes/](40-fix-refused-start-writes/).
* [41-is-durable.md](41-is-durable.md). 005-41, `isDurable()`: Frans's
  idea, the options, and two findings on the syncs; decided: not now.
* [42-transaction-info.md](42-transaction-info.md). 005-42, what
  `transactionInfo()` gives; decided A1 and B2, and done; the probe and its
  output, before and after the change, in
  [42-transaction-info/](42-transaction-info/).
* [43-fix-from-todos.md](43-fix-from-todos.md). 005-43, two fixes from the
  TODO markers of 006-05; done.
* [44-fix-sync-commit-byte.md](44-fix-sync-commit-byte.md). 005-44, a sync
  one byte short of the commit byte, found in 005-41; done; the probe and
  its output, before and after the fix, in
  [44-fix-sync-commit-byte/](44-fix-sync-commit-byte/).
* [45-fix-two-leftovers.md](45-fix-two-leftovers.md). 005-45, two faults
  found on the way in 005-40 and 005-41: `SalsaStream.getLength()` and
  `WTransaction.sync(SyncLevel)`; done.
* [46-stream-file-lock.md](46-stream-file-lock.md). 005-46, a read of the
  stream's last file waits for the writer's append and its `fsync`, and
  every read waits for a new file's forces and a physical cut's deletes;
  found in 009's measurements and 009-04's soaks; investigated, fixed
  (`eaec93e`, with interrupts), measured on s1 and F53; done; the probes
  and their output, before and after, in
  [46-stream-file-lock/](46-stream-file-lock/).
* [47-written-not-forced.md](47-written-not-forced.md). 005-47, a
  durability of "written, not forced": Frans's question, the options and
  the constraints, his decision (A, a setting) and its implementation;
  open for the latency measurement.
* [48-group-commit.md](48-group-commit.md). 005-48, group commit: a
  waiting sync starts the flush; the change, the questions, the
  measurements on s1, the outcome; done. The scripts of the runs, the two
  tables, the tools and the ReclaimReaders experiment in
  [48-group-commit/](48-group-commit/).
* [49-smooth-index-writes.md](49-smooth-index-writes.md). 005-49, smooth
  index writes: the bursts found in 005-38, the cause, the questions, the
  results; done. The report, the paced take's diff, WriteBench with every
  record logged and the analysis in
  [49-smooth-index-writes/](49-smooth-index-writes/).
* [50-fix-node-size-start.md](50-fix-node-size-start.md). 005-50, a start
  with another node size fails with a clear error; found in 005-38; the
  size in the meta block, proposed, decided and done; the probes, their
  runs and the first prototype in
  [50-fix-node-size-start/](50-fix-node-size-start/).
* [51-eviction-on-calls.md](51-eviction-on-calls.md). 005-51, eviction
  only in response to the calls: the eviction thread's wake-up a second,
  against 010-P3, the questions, the outcome; done.
* [52-cache-size-while-running.md](52-cache-size-while-running.md). 005-52,
  the cache size while the database runs: the issue, the questions, the
  first step measured, options A to C, the decision (B), the outcome, the
  pause probe with a lowered budget and its runs, the decision on them
  (option B: a transaction's warmup does not wait for eviction), its change
  and the runs again; done. The first step's night script, `BudgetBench`
  and their output, and the probe runs' script `lowered.sh` and summary
  `sum52.py`, in [52-cache-size-while-running/](52-cache-size-while-running/).
* [53-startup-distance-on-the-fly.md](53-startup-distance-on-the-fly.md).
  005-53, the startup distance on the fly: the issue, the questions,
  question 3 (fixed as 005-61), options A to E after D4:B, the decision (E)
  and the outcome; done. The history from 2013, the report with the
  evidence for both 005-53 and 005-52, `ReclaimDistanceProbe`, and the
  gates and StreamDigest of the change in
  [53-startup-distance-on-the-fly/](53-startup-distance-on-the-fly/).
* [54-open-bounds.md](54-open-bounds.md). 005-54, the bounds still open in
  the problem statement (011-01): Q1, Q2, Q3, Q5 and Q8; moved to 017-04
  on 2026-11-04.
* [55-fix-finalize.md](55-fix-finalize.md). 005-55, the deprecated API in
  the build, `finalize()` first: what `Db.finalize()` was for, the probes,
  the decision (no safety net; a `Cleaner` not chosen), the outcome; done.
  The probes, the lint script, the per-test leak finder and their output
  in [55-fix-finalize/](55-fix-finalize/).
* [56-package-dependencies.md](56-package-dependencies.md). 005-56, the
  package dependencies against the `package.html` files: Frans's question,
  a first look, the older rules of 2012 and 2015, the check with test code
  apart, the decision and the outcome; done. The check of 2026-10-27, the
  output of `java/deps.py` on the result and the gates in
  [56-package-dependencies/](56-package-dependencies/).
* [57-startup-header-reads.md](57-startup-header-reads.md). 005-57,
  startup without rule 4's header reads: the entry, its findings, Frans's
  decisions and the outcome; done. The report, the prototypes' diffs, the
  tool, the scripts, the outputs and the analysis in
  [57-startup-header-reads/](57-startup-header-reads/).
* [58-lean-rule4-by-position.md](58-lean-rule4-by-position.md). 005-58, a
  Lean theorem for 005-57's rule 4 by position: the statement, what the
  model needs, the theorems, the review and the questions for Frans; done.
  The patch in [58-lean-rule4-by-position/](58-lean-rule4-by-position/).
* [59-autocloseable.md](59-autocloseable.md). 005-59, `Db` and `Database` as
  `AutoCloseable`: the issue, four options, the questions, the decision
  (A) and the outcome; done.
* [60-block-storage.md](60-block-storage.md). 005-60, the stream on a
  block device without a file system: the idea, the questions; moved to
  017-05 on 2026-11-04.
* [61-reclaim-startup-distance.md](61-reclaim-startup-distance.md). 005-61,
  reclaim uses the database's startup distance: the fault found in
  005-53, the fix, the tests, the gates and StreamDigest; done.
* [62-lean-t9-t12-over-handles.md](62-lean-t9-t12-over-handles.md).
  005-62, T9 and T12 over handles: the statements, the proofs, the review,
  Frans's answers, the removal of the design before handles, rule 4 by
  position after a cut; done.
* [63-one-database-per-directory.md](63-one-database-per-directory.md).
  005-63, one database per directory, also while one closes: the issue
  found with `BryanRepro`, the lock file `bergdb.lock`, four options, the
  decision (C) and the outcome; done.
* [64-buffer-time-after-group-commit.md](64-buffer-time-after-group-commit.md).
  005-64, the buffer time after group commit, 20, 50 or 100 ms: the issue,
  the questions, data at risk (question 5), the results of 2026-10-28's
  runs, a recommendation (keep 20 ms), Frans's decision (50 ms) and the
  outcome; done. The scripts and probes in its `night/` and `tools/`, the
  summaries in `night/results-*-2026-10-28.md`, the gates and
  StreamDigest's outputs in `outcome/`.
* [65-gets-with-8-readers.md](65-gets-with-8-readers.md). 005-65, gets of
  27 and 36 ms with 8 readers at 665 MB under ZGC: the issue, the
  hypothesis and what would refute it, the test, the results of
  2026-10-28 night, a recommendation, Frans's decision and the fix
  (2026-10-29), and how to rerun the sweep with it; the results of
  2026-11-04 night; the AB/BA step left; open. The night step
  (`prep.sh`, `threads.sh`, `sum.py`, `ScaleBench-065.diff`) in
  [65-gets-with-8-readers/night/](65-gets-with-8-readers/night/); the
  fix's untimed count, its race tests on broken versions, its gates and
  digests in [65-gets-with-8-readers/fix/](65-gets-with-8-readers/fix/).
* [66-builder-opens-at-start.md](66-builder-opens-at-start.md). 005-66,
  the Pub API's builder opens the directories in `start()`: the issue
  left by 005-63, the change, the tests and the outcome; done.
* [67-fix-test-add-replica2.md](67-fix-test-add-replica2.md). 005-67,
  `StorageManagerTester.testAddReplica2` fails about one run in twelve:
  the issue, its history since 2015, the cause (the test), the forced
  interleavings, 2015's fault, the fix and the outcome; done. The loops,
  the probes and their output in
  [67-fix-test-add-replica2/](67-fix-test-add-replica2/).
* [68-fix-take-stream-length.md](68-fix-take-stream-length.md). 005-68,
  `TransSeq.take` gets the stream's length, not where the record begins
  (007-08's review): the issue, why it does not hold (the meta blocks are
  written eagerly), the instrumented run and the outcome; dropped. The
  probe's diff and output in
  [68-fix-take-stream-length/](68-fix-take-stream-length/).
* [69-system-clock-promise.md](69-system-clock-promise.md). 005-69,
  `SystemClock` does not keep its promise of strictly increasing times:
  the issue, why no database depends on it, the options; open.
* [70-keymodset-after-start.md](70-keymodset-after-start.md). 005-70, the
  STM startup boundary: the issue, lifecycle clarification, option A,
  Java and C fixes, regressions and validation; done. Command outputs in
  [70-keymodset-after-start/](70-keymodset-after-start/).
* [71-dbclock-read-time-after-start.md](71-dbclock-read-time-after-start.md).
  005-71, `DbClock` forgets the last read time at a start: the issue, the
  probe, the options; open.
* [72-file-layout-after-cut.md](72-file-layout-after-cut.md). 005-72, the
  files after reclaim's physical cut depend on timing: the issue, the
  probe, the options, the decisions (A for 012's cross tests, 2026-10-29;
  B dropped, 2026-11-05); done.
* [73-db-api-small-findings.md](73-db-api-small-findings.md). 005-73,
  seven small findings in `Db`'s API (012-03): the findings, what to do;
  open.
* [74-parser-corrupt-sizes.md](74-parser-corrupt-sizes.md). 005-74,
  parser and reader size checks, option A done, with regressions and
  recorded checks; later findings open as 005-82 and 005-83.
* [75-core-checks-and-comments.md](75-core-checks-and-comments.md).
  005-75, Core time/order and append-offset checks fixed, two dead checks
  removed, comments corrected; done, with regressions and validation.
* [76-wake-at-a-quarter.md](76-wake-at-a-quarter.md). 005-76,
  `BufferedStream` wakes at a quarter and continues without a timer wait
  when a flush leaves a quarter ready; done, with regressions, full level
  checks and F53/s1 performance runs. Evidence in `76-wake-at-a-quarter/`.
* [77-cap-pace-factor.md](77-cap-pace-factor.md). 005-77, cap the pace's
  factor S/sd, so that a decrease's records stay near the steady ones:
  the issue from 007-07's runs at 50M keys, the two variants, the
  questions, when it is done; moved to 015-84 on 2026-11-05.
* [78-retain-duration-in-stream.md](78-retain-duration-in-stream.md).
  005-78, the retain duration is not kept in the stream: the issue with
  the code, how the startup distance is kept, three forms of "in the
  stream", StreamDigest and the Lean model, the questions, when it is
  done; open.
* [80-setbudget-race-record.md](80-setbudget-race-record.md). 005-80,
  the record and a test of `setBudget`'s race, fixed inside 005-65's
  commit: the issue, options A to C, when it is done; open.
* [81-overload-and-retries.md](81-overload-and-retries.md). 005-81,
  transaction retries: verified current waits, the client contract the
  retries need, retry/sleep variants, and the plan for the hot-key and
  disjoint-key baselines and an `executeRw()` proposal; open. Split on
  2026-11-04: the overload/recovery investigation is 017-06.

* [82-gettrans-corruption.md](82-gettrans-corruption.md). 005-82,
  parsing errors in `getTrans` must fail the database; split from 005-74.
* [83-recovery-before-refusal.md](83-recovery-before-refusal.md). 005-83,
  power-loss tail experiment and initial designs; moved to 014-01,
  with the original artifacts kept here.

Log
===

2026-10-19. Created the item, at Frans's request, with subitems 01 to 06.
Defined, not started.

2026-10-19. Added 005-07, synchronization of transactions, at Frans's
request, with the design notes found in F1-007.

2026-10-19. Added 005-08, the node table's tree bins, at Frans's request,
from 006-02's finding and its experimental patch.

2026-10-19. 005-02 done, at Frans's request ("Fix 005-02"), by Claude (Opus
5.5, Claude Code): the top node ordinal is a `long` below 2^48 without a
format change, and a user transaction is refused before it changes anything
near the end. M46 and item 002 closed. Its outcome is in the subitem.

2026-10-19. 005-08 done, at Frans's request ("Fix bergdb 005-08"), by
Claude (Opus 5.5, Claude Code): `Cache3.mapIndex` by Fibonacci hashing, and
a unit test that the node table's bins stay small; MEM 227 to 191 bytes per
KV, `set` 10 to 13 percent faster, the streams unchanged, the four gates and
the quick performance suite passed. The change in `java/` is left for Frans
to commit. Found on the way, for 005-03: a sweep breaks ties of age by the
node table's order, not by depth (005-08, "The table's order").

2026-10-19. Added 005-09, the race that lets the node table name a released
object, at Frans's request, from 005-02's finding (a unit test that fails now
and then).

2026-10-19. Added 005-10, unused code: find it and propose what to remove,
at Frans's request. For an AI to do; nothing is removed without Frans's
approval.

2026-10-19. 005-04 done, at Frans's request ("Do as proposed"), by Claude
(Opus 5.5, Claude Code): A6 is not a target, the assumption stays A6'. Option
4's look found one kind of A6 failure only, the in-place split of a segment
root made by the same transaction, which keeps A6'; 61 Java-tier failures at
node sizes 8 to 62 are all that kind, and 21 new traces with it pass the
checker, with eviction too. No change to `java/` or `lean/`. Proposed, not
done: TREE, A6' and A-COPY as gate checks, and A6' as the checker's
diagnostic.

2026-10-19. 005-10 in progress, at Frans's request ("Do the 005-10 todo
item"), by Claude (Opus 5.5, Claude Code): the proposal is written, in
10-unused-code/proposal.md. About 11,700 lines can go in recommended groups
(A1 to F1); a patch with all of them passes the build, the unit and
f-tests, the four gates and `lake build` on a clone. Found on the way:
tests that never ran, as their classes are in no pack (one fails today),
and night tests that nothing runs (they pass). Nothing is removed; Frans
decides by ID.

2026-10-20. 005-10: Frans decided ("remove all recommended; C1 keep; C2
keep; C3 keep; D1 keep; D2 keep; D3 keep; E1 keep; G1 remove", and a
script for the night tests). Removed by Claude (Opus 5.5, Claude Code): A1
to A3, B1 to B3, F1 and part of G1, 3,071 lines in 103 files; added
`java/stress/night.sh`. The build, the unit and f-tests, the four gates,
`lake build` and `night.sh` pass on a clone; the change is in the main
tree, for Frans to commit. The rest of G1 waits: the proposal's G1 was
wrong for part of it (code behind those API methods is used), see the
subitem.

2026-10-20. 005-04's two proposals done, at Frans's request ("Yes"), by
Claude (Opus 5.5, Claude Code): TREE, A6' and A-COPY are gate checks, in
`A2A3Check2` (`level2.sh`, step 7) and in the checker's C-A, where A6'
replaces the diagnostic A6; the small and evict sets have a configuration
with A6's kind, whose traces must contain it. The four gates pass, also with
005-10's removal (`c6ca623`). See 005-04, "Follow-up".

2026-10-20. Added 005-11, replication, and 005-12, transaction outputs, at
Frans's request, from 005-10's G1 (the Pub API's methods that nothing in
the repository calls).

2026-10-20. The list split into Open and Closed, at Frans's request, by
Claude (Opus 5.5, Claude Code), so that what is done shows at a glance; the
files stay where they are. 005-08's own status said open: its outcome and
its files, written on 2026-10-19 in a clone and never copied here, are now
in the subitem and in
[08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/).

2026-10-20. 005-10 done, at Frans's request, by Claude (Opus 5.5, Claude
Code): the Pub API's `getFirstAvailableLookupTime` returned the current
time; fixed, with two unit tests. `Connection.put(Object)`, the repeated
`RwEnvironment.exists` and `NoFieldsSetException` removed; replication and
transaction outputs are 005-11 and 005-12. The four gates pass.

2026-10-20. Added 005-13, the buffer time, at Frans's request, by Claude
(Opus 5.5, Claude Code): a sweep of the buffer time on today's source
first, with the proposal of group commit (a waiting sync starts the
flush). Defined, not started.

2026-10-20. 005-13 done, at Frans's request ("Just set the default to 20
ms unless you find a good reason for not to"), by Claude (Opus 5.5, Claude
Code): the sweep of 10 to 200 ms, three rounds; a sync after a commit
waits for the timer (122 ms at 100 ms), and writers that do not sync are
as fast from 10 to 100 ms (about 100,000 puts of 1 KB a second).
`StorageManager.DEFAULT_BUFFER_TIME` is 20: one syncing thread gets 29
commits a second instead of 8, p50 35 ms. Group commit and the Pub API's
buffer time are not done; a storage design for SSD and flash is out of
scope. `before-commit.sh` passes.

2026-10-20. 005-09 done, at Frans's request ("Fix 005-09"), by Claude (Opus
5.5, Claude Code): `Cache3.pointerCreated` reads the canonical flag again
under the node table's lock, and `Cache3.released` clears it under the same
lock, so a reader no longer enters an object that a sweep has just
released. A deterministic test fails without the fix; the flaky test, under
load, failed 1 in 2,000 runs before and 0 in 8,000 after. The stream
unchanged (StreamDigest as R8's), Props and the quick performance suite
unchanged. The change in `java/` is left for Frans to commit.

2026-10-21. Added 005-14, calm when idle, at Frans's request ("I would
like the database to be calm when not used ... have a look at how 20 vs 50
vs 100 ms affects this"), by Claude (Opus 5.5, Claude Code), with the
measurements on F53: an idle database wakes 56, 85 and 163 times a second
at 100, 50 and 20 ms, against the JVM's own 25 (0.3 percent of a core and
0.14 mW at 20 ms). A prototype consumer that sleeps when nothing is
buffered makes it 25, as the JVM alone, at any buffer time. Found on the
way: the wake count overflows after 190 days without a write at 20 ms.
For Frans to decide; no change to `java/`.

2026-10-21. 005-14 done, at Frans's request ("OK, do 005-14 as proposed.
Also fix the overflow problem."), by Claude (Opus 5.5, Claude Code), in
`BufferedStream`: the consumer sleeps when nothing has been buffered for
a buffer time (an idle database wakes 26 times a second, as the JVM
alone, instead of 187); the wake count stops at 4 (it overflowed after
2^31 wakes without a write); and nothing is flushed when nothing is
buffered, also when closing: a close could append the whole buffer, 10 MB
of stale bytes, and the database then failed to start (34 of 24,000
closes in a test before the fix, 0 of 12,000 after). Four unit tests that
fail without the change; `before-commit.sh` passes; no change under load.
The change in `java/` is left for Frans to commit.

2026-10-21. Added 005-15 to 005-26, at Frans's request ("Go through it and
search for overflow issues", then "Write the findings up as 005 entries.
Then fix each one."), by Claude (Opus 5.5, Claude Code): a review of the
Java code for overflow. Six faults checked with probes (wrong index scan
results, an in-memory database that fails after 2^31 bytes, a large
transaction half committed, an unchecked clock, file names in `int`, Jmx
retain days in `int`), smaller overflows, and three faults found on the
way. Frans decided: a value that does not fit its Java field throws, and
cyclic or too deep objects get clear exceptions.

2026-10-21. 005-15 done, by Claude (Opus 5.5, Claude Code): a long index
scan's start key (`UseIndexBuilderImp.plusOne`) kept the `0xff` bytes it
carried past, so a scan after a value whose low byte is `0xff` (255, -1)
skipped or added entries: `startAt(255).inclusive(false)` missed 256 to
510. Now they become 0. Two tests; `before-commit.sh` passes.

2026-10-21. 005-16 done, by Claude (Opus 5.5, Claude Code):
`MemoryStream`'s first position was a product of two `int`s and went
negative after a cut past 2^31 bytes, so an in-memory database with a
retain duration treated a read below the cut as a storage failure and
stopped taking transactions. Now in `long`; an f-test; `before-commit.sh`
passes.

2026-10-21. 005-17 done, by Claude (Opus 5.5, Claude Code): a transaction of
1.79 GB or more was half committed and blocked the writer, since the
record's size was added up in an `int` after the go point. Now a
transaction whose value nodes pass 7/8 of the record limit (2^31 − 9
bytes) is refused before it changes anything, `TransSeq.take` keeps the
index nodes within the limit, and the serializer computes in `long`. Four
tests; streams unchanged (StreamDigest), Props unchanged;
`before-commit.sh` passes.

2026-10-21. 005-18 done, by Claude (Opus 5.5, Claude Code): a clock time of
2^56 or more (a clock in nanoseconds, say) was taken, and the database
then could not start again ("Time too large"). Now `DbClock` refuses it
with a `DbException` before the transaction begins. Two tests; streams
unchanged; `before-commit.sh` passes.

2026-10-21. 005-19 done, by Claude (Opus 5.5, Claude Code): `FileStream`
parsed its file names as `int`s, so a stream past 214.7 TB of positions
could not be opened again. Now `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-20 done, by Claude (Opus 5.5, Claude Code): Jmx's
`setRetainDurationInDays` computed in `int`, so 99,999 days set a retention
of 578.5 days. Now in `long`; a test; `before-commit.sh` passes.

2026-10-21. 005-21 done, by Claude (Opus 5.5, Claude Code): smaller
overflows fixed: `Time.millis` (unchecked product), `TimeResolver`
(seconds cast to `int`, NaN), `TransSeq.take`'s node count limit, negative
key hashes (`Keys.hash` for `Long.MIN_VALUE`, `KeyModSet`'s index,
`Trans.Builder`), a `DbObject` field name over 32,767 UTF-8 bytes, and
corrupt counts that gave `NegativeArraySizeException`. Seven tests;
streams unchanged; `before-commit.sh` passes.

2026-10-21. 005-22 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: reading an object into its class, a stored value that does not fit
its Java field (a long of 3,000,000,000 into an `int`, a NaN into a `long`)
was cast silently; now it is a `DataFormatException` that names the field.
Two tests; `before-commit.sh` passes.

2026-10-21. 005-23 done, by Claude (Opus 5.5, Claude Code), as Frans
decided: a put of an object with a reference cycle, or nested 20,000 deep,
threw `StackOverflowError`. Now `DbObject.toDbObject` refuses a cycle, and
nesting deeper than 1,000 objects, with an `IllegalArgumentException` that
names the field path. Three tests, one changed; `before-commit.sh` passes.

2026-10-21. 005-24 done, by Claude (Opus 5.5, Claude Code): a `FileStream`
read at the end of the stream looped forever, since a bound check compared
`spos` with `spos + fileLength`; one past it threw
`IndexOutOfBoundsException`. Now both throw `EOFException` and the stream
stays usable. A test; `before-commit.sh` passes.

2026-10-21. 005-25 done, by Claude (Opus 5.5, Claude Code):
`BufferedStream.read` let a read end one byte past the end of the stream,
and gave a stale byte of the ring buffer; now it throws. A test;
`before-commit.sh` passes.

2026-10-21. 005-26 done, by Claude (Opus 5.5, Claude Code):
`StringUtil.utf8Size` counted a lone surrogate as 3 or 4 bytes, where the
encoder writes 1, so an object with such a string in an array could not be
stored ("Bad type"). Now it counts as the encoder writes. Tests;
`before-commit.sh` passes. With it, 005-15 to 005-26, the findings of the
review of the Java code for overflow, are done.

2026-10-22. 005-12 changed, at Frans's request, by Claude (Opus 5.5,
Claude Code): the outputs stay ("Deleting the feature is not an option any
more"), a feature of their own, not transaction metadata. Now a decision:
an API that makes them consistent with `put` and `get` is proposed (null
for a missing output, typed by a class, the same checks in both methods,
the rules in the Javadoc; `NoSuchObjectException` goes), then the tests.
No change to `java/`.

2026-10-22. 005-12 done, at Frans's request ("The proposal for 005-12 is
good, implement it."), by Claude (Opus 5.5, Claude Code), as proposed:
`Transaction.getOutput(name, clazz)` is typed and gives null for a missing
output and for a w-transaction; both methods check the name the same way;
`NoSuchObjectException` is removed; an rw-transaction's environment
refuses calls after its action has run (`IllegalStateException`); the
rules are in the Javadoc; `GetStarted4` shows an output. Seven unit tests
in `PubTesterOutput`; `before-commit.sh` passes.

2026-10-22. 005-11 studied, at Frans's request ("Do 005-11. Replication:
study it, for Frans to decide."), by Claude (Opus 5.5, Claude Code), with
probes P1 to P11 on today's code. Replication works without cuts and
failures: replicas are byte copies, one can be added while the database
writes, a crash in its copy is harmless. It fails with reclaim (a crash
leaves the replica unusable while it is behind the cut's decision: 943 of
943 such images broken), after a start without the replica (the main hung
at startup, or the replica held another history), when a replica fails
(`NullPointerException` from later transactions), and with encryption (the
replica in plain text). Proposed: remove it, and leave mirroring to the OS
and backups to copying the files. Found on the way, outside replication: a
crash that ends the stream where a meta block starts leaves a database
that does not start. For Frans to decide; no change to `java/`.

2026-10-22. 005-01 done, at Frans's request ("Do as proposed /
Recommanded. Implement this and commit it. Refuse both reads and writes
after failure. Use the wrapper as recommanded. Task 2, as you
recommend."), by Claude (Opus 5.5, Claude Code): `Db.executeInner` has a
go point, after the checks and before the first change. A `Throwable`
after it fails the database (`DbState.FAILED`), which refuses every later
transaction and read with a `DbFailedException` (the first failure as the
cause; an `Error` is thrown as it is) until it is restarted. The
transaction's time does not become readable when its puts throw, and the
state is checked again under the write lock. No rollback; transformations
stay after the go point and must not throw. M49 and item 003 closed; no
model change. Seven tests in `DbTesterFailure`, and
`DbTesterStream.testReadOnlyStream2` changed; streams unchanged
(StreamDigest); `before-commit.sh` and the four gates pass.

2026-10-23. Added 005-27 to 005-29, at Frans's request ("For now, add 005
entries for the bugs."), by Claude (Opus 5.5, Claude Code): the faults that
005-11's probes found outside replication. 005-11 stays open (Frans: "I
need to think carefully about this one. Replication is linked to
durability and it affects the public API."); its options A, B, C1, C2 and
C3 are now described in the entry itself, with what each means for the
syncs of the API, and Frans's earlier design of durability levels from
F1-007 is summarized there. The probes ran again on `78cc5f3`: since
005-01, a replica that fails, or `addReplica` during cuts, fails the whole
database at the next cut (a `NullPointerException` after the go point),
where before some transactions threw. No change to `java/`.

2026-10-23. Added 005-30, at Frans's request ("Write it up in a new entry.
I like your proposal."), by Claude (Opus 5.5, Claude Code), from 005-01's
follow-up: a read that fails on the storage leaves the database running
half dead, as the storage below refuses all I/O after the first error;
proposed, to fail the database as a transaction does since 005-01,
corrupt data included, but not for reads that a cut has overtaken or that
run while the database stops. No change to `java/`.

2026-10-23. 005-28 done, at Frans's request ("Fix bergdb 005-28."), by
Claude (Opus 5.5, Claude Code), as proposed: `NodeStream.TransIterator`
went back to its start position after a failed transaction there and read
it again, for ever. Now a failed transaction at an exact start position
(startup, `Db.getTrans`) throws a `StreamFormatException` that names it,
and the other iterator steps on to the next transaction. P9's first case
fails at startup with it. Found on the way: it also happened in one
history, after a crash in a new database's first transaction; such a
database now fails to start with that exception. Three tests;
`before-commit.sh` passes. The change in `java/` is left for Frans to
commit.

2026-10-23. Added 005-31, at Frans's request ("Register the bug in 005."),
by Claude (Opus 5.5, Claude Code), from item 007's finding 007-02: a
transaction whose got-dirty index nodes need more bytes than one record
can hold is never taken, so the startup pos stays before it for good.
Proposed: refuse such a transaction before its go point (option A). No
change to `java/`.

2026-10-23. 005-29 done, at Frans's request ("Fix bergdb 005-29."), by
Claude (Opus 5.5, Claude Code): `MemoryStream.assertOk` expected one array
too many for an empty stream and at a length that is a multiple of
1,000,000 bytes, so `copy()` failed its assertion. The one-line fix
proposed was not enough, as `truncate` and an append of 0 bytes made that
extra array; now all three keep exactly the arrays that hold bytes. A
unit test; `before-commit.sh` passes. Found on the way:
`DbTester.testCrash3` has never started on its truncated copies; on them
it meets 005-28's case, as it takes its first length before the new
database is written. The change in `java/` is left for Frans to commit.

2026-10-23. Added 005-32 and 005-33, at Frans's request, by Claude (Opus
5.5, Claude Code), from 005-28's findings. 005-32 ("Yes, make a new 005
entry."): a start that throws leaves its storage running until the
garbage collector finalizes the `Db`; in a probe, a failed start's thread
wrote into a database started after it on the same files, which then lost
a synced transaction 4 times in 20 (assertions off); and
`BufferedStream.close()` hangs when the last flush fails. Proposed: close
the storage when a start throws. 005-33 ("Study the options and propose
something in the entry. Do not implement anything."): a crash in a
database's creation leaves a stream that never starts, with one of three
messages; in 300 kills of a creating process none left one (the creation
is one write), but a power loss can. Options: a clear error (A), create
it again at start (B), create it whole or not at all (C), no change (D);
proposed: A, then B in the Pub API, after 005-32. No change to `java/`.

2026-10-23. 005-27 done, at Frans's request ("bergdb 005-27, fix it."), by
Claude (Opus 5.5, Claude Code), as proposed first: when the stream ends at
a meta block's position, `RecoverableStream.fixMetaBlockIfNeeded` fills
out that meta block too, as one partly written; the block is invalid, and
recovery takes the one before it. Two unit tests that fail without the fix;
`CrashTest` also cuts at and next to meta block positions, and at the end
of each transaction that ends at one (three in `level2.sh`'s full run,
which fail without the fix); P11 again: none of its 13 images fails.
Streams unchanged (StreamDigest); `before-commit.sh` and the four gates
pass, on `e2c0dc0` with the change. The change in `java/` is left for
Frans to commit.

2026-10-23. 005-30 done, at Frans's request ("Fix bergdb 005-30. As
proposed. Commit when done."), by Claude (Opus 5.5, Claude Code), as
proposed: a read that fails on the storage (`getOne`, `getMany`, the
warm-up of a transaction, `getTrans`), or a sync that does, fails the
database as a transaction does since 005-01: the call throws a
`DbFailedException` with the failure as the cause, and every later
transaction and read is refused with it until a restart. A read that a cut
has overtaken still expires, and a read or a sync while the database
stops, or an interrupted sync, throws as before. The state changes under
`readSync`, in `stop()` and `close()` too. In `getTrans` a format error is
thrown as it is, because of 005-34. Ten tests in `DbTesterFailure`, three
changed; streams unchanged (StreamDigest); `before-commit.sh`, `level3.sh`
and `level4.sh` pass; Props unchanged.

2026-10-23. Added 005-34, by Claude (Opus 5.5, Claude Code), found in
005-30 with a probe: a get gives a transaction position 128 bytes too far
for a value after a meta block in its record, so `transactionInfo()` reads
the middle of a record; on the code before 005-30, one such call could
leave the database half dead. Proposed: keep the value node's offset in
stream bytes. No change to `java/` for it.

2026-10-24. 005-31 decided, by Frans ("005-31, it has my 'go'. But don't
start the implementation now."): option A, refuse such a transaction before
its go point. Not started; it is step 1 of item 007's plan (007-03).

2026-10-24. Added 005-35, at Frans's request ("Investigate this further,
then write this down as a fix item in 005."), by Claude (Opus 5.5, Claude
Code), from Frans's note in `Db.close()`: both methods are meant to close
the database properly, stop() without waiting. Probes on `685e895`: stop()
loses what is still buffered (after 2,000 puts and a stop, a restart found
0 of them in two runs of three; close() kept all); close() returns at once
after stop() or beside another close(); a writer that waits for room in
the buffer waits for ever when the stream stops or fails, so a failing
disk hangs the database. Proposed: stop() starts the close in a thread of
its own and close() waits for it; two questions for Frans. No change to
`java/`.

2026-10-24. 005-35, Frans's answers: no `Database.close()` in the Pub API
for now ("Not now."); a transaction that runs when stop() is called
completes and is written ("As you propose."). Not started.

2026-10-24. Added 005-36 and 005-37, at Frans's request ("Add to 005."),
by Claude (Opus 5.5, Claude Code), from 005-29's findings, checked again
on `685e895`: `DbTester.testCrash3` has never tested a truncation, and on
its copies it fails in the database's creation (005-33's case) unless it
syncs first, a two-line fix; `MemoryStream` takes a negative length to
`append` and a `pretruncate` past its length, after some of which it takes
no more appends, where the interface says otherwise. No change to `java/`.

2026-10-24. Added 005-38, at Frans's request ("Register the write problem
as a todo in 005 of type Investigate."), by Claude (Opus 5.5, Claude
Code), from 004-02's results: the stream grows to about 1.1 KB per key at
100M random keys, and loads into an index larger than the budget slow to
under 100 puts a second on s1. To follow incremental eviction (004-03),
before the Lean physical layer is redone.

2026-10-24. 005-36 done, at Frans's request ("fix all todo items of type
Fix", "do what is proposed"), by Claude (Opus 5.5, Claude Code), as
proposed: `DbTester.testCrash3` syncs the new database before it takes its
first length, and starts on each truncated copy, at eleven lengths after
the creation; it passes. Test code only; `before-commit.sh` passes.

2026-10-24. 005-37 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: `MemoryStream` refuses a negative length or offset to
`append`, and a `pretruncate` past its length, with an
`IllegalArgumentException`, before it changes anything; the Javadoc of
`AppendOnlyStream.pretruncate` says what the streams do. A unit test;
`before-commit.sh` passes. The other streams' checks are not done, as
decided.

2026-10-24. 005-34 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: a value node keeps the distance in the stream from its
transaction's start, so a get gives the transaction's position also for a
value after a meta block in its record; `getTrans` refuses a position that
cannot start a transaction, and a format error there fails the database.
Found on the way and fixed: after a restart, a value that startup had
rerun gave its own position, and `transactionInfo()` threw. Tests;
StreamDigest identical; `before-commit.sh` passes.

2026-10-24. 005-32 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed: a start that throws closes its storage before the
exception leaves (what it appended is written, the streams closed, the
threads ended) and stops the database; the Pub API closes the `Db`, or the
builder's streams, when it throws after or before the `Db` is built; and
`BufferedStream.close()` returns, and throws the failure, after a failed
flush, where an `Error` in a flush now fails the stream as an
`IOException` does. Tests; the probe's cases again: no thread or file is
left. Its race now ends the same way every time, but not as "Done when"
expected: the failed start writes the replica's copy to the main, which
then holds two histories (005-11). `before-commit.sh` passes.

2026-10-24. 005-35 done, at Frans's request, by Claude (Opus 5.5, Claude
Code), as proposed and with his answers: `stop()` starts one close of the
database, in a thread of its own that is not a daemon, and `close()` waits
for it, also after `stop()` or beside another `close()`. The close takes
the write lock, so a transaction that runs completes and is written, then
writes what is buffered and closes the streams. A writer that waits for
room in the buffer gets an `IOException` when the stream stops or fails.
The probes again: every key after `stop()`, also when the program returns
from `main` after it. Tests; `before-commit.sh` and the four level scripts
pass.

2026-10-24. 005-31 done, at Frans's request ("fix all todo items of type
Fix"), by Claude (Opus 5.5, Claude Code), option A as decided: a
transaction whose index nodes, those it makes dirty or creates, could take
more than 15/16 of the record limit, by a bound at the largest node size,
is refused before its go point. A cheap test from the keys first; a walk of
the paths of a large transaction's keys under the write lock
(`Dag.dirtyNodeBound`). The bound is 1.0 to 2.6 times the actual nodes on
007-02's database at the four node sizes. A test; StreamDigest identical;
`before-commit.sh` passes. Step 1 of 007-03.

2026-10-24. The final checks of the six fixes of the day (005-31, 005-32,
005-34 to 005-37), on `43d85f9`: the four level scripts pass, and Props in
ABBA order against `7f08273`, the commit before them, shows no difference
(MEM 191, SS 1.50, CORE 0.27 to 0.29). See 005-31's outcome. With them, no
entry of kind Fix is open.

2026-10-25. Added 005-39 and done, at Frans's request ("Investigate
RecoverableStream.java:516. The TODO there.", then "Yes" to a Fix
entry), by Claude (Opus 5.5, Claude Code). The TODO was right: the
Javadoc promised the last transaction completed before the position,
which the method never searched for; and in a stream whose front
reclaim had cut, it threw `NullPointerException` or gave a transaction
before the cut, so `NodeStream.createTransIterator` and `print()` failed
on such a database. Startup does not use it; it reads from an exact
position. Now the Javadoc says what the method gives, and in a cut
stream it gives the first transaction after the cut that a meta block
names. Tests; `before-commit.sh` passes.

2026-10-25. Added 005-40, at Frans's request ("Investigate this and
propose what to do. If you find it appropriate, add an item to 005."), by
Claude (Opus 5.5, Claude Code), from another session's remark that the
stream format version is not checked at start (`DbStarter.java:590`). It
is: since 2015-07-24 the parsers check the format byte of each record and
node they read, and recovery the meta blocks' version; the TODO there is
from 2014. Probes on `425d7a7` found instead that recovery writes before
it checks: after a crash that ends the stream at or just inside a meta
block, a start with a wrong crypto key, or with none, appends the rest of
the block, and then the right key fails at every start (at 0, 3 and 5
bytes into the block; at 6, for 5 of 2,560 wrong keys). And a record of
another format is refused as corrupt data, with the message for format 2.
Proposed: read the meta blocks before that fill (a prototype passes
`before-commit.sh` and `CrashTest`), `VersioningStreamException` for the
versions of records and nodes, a rule for the next format change, and
the stale TODO and constant gone. No change to `java/`.

2026-10-25. 005-40 done, at Frans's request ("fix 005-40"), by Claude
(Opus 5.5, Claude Code), as proposed: `RecoverableStream.recover()` reads
the meta blocks before it fills out one that a crash has cut, so a start
with a wrong crypto key, with none, or on a stream of another meta block
version writes nothing, and the right key then starts the database. The
versions of records and nodes are refused with a
`VersioningStreamException`, now a `StreamFormatException`, whose message
says whether an older or a newer BergDB wrote the stream. The rule for the
next format change is in the Javadoc of `MetaBlock` and
`StoredTrans.RECORD_FORMAT`, with one change: a node's new layout changes
`RECORD_FORMAT` too. The TODO in `DbStarter` and
`StoredTrans.CURRENT_FORMAT_VERSION` are gone. Tests; `before-commit.sh`
and `level2.sh` pass, StreamDigest identical, the probes again. Found on
the way, not fixed: `SalsaStream.getLength()` does not count what it
appends, which BergDB's own stack does not meet.

2026-10-25. Added 005-41 to 005-43, at Frans's request ("as proposed"), by
Claude (Opus 5.5, Claude Code), from the review of the TODO markers in
`java/` (006-05). 005-41: Frans's idea of `isDurable()`, from two comments
in the Pub API, which are gone. 005-42: `transactionInfo()`, from a TODO
of 2016 and a probe: a transaction that writes an index entry gives a KV
whose `key()` throws, and a value that reclaim has rewritten gives
reclaim's step, at 14,078 s for a put at 1 s. 005-43: two small fixes.
005-11's option B names the unit tests of `addReplica`, from a TODO of
2014 in `DbHelper`, which is gone. Found on the way, in 005-41: a sync
waits for every byte of a transaction but its last, the commit byte; it
is right because the buffer sizes in use are multiples of 4, and a core
API caller can choose another.

2026-10-25. 005-43 done, by Claude (Opus 5.5, Claude Code), as proposed:
`Db.getTrans` refuses a position at or past the end of the stream with an
`IllegalArgumentException`, where it threw a `DbException`, and
`PubKeys.udir2idir`, which the Pub API's `IndexBuilder.dir` and
`UsePrimaryBuilder.dir` use, refuses a bad directory with one, where it
threw a `BadFormatException`. Two tests, which fail without the change;
`before-commit.sh` passes.

2026-10-25. 005-41 decided, by Frans ("my decision: C, not now."): no
`isDurable()` for now. Its first finding, the sync one byte short, added
as 005-44, at his request ("Yes, register as an 005 item, fix it, then
commit the fix."), by Claude (Opus 5.5, Claude Code).

2026-10-25. 005-44 done, by Claude (Opus 5.5, Claude Code): a sync waited
until the durable length reached the transaction's last byte, the commit
byte, so it returned while that byte could still be in the write buffer;
with a buffer whose size is not a multiple of 4, which the core API
allows, a crash right after the sync lost the transaction, in 10 runs of
10 of a probe. Now `Db.sync` waits for the position after that byte, and
`Db` keeps the end of the last transaction instead of its last byte. An
f-test that fails without the fix; `before-commit.sh` passes.

2026-10-25. 005-33 decided, by Frans ("bergdb 005-33. Decision: A. Note
the decision in the readme. Implement it. Then commit if successful."):
option A, one clear error. Done, by Claude (Opus 5.5, Claude Code): a start
refuses a stream that holds a creation which did not complete, and no
committed transaction, with a `DatabaseNotCreatedException` (in
`bergdb.pub.util`, for the application to catch) that says what happened
and what to do; it does so before recovery, so it writes nothing. Before,
it threw one of three `StreamFormatException`s, after recovery had
zero-filled a cut first transaction. Without a crypto key, a stream whose
magic bytes are wrong is no longer called a wrong key. Tests;
`before-commit.sh` and `level2.sh quick` pass. Found on the way, for
005-11: with a replica, a stream that ends inside its first meta block
fails the start earlier, in the check of the streams' IDs.

2026-10-25. Before release 2026.1 (item 008), at Frans's request ("Are
there any known bugs in BergDB? If so, we should fix them before the
release."), by Claude (Opus 5.5, Claude Code): the known faults that were
left are those of the open entries 005-11, 005-33 (done meanwhile, in
another session) and 005-42, and two found on the way and not fixed, in
005-40 and 005-41. Frans's answers: 005-11, "Keep it, document as
experimental"; 005-42, "A1 + B2 as proposed"; 007-03's steps 2 to 5,
"After the release".

2026-10-25. 005-42 done, by Claude (Opus 5.5, Claude Code), A1 and B2 as
decided: `transactionInfo()` leaves out the KVs under the internal prefix,
so every `key()` works, and throws `LookupTimeNotAvailableException` for a
value that reclaim has rewritten, where it gave reclaim's step. Added
005-45, the two faults found on the way, and done: `SalsaStream.getLength()`
counts what it appends, and `WTransaction.sync(SyncLevel)` waits for its own
transaction. 005-11: the Javadoc of the Pub API's replica methods,
README.md and docs/levels.md say that replication is experimental, with
its faults. Tests that fail without the changes; `before-commit.sh`
passes.

2026-10-26. Added 005-46, found in item 009's measurements (009-03) by
Claude (Opus 5.5, Claude Code), during Frans's unattended run of 009: a
read of the stream's last file waits for the writer's append and its
`fsync`. And 005-38 got 009's answer to its question 4 for the 10M load on
s1 (009-03, section 7): 2026.1's eviction made most of its time.

2026-10-26. Added 005-47, at Frans's request, by Claude (Opus 5.5, Claude
Code): a durability of "written, not forced", Frans's question of the day
("Would the middle-ground be good to support too? That is, ensuring the
write left the process."). Three options, A recommended: a property of
the storage, `FileStream` without a force per append. Found on the way,
from the code: records have no checksum, so recovery cannot tell a hole in
an unforced tail from data; `FileStreamPowerLossTester` models a lost tail
and a prefix of it, not a hole. That holds today too, for one chunk
between its write and its force.

2026-10-26. Added 005-48, at Frans's request ("Yes, group commit as
005-48."), by Claude (Opus 5.5, Claude Code): group commit, proposed in
005-13 and not done there. A sync that waits asks `BufferedStream` for a
flush instead of waiting for its timer; the force paces the groups.

2026-10-26. 005-38 done, by Claude (Opus 5.5, Claude Code), with Frans:
the stream's growth per key at scale was 004-02's startup distance of 10
MB; at 200 to 1000 MB a put costs 180 to 670 bytes of stream at 10M and
50M keys (random updates, in memory). Node size 30 stays. Found: the index
is written in bursts at large startup distances, and a database starts
only with the node size it was written with.

2026-10-26. Added 005-49 and 005-50, at Frans's request ("Yes, register
the burst entry. Yes to node-size fix entry."), by Claude (Opus 5.5, Claude
Code), both found in 005-38: smooth index writes (the bursts at large
startup distances; 007-03's step 3 waits for it), and a start with another
node size, which should fail with a clear error, only that.

2026-10-26. Added 005-54, by Claude (Opus 5.5, Claude Code), in the docs/
cleanup (006-07), as Frans approved ("Everything as recommended"): the
open questions of the problem statement, now 011-01, that had no other
home (Q1, Q2, Q3, Q5, Q8).

2026-10-26. Added 005-55, at Frans's request ("Add a Fix item to 005. I
want a real fix for this, not SuppressWarnings. finalize() need to go. In
the item, propose a solution, but do not implement it."), by Claude (Opus
5.5, Claude Code), from the note of deprecated API that every build
prints: six uses of `finalize()` and two of `Class.newInstance()`.
Proposed: a `Cleaner` in `Db` in place of `finalize()`, which keeps the Pub
API's promise that a database dropped without `stop()` is stopped; an
eviction thread that lets go of the `Db` while it waits; the test code
stops its databases. Found on the way, with probes: a dropped database
whose eviction thread has started is never collected, as the thread holds
the `Db` (since 009's step 3b; one such database in the f-tests); and the
unit tests leave 211 storage threads of databases not stopped, which only
finalization cleans up. No change to `java/`.

2026-10-26. Added 005-56, at Frans's request ("Add a todo item to 005 to
investigate package dependencies. How do packages depend on each other?
Does this follow the documentation in package.html files?"), by Claude
(Opus 5.5, Claude Code). A first look, by the import lines and `jdeps`:
four of `java/src`'s nine packages use packages that their `package.html`
does not list (`stream`, `dag`, `pubimp`, `pub`); beyond 010-01's five
mismatches, `pub` also uses `pubimp`, `common` and `nanotest`. The rules
intended in 2012 and 2015 are in Frans's notes in F1-007. No change to
`java/`.

2026-10-27. 005-46 got a second case, from the soaks of 009-04 (section
7.3), by Claude (Opus 5.5, Claude Code): every read from the stream waits
while reclaim's physical cut deletes files and forces the directory after
each (`FileStream.pretruncate`, on the stream's monitor), 88 to 171 ms in
P4's soak on F53 under every collector. One option added, the deletes
outside the monitor; "Done when" includes P4's soak. No change to `java/`.

2026-10-27. 005-56's question 4 asks, at Frans's request, whether 006-08's
`deps.py` and `core-build.sh` become a step in `java/before-commit.sh`;
decided when 005-56 is worked on. No change to `java/`.

2026-10-27. 005-56 got a section "After 006-08", at Frans's request: 006-08
fixed `stream` (its tester moved to `core`) and `dag`'s and `stream`'s
lists; `deps.py` on `java/src` now finds 7 uses not in a list, all in `pub`
and `pubimp`, and one cycle, `pub` with `pubimp`. No change to `java/`.

2026-10-27. 005-46: item 009's target 2 waits for it, as Frans restated
the target for BergDB's own code, the collector's pauses not counted
(009-01, target 2). By Claude (Opus 5.5, Claude Code). No change to
`java/`.

2026-10-27. 005-55 decided, at Frans's word ("I think no safety net is
reasonable. [...] Calling close() is a reasonable requirement. And the
database is crash-tolerant anyways."): `finalize()` goes with nothing in
its place, the Pub API's promise of a stop by the collector goes, and the
tests stop their databases. By Claude (Opus 5.5, Claude Code): the entry
rewritten around the decision, the `Cleaner` kept as not chosen;
recommended, no change to the eviction thread (so independent of 005-51)
and a check in the suites for databases not stopped; new questions 5 and
6. No change to `java/`.

2026-10-27. 005-50: the fix proposed, at Frans's request ("Propose a
solution were the node size is stored in the MetaBlock."), by Claude (Opus
5.5, Claude Code): the size at offset 44 of the meta block, in reserved
bytes, so no new version, and release 2026.1 starts such a database; a
start with another size is refused with a `DbException` before recovery
writes; a stream written before has 0, starts as today, and has the size
from its next meta block on. Found: a start with a smaller size than
written can succeed and leave a stream that no start opens (question 3).
A prototype with its tests and probes, checked; no change to `java/`.

2026-10-27. 005-46 investigated, and a fix proposed, at Frans's request
("Investigate this more thouroughly. What is you proposal. Document your
findings. Don't implement it yet, but propose a solution."), by Claude
(Opus 5.5, Claude Code), with probes on F53 (46-stream-file-lock/). Both
waits reproduce, and 009's pause probe with a slow force now and then
shows s1's pattern of 009-03 (both readers and the writer stopped for the
force). Found: every read also waits while a new file is forced
(`newFile` holds the stream's monitor); an encrypted database's reads wait
for each other (`SalsaStream`); a commit by an interrupted thread that
makes a physical cut, or that waits for room in the write buffer, fails
the database. Proposed: positional reads on a channel of each file's own,
without a lock and safe from interrupts; the file list without a lock; a
new file made outside the stream's monitor; a cut's files deleted on a
thread of their own, in today's order; `SalsaStream` reads before its
lock. Five questions for Frans. `docs/levels.md` says the new waits
(section 7) and the interrupts (section 3). No change to `java/`.

2026-10-27. Added 005-57 and investigated it, at Frans's request
("Eliminating these reads seem like the way forward to recude the startup
time. Add this as a todo item to 005. Investigate this in detail and
document your findings in the item. ..."), by Claude (Opus 5.5, Claude
Code): rule 4 needs no header reads at startup, and the writer's
`resolvePointers` none either (a map of the pinned objects by position).
Prototypes of both in scratch clones (the diffs in 57-startup-header-reads/),
checked against today's code by id in before-commit, level2.sh and
level4.sh (full), and on 007-05's databases: no difference. Two scenarios,
10M keys at 50 and 200 MB, against release 2026.1 and the current code:
cold on s1 from 214 and 210 s to about 46 and 51 s, warm on F53 0.7 to
0.9 s less. Part 1 alone moves its reads into the time after the start.
Four questions for Frans. No change to `java/`.

2026-10-27. 005-46 decided, at Frans's word ("1. as proposed. 2. Yes. 3.
Include in this item. 4. Please elaborate in this one. 5. no, but such
conditions are worth noting in test reports."): the cut's files deleted on
a thread of their own; a failed delete fails the stream at its next
operation; `SalsaStream` and interrupts are part of the entry; a writer's
wait for room in the write buffer does not count against item 009's
target 2, and the test reports note it, with the forces (change 7). By
Claude (Opus 5.5, Claude Code): the section "Interrupts", with
`InterruptProbe`: today an interrupt fails the database in a commit that
waits for room or makes a cut, hangs it when it reaches the storage
thread (a `Bug` ends the thread, and syncs wait for ever), makes the first
`Db.close()` return before the storage is closed (its thread stays, waking
every 5 ms), makes a new `FileStream` (`dir()`) throw, and a job's
`join()` throw an `Error`. Proposed: an interrupt never fails or hangs the
database; `sync()`, a job's `join()` and the Pub API's wait before a rerun
end on it, every other call ignores it until done, and the flag is always
kept. One question for Frans. No change to `java/`.

2026-10-27. 005-50 done, by Claude (Opus 5.5, Claude Code), at Frans's
request, after his decision on the proposal ("No need to consider "today's
databases". There are none."; a `StreamFormatException`; 1 or 2 bytes):
the node size is in every meta block, 2 bytes at offset 44, and a start
refuses another size with a `StreamFormatException`, and a database whose
meta block has none, written before, with a `VersioningStreamException`,
before recovery writes. The meta block's version stays 154. Tests;
`before-commit.sh` and `level2.sh quick` pass; StreamDigest identical but
for the two bytes (`metamask=44:2`, new).

2026-10-27. 005-46 implemented and committed, at Frans's request
("Decision: A. When possible, implement this and commit it."; on the
gates, "Yes, commit sooner."), by Claude (Opus 5.5, Claude Code): reads
without a lock (positional reads on a channel of each file's own, a list
of files replaced, never changed), a new file made outside the stream's
monitor, a cut's files deleted by a thread of their own, `SalsaStream`
reading before its lock; rule A for interrupts (decided by Frans after two
options were laid out: `sync()`, a job's `join()` and the Pub API's wait
before a rerun end on an interrupt, every other call ignores it, the flag
is kept, BergDB's own threads go on); the writer's waits for room and the
forces in the test reports. Tests, `InterruptStress` in `level3.sh`;
`before-commit.sh`, `level3.sh` full and `flush-order.sh` pass. Still
open: the measurements on s1 and P4's soak (005-46, "Implemented").

2026-10-27. 005-55 done, by Claude (Opus 5.5, Claude Code), at Frans's
request ("Yes, fine to delete it. Implement this. If successful, commit
the changes."), as decided, with questions 3 and 5 as recommended:
`Db.finalize()` is gone and `stop()` or `close()` is required (`Db`'s and
`Database.stop()`'s Javadoc). The 188 unit and f-tests in 21 classes that
left a database running stop it, found by a per-test leak finder
(`55-fix-finalize/LeakFinder.java`); `DbTester`'s three `testFinalize` are
gone. Found on the way: two night tests (`KvComparison`'s restarted copy,
`PayTest`) and two stress programs (`RestartStress`, `ReclaimStress`, their
restarts without a stop) ran out of memory without `finalize()`; they stop
theirs now. `bergdb.dev.Unit`, `F` and `Night` check that no test leaves a
database running. `ValueNodeTotalMem` deleted; `Class.newInstance()`
replaced. `build.sh` prints no note; `before-commit.sh` and `level1.sh`
pass.

2026-10-27. 005-57 decided and done, by Claude (Opus 5.5, Claude Code).
Frans: "1. Part 1 alone. 2. Do not care about streams written with older
releases. 3. No, not now. Let's get this in place now. 4. Yes, but in a
separate work item in 005. Go ahead. Implement and commit this." Rule 4
(`DbStarter.linkD`, `NodeCollection.linkToCanonical`) finds a pointer's node
by its position, with no read of the stream but for a top node's pointer
that the maps do not resolve; with assertions on it also runs by node id
and fails on a difference. Four tests; before-commit, level2.sh quick and
level4.sh quick pass on `cec0032` with the change, level2.sh full on
`bf19075` with it, with the check at every startup. Part 2 not made.
005-58 added for the Lean theorem.

2026-10-27. Added 005-59, at Frans's request ("Add Question 6 as a new 005
entry."), by Claude (Opus 5.5, Claude Code): 005-55's question 6, `Db` and
`Database` as `AutoCloseable`; four options, A recommended. 005-55: the
change of the API noted for the next release in `releases/next.md`, a new
file with the next release's notes (Frans: "Good catch. Add a file to
bergdb/releases/ with this note."; "Sure, add limited release notes.": also
005-46, 005-50 and 005-57); question 4 left as it is (Frans). No change to
`java/`.

2026-10-27. 005-51 done, by Claude (Opus 5.5, Claude Code), at Frans's
request (006-09, W4: "yes, put it in java and commit."): the eviction
thread waits with no timeout when idle, the database's close wakes it, and
`close()` returns after it has ended. A unit test that fails on the code
before; `before-commit.sh` and `level4.sh` (full) pass.

2026-10-27. 005-03 done by item 009, at Frans's word ("Yes", 006-09), by
Claude (Opus 5.5, Claude Code): handles removed the sweep it measures; the
capacity controller runs batches of at most 2 ms, and the questions are
answered by 009's measurements (005-03, Outcome).

2026-10-27. 005-46 measured, at Frans's word ("Go!"), by Claude (Opus 5.5,
Claude Code), split with the session of 006-09, which has the soak and
ScaleBench in its quiet block (W1.3, W1.4). On s1, the pause probe with
the jars before and after 005-46 in turns: before, under ZGC, 19 of the 20
longest gets ended with a file force of the same length; after, none did,
and in one phase a force of 2,500 ms left every get at 12.1 ms at most,
while the commit beside it waited 1,463 ms for room in the write buffer,
which the report now shows apart. On F53 the entry's probes: no reader
waits for a slow force, a new file or a cut (a cut of 57 files from 309 ms
to 0.5 ms for the cut and 7 ms for the readers), and every call by an
interrupted thread returns and keeps the flag. In 46-stream-file-lock/after/.

2026-10-27. 005-46 done, at Frans's word ("Close it now", asked whether to
close it on the day's measurements or wait for P4's soak and ScaleBench), by
Claude (Opus 5.5, Claude Code). The soak and ScaleBench run in 006-09's
quiet block as a confirmation, and as item 009's evidence for its target 2;
if they show a read or a commit waiting for the stream's writer, 005-46 is
opened again.

2026-10-27. 005-58 done, by Claude (Opus 5.5, Claude Code; the review at
max effort, at Frans's word), as 006-09's W3: rule 4 by position is proved
in the Lean model to link what rule 4 by node id links (`Rule4_positions`,
`Rule4Pos_handles`, `RunPos_handles`; `7c1ce2f`), with no new assumption;
lake build clean, trace tests OK, axioms standard. 005-57's report and
docs/levels.md cite it. For Frans: the trusted additions, and whether the
by-id check in `linkToCanonical` goes (recommended: it stays).

2026-10-27. Added 005-60, block storage: the stream on a raw block device
without a file system, as a ring of a fixed size, at Frans's request (his
idea). The questions; nothing started.

2026-10-27. 005-48 in the code (`e611709`), by Claude (Opus 5.5, Claude
Code), as Frans decided (006-09: "Yes", if it passes the gates, keeps the
stream's bytes and measures well): a sync that waits starts the flush. The
level3 failure seen with it was a race in `ReclaimReaders`'s check, also
without it, fixed there. Still open: F53's runs tonight and question 4.

2026-10-27. 005-58: Frans's decisions on its two questions ("1. As
recommended. 2. As recommended."): the trusted additions stay as they are,
and so does the check under assertions in `linkToCanonical`.

2026-10-27. 005-49 done, by Claude (Opus 5.5, Claude Code; at max effort,
at Frans's word), as 006-09's W2: the report (49-smooth-index-writes/
report.md) recommends a paced take for 007-03's step 3, with the deadline
as its backstop; a prototype in paced-take.diff (before-commit OK,
RestartInvariance identical). Nothing in `java/`. For Frans: is a section
held at sd the right meaning of the startup distance, and should the
default or the advice of 005-38 change?

2026-10-27. 005-49: Frans's answers to its two questions: the setting of
the startup distance is the target size of the startup section, the actual
startup distance is such that the stream's size minus it is a safe
position to start from; the default setting stays 50 MB for now.

2026-10-27. 005-61 registered and done, at Frans's request (006-09: "Fix
005-53's Reclaim fault"), by Claude (Opus 5.5, Claude Code): Reclaim
spaces its iterations by the database's live startup distance instead of
the builder's copy. Two unit tests; StreamDigest identical (36 of 36);
`before-commit.sh` and `level3.sh` (full) pass.

2026-10-27. 005-59 decided and done: Frans chose option A (006-09, 17:27),
with the other questions as recommended; by Claude (Opus 5.5, Claude
Code): `Db` and `Database` implement `AutoCloseable`, `Database.close()`
waits as `Db.close()` does; tests; `releases/next.md`; `before-commit.sh`
passes.

2026-10-27. 005-63 added, by Claude (Opus 5.5, Claude Code) in 006-09,
for Frans to decide: one database per directory, also while one closes;
found when level2's step 6 (`BryanRepro`) failed on `main` from 005-46 on,
as the test started a database right after `stop()`; the test now uses
`close()` (`b0661ba`).

2026-10-27. 005-62 added and its theorems proved, at Frans's request
(006-09: "Lean: T9 and T12 over handles"), by Claude (Opus 5.5, Claude
Code, at max effort): `T9_handles` and `T12_handles`, Level 3's reclaim
theorems with eviction over handles' runs (`bba91dd` to `a506b34`); an
independent review at max effort found them faithful to `T9_readCut` and
`T12_evictCut` and not vacuous; lake build clean, axioms standard, trace
tests OK. Open: what to remove of the design before handles, for Frans.

2026-10-28. 005-63 updated with Frans, by Claude (Opus 5.5, Claude
Code): option B worked out as a lock file, `bergdb.lock`: its text,
never deleted, a lock on one byte beyond its end, taken before the
listing and released last, crashes, tests; several instances on one
directory not considered now.

2026-10-28. 005-63 decided and done: Frans chose option C (08:13), made
by Claude (Opus 5.5, Claude Code). `FileStream` holds an operating-system
lock on `bergdb.lock` in its directory until it is closed; a second one
on the directory, in the JVM or in another process, is refused with the
new `DirectoryInUseException`. Within the JVM a set of the locked
directories refuses first (Frans's choice, a deviation from 010-P9):
closing a refused channel released the first's lock for other processes
on macOS. `stop()`'s Javadoc and network file systems in `FileStream`'s;
tests; six tests and stress programs that restarted right after `stop()`
call `close()`; `releases/next.md`. `before-commit.sh`, `level3.sh`,
`level2.sh` and `level4.sh quick` pass.

2026-10-28. 005-48 closed by Frans ("Close, keep 20 ms as recommended.
Commit."): group commit is in `main` (`e611709`); the buffer time stays
20 ms; F53's runs, refused in 006-09's night by `performance.sh`'s quiet
check, are no longer a condition. The test runs' raw outputs and the
prototype's diff removed from `48-group-commit/`; the scripts, the tables,
the tools and the ReclaimReaders experiment kept. By Claude (Opus 5.5,
Claude Code).

2026-10-28. Added 005-64, at Frans's request ("create a new 005 item to
investigate 20 ms vs 50 ms, vs 100 ms"), by Claude (Opus 5.5, Claude
Code): the buffer time after group commit.

2026-10-28. 005-56 decided and done, as Frans decided (006-09, section 8,
decision 6), by Claude (Opus 5.5, Claude Code): the `package.html` lists
in one form, `Depends on: a, b, c.`, with `pub`'s and `pubimp`'s changed
as the entry's table proposed; `SyncLevel` moved from `bergdb.core` to
`bergdb.pub.util` (55 files; an API change against 2026.1, in
`releases/next.md`); `Database.PRIMARY` and `TestClock`'s range in `pub`,
`ClockConstants` deleted; `TimeResolver` stays in `pubimp`. `java/deps.py`
checks each package's uses against its list, a step of
`java/before-commit.sh`: "9 packages, all as package.html allows".
`before-commit.sh` and `level2.sh quick` pass.

2026-10-28. Added 005-65, at Frans's decision on item 009's target 2
(006-09, decision 2), by Claude (Opus 5.5, Claude Code): the gets of 27
and 36 ms with 8 readers in ScaleBench from the OS's cache at 665 MB under
ZGC, with waits of a reader's load for the eviction thread over 10 ms; a
hypothesis to test (the readers take F53's 8 performance cores since
005-46) and a night step that runs 4, 6 and 8 threads on `bf19075`,
`eaec93e` and `4f7cd60` with the eviction thread's CPU, smoke-tested. Item
009 is closed with this case open here.

2026-10-28. Added 005-66, at Frans's request (09:43), by Claude (Opus
5.5, Claude Code): the Pub API's builder opens its directories in
`start()`, not in `dir()` and `replica()`, so that a builder that is
never started holds no directory's lock (005-63's outcome); kind
implement.

2026-10-28. 005-66 done, by Claude (Opus 5.5, Claude Code), as
registered: `DatabaseBuilder.dir()` and `replica()` record their
directories, `start()` opens them, the database's first, and closes them
if it fails; a builder that is never started holds nothing. Javadoc, two
tests in `PubTester` that fail on the code before, `releases/next.md`;
`before-commit.sh` and `level2.sh quick` pass.

2026-10-28. 005-56's follow-ups, as Frans decided ("as proposed"; "Do not
add core-build.sh to before-commit.sh. Ensure it runs nightly."), by
Claude (Opus 5.5, Claude Code): three stale `package.html` titles
corrected, a `package.html` for `src-dev`'s `bergdb`, `bergdb.dev.props`
and `frans.bryan`, `Factory`'s comment names `Time`'s `TimeResolver` too,
and 010-01's P12 names its measures. 006-08's `core-build.sh` is
`java/stress/core-build.sh`, a step of `java/night.sh`; `java/deps.py` got
`--layer PKG [--list]` for it.

2026-10-28. 005-62 done, by Claude (Opus 5.5, Claude Code), as Frans
decided ("as proposed, all steps"; "Prove it!"; a cut without a restart:
"No, not for now"): the design before handles removed from lean/, steps a
to c, and rule 4 by position after a cut proved, with Java's skip of the
pointers below the stream's first position.

2026-10-28. Added 005-67, at Frans's request (through 006-10's session),
by Claude (Opus 5.5, Claude Code): `StorageManagerTester.testAddReplica2`
fails about one run in twelve, "Expected 700, got 200", a race known since
2015 and never fixed, which now fails nights; kind fix.

2026-10-28. 005-67 done, by Claude (Opus 5.5, Claude Code), as
registered: the test was wrong, not the code. `testAddReplica2` asserted
the streams' lengths right after an append, before the replica's buffer
had written the sync's last bytes and before the buffers had written the
append; now it waits for the confirmed lengths. The writer of
`testAddReplicaWhileAppending` takes the write lock, without which the
test could hang. Forced interleavings made each failure certain before
and none after; 0 failures in 400,000 runs after the fix, 4 in 40,000
before. 2015's "Expected 800, got 1200" was `BufferedStream`'s flush of
nothing at a close, fixed by 005-14. `before-commit.sh`, `core-build.sh
unit f` and `level2.sh quick` pass.

2026-10-28. 005-53 and 005-52's questions 1 and 3 ready to decide, by
Claude (Opus 5.5, Claude Code), for 006-10's W4.2, a reading of `b1111f4`
with D4:B in the core: options in full in both entries, the evidence in
[53-startup-distance-on-the-fly/report.md](53-startup-distance-on-the-fly/report.md).
005-53: options A to E; B (a `Job`) and D are obsolete, as one call is
enough since D4:B and nothing would run in the background, and C is
subsumed; E recommended, `Database.setStartupDistanceInMb` and
`getStartupDistanceInMb`, kept in the stream as today, a call with the
value in force writing nothing. 005-52: B recommended,
`Database.setCacheSizeInMb` and `getCacheSizeInMb`, clamped as the
builder, for the run only, through a setter in `Db` that JMX uses too.
One pattern for both, decided and built together: a setting that shapes
the stream's bytes is kept in the stream, one that does not is for the
run. Each entry ends with questions for Frans, each with a recommended
answer.

2026-10-28. 005-53 and 005-52 done, by Claude (Opus 5.5, Claude Code),
for 006-10, as Frans decided (2026-10-28, 12:32: "53 and 52. Yes, do this
as recommended.", the smaller questions as recommended), in one commit
(`fd8f513`): `Database.setStartupDistanceInMb` and
`getStartupDistanceInMb` (005-53's E), kept in the stream through
`Db.setStartupDistance`, which now writes nothing for the value in force
and changes nothing when the call is refused; `Database.setCacheSizeInMb`
and `getCacheSizeInMb` (005-52's B), for the run only, through the new
`Db.setCacheSizeIndicator` and its getter, which JMX uses too, the setter
waking the eviction thread after a decrease. Tests in `PubTester`,
`DbTester` and `CapacityTester`, each failing on a mutation of the change;
StreamDigest identical (36 of 36); `before-commit.sh`, `level3.sh` and `level4.sh` (full) and `level2.sh quick` pass. Left: 005-52's pause probe
with a lowered budget, for a quiet block.

2026-10-28. Added 005-68, at Frans's decision (2026-10-28, 13:09, "as
recommended", through 006-10's session), by Claude (Opus 5.5, Claude
Code): 007-08's review found that `Db.store` passes `getLength()` to
`TransSeq.take` where the model's argument is `getNextPos()`, which would
differ by a meta block after a record that ends on a block boundary; kind
fix.

2026-10-28. 005-68 dropped, by Claude (Opus 5.5, Claude Code): the
finding does not hold. `RecoverableStream.append` writes the meta block
with the record that ends at its position, and every start's recovery
fills out one that a crash cut, so `getLength()` equals `getNextPos()`
whenever `take` is called; an instrumented copy found 0 of 5,524,901
calls to differ, 229 of them after a record that ended exactly on a
boundary. No change: the change would pass the same value.

2026-10-28. Added 005-69, by Claude (Opus 5.5, Claude Code), the
conductor of 012, as 012-01's decision D5 says: `SystemClock` never sets
its last time, so its promise of strictly increasing times does not hold;
harmless, as `DbClock` keeps its own; kind fix, open for Frans's choice
between the code and the comment.

2026-10-28. Added 005-70, 005-71 and 005-72, by Claude (Opus 5.5, Claude
Code), the conductor of 012, from 012-02's determinism audit (its section
10.3, findings C4, C3 and C2, each with a probe), as 012-01's decision D5
says: the STM's `KeyModSet` is empty after a start, so a read before a
restart can commit where it would be refused (a correctness bug, kind
fix); `DbClock`'s last read time is not kept across a start (kind fix);
the files after a physical cut depend on timing (kind decide).

2026-10-28. Added 005-73, by Claude (Opus 5.5, Claude Code), the
conductor of 012, from 012-03's mapping of `Db`'s methods (its section
6.8): seven small findings in the API, none changing the bytes; kind fix.

2026-10-28. Added 005-74, by Claude (Opus 5.5, Claude Code), the
conductor of 012, from 012-06's corrupt-input tests (its section 7, F2
and F3): a negative node size makes `StoredTrans.Parser` loop until the
heap is gone, and sizes are allocated before they are read; kind fix.

2026-10-28. Added 005-75, by Claude (Opus 5.5, Claude Code), the
conductor of 012, from 012-02's review, 012-04 and 012-06: dead checks
(`KeyNode.checkIncreasingTime` checks nothing) and comments that differ
from the code; kind fix.

2026-10-29. 005-64 ready to decide, by Claude (Opus 5.5, Claude Code),
006-10's morning write-up: the runs of questions 1 to 4 at 20, 50 and 100
ms (F53 9 rounds, not quiet; s1 6 rounds; trickle and idle on F53), the
tables and a recommendation in the entry: keep 20 ms. The summaries in
`64-buffer-time-after-group-commit/night/results-*-2026-10-28.md`.

2026-10-29. 005-65 measured, by Claude (Opus 5.5, Claude Code): the
results of `threads.sh`'s quiet run of 2026-10-28 night, the hypotheses
against their predictions (H2 and H3 hold, H1, H4 and H5 refuted), the
explanation (005-46's readers fill F53's cores; `evictorLock` in
`Eviction.wake` concentrates the long waits, a fifth of the gets over
10 ms) and a recommendation for Frans; the summary in
`65-gets-with-8-readers/night/results-2026-10-28.txt`. No change to
`java/`.

2026-10-29. Added 005-76, at Frans's request (2026-10-29, 09:36, "Also
register a 005 fix for the rest", when he set the default buffer time to
50 ms in 005-64), by Claude (Opus 5.5, Claude Code), 006-10's session:
`BufferedStream` checks the quarter rule only when its thread wakes, so
at a high rate and a long buffer time writers wait for room (005-64's
runs at 100 ms: 13 to 16 % fewer puts a second at 1 KB values); proposed,
an append past a quarter wakes the thread; kind fix, registered only.

2026-10-29. 005-64 done, as Frans decided (2026-10-29, 09:36, "Use 50
ms."), by Claude (Opus 5.5, Claude Code), 006-10's session: the main
stream's default buffer time is 50 ms (`StorageManager.DEFAULT_BUFFER_TIME`,
was 20), its comment with the history and the data at risk, `Db`'s
Javadoc, docs/levels.md, 010-01's P3, `releases/next.md`. No test changed.
StreamDigest identical (36 of 36), also with the tests' buffer time at 50
ms; `before-commit.sh`, `level1.sh`, `level2.sh quick` and `level3.sh`
pass. The rest, the quarter rule, is 005-76.

2026-10-29. Added 005-77, as Frans decided (2026-10-29, 10:02, on
006-10's decision 4: "an entry for A as recommended"), by Claude (Opus
5.5, Claude Code), 006-10's session: after a one-call decrease from 1000
to 100 MB at 50M keys the catch-up's records are 12 to 14 times the new
mean (up to 15.4 MB; 007-07, section 11), from the pace's factor S/sd,
which starts at 10; proposed, investigate a cap of S/sd at 2 and at 4, at
10M and 50M keys, with the commit times in a quiet block; kind
investigate, registered only.

2026-10-29. Added 005-78, as Frans decided (2026-10-29, 10:09, on 006-10's
decision 6: "It really should be in the stream. It must be really, to
follow our principle of a deterministic stream. Still an Investigate
entry. Important to study first."), by Claude (Opus 5.5, Claude Code),
006-10's session: the retain duration decides reclaim's iterations and
cuts, so the stream's bytes, but a start takes the builder's value, as
005-53 left it; the checks set it again after each start. Three forms to
study (the meta blocks, an internal KV, reclaim's table), the start, old
databases, replicas, StreamDigest and the Lean model; kind investigate,
registered only.

2026-10-29. 005-72: Frans chose A for 012's cross tests (done in 012-11)
and keeps the entry open to consider B; kind decide.

2026-10-29. 005-52 reopened at Frans's request ("Reopen 005-52, ensure it
is clear what is left to do."): the pause probe with a lowered budget
against a fixed one, the one point of "Done when" not met, now a section
of its own, Left to do, with three steps (a property for `PauseProbe` to
lower its budget mid-phase, four runs in a quiet block, the comparison);
back in Open.

2026-10-29. 005-80 registered at Frans's request ("Add an entry for \"The
setBudget split\" since I want to finish and I don't remember this
one."): `setBudget`'s race, fixed inside 005-65's commit `988fe1a`, with
options for a record and a test; kind decide, registered only.

2026-10-30. 005-70 done, option A accepted by Frans: the STM coverage
begins at the last recovered commit, and an older read set is refused.
Java and C fixed, with real-read restart regressions; the Java test fails
before the fix. BEFORE COMMIT OK, LEVEL 2 OK (full, 70 conformance traces),
C BEFORE COMMIT OK; StreamDigest identical (36 of 36). The original probe
now refuses both runs, whose 472-byte streams are identical.

2026-10-30. Added 005-81 at Frans's request, following 006-11: investigate
client overload across storage, CPU and memory, and replace the hard-coded
retry policy in RwTransaction.executeRw if supported by the measurements.
Source-checked plan with exact current sleeps, refusal/commit boundaries,
bounded arrival tests, recovery and fairness measures, and small retry
variants to compare. Registered and planned only; no Java changes.

2026-11-02. Frans selected 005-74 option A, the parser and reader size
checks. Its later checksum and recovery findings stay open in their own
entries, 005-82 and 005-83; neither is silently closed with option A.

2026-11-02. 005-74 option A done: sizes checked before parsing and
allocation, including bounds inside a reused record buffer and reads
across meta blocks. BEFORE COMMIT OK (1,082 unit, 78 f), LEVEL 2 OK
(quick, 14 traces), all 36 stream digests unchanged. Moved to Closed;
005-82 and 005-83 remain open.

2026-11-02. 005-75 done, by Codex, at Frans's request: key-node and
startup record time/order checks fixed, append checks its buffer offset,
two dead checks removed and comments corrected. Startup seeds STM coverage
after validating recovered times. Four regressions fail on the previous
behavior and pass with the fix, with and without assertions. BEFORE
COMMIT OK (1,086 unit tests, 78 f-tests), LEVEL 2 OK (quick, 14 conformance
traces), StreamDigest identical (36 of 36); evidence in 005-75. Java only.

2026-11-02. 005-73: recommendations implemented except F4, deferred for
Frans to inspect the Java setter. F1, F2, F3, F5 and F6 fixed or removed;
F7 corrected: GetMany.cache removed, GetData pointer counters kept because
Huge reads them. close() retains its I/O failure for later callers, also
after stop(). BEFORE COMMIT OK (1,089 unit, 78 f-tests), all 36 stream
digests unchanged. Java only; entry stays open for F4.

2026-11-02. 005-73 closed after Frans approved F4: NaN explicitly
refused before changing the reclaim fraction; double API retained,
005-79 separate. Regression fails before and passes after. BEFORE COMMIT
OK (1,090 unit, 78 f-tests), all 36 stream digests identical.

2026-11-02. 005-83 experiment complete on 3ad171d: 56 ordinary controls
recover, all 56 hole images fail at startup or later reads (112 checks),
all already-forced bytes preserved in admitted images. The original
refused-start case appends 1,057,153 bytes before refusing. Item remains
open for a recovery contract and design; 005-82 remains unimplemented.

2026-11-02. 005-76 done, as Frans requested: BufferedStream notifies once
at a quarter crossing and does not wait with a quarter ready after a
flush. Three regressions fail before and pass after, with assertions on
and off. BEFORE COMMIT OK (1,093 unit, 78 f-tests), full LEVEL 2 OK (70
traces), full LEVEL 3 OK (25 traces, power loss and interrupts). All 36
logical StreamDigest cases match main; one physical cut differs with
flush timing. Three admitted performance rounds on each of F53 and s1
no longer reproduce the 100 ms penalty. Evidence and the strict digest
comparison's physical-cut difference are recorded in 005-76.

2026-11-03. New entries go to 015-todo from now on, numbered from 015-01,
at Frans's request. An entry closely related to a 005 entry may still be
added here, for now.

2026-11-04. 005-07 dropped at Frans's decision: obsolete, as the
synchronization model has changed substantially since handles (009).
Today's synchronization is reviewed in 016-07.

2026-11-04. 005-11 decided by Frans, "A with C2 now", and done: replication
removed from `java/` (the Pub API's `replica`, `addReplica`,
`removeReplica`, `getStorageInfos` and `SyncLevel.STRONG`, StorageManager's
replicas and the startup's copying, their tests), copies left to the OS and
the file system; the stream's bytes unchanged. docs/levels.md, section 9,
and README.md say so. The removed design and the options for a future
replication are 017-03. `before-commit.sh` passes.

2026-11-04. 005-54 moved to 017-04, cost bounds beyond startup, at
Frans's decision: a long-term topic, not item 007's (concrete work with a
plan, T3 proved and T4 a bound on D for startup) and not closed (Q1 points
at real behaviour; Q5 and Q8 have measurements that could become the
accepted answer). A question that becomes a real theorem goes to 007 then.

2026-11-04. 005-60, block storage, moved to 017-05 at Frans's decision
(19:05): "This is a big thing, long term, open-ended. Not a todo for 005."
Its contents, the idea, the seven questions, the principles and the notes
of 2026-10-27, are 017-05's now.

2026-11-04. 005-47 decided by Frans: "Use A, a setting. No force at an
interval. Nothing in the Pub API for now." Implemented: `FileStream(dir,
forceAppends)`, forcing on by default; with it off, forces stay at a file
opened for appends, the last file before a new one, before a cut's
deletes and at `close()`; `FileStreamPowerLossTester` has a mode without
per-append forces, with hole images, counted (014-01), and two negative
controls. Left: the sync latency on and off.

2026-11-04. 005-47: the sync latency on s1, `d-1k-t1`, 10 runs each on
`188facf`: the durable commit's p50 4.2 ms with forcing on, 0.1 ms off;
p99 12.3 and 1.1 ms. F53's runs are left for a quiet block.

2026-11-04. 005-81 split at Frans's decision (19:11): "005-81, I like
your idea to split this. So, split it." 005-81 stays open, narrowed to the
retries: the wait points and client contract they need, the diagnostic
harness, the hot-key and disjoint-key baselines, the retry variants and an
`executeRw()` proposal (its deliverables 1 to 3). The broad part, whether
BergDB needs database-wide admission control and backpressure for CPU,
reads and memory under overload (deliverable 4), is a long-term topic,
017-06. Replication's waits dropped from 005-81 (removed, 005-11), and its
mention of 005-07 corrected (dropped; 016-07).

2026-11-05. 005-72 closed as done at Frans's decision (decided
2026-11-04/05; asked 2026-11-04, 19:23, answered 2026-11-05, 07:17):
"Drop B, close." A covers what matters: the bytes from the decided cut
are deterministic, and the C clone's cross tests compare them; a file
layout that depends on timing has no effect a user can see.

2026-11-05. 005-77, cap the pace's factor S/sd, moved to 015-84
untouched, at Frans's decision (decided 2026-11-04/05): "005-77 (cap
pace factor, about a day of F53) moves to 015 untouched."

2026-11-05. 005-52 done: option B, decided by Frans on 2026-11-04 ("52,
do as recommend, Option B."), in `0c6c4be`: a transaction's warmup no
longer waits for eviction after a decrease. The six runs again, on s1 as
F53 was not quiet: no wait from the lowering on is longer than with a
fixed budget; four LONGER verdicts, all before the lowering, the
collector's and the machine's. Closed on the coordinator's reading of the
rule, recorded in the entry, so that Frans can reopen it.

2026-11-05. 005-47 and 005-65: the morning's quiet block on F53 (marker
from 07:22, limit 07:55) was not quiet, so neither timing run ran: 005-47's
sync latency on F53 and 005-65's AB/BA step (`threads.sh` with
`BUILDS="5a6befd 988fe1a" ROUNDS=4`), which Frans approved (decided
2026-11-04/05: "Run the AB/BA step in tonight's quiet block. Close the
entry if the fix isn't the cause; otherwise take the measurements and move
the decision to 015."). `mediaanalysisd` was paused by the coordinator at
Frans's word from 07:32 to 07:56; the 1-minute load still stayed at 1.33
to 3.11, and was 3.02 at 07:55. Both are left for the next quiet block,
with their commands, a built clone for 005-47 and a script for both in
`/Users/f/fl/bench/`.
