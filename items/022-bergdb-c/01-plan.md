# 022-01 The plan: the C clone at release 2026.3, then 2026.4

Created 2026-11-09 by Frans Lundberg. Status: open.

Frans, 2026-11-09, 10:08: "Create a new item for the updated C port,
release 2026.3 (then 2026.4). This allows us to leave some history behind
and start fresh. [...] I will decide later how long to update it in that
item, at least 2026.3 and 2026.4, maybe longer."

The work follows 012-18, the feasibility study of the port to 2026.3: its
section 3 says what C needs, section 4 what shows that C matches, section
5 the steps. This plan says who does each step, in which order, and how
the work is gated and landed. coord-1109 (today's head coordinator) set
its first form at 10:18; the session `022-bergdb-c` owns it and runs it.


# 1. The start

`c/` is a copy of `items/012-bergdb-c/c/` at `be51a78`, 012's last commit
to `c/`: the port of release 2026.2 (bergdb 015-02), taken with
`git archive be51a78 items/012-bergdb-c/c`, so without 012's `build/`.
The 202 files are equal to 012's. 012 stays as it is, the port of 2026.2.
Paths inside `c/` are relative and the depth is the same, so the copy
builds and tests where it is; step 0 checks that.


# 2. Decisions

* **D1, where**: this item (Frans, 10:08), replacing 012-18's D1.
* **D2, the C API**: 012-18's default (a): `bergdb_options.retain_duration`
  and `BERGDB_SYNC_STRONG` removed, as Java removed the builder's
  `retainDuration` and `SyncLevel.STRONG`; `bergdb_set_retain_duration`
  after the open is the one way, and it writes the settings.
* **D3, the workloads' settings**: the header's `set retain` and
  `set fraction` are applied once, after the creation's start, by Java's
  `Run` and C's `bergdb-run` alike (StreamDigest's `restarts-once`).
* **D4, the optional parts**: 012-18, section 6's default: 015-31, 015-68,
  015-70's test, the documentation in `bergdb.h` and the corrupt-stream
  set from 2026.3's refusal tests are in; the bounded sweep (015-67) and
  the limits harness are out; C's NOMEM refusal is kept, as a departure.

D2 to D4 are coord-1109's defaults of 10:18 and go ahead; Frans may
change them.


# 3. The steps to 2026.3

Each step's content is 012-18's, section 5.1, and the parts of its section
3.1 that it names.

| Step | What                                                      | 012-18       | After |
|---|---|---|---|
| 0 | the copy checked; the harness on 2026.3; the baseline         | 3.1 step 12  | -     |
| 1 | 015-87, 015-54, 015-50, 015-55; the API (D2); D3; vectors     | 3.1, 1 to 4  | 0     |
| 2 | 015-72, 015-75, 019-01, 019-34, 019-32, with Java's texts     | 3.1, 5 to 9  | 0     |
| 3 | the switch force, 015-06, 015-31; the power model's new mode  | 3.1, 10, 11  | 0     |
| 4 | D4: 015-68, 015-70's test, `bergdb.h`'s notes, corrupt set    | 3.2          | 1 to 3 |
| 5 | the long runs: `cross.sh full` and `scale`, the stress set    | 4, 5.1       | 4     |
| 6 | `c/readme.md`'s "Which Java", the item's report               | 5.1, step 6  | 5     |

* **Step 0** has one worker. It builds the copy and runs its gate as it
  is, against 2026.2 (`JAVA_REF=2026.2`), which shows that the copy
  works where it is. Then it makes the Java side compile against 2026.3
  (`SyncLevel.STRONG` and `retainDuration` out; D3 in `Run.java`;
  `Export.java`'s `restarts-once`; `java-build.sh`'s default
  `JAVA_REF=2026.3`; `examples/compare.sh`'s CoreDemo), writes Java's
  vectors again from 2026.3, and runs `cross.sh quick` and the unit tests
  with C unchanged: the negative control (012-18, section 4, point 7). Its
  record lists every difference by class and the step that removes it.
  D3 on C's side (`tools/run.c`) needs step 1's setter and is step 1's.
* **Steps 1, 2 and 3** run at the same time, one worker each, in their own
  clones; they touch different modules (012-18, section 3.1 names them):
  1 in `reclaim.c`, `db.c`'s settings and size check, `clock.c`, `api.c`,
  `bergdb.h`, `tools/run.c`; 2 in `strans.c`, `starter.c`, `meta.c`,
  `rstream.c`, `snode.c`, `ncoll.c`, `nstream.c`, `ntable.c`, `dag.c`,
  `getmany.c`; 3 in `stream.c` and `test/stress/power.c`. Where two touch
  one file, the later one to land rebases (section 5).
* **Step 4** starts when 1 to 3 have landed, as the corrupt set tests
  step 2's refusals and 015-68 and 015-70 touch the start and eviction.
* **Step 5** needs about 2 hours of a quiet F53 (012-18, section 5.1);
  coord-1109 gives the time.
* **Step 6** writes `c/readme.md`'s "Which Java" (2026.3, and this item's
  start at `be51a78`) and the report of the port, a subitem.


# 4. Then 2026.4

When release 2026.4 has its tag and `releases/2026.4/` (its release
candidate's checks run on 9 November), a short study as 012-18, from
`release-2026.3` to `release-2026.4`, limited to the Core's packages and
the harness, says what C needs; then the same steps, in this item. 012-18,
section 5.2 counted 9 commits in the Core after 2026.3, none a format
change (021-05 and 021-06 on keys, 019-46 a race, 019-47 the admission at
a start).


# 5. How the work runs

**Clones.** The integration repository is the bare
`/Users/f/fl/bench/022/int.git`, cloned from `main` with this item's copy
of `c/`; its branch `022` holds the landed work. Each worker has its own
clone of it, `/Users/f/fl/bench/022/<worker>/bergdb`, on branch `022`, and
builds there (`c/build/` stays in the clone). Only
`items/022-bergdb-c/` changes; `java/` and every other path stay as they
are, so `java/before-commit.sh` is not needed (AGENTS.md).

**The gate.** `c/before-commit.sh` is the gate, and it prints
`C BEFORE COMMIT OK` when it passes. Until steps 1 to 3 have all landed,
the gate against 2026.3 shows differences that a later step removes; a
landing then records, in its commit message and in this file's log, each
remaining difference and the step that removes it, and none may remain of
the landing step's own classes. From the landing of the last of steps 1 to
3 on, every landing passes the gate.

**Landing.** A worker commits in its clone, in Frans's name and without AI
attribution, with a message that starts with `022-01, step N:`. It then
runs `git pull --rebase` from `int.git`, rebuilds, runs the gate again on
the rebased tree, and pushes to `int.git`'s `022`. A refused push (another
step landed meanwhile) means the same again: rebase, gate, push. The
session then brings each landed commit to `main`: it applies the commit's
diff to `main`'s working tree (only `items/022-bergdb-c/`), stages those
paths and commits them by path (`git commit -- items/022-bergdb-c`) with
the same message, and tells coord-1109 the hash. The Git index of `main`
is shared, so the session never resets, stashes or checks out there.
`int.git` takes `main`'s later commits only when the work needs them (2026.4's
release files), by a merge of `main` into `022`.

**The log.** A worker adds one paragraph to this file's log in its landing
commit: what it changed, the gate's result, the differences that remain.
Java's faults that it finds go to the session, which asks coord-1109 for
their item numbers.

**F53.** Builds, unit tests, the gate (about 3 minutes) and
`cross.sh quick` run at any time. A run longer than 10 minutes, or any
timing, waits for coord-1109's word, which the session asks for. s1 cannot
build C (macOS only).

**Texts.** Where the scans and `corrupt.sh` compare exception names and
messages, C gives Java's, byte for byte, as 2026.3 has them.

**Effort.** Workers at xhigh, Frans's setting for today's subagents until
22:00 (coord-1109, 10:18).


# Log

2026-11-09. Created by the session `022-bergdb-c` from coord-1109's plan
of 10:18. `c/` copied from 012 at `be51a78`.

2026-11-09, step 0 (worker s0). The copy builds and passes its gate where
it is, against 2026.2 (`JAVA_REF=2026.2`): `C BEFORE COMMIT OK (225 s)`,
F53 under a load of about 20. The harness on 2026.3: `java-build.sh`
defaults to `JAVA_REF=2026.3` (its `SHA256SUMS` checked; `JAVA_REF=2026.2`
still builds 012's); `Run.java` applies the header's `set retain` and
`set fraction` once, after the creation's start (D3), and syncs with
`ORDINARY`; `Export.java` takes StreamDigest's mode `restarts-once`, which
`cross.sh` runs for the twelve configurations in `full` and once in
`quick` (`sd:l3-node14:restarts-once:n=600`); `MakeStreams.java` and
`StatsProbe.java` set the retain duration after the first start (the
probe prints a line `setretain` after `open`); `JBench.java` drops
`retainForever`, the default. 2026.3's `CoreDemo.java` is 2026.2's, so
`examples/compare.sh` needs no change. All compile against 2026.3,
`PowerImages.java` too. Java's vectors written again from 2026.3: only
`reclaim.txt` changed (its runs call `setRetainDuration`: the settings'
record, and 015-54's pSafe); the other eleven files are equal. Java's
`Run` gives StreamDigest's own digest in each of the quick set's seven
StreamDigest workloads, the four with reclaim and `restarts-once`
included, and the three modes of `l3-node14` give one digest (015-87).

The negative control, C unchanged against 2026.3 (012-18, section 4,
point 7). The gate stops at `unit`; its later steps were run by hand.
Every difference is of 015-87 and 015-54, step 1's:

* `unit`, both builds: `reclaim_java_vectors` (`reclaim.txt`).
* `func`: passes, but `f_settings.c`'s `java_stats` holds 2026.2's lines;
  `StatsProbe` on 2026.3 prints others (the settings' record, a get more
  at each start as `initFromDb` reads the settings, the setter counted as
  a transaction, the retain duration and the fraction kept at the
  reopen). Step 1 writes them in.
* `cross quick`: 152 differences, all in workloads with reclaim: the 11
  of its 23 workloads that reclaim (runs' texts, the streams from the
  decided cut, scans and dumps of C's directories: 79), the crash cuts of
  `reclaim-crash` (13 of 84 cuts: 26), the turns of
  `sd-l3-node14-restarts` (3), C's budget runs of the 11 (44). The 12
  workloads without reclaim, the 84 crash directories' starts and the 85
  corrupt variants: none.
* `write`: `bergdb-clockcheck` stops on 7 of Java's directories at the
  settings' record after the creation ("transaction 0: not the next
  record (264)"): it knows `setsd`'s dummy record, not the setters'.
  Step 1 (`tools/clockcheck.c`).
* `allocfail`, `examples`: pass.

No difference of steps 2 and 3 shows in the quick set: its corrupt
variants are bit flips, which 019-32's damage does not reach (012-18,
section 3.2), and 015-72, 015-75, 019-01 and 019-34 need records or meta
blocks made for them.

2026-11-09, step 1 (worker s0). 012-18, section 3.1, steps 1 to 4, D2 and
D3 on C's side. 015-87: reclaim's settings in the stream, the KV
`/#i/dreclaim/-settings.txt`, `retain=<d>\nfraction=<f>\n` byte for byte
as `serializeSettings` (`rc_settings_text`); `rc_set_settings` commits it
in an internal transaction unless the values are in force, refused first
once the top ordinals are used up (`db_refuse_if_top_ordinals_used`), the
fields set after the commit; `rc_settings_parse` refuses any other form
with an `InternalDataException` (ERR_FORMAT) as `parseSettings`, at every
start (`rc_init_from_db`, before the table) and in `bergdb-dump`'s start
(`sdb.c`); the two setters check the argument, then the state, then
commit. 015-54: pSafe is the stream's length at the marking. 015-50: a
step ends before a value that would take its value nodes past the value
limit (`db_value_limit`), and `check_size` is for user transactions only.
015-55: `dbclock_transaction_begin(user)`, user transactions refused after
`DBCLOCK_LAST_USER_TIME`. D2: `bergdb_options.retain_duration` and
`BERGDB_SYNC_STRONG` removed with every use (`bergdb_sync` takes 10 and 20
only); `bergdb.h` and `readme.md` say that the two setters commit, with a
transaction's errors, and are refused on a failed database. D3:
`bergdb-run` applies the header's retain and fraction once, after the
creation's start; `bergdb-clockcheck` meets the setters' records (after
the creation, and at `setretain` and `setfraction` lines). Java's tests
ported: `DbTesterRestart`'s eight on the settings and
`testReclaimSettingRefusedAtGoPoint` (`t_reclaim.c`, `t_db.c`'s top
ordinals, `f_settings.c`), `testSafePosAfterTheCallsRecords`,
`testStepWithinValueLimit` (`record_limit` 100 kB),
`testUserTransactionLeavesTimesForReclaim` and `testTimeMarginForInternal`;
`f_settings.c` holds StatsProbe's lines of 2026.3, which C prints.
`Run.java` closes the database when a header setter is refused, as
`bergdb-run` does. Departures: the refusal's text is cut at C's 240
bytes, and holds the value's bytes as they are (Java decodes them as
UTF-8); the harness compares only the exception's name. C has no
`stop()`: the setters' "not active" is a failed database (BERGDB_FAILED)
or a call from a callback (BERGDB_STATE).

The gate against 2026.3: `C BEFORE COMMIT OK (399 s)`, F53 under a load
of about 20 with other gates; `cross quick` 0 differences (23 workloads,
69 crash cuts, 85 corrupt variants, 2 in turns, 46 budget runs),
`writecheck` 0 (clock: 19 workloads' times equal, 4 skipped for a cut),
the vectors' lines all passing, StatsProbe's lines equal. `allocfail`
makes 628 runs where it made 379 (its workload's `set retain` is now a
commit after the creation), 51 s. No difference remains in the gate; the
differences that steps 2 and 3 remove do not show in the quick set (step
0's record).

2026-11-09, step 2 (worker s2). The start's checks, and damaged nodes
refused, as 2026.3's Java refuses them (012-18, section 3.1, steps 5 to
9), with Java's exception names and texts: 015-72 in `strans.c` (a
record's content ends at its size field); 015-75 in `strans.c`'s
`st_check_startup_pos` (Db.checkStartupPos: negative, not a multiple of
8, in the first meta block, after the record), called by `starter.c` and
`replay.c`, and in `starter.c` an older topPos and a got-dirty id that
differs, each a `StreamFormatException` where C gave the assert's
`AssertionError`; 019-01 in `meta.c` and `rstream.c` (the version an int,
`beginsAsBlock` over 8 bytes); 019-34 in `rstream.c`'s
`rs_check_last_trans_spos`, in the plan and in `recover.c`, before
anything is written; 019-32 in `snode.c` (a key node's count its size's
exactly, each klong's type, a key klong's pointer; a value node's key,
`sn_is_key`), `nstream.c` (a node position in the first meta block),
`ncoll.c` (`nc_check_pointee_type` on the version read, before an
install, on the handle's object and on a value read; the pointer asserts
as checks), `starter.c` (the memory pointers), `ntable.c` (one type per
id: `nt_register` and `nt_install` return an error) and `dag.c`
(Dag.checkFound's `DbException`). C-only, so that C never reads a node as
another type and never aborts where Java throws: where C cast a followed
node under an assert, a check with Java's exception at that place
(`dag.c` and `topds.c`: a `ClassCastException` with the JVM's text;
`getmany.c`'s asserts and getOne's on a klong's node: an
`AssertionError`, as Java's under `-ea`; `set_node`'s `assertOk` too);
the Dag's own errors go to `opdata`'s new `err`, set where the follower
is set. Java's type checks are in the follows, and do not see the
pointers that a start links (`linkToCanonical`) or that the writer
resolves (`resolvePointers`) by the node id at their position: a damaged
pointer that names another type's node is linked, and Java would throw a
`ClassCastException` at the read; C, which links as Java does
(`ncoll_link_to_canonical_another_type`), refuses it at the cast (found by
reading, not reproduced in Java; for the session). Tests, 11 new, each
failing before its fix (019-32's follows and the Dag's by an abort):
`t_snode.c` (new: `testRefusesBadKlongs`, `testRefusesBadKey`),
`t_records.c` (015-72 on the vectors' records; the node position),
`t_rstream.c` (019-01's version and `beginsAsBlock`,
`testIsIncompleteCreation`'s case; 019-34 on crafted blocks),
`t_sdb.c` (DbTesterRestart's six refusals of 2026.3, on the vectors'
stream), `t_ncoll.c` (the pointee types, one type per id, the bad
pointers), `t_dag.c` (checkFound, the casts); and 2026.2's tests that
took what 2026.3 refuses changed (`records_negative_node_size`,
`rs_meta_blocks`, `meta_begins_as_block`, `sdb_refusals`'s topPos).

The gate against 2026.3, on step 1's landing (`32efc37`): `C BEFORE
COMMIT OK (280 s)`, F53 under a load of about 20 to 28 with other gates;
`unit` 375 tests; `cross quick` 0 differences (23 workloads, 69 crash
cuts, 85 corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0;
`allocfail` 628 runs. Before the rebase, on step 0 alone, the gate's
steps run by hand showed only step 0's negative control (step 1's: the
reclaim vectors, `cross quick`'s 152 differences in the workloads that
reclaim, `clockcheck` on 7 directories) and none of this step's;
`func`, `allocfail` and `examples` passed. `corrupt.sh` against 2026.3,
on step 1's landing: its 144 variants, `CORRUPT OK` (84 refused by both,
with the same exception; 38 started; 22 with a read failing later; 110
s). On step 0 alone, with `HEADERS=2` on bases 501 and 503 (200 variants,
every header byte of the last two records flipped), the same status and
text in all, and 2
differences of the script's own rule that C writes nothing into a
database it refuses: a record's size made smaller by a flip of its byte
0, recovery's walk from the middle of the record zero-fills to a garbage
size (megabytes, new files), and then the start refuses the record's
last byte ("Bad lastByte"). Java does the same (its note), and so did C
before this step (the pre-step build gives the same files and text): not
step 2's, for the session (corrupt.sh's rule, or a check before the fill,
is a matter for both).

2026-11-09, step 3 (worker s3). 012-18, section 3.1, steps 10 and 11,
and 015-31 (D4), in `stream.c`; the stream's bytes do not change. (a) The
switch force, 005-47's lesson for C: `new_file` forces the old last file
before the new file is made, whose name the file system may make durable
at its creation, before any force of the directory; so a power loss
cannot leave a short file before a newer one, which both opens refuse
(`BadDirStateException`, "Bad size of file"). C forced nothing at a
switch; 2026.2's Java forced every append. With it, C's forces are those
of 2026.3's `FileStream` with per-append forcing off: the open for
writing forces the last file and the directory (Java's OPEN, which C's
port of 2026.2 lacked: `durable_length` claimed the open's length
unforced, and a start's cut, `rc_init_from_db` and `sdb.c`, deleted front
files after a decision that a process that died had written and not
forced); `stream_pretruncate` forces the files written since the last
force, and the directory after a new file, before its deletes (CUT;
nothing after reclaim's own force in `cut_if_durable`). `plat_force`
takes the reason, `enum plat_force_why` (Java's `FileStreamIo.Force`),
for the seam. The cost: per open an `F_FULLFSYNC` of the last file and
one of the directory (about 1 and 0.4 ms on F53), per new file one. (b)
015-06: the first file is made by the first write, not by the open; a
read of a stream with no file is Java's (0 bytes at 0, else
`EOFException`, "the stream is empty"); a creation refused at the open
(`BERGDB_LIMIT`) leaves only `bergdb.lock`; a NOMEM in the first file's
making fails the stream at that write, as at any new file. (c) 015-31: a
cut at the stream's length keeps the last file. Tests, each failing with
its fix taken out (in copies of `c/`): `t_stream.c`'s `stream_forces`
(SWITCH, CUT and OPEN in order, by a seam that logs them, as Java's
`ForceLogIo`), `t_append.c`'s `append_dir_first_file`
(`testNoFileUntilFirstAppend`) and `append_dir_cut_at_length`
(`StreamContract`'s cuts at the length, 0 and 3 bytes, and a full last
file), `f_durable.c`'s `durable_refused_creation` (`PubTester`'s
`testRefusedStartAfterOpenCreatesNoStreamFile`); adjusted to 015-06:
`stream_seam`, `append_dir_test0`, `_sizes`, `_mkdirs`, `_failure_runs`,
and `f_reclaim.c`'s `dir_files` (no file yet: first position 0).
`readme.md`, section 9, point 11, and `bergdb.h`, section G, say so.

(d) The power model: `bergdb-power -names now` takes a new name to be
durable at its creation, as a delete is; every image is checked for a
short file before a newer one (`power SHORT`, `short=` in `image.txt`,
exit 4); `-omit switch` leaves the switch force out (Java's
`omitForce`). `power.sh`: `NAMES=now` the default (`dirforce`, Java's and
012-14's model, by choice and for `OMIT=dir`); `OMIT=switch` must find
short files; a torn first write of the creation before any acknowledged
sync, which the new mode makes and both starts refuse alike (005-33's
`DatabaseNotCreatedException`, as Java, which forces a new name before
its first write, would leave it too), is counted, not failed. On a
workload of 500 transactions (a sync every 15, a restart) and on
`reclaim-sync.wl`, C without the switch force passes the old model (no
short-file image) and fails the new one (15 and 48 images; one started
by both: refused, with every acknowledged byte in it); with the switch
force, none in either mode. `power.sh OMIT=switch` on 1102 and 1106:
`POWER CONTROL CAUGHT` (220 and 175 images). `power.sh` on
the tree of steps 0 to 3: C's images in the new mode, Gen 1101 (n=400,
reclaim, 7 deletes), 1102, 1104, 1106 and 1107 (27, 2, 3, 3 and 9
switches): `POWER OK`, 1,405 images started and run on by C and Java
alike, no acknowledged byte lost, no short file, one torn creation (1104;
362 s); Java's images (`JAVAIMG=1`), seeds 17, 19 and 23 (the default)
and 29, 31 and 37 with 15 to 20 images per event: `POWER OK`, 984 images
(107 s). Before step 1 landed, 1101 and Java's 29 and 37 differed only in
the runs after, at reclaim's records (015-54, 015-87), every start, dump
and recovered directory equal. Step 5's long runs take `power.sh` with
the default six workloads and `NAMES=now`.

2026.3's crash contract (014-01, section 7: after a crash the stream is
a prefix of what was appended, at least up to what was forced) against
C's stream: with these forces a power loss leaves a prefix across the
files. Left, for the session: C forces the directory only at a sync or a
cut, so one write of its 10 MB buffer can make several files with no
directory force between them, and a file system that made a later name
durable before an earlier one would leave a gap, which both opens
refuse; Java forces each new file and the directory before the file
takes appends. APFS keeps namespace operations in order, as 014-01's
consequence (c) relies on for bytes, so the case is a theoretical one; if
wanted, the fix is Java's OPEN force at each new file (one directory
force per new file). And within a file C's unforced tail is longer than
Java's (all since the last sync, against one append), so a hole, outside
the contract, has more room, as with Java's per-append forcing off.

The gate against 2026.3, on step 2's landing (`d56d536`), steps 0 to 3
together: `C BEFORE COMMIT OK (335 s)`, F53 under load with other gates;
`unit` 378 tests; `cross quick` 0 differences (23 workloads, 69 crash
cuts, 85 corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0;
`allocfail` 628 runs. On step 0 alone, the gate's steps run by hand
showed step 0's negative control only (the reclaim vectors, `cross
quick`'s 152 differences in the 11 workloads that reclaim, `clockcheck`
on 7 directories), the same counts as step 0's record, and none of this
step's; on step 1's landing, `C BEFORE COMMIT OK (303 s)`. No difference
remains.
