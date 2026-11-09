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
