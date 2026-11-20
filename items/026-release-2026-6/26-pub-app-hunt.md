# 026-26. An independent hunt with Pub API apps

Created 2026-11-20 by Frans Lundberg. Status: done (2026-11-20): no
database fault; one build-script finding, S4-B1, fixed as 028-41.

An independent hunt, with apps designed apart from the earlier ones
(024-26, 026-13): eight user applications on the Pub API alone, written
from the README, the Pub API's overview (`bergdb.pub`'s package page) and
its Javadoc, each with an oracle of its own; the earlier apps' logic was
not read. They ran on the release jar of `main` at `bdf7c1ba`, on
2026-11-20 from 20:11 to 20:45; release 2026.5 (`3611130c`) was the
comparison for the one finding. Nothing in BergDB's code was changed by
the hunt.

Findings are named by severity: S1 data lost or wrong, S2 a database that
fails or cannot start, S3 a call refused wrongly, S4 minor or
documentation.


## 1. In short

* **No database fault** (S1 to S3: none). 31 runs of eight apps, all OK,
  with 160 forced stops of a child JVM, each followed by a check of the
  whole recovered state.
* **One S4 finding outside the database, S4-B1**: `java/build.sh` fails
  falsely when `JAVA_TOOL_OPTIONS` is set, on `main` and on 2026.5
  (section 4). Fixed as 028-41; not a released bug of the database, so not
  in 033.
* **The apps are maintained** in `java/stress/apps/d1-*` to `d8-*`, run by
  `java/stress/apps.sh` in its three modes (section 5).


## 2. The applications

All use the Pub API only, no Core API call; each exits non-zero on a
wrong result.

* **D1Ledger** (d1). Four writer threads transfer between twelve accounts,
  two readers check saved views; a replay of the accepted transfers in
  commit order checks every balance and the journal of transaction times,
  the views again after a restart.
* **D2ScanHistory** (d2). Each key's versions modelled: gets and scans both
  ways at the latest and older times, odd and supplementary characters,
  nested directories; a moved clock, a retain duration of 3 s and
  `maintain()` drive reclaim; a time just before the first available one
  must be refused.
* **D3ObjectIndex** (d3). Objects with compound indexes of long, double,
  string, bytes and nested fields (NaN, infinities, negative zero, UTF-8
  ties), deleted and made again with other fields, pinned builders, three
  restarts; with `retain`, large values, a moved clock and reclaim.
* **D4CrashBatches** (d4). A child JVM writes batches (values, deletes, an
  audit record, a marker and two mirrors in one transaction) and is
  stopped by force before, during or after a write or a sync; each
  recovery must be a whole prefix, at least to the last acknowledged sync
  and at most to the last batch allowed to start.
* **D5ContractEdges** (d5). The limits taken at the limit and refused one
  beyond (keys of 109 to 113 bytes, values of 8 MiB, 500 operations,
  32 MiB, index levels of 111 bytes), each refusal changing nothing;
  spoiled builders, nesting at 16 and 17 levels, connection ownership;
  124 refusals a run.
* **D6SchemaValues** (d6). 539 stored values read through twelve field
  types against an oracle of the conversion rules (extremes, NaN,
  fractional and huge text, invalid UTF-8), before and after a restart;
  32,767 fields and the refusal of the next.
* **D7RwConflicts** (d7). RW conflicts forced with latches: a read after
  another connection's commit, inserts after an absent read, write skew;
  retries, closed environments, exceptions in constructors, an action that
  returns after `stop()`.
* **D8OnlineIndex** (d8). Index builds beside a writer: cancelled, renamed
  with another field, joined by the next start; a build that must fail on
  an object of an old format, and succeed once it is replaced.


## 3. The runs

31 runs, every one with exit 0 and an OK line; none reached the runner's
guard of 20 or 25 minutes. Each JVM had a heap cap (512 MiB, 768 MiB for
D5, 256 MiB for D4's child), at most four JVMs at once. The arguments
after the data directory, and what each checked:

* D1Ledger, 4 runs (101 3 80; 211 8 300; 307 6 400; 601 4 250): 960 to
  9,600 commits, 30 to 268 views.
* D2ScanHistory, 4 runs (101 900; 211 3000; 307 6000; 601 1800): 900 to
  6,000 transactions, 3 to 17 cuts seen.
* D3ObjectIndex, 6 runs (101 360; 211 1800; 307 2400 retain; 401 4000
  retain; 601 1500 retain; 607 1000): 2,656 to 8,688 scans, up to 22
  cuts. Runs 101 and 211 had four index definitions without retention,
  307 added retention, 401 and the last two a fifth index of eight levels.
* D4CrashBatches, 4 runs (101 10; 211 40; 307 80; 601 30): 160 forced
  stops (SIGKILL), every recovery within its bounds; the last at batch
  409, 1,366, 2,896 and 1,013.
* D5ContractEdges, 4 runs (seeds 101, 211, 307, 601): 124 refusals and
  15,519 assertions each.
* D6SchemaValues, 3 runs (seeds 101, 211, 601): 12,936 conversions and
  47,099 assertions each.
* D7RwConflicts, 3 runs (101 80; 211 200; 601 120): 80 to 200 write-skew
  pairs, 240 to 600 retries.
* D8OnlineIndex, 3 runs (101 4 1600; 211 6 4000; 601 6 3000): 196 to 286
  scans, up to 532,446 rows checked.

Nine runs (seeds 601 and 607) used the final sources, as landed, on a
rebuilt jar whose entries are the first jar's.

Not covered: power loss, damaged storage, replication, Android, other
systems; the 56 KiB limit of a transaction's keys was not driven to its
exact boundary; the checks of older times read sampled whole views, not
every time.


## 4. S4-B1: the jdeps check and the JVM's "Picked up" line

With `JAVA_TOOL_OPTIONS=-Xmx1g`, to cap the heap of every JVM of a build,
`sh java/build.sh` exits 1 with "BUILD FAILED: build/bergdb-release.jar:
it uses classes that it does not hold (jdeps --missing-deps)". The file
that the check reads, `build/release-jar/jdeps.txt`, holds only the JVM's
line `Picked up JAVA_TOOL_OPTIONS: -Xmx1g`: check 2 takes both outputs of
jdeps and fails on any line. The same build passes with the cap given to
each tool directly (`JAVAC='javac -J-Xmx1g'` and so on). Reproduced 3
times of 3 on `bdf7c1ba` and on 2026.5.

A fault of the build script, not of the database or of a released jar.
Registered and fixed as 028-41 (2026-11-20): the check drops the JVM's
"Picked up" lines before it reads the file.


## 5. Landed in the repository

On the branch `026-26-app-hunt` (2026-11-20, from `main` at `591251a5`):

* The eight apps in `java/stress/apps/d1-ledger/` to `d8-online-index/`,
  as the hunt left them but for one change: D5 and D6 import
  `bergdb.pub.Limits` by name, as `a3-limits/Limits.java` (024-26), a
  class of the same unnamed package, hides the one of `bergdb.pub.*` when
  `apps.sh` compiles all the apps together. The hunt's reproduction of
  S4-B1, `BuildOptionsRepro.java`, was not landed: it asserts that the
  build fails; 028-41 has the command.
* `java/stress/apps.sh`: its header describes d1 to d8; quick runs each
  app once at the final runs' seeds (D3 twice, D4 with 10 kills), soak the
  larger runs but D4's at new seeds per round, kill D4 with 60 kills.
* `java/build.sh`: 028-41's fix.

Runs on the branch, on F53 at `nice -n 10` beside a running `week.sh`
(2026-11-20):

* `java/stress/apps.sh quick`: APPS OK in 4 minutes 6 seconds, of which
  d1 to d8 took 27 seconds.
* The d-apps' lines of soak 1 and kill 1, run alone with CC on
  (`BERGDB_TRANSCHECK`, as `week.sh` runs soak and kill): all OK, no CC
  failure, 40,115 commits checked; soak's part 35 seconds, kill's (D4, 60
  kills) 93 seconds.

* `java/before-commit.sh`: BEFORE COMMIT OK (63 s).

So the apps add about 30 seconds to quick, 35 to soak and 95 to kill,
about 2.5 minutes to `week.sh`.


Log
---

2026-11-20. The hunt ran from 20:11 to 20:45 on `bdf7c1ba` and wrote its
report at 20:51.

2026-11-20. Written and landed by an agent of coord-1120 on the branch
`026-26-app-hunt`, with 028-41 (S4-B1, fixed).
