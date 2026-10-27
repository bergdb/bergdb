005-57 report: startup without rule 4's header reads
=====================================================

2026-10-27, by Claude (Opus 5.5, Claude Code), for Frans Lundberg. The code
read at `167597a`. The prototypes are in scratch clones and their diffs here;
java/ was not changed for the report. Measured on F53 (warm OS cache) and s1
(cold), with 007-05's two databases of 10M keys.

Decided the same day (005-57's entry, "Decided" and "Outcome"): part 1
alone, rule 4 by position, now in the code; part 2 not made; the Lean
theorem for section 2's claim is 005-58.

The answer: rule 4 needs no reads, and neither does the writer, which reads
the same kind of header.

* **Part 1, rule 4.** Every pointer that rule 4 links names a position that
  startup already knows: a vpos, a position in `posToId` (the section's
  versions and the versions just before them, the map of the 2017
  reconciliation), or the linked object's own position (section 2). It is
  Frans's argument: a node that stays dirty is written at least once every
  startup section, so every write of a node after the version that a node
  of D names is in the section.
* **Part 2, the writer.** `resolvePointers` reads a header for each pointer
  without a handle of every node it writes: 1.48 million reads in the first
  300 transactions after a start at 50 MB, today as well. With part 1 alone
  they still happen, and on a cold cache they come from the disk instead of
  from the pages that rule 4 had just read: part 1 alone moves the reads
  into the time after the start. By the same argument, a map of the pinned
  objects by position makes them unnecessary (section 3).
* Prototypes of both parts made the same links and references as today's
  code, which works by id, in every startup and every `resolvePointers` of
  before-commit, level2.sh and level4.sh (full), and on the two databases:
  no difference (section 5).

The two scenarios (section 6), 10M keys and 8-byte values; the medians of
three warm starts on F53, the means of two cold starts on s1:

    Startup               2026.1   current   part 1   parts 1 and 2
    A, 50 MB, warm         7.4 s     7.7 s    6.6 s           6.8 s
    A, 50 MB, cold         240 s     214 s     46 s            45 s
    B, 200 MB, warm       12.9 s    13.2 s   12.1 s          12.5 s
    B, 200 MB, cold        212 s     210 s     51 s            52 s

And the time after a cold start (section 7): on s1, a start at 50 MB and 300
transactions of 1,000 random updates after it took 675 s with the current
code, 534 s with part 1, and 208 s with both parts.

What remains of a cold start is the rerun's loads: one random read for each
node on the rerun's paths that has no version in the section (82,865 at 50
MB, 155,471 at 200 MB), about 30 to 34 s of the 46 to 52 on s1. That is the
next lever (section 8).


# 1. What startup reads, and why rule 4 reads headers

## 1.1 The steps

`DbStarter.doOrdinaryStartup` reads the startup section, the records from
the startup pos to the end, and then:

1. **The section's maps** (`createMaps`): `newById`, each index node with a
   version in the section to its newest version there (Rule R); `posToId`,
   each index node version in the section, and the version before each key
   node version (its `prevPos`), to the node's id; `posMap`, the newest
   versions.
2. **The reconciliation** (`updateStreamPointers`): every pointer of the
   section's newest versions that names an older version of a node with a
   newer version in the section is moved to that version, by `posToId` and
   `newById`. `createMemoryPointers` then links the pointers that name a
   version in `posMap`, by exact position.
3. **The rerun** (`rerunTransactions`): the section's transactions again,
   each at its time. A put walks from the super root to its leaf, and a node
   on the way that has no object is loaded from the stream, with Rule R: one
   random read. D is rebuilt from the ids that the section's records store.
4. **Rule 4** (`linkD`): each pointer of D's nodes that holds no handle and
   names a node with a canonical object gets that node's handle.
5. **The check** (`postStartupCheck`).

Steps 1 and 2 read nothing outside the section. Step 3 loads each node on
the rerun's paths that has no version in the section. Step 4 reads a header
for each pointer it examines: it needs the pointee's id, and a stream
pointer holds a position (`NodeCollection.idOf`; `idByPos` remembers the last
100,000).

## 1.2 The reconciliation of 2016 and 2017, and Rule R

Frans's startup.md, edit of 2016-04-16: "Pointer reconciliation is
required." The 2017 code (the baseline, `195cf88`) has it as step 2: a
`NextMap` from each `prevPos` in the section to the version after it, and
`updateStreamPointers` moves every pointer of the section's newest versions
to the end of that chain. No reads. 011-03, the 2026 analysis of the 2017
startup, found it incomplete: pointers in versions read on demand from
before the section were never moved (G2), and top nodes have no version
chain (`StoredTopNode.getPrevPos()` returns `Spos.NULL`, G3); restart tests
gave wrong historical lookups. Rule R (docs/sis-model.md, 6.2) made it
uniform by node id: whenever a pointer is followed, a newer version in the
section replaces the one it names. That costs no read of its own, as the
load reads the header anyway. Today's step 2 is the 2017 one, with `posToId`
and `newById` in place of `NextMap`, and the same reach.

## 1.3 Rule 4, and why it came with eviction

Rule 4 is not about pointers that are stale at the startup, which step 2
handles. It is about pointers that become stale after it (001-08, M44;
001-01, 8.5, "the gap"):

1. x and y are nodes of D. x's object has a stream pointer to y that names
   y's newest version: right, at the startup.
2. y is taken first, written at a new position, and is then clean; with
   eviction its object can go.
3. x is taken: its pointer still names y's old position, and its record
   names an older version than y's latest.

At the startup, y's new position does not exist yet, so no reconciliation
can fix this. Before eviction (the code of 2026-10-14 to 2026-10-17) the
writer found y when x was written: `resolvePointers` looked y up by id in a
node table that kept every node (M26), reading y's header to learn the id.
The 2017 code did neither: it wrote a stream pointer as it found it
(`Pointer.getSposForStream`). Eviction (item 001, change 1, R8, 2026-10-17)
made the table forget, and rule 4 moved the lookup to the startup: x's
pointer gets y's handle, which follows y's later writes, and since item 009
keeps y's last written position when y is evicted (`Handle.writtenPos`, the
record rule `Handle.serializedRef`). In the Lean model a slot names its
node, so `Mem.linkD` and `HMem.linkD` find the canonical object by id at no
cost; the reads are Java's.

## 1.4 What it costs

The reads of a start outside the section (counted starts; 007-05 has the
same counts):

    10M keys, 8-byte values            50 MB        200 MB
    D, nodes                         176,592       387,117
    Rule 4: pointers examined        871,106     1,292,217
    Rule 4: stream reads             863,609     1,254,124
    Rule 4: links made                 3,634        69,405
    The rerun: loads                  82,865       155,471

Rule 4 links 0.4 and 5.4 percent of the pointers it examines (the
prototype's check, section 5): almost every read finds that the pointee has
no canonical object. (It reads a little less than it examines: `idByPos`
remembers 100,000 positions. A read that crosses a meta block counts as two.)
On s1 a header read costs about 0.23 ms, so rule 4 is about 197 s of a cold
start at 50 MB, and 2.5 GB read from the device.


# 2. Why rule 4 needs no reads

## 2.1 The claim

After the rerun, let x be a node of D and p the position that a pointer of
x's canonical object names, a pointer that holds no handle. If the node y at
p has a canonical object o, then p is one of:

* (a) a vpos, which is y's id;
* (b) a position in `posToId`: a version of y in the section, or the
  version just before y's first version in the section;
* (c) the position of o's version (`o.getSpos()`).

So rule 4 finds o from `posToId` and a map from each canonical object's
position to its handle, both built from what startup has already read. A
pointer whose position is in neither names a node without a canonical
object, and rule 4 leaves it, as it does today after reading the header.

The exception is a top node's pointer to another top node: top node
versions have no `prevPos` (G3), so (b)'s second case is not in `posToId`
for them. The prototype reads the header for a top node's pointer that the
maps do not resolve. On the two databases that was none; in the gates'
small databases, where top nodes are a larger part of D, 2 to 36 percent of
the pointers examined (section 5). A version chain for top nodes, which
Frans planned in 2016 (011-03, G3), would remove those too; it changes the
format.

## 2.2 The argument

It is Frans's: a node that stays dirty is written at least once every
startup section. Made exact, as 001-08 (section 5.4, case 5) uses it:

1. **What x's version names.** The references in x's latest version,
   written at w_x, are lv(y) at w_x, the latest version of y written by
   then, for every pointee y, live or dead; or y's vpos if y had never been
   written. That is the record rule (the model's `mkVersion`; Java's
   `resolvePointers` and `Handle.serializedRef`; INV-SLOT, 001-08, 5.4;
   proved in the model, T-CACHE and T2-C; checked on Java's traces, C-P and
   C-H). x's object at the startup holds those references: it is x's newest
   version in the section cut back to the startup time, or its latest
   version loaded by the rerun or by `canonicalNode`. Steps 2 and 3 move a
   reference only to a version in the section.
2. **Every write of y after w_x is in the section.** If y was written after
   w_x, y was in D then, and so was x: D is closed upward for a live
   pointer, and Rule A couples a dead one (001-08, 5.4, cases 1 to 4). x has
   no version after w_x, so it has been in D since, with the same got-dirty
   index d(x), at or before y's write. x is in D at the end of the run, so
   d(x) is after the startup pos, since the take writes every node whose
   index is at or before it. So y's write is in the section.
3. **If y has a version in the section**, the version x names is one of y's
   versions in the section, or y's last version before the section, which
   is the `prevPos` of y's first version in the section: (b). (y's canonical
   object is its newest version in the section, from `registerSectionNodes`
   or the rerun's `nodeCreated`.)
4. **If y has no version in the section**, no version of y came after w_x
   (by 2), so x names y's latest version. y's canonical object, if any, was
   loaded by the rerun through a pointer of a node on a put's path, which
   names y's latest version by the same steps, or by `canonicalNode` at the
   position stored with y's dirty id, also y's latest version. So o is at p:
   (c).
5. A vpos is y's id: (a).

The pointers that the rerun makes are memory pointers, which hold handles
and are skipped, or copies of slots (a split copies its node's live slots,
A-COPY), which carry the references of the node they come from, a current
node or a node of D, so the steps hold for them too (001-08, 5.4, "Found in
this search").

## 2.3 What it rests on

* **The record rule**, for every version that x's object comes from. BergDB
  has written versions by it since the Level 2 alignment (`resolvePointers`,
  2026-10-14) and, with eviction, since 001's R8 (2026-10-17): release
  2026.1 and later. The 2017 releases wrote a stream pointer as they found
  it, so a stream that they wrote can hold a dead pointer to an older
  version than (b) reaches. For such a pointer rule 4 by position does not
  link where rule 4 by id does. The writer then names the version that Rule
  R gives, which is good for the times the dead pointer is used (lemma M),
  but the record can differ from the model's. Nothing in the stream says
  which BergDB wrote a version: the formats did not change. A question for
  Frans (section 11).
* **The take's invariant**: every node in D at the end of a run has its
  got-dirty index after the startup pos; that is what the startup pos is
  (`TransSeq.take`; 007-01).
* **D closed upward and Rule A** (001-08, 5.4), with TREE and A6', which the
  gates check on every transaction (005-04).

The argument is not a Lean theorem. The prototype checks it on every
startup it makes (section 5).


# 3. The writer reads the same headers (part 2)

## 3.1 What it does, and what it costs

Before a node is written, `NodeCollection.resolvePointers` resolves each of
its pointers to an index node that does not hold its pointee's canonical
object: a pinned pointee (in D, or in the record) gets its handle, so that
the record names the pinned node's position, a new one if it is written
earlier in the same record, and the still-dirty test sees it (Rule A); any
other pointer gets Rule R. For both it needs the pointee's id, and for a
pointer without a handle that is `idOf(pos)`: a header read, unless
`idByPos` holds the position. It is called for every node of every record.

After a start, the take writes D's nodes from the section, and their
pointers are mostly stream pointers. Measured after the start, on an APFS
copy of each database, with N transactions of 1,000 random updates
(StartBench's `st.after`):

    Header reads by resolvePointers   50 MB, 300 tx   200 MB, 800 tx
    2026.1                                1,481,589          320,191
    current                               1,481,589          320,191
    part 1 (rule 4 by position)           1,482,090          322,699
    parts 1 and 2                                 0                0

So rule 4's reads at the startup do not spare the writer's: `idByPos` keeps
100,000 positions, and the writer reads again. Why 50 MB reads more than
200 MB, with fewer transactions, was not looked into; likely, at 50 MB the
take writes the backlog of a section of 2.15 sd at once, before the updates
have followed many of D's pointers, and at 200 MB more of them hold handles
by the time they are written.

With a cold cache it is worse for part 1 alone: today the writer's reads
mostly find the pages that rule 4 read a moment before; without rule 4 they
go to the disk. On F53, from an uncached copy (section 7), the 300
transactions after a start took 13.5 s with the current code and 23.8 s
with part 1; the start and the transactions together, 35.5 s and 34.5 s.
Part 1 alone moves the reads, it does not remove them.

## 3.2 Why the writer needs no reads either

For a pointer that holds no handle, at position p, of a node x that is
being written:

* **The pinned pointee.** If y is pinned and x's pointer does not hold y's
  handle, then x is in D and is written no later than y (INV-SLOT's second
  half, 001-08, 5.4): y has not been written since x's pointer got its
  reference, except earlier in the record being written. So p is y's last
  written position before this record, and a map of the pinned objects by
  that position finds y.
* **Rule R.** It changes p only if y has a newer version in the section,
  and then p is in `posToId`, by section 2's steps for a node that is
  current or in D. (After part 1 even that does not happen: such a pointer
  of a node of D was linked at the startup, and a node loaded later names
  y's latest version. The prototype keeps the lookup; it costs no read.)

So `resolvePointers` needs `posToId`, kept for the process as `newById` is
(Rule R stays for the process), and `pinnedByPos`: each pinned object by
its last written position. The pinned set changes in four places, all in
the writer under the write lock: a node gets dirty (`Db.makeDirtyIfNeeded`,
and `DbStarter` for D), a replaced node is cleaned (`Db.endOfTrans`), and a
record's nodes are written (`Db.store`: each leaves the map at its old
position after the record is appended, and a node that is still dirty, Rule
A, comes back at its new one).

The cost is memory: `pinnedByPos` has an entry for each node of D (387,117
at 200 MB), and `posToId` kept doubles what Rule R keeps today. As
`HashMap<Long, ...>` that is tens of MB at 200 MB; a map of primitive longs
would be a quarter of that. `posToId` could also be dropped: by the second
point it serves only a pointer that rule 4 could not link because its
pointee was evicted during the startup.


# 4. The prototypes

Both on `167597a`, in scratch clones:

* **Part 1**, rule 4 by position: [prototype.diff](prototype.diff).
  `DbStarter.linkD` builds `byPos`, the live handle of each canonical object
  by its position (one pass over the node table's handles), and calls
  `NodeCollection.linkToCanonicalByPosition` for each node of D with
  `posToId`. That method is `linkToCanonical` with the id from `posToId`
  (or the vpos itself), else the handle from `byPos`, in place of `idOf`; a
  top node's pointer that neither resolves reads the header, as today.
* **Parts 1 and 2**: [prototype-2.diff](prototype-2.diff), part 1 and
  `resolvePointers` by position: `posToId` kept (`setSectionIds`),
  `pinnedByPos` with its four places (`pinned`, `unpinned`), and
  `resolvePointers` with the id from `posToId` or the vpos, else the pinned
  handle from `pinnedByPos`, else nothing.

For the investigation each has a check: with assertions on (every test) or
`-Dbergdb.rule4.check=true` / `-Dbergdb.resolve.check=true`, each pointer is
also resolved by id, with the read, and a difference is counted, printed,
and fails an assertion. `-Dbergdb.rule4.byId=true` and
`-Dbergdb.resolve.byId=true` give today's code. A JVM with the checks on
prints their sums at exit. One unit test (`testResolvePointers`) marks a
node dirty by hand and needed a `pinned` call. The counters and properties
are not meant for java/ (section 10).

The tool, [StartBench.java](StartBench.java), is 007-05's StartupBench's
start mode for the three jars (what differs between them is read by
reflection), with the reads counted by where they come from, and with
`st.after=N`, N transactions of 1,000 random updates after the start. The
runs: [f53-57.sh](f53-57.sh), [s1-57.sh](s1-57.sh), [s1-57b.sh](s1-57b.sh);
[analyze.py](analyze.py) makes the tables from [out/](out/). A start writes
nothing to the database (checked on F53: the listing and the last file's
SHA-1 are the same after a start), so all versions start the same
databases; the runs with updates use copies.


# 5. Checked

With assertions on, every startup and every `resolvePointers` of the tests
ran both ways, by position and by id:

    Gate (parts 1 and 2)   Startups   Rule 4: pointers   Linked      Diff.   resolvePointers: pointers   Pinned   Diff.
    before-commit               464             14,596       2,461       0                      76,448      106       0
    level2.sh, full          11,951          1,827,324   1,114,127       0                   3,069,771    3,398       0
    level4.sh, full          14,027            456,896      17,356       0                  14,481,150   17,393       0

"Linked": the pointers that rule 4 by position linked, the same as rule 4
by id linked. "Pinned": the pointers that `resolvePointers` resolved to a
pinned pointee, by `pinnedByPos` or by the section's ids, the same as by
id. Rule 4 read the header for a top node's pointer 5,189, 30,918 and
30,478 times in the three (section 2.1). The gates passed: BEFORE COMMIT
OK, LEVEL 2 OK, LEVEL 4 OK (conformance: C-P and C-H 0 of 10,321
transactions fail). Part 1 alone passed before-commit with its check too.
The sums: [out/checks-before-commit.txt](out/checks-before-commit.txt),
[out/checks-level2.txt](out/checks-level2.txt),
[out/checks-level4.txt](out/checks-level4.txt).

On the two databases (part 1 with `-Dbergdb.rule4.check=true`, on F53 and
again on s1, with the same counts):

    Database   Pointers examined   Linked by position   Linked by id   Differences   Header reads
    50 MB                871,106                3,634          3,634             0              0
    200 MB             1,292,217               69,405         69,405             0              0

level2.sh has RestartStress (startup distances from 100 bytes, node sizes 8
to 62, deletes, up to 26 restarts a round) and RestartInvariance (a restart
after every transaction gives the stream of the run without restarts, byte
for byte); level4.sh has EvictionInvariance and RestartInvariance with
eviction schedules, CrashTest, ReclaimStress, and conformance with the Lean
model (C-P, C-H) after a restart. A missed link would show there as other
records (001-08, M44: "without it change 1 gave other records after
restarts").


# 6. The two scenarios: startup time

Both are 007-05's databases, made by StartupBench (key24 keys in random
order, 1,000 puts a transaction, then random updates; node size 30; the
make closes without writing D):

* **Scenario A**: 10M keys, 8-byte values, startup distance 50 MB (2M
  updates): stream 5.3 GB, a section of 108 MB (2.15 sd), 109 transactions
  rerun, D 176,592 nodes.
* **Scenario B**: 10M keys, 8-byte values, startup distance 200 MB (3M
  updates): stream 2.9 GB, a section of 201 MB (1.00 sd), 307 transactions
  rerun, D 387,117 nodes.

The versions: release 2026.1 (`releases/2026.1/bergdb-2026.1.jar`, before
handles), the current code (`167597a`), part 1, and parts 1 and 2. Warm: F53,
the OS cache warm (a start first), JDK 27, ZGC, a 16 GB heap, a cache budget
of 4 GB, three starts of each version in turn, the median. Cold: s1, the OS
cache dropped before each start, a 2.5 GB heap, a budget of 600 MB, two
starts of each version in turn.

Scenario A, 10M keys, 50 MB:

    Version            Warm, F53 (median)   Warm, the 3 starts    Cold, s1 (2 starts)   Reads
    2026.1                         7.39 s   7.29 7.39 7.47 s      254.2 224.8 s       1,113,136
    current                        7.67 s   7.44 7.67 7.79 s      208.8 219.3 s       1,113,136
    part 1                         6.55 s   6.52 6.55 6.91 s       44.9  47.0 s         249,527
    parts 1 and 2                  6.81 s   6.81 6.83 6.76 s       46.8  44.0 s         249,527

Scenario B, 10M keys, 200 MB:

    Version            Warm, F53 (median)   Warm, the 3 starts    Cold, s1 (2 starts)   Reads
    2026.1                        12.91 s   12.91 12.99 12.54 s   220.4 202.8 s       1,722,436
    current                       13.24 s   13.23 13.36 13.24 s   200.4 218.9 s       1,722,436
    part 1                        12.05 s   11.77 12.05 12.46 s    51.3  51.2 s         468,312
    parts 1 and 2                 12.51 s   12.07 12.59 12.51 s    53.9  50.3 s         468,312

Warm, part 1 saves 1.1 to 1.2 s against the current code (rule 4's CPU and
cached reads; 9 to 15 percent), and part 2 gives back a few tenths of that
at the startup (it fills the pinned map and copies `posToId`): 0.7 to 0.9 s
saved with both. The rest of a warm start is the rerun and the section's
nodes (007-05). Cold, rule 4 was most of the start, and what is left is the
rerun's loads.

Where a cold start's time goes on s1 (the counted starts; a counted start
pays about 6 µs a read for its stack trace, which is in "the rest"):

    Scenario A, 50 MB   Start     Rule 4's reads       The rerun's loads   The rest   From the device
    2026.1              233.8 s   863,609, 177.3 s     82,866, 28.8 s      27.5 s     2.96 GB
    current             255.2 s   863,609, 196.6 s     82,866, 30.0 s      28.2 s     2.98 GB
    part 1               50.5 s   none                 82,866, 34.2 s      15.9 s     0.48 GB

    Scenario B, 200 MB  Start     Rule 4's reads       The rerun's loads   The rest   From the device
    2026.1              260.8 s   1,254,124, 193.2 s   155,463, 24.6 s     42.3 s     3.33 GB
    current             268.7 s   1,254,124, 194.5 s   155,463, 29.6 s     43.8 s     3.11 GB
    part 1               61.1 s   none                 155,463, 30.1 s     30.2 s     0.58 GB

(The loads are counted by their first read, the node's header, which goes
to the device; the node's own two reads then come from the cache.)


# 7. After the start

N transactions of 1,000 random updates after the start (300 at 50 MB and
800 at 200 MB: enough for the take to write D's nodes from the section), on
an APFS copy of the database. The copy's pages are not in the OS cache, so
on F53 this is a start from the SSD, not warm. Timed (`st.phases=0`):

    Scenario A, 50 MB    Start     300 transactions   Together   Reads after the start
    2026.1               21.9 s    13.6 s             35.5 s     2,875,782
    current              22.0 s    13.5 s             35.5 s     2,583,505
    part 1               10.7 s    23.8 s             34.5 s     2,584,006
    parts 1 and 2        11.4 s    13.6 s             25.0 s     1,101,916

    Scenario B, 200 MB   Start     800 transactions   Together   Reads after the start
    2026.1               22.0 s    15.7 s             37.7 s     3,223,977
    current              21.9 s    14.4 s             36.3 s     2,478,696
    part 1               15.2 s    19.1 s             34.3 s     2,481,204
    parts 1 and 2        15.4 s    16.1 s             31.6 s     2,158,505

The reads after the start are the updates' loads (three stream reads a
load, one from the device) and `resolvePointers`' header reads (section
3.1); with part 2 only the loads are left. 2026.1 loads more (about 1.39
million reads against 1.10 at 50 MB), which is item 009's (handles), not
this.

On s1, cold, scenario A (a copy of the database, the cache dropped, a start
and 300 transactions; s1-57b.sh):

    Scenario A, 50 MB    Start     300 transactions   Together   First 150 transactions
    current              217.4 s   457.9 s            675.3 s    333.1 s
    part 1                48.6 s   485.8 s            534.4 s    354.8 s
    parts 1 and 2         48.1 s   159.9 s            207.9 s     91.2 s

The same reads as on F53 (2,583,505, 2,584,006 and 1,101,916). On s1 the
writer's 1.48 million header reads cost 300 to 330 s, whether rule 4 read
the same headers at the startup or not: s1's OS cache (about 1 GB beside
the 2.5 GB heap) keeps little of what rule 4 brought in. With both parts
the transactions after a cold start are three times as fast: a start and
the first 300,000 updates take three and a half minutes, not eleven.


# 8. What is left of a cold start

With the change, a cold start on s1 at 10M keys and 50 MB is about 46 s:
the rerun's 82,866 loads, 0.34 to 0.41 ms each (a header read from the
device, then the node from the cache), and 10 to 14 s of CPU, about twice
F53's. The
loads are those of the nodes on the rerun's paths that have no version in
the section; the section bounds them (a node per level of the tree for each
put rerun, at most), so with T3 and the deadline the startup is bounded,
now by a number that is small enough to measure in seconds. To go below
that:

* **Read the loads several at a time.** s1's disk takes 0.2 to 0.4 ms a read
  and serves several at once (four readers overlapped their reads 4.3 to 6
  times, 004-02, 10.6); the rerun reads one at a time. The rerun could
  first collect the positions it will load (the paths of the section's puts,
  level by level) and read them in parallel or in position order. 007-03's
  step 6, option A.
* **Write D at a clean close.** A planned restart then reruns nothing. Not
  for a crash.
* **The header read before each load** (`followStreamPointer`, step 1) is
  the device read; the node read after it hits the cache. Reading the node
  at once would save the extra calls, not device time.

At 10M keys and 50 MB that is about 34 s of the 46. Not investigated here.


# 9. The Lean model

The model needs no change. Its slots name nodes, so its rule 4 (`Mem.linkD`,
`HMem.linkD`) and its writer's resolution (`mkVersion`, the record rule) find
canonical objects by id without reads; the reads exist because Java's stream
pointer holds a position. The change must compute the same links and
references as the model, and the gates check that: conformance (C-P, C-H)
after a restart, RestartInvariance and EvictionInvariance on the stream's
bytes, and the check of section 4 under assertions.

What a proof would add: section 2's claim as a theorem of the model, that
on every state its startup reaches, a stream slot of a pinned object whose
node has a canonical object names a record in the section, the record of
the node's version before its first in the section, or the record its
canonical object came from; and section 3.2's for the writer. The model has
the records and `newest`, and `sectionPos` gives canonical objects their
positions (Evict.lean); "the version before" would be new. M, at a guess.
Not needed for the change, which the checker covers; it would make the
argument a theorem.


# 10. The change, for java/

1. `DbStarter.linkD` and `NodeCollection.linkToCanonical` by position, as in
   prototype.diff, without the counters and properties; the top node
   fallback.
2. `resolvePointers` by position, with `pinnedByPos` and its four places, as
   in prototype-2.diff; `posToId` kept with `newById`, or dropped (3.2);
   maps of primitive longs if the heap matters (it is counted in MEM only
   while D is large).
3. The check stays, as a test-only check like the audit: with assertions
   on, rule 4 and `resolvePointers` also run by id, and a difference fails.
   Every test's restart then checks the argument; the tests read more.
4. Tests: a node of D whose pointer names (a) a vpos, (b) a section version
   and a `prevPos`, (c) a loaded object's position, a top node's pointer,
   and a position that names no canonical object; `resolvePointers` with a
   pinned pointee by position, written in the same record before and after,
   and Rule A; the existing `testLinkToCanonical` and `testResolvePointers`
   adapted.
5. Documents: docs/levels.md, section 5 (what startup reads) and the cold
   startup figures; 007-03, step 6; the comments of `DbStarter` and
   `NodeCollection`.
6. Gates: before-commit, level2.sh, level4.sh (full), StreamDigest as
   2026.1's (no record changes), and this item's two scenarios again. Since
   005-50 (`bf19075`, the node size in the meta block), a head build refuses
   the databases made before it, so the scenarios' databases are made again
   first (StartupBench's make, 007-05; release 2026.1 starts the new ones).

Size: S for part 1, M for part 2 (the writer's pinned set), with tests and
documents.


# 11. Questions for Frans

1. Make the change, both parts (section 10)? Part 1 alone gives the faster
   start but moves its reads into the time after it, on a cold cache.
2. Streams written by the 2017 releases (2.3): accept that rule 4 by
   position may miss a link for a dead pointer in a version they wrote, or
   keep rule 4 by id, with the reads, for such streams (nothing marks them
   today)?
3. The rerun's loads (section 8), the rest of a cold start: next, as
   007-03's step 6, option A?
4. A Lean theorem for the claim (section 9)?
