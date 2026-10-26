005-38 report: writes at scale
==============================

2026-10-26, by Claude (Opus 5.5, Claude Code), for Frans Lundberg. On F53,
JDK 27, BergDB at `52d1e1f` (handles merged), all in memory. Only bytes and
node counts were measured, no time.

The answer: the stream's growth per key in 004-02 came from its startup
distance of 10 MB. At a startup distance that suits a large database, 200 to
1000 MB, a put costs 180 to 670 bytes of stream at 10M and 50M keys, and
the cost grows slowly with the database. Writes at scale are not a problem
of the design, as long as the startup distance is set for the database's
size. The node size matters much less; the default, 30, is good.


# 1. The tool

`WriteBench` ([wb/WriteBench.java](wb/WriteBench.java)) loads 24-byte keys
with 8-byte values, 1,000 puts a transaction, node size 30, infinite
retention, no eviction, into a stream that keeps only its tail. Through
`Db.testHooks.transExecuted` it splits every record into value nodes, key
nodes by kind (value leaves, leaves of a key segment that point to the next
segment, inner nodes by height), top nodes, the got-dirty list and the rest,
for every window of puts. With `wb.updates` it then makes that many puts to
random loaded keys: the steady state at a fixed size. Each window also gives
the startup lag (the stream's end minus the startup pos) and D's size (its
distinct nodes and their stream bytes, from `TransSeq`).

It reproduces 004-02: 282, 754 and 1,028 bytes a key after loads of 1M, 10M
and 50M keys at 10 MB, where 004-02 had 282, 754 and 1,028.

The runs: [wb/run1.sh](wb/run1.sh) (loads), [wb/run3.sh](wb/run3.sh) (loads
and updates; `run2.sh` was stopped, its load-only runs at large startup
distances are transients, section 3). Outputs in [wb/out/](wb/out/). The
scripts ran in a scratch clone; the paths in them are relative to it.


# 2. Why a put costs what it costs

A dirty index node is written when the transaction it got dirty in falls
more than the startup distance behind the stream's end (`TransSeq.take`). A
written node with a dirty child stays dirty and is written again a window
later (`DbHelper.handleStillDirtyNodes`). Writes a node absorbs are the puts
that reach it in between. So a put costs about one node write at each level
of the tree with more nodes than the puts in one window, and less at the
levels above. A window is the startup distance in bytes, so the more a put
costs, the fewer puts a window holds: a small startup distance feeds itself.

The marginal cost at the end of a load of 50M keys at 50 MB, 924 bytes a put:

| Part | Writes a put | Bytes a write | Bytes a put |
|---|---|---|---|
| Value node (key, value, overhead) | 1 | 68 | 68 |
| Value leaves | 0.995 | 338 | 336 |
| Segment leaves to the next segment | 0.091 | 399 | 36 |
| Inner nodes, height 1 | 0.904 | 317 | 287 |
| Inner nodes, height 2 | 0.469 | 331 | 155 |
| Got-dirty list | | | 40 |

About half of a written leaf's klongs are TIME klongs, one for each
transaction that touched it: a leaf of 19 klongs holds about 10 keys.

The transaction size does not matter: 755,
754 and 753 bytes a key after a load of 10M keys at 10 MB with 100, 1,000
and 10,000 puts a transaction. Sequential keys cost 90 bytes a key, the
value and little more.


# 3. The cost against the startup distance

Random updates after the load, the whole update phase (10M keys: 30M
updates; 50M keys: 20M updates; at least 5 windows of each startup
distance), bytes of stream a put:

| Keys | 10 MB (load only) | 50 MB | 200 MB | 1000 MB |
|---|---|---|---|---|
| 10M | 920 | 681 | 373 | 180 |
| 50M | 1,219 | 1,013 | 673 | 299 |

(10 MB: the marginal cost at the end of the load, as in 004-02.) A put's
own record is 68 bytes of it. At 1000 MB and 50M keys, a put costs 4.4 times
its record, about 9 times its 32 bytes of key and value. The cost still
grows with the database, from 180 to 299 bytes a put from 10M to 50M keys at
1000 MB: a write more a put each time the leaves outgrow the window by a
level's fanout, the shape of an LSM
tree's write amplification, not a growth without limit.

A load alone does not show this at large startup distances: the index is
written in waves (section 5), and at the end of a load most of it is still
in D. At 1000 MB a load of 10M keys writes no index node at all (70.7 bytes
a key). Steady-state figures need the update phase.


# 4. What a large startup distance costs

D pins its nodes: they cannot be evicted. Over the update phase:

| Run | D, mean | D, largest | Startup lag, mean | Largest |
|---|---|---|---|---|
| 10M keys, 50 MB | 214k nodes, 77 MB | 339k, 124 MB | 66 MB | 131 MB |
| 10M keys, 200 MB | 639k, 236 MB | 905k, 341 MB | 215 MB | 335 MB |
| 10M keys, 1000 MB | 1.63M, 672 MB | 2.27M, 979 MB | 985 MB | 1,002 MB |
| 50M keys, 50 MB | 253k, 89 MB | 432k, 146 MB | 70 MB | 132 MB |
| 50M keys, 200 MB | 889k, 304 MB | 1.36M, 466 MB | 248 MB | 465 MB |
| 50M keys, 1000 MB | 3.37M, 1,163 MB | 4.57M, 1,570 MB | 1,082 MB | 1,647 MB |

D's bytes are the nodes' stream sizes; their heap is larger. The startup
section reaches 1.65 to 2.6 times the startup distance, as in 007-01's
measurement (2.21 times): what 007-03 is about. And startup itself takes
longer: [006-06](../../006-2026-q4/06-fast-restart.md), fast restart, is a
note on that.


# 5. Bursts

At large startup distances the index is not written evenly. Bytes a put,
windows of 1M updates, 10M keys at 1000 MB:

    71 71 70 70 1012 83 79 87 75 85 75 75 83 90 91 111 1055 80 76 74 75 ...

At 200 MB: windows between 131 and 555. At 50M keys and 1000 MB, windows of
2.5M updates: 108, 620, 301, 108, 186, 793, 107, 170. The transactions of a
wave fall behind the startup distance together, and their nodes are written
in a short stretch of records: the write bandwidth, and probably the commit
latency, peak in those windows. `TransSeq.take`'s node limit (4 nodes a put
of the record, and a KB of nodes for each KB of keys and values) spreads a
wave but does not smooth it. 007-03's deadline (step 3, D1) would make it
steeper: it writes the debt beyond 2 × sd at once. Not part of this entry's
question; see Outcome.


# 6. Node size

Measured by a subagent (Opus 5.5) with the same tool in its own copy;
stopped at Frans's request before its 50M runs and its report were done. Its
draft, with placeholders, its tools and outputs, are in
[node-size/](node-size/) (`draft-report.md`). Update phase at 10M keys,
bytes a put:

| Node size | 50 MB | 200 MB | 1000 MB | MEM (bytes a KV) |
|---|---|---|---|---|
| 8 | | | | 253 |
| 14 | 679 | 483 | 219 | 165 |
| 30 | 681 | 373 | 180 | 130 |
| 62 | 771 | 330 | 167 | 120 |

(MEM: Props's memory test, `node-size/out/mem.txt`.) At 50M keys and 200 MB,
node 14's first five windows were 586 to 719 bytes a put, against node 30's
673 for the whole phase. Larger nodes write a little less at large startup
distances and use less heap; at 50 MB node 62 writes the most. Node 30 is
within 8 percent of the best at every distance measured and has the best
gets of the 2015 comparison (CorePerf, the end comments of `Db.java`;
`draft-report.md`, section 10). The default stays.

Two findings on the way, from the draft:

* A database starts only with the node size it was written with. With
  another size, the rerun of the startup section splits differently and
  the start fails with `StreamFormatException: startup error, node ... not
  found`, which looks like a corrupt stream. The size is not in the stream
  (`node-size/RestartNodeSize.java`, `node-size/out/restart-check.txt`).
* Dead versions are written and kept dirty: a leaf that a split replaces
  while dirty is written once more, and an inner dead version is dirty again
  whenever a child it shares with its replacement is dirty
  ([sis-model.md](../../../docs/sis-model.md), 6.2, describes it). The
  writes an exact still-dirty test would save: at most 17 of 232 bytes a put
  at node 30 (1M keys, 50 MB), nearly nothing once the leaves are cold.


# 7. Other key shapes

Random 24-byte keys (`rnd24`, keys that differ in the first segment): 1,058
bytes a key after a load of 10M at 10 MB, 1,166 a put at its end. Each put
makes three single-entry segment nodes for the key's last three segments,
about 160 bytes each, about 480 bytes a put whatever the startup distance.
A cost of how keys are cut into segments, not of the write policy.


# 8. Not done

* Question 3 and 4, time: item 009 answered them for the 10M load on s1
  (009-03, section 7: the slowness was 2026.1's eviction). The loads of 30M
  and 100M keys were not run again.
* Delta writes of nodes (as Berkeley DB Java Edition's BIN-deltas: write a
  node's klongs since its last full write), fewer TIME klongs and an exact
  still-dirty test would cut the bytes further; not needed with a suitable
  startup distance, and each changes the format or the model.
