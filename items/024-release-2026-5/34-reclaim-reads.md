# 024-34. Reclaim reads only what it rewrites (OP8)

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12): on
`main` since `a156fd51`. Q34-1 decided (Frans, 2026-11-13, 09:38):
option (b) in 2026.6, as 026-09, after 026-05; (a) until then.

Frans, 2026-11-12, 12:10, for release 2026.5: OP8 "Do for this release.
This changes the reclaim algorithm, or its implementation at least. Want
this in place for solid internal algos." OP8 (024-05, section 2; 023-05
P8, section 8): a reclaim step reads the value of every live KV of its
scan, also one stored at pCut or later, which it does not rewrite;
`Kvt.spos` tells before the read.

Done by the agent "tidy" of the day's coordinator, in its own clone, on
024-33's head; this item touches `Reclaim.step`, `Reclaim.Stats` and
the maintenance follower's counters (`NodeCollection`), and one sentence
of docs/levels.md, section 6.


## 1. In short

* **Done, the bytes unchanged**: a step reads a KV again at its time (the
  second read) only if the scan found its value before pCut. One found at
  pCut or later, or not yet written, is not rewritten whatever its key
  holds now, so its second read is skipped. The same puts, rows and
  stream bytes (the probe's SHA-256 and StreamDigest: section 4).
* **The second reads halve** at 1M keys (4,208,912 to 2,063,799, 49 %
  left). Without eviction a step loads nothing either way; with a 20 MB
  cache the loads drop only 3.6 % (5,190,675 to 5,005,997): the follower
  caches each version a step, so a second read loads only what changed
  since tStart.
* **What the brief hoped for is not possible with the bytes unchanged.**
  Values are 94 % of a step's loads, and 43 % of all its loads are
  values the scan found at pCut or later (2,140,170 of 5,005,997).
  The scan must still load them: its stop condition counts each KV's
  value length (`key bytes + value length + 100`) against the step's
  16 kB, and a pointer does not carry the length. Not loading them means
  a different measure of a step's size, so other step boundaries, so
  other bytes. Q34-1 asks Frans; section 6 gives the options.
* **Gates** on `b85f0e48`, 2026-11-12: StreamDigest against `main`
  48 of 48 identical (the physical cut too); before-commit OK, level1
  OK, level3 (full; RestartInvariance with reclaim: the stream the same)
  OK, conformance with reclaim OK (30 traces, C-CUT 0 of 318 cuts
  failing), count-gates OK. No expected value of a test changed.


## 2. A step's reads, before

`Reclaim.step` on `main` (`1446a2da`), what it reads and when:

1. **The scan**: a `getMany` at tStart from the row's lastKey, with the
   step's maintenance follower, which reads each version once a step and
   enters nothing in the node table. For each KV it follows the pointer to
   the value node, so it loads the value unless it is in memory, and its
   stop condition counts `key bytes + value length + 100` against the
   step's size (writeSize, at most 16 kB), and the index nodes followed
   against the reserve.
2. **The second read**: for every KV of the scan a `getOne` of its key at
   the step's time (the latest), with the same follower; the value is
   rewritten if it is live and its transaction is before pCut
   (`gd.tpos < pCut`).

The follower caches by position, so the second read loads only what the
scan did not: an index node or a value written since tStart and not in
memory.


## 3. The change

`Reclaim.step` (commit `b85f0e48`), what, when, by whom: in the step's
loop over the scan's KVs, before the second read, a KV whose `Kvt.spos`
(the position of the value node the scan followed, at tStart) is a vpos
(odd: not yet written) or at pCut or later is counted (`kvs`) and passed
over. The writer runs it, inside the external transaction's go point,
under the write lock, as the whole step.

Why the test gives the same rewrites as before: the rewrite test is
`value != null && gd.tpos != NULL && gd.tpos < pCut` on the second read.
The key's value at the step's time is (a) the one the scan saw, whose
transaction is at pCut or later, since a record lies wholly before or
after pCut (pCut is a pStart, the end of an external transaction's
record), or (b) a later one, written after tStart, so in a record after
pStart >= pCut, or not yet written (tpos NULL), or (c) none, a delete.
In each case the test fails, so the KV was never rewritten. A KV found
before pCut is read again as before. The value limit's break uses the
same `kvs`, so the step ends at the same KV.

`t.readTime` is set from the first second read of the step; with the
change that may be a later KV's, at the same time: every second read is
at `Long.MAX_VALUE`, which `dbClock.lookupTime` maps to the time of the
last transaction, constant under the write lock. A step with no second
read has no read keys, so its readTime is not used (`stmCheckConflicts`
reads it for read keys only); it is not stored.

Counters for the measurement (commit `f9c6f6e3`, no change of
behaviour): `MaintenanceFollower.valueLoads()`, and in
`Reclaim.Stats.Iteration` `valueLoads`, `scanValueLoadsAtCut` (values
the scan loaded at pCut or later, from the follower's count between two
of the stop condition's calls) and `gets` (second reads).

docs/levels.md, section 6, says it in one sentence.


## 4. Measurements

A probe (`/Users/f/fl/bench/2026-11-12/tidy/probe/bergdb/core/ReadsProbe.java`,
not committed): 1M keys of 100 bytes put in random order, 100 a
transaction, on a FileStream with the builder's defaults and a test id;
then R = 1 s (100 transactions) and random overwrites, 10 a transaction,
until 3 cuts (179,127 transactions, 5 iterations, 73,745 steps). The
same run on `f9c6f6e3` (before) and `b85f0e48` (after), without eviction
(`noEvict`) and with a 20 MB cache indicator. Counts over all steps:

| Quantity                   | no evict, before | after     | 20 MB, before | after     |
|---|---|---|---|---|
| KVs scanned                | 4,208,912        | 4,208,912 | 4,208,912     | 4,208,912 |
| values rewritten           | 1,542,901        | 1,542,901 | 1,542,901     | 1,542,901 |
| second reads               | 4,208,912        | 2,063,799 | 4,208,912     | 2,063,799 |
| loads                      | 0                | 0         | 5,190,675     | 5,005,997 |
| of them values             | 0                | 0         | 4,902,447     | 4,718,579 |
| scan's value loads >= pCut | 0                | 0         | 2,140,203     | 2,140,170 |
| index node loads           | 0                | 0         | 288,228       | 287,418   |
| load bytes (memory size)   | 0                | 0         | 978,383,444   | 949,253,386 |

The stream after the run, the 9 files of the directory: 744,503,273
bytes and the same SHA-256 prefix `3625575f915cb9f3` in all four runs
(so eviction changes no byte either). The 2.1M second reads saved are
tree walks from the root with the follower's cache: CPU, not I/O.


## 5. The Lean model and conformance

The Lean model has no reads: a reclaim step in it is its puts (the
rewritten values) and its row, which this change keeps as they were, so
the model needs nothing. Conformance with reclaim (`conformance.sh
reclaim`) on `b85f0e48`: 30 of 30 traces checked, C-CUT 0 of 318 CUT
lines failing, C-L 0 of 423,552 FIRST lines, no failed probe.


## 6. Questions for Frans

**Q34-1. Count a step's size without the values it does not rewrite?**
The loads that OP8 meant (023-05 P8, section 8: "halve the step's
reads") are the scan's loads of values at pCut or later: 43 % of a
step's loads at 1M keys with a 20 MB cache, after this change (section 4). The scan loads
them only for their length, which its stop condition adds to the step's
size. The options:

* (a) **As done**: the bytes unchanged, the second reads halved, the
  loads 3.6 % fewer. Nothing more.
* (b) **A keys-only scan, a new step size**: the scan does not follow a
  value pointer whose stream position is at pCut or later (the pointer's
  position is known before the follow; a new option of `GetMany`, for
  reclaim only), and counts such a KV as `key bytes + 100`, its value
  length unknown. Saves those loads (43 % of them here). A step
  then covers more keys when most values are new, so an iteration ends
  sooner in stream growth, and the steps' boundaries change: other
  stream bytes (new StreamDigest digests, a new pin for the C clone), no
  record format. It changes reclaim's pacing, so it needs G3 (the kept
  stream) and ReclaimCost before and after. Fits 024-05's batch of
  stream-byte changes (OP1 and the step's other changes).
* (c) **Read only the length**: for a value at pCut or later, read the
  4 bytes of its length (bytes 24 to 27 of the value node, 024-02)
  instead of the node. The bytes unchanged; still one read a KV, so the
  same count of reads, but no node parsed, checked or kept, and fewer
  bytes read for large values. Its checksum is not checked, so a
  damaged length would change a step's boundary, not the data.

My recommendation: (b), in the batch of stream-byte changes, with G3
and ReclaimCost as its measure; (a) stays in until then.


## 7. State

* Clone `/Users/f/fl/bench/2026-11-12/tidy/clone`, branch
  `024-34-reclaim-reads` from 024-33's head `d6e67fa0`; commits
  `f9c6f6e3` (counters) and `b85f0e48` (the change), head `b85f0e48`.
* Done: the change, the measurement, the gates (section 1). PART 2
  GATED, head `b85f0e48`, 13:26.
* Not done: Q34-1's options (b) or (c), which wait for Frans.
* To continue: the coordinator lands the branch (it contains 024-33's
  commit); for (b), start from section 6 and measure G3 and ReclaimCost
  before and after.

2026-11-13. Status set after the release (coord-1113).
