# 023-05 P2. The upward unlink at the delete, with a relaxed leftmost klong

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P2 of 023: a delete that leaves a key node with no live klong
unlinks it from its parent, upward, in the deleting transaction (020-30,
section 4.4, option A; 020-30-03, sections 2 and 4). The leftmost child is
handled by relaxing the invariant: the smallest live klong of a node that
is not a segment leaf covers every key below it, as the leftmost pointer of
a B+-tree. This is 023-04's UP with LE-c (2.1, 2.2). So a leftmost klong is
deleted like any other, with no relabel at the delete; a relabel comes back
at a later split of such a child (section 1.3).

Branch `023-p2-relax` in `/Users/f/fl/bench/2026-11-10/p2/clone`, on main
`1901394c` and 023-03's test prototype (`251c4b65`, cherry-picked). Code
places are on the branch.


## 1. The mechanism as built

### 1.1 The delete goes upward

`Dag.setValue` calls `Dag.deleteKey` (Dag.java:965) instead of
`appendDeleteKlong` for a delete. In the deleting transaction, at its time
tt, by the writer:

1. The leaf: if the leaf has no live klong of the key, the delete is a noop,
   as before.
2. The climb, without writing: if the leaf would keep no live key klong
   after the delete, the parent's klong to it, found in the key access path
   as the splits find it (`pd.keyAccessPath`), is to be deleted instead; and
   so on upward while a node would keep no other live klong. It crosses
   segment trees: a segment root left empty deletes its segment's klong in
   the segment leaf above. The emptiness test is one pass over the node's
   klongs with the bitmap (`hasLiveKey`, `keyBits`).
3. The target, the first node that keeps a live klong, takes the delete as
   a leaf did before: a delete bitmap at tt, or in place in the
   transaction's own bitmap, or a split if it is full (`appendDeleteKlong`,
   unchanged). Its smallest klong may be the one deleted (section 1.2).
4. The nodes below the target on the path are left out (`Dag.leaveOut`):
   each loses its klongs of tt (`toPreviousState(tt - 1)`, if it has any)
   and is reported replaced (`keyNodeReplaced`), as a node that a split
   replaces: if it got dirty in the transaction it leaves D at its end
   (`Db.endOfTrans`); its versions before tt serve the earlier times.

Nothing else is written: an emptied node gets no bitmap and no split. A
delete's record is as before (a delete node), so the startup rerun redoes
the climb by the same rule (A1).

Two rules for the special cases:

* **Rule 1, the space root.** A space root that is a segment leaf takes the
  delete (an empty leaf root, as a new database's). A space root that is not
  a segment leaf and would be left with no live klong is left out too, and
  replaced by an empty segment leaf with the time klong of tt
  (`KeyNode.nodeWithTime`), a new super root (`TopDs.newSuperRoot`, as
  time-split-2). Why: an inner node with no live klong cannot route a put
  (`checkFound` refuses it), and an empty leaf is the state every new
  database starts from. A segment root needs no rule: its segment's klong
  goes, and a later put makes a new segment tree (`setNode`, as before).
* **Rule 2, a node the transaction made** (its first klong is the time
  klong of tt, `getFirstTime() == tt`, as `handleFullNode`'s newInTrans).
  It is left out as the others, and it is dropped: in the target, its klong
  of tt is replaced in place by a delete bitmap that deletes nothing more
  than the bitmap before it (`KeyNode.replaceByNoopDelete`,
  KeyNode.java:857); no reader sees klongs of tt (KeyNode's class comment),
  and the size and the other indexes stay, so later bitmaps and reported
  pointer indexes stay right. Then `appendDeleteKlong` deletes the target's
  older klongs of that compare value (the node the dropped one replaced),
  if any. The dropped node loses all its klongs and is reported dropped
  (`keyNodeDropped`, new, which calls `keyNodeReplaced` by default): it
  leaves D at the transaction's end, and its object leaves the node table,
  as an evicted one does (`Cache3.dropNode`, Cache3.java:370; at once in
  the startup rerun). It is never written, and no node in the stream names
  it: the transaction's net effect has no node it made and left unreachable
  (Lean A3). This is 023-04's X5 (a), with the klong neutralized in place
  instead of removed, so no bit of a later bitmap moves. The case is
  common: a delete in a full node splits it, and a later delete of the same
  transaction empties the node the split made. A first version of P2 kept
  such nodes linked (the leaf took the delete): T1 at N = 100,000 then kept
  156 nodes reachable against the twin's 6. A second one did not drop the
  object from the node table: the trace checker's C-H failed with eviction
  (section 6, 4).

### 1.2 The relaxed rule

`KeyNode.searchRoute` (KeyNode.java:841): routing in a node that is not a
segment leaf takes the largest live klong at or below the key at the lookup
time (`searchLte`, as before), or, if there is none, the smallest live klong
(`searchGt(time, -1)`). It is used by puts and deletes (`setValue`,
`setNode`), gets (`getEqNodeInSegment`), `dirtyNodeBound`'s walk and scan
setup (`GetMany.Chain.setup`, both directions). In a tree that only the
rules before P2 made, every node that is not a segment leaf has a live klong
at or below every key routed to it (`Klong.EMPTY_KEY` in its roots), so
searchRoute finds what searchLte finds: the relaxed rule only acts where a
leftmost klong was deleted.

Not `KeyNode.searchFirst`: of several klongs with the smallest compare
value it takes the first, the shadowed one, an older version of the child.
P2's first version used it, and a get after a restart followed a pointer
into the cut stream (T1, N = 1,000). Every other search takes the latest;
searchFirst is used by no production code, only by KeyNodeTester.

### 1.3 Splits of a leftmost child that holds keys below its klong

The relaxed rule routes keys below the leftmost klong K to the leftmost
child, which so holds keys below K. When such a node space-splits, the
second half's first klong S2 can be at or below K: before P2 it was always
above. The parent then got K for the first half and S2 for the second: with
S2 = K the second shadowed the first (a node with live keys unreachable,
found by A2A3Check2 with half deletes), with S2 < K the order was inverted.
The fix, `Dag.relaxedSplitKlongs` (Dag.java:1549), in `spaceSplit`
(space-split-1) and `spaceSplitInPlace`: when S2 <= K, the first half gets
its own smallest klong F (below S2 and below every other live klong of the
parent, so it is the leftmost again), the second half S2, and the parent's
klongs of K go: shadowed by S2 if S2 = K, else deleted by a bitmap in the
same change of the parent (or the parent's split leaves them out, as
appendDeleteKlong's split of a full node does). In a tree that only the
rules before P2 made, S2 > K always, and nothing changes.

### 1.4 dirtyNodeBound

`Dag.dirtyNodeBound` (Dag.java:477), Db's check before the go point
(005-31), now: routes by searchRoute; counts for a delete one klong in every
node of its path, in every segment tree it passes, not only its leaf (any
of them may get the bitmap); one more node for an empty space root; and
three klongs instead of two for a split of a node that holds keys below its
klong or gets one in the transaction (relaxedSplitKlongs). In a tree that
only the rules before P2 made, the last two never apply, so the bound for
puts is today's. A first version counted three klongs for every split and
failed DbTester.testRecordsWithinLimit (975 nodes against a limit of 974).

### 1.5 The record format

`StoredTrans.RECORD_FORMAT` 5 to 6: the bytes of a record are as before, but
the startup reruns deletes by the new rule, so a stream of format 5 is
refused with the message for an older BergDB (023-02, F9 (a) and F10). The
format tests in StoredTrans now refuse 5 as older and 7 as newer.

### 1.6 Root collapse, a separate commit

023-04's RC (2.3), for the space root only. On branch `023-p2-collapse` (a
worktree of the clone, `/Users/f/fl/bench/2026-11-10/p2/rc`), on top of P2:
when the climb reaches the space root, the root is not a segment leaf, and
the delete would leave it with one live klong, the root is left out too,
and its only child becomes the space root, a new super root
(`Dag.collapseRoot`); down further while that node is not a segment leaf
and has one live klong. The child is followed before the root is left out
(the live klong may be one of tt) and without the pointer listener, so Db
does not mark it, as the model does not (no node below it changes).
A2A3Check2 (8 configurations, up to 185 collapses), the trace checker (24
traces, up to 64 collapses a trace, with eviction, reads, restarts and
reclaim) and P2Fuzz pass. Effect: with R forever, "inter" ends at 1 node a
scan and a get (P2 alone 5); with R = 1 s no change in T1 and T2, as
reclaim's internal keys and "/a.txt" lie in two leaves under the root,
which only a merge would join. Segment roots are not collapsed.


## 2. What relied on "a klong is a lower bound of its child"

Each place that reads or makes klongs of nodes that are not segment
leaves, what it relied on, and what P2 does there. "Unchanged for today's
trees" means: in every tree that the rules before P2 can build, the code
gives the same answer and follows the same nodes (023-02, R1).

| Place                              | Relied on                     | In P2                    |
|---|---|---|
| `Dag.setValue`, `setNode`: puts    | a klong at or below the key   | searchRoute; same today  |
| `Dag.checkFound`                   | none: corrupt data            | only if no live klong    |
| `Dag.getEqNodeInSegment`: gets     | searchLte, else not found     | searchRoute; same today  |
| `Dag.dirtyNodeBound`: its walk     | searchLte                     | searchRoute; 1.4         |
| `Chain.setup`, forward             | none at or below: -1, stop    | route and go down        |
| `Chain.setup`, backward            | none at or below: before all  | route and go down        |
| `Chain.setup`, hasDiff             | a node's first or last klong  | unchanged, still right   |
| `Chain.next`                       | the order of siblings only    | unchanged, still right   |
| 021-28's `endKey` (branch)         | a klong bounds its subtree    | one exception, below     |
| space-split-1, also in place       | second's klong above first's  | relaxedSplitKlongs       |
| time splits, `lastVersionGivenDel` | the same compare value        | unchanged, still right   |
| `Klong.EMPTY_KEY` roots            | the empty key is the lowest   | unchanged                |
| reclaim's scan and touch           | GetMany                       | through GetMany          |
| eviction, handles, Cache3          | no key order                  | unchanged                |
| the startup rerun (`DbStarter`)    | Dag.putKv's rules             | reruns P2's rules        |
| `linkD`, Rule R, `canonicalNode`   | node ids, positions           | unchanged                |
| `Audit`, `TraceExport`'s LIVE      | searchEq on every value       | unchanged                |
| `checkPointeeType`                 | the pointee's type            | unchanged; catches more  |
| `KeyNode.searchFirst`              | the first of equal values     | not used: 1.2            |

Notes:

* Scan setup. Before P2, a start key with no klong at or below it in a node
  above the leaf ended the setup there: forward at -1 (the node's first
  key), backward before the node's first key. With the relaxed rule the
  leftmost child may hold keys on both sides of the start key, so the setup
  goes down the child that routing takes, in both directions, and the leaf
  decides, as for any other start key. In today's trees only the forward
  scan from the first key (start key -1) finds no klong at or below, and
  both ways give it the same keys and follow the same nodes. Backward over a
  leftmost child: `searchLt` in the parent finds nothing before the
  smallest klong, which is right, as no child is before it.
* `checkFound` (019-32's check of a damaged node) now fires only for a node
  above the leaf with no live klong at all; no rule makes one (rule 1). A
  segment leaf whose flag a damage changed is still refused when the put
  follows a value pointer as a key node (`checkPointeeType`), as before for
  a key with a klong at or below it.
* 021-28's `endKey` (branch `scan-deleted-keys`, not on main):
  `GetMany.Chain.next` ends a forward scan when the klong it finds is past
  the end, as "a key node's klong is the lower bound of its child". With P2
  that is false for the smallest live klong of a node above the leaf: its
  child may hold keys below it. A merge must skip the check for a klong that
  `next()` finds in a node that is not a segment leaf from the cursor -1
  (the node's first child): its subtree's lower bound is the parent's
  klong, which the check at the parent's level passed. One node a level
  more at most.
* Lookups at earlier times: a delete adds klongs of tt only, so the state
  at every time before tt is as before, and the relaxed rule only acts at
  times when a leftmost klong is deleted.


## 3. Gates and checks

| Check                          | Result                                                    |
|---|---|
| `before-commit.sh`             | BEFORE COMMIT OK (273 s), at `a0af194d`                   |
| `level1.sh`, full              | LEVEL 1 OK; MEM 130 (at most 131), SS 1.51 (at most 1.52) |
| `level2.sh`, quick             | LEVEL 2 OK, trace checker 14 of 14                        |
| `level2.sh`, full              | LEVEL 2 OK, trace checker 70 of 70                        |
| `level4.sh`, full              | LEVEL 4 OK; conformance with eviction 45 of 45, C-H 0     |
| `level3.sh`, full              | LEVEL 3 OK; conformance with reclaim 25 of 25, C-CUT 0    |
| A2A3Check2, 5 more configs     | all checks pass, 40 to 60 % deletes, see below            |
| P2Fuzz (a probe on the branch) | 0 failures in 80 rounds, 480,000 scans                    |
| trace checker, 24 own traces   | TRACECHECK OK 24 of 24, see below                         |
| StreamDigest quick, 11 configs | the four modes agree; every digest differs from main's    |
| root collapse (1.6)            | BEFORE COMMIT OK; A2A3Check2, 24 traces, P2Fuzz pass      |

* A2A3Check2's three level-2 configurations have 20 to 25 % deletes and
  random keys, so few nodes empty. Five more, with 40 to 60 % deletes, node
  sizes 8 and 14, long keys and unsorted transactions, left out 1,421 to
  8,827 nodes each, dropped up to 65 (rule 2) and made up to 542 relaxed
  splits; A2, A3, A5, the marking, TREE, A6' and A-COPY pass in all.
* P2Fuzz (`java/stress/P2Fuzz.java` on the branch, not a gate, 230 lines):
  the Dag alone, 300 transactions a round in phases that fill, drain, put
  keys below the deleted leftmost klongs and drain again; after each
  transaction a get of every key at every time, and 20 scans from random
  start keys (below and above every key too), forward and backward,
  inclusive or not, with or without GetN, at random times, against a model.
  Node sizes 8 and 14, long keys, unsorted transactions; empty roots,
  drops and relaxed splits all occur.
* Traces: TraceExport and the Lean checker (`tracecheck`) on 24 traces of
  my own with 60 to 75 % deletes: plain, long keys, reclaim (retain 1 s),
  eviction (random schedule) with reads and restarts, A6's kind, and a key
  space of 12 keys that empties an inner root 9 to 25 times a trace. All
  OK. The checker's model needs no change: a dropped node is never in a
  record, a no-op bitmap is a delete entry of no compare value ("D 0"), and
  an empty root is a new root of a new top node.
* Two tests changed: StoredTrans's format tests (format 5 refused as older,
  `RECORD_FORMAT + 1` as newer), and A2A3Check2, which now counts a node
  made and dropped by its transaction as transient and checks that no node
  before or after the transaction names it (an A3 violation if one does);
  it also prints P2's counts. CleanupRule (023-03's prototype) prints P2's
  counts and can dump the tree and D.
* StreamDigest (main's class, both jars): in all 11 configurations of its
  quick set the four modes give the same stream, as they must (023-03,
  T8); every digest differs from main's, as the format byte of every record
  is 6, and the lengths of those with deletes differ (`l2-idle-1`: 222,152
  to 222,104 bytes). New expected digests need Frans's approval (023-03,
  6.2).
* Not run: `cross.sh` (the C port does not follow); `night.sh`.


## 4. Measurements against main (023-03)

Counts from CleanupRule, R = 1 s, startup distance 100 kB, node size 30,
no eviction unless named. Main's numbers are 023-03's (section 8) or, where
marked, from runs of main's jar (`86c45146`, the same Java code as
`1901394c`) beside P2's on the same day.

### 4.1 T1, "after", against the twin

| Measure                | Twin  | Main, 1,000 | P2, 1,000 | Main, 100,000 | P2, 100,000 |
|---|---|---|---|---|---|
| M1, MB, most in window | 2.13  | 2.26      | 2.12  | 40.42        | 2.12  |
| M3, ms                 | 1,039 | 1,221     | 1,219 | 5,951        | 1,134 |
| M4                     | 6     | 84        | 6     | 7,902        | 6     |
| M5                     | 35    | 1,047     | 26    | 102,918      | 59    |
| M6, M7                 | 1, 6  | 1, 6      | 1, 6  | 1, 6         | 1, 6  |
| M8, most in window     | 79    | 166       | 89    | 26           | 95    |
| M9, bytes              | 2,840 | 25,968    | 3,336 | 1,729,720    | 3,200 |
| M10, touch visited     | 7     | 85        | 7     | 34,629       | 7     |
| M11, after the probe   | 85    | 156       | 101   | 7,927        | 101   |
| M12, loads after probe | 2     | 163 (run) | 5     | 15,800 (run) | 5     |
| Cuts in the drive      | 11    | 11        | 11    | 0            | 15    |
| h_fill                 |       | 4         | 4     | 6            | 6     |

Pass criteria (023-03, 2.6): bounded a_n = 10 + 4 h_fill (26 at 1,000, 34
at 100,000), strict a_n = 10; a_b = 512 a_n; W = 378,264 bytes.

* N = 1,000: C1 to C3 and C5 to C10 pass with the bounded allowance and
  with the strict one but C9 (101 against 95). C4 passes (26 against 65).
* N = 100,000: all pass with the bounded allowance; strict fails C6 (95
  against 89) and C9 (101 against 95). C4 passes (59 against 65).
* C11 (M14, the deleted keys' value nodes in the kept stream) was not
  measured (023-03's H2 is not built); with 15 cuts and M1 at the twin's,
  the kept stream holds no record of the fill or the deletes.
* N = 1M: M4 6, M6 1, M7 6 (main 78,999, 1, -), but M1 283.6 MB in the
  window (main 319.0) and M8 198: fails C1 and C6. Cause: reclaim, not P2.
  The iteration in progress at the deletes scans every KV live at its tStart,
  1M keys, in steps of 10 to 16 kB, one step a user transaction
  (`Reclaim.transactionCompleted`): about 7,500 steps, more than the drive's
  4,000. With a drive of 16,000 it converges by transaction 6,000: M1 2.56
  MB, M3 1,227 ms, 13 cuts by then, 53 at the end. M8 stays at 150 to 160:
  D at the end holds 144 top nodes and 8 key nodes; the twin's D holds 53
  top nodes and 16 key nodes (section 6, finding 7).

### 4.2 T2's rows at N = 100,000, R = 1 s

| Row            | M1, MB | M3, ms | M4 | M5  | M6 | M7 | M8  | M9, bytes | M11 |
|---|---|---|---|---|---|---|---|---|---|
| twin           | 2.13 | 1,039 | 6  | 35  | 1 | 6  | 79  | 2,840 | 85  |
| after, asc     | 2.12 | 1,134 | 6  | 59  | 1 | 6  | 95  | 3,200 | 101 |
| after, desc    | 2.15 | 1,188 | 6  | 50  | 1 | 6  | 95  | 3,760 | 81  |
| after, random  | 2.14 | 1,089 | 6  | 64  | 1 | 6  | 88  | 3,520 | 84  |
| after, 3 vers. | 2.16 | 1,157 | 6  | 54  | 1 | 6  | 85  | 3,496 | 92  |
| before         | 2.17 | 1,142 | 6  | 61  | 1 | 6  | 106 | 3,840 | 115 |
| around         | 2.17 | 1,054 | 6  | 49  | 1 | 6  | 102 | 3,168 | 91  |
| inter          | 1.84 | 1,126 | 14 | 123 | 5 | 14 | 23  | 3,944 | 29  |
| hashed, random | 2.00 | 1,013 | 9  | 90  | 4 | 9  | 55  | 3,768 | 55  |
| long, N = 10k  | 2.11 | 1,166 | 6  | 29  | 1 | 6  | 83  | 3,400 | 89  |

Main's rows (023-03, 8.2): M1 23.97 to 248.11 MB, M3 4,185 to 5,953 ms, M4
7,901 to 112,765, M11 7,914 to 112,785. P2: every row passes with the
bounded allowance (a_n 30 to 54 by h_fill). Strict: M8 fails in "after,
asc", "after, desc", "before" and "around" (by 6 to 17), M11 in "after,
asc" and "before" (by 6 and 20); C4 (reported only) fails in "inter" and
"hashed", whose live key's own leaf keeps deleted klongs until its time
split. "inter" keeps the live key's tree height (M6 5), also with the root
collapse of section 1.6.

### 4.3 T3's single scans, R forever, right after the deletes

N = 100,000 (long: 10,000). M4: the key nodes a scan of every key follows
(one KV); M7: to the first user key. The twin: 1, 1, 1.

| Shape  | M4, main | M4, P2 | M7, main | M7, P2 | M6 | Deletes' bytes, P2 / main |
|---|---|---|---|---|---|---|
| after  | 7,897   | 1 | 1      | 1 | 1 | 4.74 / 6.78 MB, 0.70    |
| before | 7,897   | 1 | 7,897  | 1 | 1 | 4.74 / 6.78 MB, 0.70    |
| around | 8,039   | 1 | 4,020  | 1 | 1 | 5.30 / 6.89 MB, 0.77    |
| inter  | 7,896   | 5 | 1,182  | 5 | 5 | 4.03 / 5.96 MB, 0.68    |
| hashed | 112,759 | 4 | 4      | 4 | 4 | 97.97 / 108.96 MB, 0.90 |
| long   | 60,787  | 1 | 60,787 | 1 | 1 | 0.99 / 6.37 MB, 0.16    |

With R forever nothing is cut, and the deletes are unlinked at once: every
scan from then on passes only the live keys' paths, at the latest time and
at every time after the deletes. T3's 1,000 rounds were not run; each round
of P2 repeats these single scans (M4 1 to 5), far within T3's bound.
"Deletes' bytes": the stream's growth during the delete phase, from runs
of both jars (retain forever, so no reclaim).

### 4.4 T4, the queue

| Keys, transactions | M4, main | M4, P2 | Head, main | Head, P2 | M3, s, main, P2 | M1, MB, main, P2 |
|---|---|---|---|---|---|---|
| ordered, 100,000   | 11,147   | 117    | 11,033     | 4        | 78.2, 1.22  | 53.2, 1.34  |
| ordered, 1M        | 111,434  | 117    | 111,320    | 4        | 893.1, 1.04 | 557.1, 1.29 |
| hashed, 100,000    | 112,782  | 2,134  | 130        | 5        | 9.9, 1.23   | 112.5, 3.54 |

Cuts: ordered 163 and 1,690 (main 9 and 10), hashed 211 (main 20). M9, the
largest record: 17 to 30 kB at every checkpoint (main up to 20,643 kB). M4
is the same at every checkpoint from 10,000 to 1M: the steady state T4
asks for. Hashed keys have a segment tree of their own each (about 2 key
nodes a live key).

### 4.5 Bytes the deletes write, and the cache

* Bytes: section 4.3, 0.16 to 0.90 of main's for the deletes alone (retain
  forever). With R = 1 s, T1 at N = 100,000: 6.07 MB written during the
  delete phase against main's 10.94 MB (reclaim's work included).
  Emptied nodes are not written at all; the bitmap goes to the target.
* Objects in memory with no eviction, after the deletes (retain forever):
  as main's within 0.1 %, but "hashed", 126,126 against 117,507 (+7 %): the
  targets of hashed deletes are shared upper nodes, whose bitmaps fill them
  and make time splits.
* With eviction at a budget of 1 MB (T1, N = 100,000, the same run for
  both): resident objects after the deletes 322 (main 468), at the end of
  the drive 182 (main 972); after a restart and the probe 101 (main 1,037);
  versions loaded during the deletes 315,943 (main 264,696, +19 %, with
  three reclaim iterations against two).
* After a restart, with retain forever, "long": 6,105 objects resident
  after the start (main 4), and none more loaded for the probe (main
  182,358). P2's delete records are small, so the 100 kB section holds
  about ten times as many deletes as main's, and the rerun reads each one's
  path (finding 8).


## 5. The requirements and tests met

023-02's requirements, as P2 meets them in these runs:

| Req | Meets                                   | How shown                            |
|---|---|---|
| R1  | yes                                     | T6 in every run; P2Fuzz; traces      |
| R2  | for value nodes and records, by the cut | M1 at the twin's, cuts go on         |
| R3  | nodes yes; dead klongs in live nodes no | M4 at the twin's; M5 up to 123       |
| R4  | yes, but top nodes (finding 7)          | M11, eviction runs                   |
| R5  | yes, for nodes                          | M4, M7, M10 at the twin's            |
| R6  | yes, but the iteration over the deletes | T4 1M; T1 1M needs 6,000 (finding 6) |
| R9  | yes, at every time after the delete     | T3's scans 1 to 5 nodes              |
| R10 | as today (height in keys ever put)      | "inter" M6 5                         |
| R11 | yes                                     | M9 3 to 4 kB; climb O(H) a delete    |
| R12 | (a) yes; (b) no (no merge)              | M4; "inter", "hashed"                |
| R13 | yes, at 1,000 and 100,000               | M1                                   |
| R14 | D: top nodes grow (finding 7)           | M8                                   |
| R15 | bounded, more reads a section byte      | finding 8                            |
| R16 | yes: entries of tt only                 | KeyNode's class comment holds        |
| R17 | yes                                     | level1, level2's RestartInvariance   |
| R22 | needs Frans's approval: format 6        | section 1.5                          |
| R23 | (a): format 5 refused                   | StoredTrans's tests                  |
| R24 | the checker accepts P2 unchanged        | section 3                            |
| R25 | not done: the C port must follow        |                                      |
| R27 | yes, but StreamDigest's digests change  | before-commit, levels                |

023-03's tests: T1 passes at N = 1,000 and 100,000 with the bounded
allowance, fails at 1M by reclaim's lag (C1, C6); T2's rows pass at
100,000 with the bounded allowance; T3's single scans are at the twin's or
within its height; T4 passes (ordered and hashed at 100,000, ordered at
1M); T6 found nothing in any run. Strict: fails by up to 17 nodes in M8 and
20 in M11, and C4 in two rows.


## 6. Faults found, and limits

Found and fixed in the prototype:

1. `KeyNode.searchFirst` takes the first of klongs with the same compare
   value, a shadowed one: an older version of the child. Used for the
   relaxed rule, a get after a restart followed a pointer into the cut
   stream. Not used by production code before; P2 uses `searchGt(-1)`.
2. The relaxed rule itself: a leftmost child that holds keys below its
   klong may split with the second half's klong at or below it, and the
   first half then lost its keys (A2A3Check2: made nodes with live keys
   unreachable). Fixed by `relaxedSplitKlongs` (section 1.3). So P2's
   relabel is not gone: it moves from the delete to that split, with a
   delete bitmap in the parent.
3. Keeping a node made by the transaction linked (the first rule 2) left
   such nodes and their ancestors linked: 156 reachable nodes at N =
   100,000. Fixed by dropping them.
4. A dropped node's canonical object stayed in the node table, which the
   Lean model's memory does not allow (C-H failed with eviction). Fixed by
   `Cache3.dropNode`, at the transaction's end and in the rerun.
5. `dirtyNodeBound` at three klongs for every split refused a transaction
   of DbTester.testRecordsWithinLimit (975 nodes, limit 974); now only for
   a node that holds or gets keys below its klong. The test does not stop
   its database when the transaction is refused (a second failure,
   `databasesStopped`).

Limits, not fixed:

6. Reclaim's iteration in progress at a large delete scans every KV live
   at its tStart, one step a user transaction: at 1M keys, about 7,500
   transactions before the cuts resume (T1 at 1M). P2 makes the steps cheap
   (the touch passes no deleted key's node) but not fewer. 023-02, R6.
7. D holds top nodes, and their number grows with the root changes of the
   history: at the end of T1's drive, 53 for the twin, 144 after a fill of
   1M keys. Not P2's: P2 adds a top node only for an empty root. A resource
   that 023-02's list (K1 to K18) does not name.
8. The startup rerun reads the path of each delete in the section. A delete
   record is small now (a delete node, about 60 bytes), so a section holds
   many and the rerun may read H nodes for each: "long" at 10,000, 6,105
   objects resident after a start, read by the rerun, against main's 4.
   Bounded by the section (R15), with a larger constant than before.
9. Dead klongs in nodes that keep live keys stay until the node's time
   split (K3, K7; C4 in "inter" and "hashed"). P2 does not touch them.
10. Root collapse is a separate commit (section 1.6), for the space root
    only. Segment roots are not collapsed, and nodes are not merged (K10,
    K11): with R = 1 s "inter" keeps M6 5 against the twin's 1, as two live
    leaves stay under the root.
11. Under eviction the deletes load 19 % more versions than main's (one
    run; reclaim's work differs too).


## 7. What is left for a production version

* Frans's approval of the format change (023-02, R22; 018-01, section 2)
  and new StreamDigest digests; the C port (022) after the release: the
  climb, the two rules, searchRoute, relaxedSplitKlongs, dropNode, about
  as 020-30-04 estimates for option A plus the split.
* Tests in the repo: P2Fuzz as a level-1 step (or DagFuzz with scans
  and phases), the heavy-delete A2A3Check2 and trace configurations in
  level2.sh and conformance.sh, a DagTester test for each special case
  (empty root, drop, relaxed split in place and not, the root case of
  rule 1 with a newInTrans root).
* The prototype's counters in Dag (`P2_*`, static AtomicLongs) go, or
  become test hooks.
* 021-28's endKey, if merged: the exception of section 2.
* night.sh, StreamDigest's full set and the performance suites (023-03,
  T10): not run.
* Findings 6 to 8 and 10 are open questions (section 8); with P3's reclaim
  work, 6 and 9 may close.


## 8. Questions for Frans

* **Q1. Dropped nodes.** A node that a transaction makes and empties is
  dropped: never written, no node names it, its object leaves the table.
  The Lean model's A3 holds on the records; the Java tier (A2A3Check2)
  now counts such a node as transient. Accept this, or keep A3 strict per
  operation (then such nodes stay linked: 156 nodes at N = 100,000)?
  Recommended: accept.
* **Q2. The relaxed invariant's price.** No relabel at the delete, but a
  relabel at the split of a leftmost child that holds keys below its klong
  (three klongs in the parent instead of two), and every reader of
  "a klong bounds its subtree" must know the exception (021-28's endKey).
  Against P1's relabel at the delete: compare when both are measured.
* **Q3. Root collapse** (section 1.6, on its own branch): take it with P2?
  It helps with R forever ("inter" from 5 nodes to 1), not with R = 1 s,
  where a merge would be needed (023-04, 2.4, MG). Recommended: take it; it
  is small and passes every check here.
* **Q4. Top nodes in D** (finding 7): a resource of their own for 023?
* **Q5. Startup** (finding 8): accept more reads a section byte, or bound
  the deletes a section holds?


## 9. State

2026-11-10 12:40, the prototype's work done for today. Clone
`/Users/f/fl/bench/2026-11-10/p2/clone`, branch `023-p2-relax`, head
`13091f30`: on `2ae7fdd0` (main `1901394c` and 023-03's test prototype),
P2 in `27be3696` and `a0af194d`, and P2Fuzz (a stress file only) in
`13091f30`. At `a0af194d`: before-commit.sh OK, level1.sh, level2.sh,
level3.sh and level4.sh full OK (logs in the clone's `java/build/level*/`).
Root collapse: branch `023-p2-collapse`, head `8cc2bad2` (`4df84775` and
P2Fuzz), in the worktree `/Users/f/fl/bench/2026-11-10/p2/rc`;
before-commit.sh OK at `4df84775`; level scripts not run on it. Run
outputs (CleanupRule, StreamDigest, traces) are in the session's scratchpad
and in the clone's `java/build/p2traces/`, not in the repo. Nothing in the
main tree but this file. Next, for whoever goes on: the questions of
section 8, then section 7's list.
