# 023-08 Review B of 023-07

Written 2026-11-10, 14:50 to 15:36, from a clone at `main`'s `e45fd4c1`
with the prototype branches. What was done: 023-07 read in full against
023-01 to 023-06 and the reports P4 to P8; the code read on the heads
023-07 names (`git show` of the branches, nothing checked out); one test
run, UnlinkFuzz on P5's head `71e386de`, built in a scratch worktree: 40
rounds of shape `random` and 40 of `long`, 0 failures, 9,080 unlinks, 686
collapses, 123 nodes taken back by the climb; and one probe, P8's
iteration under a growing random-key workload (2.6, `probe/`). Not run:
level scripts, the conformance, any combination of branches, T10.


## 1. Verdict

**Accept the core with changes; P8 not as built.** The mechanisms are
sound as read: no counterexample against lookups at earlier times, held
readers, the cut, the rerun, crashes or eviction (section 2).

1. **P8 breaks reclaim's liveness under random growth** (2.6): a step
   scans at most 16 kB a transaction; measured on its head, 100 kB of
   random puts a transaction gives no cut at all, 20 kB a lag that grows
   without bound. Fix the step's limit and measure, or 2026.4 without P8.
2. **X5 (c) and RC's exit for a root of tt are dead code** (2.2, 2.4): a
   transaction never puts and deletes one key. Replace them by a `Bug`.
3. **K4** misses RC's chain (2.5); test the bound against counted nodes.
4. **Gates on the combination** before the release: level1 to level4
   full, StreamDigest, T10, a cold start at 50 MB, the ratchet test, C11.
5. **The full set** adds nothing needed for correctness or the rule (4.3):
   merges in a format 7 later; (a) later, no refusal; (b') not as
   proposed; the queue off; `maintain()` in 2026.5.


## 2. Soundness

### 2.1 What was checked and how

| Part            | How                                                                 |
|---|---|
| K1 UP, take-back | code read: `deleteUpward`, `unlink`, `takeBack`, `retarget`, rerun; fuzz run |
| K2 LE-b         | code read: `firstAndSecond`, the four split calls, every reader's bound       |
| K3 RC           | code read: `collapseRoot`, `takeBackRoot`, the quiet descent                 |
| K4 bound        | code read: `dirtyNodeBound`, `mergeBound`, `checkDirtyNodes`; an estimate    |
| K5 P8           | code read: `transactionCompleted`, `step`, `pastEnd`, the table; argument    |
| K6 dead hand    | code read: `afterTransaction`, `deadStep`, `detachable`, `Handle.usable`     |
| K7 SE, K8       | code read in part (`StoredTrans.formatRefused`); 021-28 trusted              |
| F2 (a), F3 (b') | code read: `writeAheadTops`, `rerunTransaction`, `ruleBEntry`; argument     |
| F1 merges       | not read beyond the take-back's interaction; P5's gates trusted              |
| F4, F5          | read against the dead hand (F4); not read (F5)                               |

### 2.2 K1, the upward unlink and the take-back

* **A taken-back node is named by no klong, live or deleted.** Argument,
  checked in the code (`Dag.takeBack`, `retarget`, P5 `Dag.java:1447`,
  `:1946`): a node S made by tt is named only by klongs of tt, which every
  holder appends behind its time klong of tt. At most one live klong names
  S, in its path parent (`emptyKeyNext` copies pointer j to the empty key
  and then deletes c_j; `firstAndSecond`'s shadow pair names two different
  nodes; `replaceRoot` appends one klong and unlinks the old root). A
  deleted klong of tt naming S can exist only in that parent: a split of
  an older holder builds `last` from live klongs and `toPreviousState`
  drops tt's klongs; a split in place sets the content from `first` and
  `last`; `unlink` drops tt's klongs; a taken-back holder is dropped.
  `retarget` scans the parent behind its one time klong of tt, deleted
  klongs included. The repointed klong goes in every case: the parent is
  taken back or unlinked, or gets `appendDeleteKlong(c)`, or
  `emptyKeyNext` overwrites that klong in place. Fault 6's fix is in.
* **Two generations in one transaction.** `spaceSplitInPlace` gives the
  second half and the new root `replacedBy(node)`; `handleFullNode` and
  `spaceSplit` set `madeFor(.., node)` only for a node that existed. So
  `replacedBy` always names a node that existed before tt, and the
  grandchild's repoint target is that old node; its klong is deleted or
  overwritten right after, as above. OK.
* **The rerun and the ids (I8).** `Db.setIdOfNode` and
  `DbStarter.nodeCreated` (P5 `DbStarter.java:402`) consume one vpos per
  created node in creation order; the climb is a function of the state;
  `nextVpos` is reset from the stream position at every transaction's
  begin, so the next id after a restart does not depend on how many nodes
  were taken back. The rerun registers the node and drops it at once
  (`Cache3.dropNode`); a taken-back id never reaches a got-dirty list
  (`endOfTrans` removes it first). OK.
* **The unlink** (`Dag.unlink`, `:1405`). A live klong of tt naming an
  old node N exists only by `emptyKeyNext`'s copy or `replaceRoot`'s
  append, and is overwritten or deleted when N empties later in tt. A
  deleted klong of tt may still name N: N existed, is in the stream or in
  D, so the reference resolves. Readers before tt stop at the time klong
  of tt and never read the dropped tail, as for `handleFullNode`'s
  replacement today. N dirty since before tt stays in D and is written at
  its tt - 1 state; N dirty only in tt leaves D in `endOfTrans`. Eviction
  and reload give a version at or before tt - 1. OK.
* **X5 (c) is unreachable from `Db`.** `Trans` sorts a transaction's KVs
  in a `TreeMap` and keeps one entry per key (015-41). A node tt made that
  no split made (a new segment leaf, `Dag.java` near 922; the second half
  of a node of tt split in place) holds only tt's puts, all live at tt's
  end, so the climb never meets it. The branch in `deleteUpward`
  (`statKeptNew`, P5 `:1116` to `:1127`) and UnlinkFuzz's exemption of
  "the leaves the climb kept" are dead: my runs show `kept for A3 0`. If
  it were reachable it would leave an empty leaf linked at the latest
  time, one per transaction, against I2, R3 and R12 (a). Recommendation:
  a `Bug` there, so that a change of `Trans` cannot open it unseen.
* **Crash, eviction.** A crash is a rerun of stored records with the
  same code. A taken-back node is dirty until dropped, never evicted; the
  repoint target existed before tt. OK.
* **The fuzz.** UnlinkFuzz on `71e386de`, with P5's pointer check and I1
  after every transaction, with merges on: 80 rounds, 0 failures.

### 2.3 K2, the empty key first

* **The split rule is complete.** `KeyNode.firstAndSecond` is the only
  place halves are built; the three `spaceSplit` cases and
  `spaceSplitInPlace` call it (P5 `Dag.java:2217`, `:2347`, `:2374`,
  `:2405`). The inserted klong goes by its first compare value; when it
  equals the second half's first value, both go to the second half and
  the inserted one becomes the empty key, shadowing the copied one. Time
  splits copy `last` whole, so the empty key stays first. OK.
* **No reader relies on a tight first klong.** Readers use `searchLte`,
  `searchLt`, `searchGte`, `searchGt` (ties go to the later index,
  `KeyNode.java:516`, `:592`, `:665`, `:739`) and `lastVersionGivenDel`
  (later wins), so a shadow pair reads as its newer klong. One trap:
  `KeyNode.searchFirst` (`:763`) takes the earlier klong on a tie; no
  production caller today. Note it in its Javadoc.
* **The bitmap rule in `emptyKeyNext`** (`:1478`): in the non-full case
  the bitmap of c_j comes first, then `copyPointer` in place or
  `addKlongCopyPointer`; the empty key's klong never gets a bit (the
  bitmap's bits are c_j's; an inner node's `appendDeleteKlong` is called
  with c != 0 only, `:1191`). In the full case there is no bitmap: `last`
  is built without the klongs of 0, c_j's klong relabelled 0, through
  `handleFullNode`; the delete of c_j is recorded as its absence in the
  new version. The conformance checker accepted it (P4's gates); the
  trace documentation should say so.

### 2.4 K3, root collapse

`collapseRoot` (`:1223`) and the quiet descent: the quietly followed
child is the old root's only child, either off the key's path and
unchanged, or on it and already marked (marks are sticky,
`Db.makeDirtyIfNeeded`). `replaceRoot` at depth 0 makes a new top node
only when the root time is before tt, else updates tt's top node in place
(`TopDs.newSuperRoot`); old top nodes keep the old root, whose klongs of
tt the unlink drops, so earlier-time lookups are unchanged. OK. The exit
`made && replacedBy == null` is X5 (c)'s family: unreachable for the same
reason (a root of tt that no split made is a segment leaf).

### 2.5 K4, `dirtyNodeBound`

* **One delete against the count** (`Dag.java:477` to `:650`,
  `Db.checkDirtyNodes` `:2712`): the leaf's bitmap; the unlinked nodes
  are on the walked path (an unlinked node dirty since before tt stays in
  D and is written: counted, as it is on the path); `stop` needs at most
  bitmap + empty key + time klong, within the 2 klongs + 1 time klong the
  bound gives; a full `stop` through `handleFullNode` is within
  `overflows + 1` nodes and the parent's klongs; `replaceRoot` appends one
  klong to the segment leaf above (on the path) or makes a super root
  (counted as top bytes). Puts and deletes combine as 1 klong at a put's
  leaf and 2 on every node of a delete's path. OK.
* **Undercounted: a chain of single-child roots.** `collapseRoot` loops,
  so one delete can append k klongs to the segment leaf above when k
  single-child inner roots collapse at once, where the count gives that
  leaf 2. Such a chain needs k earlier transactions each leaving a
  one-klong root (which RC's exit allows only for a root of tt, so it is
  rare); the extra is at most one more overflow of that leaf. Count the
  collapse's klongs, or cap the loop in the count.
* **The cheap test.** At node size 30 the walk starts above about 4,900
  deletes; 150,000 random deletes in a 1M database count about 300,000
  nodes, far under the limit; refusal from about 2 million deletes, as P5
  says. The walk runs under the write lock before the go point, one
  descent per key: for a cold cache it doubles a large transaction's
  reads. Not a fault; worth a line in the class comment.

### 2.6 K5, the step at its own time, with E

* **The values' argument (P8, 2.3) holds**, with one unstated premise
  that the code meets: every step's scan time is after tStart, since the
  call that starts an iteration never runs a step (`allowed` is 0 then).
  `Db.execute` calls `transactionCompleted` after the user's changes, the
  store and `afterTransaction`, so the scan at `Long.MAX_VALUE` sees the
  state after transaction t and reads at `actualLookupTime = t.tt`;
  nothing commits between the scan and the step's puts under the write
  lock. With UP, an unlink deletes every key of the leaf at u, so a key
  live at t >= tEnd was live at the step's time; no new case.
* **The index nodes (P8, 2.4) hold**: the touch is unchanged
  (`Trans.touch` in `putKvs` before the puts; `Db.touchRange` a `GetMany`
  at tt from the last key, to the end when `touchTo` is null); the ranges
  are consecutive from null, so the boundaries do not enter the argument.
  A node touched at tt_i and unlinked at u > tEnd stays in D (it was dirty
  since tt_i; `endOfTrans` takes out only the running transaction's own
  marks) and holds the startup pos until written. OK.
* **E**: `IterationInfo.pastEnd` returns STOP before adding the first
  live key after E, `eod` is set and the last step touches to the end of
  the key space, keys put after E included. E is set in
  `transactionCompleted` before `storeTable` in the same call,
  serialized, parsed and copied; `initFromDb` applies the current row
  over the table's. A row without `endKey` scans unbounded: format 6's
  refusal covers it. OK.
* **Liveness, the change I would not accept unmeasured.** `allowed` is
  the fraction of the growth minus the bytes rewritten, and a step scans
  at most `MAX_STEP_SIZE` = 16,000 bytes of KVs (`size` counts every KV
  scanned, key + value + 100), whatever the user wrote. Today the scan at
  tStart covers a fixed set and ends after at most (keys live at tStart) /
  16 kB transactions. With P8, random puts before E land ahead of the scan
  and are scanned too: a user who puts more than 16 kB of random keys a
  transaction, ahead of the scan, outruns it, and the iteration ends only
  when the growth slows. With uniform random puts of u bytes a transaction
  and s = 16 kB scanned a step, the scan's position advances as (s / u)
  ln of the growth, so the iteration ends when the database has grown
  about e^(u / s) times (P8, 7, says e^r): at 100 kB a transaction about
  500 times, against about 1 + u / s = 7 times today. No cut while it
  lasts; the stream holds every version ended since pCut. R6 and R13 then
  hold with a workload-dependent constant, not today's. Not seen in T4
  hashed because the live set there is constant. The keys-only scan (P8,
  8) lowers the cost a key but not the 16 kB cap; a cap in nodes visited
  instead of bytes, or a scan that skips a run of keys put after tStart
  without counting them, would restore today's bound.
* **Measured**, on P8's head `f56dca40` (`P8Live.java` and the runs A to
  C in this review's `probe/` directory): a Core Db on a file, budget 1
  GB, a test clock of 10 ms a transaction, retain 1 s, startup distance
  100 kB, keys `/h/` plus 16 hex digits of a random long, values of 100
  bytes, each transaction 90 % puts of new keys and 10 % deletes of live
  ones; a step ran at nearly every transaction and the 16 kB cap was its
  limit (72 KVs a step in every run).

  | Run | Ops a transaction | Transactions | Iterations done | Cuts | now - f at the end |
  |---|---|---|---|---|---|
  | A   | 1,000 (100 kB)    | 2,000        | 0               | 0    | never set; 2.2 GB stream |
  | B   | 200 (20 kB)       | 10,000       | 3               | 2    | 60 s, climbing       |
  | C   | 60 (6 kB)         | 3,000        | 7               | 6    | 2.0 to 8.6 s         |

  Run A's one iteration started with 2,400 live keys and stood at 17 % of
  the key space after 2,000 transactions (today's rule: about 34). Run
  B's iterations took 39, 382 and 3,512 transactions (today's rule about
  11, 103 and 954); the fourth stood at 13 % after 6,059 steps. Run C's
  took 1.4 to 1.5 times today's. A model fits all three: with r KVs
  scanned a step and g net new random keys a transaction, an iteration
  started with L0 live keys ends after (L0 / g) (e^(g / r) - 1)
  transactions (today L0 / r), so for g above r the length is exponential
  in g / r. Ordered keys and a steady state are unaffected, which is why
  P8's gates and T4 saw nothing. Today's figures are the rule's
  expectation, not measured (no `main` build in this review). A fix must
  make the step's limit count only what the iteration must cover (keys
  with a value before pStart, or keys live at tStart), or let the scan's
  rate grow with the growth since pStart; a larger cap only moves the
  threshold g = r.
* **Determinism**: nothing of the scan is stored; E once. OK.

### 2.7 K6, the dead hand

* **"Stored before the cut" is exact** (`Cache3.deadStep`, P6
  `Cache3.java:498`): the handle's object is evicted iff its position is a
  stream position below the cut and `Eviction.detachable` (not in the
  transaction's nodes, not the super root or the newest written top node,
  not pinned: canonical and dirty). A written node kept dirty by Rule A is
  canonical and dirty, so pinned. A reader's older version of a node
  whose latest is after the cut is killed; `Handle.usable` never served it
  to a lookup at an available time.
* **Decided but not made.** `pretruncateIfPossible` sets the first
  available time and position together at the decision, after `done`,
  startup pos >= pSafe and a meta block past pCut; lookups below tEnd are
  refused from then on. So from the decision no admitted lookup, the
  writer, a later step or touch follows a pointer below pCut. What the
  dead hand evicts is reachable only by readers admitted before the
  decision: a held object is unchanged (`kill` clears the canonical flag
  and nulls the handle's object), a re-follow reloads while the bytes are
  there (`cutIfDurable` comes later) and expires after (D1 = A). A reload,
  never a wrong answer.
* **Held readers**: `evict`, `deadStep` and `dropNode` CAS LIVE to DEAD
  under the map lock; a loader's LOADING fails the CAS; `unswizzleValue`
  takes the key node's monitor as the controller's path does. Not read:
  the reader's lock-free fast path (009) against that unswizzle; P6
  reuses the controller's code, so no new case.
* **With the queue**: every kill is behind a CAS; `replacedStep` skips an
  object that left its handle and taken-back ones. No double kill found.
* **With P8**: the step's scan reads current nodes and live values, which
  neither the queue nor the dead hand takes (by I6 they are at or after
  the decided cut); P6's 190,272 loads should go to about 0. Argument,
  not measured: no branch has both.

### 2.8 K7 and K8

SE ends a scan at the first klong past the end key, live or deleted; keys
are in order in a node and below a klong, and LE-b's empty key is the
smallest, so no live key before the end is lost. Forward only, enforced.
Trusted from 021-28's review and its 1,500-scan test. K8: `RECORD_FORMAT
= 6` on every branch; `formatRefused` still names format 2 only, as 023-07
says.

### 2.9 The full set

* **F2 (a).** `Db.store`'s order is take, `writeAheadTops`,
  `resolvePointersOfTakenNodes`, clean, `handleStillDirtyNodes`; the
  ahead nodes' pointers are resolved; only skip pointers, never a root or
  a key node; the record limit's sum stays at or below the limit. The
  start's rule (`DbStarter.rerunTransaction` `:455` to `:467`) drops an
  entry of record j iff the node's newest version in the section is after
  j: a node pulled at k > j and still dirty is refiled in gd(k) with its
  version at k (kept at k); one clean at k and marked at m > k is in gd(m)
  (kept at m). No kept entry is shadowed. One exposure, not settled: if
  the start's iterator ever returns a record that recovery completed
  after a crash with index nodes in it, a pulled node's "newer version"
  could be that record's; Rule R has the same exposure today, so likely
  handled; one CrashTest round with a torn record that pulled a node would
  settle it.
* **F3 (b').** 023-06's 18.7 argument is right in the code: a replaced
  node loses its klongs of tt, so every pointer of it predates r(x); e
  after a restart comes only from the stored entry (the rerun's listener
  never marks), not from the rerun's markings as 023-07's 5.11 says, which
  is why stored and rerun values cannot differ. The agreement of r rests
  on object identity in `IdentityHashMap`s (the rerun's super root must be
  the node table's object): RestartInvariance's five configurations are
  the evidence. e = 0 means "none": harmless while tt is never 0.
* **F1 merges, F5 `maintain()`**: not read in depth. P5's bound is "an
  argument and a probe"; its "inter" rewrites (2.1 times the bytes) are a
  Rule A effect, not a fault.

### 2.10 The model's assumptions

The core changes none: A2 and A3 hold by the take-back's "not made"
(Z18); TREE and A6' by the single live klong to each node; A-COPY by the
pointer copied while the node is current; INV-1 to INV-3 by an unchanged
take and Rule A. (a) changes INV-1 and step 5; (b') changes the physical
theorems' test. Nothing in the core needs a Lean change.


## 3. The rule and the bound

| Requirement       | Core meets it            | Allowance or gap                        |
|---|---|---|
| R1, R16 lookups   | yes (2.2 to 2.8)         | none                                    |
| R2 stream bytes   | yes, K = 2 cuts          | dead klongs in live nodes (F1) stay     |
| R3 reachable idx  | yes                      | underfill ("sparse"), chains ("inter")  |
| R4 memory         | yes, after each cut      | replaced nodes until the cut (CLOCK)    |
| R5 work           | yes                      | the rerun reads each delete's path      |
| R6 keeps up       | without P8 yes, one iteration later | with P8 as built, no (2.6)     |
| R9 scan O(n)      | yes, every available time | constant: B klongs a node, H a key     |
| R10, R12 (a)      | yes                      | in the keys ever put, as F5 allows      |
| R12 (b) strict    | no                       | merges, later                           |
| R13 stream        | yes without P8           | with P8 as built, no cut under growth   |
| R15 startup       | not measured             | run a cold start at 50 MB               |
| R17, R18          | yes (2.2, 2.6)           | none                                    |
| R24 Lean          | yes, checker only        | none                                    |
| R26, R27          | open                     | T10; new digests                        |

* **Frans's rule.** A deleted KV's value and record go at the cut after
  its death (today's); its leaf's version and the unlinked nodes' versions
  are stored before pCut and go with the same cut; its memory goes at the
  dead hand's round after that cut. Its klong in a leaf that keeps live
  keys stays until that leaf's next time split: at most B - 1 klongs a
  live leaf, the twin's own rest (023-03, C4). F1 wanted them gone
  "eventually"; the core leaves them for a node that never fills again.
  Say so in the release notes, or let the touch rewrite a node whose dead
  klongs exceed B / 2 (a later item).
* **The scan bound.** At time t a scan hands its stop condition the keys
  live at t; a deleted key was live before its delete, so it is counted
  at those times and is unreachable at the delete's time and after (UP).
  The nodes followed are the paths of the n keys plus the underfull nodes
  with a live key below, at most n + H each. O(n) with constants B and H.
  A single scan right after a mass delete follows 1 node (P4, 3.3).

## 4. Simplicity

### 4.1 What the core could be without

* **P8** is the one piece that is not needed for the rule: without it the
  iteration in progress at a mass delete scans the keys live at its start
  (one iteration of lag, bounded by the data before the delete) and ends.
  P8 removes that lag, 11 to 12 % of the steps, and P6's reloads, and, as
  built, brings the liveness fault of 2.6. It changes no format: a 2026.5
  that adds it can compute E for a row without one at start (`lastKeyAt`
  at the row's tStart, which is at or after f). So it can wait. T1 at 1M
  then needs a drive of 12,000, as P4 and P6 used.
* **X5 (c)** and RC's exit for a root of tt are dead branches (2.2, 2.4):
  remove them.
* **The rest is minimal** given Frans's answers: UP for F3 (the bound at
  every available time needs the traces gone at the delete, not at a
  rebuild); LE-b for an unlink that changes no node off the path; RC for
  the twin's shape after a mass delete; K4 as a fix; the dead hand for Y6
  (b); SE for Y7; format 6 for F9 and F10.

### 4.2 A simpler sketch

The core minus P8, with the dead code gone:

* **At a delete**, by the writer: bitmap; if the leaf empties, climb to
  the first node that keeps a live klong, taking back the nodes of tt
  and unlinking the older ones; at the stop, a bitmap, or LE-b's empty
  key; then RC. Checked by UnlinkFuzz after every transaction (I1, I2 but
  the empty space root, the pointer check) and A2A3Check2.
* **At each cut**, by the writer's thread: the dead hand's round.
  Checked by `Eviction.testDeadHand` and the held-reader test.
* **Reclaim** as today. Checked by C-CUT.
* **Format 6** with the refusal; SE on the read path.

Four mechanisms, about 1,100 lines, no reclaim change, no Lean change.
P8 then comes with the keys-only scan and 2.6's measure, in 2026.5.

### 4.3 What the full set is for

| Addition   | Needed for                                 | Correctness | Rerun rule |
|---|---|---|---|
| F1 merges  | R12 (b) strict; "sparse" 1.44 x           | no          | yes        |
| F2 (a)     | D's size and the start's objects at 1M     | no          | no         |
| F3 (b')    | bytes with merges, -15 %                   | no          | syntax     |
| F4 queue   | memory before the cut under a large budget | no          | no         |
| F5 maintain | "eventually" without user writes (F7)     | no          | no         |

None closes a fault. F1 is the only one whose lateness costs a refusal.


## 5. Risk for 2026.4

* **The combination.** Every gate ran per branch. Expected conflicts in
  `Dag`, `Db.endOfTrans`, `Reclaim`'s class comment; the StreamDigest
  digests change once, on the integration head. Gate there: level1 to
  level4 full, `night.sh large`, StreamDigest's four modes equal, T6.
* **Stream size.** P8's +24 % in an ascending mass delete (steps ahead of
  the deletes) is within the internal fraction; the drive after it -61 %.
  "inter" with merges 2.1 x (full set only). T10 before and after on a
  quiet machine, CORE and MEM, is in 6.3 and must run before the release.
* **Memory.** The dead hand's step reached 104 ms of wall time on a loaded
  F53 (2 ms of CPU): time it on a quiet machine with 10M nodes (P1, the
  20 ms guide). A reader before the cut can make dead objects resident
  until the next round: bounded by one round.
* **Time.** `dirtyNodeBound`'s walk under the write lock for large
  transactions (2.5); the rerun's climb per delete at a start (R15):
  measure a cold start at 50 MB with a mass delete in the section.
* **Format.** 2026.3 refused; the message still names format 2 (K8). A row
  without `endKey` scans unbounded: refused by the format, but a test.
* **C port.** About 500 lines after the release; `cross.sh full` with a
  new pin. The take-back's rules are the hardest part to port byte for
  byte: the retarget of deleted klongs must match exactly (I8).
* **The gates miss**: C11 (no prototype has it); the ratchet test on P8;
  a growing hashed workload (2.6); a crash round with a torn record that
  wrote ahead (if (a) is in); a cold start at 50 MB; a transaction that
  reaches the record limit with deletes only (K4 at sizes 8, 14, 30).
* **Tests to add**, beyond 6.2's list: `Bug` for X5 (c) and a `Trans` test
  that one key comes once; DagTester for `collapseRoot` over a chain of
  k roots with the count checked; `searchFirst`'s Javadoc; a
  ReclaimStress variant with random puts before E.


## 6. The claims

Checked against the reports and the code; "ok" means supported.

| Claim in 023-07                                        | Source           | Result |
|---|---|---|
| T1 17 of 18 rows at 1,000 and 100,000 (3.2)            | P4, 3.2          | ok     |
| 1,000 descending: 118 against 85 + 26                  | P4, 3.2          | ok     |
| P8 at 1M, three orders, C1 to C3, C5 to C10 (3.2)      | P8, 5.1          | ok     |
| C9 over by 1 and 6 at 1,000 and 100,000                | P8, 5.1          | ok     |
| "sparse" 4,036 against 270; "inter" 14 against 6       | P5, 4.1; P4, 3.2 | ok     |
| T3 one node a scan at 100,000                          | P4, 3.3          | ok     |
| D 178 against 94, 184 objects against 83 (3.2)         | P7, 6.1          | ok     |
| P8 D 90 against 83, 91 objects, 58 top nodes           | P8, 5.1          | ok     |
| dead hand 292 against 11,612, twin 263 (5.6)           | P6, 4.1          | ok     |
| T4 "712 to 858" (3.2, 5.6)                             | P6, 4.3          | see (1) |
| deletes 85.0 against 68.4 MB, drive 5.5 against 13.9   | P8, 5.4          | ok     |
| "after" R forever 4.82 against 6.78 MB (5.1)           | P5, 4.3 (not P4) | ok     |
| (a): D 35 / 34, objects 25 / 33, -27 %, 7 against 40   | P7, 6.1          | ok     |
| (b'): 248 to 150; 71 in memory                         | P7, 6.2          | ok     |
| left-out nodes gone within 10,000 transactions         | P7, 6.3          | ok     |
| K4: P4's count refuses about 150,000 deletes           | P5, 6            | ok, a probe |
| "no model change" for the core (3.1)                   | code, 2.10       | ok     |
| "the rerun makes the same choices" (5.1, I8)           | code, 2.2        | ok     |
| X5 (c) "never reached by a run" (5.1)                  | code, fuzz       | unreachable from Db |
| "(b'): stored and rerun values must agree" (5.11)      | code, 2.9        | see (2) |
| "Z12: as recommended" means merges go in (1, 9.1)      | 023-06, 16       | see (3) |
| about 1,200 lines for the core (1, 6.5)                | the diffs        | ok, see (4) |
| level2 full on P4 (3.3)                                | P4, 2            | ok     |
| P8's C-CUT 0 of 303 (3.3)                              | P8, 4            | ok     |

1. P6's table 4.3 gives 712 to 798 for the dead hand at 1 GB; 858 is in
   P6's summary only.
2. There is nothing to compare: e comes from the stored entry only, the
   rerun never marks (2.9).
3. The recommendation was conditional: merges into format 6 "if P5's
   gates pass full and 11.3's points 1 and 2 close within days; else
   2026.4 with P4 alone and merges in 2026.5 with the refusal". Whether
   "within days" is met is Frans's judgement, not a fact 023-07 settles.
4. P4 785, P8 123, SE about 90, the dead hand about 215 of P6's 430.

Everything else I checked holds.


## 7. Questions for Frans

1. **P8 in 2026.4?** As built, no (2.6: at 100 kB of random puts a
   transaction reclaim stops, at 20 kB the lag grows without bound). Two
   ways: (i) 2026.4 without P8, with one iteration of lag after a mass
   delete and a drive of 12,000 in T1 at 1M, and P8 in 2026.5 with a step
   limit that counts only the keys the iteration must cover, measured
   with run B's workload; (ii) that fix now, if it is a day and the
   measure passes. Recommended: (i). Z14 was taken on gates that had no
   growing random workload; add run B's to ReclaimStress either way.
2. **X5 (c) as a `Bug`**, and RC's exit for a root of tt removed, since a
   transaction never puts and deletes one key? Recommended: yes; the
   rules of 5.1 and 5.3 lose a sentence each.
3. **Merges (Z12).** The condition was "within days". Recommended: not in
   2026.4; a format 7 in 2026.5 that refuses 2026.4's databases, as 2026.4
   refuses 2026.3's. "Sparse" at 15 times the twin's nodes is bounded in
   the keys ever put, which F5 accepts.
4. **(a) now (Z13)?** Recommended: not in 2026.4. The window is bounded
   and the same on `main`; (a) changes INV-1 and the model's step 5 and
   needs the checker's step; it can come in any release without a
   refusal. Name the window in C6 and C9 now, and run the ratchet test.
5. **(b')**: never as a stored 32-byte entry; reconsider only with merges
   and a format change. **The queue**: off by default, as Z15 (2).
6. **`maintain()`** (Y10): 2026.5, rebased on P8's E; the drive serves
   the tests in 2026.4.
7. **F1's dead klongs in live nodes**: accept the rest of at most B - 1 a
   live leaf in 2026.4 (the twin's own), with a note in the release
   notes? Recommended: yes.
8. **Gates before the release**: T10 and the cold start at 50 MB on the
   integration head, not after. Recommended: yes, a day.
