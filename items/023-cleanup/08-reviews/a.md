# 023-08 Review A of 023-07

## 1. Verdict

Reject the core as written. Keep the delete design, but do not release this combination yet.

1. P8 can keep chasing a constant-size queue. E does not close R6.
2. Its final touch can dirty a large new tail outside the scan's reserve.
3. The core does not establish R2 to R5's fixed cleanup delay. An old delete entry survived 700 cuts
   in a probe. The dead hand also leaves the cache's backing arrays at peak size.
4. Keep UP, LE-b, the complete take-back, RC and the format refusal. Keep today's Rule A. Close the
   top-node window with (a), including its startup rule and Lean work.
5. Put merges, (b'), the replaced queue and `maintain()` behind those questions. They do not repair
   P8's progress rule. There is a useful simplification: mark only rewrite paths, once every current
   node has a live value below it. Section 4 gives the argument and limits.

## 2. Soundness

### 2.1 What I checked

Starting commit: `e45fd4c1`. I read the instructions, 023-01 to 023-07, the reports, current Core,
prototype changes and the model's assumptions, algorithm, dirty invariant and cut definition. SE's
`eebeb39d` was read in its cited earlier clone; that object is absent here. No other review
directory was read.

Heads: P4 `0e66d1c9`, P5 `71e386de`, P6 `c46d607d`, P7 `cd81d789` and its (a) changes, P8
`f56dca40`, P3 `7b2cf1ec`; P1 and P2 as alternatives. A scratch combination uses P7's Core, P5's
Dag/KeyNode/PutData and P8's Reclaim. It omits SE, P6 and maintain(). Checks run here, with probes
and logs kept in 023-08's review evidence:

- 96 selected unit checks: `DagTester`, `KeyNodeTester`, `DbTesterRestart`.
- Strict `UnlinkFuzz`: five seeds each of random, long and FIFO shapes, node size 8, 180
  transactions per seed. No lookup, shape or taken-back-pointer failure.
- `A2A3Check2`: 1,500 transactions, 60% deletes, long keys, up to 20 operations, node size 8. No net
  A2, A3, A5, TREE, A6' or A-COPY failure. Marking agreed; 403 nodes were taken back.
- `RestartInvariance`: 1,000 transactions, restart after each, reclaim, long keys, deletes, size 8.
  Same bytes and cut; no D, identity or lookup difference.
- P6's memory unit checks and held-reader f-test, and P8's two new step tests, passed.
- P7's counterexample passed with (a) and with (b'). Withdrawn (b) failed at seed 1: `/k/19`, time
  69, needed node 1931, neither in the stream nor memory.

I did not run level scripts, performance suites or night.sh, rebuild Lean proofs or port to C.
023-07, section 3.3's gates remain reported evidence, not rerun here.

### 2.2 UP and the history it leaves

`Dag.deleteUpward` finds its stopping node before changing the path. Below it, `unlink` removes only
entries of tt. The parent gets its delete at tt. A reader before tt still uses the old parent entry
and child history. A reader from tt uses the surviving tree. This preserves R1 and R16.

`Db.endOfTrans` drops a replaced node from this transaction's new marks, apart from touch marks. It
retains an earlier dirty node: an old reader may need its unwritten change. Dropping every unlinked
node from D would break INV-2 and recovery. Evidence: those methods on P4; 023-07, section 5.1; the
historical reads in the checks above.

X5(c) remains unfinished. It deliberately keeps a newly made empty subtree linked when `canTakeBack`
fails. If reachable, that contradicts I2 and the scan argument below. A new segment tree made by a
put should retain that put, since each key has one operation per transaction. Prove this for every
split/merge case, or bound and test the fallback. A counter staying zero is insufficient. Evidence:
P4 `Dag.deleteUpward`; 023-07, section 5.1.

### 2.3 LE-b, splits and bitmaps

Zero is a valid lower bound in every inner node; its parent still determines the range. I checked
`searchLte`, scan setup/stepping, last-version copies, both space-split paths and SE's endpoint
comparison. None needs the child's own first key to be tight.

`KeyNode.firstAndSecond` maps both the copied first key and an inserted key of that compare value to
zero in the second half. Changing only the copy leaves two live routes. All three root/parent split
cases share it. `emptyKeyNext` copies the next child's pointer and deletes its former separator.
Earlier entries remain unchanged.

Bitmaps must cover every earlier occurrence of the compare value and precede a new one they must not
delete. I checked `emptyKeyNext`, `appendDeleteKlong` and `mergeParent`. In-place writes are behind
tt's TIME entry; pointer copies read reference and pointee under the monitor. A core FIFO fuzz run
exercised LE-b 175 times with 39 take-backs and no failure. Fixed full-parent/inserted-separator
tests are still needed (023-07, section 6.2). Evidence: those P4/P5 methods, `KeyNode.copyPointer`,
`addKlongCopyPointer` and the fuzz.

### 2.4 The take-back and root collapse

Taking a transient node back is sound only if it leaves no reference anywhere that can be written,
including a deleted entry. P4 alone does not ensure that. P5's `retarget` repairs the parent's other
entries of tt. Keep it in the core. Consuming the transient id, rather than reusing it, is also
necessary for the rerun's subsequent ids.

`Cache3.dropNode` and the rerun's `keyNodeTakenBack` remove the transient canonical object.
Otherwise the memory state contains an unwritten object the logical transaction never created. The
changed A2A3 checker may ignore such a node only after checking these conditions. Simply subtracting
every created-and-replaced node is too permissive. The all-pointer check in
`UnlinkFuzz.checkTakenBack` is a useful separate check.

RC preserves history by changing the super root, or adding/repointing the segment-root entry at tt.
It follows the child before rolling the old root back. A child reached only to become the root is
not marked as changed. Taking back a root made by tt is necessary; otherwise a batch delete can
leave a chain that RC was intended to remove.

I checked split-in-place provenance and the root-of-tt case. The empty-inner-space-root case still
needs a delete-all/reinsert test. Evidence: P5 `Dag.takeBack`, `retarget`, `takeBackRoot`,
`replaceRoot`; P4 `DbStarter.rerunTransaction`; the fuzz; 023-07, sections 5.1 and 5.3.

### 2.5 The bound before the transaction

I read `Dag.dirtyNodeBound`, its overflow propagation, and `Db.checkDirtyNodes`. UP/LE-b change only
path nodes; dropping P1's off-path charge is justified. The two-klong charge must still cover the
bitmap, replacement zero and segment-root relink, with TIME and split overhead counted separately.
The reduced core bound has not been tested as an isolated integration. P5's `mergeBound` adds an
unproved aggregate estimate. I have not independently established either upper bound. Under-counting
can fail a transaction after its go point, so the counted-node check is a release condition, not
optional tuning.

### 2.6 P8: the cut argument works; the progress argument does not

The value argument in 023-05 P8, section 2.3 is sound for ordinary Core puts. A value stored before
pCut and still visible at t >= tEnd cannot have had an intervening put or delete. It therefore
existed at each scan time and at tStart, and lies at or below E. A completed scan covering the
consecutive ranges must find and rewrite it. Splits and merges copy the value pointer; they do not
make an old value into a new put.

For index nodes, an old node still current at tEnd was current throughout the iteration. UP only
expands the routing range of a surviving neighbour. Splits and merges replace nodes; RC bypasses an
old root. They do not shrink a surviving node's routing range. Thus a key routed through it at
tStart remains routed through it until replacement. The consecutive touches reach it. This supports
P8's section 2.4, conditional on I2 and A5. Rule A, pEnd and pSafe remain essential for physical
references and old readers.

This is cut safety after completion. It says nothing about whether completion occurs. Here is a
counterexample to R6, in `ReclaimBeforeEnd`, on unmodified P8:

1. Keep `/z` permanently. Fill 1,000 smaller queue keys, values of 100 bytes.
2. Set R = 1 s, startup distance 100 kB, clock step 1 ms.
3. Each transaction deletes the oldest 200 keys and appends 200 newer queue keys, all still below
   `/z`. There are always 1,001 live user keys.
4. A step scans about 75 queue keys. The next batch moves the queue farther than that. E stays `/z`.
   The scan never reaches it. The live set does not grow.

| After transactions | Completed iterations | Cut position | Stream bytes |
|---|---|---|---|
| 300   | 0 | 0 | 14,041,080 |
| 600   | 0 | 0 | 27,884,728 |
| 1,200 | 0 | 0 | 55,550,264 |

The same iteration is still running, with 1,199 steps. This can continue with keys of increasing
length. Even fixed-length decimal keys give an arbitrarily large practical lag. P4's tStart scan, on
the same probe, completed five iterations and made a cut. The combined copy also failed, both with
and without (b'). Thus merges and top-node write-ahead do not fix this. Optional `maintain()` cannot
be required to rescue it.

This is stronger than the growing random-insert caveat in 023-05 P8, section 7. It violates R6 and
R13 and prevents the eventual cleanup required by R2 to R5.

There is a second bound gap. The last step still sets `touchTo = null`. It walks all new keys beyond
E, although the scan and its reserve deliberately stopped before them. `ReclaimTail` started with
5,000 old keys, then put 1,000 new long keys beyond E per call. The iteration ended after 40 steps
and 40,000 appends. Its largest scan followed 17 index nodes; one step dirtied 81,018 nodes,
5,811,040 stored bytes, already beyond the 4 MiB pinned reserve. This is inherited touch behaviour,
not an allegation of a new wrong answer. It defeats the proposed bounded-step explanation. Evidence:
P8 `Reclaim.step`; `Db.touchRange`; 023-07, section 5.5. Bound the final touch too, or remove it as
section 4 suggests, after checking the cut argument.

### 2.7 The dead hand and replaced queue

Both are sound eviction schedules if the object is written and detachable. `Cache3.kill` clears its
handle and canonical flag but leaves a held object intact. A later follow resolves the dead handle
by id and raises its reference. With a safe cut, an available read reaches retained bytes; an
overtaken read may expire, also while the physical cut waits for durability. Readers need no
stop-the-world wait.

I checked the map-lock/CAS path, pinned checks, value unswizzling and `Handle.usable`. The writer
holds its lock; a reader cannot install a dirty canonical object during that eviction. Rule A
therefore loses no dirty child. The held-reader test passed; it exercises expiration, not every
interleaving. Evidence: P6 `Cache3.deadStep`, `Eviction.detachable`, `replacedStep`,
`unswizzleValue`; `NodeCollection.followStreamPointer`.

Object release is not complete memory release (section 3.3). The queue holds objects until serviced,
retains array capacity, and can cause historical reads to reload versions. Those are cost issues. I
found no wrong-answer path in these schedules.

### 2.8 Merges

P5 replaces both last versions with new nodes; old nodes serve earlier times. The right inner node's
zero becomes its parent separator in the merge; a second half gets zero. Copies occur while both
sources are current, preserving A-COPY. Newly made sources need retargeting and take-back. I checked
sibling choice, redistribution, full parents and depth changes after new roots. Strict fuzz reached
sources made by tt on either side and checked all-time reads and pointers. I found no contrary
lookup. This does not prove `mergeBound`. Evidence: P5 `Dag.mergeAfterDelete`, `merge`,
`mergeParent`, `retarget`.

### 2.9 Rule A, Rule R and the Lean assumptions

The core leaves the take and Rule A unchanged. Rule R still raises references, including vpos, to
the newest section version. I checked `NodeCollection.followStreamPointer`, `resolvePointers` and
`DbStarter.updateStreamPointers`. INV-1 still reconstructs D from the section's got-dirty lists.
INV-2 needs the marking and old-dirty-node treatment in section 2.2. INV-3 is conditional: a latest
version written before d is good before d. A Rule A refile has its version written at d. It does not
prove the node was clean just before d. That is precisely the error in 023-06, section 18.2,
corrected in section 18.7.

For (a), writing a dirty top-node successor early is conservative. References are prepared for the
whole record before serialization, and the still-dirty fixpoint still runs. A target that does not
fit stays dirty and keeps its predecessor dirty. Startup must drop an old gd entry when a later
section record writes that node, and keep a later refile. I checked `Db.writeAheadTops`,
`TransSeq.takeAhead` and `DbStarter.rerunTransaction`. The restart-after-every-transaction run
exercised both a pull and a dropped id.

This changes step 5 and INV-1. It is not just a different startup-position policy. The current
proof's `Inv.inv1 = sectionD` and `parts.taken` still describe the old take. R24 requires their
update and the checker, T1 and T2 to agree. Record limits must also be included; a closure truncated
by the record budget is not an unlimited closure.

For (b'), e >= r is a sound logical reason to ignore that dirty child: its clean version before e
already served every time before r. Lemma M carries that property to newer versions. Unknown e must
use today's rule. I checked setting, retaining and serializing e and r, and restoring them at
startup. The prototype does not visibly cross-check a restored value against independently
reconstructed metadata; `ruleBEntry` installs it. Add that check where both are known, as 023-07,
section 5.11 requires.

`CutOK` covers versions that physical reads can reach, not only latest versions. Its exception for a
pinned Rule A version, and the closure lemmas in `CutHist`, `CutLazyStart`, `EvLogic` and
`CutRestart`, use `javaTest`. They have not been extended to (b'). Leave it out until that work is
done. Evidence: `SIS.Algorithm.javaTest`, `SIS.Proof.Run.Inv`, `SIS.Reclaim.ReadsPhys`, `CutOK`;
023-06, section 18.7; the counterexample run above.

A2/A3 concern the whole transaction after transient nodes disappear. TREE permits one current
parent; dead references do not count as extra parents. LE-b keeps an adopted current child below the
same parent, satisfying A6'. Splits and merges copy from current sources, satisfying A-COPY.

### 2.10 Crashes, format, SE and maintain()

The delete changes need format 6 because the rerun must repeat the same node allocation and
take-backs. `StoredTrans.Parser.parse` rejects a different format before reading its body. Keep a
named 2026.3 refusal and a two-way real-file test. A successful node-id lookup at startup is
necessary, but does not prove the reconstructed histories or D are right.

No proposed mechanism should cut before the cut table and recovery metadata are durable.
`Reclaim.pretruncateIfPossible` and `cutIfDurable` retain that ordering. A crash before a step/table
record completes loses that record; after it, startup resumes its stored row. An endKey held only in
memory is insufficient. Power-loss safety still assumes the stream's existing forced-prefix
contract. The Lean model assumes complete abstract records. I read these paths; I did not physically
cut power or independently rerun the power-loss gate.

SE's bound is sound with LE-b, including seven-byte prefixes and the empty key. It checks a subtree
lower bound before following it and clears the Chain's field when stopping. Backward scans are
explicitly refused when an end key is set. This is a read optimization; UP supplies the general scan
bound. Evidence: SE `GetMany.Chain.next`, `isPastEnd`, `Dag.getMany`, `Db.getMany`; 023-07, section
5.7. I inspected SE, but did not run its tests.

The proposed extracted `maintain()` does not yet exist as an integrated mechanism. P3's forced take
allows its first whole dirty transaction to exceed 1 MiB. The claim "at most 1 MiB" is false. Also,
P8's `lastKeyAt` asserts that its requested time is an actual committed time; an idle
`Db.currentTime()` need not be one. Adapt that call when starting an iteration from maintain().
Check failure handling and waits for a meta block. Evidence: P3 `TransSeq.take(..., forced)`,
`Db.maintain`, `Reclaim.maintain`; P8 `Reclaim.lastKeyAt`; 023-05 P3, section 1.4.

## 3. The rule and the scan bound

### 3.1 What UP establishes

Provided X5(c) cannot leave an empty subtree, each current node except the empty space root has a
live KV below it. This holds at old times too: later deletes leave the old tree unchanged. A forward
or backward scan that presents n KVs visits their paths and its two boundary paths, at most about (n
+ 2) H nodes. Local searches cost at most B per node. This gives a single-scan bound, stronger than
R9's amortized form, with B fixed.

A smaller live set can still have tall, single-child paths. R10's required bound permits height in
the keys ever put. R12(a) permits a live key to pay for such a path. Neither permits an arbitrary
number of empty subtrees. Merges improve height and occupancy; they are not needed for this scan
argument. Evidence: 023-02, R9 to R12; section 2.2 above.

### 3.2 A counterexample to the cleanup delay, in both tiers

`SegmentAge` needs just two keys under a cold seven-byte prefix: a short key ending there and a
95-byte key continuing through twelve segment trees. Delete the short one. Use node size 8, R = 1 s,
and drive writes to an unrelated key. The first cold segment leaf retains the short key's delete
entry beside its pointer to the long key's continuation.

That same node, id 265, and its old entry remained current after 700 cuts. The cut frontier had long
passed the delete. This happened on P8 and on the combination with merges, (a) and (b') enabled. The
long value remained right; the deleted key stayed absent; X5(c)'s counter stayed zero. This is
leftover history, not a lookup failure.

Rewrites fill the last leaf first. Its splits eventually change the preceding segment leaf; that
leaf's splits change the one before it. The early leaf can wait far more than B iterations. These
are segment roots: merges do not combine them, and RC cannot collapse a leaf. Longer keys extend the
delay. The queue only evicts/reloads the same stored history; maintain() without rebuilding only
writes it again. Thus the full set does not close this gap.

A separate six-byte-key probe, `RoutingAge`, retained three identified current inner nodes with old
delete entries after 490 cuts and 59,455 drive transactions. Merges helped that case. They do not
solve the segment-chain case above. Evidence: both probes; `Dag.mergeAfterDelete`,
`KeyNode.toPreviousState`, `lastVersionGivenDel`, `StoredKeyNode.toLongs`. The approximately
B-iteration claim in 023-04, X4 is false for ancestors. R2 to R5 and R7 need a compaction deadline
or an explicit weaker contract. An aggregate node allowance or C11's value-only walker will miss
this.

### 3.3 Memory and startup

`CacheCapacity` used P6 with the queue off and a 1 GB budget, above the workload's need. After
100,000 puts and deletes, it drove 12,000 overwrites and allowed the dead hand to run.

| State                  | Resident objects | Live handles | Hash table slots |
|---|---|---|---|
| Filled                 | 109,635 | 109,635 | 218,592 |
| After drive            | 273     | 273     | 219,104 |
| Fresh twin after drive | 261     | 261     | 22,144  |

The cut had moved to 54,726,000. Objects went; the backing arrays did not shrink. This is R4's
explicit "no structure ... keeps a size it reached because of them" case. P6 already records this
omission in section 4.4; 023-07 leaves it out of the residuals. `KeyAccessPath.clear` also retains
array capacity; `PutData.replaced.clear` retains its identity-map capacity. The full set's queue
adds another peak-capacity structure. Keep object counts, but add whole-heap/container-capacity
checks to C9 and R14.

The dead hand needs a round of later transactions, not just a cut. Readers admitted before it can
reload objects while the physical bytes remain. `noEvict()` is an explicit exception, accepted only
if the contract says so. Memory is not released synchronously "after each cut" as 023-07's summary
suggests.

Startup still reads a bounded section, but cheaper delete records can fit more deletes in it. Each
rerun reads a path; merges can read siblings too. The memory left by those reads is not measured by
D alone. A bound on section bytes is not an unchanged constant for cold startup time, pinned bytes
or total heap. Evidence: `DbStarter.rerunTransaction`; 023-05 P2, finding 8; P8, section 5.1;
023-02, R14 and R15.

### 3.4 Requirements, without changing their meaning

R1 and R16 to R20: supported by arguments and focused checks, subject to integration and model work.
R8/R9: retain forever keeps history but still needs the scan bound. R10's required height bound and
R12(a): supported under I2. Merges improve live height and R12(b)'s occupancy; they do not establish
exact equality to a fresh twin.

R2 to R5 and R7: partial; old entries and container capacity remain. R6/R13 fail the queue.
R11/R21's work bound, and R15/R26's startup and performance costs, are unresolved. R22/R23: the
refusal is appropriate, with its message fixed. R24: the core's net change can fit today's model;
(a)/(b') need the work above. R25: C must follow the final scanner and memory rules. R27: restore
moved corruption cases and obtain mode agreement and approval for new expected bytes. Passing an
aggregate allowance does not show each old version's things have gone.

## 4. Simplicity

### 4.1 Keep one delete rule

Keep P4's path-local UP, LE-b, take-back and RC, with P5's retarget and a checked bound. They solve
the cause of repeated scans over empty subtrees at every available time. P1's relabel walks another
path and can resplit it. P2 moves the exception into routing, scan setup and later splits. Its
shorter diff is not a simpler invariant for future readers. P3 alone cannot replace UP:
retain-forever scans keep the original problem. Evidence: 023-05 P1, section 1.2; P2, sections 1.2,
1.3 and 2; P3, section 4.7.

Keep the take-back, its all-pointer retarget and the table removal: the representation and rerun
need them. RC is not needed for R1 or R9, but is small and restores the one-key shape. Merges can
wait under the bounded allowance accepted in 023-02, F5. They do not repair P8.

### 4.2 A smaller reclaim: mark rewrite paths, not whole ranges

The range touch was added because empty current nodes had no live value to rewrite. UP removes those
nodes. For an old node current at tEnd, choose a live value below it. If that value predates pCut,
reclaim rewrites it; otherwise its put was already after pCut. Either write marks its path. Splits
and merges make new nodes; unlinking does not resurrect old ones. The existing waits should
therefore suffice with the weaker, sufficient index bound pCut rather than pStart. Check an empty
space root and every physical reference too.

Mechanism: before a step's puts, the writer walks only the point paths of its rewrite keys and row,
marking them with the existing listener. Then it does the puts and ordinary take. This replaces
`Db.touchRange` by a shorter loop over those paths. No new record field, rerun operation, setting or
background job. Clearing `Trans.touch` alone is wrong: it also controls dirtied-byte accounting and
step classification. Keep that accounting, including its timing before the row's value
transformation, or separate the two meanings explicitly.

I prototyped this form with P4, the P5 retarget/bound and P8, merges off. On `ReclaimTail`, maximum
step dirtiness fell from 81,018 nodes to 27. Twenty reclaim rounds passed, each cutting, with 160
exhaustive checks; three crash rounds passed. Three traces with restarts, historical reads and
random eviction passed C-A, C-S, C-L, C-P, C-H and C-CUT, covering 15 cuts. The checker was a
prebuilt binary from a checkout with the same Lean tree (`800220fb`); I did not rebuild it or its
proofs. The patch is review evidence, not production code or a complete gate. The physical-reference
argument still needs review.

This is a useful simplification to pursue first. It removes the new-tail walk and avoids retaining a
range-wide writer access-path array. It does not cure P8's before-E chase or remove dead klongs. It
relies on I2; close X5(c) before relying on that premise.

### 4.3 Progress and literal cleanup still need decisions

For the scanner, a fixed maximum key is not a fixed work set. A smaller candidate than another
background job is to intersect the tStart and current key streams by ordered seeks: skip an old
range now empty, and jump over fresh keys before the next old key. Store progress even when a step
finds no value to rewrite. This gives a finite old frontier and avoids the demonstrated queue chase.
Bound the index work per step and test mass deletes with new interleaved keys. I have not
implemented or proved that candidate; it must not be advertised as meeting all of R6 yet. Keeping
today's scan alone also fails T1's fixed drive after a large delete. Merely reverting P8 is not a
finished solution.

For a small, uniform K on dead klongs, do explicit compaction on a reclaim pass, rather than waiting
for splits to propagate up a chain. A reduced P3 can copy touched nodes' current entries under new
ids, retain the old tree for old readers, and store the range needed to repeat the operation at
startup. UP already supplies the left-bound rule, so that pass need not include P3's relabelling or
sibling merging. It needs an honest work budget and all the rerun checks. It is additional work, not
an already gated solution.

I do not see a verified smaller design that meets every R as written. The simplest release scope is
a bounded index and cache allowance with explicit limits, after fixing progress. If "no thing of an
ended version after a small K" remains mandatory, compaction and container shrinking are correctness
work for that contract. Calling them efficiencies hides the choice.

### 4.4 The full set: now, later or never

| Part                  | When  | Reason |
|---|---|---|
| F1 merges         | Later | Bounded underfill is accepted; fix progress first.                 |
| F2 top-node (a)   | Now   | Honour Z13; close the window with its model/startup rules.         |
| F3 (b')           | Later | Logical argument is good; physical proofs and gates are missing.   |
| F4 replaced queue | Later | Default off; measure historical reloads and queue capacity.        |
| F5 maintain()     | Later | Useful optional API; fix its bounds, clock and cut progress first. |
| Withdrawn (b)     | Never | It loses retained history after restart.                           |

(a) is needed for the promised window repair, not for lookup safety under today's Rule A. The queue
is not needed to release dead objects after cuts. `maintain()` is needed if its explicit convergence
promise is shipped, but ordinary writes must suffice. Merges are needed for a live-size shape
guarantee, not R9's bound with H in the old shape. Keep SE if already approved: it is small and
preserves routing. It is separable from cleanup correctness. Leave (b')'s extra durable metadata out
of the first integration.

## 5. Risk for 2026.4 and the missing gates

The proposed combined gates are extensive. They are necessary, not sufficient for the resource
claims. A cut-safety checker can pass a run that never cuts. Total object counts can pass while
backing arrays remain large. Byte equality can pass an algorithm with the same unbounded work on
both sides. A new expected digest cannot validate itself.

Add these specific cases to 023-07, section 6.2:

1. The constant-size, batched FIFO below a permanent maximum. Vary batch bytes around 16 kB; restart
   while it is stuck; require actual completed iterations and advancing cuts. Repeat with random
   ranges, long keys, merges and every eviction schedule.
2. Bulk appends beyond E during an iteration. Bound the final step's followed nodes, dirtied bytes
   and record, not just its scan. `ReclaimTail` is a small reproduction.
3. Track identified old entries and node ids across cuts, at several heights. C11's value walker
   alone misses routing klongs, bitmap bits and repeatedly copied histories.
4. Fill and empty a cache with a large budget, without restarting. Measure map/queue/path capacities
   and total heap, alongside Residents. Include budget decreases and delayed cuts.
5. Fixed take-back, full-parent, zero-key split and root-of-tt cases. Check every pointer, including
   deleted/shadowed ones, and rerun ids. Prove or exercise X5(c).
6. Check `dirtyNodeBound` against actual newly dirty nodes before the take removes them. Include
   mixed large puts/deletes, many new roots, long keys and sizes 8, 14, 30 and 62. A delete-only
   probe does not check the new-root allowance in mixed transactions.
7. Keep the withdrawn-rule counterexample. For (a), compare D lists after every restart and exercise
   record-limit truncation. For (b'), compare stored and reconstructed r/e.
8. Keep each corruption test's original fault, found at its new structural location. Also test
   old/new format refusal on real files, with a torn last record.
9. For maintain(), start after an idle clock gap, with a dirty transaction larger than 1 MiB, with
   no new user writes, and while a meta block or durable cut is pending.
10. Run cold startup at 50 MB for a section dominated by cheap deletes, including siblings with
    merges. Run the ratchet test across repeated bursts and restarts, not one drive.

Performance risks are extra sibling loads, replay reads per section byte, repeated root and merge
descents, top-node pulls, and old-time reloads from the queue. `collapseRoot` re-descends through
the segment prefix on each collapse; `mergeAfterDelete` re-descends on a cascade. O(H) changed nodes
is not automatically O(H) total work in those prototypes. Keep the path or qualify R11 until
measured. The dead hand checks time between chunks; a map copy and up to 4,096 nodes plus their
values can overshoot 2 ms.

The final format entry must name all allocation/rerun rules and the precise gd semantics. Adding (a)
later can preserve new-reader compatibility with old streams. It is not transparent to an older
reader that reconstructs D by the old rule. Distinguish syntax compatibility from semantic
compatibility; use a version/capability refusal where needed. (b') changes entry width and must
never depend on a runtime switch in a released format.

SE's integration list also omits its 19-line change to `Db.newGetMany`, `Db.getMany` and TestHooks.
Include that code, as well as GetMany, Dag and the Pub scans.

For C, share deterministic fixtures for delete batches, transient id gaps, root collapse, merges, E,
iteration state and (a)'s gd filtering. Port the final scanner, not just the changed lookup tree.
Java/C byte identity must be re-established at the final pin. The line estimates in 023-07 are
planning estimates, not evidence of a small port.

## 6. Claims that need correction or qualification

1. **"The stream back to the live data after R"**, 023-07, sections 1 and 3.2: false as a general
   claim. The queue in section 2.6 never cuts. Even ordinary convergence waits for write volume,
   pSafe, retention and recovery metadata, not R alone.
2. **"What it leaves, all bounded"**, sections 1 and 3.2: name the bound. Sparse paths have the
   accepted live-keys-times-old-height allowance; the top window has no demonstrated twin allowance
   or ratchet result on P8. Peak cache capacity is omitted altogether.
3. **R2, R3, R5 and R7 marked as met**, section 3.2: unlinking empty subtrees does not remove every
   dead klong. The 700-cut result contradicts an approximately B-iteration bound for the core. State
   partial conformance or add a compaction deadline.
4. **"Memory released after each cut"**, section 1: only after a later hand round, only detachable
   objects, with reloading and noEvict exceptions. Hash table arrays remain. P6, section 4.4
   explicitly reports the missing shrink patch.
5. **T1 and "strict"**, sections 3.2 and 4: P8's three 1M rows support the listed criteria, not
   complete T1: C11 is absent. P5's 390 versus 270 fails strict a_n = 10. A 1.44 ratio can be a
   sensible new target, but is not the test's old strict allowance.
6. **The allowances**, section 3.2: 023-03 defines bounded a_n = 10 + L h_fill. P7/P8 commonly used
   10 + h_fill; other comparisons used fixed L = 4. Keep the actual L and the historical used
   allowance separate. The observed counts stand; the labels need care.
7. **"The window closed at every N"**, section 4: distinguish the top-window result from C9 passing.
   P7, section 7 reports a C9 miss at N = 1,000 with (a), and a one-object miss at 1M with (a)+(b').
   Relaxing phase tolerances is a contract change, not a rerun gate.
8. **The full-set take of at most 1 MiB**, sections 4 and 5.13: contradicted by P3's `TransSeq.take`
   first-transaction exception. A much larger dirty batch can be taken.
9. **Each step's bound**, section 5.5: the scan reserve does not bound the final touch. The
   81,018-node step is concrete. Setting `GetMany.endKey` on the scan alone cannot fix it.
10. **No Lean change**, for the core: reasonable only after the net transient-node conditions and
    physical cut assumptions hold. It does not prove T-SCHEME, Java concurrency, cleanup delay,
    startup cost or scan complexity. For (a)/(b'), the missing model and proof work is substantive;
    passing other branches' gates cannot supply it.

I checked the main numerical examples against the reports: P4's 4,036 versus 270, P5's 390 versus
270, P6's 292/263 object comparison, P8's 85.0/68.4 MB and 5.5/13.9 MB, and the P7 counterexample
are represented faithfully. These figures do not establish combined costs, cleanup deadlines or
integration time.

## Questions for Frans

1. **Keep the release paused for the queue and final touch?** Yes. They affect the promised cleanup
   driver. Fix and gate them before release.
2. **Require a fixed small K for each old entry and container capacity?** Keep the literal rule
   unless you explicitly accept an allowance. Neither tier currently meets it.
3. **Must merges ship now?** Defer under the accepted bounded-shape choice. If live-size shape is
   required now, include them; later merges need another format/versioned rerun.
4. **Keep Z13, closing the top window now?** Yes: (a), its startup rule and R24 work. Keep today's
   still-dirty test. Defer (b') and the queue.
5. **Test marking only rewrite paths first?** Yes, with the physical cut argument and targeted
   gates. It removes the large tail walk, but leaves progress and compaction open.
6. **Ship maintain() now?** Later, unless optional idle convergence is a release condition. If
   shipped, test the large-first-batch, clock, metadata and durability waits.
