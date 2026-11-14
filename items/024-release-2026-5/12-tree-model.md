# 024-12. The tree model: BergDB's key tree in Lean, run against Java

Created 2026-11-11 by Frans Lundberg. Status: open: on `main` since
`b84cf761`; the proofs go on (section 6: TP7, TP10, TP11; the second
prover's run 4 from 2026-11-13, 07:54).

The main step towards aim 4 of release 2026.5 (024-04, "the model
matches"): the key tree of release 2026.4 (`Dag`, `KeyNode`, `GetMany`,
`TopDs`) as a Lean definition that can be run, the trace format that
carries what it needs (B0 of 024-06, section 5.1), the definition itself
with its stated properties (B1), and the checker that runs it against
Java's traces (B2). Frans's order of 2026-11-11: model first; a design
note, then a Lean definition that runs, with its invariants and bounds
stated, then runs against small cases and Java, and the proofs when the
algorithm has settled. The proofs (C1 to C3 of 024-06) are not this
subitem's work.

Cite the design rules as "024-12, D1", the stated properties as
"024-12, TP1", the differences found as "024-12, F1".


## 1. In short

Kept current; section 9 has the exact state. Written 12:24.

* **The branch is gated and ready to land:** `024-12-tree-model`, head
  `d90586d0`, main with 024-07, 024-10, 024-13 and 024-09 merged in
  (section 7).
* **The tree of release 2026.4, with 024-07's touch and 024-10's
  builder rule, is in Lean and runs** (`lean/SIS/Tree/`, about 2,400
  lines of definitions and statements): a key node as its klongs, the
  six searches, get, scan with the end key, put with the five splits,
  delete with the upward unlink, LE-b, the take-back and root collapse,
  the top node and the search through its skip pointers, a reclaim
  step's touch, `Dag.dirtyNodeBound`. `Tree.exec` is a function of the
  transaction, its time and P@(i-1), and `treeSpec` an instance of the
  existing `Spec`: no line of the existing model or its proofs changed.
  `BVal`, `bptrs` and `blive` moved from the checker
  (`Check/Trace.lean`) to a file of the model, with their names.
* **The model gives Java's change exactly.** On 115 traces (25,169
  transactions, 192,496 operations): every node made with its id, level
  and kind, every entry, every klong of every changed key node; every
  noop; 100,676 gets and 25,169 scans; 624 touches of reclaim's steps.
  And on 9 larger traces, to node size 62 (before the merges).
* **The whole model runs on the tree, alone, and writes Java's
  records** (C-T9, section 5.5): `init` and `step` of the existing
  model with the tree's `exec`, from R(0), given only each
  transaction's operations, first id and Java's startup pos, give every
  record (versions with histories and references, gd, top) and D of
  Java's run: 25,284 records on the 115 traces, none different.
* **No difference of Java's found.** Two of the model's, both fixed
  (5.3): a time klong that no klong follows (D4), and the bound of a
  transaction without operations.
* **Every rule of the writer is reached** by the draining set, the
  rarest 3 times (section 5.2); the small set of `conformance.sh`
  reaches the take-back 9 times in 35 traces.
* **27 properties are stated** as `Prop` definitions (section 6): the
  invariants, the multiversion map, the assumptions C1 needs, the
  bounds (with a transaction's limits as hypotheses, 024-17), and I2,
  T-COVER's premise since 024-07. The computable ones hold on Java's
  tree after every traced transaction and on 340,276 states of small
  cases (exhaustive at node sizes 4, 6 and 8; section 4.3). **Proved,
  as they fell out:** TP13 (`SpecOK`, with 024-09's lemma on `blive`),
  TP17 (`ExecRootOK`), TP18 (`VirtLiveOK`) and that the model's run has
  the tree's P.
* **The existing model's own tests pass on the tree, in Lean alone**
  (4.3): on 35 pseudo-random runs of `SIS.run (treeSpec)`, every
  transaction meets `StepOK`, TREE, A6' and A-COPY, and T1 (startup from
  the stream) and T2 (restarts) hold.
* **Five things the model had to copy that look unintended in Java**
  (section 5.4), none a fault: a wasted klong in the primordial key node
  and in an emptied root; two dead tests in the searches; a search with
  another tie rule, used by no code; a depth that is not the node's.
* **Not done:** the proofs but the four small ones (by the brief, and
  the coordinator's word of 08:50); 024-11's merge in the model;
  `treeconf.sh large`; Java against the model on keys of raw bytes
  (section 9).


## 2. The design note

### 2.1 What is modelled

The Core's algorithm on keys, as release 2026.4 runs it:

| Java                                         | In the model                  |
|---|---|
| `KeyNode`: the klongs, the six searches      | `KNode`, `searchEq` and so on |
| `KeyNode.lastVersion`, `firstAndSecond`      | `lastVersion`, `halves`       |
| `Dag.getOne`, `getEqNodeInSegment`           | `get`                         |
| `Dag.putKv`, `setValue`, `setNode`           | `putKv`                       |
| `appendKlongs`, `handleFullNode`, the splits | `appendKlongs`                |
| `deleteUpward`, `appendDeleteKlong` (UP)     | `deleteUpward`                |
| `emptyKeyNext` (LE-b)                        | `emptyKeyNext`                |
| `takeBack`, `retarget`, `takeBackRoot`       | the same names                |
| `collapseRoot`, `replaceRoot` (RC)           | the same names                |
| `TopDs.newSuperRoot`, `findRoot`             | `newSuperRoot`, `rootAt`      |
| `GetMany.Chain` (setup, next, the end key)   | `scan`                        |
| `Db.putKvs`: the operations in order         | `exec`                        |
| `Db.sortByKey`, `Trans.Builder.build`        | `normalize`, `Tx.sorted`      |
| `Db.touchPaths`, `Dag.followPath` (024-07)   | `touchOf`, `pathFrom`         |
| `Dag.dirtyNodeBound`                         | `dirtyNodeBound`              |

This is the algorithm in the 5,215 lines that 024-06 counts; the rest of
them is tests, printing, concurrency and the pointer forms (2.4).

### 2.2 The state

**D1. The state is P, the existing model's structure, with no new
field.** A node of P is its id, its level, whether it is a data node,
and its history: entries, each a time and a value (`SIS.Node`,
`Check.BVal`: `K c y`, `D cs`, `R y`, `S j z`, `T z`, `V h`;
docs/trace-format.md, section 1). The tree's `exec` gets P@(i-1) as the
existing `View`, and returns `Changes`: the nodes made and the entries
added at time i. So the tree is a value of `Spec BVal Tx`, and every
existing theorem speaks about it once its assumptions are proved (2.5).

**D2. Inside `exec`, a key node is its klongs, exactly as Java has
them.** `KNode`: whether it is a segment leaf, and a list of klongs,
each one of

* `time t`: a time klong; t is the model's time, the record's index;
* `key c y`: a key klong with compare value c, and its pointer, which
  names node y (a key node or a value);
* `del bits`: a delete bitmap, the indexes of the klongs it deletes,
  cumulative as in Java (a new bitmap holds the bits of the one before).

A node's size, on which every split decision rests, is the length of
this list, time klongs and bitmaps included.

**D3. `klongsOf` reads the klongs back from a history; `entriesOf` is
its inverse.** The exporter's α (`TraceExport.keyEntries`) written in
Lean, both ways: a run of entries with one time is a time klong and the
klongs of the entries; a `D cs` entry is a bitmap with the bits of the
bitmap before it and of every key klong before it whose compare value is
in cs. The exporter writes cs as the compare values of the new bits, so
the two agree as long as a bitmap holds, for each of its compare
values, the bits of all klongs of it before the bitmap; Java makes
bitmaps only so (`Dag.bitsOf`), and the checker compares the klongs
themselves (2.7), so a bitmap of another kind is found.

**D4. A time klong that no klong follows is an entry of the model: the
marker.** Java has key nodes that are one time klong and nothing else:
the primordial key node (`KeyNode.nodeWithTime`), and a space root that
a delete emptied by a time split (`appendDeleteKlong` on a full segment
leaf whose last version is empty: `[T tt]`). The klong stays in front
when the node gets klongs later (`[T 0, T 1, K ...]`), so the node is
one klong larger than its entries say, for good, and its splits come one
klong earlier. The exporter writes no entry for it. Rule: in the model's
P such a time klong is an entry at its time, a delete entry without
compare values (`SIS.Tree.marker`); `klongsOf` reads it as the time
klong alone, `entriesOf` writes it for a time klong that no klong
follows. Klongs and histories then correspond one to one, with the true
times. `blive` ignores it (it deletes nothing), and it has no pointer.
The tree checker adds it to a key node that a trace makes without
entries, and leaves markers out when it compares entries (2.7); the
comparison of klongs covers the klong itself. (First written here as "a
key node with an empty history is `[time 0]`, but the primordial one,
which has no klong": wrong on both counts, found by the first run of the
checker, T(1) of the first trace.)

**D5. Whether a key node is a segment leaf, its segment and its height
are read from its level.** The exporter gives a key node the level
1 + (G - g)(H + 1) + h, with g its segment (0 for the first), h its
height in its segment tree (0 for a segment leaf), and G and H the
largest of the run (`TraceExport.levelOf`). The model takes G and H as
parameters and gives a new node its level by the same formula: a half or
a last version gets its node's g and h, a new root h + 1, a new segment
leaf below a leaf g + 1 and h = 0. A top node's level gives its ordinal
(level = keyMax + 1 + ordinal). So A4 (pointers go to lower levels)
holds for runs within G and H, and for no others: a statement about
bounded runs, as the checker's has been since 011-11, section 8.4.

**D6. The top of the tree.** The root (id 0) has an entry `T z` for
each top node z; a top node has `R y`, its root key node, and `S j z'`,
its skip pointers; all of a top node's entries have its root time. The
super root is the top node of the root's last entry. The model's time
is the record index, so "the top node at time t" is the root's last
entry with a time at most t.

**D7. The writer's state within a transaction** (`W`): the overlay (the
key nodes read, made or changed so far, as klongs, by id), the next id,
the nodes made, in order, with their levels, the map from a node made
by a split to the node it replaces (`PutData.madeFor`), the nodes taken
back, the key access path of the operation (`KeyAccessPath`: pairs of a
compare value and a node), the super root (its id, ordinal, root time,
root key node and skip pointers) and the values made. A node that
existed before and is replaced or unlinked gets its klongs of before
the transaction back (`toPreviousState`), so it adds nothing. At the
end, `Changes` is read off: the nodes made and not taken back, sorted
by id, and for every node of the overlay its entries of time i, sorted
by node id, as the exporter writes NEW and ADD lines.

**D8. Ids.** Java gives a transaction's nodes the ids p + 1, p + 3 and
so on, p the position of its record (`Db.begin`: `nextVpos`), in the
order of `setIdOfNode`'s calls: a put's value first; a split's halves,
then its new root, then the new top node; a time split's last version
when the split is known to be a time split; a delete's marker last,
which uses an id and is no node. The model's transaction carries the
first id (`Tx.base`) and makes ids in the same order, a taken-back
node's id used up. That the bases are far enough apart is an assumption
on the run (TP list, `BasesOK`), true in Java as records have positive
length.

### 2.3 The operations

Each is the Java method's rule, case by case; the names are 2.1's. In
words, what each does and when:

* **search** (six: Eq, Lte, Lt, Gt, Gte, First) at a time t in one
  node: over the klongs before the first time klong after t, a key
  klong counts unless the last bitmap at or before t deletes it (for
  `searchEq`: the bitmaps in order, as Java's loop); among klongs of one
  compare value the last wins.
* **get** of a key at time t: the top node at t, its root, then per
  segment `searchLte` down to the segment leaf and `searchEq` in it;
  the last segment's pointee is the value.
* **put** of a key and a value, by the writer at time i: the value is
  made (an id); per segment, down to the leaf (`searchLte`; no klong at
  or below the key is an error: LE-b says there is one); a missing
  segment gets a new segment leaf and a klong to it; the klong is added
  if the node has room for it and a time klong (size + 1 < M), else the
  node is full (`appendKlongs`).
* **a full node** (`handleFullNode`): its last version at i is made
  (the live klongs, sorted, one a compare value). More than M/2 klongs:
  a **space split** into two halves, the klongs to add going to the half
  of their compare value; an inner node's second half gets the empty key
  as its first klong (LE-b). Else a **time split**: the last version
  with the klongs to add replaces the node. A node that the transaction
  made is changed in place (it keeps the first half, or becomes its last
  version); one that existed is replaced, loses its klongs of i, and its
  parent gets the klongs of what replaces it, which may fill the
  parent: the same rule one level up. A split root gets a new root
  above its halves, with the empty key and the second half's klong; the
  space root's goes into the top node of i (a new one, or the one the
  transaction made already), a segment root's into the segment leaf
  above: a klong of the same compare value, or, for a segment root made
  and split in the same transaction, the leaf's klong of i pointed to
  the new root in place (fault 12's fix).
* **delete** of a key (`deleteUpward`): no live klong of it: nothing
  (a noop makes no node and no entry). The leaf keeps a live key: a
  bitmap in the leaf (the transaction's own last bitmap gets the bit in
  place). Else **UP**: climb while the node above would be left without
  a live klong; nothing changes until the stop node is known. Each node
  below it on the path: one that the transaction made by a split is
  **taken back** (its parent's klongs of i that name it, deleted ones
  too, name again the node it replaced; it is no node of the
  transaction), one made otherwise is an error (one operation a key
  excludes it), an older one is **unlinked** (it loses its klongs of
  i). The stop node gets the bitmap; if the klong to delete is the empty
  key's (**LE-b**, `emptyKeyNext`): the empty key gets the pointer of
  the next live klong, by a new klong or in place if its klong is of i,
  and that next klong's compare value is deleted instead. Then **RC**:
  while the root of the stop node's tree is an inner node with one live
  klong, its child takes its place: through the top node (space root),
  through a klong in the segment leaf above (segment root), or by
  pointing the klong of i in place when the root was made by a split of
  the transaction, which is then taken back.
* **a transaction** (`exec`): the touch first, if any (it changes
  nothing; it gives `Changes.touch`), then the operations in the order
  given, each as above. `Tx.sorted`: the keys strictly increasing, so
  one operation a key; `normalize` is `sortByKey`'s rule (the last put,
  or a delete if there is none) and gives a sorted transaction.
* **scan** (`GetMany.Chain`): the chain of nodes and compare values;
  setup from the start key; next by `searchGt` or `searchLt` in the last
  link, down through `searchFirst` order, up when a node is exhausted;
  forward it ends when the klong found is past the end key
  (`isPastEnd`), before following it.
* **the touch** (reclaim's part, as far as the tree is concerned).
  Since 024-07 landed (10:07): `Db.touchPaths`, the index nodes on the
  paths of the transaction's own keys at time i, before the operations:
  the super root, the space root, and per key what `Dag.followPath`
  follows (`searchLte` down each segment tree, `searchEq` in a segment
  leaf to the next segment's tree; not the value). `Tx.touch` is the
  list of those keys, empty for a transaction without a touch. Until
  then, and in the runs of sections 5 and 7 made before 10:07, it was
  `Db.touchRange`: the nodes that a forward scan from `from`
  (exclusive) to the first key after `to` follows. The reclaim step's
  rewrites are puts like any other, and are in its operations.
* **`dirtyNodeBound`**: Java's count, on the model's nodes, for C3.

### 2.4 What is abstracted away, and why

| Left out                                   | Why it can be                          |
|---|---|
| Bytes: the klong's bits, key bytes         | a segment is its compare value, a Nat  |
| Values                                     | a hash, as in the trace                |
| Array capacities, `lastTimeIndex`          | no rule reads them                     |
| Pointer forms, handles, references         | Phys.lean and Handle.lean have them    |
| Readers beside the writer, monitors        | no threads in the model (024-06, 3.3)  |
| Listeners, marking, `opChanged`            | the model marks by `marked` (T13)      |
| The quiet follows of RC                    | they only stop marks                   |
| Key and value transformations, the STM     | T(i) is the operations as applied      |
| The skip list's search                     | D6: the last top node at or before t   |
| The cycle check, statistics, printing      | not part of the algorithm              |
| The 62-bit limit of a bitmap               | M is at most 62; a stated assumption   |

* **A compare value is a natural number**, ordered as numbers. Its low
  bits hold the segment's length; the model uses that only as Java does:
  a segment of 7 bytes (`long c`) continues in the next segment's tree,
  any other is a key's last. `Key.wf`: every segment but the last is
  long, the last is not, as `Keys.toSegments` makes them.
* **Java's `Bug` and "corrupt data" exceptions** are errors of the
  model: `exec` returns no changes, `exec?` a text that starts with its
  kind: `Bug:` (a state that `Dag` excludes), `corrupt:` (a P that is no
  tree of BergDB's), `bounds:` (the tree left G or H). The checker
  reports any.
* **The skip pointers are kept** (they are entries of a top node, and
  R4 of the existing model needs them); only the search through them is
  replaced by its specification. It can be added later as a definition
  with a statement that it finds the same node.

### 2.5 How it fits under the existing model

`treeSpec M G H : Spec BVal Tx` with `ptrs := bptrs`, `live := blive`
(the checker's, moved or restated in the model), `exec := Tree.exec`,
`virt := true`, `rootVal := .top`, and `init` the primordial structure
(the root, one top node, one empty key node). `SIS.step` then runs BergDB
whole: the tree makes the change, the existing model the record and D.

What C1 (024-06, section 5.1) has to prove of it, each stated in
section 6 as a `Prop`:

| Assumption (024-06, 2.4)              | For the tree                          |
|---|---|
| `SpecOK`, `VirtInit`                  | of `blive`, `bptrs`, `init`: small    |
| `StepOK.fresh`, `distinct`            | from D8 and `BasesOK`                 |
| `current` (A2), `newReachable` (A3)   | splits in place, the take-back        |
| `dataFixed`, `dataNoPtrs`             | values get one entry                  |
| `levels` (A4)                         | D5, within G and H                    |
| `noRes` (A5)                          | no klong names an older dead node     |
| `VirtStep` (R1 to R4, `dead`)         | `newSuperRoot`'s rule                 |
| the touch (`touchUp` and two more)    | the scan walks down from the root     |
| `PhysStep` (`liveNew`, `adopt`)       | of `blive`; TREE and A5               |
| TREE, A6', A-COPY (`EvictRunOK`)      | one live parent; fault 12's fix       |
| `ExecRootOK`, `VirtLiveOK`            | `exec` reads the root by its children |
| A1                                    | holds by type, with D4's rule         |

Not the tree's: `PolicyCutOK`, `CutOK`, the take (024-06, 2.4, last
three rows). A1 needs one more statement, that `exec` reads only nodes
reachable at i-1 (it starts at the root and follows live pointers), so
that the checker may give it P itself for P@(i-1).

### 2.6 The trace: format 3 (B0)

`TRACE 3` is format 2 with these lines more; the exporter writes them
with the property `tree=1`, and `tracecheck` reads over them, so one
trace serves both checkers.

    TREE m g h k                 after CONFIG: the node size M, the level
                                 bounds G and H (D5), the primordial key
                                 node's id
    BASE b                       in TX i, first: the id of the first node
                                 that T(i) makes (D8)
    OP P n c1 ... cn h           in TX i, after BASE, in the order the Dag
                                 got them: a put of the key with segments
                                 c1 ... cn, the value's hash h
    OP D n c1 ... cn             a delete that deleted
    OP N n c1 ... cn             a delete that was a noop
    (RANGEF, RANGET              the bounds of a touch's key range: only
                                 until 024-07 landed; a transaction with
                                 a TOUCH line now touches the paths of
                                 all its OP keys)
    KN x l n k1 ... kn           in TX i, after the ADD lines: key node x
                                 after T(i), for each key node that T(i)
                                 made or gave an entry: l is 1 for a
                                 segment leaf; the n klongs, each `T t`,
                                 `K c y` or `B b` (b the bitmap's 62 bits
                                 as a number)
    GET t n c1 ... cn r          in TX i, after KN: Java's getOne of the
                                 key at model time t gave the value with
                                 hash r, or `-` for none
    SCAN t d a b n start end r kv1 ... kvr
                                 Java's getMany at model time t: forward
                                 or backward, the start and end keys and
                                 whether each is inclusive, the limit,
                                 and the r KVs it gave

`OP` lines come from a new test hook in `Db.putKvs`, called before each
`dag.putKv`, and `valueNodeCreated`, which tells a noop from a delete
that deleted. T(i) for the model is the P and D lines: what the record
stores and the rerun applies. `OP N` is not part of it; the checker
checks that the model's delete changes nothing there.

### 2.7 What the checker compares (B2)

A new program, `treecheck` (its own root file and `Check/Tree.lean`), so
that `tracecheck` and its scripts stay as they are. For each `TX i` of a
format 3 trace, with P the structure of the trace so far:

* **C-T1**, the change: `Tree.exec` of the P and D operations, from P,
  equals the trace's change, NEW and ADD lines, lists compared as they
  stand: every node made with its id, level and kind, every entry.
* **C-T2**, the klongs: each KN line equals the model's node, klong by
  klong (sizes, bitmaps by index, the lone time klong of D4).
* **C-T3**, the noops: at each `OP N`, the model's delete is a noop.
* **C-T4**, the reads: each GET line is the model's `get`; each SCAN
  line the model's `scan`; a reference map kept by the checker (key to
  the list of its puts and deletes) gives the same answers as both.
* **C-T5**, the touch: the TOUCH line is `touchOf`.
* **C-T6**, the stated invariants that can be computed, on the model's
  state after each transaction (section 6).
* **C-T7**, `Tx.sorted` and `Key.wf` of each transaction; no error of
  the model.

A new script, `java/stress/treeconf.sh`, exports with `tree=1` and runs
`treecheck`: `conformance.sh`'s small set, the draining configurations
and UnlinkFuzz's workloads; one new step in `level2.sh` calls it. A
difference is a finding (section 5).

### 2.8 Where the planned changes land

* **The last touch (024-07):** `touchOf`, one definition; the scheme
  that chooses a step's keys is not in this model (D1 of 024-06).
  **Done on 2026-11-11, 10:10**, when 024-07 was on main: `touchOf`
  went from a scan of a key range to `pathFrom` over the transaction's
  keys (30 lines of `Read.lean`), `Tx.touch` from two bounds to a list
  of keys, and two trace lines went; nothing else of the model moved.
* **The underfill fix (024-11), merges or other:** `deleteUpward`'s
  stop rule and the step after it, where RC stands now; `halves` if the
  fill rule changes. `dirtyNodeBound` with it. 024-11, section 5, states
  the merge in this model's terms: its `fix` takes the place of the
  steps after `climb` in `deleteUpward` (`collapseRoot` is its F1), its
  `merge` is a new definition beside `takeBack`, its rule O is
  `handleFullWith` unchanged, and its invariant V1 (at least m live
  klongs) is a line more in `walk` beside `NonEmptyOK`. The checker and
  `treetest` then run it as they run today's.
* **A new record format, one rerun path:** nothing here, unless the
  record stops storing what `Tx` holds. D4's rule goes if a node of one
  time klong is no longer made.
* **"The last operation wins" (024-10):** `normalize`, one definition.
  **Done** with the merge of main at 10:10 (and `ruleFor` of TP25).
  024-16 (one operation a key, strict: a transaction whose key
  transformations make two keys one fails at the commit) needs no
  change: the Dag gets one operation a key either way (`Tx.sorted`).
* **Fixed limits of a transaction (024-17, in discussion):** `Limits`
  (the most operations, the most segments of a key), `Tx.within`, and
  TP26, which bounds `dirtyNodeBound` by the limits alone; a limit on
  value sizes is not the tree's.

### 2.9 Decisions taken here, and why

* **D1 against a state of its own for the tree** (a map of klong
  nodes): with its own state the tree would be a second model beside
  the first, tied to it by a proof that does not exist. As an instance
  of `Spec`, T1 to T12 wait only for C1.
* **D2 against a tree on entries only:** the size of a node decides
  every split, and entries do not give it in D4's case; index bitmaps
  are what `Dag` computes with. Entries would be a model near Java's,
  not Java's.
* **Format 3 is opt-in** (`tree=1`) and `treecheck` a program of its
  own: 024-09 changes `conformance.sh` and maybe the checker today;
  new files merge without conflict. One step and one accepted version
  number are the only shared lines.
* **The proofs' form:** unproved statements are `def ... : Prop`, named
  and listed in section 6; no `sorry`, no axiom.


## 3. B0: the trace format 3

Done; docs/trace-format.md, section 4, is its description.

* **The exporter** (`java/stress/TraceExport.java`, property `tree=1`)
  writes `TRACE 3`: format 2 and the lines TREE, BASE, OP, KN, GET and
  SCAN (and, until 024-07 landed, RANGEF and RANGET, the bounds of a
  touch's key range). Without `tree=1` a trace is format 2,
  byte for byte as before: the reads of the GET and SCAN lines use a
  generator of their own.
* **One line of `src` changed:** `Db.putKvs` calls a new test hook,
  `Db.TestHooks.kvApplied(key, value)`, before each `dag.putKv`; a
  default method, so no other implementer changes. With
  `valueNodeCreated` it tells a delete that deleted (`OP D`) from a noop
  (`OP N`).
* **T(i) for the model** is the P and D lines, the operations the record
  stores and a rerun applies, in the order the Dag got them; and BASE,
  the first id, the record's position plus 2 in model ids.
* **KN lines** give every key node that T(i) made or gave an entry, as
  its klongs: this is what makes the comparison exact (bitmaps by index,
  sizes, the lone time klong), where the ADD lines give entries.
* **Two workload shapes** of UnlinkFuzz in the exporter: `shape=fifo` and
  `shape=long3` (keys of 1 to 5 segments with shared prefixes).
* **`tracecheck` reads over the new lines** (8 cases in
  `Check/Trace.lean`'s `parseLine`), so one trace serves both checkers.
* **Differs from 2.6 as first written:** a klong on a KN line is two or
  three tokens (`T t`, `K c y`, `B b`), not one; SCAN's form.


## 4. B1: the tree in Lean

### 4.1 The files

| File in `lean/`          | Lines | What it has                                |
|---|---|---|
| SIS/Tree/Val.lean        | 63    | `BVal`, `bptrs`, `blive`, moved, unchanged |
| SIS/Tree/Node.lean       | 380   | D2 to D5: klongs, levels, the searches,    |
|                          |       | last version, halves, `klongsOf`, marker   |
| SIS/Tree/Exec.lean       | 822   | the writer: put, splits, delete, UP, LE-b, |
|                          |       | take-back, RC, the top node; `exec?`       |
| SIS/Tree/Read.lean       | 278   | `get`, the scan's chain, `scan`, `touchOf` |
| SIS/Tree/Spec.lean       | 70    | `exec`, `initStruct`, `treeSpec`,          |
|                          |       | `normalize`, `Tx.sorted`                   |
| SIS/Tree/Inv.lean        | 154   | the invariants as a walk, `faultsAt`       |
| SIS/Tree/Props.lean      | 297   | TP1 to TP22 and TP25, `Prop` definitions   |
| SIS/Tree/Bound.lean      | 211   | `dirtyNodeBound`, TP23                     |
| SIS/Tree/Top.lean        | 82    | the skip pointers' search, TP24            |
| SIS/Proof/TreeRoot.lean  | 169   | the proofs of TP17 and TP18                |
| SIS/Proof/TreeInit.lean  | 171   | the proofs of TP13 (but `liveSub`) and of  |
|                          |       | `RunPSame`                                 |
| Check/Tree.lean          | 347   | format 3's lines; C-T1 to C-T8             |
| Check/TreeRun.lean       | 92    | C-T9, the whole run                        |
| TreeCheck.lean           | 153   | `lake exe treecheck`                       |
| TreeTest.lean            | 372   | `lake exe treetest`: the small cases       |

Each definition's comment names the Java method it restates. Where
Java's loop has an order the fold has the same, and the steps that make
a node id come in Java's order (D8).

### 4.2 What differs from the design note

* **D4**: rewritten above; the marker entry.
* **The writer is a state monad** (`M`: a reader of the parameters, the
  time and P@(i-1); the state `W`; an error text). `appendKlongs` recurs
  on the depth in the key access path; the descents and root collapse
  have a fuel, (G + 1)(H + 2) + 2, and end in a `bounds:` error past it.
* **A new key node outside G and H is an error** (`bounds:`), so that a
  run within reach has levels that meet A4 (D5), and "within reach" has a
  definition (`Within`, section 6).
* **`W.trail`** notes which rules ran, for the counts of 5.2; no rule
  reads it.
* **`scan` and `touchOf` have a fuel of 2^40 steps**, which no run
  reaches: the scan's chain goes up and down, and no measure of the
  model's P bounds it without a proof.
* **The writer has no root in its view.** `runOps` and `touchOf` take
  the top node of the root's last entry (`lastTop`) and give the writer
  P@(i-1) without the root (`rootless`); a klong that names the root, a
  top node or a value where a key node is due is a `corrupt:` error.
  Java's writer starts at `TopDs.superRoot` the same way. This shape
  makes `ExecRootOK` (TP17) a proof of twenty lines; before it, a view
  with a klong to node 0 would have broken the statement.
* **D6's search is modelled after all** (`Top.lean`,
  `findSuperRootAt`), at a record's time and between two records; the
  readers keep `topAt`, and TP24 says the two agree.

### 4.3 The small cases, in Lean alone

`lake exe treetest` (`java/stress/tree-tests.sh`; 10 min 57 s on one
core for the exhaustive and random runs below). Keys: the empty key,
keys of one segment, keys of two segments below a long first one.

**Exhaustive:** every sequence of transactions to a depth, each one
operation (a put or a delete of one of the keys) or, with "pairs", one
or two operations on two keys; from the primordial structure, or from a
tree that a prefix built (every key put: in one transaction, each in
its own, or both). After every transaction: the invariants (`faultsAt`),
pointers to nodes of P, every key's get at every time against the
reference map, scans against it (from every key and from none, forward
and backward, inclusive and not, and to every end key; at two times,
with two limits), a noop delete, the skip pointers' search at every
time, the bounds of TP21 and TP22, and for the first four transactions
`exec` on P@(i-1) against `exec` on P.

| M | Depth | Keys | Prefix          | Pairs | States  | Failures |
|---|---|---|---|---|---|---|
| 4 | 5     | 4    | none            | no    | 37,448  | 0        |
| 6 | 5     | 4    | none            | no    | 37,448  | 0        |
| 8 | 4     | 5    | none            | no    | 11,110  | 0        |
| 4 | 4     | 6    | one transaction | no    | 22,620  | 0        |
| 4 | 4     | 6    | one a key       | no    | 22,620  | 0        |
| 6 | 4     | 7    | one a key       | no    | 41,370  | 0        |
| 6 | 3     | 9    | both            | no    | 6,174   | 0        |
| 8 | 3     | 12   | both            | no    | 14,424  | 0        |
| 4 | 3     | 5    | one a key       | yes   | 127,550 | 0        |
| 6 | 2     | 8    | both            | yes   | 16,512  | 0        |

337,276 states. **Random:** 20 seeds of 150 transactions of up to 6
operations on 14 keys at M = 8, normalized (`normalize`, with TP25's
check): 3,000 states, 0 failures.

* Node sizes 4 and 6 are not Java's; the rules are the same, and small
  nodes reach splits, UP, LE-b, RC and the take-back within 3 or 4
  steps. The run with pairs at M = 4: `up.takeback` 6,121 times,
  `rc.takeback.space` 27,431, `leb.full` 49,273, `up.climb` 70,016,
  `lone-time-klong` 48. The runs of the table reach 27 of the 28 rules
  of 5.2's table; the one missing, `split.space2.inplace` (a segment
  root made and split in one transaction), is reached once by a run
  with pairs at M = 4, depth 2, from six keys (5,256 states, 0
  failures), which joined the default set after the table's run.
* At M = 4 the two prefixes "one transaction" and "one a key" reach the
  same counts to the digit: a node of four klongs is full at every put,
  so every changed node is a last version of one time klong, whatever
  the times before. Checked by hand at depth 1; not a fault of the test.
* A control: with LE-b's bitmap changed to delete the empty key's klongs
  instead of the next child's, a run that does not reach `leb.newklong`
  passes, and `treecheck` fails on the first trace (C-T1, C-T2). So a
  pass of the small cases says only as much as their reach line, which
  each run prints.

**The whole model on the tree** (`treetest model`): `SIS.run` with
`treeSpec`: the existing model's records, D and startup, with the
tree's `exec`, on pseudo-random transactions made before the run (noop
deletes among them). Checked on every transaction, with `tracecheck`'s
own functions: `SpecOK` and `VirtInit` of R(0), `StepOK` with `VirtStep`
(A2 to A5, ids, data nodes, R1 to R4), TREE, A6', A-COPY; that the
model's run has the tree's P; and with BergDB's algorithm (marking,
Java's still-dirty test, the startup pos two records back) **T1**,
startup from the stream gives P and D (every tenth transaction and the
last), and **T2**, the run with a restart after every third transaction
appends the same records. A restart reruns the tree's `exec` from the P
that startup rebuilt from the stream: A1 at work, markers included.

| M | Seeds | Transactions | Keys | Failures | Time   |
|---|---|---|---|---|---|
| 4 | 10    | 40           | 8    | 0        | 6.9 s  |
| 6 | 10    | 50           | 10   | 0        | 1.9 s  |
| 8 | 10    | 60           | 12   | 0        | 2.1 s  |
| 8 | 5     | 120          | 16   | 0        | 35.1 s |

So the theorems' assumptions (TP13, TP14, TP16) and two of their
conclusions hold on these runs of BergDB's tree in Lean, without Java.


## 5. B2: the checker's results, and the differences found

### 5.1 What is compared

`lake exe treecheck TRACE`, for each `TX i` from Java's structure before
it (P built from the trace's own NEW and ADD lines, so a difference does
not carry over to later transactions):

| Check | What                                                         |
|---|---|
| C-T1  | `Tree.exec` of the operations = the NEW and ADD lines, as    |
|       | lists: ids, levels, kinds, entries                           |
| C-T2  | each KN line = the model's node, klong by klong; and = the   |
|       | klongs of the node's history (`klongsOf`, `entriesOf`)       |
| C-T3  | `OP N` is a noop of the model, `OP D` is not                 |
| C-T4  | each GET line = `get`; each SCAN line = `scan`; at each      |
|       | GET's time the skip search finds `topAt`'s top node (TP24)   |
| C-T5  | the TOUCH line = `touchOf`: the paths of the transaction's   |
|       | keys (of RANGEF and RANGET, until 024-07 landed)             |
| C-T6  | `faultsAt` finds no fault in Java's tree after T(i); every   |
|       | pointer of an entry added names a node of P                  |
| C-T7  | keys strictly increasing; keys as `Keys.toSegments` makes    |
|       | them; no error of the model                                  |
| C-T8  | key nodes marked by the change <= `dirtyNodeBound` before    |
|       | it (TP23); nodes made within TP20's bound                    |
| C-T9  | the model's own run from R(0) writes Java's records and      |
|       | keeps Java's D (5.5)                                         |

### 5.2 Results

`java/stress/treeconf.sh all 5` on the clone's head (`0e02cbf0`), 31 s:

| Set     | Traces | Transactions | Operations | Key nodes made | Taken back |
|---|---|---|---|---|---|
| small   | 35     | 3,550        | 20,129     | 10,158         | 9          |
| drain   | 55     | 6,950        | 126,418    | 50,102         | 279        |
| reclaim | 25     | 14,531       | 44,734     | 13,824         | 1          |
| all     | 115    | 25,031       | 191,281    | 74,084         | 289        |

* **Failures: 0 in every check**, C-T1 to C-T9; exporter errors 0.
  (C-T9 from the same sets run again at `dd271920`, on one core, 122
  s: 25,146 records of the model's own run, R(0) included, equal to
  Java's; the other figures the same to the digit.)
* Compared besides: 170,198 KN lines, 100,124 GET lines, 25,031 SCAN
  lines, 572 touches (reclaim's steps; the traces have 305 cuts), 32,943
  noops.
* Node sizes 8, 14 and 30; up to 5 segments (G = 4) and height 6.
* C-T8: 281,545 key nodes marked against a bound of 1,272,780, summed:
  Java's bound holds on every transaction, with room of 4.5 times.

How often each rule ran (the model's `trail`, on the model's run, which
equals Java's):

| Rule (the Lean name's place)          | small | drain  | reclaim |
|---|---|---|---|
| space split 1, node replaced          | 1,466 | 6,847  | 968     |
| space split 1, in place               | 576   | 6,930  | 2       |
| space split 2 (a segment root)        | 78    | 176    | 10      |
| space split 2, in place (fault 12)    | 5     | 3      | 0       |
| space split 3 (the space root)        | 91    | 345    | 80      |
| space split 3, in place               | 9     | 9      | 0       |
| time split 1                          | 5,089 | 13,416 | 10,677  |
| time split 2 (the space root)         | 455   | 796    | 174     |
| time split, in place                  | 1     | 15     | 0       |
| a new top node                        | 546   | 1,148  | 254     |
| the top node of tt, in place          | 9     | 175    | 0       |
| a new segment leaf                    | 571   | 13,679 | 765     |
| a bitmap, new klong                   | 899   | 20,624 | 3,963   |
| a bitmap, the transaction's, in place | 13    | 6,009  | 40      |
| a bitmap in a full node               | 383   | 3,734  | 1,053   |
| UP: a climb                           | 344   | 14,721 | 558     |
| UP: a node unlinked                   | 356   | 22,624 | 563     |
| UP: a node taken back                 | 3     | 260    | 1       |
| UP: the stop node a segment leaf      | 259   | 7,947  | 449     |
| the space root kept, empty            | 0     | 116    | 0       |
| LE-b: a new klong of the empty key    | 24    | 4,118  | 23      |
| LE-b: in place                        | 2     | 940    | 0       |
| LE-b: in a full node                  | 13    | 779    | 19      |
| RC: the space root replaced           | 0     | 162    | 0       |
| RC: a segment root replaced           | 13    | 40     | 0       |
| RC: the space root taken back         | 0     | 11     | 0       |
| RC: a segment root taken back         | 6     | 8      | 0       |
| a lone time klong (D4)                | 0     | 31     | 0       |

**The medium set** (`PAR=1 treeconf.sh medium 1` at `dd271920`, 991 s
on one core, most of it the exports): `conformance.sh`'s three medium
configurations and six larger draining ones, 9 traces, node sizes 8,
14, 30 and 62, up to 5 segments and height 7.

| Traces | Transactions | Operations | Key nodes made | Taken back | Touches |
|---|---|---|---|---|---|
| 9      | 4,544        | 245,931    | 74,312         | 15         | 75      |

Failures: 0 in C-T1 to C-T9; 190,775 KN lines, 18,176 gets, 4,544
scans; 4,553 records of the model's own run equal to Java's; 297,884
key nodes marked against a bound of 936,409. The first runs at node
size 62 (bitmaps of up to 62 bits) and the largest transactions (200
operations).

**After the merges** (`treeconf.sh all 5` at `d90586d0`, 101 s with
two traces at a time): the same 115 configurations and seeds on main's
code with 024-07, 024-10 and 024-09. TREECONF OK, 0 failures in C-T1 to
C-T9.

| Set     | Traces | Transactions | Operations | Key nodes made | Taken back |
|---|---|---|---|---|---|
| small   | 35     | 3,550        | 20,129     | 10,158         | 9          |
| drain   | 55     | 6,950        | 126,418    | 49,957         | 282        |
| reclaim | 25     | 14,669       | 45,949     | 14,038         | 0          |
| all     | 115    | 25,169       | 192,496    | 74,153         | 291        |

* 25,284 records of the model's own run equal to Java's; 624 touches,
  each the paths of the step's own keys (`touchOf` since 024-07).
* The small set's figures are the earlier ones to the digit. The drain
  set's differ a little: its fifo workloads put a key and delete it in
  one transaction, and since 024-10 the delete, the later call, wins.
  The reclaim set's differ as 024-07 changed what a step makes dirty.

This answers 024-06, section 4.4, point 3, for the small set: its
traces reach UP and LE-b, the take-back 9 times in 35 traces (3 by the
climb, 6 by RC), and never RC of the space root. The drain set reaches
every rule.

### 5.3 Differences found

* **F1, the model's, fixed.** T(1) of the first trace: Java's primordial
  key node is `[T 0]` (`KeyNode.nodeWithTime`) and keeps that klong in
  front (`[T 0, T 1, K, K]`); the model read the node from its history
  as `[T 1, K, K]`, one klong smaller, and so split one put later (T(2):
  "Java has 440/1/I, the model nothing more"). The design note's D4 had
  the rule wrong on both counts. Fixed by the marker entry (D4 as it
  stands). After it: no difference in any run.
* **F2, the model's, fixed** (11:56, the gate after the merges). The
  new check of TP26 failed on the 20 traces whose workload has
  transactions without operations (`empty=`): "dirtyNodeBound 1, the
  limits allow 0", 546 times. The Lean restatement of
  `Dag.dirtyNodeBound` walked the space root before its loop over the
  keys; Java walks it inside the loop, so a transaction without
  operations has the bound 0. One line of `Bound.lean`. TP23's check
  could not see it (a bound that is one too large still bounds); a
  statement in the other direction did. Java's count is not compared
  with the model's number in any trace: a line for it would be format
  3's next addition.
* **No difference of Java's.** Nothing was written to `news.md`.

Controls of the checker, on a trace of the drain set changed by hand:
an `OP D` told as `OP N` fails C-T3; one bit of a bitmap on a KN line
fails C-T2 twice; a GET answer fails C-T4; a NEW line's level fails the
transaction. With LE-b's rule changed in the model: C-T1 and C-T2 fail.

### 5.4 What the model had to copy, and looks unintended in Java

Not faults: none changes an answer or the stream's meaning. Each is a
place where the Lean definition is odd because Java is.

* **O1. A wasted klong.** The primordial key node, and a space root
  that a delete emptied through a time split, are a time klong alone,
  and keep it: such a node holds one klong fewer than M for as long as
  it lives (D4). 31 nodes in the drain set. Changing it changes the
  bytes written, so it belongs with a record format change, if at all.
* **O2. `KeyNode.searchEq` skips klongs "deleted by the bitmap so far"**
  (`if ((deleteBitmap & DELETE_BITS[index]) != 0) continue`): a bitmap
  only has bits of klongs before it, so the test is never true. The
  model's fold has it too, to be literal.
* **O3. `KeyNode.searchFirst` keeps the first klong of the smallest
  compare value** (its test is `<`), where the five others keep the
  last, the current one. No code calls it but one test
  (`KeyNodeTester`); if it were used for a key that was overwritten in
  its node it would give the old pointer.
* **O4. `GetMany.Chain.setup`'s start segment "after the start key's
  last"** (`forward ? Long.MAX_VALUE : -1`) is not reached for a key
  that `Keys.toSegments` makes: such a key's last segment is short, so a
  long klong differs from it and `hasDiff` is set first.
* **O5. `Dag.setNode` gives `appendKlongs` a depth that is not the
  node's** when the segment root is a leaf it has just made (the new
  node is not on the key access path): harmless, as a new node has room
  and the depth is read only for a full one.

### 5.5 The whole run: the model alone writes Java's records (C-T9)

Added 08:38 (`lean/Check/TreeRun.lean`, on by default in `treecheck`;
`--norun` leaves it out). C-T1 to C-T8 start each transaction from
Java's structure. C-T9 never takes Java's state: it runs the model's own
`init` and `step` (SIS/Algorithm.lean: marking, Java's still-dirty test,
the virtual root) with the tree's `exec` for every change, from R(0) to
the trace's end, and compares each record the model writes, and D after
it, with Java's.

* **What the model is given of Java's run:** each transaction's
  operations, the id of its first node, the startup pos that Java chose
  (the take is not the tree's) and the first available time.
* **What must then be the model's own:** every node and entry (the
  model's P is never corrected), every version written with its whole
  history and its references, gd, top, and D.
* **How the records are compared:** `tracecheck`'s `diffRecord`. A
  version of Java's of a node with the marker (D4) gets the marker
  entry first; nothing else is adjusted. R(0)'s structure must be the
  model's `initStruct`.
* **Result** (`treeconf.sh all 5` at `dd271920`): on all 115 traces,
  25,146 records, every record and every D equal: small 3,585, drain
  7,005, reclaim 14,556 (reclaim's steps with their touches, table
  stores, and Java's cuts: the model's stream is not cut, and T12 says
  the records are the same).
* **Controls**, on a drain trace changed by hand: one reference of one
  version (an F line), one id less on a GD line, one compare value on
  an H line, one node less on a DIRTY line: each fails C-T9 at that
  record, and at no other, as the model's run does not follow Java's.

So "C-S covers the tree" (024-06, B2) holds in the stronger form: the
Lean model, tree and stream together, is a second implementation of
the Core's writer that agrees with Java record by record on these runs.
`tracecheck` itself is unchanged and still takes each change from the
trace; its other checks (C-L, C-CUT, C-P, C-H, C-R) do not use `exec`.

### 5.6 What these checks do not do

* **Not compared:** `Kvt.time` of a scan's result; the bytes; anything
  of 2.4's table. The take: C-T9 takes Java's startup pos, as
  `tracecheck`'s C-S does.
* **Restarts:** format 3's lines are run A's. That a rerun gives the
  same change is `tracecheck`'s C-R on Java, and A1 for the model: its
  `exec` is a function of P@(i-1). `treetest`'s `model` runs (4.3)
  restart the model itself.
* **Size:** the traces are small or medium (up to 979 transactions and
  200 operations a transaction, node sizes 8 to 62); `treeconf.sh
  large` (up to 5,000 transactions) is written, not run.
* **`tracecheck` on format 3:** it reads over the tree lines (tried on
  one trace: TRACECHECK OK); `conformance.sh` still exports format 2.


## 6. The stated properties

`lean/SIS/Tree/Props.lean`, `Bound.lean` and `Top.lean`: each a `def
... : Prop`. Proved, as they fell out: TP17 and TP18
(`lean/SIS/Proof/TreeRoot.lean`: `execRootOKTree`, `virtLiveOKTree`),
`RunPSame` of TP19, and TP13 but for one field (`TreeInit.lean`:
`runPSame`; `specOKTree_of_liveSub`, which takes `SpecOK.liveSub`, a
property of `blive` alone, as a hypothesis; since the merge with 024-09
`lean/Check/TreeLive.lean` closes it with that branch's `blive_sub`:
`specOKTree`). The others are not proved. `Within p ts` is a run within reach: every transaction
sorted and with keys as `Keys.toSegments` makes them, no step with an
error, each base above the ids in use. "Run" below says which are
computed on runs: T, by `treecheck` on Java's tree after every traced
transaction; S, by `treetest` on the small cases.

| TP | Name                 | What it says                                | Run  |
|---|---|---|---|
| 1  | `KlongsRoundTrip`    | well-formed klongs are those of their       | T    |
|    |                      | entries: D3 and D4 lose nothing             |      |
| 2  | `LeftmostOK`         | LE-b: an inner node's smallest live klong   | T, S |
|    |                      | is the empty key's                          |      |
| 3  | `NonEmptyOK`         | what UP leaves: a live klong in every node  | T, S |
|    |                      | but the space root                          |      |
| 4  | `PointersOK`         | every entry's pointee is a node of P: no    | T, S |
|    |                      | klong names a node taken back               |      |
| 5  | `SizeOK`             | a key node has at most M klongs             | T, S |
| 6  | `InvOK`              | all of `walk`'s: 2, 3, 5, the order         | T, S |
|    |                      | (`RangeOK`), what RC leaves (`RootsOK`),    |      |
|    |                      | the kinds of children, well-formed klongs   |      |
| 7  | `InvPreserved`       | 6 and 4 after every run within reach, at    | T, S |
|    |                      | every time                                  |      |
| 8  | `NoBug`              | a sorted transaction ends in no error but   | T, S |
|    |                      | the level bounds: Java's `Bug`s are dead    |      |
| 9  | `SearchEqSpec`       | `searchEq` is a lookup in the live klongs   |      |
| 10 | `GetOK`              | a multiversion map: a get at t gives the    | T, S |
|    |                      | last put at or before t, unless deleted     |      |
| 11 | `ScanOK`             | a scan at t gives the map's KVs in range,   | T, S |
|    |                      | in order, both ways, with the end key       |      |
| 12 | `NoopOK`             | a delete without a value changes nothing    | T, S |
| 13 | `SpecOKTree`         | `SpecOK`, `VirtInit` of `treeSpec`          | PROVED |
| 14 | `RunOKTree`          | `RunOK`: A2 to A5, ids, data nodes,         | (T), S |
|    |                      | `VirtStep`, the touch's rules               |      |
| 15 | `PhysRunOKTree`      | `PhysStep`: `liveNew`, `adopt`              |      |
| 16 | `EvictRunOKTree`     | TREE, A6', A-COPY                           | (T), S |
| 17 | `ExecRootOKTree`     | `exec` sees the root by its live children   | PROVED |
| 18 | `VirtLiveOKTree`     | the root's live children: its last entry's  | PROVED |
| 19 | `ExecReadsReachable` | `exec` on P@(i-1) = `exec` on P; with       | S    |
|    | and `RunPSame`       | `treeRun` = the P of `SIS.run` (PROVED)     |      |
| 20 | `MadeBound`          | nodes made <= operations x (4 x the         | T    |
|    |                      | longest path + 1) + 1: aim 2, first form    |      |
| 21 | `DeletedNoNode`      | key nodes reachable at t <= 1 + live keys   | S    |
|    |                      | x the longest path: aim 3, first form       |      |
| 22 | `KlongBound`         | klongs reachable at t <= M x that           | S    |
| 23 | `DirtyBoundOK`       | key nodes marked <= `dirtyNodeBound`: C3    | T    |
| 24 | `SkipSearchOK`       | the skip pointers' search finds the top     | T, S |
|    |                      | node of a time (`topAt`)                    |      |
| 25 | `NormalizeOK`        | `normalize`: one operation a key, in key    | S    |
|    |                      | order, the builder's rule for each key      |      |
| 26 | `DirtyBoundFromLimits` | `dirtyNodeBound` <= operations x (8 x     | T    |
|    |                      | segments x (H + 2) + 2), for a transaction  |      |
|    |                      | within limits (024-17): with 23, the user's |      |
|    |                      | limits bound the index nodes of a record    |      |
| 27 | `DataBelowOK`        | I2 of 024-07, T-COVER's second premise:     | (T)  |
|    |                      | every index node reachable at e has a value |      |
|    |                      | below it, when a key has a value at e       |      |

**TP11 refuted as stated, 2026-11-12** (the second prover's run,
`not_scanOK_scanBoundary`; /Users/f/fl/bench/2026-11-12/cx/REPORT.md):
`keyWf` bounds no compare value, so a key with a compare value of 2^63
passes it, and a backward scan from the end misses it at the reader's
end marker `cvHi` = 2^63 - 1. Java makes no such key (`Klong.
getCompareValue`: "A compare value is non-negative and below 2^62; its
lowest three bits are zero."). **Decided** (Frans, 2026-11-12, 13:38,
"Yes", to option (a)): `keyWf` is to say what `Keys.toSegments` makes,
every segment below 2^62 with its lowest three bits zero; a change of a
trusted definition, made after the prover's run of 2026-11-12, with
TP11 proved for it next. Proofs that use `keyWf` are rechecked by `lake
build`.

**TP11 refuted again, and decided, 2026-11-13.** The second prover's
run 2 (2026-11-12, 16:21 to 21:45, branch `024-22-proofs-2`;
/Users/f/fl/bench/2026-11-12/cx2/REPORT.md) made the change of `keyWf`
(every segment below 2^62 with its lowest three bits zero) and found
TP11 false a second way: `keyWf` allows a key of any length, and
`scan` stops after `scanFuel` = 2^40 steps (`nextGo`), so a run of one
put of a key of 2^40 + 1 segments, within `Within` at valid merge
parameters, scans wrong. **Decided** (Frans, 2026-11-13, 06:47, "Yes",
006-24, section 1): "option B, `keyWf` unchanged (what
`Keys.toSegments` makes, any length); `ScanOK` gets a premise, every
key of the run at most `scanFuel` segments, which Java meets by L3
(57,344 bytes a transaction, about 8,192 segments); `scanFuel`'s
comment corrected. Rejected: A, `keyWf` bounded at L2's 16 segments
(BergDB's own long keys pass L2, so runs Java makes would leave
`Within`); C, a fuel from the structure (changes the trusted reader).
Also yes: land the run 2 now, and delete the two false theorems instead
of keeping unbuilt modules."

What changed (Lean, branch `024-22-proofs-2`):

* `ScanOK` (`SIS/Tree/Props.lean`) has the premise
  `∀ tx ∈ ts, ∀ op ∈ tx.ops, op.key.length ≤ scanFuel` after
  `Within p ts`; its docstring and `scanFuel`'s (`SIS/Tree/Read.lean`)
  say so and name L3 (024-24).
* Deleted, false with the new `keyWf`: `treeContents_keyWf`
  (`TreeReadModel.lean`; in its place `treeContents_keyShape`, the
  segment lengths only, and for the views of a run
  `treeRun_treeContents_keyWf`, `RunEncoding.lean`), and
  `scanBoundaryHistory_within` and `not_scanOK_scanBoundary`
  (`ScanBoundary.lean`: the key 2^63 is no longer well-formed,
  `scanBoundaryKey_not_wf`, `scanBoundaryHistory_not_within`). Both
  modules keep their names and are built; no `.lean` file of `lean/` is
  outside the build.
* Kept of the long-key refutation, which the new `ScanOK` no longer
  meets: `scan_needs_keyBound` (`LongKeyRun.lean`), the premise is
  needed (without it the property is false for the long-key run), and
  the key-length bound of a scan, `scan_forward_one_key_length` and
  `scanEq_first_key_length` (`ScanFuelBound.lean`): a first forward scan
  gives a key of at most `scanFuel` segments.

What is left: the positive proof of TP11, a later run. A caution for
it (found while making the change, not proved): `scanFuel` counts the
key nodes `nextGo` enters and leaves on its way to the next KV, not
segments. An inner node on a key's path costs a step without a
segment, and so does each return up after a long key; a key of exactly
`scanFuel` segments with one inner node on its path, or next to a
two-level tree, still runs out of fuel. So the premise as decided is
likely not enough when H > 0, and no premise on key length alone
bounds the trees' heights. A premise on the parameters would be: every
path of a run within `Within` has at most `p.fuel` = (G + 1)(H + 2) + 2
key nodes (`Params.fuel`, the level bounds G and H that `Within`
enforces), so `2 * p.fuel ≤ scanFuel` or the like; Java's G and H are
far below. That is for Frans to decide before the positive run.

**TP11 option C, decided and made, 2026-11-13.** Frans, 07:07 to 07:21,
on the caution above: "I thought we could prove the algorithms for the
general case, for any size of the key, essentially. If the proofs depend
on size, they would need to be redone for any size change?"; then "OK, do
C as recommended." The proofs are to hold for every key length and every
tree size, with no fixed constant in the model; option B's key premise
is replaced. The second prover's run 3 (07:22 to 07:46, branch
`024-22-proofs-3`, merged in `2e71a297`;
/Users/f/fl/bench/2026-11-13/cx3/REPORT.md):

* `nextGo`'s fuel comes from the parameters, `2 * p.fuel + 2` in
  `scanGo` (`Read.lean`), as the get's and the writer's descents already
  take `p.fuel`: a bound that grows with G and H, which every theorem
  quantifies, so no key length or tree size is excluded. `scanFuel`, the
  long-key run (`LongKeyRun.lean`, `scan_needs_keyBound`) and the key
  premise of `ScanOK` are gone.
* The fuel is enough: proved from TP7's invariant (`ScanAdequacy.lean`
  and the new `Scan*.lean` modules).
* TP11 reduced: `scanOK_of_latest` (`HistoricalScan.lean`) proves
  `ScanOK` from TP7 (`InvPreserved`) and `LatestScanOK`, the scan's
  correctness at the latest time, as `getOK_of_latest` does for TP10.
  Both premises open.
* Checked by the coordinator: `lake build` 278 jobs; `#print axioms` of
  the 40 theorems of the new and changed modules, the standard three
  only; no `sorry`; every module imported. The conformance programs'
  scans as fast as before (the prover's runs).

Next: TP7, the prover's run 4 (from 07:54, at max).

**TP7, partial, 2026-11-13** (the second prover's run 4, 07:54 to 09:02,
at max; branch `024-22-proofs-4`, on main since `6caf8750`;
/Users/f/fl/bench/2026-11-13/cx4/REPORT.md): one component of TP7
proved through the whole writer, the klongs' well-formedness, kept by
every writer rule and by `execW` (`WriterKlong*.lean`,
`KlongPreservation.lean`), with local results on dead klongs and level
metadata; 137 theorems, `lake build` 306 jobs, `#print axioms` of all
137 the standard three only (checked by the coordinator). No
counterexample within valid parameters. Left (its report, "Remaining
proof obligations"): the writer invariant linking cached nodes, kinds,
ordered ranges and paths; order, fill and pointer closure through the
splits and the upward delete; the lift through `Struct.apply` and
`treeRun`; `LatestScanOK` and `LatestGetOK`. The run stopped by itself
at 09:02; run 5 goes on from there (from 09:37, at max).

**The provers' board, 2026-11-13** (coord-1113; Frans, 10:26 and 10:36:
Claude provers beside the second prover). Who holds what:

* TP7 `InvPreserved`: "tp7" (Claude, Fable) and the second prover
  (Codex), independently, compared when both stop. The second prover
  cancelled at 12:07 (Frans: its week's budget is nearly spent); its run
  5, as it stopped, is checked for landing.
* `LatestGetOK` and `LatestScanOK` (TP10 and TP11 from TP7): "latest".
* TP32 `MergeOpBound` and TP33 `MergeAmortized`: "cost".
* T4, the startup section's ends (007): "t4"; done at 12:26. From 12:27 "t43": T4's debt for BergDB's own
  still-dirty test, the cold start's reads without the |D| term, a bound on
  the nodes a change makes unreachable.

Landed checkpoints:

* 11:37, "tp7", `46ba22cb` (checkpoint 37984b68): TP7 reduced to its
  latest time, `invPreserved_of_latest` (`InvLatest.lean`): `InvPreserved
  p` follows from `LatestInvOK p`, `KeyNodesOK` and `PointersOK` of the
  run's structure, for runs within `Within`; `walk_succ_eq_nil_iff`
  (`WalkNil.lean`); the first rules that the writer changes no klong of
  an earlier time (`CacheGood.lean`, `WriterGood.lean`). Checked: `lake
  build` 310 jobs, 82 theorems on the standard axioms, no statement
  changed.
* 12:21, "latest", `c008bff1` (merged as `3f225564`): TP10 and TP11 at
  the latest time reduced to `OpGetOK` and `CommitGetOK`, the paragraph
  below. Checked: `lake build` 316 jobs, 128 theorems on the standard
  axioms, no statement changed.
* 12:21, "t4", `9f59e364` (merged as `622897b1`): T4 proved (007), on a
  new statement. In plain words: every record at the ends of a startup
  section holds that section's transaction and only versions of its data
  nodes and of the dirty nodes D, at most (its data nodes) + |D| of them;
  each node of D lies on the access path of a change of the last
  lev + 1 sections, lev its level; so |D| is bounded by the changes of
  the last H + 1 sections, H the root's level. The definitions it rests
  on are new (`lean/SIS/BoundT4.lean`, from 007-01's prose): **for
  Frans to review** that they say what 007-01 means. Finding: 007-01's
  "about the last two sections" is lev + 1 sections in the proof (a
  dirty child may lie one section further back per level); two sections
  is open. Checked: `lake build` 315 jobs, 63 theorems on the standard
  axioms; main with both checkpoints 321 jobs.
* 12:27, "latest", `5c80a139` (merged as `68aa78c8`): `CommitGetOK`
  proved from a smaller premise, `OverlayLiftOK` (the writer's last
  state, node by node, is the structure after the transaction); so TP10
  and TP11 rest on TP7, `OpGetOK` and `OverlayLiftOK`. A finding, proved:
  TP7's invariant alone allows two keys to share a segment tree, and then
  a valid transaction changes a key it does not name
  (`sharedSegment_changes_other_key`); the writer never makes such a
  structure, so `OpGetOK`'s proof carries TREE in its own invariant.
  `OverlayLiftOK` is also the lift that TP7's `LatestInvOK` needs: "tp7"
  takes it or says so. Checked: 323 jobs, 38 theorems on the standard
  axioms.
* 12:30, the second prover's run 5, its last (`585a46c3`, merged as
  `31290858`): TP7 partial, four files (the export history, klong history
  times, the space split's dead bound, the writer cache's uniqueness); a
  fifth, unfinished when it stopped, left out. Checked: 325 jobs, 78
  theorems on the standard axioms.
* 12:30, "t4", `48bfe93f` (merged as `8af385a0`): a cold start's reads
  bounded (`coldReads_lazy`, `coldReads_handles`, `coldReads_run`,
  `coldReads_tree`; definitions `rerunReach` and `removedAt` in
  `lean/SIS/BoundCold.lean`, for Frans's review): the handles a lazy
  startup gives out, so its reads, are at most the section's index nodes,
  the writer's paths and new nodes of the rerun, |D| and 2; with TREE, a
  path is at most H + 1 nodes per change, counting a split's replaced
  nodes. T4's debt with restarts (`T4_debt_restarts`). **007-01's "about
  the last two sections" is false in general**: `BoundT4Example.lean`, a
  run of 8 transactions on a 5-level tree, has a node of D on level 3
  whose last change below is three sections back (checked by running,
  `#guard`; the kernel cannot reduce the model's sort). Written up in
  007-09. Checked: 327 jobs, 23 theorems on the standard axioms.
* 12:35, "cost", `07e02625` (merged as `b2c7e9c0`): proved with no
  premise, a transaction's merges into two nodes are at most its deletes
  that deleted (`execW_twoMerges_le_deletes`); TP33 reduced to
  `OneMergeStep` (`mergeAmortized_of_oneMergeStep`). TP32 open. Checked:
  78 theorems on the standard axioms; main with the four checkpoints of
  12:27 to 12:35 together, 334 jobs.

**TP10 and TP11 at the latest time, reduced, 2026-11-13** (prover
"latest", 10:37 to 16:30, branch `024-12-latest`). **TP10 and TP11
follow from TP7, the run's key nodes sound and TREE for them, and the
two statements about the writer under premises on the run's structure**
(`getOK_of_runRead`, `scanOK_of_runRead`, `GetUnder.lean`): `OpGetOKUnder
p (RunReadOK p)` and `OverlayLiftOKUnder p (RunReadOK p)`, where
`RunReadOK` is TP7's invariant at the run's last time, `PointersOK`,
`KeyNodesOK` (tp7's, `InvLatest.lean`) and `KeyTreeOK` (TREE for key
nodes: two live klongs of reachable key nodes name one node only if they
are one klong). For any other premise R: `getOK_of_under`,
`scanOK_of_under`, and `opGetOKUnder_mono`, `overlayLiftOKUnder_mono` to
meet the premises of tp7's lift. The first forms, `OpGetOK` and
`OverlayLiftOK` without premises (`getOK_of_op_overlay`), ask nothing of
the run's structure; tp7 reported that the lift fails from a malformed
structure (a klong to an id not in P, an empty key node), so they are
kept only as steps. Proved on the way, on the standard axioms:

* **The scan needs nothing of the writer beyond the get.**
  `latestScanOK_of_latestGet` (`ScanLatest.lean`): `LatestScanOK p` from
  `LatestInvOK p` and `LatestGetOK p`. On a tree without faults at t a
  scan gives the tree's contents at t in its range, in its order, the
  first `limit` (`scan_eq_contents`; the setup's chain and the next step
  in `ScanModel.lean`, `ScanNext.lean`, `ScanSetupProof.lean`); the
  contents are the reference's `refKvs` when every get is `refGet`
  (`rootContents_eq_refKvs`). So TP11 follows from TP7 and
  `LatestGetOK` (`scanOK_of_latestGet`).
* **The get, one transaction at a time.** `TxGetOK` (`GetLatest.lean`):
  after a transaction within reach, a get at its time gives, for a key
  of one of its operations, that operation's value, and for any other
  key what a get gave at the time before. `latestGetOK_of_txGet`:
  `LatestGetOK` from `TxGetOK` alone (the first state has no key; a
  structure reads at the time after its last entry as at that entry's
  time, `get_succ_of_timesLE`).
* **The transaction's step, from the writer.** `txGetOK_of_writer`
  (`GetWriter.lean`): `TxGetOK` from three statements about the
  writer's state, read through it (its own nodes, values and super root
  first, then P before the transaction: `runGet`): `InitGetOK`, the
  first state reads as P at the time before, proved (`initGetOK`);
  `OpGetOK`, each operation changes what the state reads by itself
  alone; `CommitGetOK`, the structure after the transaction reads as
  the last state.
* **The structure after the transaction, from the writer's own nodes.**
  `commitGetOK_of_lift` and `commitLiftOK_of_overlay` (`GetCommit.lean`):
  `CommitGetOK` from `OverlayLiftOK`: each node of the writer's last
  state that it did not take back is, as a key node, the structure's
  node of its id; the transaction took back only nodes of its own ids,
  and not the super root it made. The super root, the values and the
  writer's other nodes are proved (`CommitInv`, `MadeNodes`, kept by
  every rule of the writer through `WriterStateInvariant`).
* **`OpGetOK` from an invariant inside a transaction.**
  `opGetOK_of_invariant` (`GetOpInv.lean`): from any invariant of the
  writer's state that its first state meets and that each operation
  keeps while it changes the reading by itself alone. The first rules,
  each from the premises an invariant must give (no node of the key's
  path taken back, the leaf's klongs well formed and of no later time,
  the next id fresh, and the uniqueness of the key's search at its
  leaf, which TREE gives), for keys of any number of segments whose
  prefix is there (`GetFrame.lean`): a put into a segment leaf with room
  (`writerWP_put_room_seg`), a delete of a key without a value
  (`writerWP_del_noop_seg`), a delete by a bitmap that leaves the leaf a
  live klong, merges off (`writerWP_del_bitmap_seg`); a put into a full
  leaf that existed before the transaction, below an inner parent with
  room: the time split, also of a leaf full by its dead klongs only
  (`writerWP_put_timeSplit_key`, `GetSplit.lean`; its further premises
  are TREE for key nodes and fresh ids on the nodes reachable through
  the writer's state), and the space split (`writerWP_put_spaceSplit_key`,
  `GetSpaceSplit.lean`; one more premise, the search tree's order: the
  leaf's compare values lie between its parent's klong to it and the
  parent's next klong); a put into a full leaf that the transaction
  made: the time split in place (`writerWP_put_timeInPlace_seg`) and the
  space split in place below an inner parent with room
  (`writerWP_put_spaceSplitInPlace_key`, `GetInPlace.lean`); a put of a
  key of one segment into the space root, a full leaf: the space split
  and the time split of the root, a new super root naming the new root
  (`writerWP_put_rootSpaceSplit`, `writerWP_put_rootTimeSplit`), and the
  space split in place of a root the transaction made
  (`writerWP_put_rootSpaceSplitInPlace`, `GetRootSplit.lean`); a put
  into a segment's root, a full leaf that existed before the
  transaction, below the segment leaf of the key's segment before: the
  time split and the space split into a new segment root
  (`writerWP_put_segTimeSplit`, `writerWP_put_segSpaceSplit`,
  `GetSegRoot.lean`; one more premise, that segment leaf not reached
  from the split leaf, which the writer's tree gives,
  `notReach_parent_of_tree`; the reading through a link moved to a new
  tree, `getFromR_graft`), and for a leaf the transaction made the space
  split in place, the segment leaf's klong repointed in place
  (`writerWP_put_segSpaceSplitInPlace`, `GetSegInPlace.lean`,
  `KNode.repoint_live_lookup`); a put of a key whose last segment has no
  tree yet, a new segment leaf below a leaf with room
  (`writerWP_put_newSeg`, `GetNewSeg.lean`). Together (`writerWP_put_leafRoot`,
  `GetLeafRoot.lean`; `writerWP_put_leafBelow`, `GetLeafBelow.lean`):
  every put of a key of one segment into a space whose root is a leaf,
  and every put of a key whose prefix is there into a leaf below inner
  nodes with room for two klongs, changes the reading by itself alone;
  under one invariant of the writer's state, `PutInv` (the writer's
  tree, well formed klongs of no later time, fresh ids, no reachable
  node taken back, the search tree's order at leaves: `GetPutInv.lean`,
  `writerWP_put_leafRoot_inv`, `writerWP_put_leafBelow_inv`; and in
  `GetSegLeaf.lean` every put into a segment's root, a leaf below the
  segment leaf of the segment before with room,
  `writerWP_put_segLeaf_inv`, and the new segment,
  `writerWP_put_newSeg_inv`). The first splits whose parent is full,
  the parent an inner node that existed before the transaction, time
  split, below a grandparent with room: after a time split of the leaf
  (`writerWP_put_timeSplit2`) and after a space split of the leaf
  (`writerWP_put_spaceSplitTime`, `GetChain.lean`; the reading: the
  leaf's split as before, then the parent renamed at the grandparent,
  `renSim_timeSplitGen`; the whole access path of a descent, `PathFrom`);
  the space splits of an inner node, the parent full by its size with
  more than h klongs in its last version, below a grandparent with room
  for two klongs: after a time split of the leaf
  (`writerWP_put_timeSpace`, `GetInnerSplit.lean`) and after a space
  split of the leaf (`writerWP_put_spaceSpace`, `GetSpaceSpace.lean`);
  two more premises, the search tree's order at the parent and neither
  the parent nor the leaf reaching the grandparent; the reading: an
  inner node's halves find what it found with the klongs put, by
  compare value, `halves_inner_searchLte_ins`, `getEqR_split_inner`.
  So a put into a leaf that existed before the transaction, below a
  parent that did too and a grandparent with room for what it gets, has
  a rule for each split the leaf and the parent can need. A delete,
  merges off, into a leaf below an inner parent with room for two
  klongs: with room for the bitmap, the time split (also in place, and
  of a leaf full by its dead klongs only), and the space split of a
  leaf that existed before the transaction (`writerWP_del_leafBelow2`,
  under `PutInv` `writerWP_del_leafBelow2_inv`, `GetDelSplit.lean`; the
  reading: `getFromR_timeSplit_del`, `getFromR_spaceSplit_del`; the
  writer's side with putinv's lemmas of `PutInvDelFull.lean`), and a
  delete whose leaf's split fills its parent, time split or space split
  below a grandparent with room, as for a put (`writerWP_del_timeSplit2`,
  `writerWP_del_timeSpace`, `writerWP_del_spaceTime`,
  `writerWP_del_spaceSpace`, `GetDelCascade.lean`). A parent the
  transaction made, full: a leaf's time split or space split and the
  parent's time split in place (`writerWP_put_timeSplitQIP`,
  `writerWP_put_spaceSplitQIP`, `GetInPlaceCascade.lean`; the reading
  through a node replaced by one with the same live klongs,
  `getFromR_congr_node`).
  With the
  writer's tree (cost's `WriterTreeOK`): `OpGetTreeOK` and
  `opGetOKUnder_of_tree` (`GetTree.lean`), and the split rules with
  `TreeOK` for TREE (`*_tree`, through cost's `htree_of_treeOK`). The
  writer's side of the space split is cost's (`SpaceSplitAfter`). The
  tools: the
  frame of a reading (`getFromR_frame`, `getFromR_leaf_change`: what a
  key's reading visits, each node with the compare value it searches
  there), a node moved to a new id (`getFromR_ren`, for the time
  split), a parent whose klong to a leaf now names two halves by
  compare value (`getEqR_split`, `getFromR_split`,
  `KNode.splitParent_searchLte`, for the space splits), the time split's
  last version with the put
  (`writerWP_replaceOrAdd_last`).
* **The chain from the writer's invariant.** `getOK_of_putInv`,
  `scanOK_of_putInv` (`GetFinal.lean`): TP10 and TP11 from TP7, a run
  premise R after every run within reach that gives the run's links,
  P's tree and TP7's invariant, cost's `OpTreeOK`, putinv's
  `OpPutInvOK`, tp7's lift under R, and `OpGetPutInvOK`: every
  operation from a state that meets `PutInv` changes the reading by
  itself alone. The rules above are its cases.
* **TP7's invariant is not enough for `OpGetOK`**, proved:
  `sharedSegment_changes_other_key` (`SharedSegment.lean`): a structure
  without faults at 1 (`InvOK`, `PointersOK`) in which two long segments
  name one tree of the next segment, and a transaction with every
  premise `Within` asks of it (keys in order and well formed, a fresh
  base, no error) give a structure without faults at 2 in which a key
  that no operation names has another value. TP7's ranges bound no
  segment root, so they allow such sharing; runs within reach have none,
  since the writer makes each segment root new. An invariant for
  `OpGetOK` must exclude it: no key node named by two klongs live at
  the time (TREE, as TP16 states it for the model); in
  `writerWP_put_room` it is the premise that no other key searches the
  key's compare value at its leaf.

Open: `OpGetPutInvOK`, so `OpGetOKUnder p (RunReadOK p)`, the
writer's refinement of the map, every rule but those above (the splits
whose grandparent is full too, or whose parent is full and the space
root or a segment root, or made by the transaction and space split in
place, or a leaf the transaction made below a full parent; a delete's
space split in place; a put that makes more than one new segment or a
new segment below a full leaf; a delete with merges on, the upward
delete, LE-b, the merges, root collapse), with its invariant inside a
transaction: TREE inside it is cost's `WriterTreeOK`
(the coordinator, 2026-11-13), and it must also give the search tree's
order, klongs well formed and fresh ids; checked, not proved, on about 900 pseudo-random
transactions of the model (node sizes 4 to 10, H 0 to 8, merges and
theta), operation by operation, no difference. `KeyTreeOK` after every
run within reach (TREE; TP16 states it for the model) follows from P's
tree, cost's `TreeAt` (`keyTreeOK_of_treeAt`, `getOK_of_treeAt`,
`GetKeyTree.lean`). The lift,
`OverlayLiftOKUnder`, which TP7's `LatestInvOK` needs too, is tp7's (the
coordinator, 2026-11-13); its premises are to meet `RunReadOK` through
`overlayLiftOKUnder_mono` when tp7's `ApplyBridge.lean` lands.

The assembly of TP10 and TP11 (prover "latest", 2026-11-13, 20:50;
the cases at 20:55):
`getOK_scanOK_of_open` (`GetAssembly.lean`) proves `GetOK` and `ScanOK`
(Props.lean, unchanged) from the named premises below.
`getOK_scanOK_of_open_runOK` is the same theorem with the run premise R
fixed to `RunOK`: the run's links, P's tree and TP7's invariant.
`opGetPutInvOK_of_cases` builds `OpGetPutInvOK` from the nine
operation cases, using `opCase_cover`: every operation from every state
is in one of the cases. The `#guard asmCheck asmP asmTx` shows the
premises are not void: a transaction within reach (twelve puts in a
second segment, node size 8, G 1, H 2) meets `Within`'s conditions, and
every state between its operations meets the fuel premise. Each premise
and its status:

- `InvPreserved p` (TP7): open here; it is the TP7 provers' target.
- Every run within reach has its links (`RunLinksOK`): open here.
  `runLinksOK_of_takeBack` gives it from the take-back discipline
  (`TakeBackOKUnder p (RunLinksOK p)`) and 2 ≤ M.
- Every run within reach has its tree (`TreeAt`): open here.
  `treeAt_run` gives it from `OpTreeOK` and `CommitLiftOK`.
- TP7's invariant at the run (`InvOK`): proved inside the theorem, from
  `InvPreserved`.
- tp7's lift (`OverlayLiftOKUnder`): proved for `RunOK`
  (`overlayLiftOKUnder_links`).
- The writer's tree at every operation (`OpTreeOK p`): open here; it is
  cost's target.
- `PutInv` kept by every operation (`OpPutInvOK p R`): open here; it is
  putinv's target. `opPutInvOK_of_T` reduces it to `OpPutInvTOK`.
- The walk's ranges kept by every operation (`OpRangeOK p R`): open here;
  it is putinv's target.
- The fuel premise along a transaction (`TxSegFitsOK p R`): open. Every
  state between operations of a transaction within reach has every path
  inside one segment tree shorter than the fuel. Cost's finding: true for
  transactions that end OK, not after every single rule. It holds in the
  `#guard` example.
- The nine operation cases (`OpGetCaseOK p R` of each case): from a state
  between operations that meets `PutInv` and `RangeOrder` (`RangeOrder`
  at every such state follows from `OpRangeOK`, `rangeOrder_reached`),
  the operation changes the reading by itself alone when the state after
  it meets the fuel premise. Six are proved (`GetCaseBridge.lean`). The
  rules' premises come from `PutInv` (klongs well formed, no node on the
  key's path taken back, the next id free, the key's uniqueness at its
  leaf), from `RangeOrder` (the order below a parent and `OrdG`:
  `rangeG_of_rangeOrder`, `ordG_of_rangeOrder`), from the global parts
  of `PutInv`, which hold at every state of a run with its links (every
  link below the next id: `putInvG_reached`), and from 2 ≤ splitAbove
  (two live klongs in a node that space splits: `lenG_of_splitAbove`).
  - (1) `PutLeafRoomCase`, a put into its leaf with room: proved,
    `opGetCaseOK_putLeafRoom` (on `writerWP_put_room_seg`).
  - (2) `PutLeafFullCase`, a put into a full leaf: proved for
    2 ≤ splitAbove and runs with their links, `opGetCaseOK_putLeafFull`
    (on `writerWP_put_accessPathR`, every split along the access path,
    the space root's and a segment root's space split included).
  - (3) `PutNewSegCase`, a put of a key with no leaf: proved for 2 ≤ M,
    2 ≤ splitAbove and runs with their links, `opGetCaseOK_putNewSeg`.
    New segments below a leaf with room (`writerWP_put_newSegs_inv`) or
    a full one (`writerWP_put_newSegFullR`); where the key's walk ends
    at a missing node or at a descent that finds no leaf, the writer
    fails (`writerWP_putSegs_put_fail`).
  - (4) `DelMergeCase`, a delete with the merges on: reduced to named step
    obligations, cost's (`opGetCaseOK_delMerge`, `DelMergeCase.lean`). The
    merges' loop, `afterDelete` and the root collapse keep the delete's inner
    invariant `DelInv`. That invariant is PutInv, its global parts, the walk's
    ranges, inner children there, the fuel, and the reading of the delete. They
    keep it by cost's merge and collapse lemmas: `writerWP_mergeUp_del`,
    `writerWP_afterDelete_del` and `writerWP_collapseRoot_del`. The merge is
    `writerWP_merge_get_inv`, which derives the merge rules' premises from
    PutInv, PutInvG, RangeOrder and the path (`PathOK`). It covers every kind of
    full parent and the space root as parent. `DelInv` carries the books
    (`PutBook`). PutInv and PutInvG after a merge and after the collapse
    follow from them: `putBook_merge`, `putBook_collapseRoot` and
    `putBook_getNode` (`DelMergeBook.lean`) give the books after, and
    `putInv_after_step` builds the rest. The obligations, all open:
    - `MergeStepOK`: a merge of the loop keeps its reached nodes not taken
      back (the take-back's `ReachedFree`), the walk's ranges and inner
      children (`StepInv`), and the state after it fits the fuel (StepFits for
      a merge). The tree after the merge is proved from the invariants
      (`writerWP_merge_tree_inv`, `MergeTreeInv.lean`). It uses the tree
      lemmas with their halves premise derived from the sorted last version
      (`hhalves_of_sorted`, `writerWP_merge_any_treeS`,
      `writerWP_merge_root_treeS`).
    - `DescentOK`: the loop's descent keeps `DelInv` and gives the path facts
      down to the node it stops at. It also gives the merge's two named
      conditions (`MergePathCond`): no space split in place below a segment
      leaf on the path, and the full parent's last version in the range of its
      link.
    - `CollapseStepOK`: the collapse's steps keep the walk's ranges and inner
      children (`CollRange`), and a segment leaf has room for a replaced
      root's klong. The collapse's tree comes from cost's collapse lemma.
    - `DelStepsOK`: the delete's other steps, with the merges' steps given. It
      holds the walk, the leaf's bitmap or split with its cascade (PutInv and
      the fuel across `appendDeleteKlong` inside the delete), and the upward
      delete. It is `writerWP_del_accessPathR`, `writerWP_del_bitmap_segR` and
      `writerWP_deleteUpward_upT` with the merges on.

    The premises 2 ≤ splitAbove and 1 ≤ mergeMax are also needed.
    `#guard dmCheck dmP dmTs dmTx` shows the hypotheses are not void: a run of
    twelve puts and then ten deletes with the merges on is within reach, every
    state between the deletes fits the fuel, and the writer merges in the
    deletes. StepFits (the inner states fit) is in `MergeStepOK` and
    `DelStepsOK`; step 4 (`SegBal`, cost) is to discharge it.

    Finding (cost, 21:35): StepFits at fuel - 1 is not a per-rule fact. A
    delete can space split a full segment root by a merge (one level more)
    and then remove a level by its root collapse, which does not descend. So
    from a segment of depth fuel - 1, a state inside the operation can have
    depth fuel. There, the reading with `p.fuel` cannot reach the deepest
    leaves, though the operation's end reads right. Whether runs within reach
    get there is a counting question: a transaction's keys are distinct, so
    a segment grows only by the transaction's own new keys. That is open.

    Decision (coordinator, 21:45): option (a). The reading lemmas that case 4
    needs are stated for any fuel f, with the `p.fuel` versions kept as
    corollaries. Inner readings use f = fuel + 1, and `getEqR_fuel_mono`
    brings the operation's end back to `p.fuel`. Step 4 then proves two
    things:
    - every rule keeps SegFits at depth fuel at inner states (`SegBal`);
    - operation boundaries have SegFits at fuel - 1, by the doomed
      transaction: a boundary state with depth fuel has nodes outside H, so
      it throws at a later descent or fails `boundsOK`.

    Case 4's `SegFits` conjuncts change accordingly.

    Done (cost, 22:00): the reading lemmas case 4 needs are generalized in
    place to a fuel f (2 ≤ f), with the p.fuel versions kept as one-line
    corollaries under their old names. They are:
    - the collapse's (`CollGetInvF`, `writerWP_collapseRoot_collF`, the space
      root's and a segment's steps);
    - the merge's (`writerWP_handleFull_lastVF` on latest's
      `writerWP_appendKlongs_chainGRVf`, `writerWP_handleFull_rootVF`,
      `writerWP_merge_any_getF`, `writerWP_merge_root_getF`,
      `writerWP_merge_get_invF`).

    `wGetAt` is the reading at f. Case 4 at f = p.fuel + 1 is
    `opGetCaseOK_delMergeF` (`DelMergeCaseF.lean`): `OpGetCaseOK p R
    DelMergeCase` from `TxSegFitsOK p R` and the obligations at p.fuel + 1
    (`DelStepsOKF`, `MergeStepOKF`, `DescentOKF`, `CollapseStepOKF`). It goes
    through `OpGetCaseOK'`, which adds the fuel premise of the state before
    the operation, and the bridge `opGetCaseOK_of'`. `runGet_of_delInvF`
    turns the reading at p.fuel + 1 into `runGet` at the operation's end. The
    fuel obligations are now SegFits at depth p.fuel inside the operation:
    `MergeStepOKF`'s and the collapse's, at f - 1 = p.fuel.

    Superseded (latest and cost, 22:20): this route, through `DescentOKF`,
    does not count as progress. `DescentOKF` asks `MergePathCond`, which runs
    within reach violate:
    - its clauses (1) and (2) fail for a segment root that an earlier put of
      the same transaction made;
    - its clause (3) quantifies over every merge value.
    The F2 route replaces it:
    - the descent without `MergePathCond`, proved (`descentOKF2`,
      `GetDescentOK.lean`);
    - the merge lemmas take the in-place split of a segment root that the
      transaction made, and derive the full parent's range from
      `RangeOrder` for the merge's actual values (latest, in progress).
      The full parent's level is done: `writerWP_handleFull_lastVF2`
      (`GetMergeLevel.lean`) takes the in-place space split below a segment
      leaf, asks the cascade's order only for a node the transaction did
      not make, and adds the reach back that putinv asked for (under
      `ChainOrd` and `LastOrd`, the last version's order below an inner
      parent). `writerWP_handleFull_lastVF` is its corollary, unchanged.
      The merge lemmas are done (latest, 22:50):
      `writerWP_mergeTail_any_getF2`, `writerWP_merge_any_getF2`,
      `writerWP_merge_get_invF2`, `writerWP_mergeTail_any_treeS2`,
      `writerWP_merge_any_treeS2` and `writerWP_merge_tree_inv2`. They
      need neither `hNoSSIP`, `hNoSSIPp` nor `hrangeL`. The full parent's
      range comes from `RangeOrder` for the merge's actual values
      (`mergeLast_range`, with `MergeGOK` for the second node's compare
      value). The old statements are their corollaries, unchanged;
    - then `opGetCaseOK_delMergeF2` (`DelMergeCaseF2.lean`), proved:
      `OpGetCaseOK p R DelMergeCase` from `DelStepsOKF`, `MergeStepOKF`,
      `CollapseStepOKF` and `TxSegFitsOK`. There is no descent obligation
      and no `MergePathCond`.
    - For putinv's take-back through a merge's full parent (latest, 22:55):
      `writerWP_handleFull_lastShape` (`LevelShape.lean`) gives the shapes
      of the nodes that the full parent's split and its cascade make or
      change (`ShapePost` from D + 1 with nothing put). `mergeLast_ord`
      (`MergeLastOrd.lean`) gives the merge's last version's `LastOrd`
      from `RangeOrder` (with `MergeGOrd`, `mergeGOrd_two`).
    - `MergeStepOKF`'s `RangeOrder` part (latest, 23:16):
      `writerWP_merge_range_inv` (`RangeMergeRoot.lean`) keeps the walk's
      ranges across a merge from the state's invariants and the path
      (`PathOK`). It uses `writerWP_merge_any_range2` below the space root,
      with the full parent's halves from `RangeOrder` (`mergeLast_halves`).
      At the space root it uses `writerWP_merge_root_range`, with the root's
      split by `writerWP_rootSplit_rangeL` (putinv's
      `writerWP_delRootSplit_range` for any last version, now its
      corollary). `MergeStepOKF` does not take `PathOK`, so the range part
      reaches the loop through the F3 obligations.
    - The F3 route (latest, 23:20; `DelMergeCaseF3.lean`):
      `opGetCaseOK_delMergeF3` gives `OpGetCaseOK p R DelMergeCase` from
      `DelStepsOKF3`, `MergeStepOKF3`, `CollapseStepOKF3`, `TxSegFitsOK`,
      `2 ≤ p.M` and the pointers of every run within reach (TP4,
      `PointersOK`). TP4 is no new open premise: it comes from the
      take-back's joint induction at the run level, as in
      `innerChildren_reached`. The loop invariant is `DelInvF3` = `DelInvF`
      ∧ `Book` ∧ `KdInv` (the kinds' books, joined by `writerWP_and` with
      `kd_descendToHeight`, `kd_getNode`, `kd_merge` and `kd_collapseRoot`).
      After a merge, its ranges are `writerWP_merge_range_inv` and its
      inner children come from the kinds (`innerChildren_of_kinds`). The
      collapse's inner children are its own `CollInv`'s.
      - Open: `MergeStepOKF3` (`PathOK` given) asks only for the reached
        nodes untaken (putinv's take-back, `ReachedFree`) and SegFits
        (cost's step 4).
      - Open: `CollapseStepOKF3` asks for the room (part 1) and the walk's
        ranges after `takeBackRoot` and `replaceRoot` (parts 2 and 3).
      - Open: `DelStepsOKF3` is putinv's `DelStepsOKF` on `DelInvF3`.
      - `CollapseStepOKF3` follows from its room part alone
        (`collapseStepOKF3_of_room`, latest, 23:23).
      - The room part is not true in general: a segment leaf can be full.
        Item 3 (latest, in progress) replaces it by a replaceRoot step with
        the leaf's cascade. That step takes SegFits after the cascade as a
        premise (cost's HeightInv route). It also takes a named premise,
        owned by the take-back: `CollapseUnlinkOK`. When the segment root x
        has a klong of the transaction (`n.lastTime = some c.i`), the tree
        with x's previous version, `updN (wNode c.p base v) x (n.toPrev
        (c.i - 1))`, is a tree from the space root, and that version names
        ids below the next id. `unlink x` leaves that tree before the
        leaf's cascade starts.
      - `CollapseUnlinkOK` was checked on runs within reach with the merges
        on (`12-tree-model/collapse-unlink-check.lean.txt`). The runs had
        two and three segments, first-segment leaves of 1 to 13 values, and
        2 to 4 transactions of puts and deletes; M was 8 or 10. It held at
        all 96 replaceRoots at a segment root, 32 of them with a full
        segment leaf. In every one, x had a klong of the transaction.
      - Item 3 is done (latest, 23:48; `CollapseCascade.lean`):
        - `writerWP_replaceRoot_seg_cascadeF` is the replaceRoot step with
          the leaf's cascade.
        - `writerWP_collapseRoot_collF4` is the collapse loop without
          `hroom`, carrying the books and the kinds. Its times and values
          come from `PutInvG`, its children from the kinds.
        - `opGetCaseOK_delMergeF4` is case (4) with `CollapseStepOKF4`, which
          has no room part and two parts instead: SegFits after a
          replaceRoot at a segment root (cost's HeightInv route) and
          `CollapseUnlinkOK` (the take-back's).
        - The open obligations of case (4) are now `DelStepsOKF3` (putinv),
          `MergeStepOKF3`'s untaken and SegFits parts, `CollapseStepOKF4`
          and TP4 (from the take-back's run-level induction).
      - For putinv's `MergeRootJ2OKF` (a merge whose parent is the space
        root), the root's split now has what `writerWP_handleFull_lastVF2`
        and `writerWP_handleFull_lastShape` give one level down (latest,
        23:59; `MergeRootShape.lean`):
        - `writerWP_handleFull_rootVF2` is `writerWP_handleFull_rootVF` with
          the reach back (`writerWP_handleFull_rootReach`). The nodes the
          tree with the root's last version reaches, but the root, are
          reached after. The root is reached after, or holds its klongs
          before the transaction. Every node cached from the next id on is
          reached after. No order premise is needed: the root has no
          parent.
        - `writerWP_handleFull_rootShape` gives `ShapePost` from 0 with
          nothing put for the one-node chain X 0 = L, Nn 0 = n, and keeps
          the path. Its premise is that the last version is a time klong
          and key klongs of distinct compare values.
    TP7's `LatestInvOK` assembled from its parts (latest, 00:10, from the
    coordinator at 23:50; `InvAssembly.lean`). Not proved yet: the parts
    `NonEmptyOK`, `RootsOK` and `FillOK` (latest's, next), `HeightLiveOK`
    (cost's) and `RangeAtOK` (putinv's `RangeOrder`, on P).
    - `HeightLiveOK` (TP7's (b)): proved from one named premise,
      `OpDelChkOK` (cost, 01:10; `treeRun_heightLiveOK_chk`,
      `invPreserved_of_open_chk`, `HeightsChkRun.lean`). The premise: a
      delete, from a state that the transaction's earlier operations
      reach, runs as its copy with a check at every take-back
      (`putKvDelChk`, `DelChk.lean`; (4) below). Tested on 310 runs within
      reach: 6828 deletes, 0 failures; 160 of them with a take-back in the
      upward delete's loop, 2305 with a merge's take-back, 453 with root
      collapse's (`/Users/f/fl/bench/2026-11-13/cost/fit/DelChk.lean`).
    - `invOK_of_parts`: the walk at t finds no fault when the space root is
      a key node and every key node is sound as it is. The kinds and the
      live heights must hold. The reachable nodes must meet `NonEmptyOK`,
      `LeftmostOK`, `RootsOK` (new: an inner segment root has two live
      klongs) and `FillOK`. And `RangeAtOK` (new) must hold: `RangeOrder`
      on P's key nodes from the space root.
    - The walk's fuel needs no premise. The walk reaches the nodes of
      `WalkVisit`, and along its edges the level falls by one at least
      (`level_inner`, `level_seg`, `walkVisit_key`). The space root's level
      is at most `keyMax`, which is below the fuel (`keyMax_lt_fuel`).
    - A node the walk reaches is in `nodesRootsAt` with its flag
      (`walkVisit_mem`) and in `RangeOrder`'s reach with its bounds
      (`walkVisit_reachR`). So the statements over `keyNodesAt` and
      `nodesRootsAt` reach every node the walk checks.
    - `latestInvOK_of_parts` and `invPreserved_of_open` are the run level,
      under `MergeParamsOK`. From TP4 come `KeyNodesOK`
      (`keyNodesOK_of_pointers`), the space root (`treeRun_rootKeyOK`), the
      kinds (`treeRun_kindsAllOK`) and `LeftmostOK` (`leftmostOK_latest`).
      Left as premises: TP4, `DeadAllOK`, `HeightLiveOK`, `NonEmptyOK`,
      `RootsOK`, `FillOK` and `RangeAtOK`.
    - Not void (`#guard invAsmCheck`): a run within reach with merges on
      (node size 8, m = 2, h = c = 4). It has thirty puts, then twenty-two
      deletes that merge 14 key nodes down to 3. At its last time the walk
      finds no fault, and the Bool forms of `NonEmptyOK`, `RootsOK`,
      `FillOK` and `RootKeyOK` hold.
    `NonEmptyOK`, `RootsOK`, `FillOK` and `RangeAtOK` reduced to the
    operation cases (latest, 00:19; `LiveCounts.lean`, `LiveCases.lean`):
    - `LiveCounts` is the three conditions as an invariant of the writer's
      tree, over the nodes reached through live klongs with the walk's
      flags (`FReach`).
    - At a transaction's first state it follows from TP7's invariant at the
      time before (`liveCounts_init`, by `walk_of_fReach`).
    - The operations keep it as the obligation `QLive` of the cases
      (`OpCaseOK`, as TP10's three posts). `live_reached` gives it at every
      state between the operations.
    - At the last state, the commit's lift turns it into the three parts of
      the next run (`liveCounts_commit`). It turns `joint_reached`'s
      `RangeOrder` into `RangeAtOK` (`rangeAtOK_commit`).
    - `latestInvOK_of_cases` and `invPreserved_of_cases` give TP7 under
      `MergeParamsOK`, by induction on the runs. The premises are TP4,
      `DeadAllOK`, `HeightLiveOK`, `TreeAt`, TP10's posts of the cases (1)
      to (4), and `QLive` of the cases (1) to (4).
    - `QLive` of case (1), a put into a leaf with room, is proved
      (`liveCase_putLeafRoom`).
    - `QLive` of (3a) and (3b), new segments below a leaf with room, is
      proved (latest, 00:26; `liveCase_putNewSeg1Room`,
      `liveCase_putNewSegsRoom`). The new segment leaves have a live klong
      each (`writerWP_putSegs_new_live`) and are segment roots
      (`liveCounts_leafAddNewSet`).
    - Open: `QLive` of (2), (3c) (the cascade of a full leaf) and (4).
    - Toward (2) (latest, 00:35; `LiveEdges.lean`): `LiveEdges` is
      `LiveCounts` link by link (`liveCounts_of_edges`,
      `edges_of_liveCounts`). Each step of the writer then checks only the
      links it changes. Two steps are proved: `liveEdges_updN_grow` (a
      node keeps its kind and live pointees and loses no live klong: a put
      in room, a time split in place, the top of a cascade) and
      `liveEdges_copy` (a time split to a new node: a fresh copy of x, and
      x's parent pointing its klong to it). The counts of a space split's
      halves are `halves_lastVersionGivenDel_live_fill`
      (`SplitLiveFill.lean`).
    - Every split step of the cascade keeps `LiveEdges` (latest, 00:44;
      `LiveSteps.lean`). Each step lemma takes the hypotheses of cost's
      matching step of the writer's tree and uses its reach, then adds the
      counts:
      - `liveEdges_timeSplit_gen` and `liveEdges_rootTimeStep`: the kinds
        kept, no live klong lost.
      - `liveEdges_spaceSplit_gen` and `liveEdges_spaceInPlaceStep`.
      - `liveEdges_segSpaceStep` and `liveEdges_segSpaceInPlaceStep`.
      - `liveEdges_rootSpaceStep` and `liveEdges_rootSpaceInPlaceStep`.
      - `liveEdges_updN_sub`, a time split in place.
      The halves must be `HalfOK` (a live klong, two, and m), and a new
      inner root needs two live klongs. Common to all is
      `liveEdges_of_sim`.
    - The cascade's walk keeps `LiveEdges` (latest, 01:02, with cost's and
      the coordinator's agreement): `writerWP_appendKlongs_chainGL` in
      `WriterTreeChainG.lean`. It is cost's walk with one more post
      conjunct: with the merges' thresholds, `LiveEdges` of the tree with
      the klongs put gives `LiveEdges` after. Each of cost's steps of the
      tree has its twin of `LiveSteps.lean` beside it. The counts come from
      `LiveChain.lean`: the halves are `HalfOK`
      (`halves_lastVersionGivenDel_live_fill`), and a time split's last
      version has the live klongs of the node with the klongs put.
      `writerWP_appendKlongs_chainG` is now its corollary, with its
      statement unchanged, so the walk exists once. To sit below it,
      `LiveEdges`' basic part moved to `LiveEdgesBase.lean`.
    - `QLive` of case (2), a put into a full leaf, is proved (latest,
      01:04; `LivePutFull.lean`). `liveEdges_put_accessPath` is
      `writerWP_put_accessPathR`'s walk down the path, with the cascade by
      `writerWP_appendKlongs_chainGL` and the leaf's klong by
      `liveEdges_updN_grow`. `liveCase_putLeafFull` is the case.
    - TP7 with every case proved so far is `latestInvOK_of_open` /
      `invPreserved_of_open_cases` (`LiveTP7.lean`). The cases (1) to (3)
      of TP10's three posts and of `QLive` are filled in, but `QLive`
      (3c), and so are cost's live heights (`treeRun_heightLiveOK`). Left
      as premises:
      - TP4, `DeadAllOK` and P's tree (`TreeAt`) at every run;
      - cost's `OpHtDelOK`;
      - TP10's three posts of (4);
      - `QLive` of (3c): new segments below a full leaf. The cascade there
        runs with the new segment leaf still empty, so `LiveEdges` of its
        virtual tree does not hold. It needs `LiveEdges` with that one
        pending node excepted.
    - The walk with exceptions (latest, 01:20): `LiveEdgesX ... E` asks
      `ChildOK` only of links to nodes outside E, and a node in E may be
      named by segment leaves only (`LiveStepsX.lean`, with every step of
      `LiveSteps.lean` for it). The walk is now
      `writerWP_appendKlongs_chainGLX`, for a set E of old nodes off the
      access path; `writerWP_appendKlongs_chainGL` is its corollary with E
      empty (`liveEdgesX_false_iff`), and `writerWP_appendKlongs_chainG`
      stays the corollary of that, so the walk still exists once.
    - `QLive` of case (3c), new segments below a full leaf, is proved
      (latest, 01:21; `LivePutNewSegFull.lean`). Before the cascade, the
      tree with the leaf's klong to the new segment leaf v meets
      `LiveEdgesX` with E = {v} (`liveEdgesX_newSegLeaf`); the cascade
      keeps it (`writerWP_appendKlongs_chainGLX`); putSegs then fills v
      and makes the leaves below it, and `LiveEdges` holds again
      (`liveEdges_fillNewSegs`). `liveEdges_put_newSegFull` is
      `writerWP_put_newSegFullR`'s setup; its cascade
      (`writerWP_appendKlongs_chainGRV`) gives that the nodes reached
      after it are below the next id. `liveCase_putNewSegFull` is the case.
    - TP7 with every put case proved is `latestInvOK_of_open_del` /
      `invPreserved_of_open_del` (`LivePutNewSegFull.lean`, beside
      `latestInvOK_of_open`). Left as premises:
      - TP4, `DeadAllOK` and P's tree (`TreeAt`) at every run;
      - cost's `OpHtDelOK`;
      - TP10's three posts of (4), the delete with the merges;
      - `QLive` of (4).
    - The target with every put case proved (latest, 01:25;
      `LatestOpen.lean`): `latestGetOK_latestScanOK_of_open_del` gives
      `LatestGetOK` and `LatestScanOK` (and `getOK_scanOK_of_open_del`
      gives `GetOK` and `ScanOK`) for the parameters of `MergeParamsOK`.
      Left as premises:
      - TP4 (`PointersOK`), `DeadAllOK` and P's tree (`TreeAt`) at every
        run;
      - the fuel premise along transactions (`TxSegFitsOK`);
      - cost's `OpHtDelOK` (from the delete's checks, `opHtDelOK_of_chk`);
      - the delete with the merges (4): TP10's three posts, its reading
        (`OpGetCaseOK`) and `QLive`.
      - `QLive` of (4), the delete with the merges.
    - `LiveCounts` was checked on runs within reach with the merges on
      (`12-tree-model/live-counts-check.lean.txt`). The parameters were
      record format 7's thresholds at node sizes 8, 10 and 14 (m = 2, 2
      and 3). The runs had puts in one and two segments, then deletes that
      merge and collapse. It held at all 6420 states between operations,
      none failing.
    Removed (latest, 23:08, as agreed with cost and the coordinator, after
    putinv's take-back moved to F2 at 65b84e5b): `DescentOKF`,
    `MergePathCond`, `opGetCaseOK_delMergeF`, `writerWP_mergeUp_delF`,
    `writerWP_afterDelete_delF` and `opGetCaseOK'_delMerge`; the route at
    p.fuel in `DelMergeCase.lean` (`DescentOK`, `MergeStepOK`,
    `CollapseStepOK`, `DelStepsOK`, `writerWP_mergeUp_del`,
    `writerWP_afterDelete_del`, `writerWP_collapseRoot_del`,
    `opGetCaseOK_delMerge`); and the corollaries only they used
    (`writerWP_merge_get_invF`, `writerWP_merge_get_inv`,
    `writerWP_merge_tree_inv`). Case (4) is `opGetCaseOK_delMergeF2`.
    Removed too (latest, 00:48, the coordinator through putinv, after the
    take-back moved to F4): the reading's F2 route (`DelMergeCaseF2.lean`:
    `opGetCaseOK_delMergeF2`, `opGetCaseOK'_delMerge2`,
    `writerWP_mergeUp_delF2`, `writerWP_afterDelete_delF2`) and F3's
    collapse with a room premise (`CollapseStepOKF3`,
    `collapseStepOKF3_of_room`, `writerWP_collapseRoot_delF3`,
    `writerWP_afterDelete_delF3`, `opGetCaseOK'_delMerge3`,
    `opGetCaseOK_delMergeF3`). Case (4) is `opGetCaseOK_delMergeF4` alone.

    Step 4, plan (cost, 22:15). The Bool evidence is cost's `SegFit.lean`,
    run outside the repository. It ran random transactions (M 4 and 8, G 2,
    H 0 to 2, with and without merges) and grow-then-shrink transactions of
    1000 keys. In the random runs, every segment tree at every operation
    boundary was balanced: 0 unbalanced states of about 14,000. SegFits
    (fuel - 1) held at every boundary checked. The route goes by heights,
    not depths. The writer knows each key node's height: `gh`, and for a
    node of P its level (`heightOf`). The invariant, `HeightInv`, is local:
    every key node is a segment leaf exactly when its height is 0, and an
    inner node's live children have its height minus one. A rule keeps it
    when every node it writes has children of the right height.
    `HeightInv` gives `SegDepthEq (height x) x` for every node, so a
    segment tree's depth is its root's height and the tree is balanced
    (`SegBal`). Three pieces are left:
    - (A) Every rule keeps `HeightInv`, and P has it at every run. After
      the commit, the transaction's nodes are in the bounds, so
      heightOf (keyLevel g h) = h.
    - (B) Inside an operation, the reached nodes' heights are at most
      fuel. Only a root split adds a height, at most one per segment and
      operation.
    - (C) At operation boundaries, SegFits (fuel - 1), by the doomed
      transaction:
      - A reached node of height fuel or more was made in the transaction
        above H (`HeightMarkedPred`). `boundsOK` then fails unless a later
        operation takes the node back.
      - An operation takes back only nodes on its path, a sibling of one,
        or a root that its own split made. A descent that passes a node of
        height fuel or more throws (`writerWP_descendLte_depth`). So every
        node taken back has a height below fuel, or was made in the same
        operation.

    Size estimate:
    - (A) 2000 to 3000 lines: about 40 writer rules, most of it in the
      splits' and the merges' node writes, and the commit lift about 500.
    - (B) 500 to 1000 lines.
    - (C) 1000 to 2000 lines: the path's heights and every take-back site.

    That is 4000 to 6000 lines in all, more than one night. (A) comes
    first.

    Step 4 (A), state (cost, 23:10). It is also TP7's open (b), at the
    coordinator's direction, so that one proof serves both.
    - The invariant (`OverlayHeights.lean`): `HasHt H w y h`, y's height
      from the writer's books (`gh`) or from an oracle H of P's key nodes,
      as the kinds' walk has K. `NodeHt c H w h n`: n's live klongs, now
      and before the transaction (`toPrev`), name nodes not taken back,
      for an inner node nodes one height below; n has no time after the
      transaction's. `HtCache`: every overlay node not taken back meets
      it.
    - The bridge to step 4: `segDepthEq_of_hasHt`, a key node of height
      h has its segment tree balanced and of depth h (`SegDepthEq`);
      `segFits_of_heights` and `segBal_of_heights`: SegFits and SegBal
      from the heights of the nodes reached.
    - The walk (`WriterHeightsRules/Steps/Split/Full/Put.lean`), on the
      books: `HtInv` (HtCache, the path's heights, the path's nodes and
      the space root not taken back, taken ids at or above the
      transaction's first id). Every primitive step keeps it, so do a
      full node's replacement with its cascade (`ht_handleFullWith`,
      `ht_appendKlongs`) and a put (`ht_putKv_put`, with tp7's
      `AppendFrameOK` as the kinds' walk takes it).
    - The run (`HeightsStep.lean`): `HeightAllOK`, every inner key node
      of P has its live children that are nodes of P one height below
      it (stronger than TP7's `HeightLiveOK`, `heightLiveOK_of_all`).
      `heightAllOK_step`: a transaction keeps it when the walk ends with
      `HtCache` (tp7's `apply_keyNode`). `heightAllOK_init`. The walk's
      premises at a transaction's start (`viewHeights_of`) and the
      reading's (`baseHeights_of`) come from `HeightAllOK`,
      `PointersOK` and `KindsAllOK`.
    - The delete side (cost, 00:05). The path's nodes are not taken back
      only up to an index (`PathFreeTo w n`, carried by the steps that
      use it), since a take-back leaves a taken node on the path. Done:
      the steps that take nothing back (`ht_handleFull`,
      `ht_appendDeleteKlong`, `ht_unlink`, `ht_retarget`,
      `ht_mergeParent`, the descents, `ht_replaceRoot`), a node taken
      back given that no kept node holds it (`ht_takenBack`,
      `NoLiveHolder`), `ht_takeBackRoot` given the root's one holder
      (`HolderAt`), and the collapse's loop (`ht_collapseRoot`).
      `liveHolder_unique` (`HeightsHolder.lean`) gives the holder fact
      from the take-back's state: a node of the transaction is named
      only by klongs of the transaction's time (`OldBelowN`), a node
      holding one is reached (`TtReachedN`), and one reached klong
      names it (`TreeOK.oneLink`).
    - Named hypotheses (Option 1, coordinator 23:40): `ht_collapseRoot`
      takes an invariant J of the take-back's, kept by its steps
      (`descendToSegmentRoot`, `getNode`, `takeBackRoot`,
      `replaceRoot`), that gives `HolderAt` at a made root. putinv's
      TakeJ2 with CollGetInv (TreeOK) is that J, through
      `liveHolder_unique`.
    - The run (cost, 00:45). TP7's (b) after every run is
      `treeRun_heightLiveOK_family` (`HeightsDelRun.lean`), the form
      latest's assembly takes (`invPreserved_of_open_htDel` puts it in
      `invPreserved_of_open`). Proved: the put; the operations of a
      transaction (`ht_reached`) and its end (`execW_htCache`); the run
      induction (`treeRun_heightAllOK`); the delete's descent
      (`ht_putKv_del`, `ht_putSegs_del`, `ht_setNode_del`,
      `ht_setValue_del`); the delete that leaves its leaf a live klong
      (`ht_deleteUpward`), with the merges (`ht_merge`, `ht_mergeUp`) and
      root collapse after them (`ht_afterDelete`).
    - Named premises (Option 1), in `HtDelFamily` for an invariant J of
      the take-back's (putinv's TakeJ2 with TreeOK) that holds at every
      state before a delete (`HtJStart`):
      - J is kept by the steps between the take-backs: `getNode`, the
        descents, `appendDeleteKlong`, `merge`, `takeBackRoot`,
        `replaceRoot`, `pathClear`, `findRoot`, `setNode`.
      - The merge's holder, `MergeTailHoldOK`: from a state that meets J,
        the merge's tail runs as its copy with a check before each
        take-back (`mergeTailChk`, `checkFree`: no kept node holds the
        node, now or before the transaction; it is not the space root and
        no node of the view). The check gives `NoLiveHolder` where the
        merge takes a node back.
      - The root's holder (`rootHold`, for `ht_collapseRoot`).
      - The upward delete that empties its leaf (`upEmpty`): the climb,
        the take-back loop and the stop node. Its loop retargets a parent
        to the node the taken node replaced, of another height when that
        node was a root made by a space split; the parent is taken back
        or unlinked next, or is the stop node, whose delete kills the
        klong (tp7's mis-heighted retarget). The walk then needs an
        exemption for that one klong until the stop node's delete.
    - One premise instead of the family (cost, 01:10):
      `treeRun_heightLiveOK_chk` and `invPreserved_of_open_chk`
      (`HeightsChkRun.lean`) take TP7's (b) from `OpDelChkOK` alone: a
      delete, from a state that the transaction's earlier operations
      reach, runs as its copy with a check at every take-back
      (`putKvDelChk`, `DelChk.lean`). The checks:
      - `checkFree` before each take-back of the merge and of the upward
        delete's loop: no kept node holds the node, now or before the
        transaction; it is not the space root and no node of the view.
      - `checkOld` before the loop's retarget: the parent is a segment
        leaf, and the node it is pointed to is a node of the view. A parent
        of height 0 has no height to keep, so tp7's mis-heighted retarget
        cannot occur; with the merges on, the upward delete climbs only
        through segment-root leaves (every other leaf keeps two live
        klongs), so a parent in the loop is a segment leaf.
      - `checkRoot` before root collapse takes a root back: its one holder
        (`HolderAt`).
      - After the loop: the path's nodes above it are not taken back
        (`checkPathFree`), and the stop node is a segment leaf.
    - With the checks the walk needs no other premise (`ht_mergeChk`,
      `ht_collapseRootChk`, `ht_climb`, `ht_takeBackChk`,
      `ht_deleteUpwardChk`, `ht_putKvDelChk`; `WriterHeightsChk.lean`,
      `WriterHeightsChkDel.lean`).
    - Checked on runs (`/Users/f/fl/bench/2026-11-13/cost/fit/DelChk.lean`,
      outside the repository): at every delete of 310 runs within reach,
      the writer's delete and its copy with the checks give the same
      result and state. That is 6828 deletes, 0 failures. Among them 209
      deletes climb (the upward delete), 160 of them with a take-back in
      the loop; 2929 merge, 2305 of them with a merge that took a node
      back; 453 have a root collapse that took a root back (counts
      corrected 01:30, after putinv found the first count read the trail
      from the wrong end). `MergeHold.lean` checks the merge's tail
      alone: 1732 merges, 1465 of them taking nodes back.
    - The holder family (`HtDelFamily`, `treeRun_heightLiveOK_family`)
      stays as a second route. `OpDelChkOK` is the one to discharge.
    - Left: `OpDelChkOK` itself (TP4's holder facts and the merges'
      fill), then (B) and (C).

    Step 4 (B) and (C), state (cost, 01:50). The fuel premises
    (`TxSegFitsOK`, `DelFullFitsOK`, `MergeStepOKF3`'s and
    `CollapseStepOKF4`'s SegFits) follow from the cached heights with
    (A)'s heights: `segFits_of_seenHeight` gives SegFits b at a state
    where the walk holds (`HtInv`) and every cached height is at most b
    (`SeenHeightBound b`; the view's heights are at most H). What is left
    is bounding the heights.
    - (B), proved in part (`HeightsFuel.lean`, `HeightsFuelMerge.lean`):
      - A split's cascade up the key access path keeps every cached
        height at most b when the path's nodes are below b
        (`sb_handleFullWith`, `sb_appendKlongs`, `sb_handleFull`): a
        split's new nodes have the split node's height, a new root one
        more, and the cascade climbs only through the path.
      - So a delete's bitmap and a put's klongs at the path's node take
        the bound from m to m + 1 (`seenHeight_appendDeleteKlong`,
        `seenHeight_appendKlongs`): `DelFullFitsOK`'s step, in heights.
      - A merge does the same: its new nodes have the merged node's
        height, its parent's split cascades up the path (`sb_merge`,
        `seenHeight_merge`). `sb_appendKlongsX` is the cascade from a
        node below b that is not on the path (a new segment leaf).
      - Not proved: the whole operation. A put has at most one cascade,
        so it adds one; the walk over its descents is not written. A
        delete runs several merges, each re-descending, and a later
        merge's path can hold a root that an earlier cascade of the same
        operation made: the lemmas then give one more per merge. One per
        segment and operation needs that the new root does not fill again
        in the same operation (the merges' fill, latest's `LiveCounts`).
    - Checked on runs (`/Users/f/fl/bench/2026-11-13/cost/fit/HeightsOp.lean`,
      outside the repository): 316 runs within reach, 18201 operations.
      In every segment the nodes an operation made are at most one above
      the nodes it found, and after every operation every cached height
      is below fuel - 1: 0 failures. 717 operations split a root, 36 of
      them two roots (in two segments).
    - (C), begun: at operation boundaries SegFits (fuel - 1), by the
      doomed transaction. A root of height fuel or more cannot be
      descended, so no later operation of the transaction reaches its
      segment tree and takes it back, and `boundsOK` fails at the end (it
      is above H, so in `outside`).
      - Proved, the first step (`HeightsFuelDescent.lean`): a descent that
        succeeds from an untaken key node of height h had fuel above h
        (`ht_descendLte_height`, from `writerWP_descendLte_depth` and the
        heights' balance; the nodes it visits are untaken,
        `ht_eqVisits_free`).
      - Left: every take-back site reaches its node by such a descent or
        made it in the same operation, and an operation that reaches no
        node of a segment tree leaves the tree's nodes as they are (a
        frame of every operation). With (B)'s one per operation, a height
        of fuel - 1 at a boundary can reach fuel inside the next operation,
        and then the transaction fails.
  - (5) `DelNoLeafCase`, a delete of a key with no leaf: proved,
    `opGetCaseOK_delNoLeaf`. It changes no reading: the writer's walk
    stops at the first segment that is not there and only reads
    (`writerWP_putSegs_del_noLeaf`), and the key reads as no value
    (`getFromR_noLeaf`).
  - (6) `DelNoopCase`, a delete that changes no bitmap: proved,
    `opGetCaseOK_delNoop` (on `writerWP_del_noop_seg`).
  - (7) `DelEmptyCase`, a delete that empties its leaf (the upward
    delete): open, cost's. Cost's `writerWP_deleteUpward_up_get` and
    `writerWP_deleteUpward_upT_get` are part of it. Void with the merges
    on (`opGetCaseOK_delEmpty_merges`).
  - (8) `DelRoomCase`, a delete into its leaf with room: proved,
    `opGetCaseOK_delRoom`, on `writerWP_del_bitmap_segR`: the rule
    `writerWP_del_bitmap_seg` with the room that the writer checks for
    the branch it takes (`DelRoom`); the old rule asked for the room of
    both branches.
  - (9) `DelFullCase`, a delete into a full leaf: open. The rules
    `writerWP_del_accessPathR` (the leaf below an inner node, split in
    time or space, in place too; below a segment leaf, in time; with
    every split above) and `writerWP_del_leafRootR` (the leaf is the
    space root) are proved; missing are the leaf's space split below a
    segment leaf and the bridge. Void with the merges on
    (`opGetCaseOK_delFull_merges`), so it is open only for parameters
    with the merges off; it waits (coordinator).

With the six cases: `getOK_scanOK_of_open_cases` gives `GetOK` and
`ScanOK` for 2 ≤ M and 2 ≤ splitAbove from the premises above, of the
cases only (4), (7) and (9). `getOK_scanOK_of_open_merges` does it for
the parameters of `MergeParamsOK` (those of
`invPreserved_of_latest_pointers`): there the merges are on, (7) and (9)
are void, and of the cases only (4) is left.

The three premises about each operation, over the same cases (prover
"latest", 2026-11-13, 21:05; `GetOpAssembly.lean`, `GetOpCases.lean`):
the writer's tree (`OpTreeOK`), `PutInv` (`OpPutInvOK`) and the walk's
ranges (`OpRangeOK`). Each is stated per case as `OpCaseOK p R Q P`, with
the posts `QTree`, `QPutInv` and `QRange`: from a state between
operations that meets `PutInv`, `RangeOrder` and the case P, the state
after the operation meets Q. The rules need `PutInv` and `RangeOrder` at
the state before, so the three are carried together along a transaction
(`joint_reached`). From them come the three premises in the forms the
assembly takes (`opTreeOK_of_any`, `opPutInvOK_of_any`,
`opRangeOK_of_any`, and cost's `OpTreeInvOK`, `opTreeInvOK_of_any`).
`OpTreeOK` has no premise on the run: it comes out for runs that all meet
R, so `runTree_joint`, which takes `OpTreeOK` to give the runs their
tree, needs a form with R at the run to use it. `getOK_scanOK_of_cases`
gives TP10 and TP11 from the cases (for 2 ≤ M and 2 ≤ splitAbove), and
`getOK_scanOK_of_cases_merges` for `MergeParamsOK`, where the cases (5)
to (9) are void for all four posts (`opCaseOK_void`). Case (3) comes from
four parts (`opCaseOK_putNewSeg_of_parts`): where the put makes no new
segment the writer fails, which proves every post; (3a) one new segment
below a leaf with room; (3b) more new segments below a leaf with room;
(3c) new segments below a full leaf. Status under `MergeParamsOK`
(`getOK_scanOK_of_cases_merges_open` takes the open ones):

- (1) a put into its leaf with room: all three proved
  (`treeCase_putLeafRoom` on cost's `writerWP_put_room_seg_tree`;
  `putInvCase_putLeafRoom` on putinv's `putInv_put_room_below`,
  `putInv_put_room_root` and `putInv_put_room_segRoot`, by the place of
  the leaf; `rangeCase_putLeafRoom` on `rangeOrder_put_room`).
- (2) a put into a full leaf: all three proved (21:10). The ranges by
  `rangeCase_putLeafFull` on putinv's `rangeOrder_put_accessPath`; the tree
  by `treeCase_putLeafFull` on `writerWP_put_accessPathR`, whose post now
  also gives the writer's tree, the taken ids kept and the nodes reached
  after reached before or new (from `writerWP_appendKlongs_chainGRV`,
  `tReach_updN_addKey`); `PutInv` by `putInvCase_putLeafFull`: its global
  parts from the books, no reached node taken back from the reach bound,
  and its order from the ranges after (`putInv_after_op`,
  `leafOrder_of_rangeOrder`).
- (3a) all three proved (`treeCase_putNewSeg1Room`,
  `putInvCase_putNewSeg1Room`, `rangeCase_putNewSeg1Room`, on
  `writerWP_put_newSeg_inv_tree`, `putInv_put_newSeg`,
  `rangeOrder_put_newSegs`).
- (3b) all three proved (21:40): the ranges by `rangeCase_putNewSegsRoom`;
  the tree by `treeCase_putNewSegsRoom` on `writerWP_put_newSegs_tree`, from
  a tree lemma for the chain of new segment leaves that `putSegs` makes
  below an empty segment leaf (`writerWP_putSegs_new_tree`,
  `GetNewSegsTree.lean`); `PutInv` by `putInvCase_putNewSegsRoom`
  (`putInv_after_op`).
- (3c) all three proved (tree 21:40, ranges and `PutInv` 22:10):
  - `writerWP_put_newSegFullR`'s post gives the writer's tree, the taken
    ids kept and the reach bound (`treeCase_putNewSegFull`).
  - It also gives the ranges after the op, given `RangeOrder`, `OrdG` and
    every klong below the next id (`KlongsBelow`, from the books,
    `klongsBelow_of_book`). The cascade keeps the ranges by putinv's
    `writerWP_appendKlongs_chainGRange`.
  - The new segment leaves below the new empty leaf keep them
    (`writerWP_putSegs_new_range`, `rangeOrder_newChain`), because the
    leaf's parents are leaves: a cascade's nodes link a fresh node only by
    the klongs put into its bottom node, with that node's leaf flag
    (`writerWP_appendKlongs_chainLeafTargets`, `ChainShape.lean`).
  - `rangeCase_putNewSegFull`, `putInvCase_putNewSegFull`.

Cases (1) to (3) are proved for all four posts (the writer's tree,
`PutInv`, the ranges, the reading). Under `MergeParamsOK`,
`getOK_scanOK_of_cases_merges_open` therefore leaves only case (4).
- (4) all three open (cost's merges).

The shapes of the nodes a cascade makes or changes (prover "latest",
2026-11-13, 21:30; for prover putinv's take-back (C); `ChainShape.lean`):
`writerWP_appendKlongs_chainShape`. It takes the premises of
`writerWP_appendKlongs_chainGRV` that concern the writer's nodes, with
`ChainOrd` at every level and the klongs put ordered by compare value.
After `appendKlongs (s + e)`, every node with an id from the next id on,
or on the chain, is one of these (`CascadeNodeShape`):

- a chain node that the cascade did not reach, unchanged;
- a chain node left behind with its klongs before the transaction;
- a node of time c.i (a time klong, then key klongs; `ShadowOK`). A chain
  node of this kind is one the transaction made. A key klong shadowed by
  a later klong of its compare value names either a split child that was
  copied, or a live klong of the bottom node for a compare value put
  there (`ChainShadow`). Halves of a space split shadow like this
  (`halves_shadow`). A time split's last version, a new root and a new
  segment root shadow nothing (`writerWP_replaceOrAdd_lastN`,
  `shadowOK_root`).
- the node where the cascade ends (`CascadeTop`), one of three kinds:
  - the bottom node with the klongs put;
  - a node with the klongs of the split below added, in compare order,
    shadowing only the old klong to a split child that was copied;
  - a segment leaf whose klong to a child split in place is repointed.

The splits of any depth (prover "latest", 2026-11-13, 16:30): **proved
for time and space splits of nodes that existed before the transaction,
below a top node with room** (`writerWP_appendKlongs_chainR`,
`GetCascadeChain.lean`, on cost's `writerWP_appendKlongs_chain`, whose
induction it follows; the steps `getFromR_timeLevel`,
`getFromR_spaceLevel`, `getFromR_updN_unreach`, `GetCascadeGen.lean`):
after `appendKlongs j (X j) ins` the writer's state reads as the state
with ins put in X j. On it, at 16:50, **proved: the put and the
delete into a leaf below such a chain**, the leaf split by its size,
time or space, or its delete's bitmap (`writerWP_put_chain`,
`writerWP_del_chain`, `GetCascadePut.lean`; the leaf's time and space
splits in place for a leaf the transaction made). At 18:15, **proved:
the reading after a cascade of any kind** on cost's
`writerWP_appendKlongs_chainG` (`writerWP_appendKlongs_chainGRV`,
`GetCascadeChainG.lean`, for every value lookup without values at the
new ids and the chain's nodes): in-place time and space splits of nodes
the transaction made, time splits below segment leaves, the space
root's time split with a new root, a top without room; and the put and
delete rules on it (`writerWP_put_chainG`, `writerWP_del_chainG`), and
a put that makes more than one new segment below a leaf with room
(`writerWP_put_newSegs`, `GetNewSegs.lean`). At 18:20, **proved: the
put and delete rules with the cascade along the whole access path from
the space root, across segments** (`writerWP_put_accessPath`,
`writerWP_del_accessPath`, `GetPutPath.lean`, on the writer's path
`writerWP_putSegs_prefix_linked`; their premises are on the nodes
reached: the order below an inner parent, two live klongs in a node
that space splits, no space split that makes a new root), **and a put
that makes new segments below a full leaf** (`writerWP_put_newSegFull`,
`GetNewSegFull.lean`: the cascade for the klong to the new segment
leaf, then the new segment leaves; a tree that differs only below one
segment root reads alike for the keys not through it,
`getFromR_override_off`). At 18:45, **proved: the space root's space
split, in place or not**, in the cascade (`writerWP_appendKlongs_chainGRV`)
and in the put rules: the reading from the new root is the reading from
the old one (`getFromR_newRootRead`, `GetNewRoot.lean`). At 19:15,
**proved: the delete along the whole access path with the space root's
space split** (`writerWP_del_accessPathR`, on
`writerWP_appendKlongs_chainGRQ`), **its leaf's time split below a
segment leaf** (`getFromR_timeSplit_delAny`, `GetDelVirtual.lean`: the
leaf with its last version in place, then the split as a step of the
tree), **and the delete in a space whose root is a leaf**, by its bitmap
or the root's time or space split under a new root, in place too
(`writerWP_del_leafRootR`, `GetDelRoot.lean`). The rules whose cascade
may reach the space root are stated as R versions
(`writerWP_put_accessPathR`, `writerWP_put_newSegFullR`,
`writerWP_del_accessPathR`): their reading holds when the writer's state
after the operation meets the fuel premise below, or when the space root
does not space split (`RootStays`); the earlier statements, whose
premises exclude the space root's space split, are their corollaries.
At 20:10, **proved: the cascade keeps what the tree reached**
(`writerWP_appendKlongs_chainReach`, a lemma of its own and the last
conjunct of `writerWP_appendKlongs_chainGRV` and `_chainGRQ`, agreed
with putinv): every node that the tree with the klongs put into X (s +
e) reaches, but the chain's nodes, is reached after the cascade, when
every node that space splits below an inner parent has its compare
values in its range (`ChainOrd`: a leaf's from the parent's klong on, an
inner node's but its first above it; `RangeOrder` gives it, and without
it a split whose divider is the parent's klong drops a first half that
no read reaches). With it, **proved: a segment root's space split below
a segment leaf, for a node the transaction did not make**, in the
cascade and in the put and delete rules along the access path
(`getFromR_segSpaceLevel`, `GetReachBack.lean`: the new segment root is
reached after the cascade, so `SegFits` of the state after bounds its
segment tree; `hspaceG`'s second case, with the tree in order, `OrdG`).
The reading needs no fuel premise when no new root is made along the
chain (`ChainNoNewRoot`, `NoNewRootG`). At 20:25, **proved: the same
split for a segment root the transaction made**, the segment leaf's
klong repointed in place to the new segment root
(`getFromR_segSpaceInPlaceLevel`), and **for putinv's take-back: the
cascade's chain nodes and new nodes after it**
(`writerWP_appendKlongs_chainReachNew`: every chain node is reached or
holds its version before the transaction, `toPrev`; every node the
cascade made is reached). Still open: the delete's leaf when it space
splits below a segment leaf.

The reader's fuel (prover "latest", 2026-11-13, 18:15; 19:15): TP10's
`get` (`Read.lean`, `getFrom`) and `getFromR` give every segment's
descent `Params.fuel` = (G + 1)(H + 2) + 2 steps, from the parameters,
not from the state. Once every descent fits, more fuel reads the same
(`getFromR_fuel_mono`, `GetFuel.lean`), so the fuel restricts nothing
where `SegFits N t d r` holds with d < fuel: every segment tree reached
from r has depth at most d (`SegDepthLe`, which counts only the links
out of inner nodes; a segment leaf ends the segment). A space split
that makes a new root grows one segment's tree by a level, and its
reading needs that level within the fuel: those cases take, as a
premise, `SegFits` of the writer's state after the operation with d =
fuel - 1, that is, every path inside one segment tree is shorter than
the fuel (one Prop for all provers, agreed with cost at 19:10). Open
premise: it holds for the states of a transaction that ends OK, not for
every state a rule can make. Cost's finding (`cost/fit/Fit.lean`): a
put whose descent goes through a segment tree of depth fuel - 1 can
split its root and reach depth fuel; that transaction then fails at its
end (`boundsOK`). The first form, `PathsFit` (every path from the space
root, through all segments, shorter than the fuel), fails in a
transaction that the writer runs to its end without error: with M = 8,
G = 1, H = 0, 1000 puts below one key and then 1000 deletes grow a
segment tree to height 5 mid-transaction. That transaction is not within
reach, though: it puts and deletes the same keys, and `Within` requires
sorted transactions of distinct keys (correction, cost, 2026-11-13,
22:30). Within reach, `PathsFit` is not refuted. `SegFits` relates to the
deferred height bound of bounded startup, `LiveHeightLe P t H root`,
which bounds the nodes on every live path from the root by H and so
every segment tree's depth; the writer's tree inside a transaction can
exceed it by the new roots it makes (a node made above the level bounds
is recorded in `outside`, MF3, and refused at the transaction's end if
still there).

**The whole path is not capped (prover "cost", 2026-11-13, 19:15).**
Within a transaction a segment tree may grow above H, because the bounds
G and H are checked only at the transaction's end (`boundsOK`), and the
writer's own guard, the fuel of a descent, counts one segment tree at a
time. So `PathsFit` (every path from the space root, through all
segments, shorter than `p.fuel`) is no invariant of the writer's states.
The case: M = 8, G = 1, H = 0, fuel 6; a transaction puts 1000 keys
[120, 64j + 8] below one existing key and deletes them again, and the
writer ends it without error (the 161 nodes made above the bounds are all
taken back). It is not within reach: `Within` requires a transaction's
keys sorted and distinct, so no transaction puts and deletes one key
(correction, 22:30; within reach the case is open, and a segment there
grows only as far as the transaction's own new keys take it);
after its 1000th put the segment tree below 120 has depth 5, so a path
from the space root has 6 links, 7 to a value. The reads are right: the
reader's fuel is per segment too. The coordinator's decision (19:20):
the premise is per segment, latest's `SegFits N t (p.fuel - 1) r`
(`GetFuel.lean`): every path inside one segment tree is shorter than
the fuel. Checked as a Bool at every operation of grow-and-shrink
transactions (M = 4 and 8, merges off and on, two and three segments)
and of random runs: it held at every state of every transaction that
ended without error; the one state without it (M = 4, a 7th put making
depth 6 = fuel) belongs to a transaction whose next descent there throws
(`/Users/f/fl/bench/2026-11-13/cost/fit/`). It is not kept by every
single rule (that put does not throw), only along a transaction that
succeeds; a rule can keep the bound one level higher, `SegFits N t
p.fuel r`, as a descent through a tree that deep throws (not yet
proved).

The design: one induction over the writer's `appendKlongs (d + 1) x ins` instead of a rule per
depth. Its statement: after it, the writer's state reads as the
state before with x replaced by x with ins put (the node of the room
case), every key alike; the nodes it made have ids from the next one
on; the nodes it split are reached no more; nothing else changes. The
room case is direct (`writerWP_appendKlongs_room`, `_room2`). A split at
x, whose parent q gets the klongs to x's new nodes, composes the step at
x with the hypothesis at q: the time split by renaming
(`renSim_timeSplitGen`, `getFromR_ren`), the space split by compare
value (`getEqR_split` for a leaf, `getEqR_split_inner` with
`halves_inner_searchLte_ins` for an inner node, `getFromR_split`), the
time split in place by `getFromR_congr_node`. The leaf's put or delete
is the step at the leaf (`getFromR_leaf_change_seg`). The rules above
are its cases of depth one and two; what the induction adds is the set
of nodes reached after a cascade (the `hreach1` of the depth-two rules,
over every level), and TREE and the order at every node of the path,
which the writer's invariant must give (putinv's `RangeOrder`).

(T) for 27: `tracecheck`'s CUT-live checks it at every cut of a trace
(024-07), and C-T6 checks what it follows from, `NonEmptyOK` and
`KindsOK`, after every transaction. (T) for 14 and 16: `tracecheck`'s
C-A checks them on the trace's change, which C-T1 shows to be the
tree's. S for 14 and 16: `treetest
model` (4.3) checks them on the tree's own runs.

How hard each proof looks:

* **Done:** 18 (a fold over entries of one kind: `blive` of a history
  of top entries is its last entry's top node), 17 (from 18, and from
  the writer's view having no root, 4.2), 13 but `liveSub` (three
  nodes, with the levels' inequalities), `RunPSame` (an induction over
  the run). About 340 lines of proofs, each at the first to third try.
* **Small, a day or less each:** 9 (two folds over one list), 5 given
  7, 25's first half (a merge sort is sorted; `keyLt` is a strict
  order).
* **Medium, days:** 1 (two folds that must agree on the bitmaps' bits;
  the invariant is `klongsWf`), 12 (from 10), 19 (every node the writer
  reads is named by a klong live at i-1, by 9), 20 (one case a split),
  21 and 22 (from 3, 5 and 10), 15 (024-09's A2, on its branch, proves
  that `PhysRunOK` follows from `RunOK` and TREE, with a property of
  `blive` that it proves too; so 15 follows from 14 and 16).
* **Large, the B-tree proof:** 7 with 8 and 4. Every rule of 5.2's
  table keeps the order, LE-b, a live klong in each node and no klong to
  a node taken back; `Bug` is what 7 excludes. The time splits and the
  in-place cases double the cases; 16 follows from 7's order (one live
  parent). A guess as 024-06's: one to two weeks of agent work at the
  highest effort, uncertain.
* **Medium, on top of 7:** 27, I2 (Frans, 10:21: the cut's safety
  rests on it since 024-07). It is `deleteUpward`'s property: a delete
  that empties a node unlinks it, up to the first node that keeps a live
  klong, so every reachable key node but the space root has a live klong
  (TP3); a segment leaf's live klong names a value or the next
  segment's tree, which is not empty either; so by induction on the
  level every key node's subtree ends in a value, and the top node has
  the space root below it. The proof needs TP3 and `KindsOK` from TP7,
  and that `blive`'s live children are `liveAt`'s (as TP9). It is
  stated in `T_cover`'s own words, on `treeRun p (ts.take e)`, so that
  with `RunPSame` (proved) it is that theorem's premise for `treeSpec`.
  **Its exception is real:** with no key at e the tree is an empty space
  root under its top node (`EmptyTreeOK`), and those two have no value
  below them. With reclaim on, its settings key always has a value, so
  a cut never meets that case; a database whose user deletes every key
  with reclaim off has no cut.
* **Medium, with 23:** 26 (Java's count term by term: the nodes walked
  are at most the operations times the path, and each klong counted
  adds at most a split's share).
* **Medium, of its own:** 24 (the skip list: a top node's skip pointer
  i names the top node 2^i ordinals back or the one it inherited; the
  search is a binary descent).
* **Large, on top of 7:** 10 and 11 (the map: 7 at every time, and that
  a node's klongs before a time never change; the scan's chain has an
  invariant of its own), 14 (A2, A3 and A5 are statements about
  reachability after each rule; R4 is the skip list's closure), 23
  (Java's count was wrong three times, 024-01, LM2; the proof follows
  the count's cases).

`NoDeadKlongsAim` is in the file and is not a property of 2026.4's
tree: no dead klong in a reachable node. False today (024-05, ST4); it
is what "a deleted KV costs nothing, eventually" asks of a klong, where
21 says it of a node. 22 is what holds instead.

Not stated yet: the five other searches' specifications (as 9); the
levels' formula against A4 alone.


### 6.1 The touch after 024-07: what the model says about removing it

For the later question (the coordinator, 10:23: a reclaim step as a
plain transaction). By reading the definitions; nothing run for it.

* **Where the touch enters.** The tree's `exec` computes
  `Changes.touch` and never uses it: it changes no node and no id. In
  `step` it enters step 3 only: got dirty = the index nodes not in D on
  the access path of the change (`markOf`: reachable at i with a
  changed node at or below them), and the touched index nodes not in D
  that the first set lacks (`touchOf` of SIS/Algorithm.lean).
* **What it adds for a step.** A step's operations are puts (the
  rewrites, its row), and a put changes its key's segment leaf. So
  every node of a key's path that is still reachable after the
  transaction has a changed node below it, and step 3 marks it without
  the touch. The touch is the paths before the puts. So what it adds is
  exactly **the nodes of those paths that the step itself replaces**: a
  node that one of its puts splits, and the old top node when the space
  root is replaced. With the touch they enter D at i and are written
  once more, though no lookup at i or later reaches them ("stays dirty
  also if the puts then replace it", `Trans.touch`'s comment); without
  it they leave D as after a user transaction's split.
* **The cut does not need it.** `T_cover` and `T_latest` have two
  premises, the data nodes at c or later (the rewrites) and I2 (TP27),
  and none about a touch; they speak of the nodes reachable at the
  iteration's end, and a node replaced before it is reachable only at
  times that the cut makes unavailable.
* **What it gives besides**, outside the model: Java knows a step's
  dirtied nodes and bytes before the step's row is put
  (`Trans.dirtiedNodes`, `dirtiedBytes`, the pacing's charge). A plain
  transaction would count after its puts, or charge the next step.
* **To do before removing it:** the second point as a check in
  `treecheck` on the reclaim traces (C-T5 has both sets: a touched node
  still reachable at i is marked) and as a stated property; then the
  records change (gd, D, the versions of replaced nodes), so C-T9 and
  `tracecheck` say at once whether the model without the touch is
  Java without it.


### 6.2 Frans's decisions of 2026-11-11 that touch the model

From the coordinator's messages (10:08, 10:23, 11:25); no work done for
them here but where it says so.

* **One operation a key is strict** (024-16): a transaction whose key
  transformations make two keys one fails at the commit. The model's
  `Within` asks `Tx.sorted` of every transaction already; `normalize`
  is the builder's rule for the calls as written (done: 2.8).
* **A key is at most 256 bytes** (024-17): 37 segments. Then G, the
  largest segment index, is at most 36 for every run: a constant of
  BergDB, where it is the run's bound today (D5). H stays a bound of the
  run. `Limits.maxSegs` (TP26) is 37 under it.
* **Fixed limits of a transaction** (024-17, in discussion): TP26 has
  the form asked for: the limits as hypotheses, the bound a function of
  them, M and H.
* **I2 is the tree's property** (10:21): TP27, stated (done).
* **`LiveAppend` will take `PhysRunOK`'s place in the trusted
  statements**, in a commit of its own after this branch lands: TP15
  then asks `LiveAppend` of `treeSpec`, a property of `blive` alone,
  which 024-09's `blive_append` proves; TP15 becomes a proved line as
  TP13 did.
* **The gates will require A6, not A6'**: TP16's A6' becomes A6 (no
  pointer of a reachable node to a reachable node that is not its live
  child, even below it). For the tree this is fault 12's fix (a segment
  root made and split in one transaction: the leaf's klong is pointed
  to the new root in place). `treetest model` checks A6' today
  (`adoptFailures`' first list); for A6 it must ask its second list
  empty too. Not changed here.
* **The touch may go altogether, later**: 6.1.


## 7. Gates

**On the head to land, `d90586d0`** (main `0016b9a5`, code `379d8acf`,
merged in; one slot a run, two traces at a time):

| Gate                            | Result                                |
|---|---|
| `cd lean && lake build`         | completed; `treetest` built too       |
| grep in the tree's Lean files   | no unproved theorem, nothing assumed  |
| `java/before-commit.sh`         | BEFORE COMMIT OK (105 s), `e52ed151`  |
| `treeconf.sh all 5`             | TREECONF OK, 115 traces, C-T1 to C-T9 |
| `java/stress/level2.sh` full    | LEVEL 2 OK (18 min)                   |
| its step 8, `treeconf.sh`       | 195 traces, 29,794 transactions, OK   |
| its step 7, `conformance.sh`    | small: 70 traces, TRACECHECK OK;      |
|                                 | drain (024-09's): 50 traces, OK       |

* `before-commit.sh` ran on `e52ed151`, the merge commit; `d90586d0`
  differs from it by one line of `lean/SIS/Tree/Bound.lean` (F2), so no
  Java file changed after it.
* `level2.sh`'s step 8 at full size: `small` 70 traces (7,100
  transactions), `drain` 110 traces (13,900 transactions, 251,431
  operations, 554 nodes taken back), `reclaim` 15 traces (8,794
  transactions, 369 touches). Its step 7 has 024-09's draining
  A2A3Check2 configurations and `conformance.sh drain` (1,366 nodes
  taken back in its 50 traces).
* Not run on this head: level1, level3 and level4 (the integration
  agent runs level1 and level3 on it before it lands); `treetest`'s
  whole set (run on `15d04e1c`, 340,276 states; on the head a `model`
  run and a random run); `treeconf.sh medium` (run on `dd271920`, 9
  traces to node size 62, OK); `tree-tests.sh` as a script; `night.sh`.

**Before the merges**, on this branch's own commits:

| Gate                            | Result                                | On         |
|---|---|---|
| `java/before-commit.sh`         | BEFORE COMMIT OK (262 s)              | `0e02cbf0` |
| `java/stress/level2.sh` full    | LEVEL 2 OK (11 min)                   | `0e02cbf0` |
| `treeconf.sh all 5`, one core   | TREECONF OK, 115 traces, C-T1 to C-T9 | `dd271920` |
| `treeconf.sh medium 1`, one core| TREECONF OK, 9 traces, C-T1 to C-T9   | `dd271920` |
| `lake exe treetest`             | TREETEST OK, 340,276 states           | `15d04e1c` |
| `treetest model`, four sizes    | 35 runs, 0 failures                   | `dd271920` |


## 8. Log

2026-11-11. 07:27, started (agent "tree" of coord-1111). Read 024-04,
024-06, docs/levels.md, docs/trace-format.md, `Klong`, `KeyNode`, `Dag`,
`TopDs`, `PutData`, `KeyAccessPath`, `GetMany`, `Db.putKvs` and its
listeners, `TraceExport`, `lean/SIS/Basic.lean`, `Assumptions.lean`,
`Algorithm.lean`, `lean/Check/Trace.lean`. Clone made. 07:36, the
design note (section 2).

07:37 to 07:52. B0 in `TraceExport` and `Db`; the clone's `lean/.lake`
copied from the main tree's, so that `lake build` is incremental;
`Node.lean`, `Exec.lean`, `Read.lean` (get), the checker. First run:
F1. With the marker: the first trace passes; then `treeconf.sh small`
and `drain`, all traces.

07:53 to 07:54. **A mistake:** the lock's owner changed to touch's
timing hold at 07:53:12, and I ran a lake build, `treeconf.sh drain` and
`small` and four checker runs from 07:53:40 to 07:54:25 without reading
the owner again: about 25 s on 4 to 5 cores inside a timing
measurement. Told the coordinator at once. From then to 08:06 nothing
of mine ran: the scan, the touch, `Spec.lean`, `Inv.lean`, `Props.lean`,
`Bound.lean` and `TreeTest.lean` were written without a compile.

08:06 to 08:17, with the lock: `before-commit.sh` (OK), the compile of
what was written (six small errors of form, no error of content: the
scan, the touch, the invariants and the bound passed on their first
run), `treeconf.sh all 5`, the small cases, the commit `0e02cbf0`.
**A second mistake:** I kept the lock between `before-commit.sh` and
`level2.sh` while I edited and ran small things, 11 minutes in which
touch and cc waited; the coordinator said so at 08:18. `level2.sh`
released it when it ended, 08:28:34, LEVEL 2 OK.

08:18 to 08:31, without the lock (the item's text while `level2.sh`
ran; then single-file compiles on one core): the skip pointers' search
(`Top.lean`); the writer's view without the root; transactions of two
operations in `treetest`; the checks of TP20, TP21, TP22 and TP24; the
proofs of TP18 and TP17 (`SIS/Proof/TreeRoot.lean`), which compiled at
the third try; lean/README.md and docs/levels.md.

08:32 to 08:47, without the lock, one core: `treetest`'s whole set (10
min 57 s; 340,276 states, 0 failures); meanwhile, by single-file
compiles: the whole run, C-T9 (`Check/TreeRun.lean`), which passed on
the first trace and then on all 115; `treetest model`, the existing
model's assumptions, T1 and T2 on the tree alone; the proofs of TP13
(but `liveSub`) and `RunPSame`, each at the first try; TP25;
`tree-tests.sh` and its night step; `treeconf.sh medium` and `large`.
Commit `dd271920`.

08:47 to 09:05: `treeconf.sh medium 1` on one core (991 s, OK). 08:50,
the coordinator: usage is tight; gate, write up, stop; no proofs, no
merge of 024-11. 09:31 to 09:35: Frans approved landing this branch
after 024-07 and with 024-09; the queued `level2.sh` run was cancelled;
the adaptation to 024-07 was prepared as a script by reading its
branch.

10:08 to 10:30: 024-07 on main. Merged (one conflict, `Db.TestHooks`);
the touch as the paths of the transaction's keys, `normalize` as "the
last operation wins" (024-10), TP26 for 024-17's limits, TP27 for I2
(the coordinator, 10:23); `lake build` and a reclaim trace with the new
touch passed. The gates then waited for a slot until main moved again.

11:25 to 12:24: 024-09 on main. Committed the first merge
(`5b6843cf`), merged again (two conflicts, by the merge notes), closed
TP13 with 024-09's `blive_sub`. Gates, one slot a run: `lake build`,
`before-commit.sh`, the commit `e52ed151`, `treeconf.sh all 5`: F2,
fixed in one line (`d90586d0`); then `lake build`, `treeconf.sh all 5`
and `level2.sh` full passed (12:03 to 12:23).


## 9. State

Written 2026-11-11, 12:24. Nothing of this subitem is running; no slot
is held.

* **The head to land:** `d90586d0` on `024-12-tree-model`, in
  `/Users/f/fl/bench/2026-11-11/tree/clone`, working tree clean. Its
  commits: `0e02cbf0`, `15d04e1c`, `dd271920` (this subitem's work,
  sections 3 to 6), `5b6843cf` (the merge of main with 024-07, 024-10
  and 024-13, with the adaptation of the touch, `normalize`, TP26 and
  TP27), `e52ed151` (the merge of main with 024-09, code `379d8acf`;
  TP13 closed), `d90586d0` (F2). Gates: section 7. The integration
  agent runs level1 and level3 on it, and the coordinator lands it.
* **Not run on the head:** level1, level3, level4; `treetest`'s whole
  set; `treeconf.sh medium` and `large`; `tree-tests.sh` as a script;
  `night.sh` (its new step `tree-tests` is one line after
  `lean-tests`).
* **Small things left in the files:** `treetest model` checks A6', not
  A6 (6.2); `conformance.sh` exports format 2, `treeconf.sh` format 3:
  one export could serve both checkers.
* **Dropped, for later:** a workload `shape=bytes` for `TraceExport`
  (keys of raw bytes through `Trans.Builder.put(long[], ...)`: the
  empty key, keys of exactly 7, 14 and 21 bytes, the bytes 0x00 and
  0xff, keys that are prefixes of keys). The traces' keys are all text
  (`/k/12`); `treetest` has the empty key and a key of 7 bytes with an
  empty last segment, Java against the model has not. Written and
  reverted unbuilt at 08:50.
* **Next, in order** (2 to 4 wait for Frans's pacing):
  1. After it lands: the commit that names `LiveAppend` in place of
     `PhysRunOK` makes TP15 a proved line (6.2); `treetest model` for
     A6.
  2. `shape=bytes`, `treeconf.sh large`, and a trace line with Java's
     own `dirtyNodeBound`, so that the model's number is compared (F2).
  3. The proofs, in section 6's order: TP9 and TP1 first (small, and
     the base of the rest), then TP7 with TP8 and TP4, then TP27 (I2).
  4. 024-11's merge in `deleteUpward` (2.8), then its invariant V1 in
     `walk`; the checker and `treetest` run it as they are.
  5. The touch removed altogether (6.1): its check first.
* **To continue:** `cd clone/java && ./build.sh && stress/treeconf.sh
  all 5` (a slot; `PAR=1` for one core); `cd ../lean && lake build &&
  lake build treetest && .lake/build/bin/treetest`. The Lean files name
  the Java method each definition restates; section 2 is the design,
  6.2 Frans's decisions of the day that touch the model.

2026-11-13. Status set after the release (coord-1113).
