# 027-08. The key tree: the writer

Created 2026-11-13 by Frans Lundberg. Status: written (2026-11-19), for
Frans to read; not yet reviewed against the code by a second agent
(027-04, section 5.2).

Part 4 of 027 (027-04, section 2.3; Level 0): what a transaction's puts
and deletes do to the key tree. Since record format 8 (026-25) the writer
is PE, "plan, then emit": from the transaction's whole batch a plan
decides, on lists only, what each node it touches holds after the
transaction, and then each decided node is written once. The rule as
`main` has it at ba81b104 (2026-11-19; the writer's code as at d64e5638),
read from the code (`PeWriter`, `Dag`, `Db`, `DbStarter`) and the proved
model (lean/contract/Contract/PeWriter.lean). It replaces 027-01's
`levels.md` on Level 0's writer and `sis-model.md`'s pages on the old
writer, both stale since format 8 (they describe the splits, the upward
unlink and the merges at the delete). The tree's structure and the reads
are part 3 (027-07, a stub; until it is written, 027-03, sections 11 and
13, and 027-01's `levels.md`); the bytes are 027-03's; D, the take and
Rule A are part 6's (027-10, a stub; until then 027-01's `sis-model.md`,
sections 5 and 6). Each claim carries one status word of 027-04, section
2.2 (proved, checked, gated, argued, measured, open).

The words "kept", "appended" and "new" are about one node in one
transaction; "a cut" here is a list cut into parts, not reclaim's cut
(027-13).


## 1. What it does

### 1.1. Terms, settings and constants

* **B**, the node size: the most klongs of a key node, 8, 14, 30 (the
  default) or 62 (`DbBuilder`), kept in the stream (027-03, section 6).
  Sizes below 8 exist for the Dag's own tests only.
* **The thresholds**, functions of B by integer division, rules of record
  format 8 (a start's rerun uses them, so a change of any is a change of
  the format; `Dag.splitAbove`, `minFill`, `mergeCap`, `theta`,
  `cutSize`):
  * **h** = 17 B / 30: a list of at most h entries that its node cannot
    take becomes one new node; a longer one is cut.
  * **m** = max(2, 8 B / 30), and 1 below B = 8: a changed node that is
    not a root of its segment tree and holds fewer than m entries is
    joined with a neighbour. m = 1 means no joins.
  * **c** = 17 B / 30: the most entries of one node made by a join; a
    longer joined list is cut into parts of at most c.
  * **theta** = max(2, 7 B / 30), and 0 (no bound) below B = 8: the most
    dead key klongs of a key node after a transaction.
  * **cap** = B / 2, the cut size: the most entries of a part when a list
    of more than h entries is cut.
  * The values: B = 8: h 4, m 2, c 4, theta 2, cap 4. B = 14: 7, 3, 7,
    3, 7. B = 30: 17, 8, 17, 7, 15. B = 62: 35, 16, 35, 14, 31. Decided
    by Frans for B = 30 (024-14, QT1; 024-18, QD1; 024-19, Q4; the cut
    size 026-24, section 2.6); the other sizes scale them (024-14, QT2,
    open).
* **Key, segment, compare value**: a key of n bytes is n / 7 + 1
  segments, each a compare value (cv); the order is segment by segment, a
  prefix first (027-03, section 13). The tree of segment g holds, for
  each key, its g-th cv; a segment leaf's entry of a cv of 7 bytes names
  the root of the next segment's tree, of 0 to 6 bytes a value (027-03,
  section 11.3). So in one segment leaf a cv is either the last segment
  of exactly one key or a segment that every key with it goes on from.
* **Live list** of a key node (`PeWriter.live`; the model's `live`): for
  each cv that has a key klong not deleted by the node's last delete
  bitmap, the last such klong; in increasing order of cv. An **entry** is
  a pair (cv, pointer). The node's other key klongs are **dead**:
  deleted by the last bitmap, or followed by a later key klong of the
  same cv (`Dag.deadCount`). Since the writer appends only, the latest
  state of a node is its live list.
* **Untouched**: a node or value of the tree before the transaction that
  no operation reaches; it stays as it is, named by the pointer that
  named it.
* **A planned node** (the model's virtual node, `VN`): for a key node
  that an operation reaches, or one the plan makes: its **base** (the key
  node of the tree before, or none), its segment g and height (a segment
  leaf 0, an inner node one above its children), whether it is a
  **joined** list, its **entries** (cv and child: an untouched node or
  value, a value the transaction made, or a planned node), its **final
  list** F (its entries with each child's parts, 1.4), and its
  **decision**: **same** (F is the base's live list), **append** (klongs
  appended to the base), or **parts k** (k new nodes, k at least 1).
* **Changed**: a planned node whose decision is not same.

### 1.2. Who calls it and when

* **A transaction** (027-09): `Db.putKvs`, after the go point, under the
  write lock, with the transaction's time tt. Before the go point: the
  limits and the dirty-node check (section 4.2), the key transformations
  and the refusal of a transaction that they leave with two KVs at one
  key, and a user transaction's value transformations (005-01, 024-16,
  026-06). The KVs reach the writer as **one batch**, one operation a
  key, in strictly increasing key order: a put of a key with a value, or
  a delete (a null value). A reclaim step's touch, and its row (an
  internal transaction's value transformation), run in `Db.putKvs` before
  the batch reaches the writer, so the row reads every value as it was
  before the transaction (027-13, 1.4).
* **One writer**: at most one transaction writes at a time; readers read
  at lookup times before tt without locks and see nothing of it, since a
  writer only appends klongs after a time klong of tt and makes new
  nodes (part 3).
* **The writer refuses nothing**: every refusal is before the go point
  (R1). An exception in the writer fails the database (005-01): a cycle
  of a damaged stream (a descent of more than 1,000 key nodes in one
  segment tree, `PeWriter.MAX_DEPTH`), a pointer where a key node is
  expected that names a value or nothing, an inner node without a live
  klong. `Dag.putKvs` refuses an empty key or keys not strictly
  increasing with an `IllegalArgumentException` (a bug of the caller,
  never a user's input); an empty batch changes nothing.
* **The start's rerun** (027-11, 1.7) gives the writer a record's KVs in
  their stored order, at the record's time; a record whose KVs are not
  strictly increasing is refused there, an SFE (1.12).

### 1.3. The transaction

    run(ops, tt):
        root := the space root at tt, found from the super root
        if |ops| <= 8 and shortWay(root, ops): return            (1.10)
        v := plan(root, ops, segment 0)                           (1.4)
        r := settle(v, space root)                                (1.6)
        e := emit(r)                                              (1.7)
        if e names a node other than root:
            a new top node at tt that names e (TopDs.newSuperRoot)

Everything that is planned is decided before anything is written, but
for the trees of segments after the first: such a tree is planned,
settled and emitted when the plan of its segment leaf reaches it (1.4),
so that the leaf's entry can name its new root. Its nodes are below the
leaf and are not changed again in the transaction.

The space root changes (a new top node) when it is replaced by a new
node, cut (a new root above it), or collapsed (1.6). The new top node's
ordinal is the next one, and its skip pointers are `TopDs.newSuperRoot`'s
(part 3; the model's `newTopNode`).

### 1.4. Plan

**plan(x, ops)**, for key node x of the tree before, reached by a
pointer, with the operations in its range, at segment g:

* **A segment leaf.** Its entries start as its live list. The
  operations are taken in groups by their cv at segment g, in increasing
  order (the keys are sorted, so a group is consecutive):
  * a key that ends at g: a **put** makes a new value node (it gets its
    id now, 1.8) and sets the entry of the cv to it; a **delete** of a cv
    that has an entry makes a delete node for the record (an id too) and
    removes the entry; a delete of a cv without an entry is a **noop**:
    it makes nothing and is not stored;
  * the keys that go on after g: **planTree** of the next segment's tree,
    from the entry's child (none if the cv has no entry), with these
    operations: that tree is planned, settled (1.6) and emitted (1.7)
    now, and the entry is set to its new root, or removed if the tree is
    empty.

  Then mkNode(base x, height 0, the entries).
* **An inner node.** The operations are divided among its children by
  its live list (`route`): the first child takes every operation whose
  cv is below the second entry's cv, and each other child those from its
  own cv up to the next entry's. Each child that got operations is
  planned (one height down), left to right; the others stay untouched.
  Then the children are **rebalanced** (1.5), and then mkNode(base x,
  the children's height + 1, the entries).
* **A new tree** (planTree from no root: a key with a segment that the
  leaf above does not have): a segment leaf with no base and no entries,
  with the operations applied as above (a delete is a noop there), then
  mkNode(no base, height 0).

**mkNode(base, height, join, es)** makes the planned node:

1. In an inner node the first entry's cv becomes 0, the empty key
   (LE-b: an inner node's smallest live cv is the empty key).
2. F := the entries that each entry (cv, child) gives its parent
   (`ents`):
   * an untouched child: (cv, its pointer);
   * a planned child decided parts k with k >= 2: k entries, all new:
     the first with cv, and for each later part its first cv; the parts'
     sizes are those of 1.7;
   * a planned child decided parts 1, or without a base: (cv, new);
   * a planned child decided same or append: (cv, the pointer that
     reached its base).

   In an inner node F's first cv becomes 0 too.
3. The decision, decide(base, join, F), with n = |F|:
   * **No base** (a new tree's leaf, a joined list, a new root, a new
     empty space root): parts nParts(c, n) if joined, else parts
     cutParts(n).
   * **F is the base's live list** (the same cvs, each entry the base's
     own live klong of its cv): **same**.
   * Else the klongs that would make the base hold F are: a time klong
     of tt; a delete bitmap if a cv of the live list is not in F; and a
     key klong for each entry of F that is not the base's live klong of
     its cv (an entry **new**, its cv not in the live list, or
     **repointed**). If the base's klongs and these are at most B:
     * if theta > 0 and the base's dead klongs, plus the cvs removed,
       plus the entries repointed, are more than theta: a
       **compaction**, parts 1 if n + 1 <= B, else parts cutParts(n);
     * else **append**.
   * Else (they do not fit): parts cutParts(n).

   cutParts(n) is 1 if n <= h, else max(2, ceil(n / cap)). nParts(c, n)
   is 1 if n <= c, else ceil(n / c).

The dead klongs after an append are the base's, one for each cv removed
(its live klong gets a bit) and one for each entry repointed (its old
klong is followed by a new one); an entry added is live, as F has one
entry a cv. A new node holds a time klong and its entries, so a node made
has at most B klongs: at most h, cap, c, or B - 1 entries (027-03,
section 11.3).

### 1.5. Rebalance

rebalance(children, height hc), on the entries of an inner node whose
children are at height hc:

1. **Drop the empty**: a planned child with an empty F is left out; its
   base, if any, is not reachable after the transaction.
2. **Join** (only if m >= 2), at most |children| + 1 rounds:
   * stop if fewer than two children are left;
   * x := the first child that is planned, changed and holds fewer than
     m entries (|F| < m); none: stop. An untouched child, or one decided
     same, is never joined;
   * **M1**: x joins its left neighbour if it has one and either it is
     the last child or the left neighbour's count plus |F of x| is at
     most c; else its right neighbour. A count is an untouched node's
     live list length, or a planned node's |F|;
   * the joined list J: the left one's entries, then the right one's. An
     untouched node gives its live list, each entry an untouched child,
     and is not reachable after the transaction; a planned node gives its
     entries as planned (its children before their cuts), and its base,
     if any, is not reachable after. In an inner node (hc > 0) the right
     one's first entry gets the right one's cv in the parent, and J is
     rebalanced one level down, rebalance(J, hc - 1), so that a small
     grandchild gets a neighbour too;
   * the joined node, mkNode(no base, hc, joined, J), takes the left
     one's place with the left one's cv; the right one's entry goes.

A joined node is changed, so a joined node with fewer than m entries is
joined again in a later round. A planned node that a join opens is never
emitted: its decision is replaced by the joined node's.

### 1.6. Settle a root

settle(v, space) for the root of a segment tree (space: the space root,
segment 0's), repeated until it stops:

* **An untouched node** (reached by a collapse): an inner node with one
  live entry is not reachable after, and settle goes on with its child;
  otherwise it is the root.
* **A planned node with an empty F**: in a segment tree after the first,
  none: the tree is empty and the segment leaf above removes its entry
  (1.4); the base is not reachable after. The space root: a segment leaf
  stays the root with its decision; an inner node gives way to a new
  empty segment leaf (no base, parts 1: a node of one time klong).
* **A planned inner node with one entry**: its base is not reachable
  after, and settle goes on with that entry's child (**collapse**).
* **A planned node decided parts k, k >= 2**: a **new root** above it,
  mkNode(no base, height + 1, [(0, v)]), whose F is the k parts' entries
  and whose decision is cutParts(k); settle goes on with it (so a very
  large batch can raise more than one level).
* Otherwise the node is the root.

### 1.7. Emit

emit(v) writes the planned subtree, children first, and gives the
entries that v's parent gets:

* **Untouched**: nothing written; its pointer.
* **Same**: each planned child is emitted, in order. If one of them, or a
  segment tree below this segment leaf (1.4), wrote a node, the base is
  **on the path** (reported, so that Db marks it, 1.9). Gives the
  pointer that reached the base.
* **Append**: the planned children are emitted, in order, and F is made
  again with the pointers they gave. Then the base gets, in this order:
  a time klong of tt; if a cv of its live list is not in F, a delete
  bitmap: the base's last bitmap with the bit of every key klong, live or
  dead, whose cv is removed (one bitmap a node and transaction since
  format 8, 027-03, section 11.2); a key klong for each entry of F that
  is not the base's own live klong of its cv, in increasing cv order.
  Each key klong names a node made, a value, or the node an old pointer
  named, copying that pointer (its handle and reference, A-COPY). The
  base is reported changed. Gives the pointer that reached it.
* **Parts k**: the planned children are emitted in order and F is made
  again with what they gave (a child cut into parts gives an entry for
  each part: the first with the child's cv, the others with their own
  first cvs; in an inner node F's first cv is 0). F is cut into k parts,
  their sizes as even as possible: with n = |F|, q = n / k and r = n mod
  k, r parts get q + 1 entries, the first r of them for a joined list,
  the last r otherwise (`partSizes`). Each part, left to right, becomes
  a new node: a time klong of tt, then a key klong for each entry, the
  first entry of an inner node's part with the empty key. Each new node
  is reported made (it gets its id), then its pointers, then changed.
  The base, if any, is not reachable after. Gives an entry for each part:
  the first with cv 0 (its parent puts its own cv there), the others
  with their first cvs.

No node is written twice. A planned node that is not in the settled tree
(dropped, opened by a join, collapsed) is never emitted.

### 1.8. Ids, and the order of the nodes made

Db gives a node its id when it is reported made: the next vpos, from the
record's position + 1 on, two apart (027-03, section 5; the start's rerun
gives the same, 027-11, 1.7). So the ids follow the order of the reports:

1. **In the plan, in key order**: a value node when its put is applied
   at its segment leaf; a delete node when its delete removes an entry;
   a tree of a segment after the first when it is emitted, its new key
   nodes bottom-up and left to right, before the leaf's later groups
   (and a tree below that one's leaves before it).
2. **The space root's tree**, emitted after the whole plan: bottom-up
   and left to right, each part of a cut left to right.
3. **The top node**, last, if the space root changed.

Since format 8 a record's ids have no gaps: every id names a node of the
record (027-03, section 5; until format 8 the take-back left gaps).

### 1.9. The dirty set

Db marks the index nodes of the transaction (`markAtEndOfOp`), in this
order: the super root and the space root, which the find of the root
follows (1.3); then each key node reported made, changed or on the path,
and the top node made, in the order of the reports (1.7, 1.10). After the
batch, if the transaction made a value, a delete node or a node, or
changed a node, each marked node that is not dirty becomes dirty and joins
the transaction's got-dirty list, in that order; a transaction of noops
marks nothing. At the end of the transaction, a node that the transaction
made unreachable (a key node reported replaced: a base not reachable
after; the super root that a new top node replaces) leaves the got-dirty
list and is clean again if it joined it in this transaction, unless a
reclaim step's touch made it dirty (027-13, 1.4).

So D gains the nodes the transaction made or changed and their current
ancestors: the Lean model's marking of step 3 (`SIS/Algorithm.lean`,
`marked`; T13), checked (C-T9 and A2A3Check2's MARKING, equal at every
traced transaction, 026-25, section 6). The order of the got-dirty list
is the record's (its got-dirty pairs) and the order in which later takes
write the nodes (027-03, section 8.4); the model compares the list as a
set. The short way marks in another order than the plan (1.10, 028-25).

### 1.10. The same decisions by counts

PE decides a node by its final list. Java decides most nodes by counts,
without their lists, where the counts give PE's decision and klongs; the
rest by their lists (`PeWriter`'s class comment and 026-25, section 2):

* **The short way** (`shortWay`), tried for a transaction of at most 8
  operations. For each operation a descent as a get at the latest state:
  in an inner node the latest live klong of the greatest cv at or below
  the operation's; at a segment leaf above the key's last segment, the
  entry of its cv. It is **not taken**, and nothing is changed or
  reported, if:
  * an inner node's smallest live cv is not the empty key, or an inner
    root of a segment tree has no live cv but the empty key (mkNode or
    settle would change it);
  * a put needs a new segment tree (a delete there is a noop);
  * a segment leaf reached, with n' the entries after its operations,
    has n' < 1; or is not a root of its tree, m >= 2 and n' < m; or its
    klongs plus 1 (a time klong), plus 1 if a cv is removed (a bitmap),
    plus one for each put, are more than B; or theta > 0 and its dead
    klongs plus the cvs removed plus the puts of cvs it has are more than
    theta;
  * a descent passes 1,000 nodes in one segment tree.

  If it is taken: (1) the value and delete nodes are made in key order
  (their ids), the noops make nothing; (2) each segment leaf reached, in
  the order of its first operation, gets its klongs as append writes them
  (a time klong, a bitmap of the cvs removed, a key klong for each put in
  cv order) and is reported changed; (3) for each operation that wrote,
  in key order, the nodes of its path above its leaf (the inner nodes of
  each segment tree from the space root down, and the segment leaves of
  the segments before), each once, are reported on the path. For such a
  transaction PE's plan decides each leaf append and every node above it
  same, joins and settles nothing, and so writes exactly these klongs
  and ids: argued in `PeWriter`'s comment; checked (the tree checker
  compares both ways with the model on every traced transaction).
  `DagTester.testShortWayLeafAroundASegmentTree` gates a leaf whose
  operations come before and after a segment tree's.
* **In the plan**: a segment leaf kept or appended to is decided by
  counts over its changes (`LeafFrame.leafNode`); an inner node whose
  planned children are all kept, none empty or to be joined, with the
  empty key first, is same without its list (sparse); one whose planned
  children are kept or decided parts, none empty or joined, is appended
  to by counts (`appendedByCounts`: no bitmap, as no cv leaves; a key
  klong for each part, in cv order); an inner node with at most 16
  operations finds their children by one scan of its klongs
  (`routeBySearch`), not by its live list.

**The order of the marks differs between the two ways.** The plan
reports bottom-up (a node on the path after the nodes below it); the
short way reports the leaves first and then each path top-down. For a
path of two or more inner nodes below the space root that are not dirty
yet, the got-dirty list's order differs from the plan's (the super root
and the space root come first in both, 1.9). The trees, the ids and the
set D are the same; the record's got-dirty pairs and the order of later
takes follow the way Java took. Both are deterministic, so the stream is
too (P2); a second implementation that wants Java's bytes must follow
both orders. 028-25 asks whether to keep this or make one order.

### 1.11. What the record holds of it

The writer's part of a record (027-03, section 8): the value and delete
nodes, one for each operation that is not a noop, in key order; the top
node if one was made; the got-dirty list (1.9). The key nodes made and
changed are dirty and are written by the takes of this or later records
(part 6), not by the writer. A noop leaves nothing in the record.

### 1.12. The rerun

A start reruns each transaction of the startup section with its record's
value and delete nodes (027-11, 1.7): the same batch, without the noops,
at the same time, on the same tree, with the same B. PE is a function of
these alone: of the tree's klongs, the operations, tt and B (no clock, no
cache, no state between transactions). So the rerun makes the same nodes
with the same ids: argued; gated (the restart tests, `RestartInvariance`,
kill-restart; C-T9 runs the model's whole run with its own records). The
noops do not change a plan; without them a rerun may take the short way
where the run took the plan, which changes only the order of the marks
(1.10), and the rerun's D comes from the stored ids, not from its marks
(027-11, 1.7). A record of format 7 is refused at a start: the same KVs
make another tree under PE (027-03, section 8.2).

### 1.13. What PE never does

* No node is written twice in a transaction, and no klong is written to
  a node that the transaction does not keep (030-21: `PeOwn`, emit's
  lemma; TransCheck fails a node made or changed and then replaced).
* No node is made and left out: every node made is reachable after the
  transaction (no take-back; `made.unnamed` 0 in 026-24's trial; C-T1).
* No klong is changed in place, and no klong is written before a time
  klong of tt: a reader at an earlier time reads every node as before
  (the contract's clause 3; proved for the model, 030-21).
* Nodes off the operations' paths are not read or written, but for the
  neighbours that M1 reads for a count and that a join opens (1.5); an
  opened neighbour becomes unreachable, it is not written.


## 2. State

* **In memory**: only the tree. A transaction's plan (its planned nodes,
  the leaves' changes, the live lists) lives until the transaction ends;
  `Dag.stat*` counts the decisions for tests.
* **In the stream**: nothing of the plan. B is in the stream (027-03,
  section 6); the thresholds are rules of record format 8, functions of
  B, not stored. The record holds what 1.11 says; the nodes' bytes are
  027-03, section 11.


## 3. Invariants

* **The writer's contract** (030-04; 030-05): after a transaction (1) the
  tree meets the invariants at tt (well-formed nodes and klongs, W1 to
  W4, the key order, the kinds of children, a live klong in every node
  but an empty space root); (2) its contents at tt are those at tt - 1
  with the operations applied to a plain map; (3) the frame: every node
  stays, keeps its level, kind and klongs, gets klongs only after a time
  klong of tt, a node not in D is unchanged, a node made is in D, space
  roots are only added; with **TREE** (no node reached twice from a space
  root) and the top's clauses. Proved for `Contract.PE.peTx` (030-21:
  `pe_step`, `pe_meetsTop_start`, and `MeetsFull` with K-LEVEL,
  `pe_full`); Java's writer gives that program's trees: checked (1.10,
  section 5). Java's own check of clauses 1 to 3 on the nodes it touched:
  TransCheck, gated.
* **LE-b** (LeftmostOK): an inner node's smallest live cv is the empty
  key: by mkNode; proved (`Shaped`, part of 030-21's `Inv`); checked
  (C-T6, the shape check).
* **Balanced** (BalancedOK): the segment leaves of a tree are at height
  0 and an inner node's children one below it: proved (`Shaped`);
  checked.
* **Roots** (RootsOK): an inner root of a segment tree has at least two
  live klongs: by settle (1.6); checked (C-T6, the shape check); not
  proved.
* **V1, BU1** (FillOK; 024-11): with m >= 2, every key node that is not
  a root of its segment tree holds at least m live klongs after every
  transaction, and the key nodes are at most S + (n + S - 1) / (m - 1)
  for n live keys and S segment trees. Argued: a changed node below m is
  joined while it has a neighbour; one without a neighbour is its
  parent's only entry, so its parent is changed and below m too, or is a
  root and collapses. Checked (C-T6, the shape check); gated
  (`MergeTester.testFillAfterEveryTransaction`, UnlinkFuzz's
  `Dag.checkFill`). Not proved.
* **TP39** (DeadOK; 024-23): at most theta dead key klongs a node: by
  decide (1.4); checked; gated (`DeadKlongTester`, 5 tests).
* **At most B klongs a node**, and at most 62 (a bitmap's bits): by
  decide; proved for the model (`Holds`, 030-21); checked.
* **One bitmap a node and transaction**, holding every bit of the
  bitmap before it (W3): by emit; proved (W2 to W4 in clause 1).


## 4. Costs and bounds

### 4.1. Work

* **Each node decided once and written at most once**; a transaction
  reads the paths of its operations and, for each join, the neighbour M1
  counts and the one it opens: argued (1.13). P1: at most 500 operations
  a user transaction (L1), so the work of one is bounded by its paths
  and their neighbours.
* **Time**: measured (026-25, section 7). CORE's set test (one put a
  transaction, 100,000 keys in memory) 11 to 18 % slower than format 7's
  writer, mostly the short way's live list of the leaf; at 10M keys
  CCBench within a few per cent (1.03), the load (transactions of 100 or
  500 puts) 0.90 to 0.97 of format 7's puts a second. Open: 028-19.
* **Bytes**: measured on the model (026-24, section 2.3): new key nodes'
  bytes 0.962, all changed nodes' 0.992 of format 7's writer over 288
  traces; with reclaim on, Java's databases 1.05 to 1.07 times the bytes
  a put (reclaim's pace, 026-25, section 7; 028-19).
* **Stack**: the walk over the segments is a loop with a stack of frames
  (a key of BergDB's own may have 8,193 segments, 024-17's L3); within a
  segment tree the recursions are bounded by its height: gated
  (`DbTesterLongKeys.testOwnLongKeysSmallStack`, a 256 kB stack).

### 4.2. The dirty nodes: dirtyNodeBound

Before the go point a user transaction is refused if the index nodes it
can make dirty or create could pass the record's index limit, 15/16 of
the record limit (`Db.checkDirtyNodes`; 027-03, section 8.3; 005-31):

* a cheap test first: a put counts 3 nodes a level, a delete 20, of a
  path of `height` levels a segment, plus 3, `height` = 2 + log2(the
  stream's length / 48); a transaction under the limit by it is let
  through;
* else `Dag.dirtyNodeBound` walks the keys' paths at the latest state
  and counts: the distinct key nodes on them; for each node, the klongs
  it can get (one a put and a new segment below, the overflows of its
  children, four on a delete's path) and its overflows, 1 + (k - r - 1) /
  q for k klongs and r free, q = max(2, min(B / 2, B - h, B - c) - 3)
  (10 at B = 30); a node that overflows counts at least PE's parts of its
  list, `cutPartsBound(size + k)`, as new nodes and as klongs in its
  parent, and a root the new roots above them (`rootsAbove`); the new
  segment trees PE's parts and roots, or the old count if more; for the
  deletes, the root collapses below each segment leaf and four nodes for
  each level of the path and two more levels (the old writer's merges);
  a node over theta dead klongs overflows at least once;
* each node at 32 + 16 (B + 1) + 16 bytes, and two top nodes.

The count was argued for the writer of formats 6 and 7; for PE it is
argued in its Javadoc since 028-21, which found it short in three ways
and added them (a new segment tree of more than h entries cut into
parts; a node cut into more parts than its overflows and one, its
parent a klong short; the new root above a cut segment root). Joins are
covered by a delete's four nodes a level, as a child is joined only if a
delete below it left it under m entries (V1). Checked by C-T8 (the key
nodes the transaction marks are at most the bound, every traced
transaction, with the Lean copy) and DagTester's
`testDirtyNodeBoundOfPe`, `testDirtyNodeBoundOfDeletes`,
`testDirtyNodeBoundSumsCollapsesOverTrees`. Reclaim's internal
transactions are not checked (027-13, 1.4).


## 5. In the model

* **Definitions**: lean/contract/Contract/PeWriter.lean,
  `Contract.PE.peTx` and its parts (`Cfg`, `route`, `applyGroups`,
  `planTree`, `plan`, `planKids`, `rebalance`, `joinAt`, `findSmall`,
  `cntOf`, `openEs`, `settleRoot`, `mkNode`, `ents`, `decideNode`,
  `cutParts`, `nParts`, `partSizes`, `emit`, `emitKids`, `newParts`,
  `emitKs`, `newTopNode`): PE as total functions with fuel on the
  contract's tree, each Java method naming the definition it restates.
  Its differences of form from Java change no node: a node is named by an
  id, not by the pointer that reached it; heights come from levels; a
  delete that deletes makes no node (Java makes a delete node, with an
  id); a recursion, not frames. lean/SIS/Tree/Pe.lean is its copy on the
  tree model's P, with Java's ids (a delete node takes one), bitmaps as
  bit sets and cap = B / 2, for the tree checker; 026-25's `pecmp` found
  the two equal on Java's traces (026-25, section 3).
* **Proved** (030-21; lean/contract, `gate.sh`, Lean's three standard
  axioms):
  * `pe_step`, `pe_meetsTop`, `pe_meetsTop_start`: every history PE
    writes from the empty tree meets the writer's contract, TREE and the
    top's clauses; so every get and scan at every time gives the plain
    map's answer (the contract's read theorems, 030-05, 030-08);
  * `pe_full`, `pe_crash_reads`: such histories meet `MeetsFull` and
    K-LEVEL, so recovery, restarts, lazy reading, eviction with handles
    and reclaim's safe cuts hold for PE (030-07, 030-14, 030-17), given
    the top nodes' level at most 2^62, fewer than 2^48 - 1 transactions
    and each transaction's keys distinct;
  * `pe_accepts`, `pe_refuses`, `pe_accepts_step`, `pe_extend`: PE
    accepts every transaction whose puts' keys the tree can hold, if the
    height leaves room and the fuel suffices (below).

  For any cut size from 1 to B - 1 and h and c alike (`Cfg.Ok`).
* **The limits at which the model refuses** (030-21, part 3):
  * a put of a key that is not well formed or has more than G + 1
    segments (`keyOk`): exact; a delete of such a key is a noop
    (`dropNoops`);
  * the height (`Room`): every node's height e leaves 2^(H - e) more
    than the tree's nodes plus the operations; sufficient, not exact
    (refused only where a root at height H would be cut);
  * the fuel (`FuelOk`): (G + 1)(H + 1)(B + p + 2H + 6) at most 2^40 for
    p operations; sufficient.

  Java has none of these: no level bounds G and H (a key's segments are
  bounded by L2 and L3, 111 bytes for a user's key, 57,344 bytes of keys
  a transaction for BergDB's own, 024-17), no fuel; so Java refuses
  nothing in the writer (1.2), and a tree beyond H is outside what is
  proved.
* **Left out** of the model: the short way and the decisions by counts
  (1.10; Java's equality with the model is checked, not proved); the
  order of the marks; the reads of nodes not in memory (eviction,
  part 8); the record's bytes.
* **Conformance**: the tree checker (`treecheck`, `treeconf.sh`; 027-02,
  section 4): C-T1 the change (Java's nodes made, with ids, levels and
  kinds, and entries added, against Pe.lean's), C-T2 the klongs of each
  node changed, C-T3 the noops, C-T4 the reads, C-T6 the invariants, C-T7
  the form (keys strictly increasing), C-T8 the bound (4.2), C-T9 the
  whole run (records, gd as a set, D); the contract checker
  (`lean/contract/check.sh`: the contract on Java's tree before and after
  every traced transaction); the bridge checker.


## 6. In Java

* `dag/PeWriter`: `run` (1.3), `shortWay`, `shortLeaf`, `innerChild`
  (1.10), `TreeFrame` (planTree), `NodeFrame` (plan of an inner node,
  `routeBySearch`, `routeByList`, `appendedByCounts`), `LeafFrame`
  (applyGroups, `leafNode`), `mkNode`, `ents`, `decide`, `cutParts`,
  `nParts`, `partSizes`, `rebalance`, `joinAt`, `findSmall`, `cntOf`,
  `openEs`, `settleRoot`, `emit`, `append`, `appendPlanned`,
  `appendChanges`, `emitBits`, `live`; its class comment.
* `dag/Dag`: `putKvs`, `putKv` (a transaction of one operation, for
  tests); the thresholds (`splitAbove`, `minFill`, `mergeCap`, `theta`,
  `cutSize`, `deadCount`); `dirtyNodeBound`; `stat*`. `dag/TopDs`:
  `findRoot`, `newSuperRoot`. `dag/KeyNode`: `addKlong` (a time klong
  first when the node has none of tt), `addKlongCopyPointer`,
  `addDeleteKlong`.
* `core/Db`: `putKvs` (the batch), `newPutData`'s listeners (ids,
  `markAtEndOfOp`), `endOfOp`, `endOfTrans`, `makeDirtyIfNeeded`,
  `checkDirtyNodes`; `core/DbStarter.rerunTransaction`; `core/TransCheck`.
* The C clone (012) has release 2026.2's writer (splits, no merges), not
  PE.


## 7. Tests

* **Gated by `before-commit.sh`**: DagTester (22 tests, among them
  `testTwoNewRootsInOneTransaction`, `testShortWayLeafAroundASegmentTree`,
  `testTransactionLeavesNoUnreachableNode`,
  `testDeleteEveryKeyAfterTheRootSplit`, the two of the bound), MergeTester
  (6, `testFillAfterEveryTransaction`, `testNoChainOfSingleChildren`,
  `testThresholds`), DeadKlongTester (5, `testCompactionAtTheta`,
  `testRandomAtMostTheta`), `DbTesterLongKeys`; TransCheck on in the unit
  tests.
* **In the level scripts and the night**: `level1.sh`'s DagFuzz (node
  sizes 8 to 62, against a model of every key's history); `level2.sh`'s
  tree checker on the small, drain and reclaim sets (C-T1 to C-T9, the
  joins required in each draining configuration), A2A3Check2's MARKING,
  the contract checker; `transcheck.sh` (TransCheck in the unit and
  f-tests); `stress/unlinkfuzz.sh` (UnlinkFuzz: gets and scans at every
  time, LE-b, BU1, TP39, the key ranges); `treeconf.sh medium` by hand.
* **The model**: lean/contract's gate (the proofs, and
  `Contract.PE.Example`, a history of three transactions computed by the
  kernel); 030-21's runs of `peTx` on 288 traces (221,142 transactions,
  the contract's checks at each).


## 8. Principles and rules

* **P1**, no stop-the-world: a transaction's work is its paths and its
  joins' neighbours, at most 500 operations (L1).
* **P2**, a deterministic stream: the writer is a function of the tree,
  the batch, tt and B (1.12); the order of its reports, and so of D, is
  fixed for each transaction (1.10).
* **P11 and P13**, simple before optimal: the theme of release 2026.6;
  PE replaced the per-operation writer, its five splits, the take-back
  and the merges at the delete, about 8 % slower in CCBench (026-25,
  section 6; 028-19).
* **P12**, a small Core: keys and values are bytes; the writer knows
  nothing of objects or indexes.
* **R1**: a refused transaction changes nothing: every refusal is before
  the go point; the writer refuses nothing (1.2).


## 9. Limits and open work

* **dirtyNodeBound** is argued for PE since 028-21 (4.2), given V1.
* **The order of the marks** differs between the short way and the plan
  (1.10); the model checks D as a set: 028-25 (keep both orders as
  described here, or make the short way report in emit's order).
* **Speed**: PE's set test 11 to 18 % slower than format 7's writer, the
  load up to 10 %; reclaim's pace with PE: 028-19.
* **Java against the model**: tested node for node on the traces, not
  proved; the short way and the decisions by counts are argued equal to
  the lists' decisions in `PeWriter`'s comment.
* **Not proved**: RootsOK, V1 and BU1 (section 3), the rerun's equality
  (1.12).
* **The thresholds** for node sizes other than 30 are scaled, not
  decided (024-14, QT2).
* **Startup**: the rerun's reads of M1's neighbours are not in the
  cold-read bounds, and `DropStep` was not examined against PE's cuts,
  joins and collapses (027-11, sections 5 and 9).
* **Stale comments** of the old writer in Java: 028-22.


## 10. A worked example

B = 8: h = 4, m = 2, c = 4, theta = 2, cap = 4. Keys of one byte, each a
key of one segment; a cv is written as its byte, '' for the empty key.
A node is written `nX leaf [klongs]` or `nX inner [...]`; a klong `Tt`
(a time klong), `cv->target` (a key klong) or `B{i}` (a bitmap, klong i
deleted); a value `nX=v`. The ids are numbered 1, 2, 3 in the order made;
in Db they are the vposs after the record's position (1.8). Each step
below was run by `Dag.putKvs` (a probe of this item, with a listener that
numbers the nodes; not kept). "Marked" lists 1.9's marks in order; a
marked node that is dirty already does not join the got-dirty list.

**Start**: the space root is n1, an empty segment leaf, `n1 leaf [T0]`;
the top node n0.

**T1**: puts of a to j (value 1). Plan: n1's final list is 10 new
entries; its klongs and 1 + 10 more do not fit B = 8, and 10 > h, so
parts cutParts(10) = max(2, ceil(10 / 4)) = 3, sizes 3, 3, 4 (the larger
last). Settle: a space root of 3 parts gets a new root of 3 entries,
cutParts(3) = 1. Emit: the values n2 to n11 were made in the plan; the
three parts n12, n13, n14, then the root n15; n1 is not reachable; a new
top node n16.

    n15 inner [T1, ''->n12, d->n13, g->n14]
    n12 leaf  [T1, a->n2=1, b->n3=1, c->n4=1]
    n13 leaf  [T1, d->n5=1, e->n6=1, f->n7=1]
    n14 leaf  [T1, g->n8=1, h->n9=1, i->n10=1, j->n11=1]

Marked: n0, n1 (the find of the root), n12, n13, n14, n15, n16; n1 and
n0 are replaced, so they do not stay in T1's got-dirty list.

**T2**: put c (value 2), delete d, delete e, put k (value 2), delete x.
Five operations: the short way is tried and not taken (n13 would hold
one entry, fewer than m). Plan:

* n15 routes a to c to n12, d and e to n13, k and x to n14.
* n12: c repointed to the value n17; append fits (4 + 2 klongs) with 1
  dead klong: append.
* n13: delete nodes n18 (d) and n19 (e); F = [f]: append (a time klong
  and a bitmap), but 1 < m.
* n14: k new (n20), x a noop (no entry, nothing made): append (5 + 2).
* Rebalance at n15: n13 is the first changed child with fewer than m
  entries; it has a left and a right neighbour, and the left one's count
  plus its own, 3 + 1, is at most c = 4: it joins n12. The joined list
  [a, b, c->n17, f] is one new node (nParts(4, 4) = 1); n12's append is
  never written; n12 and n13 are not reachable after.
* n15: F = [('' new), (g n14)]: d removed, '' repointed. A time klong, a
  bitmap and one key klong fit (4 + 3 = 7); its dead klongs would be 0 +
  1 + 1 = 2, not more than theta: append. The root settles as it is.

Emit, bottom-up: the joined node n21 (made), n14 (changed), n15
(changed); no new top node.

    n15 inner [T1, ''->n12, d->n13, g->n14, T2, B{2}, ''->n21]
    n21 leaf  [T2, a->n2=1, b->n3=1, c->n17=2, f->n7=1]
    n14 leaf  [T1, g->n8=1, h->n9=1, i->n10=1, j->n11=1, T2, k->n20=2]

The record holds the values n17 and n20 and the delete nodes n18 and
n19, nothing of x. Marked: n16, n15, n21, n14.

**T3**: put b (value 3). The short way is taken: the descent n15 to n21;
n21 keeps 4 entries (at least m), 5 + 2 klongs fit, 1 dead klong. The
value n22; n21 gets `T3, b->n22=3` and is reported changed; n15 is on
the path. Marked: n16, n15, n21.

    n21 leaf  [T2, a->n2=1, b->n3=1, c->n17=2, f->n7=1, T3, b->n22=3]

**T4**: put a (value 4). Not the short way: n21's 7 klongs and 2 more do
not fit. Plan: n21's F has 4 entries, which do not fit it: parts
cutParts(4) = 1 (4 <= h), a new node; n15's F = [('' new), (g n14)] with
'' repointed: 7 + 2 klongs do not fit: parts cutParts(2) = 1, a new root.
Emit: the value n23 (in the plan), n24, n25, a new top node n26; n21 and
n15 are not reachable. Marked: n16, n15, n24, n25, n26; n15 and n16 are
replaced.

    n25 inner [T4, ''->n24, g->n14]
    n24 leaf  [T4, a->n23=4, b->n22=3, c->n17=2, f->n7=1]

**T5**: delete g, h, i, j, k. Not the short way (n14 would be empty).
Plan: the delete nodes n27 to n31; n14's F is empty. Rebalance at n25
drops n14; n25's F = [('' n24)]. Settle: an inner root with one entry
collapses to its child, the untouched n24, a segment leaf: the root.
Emit writes no key node; n14 and n25 are not reachable; a new top node
n32 names n24, the space root from T5 on. Marked: n26, n25, n32; n26 and
n25 are replaced, so of these only n32 stays in T5's got-dirty list.

    n24 leaf  [T4, a->n23=4, b->n22=3, c->n17=2, f->n7=1]

Every earlier state stays readable: a get of g at time 3 finds T1's top
node n16, follows it to n15, reads n15's klongs up to time 3, and finds
n14 and the value n8.


## 11. Evidence

006-28 (NW, each node made once from the net change); 026-23, section
1.2 (PE's design); 026-24 (the trial in the model: no fault on 288
traces, bytes, the cut size B / 2); 030-21 (the proof, parts 1 to 3);
026-25 (Java's PE, format 8, the ways by counts, the gates, the timings);
024-11, 024-14, 024-21, 024-22 (the fill rule, the thresholds, M1); 024-18,
024-19, 024-23 (theta and option 2); 023-07, section 5.2 (LE-b); 024-17
(the limits L1 to L5); 005-31 (the dirty-node check); 030-04, 030-05
(the contract); 030-09 (TransCheck).


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The description of the writer since record format 8, PE
(026-25).

2026-11-19. A summary of PE, until the part is written, from the code at
`b03dcea7` (`PeWriter`, `Dag.putKvs`) and 026-25. By an agent of
coord-1118, on the branch `027-pe`.

2026-11-19. Written in full (Frans, 10:54: "Write it for me."), from the
code at ba81b104 (`PeWriter`, `Dag`, `Db`, `DbStarter`, `TopDs`), the
proved program (Contract/PeWriter.lean), 026-23 to 026-25, 030-21, 027-02
and 027-03; the worked example run on `Dag.putKvs` by a probe. Found: the
short way and the plan mark D's nodes in different orders (1.10),
registered as 028-25. By an agent of coord-1118, on the branch
`027-08-writer`.

2026-11-19. 028-21: 4.2 and 9, `dirtyNodeBound` argued for PE and its
three gaps closed. By an agent of coord-1118, on the branch
`028-21-dirty-bound`.
