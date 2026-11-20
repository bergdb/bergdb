# 030-29. The dirty-node bound proved for PE

Created 2026-11-20 by Frans Lundberg. Status: open.

Java's `Dag.dirtyNodeBound` (java/src/bergdb/dag/Dag.java) bounds the index
nodes that a transaction can make dirty or create; `Db.checkDirtyNodes`
refuses a transaction before its go point if that count, each node at its
largest, could take the record past the record limit (rule R1; 027-08,
section 4.2; 027-03, section 8). If the count were short, a transaction Java
admits could need a record above the limit after the go point. 028-21 found
it short for the writer PE in three cases of puts, fixed them, and argued
the fixed count on paper; Frans decided on 2026-11-20 to prove it. This item
models the count in Lean, function for function, and proves that it bounds
the key nodes the proved writer PE (030-21) writes; and it proves 030-28,
section 5's argument that `pe_accepts`' premises hold for Java's parameters.
Done by an agent of the day's coordinator on the branch
`030-29-dirty-bound-proof`, with two helper agents for parts of the Lean.


# Result

- **Proved for transactions of puts** (`Contract.PE.pe_dirtyNodeBound_puts`,
  section 2): from a state PE keeps whose tree meets the writer's fill
  rules, for every transaction of puts that PE accepts, the key nodes PE
  writes are at most Java's count, at Java's parameters at every node size
  from 8. Every node PE writes once (030-21), and each has at most the node
  size of klongs, so Java's bytes for the record's index nodes bound PE's.
  The premise on the fill rules (RootsOK, FillOK) is what the tree checker
  checks on Java's tree after every traced transaction (C-T6); that PE keeps
  them is not proved.
- **Not proved for transactions with deletes.** The leaf's and the new
  segment trees' parts are proved (section 4), but not the joins of
  `rebalance`, in particular a join of two inner nodes that is rebalanced
  one level down, where cut parts merge again; there 028-21's paper argument
  has a false step, shown by a constructed transaction (section 4), though
  the count covers that case many times over. The count holds on every
  transaction tried
  (section 3): its deletes' terms are generous (4 nodes a level and 8 a
  delete), and 028-21 found deletes at least 5.7 times under it.
- **The model of Java's count** is `Contract/DirtyBound.lean`, a
  restatement of `dirtyNodeBound` and the methods it calls, compared with
  the Java line by line in section 1. Java's walk and the structural count
  of the proof are proved equal (`dirtyNodeBound_eq_sb`).
- **PE accepts every transaction Java admits** (`pe_accepts_java`, section
  5): at node sizes 8, 14, 30 and 62, with the model's G = 8,192 and
  H = 126, every transaction of at most 2^20 operations whose puts' keys the
  tree can hold, on every tree of fewer than 2^63 nodes that meets the fill
  rules. 030-28, section 5, said H = 100: that holds at node sizes 30 and 62
  but not on every such tree at 8 and 14 (section 5); H is the model's
  parameter, which Java does not have, and H = 126 serves all four. 030-28
  and 030-26 are corrected.
- **No defect found in Java.** Nothing here changes Java; no 028 entry.


# 1. The model of Java's count

`Contract/DirtyBound.lean`, namespace `Contract.DNB`, nothing from Mathlib.
Each definition restates one method of `Dag` (java/src/bergdb/dag/Dag.java,
lines as on `main` 6d379122):

- `splitAbove`, `minFill`, `mergeCap`, `cutSize`, `theta`: Dag's static
  methods of the node size b (lines 1084 to 1109, 1159), the same integer
  arithmetic. `roomAfterReplacement` (line 1121): `max(2, min(b / 2, b - h,
  b - c) - 3)`; Java's int below zero is 0 in Nat, and `max` with 2 gives the
  same.
- `overflowsD b klongs size merged dead` is `overflows(klongs, size, merged,
  dead)` (line 775): 0 for no klongs; `least` 1 if theta > 0 and dead +
  klongs > theta (Java's dead = -1 for a new tree is `none`); k = klongs + 1;
  `room = max(0, b - 2 - size)` is Nat's `b - 2 - size`; `min(room, q)` if
  merged; then `least` if k ≤ room, else `1 + (k - room - 1) / q`.
  `overflows` (line 761) is the three-argument form, which passes -1.
- `cutPartsBound` (line 851), `rootsAbove` (line 861): the same; Java's loop
  `for (p = parts; p > 1; ) { p = min(p - 1, cutPartsBound(p)); count += p; }`
  is `rootsAboveLoop` with fuel p (p falls each time).
- `freshTreeBound` (line 800): Java loops over a stack of trees; the model
  recurses over the trees below, which sums the same counts (Java's comment:
  "The count is a sum, the same in any order"). `freshGroup` is the loop over
  one tree's keys (a klong for each key that ends at the level, and one the
  first time each other segment is met, the key added to that segment's
  list); `freshSplits` is the loop `for (ov = overflows(klongs, 0, false);
  ov > 0; ov = overflows(ov, 1, false)) splits += ov + 1`; the tree counts
  `max(splits, parts + rootsAbove(parts))` with `parts =
  cutPartsBound(klongs)`, as line 838. Java's `HashMap` of segments is a
  list in the order first met; the sum does not depend on it.
- `Walked` is `Dag.Walked` (line 712) with the node's `size` and `leaf`
  read once (Java reads `w.node.size`, `w.up.node.isSegmentLeaf()`; the node
  does not change during the call). `Walk.reach` is `walked(walked, node,
  up)` (line 746): a record keeps its first `up` and depth. Java's
  `IdentityHashMap` of walked nodes is a list by node id, in the order first
  reached. `Walked.addFresh` is `Walked.fresh(key, i)` (line 731).
- The first loop (lines 610 to 662): `walkAll` over the keys, each
  starting at the space root (`walked(root, null)`), `walkKey` over the
  key's segments (`for (i = 0; i < key.length; i++)`, fuel the key's length
  and one), `descend` the inner `while (!node.isSegmentLeaf())` with
  `searchLte`, the contract's `searchLte` and `searchEq` (Contract/Tree.lean,
  Java's loops over the klongs at the time; `searchEq_spec`, `searchLte_spec`
  prove them lookups in the live list). At the last segment a put's
  `w.klongs++` (line 647) or a delete's climb `markDelete` (lines 627 to
  645: four klongs and `deleteBelow` on every node up to the space root, at
  each segment leaf the inner nodes counted since the last one as the
  collapses of the tree's root below it) and `mergeLevels += depth + 3`
  (line 632); else `searchEq` in the leaf: a missing segment is a put's new
  tree (`fresh`) and ends the walk.
- The second part (lines 664 to 708): the count starts at the walked
  nodes; after a delete each walked node's collapses go to the node above
  (`addCollapses`, line 668); the records sorted deepest first (Java's
  `Collections.sort` by depth, stable; the model's `mergeSort`, stable too;
  the order among equal depths changes nothing, as a node changes only the
  klongs of the node above it); `countNode` is the loop body: the new trees
  (line 686), the overflows (line 689), the parts (line 692), the parent's
  klongs (a parent in the tree gets the parts; a tree's root counts the new
  roots above and gives the segment leaf above its overflows and one), and
  `4 * mergeLevels` after a delete (line 706).
- Java's arguments: Db passes the transaction's keys and, for each,
  whether it is a delete (`Db.checkDirtyNodes`, java/src/bergdb/core/Db.java,
  line 3306 on main 4de9ca7f); `opsKd` gives them for a transaction without key or value
  transformations. A key transformation is counted coarsely by Db itself; a
  value transformation is walked as a put and as a delete, which the
  theorem does not cover (a transaction of puts has none).
- What PE makes dirty: `keyWrites`, the key nodes among PE's writes (each
  node once, 030-21's `pe_step`). Db's check multiplies the count by a key
  node's largest size and adds the top nodes; PE's top node is written apart
  (`Out.top`), and Db counts it apart.

- The time. Java's searches read the klongs at the lookup time, its
  `w.node.size` and `deadCount(node)` the node as it is; the model reads
  both at `s.at t`. Db passes the latest time, `dbClock.lookupTime(MAX)`,
  which every transaction's end sets, so no node has a klong after it (the
  theorem's `Inv` says the same), and the two agree. At an earlier time
  Java's sizes and dead counts could only be larger, the safe side.
- What Db does around the call: when its cheap estimate (three nodes a
  level of a put's path, twenty of a delete's) fits, Db does not call
  `dirtyNodeBound` at all, and a key with a key transformation is counted
  only by that estimate. That the estimate bounds PE is not proved here
  (028-21 argues that it is above PE's own count).
- Java's long arithmetic does not overflow for any transaction Db admits;
  the model's numbers are unbounded.
- One difference outside the theorem: at node sizes of 4 and below, Java's
  loop of the splits in `freshTreeBound` (line 833) never ends once
  `overflows(ov, 1, false)` is 1 (room 1 or 0, q = 2); the model's fuel ends
  it. Only Dag's own tests use such sizes (a database has node size 30; 8,
  14 and 62 are for BergDB's tests; DbBuilder), and the theorem needs 8 or
  more. A defect of test sizes only, for a later 028 entry if wanted.

A second reading of the model against Dag.java, KeyNode's searches and
Db.checkDirtyNodes, by a helper agent, found no difference that could make
the model count more than Java at the arguments Db passes, besides the
points above.

That the model is Java's count rests on this reading, as PE's model rests
on 030-21's; the tree checker's own copy of the count
(lean/SIS/Tree/Bound.lean, C-T8) is a second restatement, checked on the
traces against the nodes Java marks.


# 2. The theorem

`Contract.PE.pe_dirtyNodeBound_puts` (Contract/Proof/DnbMain.lean; the
statement's definitions in Contract/DirtyBoundStatement.lean):

    theorem pe_dirtyNodeBound_puts {b G H : Nat} (hb : 8 ≤ b) {t i : Time}
        {s : Tree} {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
        (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
        (hputs : ∀ op ∈ ops, ∃ k v, op = .put k v)
        (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
        keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops)

In words: take a state that PE keeps after the transaction of time t
(030-21's `Inv`: the contract's invariants, TREE, PE's shapes) at Java's
parameters at node size b ≥ 8 (`Cfg.java`: h = c = 17 b / 30, m, theta, the
cut size b / 2; G and H are the model's level bounds, free), whose tree meets
the writer's fill rules (`FillOk`: `shapeFaults`, Contract/Shape.lean, finds
no fault; the contract checker reports its faults on Java's tree after every
traced transaction, and the tree checker's C-T6, its own restatement of the
rules, fails on them). For every transaction of puts that PE accepts, at any
time i, the
key nodes PE writes are at most Java's `dirtyNodeBound` of the transaction
on the tree read at t, the lookup time Db uses (the latest). A transaction
without operations writes none.

`Contract.PE.pe_dirtyNodeBound_puts_hist` says the same for every history
PE writes from the empty tree (030-21's `PeHist`): the next transaction of
puts, on a tree that meets the fill rules, writes at most Java's count of
it, read at the history's last time.

`Contract.PE.DnbExample` (Contract/DnbExample.lean) shows the premises can
hold: from the empty tree at node size 30, a transaction of two puts, one
key node written and counted.

How it is proved (Contract/Proof/Dnb*.lean):

- `dirtyNodeBound_eq_sb` (DnbWalk.lean and the files it imports): Java's
  walk computes `sbTop`, the same count as one recursion over the tree
  (Contract/Proof/DnbSpec.lean: `sbPlan`), which routes the operations among
  an inner node's children as PE does and takes a leaf's operations compare
  value by compare value. It rests on TREE: each node reached has one
  parent, so Java's records by node identity are the nodes of the paths.
- `pe_keyWrites_le_sb_puts` (DnbTop.lean): PE writes at most `sbTop`, by
  induction on PE's plan (DnbPlan.lean, `plan_tree_puts`). At each node
  of the paths: Java's klongs for it are at least the entries PE adds to
  it, so PE replaces or cuts it only where Java has it overflow, into at
  most Java's parts (DnbDec.lean, `dec_parts_ov`; dead klongs:
  `deadCount_emit`); a node kept or appended to counts as the node walked; a
  new segment tree writes at most `freshTreeBound` (DnbFresh.lean,
  `fresh_le`); the new roots above a cut root at most `rootsAbove`
  (DnbEmit.lean, `settle_chain`); emit writes exactly the planned nodes
  (`emit_kw`). With the fill rules no child of a transaction of puts has
  fewer than m entries, so `rebalance` joins nothing (DnbKids.lean,
  `rebalance_id`), and no root collapses.


# 3. Tests

The model runs. A random test (in the session's scratch, not in the
repository) wrote PE histories from the empty tree at node sizes 8, 14, 30
and 62, with transactions of random puts and deletes, runs of keys under
one new segment, runs of consecutive keys and runs of deletes, and checked
at every transaction that PE's key writes are at most the model's count:
224,000 transactions, none above, 1,468 exactly at it (puts that append to
every node of their paths), every tree meeting the fill rules. The model's
count and `sbTop` were equal on all of them, before the proof of their
equality. A second batch with more deletes (ranges thinned to every third to
fourteenth key, with and without runs of puts beside them, at node sizes 8,
14 and 30): 197,000 transactions, 127,615 of them with deletes, none above
the count; some transactions with deletes at it exactly (their deletes of
keys whose walk stops at a missing segment count nothing, and their puts
are tight).


# 4. Deletes

What is proved toward them, outside the branch and not landed: the
segment leaf with deletes (each compare value adds or removes at most one
entry, and Java counts at least one klong for an entry added and four for
one removed), a new segment tree with deletes (`freshTreeBound` of the
puts), and the interface of the induction with deletes (a node keeps four
nodes of Java's count for each delete through it, for the joins its parent
makes). Not proved: the joins.

The joins. A changed child with fewer than m entries is joined with a
neighbour; the joined list of two inner nodes is rebalanced one level down,
which joins a small child left alone in either. 028-21's argument counts, for
each delete, three nodes a level and three entries and a bitmap in the
parent, from "a joined group is its small children and at most one other
node". That is not always so, as a constructed transaction shows (run on the
Lean model, PE as proved, in the session's scratch): node size 30 (m = 8,
c = 17, cut size 15), a space root R of height 2 with three children, L, O
and P, each with eight leaves of eight keys. One transaction of 170
operations deletes all of L's keys but one, empties five of O's leaves, and
puts 23, 23 and 21 keys into O's other three leaves. L ends with one leaf of
one entry: small. O's three leaves are cut into 3, 3 and 2 parts (31, 31 and
29 entries, cut by 15), so O holds 8 entries: not small. R joins L with O;
one level down the leaf of one entry is joined with O's first leaf, whose 32
entries are cut by c into 2 parts where they were 3: the joined node holds 7
entries, fewer than m, and R joins it again, with P, a second node that is
not small. The tree after is a root of 15 leaves. PE writes 8 key nodes;
Java's count is 2,279. So the paper argument's step is wrong, but not the
count: such a join needs many deletes below the small node (it lost all its
entries but one, each through a delete), and the count's four nodes a level
for each delete cover it many times over. A proof needs an invariant that
charges each join to the deletes below it, through the joins one level
down, and a loss lemma (a node loses at most as many entries as deletes pass
through it). That is left for later work, or for a simpler rule (028).

# 5. PE's acceptance at Java's parameters

030-28, section 5, argued on paper that `pe_accepts`' premises `FuelOk`
and `Room` hold for Java's parameters with G = 8,192 and H = 100 on every
tree a stream can hold. In Lean (Contract/Proof/DnbRoom.lean,
Contract/Proof/DnbFill.lean):

- `filled_of_shapeFaults`: a tree on which the trace checker's walk finds
  no fault meets the fill rules as the proofs use them (`Filled`).
- `room_of_filled`, `room_of_bounds`: a key node at height e of its segment
  tree has at least 2^e nodes in its walk (each inner node two live
  children at least: RootsOK, FillOK), and at least 2 m^e / m; so `Room`
  holds for p operations on a tree of N nodes if (N + p) N < 2^H.
- `fuelOk_java`: `FuelOk` for up to 2^20 operations when H ≤ 126 (at H =
  128 it fails for 2^20: (G + 1)(H + 1) is then above 2^20).
- `room_java`, `accept_java`, `accept_java_of_shapeFaults`: `Room` at
  H ≥ 126 on every tree of fewer than 2^63 nodes at node sizes 8, 14, 30
  and 62.
- `room_java_100`, `room_java_100_b14`, `room_java_100_b8`: with H = 100,
  every tree of fewer than 2^63 nodes at node sizes 30 and 62 (m = 8 and
  16: a segment tree is at most 21 and 16 high), fewer than 2^61 at node size
  14, fewer than 2^50 at node size 8. At node size 8 a segment tree 61 high,
  every node with two live klongs, has 2^63 - 1 nodes, and `Room` asks
  N + p < 2^39 at its root: H = 100 does not cover it.
- `pe_accepts_java`: so, at H = 126, PE accepts every transaction of at
  most 2^20 operations whose puts' keys the tree can hold, on every tree of
  fewer than 2^63 nodes that meets the fill rules. Java admits at most 500
  operations a user transaction (`Db.MAX_OPERATIONS`); a reclaim step and a
  start's rerun are smaller. The base level of the top nodes,
  (G + 1)(H + 1) + 1, is 1,040,512 at H = 126, below 2^62 (030-26, 2.6).

Corrected in 030-28, section 5, and in 030-26 (2.1, 2.6, section 4): H = 126
in place of H = 100, and the argument is in Lean.


# 6. Files

In lean/contract/:

- Contract/DirtyBound.lean: the model of Java's count (pinned).
- Contract/DirtyBoundStatement.lean: `Cfg.java`, `FillOk` (pinned).
- Contract/DnbExample.lean: the example.
- Contract/Proof/: DnbDefs (`Filled`), DnbFill, DnbRoom (section 5);
  DnbSpec (`sbPlan`, `sbTop`, `vcost`), DnbDec, DnbEmit, DnbLeaf, DnbFresh,
  DnbKids, DnbPlan, DnbTop (PE against `sbTop`); DnbCount, DnbJava, DnbTree,
  DnbRec, DnbSb, DnbWalk (Java's walk is `sbTop`); DnbMain (the theorem).
- Axioms.lean: the new theorems' `#print axioms` lines; statements.pin:
  the new pinned files.


# 7. Gates

On the branch's Lean commit 9cd46821, in lean/contract/:

- `sh gate.sh`: GATE OK. 1. lake build passes (no warnings); 2. no
  `sorry`, `admit`, `native_decide` or axiom; 3. the standard axioms only
  (198 theorems, 191 before); 5. the statements pinned: 91 files of the
  main theorems' closure, 112 pinned (106 before).
- `sh gate.sh 6d379122`: steps 1, 2, 3 and 5 pass; step 4 lists the edits
  of 027-03 and 027-08 (outside the paths it allows, by design); step 5
  lists the pinned files changed since the base: Axioms.lean (seven lines
  added) and six new files (DirtyBound, DirtyBoundStatement, DnbSpec,
  DnbWalk, DnbMain, DnbRoom). No existing statement changed.
- `sh pins.sh`: PINS OK.
- Java is not changed: no `before-commit.sh` needed; the checkers, the copy
  of PE and pecmp are not changed.


# State

2026-11-20, 13:30. Stopped at Frans's stop for the day (the week's usage at
95 %). Done for puts, gated on the branch's head (merged with main
4de9ca7f): the model, the theorem and its form for histories, the walk's
equality, the example, section 5; 030-26, 030-28, 027-03 and 027-08
updated; the model read a second time against the Java (section 1). The
delete case is open (section 4): the leaf, the segment tree, the new
segment tree with deletes, and the decision and rebalance facts are proved
by helpers outside the branch, kept in the session's scratch for a later
session; the joins (a loss lemma, and the chains of lone small children
one level down) are not started in Lean.


# Log

2026-11-20. Created by an agent of the day's coordinator (Frans decided to
prove the bound, 2026-11-20): the model of Java's count, a random test of
it against PE (no counterexample), the proof for puts, PE's acceptance at
Java's parameters.

2026-11-20. Merged with main (4de9ca7f); gated again. Stopped at 13:30 at
Frans's stop, with the delete case open.
