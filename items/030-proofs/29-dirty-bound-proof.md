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
  needs a step it does not give (section 4). The count holds on every
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
  line 3304); `opsKd` gives them for a transaction without key or value
  transformations. A key transformation is counted coarsely by Db itself; a
  value transformation is walked as a put and as a delete, which the
  theorem does not cover (a transaction of puts has none).
- What PE makes dirty: `keyWrites`, the key nodes among PE's writes (each
  node once, 030-21's `pe_step`). Db's check multiplies the count by a key
  node's largest size and adds the top nodes; PE's top node is written apart
  (`Out.top`), and Db counts it apart.

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
equality.


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
node". A proof has to show that from PE's rules, and one step needs more than
the argument gives: in the join one level down, a small child joined with a
neighbour that was cut into parts of the cut size (15 at node size 30) is cut
again by c (17), into fewer parts, so a joined node can hold fewer entries
than its two lists did, and so possibly fewer than m though one of them held
m or more; it would then be joined again, with a second node that is not
small. This case was not constructed. It needs many deletes below the
joined nodes (a small node lost entries, each through a delete), so the
count's four nodes a level a delete would still cover it; a proof needs an
invariant that charges each join to the deletes below it, through the joins
one level down. That is left for later work.


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

2026-11-20, 13:15. Done for puts, gated (9cd46821): the model, the
theorem, the walk's equality, the example, section 5; 030-26, 030-28,
027-03 and 027-08 updated. The delete case: the leaf, the segment tree and
the new segment tree with deletes are proved by a helper outside the
branch; the inner nodes' joins are being tried by the same helper, with a
report due by 03:30. If they are proved, the theorem for every transaction
replaces the one for puts; if not, section 4 says what is open.


# Log

2026-11-20. Created by an agent of the day's coordinator (Frans decided to
prove the bound, 2026-11-20): the model of Java's count, a random test of
it against PE (no counterexample), the proof for puts, PE's acceptance at
Java's parameters.
