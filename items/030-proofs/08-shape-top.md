# 030-08. The tree's shape and its top in the contract

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 4b of 030-04: the two simplifications that 030-05 and 030-06 name,
and the shape clauses of 030-06's finding F3. TREE (no node is reached
twice) as a clause of the contract; Java's top nodes and skip pointers in
the contract's tree, with the readers' top search as Java does it
(`TopDs.findSuperRootAtTime`); the reads' theorems restated over the tree
with its top. Written by an agent of coord-1117, "I" below, on the branch
`030-08-top`.


# 1. The result

Items 1 to 3 of the work list are done; item 4 is open (section 6).

- **TREE is a clause** (item 1). `MeetsShape`
  (`Contract/ShapeStatement.lean`): a history that meets the writer's
  contract, in which the start tree and the tree after each transaction,
  at its time, meet TREE: the walk from the space root through the live
  klongs reaches no node twice, values included (`TreeOk`,
  `Contract/Reach.lean`). Proved: such a history meets the contract
  (`MeetsShape.meets`), so `inv_right`, `get_right` and `scan_right` hold
  for it unchanged; and TREE holds at every time of it, the earlier ones
  too (`tree_right`). The DAG of 030-06 does not meet it
  (`ExampleDag.not_tree`); Example3's three transactions do
  (`Example3.meetsShape`).
- **The top is in the contract** (item 2). The state is the tree and its
  top: Java's top nodes, each with its root time, its root pointer and its
  skip pointers with their cached times (`Top`, `Contract/Top.lean`).
  `MeetsTop` adds to `MeetsShape` the top's clauses (`TopStart`,
  `TopStep`): at most one new top node a transaction, the old ones fixed,
  the new one's skip pointers in index order, each naming an older top
  node with its root time cached, the lowest naming the super root before
  it; and the tree's space roots are the top nodes' root pointers. With
  them R4 (from the super root every top node is reached through skip
  pointers, `skip_closure`) and the dead top nodes (no skip pointer names
  the super root, `skip_dead`) are proved, not assumed.
- **TP24 is proved** (item 2): Java's search, `findTop`, written as
  `TopDs.findSuperRootAtTime` is (the super root if old enough, else down
  the highest skip pointers whose cached time is at or after the lookup
  time, then the node reached or the target of its lowest skip pointer),
  finds the top node made last at or before the lookup time, at a record's
  time and between two records (`findTop_right`, for any top built by the
  clauses; `top_right`, its root pointer is the tree's space root of that
  time, for any history that meets `MeetsTop`). About 420 lines.
- **The reads, restated** (item 3). `jget` and `jscan` are Java's readers:
  from the space root that Java's search finds, then the get and the scan
  of `Read.lean`. Proved for any history that meets `MeetsTop`, at every
  time, the latest and every earlier one, at a record's time or between
  two records: every get (`jget_right`) and every scan (`jscan_right`)
  gives what the plain map gives. The "one root per time" simplification
  is gone from these: no reader starts from the specification's root.
  `get_right` and `scan_right` are kept unchanged, as the step to these
  (they speak of readers that start from `Tree.root`); the new two replace
  them as the statements about Java's reads.
- **Not vacuous:** Example3's history with a top of two top nodes meets
  `MeetsTop` (`Example3.meetsTop`), and the theorems give reads between
  records through the skip pointer.
- **Tested.** The checker checks every clause on Java's traces: C4 (TREE,
  `treeOkB`), C5 (the top's clauses, the roots' link, and every SKIPT line
  against the cached times), L2 (every LIVE 0 line, Java's own top search
  at every time, against `findTop`). On the small and drain sets with
  030-09's LIVE lines: 180 traces, 21,000 transactions, 56,910 SKIPT
  lines, 1,106,157 LIVE 0 lines, no failure. What the checker computes for
  a whole trace gives `MeetsTop` (`historyTopOk_meetsTop`). Its own test,
  `faults-top.sh` (run by `check.sh`): six faults made in the top lines of
  a good trace each fail C5 or L2.
- **Lines:** about 1,400 of Lean and script, 420 of them TP24's proof.


# 2. What is proved, in plain words

For any run of transactions in which each transaction meets the writer's
contract with the shape clauses (checked on traces, not proved for Java):

- no node is reached twice from a space root, at any time;
- Java's search through the top nodes' skip pointers finds the right top
  node for every lookup time, so readers start from the right space root;
- so Java's get and scan, as written in Lean, are right at every time.

What stays assumed and tested: that Java's writer meets the clauses (C1
to C5 on traces), that Java's search code is the Lean `findTop` (L1 and L2
on the LIVE lines), and that the trace is all of Java's change (030-09).


# 3. Decisions

- **TREE as "no node reached twice"** (`(reach s).Nodup`), not the
  abstract model's form (every reached node but the root has exactly one
  reached parent among the distinct parents, `treeAt`). Mine is a little
  stronger (it also rules out one node naming the same child by two live
  klongs) and much simpler to state and to compute; Java met it on every
  trace. The bridge (030-07) derives `treeAt` from it.
- **Only at the transaction's own time in the clause;** the earlier times
  follow from the frame (`Frame.treeOk`), as the invariants do.
- **Values count.** A value node is a node of the abstract model; two keys
  must not share one.
- **The checker computes TREE by sorting** (`treeOkB`), O(n log n) a
  transaction, with a proof that it gives `TreeOk`; `List.Nodup`'s own
  decision is quadratic.
- **The top as a list of top nodes in the order made** (`Top`), beside the
  tree, not as a new kind of node in `Tree.obj`: a new constructor of
  `Obj` would touch every proof that cases on a node and every file of the
  other agents. The list is the model's root with its entries (027-02);
  Java's reader holds only its last, the super root, and the search uses
  only that and the skip pointers.
- **The skip rule without ordinals.** The clause asks what the search and
  the abstract model need: each skip pointer names an older top node with
  its root time cached, the lowest names the one just before, in index
  order. Java's rule (one skip pointer for each bit set in the ordinal,
  `TopNode.height`, each inherited or naming the super root) gives this;
  which indexes are set only makes the search take about log n steps: a
  cost property, like the fill (030-05, section 3), not in the contract.
  It also covers `TopDs.setSecondOrdinal`, the tests' jump of ordinals.
- **The cached times.** The trace gives a skip pointer's cached time only
  in the SKIPT lines of a version of the top node, written in a later
  record. The checker's top caches the root time of the node named, and
  compares every SKIPT line with it (C5): Java's cached times are checked
  wherever a version of the top node is written; the newest top node of a
  trace, never written, is checked only through the LIVE lines.
- **Between records.** Java looks up at clock times; between the records
  t and t + 1 the model's time is t with `mid` true, as the old model had
  it (`lean/SIS/Tree/Top.lean`). The checker reads the second LIVE 0 line
  of a time as `mid` (`TraceExport.recordLive` writes the record's time
  first, then the last time before the next record, if there is one).
- **The old statements:** `get_right` and `scan_right` are kept, not
  restated; `jget_right` and `jscan_right` follow from them and TP24.
  Nothing existing was restated in this item.
- **030-09's LIVE lines.** 030-09 landed first with LIVE lines in the tree
  sets (hot and d-random, `live=1`) and L1, which compares Java's top node
  through its root pointer with the contract's space root. I built on
  them: L2 compares the same lines with the Lean search itself, top node
  by top node; `TraceTop.lean` reads 030-09's `lives`.
- **New files, the shared ones in small hunks** (common rules):
  `Reach.lean`, `ShapeStatement.lean`, `CheckShape.lean`, `Top.lean`,
  `TraceTop.lean`, `HistoryTop.lean`, `Proof/Reach.lean`, `Proof/Top.lean`,
  `TheoremsShape.lean`, `TheoremsTop.lean`, `ExampleShape.lean`,
  `faults-top.sh`; in `Trace.lean` three fields and three line kinds (S
  entries, VER, SKIPT); in `ContractCheck.lean` the C4, C5 and L2 lines;
  in `check.sh` one line; `Contract.lean` and `Axioms.lean` at their ends.


# 4. The clauses, in English

TREE (`TreeOk`): walk the tree from the space root through the live
klongs, as the invariants' walk does, and list every node reached, values
too: no node is in the list twice.

The top (`TopStep i tp tp'`, the transaction at time i):

- T1. Either no top node is made, or one: added at the end, the new super
  root. Every top node before it stays as it was.
- T2. The new top node's id is not one of a top node before it; its root
  time is i.
- T3. Its skip pointers are in increasing order of their index; each names
  a top node before it and caches that node's root time; the first names
  the super root before it.

The start (`TopStart`): one top node, of time 0, with no skip pointer.
The link: the tree's space roots are the top nodes' root pointers, with
their root times (`Tree.roots = rootsOf tp`).


# State

2026-11-17, 15:45. Items 1 to 3 done and gated; item 4 next. Branch
`030-08-top` in the clone `/Users/f/fl/bench/2026-11-17/night/s4b/clone`,
main 9a6692cf merged in (030-09's completeness and LIVE lines).

- Build: `cd lean/contract && lake build`. Gate: `lean/contract/gate.sh
  9a6692cf`. Traces: `java/build.sh`, `cd lean && lake build treecheck`,
  `java/stress/treeconf.sh small` and `drain`, then
  `lean/contract/check.sh` (runs faults.sh and faults-top.sh first).
- To read first: `Contract/Top.lean` (the top, Java's search, the
  clauses), `Contract/ShapeStatement.lean` (`MeetsShape`, `MeetsTop`),
  `Contract/TheoremsTop.lean` (the theorems).


# Log

2026-11-17, 15:09. Started from the brief of coord-1117.
2026-11-17, 15:24. TREE as a clause: `MeetsShape`, `tree_right`, C4 on
the small and drain sets (180 traces, no failure).
GATED 1a1a441b: TREE as a clause of the contract (`MeetsShape`, `tree_right`), C4 on the traces.
