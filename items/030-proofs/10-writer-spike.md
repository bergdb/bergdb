# 030-10. Does the model's writer meet the contract? A spike

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 5 of 030-04, optional there (section 3.6): a proof that the model's
writer (`lean/SIS/Tree/Exec.lean`, the run of `Tree.exec?`) meets the
writer's contract. Frans asked whether it could later be proved and fitted
in for full completeness; this spike finds out how hard it is now. Written
by an agent of coord-1117, "I" below, on the branch `030-10-writer`, in the
night of 17 November.


# 1. The result

(Kept current; the last update is in the State note.)

- **The map is right** (item 1). The writer's state within a transaction
  gives the contract's tree, its top and D (`treeOf`, `topOf`, `dirtyOf`,
  `Contract/Writer.lean`). On the 195 traces of the small, drain and
  reclaim sets (29,735 transactions, 318,900 operations) the map of the
  model's state after each transaction is Java's tree and top, node for
  node (`lean/contract/writer.sh`: WRITER OK).
- **The statement** (item 2), `Contract/Writer.lean`, section 3:
  `OpStep`, one operation keeps `Mid` (the contract's invariants, the
  contents, the frame, TREE, the top's clauses, BalancedOK and twelve
  books of the writer, B1 to B12); `WriterMeets`, one transaction meets
  the contract. Checked on the same traces after every one of the 318,900
  operations, inside the transactions too: no failure.
- **Proved so far:** the step from operations to a transaction and to a
  history. If every operation keeps `Mid`, the writer meets the contract
  for every transaction (`writerMeets_of_opStep`), and a run of the writer
  is a history that meets `MeetsTop` (`runs_meetsTop_of_opStep`), the
  premise of the theorems on reads. What is left is `OpStep` itself, for a
  put and for a delete.


# 2. The map (item 1)

The model's writer keeps an overlay over the tree before the transaction:
the key nodes it read, made or changed, as klongs (`W.nodes`), the values
made, the nodes taken back, its top node. The map, `treeOf i s w`, from the
tree s before the transaction at time i and the state w:

- a node taken back is no node;
- a key node of the overlay is that key node, with the level it had in s,
  or for a node made the level the writer gave it (the trace's NEW line);
- a value made is a value; any other node is as in s;
- the space roots are those of s, and the writer's root pointer with time
  i if it made a top node; the top (`topOf`) likewise;
- D is the overlay (`dirtyOf`). The frame holds for any D that holds the
  nodes changed and made; that the model's D is Java's is `treecheck`'s
  test (C-T9).

The writer reads the tree through a view of the abstract model's structure,
where a key node is its entries. `Shows` says that the view shows the
contract's tree: every key node is in the view with its level and the
entries of its klongs, and the writer's super root is the last top node.

The check (`lake exe writercheck`, `lean/contract/writer.sh`), for every
traced transaction, on Java's tree before it (the contract checker's) and
the model's view of it (the tree checker's):

- S: `Shows` and the books of a start (`Books`: the times before i, the
  ids below the first id, the space roots the top's);
- M: after the model's run of the operations, the map of its state is
  Java's tree after the transaction, for every id of both, and the top;
- J and B: after every operation, on the map of the state then (section 3).


# 3. The statement (item 2)

`Contract/Writer.lean`, section 3, in English and in Lean.

- `Mid`, between two operations of a transaction: J1 the contract's
  invariants; J2 the contents are those before the transaction with the
  operations so far applied; J3 the frame; J4 TREE; J5 the top's clauses;
  BalancedOK; and the books B1 to B12 (which nodes are made, the times,
  what `madeFor` names, no klong names a node taken back, the levels, the
  ids, replaced nodes as they were, made nodes reached, the bounds).
- `OpStep`: an operation that `putKv` accepts, and that leaves no key node
  outside the bounds G and H, keeps `Mid`.
- `WriterMeets`: from a tree with the invariants, TREE, BalancedOK and the
  books of a start, shown to the writer, the accepted operations of a
  transaction end in a state whose map meets the contract, TREE, the top's
  clauses, and what the next transaction starts from.
- `Runs`: a run of the writer, transaction by transaction.

Decisions, with reasons:

- **D1. The fill is not in the statement,** nor RootsOK, LeftmostOK and
  DeadOK. The writer checks what it relies on as it goes: no sibling to
  merge with, an inner node without the empty key's klong, an emptied
  inner space root are errors (Java's `Bug`). A transaction with an error
  is not accepted, and the contract speaks of the accepted ones (030-04,
  section 3.2). So the statement is: what the writer accepts is right. That
  the writer never gives an error from a tree in shape is a statement of
  its own, not made here; the fill comes back there, not here.
- **D2. BalancedOK is in it.** A merge joins the klongs of two siblings
  into a node of the height of one of them; the contract's rule that a
  pointer goes to a lower level then needs the siblings on one height.
- **D3. The accepted operations are taken one by one** (`OpsRun`), each
  with no key node outside the model's bounds G and H after it. The bounds
  are the model's (024-12, D5), not Java's; with a node outside them the
  model's levels are not ordered. `exec?` itself looks at the bounds only
  at the transaction's end, and lets a later operation take such a node
  back; that case is not covered. None on the traces: B11 holds after
  every operation.
- **D4. The writer's view after the transaction is not covered:** that the
  model's change (`changesOf`), applied to the abstract structure, is
  shown again as the map of the last state is the model's round trip
  between klongs and entries (024-12, D3 and D4). `Runs` asks for a view
  that shows the tree at each transaction; the tree checker tests it
  (C-T2).
- **D5. The books are statements over every node; the checker computes
  them over the heap's nodes.** No proof ties the two (as `frameCheck_sound`
  does for the frame). The books are candidates: the proofs of `OpStep`
  may need more or fewer.


# State

2026-11-17, 16:15. Items 1 and 2 done; the reduction from `OpStep` proved;
`OpStep` open.

- Branch `030-10-writer` in the clone
  `/Users/f/fl/bench/2026-11-17/night/s4d/clone`, from 030-07's branch
  (d579f7e9) with main 5081565d merged in.
- Build: `cd lean/contract && lake build`. Gate: `lean/contract/gate.sh
  5081565d` (the main commit merged in; 9a6692cf is before it, and main's
  own later files then count as changed).
- Traces: `java/build.sh`, `cd lean && lake build treecheck`,
  `java/stress/treeconf.sh small`, `drain` and `reclaim`; then
  `lean/contract/writer.sh` (and `check.sh` as before).
- To read first: `Contract/Writer.lean` (the map, the statement),
  `Contract/Proof/WriterRun.lean` (the reduction), `WriterCheck.lean`.


# Log

2026-11-17, 15:50. Started from the brief of coord-1117; main (030-08's
top, 030-09) merged into the branch.
2026-11-17, 15:55 to 16:05. The map and `writercheck`; the three sets pass
(S, M, J1 to J5, B1 to B12, no shape fault after any operation).
2026-11-17, 16:05 to 16:15. The statement (`Mid`, `OpStep`, `WriterMeets`,
`Runs`); `writerMeets_of_opStep`, `runs_meetsTop_of_opStep`.
