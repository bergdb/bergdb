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

- **The puts are proved** (item 3). For every key as `Keys.toSegments`
  makes it, and a tree of any shape: a put that the model's writer accepts
  keeps the contract's invariants, the contents with the put applied, the
  frame, TREE, the top and the writer's books for a put (`putKv_put`).
  A transaction of puts meets the writer's contract (`writerMeets_put`).
  A run of such transactions is a history that meets `MeetsTop`
  (`runs_meetsTop_put`), so every get and scan of it is right at every
  time (030-08's theorems). All of a put is in it: the descent through
  inner nodes and segment leaves, the leaf's klong, the time split (also
  in place, also by dead klongs), the space split under a parent, under a
  segment leaf and at the space root (also in place), the recursion up the
  path, a new top node with its skip pointers, new segment leaves (also
  above a full leaf, which is split while the new leaf has no klong yet).
  On the standard three axioms. The premises that are left are in section
  6: the parameters (`ParamsOK`: Java's meet them), the writer's view at
  each transaction (`Shows`: it shows the nodes reached), and `SNamed` of
  the start tree. For a transaction that the model's `runOpsFrom` accepts
  the bounds G and H need no premise (`writerMeets_exec_put`).
- **Not vacuous:** `Contract/WriterExample.lean` and `WriterExample2.lean`
  run the model's writer from the primordial tree with Java's parameters
  at node size 8, two transactions of one put each: keys of one segment,
  and keys of two segments, the first making a new segment leaf, the
  second put into it. The runs meet every premise, so the theorems give
  `MeetsTop` for them, and `jget_right` then the reads.
- **The first delete is proved** (item 4): a delete of a one-segment key
  whose segment leaf has room for a bitmap and keeps a live klong, and
  after which no merge is due; also the delete of a key that is not there
  (`putKv_del1_leaf`, `putKv_del1_leaf_merges`). Since 19:12 a second
  prover, 030-16, has the other deletes; for them this item leaves
  `handleFullWith`'s time split for any caller (`handleFull_time_h`).
- **The map is right** (item 1). The writer's state within a transaction
  gives the contract's tree, its top and D (`treeOf`, `topOf`, `dirtyOf`,
  `Contract/Writer.lean`). On the 195 traces of the small, drain and
  reclaim sets (29,735 transactions, 318,900 operations) the map of the
  model's state after each transaction is Java's tree and top, node for
  node (`lean/contract/writer.sh`: WRITER OK).
- **The statement** (item 2), `Contract/Writer.lean`, section 3:
  `OpStep`, one operation keeps `Mid` (the contract's invariants, the
  contents, the frame, TREE, the top, BalancedOK and fourteen books of the
  writer); `WriterMeets`, one transaction meets the contract. Checked on
  the same traces after every one of the 318,900 operations, inside the
  transactions too, the writer reading through the model's own view
  (since 21:40; section 3): no failure. For any operation the step from operations
  to a transaction and a history is proved (`writerMeets_of_opStep`,
  `runs_meetsTop_of_opStep`). What the puts are proved to keep is `MidP`,
  `Mid` without the six books that only a delete reads.
- **The view** (the second review's first point; section 6 has the
  route). `Shows`, the writer's view at each transaction, is still a
  premise of a run. Towards having it from the model's own structure
  (`exec?`'s changes applied, then `SIS.view`), two of three parts are
  proved for the key nodes (`Contract/Proof/WriterView.lean`): the
  structure after the model's changes holds the tree of the writer's
  state (`holds_apply`, by the old package's `apply_keyNode`, imported),
  and the model's own view shows the key nodes that the tree reaches,
  if the space root is reachable (`reachable_of_holds`,
  `shows_key_of_holds`). Left: the top, two premises to take from `Mid`,
  and the join with the run; 1,500 to 3,000 lines by my estimate.
- **030-16's deletes on the restated statement**: its delete of a
  one-segment key, the merges' loop and root collapse (main 53e66e73)
  are carried to the balance rule for the nodes reached and to `Shows`
  for the nodes reached (section 3, 22:15).
- **The main answer** (item 5, section 5): the old route's hard cases do
  not come back. `l4`, R3, R4 and ValOld are all about the fill and the
  rule of two live klongs in an inner root. The old theorem needed them
  because the model's `exec` turns a writer's error into "no change", so
  it had to prove that the writer never gives an error, and a merge
  without a sibling is one. The contract speaks of accepted transactions
  only, and no reader needs the fill; so neither is in the statement, and
  an error is a refusal. For the puts this is now a fact, not a reading:
  no proof used the fill, the leftmost rule or the dead klongs' bound. For
  the deletes it is by reading the writer case by case (section 5.2).
  What does come back, smaller: the take-back's link invariant (which
  klongs name a node the transaction made), started clean at each
  transaction's start.
- **What it cost** (section 5.3): the puts took 22,500 lines of proof in
  four hours (15:50 to 19:55), 20 runs of provers, about 15 points of the
  week with the other agents' work in them. My estimate for the deletes is
  20,000 to 35,000 lines more. The old line has about 230,000 lines of
  proof for the same writer, with `l4` open.
- **What is given up:** the statement is "what the writer accepts is
  right". "The writer never refuses a transaction on a tree in shape" is a
  second statement, not made; the fill and `l4` live there. It is tested:
  the model gave no error on the 318,900 operations, and Java's `Bug`
  fails its tests.


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
  operations so far applied; J3 the frame; J4 TREE; J5 the top (`WTopInv`:
  the writer's super root is the one it started with, or one it made, of
  time i, with skip pointers that meet the top's clause);
  BalancedOK for the key nodes reached and their live klongs (`Balanced`;
  until 20:50 `BalancedAll`, for every node and klong); and the books B1 to
  B14 (which nodes are made, the times, what `madeFor` names, no klong
  names a node taken back, the levels within G and H, the ids, replaced
  nodes as they were, made key nodes reached, the bounds, a time klong
  first, the link of a made node).
- `OpStep`: an operation on a key as `Keys.toSegments` makes it that
  `putKv` accepts, and that leaves no key node outside the bounds G and H,
  keeps `Mid`.
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
- **Restated at 16:25** (my own statements of 16:10, before any proof of
  `OpStep`), each found by working out the first put by hand:
  - `OpStep` and `OpsRun` ask for a key as `Keys.toSegments` makes it
    (`keyWf`). Without it the statement is false: a put of a one-segment
    key whose segment has 7 bytes makes a value klong where the invariants
    want a key node (KindsOK). Not shown false in Lean; by reading
    `setValue`. The tree checker tests the keys' form (C-T7), and
    `writercheck` now does.
  - `Books.first` and B13: every key node starts with a time klong. The
    writer takes a node whose first time is i for one it made
    (`newInTrans`) and changes it in place; a node of s without a time
    klong would get the time i as its first by a put, and its next split
    would break the frame. The contract's W1 allows a node with no klong.
  - BalancedOK is `BalancedAll`, over every key node and key klong, not
    only the reached ones and the live ones: a rule about every node is
    kept by looking at the node changed alone, with no walk. Tested: S (all
    nodes of the heap) and B14 (the overlay).
  - B8 speaks of key nodes only. For values it is false in a transaction
    that puts one key twice (the first value is made, kept and no longer
    reached); Java gives the Dag one operation a key, so the traces do not
    show it.
- **Restated at 16:50 to 17:00**, from the proof of the new top node and
  the take-back's reading:
  - J5 is `WTopInv` (first named `TopInv`; 030-07 has that name), not only
    the top's clauses: the writer makes the next top node's skip pointers
    from its super root's, so the statement must say what its super root
    is. `Shows` says that the super root's skip pointers are at the bits
    of its ordinal, and `Books` that they name top nodes with their times;
    `WriterMeets` gives the second back; the first is the view's.
  - B5 says that the segment and the height are within G and H.
  - B14, the link of a made node, added (section 5.2, the take-back).


- **Restated at 20:50, `BalancedAll` to `Balanced`** (the coordinator's
  decision of 20:46 on 030-16's finding F1; the Log has both). My form of
  16:25, for every key node and every key klong, live or dead, was shown
  false in Lean by 030-16: a take-back leaves a dead klong that names a
  node two levels down (`Contract/WriterBalancedFalse.lean`:
  `balancedAllOld_false`, kept as the record; `balanced_last`: the same run
  meets the new rule). The rule is now Shape.lean's BalancedOK: for a key
  node reached from the space root, a level above 0, a segment leaf
  exactly at height 0, and each live klong of an inner node names a key
  node one level below. What it cost the put's proofs: the rule is carried
  from one map to the next by the nodes reached (`Balanced.of_reach`), not
  node by node; a node read must be shown reached (`getNode_spec`); and
  the recursion asks that no node is twice on the path (`CasPre.nodup`),
  which the old form's levels had given. Tested: the checker's shape
  faults (BalancedOK) after every operation.


- **Restated at 21:40, `Shows` for the nodes reached** (finding 1 of a
  second independent review, the Log's entry of 21:32). `Shows` asked the
  view to show every key node of the tree. The model's view (`SIS.view`)
  holds only the nodes reachable at the time, and the tree keeps the nodes
  of earlier times; so the old `Shows` could not hold for the model's own
  view after a split. `writercheck` had not seen it: it gave the writer the
  whole accumulated structure. With the model's view in the checker: the
  old `Shows` fails before 29,153 of the 29,735 traced transactions; the
  new one, for the key nodes reached from the space root, holds before
  all, and the writer's run is the same. What it cost the proofs: a node
  that the writer reads from its view must be reached in the tree before
  the transaction, so the operations' theorems carry `OldReach` (a node of
  s that is reached in the state's map was reached in s: the writer links
  no node of an earlier time again), a new field of `Mid` (the checker's
  B16, no failure).
- **The checker and the statement** (the review's finding 3): the
  checker's B8 is now the statement's (key nodes). B11 stays the model's
  own check (a node made outside G and H was taken back); the statement
  asks that none is made (`within`, `OpsRun`), and the checker counts the
  operations after which the writer's list of such nodes is not empty: 55
  of 318,900, all in one trace of the drain set (`d-long3b-5`: a delete
  makes a root one height too far and takes it back in the same
  operation; the list stays to the transaction's end). Such a transaction
  is accepted by the model and not covered by `OpsRun` (D3); for puts
  there is no such case (`opsRun_of_runOps`).
- **Restated at 22:15, in 030-16's files, at the merge of main 53e66e73**
  (030-16's delete with the merges on, root collapse and the merges' loop
  were written on the statement of before the two restatements above; the
  coordinator's message of 22:00). Its theorems now carry `OldReach` as
  the put's do: `collapseRoot_spec`, `AfterOk`, `AfterOkW`, `MergeOk`,
  `mergeUp_spec` take `OldReach i s w` after the invariant and give
  `OldReach i s w'`; `wmg_pick_spec`, `merge_spec_of_rest` and the open
  premise `WmgRestOk` (what is left of the merge) likewise; `wmg_sibling`
  also takes that the klong it follows is live (the balance rule speaks
  of live klongs). No conclusion is weaker than 030-16's. New:
  `mergeOk_of_rest`, the merges' loop's premise `MergeOk` from
  `WmgRestOk` (the two had been stated apart).


# 4. What is proved (items 3 and 4)

In `lean/contract/Contract/Proof/`, on the standard three axioms. The
package does not import the old proofs: the old lemmas speak of the old
invariants (`TreeOK` on a node map, the kinds' walk, the live counts), not
the contract's; 70 lines were copied (`WriterWP.lean`, the rules for the
writer's steps).

The files, in the order they build:

- `WriterRun.lean` (430 lines): from one operation to a transaction and a
  history (`mid_start`, `mid_run`, `writerMeets_of_opStep`,
  `runs_meetsTop_of_opStep`).
- `TreeCtx.lean` (990): two trees that differ below one node. The context
  lemma (`Good.ctx`, `ctx_L`, `ctx_route`, `ctx_reach`): if the trees
  agree outside q's subtree and q is sound in the second for every range
  it is sound for in the first, the root is; the keys are the same, or
  with a put or a delete applied if the key is routed to q; TREE is kept
  if q's new subtree holds only its old nodes and new ones.
- `NodeAlg.lean`, `NodeAlg2.lean` (920, 570): the node algebra: what
  `add`, `lastVersion`, `replaceOrAdd`, `halves` and `toPrev` do to a
  node's live klongs, well-formedness, size and frame; the model's
  searches as lookups in the live klongs; the levels' arithmetic.
- `Sound.lean`, `TreeRules.lean` (40, 2,040): `Sound M ex T r C` (the
  invariants, TREE and the keys C from the space root r, the node `ex`
  maybe over its size), and each rule of a put as a statement about two
  trees: `Sound.put`, `Sound.inPlace`, `Sound.timeSplit`,
  `Sound.timeSplitRoot`, `Sound.spaceSplit`, `Sound.spaceSplitRoot`.
- `WriterState.lean`, `WriterPrim.lean` (110, 1,290): the writer's state
  within a put (`PInv`, the put's books) and its primitives: each as an
  equation, what it does to the map, and that the books, the frame,
  BalancedOK and the path are kept over a change of one node.
- `WriterTop.lean` (460): `newSuperRoot`, the new top node; the lowest
  skip pointer names the old super root since the lowest bit set in
  ord + 1 is not set in ord.
- `WriterCascadeDefs.lean`, `WriterTimeSplit.lean`,
  `WriterSpaceSplit.lean` (100, 1,110, 2,250): `handleFullWith`, in the
  form "if node x had these klongs added, the state would be sound with x
  over its size" (`CasPre`), which each split hands to the parent.
- `WriterPut.lean` (690): `appendKlongs_spec` (the recursion), the
  descent, `putKv_put1`, `writerMeets_put1`, `runs_meetsTop_put1`.

- `NodeAlg3.lean`, `TreeRulesDel.lean`, `WriterDel.lean` (610, 160, 590):
  the first delete: the bitmap's node algebra (a new bitmap klong, or the
  bits in the transaction's own bitmap; W2 to W4 kept), `Sound.del`, and
  `deleteUpward` with `appendDeleteKlong` and the merges' descent that
  finds nothing to merge.
- `Contract/WriterExample.lean` (270): the example run.
- Keys of more segments: `WriterCascadeDefsG.lean` (the recursion's
  statement with a segment leaf as a parent), `TreeRulesSeg.lean`
  (`Sound.spaceSplitSeg`, 350), `NodeAlg4.lean` (a klong pointed in place,
  390), `WriterTimeSplitG.lean`, `WriterSpaceSplitG.lean` (590, 2,180),
  `WriterPutG.lean` (750: `putKv_put_routed`), `TreeRulesChain.lean`
  (`Sound.putSeg`, 300), `WriterPutSeg.lean` (1,100: `putKv_put_newseg`,
  `writerMeets_puts`).
- The last put: `WriterCascadeDefsO.lean` (the recursion's statement
  while a new segment leaf has no klong yet: soundness is read on the map
  with the nodes set that the writer fills right after the recursion),
  `WriterTimeSplitO.lean`, `WriterSpaceSplitO.lean` (1,170, 3,120),
  `WriterPutAll.lean` (1,500: `appendKlongs_spec_o`,
  `putKv_put_newseg_full`, `putKv_put`, `writerMeets_put`,
  `runs_meetsTop_put`).
- For the delete of a full leaf (030-16's): `WriterCascadeDefsH.lean`,
  `WriterTimeSplitH.lean` (780: `handleFullWith`'s time split for any
  caller), `NodeAlg5.lean` (110).

How it went: I wrote the definitions and each file's statements; provers
(Opus, xhigh) proved one file each, in waves of two to five at once, and
reported where a statement was wrong or lacked a hypothesis. The first
put, of a one-segment key, took ten runs in three waves: 10,900 lines of
proof in two and a half hours (15:50 to 18:25). The cost of all puts is in
section 5.3.

What the proof showed that the statement did not have (all now in
`Contract/Writer.lean`, each tested by `writercheck`):

- the keys' form (`keyWf`), a time klong first in every key node, the
  levels' bounds in B5, BalancedOK for every node and klong;
- the top's books: the super root's skip pointers are at the bits of its
  ordinal (`Shows`), and name top nodes with their times (`Books`);
- `ParamsOK`: with a node size below 6, or h + 2 above M, a split makes a
  node over its size or an empty half. The model and Java do not check
  it; Java's sizes meet it.


# 5. How hard is the rest (item 5)

## 5.1 The route for one operation

Worked out at 16:20; built since for the put of a one-segment key
(section 4). All of it is about two trees that differ below one node.

- **The context lemma.** If two trees agree on every node reached that is
  not below a node q, and q in the second tree is sound for every range q
  is sound for in the first, and holds the same keys, then the second tree
  meets the invariants, holds the same contents, and meets TREE if q's new
  subtree is its old one and new nodes. Proved once, by the walk's
  recursion; TREE is what makes "below q" a set (a node has one parent).
  Every rule of the writer then needs a local argument only, about q and
  its children.
- **A put** changes one segment leaf (a klong added), or replaces it: by
  its last version (a time split) or by two halves and maybe a new root (a
  space split), and the parent gets one or two klongs in turn
  (`appendKlongs`, a recursion up the key access path). The induction: "if
  node x had these klongs added, the tree would meet the invariants and
  hold the contents C" is kept by each step up, with x the parent; at a
  node with room it is the real tree. A node with the klongs added and no
  room is a tree for the invariants at node size M + 3.
- **The node algebra.** What `add`, `lastVersion`, `replaceOrAdd` and
  `halves` do to a node's live klongs, the well-formedness (W1 to W4), the
  frame's "klongs only added after a time klong of i"; and that the
  model's searches are the contract's.
- **The books** of each step, B1 to B13: local, one small argument each
  per primitive (`getNode`, `putNode`, `newKey`, `newValue`,
  `newSuperRoot`, `takenBack`).

## 5.2 The old hard cases, one by one

By reading `Exec.lean` against the contract's invariants (KindsOK,
NonEmptyOK, RangeOK, the node's rules), TREE and the frame.

- **`l4`** (a delete keeps the live counts: one live klong in every node,
  two in an inner root, m in a node an inner node names; hard because the
  delete leaves a hole that the merges move up). **Vanishes.** Of the
  three counts the contract has only the first, NonEmptyOK, and it is
  local: a leaf's delete that leaves no live klong goes to the upward
  unlink, whose stop node is by its definition the first that keeps one; a
  merge joins two nodes that each have one (it gives an error otherwise),
  and its parent had two; a root with one live klong is replaced by a
  child that has one. No hole to follow.
- **R3** (root collapse returns early at a root the transaction made with
  no made-for entry; then an inner root might keep one live klong).
  **Vanishes:** that is RootsOK, not in the contract.
- **R4** (a hole below a parent's split or cascade). **Vanishes** with the
  fill.
- **ValOld** (at a delete's start the key's live klong names a node from
  before the transaction). It served R3. **Vanishes.**
- **The fill as a premise of the merge.** 030-05 expected "a proof that
  the writer meets the contract will want the fill and the root rule as
  premises of its own, since a merge relies on a sibling". It does not:
  `merge` gives an error when there is no sibling, when a node to merge
  has no live klong, when an inner node's first live klong is not the
  empty key's. An error is a refusal. What a merge does need is that the
  two siblings are on one height, for the levels of the merged node's
  children: BalancedOK, which is local and is in `Mid`.
- **`htb`, the take-back's premises** (proved in the old line, 025-05).
  **Comes back, smaller.** A node taken back is no node, so no klong kept,
  live or dead, may name it (B4; PointersOK). `takeBack` and `merge`
  repoint the klongs of the transaction in the parent on the key access
  path. That this reaches every klong that names the node needs: a klong
  that names a node the transaction made is a klong of the transaction,
  in the node's one parent. It holds because a node's klongs are copied
  only as a last version (live klongs only), and a node from before the
  transaction that is replaced loses its klongs of the transaction. It is
  an invariant over the operations of one transaction (a node made by a
  split in one operation is emptied in a later one), so it belongs in
  `Mid`; it is not there yet (B3, B4, B9 and B12 are its consequences that
  the checker tests).
- **New against the old line:** the frame (local: each change to a node
  from before the transaction is one of five forms, each an addition
  after a time klong of i, or a cut back to the node of s) and TREE (by
  the context lemma). The intra-operation states: between a split and its
  parent's klong, and a new segment leaf that is empty until its first
  klong; both are handled by the "if x had these klongs" form above.

What stays hard is what was hard and proved in the old line: the number
of cases. A put has ten rules (room, time split, three space splits, each
also in place for a node the transaction made, a new segment); a delete
about twenty (the bitmap's four forms, the unlink's climb, the take-back,
LE-b, the merge's left and right, one and two nodes, the parent's five
forms, root collapse's four).

## 5.3 The cost, and the estimate for the deletes

Measured, the puts (all of them, section 4): 22,500 lines of proof and
1,300 of statements, definitions and the checker, in four hours of the
clock, by 20 runs of eight provers (Opus, xhigh), one file each, about 3.5
million tokens of provers (the first delete, the example and the delete's
time split: 2,600 lines and five runs more); the week went from 27 to 44
points in that time, with the other agents' work in it. About 6,000 lines are shared by
every operation (the context lemma, the node algebra, the primitives, the
top node, the run).

My estimates of the puts were low twice: 6,000 to 9,000 lines from the
route alone (16:20), then 13,400 to 15,400 after the first put (18:30).
Why: the same recursion was proved three times, for a path of inner nodes,
for a path through segment leaves, and with an unfilled segment leaf (the
later forms copy the earlier proofs with the statement's form changed; the
first could now be made a case of the third, about 5,000 lines less).
Each form was found by the proof of the one before failing at a named
place, not by planning.

For the deletes, with the same method (statements first, one prover a
file) and the same factor of two on my first reading:

- the bitmap with a full leaf (`handleFullWith` for any caller: the time
  split is there, the space split is not): 3,000 to 5,000;
- the upward unlink with the take-back, and LE-b: 6,000 to 10,000;
- the merge's forms with the parent's five, the loop, root collapse:
  8,000 to 14,000;
- the delete's books (B3, B4, B7, B8, B12, B14) through every rule of the
  put too, and `OpStep` whole: 3,000 to 6,000.

Together 20,000 to 35,000 lines, four to eight waves like today's, one to
two nights of this kind. Against about 230,000 lines of proof in the old
line for the same writer, with `l4` open.

The reason it is not more: every rule is local once the context lemma is
there, and the fill is gone. The uncertain part is the merges' loop and
root collapse, which descend again from the root after each change
(`descendToHeight`, `descendToSegmentRoot`): each round needs the tree
closed, so `Mid`-like facts must hold between rounds, not only between
operations. I did not check that on traces (the checker looks between
operations).

What the method needs, as today showed: a statement's holes are found by
the proof, at a named place, in minutes (a missing "q is a key node"; no
node twice on the path; a step that must not empty a book). Six times a
prover reported such a hole and the fix; none of my statements was found
false in what it concluded.


# 6. What is not closed

For a claim "the model's writer meets the contract for puts", these are
the premises that are not proved or not given back, each tested:

- **`SNamed`**: every klong of the tree before the transaction names a
  node of it. Used where a segment leaf's klong is pointed to a new
  segment root in place. A put gives it back (`putKv_put_named`), so a
  run of puts needs it of the start tree only (`RunsPuts`); it is not in
  `Mid`, so `OpStep` as stated cannot be proved for a put without it: the
  shared statement should get it (a book "every klong of a node kept
  names a node kept", which also gives B4), when the delete's proofs say
  what they keep of it. `writercheck` tests it at every traced start.
- **The view** (`Shows`): at each transaction the writer's view shows the
  key nodes reached and the top (section 3, D4), with the super root's
  skip pointers at the bits of its ordinal. Given at each step of `Runs`;
  that the model's own change (`changesOf`, applied to the abstract
  structure, then `SIS.view`) gives such a view again is not proved: the
  model's round trip between klongs and entries, and that the model's
  reachable nodes are the tree's reached ones. This is what the second
  review asks for as "the refinement through `exec?`'s real steps"; of
  those steps the run and the bounds check are proved for puts
  (`opsRun_of_runOps`), the view and `changesOf` are not. Tested: S, with
  the model's view computed from Java's structure before every traced
  transaction; the tree checker's C-T2.
  A route for it (a plan, nothing of it written in Lean): a relation
  between the model's abstract structure P and the tree s with the top tp
  before time i, stronger than `Shows` because it speaks of every node of
  P, reached or not: the key node x of s with klongs ks is in P with its
  level and the entries of ks (`SIS.Tree.entriesOf`), the top nodes and
  the root's entries are tp's, the values are s's. Then three parts.
  (1) The relation gives `Shows` for `rootless (SIS.view P (i-1))`: the
  model's reachable nodes at i-1 (`SIS.reachFrom`, by the live entries up
  to the time, a pointer followed only to a lower level) are the tree's
  reached ones (`reach`, by the live klongs; the level test is the
  balance rule), and klongs to entries and back is the identity for
  `klongsWf` klongs. (2) `P.apply i (changesOf i w)` has the relation
  with `treeOf i s w` and `topOf i tp w`: for a node of the overlay not
  taken, the entries of time i added are the new klongs' (the frame: the
  klongs of earlier times are kept); a node made and not taken is new; a
  node made and taken is in neither; a node of s taken keeps its entries.
  (3) The same for the top node made. With (1) to (3), `Runs` no longer
  takes the view at each step, only the relation at the start. The old
  package has two of the pieces, proved for every accepted run with
  premises on P only, none of them the joint induction's (read 22:30, not
  yet used here): the round trip (`SIS.Tree.klongsRoundTrip`,
  KlongRoundTrip.lean), and part (2) for the key nodes
  (`SIS.Tree.apply_keyNode`, ApplyBridge.lean, the old TP7: a key node of
  the structure after the transaction is an overlay node not taken, with
  the overlay's klongs, or a node of P as it was; its premises
  `KeyHistOK`, `ViewLinksOK`, `StructTimesLE` and the ids are the relation
  in the old package's words, and `keyHistOK_step` keeps the first).
  They can be imported: lean/contract depends on the old package since
  030-07. Left to write: the relation in the contract's words, part (1)
  (the two notions of reached), the top's part (3), and the join with
  `Mid`. Estimate: 2,000 to 4,000 lines. No old hard case is in it:
  nothing here reads the fill or asks that the writer accepts.
  Done of it (22:45, `Contract/Proof/WriterView.lean`, 180 lines): the
  relation for the key nodes, `Holds p P s` (each key node of s is a key
  node of P with its level and its klongs), and part (2) for it,
  `holds_apply`: after a run that the model accepts at time i from P@(i-1)
  with the state w and the writer's books (`MidBooks`), the structure
  after the model's changes holds `treeOf i s w`. Its premises on P are
  the old `apply_keyNode`'s (`KeyHistOK`, `ViewLinksOK`, `StructTimesLE`,
  the ids below the first id, the root above the key levels), which the
  old package keeps along a run. **Decision: imported, not copied**
  (`SIS.Tree.ApplyBridge`, `SIS.Tree.GetCommit`): `apply_keyNode` rests
  on about 100 modules of the old package's plain facts about a run (no
  klong of an earlier time changed, each node held once, klongs well
  formed, the ids, the ledger); a copy would be thousands of lines for
  nothing new. The cost: the first build takes about 6 minutes more, and
  `lake build` now replays 29 linter warnings of those old files (unused
  simp arguments; the gate prints "lake build has warnings" and passes;
  the files are outside what this item may change). Not tested apart: it
  is proved, and the traced M (the map is Java's tree) with the tree
  checker's C-T2 (the model's changes are Java's) test the same.
  Part (1) for the key nodes (22:57, the same file, 410 lines in all):
  `reachable_of_holds`, the key nodes that the tree reaches are reachable
  in the model's structure at the time, if the space root is; and
  `shows_key_of_holds`, the model's own view (`SIS.view` of P at i-1,
  without the root) then shows them as `Shows` asks. Premises, named: the
  levels fall along the live klongs of the nodes reached (`LevFalls`; the
  model follows a pointer only to a lower level), and the nodes reached
  have well-formed klongs with W5 (030-07's `AllWf`, for the nodes
  reached); both are tested for every node and klong by `bridgecheck`
  (its clauses A4 and W5: BRIDGE OK on small and drain).
  Left, in this order: part (3), the top (the root's last top node and
  its root pointer: the space root is reachable, and `Shows.top`; kept by
  the changes of a new top node); `LevFalls` and the well-formed klongs
  from `Mid` (for inner nodes the balance rule gives the levels; for a
  segment leaf the segments' levels are needed); the old package's
  premises on P along the run (`keyHistOK_step` keeps the first; the
  others have their run theorems there); the join: `Runs` with the
  structure's relation at the start in place of the view at each step.
  Estimate for what is left: 1,500 to 3,000 lines.
- **The bounds G and H** (D3): each accepted operation leaves no key node
  outside them (`OpsRun`). Tested (B11). Two of the proofs' gaps were of
  this kind. For a transaction of puts that the model's `runOpsFrom`
  accepts it is proved (`opsRun_of_runOps`): a put takes nothing back, so
  the model's own check at the transaction's end gives it for every
  operation.
- **The parameters** (`ParamsOK`): M ≥ 6, 2 ≤ h, h + 2 ≤ M. Java's sizes
  meet them; nothing checks it in the model or in Java.
- **The delete's books** (B3, B4, B7, B8, B12, B14): the puts are proved
  to keep `MidP`, which is `Mid` without them. A transaction of puts and
  deletes needs the puts to keep what the delete reads of them. Which
  that is, the delete's proofs say (030-16): its link book for the nodes
  reached (`LinkLive`) is proved kept by the put's splits in 030-16's
  parked files (`/Users/f/fl/bench/2026-11-17/night/s4j/linklive/`), in
  the forms of before this evening's restatements; not joined here.
- **The books are tested as computed over the heap's nodes** (D5), the
  statements speak of every node.
- **The statement is "what the writer accepts is right".** That the
  writer accepts every transaction on a tree in shape is not stated.


# State

2026-11-18. Taken off `main` on Frans's word (2026-11-18, 08:42; 006-31,
section 1; done in 030-18): the writer proof's files left `lean/contract/`.
The code is at the tag `writer-proof-2026-11-18` (main 52459c9d); to go on,
start from the tag. The notes below are as the work left them.

2026-11-17, 23:00. Items 1 and 2 done; item 3 (the puts) done for every
key; item 4: the first delete done, the rest is 030-16's since 19:12;
item 5 written (section 5). The statement was restated three times this
evening on findings (section 3: the balance rule, `Shows`, the checker),
and 030-16's delete, merges and root collapse (main 53e66e73) are carried
to the restated statement.

- Branch `030-10-writer` in the clone
  `/Users/f/fl/bench/2026-11-17/night/s4d/clone`, on main 53e66e73.
  Last gated commit: 6ad9b53a.
- Build: `cd lean/contract && lake build`. Gate: `lean/contract/gate.sh
  53e66e73` (main's head as merged); after a change of a pinned file
  `lean/contract/pin.sh`, the pin file in the same commit.
- Traces: `java/build.sh`, `cd lean && lake build treecheck`,
  `java/stress/treeconf.sh small`, `drain` and `reclaim`; then
  `lean/contract/writer.sh` (and `check.sh`; see the Log, 19:45, on its
  `bridge-faults.sh`).
- To read first: `Contract/Writer.lean` (the map, the statement),
  `Contract/Proof/WriterState.lean`, `WriterCascadeDefs.lean`,
  `WriterCascadeDefsG.lean`, `WriterCascadeDefsO.lean` (the put's
  invariant and the recursion's three forms), `WriterPutAll.lean` and
  `WriterPutNamed.lean` (the theorems), `WriterExec.lean`,
  `WriterView.lean` (the structure after a transaction), `WriterCheck.lean`.
- Open on the put side (section 6), in the order I would take them:
  the view after a transaction (the model's `changesOf` and `SIS.view`
  give `Shows` again; section 6 has the route in three parts, parts (1)
  and (2) are done for the key nodes: next part (3), the top, then the
  join); `SNamed` as a book of `Mid`; the delete's books
  through the put (with 030-16: its `LinkLive`, parked in
  `/Users/f/fl/bench/2026-11-17/night/s4j/linklive/`, was proved for the
  forms of before the restatements); the bounds by heights, so that
  `OpsRun` is what `runOpsFrom` accepts for deletes too.
- The three forms of the recursion (`CasPre`, `CasPreG`, `CasPreO`) and
  the two of `handleFullWith`'s time split for a delete (`CasPreH` here,
  `CasPreD` of 030-16) are copies with the statement's form changed; one
  form would do (about 5,000 lines less).
- The provers' briefs, as examples of the method:
  `/Users/f/fl/bench/2026-11-17/night/s4d/scratch/brief-*.md`.


# Log

2026-11-17, 15:50. Started from the brief of coord-1117; main (030-08's
top, 030-09) merged into the branch.
2026-11-17, 15:55 to 16:05. The map and `writercheck`; the three sets pass
(S, M, J1 to J5, B1 to B12, no shape fault after any operation).
2026-11-17, 16:05 to 16:15. The statement (`Mid`, `OpStep`, `WriterMeets`,
`Runs`); `writerMeets_of_opStep`, `runs_meetsTop_of_opStep`.
2026-11-17, 16:15 to 16:25. Main 863b69cb merged (030-07 landed; the
coordinator's word, 16:15); the statement restated (D5's list); the item's
sections 4 and 5. The gate passes against 863b69cb; against 79678f4e the
one file outside is main's own line in 006-30.
GATED 7332f7d2: the map and its check on the traces, the statement, the step from operations to a transaction and a history (writerMeets_of_opStep, runs_meetsTop_of_opStep).
2026-11-17, 16:25 to 16:45. Two provers (Opus, xhigh), one file each, from
statements I wrote: `TreeCtx.lean` (two trees that differ below one node:
the context lemma, 989 lines) and `NodeAlg.lean` (the node algebra of
`add`, `lastVersion`, `replaceOrAdd` and the model's searches, 918 lines).
All proved; the provers fixed four of my statements (three needed "q is a
key node", `L_agree` needed no soundness) and dropped three unused
hypotheses. B14, the link of a made node, added to `Mid` and tested (the
checker's B15). `writer.sh` on the three sets: WRITER OK.
GATED 0212cae0: the context lemma, the node algebra, the primitives, the top node; main d656263a merged (gate base d656263a).
2026-11-17, 16:45 to 18:25. Three waves of provers, one file each, from
statements I wrote: the rules as statements about two trees
(`TreeRules.lean`), the primitives (`WriterPrim.lean`), the top node
(`WriterTop.lean`), `NodeAlg2.lean`; then the time split, the space split
and the put (`WriterTimeSplit.lean`, `WriterSpaceSplit.lean`,
`WriterPut.lean`). J5 restated as `WTopInv` with the skip pointers' books.
`check.sh` and `writer.sh` on the merged tree: CONTRACT OK, WRITER OK.
GATED 2aad54c9: a put of a one-segment key proved (putKv_put1, writerMeets_put1, runs_meetsTop_put1).
2026-11-17, 18:25 to 18:50. A fourth wave: the first delete (`NodeAlg3.lean`,
`TreeRulesDel.lean`, `WriterDel.lean`) and the example run
(`WriterExample.lean`); main d3d98a4e merged (the coordinator, 18:40: the
put is landed; Frans, 17:39: correctness first, then keys of more
segments, then the delete). The gate passes against main's head 556cc927
(against d3d98a4e the one file outside is main's own line in 006-30);
`check.sh` and `writer.sh`: CONTRACT OK, WRITER OK.
GATED 24ed4a2f: the first delete (putKv_del1_leaf, putKv_del1_leaf_merges), Sound.del, the example run (WriterExample.meets, meets2).
2026-11-17, 18:55. A fifth wave started: a put of a key of more segments
whose segment trees exist (`WriterCascadeDefsG.lean`, `TreeRulesSeg.lean`,
`NodeAlg4.lean`, `WriterTimeSplitG.lean`, `WriterSpaceSplitG.lean`,
`WriterPutG.lean`). It needs `SNamed s` (every klong of the tree before
names a node of it), a premise that the writer's theorem does not yet give
back for the next transaction; `writercheck` tests it at every start.
2026-11-17, 19:00 to 19:15. The fifth wave's findings, each a hole in my
statement that a prover met in the proof: without `PathInner` nothing says
that a node is on the path once (`CasPreG.nodup`, from the falling levels
of the descent); a new segment root outside the bounds is made before the
parent's step, so that step must be known not to empty `W.outside`
(`hupo`, `handleFullWith_outside`). Main 6fd5fdeb merged (030-15's pinned
statements; `pin.sh` run). The coordinator, 19:12: a second prover,
030-16, takes the delete in `Contract/Proof/WriterDel*.lean`; I keep the
puts. For 030-16, on this branch: `WriterDel.lean` (the first delete),
`NodeAlg3.lean` and `NodeAlg5.lean` (the bitmap, `lastVersionGivenDel`),
`TreeRulesDel.lean` (`Sound.del`), and `WriterCascadeDefsH.lean` with
`WriterTimeSplitH.lean`: `handleFullWith`'s time split for any caller
(`CasPreH`: a delete's `handleFull` with its own last version), proved;
the space split in that form is not made.
2026-11-17, 19:15. The last put, in work: a new segment leaf above which
the segment leaf is full (`WriterCascadeDefsO.lean`: soundness read on the
map with the new leaves set as they will be right after the recursion).
2026-11-17, 19:15 to 19:45. The fifth wave done: a put of a key of more
segments whose segment trees exist, and one that makes new segment leaves
where the leaf above has room. Main 84e7b8e3 merged (the coordinator,
19:35). The commits since 84e7b8e3 are one commit, c9015c05: one of mine
had changed a file that was pinned later without the pin file, which the
gate's step 5 refuses for every commit since the base; nothing landed was
rewritten. `gate.sh 84e7b8e3`: GATE OK (141 theorems). `writer.sh`: WRITER
OK. `contractcheck` and `bridgecheck` on the small and drain sets, run
directly: CONTRACT OK, BRIDGE OK.
For the coordinator: `check.sh` stops in this clone at main's own
`bridge-faults.sh`: its case `small` (`test/small.trace`, 030-15) is
expected to pass and fails KIND (030-14's K-LEVEL), on main 84e7b8e3 as
it is, before any file of mine. `check.sh` runs `bridge-faults.sh` only
where the reclaim set is there, so a clone without it does not see this.
GATED c9015c05: keys of more segments: putKv_put_routed, putKv_put_newseg, writerMeets_puts; the recursion with an unfilled segment leaf (handleFull_time_o, handleFull_space_o); handleFull_time_h for the delete.
2026-11-17, 19:45 to 19:55. The last put: `handleFull_time_o`,
`handleFull_space_o`, and `WriterPutAll.lean`: `putKv_put` for every key,
`writerMeets_put`, `runs_meetsTop_put`. `gate.sh 84e7b8e3`: GATE OK (145
theorems). The checkers are as at c9015c05.
GATED 3c0208d7: the puts proved whole: putKv_put (any key), writerMeets_put, runs_meetsTop_put.
2026-11-17, 20:00 to 20:25. `WriterExample2.lean` (keys of two segments);
`WriterExec.lean`: a transaction of puts that the model's `runOpsFrom`
accepts is an `OpsRun` (`opsRun_of_runOps`) and meets the contract
(`writerMeets_exec_put`). Main e7c873ee merged (the coordinator, 20:20).
2026-11-17, 20:25. **What 030-10 takes next, on the put side** (for the
coordinator and 030-16): the restatement of `BalancedAll`. 030-16 showed
my statement false in Lean (030-16, F1, `writerMeets_false`): a take-back
leaves a dead klong that names a node two levels down, so "every key
klong of an inner node, live or dead, names a node one level below" does
not hold after a delete. I restate it as 030-16 proposes (its D3): a live
klong of an inner node names a key node one level below; every key klong
of it names a key node of a lower level. I change `Contract/Writer.lean`
(`BalancedAll`; `Mid`, `Before`, `WriterMeets` through it), the checker,
and every proof file of main e7c873ee that builds or reads it: the put's
files, and 030-16's landed delete files (`WriterDel*.lean`) as far as the
new form asks; 030-16's `WriterBalancedFalse.lean` keeps its theorem
about the old form under a name of its own. 030-16 should not restate
`BalancedAll` itself, and gets the new form by pulling main. Also on the
put side, after that: `SNamed` given back (in work).
2026-11-17, 20:35. `WriterPutNamed.lean`: a put gives `SNamed` back
(`putKv_put_named`, `writerMeets_put_named`); `RunsPuts` asks it of the
start tree only (`runs_meetsTop_puts`). `gate.sh dc642af1` (main's head as
merged): GATE OK (159 theorems).
GATED 00c5075d: SNamed given back after a put; a transaction of puts that runOpsFrom accepts meets the contract (writerMeets_exec_put); the example with keys of two segments.
2026-11-17, 20:35 to 20:50. `BalancedAll` restated as 030-16 proposed (a
live klong one level below, every klong lower), tested on the traces
(WRITER OK), and the put's files half adapted, when two provers found
that this form asks more of the put than the old one read: a node cut
back and a split node in its parent's "if" state must keep their live
klongs one level below, which needs the rule of the tree before the
transaction and of the state itself.
**The coordinator's decision, 20:46** (030-16 proposed, the coordinator
decides): `BalancedAll` is restated in Shape.lean's BalancedOK form: about
the key nodes REACHED from the space root and their LIVE klongs only, not
about every node of the map and not about dead klongs. The reasons, in the
coordinator's words: it is the rule Java's traces are tested by; the
every-node form is false at reached states after a take-back (030-16's
`writerMeets_false`) and needs a link book over all nodes that fails at a
split's intermediate states; with the reached-only form 030-16's
reached-only book `LinkLive` suffices. I switch to it (`Balanced`,
Contract/Writer.lean): no proof of the put needs the stronger form; the
two gaps above go away with it, since a node cut back and a split node in
its parent's "if" state are not reached.
2026-11-17, 20:50 to 21:30. The balance rule restated in its final form
through the statement, the put's files and 030-16's landed delete files
(`Balanced.of_reach`; nine runs of provers); `gate.sh dc642af1`: GATE OK
(159 theorems); `writer.sh`: WRITER OK; `contractcheck`, `bridgecheck` on
small and drain: CONTRACT OK, BRIDGE OK.
GATED ea73b414: the balance rule restated (Balanced: the nodes reached, their live klongs), every proof carried over; balancedAllOld_false kept as the record.
2026-11-17, 21:32. **Findings of a second independent review** (another
model, of main 3f1e2fea; the coordinator's message; the full text is
`/Users/f/fl/bench/2026-11-17/night/codex2/review.md`), my work list in
this order:
1. `Shows` asks the view to show every key node of the tree, but the
   model's view (`SIS.view`) holds only the nodes reachable at the time,
   and `treeOf` keeps the nodes of earlier times: after a split the
   model's own next view lacks the node replaced, so `Shows` cannot hold
   for it (the review's probe: seven puts from the primordial tree).
   `writercheck` did not see it: it gave the writer the whole accumulated
   structure, not `SIS.view`. To do: `Shows` for the nodes reached; the
   puts then need that a node of s that is reached now was reached in s;
   `writercheck` with the model's view.
2. `MidP` omits B3, B4, B7, B8, B12, B14 (section 6); `SNamed` at each
   step of `RunsPut` (given back since 00c5075d: `RunsPuts`); `OpsRun`'s
   bounds are stronger than `runOpsFrom`'s (for puts proved equal since
   c8390ab0: `opsRun_of_runOps`).
3. The checker and the statement differ: the checker's B8 counts values
   (the statement: key nodes); its B11 lets a node outside the bounds
   pass if it was taken back (the statement: none outside).
4. `BalancedAll` in `WriterMeets`: restated (ea73b414).
2026-11-17, 21:35 to 22:05. `Shows` restated for the nodes reached, with
`OldReach` through every operation's theorem of the puts and of 030-16's
landed delete files (three provers); `writercheck` with the model's view
(caa4bdd4). `gate.sh dc642af1`: GATE OK; `writer.sh`: WRITER OK on the 195
traces (the old `Shows` fails before 29,153 of the 29,735 transactions,
the new one before none; 55 operations with a node outside the bounds,
taken back, on the list); `contractcheck`, `bridgecheck` on small and
drain: CONTRACT OK, BRIDGE OK. Not logged as gated on its own: it is in
the merge below, which is the one to land.
2026-11-17, 22:00. The coordinator: ea73b414 could not be landed, its
merge into main 53e66e73 conflicts with 030-16's later work in
`WriterDelSpace.lean` and `WriterDelTime.lean`; pull main, resolve, gate.
2026-11-17, 22:05 to 22:30. Main 53e66e73 merged (1cf23286). 030-16's
files of that work (`WriterDelDefs`, `WriterDelTime`, `WriterDelSpace`,
`WriterCollapse`, `WriterMergeParent`, `WriterMerge`, `WriterMergeUp`)
carried to the restated statement: its statements and proofs kept, the
balance rule by the nodes reached, `OldReach` taken and given (section 3,
"Restated at 22:15"; two provers). Then a3ec5ff8: `WmgRestOk` carries
`OldReach`, and `mergeOk_of_rest`. `gate.sh 53e66e73`: GATE OK (192
theorems, 128 files pinned). On the merge, before a3ec5ff8 (which
changes two proof files and no checker): `writer.sh`: WRITER OK, the
counts as above; `contractcheck`, `bridgecheck` on small and drain:
CONTRACT OK, BRIDGE OK.
GATED a3ec5ff8: main 53e66e73 merged; the balance rule and Shows restated (the nodes reached; OldReach) through the puts and 030-16's delete, merges and root collapse; writercheck with the model's view; mergeOk_of_rest.
2026-11-17, 22:30 to 22:50. The second review's point 1, the view after a
transaction (week 57 %, under the coordinator's 58 %): the route written
(section 6); the old package's `apply_keyNode` and round trip found;
`WriterView.lean`: `Holds`, `holds_apply` (one prover, 4 minutes; no
hypothesis added). `gate.sh 53e66e73`: GATE OK (193 theorems, 135 files
pinned: the old package's files that the statement reads are pinned now);
the gate's step 1 prints "lake build has warnings" for the old package's
files built with it (section 6, the decision to import). No checker
changed: the traces' results of 22:25 stand.
GATED 10489bff: the model's structure after a transaction holds the tree of the writer's state (Holds, holds_apply), by the old package's apply_keyNode, imported.
2026-11-17, 22:47 to 22:57. Part (1) of the view's route: `LevFalls`,
`reachable_of_holds`, `shows_key_of_holds` (the same prover, 8 minutes;
one hypothesis added: the nodes reached have well-formed klongs with W5,
needed for 030-07's `mem_blive_entriesOf`). `gate.sh 53e66e73`: GATE OK
(195 theorems). No checker changed.
GATED 6ad9b53a: the model's own view shows the key nodes that the tree reaches (reachable_of_holds, shows_key_of_holds), given the space root reachable, falling levels and well-formed klongs.
2026-11-17, 23:00. The week is at 58 %: by the coordinator's word of 22:00
no new part is started. The night's STOP file is not there yet.
2026-11-18. Taken off `main` (030-18); the code is at the tag
`writer-proof-2026-11-18`.
