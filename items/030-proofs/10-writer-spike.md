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
  each transaction (`Shows`), the bounds G and H, and, in work when this
  was written, `SNamed`.
- **Not vacuous:** `Contract/WriterExample.lean` runs the model's writer
  from the primordial tree with Java's parameters at node size 8, two
  transactions of one put each; the run meets every premise, so
  `runs_meetsTop_put1` gives `MeetsTop` for it, and `jget_right` then the
  reads.
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
  transactions too: no failure. For any operation the step from operations
  to a transaction and a history is proved (`writerMeets_of_opStep`,
  `runs_meetsTop_of_opStep`). What the puts are proved to keep is `MidP`,
  `Mid` without the six books that only a delete reads.
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
  BalancedOK for every node and klong (`BalancedAll`); and the books B1 to
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

How it went: I wrote the definitions and each file's statements; ten
runs of provers (Opus, xhigh) proved one file each, in three waves; they
corrected six of my statements (a missing "q is a key node", three unused
hypotheses, an unneeded case split) and found none false beyond that.
Measured: 10,900 lines of proof in two and a half hours (15:50 to 18:25),
2.7 million tokens of provers, about 7 points of the week with the other
agents' work in them.

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

- **`SNamed`** (keys of more segments only): every klong of the tree
  before the transaction names a node of it. Used where a segment leaf's
  klong is pointed to a new segment root in place. The put's theorems do
  not give it for the tree after the transaction, so a history of such
  transactions needs it at each one. To close it: a book of `Mid` (every
  klong of a node kept names a node kept), through every rule, about as
  BalancedOK is; the take-back needs the same book (B4). `writercheck`
  tests it at every traced start.
- **The view** (`Shows`): at each transaction the writer's view shows the
  tree and the top (section 3, D4), with the super root's skip pointers
  at the bits of its ordinal. Given at each step of `Runs`; that the
  model's own change gives such a view again is the model's round trip
  between klongs and entries. Tested (S; the tree checker's C-T2).
- **The bounds G and H** (D3): each accepted operation leaves no key node
  outside them (`OpsRun`). Tested (B11). Two of the proofs' gaps were of
  this kind.
- **The parameters** (`ParamsOK`): M ≥ 6, 2 ≤ h, h + 2 ≤ M. Java's sizes
  meet them; nothing checks it in the model or in Java.
- **The delete's books** (B3, B4, B7, B8, B12, B14): the puts are proved
  to keep `MidP`, which is `Mid` without them. A transaction of puts and
  deletes needs the puts to keep them too.
- **The books are tested as computed over the heap's nodes** (D5), the
  statements speak of every node.
- **The statement is "what the writer accepts is right".** That the
  writer accepts every transaction on a tree in shape is not stated.


# State

2026-11-17, 19:55. Items 1 and 2 done; item 3 (the puts) done for every
key; item 4: the first delete done, the rest is 030-16's since 19:12;
item 5 written (section 5). In work: `SNamed` given back after a put
(`WriterPutNamed.lean`), and an example run with keys of more segments
(`WriterExample2.lean`).

- Branch `030-10-writer` in the clone
  `/Users/f/fl/bench/2026-11-17/night/s4d/clone`, on main 84e7b8e3.
  Last gated commit: 3c0208d7.
- Build: `cd lean/contract && lake build`. Gate: `lean/contract/gate.sh
  84e7b8e3`; after a change of a pinned file `lean/contract/pin.sh`, the
  pin file in the same commit.
- Traces: `java/build.sh`, `cd lean && lake build treecheck`,
  `java/stress/treeconf.sh small`, `drain` and `reclaim`; then
  `lean/contract/writer.sh` (and `check.sh`; see the Log, 19:45, on its
  `bridge-faults.sh`).
- To read first: `Contract/Writer.lean` (the map, the statement),
  `Contract/Proof/WriterState.lean`, `WriterCascadeDefs.lean`,
  `WriterCascadeDefsG.lean`, `WriterCascadeDefsO.lean` (the put's
  invariant and the recursion's three forms), `WriterPutAll.lean` (the
  theorems), `WriterCheck.lean`.
- To go on with the puts: section 6. The largest is `OpStep` itself for a
  put: the six books of the delete through the put's rules.
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
