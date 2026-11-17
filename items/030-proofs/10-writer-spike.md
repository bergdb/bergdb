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
  contents, the frame, TREE, the top's clauses, BalancedOK and thirteen
  books of the writer, B1 to B13); `WriterMeets`, one transaction meets
  the contract. Checked on the same traces after every one of the 318,900
  operations, inside the transactions too: no failure.
- **Proved** (item 3, section 4): **a put of a one-segment key** (a key
  of at most 6 bytes), for a tree of any shape. `putKv_put1`: the put
  keeps the contract's invariants, the contents with the put applied, the
  frame, TREE, the top and the put's books, through the descent, the
  leaf's klong, the time split (also in place, also by dead klongs), the
  space split under a parent and at the space root (also in place), the
  recursion up the path, and the new top node with its skip pointers.
  `writerMeets_put1`: a transaction of such puts that the writer accepts
  meets the writer's contract. `runs_meetsTop_put1`: a run of such
  transactions is a history that meets `MeetsTop`, so every get and scan
  of it is right at every time (030-08's theorems). On the standard three
  axioms; no premise but the parameters (`ParamsOK`: node size 6 or more,
  2 ≤ h, h + 2 ≤ M; Java's meet it) and the view's (`Shows`). 11,600
  lines with the map, the statement and the checker.
- **Reduced, not proved:** a put of a key of more segments (the descent
  through segment leaves, a segment root's split, a new segment leaf) and
  every delete. For any operation the step from operations to a
  transaction and a history is proved (`writerMeets_of_opStep`,
  `runs_meetsTop_of_opStep`): what is left is `OpStep` for those
  operations.
- **The main answer** (item 5, section 5): the old route's hard cases do
  not come back. `l4`, R3, R4 and ValOld are all about the fill and the
  rule of two live klongs in an inner root. The old theorem needed them
  because the model's `exec` turns a writer's error into "no change", so
  it had to prove that the writer never gives an error, and a merge
  without a sibling is one. The contract speaks of accepted transactions
  only, and no reader needs the fill; so neither is in the statement, and
  an error is a refusal. By reading the writer case by case (section 5.2),
  the contract's own invariants go through every delete without the fill.
  What does come back, smaller: the take-back's link invariant (which
  klongs name a node the transaction made), now started clean at each
  transaction's start.
- **What it costs** (section 5.3): my estimate is 12,000 to 19,000 lines
  for both, 6,000 to 9,000 for the puts and 6,000 to 10,000 for the
  deletes, against about 230,000 lines of proof in the old line. It is an
  estimate from the design, with one measured point (section 4).
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
  operations so far applied; J3 the frame; J4 TREE; J5 the top's clauses;
  BalancedOK for every node and klong (`BalancedAll`); and the books B1 to
  B13 (which nodes are made, the times, what `madeFor` names, no klong
  names a node taken back, the levels, the ids, replaced nodes as they
  were, made key nodes reached, the bounds, a time klong first).
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

## 5.3 The estimate

My first estimate (16:20, from the route alone) was 6,000 to 9,000 lines
for the puts. The put of a one-segment key alone took 10,900 lines of
proof, of which about 6,000 are shared by every operation (the context
lemma, the node algebra, the primitives, the top node, the run) and about
4,900 are the put's own (its rules as trees, the two splits, the
recursion, the descent). So I was low by a factor of two. With that
factor, and the same method (statements first, one prover a file):

- **The puts of keys of more segments:** 2,500 to 4,500 lines: the
  descent through segment leaves, a segment root's split (a new root under
  a segment leaf, and its in-place form), a new segment leaf (it is empty
  until its first klong, so the "if x had these klongs" form must carry a
  node that is not yet filled; this is the one open design point of the
  puts).
- **The deletes:** 15,000 to 25,000 lines: the bitmap's four forms and
  their well-formedness (W2 to W4), the upward unlink with the take-back,
  LE-b, the merge's forms with the parent's five, the loop, root
  collapse's four forms; and the delete's books (B3, B4, B7, B8, B12,
  B14) through every rule of the put too, about 2,000 of them.
- **Together 17,000 to 30,000 lines** more, three to six waves like
  today's three (two and a half hours, 7 points of the week): one to two
  nights of this kind. Against about 230,000 lines of proof in the old
  line for the same writer, with `l4` open.

The reason it is not more: every rule is local once the context lemma is
there, and the fill is gone. The uncertain part is the merges' loop and
root collapse, which descend again from the root after each change
(`descendToHeight`, `descendToSegmentRoot`): each round needs the tree
closed, so `Mid`-like facts must hold between rounds, not only between
operations. I did not check that on traces (the checker looks between
operations).


# State

2026-11-17, 18:30. Items 1 and 2 done; item 3 done for keys of one
segment; item 4 (the deletes) not started; item 5 written (section 5).

- Branch `030-10-writer` in the clone
  `/Users/f/fl/bench/2026-11-17/night/s4d/clone`, main d656263a merged in.
  Last gated commit: 2aad54c9.
- Build: `cd lean/contract && lake build`. Gate: `lean/contract/gate.sh
  d656263a`.
- Traces: `java/build.sh`, `cd lean && lake build treecheck`,
  `java/stress/treeconf.sh small`, `drain` and `reclaim`; then
  `lean/contract/writer.sh` (and `check.sh` as before).
- To read first: `Contract/Writer.lean` (the map, the statement),
  `Contract/Proof/WriterState.lean` and `WriterCascadeDefs.lean` (the
  put's invariant and the recursion's form), `WriterPut.lean` (the
  theorems), `WriterCheck.lean`.
- To go on: the next put is a key of more segments (drop `PathInner` from
  `CasPre`; the tree rule for a segment root's split; the descent's leaf
  step with `searchEq_some`). The first delete is the one that changes
  only its leaf (a bitmap, no merge): a tree rule `Sound.del` with
  `ctx_route` and `mapDel_local`, the bitmap's node algebra, and the
  delete's books in `PInv`.
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
