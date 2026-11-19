# 030-21. The PE writer meets the writer's contract: the proof

Created 2026-11-18 by Frans Lundberg. Status: done (2026-11-19): part 1,
the contract, TREE and the top; part 2, `MeetsFull` for PE (section 5).

The complete proof that PE's writer, "plan, then emit" (026-23, section
1.2; the trial 026-24), meets the writer's contract (030-04), so that the
read proofs (gets and scans at every time, recovery, restarts, eviction,
safe cuts) hold for every history the writer makes. Frans, 2026-11-18,
21:42: "Go! Good luck with the proof." By an agent of coord-1118, from
21:43, on the branch `030-21-pe-proof` in
/Users/f/fl/bench/2026-11-18/pw/clone.


# Result

For Frans, in plain words. The details are in sections 2 to 5.

**The proof is complete.** PE's writer meets the writer's contract, with
TREE and the top, for every transaction it accepts, and so every history
it writes from the empty tree meets `MeetsTop`: by the contract's read
theorems, every get and every scan at every time of such a history, also
through Java's search of the top nodes' skip pointers, gives what the
plain map gives (030-05, 030-08). Lean's three standard axioms only, no
`sorry`; `lean/contract/gate.sh` prints GATE OK.

- **The writer proved** is `Contract.PE.peTx` (lean/contract/Contract/
  PeWriter.lean, 705 lines): PE as total functions on the contract's tree.
  It gives the trial's tree (026-24) at every one of the 221,142
  transactions of 026-21's 288 traces, and run alone it meets the
  contract's checks at each of them and refuses none (section 4).
- **The main theorem**, `Contract.PE.pe_meetsTop_start`: for parameters in
  which a list cut by h, by cap or by c fits a node (`Cfg.Ok`: each between
  1 and M - 1; Java's meet it from M = 2), every history that PE writes
  from the empty tree meets the writer's contract, TREE and the top's
  clauses (`MeetsTop`).
  - `pe_meetsTop`: the same from any state PE keeps whose tree is a start
    tree of the contract (`Start`) with a start top; so it holds whatever
    028-18 decides about the start tree (option A puts the creation's key in
    it): only the corollary from the empty tree, `start_inv`, would change.
  - `pe_step`, one transaction: from a state PE keeps at i - 1 (`Inv`: the
    contract's invariants, TREE, PE's shape from the space root, every key
    node meeting the rules of one node with no klong after i - 1, the ids
    from `next` free, the top's own rules), a transaction PE accepts at i
    meets the contract (clauses 1 to 3, D the nodes written), TREE at i and
    the top's clauses, and leaves a state PE keeps at i.
  - `pe_meets`: such a history meets `Meets`.
  - Not vacuous: PE accepts a history of three transactions from the empty
    tree (puts, a key of two segments, a delete), computed by the kernel,
    and it meets `MeetsTop` (`Contract.PE.Example.meetsTop`).
- **Proved, not reduced**: no premise but `Cfg.Ok` and the start. The
  statements are in lean/contract/Contract/PeStatement.lean (`Inv`,
  `PeHist`), with the program, PeDefs.lean (`Cfg.Ok`, `Shaped`) and
  PeTop.lean (`TopInv`), pinned in statements.pin; no existing statement
  changed.
- **Left**:
  1. That PE accepts every transaction but a put of a key the tree cannot
     hold (not well formed, or more than G + 1 segments) and a tree that
     would grow past H. Tested (no refusal on the 288 traces), shown for one
     history in Lean, not proved. The theorems speak of the transactions PE
     accepts; a refused one changes nothing.
  2. ~~`MeetsFull`~~: done in part 2 (section 5): every history PE writes
     from the empty tree meets `MeetsFull` and K-LEVEL (`pe_full`), so
     recovery, restarts, lazy reading, eviction with handles and reclaim's
     safe cuts (030-07, 030-14, 030-17) hold for PE, and the reads after a
     crash are right (`pe_crash_reads`). Premises: `Cfg.Ok`, the top
     nodes' level at most 2^62, fewer than 2^48 - 1 transactions, each
     transaction's keys distinct (Java's Dag keeps one operation a key).
  3. Java: PE is the model's writer; Java's write half is not PE yet
     (026-24's recommendation, step 2). Java against the model stays
     tested, by design.
- **Size**: 15,003 lines in lean/contract (the program 705, the
  statements 56, an example 55; 026-24's lemmas of emit, settle and the
  abstract tree, 3,600, copied and kept; new tonight about 10,600). 026-24
  estimated 6,500 to 9,500 lines of its own; the bookkeeping (each node
  written once, which old nodes a run uses, TREE) and the keys of several
  segments took more than estimated.


# 1. The plan

As 026-24 recommends (section 3.5 and the Result):

1. PE's writer as total functions on the contract's tree, executable
   (`lean/contract/Contract/PeWriter.lean`, `Contract.PE.peTx`), shown on
   the traces to give the trial's trees.
2. The main theorem: for a tree that meets the contract's invariants,
   TREE and PE's shape at time i - 1, every transaction PE accepts at
   time i meets the contract (C1 to C3), TREE (C4) and the top's clauses
   (C5), and leaves a tree with the same properties at i; so every
   history PE writes from the start tree meets `MeetsTop`, and the read
   theorems apply. Named in Statements.lean, Axioms.lean and
   statements.pin.
3. The order of work: the program, the top, the trial's lemmas moved into
   the contract package, then the segment theorem (plan, settle and emit
   of one segment's tree, with the next segment's trees as the leaves'
   payloads), then the transaction and the history.


# 2. The program

`Contract/PeWriter.lean`, about 700 lines, no Mathlib. The trial's rules
(026-24, section 2.1) as total functions with fuel on the contract's tree
(`Tree`, `Top`); a run that runs out of fuel or meets a tree that is not
PE's refuses (none), as the trial threw an error. Changes of form from the
trial, none of which changes a tree but the ids of new nodes:

- a segment's tree is planned and emitted before the segment leaf above
  it is planned (`planTree` inside `applyGroups`), so the leaf gets the
  new root's id;
- a new node is a pointer of none in the decisions, not the sentinel id;
- a delete of a key the tree cannot hold (not well formed, or of more
  than G + 1 segments) is dropped as the noop it is (`dropNoops`): the
  trial and Java do nothing for it; a put of such a key is refused.

A first version cut a child into its parts in its parent's plan, not at
emit; the trace run found that a joined planned node then gives its parts,
not its whole list, and that this changes a tree in 3 of 221,142
transactions (the drain traces d-fifo2-3 and d-fifo2-5; the smallest case,
29 operations, in 21-pe-proof/runs/min-case.txt). The program now cuts
at emit, as the trial does.


# 3. The proof

In lean/contract, beside the contract's proofs; each file's header says what
it proves and from what. The order of the argument:

- **The statements**: `Contract/PeStatement.lean` (`Inv`, what PE keeps of
  its state; `PeHist`, the histories PE writes), `Contract/Proof/PeDefs.lean`
  (the shared definitions: `view`, a tree node read as an abstract node of
  lists, a segment leaf's entries its payload ids; `Shaped`, PE's shape
  through the segments; `absV` and `fin`, a planned virtual node before and
  after its children's cuts; `Holds`, what a written node holds; `Ui`, `pays`
  and `oldPart`, the old nodes a run uses; `Cfg.Ok`).
- **026-24's lemmas**, copied from the trial's `lean/peproof` and kept as
  they were but for the definitions now in the program: `PeEmit.lean` (the
  lemma of emit: a node written holds its list, stays well formed, earlier
  readers see it unchanged), `PeSettle.lean` (the lemma of settle: dropping,
  joining and cutting children keeps the keys and the ranges), `PeAbs.lean`,
  `PeAbsOrder.lean`, `PeAbsRoot.lean` (PE's plan as relations, `Plan`,
  `Sett`, `Root`, on an abstract tree of one segment: the keys and the order
  kept, `Plan.keys`, `Plan.wf`, `Root.keys`, `Root.wf`; one constructor
  added, `Root.down`, the materialization of a root's children), and
  `PeQuarry.lean` (030-10's node algebra). The trial's one-segment glue
  (its View, Chain, Realize, Quarry2) is not used and was removed.
- **The program is an instance of the relations** (`PeInst.lean`,
  `plan_inst`, `settle_root`, `mat`): `plan` is a `Plan` with the
  operations of the compare values it touches, `rebalance` a settle (drops,
  joins, joins of inner nodes rebalanced one level down), `settleRoot` a
  `Root`, and the cuts at emit a settle; `PeRuns.lean` (`plan_runs`) ties
  each touched compare value to what the leaf did for it.
- **The old nodes a run uses** (`PeOwn.lean`, `plan_own`, `settle_own`):
  each node of the tree before is used at most once (a base, an untouched
  subtree, a payload's old subtree), so with TREE at i - 1 no node is
  written twice and no untouched subtree is touched.
- **Emit realizes the plan** (`PeEmitSpec.lean`, `emit_spec`): emit writes
  each planned node once, fresh or an appended base; every entry it gives
  holds its planned piece (`Holds`: its level, at most M klongs by the
  decision and `Cfg.Ok`, W1 to W4, pointers to nodes, its live list); the
  nodes reached are among the old nodes used and the run's fresh ids.
- **The keys** (`PeKeys.lean`): the contract's plain map split by a key's
  first segment, each block changed by its own operations (`applyOps_blocks`),
  a short segment's last put, a long one's next segment's tree
  (`applyOps_cons_block`), and the deletes of keys the tree cannot hold
  dropped (`applyOps_dropNoops`).
- **What the tree after is** (`PePost.lean`): a node that holds an ordered
  plan, with sound payloads, is sound for the contract (`good_of_holds`),
  holds the plan's keys (`L_of_holds`), is shaped (`shaped_of_holds`); the
  tree before read the same way (`view_wfe`, `view_L_pays`); unchanged
  subtrees keep all of it (the transfer lemmas); the times; the contract's
  clauses 1 and 2 from a sound root (`clauses_of_good`).
- **One segment's tree, with the next segments' below** (`PeSeg.lean`,
  `planTree_ok` by induction on the fuel, `seg_space` for the space root):
  the writes, and in the tree after the new root's shape, soundness, keys
  (the old keys with the operations), the rules of one node at every node
  reached, and the nodes it reaches.
- **The top** (`PeTop.lean`, `topInv_new`): the new top node, with Java's
  skip pointers (`TopDs.newSuperRoot`), meets `TopStep`.
- **The transaction and the histories** (`PeTx.lean`): `pe_step` (clause 3,
  the frame, from the writes: an old node written keeps its klongs and gets
  a time klong of i first; TREE from the reach bound, the old tree's TREE
  and the fresh ids), `pe_meetsTop`, `pe_meets`, `start_inv`,
  `pe_meetsTop_start`; `Contract/PeExample.lean`, the example.

Lines: PeWriter 705, PeStatement 56, PeExample 55; PeDefs 204, PeInst
1,851, PeRuns 841, PeOwn 1,319, PeEmitSpec 2,044, PeKeys 1,003, PePost
972, PeSeg 1,940, PeTop 367, PeTx 457; 026-24's PeEmit 466, PeSettle 569,
PeAbs 408, PeAbsOrder 974, PeAbsRoot 128, PeQuarry 644. In all 15,003.


# 4. The program on the traces

In 21-pe-proof/ (the trial's program with two checks added, as
`PeTrial.lean.txt`; `runpec.sh`; the summaries in `runs/`), run on 026-21's
288 traces (221,142 transactions; node sizes 8, 14, 30, 62):

- `--pec`: at every transaction, `peTx` from the trial's PE tree before; its
  tree after compared with the trial's, ids matched: the same tree at all
  221,142 transactions, no node written twice, no refusal.
- `--pecrun`: `peTx` alone from its start tree through every trace, with
  the contract's checks at every transaction (C1 to C5, the frame, fresh
  ids, the shape rules), the contents against the reference map, and Java's
  1,067,010 GET and SCAN lines: no failure, no refusal; its counts that
  depend on the trees only (nodes made, nodes changed, top nodes, bytes)
  equal the trial's on all 288 traces.
- The trial's own RESULT lines are unchanged (282 of 288 whole; 6 differ
  only in counts the trial program got after its first runs).


# 5. Part 2: `MeetsFull` for PE

The coordinator, 2026-11-19, 02:10, within Frans's go: `MeetsFull` for PE,
so that recovery, restarts, lazy reading, eviction with handles and
reclaim's safe cuts (030-07, 030-14, 030-17) hold for PE; then, if time
allows, PE's acceptance. On the branch `030-21-full`.

- **PE's record in the model's words** (`Contract/PeRecord.lean`): the
  primordial change (`c0`: the root, node 0, on the root's level; the space
  root, node 1; the start top node, node 2, on the top nodes' level); a
  transaction's change (`peChange`: the fresh ids written as the nodes
  made, with their levels, a value a data node; a new top node on the top
  nodes' level plus its ordinal; the entries added, for each node written in
  the order written, the entries of the klongs it got, `newVals`; the
  root's entry for a new top node and its root and skip pointers; no touch);
  a run and its history (`peRun`, `peHist`). The levels are the model's
  (`Params.topLevel`, `Params.rootLevel`). Every computed clause of
  `MeetsFull` holds for it on a test history of 72 transactions.
- **The bridge's computed clauses** (`Contract/Proof/PeBridge.lean`,
  `pe_bridge`, `pe_bridge_hist_full`; by a sub-agent): N, K, F4, W, W5, A4,
  A2, A3, A5 (`bridgeOk`) and `Made`, with a new invariant `InvB` (node 0
  is no node; W5 and A4 of every key node). A premise: each transaction's
  keys are distinct (Java's Dag gets one operation a key): with two puts of
  one key the first put's value is made and never reached (A3 fails; the
  test history shows it).
- **The top's clause TB** (`Contract/Proof/PeFull.lean`, `pe_topLocal`,
  `pe_topChange_hist`), with the model's levels along the history
  (`pe_levels`). Premises: fewer than 2^48 - 1 transactions (the top
  nodes stay below the root's level: Java refuses at 2^48 top nodes, 030-02,
  which PE's model does not), and the top nodes' level at most 2^62.
- **The start** (`pe_start`: `StartB`, `topStartOk`), **the touch** (PE
  touches nothing: `pe_touch_hist`).
- **A6' and A-COPY** (`Contract/Proof/PeAdopt.lean`, `pe_adopt_hist`; by a
  sub-agent): proved from `Prov` (every old node that a written node names by
  a live klong was before a live child of it, or of an old node reached and
  not written), with an invariant `InvA` (A6' without "below x": every key
  klong names a live child, a value, or a node not reached), and TREE before
  and after; `Prov` holds on all 221,142 transactions of the 288 traces
  (21-pe-proof/runs/adopt.txt).
- **`Prov` proved** (`Contract/Proof/PeProv.lean`, `pe_prov`,
  `pe_prov_hist`; the same sub-agent): emit writes only bases decided
  `append`, and a node written names fresh ids or kept children of its own
  planned node (`emit_prov`); the plan's kept children are children before
  of their node's base, of a node the plan consumed (opened by a join,
  collapsed by the root's settle: in no planned node's old nodes, so not
  written), or of a node below the segment that a run moved
  (`rebalance_step`, `plan_prov`, `settle_prov`); the runs, by an induction
  over the fuel with the next segment's trees (`fp_all`), each run's writes
  the only ones on its old part; a segment's step (`seg_prov_some`).
  Without the premise: `pe_adopt_copy`, `pe_adopt_hist_full`.
- **K-LEVEL** (`pe_kinds`: every key node's kind is its level's, `peKind`),
  which the reads after a crash ask besides `MeetsFull`.
- **The whole**: `pe_meetsFull_of_prov`, `pe_full_of_prov` (`MeetsFull`
  and K-LEVEL) and `pe_crash_reads_of_prov` (reads after a crash for PE),
  given `Prov`; with `Prov` proved, `pe_full` and `pe_crash_reads`
  (`Contract/Proof/PeFullProved.lean`), in Axioms.lean.
- **Size of part 2**: PeRecord 104, PeBridge and PeBridgeKs about 1,000,
  PeAdopt 1,046, PeProv 2,580, PeFull 970, PeFullProved 38, examples 72.


# State

2026-11-19, 04:43. **Done.** Part 1 on main (b15f4b1b). **Part 2,
`MeetsFull` for PE, proved**, GATED: 06d03970 on the branch
`030-21-prov-land` in /Users/f/fl/bench/2026-11-18/pw/clone (one commit on
main d035643c; the history on `030-21-full` and `030-21-adopt`, the same
tree; `gate.sh d035643c` GATE OK, 137 theorems, the standard axioms only;
the pinned files changed: Axioms.lean, with `pe_full` and `pe_crash_reads`
added, PeAdopt.lean, its header only, and the new PeFullProved.lean; no
existing statement changed). No run going. Left (Result): PE's acceptance
(tested), Java.

# Log

2026-11-18. Created the item; the clone at main 6015f9cf, branch
`030-21-pe-proof` (21:43). The program written and run on small examples
(22:05); the top (`TopInv`, `topInv_new`: the new top node meets
`TopStep`, Java's skip pointers) proved by a sub-agent (22:10). The trace
comparison (a sub-agent, 22:10 to 22:57): the program gives the trial's
tree in all but 3 of 221,142 transactions; refusals of 3,893 transactions
for deletes of keys of more than G + 1 segments. Both fixed (23:05).

2026-11-18 to 19. The proof, by this agent and five sub-agents of it, each
on a branch of its own in /Users/f/fl/bench/2026-11-18/pw/, merged here:
the shared definitions (23:35 to 23:47); the program as an instance of
026-24's relations, `PeInst.lean` (23:15 to 23:45); emit realizes the plan,
`PeEmitSpec.lean` (23:50 to 00:20); the keys by blocks, `PeKeys.lean`
(00:22 to 00:34); the old nodes a run uses, `PeOwn.lean` (00:25 to 00:38);
what the tree after is, `PePost.lean` (00:35 to 00:49); one segment's tree,
`PeSeg.lean` and `PeRuns.lean` (00:55 to 01:55); the transaction and the
histories, `PeTx.lean` and `PeStatement.lean` (01:55 to 02:02); the gate
(02:04), the example (02:05). The trace comparison again with the fixed
program (23:02 to 23:20): the trial's tree at all 221,142 transactions.

2026-11-19. Status done: the proof complete and gated (02:10).

2026-11-19. Part 2 (the coordinator, 02:10): PE's record in the model's
words (02:15), the bridge's computed clauses (a sub-agent, 02:20 to 03:00),
A6' and A-COPY from `Prov` (a sub-agent, 03:10 to 03:50), TB, the start,
K-LEVEL and the whole given `Prov` (03:55 to 04:10); `Prov` started (a
sub-agent, 03:55) and proved (04:37: emit, rebalance, plan, settle, the
runs, a segment's step, the transaction); `pe_full`, `pe_crash_reads`
(04:40).
