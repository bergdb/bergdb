# 030-16. The model's writer meets the contract: the delete

Created 2026-11-17 by Frans Lundberg. Status: open.

Beside 030-10 (the puts), the night of 17 November: a proof that a delete
of the model's writer (`lean/SIS/Tree/Exec.lean`, `deleteUpward` and below)
keeps `Mid` (030-10's `OpStep` for a delete), so that a transaction with
deletes meets the writer's contract. Written by an agent of coord-1117, "I"
below, on the branch `030-16-writer-delete`. Frans, 17:39: correctness is
the focus.


# 1. The result

(Kept current; the last update is in the State note.)

- **A statement found false, shown in Lean** (section 3, F1):
  030-10's `WriterMeets` (and so `OpStep` for a delete) is false: its
  `BalancedAll` asks every key klong of an inner node, live or dead, to name
  a node one level below, and the writer leaves a dead klong that names a
  node two levels down. `writerMeets_false`: one transaction of 14 puts and 4
  deletes at node size 6 (`Contract/WriterBalancedFalse.lean`, evaluated in
  the kernel). Readers do not care (a dead klong is never followed), and
  the writer's own rule as Shape.lean tests it (live klongs only) holds. Not
  yet restated (section 3, D3).
- **Proved, a delete of a one-segment key whose segment leaf keeps a live
  klong, or is the space root** (`putKv_del1_keep`), for any parameters with
  `ParamsOK`, option 2 (theta) on or off, given that the merges after it keep
  the invariant (`AfterOk`); with the merges off that holds
  (`putKv_del1_keep_off`). The bitmap in every form
  (`appendDeleteKlong_spec`: the transaction's own bitmap in place or a new
  one, each with or without a compaction, and a full node), the full node's
  time split and space split from a delete, with the recursion up the path
  (`handleFullD_time`, `handleFullD_space`). The delete keeps `MidP`, as the
  put does. This removes the first delete's premises (room for a bitmap,
  theta 0, no merge) but the merges.
- **Proved, the merges' parts:** the merge as a tree rule
  (`Sound.mergeOne`, `Sound.mergeTwo`: two adjacent siblings' live klongs in
  one or two new nodes, the parent's klongs set; the same keys); a merge's
  parent in every form (`mergeParent_spec`: the bitmap of the right child's
  klong, the pointers set in place or by new klongs, a full parent by a time
  or space split); root collapse at the space root (`Sound.collapse`,
  `collapseRoot_spec`: a root of before cut back, a root the transaction made
  taken back); the merges' loop and `afterDelete` with the merges on
  (`mergeUp_spec`, `afterOkW_on`), given the merge's step (`MergeOk`); the
  merge itself reduced to its middle part (`merge_spec_of_rest` from
  `WmgRestOk`: proved are the sibling's choice, the reads, and the two merged
  nodes left out with the take-back; open: the new nodes and the parent's
  change from the tree rules, 2,400 lines so far).
- **The take-back needs a link book, and it must speak of every node** (F2,
  section 3): `WcrLink` (a node reached that the transaction made is named by
  one node of the map at most, by none if it is the space root) with `SNamed
  s` (030-10's: a klong of before names a node of before). Root collapse and
  the merge take it as a premise and give it back. That every other step of
  the writer keeps it (the put's, the bitmap's, the splits') is not proved:
  the one open piece between the merges and a whole delete with the merges on.
- **Not yet:** the upward unlink of an emptied leaf (the climb, the
  take-back, LE-b), keys of more segments.


# 2. What is proved

In `lean/contract/Contract/Proof/`, on the standard three axioms; the gate
passes.

- `WriterDelDefs.lean`: `CasPreD`, `CasPostD` (the put's `CasPre` and
  `CasPost` for a node that a delete changed: x would be V, maybe over its
  size, and the writer gives V's last version), `DelVirt` (what a caller of
  the bitmap gives: the state with x set to any V with x's live klongs but
  those of the compare value meets `PInv`).
- `WriterDelTime.lean` (710 lines), `WriterDelSpace.lean` (1,720):
  `handleFullD_time`, `handleFullD_space`, copied from 030-10's
  `WriterTimeSplit.lean` and `WriterSpaceSplit.lean` and adapted; the
  parent's step is the put's `appendKlongs_spec`.
- `WriterDelBitmap.lean` (240): `appendDeleteKlong_spec`, and `wdb_spec`
  for any compare value whose bits are not all in the last bitmap (a
  well-formed bitmap need not be sorted, so `appendDeleteKlong`'s noop test,
  a list compare, may fail for a compare value with no live klong).
- `WriterDelKeep.lean` (720): `AfterOk`, `afterOk_off`, `putKv_del1_keep`,
  `putKv_del1_keep_off`; `WdkGrow` (a step of the writer never takes a node
  out of `outside`), with small tactics, for every step `afterDelete` calls.
- `Contract/WriterBalancedFalse.lean` (330): `writerMeets_false`,
  `opStep_false`.

How it went: I wrote the statements; four provers (Opus, xhigh), one file
each, 19:20 to 19:50. They changed no statement.


# 3. Decisions and findings

- **D1. New files only; 030-10's statements unchanged.** The delete's split
  is a copy of the put's with V for the node with the klongs added
  (`CasPreD`), not a change of `CasPre`: 030-10 works on those files the
  same night. (030-10 has since made `CasPreH`, the time split for any
  caller; the two may be joined later.)
- **D2. The merges are a premise (`AfterOk`)** of the delete whose leaf
  keeps a live klong, so that the leaf's change is proved for every
  parameter now and the merges plug in when proved.
- **F1. `BalancedAll` is false at reached states.** Found by evaluating the
  writer (a probe over runs of puts and deletes, node size 6, G = 0, H = 2),
  then shown in Lean (`writerMeets_false`). The mechanism: a root made by a
  split in the transaction records the old root, one level lower, as the node
  it replaces (`madeFor`); a later in-place split of that root makes a node
  that inherits the record; when the deletes empty that node, the upward
  unlink takes it back (`takeBack`) and points the stop node's klong to the
  recorded node, two levels below the stop node; the stop node's bitmap then
  deletes that klong. A dead klong; Shape.lean's BalancedOK (live klongs,
  tested on Java's traces) holds. The traces have no such transaction
  (030-10's `writercheck` checks `BalancedAll` after every operation).
- **D3. The restatement, proposed, not made:** `BalancedAll` as Shape.lean's
  BalancedOK, the rule Java's traces are tested by: for the key nodes
  reached, a live key klong of an inner node names a key node one level
  below. It changes 030-10's `Mid`, `PInv`, `Before` and `WriterMeets` and
  about 25 places of 030-10's put proofs (they read every klong of a node's
  level). For 030-10, whose puts are done, or the coordinator: with it the
  link book could be the cheaper `LinkLive` (F2).


- **F2. The take-back's link book speaks of every node, not only those
  reached.** Found by the provers: `Sound.mergeOne` is false without a
  premise on other nodes' klongs that name the merged nodes (E: a dead klong
  in another reached node; checked by `#eval`); `collapseRoot_spec` is false
  with only a book on nodes reached (H: a node not reached, one level above
  a root the transaction made, with a klong to it; then `BalancedAll`, which
  speaks of every node, fails after the take-back). My first book,
  `LinkLive` (a klong of a reached inner node that names a node of the
  transaction names one that node names live), was therefore too weak for
  `Mid` as it stands; two provers had proved it kept by the put's and the
  delete's time and space splits (in restated forms: the "if" state's book,
  not w's; A and B found the statements false as I gave them, by
  counterexamples), 3,500 lines, parked in
  `/Users/f/fl/bench/2026-11-17/night/s4j/linklive/`, not landed. With
  `BalancedAll` restated to the nodes reached (D3), `LinkLive` would do and
  those proofs come back.
- **D4. `WcrLink` and `SNamed s` are the link book of the delete** (H's,
  close to 030-10's B14 `link`), premises of the take-back's steps and given
  back by them.
- **D5. `CasPreD` restated (20:30):** the state with x set to V is asked to
  be sound with BalancedOK (`vsound`, `vbal`), not to meet all of `PInv`: a
  merge's parent may need four klongs more than a full node, beyond
  `Sound`'s M + 3, so its virtual node is its last version, which does not
  extend its node of before (the frame).
- **Statements the provers changed** (each with its reason in the file's
  header): `Sound.mergeOne`/`Two` got `hnames` (F2), `mergeTwo` lost an
  unused `hnl`; `mergeParent_spec` lost two unused hypotheses;
  `collapseRoot_spec` got `WcrLink` and `SNamed s` (F2) and lost
  `ParamsOK`.


- **The second independent review** (another model, at main 3f1e2fea,
  `/Users/f/fl/bench/2026-11-17/night/codex2/review.md`, section 4; the
  coordinator, 21:32), point by point, with where it stands:
  - R1. `mergeParent_spec` assumes `MergeVirt` (the virtually updated
    parent is sound). By design: the caller, `merge_spec`, gives it from the
    tree rules `Sound.mergeOne` and `Sound.mergeTwo`.
  - R2. The tree merge rules assume that other nodes' klongs to the merged
    siblings stay valid (`hnames`). `merge_spec` gives it from the link book
    `WcrLink`.
  - R3. Root collapse is proved under `WcrLink` and `SNamed s` (`LinkLive`
    is gone from it since 20:50), and their preservation through the whole
    writer is unfinished. True: the open piece (section 4).
  - R4. No landed `merge_spec`, `mergeUp_spec`, merges-on `AfterOk`. The
    loop and `afterOkW_on` are proved given `merge_spec`; `merge_spec` in
    work.
  - R5. `AfterOk` is the correctness of `afterDelete` as an assumption.
    `afterOkW_on` proves it with the merges on, from the link book; the leaf's
    change does not yet give the link book back, so the two are not joined.
  - R6. `hkeep` leaves out the upward unlink of an emptied leaf below the
    space root (the climb, the take-back, LE-b). True; not started.
- **F3. Every premise about all nodes of the map is a consequence of
  `BalancedAll` speaking of all nodes.** `WcrLink` (H), `WmgFresh` (C: a
  dead klong of a node not reached may name the next id, which the merge
  then makes, so two nodes name it), `WmgSplitLink`: each is needed only
  because a node not reached must not name a node taken back. With
  `BalancedAll` on the nodes reached (the coordinator's decision, 21:32;
  030-10 restates it), a book on the nodes reached does, and its proofs
  through the splits exist (parked, F2).


# 4. The plan for the rest

- The merges: a tree rule `Sound.merge` (two siblings' live klongs in one
  or two new nodes, the parent's klongs set), `mergeParent` (its forms; a
  full parent by `handleFullD`), `merge`, the loop `mergeUp`; then
  `AfterOk` with the merges on.
- Root collapse for a key of one segment (depth 0: `replaceRoot`,
  `takeBackRoot`, then the loop).
- The upward unlink: the climb, the take-back or unlink of the nodes below
  the stop node, the stop node's bitmap or LE-b (`emptyKeyNext`); a tree rule
  for the stop node losing the klong of a subtree that holds the one key.
- The take-back needs the link book (030-10's B14: a klong that names a node
  the transaction made is a klong of the transaction, in a node that names
  it live), kept by every step, the put's too, and `SNamed s`.


# State

2026-11-17, 22:05. Section 1. The last gated commit: 868af087 (on main
d7966251). I stopped here for the week's budget (55 %, the stop at 60 %),
with 030-10's restatement of `BalancedAll` to come first (F3).

- Branch `030-16-writer-delete` in the clone
  `/Users/f/fl/bench/2026-11-17/night/s4j/clone`. Build: `cd lean/contract &&
  lake build`; gate: `lean/contract/gate.sh <main's head>`. My commits are
  squashed onto main before each GATED (the pins, gate step 5).
- The provers' briefs: `/Users/f/fl/bench/2026-11-17/night/s4j/brief-*.md`;
  the parked `LinkLive` proofs (the put's and the delete's time and space
  splits keep a link book on the nodes reached, in the restated forms of
  F2): `/Users/f/fl/bench/2026-11-17/night/s4j/linklive/`.
- To go on, once 030-10's `BalancedAll` on the nodes reached (live klongs)
  has landed: (1) take a link book on the nodes reached as the delete's
  book (the parked `LinkLive`, or `WcrLink` restricted to namers reached),
  replace `WcrLink`, `WmgFresh` and `WmgSplitLink` by it in
  `collapseRoot_spec`, `merge_spec` and the loop (F3), and the tree rules'
  `hnames` follows from it with TREE; (2) prove it kept by the put
  (030-10's rules: the parked time and space split proofs, the recursion
  `appendKlongs`, the leaf, a new segment) and by the delete's leaf change;
  (3) join `putKv_del1_keep` with `afterOkW_on`: a delete of a one-segment
  key whose leaf keeps a live klong, with the merges on; (4) the upward
  unlink (the climb, the take-back, LE-b; tree rules `Sound.delKid` and
  `Sound.leb` are written in
  `/Users/f/fl/bench/2026-11-17/night/s4j/later-unlink-rules.lean.txt`, not
  proved); (5) keys of more segments.


# Log

2026-11-17, 19:06. Started from the brief of coord-1117; merged 030-10's
gated first delete (24ed4a2f).
2026-11-17, 19:20 to 19:50. The statements (WriterDelDefs, the four files);
the probe found F1; four provers proved the files.
2026-11-17, 20:00. Main 3df76ed5 merged; my commits squashed onto it (the
gate's pins ask the pin file in the commit that changes a pinned file).
GATED 9028c307: the delete's full node, the bitmap in every form, a delete whose leaf keeps a live klong or is the space root (putKv_del1_keep); WriterMeets's BalancedAll shown false (writerMeets_false).
GATED 7ef7ed2d: the merge as a tree rule (Sound.mergeOne, mergeTwo), a merge's parent (mergeParent_spec), root collapse at the space root (Sound.collapse, collapseRoot_spec, with WcrLink and SNamed); CasPreD restated.
2026-11-17, 20:45. Main dc642af1 merged (my commits squashed onto it, for
the pins). Two provers on `merge_spec` and the loop (`mergeUp_spec`,
`afterOkW_on`); the week at 48 %.
2026-11-17, 20:50 to 21:30. The merges' loop proved (`mergeUp_spec`,
`afterOkW_on`: the merges after a delete keep `PInv`, the keys and
`WcrLink`, given `merge_spec`); root collapse restated without `LinkLive`
(only `WcrLink` and `SNamed s`); `LinkLive` retired from the package
(parked). `merge_spec` in work (prover C, 1,850 lines so far): proved where
the parent has room; for a full parent it takes the link book through the
parent's split as a premise (`WmgSplitLink`), the one piece not proved.
The coordinator, 21:32: a second independent review's points on the delete
(section 3, R1 to R6); 030-10 restates `BalancedAll` (reached nodes, live
klongs), my D3.
2026-11-17, 21:30 to 22:05. Prover C: the merge reduced to `WmgRestOk`
(stopped for the week's budget; `merge_spec` left out); prover H: the loop
restated on `MergeOk` and `WmgFresh`. Main d7966251 merged.
GATED 868af087: the merges' loop (mergeUp_spec, afterOkW_on, given MergeOk), the merge reduced to WmgRestOk (merge_spec_of_rest), root collapse with WcrLink and SNamed only; the review's points in the item.
