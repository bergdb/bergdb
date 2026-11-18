# 026-22. MT against the contract: a short check

Created 2026-11-18 by Frans Lundberg. Status: done (the check run
2026-11-18, 11:53 to 12:40; the result below).

A short check of MT (026-17; 006-28, section 7.5) against the writer's
contract of `lean/contract` (030-04, 030-05), for 2026.6's focus (Frans,
2026-11-18, 11:51: "the algorithms, simplifying them, proving them. If
possible."): do MT's in-between states meet the contract, does a read
theorem need a live key below every index node, what is left of the
take-back in MT, what of the writer proof at the tag
`writer-proof-2026-11-18` carries over, and does MT change the stream
format. By an agent of coord-1118, in 90 minutes.

The evidence is in 22-mt-contract-check/; the program on the branch
`026-22-mt-contract`, in `lean/mtcheck/` (026-21's `steptimes` with a mode
`mt` added; `lean/contract/` and today's writer unchanged).


# Result

For Frans, in plain words; the details are in sections 1 to 5.

1. **No, by one clause only.** After a user transaction that empties a
   leaf, and after the fix steps until that leaf is merged away, the tree
   has an empty leaf, which the contract forbids (NonEmptyOK). Everything
   else holds at every step, and every group's end meets the whole
   contract and the writer's own rules. On 288 traces, 453,208 steps:
   C1 fails at 195,177, all by empty leaves; C2 to C5 fail at none.
2. **Yes, the scan.** NonEmptyOK is in the contract's invariants, and
   the scan's proof uses it for its step budget (`Good.nonempty`,
   `nextGo_spec`). The get does not need it.
3. **`toPrev`** returns an older node to its klongs of before when a
   later operation of the same transaction splits it: entries, not nodes,
   and allowed by the frame clause. Its one book (B7, `toPrev_ext`) is
   already proved and used by the put proofs at the tag.
4. **Carries over:** every put; the delete at the leaf when the leaf
   keeps a live klong; for the fix steps the merge's parent, the merge of
   two non-empty nodes as a tree rule, root collapse. **Left:** a contract
   that allows empty leaves, with the scan's proof redone; the delete
   that empties a leaf; the merge with an empty leaf, and the rest of the
   merge, now without take-back or link books; the unlink of an empty
   segment tree; keys of more segments. My judgment: 7,500 to 18,000
   lines, against 13,500 to 24,000 for 026-21's (b).
5. **Yes, a format change** (the record format number, as 6 to 7): a
   start reruns a record's operations, so a user record must rerun
   without merges. A fix step has no operations, so either the start runs
   the fixing itself or a fix record names its key. A stop between the
   two leaves the fixing undone.

**Is MT the shortest route to a complete writer proof?** Possibly, but
only after the contract is changed to allow empty leaves. MT never made
an empty inner node in these runs. The scan's proof would then need a
budget that does not count on a live key below every node, as Java's scan
has none. With that change every MT step goes from a tree that meets the
contract to one that meets it, and the open hard part of 030-16 (the
take-back's link books) and the upward unlink (the climb, LE-b) are gone.
Without the change, MT needs 026-18's two-level contract and a proof that
the fixing removes every empty leaf: the kind of proof 026-19 tried, with
no clear gain. 026-21's (b) needs no contract change. The choice is
Frans's.

**Unknown:** the size is a judgment, not a count; the changed contract
and its scan proof are not written; on the medium and large sets the
full scans inside a group ran at every 20th boundary only.


# State

2026-11-18, 12:40. Done. The branch `026-22-mt-contract` in
`/Users/f/fl/bench/2026-11-18/mt/clone` holds `lean/mtcheck/` and this
item; the runs' outputs are in `/Users/f/fl/bench/2026-11-18/mt/`
(`final/` names the run of each set), their RESULT lines and sums in
22-mt-contract-check/runs/.


# 1. MT's states against the contract

**How.** 026-21's program (`steptimes`, `lean/study/` on the branch
`026-21-study`) copied to `lean/mtcheck/` as `mtcheck`, with a mode `mt`:

- the writer is 026-17's `Mt.lean`, unchanged (`Study/Mt.lean`; today's
  `Exec.lean` underneath, unchanged since 2026-11-13);
- transaction T's user transaction (`Mt.putKv` for each operation) is
  step T · 2^14; then the driver of 026-17 (R5: for each deleted key in
  key order, `Mt.fixStep` until its path needs none), each fix step that
  changes something a step of its own, T · 2^14 + k;
- the contract's checks of 026-21 at every step (C1 the invariants, C2 the
  contents with the step's operations, none for a fix step, C3 the frame,
  C4 TREE, C5 the top), unchanged; a C1 failure is checked again with
  NonEmptyOK left out (`invLoose`: `Contract.invOk` with `kidOk`'s
  `!(live m.ks).isEmpty` removed), and counted as `c1loose` when that
  holds; at each group's end, C1 again (`C1.end`) and the writer's own
  rules (`shapeFaults`);
- at each boundary inside a group (after the user step and after each fix
  step): the get of each of the group's keys by the contract's reader
  (`Contract.get`, a failure if wrong), and a full scan by the contract's
  reader against the reference, once with its own budget (`Contract.scan`:
  `2 · fuel + 2` a `next`; counted when wrong, `midscanshort`) and once
  with 026-17's A1 budget (`2 · fuel + 2 + 2 · nodes`; a failure if
  wrong);
- 026-21's other checks as they were: the gets after each transaction at
  its end, Java's GET and SCAN lines, the full scans, the history.

**Traces**: 026-21's copies (`/Users/f/fl/bench/2026-11-18/st/traces/`):
level 2 (`small` 70, `drain` 110: the night of 17 November's `tree-small`
and `tree-drain`, node sizes 8, 14 and 30), `reclaim` 15, `own` 6 (026-21's
bulk loads and Pub-like index, node size 30), `medium` 27 and `large` 60
(030-12's).

**Counts** (`22-mt-contract-check/runs/aggregate.txt`):

- **Steps**: 288 traces (the same 221,142 transactions and 1,792,106
  operations as 026-21's main set, 647,332 of them deletes); 232,066 fix
  steps in 33,599 groups (of 602,549 calls of `Mt.fixStep`); 453,208
  steps checked with the contract. No writer error; nothing taken back
  (`taken` 0).
- **C1, the invariants**: fail at 195,177 steps, on 142 traces: 18,104
  user steps and 177,073 fix steps. Every one of them holds without
  NonEmptyOK (`c1loose` 195,177), and with NonEmptyOK kept for inner
  nodes (`c1leaf` 195,177): the only fault is an empty leaf.
- **C2 to C5** (the contents, the frame, TREE, the top): 0 failures at
  453,208 steps.
- **The groups' ends** (221,142): C1 holds at every one (`C1.end` 0), and
  the writer's own rules too (`shapeend` empty). In between, `FillOK`
  fails at 84,627 steps and `RootsOK` at 2,784.
- **Reads after each transaction**: 1,792,106 gets, Java's 1,067,010 GET
  and SCAN lines, 26,762 full scans and the history: 0 failures.
- **Reads inside a group**, at 306,133 boundaries: the gets of the
  group's keys by the contract's reader, 0 wrong. Full scans by the
  contract's reader at every such boundary on level 2, reclaim and own,
  at every 20th on medium and large (86,886 in all): with the contract's
  budget 18,919 short (17,573 on level 2's drain set, 1,346 on medium);
  with A1's budget 0 wrong.
- **MT's rules reached**: 162,899 leaves emptied by a user transaction;
  162,891 unlinks of an empty segment tree (`fix.unlink`; most emptied
  leaves are one-key segment trees); 57,352 merges into one node and
  9,043 into two, 18,999 of inner nodes, 4,798 with an empty node (2,788
  of two); 2,780 root collapses (532 of a segment tree); 2,453 only
  children passed over.
- **`toPrev`** in user steps (026-21's V2, `wouldbump` V2.version): 37,519.

Versions: every set but own was run with the program as on the branch;
own with an earlier build without `c1leaf` and the sampling (it made the
full scans at every boundary, `midscans` printed as 0; it has no C1
failure). The medium and large sets ran with `--midscan=20`.

What the counts say:

- **C2 to C5 hold at every step**, the user steps and the fix steps: the
  contents (a fix step changes no key), the frame (MT never takes a node
  back: `taken` 0), TREE and the top.
- **C1 fails only by NonEmptyOK** (`c1loose` equals the C1 failures),
  and only by empty leaves (`c1leaf`, NonEmptyOK kept for inner nodes,
  equals them too): the empty leaves that the user transaction leaves,
  and those still there after the group's earlier fix steps (a group
  fixes one key's path a step; a merge of two empty leaves makes an
  empty leaf, 026-17's guard 6). No empty inner node (026-17's `MT: an
  empty inner node` never fired).
- **Every group's end meets the contract** (no `C1.end`) and the writer's
  own rules (`shapeend` empty): the fill, two live klongs in an inner root,
  the leftmost rule, theta, the heights. In between only `FillOK` and
  `RootsOK` fail, as in 026-17.
- **Reads in between**: the contract's get is right at every boundary;
  the contract's scan with its own budget is short at the boundaries
  counted in `midscanshort` (the fifo workloads, deletes at one end:
  d-fifo and d-fifo2 at node size 8, m-fifo at 30), and right everywhere
  with A1's budget.


# 2. Does a read theorem need a live key below every index node?

**Yes, the scan.** The main theorems (`Contract/Theorems.lean`:
`inv_right`, `get_right`, `scan_right`) take a history that meets the
contract (`Meets`), so the invariants at every time (`invOk`,
Contract/Statement.lean, section 2). Those include NonEmptyOK: `kidOk`
asks `!(live m.ks).isEmpty` of every key node a live klong names, and
`invOk` asks it of an inner space root.

- The scan's proof uses it: `Good.nonempty` (Contract/Proof/Good.lean: a
  sound node with a live klong holds a key) gives `nextGo_spec`
  (Contract/Proof/Chain.lean) its bound, `ch.links.length + s.fuel r + 1`
  steps for a `next`, from a descent that always finds a key. The scan
  (`Contract.scan`, Contract/Read.lean) gives each `next` `2 · fuel + 2`.
  This is the model's TP27 that 026-17's scans broke.
- The get does not need it in substance: `getGo` follows one path, with
  the root's level as its fuel. It still gets the invariants through
  `Meets`, so a changed NonEmptyOK changes its premise, not its proof.
- So the contract as it stands does not admit MT's in-between states,
  and section 1 shows that this is the only thing it does not admit.

**What a change would take** (not done here): NonEmptyOK kept for inner
nodes and dropped for leaves below the space root (MT never makes an empty
inner node), and the scan's budget made independent of it, as 026-17's
A1 did: a bound from the number of nodes, or Java's loop without a bound
(`GetMany.Chain.next`). Then `nextGo_spec`'s fuel argument is redone (a
`next` may cross a run of empty leaves; each is entered and left once).
`Contract/Proof/Chain.lean` and `Scan.lean` are where; the get and the
contents (`contents`, `listAt`: an empty leaf holds no key) are as they
are. My judgment: 1,500 to 4,000 lines, and a change of a pinned statement
(030-15's gate), which is Frans's to approve.


# 3. The take-back of entries left in MT: `toPrev`

**What it is.** `handleFullWith` (Exec.lean, the end of the definition)
and `unlink` call `n.toPrev (tt − 1)`: when a node that existed before the
transaction gets klongs of the transaction from one operation and a later
operation of the same transaction splits it, the node goes back to its
klongs of before (Java's `KeyNode.toPreviousState`), and the split's new
nodes hold its last version. MT's user transaction keeps it, because it
calls today's splits unchanged (026-17, T3's finding 4). In a fix step it
never acts: a fix step writes nothing into a node before splitting it.
026-21 counts it as V2; here 37,519 times in user steps over all 288
traces (`wouldbump` V2.version).

**Would a writer proof need books for it?** One, and it exists. The
frame clause of the contract allows it: the node of before ends with its
klongs of before (`o' = o`, or klongs added after a time klong of the
transaction), which is what `toPrev` gives back. During the transaction a
proof must know that such a node's klongs are its klongs of before with a
version of the transaction after them, and that it is no longer reached
after the split: 026-21's B7 ("an older node that leaves the tree loses
its version of the step"), local to one node. At the tag it is
`toPrev_ext` (Contract/Proof/NodeAlg2.lean: the node's klongs after
`toPrev (i − 1)` are its klongs of before), used by every split proof of
the puts and of the delete's full leaf (`WriterTimeSplit*`,
`WriterSpaceSplit*`, `WriterDelTime`, `WriterDelSpace`) and by root
collapse. So the proved puts carry it already. It is not one of the
books that made 030-16 stop (the link books, `WcrLink`, `WmgFresh`,
`WmgSplitLink`, are about nodes taken back). 026-21's strict rule (bs)
removes it for a third more steps; that was judged not worth it, and the
same holds here.


# 4. What of the writer proof at the tag carries over

The tag `writer-proof-2026-11-18`: 030-10 (every put) and 030-16 (part
of the delete), `lean/contract/Contract/Proof/Writer*.lean` and
`TreeRules*.lean`, about 30,400 lines in the `Writer*` files.

**Carries over as it is:**

- **Every put** (030-10): MT's user transaction runs today's put
  (`Mt.putKv` on a put is `putSegs` with today's `setNode` and `setValue`
  for a value).
- **The delete at the leaf, when the leaf keeps a live klong or is the
  space root** (`putKv_del1_keep`, `putKv_del1_keep_off`): the bitmap in
  every form (`appendDeleteKlong_spec`), the full leaf's time and space
  splits with their cascade up the path (`handleFullD_time`,
  `handleFullD_space`). MT's user delete is exactly this code
  (`Mt.deleteLeaf`: `appendDeleteKlong` and nothing after), and its
  premise `AfterOk` (the merges after the delete) is not needed, as with
  the merges off.

**Carries over in part, for the fix steps:**

- **The merge's parent in every form** (`mergeParent_spec`, a full parent
  by a split): MT's merge calls `mergeParent` unchanged.
- **The merge as a tree rule** (`Sound.mergeOne`, `Sound.mergeTwo`), for
  two non-empty siblings (`hnl`, `hnr`). Its premise `hnames` (other
  klongs that name the merged nodes stay valid) is trivial in MT: nothing
  is taken back, so the merged nodes stay in the map.
- **Root collapse** (`Sound.collapse`, `collapseRoot_spec`), the case of a
  root of before (`replaceRoot`); the take-back cases are not needed. Its
  premises `WcrLink` and `SNamed` hold at a fix step's start: the step has
  made no node yet.
- **The merge reduced to its middle part** (`merge_spec_of_rest`, from
  `WmgRestOk`): the sibling's choice and the reads carry over; the rest,
  without the take-back, is smaller.

**Not needed under MT:** the merges' loop (`mergeUp_spec`,
`afterOkW_on`): one merge is one step; the take-back's link books
(`WcrLink`, `WmgFresh`, `WmgSplitLink`, `LinkLive`), which 030-16's F3
found needed "only because a node not reached must not name a node taken
back"; the upward unlink of an emptied leaf (the climb, the take-back,
LE-b), which 030-16 had not started: MT merges an empty leaf instead.

**Left, each a step from a tree that meets the contract to one that meets
it** (with the contract changed as in section 2; a fix step has no
operations, so its contents clause is "the same keys"):

- the contract change and the scan's proof (section 2);
- the restatement of the proved puts and the leaf's delete to the changed
  invariant: mostly mechanical where they use NonEmptyOK;
- the user delete that empties its leaf (the same code as the case that
  is proved; the invariant now allows the result);
- the merge with an empty node (026-17's R3): a tree rule beside
  `Sound.mergeOne` without `hnl` or `hnr`, and the rest of `merge_spec`
  without the take-back;
- the unlink of an empty segment tree's root: a bitmap on the segment
  leaf above (`appendDeleteKlong_spec` applies), for keys of more
  segments;
- keys of more segments for the delete (030-16 had not started them);
- root collapse of a segment tree (`collapse` at depth above 0).

Not needed for the contract: that the fixing ends, and that it restores
the fill. Neither is a correctness property under the contract. Both
matter for the database's size and speed, and the model tests them
(026-17's fuel; here `shapeend` empty).

**Size, a judgment.** From 030-10's and 030-16's sizes and 026-21's
estimate for (b) (section 5.3 there): the contract change and scan proof
1,500 to 4,000; the restatement 1,000 to 3,000; the user delete with an
empty leaf and more segments 1,500 to 3,000; the merge without take-back,
with the empty case, 2,500 to 5,000; the unlink and root collapse as steps
1,000 to 3,000. In all 7,500 to 18,000 lines, against 13,500 to 24,000 for
(b) of 026-21. The difference is (b)'s delete with its climb and LE-b,
which MT does not have. Neither has the link books. The estimate is not
counted from code; 026-19's trial (MT with a fill invariant, before the
contract) found its fill proofs costly, and the contract drops the fill.


# 5. Does MT need a stream format change?

**Yes: at least the meaning of a record, and so the record format number
(7 to 8, as 6 to 7 was for the merges, 027-03, section 8.2).** A start
reruns the records of its startup section from their operations, at their
times, with the same ids (027-03, section 14.2, `rerunTransaction`). The
tree a rerun builds is part of the format.

- **The user record.** Its deletes must be rerun as MT's user delete:
  a bitmap, no merge, no upward unlink, no root collapse.
- **A fix step as a record of its own.** It is a transaction with its own
  time, as 026-17's model runs it. It has key nodes and maybe a top node,
  and no value or delete node: the layout allows that (an empty record is
  48 bytes; the creation's record has no KV). But a rerun has nothing to
  rerun it from. Either the start runs the fixing itself after each user
  record (the driver is deterministic, so it makes the same steps, times
  and ids, and the fix records are only checked), or a fix record names
  the key it fixed (a new field, or an internal KV), and the start reruns
  `fixStep` for that key.
- **A stop between a user record and its last fix record** leaves a tree
  with empty leaves. It is right for Java's readers (by reading, 026-17),
  and right for the contract only if the contract is changed as in
  section 2. Its fill is restored only when a later delete fixes the same
  path, or when a start finishes the group, but a start appends nothing
  today (027-03, section 14.2).
- **Under 026-18** (readers see only the ends of main transactions): the
  times must tell a main transaction from its subtransactions, a change of
  the time klong like 026-20's 48 + 14 bits. A stop between
  subtransactions then shows readers a state between them, unless the
  start finishes the group.

Not changed: the node layouts (key node, klongs, top node, value and
delete nodes) and the record's header.


# Evidence

In 22-mt-contract-check/:

- `MtCheck.lean.txt`: the program (`lean/mtcheck/MtCheck.lean` on the
  branch); `MtCheck-vs-StepTimes.diff.txt`, its difference from 026-21's
  `StepTimes.lean`; `lakefile.toml.txt`, the package. The writer is
  026-17's `Mt.lean` (17-mt-trial/Mt.lean.txt), unchanged, as
  `lean/mtcheck/Study/Mt.lean`.
- `scripts/runall.sh`, `scripts/runall2.sh` (the same, with a sample of
  the scans inside a group, `--midscan=K`), `scripts/agg.py` (the sums).
- `runs/results-SET.txt`: every RESULT line of mode mt, a trace a line,
  for the sets level2-small, level2-drain, reclaim, own, medium,
  large-seed1 (seed 1 of each of the large set's six workloads) and
  large-rest; `runs/aggregate.txt`, the sums by set and in all.


# Log

2026-11-18, 11:53. Started (coord-1118's brief): the clone, the branch
`026-22-mt-contract`, the Lake caches copied.

2026-11-18, 11:56. `lean/mtcheck/` built: 026-21's program with mode
`mt`; level 2 and reclaim run (no error, C1 fails only by NonEmptyOK).

2026-11-18, 11:58. All sets started, 6 at a time. The medium set was
slow with a full scan at every boundary inside a group: restarted with
`--midscan=20`.

2026-11-18, 12:06. `c1leaf` added (NonEmptyOK kept for inner nodes); the
sets without it run again (12:20 to 12:36).

2026-11-18, 12:40. Done: all 288 traces, the result, sections 1 to 5.
