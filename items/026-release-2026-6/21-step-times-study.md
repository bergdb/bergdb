# 026-21. A first study of two writer designs: step times and net change

Created 2026-11-18 by Frans Lundberg. Status: done (the study run
2026-11-18, 09:00 to 10:55; the result below). The recommended (b),
step times with the delete in pieces, not taken (Frans, 11:23; 006-31);
the writer became PE (026-24, 026-25).

A first study of both designs of 026-20 (step times, net change), in the
Lean model only, before Frans decides the direction of 2026.6's writer
(Frans, 2026-11-18, 08:49). One combined study (Frans, 08:56).

The goal, in Frans's words (08:56): "Note that simplification is the
overall goal, getting rid of take-back completely is one way to reach it.
It is not a goal itself." So the question is: which design, if any, makes
the writer (the algorithm and a future proof of it) simpler, and at what
cost in bytes, node fill and speed.

The evidence is in 21-step-times-study/: the program and the writers as
`.lean.txt`, the scripts, the runs' summaries. The code is on the branch
`026-21-study`, in `lean/study/` (a Lake package of its own beside
`lean/contract/`; today's writer, `lean/SIS/Tree/Exec.lean`, and
`lean/contract/` are not changed).


# Result

For Frans. The details and the evidence are in sections 1 to 6.

**Recommendation: (b), step times, with a delete cut into its pieces.** It
is the only one of the designs that makes the writer simpler; net change
(a) is already today's Java, so (c) is (b); deletes apart changes nothing
that matters.

- **Net change (a) is today's Java** (section 1): a transaction reaches the
  writer with one operation a key (`Trans.Builder`, `Db.transformKeys`;
  Frans, 2026-11-11). No trace has a key twice in a transaction. The
  take-back that is left is all between different keys.
- **Risk 2's answer** (section 2): step times cannot work with bumps
  between operations only. A delete makes nodes and then merges or
  collapses them itself (a full leaf's split and then its merge; a merge's
  full parent and the next merge; a root made and collapsed): with bumps
  between operations only (b0), 61 % of today's take-backs are left. Cut
  into pieces (the change at the leaf or the upward unlink; each merge;
  each root collapse), with a bump allowed between pieces, the rule holds
  everywhere: 0 take-backs, and no piece ever changes a node it made. The
  steps that end between pieces meet the contract (checked at every step);
  only the fill and the root's two live klongs wait for the next piece.
- **The checks**: on 288 traces (221,142 transactions, 1.8 million
  operations) every variant gave the right map at every transaction,
  Java's 1,067,010 reads, and the contract at every step (340,223 steps of
  b). The pieces run back to back are today's delete exactly. A pruned step
  writer (today's minus the take-back, the splits in place and their
  books) gives the same results as b.
- **The cost** (section 4), b against today: at node size 30 on random
  work nothing (B-new 1.000 to 1.017), on a Pub-like index workload 2 to
  4 % more bytes (the index 4 to 7 %), 3 % less fill. The bad case is
  sequential inserts in large transactions: a sorted bulk load of 500 keys
  a transaction writes 1.41 times the bytes (2.2 times the index), with
  10 % less fill and a tree one level taller at 20,000 keys; m-fifo
  (inserts at one end, deletes at the other) 1.31. That is exactly
  what today's writer pays for the same load in transactions of 10 keys:
  the splits in place, which step times forbid, are what makes large
  sorted transactions cheap today. Over all 288 traces: B-new 1.12, B-all
  1.06, 1.54 steps a transaction, at most 44.
- **The simplicity** (section 5): gone from the writer are the take-back
  in its four forms, the splits in place (a put has six rules, not ten),
  the top node changed in place, and the books of what a node replaces;
  the model writer is about 13 % smaller. Gone from a proof are the books
  B3, B4, B9, B12, B14 and the delete's link books (`WcrLink`, `WmgFresh`,
  `WmgSplitLink`, `LinkLive`, `SNamed`), which were the open, hard piece
  where 030-16 stopped. Each piece starts from a tree that meets the
  contract. My estimate: the deletes' proof a third smaller (13,500 to
  24,000 lines instead of 20,000 to 35,000), and without its open problem.
  The strict rule (bs, an older node's version never cut either) removes
  one more book for a third more steps: not worth it.
- **Java** (section 6): the time klong's 62 bits as 48 + 14 (a format
  change), the end of T for readers, a `Time` type, the delete in pieces,
  and one new thing to design: a check before each piece that tells
  whether it will change a node of the step (the model runs and compares;
  Java cannot). Out go the take-back and the splits in place.

**Still unknown**: Java's real bytes and commit times; how close Java's
check before a piece comes to the model's (a cruder check on the key's
path bumps up to about 60 % more); heights and fill at 10 million keys;
restarts, reclaim and eviction run with step times (by design unchanged:
a record holds all the steps of its transaction, cuts fall on transaction
ends; not run); the proof estimate is a judgment.

**Next step**, if Frans takes (b): a design note (a 026 subitem) that
settles the check before a piece, the time klong in the stable format
(026-12), a top node a step, and whether to soften the sorted-load cost (an
uneven split for appends; a merge that takes a full leaf's live klongs
without the split first, D1 of section 2); then the step writer in the
model (`Study/ExecStep.lean` is a start) as the trace checker's writer, and
the writer proof restarted on it, per piece; then Java.


# State

2026-11-18, 11:00. Done. All runs ended, with no failure: 288 traces in
modes today, split, b0, b, bs, bp and d, and 120 more (the large set's
seeds 11 to 30) in today and b. The branch `026-21-study` holds the code
and this item.


# 1. Net change is today's Java

Design 1 (026-20) computes a transaction's last operation for each key
before the writer runs. Java does that already, and has since before
2026.4:

- `Trans.Builder.build` keeps one KV a key (a `TreeMap`, the last call
  wins), and `Db.transformKeys` refuses a transaction whose key
  transformations make two KVs one key (024-16; Frans, 2026-11-11, 09:43:
  "One transaction must not set (put or delete) a value more than
  once! This is a strict rule."). A transaction reaches the Dag with one
  operation a key, in key order.
- The trace checker tests it on every trace (C-T7, the keys strictly
  increasing), and this study counts it again: `dupkeys` is 0 in every
  transaction of every set.

So the take-back that is left is all between different keys, and design 1
as written changes nothing: variant (a) is today's writer, and (c), both
together, is (b). What 026-20 calls churn on one key ("put then delete of
k") never reaches the writer. The variant "deletes apart" (a transaction's
deletes at one internal time, its puts at the next) is measured below as
mode d, as the one form of net change that changes something.


# 2. Risk 2: the rule inside one operation

026-20's risk 2: a bump in the middle of an operation would end a step in a
state that is not a finished tree. Read in `Dag.java` and in the model's
writer (`Exec.lean`, which follows `Dag.java` node for node), and counted
on the traces (mode b0, section 4).

**The answer: step times cannot work with bumps between operations only.**
A delete changes or drops nodes that it made itself, so it needs a bump
inside it. But the places where it needs one are between its own pieces of
work, and each piece leaves a finished tree for the contract (the contract
has no fill rule). With the delete cut into its pieces, and a bump allowed
between them, the rule holds everywhere: no piece ever changes or drops a
node it made itself (mode b: 0 on every trace). The states between the
pieces fail only the writer's own rules (the fill, two live klongs in an
inner root), never the contract (checked at every step).

The paths, put first:

- **A put never needs one.** Its splits go up the key's path: each makes
  its new nodes whole (the halves, the last version, a new root) and adds
  klongs to the parent, a node from before. A new segment leaf is made
  empty, linked, and then gets the key's klong (`Dag.setNode`, then
  `setValue`): a node changed by the operation that made it, but only to
  build it; nothing reads it in between. Making it with its klong is a
  two-line change, if a proof wants it.
- **D1, the delete's split, then its merge.** A delete in a full leaf
  (`appendDeleteKlong`: `bitmap.full`, or theta's `bitmap.dead`) replaces
  the leaf by its last version (a time split) or two halves; then
  `mergeAfterDelete` finds the new node under the fill and merges it with
  a sibling: the node the delete made is taken back (`merge.made.*`,
  `merge.takeback`). With bumps between operations only (mode b0), the
  take-backs left are all of D1 to D3: on the level 2 and reclaim sets,
  mostly of node size 8, 18,605 of today's 25,863; at node size 30, over
  all sets, 400 of 11,525 (section 4.2).
- **D2, the merges' cascade with a full parent.** A merge takes a klong
  out of the parent (`mergeParent`); a full parent is replaced by its last
  version; one level up the loop finds that new node under the fill and
  merges it: taken back again.
- **D3, root collapse of a root the delete made.** A merge's parent that is
  the root, full, is replaced by a new root (and a new top node); then
  `collapseRoot` finds the new root with one live klong and takes it back
  (`rc.takeback.space`, `rc.takeback.segment`, `takeBackRoot`), changing
  the top node it made (`top.inplace`).
- **D4, root collapse twice.** A collapse makes the child the root through
  a new top node; if the child has one live klong too, the next collapse
  changes that top node in place (`top.inplace`), or adds a klong again to
  the segment leaf above, which the first may have split. Possible by
  reading; on the traces every `top.inplace` of mode b0 comes with a
  `rc.takeback.space` of D3 (the counts are equal), so D4 was not seen
  apart.
- **D5, LE-b's split, then its merge.** The upward unlink that stops at an
  inner node gives the empty key the next child's pointer (`emptyKeyNext`);
  a full stop node is replaced by its last version, which the merges then
  find under the fill: as D1.
- Not risk 2: the upward unlink's take-back of nodes below the stop node
  (`up.takeback`): the climb changes nothing before it knows the stop
  node, so those nodes were made by earlier operations of the
  transaction; a bump before the operation removes it.

**What it takes.** A delete is cut into its pieces, each an action of its
own, and the rule is applied between actions, not between operations:

- the core: the delete's change at the leaf, or the upward unlink with the
  stop node's delete or LE-b, with the splits these cause;
- each merge, one level at a time (one turn of `mergeAfterDelete`'s loop);
- each root collapse, one at a time (one turn of `collapseRoot`'s loop).

This is how `Study/Steps.lean` and `Study/ExecStep.lean` run it; each piece
re-finds its node from the space root by the key, as today's loops do
after a split (`descendToDepth`). Mode split checks that the pieces run
back to back are today's delete exactly (the same changes, node for node,
on every transaction). The cost is more steps (section 4): a step can end
between a delete's core and its merge, or between two merges. Readers never
see those states: a user's time T reads at the end of T.

Two alternatives were not tried: a merge that takes a full leaf's live
klongs directly instead of splitting it first (D1 and D5 without the split;
close to 024-22's "merges in place and net", QM1), and a parent replaced
and merged in one piece (D2). Each would remove a bump and a node written
for nothing (section 4), at the cost of new merge forms.


# 3. How it was measured

**The program**, `steptimes` (`lean/study/StepTimes.lean`; as text in
21-step-times-study/StepTimes.lean.txt), runs a writer on the operations
of each transaction of a trace, from the empty tree, on its own structure
P (a hash map, as 026-17's `mttest`): the model's own run, not Java's
structure. Node ids are its own. Every variant gets the same operations.

**Times.** Transaction T's steps are T · 2^14 + k, k = 0, 1, ... (026-20:
14 bits of step); today's writer runs each transaction at T · 2^14. A
user's T reads at the end of T, T · 2^14 + 2^14 − 1. The model's H is the
trace's H + 2, so that a variant may grow a taller tree than Java's (the
greatest height is counted).

**The modes** (one writer each):

- `today`: today's writer (`Exec.lean`'s `putKv`), a transaction one step.
- `split`: today's, with the delete cut into its pieces
  (`Study/Steps.lean`); today's `runOpsFrom` runs beside it on the same P,
  and the changes must be equal: the check that the pieces are today's
  delete.
- `b0`: step times with bumps between operations only. An operation that
  changes or drops a node made earlier in its step is run again at a new
  step; one that changes or drops a node it made itself is let through and
  counted (risk 2).
- `b`: step times as 026-20 states the rule, with the delete in pieces and
  bumps between pieces: a piece that changes or drops a node made earlier
  in its step (V1) runs again at a new step. A piece that cuts back an
  older node's version of the step (`toPrev`, by `unlink` or by a split of
  that node; V2) is allowed: the node is not a fresh node.
- `bs`: as b, with the strict rule: V2 bumps too.
- `bp`: as b, with the step writer as it would be (`Study/ExecStep.lean`:
  today's writer without the take-back, the splits in place, the top node
  changed in place and the books of what a node replaces). Its counts must
  be b's; they are (section 4.6).
- `d`: deletes apart (026-20, design 1's variant): a transaction's deletes
  at one step, its puts at the next; no other bump.

How a bump is found: the program runs a piece from the step's writer
state, compares the state after with the one before (a node made at the
step whose klongs changed, or that was taken back; the top node made at
the step changed; for bs, an older node whose version of the step was
cut), and if so ends the step (its changes go into P at the step's time),
starts the next one and runs the piece again from there. A piece at a
fresh step can break the rule only on nodes it made itself; that is
counted as `self`.

**The checks**, every one on every run, with their failures counted:

- the map: after each transaction, the get of each of its keys at the end
  of T against the program's reference map; each GET and SCAN line of
  Java's trace at the end of its time; a full scan every 10th transaction
  and at the end; at the end, a full scan at the end of every 50th
  transaction against the reference of then (the history);
- the contract of `lean/contract` at every step (`--contract`): the
  invariants and the contents with the step's operations (`contractOk`),
  TREE (`treeOkB`), the top's clauses and the roots' link (`topStepB`),
  and the frame computed over the nodes the step changed (`extOk` and D;
  no other node of P changes). The writer's own rules (`shapeFaults`: the
  fill, two live klongs in an inner root, the leftmost rule, theta, the
  heights) are counted by name, at the transactions' ends and between.

The contract's checkers `contractcheck` and `bridgecheck` read Java's
traces, with Java's KN, NEW, DIRTY and LIVE lines; the model makes no such
trace. So the contract's own functions run on the model's states instead,
at every step: the same clauses, on the variant's trees. `bridgecheck`'s
clauses (Java's structure against the contract's) have nothing to check
here.

**The traces** (read only, copied into the study's area):

- level 2: the night of 17 November's `tree-small` (70 traces) and
  `tree-drain` (110), node sizes 8, 14 and 30;
- reclaim (15), medium (27) and large (60, and 120 of seeds 11 to 30) of
  030-12, with live=0; node sizes 8 to 62;
- the study's own (`scripts/workloads.py`), node size 30:
  - `bulk-500`, `bulk-100`, `bulk-10`: 20,000 keys put in key order, 500,
    100 or 10 a transaction: the sorted bulk load;
  - `pub-1`, `pub-10`, `pub-100`: a Pub-like index: 5,000 objects, each a
    key [O, id] with an index entry [I, value.id], loaded 50 objects a
    transaction; then 4,000, 1,000 or 200 transactions of 1, 10 or 100
    changes to random objects: 80 % an update (put the object, delete the
    old index entry, put the new one), 10 % a delete of the object and its
    entry, 10 % a new object.

**The evidence** in 21-step-times-study/:

- `StepTimes.lean.txt`, `Steps.lean.txt`, `ExecStep.lean.txt`,
  `lakefile.toml.txt`: the program, the delete's pieces, the step writer,
  the package (in `lean/study/` on the branch);
- `scripts/workloads.py` (the own workloads), `scripts/runall.sh` (the
  runs), `scripts/aggregate.py` (the sums), `scripts/compare-bp.py` (bp
  against b), `scripts/sizes.py` (section 5.2);
- `runs/results-SET.txt`: every RESULT line, a trace and a mode a line;
  `runs/aggregate-main.txt` (by set, by node size, all),
  `runs/aggregate-by-config.txt` (by workload), and
  `runs/aggregate-own-by-trace.txt`; `runs/aggregate-large2.txt` and
  `runs/results-large2.txt` for the seeds 11 to 30 (section 4.6).

**The counts.** Steps a transaction; bumps, between operations and inside
one, by reason; take-backs left (nodes taken back); key nodes made; top
nodes made; versions (a key node changed at a step: one time klong and its
entries); key klongs added; time and space splits, merges (the writer's
notes); the fill of the tree reached at the end of every 20th transaction
and at the end (klongs, live klongs, dead klongs and time klongs a node,
nodes, height); `pathfresh` (section 4.5). The bytes by 026-17's stand-ins
(section 5.5 there): a record 48 + 16 a changed key node, a key node 32 +
16 a klong, a value 40 + 8 a segment, a delete 28 + 8 a segment, a top
node 48 + 16 a skip pointer; B-new counts the key nodes a transaction
made, B-all every key node it changed, each whole at the transaction's
end. Java writes a key node when the take reaches it, so its stream is
between the two.


# 4. The numbers

All from `runs/aggregate-main.txt` (the sums over 288 traces: level 2,
reclaim, medium, large with seeds 1 to 10, and the study's own; 221,142
transactions, 1,792,106 operations, 647,332 of them deletes), its parts by
node size, and `runs/aggregate-by-config.txt` (by workload). Ratios are
against today on the same traces. Section 4.6 has the large set's seeds 11
to 30 and mode bp.

## 4.1 The checks

- No failure in any mode on any trace: every get after each transaction,
  1,067,010 GET and SCAN lines of Java's traces read at the end of their
  time, the full scans and the history.
- The contract held at every step of every mode: C1 to C5 (invariants,
  contents, frame, TREE, the top) at 221,142 steps of today, 340,223 of b,
  449,301 of bs, 314,186 of b0, 304,995 of d. So each step of step times
  goes from a tree that meets the contract to one that meets it, also the
  steps that end between a delete's pieces.
- The writer's own rules hold at every transaction's end in every mode.
  Between steps (b) they fail at 32,996 step ends with `FillOK` and 3,355
  with `RootsOK` (a merge or a collapse still to come), never with another
  rule.
- Mode split equals today, change for change, on all 221,142 transactions:
  the pieces are today's delete.

## 4.2 Take-backs left

- today: 50,015 nodes taken back (11,525 at node size 30);
- (a) net change: the same, it is today's writer (`dupkeys` 0 everywhere);
- d, deletes apart: 48,557 (97 % of today's);
- b0, bumps between operations: 30,387 (61 %; 400 at node size 30, from
  11,525): risk 2 is most of today's take-back at node size 8, little of
  it at 30, where most take-backs are between operations;
- b, bs, bp: 0.

## 4.3 Steps

- b: 1.54 steps a transaction (12.8 % of the transactions have more than
  one), most 44 (the bound is 16,384); 82,730 bumps between operations and
  36,351 inside one (between a delete's pieces). At node size 30: 1.36 a
  transaction, 7.3 % with more than one, most 40.
- bs: 2.03 a transaction, most 79; at node size 30: 1.74.
- b0: 1.42; d: 1.38 (two at most, by its rule).
- By workload at node size 30, b: 1.01 on the large set's random work
  (l-5000, l-long), 1.55 on the Pub-like index, 1.8 to 2.6 on 60 to 120
  random operations a transaction (d-30, m-d30), 13.6 on m-fifo (inserts at
  one end, deletes at the other), and on the sorted bulk loads 39 (500 keys
  a transaction), 8.6 (100) and 1.7 (10).

## 4.4 Bytes, nodes, fill

Mode b against today. "Index" leaves out the values and the delete nodes,
which no design changes.

- **Node size 30, random work** (l-5000, l-long, m-long, m-d30, d-30):
  B-new 1.000 to 1.017, B-all 1.000 to 1.019; the index 1.000 to 1.034.
  Nothing to speak of.
- **The Pub-like index** (pub-1, pub-10, pub-100): B-new 1.02 to 1.04,
  B-all 1.00 to 1.01; the index B-new 1.04 to 1.07; key nodes made 1.06 to
  1.10; live klongs a node 12.1 against 12.6, 11.8 against 12.2 (3 % less
  fill); the same height.
- **Sorted bulk loads**: 500 keys a transaction: B-new 1.41, the index
  B-new 2.24, key nodes made 2.18, live klongs a node at the end 12.6
  against 13.9 (10 % less fill), 12 % more nodes, the greatest height 4
  against 3; 100 a transaction: B-new 1.32, the index 1.85; 10 a
  transaction: 1.00. Why: today a node made in the transaction is split in
  place, so a sorted load makes one node a split; under step times the node
  made at a step cannot be split, so at the next step it is split as an
  older node, into two new ones. The load then costs exactly what today's
  writer pays for the same load in transactions of 10 keys (3,563 key
  nodes made in both, the same fill).
- **m-fifo** (100 operations a transaction at one end and the other):
  B-new 1.31, the index B-new 1.77, B-all 1.37: the same cause, at the
  inserting end.
- **m-big** (bulk transactions of random keys): B-new 1.07, the index 1.12.
- **Node size 30 in all** (48 traces, the bulk loads and m-fifo in them):
  B-new 1.078, B-all 1.033, the index 1.149 and 1.040; key nodes made
  1.136; live klongs a node 6.10 against 6.15; dead klongs a node 1.007.
- **Node sizes 8, 14 and 62** (BergDB's tests only, 026-08): B-new 1.24,
  1.03 and 1.01, the index 1.35, 1.05 and 1.02; the worst traces are the
  small nodes' sequential ones (d-fifo2 2.95, d-bulk and the small set's
  bulk 2.1 to 2.2 for the index).
- **All 288 traces**: B-new 1.121, B-all 1.058, the index 1.203 and 1.069;
  key nodes made 1.227; versions 1.178; key klongs 1.180; time splits
  1.093, space splits 1.189; the fill the same (3.41 live klongs a node
  against 3.43; dead klongs 1.004).
- **Top nodes**: 1.39 times today's in all, 1.25 at node size 30: a step
  that changes the root makes its own. Against 002's bound (2^30 − 1 over
  a database's life) this is a factor, not a new kind of cost.

**bs, the strict rule**, against b: about a third more steps and 2 to 4
points more bytes (all: B-new 1.143, B-all 1.100; node size 30: 1.103 and
1.070), for one book less (B7). Not worth it.

**d, deletes apart**: B-new 1.009, 1.4 steps a transaction, and 97 % of the
take-backs left.

## 4.5 Speed

The model does not time Java. What a commit costs is mostly the nodes it
makes and writes; a step boundary itself writes nothing (a record holds all
the steps of its transaction). By the bytes above: no change for random
work at node size 30, a few per cent for the Pub layer's index updates,
and up to 40 % more bytes (twice the index bytes) for a sorted bulk load
in large transactions. Reads see one node more on the path where the tree
is a level taller (the 500-key bulk load at 20,000 keys).

The check before a piece (section 6) costs a walk the writer makes anyway.
A cruder check, "a node of the step on the key's path", would bump more:
over the 288 traces, 70,630 pieces changed something with such a node on
their path but no breach, against 119,081 bumps (`pathfresh`, mode bp);
at node size 30, 19,305 against 30,493. So up to about 60 % more bumps,
before the effect of those bumps on the later tree: the check should look
at the nodes the piece will change, not at the path.

## 4.6 The step writer, and more seeds

- **bp equals b** on all 288 traces: every count of the RESULT lines is the
  same (`scripts/compare-bp.py`; only the names of the first breach found
  differ, where the pruned writer breaks the rule in another way before its
  bump). So the parts that `Study/ExecStep.lean` leaves out are never
  needed under the rule, and that file is a working step writer.
- **The large set's seeds 11 to 30** (120 traces, 340,000 transactions,
  1,100,217 operations), in today and b only, for time
  (`runs/aggregate-large2.txt`): no failure (the map, Java's 1,700,000
  reads, the contract at 370,941 steps); 0 take-backs left of today's
  17,287; 1.09 steps a transaction, most 11; B-new 1.030, B-all 1.015, the
  index 1.047 and 1.018. The same as seeds 1 to 10 (1.029, 1.014, 1.045
  and 1.017).


# 5. Simplicity

## 5.1 What goes, what stays, what is new

**Step times (b).** What the rule removes from the writer is checked two
ways: on every trace, mode b reaches none of the notes of these rules (0
take-backs, 0 splits in place, 0 top nodes changed in place, 0 merges of a
node made at the step: the `self` and `reached` counts); and mode bp, the
step writer with these parts deleted (`Study/ExecStep.lean`), gives the
same counts as b on every trace (section 4.6).

Gone from the writer:

- the take-back, all four kinds: of the nodes below the stop node of an
  upward unlink (`takeBack`, `canTakeBack`, `retarget`), of a root that
  root collapse removes (`takeBackRoot`), of a merged node the transaction
  made (`merge`'s take-back, `merge.made.*`);
- the splits in place of a node the transaction made: `spaceSplitInPlace`
  with its three forms (one is fault 12's fix, `split.space2.inplace`) and
  `timeSplitInPlace`: a put has six rules instead of ten;
- the top node changed in place (`newSuperRoot` with a top node of the
  transaction);
- the books of what a node replaces: `PutData.madeFor`, `replacedBy`,
  `setMadeFor`, the writer state's `taken` and `madeFor`; root collapse's
  early return at a root "made, but not by a split".

Gone from a writer proof (030-10, section 3.1's books; 030-16's link
books):

- B3 (a node replaced is a node of s), B4 (no klong names a node taken
  back), B9 (a node taken back was made by the transaction), B12 (a node
  made with a node it replaces is of its segment), B14 (the link of a made
  node: the klongs that name it are of the transaction, in one node);
- the delete's link books, `WcrLink`, `WmgFresh`, `WmgSplitLink`,
  `LinkLive`, `SNamed`: 030-16's F3 found each "needed only because a node
  not reached must not name a node taken back". They were the open piece
  where 030-16 stopped (its review's R3: their preservation through the
  whole writer, unfinished), and the reason for the parked 3,500 lines;
- the take-back's cases of the delete: the upward unlink's take-back, root
  collapse's two take-back forms (of four), the merge's two "made" forms;
  `WmgRestOk` (what is left of a merge) shrinks to two `unlink`s.

Gone already, by the contract, not by the design (030-10, section 5.2):
`l4`, R3, R4 and ValOld were all about the fill and two live klongs in an
inner root, which the contract does not have.

Stays:

- B1 (a node is new exactly if its first time is the step's: how a fresh
  node is told), B2, B5, B6, B8 (a node made is reached; no "kept" case),
  B10, B11, B13, B15 (`OldReach`), BalancedOK, J1 to J5;
- B7 and `unlink` (an older node that leaves the tree loses its version of
  the step): the rule speaks of fresh nodes only. The strict rule (bs)
  removes them too, at a cost (section 4);
- the half-finished states inside one piece: a split's cascade up the
  path, a merge's full parent (`MergeVirt`, the parent's virtual last
  version), LE-b's forms, the bitmap's four forms;
- the same recursion proved three times in the puts (030-10, 5.3), which
  no design here touches.

New:

- the delete in pieces, with what is left to do (`Fix`: the merges from a
  node, then root collapse) carried from piece to piece, each piece
  finding its node again from the space root by the key;
- the rule itself, a check before each piece (section 6);
- the time klong's layout, the end of T for readers, and the history of the
  contract stated over step times (its times are not 0, 1, 2, ... but
  T · 2^14 + k; the clauses do not care, `historyOk`'s numbering does);
- a top node for each step that changes the root.

**Net change (a)** changes nothing (section 1). **Deletes apart (d)**
keeps nearly every take-back (48,557 of today's 50,015 on all sets): it
removes only the put/delete interactions, and nearly all take-backs are
between deletes or inside one delete. It adds internal times and removes
no book. It is not simpler.

## 5.2 The size of the model writer

`scripts/sizes.py`, all lines and code lines (no comment, no blank line):

- today's writer, `Exec.lean`: 77 definitions, 1,066 lines, 831 code lines
  (809 without its transaction driver, `runOps`, `runOpsFrom`, `exec?`,
  `boundsOK`);
- the step writer: 49 of today's definitions as they are (397 lines, 266
  code), 19 of its own (`ExecStep.lean`, 420 lines, 392 code; 13 of them
  today's with parts taken out, 6 new: the put and the delete's pieces),
  and `Fix`: 828 lines, 665 code lines, without the step driver; with one
  of about 40 lines (the program's `act`), about 705;
- so about 13 % less code. The parts that shrink most: `handleFullWith`
  (100 code lines to 44), `merge` (69 to 56), `climb` (17 to 11),
  `deleteUpward` with `collapseRoot`, `mergeUp` and `afterDelete` (83) and
  the take-back's seven definitions (53), against the pieces (72).

The code is not where the gain is. A writer proof's size is in the states
it must describe between the writer's steps, and that is where the
take-back sat: in every book that speaks of the nodes taken back, and in
the link books over all nodes.

## 5.3 How much simpler a proof would be

My judgment, from 030-10's estimate for the deletes (20,000 to 35,000 lines
on today's writer, section 5.3 there) and what the rule removes:

- the bitmap with a full leaf (3,000 to 5,000): stays;
- the upward unlink with the take-back, and LE-b (6,000 to 10,000): the
  take-back goes, the climb and LE-b stay: 4,000 to 7,000;
- the merges with the parent's forms, the loop, root collapse (8,000 to
  14,000): the "made" forms, the take-back's two root forms and the link
  book's premises go; the loop becomes a sequence of pieces, each from a
  finished tree: 5,000 to 9,000;
- the delete's books through every rule (3,000 to 6,000): B3, B4, B12, B14
  go, B7 and B8 stay: 1,500 to 3,000;
- the puts, already proved on today's writer (22,500 lines): their four
  in-place forms would go; the rest carries over, restated per piece and
  per step.

So the deletes would take about 13,500 to 24,000 lines instead of 20,000 to
35,000: about a third less. More important than the lines: the part that
was open and hard, the link books over all nodes (030-16, F2 and F3), does
not exist, and every piece starts from a tree that meets the contract. A
proof per step, from finished tree to finished tree, is what 026-20
promised; it holds per piece, with the books that are local (one small
argument a primitive, 030-10, 5.1) and nothing that follows a node taken
back.

What it does not make simpler: the number of cases inside a piece (a
delete still has its bitmap's four forms, the climb, LE-b, the merge's
left and right, one and two nodes, the parent's five forms, root collapse's
two), and the recursion of the splits.


# 6. What Java would change (step times)

Rough sizes, by reading; nothing built.

- **The time klong** (`Klong.java`, 026-20's layout): 48 bits of the
  transaction's time and 14 of the step in the 62 bits that are a 56-bit
  time and 6 reserved bits today. `StoredKeyNode.parse` refuses a time
  klong with a reserved bit set, so this is a format change under 027-03's
  versioning rule (section 21): a stream of 2026.6 is refused by 2026.5. A
  few dozen lines; the risk is in the uses: 70 uses of a klong's time
  outside `Klong.java` (in `Dag`, `KeyNode`, `StoredKeyNode`,
  `NodeCollection`, `Residents`, `DbStarter`, `TransCheck` and testers).
- **The readers' time** (risk 3): one function maps a user's T to the end
  of T at every entry point (`Db`'s gets and scans at a time, `GetMany`,
  the Pub layer's history); 28 lines with raw time arithmetic (`tt + 1`,
  `time - 1`) in 15 files, most in testers; a `Time` type for the internal
  times, so that the two kinds cannot be mixed. Retention, the first
  available time and the startup position stay in transaction times
  (risk 5): records stay one per transaction, and a record holds all its
  steps, so a cut or a restart never falls inside a transaction.
- **The Dag**: the delete in pieces (the loops of `mergeAfterDelete` and
  `collapseRoot` become the driver's); the rule, a check before each
  piece; out go `takeBack`, `takeBackRoot`, `retarget`, `canTakeBack`,
  `timeSplitInPlace` (14 lines), `spaceSplitInPlace` (62),
  `PutData.madeFor` and `replacedBy`, and the listener's
  `keyNodeTakenBack` with what `Db`, `TransCheck` and the caches do for
  it (about 60 references in 9 files). Net, the Dag shrinks.
- **The check before a piece** is the new part with a real question. The
  model runs a piece, compares, and runs it again at a new step; Java
  cannot undo a piece cheaply. It must know beforehand whether the piece
  will change a node of the step: for a put, the leaf, and each node above
  that a split would reach (a full node's parent, up the path); for the
  core of a delete, the leaf and the stop node's path; for a merge, the
  node, its sibling and the parent; for a collapse, the root and the
  segment leaf above. A cruder check, "a node of the step on the key's
  path", bumps more: up to about 60 % more bumps (section 4.5).
- **Top nodes** (risk 4): a top node for each step that changes the root,
  so more top nodes and ordinals (002's bound of 2^30 − 1 over a
  database's life): section 4 counts them. TP24's proof (about 420 lines)
  and "at most one new root per transaction" are restated per step.
- **The trace format and its checkers** (027-02, `TransCheck`, `treecheck`,
  `contractcheck`, `bridgecheck`), the model's writer for the trace check
  (`Exec.lean` is replaced by the step writer), the C clone (012): each
  learns step times. The checkers' clauses are per transaction today and
  hold per step unchanged (this study ran them per step); the trace needs
  the step times in its NEW, ADD and KN lines.


# Log

2026-11-18. The study, by an agent of coord-1118, from 09:00:
the clone /Users/f/fl/bench/2026-11-18/st/clone at main f8865cb8, branch
`026-21-study`; the Lake caches of the night of 17 November; the traces
copied from the night's clones (s4c's level 2 sets, s4e's reclaim, medium
and large sets of 030-12, live=0). Read for it: 026-20, 026-17, 006-28,
030-10, 030-16, `Exec.lean`, `Dag.java`'s put and delete, the contract's
`Statement.lean`, `Check.lean`, `CheckShape.lean`, `Writer.lean`. The
program `steptimes` and the step writer built in `lean/study/` (a package
of its own, beside `lean/contract/`, whose sources it reads through a
link); `Exec.lean` and `lean/contract/` unchanged. Runs from 09:22 on four
cores: the level 2, reclaim, medium and own sets in modes today, split,
b0, b, bs and d; at 10:01 the queue reordered (the large set in all six
modes; bp on every set; the large set's seeds 11 to 30 in today, b0, b
and bp). At 10:46 the last part cut to today and b on the 120 traces of
seeds 11 to 30 (the other two modes would have added half an hour and
nothing new). All runs ended at 10:55 with no failure.

2026-11-24. Status set after the release (lead-1124).
