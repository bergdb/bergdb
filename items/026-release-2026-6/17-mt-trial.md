# 026-17. MT's trial: maintenance transactions in the model

Created 2026-11-16 by Frans Lundberg. Status: open (the trial running
since 2026-11-16, 11:17).

A trial, in the Lean model only, of MT (006-28, section 7.5): a user
transaction makes no merge, no upward delete and no root collapse; each
of those is one fix step in a transaction of its own, run right after the
user transaction. The trial runs MT beside today's writer on the model's
workloads and counts, before any design, proof or Java. Its result goes
to Frans's choice between MT, NW and neither, with 026-12's SF10.

Frans, 2026-11-16, 10:29, on 006-28's questions 7 to 9: "MT's trial
first. Yes, let me know what you mean by "trial" here and how we should
plan this. Do not start the work."; the provers wait for it ("Yes");
"Yes. Deletes can cost more. In general, trading performance for
simplicity can be good trade. But this is a judgement call, a tradeoff.
Let's keep measuring performance and and judge complexity so we can make
the right tradeoffs."

Frans, 10:47: "About the trial. So, you suggest model-first to
investigate this. I like this. It is a new way of working for me and I am
excited about it. Plan for the trial. Run a Fable High agent that makes a
plan for excuting the trial."

Frans, 11:17, the go: "Run the trial unattended now; if you run out of
usage, restart it at 22:01 tonight." With it the defaults of section 11
stand (node size 30 plus 8; Frans, 10:57, "Good." to the coordinator's
view of 30 for the counts and 8 as a stress check). The week's ceiling
until 22:00 is 99 % (Frans, 10:57); `usage-watch.sh` in
`/Users/f/fl/bench/026-17/` touches `STOP` there, and the coordinator
resumes the trial at 22:01.

**What the trial answers** (the coordinator's outline of 10:29, which the
plan makes exact):

1. Nothing is taken back: no fix step and no user transaction makes a
   node and leaves it out. MT's point; if it fails, MT is off.
2. Every get and scan is right at every transaction boundary, between a
   user transaction and its last fix step too.
3. After the last fix step, today's invariants hold (fill, live counts,
   heights); at best the tree is today's writer's, but for the ids.
4. The fixing ends: fix steps per deleted key, mean and most.
5. The cost: nodes and bytes written per delete against today; the
   tree's height between.
6. The two new rules (a merge of an empty node, of an only child) work
   as sketched.
7. The complexity: the lines of the model's definitions that MT adds and
   removes.

The plan follows.

# 1. The plan in short

- **What is built.** Two Lean files on a branch in a clone: `Mt.lean`,
  MT's rules as definitions beside today's writer (about 300 lines), and
  `MtTest.lean`, a program that runs MT and today's writer on the same
  transactions and checks and counts (about 700 lines). Today's
  `Exec.lean` and every proof stay as they are.
- **The main line is node size 30**, the only size a user gets (026-08).
  Every count that informs the choice (fix steps, nodes, bytes, the
  height between) is taken at 30, on trees of 100, 1,000 and, if the
  model's time allows, 6,000 keys. Node size 8 is a separate, optional
  step, a stress check of the pass or fail questions only (Frans and the
  coordinator, 10:55; question 1 of section 11).
- **Three results stop MT** (section 2.3): a node made and left out in
  one transaction; a wrong get or scan at a boundary; a fixing that does
  not end, or does not end in a tree that meets today's invariants.
  Everything else is a count for the choice.
- **Nine steps, T0 to T8** (section 7): about 12 agent-hours, 7 to 9
  hours on the clock with two agents at a time, and 2 to 5 core-hours of
  runs. My guess of the usage is 5 to 10 % of a week (section 9).
- **When.** Not before the week's reset, Monday 16 November, 22:00 (the
  week is at 92 %). It fits one unattended night, or an attended day. It
  starts on Frans's go.
- **Not measured by me:** the build time in a clone, the model's time a
  boundary at 1,000 and 6,000 keys, the usage. Step T0 measures the first
  two before the sizes are fixed (section 12).

Words used below:

- **A boundary** is the state of the tree after one transaction: after a
  user transaction, or after a fix step.
- **A tidy boundary** is one where the fixing has ended: after the last
  fix step of a user transaction, or after a user transaction that needs
  none. The other boundaries are **untidy**.
- **A group** is a user transaction with its fix steps.
- **Pending keys** at an untidy boundary: the group's deleted keys whose
  fixing has not ended.


# 2. The trial's questions, exact

The seven points of the outline, each as a pass or fail (Q1 to Q4, Q6)
or as counts (Q5, Q7). The checks K1 to K7 and the counts are defined in
section 5; the rules R1 to R5 in section 3.

## 2.1 Pass or fail

- **Q1. Nothing is taken back.** Pass: at every boundary of every run,
  K3 holds: every key node that the transaction made is reachable from
  the space root at the transaction's time, and the top node it made, if
  any, is the super root. And no fix step meets a node of its own
  transaction where today's rule would take one back (`Mt.merge` and the
  collapse throw `MT:` there, section 3.3). Fail: one case.
- **Q2. Every get and scan is right at every boundary.** Pass: K1 at
  every boundary, tidy or not, and K2 (the reads of earlier times, the
  untidy ones too, at each run's end). Fail: one difference from the
  reference map.
- **Q3. After the last fix step, today's invariants hold.** Pass: K4 at
  every tidy boundary: today's walk (`faultsAt`) finds no fault, and the
  other checks of a state that `treetest` makes hold. And K5 at every
  untidy boundary: the walk's faults are only the fill's three
  (`NonEmptyOK`, `RootsOK`, `FillOK`), and only at nodes on a pending
  key's path. Fail: a fault at a tidy boundary, or a fault of another
  kind or at another node at an untidy one.
- **Q4. The fixing ends.** Pass: no key reaches the driver's fuel
  (section 3.4), and K6: a fix step on a path that needs none changes
  nothing. The counts: fix steps for each deleted key, the mean, the
  most, and by the tree's height.
- **Q6. The two new rules work as sketched.** Pass: the merge of an empty
  leaf (R3) and the only child passed over (R4) are each reached at least
  100 times at node size 30, and Q1 to Q4 pass on the runs that reach
  them; `LeftmostOK` holds at every boundary with no exception, so LE-b
  is not needed; no inner node is ever empty. Fail: a rule is needed that
  section 3 does not have. If a rule is not reached 100 times, the result
  says "not reached", which is neither.

## 2.2 Counts, for the choice

- **Q3, second half: is the tree today's writer's?** For each group,
  today's writer runs the same user transaction from the same tree, and
  the two trees are compared by shape (section 5.4). A count: groups
  equal, groups different, apart for groups of one delete and of
  several. A difference is not a failure: MT's fix steps use more klongs
  in a parent, so a parent can be full, and be split, at another moment.
- **Q5. The cost**, at node size 30 only: nodes made, nodes changed,
  klongs and bytes written for each group against today's writer on the
  same transaction (section 5.5); the height at the untidy boundaries
  against today's (5.6); the number of untidy boundaries.
- **Q7. The complexity** (section 5.7): lines of definitions MT adds;
  today's definitions that MT's writer never calls, and their lines; the
  proof lines that name those; the size of the invariant between.

## 2.3 What stops MT, and what only costs

**Stops MT** (the trial ends with "MT off as specified", and says what
failed, with the smallest run that shows it):

- S1. Q1 fails: a node made and left out. MT's point is gone.
- S2. Q2 fails and no change within R1 to R5 mends it. A reader that
  must change for MT is a finding for Frans, not a thing the trial does.
- S3. Q3's first half or Q4 fails: the fixing does not end, or ends in a
  tree with a fault, and no change within R1 to R5 mends it.

**Only costs** (counted, reported, no stop):

- more fix steps than the path's length; a second pass over the keys
  (K7); a merge of two empty leaves that makes an empty node;
- more nodes, klongs and bytes than today, whatever the factor;
- a tree of another shape than today's writer's;
- a height one above today's at untidy boundaries, or a run that leaves
  the level bounds there;
- more definitions added than freed.

**A slip in the trial's own code is neither.** A failure is first made
small: the program prints the transactions, and the agent cuts them down
by hand to the shortest run that fails. Then:

- if the cause is a slip in `Mt.lean` or `MtTest.lean` against section 3
  or 5: mend it, run again, note it in the log;
- if it needs a rule that R1 to R5 do not have: the agent may add at
  most two such rules, each written into the result as "rule added",
  with the case that asked for it; a third ends the trial with S2 or S3.


# 3. MT's rules as definitions

All in one new file, `lean/SIS/Tree/Mt.lean`, namespace `SIS.Tree.Mt`,
importing `SIS.Tree.Exec`. Line numbers of `Exec.lean` are those of
commit 13beb100.

## 3.1 A separate definition, not a parameter

I recommend separate definitions beside today's writer, not a parameter
of it (006-28, section 7.7, said a parameter).

- A parameter changes `deleteUpward`, `merge` and `putKv`, which the
  tree's 167,000 lines of proofs unfold. They would break on the branch.
  A new file breaks nothing: `Exec.lean` is the same bytes as on main.
- The trial runs MT and today's writer in one program. Both must exist
  at once.
- What MT adds is one file's lines. What it frees is what its entry
  points never call. Both are clean counts (section 5.7).
- The price: three small wrappers and `merge` are copied with changes,
  about 90 lines. The counts of 5.7 take the copies out.

MT is defined for the merges on (`Params.merges`, node size 8 or more,
record format 7's thresholds with theta). The trial runs nothing else.

## 3.2 R1: the user transaction

A user transaction is today's, but its delete is a bitmap and no more.

- `Mt.deleteLeaf leaf depth cv : M Bool`. From `deleteUpward` (981), its
  first lines only: if the key has no live klong, a noop; else
  `appendDeleteKlong leaf depth cv` (437), unchanged, with the full
  leaf's split and its cascade inside it. No `afterDelete`, no `climb`,
  no upward loop, no `emptyKeyNext`, no `collapseRoot`. The leaf may be
  left under the fill or empty; a full leaf whose last version is empty
  becomes a node with a lone time klong, by `handleFullWith` as it is.
- `Mt.setValue`, `Mt.putSegs`, `Mt.putKv`: copies of 1038 to 1093 that
  call `Mt.deleteLeaf`. A put is unchanged.
- `Mt.runUser p base ops i view : Except String (List Bool × W)`: as
  `runOps` and `runOpsFrom` (1154 to 1170) with `Mt.putKv`. In place of
  `boundsOK`: a node made outside G and H is an error at once, since
  nothing is taken back.
- The changes are `changesOf i w` (1128), unchanged.

## 3.3 R2 to R4: the fix step

**R2: one fix a step, at the lowest node of the key's path that needs
one and can get it.** `Mt.fixStep key : M Bool` is run from an empty
writer's state, at a time of its own. It returns false, and changes
nothing, if the key's path needs no fix.
`Mt.runFix p base key i view : Except String (Bool × W)` runs it.

**The path.** `Mt.path key : M Unit` builds the key access path as far
as the key goes: from the space root (`findRoot`), in each segment's
tree down to the segment leaf (`descendLte`, 570), then to the next
segment's root if the leaf has a live klong of the segment
(`searchEq`); it ends at the last segment's leaf, or at the leaf where
the segment is not found. It is `descendToSegmentRoot` (585) without
the error for a segment that is not there.

**The target.** `Mt.target : M Fix` walks the path from its lowest node
up and returns the first node that needs a fix and can get it. For the
node x at depth d, with q the node at depth d − 1 and cnt its live
klongs (`KNode.cnt`):

- **x is a segment root** (d = 0, or q is a segment leaf, as `mergeUp`
  tests it, 934):
  - x is a leaf, empty, and not the space root: **unlink the tree**;
  - x is an inner node with one live klong: **collapse**;
  - x is an inner node with none: the error `MT: an empty inner node`;
  - else go up. An empty space root that is a leaf stays, as today.
- **x is not a root** and cnt is below m (`Params.mergeBelow`):
  - q has another live key klong: **merge** x;
  - q has none (x is an only child): go up. R4.
- else go up. Above depth 0: no fix.

**The three fixes**, one a step:

- **Merge**, `Mt.merge x d`. From `merge` (860 to 931), with
  `mergeIdx`, `sibling`, `mergeKlongs`, `newKlongs` and `mergeParent`
  (719 to 857) called unchanged. Three changes:
  - R3, an empty node: for leaves, the error "has no live klong" goes;
    the general rule makes the new node from the other node's klongs,
    under the left one's klong. For inner nodes the error stays.
  - no take-back: the lines for a node of the transaction (`lMade`,
    `rMade`, `retarget`, `takenBack`, `replacedBy`, `setMadeFor`) go. A
    node of the step's own transaction there is the error `MT: a fix
    step merges a node of its own transaction`. That error is S1.
  - the two merged nodes need no `unlink`: they have no klong of the
    step's time.
- **Unlink the tree** (the upward delete, one level):
  `appendDeleteKlong q (d − 1) (klongAt d)`, unchanged, with the split's
  cascade if q is full. If that empties q, the next step sees it: q is
  then the lowest node of the path.
- **Collapse** (root collapse, once): `collapseRoot`'s body (648)
  without its loop and without `takeBackRoot`: the one live klong must
  be the empty key's, else today's `Bug:`; then `replaceRoot x d only`
  (627), unchanged. A root of the step's own transaction is the error
  `MT: a fix step collapses a root of its own transaction` (S1).

**R4, the only child.** A node under the fill with no sibling is passed
over; the node above it has one live klong, so it is under the fill
itself (m is 2 or more) or a root that collapses. So the walk always
finds a fix above an only child. The trial counts the passes.

**What a fix step never calls**, by this design: `takeBack`,
`canTakeBack`, `takeBackRoot`, `retarget`, `takenBack`, `replacedBy`,
`emptyKeyNext`, `climb`, `mergeUp`, `afterDelete`, `deleteUpward`. 5.7
checks it by a walk of the dependencies.

## 3.4 R5: the driver

`Mt.fixAll`, generic in the state (an apply and a view function), so
that the test program runs it on its own table of nodes:

- **When:** right after a user transaction's changes are applied.
- **The keys:** the user transaction's deletes that deleted (not the
  noops), in key order.
- **For each key:** `runFix` at the next time, from the state so far.
  False: no transaction is made, no time is used, the next key. True:
  its changes are applied as a transaction of its own, the time goes up
  by one, and the same key is tried again.
- **The fuel:** at most `(p.M + 2) * p.fuel` fix steps a key. A merge
  into one node takes a live klong from the parent, so a level gives at
  most M merges, and a path has at most `p.fuel` levels. A key that
  reaches the fuel is the error `MT: the fixing does not end` (S3).
- **When it stops:** after the last key. The claim to test: then no
  node of the tree needs a fix (K4), and no key's path needs one again
  (K7).
- **Ids:** each transaction's first id is the one after the last id
  used so far, so a group of any size has room.

## 3.5 Small cases in the file

Five to ten `#guard`s in `Mt.lean` on trees of a few keys at node size
8: a leaf left under the fill and merged by one step; a one-node
segment tree emptied and unlinked; a root with one child collapsed; an
empty leaf merged; an only child passed over; a fix step on a tidy path
that returns false. They fix the meaning before the runs.


# 4. Where the work happens

- **The clone:** `/Users/f/fl/bench/026-17/bergdb`, made by
  `git clone /Users/f/fl/repos/bergdb` at main's commit of the start,
  which the trial's log names. The branch: `026-17-mt-trial`.
- **The build's start:** `lean/.lake` (412 MB) copied from the main tree
  into the clone with `cp -Rc` (a copy-on-write copy), when `ps` shows no
  `lake` or `lean` at work there. If Lake rebuilds anyway, it rebuilds
  the 38 modules that `treetest` needs (12,295 lines), not the proofs.
- **The files the branch adds:**
  - `lean/SIS/Tree/Mt.lean`: MT's definitions (section 3);
  - `lean/MtTest.lean`: the test program (section 5);
  - `lean/MtDeps.lean`: the walk of the dependencies (section 5.7);
  - in `lean/lakefile.toml`, one stanza: the program `mttest` with root
    `MtTest`. It is not a default target, so `lake build` is as on main.
- **Nothing else changes on the branch.** Checked at each step's end
  with `git diff --name-status main -- lean java`: three `A` lines and
  `M lean/lakefile.toml`.
- **The branch builds:** `lake build SIS.Tree.Mt mttest` ends with
  status 0 in the clone. That is the only gate. There is no gate on
  main, since nothing of `java/` or `lean/` reaches main.
- **Scratch and raw output:** `/Users/f/fl/bench/026-17/`: `runs/` for
  the programs' output, `state.md` for where the work stands, `STOP` to
  end it (section 7.3).
- **What reaches main**, by the coordinator's commit, items only:
  - 026-17's text: a "Result" section, short, the result first;
  - the evidence directory `items/026-release-2026-6/17-mt-trial/`:
    `report.md` (the counts in full), the three Lean files as
    `.lean.txt` with the lakefile's stanza, the runs' summary lines
    (`runs/*.txt`, not the raw output), the scripts of 5.7.
- **The branch is kept:** at the end the coordinator fetches it into the
  main repository as a branch of the same name
  (`git fetch /Users/f/fl/bench/026-17/bergdb 026-17-mt-trial:026-17-mt-trial`).
  That touches no index and no work tree. It is not merged. 026-17
  records the branch and its last commit (items/readme.md, "Items and
  the current state").
- **The machine.** Before a build or a run that loads the cores for more
  than a minute: one slot of `/Users/f/fl/bench/2026-11-11/slot.sh`
  (`take`, then `release`), which waits while a timing run holds the
  machine. The trial makes no timed measurement; every figure is a
  count.


# 5. The checks and the counts

## 5.1 The program

`lake exe mttest FAMILY ...` (`lean/MtTest.lean`), made from
`TreeTest.lean`, which it cannot import (two `main`s): the key sets, the
generator, `testReqs` and the form of `checkSt` are copied, and the file
says from where. What differs:

- **The nodes are in a hash table** (`Std.HashMap NodeId (Node BVal)`,
  as `Check/Tree.lean`'s `PMap`), and the writers and the readers get it
  as a view. `treetest` keeps a list, which is too slow above some
  hundred keys.
- **A group at a time.** From the tree P at time t, for a user
  transaction U:
  - today's writer: `runCounted` on U at time t + 1, giving the tree A;
  - MT: `Mt.runUser` on U at t + 1, then `Mt.fixAll`, giving the
    boundaries B1 (after U) to Bk (tidy), at times t + 1 to t + k;
  - the checks at every Bj, the comparison of A with Bk, the counts;
  - the run goes on from Bk. A is dropped. So every group compares the
    two writers from the same tree.
- **The reference** is the program's own map from keys to values,
  changed by each user transaction and by nothing else. At a fix step's
  time it is its group's. On trees of up to 200 keys it is also checked
  against `refGet` and `refScan` (`Props.lean`), with each fix step as a
  transaction without operations.

## 5.2 The checks at a boundary

- **K1, the map** (Q2), at every boundary, at its own time:
  - up to 200 keys: `get` of every key of the run's key set, and every
    scan of `testReqs` with limits 100 and 2, as `treetest` in full;
  - above 200 keys: one forward and one backward `scan` of everything,
    compared whole with the reference; `get` of the group's keys, of
    their neighbours in key order and of 200 keys drawn by the seed; 20
    of `testReqs`' scans drawn by the seed; every key's `get` at every
    50th boundary.
- **K2, earlier times** (Q2), at a run's end: for every 10th time, tidy
  or not, K1's gets and the forward scan at that time against the
  reference of that time. The untidy states stay in the history; this
  reads them after later transactions.
- **K3, nothing left out** (Q1), for every transaction: every key node
  in its `changesOf.new` is in the list of key nodes reachable at its
  time (`nodesAt` from the space root); its `W.taken` is empty; a top
  node it made is the root's live child (`topAt`). No error that starts
  with `MT:`.
- **K4, tidy** (Q3), at every tidy boundary: `faultsAt` (`Inv.lean`)
  gives no fault. That one walk holds the checks the outline names: the
  fill (`FillOK`), the live counts (`NonEmptyOK`, `RootsOK`, `FillOK`,
  what `live-counts-check` tests), the heights and the kinds
  (`KindsOK`: a child is one height below, in its segment), the dead
  klongs (`DeadOK`, theta), and with them the sizes, the pointers, the
  empty key first and the ranges. Beside it, from `checkSt`:
  `PointersOK` over every node, the noop delete, the count of key nodes
  against the live keys and BU1's count, and every segment tree
  balanced (`balanced`, from `segfit-check`). A6 and the skip pointers'
  search need the list form: at every boundary up to 200 keys, at every
  50th above.
- **K5, untidy** (Q3), at every untidy boundary: a copy of the walk
  that returns each fault with its name and its node. Pass: every fault
  is `NonEmptyOK`, `RootsOK` or `FillOK`, and its node is on the path
  (`Mt.path`, at that boundary) of a pending key. `SizeOK`, `klongsWf`,
  `PointersOK`, `LeftmostOK`, `DeadOK`, `RangeOK`, `KindsOK` and
  `balanced` have no exception.
- **K6, a fix step that is not needed does nothing** (Q4): every call
  of `Mt.runFix` that returns false has made no node and added no
  entry. The driver makes one such call a key.
- **K7, one pass is enough** (a count): after the driver's last key,
  the program calls `Mt.runFix` once more for each of the group's
  deleted keys. Pass: all return false. If one returns true, the
  driver's order was not enough: counted as "second pass", the step is
  applied, and the program goes round again, with the driver's fuel.
  More than 0 changes the driver's rule; it does not stop MT.
- **Errors.** A `Bug:` or `corrupt:` from either writer fails the run,
  with its transactions printed. `bounds:` is counted apart, as
  `treetest` does.

The `*Run.lean` files of the tree (`HeightsRun`, `DeadRun`, `KindsRun`
and the like) are proofs over runs, not checks that run. What runs is
the walk, `checkSt` and the check scripts of 024-12; the trial uses
those.

## 5.3 That the checks bite

- **The program on today's writer alone** (`mttest selftest`): today's
  writer in MT's place, with no fix steps, so that every boundary is
  tidy. Pass: K1 to K4 with no failure and every group "equal" in 5.4.
  It is run before MT is put in.
- **A broken MT** (`mttest mutant`): the driver stops one fix step
  early. Pass: K4 reports faults. So a green K4 means something.
- **What was reached**, printed for every run, as `treetest`'s
  `reached`: how often each rule ran. The fix step notes its own names:
  `fix.merge.one`, `fix.merge.two`, `fix.merge.inner`,
  `fix.merge.empty`, `fix.merge.bothempty`, `fix.unlink`,
  `fix.collapse.space`, `fix.collapse.segment`, `fix.pass.onlychild`;
  with today's notes for a full parent (`merge.parent.full`,
  `merge.parent.dead`), a full leaf at the delete (`bitmap.full`) and a
  lone time klong. A rule not reached at node size 30 is said so in the
  result.

## 5.4 The tree against today's writer's

- **The shape** of a tree at a time: from the space root, each key node
  as leaf or inner with its live klongs in order (`KNode.liveAt`), each
  as the compare value and the shape below, a value as its hash. No
  ids, no times, no dead klongs.
- **Equal** if A's shape at t + 1 is Bk's at t + k. Counted for groups
  with one delete, with several, and with none (always equal: a check
  of the program).
- **When different:** the two trees' key nodes, heights and live klongs
  a node are counted, and the first three cases of a family are printed
  for the agent to read and explain in the result.

## 5.5 The cost of a group, at node size 30

For a transaction X at time t, from its changes and the tree after it:

- **made**: the key nodes in `changesOf.new`;
- **changed**: the key nodes with an entry of time t, the made ones
  included;
- **klongs**: the entries of time t added to key nodes;
- **tops**: 1 if X made a top node.

The bytes, from 027-03's layouts:

- a record: 48 (section 8.1), and 16 for each changed key node, as its
  got-dirty pair. The pair's rule is not yet written in 027-03 (8.4);
  this is a stand-in;
- a key node: 32 + 16 n, n its klongs after X (section 11.1);
- a top node: 48 + 16 h, h its skip pointers (section 10);
- a delete node: 28 + 8 k, k the key's segments (section 12);
- a value node: 28 + 8 + 4 + 8 k, with 8 bytes for the value, a
  stand-in: the model holds a value's hash only;
- a fix step's own node: 32 + 8 k, a stand-in for "the key and the user
  transaction's position". Its format is out of scope.

Two sums, since Java writes a key node when the take reaches it, not
with its record:

- **B-new** = the records, the value, delete and fix nodes, the top
  nodes, and the made key nodes: what must be written at least once;
- **B-all** = the same with every changed key node, whole: as if each
  transaction's nodes were written with it.

MT's cost of a group is the sum over U and its fix steps. Today's is
that of U by today's writer from the same tree. Reported for each
family:

- the sums of made, changed, klongs, tops, B-new and B-all, MT against
  today, and their ratios; the same without the value nodes (the index
  alone);
- for each deleted key: the extra made nodes and the extra bytes, the
  mean and the most;
- today's nodes taken back a merge (`merge.takeback` against the
  merges), to set beside 024-22, section 2.9;
- for family C, the mixed one, the ratio of the whole run: the user's
  number.

## 5.6 Fix steps, the height between, the untidy states

- **Fix steps** for each deleted key: 0, 1, 2 and so on; the mean, the
  most, the spread; by the height of the key's segment tree before the
  delete, and against the number of nodes on its path (P4's "about the
  path's length"); by kind (5.3's names). For a group: the sum and the
  most.
- **The height** of a tree at a time: the greatest height of a key node
  reached (`Params.heightOf`). For a group: before; today's after;
  MT's greatest over B1 to Bk; MT's after. Counted: groups where MT's
  greatest is above both the first two, and by how much. The runs have
  room in H (section 6), so a higher tree is seen and not refused; the
  result names the H that MT needed and the H today's writer needed.
- **The untidy states:** boundaries untidy of all; the most key nodes
  with a fill fault at one boundary; boundaries with an index node that
  has no live key below it (reclaim's premise, 006-28, section 7.4: a
  count for the design note, no verdict here).
- **Top nodes:** those made by fix steps (a collapse or a split at the
  space root), against today's. Each uses a top node ordinal (002).

## 5.7 The complexity

- **C1, added.** The lines of `Mt.lean`, all and without comments and
  blank lines, by part: R1's wrappers, the path and the target, the
  merge, the driver.
- **C2, freed.** `lean/MtDeps.lean`, run with `lake env lean`: from
  Lean's own environment, the constants of `SIS.Tree` that `exec?` uses,
  through every call, and those that `Mt.runUser`, `Mt.runFix` and
  `Mt.fixAll` use. Today's that MT's do not use are freed. Each with
  its lines in `Exec.lean` or `Node.lean`. Also the fields of `W` that
  no definition of MT's set reads. I expect `deleteUpward`, `climb`,
  `afterDelete`, `mergeUp`, `collapseRoot`, `takeBackRoot`, `takeBack`,
  `canTakeBack`, `retarget`, `takenBack`, `replacedBy`, `emptyKeyNext`,
  `merge`, `boundsOK`, and of `W`: `taken`, `madeFor`, `outside`. And
  that `toPrev` and `unlink` stay, by the split and by `replaceRoot`;
  006-28, section 7.5, lists `toPrev` among what goes. The walk
  decides.
- **C3, net.** `Exec.lean`'s lines if MT's writer replaced today's:
  today's 1,175, less C2, plus C1 without the copied wrappers.
- **C4, the proofs that name what is freed.** 006-28's `mentions.py`
  with C2's names as the pattern, over `lean/SIS/Tree`: the
  declarations whose text names one, and their lines. By names, with no
  build: an upper bound, as 006-28, section 2, says of its own.
- **C5, the invariant between.** The lines of K5's exception, as it is
  written in the program.

No pass or fail. If C1 is above C2, the result says so first.


# 6. The workloads

## 6.1 Node size 30, the main line

The parameters: `({M := 30, G := 2, H := 6} : Params).withMerges.withTheta`,
which is m = 8, h = 17, c = 17, theta = 7: record format 7's, Java's.
G = 2 lets keys have up to three segments. H = 6 is room above what the
trees need.

**How deep the model gets at 30.** This decides whether 30 alone is
enough (question 1).

- By my arithmetic from the thresholds, not run: a leaf holds 8 to 29
  live klongs and a split's halves 9 or more, so a segment tree is of
  height 1 from about 30 keys, of height 2 from about 200 to 500 keys,
  and of height 3 from about 1,500 to 5,000 keys.
- What was run before: 024-22's random run at 30 had 10 seeds of 300
  transactions on 100 keys, half deletes: 3,000 states and 87 merges.
  At 100 keys the tree is of height 1, so no inner node was merged and
  no root collapsed at height. The earlier checks ran at node sizes 8
  and 10 for that reason.
- So the main line needs 1,000 keys for height 2 (merges of inner
  nodes, a parent's cascade, a collapse from height 2) and about 6,000
  for height 3. With the nodes in a hash table that is in reach, by my
  estimate; T0 measures it.

**The families.** Keys from `treetest`'s builders, made longer:
one-segment keys, with every fourth of two segments, unless said.

- **A, random-100:** 10 seeds, 300 transactions of up to 16 operations,
  100 keys, half deletes. 024-22's run, for comparison.
- **B, random-1000:** 5 seeds, 400 transactions of up to 40 operations,
  1,000 keys, half deletes.
- **C, mixed-1000:** 5 seeds, 400 transactions of up to 20 operations
  on a pool of 2,000 keys, from a tree of 1,000: 30 % deletes, the rest
  puts, half of them of keys that have a value. The user's mixed case.
- **D, shrink-1000:** 1,000 keys put, 50 a transaction; then all
  deleted, in four ways: one a transaction in key order; one a
  transaction in random order; 10 a transaction in random order; 100 a
  transaction in key order. 3 seeds for the random ones. To the empty
  tree: every collapse on the way down.
- **E, mass-1000:** from 1,000 keys, built in three ways (one
  transaction; 50 a transaction; one a transaction): one transaction
  that deletes the middle half; one that deletes every second key; one
  that deletes all. The longest fixing in a row; leaves emptied side by
  side (the merge of two empty leaves).
- **F, dead-1000:** every key put twice, so the nodes are full of dead
  klongs; then D's two random ways. A delete's time split before its
  merge: 024-22, section 2.9's costliest case.
- **G, segments:** 30 first segments with 20 keys each (one-node
  segment trees that empty: the unlink); 3 first segments with 200 keys
  each; 100 keys of three segments. All deleted in random order, one
  and 10 a transaction, then put again. 3 seeds.
- **H, deep-6000:** 6,000 one-segment keys put, 200 a transaction; all
  deleted in random order, 20 a transaction. 2 seeds. For height 3.

Seeds are 1, 2, 3 and so on, each run's generator started at seed ×
7919, as `treetest`.

**The size and the time.** About 20,000 groups and, by my guess, 60,000
to 100,000 boundaries. What is known: the night of 15 November ran
`treetest`'s whole set, about 715,000 states on trees of mostly 14 keys
or fewer, in 3,145 s on one core: 4.4 ms a state. What is not known:
the time of a boundary at 1,000 keys. My guess is 20 to 100 ms, so 1 to
3 core-hours for the main line, in four processes under an hour on the
clock.

**The rule if it is more.** T0 measures a boundary at 1,000 and at
6,000 keys with `selftest`. If the main line would pass 4 core-hours:
first 3 seeds in A to C; then H at 3,000 keys; then 200 transactions in
B and C. If H does not reach height 3 in its time, the result says
which height was reached, and question 1's answer leans to "30 plus 8".
What was cut is written in the result.

## 6.2 Node size 8, the optional stress check

A step of its own (T6), which Frans may drop. Only Q1 to Q4 and Q6 are
read from it; no cost and no count for the choice. The parameters:
`({M := 8, G := 2, H := 8} : Params).withMerges.withTheta`: m = 2,
h = 4, c = 4, theta = 2. Trees of height 3 and 4 from 12 to 200 keys,
and every transaction on a few keys.

- `treetest`'s sets with merges and theta, as groups: `subsets 8 12 2
  0` (every set of deletes on 12 keys, 4,095 transactions), `subsets 8
  9 3 0 puts` (19,682), `subsets 8 210 0 1 puts`, `exhaustive 8 3 12 2`
  and `8 3 12 4`, `exhaustive 8 2 12 2 pairs`, `random 8 20 200 40` and
  `random 8 10 200 124` with half deletes.
- D's four ways on 200 keys.

About 160,000 groups. `treetest`'s header gives its set with merges
about 15 minutes of the whole set's 52; with MT's boundaries and
today's side run my guess is 1 to 2 core-hours.

Node size 14, which the coordinator's brief named, is dropped (10:55).

## 6.3 What the workloads do not have

No touch (`Tx.touch`, reclaim's steps), no restart, no trace of Java's.
A transaction has one operation a key, in key order, as `normalize`
makes it, and noop deletes are left out, as Java's record leaves them.


# 7. The steps

Agents by 013-02, section 9: Opus 5.5 (`model: "opus"`), high; xhigh for
the two steps where the rules' exact form is the work (T1, T4), when
the usage level is plenty or normal, else high. Frans may ask
otherwise. Two agents never write the same Lean file. Each brief names
026-17, the clone, the files the agent may write, its stop time and the
length of its report. An agent that waits for a run waits on a marker
file, not on `pgrep`.

## 7.1 The steps in order

- **T0. The clone and the measure.** The coordinator itself, or agent
  B's first half hour. 0 Lean lines, 0.5 h.
  - Does: section 4's clone, branch and `.lake`; `lake build treetest`
    in the clone; one run of `treetest random 30 3 100 100 merge 16 50
    theta` for the time of a state.
  - Delivers: `state.md` with main's commit, the build's time, the time
    a state.
  - Checked: `treetest` prints `TREETEST OK`.
- **T1. MT's definitions.** Agent A, xhigh. About 300 lines of Lean,
  2 to 3 h.
  - Does: `Mt.lean` by section 3, with 3.5's `#guard`s.
  - Delivers: the file, committed on the branch; a list of every place
    where it left section 3, with the reason.
  - Checked: `lake build SIS.Tree.Mt` with status 0; the guards hold;
    T3's review.
- **T2. The program.** Agent B, high. About 700 lines, 3 to 4 h. Beside
  T1, from the three signatures of section 3 (`Mt.runUser`, `Mt.runFix`,
  `Mt.fixAll`), which T1 fixes in its first minutes as a file that
  builds with `sorry`-free stubs returning an error.
  - Does: `MtTest.lean` by section 5; the families of section 6;
    `selftest` and `mutant`; the lakefile's stanza.
  - Delivers: `mttest selftest` green on family A and on `subsets 8 12
    2 0`; the measure of a boundary at 1,000 and 6,000 keys; the sizes
    after section 6.1's rule.
  - Checked: `lake build mttest` with status 0; 5.3's first two points.
- **T3. A review of `Mt.lean`.** Agent R, a fresh one, high. 0.5 to
  1 h, when T1 is done, beside T2's end.
  - Gets: section 3 of this plan, `Mt.lean`, `Exec.lean`. Not agent A's
    reasoning.
  - Asked: where does the file differ from today's rules beyond what
    section 3 says; is there a path where a node of the step's own
    transaction is left out; is the target's order right.
  - Delivers: findings. Agent A answers each in the file or in the
    log: mended, or kept with the reason.
- **T4. The first runs.** Agent A, xhigh. 1 to 3 h.
  - Does: family A and `subsets 8 12 2 0` with MT; reads every failure;
    section 2.3's rule for slips and for added rules; `mutant`.
  - Delivers: Q1 to Q4 green on the two families, or a stop by S1 to
    S3 with the smallest run.
  - If node size 8 is dropped: family A, and D and E on 200 keys at
    node size 30, here and in T2's `selftest`.
  - Checked: the program's summary lines; the reach of each fix rule
    above 0.
- **T5. The main line's runs, node size 30.** Agent B starts them and
  waits. 1 to 3 core-hours, up to four processes, each with a slot;
  half an hour of the agent's time.
  - Delivers: `runs/30-*.txt`, one summary a family: the checks, what
    was reached, the counts of 5.4 to 5.6.
  - Checked: every process ended with its last line `MTTEST OK` or
    `MTTEST FAILED`; none was killed.
- **T6. Node size 8, optional.** Agent B, beside T5 in other slots.
  1 to 2 core-hours; half an hour to an hour of the agent's time.
  - Delivers: `runs/8-*.txt`: Q1 to Q4 and Q6 only.
- **T7. The complexity.** Agent A, high, beside T5 and T6. About 80
  lines of Lean and script, 1 to 1.5 h.
  - Does: `MtDeps.lean` and 5.7's C1 to C5.
  - Checked: C2's list holds no definition that `Mt.lean` names (a
    `grep`); the lines of C1 by `wc`.
- **T8. The result.** Agent A, high. 1 to 1.5 h.
  - Does: 026-17's "Result" section, at most 60 lines, the verdict on
    Q1 to Q7 first; `report.md` and the files of section 4 in the
    evidence directory; what was cut, what was not reached, every rule
    added; in plain words what the counts mean for a database of 10
    million keys, and what they cannot say.
  - Checked by the coordinator: five numbers of the result against
    `runs/*.txt`; `git diff --name-status` of section 4; then it
    fetches the branch, commits items only, and adds the entry to
    `news.md` (`tools/news.sh`).

## 7.2 What runs at the same time

- T1 and T2, from the start. T3 when T1 is done.
- T4 needs T1, T2 and T3's findings answered.
- T5, T6 and T7 beside each other, after T4.
- T8 last.

On the clock with two agents: T1 and T2 3 to 4 h; T3 and T4 2 to 3 h;
T5 to T7 1.5 to 2 h; T8 1 to 1.5 h. 7 to 9 hours, 10 with a hard
failure in T4.

## 7.3 The stop rules

- **S1 to S3** (section 2.3) end the trial with "MT off as specified".
  T7 and T8 are still made: the result says what failed, and the
  complexity counts hold for the choice between NW and neither.
- **A third rule added** ends it the same way.
- **`selftest` is not green** after 2 hours of T2's mending: stop. The
  program is not to be trusted, and no MT result is reported.
- **`Mt.lean` does not build** 4 hours after T1's start: stop, with the
  state.
- **The clock:** 12 hours after T0. What is not run is listed.
- **The usage:** the coordinator notes the week's figure at T0 and at
  every check-in (`usage.log`). 12 points above T0's: stop after the
  step in hand.
- **The file `/Users/f/fl/bench/026-17/STOP`:** each agent looks for it
  between its steps and before each run; if it is there, it writes
  where it stands into `state.md` and ends.
- **Main is never touched** by an agent of the trial: not its work
  tree, not its index. An agent that finds it must is to stop and ask
  the coordinator.

Every stop ends with `state.md` up to date and a `news.md` entry of
`needs a look`.


# 8. Out of scope, and what follows

**Not in the trial:**

- **Proofs.** No theorem is stated or proved. `l4` and `htbL` wait
  (Frans, 10:29).
- **Restarts and P2's rule** (010-01, P2): what a start does after a
  crash between a user transaction and its last fix step, and T2 for
  it. The model's driver runs to its end, always.
- **Reclaim's argument** at the untidy times (006-28, section 7.4), the
  touch, the take, eviction, `maintain()` (027-13; 026-03). The trial
  gives one count for it (5.6).
- **The record's byte format**: the fix step's kind of record, the
  format number, 026-12's SF10. The bytes of 5.5 use stand-ins.
- **Java**, the trace format, the conformance sets, the C clone, the
  Pub layer's view of internal transactions.
- **The whole model on MT's transactions** (`treetest model`'s checks
  of the abstract model's assumptions, T1 and T2): it needs MT as a
  `Spec`, which is the next step's work. K4 has A6 and the pointers.
- **NW.** No spike of it here.
- **Node sizes other than 30 and 8.**

**What follows** (006-28, section 7.7):

- **Step 3: Frans decides** MT, NW or neither, with SF10, on 026-17's
  result. If the counts are bad, NW's spike may come first (006-28,
  question 7's default).
- **Step 4, if MT: the design note.** The fix record, the start's rule,
  the order of the fixes (K7's count says if one pass is enough),
  reclaim's argument, `maintain()`, the H that covers the height
  between (5.6's count).
- **Then** the model and its statements for two kinds of transaction,
  the proofs, Java (step 5). `Mt.lean` is a start for the model: its
  rules are tried.
- **The provers:** if MT is off, they go on with `l4` and `htbL` as
  006-27 decided.


# 9. The cost and the time

- **Agent time:** T1 2.5 h, T2 3.5 h, T3 0.75 h, T4 2 h, T5 0.5 h, T6
  0.75 h, T7 1.25 h, T8 1.25 h: about 12.5 agent-hours, of which 4.5 at
  xhigh. Without T6: under 12.
- **The machine:** 2 to 5 core-hours of runs, one build of a few
  modules. No quiet machine is needed: nothing is timed.
- **Usage: my guess is 5 to 10 % of a week.** From one figure: seven
  Fable agents used about 10 points an hour on 11 November, 1.4 a
  Fable agent-hour. Opus 5.5 costs less; I do not know by how much. At
  half of it, 12.5 agent-hours are 9 points. The stop rule is 12.
- **When.** The week is at 92 % and resets on Monday 16 November at
  22:00. Before that the level is tight: nothing of the trial starts
  but T0, which calls no model. After it:
  - **as an unattended night**, 16 to 17 November: T0 by the
    coordinator in the evening, T1 and T2 at 22:05, the result by about
    07:00. No step waits for Frans; the stop rules decide. The night
    must have no quiet block for timing, or the runs of T5 and T6 wait
    for their slots until it ends;
  - **or attended**, Tuesday 17 November, from the morning: the result
    in the afternoon.
- **Frans's part:** the go, question 1, and reading the result (60
  lines).


# 10. The risks

**What could make MT look better in the model than in Java.**

- **Small trees.** The model has 1,000 to 6,000 keys and height 2 or
  3. At 10 million keys and node size 30 the tree has height 5 or 6, by
  the same arithmetic.
  A delete's fix steps and its nodes grow with the height. 5.6 gives
  the fix steps by height, so that the trend is seen; it is still a
  trend from two or three heights.
- **No restart.** The driver always finishes. In Java a crash can come
  between a user transaction and its last fix step, and the start must
  go on with the fixing and write the same bytes (P2). That is where
  006-28 puts MT's risk, and the trial does not touch it.
- **No time.** Each fix step is a record of its own in the commit. What
  that costs a commit, and against P1's 20 ms, only Java can say.
- **No reclaim, no eviction, no lazy reading.** Untidy states with an
  empty node are in the history. Whether reclaim's cut is safe over
  them is not tried.
- **More times and top nodes used.** Each fix step uses a time, and a
  collapse or a split at the space root a top node ordinal (002's
  bound). 5.6 counts them; the model has no limit that would show a
  problem.
- **Java's checks before the go point** (the record limit, the dirty
  node bound, 027-03, section 8.3) are made for a user transaction. A
  fix step cannot be refused. Not looked at.

**What could make MT look worse than it would be.**

- **The bytes are counts by layout, not Java's stream.** Java writes a
  key node when the take reaches it. A node that two fix steps of one
  group change may be written once, where B-all counts it twice. So
  B-all is high for MT; B-new is the floor. The truth is between, and
  only Java gives it.
- **The stand-ins**: 8 bytes a value, 32 + 8 k for a fix node, 16 a
  got-dirty pair. With small values the index's share is large, so the
  ratios look worse than with a user's values. 5.5 gives the index
  alone too.
- **Workloads made of deletes.** D to H are worst cases by design. A
  user's mix deletes less (family C).
- **The general rule for two empty leaves** makes an empty node that
  the next step merges again. A rule that unlinks an empty leaf would
  be cheaper, but brings LE-b back. Counted (`fix.merge.bothempty`),
  not changed.

**What could make the trial wrong either way.**

- **A fault in the program.** `selftest` and `mutant` (5.3) are the
  guard, and the reach counts.
- **The definitions drift from today's.** `Mt.merge` is a copy with
  changes. T3 reads it against `Exec.lean`; `selftest` and the "no
  delete" groups of 5.4 check the put's side.
- **Node size 8 behaves otherwise**: m = 2 and c = 4, so a merge makes
  two nodes more often. That is why its counts are not read.
- **A rule not reached.** At 30 a parent's cascade inside a fix step, a
  collapse of an inner root's inner child, or a merge of an empty leaf
  may be rare. The reach counts say; family E and H are made for them.


# 11. Questions for Frans

Each with the default that the plan follows. None is waited for, but
the go.

1. **Node size 30 alone, or 30 plus 8 as a stress check?** Default: 30
   plus 8. Every count for the choice comes from 30. Node size 8 (T6)
   answers only pass or fail, on small trees where every transaction on
   a few keys can be run and trees are of height 3 and 4 at 200 keys.
   The number: at 30, 024-22's run on 100 keys made 87 merges in 3,000
   transactions, on a tree of height 1; height 2 needs about 200 to 500
   keys and height 3 about 1,500 to 5,000, by my arithmetic. The plan
   runs 30 at 1,000 and 6,000 keys. If T0 shows that 6,000 keys run in
   their time, 30 reaches height 3, and node size 8 adds only the
   exhaustive small cases; T6 costs about 1 agent-hour and 1 to 2
   core-hours.
2. **The go, and when?** Default: the plan is ready for the night of 16
   to 17 November, after the reset at 22:00. It does not start without
   your go (your word of 10:29); the coordinator asks for it.
3. **MT as separate definitions beside today's writer**, not a
   parameter of it? Default: separate (section 3.1).
4. **Two empty leaves: the general merge**, which makes an empty node
   that is merged again? Default: yes, as 006-28 sketched it, and
   counted; a cheaper rule is for the design note.
5. **May the agent add a rule** when a failure asks for one that
   section 3 does not have? Default: at most two, each written into the
   result; a third stops the trial.
6. **The bytes' stand-ins** (5.5): a fix node of 32 + 8 k bytes, 8
   bytes a value, both sums B-new and B-all? Default: yes.
7. **The branch kept in the main repository**, not merged, and its
   three files as text in the evidence directory? Default: yes.
8. **The agents:** two Opus 5.5 agents and a reviewer, xhigh for T1
   and T4, high for the rest? Default: yes, by 013-02. You asked for
   Fable high for this plan; say if you want it for the trial too.


# 12. What I could not check

Nothing was built or run for this plan.

- **The build in a clone:** that Lake takes the copied `.lake` without
  a rebuild, and how long the 38 modules take if it does not. T0.
- **The model's time a boundary** at 1,000 and 6,000 keys, and so
  every run time of section 6. T0 and T2 measure; 6.1 has the rule.
- **The heights at node size 30** by key count: arithmetic from the
  thresholds. The runs print the heights reached.
- **That `get` and `scan` are right over an empty leaf and an empty
  segment tree.** 006-28 says so by reading. It is Q2, the trial's to
  find.
- **That a full, emptied leaf under an inner node is handled** by
  `handleFullWith` as a node with a lone time klong: by reading. T1's
  guards try it.
- **That every node that needs a fix is on a pending key's path**, and
  that one pass over the keys is enough: my reasoning, K4 and K7 test
  it.
- **That an inner node is never empty** under R1 to R5: my reasoning;
  the target has an error for it.
- **The usage:** one figure, for another model.
- **The got-dirty list's rule** and what a record carries besides its
  48 bytes: 027-03, section 8.4, has it as "to be written".
- **`MtDeps.lean`:** that a walk of the constants gives clean lists.
  Shared match helpers have fooled such walks before; T7 checks its
  list against a `grep`.
- **`treetest random 30 ...` in T0** as a fair measure: it keeps the
  nodes in a list, so it is slower than the trial's program will be.



# Log

2026-11-16. The header, Frans's words and the outline by the coordinator
(coord-1116), 10:47. The plan, sections 1 to 12, by an agent of
coord-1116 (Fable, high): the skeleton at 10:48, complete at 11:03
(times from `date`). At 10:55 the coordinator changed the brief on node
sizes, after Frans: 30 is the main line, 8 an optional stress check, 14
dropped (sections 1, 6 and 11, question 1). Read for it: 006-28,
sections 2, 3 and 7 to 9; 025-01, section 5, and its brief, sections 1
to 4; 025-05, section 4.4; 024-22, section 2.9 and its runs at node
size 30; 027-03, sections 8 to 12; 027-13, section 1; 026-03, sections
1 and 2; 010-01, P2; 013-02, sections 6 and 9; `Exec.lean` from the
delete to its end, `Inv.lean`'s walk, `Read.lean`'s get, `Props.lean`'s
reference map, `Node.lean`'s parameters, `TreeTest.lean`,
`segfit-check` and `live-counts-check` of 024-12, the lakefile, and the
night's `treetest` report of 15 November. Nothing built, nothing run.
The trial is not started.
