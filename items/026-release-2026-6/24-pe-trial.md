# 026-24. The PE trial: plan, then emit, in the model

Created 2026-11-18 by Frans Lundberg. Status: done (2026-11-18): go, for
Frans to decide.

The model-first test of PE, "plan, then emit" (026-23, section 1.2), the
writer design that removes the take-back at its cause: one recursion over
the tree decides each node once, from the transaction's whole batch, and
then each decided node is written once. Frans, 2026-11-18, 12:47: "The PE
trial. Yes, do it as recommended. Good if done by 07:00 tomorrow. If
possible." Three phases (026-23, 1.2, "The cheapest checks that could
refute it"): paper, the model on the traces (the go/no-go), a proof spike.
By an agent of coord-1118, from 12:50.

The evidence is in 24-pe-trial/: the Lean as `.lean.txt`, the scripts, the
runs' summaries. The code is on the branch `026-24-pe-trial`, in
`lean/pe/` (a Lake package of its own beside `lean/contract/`; today's
writer, `lean/SIS/Tree/Exec.lean`, and `lean/contract/` are not changed).


# Result

For Frans. The details and the evidence are in sections 1 to 3.

**Go.** PE passes the trial in the model: at every transaction of every
trace it writes a tree that meets the contract, with fewer bytes than
today's writer, and the proof of it is small and has no in-between states.
One of 026-23's checks fails by its letter, for a reason found on paper
first (below); I judge that it does not refute PE, and the call is
Frans's.

- **What PE is** (026-23, 1.2): the writer first plans the whole
  transaction on lists (each touched node's last list: the operations
  applied at the leaves, empty children dropped, small ones joined with a
  neighbour, long ones cut, the root collapsed or raised), and then writes
  each planned node once: nothing, a few klongs appended to the node of
  before, or new nodes. No node is made and then taken back, none is
  written twice. The model's writer is about 280 code lines (297 with the
  trial's two options); today's is 829.
- **Phase 1, on paper**: for one operation, today's writer gives each
  node's last list, except in a full node, where the cut of a space split
  (F1), when it splits (F2) and the layout of its klongs (F3) depend on the
  order of work inside the operation. Phase 2 found a fourth (F4): a
  delete's take-back leaves a dead klong that can make a parent compact or
  split.
- **Phase 2, on 026-21's 288 traces** (221,142 transactions, 1.8 million
  operations), and the large set's seeds 11 to 30 (120 traces, 340,000
  transactions) for the checks and the bytes:
  - no fault: the contract (C1 to C5) and the writer's own rules held at
    every transaction; every get, scan and Java's 1,067,010 reads right; no
    node made left out;
  - bytes: B-new 0.962 and B-all 0.992 of today's over all, every set
    below 1.0 but own's B-all at 1.004 (the limit was 1.02); seeds 11 to
    30: 0.974 and 0.996; key nodes made 0.917; trees a little fuller (3.49
    live klongs a node against 3.43), never taller (6 against 7);
  - sorted loads in large transactions, step times' bad case (1.41 in
    026-21): PE 0.98 for 500 keys a transaction, 0.85 for 10;
  - one operation: 93.2 % of 62,854 transactions give today's change entry
    for entry; the other 6.8 % differ by F1 to F4 only (with today's count
    and cut put into PE, 85 remain, all F4 or one counting case of F2), and
    PE never writes more klongs or more new nodes there (B-all, counting a
    changed node whole, is higher in 8). By the letter of
    026-23's check this refutes PE; by its purpose it does not (section
    2.5).
- **Phase 3, the proof spike**, in Lean against the contract's definitions,
  Lean's three standard axioms, no `sorry`; 3,288 lines of its own and 980
  reused from the tag:
  - the lemma of emit (498 lines): a node written by emit holds exactly
    its planned list, stays well formed, and readers at earlier times see
    it unchanged;
  - the lemma of settle (588 lines): dropping, joining and cutting
    children never loses, adds or reorders a key, and keeps every child in
    its key range;
  - together 1,086 lines, under the limit of about 2,000; and no lemma
    needs a fact of a half-done transaction, the spike's other refutation;
  - beyond them, for keys of one segment: the whole transaction's plan
    keeps the keys and the order; and PE's contract, all three clauses, is
    reduced to four facts of the tree that emit writes, each node's part of
    which is emit's lemma. For the database: if emit writes each planned
    node as the lemma says, within the node size and with pointers to
    nodes that exist, then every get and scan after the transaction is
    right (the contract's read theorems, 030-05);
  - not proved: that emit's tree has the four facts (the heap's
    bookkeeping), the program as an instance of the relations proved,
    keys of several segments, TREE and the top, the level bounds.
- **A complete proof** (a judgment): about 6,500 to 9,500 lines of its
  own, 3,288 of them done; today's writer took 22,500 lines for its puts
  alone at the tag, with 20,000 to 35,000 more estimated for its deletes.
- **Recommendation**: take PE as 2026.6's writer, model first. (1) The
  program as total functions on the contract's tree, and the proof
  completed, one segment first. (2) Then Java's write half rewritten to
  match it, under a new record format number (ids come in another order).
  (3) Step times (026-21's (b)) is then not needed: PE has none of its
  costs (the time klong, more top nodes, 1.41 on sorted loads). Keep the
  cut size a parameter, M / 2 by default (section 2.6: then below today's
  on every trace of the own and medium sets).
- **Unknown**: Java's real bytes and commit times (the model counts 026-17's
  stand-ins); trees of millions of keys (the traces reach tens of
  thousands); memory in a very large transaction (a list a touched node);
  the Java effort (026-23 guessed two to three weeks).


# 1. Phase 1, on paper: does today's writer give the last list?

The question (026-23, 1.2, check 1): is there a rule of today's writer
whose result is not "the last live list of each node, emitted once"?

Read for it: the model's writer, `lean/SIS/Tree/Exec.lean`, whole, with
`Node.lean`'s `halves`, `lastVersion` and `add`. The model follows
`Dag.java` node for node (treecheck compares them on every traced
transaction), so its rules are Java's.

**With many operations in a transaction, yes, by design.** Today's result
depends on the order of the operations: a node made by one operation is
split in place by the next, a merged node is merged again, a node made is
taken back. That is what PE changes; whether it costs bytes is phase 2's
question.

**With one operation, three rules, all in the rule of a full node**
(`handleFullWith` with `halves`):

- **F1, the cut of a space split.** `halves` cuts the node's last version
  *before* the operation's new klongs (`ins`) at its middle, and then
  appends `ins` to the half where the first of them falls. So for a put
  of a new key into a full node, the cut depends on which key is the new
  one: at node size 8 (h = 4), a leaf of 4 live entries and a new key
  below the middle gives halves of 3 and 2 entries, above the middle 2
  and 3. A rule on the last list (5 entries) cannot tell which key came
  last. Any PE cuts the last list, so in about half of the puts' space
  splits its halves differ from today's by one entry: the same number of
  nodes and klongs, another cut.
- **F2, the count of rule O** (a full node is space split if its last
  version has more than h klongs, the time klong counted). The last
  version is taken before `ins`. So a node that gets a new compare value
  from the operation (a put of a new key, a new segment, the second half
  of a split below) is space split when its final list has more than h
  entries; a node whose final list only lost entries or got a pointer
  changed (an update, a delete, a merge's parent, LE-b, a time split
  below) when it has h or more. A merge's parent that gets a new compare
  value for a merge's second node (`insertSorted`) counts it, as the
  second kind. A rule on the last list takes one count; PE takes "more
  than h" (one new node holds at most h entries), so the second kind
  differs when the final list has exactly h entries: today two halves,
  PE one node.
- **F3, the layout of a new node.** A space split of a node that gets an
  update keeps the replaced klong in the half beside its replacement, and
  both splits append the operation's klongs at the end of the node, not
  in compare order. PE's new node is a time klong and its list in compare
  order: the same live list, never more klongs. 026-23, section 4, counted
  this on Java's traces (Java's new nodes 3.3 % more klongs).

Not a difference of result: the take-back inside one operation (a full
node replaced and then merged, 026-21's D1 to D5; a root made and taken
back, 024-22's MF1). Today's change after the take-back is the last list;
PE never makes the node.

**So**: for one operation, today's result is the last live list of each
node emitted once, except in a full node, where the cut (F1) and the count
(F2) depend on the order of work inside the operation (the list before the
new klongs), and the layout (F3) shows it. The check "a transaction of one
operation gives today's change klong for klong, beyond the ids and MF1"
(026-23, 1.2) therefore cannot pass for every transaction, for any PE.
Phase 2 counts the differences, shows that they are these three and no
other, and compares their cost.

**Corrected by phase 2 (section 2.4): a fourth rule, F4.** The paragraph
above "Not a difference of result" is wrong in a few deletes. When a
delete finds its leaf full, today's writer first replaces the leaf (a time
split), which adds a klong to the parent, and then merges the new leaf,
which deletes that klong again. The klong stays in the parent as a dead
klong. With it the parent can pass theta and be compacted into a new node
(`merge.parent.dead`), or be full and be split (`merge.parent.full`), where
the parent's final list alone would have let the klongs be appended; a
split parent may then be merged back one level up. PE never writes that
klong. Found by the model: 80 transactions of the 62,854 of one operation
(section 2.4), all deletes of this kind.


# 2. Phase 2, the model on the traces

## 2.1 What was built

- **PE's writer in the model**, `lean/pe/Pe/Plan.lean` (444 lines, 297 code
  lines, about 280 without the trial's options `todayCut` and `cap`; as
  text in 24-pe-trial/Plan.lean.txt), as 026-23, 1.2 describes
  it, with one change of order: the whole plan is made first, lists only,
  each virtual node with its decision (`same`, `append`, or `parts k`), and
  only then does emit write, bottom-up, each node once. So a root collapse
  or a join can drop a virtual node that was planned but never written. It
  uses today's writer's state and small steps (`getNode`, `newKey`,
  `newValue`, `newSuperRoot`, `changesOf`, about 120 code lines of
  `Exec.lean`), not its rules. Today's writer is 829 code lines.
- The rules of plan and emit, as built:
  - a segment leaf: its live list with the operations applied; operations
    with more segments go, by compare value, to the next segment's tree;
  - an inner node: the operations divided by its live list; plan on each
    child that got some; `rebalance`: an empty child dropped; a changed
    child with fewer than m entries joined with a neighbour by M1 (the
    left one if it exists and the two hold at most c, or there is no right
    one; else the right one); a join of two inner nodes is rebalanced again
    one level down, so that a child left alone under its parent gets a
    neighbour; the first entry gets the empty key;
  - a root alone: empty, the tree is empty (the space root an empty
    segment leaf); an inner root with one entry, its child is the root; a
    root of more than one part, a new root above, until one part;
  - the decision (emit's three cases): F is the base's live list, nothing;
    the base has room for a time klong of i, a bitmap if a compare value
    left, and a key klong for each entry new or repointed, and stays
    within theta: those klongs appended; else new nodes: one if the base is
    full by its dead klongs only or F has at most h entries (c for a
    joined list), else ceil(|F| / h) parts as even as possible, the larger
    last (as a space split's halves) or first for a joined list (as a
    merge's two nodes).
- **The trial program**, `lean/pe/PeTrial.lean` (as text in
  24-pe-trial/PeTrial.lean.txt), 026-21's `steptimes` cut down to one step
  a transaction, with three modes: `today` (today's writer), `pe`, and
  `pet` (PE with today's cut of a full node emulated in transactions of one
  operation, for section 2.4 only). Each trace runs from the empty tree on
  the mode's own structure P.
- The checks at every transaction, as 026-21's (its section 3): the map
  (every get of the transaction's keys, every GET and SCAN line of Java's
  trace, a full scan every 10th transaction and at the end, the history at
  every 50th); the contract of `lean/contract` (C1 invariants, C2 contents,
  C3 frame over the nodes changed, C4 TREE, C5 the top); the writer's own
  rules (`shapeFaults`: FillOK, RootsOK, LeftmostOK, DeadOK, BalancedOK),
  each fault a failure of PE; and new: every key node made is named by a
  live klong of a node the transaction changed, or is the new space root
  (`made.unnamed`). In mode pe, today's writer runs beside PE from PE's
  tree: in every transaction of one operation (compared, section 2.4), and
  in every transaction (`--paired`) for its bytes from the same tree.
- Bytes are 026-17's stand-ins, as 026-21's: B-new counts the key nodes a
  transaction made, B-all every key node it changed, each whole at the
  transaction's end, both with the record, the values, the deletes and the
  top nodes; "index" leaves out the values and the deletes. Java's stream
  lies between B-new and B-all. Against today's model writer: it is Java's
  writer node for node (treecheck), so these are Java's shapes.
- The traces: 026-21's 288 (level 2's small 70 and drain 110, reclaim 15,
  medium 27, large 60, the study's own 6: sorted bulk loads of 500, 100 and
  10 keys a transaction, and a Pub-like index with 1, 10 and 100 changes a
  transaction), 221,142 transactions, 1,792,106 operations. Node sizes 8,
  14, 30 and 62, record format 7's m, h, c and theta.

## 2.2 The checks: no fault

On all 288 traces, in modes pe and today (and pet):

- the map: no failure (every get, Java's 1,067,010 GET and SCAN lines, the
  scans, the history);
- the contract: C1 to C5 held at all 221,142 transactions of PE;
- the writer's own rules: no fault at any transaction's end (FillOK,
  RootsOK, LeftmostOK, DeadOK, BalancedOK);
- no node made is left out (`made.unnamed`: 0), none taken back (`taken`:
  0), no error, no node outside the level bounds G and H + 2 (the greatest
  height PE reached is 6, today's 7).
- the large set's seeds 11 to 30 (`large2`, 120 traces, 340,000
  transactions, 1.1 million operations), in mode pe: the same, no failure
  (the map, Java's 1,700,000 reads, the contract and the shape at every
  transaction).

## 2.3 Bytes, nodes, fill

PE against today on the same traces (each from its own tree), from
24-pe-trial/runs/agg-v1.txt. B-new, B-all; the index's B-new, B-all:

- small (70): 0.942, 0.958; index 0.908, 0.947
- drain (110): 0.892, 0.955; index 0.830, 0.941
- reclaim (15): 0.989, 0.996; index 0.982, 0.995
- medium (27): 0.972, 0.994; index 0.950, 0.993
- large (60): 0.973, 0.995; index 0.958, 0.994
- own (6): 0.976, 1.004; index 0.950, 1.005
- all 288: 0.962, 0.992; index 0.936, 0.990

By node size: 8: 0.926, 0.963; 14: 0.958, 0.990; 30: 0.983, 1.002 (index
0.968, 1.003); 62: 0.985, 0.998.

The large set's seeds 11 to 30 (120 traces), against today's RESULT lines
of 026-21 (its 21-step-times-study/runs/results-large2.txt; today's writer
is the same, its bytes do not depend on the times): 0.974, 0.996; index
0.959, 0.995; key nodes made 0.928; the greatest height 6 against 7.

- **Key nodes made** 0.917 of today's, key klongs added 0.944, top nodes
  0.925, nodes changed 0.968.
- **Fill** (live klongs a key node, sampled every 20th transaction): 3.49
  against 3.43; dead klongs a node 0.75 against 0.78; at the end 143,958
  key nodes against 148,249; the greatest height 6 against 7.
- **Paired** (today's writer from PE's tree before each transaction, so
  both start every transaction from the same tree): B-new 0.947, B-all
  0.985, key nodes made 0.883. PE writes less per transaction; over a run
  its trees are a little fuller, which gives some of that back.
- **The own workloads**, one trace each: bulk-500 0.980, 0.980 (index
  0.939, 0.941), bulk-100 0.966, 0.966, bulk-10 0.849, 0.885: PE is
  cheaper on sorted loads in large transactions, the case where step
  times cost 1.41 (026-21): a long list is cut once into parts of at most
  h (17 at node size 30), 16.5 live klongs a node at the end against 13.9.
  The Pub-like index: pub-1 1.002, 1.017 (index 1.004, 1.020), pub-10
  1.008, 1.019 (index 1.016, 1.022), pub-100 0.992, 1.010 (index 0.983,
  1.011): within 2 % over
  today, from fuller nodes (13.2 live klongs a node against 12.2, so more
  of each changed node is written); paired, PE is below today there too
  (0.987 and 0.998).
- **Single traces above 1.02**: a few small ones, the worst r-small-1 (node
  size 8, 30 keys) at 1.046 and r-idle-1 at 1.039 for B-new: tiny trees
  where PE's fuller nodes make the tree a level shallower, so the root
  takes more of the changes (top nodes 2.9 times today's there). No set
  is above 1.02.

## 2.4 One operation: today's change, but for F1 to F4

In each transaction of one operation, today's writer ran beside PE from
PE's tree, and the two trees at T were compared: the key nodes reached that
are new or got entries at T, new ids renamed in the order of a walk.
Three outcomes: the same entries; the same live lists in another layout of
klongs; other (the lists differ).

- **pe**, all 288 traces, 62,854 transactions of one operation: the same
  entries 58,553 (93.2 %); the same lists in another layout 1,382 (2.2 %,
  F3); other 2,919 (4.6 %). The other ones are space splits cut one entry
  over (F1) and full nodes whose final list has exactly h entries (F2),
  with their effects one level up.
- **pet**, PE with today's count and cut of a full base emulated in
  transactions of one operation (the count and the cut of the entries
  whose compare value the base had, the list before the operation's new
  compare values): the same entries 59,028 (93.9 %); the same lists in
  another layout 3,741 (6.0 %, F3: today's halves keep a replaced klong,
  and append the new one out of order); other 85 (0.14 %), all deletes,
  each printed (CMP1 lines): 80 have today's take-back inside the delete
  (F4: `merge.made.*` and `merge.takeback`, a full leaf replaced and then
  merged, its parent compacted or split for a klong it no longer holds);
  5 are merges into two nodes whose parent is full, where today counts the
  second node's new compare value (`insertSorted`) and the emulation does
  not (F2's merge case).
- So the differences are F1 to F4 and no other: once today's count and cut
  are put into PE, only the take-back's traces and one counting case of
  F2 remain.
- PE never writes more key klongs, more bytes of new key nodes (B-new) or
  more new key nodes than today in a transaction of one operation, on all
  288 traces (`more`, 24-pe-trial/runs/more.txt). B-all is higher in 8 of
  the 62,854, all F4 deletes in the large set's l-few traces: today's
  take-back there replaces the root by a compacted new one, where PE
  appends one or two klongs to the old root, which B-all counts whole
  (MORE lines; there PE writes 8 klongs against today's 12, and 208 bytes
  of new nodes against 336).

## 2.5 The go/no-go

The refutations of 026-23, 1.2, check 2, one by one:

- **A fault of the contract or of the shape check: none.** 221,142
  transactions of 288 traces, C1 to C5 and the writer's own rules at every
  transaction; the map right everywhere; no node made left out.
- **Bytes of a set above 1.02 times today's: none.** The highest set is own
  at 0.976 (B-new) and 1.004 (B-all), its index 1.005; all others below
  1.0. Today's model writer is Java's writer node for node (treecheck), so
  these are Java's shapes; the bytes are 026-17's stand-ins.
- **A transaction of one operation that differs from today's change beyond
  the ids and MF1: by the letter, yes**, 4,301 of 62,854 (6.8 %; 1,382 of
  them only in the layout of klongs). Phase 1 shows that no PE can pass
  this check in full: today's result there is not a function of the last
  lists (F1 to F3). Phase 2 shows that every difference is F1 to F4, and
  that PE never writes more klongs or new nodes there (B-all, which counts
  a changed node whole, is higher in 8).

**My verdict: go.** Check 2's third refutation was meant to catch PE being
a different algorithm with different costs from today's in the simple
case; it is not: where PE differs, today's own result depends on the order
of work inside one operation, and PE writes no more klongs. If Frans reads the
third refutation by its letter, this is a no-go by it alone; the numbers
above are the same either way.

## 2.6 The cut size and the fill

PE cuts a list that does not fit its base into parts of at most h entries
(17 at node size 30). Its trees are then a little fuller than today's
(own: 13.5 live klongs a node against 12.5), which costs B-all on the
Pub-like index (pub-1, pub-10, pub-100: 1.017, 1.019, 1.010; index up to
1.022), where every changed node is counted whole. A variant, mode `peh`
(`Pe.Opt.cap`): when a list is cut, parts of at most M / 2 entries (15).
Run on the own and medium sets (24-pe-trial/runs/peh-own.txt,
peh-medium.txt; no failure):

- own, all six: B-new 0.964, B-all 0.983 (index 0.925, 0.980), against
  pe's 0.976, 1.004; fill 11.5 against today's 12.5;
- the Pub-like index: B-all 0.990, 0.993, 0.989, now below today's; the
  sorted loads give a point back: bulk-500 0.990 (pe 0.980), bulk-100
  0.974 (0.966), bulk-10 0.875 (0.885);
- medium: the same as pe (0.973, 0.993).

So the cut size is a parameter that moves cost between sorted loads and
index updates; with M / 2, PE is below today's on every trace of these two
sets. Not run on the other sets. My judgment: M / 2 as the default.


# 3. Phase 3, a proof spike

## 3.1 What is proved

A Lake package of its own, `lean/peproof/` (Mathlib, as `lean/contract/`;
it reads the contract's definitions through a link, and `lean/contract/` is
not changed). The Lean as text in 24-pe-trial/peproof/. Lean's three
standard axioms only (`Axioms.lean` prints them for every theorem below:
`propext`, `Classical.choice`, `Quot.sound`), and no `sorry`.

**The lemma of emit** (`PeProof/Emit.lean`, 498 lines), on the contract's
klongs (`Contract.Klong`, `live`, `klongsWf`, `extKs`, `prefixAt`). For a
base whose klongs ks are well formed, nonempty and of times before i, and a
list F in strictly increasing order of compare values, emit's klongs
(`emitKs`: a time klong of i; a bitmap with the last bitmap's bits and the
bits of every klong of the compare values that F leaves out, if any; a key
klong for each entry of F that is new or repointed):

- `emitKs_live`: the node then holds exactly F;
- `emitKs_wf`: its klongs stay well formed (W1 to W4);
- `emitKs_ext`, `emitKs_extKs`: the base's klongs are kept and the first
  klong added is a time klong of i (the contract's `Ext`), and
  `emitKs_prefixAt`: a reader at an earlier time sees the base as it was;
- `emitKs_ptrs`: every key klong written names an entry of F;
  `emitKs_length`: the klongs added are what PE's decision counts against
  the node size;
- for a new node, a time klong of i and F's entries: `newKs_live`,
  `newKs_wf`, `newKs_ptrs`, `newKs_length`.

**The lemma of settle** (`PeProof/Settle.lean`, 588 lines), on lists. A
parent's entries are its children's compare values and lists; the child
level read as one list (`flat`) gives an inner child's first entry its
compare value in the parent. The steps of settle (`Step`): drop an empty
child, join a child with the next one, cut a child's list into nonempty
pieces (the parent gets each piece's first compare value, an inner piece
starts with the empty key):

- `Step.flat_eq`, `Steps.flat_eq`: every step keeps the child level, so no
  key is lost, added or moved;
- `Step.ranged`, `Steps.ranged`: every step keeps each child in its range,
  from max(lo, its compare value) to the next one's or the parent's bound,
  in strictly increasing order (`RangedFrom`: the contract's RangeOK for a
  parent and its children), and `ranged_renameFirst`: so does the empty
  key put on the parent's first entry (LE-b); `flat_sorted`: then the
  child level is in strictly increasing order;
- `cut_spec`: emit's cut (`partSizes`, `cutList`, the definitions of
  `Pe/Plan.lean`) of a list of n entries into k parts, 0 < k ≤ n, gives
  nonempty parts that make the list again, k of them, each of at most n / k
  + 1 entries.

**Reused, not counted**: `PeProof/Quarry.lean`, 644 lines taken unchanged
from the tag `writer-proof-2026-11-18` (030-10's node algebra, the parts
about the contract's klongs: NodeAlg.lean section 1, and pieces of
NodeAlg2.lean and NodeAlg3.lean), and main's `Contract/Proof/Node.lean`.
Three of their lemmas are generalized in Emit.lean from one compare value
to several (`liveWith_unionR`, `bitmapOk_unionR`, `klongsWf_snoc_unionR`).

So the two lemmas need 1,086 lines of their own: under 026-23's limit of
about 2,000.

**Beyond the two lemmas: the proof's part 1 for one segment** (026-23,
1.2: "plan and settle keep the keys, the order and the kinds"), on an
abstract tree of lists, where a node of height h is its list of entries
(`PeProof/Abs.lean`, 408 lines; `AbsOrder.lean`, 974; `AbsRoot.lean`,
107). PE's plan is stated as a relation, `Plan`, so that what is proved
holds for every choice PE makes (M1's neighbour, h and c, the number of
parts): a leaf gets the operations applied; an inner node's operations are
divided among its children by its list (`route`, as `Pe.plan` divides
them), each child with operations is planned, and the children are
settled by any sequence of the settle steps above, where a child's own
list may be settled again one level down (`Sett.down`: the join of two
inner nodes rebalanced at its boundary), no child is left empty, and the
first entry gets the empty key. The root alone (`Root`): an inner root
with one child gives way to it, a root of more than one part gets a new
root above, settled there, and an empty space root becomes an empty leaf.

- `Plan.keys`: the planned node holds the old node's keys with the
  operations applied, for operations in its range;
- `Plan.wf`: a node in order (nonempty, its entries in strictly increasing
  order and below hi, a leaf's at or above lo, an inner node's first entry
  the empty key and each child in order with its range), with operations
  in its range, is planned into a node in order with the same range, or an
  empty one; through every level settle touches (`Sett.inv`), including
  the join of two inner nodes, whose children's ranges are then checked
  across the old border (`WF_join`), and the cut, whose pieces get new
  bounds (`cut_pieces`);
- `Root.keys`, `Root.wf`: the root alone keeps the keys and the order.

**Beyond: the glue, for keys of one segment** (`PeProof/View.lean`, 382
lines; `Chain.lean`, 103; `Realize.lean`, 228), against the contract's own
`Good` and `L` (main's Contract/Proof/Good.lean):

- `view_wf`, `view_L`: a node of the contract's tree that the walk finds
  sound (`Good`) and that is shaped as PE's trees (`Shaped`: of height h,
  each child one height down, an inner node's first live klong the empty
  key, a leaf's segments short) is, read as an abstract node (`view`), in
  order, and holds the contract's contents below it; `applyOps_kv1`: the
  plain maps agree; `plan_contract`: PE's plan of it holds the contract's
  contents with the contract's operations applied, in order;
- `good_of_view`: the converse: a node shaped as PE's trees, with the
  facts the view forgets (`Sound`: well-formed klongs, values, lower
  levels), whose view is in order, is sound for the contract;
- `contractOk_of_view`: **clauses 1 and 2 of the contract** (the
  invariants at i, the contents) hold for PE's transaction if the tree
  after is shaped as PE's, sound, its view is the plan, its nodes meet the
  rules of one node (`nodeOk`) and its root is a leaf or has a live klong;
- `Realizes.holds`: the inductive step of the glue's second half: a node
  that emit wrote, whose live list is the planned entries with its
  children's ids (what emit's lemma gives), each child holding its planned
  child at a lower level, or an old node kept as it was, holds the plan;
- `frame_of_writes`: **clause 3, the frame**, for a writer that leaves an
  old node as it was or gives it emit's klongs (`emitKs_ext`), and adds
  new nodes and roots of time i;
- `contract_of_writes`: **the whole contract, clauses 1 to 3**, for PE's
  transaction on keys of one segment, from four facts of what emit writes:
  the tree after holds the plan (`Realizes`), its nodes meet the rules of
  one node, its root is a leaf or has a live klong, and each node is
  written once (`Writes`).
- `view_agree`, `at_agree`: a kept subtree holds what it held: a node that
  the transaction leaves unchanged, all of whose times are before i, is at
  i what it was at i - 1, and so is its view, shape and soundness if every
  node below it is so (the case `Realizes.kept`).

Reused, not counted, besides `Quarry.lean`: `PeProof/Quarry2.lean`, 336
lines of the tag's `TreeCtx.lean` (its sections 1 and 2 and `Good.widen`:
`invOk_iff`, the invariants as `Good` and the rules of each node reached).

In all, 3,288 lines of the spike's own, and 980 reused.

## 3.2 In plain words

- **Emit**: whatever list the plan decides for a node, writing it by emit
  gives a node that holds exactly that list, stays well formed, and looks
  to every reader at an earlier time as it did. It holds for any node of
  the tree before (well formed, times before the transaction's) and any
  ordered list: no fact of a half-done transaction is used, because there
  is none.
- **Settle**: dropping empty children, joining neighbours and cutting long
  lists never loses, adds or reorders a key at the level below, and keeps
  every child inside its key range, also after the empty key is put first.
- **Plan, for keys of one segment**: whatever PE decides, the whole
  transaction's plan gives a tree that holds exactly the old keys with the
  operations applied, in key order, every node within its key range, and
  settling the root alone does not change that.
- **The contract, for keys of one segment**: if the nodes that emit writes
  hold the plan (each node's part is emit's lemma), are within the node
  size, point to nodes that exist, and are written once, then PE's
  transaction meets the whole contract: a sound tree at i, the right
  contents, and nothing earlier changed. So gets and scans are right after
  it, by the contract's read theorems (030-05).

## 3.3 Not proved, or reduced

`contract_of_writes` reduces PE's contract, for keys of one segment, to
four facts of the tree that emit writes. Not proved:

- **That emit's tree has them**: written bottom-up, each node by `emitKs`
  (on its base) or `newKs` (new), its children's ids first, so that the
  tree after holds the plan (`Realizes`); each node within the node size
  (the decision's fit test, the bound of `cut_spec`) and its pointers
  naming nodes that exist (`nodeOk`); fresh ids, each base written once
  (`Writes`). Emit's lemma gives each written node's part, and
  `view_agree` with `at_agree` a kept subtree's; the bookkeeping of the
  heap that joins them is what is left.
- **The executable writer is an instance of the relations**: `Pe/Plan.lean`
  is a `partial` program; that its `plan`, `rebalance`, emit's cut and
  `settleRoot` are steps of `Plan`, `Sett` and `Root` is not proved. In
  the program the cut is decided in the plan and made in emit; in the
  relation it is a step of settle at the parent.
- **Keys of several segments**: the abstract tree and `Shaped` have one
  segment; a segment leaf whose entry roots the next segment's tree is the
  same recursion once more, with the key's prefix.
- **TREE and the top (C4, C5)**, the space roots' link to the top nodes,
  and the level bounds G and H (the refusal).
- **The model's entries**: the contract reads klongs; the model's writer
  makes entries (`Changes`, `entriesOf`). A proof made directly on the
  contract's tree avoids this bridge; one on the model's state needs it
  (the tag's `BridgeMap.lean` is its quarry).

## 3.4 The refutations of the spike

- **More than about 2,000 lines for the two lemmas: no**, 1,086.
- **The induction needs a fact about a state that is not a tree: no.**
  Every premise of what is proved is a fact of the tree before (a node of
  P@(i-1): well formed, of times before i; sound and shaped), of lists (F
  ordered; the settle steps), of the planned virtual tree (a tree of
  lists), or of the tree after (the four facts of `contract_of_writes`).
  The induction of part 1 is on the old tree's height, each step using
  only the children's results and the settle lemma; the glue's induction
  (`Realizes`) is on the planned tree. Nothing describes a half-done
  transaction.

## 3.5 The size of a complete proof (a judgment)

Done: 3,288 lines of the spike's own, with 980 reused from the tag: the
two lemmas, part 1 for one segment, and the contract for one segment
reduced to what emit writes. Left, by my estimate from what the spike cost
and from the tag's sizes:

- emit's tree has the four facts (the heap's bookkeeping: ids, bases
  written once, sizes, pointers, kept subtrees): 1,000 to 2,000;
- the program as an instance of the relations, written as total functions
  on the contract's tree: 800 to 1,500;
- keys of several segments (the abstract tree, `Shaped` and the view with
  segment roots): 800 to 1,500;
- TREE, the top and the roots' link (C4, C5): 300 to 700 (030-10's TP24
  was about 420);
- the level bounds and the fuel: 200 to 400.

So 3,100 to 6,100 lines more, and **about 6,500 to 9,500 lines of its own
for the whole PE writer against the contract**, deletes, merges and root
collapse included. For comparison: the puts alone of today's writer took
22,500 lines at the tag, and 030-10 estimated 20,000 to 35,000 more for
its deletes (026-21: 13,500 to 24,000 under step times). 026-23 guessed
8,000 to 15,000 with no trial behind it. What makes it small is what PE
removes: no in-between states, no take-back and its books, one form of
each rule; the part that is hard for any B-tree, the order across the
join of two inner nodes, took under 1,000 lines here.


# State

2026-11-18, 14:40. Done: phases 1 to 3, the cut variant (section 2.6), the
result. No run going.

- Branch `026-24-pe-trial` in /Users/f/fl/bench/2026-11-18/pe/clone, from
  main f2d034e1; not pushed, not merged. `lean/pe/` (the writer and the
  trial program) and `lean/peproof/` (the proofs) are Lake packages of
  their own; `lean/contract/` and `lean/SIS/` are not changed.
- To run again: `cd lean/pe && lake build petrial`; then
  `24-pe-trial/scripts/runall.sh BIN TRACEDIR OUTDIR "SETS" "MODES" 4` and
  `24-pe-trial/scripts/agg.py OUTDIR` (the traces are 026-21's, in
  /Users/f/fl/bench/2026-11-18/st/traces). The proofs: `cd lean/peproof &&
  lake build && lake env lean Axioms.lean`.
- Raw outputs outside the repository, in /Users/f/fl/bench/2026-11-18/pe/
  (runs/v1, v2, v5, more; the binaries petrial-v1 to v5).
- For Frans: the go/no-go (section 2.5: go, with check 2's third
  refutation failed by its letter), and whether PE is 2026.6's writer.


# Log

2026-11-18. Created the item; the clone /Users/f/fl/bench/2026-11-18/pe/clone
at main f2d034e1, branch `026-24-pe-trial`, the Lake caches of land/clone
and st/clone. Phase 1 (12:50 to 13:15).

2026-11-18. Phase 2: PE's writer and the trial program built (13:00 to
13:10); runs on the 288 traces in modes pe and today (13:05 to 13:30, no
failure), again with the made-node check and mode pet (13:31 to 14:00,
the same numbers), the one-operation count without the contract (14:00 to
14:08); the go/no-go written. The night's run (java/night.sh) shared the
machine; at most four of these processes at a time.

2026-11-18. Phase 3: the lemma of emit (13:15 to 13:28), the lemma of
settle (13:28 to 13:30), then part 1 on the abstract tree (13:37 to
13:59), the glue's first half and the reduction of the contract to what
emit writes (14:04 to 14:16), a kept subtree (14:21). Result written
(14:20). The large set's seeds 11 to 30 in mode pe (14:10 to 14:18; today's
bytes from 026-21's RESULT lines), the cut variant on the own and medium
sets (14:23 to 14:38). Done.
