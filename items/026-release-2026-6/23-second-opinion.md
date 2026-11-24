# 026-23. A simpler writer for a complete proof: a second opinion

Created 2026-11-18 by Frans Lundberg. Status: done (2026-11-18): the
proposals, the comparison and one count. PE, the first proposal, taken
to a trial (Frans, 12:47; 026-24), proved (030-21) and made in Java
(026-25).

Frans's question, 2026-11-18: how could BergDB's writer be made simpler,
so that a complete proof of it becomes feasible, with similar performance
to today? A second opinion, open-ended: proposals of my own, not a review.
I am an agent of coord-1118, "I" below; started 11:53, to be committed by
13:20.

**What I read, and what I did not.** Read: 006-28, sections 1, 3 and 4;
030-04, sections 1 to 4; 030-05; 030-10 (sections 1 and 5, the State
note); 030-16; 024-11, section 1; 027-03, section 11; 006-19's summary;
the model's writer, `lean/SIS/Tree/Exec.lean`, whole; the list of books at
the tag `writer-proof-2026-11-18`; the method list of `Dag.java`. Not read
before sections 1 and 2 were committed: 026-17 to 026-22 and 006-28,
section 7. Two things of them reached me anyway, and I name them where
they matter: 006-28's summary names NW (a writer that computes the net
change) and MT (maintenance transactions), and the subject line of
026-21's commit says that step times cost about 1.12 times the bytes.

Proposals are PE, GS, CC and FR; cite them as "026-23, PE".


# 1. The proposals, ranked

## 1.1 What makes the writer hard, in one paragraph

Today's writer is a loop over operations that edits the real tree: nodes
with times, bitmaps and dead klongs. So between two operations the real
tree is half made, and every fact a proof needs must be carried through
every rule in that state: that is what the books are. I see two separate
causes. (1) A node is made, given an id and linked before the writer
knows whether the transaction will keep it; the take-back, `madeFor`,
`retarget` and the link books (B14, `WcrLink`, `WmgFresh`,
`WmgSplitLink`, `LinkLive`) exist only to undo that. (2) A node is edited
more than once at one time, so every rule has a second form for "my own
node" (in place) and old nodes need `toPrev`. Neither cause is in the
problem; both are in the order of work. The contract (030-05) speaks only
of the tree when the transaction ends. A writer that decides each node
once, when everything about it is known, has neither cause.

## 1.2 PE: plan, then emit (first)

The idea is 006-28's NW (each node made once from the net change). I did
not find a better one. What I add is a mechanism exact enough to refute,
the proof's shape, and the checks.

**Terms.** The *live list* of a key node at a time: its live key klongs in
compare order, as pairs (compare value, pointer). A *virtual node*: a live
list that is not yet a node; it remembers the node of before that it
comes from (its base), or none.

**The mechanism.** By the Dag, at commit, under the write lock, for the
transaction's operations as `Db.putKvs` gives them today: sorted, one a
key. Two functions, one recursion over the tree, no loop over operations.

- **plan(x, ops)** for key node x and the operations in x's range gives
  x's virtual node. No times, no bitmaps, only lists.
  - A segment leaf: its live list at time i - 1 with the operations
    applied as on a sorted list. A put sets (cv, the new value). A delete
    removes cv. Operations with more segments go, grouped by cv, to the
    tree of the next segment (plan of its root); the entry is set to the
    root that comes back, or removed when that tree comes back empty.
  - An inner node: the operations are divided among its children by its
    live list; plan runs on each child that got some; then the children
    are *settled* (below), which gives x's new live list. The first
    entry's compare value is set to the empty key.
  - A root (the space root, a segment root): settled alone. Two nodes
    back: a new root above them. An inner root with one entry: its child
    is the root. Nothing left: the tree is empty.
- **settle**, at a parent, for its children's virtual nodes, left to
  right. Two steps.
  - Rebalance, on lists only: an empty virtual node is dropped; one with
    fewer than m entries is joined with a neighbour's list (today's rule
    M1: the left one first; an untouched neighbour is read now); a joined
    list of more than c entries is cut in two.
  - **emit** each virtual node. This is the only place that knows times,
    bitmaps, dead klongs, M and theta:
    - its list is its base's live list: nothing; the entry stays;
    - it has a base, and the difference fits (size at most M, dead klongs
      at most theta): the base gets, appended, a time klong of i, a bitmap
      if entries were removed, and the key klongs that are new or
      repointed;
    - else it becomes new nodes with fresh ids: one, `[time i, entries]`,
      for at most h entries, else two halves (more for a large batch).
      The base gets nothing; it is just not named at time i.
- **The plan** is the list of emit's decisions. It is the transaction's
  change: new nodes and added klongs. Refusals (the level bounds G and H,
  the ordinals) are tested on the plan; only then is it applied to the
  nodes in memory and given to the stream.
- **How it is checked.** As today: `contractcheck` on every traced
  transaction, the shape check (`shapeFaults`) for the fill, `treecheck`
  for Java against the model's plan. And one new, strong check: for a
  transaction of one operation the plan should be today's change klong
  for klong. I walked through the put into a full leaf under a full
  parent, the delete that empties a leaf (the stop node's bitmap, LE-b as
  "a new klong of the empty key and a bit for the old compare value"), a
  merge with a full parent and root collapse: emit gives today's klongs in
  each. The one exception I know is 024-22's MF1 (a root made and taken
  back within one delete), which PE never makes.

**What it removes from the code.** Of `Exec.lean` (1,175 lines) and
`Dag.java`'s write half (about 2,000 lines, `putKv` to `spaceSplit`):

- the take-back, `takeBackRoot`, `retarget`, `unlink` and `toPrev`,
  `madeFor`, `canTakeBack`: nothing made is unmade, nothing old is edited
  twice;
- every "in place" form: of the two splits, of the bitmap, of the merge's
  parent, of LE-b, of the top node;
- the key access path and the descents that rebuild it
  (`descendToHeight`, `descendToDepth`, `descendToSegmentRoot`,
  `newRootsMade`): the recursion holds the parent;
- the upward unlink as a rule (the climb, the stop node): a child that
  comes back empty is dropped from a list; LE-b is the rename of a list's
  head;
- the five forms of the merge's parent and the four of the bitmap: one
  function, the difference of two lists;
- the fuel: the recursion goes down the levels, which A4 makes decrease;
  and `outside` with MF1, since no root is made for a moment;
- most of the 30 `Bug` sites, which name states between operations.

My guess: a plan of 300 to 400 lines in the model, 600 to 800 in Java.

**What it removes from a proof.**

- `Mid` and `OpStep`: there is no state between operations. The
  statement is `WriterMeets` itself, proved by induction on the tree.
- Books B3, B4, B7, B8, B9, B12, B14 and the link books (`WcrLink`,
  `WmgFresh`, `WmgSplitLink`, `LinkLive`): they say what a half-made
  transaction may name or reach. `SNamed` stays as a fact of the tree before the
  transaction. R3 and ValOld have no place to arise. B1, B2, B5, B6, B10,
  B11, B13 become one-line facts of emit (a fresh id, one time klong).
- The "if x had these klongs" forms (`CasPre`, `CasPreG`, `CasPreO`,
  `CasPreH`, `CasPreD`): the virtual node is that hypothetical made a
  value, in one form.
- 030-16's F1 to F3 (dead klongs that name nodes two levels down or nodes
  taken back) cannot occur: no klong is ever written to a node that is
  not kept.

**The proof's shape**, three parts that do not know each other:

1. Lists: plan and settle keep the keys (the concatenation of the lists
   is the old one with the operations applied), the order and the kinds.
   Sorted lists and a recursion; the textbook proof of a functional
   B-tree (Mündler and Nipkow's verified B-trees in Isabelle are the
   nearest published; the join-based bulk algorithms of Blelloch,
   Ferizovic and Sun, "Just join for parallel ordered sets", 2016, and
   PALM, Sewall and others, 2011, are this batch shape).
2. One node: after emit, the node's live list at time i is the virtual
   node's list, its klongs before the time klong of i are untouched (the
   frame), the node's own rules (W1 to W4) hold. The tag's node algebra
   is the quarry.
3. The glue: 030-10's context lemma, used once per level.

My guess is 8,000 to 15,000 lines of Lean for the whole writer, deletes
and merges included, against 22,500 for the puts alone at the tag and
20,000 to 35,000 more estimated for the deletes (030-10). No trial is
behind my number.

**The cost against today.**

- Bytes, one operation a transaction: the same, by construction.
- Bytes, many operations a transaction: the same or fewer. Today a node
  that the transaction made and then changed is written with the klongs
  of the changes between (a bitmap in a new node); PE writes its last
  list only. A sorted load in one large transaction can cut a long list
  into nodes of c entries, not halves of halves; that could be a gain on
  the worst case, and I did not measure it.
- Commit time: one walk of the tree for the transaction, not a descent
  per operation and one more per merge. Against that, a live list is
  built for every node touched. My guess: within 10 % either way for one
  operation, faster for large transactions.
- Gets and scans: the format and the fill rules are today's, so the
  same.
- Reads of siblings for a merge: as today.

**Where I am guessing.** The Lean line count. The Java effort: the write
half is written again, and Java must match the new model node for node;
I guess two to three weeks with the conformance sets. That reclaim's
touch, `TransCheck`, eviction and the handles need nothing new (not
read). Memory in a very large transaction (a list per node touched, the
order of the dirty nodes themselves). The ids come in another order, so
the stream is not byte for byte today's: a new record format number, same
layout, as format 7 was.

**The cheapest checks that could refute it.**

1. Paper, an hour: find a rule of today's writer whose result is not "the
   last live list of each node, emitted once". I found none.
2. The model, one to two days: `plan` as an executable definition, run on
   the operations of the traces (195 traces, 318,900 operations).
   Refuted if `contractcheck` or the shape check gives one fault, if the
   bytes of any set are above 1.02 times Java's, or if a transaction of
   one operation differs from Java's change beyond the ids and MF1.
3. A proof spike, one to two days: the lemma of emit and the lemma of
   settle. Refuted if the two need more than about 2,000 lines, or if
   the induction needs a fact about a state that is not a tree.

**A variant, if Java should keep its loop over operations:** plan one
operation at a time on virtual nodes (a textbook insert and delete on
plain lists), and emit once at the end by the difference between each
node's first and last list. The same proof parts 2 and 3; part 1 is then
the standard one-key B-tree proof. More passes, the same bytes.

## 1.3 GS: ghosts, and structure transactions (second)

The fallback if PE's rewrite of Java is too much: it keeps today's
writer and its rules, and saves the proofs at the tag.

**The mechanism.**

- **The user's transaction changes the contents only,** by rules that are
  proved at the tag: every put, and the delete by a bitmap in a leaf that
  keeps a live klong. A delete of a leaf's last live klong leaves a
  *ghost*: the key's klong names the delete node that the transaction
  writes anyway. A reader takes a klong that names a delete node as no
  key. So the user's transaction never unlinks, merges or collapses, and
  nothing it makes is unmade: no take-back.
- **A structure transaction changes the shape only.** One step, at a time
  of its own, contents unchanged: a merge of an underfull node with a
  sibling (ghosts dropped), the removal of a child that holds only
  ghosts, or a root collapse. By the writer, in the same commit call,
  right after the user's record, from a work list of the nodes the user's
  transaction left under m; a step that leaves the parent under m puts it
  on the list. Written in the same append, so no sync more.
- **How it is checked.** The contract on each record, a structure record
  with no operations. The fill holds when the work list is empty, not
  after every record.

Sources: Graefe's ghost records and system transactions ("Modern B-tree
techniques", 2011; "A survey of B-tree logging and recovery techniques",
2012); B-trees with relaxed balance (Nurmi, Soisalon-Soininen and Wood,
1987; Larsen and Fagerberg, 1996), where updates and rebalancing are
separate steps and each rebalancing step is proved alone; the Bw-tree's
structure changes as steps of their own (Levandoski, Lomet and Sengupta,
2013).

**What it removes.** The take-back (17.6 % of the old tree's proof lines;
48 % of them name it), the upward unlink of nodes that the transaction
made, B4, B9, B14, the link books, R3. It keeps the loop over operations,
the in-place forms, the key access path, the fuel and all of today's
rules. Its merge is 030-16's `Sound.mergeOne`, `mergeTwo` and
`mergeParent_spec`, whose open piece was the link book between steps:
alone in a transaction, a step starts clean.

**The cost.** Bytes: a record's header (37 bytes) for each structure
transaction, and the merged node is written once more, with the change
of the user's time, before it is replaced. Puts: nothing. Deletes: my
guess is about 1.1 times; 026-21's commit line reports 1.12 for a design
I take to be near this. Scans meet ghosts until the purge. The read
proofs change: the contents are the live klongs that are no ghosts, so
the scan's proof gets a filter (my guess: 1,000 to 2,000 lines). A crash
between the user's record and its structure records loses the work list:
the node stays underfull until it is next changed, so the fill is no
longer an invariant of every start.

**Where I am guessing.** That a time of its own is free: the Pub API's
times are clock times (`Connection.setLookupTime`), so I think a
structure transaction needs only a later time; not checked in the Core.
The bytes. The size of the change to the read proofs.

**The cheapest check.** In the model, on the delete traces: today's
writer with each structure step moved to a transaction of its own; count
the bytes and the ghosts. Then list which lemmas of the tag hold
unchanged.

## 1.4 CC: the commit check (third; good with either)

Not a simpler writer: a change of who must be right.

**The mechanism.** At commit, after the writer has its change and before
the record is appended, a small checker walks the tree before and after
along the changed nodes and the operations, and tests the contract there:
the changed nodes' own rules, the kinds, the order, the frame, and that
the contents differ by exactly the operations. Every changed node must be
met by the walk; what the walk does not enter is unchanged by the frame.
A failure refuses the transaction (with PE the plan is data, nothing was
changed yet) or stops the database before the record is written (today's
writer: memory is changed, the stream is not). Proved in Lean: the check
passes and the tree before meets the invariants, so the transaction
meets the contract. `checkTx_sound` is this for the whole tree; the
local form adds the context lemma for a set of nodes.

**What it gives.** "No record on the stream breaks the contract", for any
writer, today's too, with assumption 1 (the writer, 2,000 lines of Java)
replaced by "Java's checker is the Lean checker" (200 to 300 lines by my
guess, tested on the traces by its verdicts and by 030-05's six faults). It
does not prove that the writer never fails the check; that stays tested,
as in 030-10.

Sources: translation validation (Pnueli, Siegel and Singerman, 1998);
certifying algorithms (McConnell, Mehlhorn, Näher and Schweitzer, 2011);
CompCert's validated register allocation (Rideau and Leroy, 2010), an
unproved heuristic with a proved validator.

**The cost.** No bytes. Commit time: one more walk of the changed nodes.
My guess is 10 to 30 % of the tree's part of a commit; I do not know the
tree's share of a commit.

**The cheapest check.** Profile a commit for the Dag's share. Write the
local check in Lean and run it on the 29,735 traced transactions: its
verdicts must be `contractcheck`'s, the six faults found.

## 1.5 FR: fewer kinds of things in a node (fourth; only with PE)

Three format changes that shrink the node's algebra for readers and
writer alike. Each touches the read proofs, so none is worth it alone.

- **One kind of edit.** A delete in a node as a klong "this compare value
  has no pointer from here on" (klong type 2 is unused), not a bitmap over
  klong indexes. A node's live list is then one fold: the last klong of
  each compare value. The bitmap's rules (W2 to W4), `bitsOf`,
  `lastBitmap`, the union and the limit of 62 klongs a node go. Cost: a
  bitmap is cheaper only when one transaction deletes two or more klongs
  of one node, and emit then often writes a new node anyway. A guess.
- **No rename of the empty key.** A reader that finds no klong at or
  below its key takes the node's smallest live klong. LE-b, 4.8 % of the
  old proof lines, is then nothing at all. In PE it is one rename, so the
  gain there is small.
- **One rule for a full node:** its last list in pieces of at most h.
  PE's emit is this already.

## 1.6 Looked at and dropped

- **Path copying** (every change a new node up to the root; the classic
  append-only B-tree). The simplest writer to prove, and in today's
  format (a node with one time klong). Refuted by 006-19: a put writes
  867 bytes at 10M keys; a copied path through four segment trees is 2
  to 4 KB by my estimate (six or more nodes of 32 + 16 n bytes). It is,
  though, part 1 of PE's proof.
- **A shape decided by the keys alone** (node borders by a hash of the
  key: B-treaps, Golovin 2009; Merkle search trees, Auvolat and Taïani
  2019; Dolt's prolly trees). No fill rule, no sibling choice, no
  cascade. But node sizes are then random, against a limit of 62 klongs
  and a worst-case aim, and the contract needs no shape, so the proof
  gains nothing that PE does not have.
- **Rebuilding a subtree when it is too thin** (Overmars 1983; scapegoat
  trees): pauses, and more bytes than a merge; 024-11 measured the same
  kind of thing for reclaim's rebuild.
- **A log-structured index** (sorted runs and merges): easy proofs,
  another database.


# 2. My recommendation

1. Do PE, model first: two days for `plan` in Lean on the traces and for
   the two lemmas (checks 2 and 3 of 1.2), with the refusals stated
   there; no Java before both pass.
2. If they pass, the model's writer is replaced by the plan and proved
   whole; Java's write half is rewritten to match it, under a new record
   format number.
3. Add CC when its cost is measured and small: it holds for any writer,
   and it is the safety net while Java is rewritten.
4. Keep GS as the fallback if the rewrite is too much for 2026.6: it
   saves the tag's proofs, at about 1.1 times the bytes on deletes and a
   change to the read proofs.
5. Leave FR until PE stands. What I would not do: prove today's loop
   further; its books come from its order of work, not from the problem.


# 3. Afterwards: comparison with 026-17 to 026-22

Written after sections 1 and 2 were committed (18b520db); they are left
as they were. Read then: 026-17 (the result), 026-18, 026-19 (the
result), 026-20, 026-21 (the result and section 1), 006-28, sections 5.1
and 7.1. 026-22 was not in the repository (main at b6535736).

**The main point: PE is not 026-20's "net change", and it has never been
tried.** 006-28's NW is "each node made once, level by level". 026-20's
design 1 kept the name and only the first half: the last operation of
each key, then applied one key at a time by today's writer. 026-21 found,
rightly, that Java does that already and that it leaves the take-back
between different keys. That finding is not about NW. PE (NW with a
mechanism) has no take-back between different keys: no node exists
before its parent's level is settled. 026-17 says "NW. No spike of it
here"; I found no later one.

- **026-17, MT's trial.** GS is MT with one change: a ghost where MT
  leaves an empty leaf. MT's trial is the evidence that I guessed at, and
  it corrects me twice. Bytes: 1.05 to 1.06 over all, 1.15 to 1.17 for
  mass deletes, where I guessed 1.1 on deletes. And "nothing is unmade"
  holds for nodes only: `toPrev` stays in the user transaction's split
  (step T7), which I missed. MT's scan finding (25 empty leaves side by
  side after a mass delete) is what my ghost was for; a ghost keeps "a
  live klong in every node" true but the scan still crosses those
  leaves. MT's writer is not smaller than today's (86 lines fewer), as I
  wrote of GS. Mine is no better than MT.
- **026-18, main transactions and subtransactions.** Better than GS
  where they differ. Readers see only the times that end a group, so no
  reader changes and my ghost is not needed; a start drops a group that
  did not end, so the lost work list of 1.3 cannot happen. GS should be
  read as MT under 026-18. PE needs none of it: one transaction, one
  time, one record, as today.
- **026-19, the proof trial.** Its verdict (MT not clearly simpler to
  prove, stay) was reached under the old statement, with the fill in the
  invariant: the holes and their frames (`FrameW`, `FrameUser`, about
  6,000 lines each) and the open case (`MergeFullLive`) are all about
  the fill. A day later the contract took the fill out of the statement
  (030-05). So, by my reading, the trial's "no" does not carry over to MT
  under the contract; that has not been tried. Its other lesson does
  carry over, and it speaks for PE: the lines went to the full node's
  cascade in each of its forms, which MT keeps and PE folds into one
  function.
- **026-20, the two designs.** Design 1: see the main point. Design 2,
  step times, has PE's aim ("the writer never changes or drops a fresh
  node") and reaches it by another road: it adds times until the rule
  holds; PE adds no node until the rule holds. Step times keeps today's
  code and prunes it; PE writes the write half again. Step times changes
  the time klong (48 + 14 bits), the lookups (the end of T), the top
  node (one a step), the time arithmetic; PE changes none of them. The
  diagnosis is the same; my 1.1 had its start from my brief, which
  carries 026-20's words.
- **026-21, the study.** It measured what I only argued. Step times with
  the delete in pieces: no take-back, the contract at every step, 1.12
  times the bytes over the traces and 1.41 for sorted loads in large
  transactions, "the splits in place, which step times forbid, are what
  makes large sorted transactions cheap today". PE keeps that cheapness
  by construction: a split in place is today's way to reach a node's
  last list, and emit writes the last list (section 4 counts it). Where
  step times is better than PE: it is measured; it is a smaller step
  from today's Java; its proof is today's rules piece by piece. Where PE
  is better: no cost in bytes, no change of the time klong, no "check
  before each piece", which 026-21 names as a new thing that Java cannot
  do as the model does; and it removes the forms of each rule, not only
  the take-back (026-21: the model writer 13 % smaller, the deletes'
  proof a third smaller; my guess for PE is a writer a third of today's
  and a proof a quarter, with no trial behind it). Where PE is worse:
  every writer proof of the tag is void but the node algebra, and Java's
  risk is that of new code.
- **006-28, section 7 (MT)** agrees with GS on the sources' idea; it says
  "MT in place of NW, not before it; and a spike before either". MT got
  its spike and its proof trial; NW got neither.
- **CC and FR** have no counterpart in 026-17 to 026-21. But CC exists
  in part, and I should have found it: `TransCheck` (030-09, 587 lines,
  test-only, on in the unit tests and f-tests) is Java's local check of
  the contract, and 030-04, section 3.4, already says "production only
  after its cost is measured". What CC adds to it: the Lean proof that
  the local check gives the contract (TransCheck's own list of what is
  "not local, so not checked here" is that proof's work list), and the
  switch. My 200 to 300 lines were too few.

**What I would change in section 2 after reading.** Lines 1 to 3 stand.
Line 4: the fallback is not GS but 026-21's (b), step times: it is
measured, and it removes the splits in place too, which GS and MT keep;
its price is 1.41 on sorted loads and the time klong. Before Frans takes
(b), PE should get the two days that MT and step times each got: in
026-21's harness (`lean/study/`, 288 traces, B-new and B-all), a third
writer beside today's and the step writer. If PE passes, it gives what
(b) gives without (b)'s costs; if it fails, (b) is the choice and
nothing is lost but the two days.


# 4. A count on Java's traces, made after section 3

A throwaway count for 1.2's claim on bytes
([23-second-opinion/emitcount.py.txt](23-second-opinion/emitcount.py.txt),
Python, 85 lines). For every key node that Java made or changed in a
traced transaction (the `KN` lines), it compares the klongs that Java
added with the klongs that emit would add to reach the same last live
list: for an old node a time klong, a bitmap if a compare value left, and
a klong for each entry new or repointed; for a new node a time klong and
its live klongs. Java's traces of 17 November: the small set (70
traces), drain (110), reclaim (15), medium (27).

- **Emit never adds more than Java:** 0 of 854,867 nodes.
- **Old nodes in transactions of one operation:** 8,790 nodes; the same
  klong count in all but 4, where emit has one fewer (a klong that the
  same delete added and then deleted).
- **Old nodes in transactions of many operations:** 441,256 nodes;
  980,341 klongs added by Java, 977,869 by emit.
- **New nodes:** 404,821 nodes; Java's hold 1,745,391 klongs, emit's
  1,687,963 (3.3 % fewer). Java's new nodes are born with dead klongs: a
  klong repointed by a later operation, a klong that a take-back
  retargeted and a bitmap then deleted, and, in a put's split too, the
  replaced klong beside its replacement.
- **Bytes of the key nodes written** (32 + 16 n for each node changed):
  emit's are 0.985 of Java's on the small set, 0.982 on drain, 0.994 on
  reclaim, 0.997 on medium.

What it shows: on the shapes that Java made, writing each node's last
list once costs no more than Java's klongs for any node, and one
operation gives Java's klongs. What it does not show: PE's own shapes
(settle may cut and join other nodes than today's loop in a transaction
of many operations); later effects (fewer dead klongs, later splits);
value nodes and top nodes; sorted loads in large transactions beyond the
small set's `bulk` family (0.98 there for new nodes; 026-21's own bulk
traces hold operations only). And one thing to check before PE drops
them: whether anything reads a new node's dead klongs (Rule A's test
over dead pointers, reclaim's touch).


# State

2026-11-18. Done: sections 1 and 2 committed (18b520db) before 026-17 to
026-22 were read; then section 3; then the count of section 4.

- Branch `026-23-second-opinion`, in the agent's clone. No Java or Lean
  was changed. One count was run (section 4), reading Java's traces of
  17 November; no build, no timing run.
- For Frans to decide: whether PE gets its two days in 026-21's harness
  before the choice of (b).


# Log

2026-11-18. Created the item; sections 1 and 2 (an agent of coord-1118),
committed before 026-17 to 026-22 were read. Then section 3, the
comparison, and section 4, a count on Java's traces. Done.

2026-11-24. Status set after the release (lead-1124).
