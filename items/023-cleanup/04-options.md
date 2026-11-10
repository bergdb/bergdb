# 023-04. The options

Created 2026-11-10 by Frans Lundberg. Status: open.

The first phase of 023's solution: the building blocks a cleanup can be
made of, the options as combinations of them judged against 023-02's
requirements and 023-03's tests, the design decisions they leave open,
and what phase 2 should do. It carries phase 1 of 020-30 (its section 4
and the helpers 020-30-01 to 04) into 023, checked against the code and
rewritten. No code of a fix is made here.

Names: building blocks have two letters (UP, LE, RC, ...; section 2);
options keep 020-30's letters (A, B, C, D; section 3); open decisions are
X1 to X11 (section 4); questions for Frans are Y1 to Y10 (section 7).
Cite them as "023-04, X1". They are not 023-02's R and F, 023-03's T, M,
C and Q, nor 020-30's F1 to F7.


## 1. Purpose and inputs

### 1.1 What this is for

023-02 says what a solution must do (R1 to R27) and 023-03 how it is
tested (T1 to T12). This subitem says which mechanisms can do it, alone
and together, what each costs and risks, and what is left for Frans to
decide. Phase 2 makes full proposals and prototypes of the chosen ones
and judges them by 023-03's tests (section 6).

### 1.2 Inputs

* 023-01 (how the Core works), 023-02 (R1 to R27, F1 to F12) and 023-03
  (T1 to T12, M1 to M14, C1 to C12, Q1 to Q7, and today's numbers).
* Frans's answers (023-02, section 7.2; 023-03, Q2):
  * F10, 10:30: a change of the record format is acceptable in 2026.4.
    F9 (a), 10:30: 2026.4 refuses the databases of earlier releases. So
    no option here needs a second rerun path for format 5 records, nor a
    cleanup of what 2026.3's databases already hold.
  * F5 and Q2, 10:38: "I agree in general. However, it depends on how
    difficult Strict is. If we find a good Strict solution, let's go for
    it. But Bounded is ok. For Strict, it is enough to eventually, after
    one or several reclaims, to get the original Hello-world resource
    consumption." So 023-03's bounded allowance is the gate, and strict
    may come lazily, from reclaim (RB, 2.6; X3).
  * F2, 10:41: "Yes, it should cover every version that has ended." So
    R7 holds as written: old versions of overwritten keys, node versions
    replaced by splits, shadowed klongs and internal keys too.
  * F3, 10:44: "At every available time; this is what we want." So R9
    holds at every available lookup time, and the unlink must happen at
    the delete's own time; reclaim alone cannot give it (B).
  * F1, implied by F2 and F5 (the coordinator, 10:44): dead and shadowed
    klongs in nodes that still hold live keys go too, eventually, after
    one or more reclaims (RB's compaction, 2.6; X4).
  * F7, 10:49: the user's writes drive the cleanup, and an explicit
    maintain() is good too: "repeatedly calling maintain() must
    eventually release resources so a database with only one
    hello-world entry will consume about as much as a fresh hello-world
    database" (MT, 2.12; 3.7; X11).
  * Open: F4, F6, F8, F11, F12.
* 020-30, section 4, and its helpers: 020-30-01 (reclaim), 020-30-02
  (Frans's 2012 intent and prior art), 020-30-03 (the upward delete's
  mechanics), 020-30-04 (format, Lean, C, tests). 021-25 with its fix (a)
  (branch `021-25-fix-a`), 021-28 (branch `scan-deleted-keys`).
* The code of `main` at `9acf5c38`, whose Java is the candidate's
  `03ce6ec`; the Lean model's assumptions (sis-model.md, 3.4 and 15.2).

### 1.3 What was checked, and how

Code places are file:line on `main` at `9acf5c38`, in
`java/src/bergdb/dag/` and `core/`. Read for this subitem: every place
that relies on a klong above the leaf being a lower bound of its child
(X1), the splits (`Dag.handleFullNode`, `KeyNode.firstAndSecond`), a node
made and emptied in one transaction (X5), the startup rerun and what a
clean close leaves (section 5), eviction and the node table (X6).

Probes in package `bergdb.core` against a build of `main`, outside the
repo (`/Users/f/fl/bench/2026-11-10/o23/probe`): counts, not times. They
walk the tree at the latest time and count the key nodes reachable,
those with a live key below them (what option A would leave), the root
levels with a single live child (what RC would take), and the klongs
that are not live; one closes a database and counts what the next start
reruns; one follows the klongs through reclaim's iterations. The numbers
are in section 8.


## 2. The building blocks

Each block: what is done, when, by whom, how it is checked; then its
cost, what readers see, and what the rerun and the model need. "The
rules" are the Lean model's assumptions A1 to A5 (sis-model.md, 3.4) and
TREE, A6' and A-COPY (sis-model.md, 15.2), which A2A3Check2 and the trace
checker check on every transaction of their runs (level2.sh,
conformance.sh). Every block below meets them as far as reading the code
shows; phase 2 runs the checkers.

### 2.1 UP, the upward unlink

**What.** A delete that leaves a key node with no live KEY klong at the
transaction time tt does not write that node. It deletes the parent's
klong to it instead, and so on upward while a node is left with no live
klong; the first node that keeps a live klong gets the delete bitmap.
Across segment trees too: an emptied segment root takes with it the
klong of the segment leaf above, a segment of a longer key. This is
Frans's rule of 2012, "If lastVersion is empty, remove from parent"
(020-30-02, section 1), applied to every emptied node, not only to a
full one; with it, `Dag.timeSplit`'s comment "but not empty" becomes
true.

**When and by whom.** In the deleting transaction, by `Dag.setValue`'s
delete (`appendDeleteKlong`, Dag.java:899), at once for each delete, so
that the transaction's later operations see it: they search at tt, with
the transaction's bitmaps.

**How.**

1. The emptiness test, in `appendDeleteKlong`'s loop over the node's
   klongs: the node is empty after the delete if every KEY klong's bit is
   in `union` (Dag.java:955). A delete sets the bits of every klong of its
   compare value, so a KEY klong outside `union` is a live compare value.
   No extra pass.
2. Not empty: as today, a bitmap or a split (Dag.java:958 to 975).
3. Empty: no bitmap, no split. The node loses any klongs of tt
   (`toPreviousState(tt - 1)`, as a node replaced by a split does,
   Dag.java:1090) and leaves D if it got dirty in this transaction only
   (`keyNodeReplaced`, `Db.endOfTrans`, Db.java:1503). If it got dirty in
   an earlier transaction it stays in D and is written: lookups at times
   before tt need that state. Then step 1 in the parent, found as the
   splits find it (`pd.getParent(depth)`; its klong in `keyAccessPath`).
4. The parent is a segment leaf (the node was a segment root): delete the
   segment's klong there. `setNode` treats a deleted segment as absent
   already, and a later put makes a new segment tree (Dag.java:858 to
   878).
5. The parent is an inner node and the klong is not its smallest live
   one: delete it. The key range joins the left sibling's, whose keys are
   all below it: a later put there finds the sibling (`searchLte`).
6. The klong is the inner node's smallest live one: LE (2.2).
7. The node was made by this transaction (a split's half): X5.
8. The space root has no parent. With RC (2.3) an inner root never
   empties, as it collapses first; without RC, an inner root left with no
   live klong is replaced by a new empty segment leaf as the new super
   root (`TopDs.newSuperRoot`, as time-split-2 does).

`Dag.dirtyNodeBound` (Dag.java:477), Db's check before the go point
(005-31), counts a delete as one klong in its leaf (Dag.java:500). The
climb's bitmap lands in an ancestor that the bound already counts as
dirty; LE's klong, RC's top node and the splits they can cause must be
added: at most two klongs a level and one top node a delete.

**Checked by** T1 to T5 (what is left and what it costs), T6 and T7 (no
lookup changes; restarts, crashes, readers), A2A3Check2 and conformance
(the rules: A2, as the emptied node gets no entry; A5, as nothing comes
back).

**Cost.** The climb runs only when a node empties, and a node empties
once: O(1) amortized a node made, at most the path's levels H for one
delete (a long key with tail segments of its own). Fewer bytes than
today: an emptied node is not written again, and no later touch reaches
it (020-30-01, section 3).

**Readers.** A bitmap of tt in an inner node is what leaves have today:
readers at earlier times stop at the time klong of tt (KeyNode's class
comment). Readers before tt still reach the unlinked node through the
klong as it was; after the cut no available time reaches it.

**The rerun.** A function of the delete and the state at tt - 1 (A1), so
a start reruns it as any delete; it is part of what a record of format 6
means (section 5).

**What it leaves**, in the probe (section 8.4, 023-03's shapes at N =
100,000, R forever): 1 node in "after", "before" and "long", as the twin;
5 in "inter" and "hashed", a path of single children down to "/a.txt";
4,031 in "sparse" against the twin's 263.

### 2.2 LE, the leftmost child of an inner node

Every put relies on an inner node having a live klong at or below any key
routed to it, else `Dag.checkFound` (Dag.java:835) fails the database
with "corrupt data". So UP cannot simply delete an inner node's smallest
live klong, and that is the common case: a FIFO, a queue's head, a
time-ordered index (020-30-03, section 2). Four ways; X1 compares them.

* **LE-a, relabel down the left edge** (020-30-03's A-relabel). The parent
  gets a new klong with the emptied child's compare value, pointing to
  the next child, and that child's own klong is deleted. If the next
  child is an inner node, its smallest klong is above the new bound, so
  the same is done down its left edge, one node a level: O(H) nodes
  changed, off the delete's path, once per emptied leftmost child.
* **LE-b, the empty key first** (new here). Every inner node has
  `Klong.EMPTY_KEY`, the compare value 0 (Klong.java:79), as its first
  klong, as the roots of space splits have today (Dag.java:1139, 1256,
  1281). One rule changes: a space split of an inner node gives its
  second half the empty key as its first klong, while the parent gets
  the second half's first compare value as today (`firstAndSecond`,
  KeyNode.java:1276; Dag.java:1308 to 1323). Then an emptied leftmost
  child is replaced by the next child with one new klong of the empty key
  in the parent, which shadows the old one as a time split's klong does,
  and the next child's own klong is deleted. Nothing below changes: the
  next child's first klong is the empty key already, or it is a leaf.
  The empty key is a lower bound of every key, so every reader of today
  reads such a tree right, 2026.3's too.
* **LE-c, relax the rule.** An inner node's smallest live klong covers
  every key below it, as a B+-tree's leftmost pointer does. No relabel;
  the routing changes (X1).
* **LE-d, keep** the empty leftmost child linked (020-30-03's A-keep).

### 2.3 RC, root collapse

**What.** A root that is an inner node with one live klong is replaced by
its only child, again while the new root is so. The space root through a
new super root (`TopDs.newSuperRoot`, TopDs.java:61; a second new root in
the same transaction updates the first, TopDs.java:64 to 73); a segment
root through a new klong of the same compare value in the segment leaf
above, which shadows the old one, as time-split-1 does for a segment
root.

**When and by whom.** In the deleting transaction, at the end of UP's
climb (and of MG's), on the roots of the segment trees on the path.

**Why.** UP never lowers a tree, and the height is a factor of every
bound (R9, R10). With RC the hello-world shapes end as their twins: in
the probe, "inter" and "hashed" go from 5 nodes to 1 (section 8.4). In
021-25's FIFO of 1,024 live keys after 100,000 transactions, A leaves 123
nodes in 6 levels, the top three single children; RC leaves 121 in 4
levels, against the twin's 117 in 3 (section 8.2).

**Needs** a new root whose smallest live klong covers every key, as its
parent's klong did: true with LE-a and LE-b, where the left edge holds
the empty key, not with LE-d, where a root keeps an empty leftmost child
beside its live one.

**Cost.** A top node, or a klong, a level lost; a level is lost at most
once for each made. Readers at earlier times find the old root through
the older top node (`TopDs.findSuperRootAtTime`).

**Checked by** T1 and T2 (M4, M6, M7 against the twin, rows "inter" and
"hashed"), T4 (the queue's height), the rules (A5: the child was
reachable; A-COPY: its pointer is copied from a current node).

### 2.4 MG, merging underfull nodes

The multiversion B-tree's rule (Becker et al. 1996; 020-30-02, section
2): every current node but a root keeps at least m live klongs. Frans
planned it in 2012 ("Merges are made when the current version of a node
shrinks because of a delete") and postponed it (020-30-02, section 1).

**What.** When an operation leaves a current node X, not a root, with
fewer than m live klongs, X is merged with an adjacent sibling S under
the same parent P: the next live klong's child, or the previous one's if
X is the last. If the two hold at most B/2 live klongs, one new node N
holds them all, sorted, as a last version at tt; else two new nodes
share them (a redistribution). In P, the left one's compare value gets a
new klong to N, which shadows the old one, and the right one's klong is
deleted (with two nodes, a klong for the second at its first compare
value). X and S are replaced: they lose their klongs of tt and serve the
times before tt, as a node replaced by a split does. P has lost a klong
and may be underfull in turn: the same up the path, and RC at the root.
With LE-b, N's first klong is the empty key when it is an inner node. An
empty X is UP's case, not MG's.

**When and by whom.** In the deleting transaction, after each operation,
bottom-up on its path, by the Dag. RB (2.6) does the same merges lazily,
in reclaim's touch; X3 compares the two.

**Thresholds.** m = B/4 (7 at B = 30, 2 at B = 8), and a merged node at
most B/2: a time split keeps at most B/2 klongs and a space split makes
halves of about B/4 to B/2 (`handleFullNode`, Dag.java:1071), so a node
between a merge and a split has a gap of about B/4 operations, and the
restructuring is O(1) amortized an operation, as in B-trees. Constants
for phase 2 to set from T2's "sparse" row and T10.

**Bounds.** At every time, every reachable node but the roots has at
least m live klongs at that time, as each node's count is the one its
last change left, and that change ran MG. So: reachable nodes O(n / m)
for n live keys; height O(log_m n), H in the live keys (R10's wish); a
scan of n KVs O(n / m + H) key nodes; the stream's index within a
constant of the twin's (R12 (b)). In "sparse", not within 10 nodes of
the twin: its nodes keep m to B/2 live klongs, so about 2 to 3 times the
twin's count (3.3); RB packs to its fill instead (2.6, Y5).

**Cost.** A merge reads the sibling, which may be a stream read in the
writer (the eviction may have taken it), writes one or two new nodes of
at most B/2 klongs (32 + 16 x 16 = 288 bytes) and two or three klongs in
P, which is dirty anyway. `dirtyNodeBound` adds a sibling and up to two
new nodes a level. Amortized O(1) a delete; O(H) for one.

**Risks.** The most cases of any block: merges of nodes split or made in
the same transaction (X5), a sibling made by a split of this transaction,
segment roots (never merged: a root collapses instead). Reads in the
writer under the write lock (P1: one node a level, at most H a delete).
Thrash at the thresholds, if they are too close.

**Model and checks.** No new kind of change: N is a new node, X and S are
replaced, the copied pointers come from current nodes (A-COPY), each
child keeps one current parent (TREE). A2A3Check2 and conformance check
it; T2's "sparse" row measures it (M4 against the twin).

### 2.5 DC, compaction in the deleting transaction

**What.** A delete that leaves a node holding live keys with more klongs
that are not live (deleted or shadowed) than live ones replaces the node
by its last version at tt (a time split, `lastVersionGivenDel`,
KeyNode.java:1091) instead of adding a bitmap to it. **When:** in the
deleting transaction, by `appendDeleteKlong`. **Bound:** a node keeps at
most as many dead klongs as live ones plus a node's put history, not
zero. **Cost:** a new node and a parent klong where today a bitmap goes
in; the node is written by the take in both cases. Overlaps MG and RB,
whose merges and rebuilds are compactions. Listed for completeness (X4);
not recommended.

### 2.6 RB, reclaim rebuilds what it rewrites

Reclaim's touch visits every node reachable in its range at the step's
time ts and makes each dirty, so that it is written again as it is, with
its history (023-01, 9.3). RB makes it write a compact shape instead.
It is how Frans's strict reading can come "after one or several
reclaims" (10:38), and how the klongs of every ended version go (F2,
R7).

**What.** As the touch leaves a node for good (in post-order, after its
last child in the step's range), it rebuilds what it has just passed,
with replacement nodes, never in place:

1. **Compaction.** A node that holds a klong not live at ts (deleted,
   shadowed, or a bitmap) is replaced by its last version at ts, as a
   time split makes it (`KeyNode.lastVersionGivenDel`, `Dag.timeSplit`):
   the klongs of ended versions, deleted and overwritten (K3, K7), and
   UP's deleted klongs in parents, leave the current tree. A new klong in
   the parent shadows the old one.
2. **Merges.** Adjacent children of one parent with fewer than m live
   klongs each are merged into new nodes of at most f B live klongs (MG's
   rule, 2.4, done lazily); the parent gets a klong for each new node and
   loses the others. With LE-b, an inner one's first klong is the empty
   key.
3. **Root collapse.** A root left with one live child collapses (RC,
   2.3): a segment root in the step that leaves it, the space root in the
   iteration's last step.

The old nodes serve the times before ts and go with the cut after the
next one. In place would give a read admitted before a cut a wrong
answer instead of `LookupTimeNotAvailableException`, and break lemma M
(020-30, section 4.4; 020-30-04, section 4). A node that needs none of
this is made dirty, as today.

**When and by whom.** In each reclaim step's internal transaction, by
the touch (`Db.touchRange`, Db.java:2944; `Reclaim.step`,
Reclaim.java:540): so only with a finite R, and each node once an
iteration. Its work is the touch's, charged to the iteration as today
(Reclaim.java:656).

**Bound.** One iteration after the last write in a range, no reachable
node there holds a klong that is not live, every node but a root has at
least m live klongs, and no root has a single child: the twin's shape,
up to the fill f. Between iterations, what one span's writes changed.
UP and RC keep the bounded allowance at every time; RB takes the residue
to strict within an iteration or two, and the cut takes its bytes two
cuts later.

**The rerun.** The touch is not stored and not rerun today: D is rebuilt
from the stored ids (`DbStarter.canonicalNode`'s comment, DbStarter.java
474 to 486). RB makes nodes whose ids later records name, so a start
must rerun the touch, at its time, over its range: the record must mark
a step and give its range (the row's `lastKey` before and after, and
whether it reached the end; Reclaim.java:674 to 676). A field of format
6. The rebuild must be a function of the tree, not of what is resident:
it reads through the writer's follower, as the touch does.

**Step boundaries.** A node on the edge of a step's range is passed again
by the next step, which leaves it for good and rebuilds it then. A merge
needs both siblings in one step: an underfull node at a step's end
waits for the next iteration, or merges with its left sibling. For phase
2.

**Fill.** f between 1/2, as a time split's last version, which the next
put does not split at once, and about 2/3, as a twin built by random
puts (about 17 klongs a leaf in the probe's hashed twins, section 8.3).
Denser nodes are fewer and split sooner after puts. A constant for
phase 2, from T2's "sparse" row and T10.

**Cost.** The touch writes every reachable node of its range once an
iteration today; RB writes them as new nodes, fewer and smaller, plus a
klong in each parent, which it rebuilds in turn, and a new top node an
iteration: about the bytes of today's touch, more work in the writer for
the last versions and the merges.

**Risks.** The touch becomes a writer of the tree, the largest change to
reclaim of any block. The cut's safety (every node reachable from tEnd
on is at pCut or later, or dirty; Reclaim.java:52 to 55) must be argued
again for replacement nodes: they are new, so dirty, and the old ones
are unreachable from ts on. The touch's rerun is new code in
`DbStarter`. The step's charge and reserve (`DEFAULT_STEP_RESERVE`)
count other bytes. The trace export and the model's touch steps
(`touchOf`) meet a touch that adds nodes, as a step's own puts do today
(020-30-04, section 4: no change of SIS expected; to check).

**Checked by** T1 and T2 with the strict allowance after the drive (C3
to C5), T2's "sparse", T4's M4 against its twin, T7 (restarts at the
drive's cuts: the touch's rerun), StreamDigest's modes, ReclaimStress
and ReclaimReaders.

### 2.7 TU, reclaim's unlinking

**What.** The touch, as it leaves a node in post-order, unlinks it if it
found nothing live below, as UP does (020-30's B1). **Needed for** what a
transaction leaves linked: nothing, with UP, LE-a or LE-b and X5 (a); and
the trees that 2026.3 wrote, which 2026.4 refuses (F9 (a)). So TU is
needed only by option B. Its rerun is RB's.

### 2.8 SE and TE, the ends of scans and of the touch

* **SE**, 021-28's `GetMany.endKey` (branch `scan-deleted-keys`): a
  forward scan ends when the klongs it follows are past its range's end,
  live or deleted; the Pub API's index scans and listings set it. Read
  path only, no change of bytes; reviewed. Alone it fixes U17-1 and not
  U16-1 (021-28). With UP, a scan past its range follows only the path
  to the next live key; SE still saves that path and the read of that
  key's value (U16-9).
* **TE**, 021-25's fix (a) (branch `021-25-fix-a`): the touch ends at its
  range's end, not at the next live key. With UP, the touch past its
  range follows O(H) nodes; TE keeps a step's dirtying within its range.
  Changes which nodes get dirty, so the bytes of the 4 `l3-*`
  configurations of StreamDigest, not the format (today's touch is not
  rerun; with RB, TE is part of the touch that is).

### 2.9 RD, a range delete

One operation that deletes every key of a range and unlinks whole
subtrees (2012-06 notes: "A range-delete operation could possibly be
significantly more efficient"). For the Pub API's `deleteIndex` and a
directory's delete. A new Core operation (P12: Frans decides), a new kind
of record content and rerun, and a new rule for the STM, which hashes
single keys (`stmRecordKeys`, Db.java). UP gives the bounds without it:
the cleanup thread's 100 deletes a transaction (`CLEANUP_KEYS`) unlink as
they go.

### 2.10 MR, the memory of unreachable nodes

An unlinked node, once written, is not pinned (`Residents.isPinned`,
Residents.java:274: the super root, and the canonical objects of D and
of the record being written), and no lookup from the delete's time on
follows it, so its CLOCK bit stays clear and eviction takes it at its
first pass after the resident bytes reach the budget (`Cache3.evict`,
Cache3.java:332; `Eviction.detachable`, Eviction.java:305). After a
restart it is never loaded. Below the budget it stays, as any cached
object does. Three ways (X6): **(a)** as today; **(b)** at the end of a
transaction, evict at once the clean objects of the nodes it unlinked or
replaced (`Cache3.evict` takes one handle; readers that hold the object
finish with it, later ones load the version from the stream, which is
there until the cut); **(c)** after each cut, a pass in bounded steps
over the node table for objects below pCut.

### 2.11 AP, the writer's key access path

`KeyAccessPath`'s arrays keep the length of the longest path ever
followed, the touch's included (K16; KeyAccessPath.java, `clear()` nulls
the used entries only). AP: `clear()` gives back arrays far longer than
the last use (say 4 times, and over 1,024 entries). A few lines, no
change of the stream; R4 and R14 ask for it.

### 2.12 MT, an explicit maintain()

Frans, 10:49 (023-02, F7): the user's writes drive the cleanup (P3), and
"The explicite call to maintain() is also good. Feel free to add it if
needed to test the solution. That makes the 'eventually' well-defined;
repeatedly calling maintain() must eventually release resources so a
database with only one hello-world entry will consume about as much as
a fresh hello-world database."

**What.** One call does a bounded part of the maintenance that user
writes carry today, in internal transactions under the write lock:

1. **Reclaim.** If no iteration runs and a quarter of R has passed since
   the last one began, begin one without today's other condition, a
   stream grown by twice the startup distance (Reclaim.java:460 to 469),
   which an idle database never meets. Then one step, with its rewrites
   and its touch (RB's rebuild, in C).
2. **The take.** A bounded share of D written, oldest first, so that the
   startup pos moves on and passes pEnd and pSafe, which the cut waits
   for; today the take is paced by each record's own bytes (005-49), and
   an idle database's records are small.
3. **The cut**, when it is due (`pretruncateIfPossible`, `cutIfDurable`).
4. With MR (c), the clean objects below the cut out of memory (X6).

It returns whether more is due, so that a caller, or a test, can call it
until it is done.

**Where.** `Db.maintain()` in the Core and `Database.maintain()` in the
Pub API: a new method of each, which P12 leaves to Frans; his words above
allow it. Nothing calls it on its own (P3). Each call's work is bounded,
as a user transaction's share of reclaim is (`MAX_STEP_SIZE`, the step
reserve), so P1 and P4 hold. A database is bounded without it: it only
makes "eventually" come without user writes (P10: no administration).

**The stream.** Its records are reclaim's internal transactions and,
for the take, a transaction with no keys, as a user may commit one
today: no new kind of record, no change of the format of its own. A
start reruns them as it reruns a step (with RB, the step's touch too).

**What it gives.** With R finite and the clock moving between calls (a
test's clock, or real time): an idle database's iterations end and cut,
so the stream comes back to the live data, rewritten, plus maintain()'s
own records of the retained window. With R forever there is no reclaim
and no cut: the history is kept (R8), and maintain() has no stream bytes
to release; the nodes are released by UP at the delete anyway (3.7).

**Checked by** 023-03's second drive of T1, repeated maintain() calls
with the clock moving (F7, recorded in 023-03 by the coordinator), and
T7's restarts between calls.


## 3. The options

### 3.1 The combinations

| Option | Blocks               | In short                                          |
|---|---|---|
| B      | TU, RB, AP           | reclaim alone cleans up; for comparison           |
| A      | UP, LE-b, X5 (a), AP | the deleting transaction unlinks what it empties  |
| A+RC   | A, RC                | and the roots collapse                            |
| C      | A+RC, RB             | and reclaim rebuilds what it rewrites, compact    |
| D      | A+RC, MG             | and underfull nodes merge at the delete           |
| C+D    | A+RC, RB, MG         | both                                              |

C is 020-30's "A with reclaim's compaction", widened by Frans's answer
to F5: RB compacts, merges and collapses roots, lazily. SE and MT can go
with any option (X8, X11); TE, MR, DC and RD are not part of any (X4,
X6, X8, X9).
020-30's E (SE and TE alone) bounds two cases of the read path and
releases nothing; it is not an option here.

### 3.2 Against 023-02's requirements

"met", "partly" or "not". C+D is met where C or D is. "Dead klongs" are
the klongs and bits of ended versions in nodes that still hold live
keys (K3, K7), which F1 and F2 now count (1.2).

| R   | B      | A      | A+RC   | C      | D      | Why                                      |
|---|---|---|---|---|---|---|
| R1  | met    | met    | met    | met    | met    | entries at tt and new nodes; T6, T7      |
| R2  | met    | partly | partly | met    | partly | dead klongs: by RB, else K about B       |
| R3  | met    | partly | partly | met    | partly | nodes: UP at once, B at a touch; klongs  |
| R4  | met    | partly | partly | met    | partly | a dead klong is pinned with its node     |
| R5  | met    | partly | partly | met    | partly | a search still passes it inside a node   |
| R6  | partly | met    | met    | met    | met    | B: a step passes a span's deletes        |
| R7  | met    | partly | partly | met    | partly | shadowed klongs: as R2                   |
| R8  | not    | met    | met    | met    | met    | retain forever turns reclaim off         |
| R9  | not    | met    | met    | met    | met    | needs the unlink at the delete (F3)      |

| R   | B      | A      | A+RC   | C      | D      | Why                                      |
|---|---|---|---|---|---|---|
| R10 | partly | partly | partly | met    | met    | H in live keys: D at once, C lazily      |
| R11 | partly | met    | met    | met    | met    | B: a step carries a span's unlinks       |
| R12 | partly | partly | partly | met    | met    | (b): D at once, C after an iteration     |
| R13 | met    | met    | met    | met    | met    | A: index up to about B/2 the twin's      |
| R14 | met    | met    | met    | met    | met    | with AP; the touch pins no dead node     |
| R15 | met    | met    | met    | met    | met    | no pass at a start; B, C rerun the touch |
| R16 | met    | met    | met    | met    | met    | appends behind tt's time klong; X5 too   |
| R17 | met    | met    | met    | met    | met    | B and C only with the touch rerun        |
| R18 | met    | met    | met    | met    | met    | one record a transaction, as today       |

| R   | B      | A      | A+RC   | C      | D      | Why                                      |
|---|---|---|---|---|---|---|
| R19 | met    | met    | met    | met    | met    | unlinked or replaced before tEnd         |
| R20 | met    | met    | met    | met    | met    | eviction unchanged                       |
| R21 | partly | met    | met    | partly | partly | B: P4; C, D: P11 and P13, more code      |
| R22 | met    | met    | met    | met    | met    | format 6, approved (F10)                 |
| R23 | met    | met    | met    | met    | met    | F9 (a): refused at the start             |
| R24 | partly | met    | met    | partly | met    | no SIS change; a writing touch: to check |
| R25 | met    | met    | met    | met    | met    | C after 2026.4: 3.6's lines              |
| R26 | partly | met    | met    | partly | partly | expected; T10 decides                    |
| R27 | met    | met    | met    | met    | met    | new digests and shapes, each approved    |

Notes, where the reason needs more than a line:

* **R2 to R5, R7 for A and A+RC.** UP takes every node with nothing live
  below at once, so for nodes these hold from the delete on, also with R
  forever. What stays is the klong and bit of an ended version in a node
  that keeps live keys, deleted or overwritten, until that node's next
  time split: at most B a node, copied by every touch until then. With R
  finite that split comes, as reclaim's own rewrites fill every leaf that
  holds a live key: each such klong goes within about B iterations (X4;
  probe 8.5). "partly", as 023-02's F6 recommends K = 2. MG drops them
  from the nodes it merges; RB drops them all within an iteration, so C
  meets R2 to R5 and R7 with a small K. Node versions replaced by splits,
  old values and reclaim's table rows go by the cut in every option, as
  today.
* **R6 for B.** With R finite, B's first step after a mass delete visits
  every node emptied since the touch passed its range: 023-03's numbers
  (T1 at 1M: 76,480 nodes in one touch, section 8.1 there) are B's step
  too, without the copies. Bounded by one span's deletes, not by the
  live data.
* **R9.** At every time t on or after a delete, every node reachable at
  t but a root has a live key below it at t. So with UP a scan of n KVs
  follows at most (n + 2) H key nodes, at the latest time and at every
  earlier available time, forward and backward: a bound on every single
  scan, not only amortized (023-02's F4 is then moot). B cannot give it:
  a lookup at t reads only entries up to t (sis-model.md, 3.4), so a
  cleanup made later leaves t's paths as they were (F3).
* **R10 and R12.** (a) holds with UP: no node but a root has nothing
  live below. (b) and R10's wish need merges: D keeps every node but a
  root at m live klongs or more at every time; C rebuilds to that shape
  in the iteration after the writes, so between iterations the shape is
  A+RC's plus one span's changes. A+RC alone: in "sparse", 4,031 nodes
  against the twin's 263, about B/2 times (section 8.4); at worst a
  chain of single children above each live key, H times more. So the
  index that the touch copies, and R13's c1, can be about B/2 times the
  twin's until RB has passed.
* **R21.** B's step carries the unlinks of a span (P4). C and D add the
  most code (P11, P13); D's sibling read is a stream read in the writer,
  one a level (P1, to measure). C's work is the touch's, which reclaim
  already paces.
* **R24.** UP, LE-b, RC and MG make nothing the model lacks: entries at
  tt, new nodes, replaced nodes (020-30-04, section 4). A touch that adds
  nodes (RB, TU) has to be checked in the trace export and the model's
  touch steps.

### 3.3 Against 023-03's tests

Which tests each option is expected to pass, and with which allowance
of 023-03, 2.6 (strict: a_n = 10 nodes; bounded: 10 + L h_fill, the gate
by Frans's answer to Q2). T1 measures at the end of its drive, about 20
iteration spans (023-03, 2.3): after "one or several reclaims", so a
strict reached by RB counts. From the probe (section 8) and the code;
nothing of a fix has run.

| Test, measure                       | B       | A       | A+RC    | C       | D       |
|---|---|---|---|---|---|
| T1, T2 nodes (C3, C5), not sparse   | strict  | bounded | strict  | strict  | strict  |
| T2 sparse, nodes (C3)               | strict  | bounded | bounded | strict  | bounded |
| T2 sparse, nodes against the twin's | 1       | 15      | 15      | 1       | 2 to 3  |
| C4, dead klongs, not sparse         | pass    | pass    | pass    | pass    | pass    |
| C4, dead klongs, sparse             | pass    | fail    | fail    | pass    | partly  |
| T1 C1, C2, C7: stream, lag, records | pass    | pass    | pass    | pass    | pass    |
| T1 C6, C8, C9: D, touch, residents  | pass    | pass    | pass    | pass    | pass    |
| T3, scans at every time             | fail    | pass    | pass    | pass    | pass    |
| T4, the queue                       | fail    | pass    | pass    | pass    | pass    |
| T5, U16-1 and U17-1                 | fail    | pass    | pass    | pass    | pass    |
| T5, U18-1, U14-1, the FIFO          | pass    | pass    | pass    | pass    | pass    |
| T6 to T9, T11                       | gate    | gate    | gate    | gate    | gate    |

* **T1 and T2.** UP takes every deleted key's subtree whole in "after",
  "before", "around", "long", "versions" and the Pub rows: the twin's
  nodes at once. In "inter" and "hashed" it leaves a path of single
  children down to each live key, within L h_fill (bounded); RC makes it
  the twin's (probe: 5 nodes to 1). The drive's overwrites of "/a.txt"
  time-split its leaf, so C4 holds there for all.
* **"sparse".** A and A+RC leave about 15 times the twin's nodes and
  about 13 dead klongs a leaf (section 8.4); D merges to within its
  thresholds, about 2 to 3 times (not measured); B and C rebuild to RB's
  fill. With f = 1/2, about 240 nodes against the twin's 263: the row's
  twin is put in key order (023-03, 3), with about 14 klongs a leaf. A
  twin put in random order has about 17, so strict against it needs f
  near 2/3 (Y5).
* **C1, C2, C7, C8.** Today reclaim's iteration in progress at the
  deletes never ends at N = 100,000 and 1M, because its touch passes the
  emptied nodes (023-03, 8.1). With UP the touch never meets them, so the
  iteration ends and the cuts come as the twin's. B's touch meets them
  once and unlinks them: pass, with a long first step (R6).
* **T3** is where A and B part: B leaves the deleted range reachable at
  every time up to its touch, and with R forever for ever (023-03, 4.1;
  F3).
* **T4.** With UP the queue's head is the path to its first live key, as
  in the twin: H nodes, within 4 H; the reachable nodes stay the live
  tree's (probe of 021-25's FIFO: 123 against 117, 121 with RC). B passes
  the keys deleted since the last touch at every head scan.
* **T5.** U16-1's entries each have a segment tree of their own (021-28,
  "Cause"): UP takes the tree and the segment leaf's klong at once, and
  the inner nodes as they empty. U17-1's deleted generations are
  unlinked as the cleanup thread deletes them.
* **T6 to T9, T11** are gates, the same for all; the more code, the more
  to get right (3.5). T11 with F9 (a): 2026.3's database refused at the
  start (section 5). **T10** measures (3.4). **T12** follows the release.

### 3.4 Bounds and costs

n: the KVs a scan hands its stop condition; H: the key node levels on a
key's path, from every key ever put in each segment tree; H_live: the
same from the live keys; m: the merge threshold. "Lazily": after RB's
next iteration over the range.

| Option | A scan of n KVs, key nodes  | A get          | Reachable key nodes         |
|---|---|---|---|
| today  | (n + 2) H + deleted keys'   | H              | grow with every delete      |
| B      | as today until a touch      | H, lazily less | the twin's shape after one  |
| A      | (n + 2) H, every time       | H              | (n + 1) H at most           |
| A+RC   | as A, H lower at the roots  | H              | as A                        |
| C      | as A+RC; D's lazily         | H_live lazily  | as A+RC; the twin's lazily  |
| D      | O(n / m + H_live)           | H_live         | O(n / m)                    |

| Option | Cost of a delete                       | Write amplification, with deletes   |
|---|---|---|
| B      | as today                               | the touch writes rebuilt nodes      |
| A      | a climb when a node empties; O(1) am.  | less than today: emptied nodes go   |
| A+RC   | and a top node when a root collapses   | as A                                |
| C      | as A+RC                                | as A+RC; the touch writes rebuilt   |
| D      | and a merge, a sibling read; O(1) am.  | a merged node replaces two          |

* Without deletes nothing changes in A and A+RC but LE-b's first klong
  in new inner nodes, the same size. Puts cost the same; gets and scans
  read the same nodes.
* With deletes, A writes fewer bytes than today: the emptied node is not
  written again, and the touch, which copies every reachable node of its
  range in each iteration, no longer copies emptied ones (today 17,493
  nodes in one step of 021-25's FIFO, 4.17 MB).
* C's touch writes the nodes today's touch writes, as new nodes, fewer
  and smaller after the merges and the compaction, and a klong more in
  each parent, which it rebuilds in turn; a top node an iteration. About
  today's bytes; more work in the step's transaction.
* D's extra cost is in the deletes of sparse ranges: about one merge a
  level per m deletes, each a read and one or two node writes.

### 3.5 Risks

* **A.** A climb that unlinks a node with a live key below loses the key
  at the latest time: T6 (lookups against a model), DagFuzz, DeleteRepro
  and RestartStress catch it. X5's in-place change of the transaction's
  own klongs is new code in the most delicate place. `dirtyNodeBound`
  must not undercount (005-31). The rerun must make the same ids
  (RestartInvariance, StreamDigest's four modes). Readers: no new
  protocol.
* **LE-b.** A change of the space split of inner nodes: DagTester's split
  tests get new expected shapes. Nothing in the read path changes.
* **RC.** Small: today's path for a second new root in a transaction
  (TopDs.java:64), and time-split-1's klong for a segment root.
* **B, C.** RB makes the touch a writer of the tree (2.6): the cut's
  safety argued again, the touch rerun at a start (new code in
  `DbStarter`), step boundaries, the step's charge and reserve, the trace
  export of a touch that adds nodes. The largest change to reclaim since
  2026-10-13.
* **D.** The most cases in the delete path (2.4); reads in the writer;
  thresholds; more states for the checkers to see.

### 3.6 The format, StreamDigest, the Lean model and the C port

| Option | Format 6 for                     | StreamDigest | Lean            | C, lines       |
|---|---|---|---|---|
| B      | the touch, rerun from the record | 4 `l3-*`     | a writing touch | 400 to 800     |
| A      | the delete rule, LE-b's split    | all 12       | none in SIS     | 150 to 300     |
| A+RC   | and RC                           | all 12       | none in SIS     | A + 50         |
| C      | and RB's touch, rerun            | all 12       | a writing touch | A + 400 to 800 |
| D      | and MG                           | all 12       | none in SIS     | A + 300 to 600 |

* All of StreamDigest's 12 configurations delete (`del=1`,
  StreamDigest.java:76 to 91), so UP changes every digest where a node
  empties; its four modes must still agree with each other (T8, T9). RB
  changes the 4 `l3-*` ones more.
* Lean: SIS is generic in the entries and needs no change for UP, LE,
  RC or MG; the trace checker's `blive` takes the last key entry of each
  compare value that no later delete names, in any key node
  (Check/Trace.lean:56 to 69), which is how LE-b's shadowing klong and
  UP's bitmap in an inner node read. A touch that adds nodes (RB) is to
  check. Traces are made fresh by TraceExport; the 20 hand-made traces
  stay.
* C: 020-30-04, section 5's estimates for A, MG and a compaction (200 to
  400); RB adds the merges, the roots and the touch's rerun, so more, an
  estimate. RC and LE-b are small. The C port follows Java after 2026.4's
  release, with a new pin for `cross.sh full` (022).


### 3.7 With repeated maintain(): the one-entry database

Frans's F7: repeatedly calling maintain() must eventually bring a
database with only one hello-world entry to about a fresh hello-world
database's resources. For each option, after the deletes, with only
maintain() calls (MT, 2.12) and the clock moving, R finite; then the
allowances for one entry.

| Resource                       | B       | A       | A+RC    | C       | D       |
|---|---|---|---|---|---|
| Key nodes, M4                  | twin's  | path    | twin's  | twin's  | twin's  |
| Get of the entry, M6           | twin's  | path    | twin's  | twin's  | twin's  |
| Dead klongs in its leaf, M5    | 0       | splits  | splits  | 0       | splits  |
| Stream from the cut, M1        | twin's  | twin's  | twin's  | twin's  | twin's  |
| Objects after a restart, M11   | twin's  | path    | twin's  | twin's  | twin's  |
| The same with R forever        | today's | nodes   | nodes   | nodes   | nodes   |

* "path": the nodes from the root of each segment tree down to the
  entry, single children, up to h_fill; RC takes them. In "after",
  "before" and "long" there is none, as the deleted keys had segment trees
  of their own (section 8.4).
* "splits": the dead klongs of the entry's leaf go when the leaf next
  time-splits, which reclaim's rewrite of the entry, every other
  iteration, brings within about B iterations (X4); at most B until then.
  "0": RB drops them at its next touch, B and C.
* M1: the iterations rewrite the entry and the internal keys, the cut
  takes the rest; what is kept is the live data plus maintain()'s own
  records of the window, as for the twin under the same calls. 023-03's
  W and a_b cover the difference of phase.
* With R forever nothing is cut: every option keeps the history, as the
  user asked (R8); UP's options release the nodes ("nodes"), B nothing.

**The allowances for one entry** (023-03, 2.6): bounded a_n = 10 + L
h_fill, strict 10 nodes. With one entry, L = 1 (R forever; with R
finite, L = 4 with reclaim's three internal keys), the bounded allowance
is 10 + h_fill, 16 nodes at N = 100,000 (h_fill 6), against the strict
10. The path that A leaves is h_fill nodes against the twin's one, so 5
more at N = 100,000 and about 7 at 10M: within the strict 10 too, for
one entry, though not the twin's shape. With L live keys the paths add
up, about L (h_fill - 1), and only RC (or RB's root collapse) keeps
strict; that is where A and A+RC part. In bytes, a_b = a_n x 512: 8,192
bounded and 5,120 strict, for one entry.


## 4. The open design decisions

### X1. The leftmost child: LE-a, LE-b, LE-c or LE-d

The coordinator's first open point (2026-11-10): relabel, or relax the
rule so that an inner node's smallest live klong covers every key below
it. 020-30-03 rejected relaxing because 2026.3 could not read such a
tree; with format 6 and F9 (a) 2026.3 refuses those databases at the
start, so that objection is gone. What remains is what relies on the
rule. Checked in the code, every place:

* **Routing.** A get (`Dag.getEqNodeInSegment`, Dag.java:432: no klong,
  "not found"), a put (`setValue` and `setNode`, Dag.java:783 and 849,
  then `checkFound`: "corrupt data", the database fails) and
  `dirtyNodeBound` (Dag.java:492: the walk stops).
* **A scan's setup** (`GetMany.Chain.setup`, GetMany.java:246 forward
  and 257 backward above the leaf). When an inner node has no klong at or
  below the start key, the scan does not go down (262 to 267): forward it
  starts before the node's first klong, so it returns every key of the
  first child; backward it starts before the first. Right only if no key
  of the first child is below its klong.
* **021-28's end key** (`isPastEnd`, branch `scan-deleted-keys`): it ends
  the scan when a klong's compare value, with the segments passed, is
  past the end, because that value is a lower bound of every key below.
* **The splits.** A space split of a node that is not a root gives the
  parent the node's old klong for the first half and the second half's
  first compare value for the second (Dag.java:1308 to 1323). The two
  klongs come in the halves' order only if the old klong is at or below
  the first half's keys.
* **Reclaim**: its scan and touch are `getMany`s (Reclaim.java:557,
  Db.java:2944), so as scans. Gets at earlier times, eviction, the node
  table and startup do not route by keys.

Against these:

* **LE-c, relax**, changes every place above. Routing falls back to the
  smallest live klong; a scan's setup must go down into it in both
  directions (a forward scan would else return the first child's keys
  below its start key); `isPastEnd` must not take the leftmost klong as a
  bound; `checkFound` loses its check of corrupt data (019-32). And the
  splits: the leftmost child then holds keys below its klong, and when it
  splits, the second half's first key can be below that klong, so the
  parent's two klongs come in the wrong order and keys go to the wrong
  half. LE-c needs a new split rule too: a klong at the first half's
  first key and the old one deleted. Gets and scans at earlier times run
  the new routing too, over every tree.
* **LE-a, relabel down the edge**, changes no reader. It writes O(H)
  nodes off the delete's path once per emptied leftmost child: in a FIFO,
  with nodes of about 15 klongs, an inner node at height j empties once
  per about 15^j deletes, so about 1/15 of a node write a delete
  (020-30-03, section 4); one delete at most H more nodes.
* **LE-b, the empty key first**, changes no reader either: `searchLte`
  finds the empty key where it found the old bound, and `isPastEnd` sees
  a bound of 0 for a first child, which is right and only stops one
  klong later. The relabel is one klong in the parent, which is on the
  delete's path and dirty anyway. Its cost is one rule in the space split
  of inner nodes, so new inner nodes differ from today's in their first
  klong: other bytes, inside format 6. A database of 2026.4 is new
  (F9 (a)), so every inner node it has follows the rule from its first
  split on.
* **LE-d, keep**: at most one chain of empty nodes on the left edge of
  each live inner node, about H squared in a FIFO (020-30-03); fails R3,
  and blocks RC (a root keeps an empty child beside its live one).

**Recommended: LE-b.** LE-a if phase 2 finds a reason against the change
of the space split; both keep the rule that every reader relies on, and
can share the code that re-points the leftmost klong. Not LE-c: it moves
the change from one write path into every read path and the splits, for
a saving of about 1/15 of a node write a delete over LE-a, and none over
LE-b. Not LE-d.

### X2. The tree's height: RC

Alternatives: (a) no RC, H never shrinks (K11); (b) RC in the deleting
transaction, for the space root and the segment roots (2.3); (c) RC by
reclaim's touch (only with R finite, and after a touch). Evidence: RC
alone brings the hello-world shapes to their twins (section 8.4) and the
FIFO from 6 levels to 4 (8.2); it costs a top node a level lost; MG's
root case is RC. **Recommended: (b), in 2026.4 with A.**

### X3. Strict: rebuild by reclaim (RB) or merge at the delete (MG)

Frans, 10:38: the bounded allowance is the gate; strict is welcome, and
"it is enough to eventually, after one or several reclaims, to get the
original Hello-world resource consumption". What A+RC leaves beyond the
twin is underfill (in "sparse", about B/2 times the twin's nodes,
sections 8.3 and 8.4) and dead klongs (X4). The scan bound at every time
comes from UP at the delete (F3), not from either way below.
Alternatives: (a) none, A+RC's bounded shape, which passes the gate; (b)
MG, merges at the delete (option D, 2.4); (c) RB, the touch rebuilds
what it rewrites (option C, 2.6); (d) both.

| Point                        | MG, at the delete           | RB, in reclaim's touch        |
|---|---|---|
| Strict, when                 | at the delete               | an iteration after the writes |
| With R forever               | yes                         | no reclaim, so nothing        |
| Klongs of ended versions, R7 | merged nodes; else as A+RC  | all, within an iteration      |
| Where the work goes          | the deletes; a sibling read | the touch, which reads it all |
| P4, each call's share        | a delete pays its merges    | paced as the touch is today   |
| What a start must rerun      | the delete's rule           | the touch: a field            |
| Where the new code is        | the delete path, X5's cases | the touch, its rerun, the cut |
| The main risk                | the most cases in the Dag   | the touch becomes a writer    |

* F2 and F1 ask that the klongs of every ended version go. With R
  finite, A+RC already lets them go at the splits that reclaim's
  rewrites bring, within about B iterations (X4); MG takes them sooner
  only from the nodes it merges; RB takes them all within an iteration.
* (b) gives what Frans did not ask for: the shape at every time, and
  with R forever. R8 asks only section 4's bounds with R forever, which
  A+RC meets.
* (c) puts the work where reclaim already reads and writes every node of
  the range once an iteration, paced by the internal fraction; its cost
  is the touch becoming a writer and being rerun at a start (2.6).

**Recommended: (c), C = A+RC with RB**, as phase 2's second proposal, on
a branch on top of A+RC. Not MG for now. Into 2026.4's format 6 if it
passes the gates when A+RC does; else 2026.4 with A+RC alone (bounded,
the gate), and RB in a later release with a format of its own, which by
F9's precedent refuses 2026.4's databases or reruns their records by
A+RC's rules (Y4).

### X4. Dead and shadowed klongs in live nodes

F2 (10:41) and F1 (implied): the klongs and bits of every ended version
go, eventually, also from nodes that still hold live keys. Alternatives:
(a) leave them to the node's next time split; (b) DC (2.5); (c) RB's
compaction (2.6, part 1). Evidence:

* On the hello-world shapes A leaves 4 to 22 dead klongs (section 8.4),
  within C4's twin + B; in "sparse" 43,032, about 13 a live leaf.
* With R finite, (a) does take them, slowly. Reclaim rewrites each live
  value stored before pCut (Reclaim.java:622), so every value about every
  other iteration; each rewrite is a put that adds a klong, and a time
  klong, to the value's leaf. So a leaf with a live key fills and
  time-splits within about B / (k + 1) rewrites, k its live keys, and the
  split drops its dead and shadowed klongs; its parent gets a klong and
  in turn splits. The probe (section 8.5, today's code, "sparse" at N =
  3,000, R = 1 s): the dead klongs in nodes with live keys went from
  1,700 to 323 within 16 iterations of the drive. They never reach zero:
  the rewrites themselves end versions and leave shadowed klongs, so the
  count rises again (to 1,355 at 40 iterations) until the next splits.
  Each dead version's klong goes within about B iterations; the rest is
  at most B a node at any time.
* (c) takes each within an iteration or two: the touch runs before the
  step's rewrites (Db.java:2903 to 2913), so right after a step a leaf
  holds at most the shadowed klongs of that step's rewrites, one a live
  key. (b) bounds them by the live ones, not to zero, and overlaps MG and
  RB.

**Recommended: (a) in 2026.4 with A+RC**: it meets F1 and F2's
"eventually" with R finite, with a K of up to about B iterations (023-02,
F6, still open: its recommendation is K = 2), reported as M5. **(c) with
RB** when RB comes (X3): K of one or two iterations.

### X5. A node emptied in the transaction that made it

A delete that meets a full leaf replaces it by its last version, split
in two if it holds more than B/2 klongs (Dag.java:972, 1071 to 1076): two
new nodes of tt with the old keys. The next deletes of the same
transaction, in key order, can empty one of them: likely in batch
deletes of consecutive keys, as the Pub API's index cleanup's 100 a
transaction (`CLEANUP_KEYS`). Then UP would leave a node made at tt
unreachable at tt, against A3, the rule `handleFullNode`'s comment keeps
(Dag.java:1049 to 1056). Alternatives:

* (a) **Take it back in place.** The parent's klong to it is of tt,
  behind the time klong of tt, where every reader stops, as
  `toPreviousState` and `replaceKlong` change such klongs today: remove it
  (and remap the bits of the transaction's bitmap after it), and drop the
  node from the node table, D and the record. As far as the stream and
  the model see, it was never made. Its vpos id is never written; the
  rerun makes and drops it the same way, so the next ids are the same.
* (b) Delete its klong with a bitmap and write it: a node made and
  unreachable at its own time. A3 must be weakened in the model.
* (c) Leave it linked and empty: no later delete reaches it (it has no
  klong to delete), so it stays for ever.

**Recommended: (a).** Phase 2 prototypes it first, with a unit test of a
batch delete that empties a split's half, and A2A3Check2 with `del` and
`ops` high.

### X6. Memory without pressure: MR

The coordinator's third open point. Alternatives (2.10): (a) CLOCK as
today; (b) evict at once the clean objects of the nodes a transaction
unlinked or replaced; (c) a pass after each cut. Evidence: once written,
an unlinked node is not pinned and no lookup at a later time follows it,
so R4 as worded holds with (a): it goes at eviction's first pass once
the budget is reached; after a restart it is never loaded (023-03's M11
is taken after a restart and a probe). What (a) leaves is a process that
stays under its budget keeping dead objects, as any cache. The Pub API
always evicts; `noEvict()` is the Core's only and a non-goal (023-02,
7.1). **Recommended: (a)**, with M11 and M13 reported; (b) is a small
later step (`Cache3.evict` takes one handle) if the comparison with the
twin in a running process matters (Y6).

### X7. The format

Alternatives: (a) one `RECORD_FORMAT` 6 for every rule 2026.4 changes:
UP, LE-b's split, RC, X5, and RB's touch with its field if it is ready;
(b) a format for each change. **Recommended: (a)** (section 5). The parser
reads format 6 only; `StoredTrans.formatRefused` (StoredTrans.java:230)
names format 5 as 2026.3's and before.

### X8. 021-28's end key (SE) and 021-25's fix (a) (TE)

020-30's F7. With UP neither is needed for a bound. SE saves the path to
the next live key and the read of its value at the end of every index
scan and listing, changes no byte, and is reviewed. TE keeps a step's
dirtying within its range, and changes the `l3-*` digests, which UP
changes anyway. **Recommended: SE in 2026.4, with A; TE with A or not at
all** (Y7).

### X9. A range delete: RD

**Recommended: not now.** UP gives the bounds without it; it needs a new
Core operation (P12), a new record content and an STM rule. A todo item
if the Pub API's `deleteIndex` turns out too slow with UP.

### X10. Reclaim's unlinking: TU

With F9 (a) no 2026.3 tree is opened, and with UP, LE-b and X5 (a) no
transaction leaves a node with nothing live below. **Recommended: no
TU**; Reclaim.Tester's `testDeletedKeysAfterCut` (011-01, Q7) stays, and
checks that the cut stays safe without it.

### X11. An explicit maintain(): MT

F7 (10:49). Alternatives: (a) none: "eventually" is counted in the
user's writes only, and an idle database never cleans up (P3); (b) MT
as in 2.12: one reclaim step, a share of the take and the cut a call,
iterations begun by time alone when it is called, bounded work a call;
(c) a maintain() that runs to the end in one call, all of D and a whole
iteration: simpler, but a call of any length (P1, P4). **Recommended:
(b)**, made with the tests in phase 2 (023-03's second drive of T1 needs
it), on `main` before the prototypes: it changes nothing unless it is
called, and with today's code it shows today's failure, as each call's
step passes the emptied nodes.


## 5. The format and compatibility

### 5.1 What a record means

A start reruns every record of its startup section but the first through
`Dag.putKv` (`DbStarter.rerunTransaction`, DbStarter.java:373 to 465),
with the ids counted from the record's position (`Spos.nextVpos`), and
then must find each id of the record's got-dirty list ("startup error,
node ... not found", 452). So the Dag's rules for deletes and splits are
part of what a record means (020-30-04, section 2). UP, LE-b's split
rule, RC, X5 and MG change those rules; RB changes what a step's touch
makes. Each is a change of the format in the sense of 018-01, section 2,
and needs Frans's approval in its entry: F10 says that such a change is
acceptable in 2026.4.

### 5.2 A clean close

The coordinator asked whether a clean close leaves nothing to rerun,
which would have let 2026.4 open a cleanly closed 2026.3 database without
the old delete rule. It does not. `Db.closeStorage` (Db.java:1676) waits
for the running transaction, ends the eviction thread and closes the
storage, which writes what is buffered; nothing writes D, and the
startup pos stays where the last record's take left it. The probe
(section 8.1): 20,000 transactions on a `FileStream` with a startup
distance of 1 MB, `close()`, a start: a startup section of 1,006,704
bytes and 1,054 records, of which 1,053 are rerun; 2026.3's jar gives
the same numbers. So opening a 2026.3 database would have needed the old
rule as a second rerun path. With F9 (a) it is moot: 2026.4 refuses
those databases.

### 5.3 What 2026.4 writes and refuses

* `RECORD_FORMAT` 6 (StoredTrans.java:53). The parser takes 6 only and
  throws `VersioningStreamException` for any other (StoredTrans.java:340
  to 341), with a message (`formatRefused`, 230 to 239) that should name
  format 5 as that of 2026.3 and before, as it names format 2 today. A
  start parses at least the record that the last valid meta block names,
  so the refusal comes at the start, never later (023-03, T11).
* 2026.3 refuses format 6 by the same check: it reads 5 only.
* The node encodings do not change: the klong kinds TIME, KEY and
  DELETE_BITMAP (Klong.java:64 to 70) in any key node, which both parsers
  take (020-30-04, section 2); key node format byte 2, value node 4, top
  node 2. New are a bitmap in an inner node (UP) and the empty key as an
  inner node's first klong in more nodes (LE-b): shapes that both read.
* RB, if it comes: a field that marks a step's record and gives its
  touch's range, so that a start reruns the touch. TE needs none: it
  changes only which nodes get dirty, and D is rebuilt from the stored
  ids.
* No second rerun path, no cleanup of old trees (TU), no check of a
  clean close: F9 (a).

### 5.4 What changes beside the format

* StreamDigest: every configuration's digest where a node empties, so
  likely all 12. 018-01, section 2: the entry keeps the digests before and
  after, `releases/next.md` names them, and 2026.2's reference no longer
  compares for them, as 2026.3's notes said for reclaim's four.
* Unit tests that assert a shape the Dag's rules decide (DagTester's
  splits), named in the change's entry; `StoredTrans`'s format tests.
* The C port: after 2026.4, with a new pin (3.6).
* Lean: no change of SIS; conformance on fresh traces (3.6).


## 6. The recommended direction and phase 2

### 6.1 Direction

**First, for 2026.4, in one `RECORD_FORMAT` 6: A+RC**, with LE-b (X1),
RC (X2), X5 (a) and AP, and SE from `scan-deleted-keys` (X8). It fixes
every case observed (U16-1, U17-1, U18-1, U14-1, 021-25); it passes T1 to
T5 with the bounded allowance, the gate (Frans, 10:38), and the strict
one in every row but "sparse"; and it gives R9 at every available time
(F3), with R forever too, as a bound on each single scan. It is the
smallest change: one rule of the write path in `Dag`, one rule of the
space split, nothing in the read path, nothing in reclaim. It is Frans's
2012 rule.

With R finite, A+RC also meets F1 and F2's "eventually" for the klongs
of ended versions in live nodes: reclaim's own rewrites fill and
time-split every leaf that holds a live key, within about B iterations
(X4). Its K is large (023-02, F6).

**Then, for strict: C, A+RC with RB** (X3, X4). What A+RC leaves beyond
the twin, underfill (about B/2 times the twin's nodes in "sparse") and
those klongs (at most B a node until their split), RB takes in the
iteration after the writes, as Frans's strict allows ("after one or
several reclaims"). Into 2026.4's format 6 if it passes the gates when
A+RC does; A+RC does not wait for it.

**Not now: D (MG) and B.** MG gives the shape at every time and with R
forever, which Frans did not ask for, puts the most cases into the
delete path, and drops the klongs of ended versions only from the nodes
it merges. B fails F3 (T3, T4) and gives nothing with R forever.

### 6.2 Phase 2

1. **The tests first**, as 023-03's state asks: `CleanupTester` and
   `cleanup.sh` on `main`, with H1 to H3, so that every prototype is
   judged by the same code; with them MT, `Db.maintain()` and
   `Database.maintain()` (X11), which T1's second drive needs. Today's
   `main` fails them (023-03, 8.5).
2. **P-A, a full proposal and prototype of A+RC**, on a branch in a
   clone: UP with X5 (a), LE-b, RC, `dirtyNodeBound`, AP, format 6 with
   its refusal message, SE taken from `scan-deleted-keys`. Its entry
   holds the proposal of the format change for Frans's approval (018-01,
   section 2). Gates: T1 to T5 with the bounded allowance, T6 to T9
   (`before-commit.sh`, the four levels, A2A3Check2 with deletes), T11,
   then T10. One agent, effort xhigh or max.
3. **P-C, a full proposal and prototype of RB**, on its own branch on top
   of P-A once P-A's climb works: the post-order rebuild (compaction,
   merges, roots), the fill f and the threshold m, step boundaries, the
   record's field and the touch's rerun in `DbStarter`, the cut's safety
   argued for replacements, the step's charge and reserve. Judged by T1
   and T2 with the strict allowance at the end of the drive ("sparse"
   included), C4, T4's M4 against its twin, T7's restarts at the drive's
   cuts, ReclaimStress, ReclaimReaders, and T10. A second agent; a design
   note first, as the touch becomes a writer.
4. **A review** of P-A, and later of P-C, by an agent that has not
   written them, and the comparison with the independent study of
   2026-11-10 (006-21, W2).
5. The C port after the release (022), and the Lean conformance on fresh
   traces with each prototype's gates.

LE-a needs no prototype of its own unless LE-b meets a problem in P-A:
the code that re-points a leftmost klong is the same; only how far down
it goes differs. MG (D) gets a proposal only if Frans wants the shape at
every time, or T10 shows that RB costs too much.


## 7. Questions for Frans

Each with a recommendation, and the questions of 023-02 and 023-03 it
meets. Answered already: F2, F3, F5 and Q2, F7, F9, F10; F1 implied
(1.2).

* **Y1. The leftmost child** (X1). LE-b, the empty key as every inner
  node's first klong, so that an emptied leftmost child is replaced by
  one klong in its parent; or LE-a, relabel down the left edge; or LE-c,
  relax the routing? Recommended: LE-b; LE-a as the fallback; not LE-c.
* **Y2. Root collapse at the delete, in 2026.4** (X2)? Recommended: yes,
  with UP: it gives the hello-world shapes their twins at once.
  **Frans, 2026-11-10, 12:31: yes.**
* **Y3. Strict by reclaim's rebuild** (X3; 023-02, F5; 023-03, Q2). C, RB
  in reclaim's touch, rather than D, merges at the delete? Recommended:
  C; not MG for now.
* **Y4. RB in 2026.4** (X3, X4; 023-02, F11). Into 2026.4's format 6 if it
  passes the gates when A+RC does, else a later release with a format of
  its own, which would refuse 2026.4's databases as 2026.4 refuses
  2026.3's (F9)? Recommended: yes, and A+RC does not wait for it.
* **Y5. RB's fill** (X3; 023-03, C3 strict). Rebuilt nodes of up to B/2
  live klongs, as a time split's, which the next put does not split, or
  up to about 2/3 B, so that strict holds in "sparse" also against a twin
  put in random order? Recommended: phase 2 measures both on T2's
  "sparse" rows and T10; T2's row as specified, with its twin put in key
  order, passes with B/2.
* **Y6. Memory without pressure** (X6; 023-02, R4). CLOCK as today, with
  M11 and M13 reported? Recommended: yes.
  **Frans, 2026-11-10, 12:35:** "Option (b), we follow the rule for
  resource release, also for memory." Not CLOCK alone: the memory of
  ended versions is released too, eventually, in the ordinary operations
  (Y10's note), not only under the cache's pressure or at a restart. The
  coordinator's (b), not yet checked in the code: after a cut, every node
  that a lookup at an available time can reach is stored at the cut's
  position or later, or is dirty, so a cached node stored before it is
  dead and can be dropped, a little at a time; 023-03's M11 and M13 then
  gate.
* **Y7. 021-28's end key** (X8; 020-30, F7). Into 2026.4 with A+RC, and
  021-25's fix (a) with it or not at all? Recommended: SE yes; TE
  optional.
  **Frans, 12:31: as recommended** (SE into 2026.4; TE optional).
* **Y8. One format 6** (X7; 023-02, F9 and F10 answered). Every rule of
  2026.4 in one `RECORD_FORMAT` 6, and 2026.3's databases refused at the
  start with a message that names 2026.3? Recommended: yes.
  **Frans, 12:31: as recommended.**
* **Y9. 2026.4's scope** (023-02, F11). Recommended: A+RC's at least: R1,
  R6, R8 to R11, R12 (a), R13 to R27, R2 to R5 for nodes, and for klongs
  with K up to about B iterations; with RB also R2 to R5 and R7 with a
  small K, R10's wish and R12 (b), lazily. F4 is met as recommended:
  with UP, R9 bounds each single scan.
* **Y10. maintain()** (X11; 023-02, F7 answered). `Db.maintain()` and
  `Database.maintain()`, each call bounded (one reclaim step, a share of
  D, the cut when due) and returning whether more is due, made with the
  tests? Recommended: yes.
  **Frans, 12:31:** "Y10, yes to maintain(), note: maintainance should be
  performed while doing other operations on the database, so the user
  explicitely calling maintain() should be optional, not a requirement on
  the user that she must call maintain." So the cleanup goes on in the
  ordinary operations; `maintain()` only lets an application ask for more.


## 8. The probes' numbers

On F53, 2026-11-10, in package `bergdb.core` against `java/build.sh`'s
jar of `main` at `9acf5c38` (and 2026.3's jar for 8.1); counts, not
times. Node size 30, `testSetup()` (memory, no eviction, R forever) but
in 8.1. "A" counts the key nodes reachable at the latest time that have a
live key below them, which is what UP with LE-a or LE-b would leave
where no put came back into an emptied range; "A+RC" takes from those
the root levels with a single live child, in every segment tree.

### 8.1 A clean close

A `FileStream`, startup distance 1 MB, 20,000 transactions of one put of
1,000 bytes or one delete (every third), hashed keys; `close()`; a new
start. `StartInfo`: stream 17,457,888 bytes, startup pos 16,451,184, a
section of 1,006,704 bytes and 1,054 records, 1,053 of them rerun. The
same with `releases/2026.3/bergdb-2026.3.jar`.

### 8.2 021-25's FIFO

1,024 live keys of 6 bytes, then 100,000 transactions of one delete and
one put, keys in time order. The twin: the 1,024 live keys, one put a
transaction.

| Tree   | Key nodes | Levels | By level, root first     | Dead klongs |
|---|---|---|---|---|
| today  | 11,745    | 6      | 1/3/28/204/1,435/10,074  | 10,368      |
| A      | 123       | 6      | 1/1/1/2/15/103           | 29          |
| A+RC   | 121       | 4      | 1/2/15/103               |             |
| twin   | 117       | 3      | 1/14/102                 | 3           |

Today 11,622 of the 11,745 nodes have nothing live below.

### 8.3 All but one of every 30 deleted

N = 30,000 keys of 6 bytes, 100 a transaction, then all but every 30th
deleted, 100 a transaction. The twin: the 1,000 left, put fresh.

| Order     | Today, nodes (levels) | A, nodes | A, dead klongs | Twin, nodes (levels) |
|---|---|---|---|---|
| ascending | 2,368 (5)             | 1,208    | 12,903         | 78 (3)               |
| hashed    | 2,772 (5)             | 1,278    |                | 66 (3)               |

RC takes nothing here: the roots have many live children.

### 8.4 023-03's shapes, A against the twin

"/a.txt" put, then N keys of the shape, 100 a transaction in key order,
then deleted, 100 a transaction ("sparse": all but every 30th). R
forever, so L = 1 ("sparse": 3,335). The twin: the live keys put fresh.

| Shape  | N       | Today, nodes (levels) | A, nodes | A, dead klongs | A+RC | Twin |
|---|---|---|---|---|---|---|
| after  | 100,000 | 7,897 (6)             | 1        | 6              | 1     | 1    |
| before | 100,000 | 7,897 (6)             | 1        | 6              | 1     | 1    |
| inter  | 100,000 | 7,896 (5)             | 5        | 22             | 1     | 1    |
| hashed | 100,000 | 155,351 (7)           | 5        | 4              | 1     | 1    |
| long   | 10,000  | 60,787 (11)           | 1        | 4              | 1     | 1    |
| sparse | 100,000 | 7,897 (6)             | 4,031    | 43,032         | 4,031 | 263  |

Today's "after" is 023-03's M4 with R forever (8.3 there: 7,897).
"hashed" here puts in key order random 64-bit hashes, so its count
differs from 023-03's random order (112,759). In "sparse" A keeps 3,335
leaves for 3,335 live keys: one live key a leaf.


### 8.5 Reclaim's rewrites and dead klongs

Today's code, a `MemoryStream`, a `CoreTestClock` 1 ms a transaction, R =
1 s, startup distance 100 kB: "/a.txt", then 3,000 keys "/k/" and 10
digits, 100 a transaction, all but every 30th deleted, 100 a
transaction; then a drive of 16,000 overwrites of "/a.txt" with 1,000
bytes. Counted at the latest time: the nodes reachable, those with a
live key below (what A would keep), and the KEY klongs in those that are
not live (deleted or shadowed).

| When           | Iterations | Reachable | With a live key | Klongs not live |
|---|---|---|---|---|
| after deletes  | 1          | 240       | 124             | 1,392           |
| drive 2,000    | 8          | 240       | 124             | 1,700           |
| drive 4,000    | 16         | 243       | 127             | 323             |
| drive 6,000    | 24         | 243       | 127             | 595             |
| drive 10,000   | 40         | 243       | 127             | 1,355           |
| drive 12,000   | 48         | 243       | 127             | 372             |
| drive 16,000   | 64         | 243       | 127             | 1,132           |

The deleted keys' klongs go when reclaim's rewrites have filled and
time-split their leaves; the rewrites' own shadowed klongs come and go
with the splits. Today's 116 nodes with nothing live below stay: no
rewrite reaches them.


## 9. State

2026-11-10, 12:35, o23 for coord-1110: written, sections 1 to 8, with
023-03 (`b23074ea`) and Frans's answers to F2, F3, F5 with Q2, F7, F9 and
F10 (F1 implied), as the coordinator relayed them by 10:49. The probes:
`/Users/f/fl/bench/2026-11-10/o23/probe` (`O23Probe.java`: the clean
close, the FIFO, every 30th; `O23Shapes.java`: 023-03's shapes;
`O23Rewrites.java`: reclaim's rewrites and dead klongs), against the
clone `/Users/f/fl/bench/2026-11-10/o23/clone` at `9acf5c38`, built,
unchanged. Not done: no prototype of any block, as asked; MG's factor in
"sparse" (2 to 3) and RB's counts there come from their rules, not from
a run. Next: Frans's answers to Y1 to Y10; phase 2 as in 6.2.
