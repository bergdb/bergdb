Self-indexed streams: the model
===============================

Draft 2, 2026-10-12. Written by Claude for Frans Lundberg.

A self-indexed stream is a database that keeps all its data, index
included, in one append-only stream, and that after a crash rebuilds its
state in RAM by reading only the last part of the stream. This text is an
abstract model of it: the data structure, the stream, the algorithm that
writes the stream, and the startup that reads it back. It states two
theorems in plain English. T1, recovery: after a crash, startup gives back
the database as it was after the last complete transaction. T2, restart
invariance: a restart does not change what the database appends to the
stream. Both are proven in the Lean proof assistant
([../lean/](../lean/README.md)). Each definition here is one definition in
Lean, and each theorem one Lean theorem, so this text is also the guide to
reading the Lean files. Draft 1 was the problem statement before the
proofs; section 14 lists what the proofs changed.

Builds on Frans's [startup.md](sources/startup.md) and
[v5](sources/self-indexed_streams_v5_130704.pdf),
and on [011-03](../items/011-docs-archive/03-startup-invariants.md). Uses the notation of
startup.md where it can, all defined below: the database state
DB = <P, D, S>, where P is the data, D the dirty nodes and S the stream;
the transactions T(i); the startup positions s(i); and the got-dirty sets
gd(i). In the terms of [levels.md](levels.md), this is the theory of level
2, bounded startup.

Scope: correctness of the stream and the startup. Nothing here depends on
klongs (the 64-bit words that BergDB's nodes are made of), cache-awareness
or the Java code. Sections 2 to 9 leave out bounds on the costs, eviction
(dropping nodes from RAM) and reclaim (cutting the front of the stream);
see section 10. Section 15 adds eviction and reclaim.

Review, 2026-10-13: the model and proof scope are unchanged at `ebe5f77`.
[levels.md](levels.md) records Java's tested status and what remains to
show that the Java code implements the model. Fresh Lean build, randomized
and axiom checks passed during the documentation review; details are in
[lean/README.md](../lean/README.md).


1 Summary
=========

The database has two kinds of storage:

* S, the stream. Durable and append-only, and any record can be read. Each
  transaction appends one record. A crash keeps a prefix of complete
  records.
* RAM. Lost in a crash. It must hold the dirty nodes. Everything else in RAM
  is cache, and the model does not need it.

The data is P, a partially persistent linked structure: nodes that point to
other nodes and remember their history, so a lookup can see P as it was at
any earlier time. Every lookup starts at one node, the root. Data nodes are
nodes without pointers that never change, such as BergDB's values; all
other nodes are index nodes. Nodes are written to the stream as versions. A
version holds the node's history so far and, for each node it points to, a
reference to that node's latest version in the stream. An index node is
dirty when the stream, read from its latest version, does not show the node
correctly at every time the node has been reachable from the root (5.2). D,
kept in RAM, holds the dirty index nodes, each with its got-dirty index: the
transaction in which it got dirty (5.3).

Each record also holds a startup pos, an earlier transaction index that
never decreases. The records after the startup pos of the last record are
the startup section, the part of the stream that startup reads.

Data nodes are written to the stream by the transaction that creates them.
Index nodes are written lazily: each one before its got-dirty transaction
leaves the startup section. A node that is still dirty after it is written
goes back to D as if it got dirty in the current transaction (Rule A).

Startup reads the startup section and rebuilds D from the got-dirty ids
stored in its records. It reads P as of the startup pos through the stream,
where a reference to a node that has a version in the section is followed to
that node's newest version (reconciliation, Rule R). Then it reruns the
transactions of the section.

The claims below hold for every run, a sequence of transactions, that meets
the model's assumptions (A1 to A5, section 3.4). They hold whether the
algorithm finds the nodes that got dirty by testing every index node or by
marking the nodes on the access path of the change, the changed nodes and
their ancestors (6.1, step 3), and whether it decides that a written node is
still dirty by the exact test or by BergDB's simpler, conservative one (6.1,
step 7). BergDB has no single root node but a chain of top nodes, which the
model handles as a virtual root (6.3); with a virtual root, the claims need
BergDB's test. A crash here preserves a prefix of complete abstract records;
byte recovery and hardware durability are not modeled.

* T1 Recovery. For any run and any crash, startup gives back the same P, for
  every node and every lookup time, and the same D.
* T2 Restart invariance. After startup, the database appends exactly the
  records it would have appended without the crash.

Decisions of 2026-10-12: Rule A rather than the alternative of section 7, so
that a node that stays dirty is written only once per startup section, and
Lean 4 for the proofs.


2 Time and transactions
=======================

* Transactions are T(1), T(2), ... Time i means just after T(i). T(0) is the
  primordial transaction that creates the initial structure. k is the last
  transaction.
* A lookup can use any time t from 0 to k. There is no reclaim in this
  model, so all history is kept.
* Each transaction appends exactly one record to the stream, R(i). In the
  2017 code, this is the user transaction with its piggybacked internal
  transaction, which writes index nodes. startup.md describes them as two
  transactions; one record per transaction is simpler and loses nothing.


3 The structure P
=================


3.1 Nodes and histories
-----------------------

* A node has an id, fixed when the node is created.
* A node has a history: a list of entries, each with the time it was added.
  Entries are only appended, and always with the current time. So the past
  never changes. This is what partially persistent means here.
* x@t, the content of node x at time t, is the list of entries of x with a
  time <= t.
* An entry may contain pointers to other nodes, as node ids.
* children(x, t) is the set of nodes that x@t points to with a live pointer.
  The structure decides which pointers are live, from x@t alone. In a key
  node, for example, a later klong for a key replaces the earlier one, so
  the pointer in the earlier klong is dead from then on.

Examples from BergDB. A key node, a node of BergDB's B-tree: its KEY klongs
(a key and a pointer), each with the time of its TIME klong; a DELETE bitmap
is an entry too. A top node (BergDB makes one when the B-tree gets a new
root node; 6.3): all its entries are added when it is created. A value node:
one entry and no pointers.


3.2 Data nodes and index nodes
------------------------------

A data node has no pointers and never changes after it is created. BergDB's
value nodes are data nodes. Every other node is an index node.


3.3 Reachability
----------------

* The entry node, root, exists from time 0. Every lookup starts there. For
  BergDB, it stands for the entry point to the chain of top nodes (`TopDs`,
  6.3); the details do not matter here.
* x is reachable at t if x is root, or x is a child at t of a node that is
  reachable at t.
* P@t is the set of nodes reachable at t, each with its content at t. A
  lookup at time t sees P@t and nothing else.
* Two structures are equivalent, P ≈ P', if P@t = P'@t for every time
  t <= k. Equivalent structures give the same answer to every lookup.


3.4 Assumptions
---------------

The theorems hold for every structure with these five properties.

A1 Determinism. T(i) changes P by adding entries at time i and by creating
   nodes. Which entries and nodes, with which ids, is a function of T(i) and
   P@(i-1) only. New ids are made from i and a counter, so a rerun gives the
   same ids.

A2 Only current nodes change. T(i) adds entries only to nodes that are
   reachable at time i, after the change. So every entry of a node is seen
   by a lookup at the entry's time.

A3 New nodes are reachable. A node created by T(i) is reachable at time i.

A4 Levels. Every node has a level, and every pointer goes to a node of a
   lower level. In a B-tree, the level is the height. This lets a
   transaction write children before parents.

A5 No resurrection (since 2026-10-15). A node reachable at time i, after
   the change, was reachable at time i-1 or was created by T(i). Marking
   (6.1, step 3) needs it.

The intended multiversion B-tree abstraction uses splits, parent repointing
and downward levels to meet these properties. That is not a proof that
BergDB's Java B-tree (`Dag`) satisfies them: A2 and A3 must also be checked
for compound transactions with transient nodes and multiple root changes. A
balanced binary tree with rotations does not automatically supply A4 with
fixed levels, since a child can become its parent's parent.

Since 2026-10-16, BergDB's Java transactions are built to meet A2 and A3
(F1-008-11; mismatch M1 of [011-11](../items/011-docs-archive/11-level2-alignment.md)). Two
checkers check A2 to A5, with the levels of 011-11, section
8.4, on every transaction of their runs: the trace checker, which runs the
Lean model on traces of Java runs (section 13), and the Java tier, a Java
stress test (`A2A3Check2`). That is a check on many runs, not a proof.


4 The stream
============

S is the list of records R(0), R(1), ..., R(k). R(i) is appended by T(i),
completely or not at all. The model has records, not bytes.

R(i) holds:

* T(i), enough to rerun it. Its data nodes (below) can be part of it, as in
  BergDB, where a stored transaction is its value nodes with their keys.
* s(i), the startup pos: a transaction index with s(i-1) <= s(i) < i.
  s(0) = 0.
* V(i), the node versions written by T(i), in order.
* gd(i), the ids of the index nodes that got dirty in T(i), including the
  ones that stayed dirty after being written (Rule A).
* top(i), a reference to the latest version of root.

A version v of node x, written in record w, holds:

* the id x and the record number w;
* the history of x up to time w, x@w. This is all of x's history so far,
  since entries are only added at the current time;
* a reference for each node y that the history points to, through a live or
  a dead pointer: the latest version of y in the stream at the moment v is
  written (versions earlier in the same record count), or none if y has
  never been written. In BergDB, the pointer then holds y's id, a vpos,
  instead of a stream position.

A reference names a version, (y, record), not just a node. lv(x) is the
latest version of x in S.

R(0) holds a version of every node of the initial structure, and gd(0) is
empty.


5 Good versions and dirty nodes
===============================


5.1 Good for a time
-------------------

A version v of node x is good for time t if:

1. its history gives x's content at t: the entries of v with a time <= t
   are x@t; and
2. for each child y of x at t, the reference in v for y is a version that is
   good for t.

Reading the stream from a version that is good for t shows exactly P@t below
that node. This is "complete for t" in 011-03. The definition
is recursive, and A4 makes the recursion end.

Stability. A version that is good for t stays good for t: versions never
change, and the past of P never changes.


5.2 Dirty
---------

At time i, a node x is dirty if it has no version yet, or if lv(x) is not
good for some time t <= i at which x is reachable. Otherwise x is clean.

This one definition replaces the "Rules of dirtiness" in startup.md. They
become consequences. If the reference in lv(x) for a child leads to a
version that is not good, x is dirty. Writing a node does not make its
ancestors dirty, since their latest versions do not change. An
implementation has two kinds of pointers: memory pointers, between nodes in
RAM, and stream pointers, from a version to a version. Dirtiness through
stream pointers (INV-CLOSURE in 011-03) needs no rule of its
own: the definition is about versions and does not know about memory
pointers.


5.3 D
-----

D is the algorithm's bookkeeping: a map from node id to a got-dirty index
d(x), a transaction index. Every dirty index node is in D (INV-2, section
8). D may also hold some clean nodes, if the algorithm's test of whether a
written node is still dirty is conservative (6.1, step 7).


6 The algorithm
===============

The database is DB = <P, D, S>, as in startup.md. P is the structure as the
running database knows it, in RAM and in the stream.


6.1 Transaction i
-----------------

1. Change. Apply T(i) to P at time i (A1).
2. Write data. Write a version of each data node created by T(i). Data nodes
   are clean from then on, since they never change.
3. Got dirty. Every index node that is not in D and is dirty now gets
   d(x) = i, and its id goes into gd(i).
4. Startup pos. Choose s(i), with s(i-1) <= s(i) < i, by any policy that
   depends only on S, D and T(i). (T(i) since 2026-10-16: BergDB's limit on
   the nodes taken, then, depended on the size of the transaction.) In
   BergDB (since bergdb 007-07): whole transactions from s(i-1) + 1 on, as
   many as the record's share of D asks for, in proportion to the stream it
   adds, and every one that starts at least the larger of twice the startup
   distance, a configured number of bytes, and the span of the section's
   transactions before the end of the stream (`takePolicy` in Lean).
5. Take. Remove every node with d(x) <= s(i) from D. These are the taken
   nodes.
6. Write index. Write a version of each taken node, lowest level first.
7. Still dirty (Rule A). Each taken node that is still dirty goes back into
   D with d(x) = i, and its id goes into gd(i).
8. Append R(i).

Step 3 is stated by what it achieves. An implementation finds these nodes on
the access path: the nodes created or changed by T(i), and their ancestors
at time i (section 11). Since 2026-10-15 the model has both forms
(`Algo.mark`): testing every index node, as above, and marking the access
path, BergDB's way. Theorem T13 (section 9) shows that they find the same
nodes.

Step 7 uses a still-dirty test. The model allows any test that is sound: if
the node is dirty after step 6, the test must say so. It may depend on P only
through P@t for t <= i. Two examples: the exact test (the definition in 5.2),
and "the node points to a node in D, through any pointer". The second is
BergDB's (`javaTest`; step 7 tests the taken nodes lowest level first). It is
easier to implement but costs more (section 11). T1 and T2 are proven for
both (section 9).


6.2 Startup
-----------

Given the stream R(0), ..., R(k), where R(k) is the last complete record:

1. Section. s = s(k). The startup section is R(s+1), ..., R(k).
2. D. For each j from s+1 to k, and each id x in gd(j): d(x) = j. Each node
   occurs at most once (INV-1, section 8).
3. Newest versions. Read R(s), ..., R(k). For each node y with a version
   there, New(y) is its newest version there. (Since 2026-10-16, as in
   BergDB, whose startup section begins with R(s); before, R(s+1), ...,
   R(k). The proofs needed only a < changed to <= in the lemma L-SEC,
   section 8.)
4. Rule R, reconciliation. Whenever the stream is read, a pointer to a
   node y that has a version in the section is followed to New(y),
   whatever reference the version holds for y, also when it holds none (a
   vpos).
5. P up to s. For t <= s, read P@t from the stream: start at top(k) and
   follow references, with Rule R.
6. Rerun. Rerun T(s+1), ..., T(k), each at its own time. Data node versions
   are not written again; they are already in the stream.
7. The result is <P', D', S>.

P' is not built in RAM. Only the nodes in D and the nodes the rerun touches
are in RAM; the rest is read from the stream when a lookup needs it. As a
mathematical object, P' is: for times t <= s, what step 5 reads; for times
after s, the content at s plus the entries added by the rerun.

T(s) is not rerun. Its changes are in versions written in the section or
earlier, as in startup.md.

Rule R is the reconciliation of v5 and of startup.md's edit of 2016-04-16,
made uniform: by node id, for every pointer, top nodes included. It needs
no prevPos chains, BergDB's links from a version to the previous version of
its node (G3 in 011-03). It covers references in
versions written before the section (E4), and it resolves vpos pointers.
That last part is needed: a version written before its child was first
written holds no reference for the child, and the child's first version can
be in the section. The Lean model found this (section 13).


6.3 The virtual root
--------------------

Since 2026-10-16 (F1-008-11, option (a) of
[011-11](../items/011-docs-archive/11-level2-alignment.md), sections 8.2 and 8.6), the root
can be virtual (`Spec.virt`), as in BergDB, which has no root node but a
chain of top nodes. Each top node points to the B-tree's root node of its
time and to some older top nodes; the newest, the super root, is the entry
point. In the model, the root's children are the top nodes; the root is
never in D and never written. top(i) names the root's child at s(i), the
super root at the startup time, and the record of its latest version.
Startup reads the root's children from that version through their pointers, live or
dead, with Rule R, rebuilds the root from them, and then reads as in 6.2.

The virtual root needs more assumptions (R1 to R4 of 011-11,
8.2, and two more): the root's entry for a child points to it; at most one
new root child per transaction, an index node with entries; a root child
gets entries only in the transaction that creates it; the root gets exactly
the entry for the new child; every older root child can be reached from the
new one through pointers between root children; and a root child that a
root child points to is not reachable. With a virtual root, T1 and T2 need
BergDB's still-dirty test. Startup finds an older top node only through the
references of newer ones, and the exact test can leave a top node with a
reference to a stale version of an older one: `exactWitness3` in
lean/SIS/Example.lean is a run where T1 then fails.


7 An example
============

A root R (level 1) with two leaves A and B (level 0). Policy:
s(i) = max(0, i - 2). Each transaction adds one entry to a leaf.

* R(0): versions of A, B and R. All clean, D is empty.
* T(1) adds an entry to A. A is dirty (changed), and so is R (its reference
  for A leads to a version that is not good for time 1). d(A) = d(R) = 1.
  s(1) = 0, nothing is taken. gd(1) = {A, R}.
* T(2) adds an entry to B. d(B) = 2; R is already in D. s(2) = 0.
  gd(2) = {B}.
* T(3) adds an entry to A, which is already in D. s(3) = 1, so A and R are
  taken and written, A first. R's reference for B is B's version in R(0),
  which is not good for time 2. So R is still dirty: d(R) = 3, gd(3) = {R}.
* T(4) adds an entry to A: d(A) = 4, gd(4) = {A}. s(4) = 2, so B is taken
  and written. B is clean.

D is now {R: 3, A: 4}. Suppose the database crashes after R(4).

Startup: s = 2, and the section is R(3), R(4). From gd(3) and gd(4), D' =
{R: 3, A: 4}, the same as D. New(R) and New(A) are in R(3), New(B) in R(4).
Reading P@2 starts at top(4), R's version in R(3). Its reference for B names
B's version in R(0), which does not have the entry of T(2). Rule R follows
New(B) in R(4) instead, which has it. Without Rule R, a lookup in B at time
2 would miss the entry. Then T(3) and T(4) are rerun.

This is the cost trade-off of Rule A in small: R is written in T(3) and
next when s passes 3, once per startup section. The alternative rule gives
a node that is still dirty the earliest time its new version is not good
for, here 2. It would have given R d(R) = 2 in T(3), written it again in
T(4) together with B, and needed no Rule R.


8 Invariants and lemmas
=======================

These hold after every transaction i of every run. They are the steps of the
proofs, which are checked in Lean ([../lean/SIS/Proof/](../lean/SIS/Proof/));
the text gives the ideas. The Lean names are in section 13.

INV-1 D is exact. D holds exactly the nodes in gd(j) for s(i) < j <= i,
each with d(x) = j, and each node at most once.
Why: step 5 removes everything up to s(i). A node goes back with
d = i > s(i). A node in gd(j) with j > s(i) has not been taken since, since
s has not passed j.

INV-2 Clean outside D. Every dirty index node is in D.
Why: by stability, a clean node can only become dirty for the new time i,
and step 3 catches that. A written node that is still dirty is caught by
step 7, since the test is sound.

INV-3 Clean before. If x is in D and its latest version was written before
d(x), that version is good for every time t < d(x) at which x is reachable.
Why: x then got into D in step 3 of T(d(x)), so it was clean at the end of
T(d(x)-1) (INV-2), and stability keeps its version good for those times.

INV-4 Unwritten nodes are new. If x is in D and has no version at all, x is
not reachable at any time before d(x).
Why: an index node without a version is dirty from its creation, so it got
into D in the transaction that created it, and it has not been taken since.

L-OUT. A latest version written before the section is good for every
t <= s(i) at which its node is reachable.
Why: if the node x is clean, lv(x) is good for every such t. If x is in D,
then d(x) > s(i) (INV-1). x did not get into D through step 7, since then it
would have been written in record d(x), which is in the section. So x got
dirty in step 3 of T(d(x)) and was clean just before. So lv(x) is good for
every t < d(x), and so for every t <= s(i).

L-SEC. A version written in the section, read with Rule R, is good for every
t <= s(i) at which its node is reachable.
Why, by induction on the level: let v be a version of x in record w > s(i).
It has all of x's entries up to time w, so condition 1 holds for t <= s(i).
For a child y, the reference in v names lv(y) as it was when v was written,
or none if y had not been written yet. If y has been written since, that
version is in the section, and Rule R follows New(y), which is good by
induction. If not, the reference names lv(y) now. It cannot be none: a node
without a version is in D (INV-2), with d(y) > s(i) (INV-1), and by INV-4 it
is not reachable before d(y); but y is reachable at t <= s(i). lv(y) is in
the section (good by induction) or before it (good by L-OUT).

Read with Rule R: a version that is good for t stays good for t when read
with Rule R, since a redirected reference leads to a version in the
section, good by L-SEC at a lower level. L-OUT and L-SEC are proven
together, by induction on the level.

L-RECON. Reading the stream from top(i), with Rule R, gives P@t for every
t <= s(i).
Why: top(i) is lv(root), good by L-OUT or L-SEC, and a version that is good
for t shows P@t.

L-BASE. P up to s, as startup reads it, has the same nodes as the run's P
after T(s), with the same histories.
Why: by L-RECON, reading at a time t <= s gives exactly the nodes reachable
at t. Each node gets the history of the version read at the last time
t <= s at which it is reachable, cut at s. By A2, the node has no entries at
later times up to s, so this is its whole history up to s. And by A3, every
node that exists at s is reachable at some time up to s.

L-RERUN. If P' and P have the same nodes after T(j-1), the rerun of T(j)
adds the same entries and creates the same nodes (A1), so they have the same
nodes after T(j).

Where Rule A matters. Only in L-OUT, through INV-1: a node in D that is not
written in the section got dirty after s. This suggests a generalization
to choices of d with s(i) < d <= i in step 7, recorded in the stream;
that generalization has not been formalized or proved in the current Lean
algorithm. Rule A takes d = i, the latest choice, so a node that stays
dirty is written once per startup section. The cost is that a latest
version can name versions that are no longer good, so startup needs Rule R.


9 Theorems
==========

A run is any sequence of transactions on a structure with A1 to A5, with a
valid startup pos policy, step 3 by testing or by marking, and in step 7
BergDB's still-dirty test or the exact one; with a virtual root (6.3), also
its assumptions, and BergDB's test only. (Until 2026-10-15: the exact test,
step 3 by testing, and A1 to A4.)

T1 Recovery. Let <P, D, S> be the state after T(k) in a run, and let
startup(S) = <P', D', S>. Then P' ≈ P and D' = D. In fact P' has the same
nodes as P, each with its whole history, not only what lookups see
(T1_nodes in Lean).

A crash keeps a prefix R(0), ..., R(k) of complete records, which is the
stream of the state after T(k). So after a crash anywhere, startup gives
back the state after the last complete transaction: every lookup, at every
time, gives the same answer.

Proof: D' = D is INV-1. P up to s(k) is L-BASE, and the rest is L-RERUN
for j = s(k)+1, ..., k.

T2 Restart invariance. A run with restarts after any transactions appends
exactly the same records as the run without restarts.

Proof: let <P1, D, S> and <P2, D, S> be states where P1 and P2 have the same
nodes. Running T(i) on each appends the same record R(i), and the new states
again have the same nodes. With T1, startup gives such a state. And T1 then holds for runs with any number of crashes and
restarts. This is Frans's goal of 2015-12-28, "a restart can be inserted
between any two transactions without affecting the bytes in the stream".
Same records give the same bytes if records are serialized
deterministically. The recovered 2017 Java code left padding bytes
uninitialized; that defect was fixed on 12 October. The recorded Java
restart checks now require byte equality, independently of this proof of
abstract-record equality.

Each step of T(i) depends on P only through its nodes: the change by A1,
dirtiness by its definition, the written versions by the nodes' histories,
the references by S, and the startup pos by S and D. In Lean, step 3 lists
the nodes by id, so the record does not depend on the order of nodes in the
list that holds P.

T13 Marking is exact (since 2026-10-15). After the change of T(i), an index
node that is not in D, other than a virtual root, is marked (on the access
path of the change) if and only if it is dirty. So both forms of step 3 give
the same D and the same records (`T13_markExact`). It needs A5: a node that
becomes reachable again with nothing changed below it could be dirty without
being on the access path.


10 Not in this model
====================

* Bounds (the planned theorems T3 and T4): the length of the startup
  section, the memory for D, the write overhead. They need a cost model and
  a policy for s(i). Since 2026-10-23 (bergdb item 007), T3 in a first
  form: with any cost of a record, and a policy that never asks for a
  startup pos before the one a startup distance d asks for, the startup
  section without its last record costs less than d, after every run
  (`T3_section`, lean/SIS/BoundTheorems.lean). Since 2026-10-28 (bergdb
  007-08), T3 for BergDB's take (6.1, step 4), with any share: after a
  transaction the section without its last record costs less than the
  larger of twice the startup distance and what it cost before, so less
  than twice the startup distance while it is constant, and after a
  decrease it shrinks with every transaction until it is below twice the
  new one (`T3_take`, `T3_take_decrease`). The record limit and the
  stream's meta blocks are left out. The size of the records at the ends
  of the section (T4) and the rest are open
  ([../items/007-bounds/](../items/007-bounds/readme.md)).
* Reclaim: cutting the front of the stream (INV-RECLAIM of
  [011-01](../items/011-docs-archive/01-problem.md); level 3 of levels.md), and eviction and the
  cache (the planned T5; level 4): not in sections 2 to 9; bergdb item 001
  added both, with their theorems (section 15).
* Concurrency, sync levels and torn records. A record is assumed complete
  or absent.
* Bytes. Records are values, not byte strings.


11 Obligations for an implementation
====================================

Found while writing the model. Not part of the proofs, but an
implementation must meet them.

* Finding got-dirty nodes. Step 3 is semantic. An implementation marks the
  nodes on the access path. This finds every dirty node only if every
  ancestor, at time i, of a changed node is on the access path, which holds
  if P@i is a tree. In BergDB it is: a node has at most one current parent.
  The model's marking (6.1) takes every ancestor; T13 shows it exact.
* The still-dirty test. The conservative test (points to a node in D through
  any pointer) is sound, but it can keep dead nodes dirty. A time split in
  the B-tree copies a node's current entries to a new node; the old node is
  dead from then on but stays for lookups at earlier times, and it shares
  children with the new one. A hot child, one that changes often, keeps
  such a dead node dirty. It is then written once per section for as long
  as the child stays hot, and every time split can add one more. The exact
  test compares, for each pointer,
  the time the pointer died with the time the child's latest version stopped
  being good. This matters for the bounds, not for correctness.
* References for dead pointers. A version must name lv(y) for each node y
  its history points to. For live pointers, an implementation knows lv(y)
  (to prove: the reading at s(k) reaches every node that is reachable at
  s(k) through its latest version). For a dead pointer, it may only know an
  older version, for example when the node was evicted while y was written
  through another parent. Keeping an older reference is correct for queries
  only if it is complete for every time the pointer may be followed and its
  backing bytes are retained. It can still give different records, so a
  modified reference rule needs its own restart/cache-invariance argument;
  query equivalence alone does not establish T2.
* One object per node. The model has one history per node id. An
  implementation must not let an object read from an older version stand for
  the node at a later time (G8 in 011-03).
* Finding the root. The model stores top(i) in every record. Any way to find
  lv(root) at startup will do. BergDB stores topPos in every record since
  2026-10-15 (format 5): the position of the super root at the startup time
  (011-11, mismatch M18; with a virtual root, top(i) of 6.3).


12 Compared with startup.md
===========================

| startup.md (2016)                         | Here                                   |
|-------------------------------------------|----------------------------------------|
| DB = <P, D, S>                            | The same                               |
| User and internal transactions            | One record per transaction (6.1)       |
| "dirty for database state i"              | Dirty, defined on versions (5.2)       |
| Rules of dirtiness                        | Consequences of the definition         |
| Becoming clean, readded to D with i       | Rule A, step 7                         |
| The Clean Rule                            | L-OUT and L-SEC                        |
| "Pointer reconciliation is required"      | Rule R and L-RECON                     |
| Recreate D from gd(i).ids()               | INV-1                                  |
| P(i) = P(i-1).exe(T(i))                   | A1 and L-RERUN                         |
| Induction over transactions               | The invariants, and T2                 |


13 Lean
=======

The model in Lean is in [../lean/](../lean/README.md).

* Milestone 1 (2026-10-12): the definitions of sections 3 to 6, the
  assumptions, and the statements of T1 and T2. The trusted part, the
  definitions and statements that a reader must check to trust the result
  (Lean checks the proofs), is the files Basic, Stream, Algorithm, Startup,
  Assumptions and Theorems, about 550 lines with comments.
* Milestones 2 to 5 (2026-10-12): the proofs, in lean/SIS/Proof/, about
  3,500 lines. T1_recovery, T1_crash, T1_nodes and T2_restart are proven, and
  `#print axioms` shows only Lean's standard axioms (propext,
  Classical.choice, Quot.sound): no `sorry`, Lean's placeholder for a
  missing proof.
* The definitions can be run. The example of section 7 runs in Lean and
  gives the D, gd(i) and s(i) of section 7; startup gives back P and D; and
  startup without Rule R gets time 2 wrong. A second example has four
  levels, data nodes, and time splits of leaves. A test program checks, on
  pseudo-random runs, that the examples meet the assumptions, and T1 and T2.
* 2026-10-15 and 2026-10-16 (F1-008-11): A5, marking and T13, BergDB's
  still-dirty test, Rule R from R(s), a policy that sees T(i), and the
  virtual root (sections 3.4, 6 and 9; lean/README.md, the changes to the
  trusted part). The trace checker (lean/Check/, `tracecheck`) runs the
  model's `init` and `step` on traces of Java runs
  ([trace-format.md](trace-format.md); [011-11](../items/011-docs-archive/11-level2-alignment.md),
  section 10).

The lemmas of section 8, by Lean name:

| Text     | Lean                                        | File           |
|----------|---------------------------------------------|----------------|
| INV-1    | `Inv.inv1`                                  | Proof/Run      |
| INV-2    | `Inv.inv2`                                  | Proof/Run      |
| INV-3    | `Inv.inv3`                                  | Proof/Run      |
| INV-4    | `Inv.inv4`                                  | Proof/Run      |
| The invariant holds after every transaction | `inv_st` | Proof/StepInv |
| Stability | `good_mono`                                | Proof/StreamLemmas |
| L-OUT    | `Inv.lout`                                  | Proof/Recon    |
| L-SEC    | `Inv.recon`                                 | Proof/Recon    |
| L-RECON  | `Inv.readAt_spec`                           | Proof/Base     |
| L-BASE   | `Inv.base_get?`, `base_sameNodes`           | Proof/Base, Proof/Recovery |
| L-RERUN  | `rerun_sameNodes`                           | Proof/Recovery |
| T1       | `T1_strong`, `T1_recovery`, `T1_crash`, `T1_nodes` | Proof/Recovery, Theorems |
| T2       | `step_congr`, `T2_strong`, `T2_restart`     | Proof/Restart, Theorems |
| T13      | `step_marked_iff`, `T13_markExact`          | Proof/Mark, Theorems |
| BergDB's still-dirty test | `step_java_child`          | Proof/Still    |
| The virtual root | `VInv`                              | Proof/Run, Proof/VStep |


14 What the proofs changed
==========================

From draft 1 to draft 2, all on 2026-10-12.

* Rule R must also follow vpos pointers (6.2, step 4). Found by the random
  test before the proofs: a version written before its child was first
  written holds no reference for it, and the child's first version can be
  in the section.
* A2 is stronger. Draft 1 said "entries only to nodes reachable at time
  i-1". That allows a transaction to add an entry to a node and cut the node
  off in the same step. No lookup sees that entry, so startup cannot rebuild
  it, and the node's next version would differ after a restart. The intended
  B-tree abstraction uses the stronger form; Java refinement remains open.
* A3 is weaker. "No resurrection" is not needed; only that a new node is
  reachable when it is created.
* Two invariants were missing from the sketch: INV-3 and INV-4.
* Step 3 lists the nodes by id, sorted, so that the record does not depend
  on the order of nodes in P. Needed for T2, where P after a restart is
  built in another order.
* The theorems were proven for the exact still-dirty test only. Since
  2026-10-15 they are proven for BergDB's test too (lean/SIS/Proof/Still.lean).
  That needed less than expected: only that the test looks at P through its
  nodes and puts back every taken node that is still dirty, which BergDB's
  test does because it tests the taken nodes lowest level first. No theorem
  that D stays closed upward (T15 of F1-008-08) was needed.

From 2026-10-15 to 2026-10-16 (F1-008-11):

* A5, no resurrection, is back: marking needs it (T13).
* With a virtual root, the exact still-dirty test breaks T1 (6.3).
* Rule R from R(s), as in BergDB: only a < changed to <= in L-SEC.


15 The physical layer, eviction and reclaim
===========================================

Added 2026-10-18 by Claude (Opus 5.5, Claude Code), bergdb item 001. The
model of sections 2 to 9 is logical: P, D and the stream. Item 001 added
what Java holds in memory and how it evicts (Level 4 of levels.md), and how
the front of the stream is cut (Level 3), each with its theorems, proved in
Lean with
only the standard axioms. The definitions and statements are in
[../lean/](../lean/README.md) ("What to read"); the design and its reasons
in [011-11](../items/011-docs-archive/11-level2-alignment.md), section 13 (the physical
layer, part 1), [001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), section 5
(eviction) and [001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), sections 2 and 5
(reclaim). Since bergdb item 009 BergDB evicts with handles
([009-02](../items/009-handles/02-implementation-plan.md), section 4), and since
bergdb 005-62 (2026-10-28) the model of eviction is that one only.

15.1 Memory: objects, pointers, handles
---------------------------------------

The physical layer is a memory of objects: each holds a node's history,
either the node's whole history (the canonical object, at most one per node)
or a version read from the stream (a snapshot). An object has a pointer per
pointee. Stage 1, lazy reading without eviction (`SIS/Phys.lean`), calls a
pointer a slot: a memory slot (to another object) or a stream slot (naming a
record); following a stream slot is a first touch, which takes the canonical
object if there is one, in the node table, else the version the slot names
after Rule R. The startup is stage 1's, whatever is evicted later.

With eviction (`SIS/Handle.lean`), each node that is in memory, or that a
pointer in memory names, has one live handle, in a table from node to
handle; the handle holds the node's one object, or none. A pointer holds a
reference (the record of the version it names) and a handle, or none until
it is first followed. A follow takes the handle's object when it can serve
the reference (canonical, or a snapshot at least as new: the fast path).
Otherwise the slow path raises the reference after Rule R to the written
position of the handle the pointer holds, takes the node's live handle, and
loads the version at that reference if the handle's object cannot serve it.
The writer, the algorithm of 6.1 on this memory, makes every node it reaches
canonical.

Eviction is one local operation, at any time between transactions: a live
handle whose object is not pinned and has been written dies, keeps a
canonical object's position as its written position, and its object leaves
memory; no walk, and nothing about the pointers that hold the handle. The
pinned objects are the root's and the canonical objects of D. The physical
writer writes from the pointers and the pinned set (`HMem.refOf`, the record
rule): a version names the latest version of each pointee (Option K of
[011-05](../items/011-docs-archive/05-level4-plan.md)), with no table of all
nodes. Before handles, the model had Java's earlier design: memory slots and
stream slots, with eviction as unswizzle and release (`SIS/Evict.lean`, until
bergdb 005-62).

15.2 What is proved for it
--------------------------

* Lemma M (`LM_newer`, `LM_ruleR`, `LM_cutTo`): a newer version of a node
  serves (is good for, 5.1) every time an older one serves, so Rule R's
  version does.
* T1-L (`T1_lazy`): after a lazy startup, reads at any time give P. A lazy
  startup, like Java's, does not read P up to s at startup (6.2, step 5)
  but reads each node from the stream when it is first touched.
* CC (`CC_canonical`): in a run with lazy restarts, every canonical object
  holds its node's whole history. T2-L (`T2_lazy`): such a run appends the
  records of the run without restarts.
* T-CACHE (`TC_handles`): with any reads and evictions between
  transactions, the physical writer with handles appends exactly the model's
  records and leaves the model's D, and the invariants hold: the table and
  the handles, INV-CAN (at most one canonical object per node, its live
  handle's), INV-SNAP (every other object is exactly the version at its
  position), INV-SLOT (what each pointer's record is; 001-08, 5.3 and 5.4)
  and those of the fast path. T-READ (`TR_handles`): reads give P. T2-C
  (`T2_handles`, `TR_handles_restarts`): with restarts too. T-PIN
  (`TP_handles`): every live handle whose object is not pinned may be
  evicted. Rule 4 by position (`Rule4Pos_handles`, `RunPos_handles`): Java's
  startup since bergdb 005-57 links what the model's rule 4 by node id links;
  after a safe cut too, where it skips the pointers below the stream's first
  position (`Rule4PosCut_handles`, `RunPosCut_handles`, bergdb 005-62).
  They assume three properties of BergDB's tree that Java runs meet: TREE
  (every reachable node but the root has exactly one current parent), A6'
  (no adoption, weakened: a node that x points to without it being x's live
  child is a data node, unreachable, or reachable from x through live
  pointers) and A-COPY (a new pointer copies a pointer only from a current
  node).

15.3 Reclaim
------------

A cut at record c (`SIS/Reclaim.lean`) leaves of every version before c a
stub (`Version.stub`): its position, no history. After a cut, lookups are
supported only from the first available time f on. To make cuts possible,
reclaim touches index nodes, making them dirty so that they are written
again. A cut is safe (`CutOK`) when c <= f, every version a read
from f on may follow is at c or later, every node of D has its latest
version at c or later with references below c to latest versions only, and
the top is after the cut. Then:

* T13' (`T13_markTouch`): with reclaim's touches, step 3 gives exactly the
  index nodes not in D that are dirty or touched.
* T8 (`T8_recoverCut`): startup from the cut stream gives the same lookups
  at every time from f on, and the same D.
* T9 (`T9_handles`): with eviction, reads through the handles in the
  running process from f on give the same on the cut stream as on the whole
  stream.
* T12 (`T12_restartCut`, and with eviction `T12_handles`): a run that
  restarts from safe cut streams appends the records of the run without
  restarts.

That Java's reclaim (its touches, rewrites and waits) gives safe cuts
(T-SCHEME) is checked, not proved: at every cut of every trace the checker
sees, and by running on the model's example (001-07, section
5).

15.4 Java against it
--------------------

The trace checker (`lake exe tracecheck`) runs the model's step on traces of
Java runs and compares every record and D, the first touches after
restarts (C-L), `CutOK` at every cut Java decides (C-CUT), INV-SLOT on
Java's physical states with eviction (C-P), and the invariants with handles
on Java's handle state (C-H, bergdb item 009). The gates, the test scripts
that must pass, run it:
`level2.sh` (step 7), `level3.sh` (step 8) and `level4.sh` (step 5).
