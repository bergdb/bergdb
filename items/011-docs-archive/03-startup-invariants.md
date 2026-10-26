BergDB startup: model, invariants and status
============================================

Draft 1, 2026-10-12. Written by Claude for Frans Lundberg.

Status, 2026-10-13: historical. This is the analysis of the 2017 code that
led to [sis-model.md](sis-model.md) and to the level 2 design in
[levels.md](levels.md). The defects it found are fixed, by that design rather
than by the experiments and next steps here (Rule R by node id instead of prevPos
chains, one node table instead of E1 to E6). For the current status, see
[levels.md](levels.md). Closure review cutoff: `ebe5f77`, 2026-10-13
18:02 CEST. The algorithms, failures and next steps below describe the
original investigation, not instructions for repairing today's code.

Formalizes requirement R3 (bounded startup) and invariant INV-RESTART of
[problem.md](problem.md): the algorithms as they are in the 2017 code, the
invariants they rely on, the proof obligations, and what the targeted test
[RestartInvariance.java](../java/stress/RestartInvariance.java) showed in those
experiments. The linked harness and Java files have since been repaired;
for unmodified source use the baseline commit of this repository (the 2017
source, original commit `49aa48d`). The initial harness and experiment patch,
[restart-experiments.diff](../java/stress/restart-experiments.diff), were made
against a source that already included the first delete repair, so that
source is not the unmodified baseline.

Builds on Frans's [startup.md](sources/startup.md)
(2016-05-05), [startup-1604.md](sources/startup-1604.md),
[2015-algos.pdf](sources/2015-algos.pdf) and
2014-08-startup.odt. Terms follow
2015-algos. Code references are to
[java/src/bergdb/](../java/src/bergdb/).


1 Model
=======


1.1 The stream
--------------

The stream S is a sequence of stored transactions T(0), T(1), ..., T(k) at
increasing positions tpos(0) < tpos(1) < ... A 128-byte meta block sits at
every multiple of 200,000 bytes; it is ignored here. T(0) is the primordial
transaction. Each stored transaction T(j) holds:

* tt(j), the transaction time, strictly increasing;
* sp(j), the startup pos after T(j): the tpos of an earlier transaction;
* the value nodes created by T(j), with their keys (the user data);
* index node versions (top nodes and key nodes) taken from D, see 2.1;
* gd(j), the ids (and positions) of the index nodes that got dirty in T(j).

A node version is the state of a node as written at one stream position.
A key node version also stores prevPos, the position of the previous version
of the same node. A top node version stores no prevPos:
StoredTopNode.getPrevPos() returns NULL.


1.2 Nodes, ids and versions
---------------------------

Every node has an id, given when it is created: a vpos, an odd number made
from the tpos of the creating transaction and a counter (Spos.nextVpos). A
node's spos is its vpos until the node is first written; after that, it is
the position of its latest version. Nodes are written at even positions
(index nodes at multiples of 8, value nodes at multiples of 4), so an odd
pointer value in a stored version is a vpos: a pointer to a node that had
not been written when the version was written.

Key nodes are append-only: a later version of a key node contains
everything the earlier versions contain, and more. Top nodes are immutable,
but they are written again when they are dirty, so a top node can also have
several versions in the stream. Value nodes are written once.


1.3 The Dag
-----------

As in 2015-algos: top nodes form TopDs, a deterministic skip list over time;
key nodes hold klongs (time klongs, key klongs, delete bitmaps); value nodes
hold values. A pointer is a memory pointer (to an object in memory) or a
stream pointer (a position). dag(t) is a tree for every time t, but the Dag
as a whole is not: after splits, a node can have several parents. At most
one parent is current, on a lookup path for the latest time. The others are
dead: on lookup paths for older times only.


1.4 Dirty nodes and D
---------------------

An index node is dirty if its latest stream version does not represent it:
it has never been written, or it has changes that are not written, or it
points to a node that is dirty (its stream version would point to an
outdated version).

D, the TransSeq, is a queue with one entry per transaction in the startup
section: (tpos(j), gotDirty(j)), where gotDirty(j) holds the index nodes
that got dirty in T(j). Every dirty node is in exactly one gotDirty set.


2 The algorithms as implemented
===============================


2.1 Executing a transaction
---------------------------

Db.executeInner() and Db.store(). Transaction T(i):

1. Puts and deletes change the Dag. Every index node reached while following
   pointers for a put, and every node created or changed, becomes dirty if
   it is not, and is added to gotDirty(i) (Db.makeDirtyIfNeeded, called from
   the pointer listener and the node change listener). New nodes get ids.
2. take (TransSeq.take): find the last entry j in D with
   tpos(j) <= length(S) - D, subject to a limit on the number of nodes per
   transaction. Remove the entries up to and including j from D and collect
   their got-dirty nodes. sp(i) = tpos(j).
3. Mark the collected nodes clean. Then, repeatedly, mark a collected node
   dirty again if it points to a dirty node, and add it to gotDirty(i)
   ("still dirty", DbHelper.handleStillDirtyNodes).
4. Append T(i): the value nodes, the collected index node versions, sp(i)
   and the ids in gotDirty(i).
5. Add (tpos(i), gotDirty(i)) to D.

Steps 2 to 4 are Frans's "internal transaction"; it piggybacks on every user
transaction.


2.2 Startup
-----------

Db.startInner() and DbStarter. Let s be the transaction at the startup pos
stored in the last complete transaction, and k the last transaction. The
startup section is T(s), ..., T(k), and startupTime = tt(s).

1. Read T(s), ..., T(k) and validate them.
2. Build nextMap (from prevPos: each version to the next version of the same
   node), posMap (the latest version of each node in the section, excluding
   nodes created after startupTime) and idMap (id to object, for all nodes
   read).
3. Forward the stream pointers of the posMap nodes along nextMap.
4. Cut every key node read back to its state at startupTime
   (KeyNode.toPreviousState).
5. Turn pointers between posMap nodes into memory pointers.
6. Find the super root at startupTime.
7. Rerun T(s+1), ..., T(k): for each stored value node, put its key and
   value, giving new nodes the same ids as in the original run. Then mark the
   nodes of gd(j) dirty, looking them up in idMap, or, if an id is not
   there, reading the node from the stream at the stored position. Rebuild
   D from the gotDirty sets.

T(s) itself is not rerun. Its changes are in the index node versions
written in the section: its got-dirty nodes were written by the transaction
that moved the startup pos to s. Nodes outside posMap are read later, on
demand, from their stored positions, without any forwarding.


3 Invariants
============

The proof of INV-RESTART, by induction over transactions as in startup.md,
needs the following invariants. The first three appear in Frans's 2016
documents; the last three are at most hinted at there.

INV-CLEAN, the Clean Rule. Every index node version written in T(i)
represents the node's state at time tt(sp(i)) completely: it contains all
changes up to that time, and each of its pointers that is valid at that
time leads, after forwarding, to a version that does the same for the
pointee. (startup.md says "clean at time s(i)", startup-1604.md says
"st(i)-1". The code does not rerun the transaction at the startup pos, so
s(i) is the right one.)

INV-ANCESTORS. If a node is dirty, all its current ancestors are dirty.
(startup.md, "Rules of dirtiness". In the code: the pointer listener marks
every node reached while following pointers for a put.)

INV-RERUN, determinism. Rerunning T(j) on the rebuilt Dag creates the same
nodes, with the same ids, and the same got-dirty sets as the original run.
(Needed for the step "P(i) = P(i-1).exe(T(i))" in startup.md; Frans's
"Recreatable TransSeq" plan, 2015-12-28.)

INV-ID, identity. Every node that is reachable for the current time (where
puts happen) has exactly one in-memory object for that use; it holds the
node's latest state (its latest version plus any unwritten changes); and D
holds exactly those objects. An object read from an older version, for a
lookup at an older time, may be complete only for older times (see
INV-FORWARD); it must never stand in for the node at a later time. (The
first part is implicit in startup.md: "recreate D from node ids stored in
S". Frans's 2016 Easter plan lists "Ensure *one* Java Node object per node
(per node ID)". The rest is not stated anywhere; section 5 shows why it is
needed.)

INV-CLOSURE. Dirtiness does not depend on how a pointer is represented: a
node that points to a dirty node is dirty, through a memory pointer or a
stream pointer alike.

INV-FORWARD. Define: a version of node X is complete for time t if it
contains all of X's changes with a time <= t, and each of its pointers that
is valid at t leads to a version that is complete for t. The invariant:
after startup, a pointer valid in the time interval [a, b) leads to a
version that is complete for every lookup time in [a, b) within the
retention window. So a lookup at time t only reaches versions complete for
t, and never follows a vpos: a vpos pointer can only sit in a version that
is used for times before the pointer became valid. (Frans's edit of
2016-04-16 in startup.md: "Pointer reconciliation is required.")

A complete runtime representation must serve every permitted time for
which it is used. The latest stored version is not automatically complete:
it may itself be dirty. Pointers valid now, with b = infinity, need the
complete current state for lookups, puts and the parent's next write.
A dead pointer, with b in the past, may use an older version only if that
version and its descendants are complete for all times in the pointer's
validity interval. Recency alone does not establish this condition.

INV-FORWARD is the property the startup really needs. Without restarts it
holds trivially: every pointer that matters is a memory pointer to the one
object of its pointee, which has all changes. After a restart, pointers are
stream pointers to whatever version was current when the pointing version
was written. Startup repairs this for the latest versions in the section
(nextMap). For everything else, it relies on INV-CLEAN together with the
dirtiness rules: if they hold, every version that a lookup reaches is
complete for the times it is used.

Dirtiness could be made time-relative in the same way, as Frans's 2016
definitions ("dirty for database state i") already are: a dead node needs
rewriting only if a child is incomplete for times before the node died.
The code's rule (any dirty child) is stricter; that costs extra writes but
is safe.


4 Proof outline and gaps
========================

Induction over i, as in startup.md: the startup algorithm works for DB(0);
if it works for DB(i-1), it works for DB(i) = DB(i-1).exe(T(i)).

* User transaction step. If P(i-1) and D(i-1) can be rebuilt, rerunning
  T(i) rebuilds P(i) and D(i). Needs INV-RERUN, and INV-ID for D.
* Internal step. Moving the startup pos from s(i-1) to s(i) writes the
  nodes in gotDirty(s(i-1)+1, ..., s(i)). Needs: all versions written are
  clean at s(i) (INV-CLEAN), and every pointer a lookup can follow resolves
  (INV-FORWARD).

Gaps in the 2016 proof:

G1. The internal step is asserted: "we know that all current nodes in S(i)
are clean for state s(i)". It must be shown that the take step and the
still-dirty rule keep INV-CLEAN, also for nodes that are written while
still dirty.

G2. The proof treats the Dag as if only current nodes mattered. Dead parents
keep versions that point to old versions of shared children, and lookups
for older times use them. Old versions written while a child was unwritten
hold vpos pointers. INV-FORWARD must be proven for every version reachable
for any time in the window, not only for the latest versions in the
section.

G3. Top nodes have no version chain. They are written again when dirty, but
StoredTopNode.getPrevPos() returns NULL, so nextMap has no entries for them,
and pointers to old top node versions are never forwarded. Frans noticed
this on 2015-12-28 ("StoredTopNode.getPrevPos() always returns Spos.NULL.
Hmm, is this correct?") and planned "Use field StoredTopNode.prevPos" in the
2016 Easter plan; the 2017 code still returns NULL. More generally, pointers
in versions read on demand from before the section are never forwarded.

G4. The proof takes for granted that the rebuilt D is the same D. That needs
INV-ID and INV-CLOSURE, which the code breaks after a restart (section 5).

G5. INV-RERUN is assumed and never checked. One test run broke it
(section 5).

G6. Deletes are not covered: delete bitmaps, time splits of nodes whose last
version has few or no live keys, and key nodes without klongs (which the
stream format rejects).

G7. Eviction is out of scope, but INV-CLOSURE matters even more with
eviction, since pointers to evicted children are always stream pointers.

G8. Versions versus ids. A stored pointer names a version (a position), but
the cache and idMap are keyed by node id. An object read from an old version
may be complete only for older times. After a restart, it can be found by
id and used for later times: by a lookup that follows a newer pointer, and
by a parent on a current path, whose next write then stores a pointer to the
old version as if it were current. Section 5 has examples. The theory must
say which object a pointer may resolve to: one that is complete for the
pointer's validity interval (INV-FORWARD).


5 Test results, 2026-10-12
==========================

Historical test behavior: the comparator then ignored got-dirty ordering
and uninitialized padding. The padding defect was fixed later on 12 October;
the current harness and Level 1–3 gates require byte-identical streams.
The commands below name the old workloads and need the old source/patch
combination to reproduce these failures, not the current `java/build/bergdb.jar`.

[RestartInvariance.java](../java/stress/RestartInvariance.java) runs the same
deterministic transactions twice: run A without restarts, run B with a
restart (sync, stop, start) every N transactions. At a checkpoint after
every N transactions, it compares the two streams, D (TransSeq.checksum()),
lookups against the transaction history (all keys at the latest time, and
300 random historical lookups), and INV-ID. The streams are compared by
content: transaction by transaction, with node versions, pointers and
got-dirty ids, ignoring the order of got-dirty ids and the padding bytes
(raw bytes differ anyway, since the serializer leaves padding bytes
uninitialized). Run A is the reference: it never violates INV-ID or
INV-LOOKUP in any run below.

Workloads: "small" is seed 1, 3000 transactions, 500 keys, values up to 40
bytes, startup distance 10,000 bytes, restart every 250 transactions.
"Large" is 12,000 transactions, 3000 keys, values up to 8,000 bytes, the
default startup distance (20 MB), restart every 4,000 transactions.

To run, after ../java/build.sh, from a scratch directory:

    JAVA_DIR=/absolute/path/to/this/repository/java
    CP=$JAVA_DIR/build/bergdb.jar:$JAVA_DIR/build/stress
    java -Xmx4g -cp $CP bergdb.core.RestartInvariance 1
    java -Xmx8g -Dsd=0 -Dn=12000 -Dkeys=3000 -Dvalsize=8000 -Devery=4000 \
        -cp $CP bergdb.core.RestartInvariance 1

The experiments need a jar built from a copy of java/ with the
diff applied: in the directory that holds the copy, run
`patch -p1 < restart-experiments.diff`.


5.1 The 2017 code as is
-----------------------

Small workload:

* Streams: run B differs from run A in T(260), the 11th transaction after
  the first restart. In B, T(260) records an extra got-dirty node, id 43747
  (last written at 77016), that A does not have: most likely a node that is
  dirty in A but whose Dag object in B is not marked dirty (next point).
* INV-ID: violated in B at all 12 checkpoints, starting right after the
  first restart, when 7 nodes in D are copies, not the Dag's objects. Cause:
  in step 7 of the startup, a got-dirty id that is not in idMap is resolved
  by reading the node from the stream, giving a second object ("TODO B" in
  DbStarter.rerunTransaction). Nodes that the rerun loads from the stream on
  demand are not added to idMap. The Dag's own object then has the rerun's
  changes but is not marked dirty, so those changes are written only if the
  node gets dirty again.
* D differs from run A at 11 of 12 checkpoints.
* Lookups: wrong results in B at 8 of 12 checkpoints, all for older times
  (for example, get(/k/436, t=3337) returns 35 bytes, should be 9).


5.2 Experiments
---------------

Patches to the 2017 code in
[restart-experiments.diff](../java/stress/restart-experiments.diff), switched on
with system properties. They test the invariants; they are not proposed
fixes, and are not applied to the source in bergdb/.

E1 (always on in the patch). During the rerun, register every node loaded
from the stream in idMap. No more copies in D. The first difference in
content moves from T(260) to T(750).

E3 (-Dexp3=true). Before the still-dirty check, turn stream pointers of the
nodes being written into memory pointers when a node with the pointee's id
is in memory, so DbHelper.hasDirtyChild(), which only looks at memory
pointers, sees every in-memory child. Example of the violation without E3:
before T(750), node 208367 points to the dirty node 294573 through a memory
pointer in A but a stream pointer in B. When 208367 is written in T(750), A
keeps it dirty, B does not. With E1 and E3, D is identical to run A's at all
12 checkpoints. But E3 matches by id, so it can pick an object loaded from
an old version (G8); with E3, the stress test does worse (table below).

E4 (-Dexp4=true). At startup, do two things: chain top node versions by id,
and forward pointers into versions written before the section by id, when
the node has a later version in the section. The runs do not tell which of
the two matters. With E1 and E3 but without E4, the large workload gives 18
bad lookups after the second restart. The first one is a historical lookup
whose path goes through top node 1024533 in a version written at 41 MB,
before the section; then key node 1024531, version at 41 MB; then key node
3039941, version at 23 MB, whose pointers to children that were unwritten at
the time are vpos values (odd positions). Reading one gives "unknown node
type, 0". With E1, E3 and E4: no bad lookups in the large workload.

E6 (-Dexp6=true). When following a stream pointer finds a cached object for
the node's id that comes from an older version than the pointer names, read
the newer version instead (G8). Without E6, following the pointer to
version 220456 of node 49797 returns the cached object loaded from version
107976, and a historical lookup gets a wrong value. E6 does not catch every
case: with E1, E3, E4 and E6, in T(512), B writes a key node whose pointer
for /k/430 names version 107976 of node 49797, where A names version 220456.
The parent got a memory pointer to the object from the old version, most
likely through E3, which matches by id.

A test of the stream alone: run A's stream (no restarts), restarted once at
the end with E1, E3, E4 and E6, gives correct lookups for 4 seeds of the
small workload. So the stream written without restarts appears to be
complete, and the remaining problems come from restarts in the middle.

Effect on [RestartStress.java](../java/stress/RestartStress.java), number of
failing seeds:

| Case | As is | E1 | E1+E4 | E1+E4+E6 | E1+E3+E4+E6 |
|---|---|---|---|---|---|
| Default settings, on disk, no deletes, restarts past 20 MB (5 seeds) | 5 | 5 | 0 | 0 | 0 |
| Default settings, deletes, several keys per transaction (10 seeds) | 10 | – | 10 | 10 | 10 |
| Random settings, no deletes (100 seeds) | 66 | – | 57 | 15 | 43 |
| Random settings, with deletes (100 seeds) | 68 | – | 60 | 34 | 53 |

"–" means not measured. The random settings use small startup distances
(100 to 100,000 bytes) and node sizes from 8 to 62 klongs.

Still failing with E1, E4 and E6:

* With deletes, almost every seed fails at startup with "Key node with size
  0": an empty key node was written in an earlier session. Found later the
  same day: a delete of a missing key of 7 bytes or more created a segment
  key node (the level 1 bug in [levels.md](levels.md), now fixed). With the
  fix and E1, E4 and E6, random settings with deletes fail 14 of 100 seeds,
  as without deletes; the default settings with deletes still fail 9 of 10,
  with other errors (a wrong checksum after the first restart, a corrupt
  read, ids that differ after a rerun).
* In one run with deletes, a got-dirty id resolves to a value node at
  startup: the rerun gave ids that differ from the original run (INV-RERUN,
  G5).
* Without deletes, 15 of 100 random configurations still fail: lookups after
  a restart return a wrong value or none.

Also found: DbStarter.checkStreamPointers() checks node.getSpos() instead of
the pointer's position for key nodes, so vpos pointers in key nodes pass the
check unnoticed. And on a cache hit, NodeCollection.followPointer() neither
turns the pointer into a memory pointer nor calls the pointer listener, so a
node reached that way is not made dirty by a put; that may break
INV-ANCESTORS after a restart. Patching the cache hit (-Dexp2=true) made no
difference in these runs.


6 Next steps
============

These were proposed after the initial failing experiments. They are
superseded by the abstract model in [sis-model.md](sis-model.md) and the
implemented Level 2 design and current priorities in [levels.md](levels.md).

1. Decide how pointers are resolved (G8, G2, G3). A pointer needs a
   version that is complete for the times it is valid: dead pointers can
   keep old versions, pointers valid now need the node's latest state. The
   code mixes the two through the cache. Options: keep objects read from
   old versions apart from the current ones (for example, keyed by position
   instead of id), or always resolve to the latest version by id, as the
   Bw-tree's mapping table does; that is simpler, but stronger than needed.
   This choice shapes INV-FORWARD and the proof.
2. Define dirtiness on the abstract structure (INV-CLOSURE), independent of
   memory and stream pointers, and prove that the still-dirty rule keeps
   INV-CLEAN (G1).
3. Add deletes to the theory (G6). The empty key nodes came from the delete
   bug in levels.md, now fixed.
4. Add a check of INV-RERUN to RestartInvariance: compare the ids created by
   each rerun transaction with the original run.
5. Then design the fixes. The experiments point at four: one object per node
   id at startup (E1), dirtiness through stream pointers (E3, done by
   version, not by id), version chains for top nodes (E4), and never using
   an object of an older version (E6).
