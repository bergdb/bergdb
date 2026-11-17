# 006-26 The proofs as of 14 November 2026

Created 2026-11-14 by Frans Lundberg. Status: done.

A standalone report on the state of BergDB's Lean proofs: what is proved, the premises
that are left, what the model covers and what it does not. Requested by Frans at 12:32 on
14 November. It describes `main` at `615f621b`, where `lean/` is as the night's last push
left it (`14f17be6`, 03:55).

An epub of this report, for reading offline, is
[26-proofs-status/006-26.epub](26-proofs-status/006-26.epub), made with
`pandoc 26-proofs-status.md -o 26-proofs-status/006-26.epub --metadata
title="BergDB proofs, 14 November 2026" --metadata author="Frans
Lundberg"`.

**Correction, 2026-11-15, 06:15 (coord-1114).** Three of the top
theorem's 10 premises are false as stated, for every parameter set:
`hCoU`, `hU` and `hHL` (proved in Lean, SIS/Tree/PremisesFalse.lean,
80828487). Each speaks of every writer state that meets a local
invariant, and those invariants carry none of the writer's books, so
an unreachable state refutes it; the run tests saw only reached states.
So `invGetScanOK_merges` holds vacuously and is not "reduced" as
sections 1 and 4 say. The night of 14 to 15 November (024-12, section
1; 024-22, section 11.1; 025-03) removed `hMF`, `hHL` and `hCoU` with no
statement change, and narrowed `hchk`; the current theorem,
`invGetScanOK_merges_joint6`, has the premises hp, hth, hchk5, htb, d4,
l4, hU, hMSF and hCoF, and is still vacuous while `hU` is false as
stated (`hMSF` and `hCoF` are likely false as stated too). The rest of
this report is as written on 14 November.

Three words are used strictly in this report:

- **Proved**: a Lean theorem with no premise left open. Its hypotheses are only
  definitions and parameters.
- **Reduced**: a Lean theorem that derives the result from named premises, where the
  premises are not themselves proved. A reduced result is not a proved result. It says
  only: if these smaller facts hold, the large one holds.
- **Tested only**: checked on runs, traces or examples. There is no theorem.

One more distinction matters. Many theorems are proved for *any structure that meets a
list of assumptions*. Such a theorem is proved as a statement about the model. As a
statement about BergDB it is reduced, until the assumptions are proved for BergDB's
tree. This report says which is meant each time.

IDs such as 024-12, 007-09 or TP7 are pointers for later. Nothing here depends on
following them.


# 1. Summary

**What there is.** BergDB's Lean model has two parts. The older part, the abstract
model, describes the stream: records, the dirty set D, the startup pos, startup,
reclaim's cut, lazy reading, and eviction with handles. It takes a transaction's change
to the index as given. The newer part, since 11 November, is the key tree itself: put
with its splits, delete with the upward unlink, the merges, root collapse and the
take-back, get and scan. It is a definition that runs. Run on Java's traces, it gives
Java's nodes, klongs and records exactly. `lean/` holds about 297,000 lines and 7,300
theorems. It has no `sorry`, no `admit`, no axiom of its own and no `native_decide`. The
24 main theorems, checked today, depend only on Lean's three standard axioms.

**The night's result.** One theorem, `invGetScanOK_merges_flat`, speaks of the tree
model with Java's parameters, at every node size from 8 up, 30 included. After every run
of transactions that the model runs without an error, the tree keeps its invariants, and
every get and every scan, at the latest time and at every earlier time, returns what a
plain reference map returns. This is **reduced, not proved**. It rests on 10 named
premises. None is about a get or a scan. Nine of the ten are about steps that only a
delete takes; the tenth is about a note that the writer keeps for its splits. Every put
case is proved. Each premise held on the model's own runs, at hundreds to tens of
thousands of states, with no failure.

**Proved, with no premise.**

- The startup section stays below twice the startup distance, and shrinks after a
  decrease. This is for BergDB's take without its byte limit.
- A record holds its transaction and at most as many index node versions as D has nodes.
- In the tree: the searches in a key node, the klongs' round trip, every put case, the
  nodes a merge or a split makes, and that LE-b never runs with the merges on, given the
  tree's live counts.
- For the abstract model, given its assumptions: recovery after a crash, restarts,
  lazy reading, eviction with handles, startup by position, safe cuts.

**Reduced to premises.**

- Gets and scans return the right data (the 10 premises).
- Recovery, restarts, lazy reading and eviction *for BergDB's tree*. The abstract
  model's assumptions on each transaction are stated for the tree, and most are not
  proved for it.
- Reclaim keeps the data: reduced to "each cut is safe", which is tested at every cut of
  Java's traces.
- The startup distance with the take's byte limit (one premise, measured with a wide
  margin).
- Bounded startup: one theorem, `bounded_startup`, with about ten open premises for the
  tree. Two of them, Q and Hp, may grow with the database's age. So "a cold start does
  not grow with age" is not shown for BergDB today.

**Tested only.**

- That Java does what the model does. This is the largest item, and it will stay a test:
  the trace checkers compare every traced transaction with the model.
- That the writer never ends in a `Bug`.
- The merges' costs, the bound on a transaction's dirty nodes, the node count against
  the live keys.
- Threads, bytes, torn tails, the cache's budget, the Pub layer's objects. They are
  outside the model.

**How much is left.** For the 10 premises the sources give two sizes: 2.5 to 3 hours of
prover work for a part of one premise, and "a night of its own" (1,500 to 2,500 lines)
for another. The night of 13 to 14 November took the count from 17 to 10 in its last two
hours; that day and night together used 72 % of the week's allowance. This report's estimate, not
the sources': the 10 premises are one to three more such nights, and the two about the
delete with the merges are the hardest. Bounded startup is further away and less
certain: two of its premises must first be measured, and may need a weaker statement.
Before any of this comes a cleanup, which is today's work. It makes the proofs smaller
and easier to change. It changes nothing in what is proved.


# 2. The model

## 2.1 The abstract model

The abstract model is the theory of the stream and of memory. Its Lean name is SIS,
for self-indexed streams. It has:

- a **structure** P: nodes with a level and a history of entries, each entry stamped
  with a time. Index nodes point to nodes on lower levels. Data nodes hold values.
- a **stream**: one record for each transaction. A record holds the transaction and
  versions of index nodes.
- **D**, the dirty index nodes not yet written, each with the time it got dirty.
- a **step** for one transaction: apply its change, write the new data nodes, mark the
  nodes that got dirty, run the still-dirty test, choose the startup pos (the take),
  append the record.
- **startup**: read the startup section and rerun its transactions.
- **reclaim**: a cut of the stream's front, and the touch.
- **lazy reading** and **handles**: nodes read from the stream at first touch, with any
  reads and evictions between transactions.

The abstract model knows nothing of keys. A transaction's change is produced by a
function called `exec`, which the model takes as a parameter. So its theorems hold for
any index structure that meets a list of assumptions. The main ones are these:

- `RunOK`: in every transaction new nodes get fresh ids, entries go only to reachable
  nodes, pointers go to lower levels, data nodes are never changed, and the root's
  rules hold. (A2 to A5 in the older documents.)
- TREE: every reachable node but the root is the live child of exactly one reachable
  node.
- Two smaller ones for eviction, called A6' and A-COPY, on what a pointer may name.
- `CutOK`: a cut removes nothing that a later read or startup needs.

## 2.2 The levels

BergDB's features are counted in levels, and the model follows them:

- Level 0 is the multiversion map in memory. Level 1 adds restart by replaying the whole
  stream.
- Level 2 adds bounded startup. The model has recovery, restarts and the bounds here.
- Level 3 adds reclaim. The model has the cut and its safety.
- Level 4 adds eviction. The model has lazy reading and the handles.

## 2.3 The tree model

Since 11 November the key tree is in Lean too (item 024-12, `lean/SIS/Tree`). It
restates Java's `Dag`, `KeyNode`, `GetMany` and `TopDs`:

- a key node as its klongs, with the six searches;
- put, with the splits and their cascade, and new segments for long keys;
- delete, with the upward unlink, LE-b, the take-back and root collapse;
- the merges at the delete, with record format 7's thresholds (8/17/17 at node size 30,
  scaled for other sizes), and the limit theta on dead klongs in a node (7 at node size
  30);
- the top node with its skip pointers, get, scan with an end key, and reclaim's touch.

The tree is plugged into the abstract model as its `exec`. The model's step with the
tree's `exec` is then BergDB whole: the tree makes the change, and the abstract model
makes the record and D. The Lean name for this instance is `treeSpec`.

The definitions that must be read and trusted are small: about 3,400 lines in ten files
for the tree, and about 9,200 lines of definitions, statements and examples for the
abstract model. Everything else is proof, which Lean checks.

The tree's properties are stated as numbered definitions, TP1 to TP40 (TP for tree
property). Three of them carry the main claim, and they are used throughout this report:

- **TP7**: after every run, at every time, the tree's invariants hold. These are the
  key order, the kinds of the nodes, a live klong in every node, the fill that the
  merges keep, at most M klongs in a node, and every pointer naming a node that exists.
- **TP10**: a get at time t returns the value of the key's last put at or before t, and
  nothing after a delete.
- **TP11**: a scan at time t returns the keys and values of the map at t in its range,
  in order, forward or backward, with the end key.

TP10 and TP11 compare the tree with a reference: a plain list of the transactions'
operations, searched from the start.

## 2.4 How Java is tied to the model

The tie is a test, not a proof. No theorem speaks of the Java code. Java writes traces
of its runs, and two Lean programs check them:

- The **trace checker** (`tracecheck`) runs the abstract model's own step on each traced
  transaction. It checks the model's assumptions on the change (`RunOK`, TREE, A6',
  A-COPY), that the model's step writes Java's record and leaves Java's D, the restarts,
  every cut of reclaim (`CutOK`), and the handle state under eviction.
- The **tree checker** (`treecheck`) runs the tree model on each traced transaction. The
  model must make Java's nodes with their ids, levels and kinds, and every klong of
  every changed key node. Gets and scans must give Java's answers. The tree's invariants
  must hold on Java's tree. And the model alone, given only each transaction's
  operations, its first node id and Java's startup pos, must write Java's records and D.

The scripts: `before-commit.sh` runs no Lean. `level2.sh` runs both checkers on the
small and the draining sets, `level3.sh` the trace checker on reclaim traces,
`level4.sh` on traces with eviction, and `night.sh` all of them and a medium set.

How much was run:

- The last night run on record is of 12 November. Its level 2 ran the tree checker on
  29,783 transactions and 318,980 operations, and the trace checker on 120 traces. Level
  3 checked 315 cuts, level 4 the handle state after 11,952 transactions. No check
  failed.
- With the merges, on 11 November: 239 traces, 54,877 transactions and 36,923 merges.
  The model gave Java's change, klongs and records in every one.
- `night.sh` was skipped on 13 November. Today the quick form of level 2 passed on the
  commit that became `main` (028-10).

What this tie cannot see:

- bytes: the record format, checksums, meta blocks, a torn tail;
- threads: the traces are of one writer, with no reader beside it;
- the inside of a transaction: only its net change is traced;
- the take's choice: the checker takes each startup pos from Java. A separate Java
  check compares Java's take with the model's;
- size: the traces are small and medium runs, up to node size 62. The large set of the
  tree checker has not been run, and the traces' keys are all text.

The tie has found faults all the same: three faults of the delete path that every other
gate had passed.

## 2.5 What the model covers, and what it does not

**Concurrency: not covered.** The model has one writer and takes one step at a time. It
has no threads and no locks. Reads at an earlier time are covered as a result (a read at
time t gives the structure at t), with no interleaving. The handles' model allows any
reads and evictions *between* transactions, not during one. The commit's conflict check
is not in the model. It is an algorithm, not a matter of threads, and is proposed as an
addition (026-14).

**Crashes and torn tails: partly.** A crash is modelled as losing the stream's tail at a
record boundary: the stream keeps its first k + 1 complete records. For that, recovery
is in the model (T1, section 3.1). A torn last record, checksums and damaged bytes are
below the model. "A crash leaves at most a torn tail" and "a synced append is durable"
are assumptions about storage. They are not yet written down in one list. Java's crash
tests check them on runs.

**The byte format: not covered.** The model starts above the bytes. A record is a list
of versions, a key is a list of numbers, and a value is one number. Meta blocks are not
modelled. The only encoding result is TP1: klongs and history entries are two forms of
the same thing, and nothing is lost between them. The bounds count versions, ids and
reads, not bytes. The take's byte limit is modelled as a count of nodes times a size.

**The cache and eviction: partly.** Memory pointers and stream pointers, canonical
objects, pins, and eviction of any unpinned object in any order are modelled, and the
theorems are proved from the assumptions of 2.1. The cache's budget, its policy, its
timing against readers and its memory use are not in the model.

**The Pub layer: mostly not.** The model is of the Core. One part of the Pub layer has
its own small model with proofs: the user indexes' protocol (`lean/BergDB/Index`, about
5,200 lines). Its theorems say that an index stays a function of the data and keeps no
stale entry, for any number of writers and crashes. Objects, the object format, and key
and value transformations are not modelled.

**Parameters other than Java's: covered, more widely than Java needs.** The top theorem
holds for every parameter set that meets a condition on the merge thresholds
(`MergeParamsOK`) and has theta 0 or at least 2. Java's thresholds meet it at every node
size from 8 up. So node size 30, the users' size, is covered, and so are the test
sizes. The level limits G (segments of a key) and H (height of a segment tree) are
parameters too, with no fixed value. **Not covered: the merges off.** That is the tree
of release 2026.4, and Java's tree below node size 8. The abstract model's theorems hold
for any structure, so they have no parameters to speak of.

**Key and value sizes: keys covered in shape, sizes not.** A key in the model is what
Java's `Keys.toSegments` makes: a list of segments, each a number below 2^62 with its
three lowest bits zero. Keys of any length are allowed. Since 13 November no theorem
depends on a fixed bound on key length or tree size (Frans's decision that day, after a
scan property was found false for very long keys). A run that needs more segments than G
or more height than H ends in an error in the model, and the theorems do not speak of
it. A value is a number that stands for its hash. Value bytes, large values, and the
user limits on key and transaction bytes are not in the model. Java against the model
on keys of raw bytes (the empty key, the bytes 0x00 and 0xff, exact segment lengths) has
not been run.

**Bounded startup: covered, reduced.** T3, T4 and a cold start's reads are in the
model, and joined in one theorem. Its premises for the tree are open (sections 3.5 and
5.1).

**Reclaim: the cut, not the iteration.** The model has the cut and its safety
condition, the touch, and two theorems on why the index nodes end up after the cut. It
does not have the iteration: the steps, the end key, the rewriting of values as a
mechanism, the waits, or that the stream kept comes back down after deletes. That the
scheme's waits give safe cuts is tested only.

**Merges: covered.** The merges are in the tree model, and the top theorem is for the
tree with the merges on. The merges' costs (at most one merge a level for a delete, and
the amortized count) are stated and not proved.


# 3. What is proved, by subject

For each subject: what the theorems say, what a user can rely on because of them, and
the category.

## 3.1 Recovery and restarts

- **T1** (`T1_recovery`, `T1_nodes`, `T1_crash`): after any run, and after a crash that
  keeps a prefix of complete records, startup from the stream gives back every node with
  its whole history, the same answer at every time, and the same D.
- **T2** (`T2_restart`): a run with restarts after any transactions appends exactly the
  records of the run without restarts.
- **T13** (`T13_markExact`): marking the access path of a change finds exactly the index
  nodes that got dirty. So Java's marking is as good as testing every node.

For the user: a crash loses nothing that was written whole, and a restart is invisible
in the stream.

Category: **proved for the model** from `RunOK` and BergDB's still-dirty test. **Reduced
for BergDB**: `RunOK` for the tree is stated (TP14) and not proved. It is tested at
every traced transaction of Java, and held on the tree model's own runs.

## 3.2 Lazy reading, eviction and handles

- With nodes read from the stream at first touch, reads at every time give the
  structure, and the records are those of the run without restarts (`T1_lazy`,
  `T2_lazy`).
- With handles, under any reads and evictions between transactions, the writer appends
  the model's records and leaves the model's D. Reads at every time give the structure.
  Every object that is not pinned may be evicted (`tc_handles`, `tr_handles`,
  `tp_handles`).
- Java's startup by position, in use since October, links what the model's startup by
  node id links (`rule4Pos_handles`).

For the user: eviction changes no answer and no record that is written.

Category: **proved for the model** from `RunOK`, TREE, A6', A-COPY and one more
assumption, that an appended entry keeps the live pointers it does not replace
(`LiveAppend`). **Reduced for BergDB**: `LiveAppend` is proved for the tree (TP15), the
others are not (TP14, TP16). They are tested on Java's traces.

## 3.3 Reclaim keeps the data

- **T8, T12** (`T8_recoverCut`, `T12_restartCut`): after a safe cut, startup from the
  cut stream gives every lookup from the first available time on, and the records stay
  those of the run without cuts.
- **T-COVER, T-LATEST** (`T_cover`, `T_latest`): if every value reachable at an
  iteration's end was rewritten at the cut or later, and every index node has a value
  below it, then every index node's latest version is at the cut or later, or the node
  is in D.

For the user: reclaim never removes data that a supported lookup needs.

Category: **reduced**. T8 and T12 rest on "the cut is safe" (`CutOK`). T-COVER and
T-LATEST prove a part of that from two premises, which the model takes as given: the
rewrites, and a value below every index node (TP27, stated for the tree, not proved).
The rest of the argument, that BergDB's waits give a safe cut (T-SCHEME), is **tested
only**: at every cut of Java's reclaim traces, and on an example in Lean.

## 3.4 The startup distance (T3)

P5 of the principles says that the startup distance bounds the startup section. In Lean:

- **`T3_take`**: with BergDB's take at any pace, and every setting of the startup
  distance at most M, the startup section without its last record costs less than 2 M.
  **Proved**, with one limit: this take has no byte limit on a record.
- **`T3_take_decrease`**: after the setting is lowered to sd', and n more transactions,
  the section is below 2 sd', or it has shrunk by at least n. **Proved**, for the same
  take.
- **`T3_takeB`**: the same bound of 2 M for Java's take with its byte limit, where the
  take stops at the first transaction that does not fit. **Reduced** to one premise:
  the debt D always fits in a record's room. Without the premise the bound is false in
  the model (an example has a section above 100 against a bound of 6).
- **`T3_takeB_count`**: the section then has at most N = 2 M / m + 2 transactions, where
  m is the least cost of a record. **Reduced**, to the same kind of fit premise.

For the user: with a fixed startup distance sd, startup reads less than 2 sd bytes of
stream, plus the records at the section's two ends.

The fit premise is tested: in 18 Java runs the byte limit never stopped the take, and
the debt was at most about half the room. Since today the builder refuses a startup
distance above 10^9. The stream's meta blocks are not in the model. The earlier
theorems, `T3_section` and its like, are proved for a policy that "keeps up", which
BergDB's take does not always do after a decrease. They do not apply to BergDB.

## 3.5 T4 and bounded startup

T4 bounds the records at the section's ends and the debt D.

- **T4's record** (`T4_record`, `T4_ends`): a record holds its transaction and at most
  |D| versions. **Proved**, with no assumption at all.
- **T4's debt** (`T4_debt_java`): with BergDB's own still-dirty test and its virtual
  root, every node x of D reaches, through pointers live or dead, a node that was
  changed or touched in the last few startup sections: one more than x's level.
  **Reduced**, to `RunOK`.
- **T4's count** (`T4_debt_java_tree_height`): |D| is at most a sum over the last
  Hp + 1 sections' changes, times (1 + Q + ... + Q^Hp). **Reduced**, to `RunOK`, TREE
  and three numbers explained in section 5.1: H, Hp and Q.

One sentence of the October argument turned out false: "D holds about the last two
sections". For a tree of height h it is the last h + 1 sections; two do not suffice. An
example in Lean shows it.

**`bounded_startup`** joins T3's count, T4 and a bound on the reads. It says: after any
run that meets its premises, a cold start makes at most F reads. A read is a version
that the start parses, a header read, or a pointer followed by the rerun.

```
F = (N+1)(V0+A+Dm) + 2 + N((H+1)A+Dm)Pt + 2N(H+1)(A+K) + 2NB
N = 2M/m + 2,   Dm = (1+Q+...+Q^Hp)(Hp+1) N (H+1) A
```

Category: **reduced**, with many premises. Section 5.1 lists them. No term of F counts
the keys directly, but H grows with the logarithm of the number of keys, and Q and Hp
are not known to be bounded as the database ages. F is also loose: it holds N squared,
and N is in the millions for a 200 MB startup distance and small records. Its value is
that it is a bound at all, and that it names every quantity that startup's cost can
depend on.

For the user, today: startup's reads are bounded in the model, given its premises. For
BergDB the bound is measured, not proved: a section that stayed at 1.00 to 1.14 times
the startup distance in the runs, and a cold start of about 46 seconds on the server s1
at 10M keys, measured when rule 4 went over to positions.

## 3.6 The tree: gets and scans

The main result is section 4. Proved outright, on the way:

- **TP9**: a search in a key node is a lookup among its live klongs.
- **TP1**: klongs and history entries correspond; nothing is lost between them.
- **Every put case** keeps the tree's invariants, the live counts, the bound on dead
  klongs, and the conditions for a correct get: a put into a leaf with room, into a full
  leaf with its split and cascade, and a put that makes new segments.
- **The scan never runs out of steps**, given the tree's invariants.
- **Earlier times follow from the latest time**: if the invariants, gets and scans are
  right at the latest time after every run, they are right at every earlier time.
- **LE-b never runs with the merges on**, given the live counts at the delete's start.
  No run had ever shown it; now it is a theorem.
- Four of the abstract model's assumptions for the tree: its structure is well formed
  (TP13), `LiveAppend` (TP15), and two on how the writer sees the root (TP17, TP18).

## 3.7 Node sizes

- **At most M klongs in a key node** (TP5): kept by every transaction. It is a part of
  TP7, so **reduced** with it.
- **The fill**: with the merges on, a node that an inner node names holds at least m
  live klongs (8 at node size 30). Also a part of TP7. It is exactly the premise `l4`
  for the deletes that are left. **Reduced.**
- **What a merge or a split makes**: every node that a merge or a space split makes
  holds at least m live klongs, a merge keeps all the klongs, and its nodes are in
  order (TP34 to TP38). **Proved.** So is the thresholds' condition for every node size
  from 8, and its failure at sizes 4 and 6 (TP28).
- **Dead klongs**: at most theta in a node after a write. **Reduced** (the premise
  `d4`).
- **The number of key nodes against the live keys** (TP31, "storage is proportional"):
  stated, **tested only**.
- **A transaction's dirty nodes** (`dirtyNodeBound`, TP23 and TP26): stated, **tested
  only**, on Java's traces. One piece of arithmetic is proved: if the bound is right, a
  transaction within the user limits fits in a record, at node sizes 8, 14, 30 and 62
  with a height limit for each.
- **A top node's pointers**: about 49 in Java. Not proved; it is a premise of bounded
  startup (Pt).


# 4. The top theorem of 14 November

## 4.1 What it states

The theorem is `invGetScanOK_merges_flat`, in `lean/SIS/Tree/LatestTopFlat.lean`. In
words:

> Take any parameters that meet the merge thresholds' condition and have theta 0 or at
> least 2. Assume the 10 premises. Then, after every run within reach: the tree's
> invariants hold at every time (TP7); every get at every time returns what the
> reference map returns (TP10); every scan does (TP11).

Its conclusion in Lean is the five statements below together, where `p` is the
parameter set:

```
InvPreserved p     -- TP7
GetOK p            -- TP10
ScanOK p           -- TP11
LatestGetOK p      -- TP10 at the latest time
LatestScanOK p     -- TP11 at the latest time
```

Two small theorems, `mergeParamsOK_java` and `theta_java`, are **proved**: Java's
thresholds and theta meet the two conditions on the parameters at every node size from
8. So the theorem applies to Java's parameters, node size 30 included.

"A run within reach" has an exact meaning (`Within` in Lean):

- every transaction has its keys in order, one operation a key, with keys as
  `Keys.toSegments` makes them;
- each transaction's first node id is above every id in use;
- **no step of the model's writer ends in an error.** The errors are a `Bug`, a corrupt
  structure, and a tree that would pass the level limits G and H.

The last point is a limit of the theorem. It does not say that the writer never reaches
a `Bug`. That is a separate property (TP8), stated and not proved; it is tested on the
model's runs and on Java's traces.

## 4.2 What is proved inside it

The theorem is an induction over the run, and inside each transaction over its
operations.

Proved outright, with no use of the 10 premises:

- every put case, as in 3.6;
- a delete that changes nothing, a delete of a key with no leaf, and a delete whose
  leaf has room and stays full enough for no merge to run;
- the klongs stay well formed through every rule of the writer; the kinds of the
  nodes; at most M klongs in a node;
- that right operations give right answers: once every operation keeps the tree, the
  writer's invariant and the key order, every get and scan at the latest time is right;
- earlier times, from the latest time.

Derived inside the theorem from the 10 premises. These were premises of earlier forms
of the theorem, and are no longer:

- for the delete with the merges: that it leaves a tree, the writer's invariant and the
  key order;
- the upward delete's stop node, with its cascade when it is full, and LE-b;
- every pointer names a node that exists (TP4), and the structure is a tree after every
  run;
- the bound on dead klongs after every run, and the nodes' heights;
- that every state between operations fits the fuel (the word is explained below).

Some words of the model, needed for the premises:

- **A state between operations**: the model runs a transaction as its operations in key
  order. The writer's state after some of them is a state between operations.
- **The take-back**: a node that a transaction makes and then makes unreachable is
  removed from the transaction's change, as in Java.
- **The fuel**: every descent in the model is a recursive function with a step budget,
  computed from G and H. Java has no fuel. "A state fits the fuel" means that no segment
  tree is deeper than the budget, so no descent can run out of steps there.
- **The live counts**: TP7's conditions on live klongs. Every node has a live klong
  (but an empty space root), an inner segment root has two, and with the merges on a
  node named by an inner node has at least m.
- **The made-for id**: for a node that a split made, the node it replaces (Java's
  `PutData.madeFor`).

## 4.3 The ten premises

Each premise is a statement about one operation or one step of the writer. All were
tested on runs of the Lean model itself, not on Java: small runs with the merges on, at
node sizes from 8 to 30 (most at 8, 10 and 14), with overwrites and pseudo-random mixes
of puts and deletes. No test failed. The test scripts are kept with item 024-12.

The names in the first position are the hypotheses' names in the theorem.

**Group A: the delete with the merges.** These two are the proof's hard core: a real
B-tree argument through the merges' loop.

1. **`l4`: a delete keeps the live counts.** From a state where the live counts hold, a
   delete with the merges on leaves a state where they hold.
   - Open only for three kinds of delete: a delete into a full leaf (the split and its
     cascade, then perhaps merges); the upward delete, which empties its leaf; a delete
     that leaves a leaf, named by an inner node, with at most m live klongs, so that the
     merges' loop and root collapse run. The other kinds are proved.
   - Believed because: the live counts held at all 6,420 states between operations of
     runs with merges and collapses, and at 8,843 more with Java's theta.
   - To prove: an invariant that excepts the nodes on the merged path until their
     merge, carried through the same step lemmas as `d4`. The pieces exist: a merge's
     nodes are filled, the parent's cascade is walked, root collapse leaves a root with
     two live klongs. The sources give no size. This report's estimate: the largest item of the
     ten.

2. **`d4`: a delete keeps the bound on dead klongs.** After the same three kinds of
   delete, every key node that the writer has read holds at most theta dead klongs.
   - Believed because: the bound held at all 11,927 states between operations, and at
     all 1,512 run ends (18,243 key nodes, 2,694 of them exactly at theta, none above).
     Inside deletes it held at 4,069 states. It is also checked on Java's traces.
   - To prove: one more clause in the invariant of about eight step lemmas of the
     delete. Every write there is guarded by Java's check, or makes nodes with no dead
     klong, or goes to the full-node rule, whose cascade is proved bounded. Left for the
     merge itself: that its new nodes' klongs are in strict order. No size given. This report's
     estimate: mostly mechanical, medium.

**Group B: fuel and heights.** These say that the tree does not grow too deep, or get
confused about who points to what, in the middle of a delete.

3. **`hchk`: a delete takes back only nodes that nothing else holds.** In Lean
   (`OpDelChk2OK`): a delete runs exactly as a copy of itself that checks, before each
   take-back, that no kept node points to the node, now or before the transaction; that
   a retargeted parent is a segment leaf; and that a root taken back has one holder.
   - Believed because: the copy gave the same result and state at 7,987 deletes: 160
     with a take-back in the upward loop, 2,305 with a merge's, 453 with root
     collapse's.
   - To prove: one of its checks is already proved. For the stop node's check and the
     segment-leaf check the sources say 2.5 to 3 hours of prover work. The holder checks
     should come from the proof that every pointer names a live node; the last check
     needs a walk of the made-for ids, as `hMF` does.

4. **`htb`: a node taken back is not deep.** Every node that a delete takes back, among
   those it found at its start, has a height below the fuel. With the heights it gives
   that every state between operations fits the fuel.
   - Believed because: 316 runs, 18,201 operations, 3,205 deletes that took nodes back.
     The fit itself held at about 14,000 operation boundaries.
   - To prove: an invariant on what is reachable through the delete's writes. The
     sources: "about 1500 to 2500 lines, a night of its own".

5. **`hMSF`: after a merge, the tree fits the fuel.** In Lean `MergeFitsOK`.
   - Believed because: all 3,032 states after a merge fit, among 11,057 states inside
     deletes that were checked.
   - To prove: the heights' bookkeeping carried inside an operation, which today is
     proved between operations and for a split's cascade. No size given.

6. **`hCoF`: after a step of root collapse, the tree fits the fuel.** In Lean
   `CollapseFitsOK`.
   - Believed because: all 635 states after a step of root collapse fit.
   - To prove: with `hMSF`, the same work.

**Group C: bookkeeping.** These are about the writer's books: versions of nodes before
the transaction, and who holds the nodes that the transaction made.

7. **`hU`: after the upward delete's loop, the writer's tree is a tree.** In Lean
   `UpUnlinkTreeOK`.
   - Believed because: a stronger form held at all 2,529 loop ends: 1,385 with a
     take-back in the loop, 954 with an unlink to the previous version, 173 with a
     cascade at the stop node.
   - To prove: with `hHL` and `hCoU`, an invariant on previous versions and on the
     holders of nodes made in the transaction. The sources note that the operations'
     key order seems essential to it: a node is split only before its keys' block ends.
     No size given.

8. **`hHL`: no kept node points to a node taken back.** At the upward loop's end, no
   node that was not taken back names a taken-back node, by a live klong now or in its
   version before the transaction. In Lean `UpHolderLiveRunOK`.
   - Believed because: it held at all 2,529 loop ends, and at all 56,404 states between
     operations.
   - To prove: with `hU`.

9. **`hCoU`: root collapse's previous version is sound.** When root collapse replaces a
   segment root that the transaction itself has written to, the tree with that root's
   previous version is a tree, and that version names only ids already given out. In Lean
   `CollapseUnlinkAllOK`.
   - Believed because: it held at all 173 replacements of a segment root in the runs,
     92 of them with a full leaf.
   - To prove: with `hU`. Its test count is the smallest of the ten.

10. **`hMF`: a made-for id names an old node.** At every state between operations,
    every made-for id is below the transaction's first id. So a split's "node I replace"
    is always a node from before the transaction.
    - Believed because: it held at all 56,404 states between operations.
    - To prove: a walk over every place that sets a made-for id, where each place
      knows the books of the node replaced. No size given. This report's estimate: the smallest of
      the ten.

## 4.4 What the theorem does not say

- Nothing about Java. It is about the Lean tree. Java is tied to it by the traces.
- Nothing about parameters with the merges off.
- Nothing about runs where the model's writer ends in an error (4.1).
- Nothing about the stream. It speaks of the tree's structure after each transaction,
  not of records, startup or reclaim. Joining it with the abstract model's theorems
  needs the assumptions of section 5.2.


# 5. The other open premises

## 5.1 Bounded startup's premises

`bounded_startup` has these premises. On 13 November at 16:14 Frans deferred the open
ones ("Would it help to relax 'bounded startup'? It could be done later."), so that the
night's provers worked only on TP7, TP10 and TP11.

- **`RunOK`** (TP14 for the tree): the abstract model's assumptions on each
  transaction. Open. Tested on traces.
- **TREE** (TP16): one live parent for every reachable node. Open. See 5.3.
- **The fit** (`hfit`): each transaction's dirty nodes fit in a record. Open in Lean.
  Measured in Java with a wide margin.
- **H**: the height of the root above the values, after every transaction. Open: the
  writer keeps the trees within the limits, but no theorem gives the height in the
  abstract model's terms. H grows with the logarithm of the number of keys.
- **Hp**: the height of every node of D, counted along *all* pointers, live or dead.
  Open. For a top node it follows dead skip pointers to older top nodes, so it may grow
  with the database's age. Not measured on Java.
- **Q**: the most parents of a node, counting every pointer that ever named it, live
  or dead. Open. A node that a split replaces keeps its pointers to its old children, so
  a long-lived node may gather old parents with age. No useful bound for Java is known.
  Not measured on Java.
- **A**: the size of a transaction's change: its new nodes, entries and touched nodes.
  A premise on the workload. The like statement for the tree, in operations (TP20), is
  open.
- **K**: the nodes that a transaction makes unreachable. Open. A first guess, H + 1 per
  operation, is refuted by an example: one delete with merges at four heights made 11
  nodes unreachable at H = 7. About 2 (H + 1) is the conjecture.
- **B**: the sibling nodes that a transaction's merges read, at most two a merge. Open:
  it needs the merges' cost bounds, TP32 (a delete merges at most once a level) and TP33
  (the amortized count). Both are open; TP33 is reduced to a statement about one merge
  step.
- **Pt**: the pointers of a top node's version, about 49 in Java. Not proved in the
  model.
- Not open: BergDB's still-dirty test and the take are definitions. `LiveAppend` is
  proved for the tree. The rule for the nodes that Java's deletes remove is proved for
  the tree, but for its count K.

The serious ones are Q and Hp. They are not just unproved: nobody knows whether they
stay bounded. The open question on them (007-09, Q4) has this default: measure both on
Java's traces at growing ages of one database first; if they grow, restate T4's debt
with weaker premises.

## 5.2 The abstract model's assumptions, for the tree

The theorems of 3.1 to 3.3 hold for BergDB's tree once these are proved for it. They
are stated in Lean as numbered properties:

- TP13, TP15, TP17, TP18: **proved** (3.6).
- **TP14** (`RunOK`): open. Tested on Java's traces and on the model's runs.
- **TP16** (TREE, A6', A-COPY): open. Tested the same way.
- **TP19**: the writer reads only nodes reachable before the transaction. Open. Tested
  on small cases.
- **`CutOK`** from reclaim's scheme: tested only (3.3).

## 5.3 Does the 14 November theorem discharge any of them?

No, not as theorems stand. It brings two of them near:

- **TREE.** Inside the top theorem, "the structure is a tree after every run" is
  derived, not assumed. But it is the tree model's own statement of a tree. No theorem
  connects it to the abstract model's TREE. And it rests on the 10 premises.
- **H.** The heights of the key nodes are tracked inside the top theorem. No theorem
  turns them into the height that `bounded_startup` asks for.

This report's reading: both links are bridge lemmas between two statements of the same fact, far
smaller than the 10 premises. Nobody has sized them. Everything else in 5.1 and 5.2
stays open and is untouched by the night's work.


# 6. What is neither proved nor reduced

## 6.1 Gaps

- **Java against the model.** Tested only, by the two checkers, on small and medium
  traces. It will stay a test.
- **No `Bug`** (TP8): the writer never ends in an error but the level limits. Tested
  only.
- **The merges off**: the tree of 2026.4 and node sizes below 8. No top theorem.
- **A delete of a missing key changes nothing** (TP12): tested only.
- **The costs**: a transaction's work against its path (TP20), a deleted key keeps no
  node (TP21), the klong and node counts (TP22, TP31), the merges' costs (TP32, TP33),
  the dirty-node bound (TP23, TP26). Stated; tested, some only on small cases.
- **The skip pointers' search** finds the top node of a time (TP24): tested only.
- **Reclaim's scheme** gives safe cuts (T-SCHEME): tested only. It has a written
  argument, gone through again on 11 November for the delete path of release 2026.4
  (024-09), but no Lean proof.
- **Everything outside the model** (2.5): threads, the conflict check, bytes, torn
  tails, the cache's budget, objects.
- **That the statements say what is meant.** Lean checks proofs, not intentions. The
  definitions are read and reviewed. Review has found real errors in them (6.3).

## 6.2 Stale or overstated text in lean/

These are known and not yet fixed. They are comments; no theorem is wrong. Their repair
is planned with the cleanup.

- **`bounded_startup`'s docstring** says: "F does not grow with the database's size or
  its age". That is wrong. H grows with the logarithm of the number of keys, and Q and
  Hp are not known to be bounded with age. The same docstring says that D "holds only
  nodes on the access paths of the last Hp + 1 sections"; the theorem says only that D's
  nodes *reach* such nodes through pointers.
- **`BoundColdDrop.lean`'s header** presents its assumption ("a change drops no
  subtree") as a fact of BergDB's tree, "to check on Java's runs". It is false for
  Java: one delete bitmap removes several children at once, and the upward delete
  unlinks a parent with its children. The file that replaces it says so. The old
  definition and its theorems are still on `main`, true of the model but not of BergDB.
- **`BoundCold.lean`'s header** says "rule 4 reads nothing" and that every object made
  at startup is a version read. Both are wrong for Java: rule 4 reads headers for a top
  node's pointers (the Pt term), and Java parses every version, repeats included.
- **`lean/README.md`** is behind. It says that the tree's properties are "without
  proofs". It names about a dozen of the 507 tree files. It does not name the newer
  files on the bounds: Java's removals, reads counted as reads, the byte limit,
  `bounded_startup`. It still presents the false assumption above as BergDB's. It says
  that T3 is proved "without its record limit", which was true until `T3_takeB`. It
  does not mention the top theorem.
- Smaller: a comment in the tree's property file names a file that does not exist
  (`Small.lean`). The snapshot of the old `docs/` says the tree's properties are "not
  proved but for four small ones"; it is a snapshot and is not updated by design.

## 6.3 Statements that were found false

The proving has refuted statements, and that is part of its value. None was a Java bug.

- TP11 (scan) as first stated, twice: a key with a segment of 2^63, and a key longer
  than the scan's fixed step budget. Both were faults of the statement. Fixed by
  defining keys as Java makes them, and by a step budget taken from the parameters.
- TP32 (the merges' cost) as first stated: false for a transaction that repeats and
  misorders keys, which Java does not make. Restated with premises.
- "D holds about the last two sections" (3.5).
- "A change drops no subtree" (6.2), and "H + 1 nodes become unreachable per operation"
  (5.1).
- During the night: a fuel bound over the whole path seemed false, then turned out to
  need a transaction that was not sorted; a descent condition for one delete case was
  false as stated, and its route was rebuilt.


# 7. The size and shape of lean/

Lines, counted today, without build files:

- `lean/SIS/Tree`, the tree and its proofs: 507 files, 227,923 lines.
- `lean/SIS/Proof`, the abstract model's proofs: 108 files, 50,364 lines.
- `lean/SIS`, the abstract model's definitions and statements: 51 files, 9,222 lines.
- `lean/BergDB`, the user indexes: 11 files, 5,220 lines.
- `lean/Check`, the checkers: 8 files, 2,413 lines.
- The programs at the top level: 9 files, 1,542 lines.
- In all: 694 files, 296,684 lines, about 7,300 theorems, 5,268 of them in the tree.

The tree directory had about 90,000 lines on the afternoon of 13 November. Between
16:13 and 03:45, `lean/` grew by 142,295 lines in 256 files. Every push in that time
was made after a full build and an audit of the new theorems' axioms.

Why it is so large:

- **Several versions of the same route.** When a premise was replaced by a weaker one,
  the provers added a new version of each theorem on the route and kept the old one.
  The versions carry suffixes: F2, F3, F4. 129 definitions and theorems have such a
  name. 30 more are numbered steps of one assembly (`delStepsOKF3_of_open10` up to
  `open16`, and their like for the take-back).
- **Two top theorems.** `invGetScanOK_merges` is the earlier form, with larger
  premises; `invGetScanOK_merges_flat` is the same theorem with its premises taken
  apart.
- **Two walks of the delete.** The delete is proved once for what a get reads and once
  for the take-back's books, with step lemmas of the same shape.
- **No library.** The model uses Lean's core only, so list and arithmetic lemmas are
  local.

The cleanup, which Frans made today's work: one name for each route, and one top
theorem. The superseded versions go. About 2,400 lines of dead routes were already
removed during the night.

- What it changes: the size, the names, how long a build takes, and what it costs to
  change the proofs when the algorithm changes. That cost is the open question behind
  it: the proof base more than doubled in one night.
- What it does not change: what is proved. The 10 premises stay 10. The trusted
  definitions (the tree, its readers, the stated properties) do not change; they have
  not changed since the morning of 13 November.


# 8. What is left, in order

Frans's rule of 13 November stands above the list: no release waits for proofs. The
Lean model and the trace checkers are kept up to date with every change. Proofs run on
spare tokens.

1. **The cleanup.** Today. With it, the stale comments of 6.2.
2. **A study of simpler algorithms for the remaining premises** (026-16), started today
   beside the cleanup: whether a change to the algorithm would make the open deletes
   easier to prove.
3. **The 10 premises.** When they are proved, TP7, TP10 and TP11 are proved for the
   tree model with the merges on. Frans planned provers for tonight. In the order of
   the tree item's notes:
   - `l4` and `d4`, the three kinds of delete. No size given; the largest part, by this report's
     estimate.
   - `hchk`: 2.5 to 3 hours for its stop-node part, the holder checks beside.
   - `htb`: a night, 1,500 to 2,500 lines.
   - `hU`, `hHL`, `hCoU`: one invariant on previous versions and holders. No size given.
   - `hMSF`, `hCoF`: the heights inside an operation. No size given.
   - `hMF`: a walk of the made-for ids. No size given; small, by this report's estimate.
4. **The bridges to the abstract model**: TP14 (`RunOK`), TP16 (TREE, A6', A-COPY),
   TP19. With them, recovery, restarts, lazy reading and eviction are proved for
   BergDB's tree, not only for "any structure that meets the assumptions". On 11
   November this part and the top theorem were each guessed at one to two weeks of
   prover work; the top theorem then reached its 10 premises in about two days.
5. **Bounded startup's premises** (deferred): first measure Q and Hp on Java's traces;
   then TREE and H through the bridges, A, K, B with the merges' costs, Pt, the fit.
6. **The costs**: the dirty-node bound, the node count, the merges' costs.
7. **Reclaim's scheme** (T-SCHEME). Judged earlier as several days with an uncertain
   outcome. A proposal of 13 November (026-14) goes further: reclaim's whole iteration
   in the model, then the stream format as bytes, then the commit's conflict check, and
   one written list of the assumptions on storage, the runtime and the single writer.
   Frans has not decided on it.
8. **The tie to Java**, beside all of this: the large trace set, keys of raw bytes, and
   a night run after the changes of 13 and 14 November.


# 9. How this report was checked

- **Sources read**: the top theorem's file and the definitions of its premises; the
  stated properties; `bounded_startup` and the T3 and T4 statements; the tree item
  (024-12, section 1 and parts of 5 and 6); the merges item (024-22, the night's state
  note); the bounds item (007-09, sections 1, 5 and 6); the model-gap item (024-06) and
  the scope proposal (026-14); the day reports of 13 and 14 November and the night's
  event log. Notes on the other bounds items, the levels document and `lean/README.md`
  were gathered separately and spot-checked against the Lean source.
- **Forbidden words**: a search of every `.lean` file under `lean/` found no `sorry`,
  no `admit`, no `axiom` declaration and no `native_decide`.
- **Axioms**: the main tree's `lean/` has no fresh build, so `#print axioms` was run in
  the built copy that the night's last check left. Its `lean/` is identical to `main`'s
  (an empty diff). 24 theorems were asked, among them the two top theorems, the two
  theorems on Java's parameters, `bounded_startup` and its tree form, T1, T2, T13, the
  T3 and T4 theorems named here, and the reclaim theorems. All depend only on `propext`,
  `Classical.choice` and `Quot.sound`, Lean's standard three.
- **Counts**: the lines and files were counted today. The test counts of the premises
  are from the tree item and the provers' closing notes; the scripts were not run again.
- **Not verified here**: that the open tree properties (TP8, TP12, TP14, TP16, TP19
  and the costs) have no proof anywhere under another name; a search by name found
  none. The user indexes' theorems and the handle theorems' exact premises were checked
  by name only. The Java measurements are quoted from the items. No conformance run on
  Java was made for this report.
