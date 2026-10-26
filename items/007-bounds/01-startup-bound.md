007-01. Bounded startup: the claim, T3, and what remains
=========================================================

Created 2026-10-23 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request of that day:

> My current top prio is to show that the database starts within a bounded
> time, O(1). Given a startup distance setting the length of the startup
> section is bounded and thus the time to start the database. [...] In
> practice, the db user should be able to rely on "it starts within 10
> seconds" or something. Independent of database size and for how long it
> has run.

Based on bergdb at `f6bc3ce`. The first theorem, T3, is proved in Lean
(section 3). The rest is analysis and a plan, with decisions for Frans in
section 8. A finding on the way, 007-02: one large transaction can stop
the startup pos for good.


1 The claim
-----------

In the terms of [sis-model.md](../../docs/sis-model.md), with d the startup
distance:

    Startup reads about d bytes of the stream and reruns only the
    transactions in them, whatever the size of the database and however
    long it has run.

The time then follows from the machine. Measured on F53 with a warm OS file
cache ([levels.md](../011-docs-archive/04-levels.md), "Default startup distance 50
MB"): 0.36 to 1.45 s at the default of 50 MB; 7 to 29 ms per MB of section,
or 15 to 25 µs per transaction rerun.

Frans's requirement 4 of 2016 ([startup.md](../../docs/sources/startup.md)):
"The startup time of DB must be O(1), or at least not greater than
O(log(G.size()))". Both halves show up below. What startup reads is O(1)
in the size and the age of the database; the rerun's work in the tree has
the height of the tree as a factor, O(log n) (5.2).


2 What startup costs
--------------------

Java's startup (`DbStarter`; the lazy startup of lean/SIS/Phys.lean):

1. It reads R(s), ..., R(k), the startup section and the record at the
   startup pos, in order.
2. It rebuilds D from gd(s+1), ..., gd(k), and Rule R's map from the
   versions in R(s), ..., R(k).
3. It reruns T(s+1), ..., T(k). Each transaction walks the tree as it did
   the first time. A node that is not in memory is read from the stream at
   its first touch: a random read.
4. It reads the nodes of D that the rerun does not reach (random reads), and
   links D (rule 4).

All of it is a function of the section: its bytes (1, 2), its transactions
(3), its got-dirty lists (2, 4), and what the transactions touch (3). D has
at most as many nodes as the section has bytes / 16, since each got-dirty
id takes 16 bytes of a record. So a bound on the section is the core of a
bound on startup.


3 T3: the section is bounded (proved)
-------------------------------------

In Lean: [lean/SIS/Bound.lean](../../lean/SIS/Bound.lean), the
definitions; [lean/SIS/BoundTheorems.lean](../../lean/SIS/BoundTheorems.lean),
the statements; lean/SIS/Proof/Bound.lean, the proofs (285 lines); and
lean/SIS/BoundExample.lean, checks by running. No `sorry`: `#print axioms`
gives Lean's standard axioms only.

**The cost model.** The model has records, not bytes. T3 takes any cost of
a record, `size : Record V T → Nat`. For Java's startup distance it is the
record's bytes in the stream. It could as well be an estimate of the time
to read the record and rerun its transaction (5.4). `S.cost size a b` is
the cost of R(a), ..., R(b-1).

**The policy.** In transaction i, the startup distance d asks for the
startup pos `sdTarget size d S`: the last transaction j < i whose record
begins at least d before the end of the stream. S is the stream before
R(i), as in Java's `TransSeq.take`. (Java's positions also count the meta
blocks, 128 bytes every 200 kB, which makes its take slightly more eager.)
A policy keeps up with d (`KeepsUp`) if it never asks for an earlier
startup pos. `sdPolicy` asks for exactly that one.

    theorem T3_section (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
        (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T) :
        let S := (run sp al ts).S
        S.cost size (lastSp S + 1) (S.length - 1) < d

In words: in every run whose policy keeps up with a startup distance d > 0,
after the last transaction k, the section without its last record,
R(s+1), ..., R(k-1), costs less than d.

The same file has four more:

* `T3_restarts`: the same for runs with restarts after any transactions.
* `T3_reads`: startup reads R(s), ..., R(k) for less than d plus the costs
  of R(s) and R(k).
* `T3_rerun`: if every record costs at least m, startup reruns fewer than
  d/m + 1 transactions, and their records cost less than d plus the cost of
  R(k). In Java every record has at least 48 bytes, so a section of 50 MB
  has at most about a million transactions.
* `T3_bounded`: if every record costs at most M, startup reads less than
  d + 2M, and reruns records that cost less than d + M.

The proof is short. The policy and the clamp of step 4 put s(k) at or after
the target, or at k-1, where R(s+1), ..., R(k-1) is empty. If R(s+1), ...,
R(k-1) cost d or more, then R(s+1) begins at least d before the end, and
the target would be at s+1 or later. Nothing
else is used: not A1 to A5, not the still-dirty test, nothing of P. So T3
holds for every structure and every run, of any length. Its one premise is
the policy.

Checked by running (BoundExample.lean): the policy of the example in
section 7 is a startup distance of two records; on random runs of example 2
with a cost like bytes, the bound holds with `sdPolicy`, with and without
restarts; and a sketch of Java's take with a tight node limit does not keep
up (its section reaches 1.4 d).

T3 leaves two things open, the subjects of the next two sections: Java's
take does not keep up, and the records at the ends, R(s) and R(k), can be
large.


4 Java's take, and the debt of D
--------------------------------

### 4.1 Java's take does not keep up

`TransSeq.take` takes whole transactions from the front of the section
while they begin at least the startup distance before the end. After the
first two it stops when the nodes taken reach a limit: 4 per value of the
current transaction and 1 per KB (`nodeCountLimit`). And it stops before a
record would pass the record limit of about 2 GB, even before two (bergdb
005-17). So it does not keep up, and T3 does not apply to it
([problem.md](../011-docs-archive/01-problem.md), Q4).

Measured, the section stays near d but goes past it (levels.md): up to
1.36 d with 1M keys at 20 MB, 2.21 d with 10M keys at 20 MB, 1.67 d with 1M
keys at 5 MB.

The record limit can stop the take for good: a transaction whose got-dirty
nodes need more bytes than one record can hold is never taken, and the
startup pos stays before it for ever. See 007-02.

### 4.2 The debt of D

Call the debt of D the bytes it takes to write the nodes of D: about 360
bytes per key node (levels.md), and 16 more for a got-dirty id if it stays
dirty. Every node of D must be written before the startup pos passes the
transaction in which it got dirty. So the debt must be paid within the
section, by any policy. The debt is large when many index nodes are dirty
at once: when a section's transactions touch many nodes, each once.

The measured overshoot follows the debt. With D's largest size (sampled,
levels.md) times 360 bytes as the debt:

| Run | d | D, max | Debt / d | Section, max |
|---|---|---|---|---|
| 10M keys, uniform | 20 MB | 111,000 | 2.0 | 2.21 d |
| 1M keys, uniform | 5 MB | 20,000 | 1.44 | 1.67 d |
| 1M keys, uniform | 20 MB | 63,000 | 1.13 | 1.36 d |
| 1M keys, 40 puts | 50 MB | 119,000 | 0.86 | 1.22 d |
| 1M keys, uniform | 50 MB | 90,000 | 0.65 | 1.00 d |
| 1M keys, hot | 5 MB | 7,600 | 0.55 | 1.22 d |
| 1M keys, hot | 20 MB | 31,000 | 0.56 | 1.07 d |
| 1M keys, hot | 50 MB | 72,000 | 0.52 | 1.00 d |
| 1M keys, uniform | 200 MB | 215,000 | 0.39 | 1.00 d |

A hypothesis that fits all nine: with Java's take, the section reaches the
larger of d and the debt, plus at most 0.25 d of lag from the node limit.
To check with a test that drives the debt up (8, step 3).

A policy can pay the debt in three ways:

* A. Spread it over many records, as Java's take does. The records stay
  small, and the section grows to about the debt.
* B. Pay it when due, as `sdPolicy` does, or with a deadline. The section
  without its last record stays below d, but one record can hold a large
  part of the debt, at most all of D. Startup reads that record in order;
  it does not rerun it.
* C. Pay it as it arises: keep the section plus the debt below d. Then the
  section and every record stay below about d. The price: nodes are written
  earlier and more often. With the same d the section is shorter, by the
  debt, and the write overhead higher.

### 4.3 What the minimum of two transactions gives

Even without a deadline, the take's minimum of two transactions bounds the
section, if the records are bounded and the record limit never stops the
take (it does in 007-02). A proof sketch, not in Lean: let every record
cost between m and M. When the target is at least two transactions past
the startup pos, the take takes at least two, and the section loses a
record. Otherwise the take reaches the target, and by T3's argument the
section without its last record is shorter than d, so it has fewer than
d/m + 1 records. So the section never has more than d/m + 1 records, and
costs at most (d/m + 1) M.

So the answer to Q4's "without bound" is no, under those conditions. But
the bound is too weak to promise anything: with d = 50 MB, m = 48 bytes and
records of 4 KB, it is 4 GB.


5 What else a bound on startup time needs
-----------------------------------------

**5.1 The records at the ends.** A record holds T(i), its value nodes,
gd(i) and the versions of the nodes taken, which come from D. So R(s) and
R(k) cost at most a transaction plus the debt. Bounding the debt is T4
(section 6). For the time, the ends matter less: R(s) is not rerun, and
R(k) has one transaction; the rest of each is read in order.

The versions must be bounded too. BergDB's nodes hold at most a fixed
number of klongs. The model's example 2 does not have that: its mid nodes
get an entry at every split of a leaf, so its records grow with the run.

**5.2 The rerun.** Rerunning T(j) costs about what running it did the first
time, without the index writes: its keys times the height h of the tree
(more for keys longer than 7 bytes, problem.md, Q2). BergDB never merges
nodes, so h is the log of the largest tree the database has had (Q1),
about 4 to 7 for a million to a billion keys. So the rerun is O(log n) per
key, as every lookup is. That is the second half of requirement 4.

**5.3 First touches.** The rerun reads each node it reaches that is not in
memory. Nodes with a version in the section come with it; the others,
clean nodes written before the section, are random reads, at most h per
key. With a cold disk cache they can dominate: 100,000 random reads of
100 µs take 10 s. The measurements so far had a warm OS file cache. To
measure (8, step 4).

Note, 2026-10-26: measured since, a cold startup on s1 takes minutes, and
its time goes to rule 4's header reads in `DbStarter.linkD` (step 4 of
section 2), one random read per stream pointer of D that startup's maps do
not resolve, about 590,000 at 10M keys, rather than to the rerun's first
touches ([004-02](../004-indirect-swizzling/02-scale-tests.md), 10.5.8;
unchanged with handles, 009-03). See 007-04, 3, and 007-03, step 6.

**5.4 Bytes or time.** Startup time follows the transactions rerun more
than the bytes: 29 ms per MB with 100-byte values, 7 with 10 kB (levels.md,
which adds that "a default given as a target startup time would fit all
value sizes better than a byte count"). T3 holds for any cost of a record,
so the startup distance could be a time: size(R) = a × bytes + b × keys,
with a and b from measurements. T3 then bounds the estimated time directly.


6 T4: the size of D
-------------------

D bounds the records at the ends (5.1), and it is the memory that eviction
cannot free (problem.md, R6; 72 to 95 MB at the default of 50 MB,
levels.md, "Bounds, measured").

By INV-1, D holds the nodes of gd(j) for the transactions j of the section.
A node gets into gd(j) in step 3, on the access path of T(j)'s change (the
changed nodes and their ancestors), or in step 7, taken and still dirty.

* With the exact still-dirty test, a written node stays dirty only if it is
  reachable at a time after s with a child that is dirty then. So D holds
  the nodes changed in about the last two sections and their ancestors at
  those times: at most h times those changes, with A4 for h and TREE (one
  current parent).
* With BergDB's test (Rule A over all pointers), a written node stays dirty
  while any pointee is in D, so nodes that are no longer current stay dirty
  too (sis-model.md, section 11). They are 20 to 46 percent of the index
  nodes written at 50 MB (levels.md, "Bounds, measured"). A bound needs an
  assumption on how many such nodes point to a node of D, to state, and to
  check on Java's runs as TREE and A6' are.

T4 is harder than T3. It is about the structure and how D evolves, not
only about the policy.


7 What the bounds would say together
------------------------------------

With policy B and a deadline at d_h, say 2 d, T3 and T4 together give:
startup reruns records that cost less than d_h plus one transaction,
whatever the debt; and it reads less than d_h plus two records of at most a
transaction and the debt each. The rerun does not depend on the size of
the database but through h, nor on its age. With the default of 50 MB and
d_h = 100 MB, the rerun is about 3 s at the 29 ms per MB measured for
100-byte values with a warm cache; the debt adds reads in order.


8 Decisions and next steps
--------------------------

Decisions for Frans:

* D1. The policy: A, today's take, with a bound under conditions (4.3);
  B, a deadline: the take ignores its node limit for transactions that begin
  more than d_h before the end (Frans's TODO D in `TransSeq.take`, made
  strict); or C, keeping the section and the debt below d (4.2).
  Recommended: B. It is a small change to the take, T3 then applies to
  Java with d = d_h, and it bounds the rerun, the costly part, whatever the
  debt. Decided 2026-10-24 (Frans: "As you propose."): B, with d_h = 2 × sd.
* D2. The fix of 007-02, now 005-31 (its options; A is proposed there).
* D3. The cost of a record for the startup distance: bytes, as now, or an
  estimate of startup time (5.4).

Next steps, in order (since 2026-10-24 the plan is
[007-03](03-plan.md), which orders them differently and puts 005-31
first):

1. Model Java's take in Lean as a policy, with the deadline, and prove that
   it keeps up with d_h, so that T3 holds for it. The trace checker can then
   check Java's startup pos against it on every record; today it takes
   Java's s(i) as given.
2. Java: the deadline in `TransSeq.take`, and the fix of 007-02.
3. A test that drives the debt up: many keys loaded, then updates spread
   over them, at a small d. It checks the hypothesis of 4.2 and measures
   the records of B.
4. Measure startup with a cold OS file cache, and its first touches.
5. T4 (section 6), for the exact test first.
6. When T3 and T4 hold for Java, state the promise for users: what the
   startup distance and the deadline bound, and what bounds the rest.
