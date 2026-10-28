007-03. Plan: bounded startup for BergDB itself
================================================

Created 2026-10-24 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request ("Do: write this plan into item 007."), from Claude's proposal
of 2026-10-23, which followed 007-01 and 007-02. Updated 2026-10-26 from
the review after item 009, [007-04](04-review-after-009.md).

**Status (2026-10-28): step 1 done (005-31, 2026-10-24); step 5 done
(007-05, 2026-10-27); step 6 done, rule 4 without reads (005-57,
2026-10-27); step 2 done (007-06, 2026-10-27); step 3 done, with D4:B
(007-07, 2026-10-28); step 4 done (007-08, 2026-10-28).** Step 3: 005-49's
paced take with the deadline at d_h = 2 × sd as its backstop, and after a
decrease of the startup distance the deadline at the span of the section's
transactions, which shrinks with every commit (D4:B). Step 4: that take is
a policy of the Lean model, and T3 is proved for it: with a constant
setting the section without its last record stays below d_h, and after a
decrease it never grows and shrinks with every commit until it is below
the new d_h. Step 5: warm on
F53, 7.4 s at 50 MB, 12.4 s at 200 MB and 70 to 86 s at 1000 MB with 10M
to 50M keys and 8-byte values; cold on s1, 3.5 minutes at 10M keys, most of it rule 4's
reads. Step 6: rule 4 finds a pointer's node by its position, with no read
(005-57); with it a cold start on s1 at 10M keys took about 46 and 51 s at
50 and 200 MB, the rest the rerun's loads. Steps 2 to 5 waited for release 2026.1 (Frans,
2026-10-25: "After the release"), which is out, so they wait only for
Frans's start. Since 007-04, step 2 is smaller (005-38 measured its first
workload); steps 3 and 4 wait for
[005-49](../005-todo/49-smooth-index-writes.md), smooth index writes, and
step 3 for D4; step 5 goes first, and counts a cold startup's random
reads; step 6, for those reads, is new. D4 and D5, new, are decided (Frans,
2026-10-26: "D4:B. D5: as recommended.").

Step 1, 005-31, had Frans's go for its option A (2026-10-24: "005-31, it
has my 'go'. But don't start the implementation now."), and then his
request to fix it ("fix all todo items of type Fix"). Step 3, the deadline,
is decided too (D1, Frans, 2026-10-24: "As you propose."): d_h = 2 × sd, a
constant factor.


The goal
--------

T3 bounds the startup section for a policy that keeps up with the startup
distance (007-01, section 3). BergDB's take does not keep up (007-01, 4.1;
007-04, 1), and one large transaction could stop it for good (005-31,
fixed). The goal: bounded startup that holds for BergDB itself, proved for
BergDB's own policy, and a startup time a user can rely on, from a warm OS
cache and from a cold disk. In the words a user should be able to rely on:

    Startup reruns the transactions of less than 2 × sd of records, and
    the last transaction, whatever the size and the age of the database,
    where sd is the startup distance: about X s per 100 MB of startup
    distance on F53 with a warm OS cache. From a cold disk it also reads
    about N nodes at random, Y s on s1.

X, N and Y come from step 5. Today N is mostly rule 4's header reads,
whose number follows D, not the section (007-04, 3); step 6 is to make
them few, so that N follows the section, which T3 bounds. Not in this
plan: T4, a bound on D (007-01, section 6), which bounds the two records at
the ends of the section and the memory that D pins (007-04, 4); and the
startup distance as an estimated time instead of bytes (007-01, D3).


The steps
---------

### Step 1. Fix 005-31 (option A, decided)

Refuse, before the go point, a transaction whose got-dirty index nodes
could not be written in one record: a cheap test for every transaction, and
the precise count, under the write lock, only for the rare large ones
([005-31](../005-todo/31-fix-take-blocked.md), "The fix, options", A).

* Why first: with it, the nodes of every transaction fit in one record,
  which the deadline of step 3 needs. Without it, no policy can bound
  startup.
* First: 005-31's first step, comparing the precise count with the bytes
  the nodes take when written, on 007-02's probe and on a large load of new
  keys.
* Done when: as 005-31 says (a unit test with the record limit lowered,
  `before-commit.sh`, StreamDigest identical, the docs).
* Size: S.
* Done 2026-10-24, by Claude (Opus 5.5, Claude Code); see 005-31's
  outcome. The bound is at 15/16 of the record limit, so a transaction's
  nodes fit in the record of a later transaction whose own part is below
  1/16 of the limit. For step 3: "one transaction always fits in a record"
  holds for such records; a record whose values take nearly 7/8 of the
  limit (005-17) leaves less, and the take then waits for a smaller one. A
  dirty limit of 1/8 of the record limit would make it hold for every
  record, at the price of refusing eight times smaller updates; for Frans
  to decide if step 3 or 4 needs it.

### Step 2. A test that drives the debt up

A stress test that makes the debt of D large compared with the startup
distance (007-01, 4.2), run on today's take first. After every
transaction, it records the section without its last record, the record's
size, D in nodes, and the debt: the stream size of D's nodes plus 16 bytes
each, as `TransSeq.recordBytes` counts them.

Its first workload is measured (2026-10-26; 007-04, 1): a load of n keys,
then updates spread uniformly over them, by 005-38's WriteBench at 10M and
50M keys and 50, 200 and 1000 MB, in transactions of 1,000 puts, with the
lag and D sampled at the end of every window of updates. 007-01's
hypothesis fits it. 005-49's first step extends WriteBench to count every
record, which gives the largest record per transaction for that workload.
Left, on 005-49's version of WriteBench, with the section per transaction
added:

* The startup distance lowered at runtime (`Db.setStartupDistance`), from
  1000 to 100 MB and from 200 to 50 MB, in one call and in steps: how long
  until the section is below the new d_h, and the largest record and
  commit meanwhile. It answers 006-06's question 2 for today's take, and
  gives D4 its sizes.
* Deletes of existing keys spread over the keys: small records, each with
  a key path's worth of got-dirty ids.
* Single puts: the first workload with transactions of one put, at 50 and
  200 MB.

Startup distances of 50, 200 and 1000 MB (Frans, 2026-10-26; 007-04, 5);
smaller ones only as a quick stress. In memory, as 005-38 ran it, with a
12 GB heap at 10M keys and 22 GB at 50M.

* Done when: the workloads left are measured on today's take, with the
  outputs in this item's directory. The same runs again after step 3.
* Size: S, and runs in the background. They count bytes and nodes, not
  time, so a busy machine does not matter.
* Done 2026-10-27 ([007-06](06-debt-test.md)): 50 runs at 10M keys on
  today's take, on 005-49's paced take and on 007-07's patch. The same runs
  again on step 3 with D4:B, 2026-10-28: 007-07, section 10.4 (the steady
  runs the same bytes as the patch's; one call from 1000 to 100 MB or from
  200 to 50 MB writes no record over 5.4 MB, where the patch wrote 87 to
  486 MB).

### Step 3. The deadline in `TransSeq.take` (D1, decided)

**Waits (2026-10-26) for [005-49](../005-todo/49-smooth-index-writes.md),
smooth index writes, and for D4** (007-04, 2 and 6). Frans wants the cost
of a commit in proportion to its own size ("Bursts are to be avoided"), and
the deadline alone makes the bursts steeper. 005-49 recommends how the take
paces its writes, and this step follows it. The deadline stays in the take
as the backstop that T3's proof uses, and acts only when the pace falls
behind. The rest of this step is the deadline as planned on 2026-10-24.

The take ignores its node limit for transactions that begin more than d_h
before the end of the stream; d_h is 2 × the startup distance, a constant
factor, so no new setting. In `take()`'s loop, one more way to go on:

    first.tpos <= maxSp
        && (nodeCount < nodeCountLimit || transCount < 2 || first.tpos <= hardSp)

where `hardSp` is the stream length minus d_h, computed in a long
(`2L * startupDistance`: the distance is an int, and
`DbBuilder.startupDistance` takes any int; 007-04, 5). The record limit
stays: after step 1 one transaction always fits in a record, so a take that
lags passes at least one transaction per record.

* Streams change only where the take lagged more than d_h: tests with small
  startup distances, runs like the 10M one. StreamDigest on the standard
  sets says which, and each change needs its reason.
* The price, to measure with step 2's and 005-49's runs: the largest record
  the deadline makes, which writes the debt beyond d_h; the longest commit,
  against the target of about 20 ms; and the readers that wait while that
  record is appended and forced (005-46; 007-04, 7).
* `Db.setStartupDistance`'s Javadoc warns that a large decrease "can cause
  a large transaction to run". Today the node limit spreads the work; with
  the deadline, the next transaction writes the debt beyond d_h at once,
  unless D4 decides otherwise. Update the Javadoc.
* `take()`'s comment: its "TODO D." of 2015, which asks for a factor on the
  node limit when the startup pos falls behind by more than 2 × sd (D1's
  origin), goes with the change, and so does the claim that the startup
  pos "should never fall exceedingly behind" (007-01, 4.1). Noted
  2026-10-25 (006-05, T7).
* Done when: in step 2's and 005-49's runs, the section without its last
  record stays below d_h; `before-commit.sh`; `level2.sh`, since the take
  is Level 2's mechanism; `level3.sh` and `level4.sh` if their streams
  change; the quick performance suite unchanged; docs/levels.md, section
  5 (Level 2), updated.
* Size: S for the code, M with the gates and runs.
* Done 2026-10-28 ([007-07](07-step3-paced-take.md), section 10), at
  Frans's decision (006-09, section 8, decision 1), by Claude (Opus 5.5,
  Claude Code): 007-07's patch, 005-49's paced take with the deadline at
  d_h = 2 × sd as its backstop (the take loop above, with its node limit,
  is gone), and D4:B as 007-06 measured it: while the section's
  transactions span more than d_h, the deadline is at that span, which
  shrinks with every commit. Gates: before-commit.sh, level2.sh, level3.sh
  and level4.sh, full, pass; StreamDigest: every stream changes, as
  expected, the same with or without D4:B. Step 2's runs again: the section
  without its last record below the deadline in force in every run, at
  most 1.12 sd in steady runs. The quick performance suite waits for a
  quiet block (007-07's night step). 7.1 and 7.2's whole-transaction
  bursts are accepted for now; a pace by nodes is a model change for step
  4.

### Step 4. BergDB's take in Lean

BergDB's take, as step 3 leaves it, becomes a policy of the model, in the
trusted part (`lean/SIS/Bound.lean`). With the deadline alone: from
s(i-1) + 1 on, whole transactions while they begin at least sd before the
end of the stream, and fewer than two have been taken, or their got-dirty
ids are below the limit, or they begin at least d_h before the end. The
limit is a function of T(i), which the policy may see (011-11, M10).
BoundExample.lean's sketch, `javaTake`, becomes this definition. A take
paced by 005-49 changes the definition, so this step waits for 005-49 too.

* The proof: every transaction up to the target of d_h passes the loop's
  test, since the cost to the end only shrinks along the stream and
  d_h ≥ sd. So the policy keeps up with d_h (`KeepsUp`), and T3 holds for
  runs with BergDB's take, with d = d_h. A pace that only takes more
  transactions, earlier, needs no more than the deadline's test. A pace
  that writes nodes of transactions it does not take (005-49, question 4)
  changes the model itself, whose algorithm writes exactly the nodes taken
  (sis-model.md, 6.1, step 6; 007-02's third option), with proofs of its
  own.
* The record limit is left out of the model. Java's take is the model's as
  long as the record limit does not stop it, which after step 1 takes the
  transactions due at once to need more than one record, about 2 GB of
  index nodes. The theorem's comment says so.
* A startup distance that changes between transactions (006-06, question
  4; 007-04, 6): T3's proof uses only the startup pos of the last
  transaction, so it should carry over to a d given, like the limit, by
  the stream and T(i). State it, with a `#guard` on a run that lowers d.
* Done when: the theorem (`T3_take`, say) proved, with `#guard`s on
  example 2: the take with the deadline keeps the section below d_h, and
  with a tight limit and no deadline it does not; `lake build` with no
  warnings and no `sorry`; lean/README.md and docs/sis-model.md, section
  10, updated.
* Size: S to M.
* Since step 3 (007-07, 2026-10-28): the take is 005-49's pace with the
  deadline, and the deadline's distance is the larger of d_h and the span
  of the section's transactions, from the oldest's tpos to the newest's,
  a function of the stream and of T(i). After a decrease of the startup
  distance it is the span at the decrease and shrinks with every
  transaction, so T3 holds for the deadline in force (007-06, section 5,
  point 2). The pace only takes transactions earlier than the deadline
  does; its share needs no proof of its own.
* Done 2026-10-28 ([007-08](08-step4-take-in-lean.md)), at Frans's go
  (006-10, question 3), by Claude (Opus 5.5, Claude Code): the take is
  `takePolicy` in `lean/SIS/Bound.lean`, whole transactions oldest first,
  each taken if it begins max(2 sd, span) or more before the end or if the
  pace takes it, with any pace, and BergDB's own (`javaPace`: the share in
  Java's double arithmetic, the dither) giving `javaTake`, which gives
  Java's startup pos on 300 generated cases; the setting is any function
  of the transaction. Proved, for every pace and every cost of a record,
  with nothing else assumed: after a transaction the section costs less
  than the larger of 2 sd and the section before (`T3_take_step`); with
  settings at most M, less than 2 M, with and without restarts (`T3_take`,
  `T3_take_restarts`; with a constant setting, less than d_h, this step's
  T3); after a decrease to sd', less than 2 sd' or at least one unit less
  for each transaction since (`T3_take_decrease`, also with restarts); and
  what startup reruns (`T3_take_rerun`). "The policy keeps up with d_h"
  above is false with D4:B (`KeepsUp` is over all streams, and on a stream
  whose span is longer than d_h the deadline is at the span); the proof
  goes by induction over the run from the one-transaction bound. The
  record limit and the meta blocks are left out, as planned. `#guard`s on
  example 2: the take keeps the section below d_h, also with restarts,
  and through decreases; the take before step 3 with a tight limit does
  not keep up. docs/sis-model.md (6.1, step 4; section 10) and
  lean/README.md updated.

Later, not in this plan: the trace checker compares Java's startup pos
with this policy on every record. It needs each record's length in bytes
in the traces (a trace format change, in Java's exporter and in `Check/`,
after 009's step 4c, which changes both now; 007-04, 8), and Java's
positions also count the meta blocks, 128 bytes every 200 kB, which the
model's cost of a record does not.

### Step 5. Startup time

Startup time against the section, at startup distances of 50, 200 and 1000
MB, so sections from 50 MB to d_h = 2 GB, for 10M and 50M keys, with values
of 10 bytes to 10 kB: on F53 with a warm OS file cache, and cold on s1,
where root can drop the caches (F53 has no passwordless sudo; a database
larger than its memory, such as 100M keys, gives a partly cold start
there). Besides the time, count what startup does: the bytes it reads in
order, the transactions it reruns, and its random reads by source: the
rerun's first touches, rule 4's header reads (the calls of
`NodeCollection.idOf` from `DbStarter.linkD` that read the stream), and the
reads of the nodes of D that the rerun does not reach. Fit
time ≈ a × bytes + b × transactions + c × random reads, with c for a warm
and for a cold cache.

* It needs neither 005-49 nor the deadline: the startup distance makes the
  sections, and the deadline only bounds them. So it can go first (Order).
* Done when: the table, the fitted constants, and the numbers for the
  promise for each startup distance, warm and cold; rule 4's share of the
  random reads, for step 6.
* Size: S to M, in the background with the session idle, and not while
  another timing run is on.
* Scheduled for 2026-10-27 from 04:00, after `night.sh` (Frans, 2026-10-26:
  "Schedule Step 5 tonight at 04:00; I assume night.sh is done by then;
  report to news.md."). The tool, the scripts, what the night runs, and
  the results: [007-05](05-startup-time.md).
* Done 2026-10-27: the night ran from 04:00 to 05:27, and 007-05 has the
  table, the fit, the numbers for the promise, and rule 4's share. Not
  done: the count of rule 4's reads that find a canonical object, left to
  step 6.

### Step 6. Fewer random reads at startup (D5: in this plan)

Proposed 2026-10-26 (007-04, 3); in this plan by D5 (Frans, 2026-10-26).
Rule 4 (`DbStarter.linkD`; 001-08, M44; `Mem.linkD`, and
`HMem.linkD` for handles, in the Lean model) links each stream pointer of
D's nodes to its pointee's canonical object, if it has one, so that a node
of D never names an older version of a node written since. To find the
object it needs the pointee's id, and a pointer that startup's maps do not
resolve costs a read of the pointee's header: the 590,000 random reads of
a cold startup at 10M keys and a startup distance of 10 MB, minutes on s1.
Step 5 (007-05) counted 864,000 and 1,254,000 at 50 and 200 MB: 78 and
73 percent of a cold start's reads, and about 80 percent of its 3.5
minutes on s1; the rerun's first touches are the rest (249,000 and
467,000 reads, 34 s). Their number follows D, not the section. Most likely
find no canonical object; step 5 did not count how many do, so this step
does. The writer may read the same headers
again when it takes those nodes:
`NodeCollection.resolvePointers` calls `idOf` for each stream pointer left,
and `idOf` remembers the last 100,000 positions.

Options, for the investigation to weigh:

* A. The same reads, cheaper: in position order, or several at a time (an
  SSD serves many at once). No change to the rule or the model.
* B. Fewer reads: decide from what startup knows which pointers can name a
  node with a canonical object (the section's positions and prevPos
  chains, the positions of what the rerun loaded), and read only for
  those. It needs the argument, against M44, that the others need
  nothing, and maybe a matching change to the model's startup.
* C. No reads: the pointee's id in the stream with each pointer, as a
  handle keeps it in memory. A format change, the largest of the three; it
  would spare the writer's reads too.

With the reads few (B) or gone (C), a cold startup reads at random only
what the rerun touches, at most a node per level of the tree for each key
rerun, and the section bounds that, with T3 and the deadline, without T4.
Measured, that still leaves 45 to 55 s on s1 at 10M keys (007-05, "What
it means", 3): a cold start in seconds needs the rerun's reads cheaper
(A) or fewer too.

* Done when: the reads counted by source (step 5), the options costed, and
  Frans's choice. The change itself is a step of its own after that.
* Size: M for the investigation.
* Investigated 2026-10-27 in 005-57, at Frans's request, by Claude (Opus
  5.5, Claude Code): B goes all the way, to no reads. A pointer of D that
  names a node with a canonical object names a vpos, a position in
  `posToId` or that object's own position (005-57's report, section 2);
  rule 4 links 0.4 and 5.4 percent of the pointers it examines at 50 and
  200 MB. The writer's `resolvePointers` reads the same kind of header and
  needs none either, with a map of the pinned objects by position (part 2;
  without it, part 1 moves the reads into the time after the start).
  Prototypes of both, checked against today's code in the gates and on
  007-05's databases; on s1 a cold start at 10M keys and 50 MB from 214 s
  to about 46 s, the rest the rerun's loads (A). The change waits for
  Frans.
* Done 2026-10-27 (005-57, "Decided" and "Outcome"): Frans chose part 1
  alone ("1. Part 1 alone. ... 3. No, not now. Let's get this in place
  now."): rule 4 by position is in the code, checked against rule 4 by node
  id at every startup of the tests. Not done: the writer's reads (part 2),
  and A, the rerun's loads, "not now". The Lean theorem for the argument is
  005-58.


Order
-----

Since the review (007-04):

* 005-49 first, as its entry says: before steps 3 and 4.
* Step 5 now, beside 005-49: it needs neither 005-49 nor the deadline,
  and it shows where a startup's time goes at 50, 200 and 1000 MB, warm
  and cold, which step 6 and the promise need. Step 6's count comes from
  its runs. Done 2026-10-27 (007-05).
* Step 2's runs left after 005-49's first step, on its version of
  WriteBench, in the background: they count, they do not time.
* D4 and step 3 after 005-49's recommendation; step 2's runs again after
  step 3.
* Step 4 after step 3's design, which it must match. Done 2026-10-28
  (007-08).
* Step 6 after D5, from step 5's count. Done 2026-10-27 (005-57), rule 4
  by position; the rerun's loads (its option A) not now.

Before the review: 1, 2 and 3 in that order, 4 beside 2 and 3 once D1 had
fixed the deadline's rule, and 5 after 3.


Decisions
---------

* 005-31, option A: decided, go (Frans, 2026-10-24); done (2026-10-24).
* D1 of 007-01: the deadline, with d_h = 2 × sd as a constant factor:
  decided (Frans, 2026-10-24, "As you propose."); not started. Since 007-04
  it is the backstop of the take that 005-49 recommends: that take must
  still take every transaction that begins at least d_h before the end.
* D3 of 007-01, bytes or estimated time: not needed for this plan. 006-06
  (question 3) asks it again, for fast restart.
* Steps 2 to 5 before or after release 2026.1 (item 008): after (Frans,
  2026-10-25, "After the release"). The release shipped with the take as
  it is, and says so: README.md, and the old levels.md (011-04, "Bounds,
  measured"). It is out (2026-10-25).
* The bursts as an entry of their own: yes (Frans, 2026-10-26: "Yes,
  register the burst entry."), 005-49, before steps 3 and 4.
* Open since step 1: a dirty limit of 1/8 of the record limit instead of
  15/16, if step 3 or 4 needs it.
* **D4 (new, 2026-10-26): how a decrease of the startup distance meets the
  deadline** (007-04, 6 and 7). To decide with 005-49's recommendation,
  before step 3.
  * A. At once: the transaction that `setStartupDistance` runs takes every
    transaction that the new d_h makes due. One call does fast restart's
    "write D now". But one commit may write hundreds of MB of index nodes
    (D held up to 1.57 GB at 1000 MB and 50M keys), while the other
    writers wait, and the readers of the stream's last file (005-46).
  * B. In steps: `setStartupDistance` lowers the distance a little at a
    time, each step with its own transaction and the write lock released
    between them, so that every record stays short, and returns when the
    section is below the new d_h. Its Javadoc asks callers for such steps
    today ("no more than 10M for every call"). A take paced by 005-49 may
    do the same by itself, if d_h comes down gradually.
  * C. As today: the steps are the caller's business, as the Javadoc says,
    and the deadline acts at once on whatever the caller does.

  Recommended: B. Fast restart gets one call to wait for, and every commit
  stays in proportion to its own size, as Frans asks of a user operation
  (005-49). Step 2's runtime decrease gives the sizes of the steps.
  Decided (Frans, 2026-10-26, "D4:B."): B.
  Built 2026-10-28 as 007-06's "pace" (Frans, 006-09, section 8, decision
  1: "the pace takes the new startup distance at once, and the deadline
  has its own distance, lowered with the lag to max(2 × new sd, lag)"):
  `setStartupDistance` returns after its one transaction; the commits that
  follow take shares of the new setting at once, and while the section's
  transactions span more than 2 × the new sd, the deadline is at that
  span, which a start rebuilds and which shrinks with every commit
  ([007-07](07-step3-paced-take.md), section 10).
* **D5 (new, 2026-10-26): step 6, fewer random reads at startup**: in this
  plan, as proposed, or as an entry of its own. Either way, its count goes
  with step 5's runs. Recommended: in this plan, since a startup time that
  holds from a cold disk needs it. Decided (Frans, 2026-10-26, "D5: as
  recommended."): in this plan.


After the plan
--------------

* T4 (007-01, section 6): a bound on D, for the exact still-dirty test
  first. It bounds the records at the ends of the section, the memory that
  eviction cannot free (with handles, the resident bytes follow D once D
  outgrows the budget), and the cold startup's random reads, unless step 6
  removes them (007-04, 3 and 4). Steps 2 and 5 give its numbers at 50 to
  1000 MB.
* The problem statement's Q1 (the lookup bound), Q3 (the cost model) and
  Q5 (the write overhead) (011-01): 005-54 names this item, with T4, as
  their natural home; which of them matter now is for Frans to say.
* The trace checker's comparison of the startup pos (after step 4, and
  after 009's step 4c).
* The promise in the user documentation: the Pub API's startup distance,
  and docs/levels.md, section 5, per startup distance, warm and cold; fast
  restart (006-06) for planned restarts at large distances. From step 5
  (007-05, "What it means", 1 and 2): 10 s warm holds up to a startup
  distance of about 75 MB at 10M keys with 8-byte values (580 MB with 10
  kB values), while the 200 to 1000 MB that 005-38 found best for the
  write overhead give warm starts of 12 to 86 s.


How to work
-----------

Several sessions work in the bergdb tree at once: Java and Lean changes are
made and gated in a scratch clone, and copied into the main tree last, with
the gates run again on the combined tree. Frans commits, or the session he
asks to; no session commits on its own.
