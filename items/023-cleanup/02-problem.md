# 023-02. The problem

Created 2026-11-10 by Frans Lundberg. Status: open.

The problem of 023 stated exactly, and what we want from a solution: what
was observed, everything the Core keeps after nothing needs it, Frans's
rule that a deleted KV eventually consumes no resources, the bounds
wanted, and the constraints. It proposes no solution: it is what a
solution is judged against. How the Core works today is 023-01; the first
study of options is 020-30; the tests are 023-03.

Requirements are R1 to R27, questions for Frans F1 to F12; cite them as
"023-02, R9". They are not 011-01's R1 to R7, nor 020-30's F1 to F7.


## 1. The problem, as observed

### 1.1 What was seen

Round 6 of the new-user apps (020-24) and two investigations found costs
that grow with every key ever deleted, not with the live data. No wrong
answer and no lost data in any of them.

* **A queue's head** (020-24-16, U16-1). The first 16 entries of an index
  range: 27 key nodes followed and 0.14 ms fresh, 204,226 and 24.4 ms
  after 190,000 entries had left it, about one key node per entry that
  left (each entry key has a segment tree of its own; 021-28). Restarts
  and reclaim do not help; an index built again does.
* **A scan past deleted entries** (020-24-17, U17-1). An empty index scan
  followed in key order by a deleted index's entries: 10 key nodes, then
  139,233 and 30.9 ms after 160 cycles of that index. 021-28's end key (a
  branch) brings it back to 10, and does nothing for the queue's head.
* **Reclaim stops cutting a FIFO** (021-25). One put and one delete a
  transaction, keys in time order, 1,024 live keys, R = 20 s: no cut after
  transaction 195,000; at 300,000 the first available time 182 s back and
  135 MB on disk for 300 KB of live data. An iteration's first step
  scanned 20,642 index nodes for 4 KVs, and its touch made 17,493 nodes
  dirty: a record of 4.17 MB for a transaction of one put and one delete.
  Hashed keys: cuts go on, but the stream grows 1.6 to 2.7 KB a
  transaction against 0.75, to 349 MB. 2026.3 and the C library alike.
* **A metrics store** (020-24-18, U18-1). Samples deleted after 15
  minutes, R = 20 minutes: one cut in 12 simulated hours, the first
  available time up to 41,140 s back, 1,188 MB for 1.8 MB of live data,
  records up to 149 MB, commits of 4 s. The control, a ring of keys
  overwritten in place, stays at 71 to 266 MB and cuts every half hour.
* **Index churn** (020-24-14, U14-1): with R = 2 s reclaim stops cutting
  (350 MB and growing); the slower puts were fixed by 021-25's fix (c).
* **Above the Core** (020-18, F5 and O3): a deleted generation's cleanup
  took the square of its entries until it read on from the last key it
  deleted, a workaround of the Core's cost; a scan of a range that
  100,000 entries left takes 2 to 12 ms against 0.1 ms.

### 1.2 The root

Facts, from the code of `main` (020-30, sections 3 and 4.1; 023-01):

1. A delete sets a bit in a delete bitmap of the segment leaf that holds
   the key's last segment (`Dag.setValue`, `appendDeleteKlong`). Nothing
   above that leaf changes.
2. Nodes are split by time and by space, never merged or removed; there is
   no merge code. A leaf whose keys are all deleted stays linked, its
   parent's klong to it live; so do inner nodes with nothing live below,
   and the segment trees after a deleted long key's segment. A full leaf
   with no live key is replaced by an empty node, still linked
   (`Dag.handleFullNode`). So the index keeps the nodes of deleted keys
   reachable at the current time, and at every later time, for ever.
3. A scan (`GetMany.Chain.next()`) enters each such subtree on its way,
   finds nothing live and climbs back. Its stop condition sees live KVs
   only, so it learns of its range's end at the first live key after it.
4. Reclaim's touch (since 2026-10-13; 011-01, Q7) makes every index node
   reachable in its key range dirty, those of deleted keys too: they are
   copied forward on every iteration and never released, and the touch
   runs on to the next live key. An iteration's work grows with every key
   ever deleted, so iterations lengthen until the cuts stop.
5. The value nodes of deleted keys go with the cut already: reclaim
   rewrites live values only.

Which bound BergDB promises, with nodes never merged, was asked in
October (011-01, Q1) and not decided. 011-01's R5 asked that deleted keys
"eventually be removed by cutting the front of the stream". Frans's 2012
notes planned that an emptied node leaves its parent, and merges; both
were postponed (020-30-02, section 1).


## 2. The wider question

Frans (023's readme): "we want to have a look at resource cleanup in
general". The resources: **stream bytes** and the files that hold them;
**the reachable index**, the key nodes and klongs reachable at a lookup
time, which lookups pass and reclaim and the take copy; **memory**, pinned
(D, the roots, the record being written), cached (under the budget,
taken by CLOCK), handles, and structures of their own; and **work**: key
nodes followed and bytes read by scans, gets, puts and deletes, reclaim's
scan and touch, the take, startup and eviction.

### 2.1 What the Core keeps

Checked against `java/src/bergdb/` on `main`.

| Kind | What is kept                         | Released today            | Bounded by today     |
|---|---|---|---|
| K1  | the value node of a deleted KV       | by the cut                | the history within R |
| K2  | the delete in its record             | by the cut                | the history within R |
| K3  | its klong and bit in its leaf        | at the leaf's time split  | B a node             |
| K4  | a leaf with no live key, linked      | never                     | nothing              |
| K5  | inner nodes with no live key below   | never                     | nothing              |
| K6  | later segment trees of a deleted key | never                     | nothing              |
| K7  | shadowed klongs in a node            | at the node's time split  | B a node             |
| K8  | old value nodes of overwritten keys  | by the cut                | the history within R |
| K9  | node versions replaced by a split    | by the cut                | the history within R |
| K10 | underfull nodes                      | never (no merge)          | nothing              |
| K11 | the height of a tree                 | never                     | log of keys ever put |
| K12 | reclaim's table rows                 | at a cut                  | rows within R        |
| K13 | index entries and markers of Pub     | as K1 to K6               | as K1 to K6          |
| K14 | dead nodes in D, from the touch      | when the take writes them | the startup section  |
| K15 | cached objects, their handles        | by eviction (CLOCK)       | the cache budget     |
| K16 | a writer's key access path arrays    | never (no shrink)         | the longest touch    |
| K17 | stream files before the cut          | whole files at a cut      | 6 to 9 % more        |
| K18 | STM's write hashes                   | by bins                   | a constant           |

* K3, K7: a node holds at most B klongs (B = 30, the node size); a time
  split (`KeyNode.lastVersionGivenDel`) drops deleted and shadowed ones
  (023-01, 2.1), but a node that gets no write keeps them, and the touch
  copies them forward. Shadowed klongs come from overwrites, from
  reclaim's rewrites of live values (each a put), and from time splits,
  which add a klong for the new node in the parent beside the old one.
* K4 to K6 are the root of 1.2. Hashed keys may refill an empty leaf;
  keys in time order never do.
* K10, K11: the shape deletes leave (011-01, Q1). With all but one key of
  every B deleted, about B times the nodes of the live keys alone.
* K12: rows before the cut row go at a cut (`Reclaim`, near line 860).
  K13: to the Core, the Pub API's index entries and markers are KVs like
  any other (010-01, P12). K14: the touch puts K3 to K7 into D, pinned
  until written. K15: an object no lookup follows loses its CLOCK bit and
  goes at a pass once the budget is reached; with `noEvict()`, the Core's
  only, nothing goes. K16: since 021-25's fix (c) a clear costs what was
  used, but the arrays keep the longest length ever followed.

### 2.2 Who pays, today

Scans pay for every key node of K4 to K6 between their start and the
first live key after their end, forward and backward, at the latest time
and at earlier times, through restarts. Gets, puts and deletes pay for
K11's levels; every transaction may carry the take of what the touch made
dirty (records of MBs, 021-25). Reclaim's scan and touch pass K4 to K6 on
every iteration and copy them, with K3 and K7. Startup stays bounded (P5,
T3), with K14's dead nodes in D. So what grows without a bound is K4 to
K6, K10, K11 and K16, and the work they cause.


## 3. Frans's rule

### 3.1 His words

Frans, 2026-11-10, 08:50: "Deletes need to be handled so that eventually,
some time after the retain period has passed, deleted KVs consume no
resources of the database. I see this as some sort of clean up. We can do
as much as possible in the deleted transactions. But it is also possible
to leave things for the Reclaim to clean up. Either way, a deleted KV must
consume zero resources eventually after the retain period has passed."

08:29: "The theme of 2026.4 is a bug-free database. I consider this a bug.
The bounds are not ok. Scans are supposed to be O(n) amortized for
scanning n items."

09:55: "The solution must, of course, be aligned with the current database
design, with our principles 010, with the API and it should not degrade
performance too much. In any case, it must be correct. Current
correctness testing must continue to work. No regression. Performance
(stream size, memory, time) should stay near current performance, but can
be discussed."

### 3.2 Terms

* **Version** (of a key; 023-01's "version" is a node's, here "node
  version"): a key's value from the time tp of the put that made it to the
  time te of the key's next put or delete, its end; a version with no end
  is live. A lookup at time t sees it if tp <= t < te.
* **Deleted KV**: a version ended by a delete; **old version**: one ended
  by a put; both are **ended versions**. A delete of an absent key stores
  nothing (`Dag`, near line 764).
* **R**, the retain duration in force: `setRetainDuration`, forever by
  default, kept in the stream (015-87).
* **f**, the first available lookup time: lookups at times in [f, now],
  the **available times**, are served. f moves only at a cut, to the cut
  iteration's tEnd, never back, and then f <= now - R (levels.md, section
  6). With R forever, f never moves.
* **Dead**: an ended version once f > te. No lookup at an available time
  can see it; a read admitted before that cut may, and may expire.
* **A version's things**: its value node; its entry in its record; its
  klong and its bit in a delete bitmap, in every node version that holds
  them; every key node and segment tree below which there is nothing but
  things of ended versions; their objects and handles in memory.
* **B**, the node size, 30 klongs. **H**, the key node levels on a key's
  path: the sum of the heights of the segment trees it passes.
* **An iteration span**: from one reclaim iteration's start to the next's,
  at least twice the startup distance of stream growth and R / 4 of time.
* **The twin** of a database at a moment: a fresh database with the same
  settings and the same live KVs, put in the order of their last puts, in
  transactions of the same sizes, with no deletes. Frans's hello-world
  database against one that put much more and deleted all but `/a.txt` is
  the simplest pair (023-03).

### 3.3 The rule, made exact

**R1. Lookups unchanged.** At every available time, every get and scan,
in both directions, answers as INV-LOOKUP (011-01) says, whatever a
cleanup has done. A version that is not dead keeps every thing a lookup at
an available time needs: that history is what the user asked for. A read
admitted before a cut may expire with `LookupTimeNotAvailableException`,
never answer wrongly (D1 = A; levels.md, section 6).

**R2. Stream bytes.** With R finite, from the K-th cut after the first cut
at which a version is dead, no byte of the stream holds a thing of it. K
is a small constant, the same for every database and workload (F6).

**R3. Reachable index.** From the same cut on, no node version reachable
at an available time holds its klong or its bit, and no node reachable at
an available time has nothing below it but things of dead versions.

**R4. Memory.** From the same cut on, none of its things is pinned (D, a
root, a record being written); no object that a lookup at an available
time can reach points to them, so a cached one is never followed again
and goes at eviction's next pass once the budget is reached; and no
structure in memory keeps a size it reached because of them (K16).

**R5. Work.** From the same cut on, no operation follows a pointer to its
things or reads them: scans and gets at every available time, puts,
deletes, reclaim's scan and touch, the take, startup (the rerun and the
linking of D), and eviction beyond the pass that takes its objects.

**R6. Reclaim keeps up.** With R finite and a user who keeps writing, the
stream growth and the time a reclaim iteration needs are bounded by the
live data (the twin's values and index), the startup distance and R, not
by the versions ended before; so f stays within R plus a bounded number of
iteration spans of now. Without R6, "eventually" may never come (U18-1).

Today, with deletes: R2 holds for value nodes and records only; R3, R5
and R6 do not hold (1.2; 021-25; U18-1); R4 in part (K14, K16).

So "eventually", in Frans's words: within R plus a bounded number of
iteration spans after the version's end, each bounded by the live data;
counted in the user's writes, as nothing runs without the application's
calls (P3). My reading, for Frans to confirm: R2 to R5 cover all of a dead
version's things, also its klong in a node that still holds live keys, as
"zero resources" says (F1).

### 3.4 Special cases

* **Retain forever** (the default; no reclaim): no version is ever dead,
  the history is kept, R2 to R5 never apply; section 4 holds (R8).
* **An idle database**, or one that only reads: no work (P3), so nothing
  is released while it idles; the bound resumes with the writes.
* **A restart in between**: the cuts, and with them R2 to R5, are a
  function of the stream (P2): the same with or without restarts.
* **Lookups at earlier times** in [f, now]: R1. A version that ended at or
  after f keeps its value node and its klongs on its paths at those times.
* **R changed**: a larger R brings nothing back; a smaller one makes
  versions dead at the next cut.
* **A key deleted and put again**: the deleted version follows the rule
  by its te. **A node created and emptied by one transaction** (020-30-03,
  section 4) holds nothing visible, and falls under R3 and R9. **Large
  deletes**: the same rule, each transaction's work in proportion to its
  size (R11).

### 3.5 Beyond deleted KVs

**R7. Every ended version** (my reading of 023's wider framing; F2). R2 to
R5 hold for old versions too (te the time of the put that replaced it),
for node versions replaced by a split (dead once f passes the split), and
for the Core's internal keys. Today their value nodes and replaced node
versions go with the cut; their klongs (K7) stay in live nodes.

**R8. Retain forever** (my reading; 020-30, F3). Only section 4's bounds
are required; the history's bytes are kept.

Not covered by R2 to R7 as read here: the shape deletes leave (K10, K11),
no version's things. R10 and R12 ask for it; F5 is the question.


## 4. The bounds wanted

### 4.1 Scans

**R9. A scan is O(n) amortized.** A scan at an available time t, forward
or backward, from any start, with any stop condition, hands its stop
condition n KVs live at t, the one that stops it included, those it skips
(`CONTINUE`) too. Its cost is the key nodes it follows, as a
`Dag.PointerListener` counts them. Over the life of a database, for any
sequence of operations:

    sum over the scans of key nodes followed
        <= c * sum over the scans of (n + 1) * H
         + c' * H * (the puts and deletes made)

with constants c and c' that depend on nothing (not the data, the history
or R). A scan pays for its n KVs and its ends; a put or a delete pays,
once in the life of the database, for every scan that passes its traces.
A cold scan reads at most a node's bytes a key node followed, and its n
values.

* "Amortized" is Frans's word: one scan may pass many deleted keys once;
  P1 measures the worst single scan (F4).
* At every available time, not only the latest: my reading, as 011-01's
  R1 asked its scan bound for every time of the window (F3). A lookup at t
  reads only entries of times up to t (sis-model.md, 3.4, A2; lemma M), so
  traces left on the paths at time t cost every later scan at t.
* H as a factor: O(n) with the key's length and the tree's height as
  constants, as 011-01's R1 and Q2 put them.
* Today: no (U16-1, U17-1, 020-18 O3), through restarts.

### 4.2 Gets, puts and deletes

**R10. Gets.** A get at an available time follows at most H key nodes,
one a level. Today H grows with about the logarithm of the keys ever put
in each segment tree on the path (K11). Must: no worse than today.
Wanted, for Frans (F5): H in the live keys, as 011-01's R1 asked.

**R11. Puts and deletes.** One path, H key nodes; O(H) nodes changed, O(1)
amortized new ones. A transaction's whole work, with its share of the
take, of reclaim's steps and of any cleanup, is in proportion to its size
(P4), by constants that do not grow with the history, within the record
limit (005-31). Today: its own path, yes; the work carried, no (4.17 MB
for one put and one delete, 021-25; commits of 4 s, U18-1).

### 4.3 Space and memory

**R12. The index.** (a) At the latest time, after every transaction, no
node but the root and a bounded number a level has nothing live below it:
the reachable index has at most about (n + 1) * H nodes for n live keys
(my reading: R9 needs it for scans, R6 for reclaim). (b) Wanted, for Frans
(F5): at most a constant times the twin's nodes, whatever the deletes
(bounded underfill, K10). Today: neither; the C library's probe counted
22,134 key nodes for 1,024 live keys (022-06-3, in 021-25).

**R13. The stream.** With R finite, after every cut: stream length <= c1 *
the twin's stream + c2 * the records of the retained window + the growth
of a bounded number of iteration spans. This is 011-01's R5 ("stream
length <= c * (L + history within R)") with the spans a cut needs. Today:
yes with overwrites only (U18-1's ring), no with deletes. With R forever
the stream is the whole history.

**R14. Memory.** Pinned memory stays within what the startup section
needs (D, bounded by T3); no structure grows with ended versions (K14,
K16); heap bytes a live KV (MEM, 006-02) stay near today's (R26).
Today: D yes; K14 and K16 no (021-25, parts 1 and 3).

**R15. Startup.** Bounded as today (P5; T3; 007): no cleanup adds a pass
over the database at a start, and the rerun's and the linking's work does
not grow with ended versions beyond what the section holds. Today: yes,
with dead nodes in the section (K14).

## 5. What a solution must keep

Frans's words of 09:55 (3.1) are the frame. In detail:

**R16. Readers.** Readers take no lock and may hold any node object at
any available time; whatever a cleanup changes leaves every lookup a
reader has begun right, or expired (D1 = A), never wrong. Today this rests
on lemma M and on node objects that change only by entries of the
writer's transaction time (`KeyNode`'s class comment); a change of that is
a change of the model (R24). No stop-the-world for readers (P1).

**R17. Determinism and restarts.** The stream's bytes are a function of
the accepted transactions (P2); a restart between any two transactions
changes nothing (INV-RESTART); the startup rerun makes the same node ids,
or the start fails ("startup error, node ... not found", `DbStarter`).
Reclaim's touch is not rerun; D is rebuilt from the stored ids. Whatever a
cleanup changes is rerun the same way, or stored.

**R18. Crashes.** A cut of the stream at any byte gives the state after
the last complete transaction, with no repair (INV-CRASH). **R19.
Reclaim's cut** removes nothing a lookup at an available time can reach
(INV-RECLAIM; `CutOK`). **R20. Eviction** changes no record, no D and no
answer (INV-EVICT), with handles as today (009).

**R21. The principles** (010-01): P1, no wait of about 20 ms or more from
BergDB's own work (a guide; under 50 ms on F53 and 100 ms on s1 is good);
P3, nothing runs without the application's calls; P4, each call's share
of the cleanup in proportion to the call; P8; P10, no new setting and
nothing for the user to run; P12, inside the Core, no new Core API method
unless Frans decides, nothing that knows of indexes; P11 and P13, simple.

**R22. The stream format.** Any change of the format, the layout and
meaning of what a start reads, the Dag's rules that the rerun applies
included (020-30-04, section 2), is approved by Frans before it is made,
in its entry (018-01, section 2).

**R23. Earlier databases.** 2026.4 opens the databases of 2026.3 and
before as Frans decides (F9): right, or refused with a clear error, never
as a silently different tree. 2026.3 must refuse what it cannot read
right; it refuses a record format above 5.

**R24. The Lean model.** Java stays aligned: the trace checker accepts
Java's transactions as steps of the model (A1 to A5, TREE, A6', A-COPY),
`CutOK` at every cut, C-L, C-P and C-H; `docs/sis-model.md`, `lean/` and
`docs/trace-format.md` change with the code if the model must.

**R25. The C port.** The C library (022) follows Java byte for byte, after
2026.4's release (022's log); a solution names its C work.

**R26. Performance**, "near current performance, but can be discussed"
(09:55). Measured before and after at 1M to 100M keys, worst cases first:
`performance.sh` (quick and reference, `ab` against a preserved build of
today) and Props's CORE, MEM and SS (006-02), for stream size, memory and
time, with deletes and without. The tolerance is Frans's to set (F12);
the solution reports every difference.

**R27. Tests.** "Current correctness testing must continue to work. No
regression." (09:55.) Every functional test, `before-commit.sh`, the
level scripts and `night.sh` pass unchanged in what they check, and so do
RestartInvariance and StreamDigest's agreement of its four modes, which
compare a run with itself. The bytes written will likely change, so the
checks that compare exact bytes may get new expected values, each with
Frans's approval, recorded as 018-01, section 2 asks: StreamDigest's
digests against 2026.2's reference; the C port's byte equality
(`cross.sh full`, a new pin); the trace conformance, if the model or its
checker must change (R24; the 20 hand-made traces stay); and unit tests
that assert a shape the Dag's rules decide (DagTester's splits).


## 6. How the requirements will be checked

The tests are 023-03; here only what they must show. The agent that
makes a change runs them before it asks for a commit, with the level
scripts its item names; `night.sh` runs them for the coordinator. A check
of more than a few seconds gets its own script in `java/stress/` and a
`night.sh` step, not a place in `before-commit.sh`.

**Workloads**, each with R forever and R finite, with restarts (cold too)
between phases: 021-25's FIFO in time order and hashed; a queue's head
scanned again and again (U16-1's `ScanCost`); index cycles (U17-1's
`ScanAfterChurn`, U14-1's churn); a metrics store (U18-1's `Repro`, with
the ring as control); a large range deleted, in one transaction and in
many, then scanned both ways at the latest time and around the deletes;
all but one key of every B deleted (R12 (b)); long keys with unique
tails; keys deleted and put again; overwrites only, which must stay as
they are. At 1M, 10M and 100M keys.

**Measures**, against the twin (3.2), the steady-state churn twin and
Frans's hello-world database (023-03): key nodes followed by scans and
gets (summed, for R9) and bytes read cold; nodes and klongs reachable at
the latest time and at f (all, of dead versions, with nothing live
below); the stream after each cut and on disk, the cuts, now - f;
reclaim's nodes scanned and touched an iteration; the largest record and
the longest commit; D, pinned and resident bytes, MEM; startup time and
reads, warm and cold, with a startup distance of 50 MB or more.


## 7. Non-goals and open questions

### 7.1 Non-goals

* Choosing or ranking a mechanism: later subitems of 023.
* The history's bytes with R forever (R8); memory with `noEvict()`;
  `FileStream`'s whole-file cut (K17); protected long-lived snapshots; an
  exact write time (011-01, Q9).
* Bounds of the write overhead (011-01, Q5) and of startup (007) beyond
  R11 and R15: a solution must not make them worse.
* The Pub layer's own jobs (index builds, a generation's cleanup): they
  gain from R9 and are not changed here.
* A Lean proof of the bounds: the model has no keys and deletes
  (020-30-04, section 4); the alignment (R24) is required, a proof is not,
  unless Frans asks.

### 7.2 Questions for Frans

* **F1. Dead klongs in live nodes.** Must a deleted KV's klong, and a
  shadowed one, go from a node that still holds live keys (R3 as read),
  or is a rest of at most B a node enough? Recommended: they go, as "zero
  resources" says; a solution may take longer for them (a larger K).
  Implied by Frans's answers to F2 and F5 (10:38, 10:41; coordinator,
  10:44, not contradicted): they go, eventually, after one or more reclaims,
  as ended versions.
* **F2. Old versions.** Does the rule cover every ended version, replaced
  node versions and internal keys (R7), or deleted KVs only? Recommended:
  every ended version.
  **Frans, 2026-11-10, 10:41: "Yes, it should cover every version that has
  ended."** R7 holds as written.
* **F3. The scan bound's times.** R9 at every available time, at the
  latest only, or at the latest at once and in the past eventually?
  Recommended: every available time, as 011-01's R1.
  **Frans, 2026-11-10, 10:44: "At every available time; this is what we
  want."**
* **F4. Amortized or worst case.** R9 amortized only, or also a bound on
  a single scan (P1)? Recommended: amortized; the worst single scan
  measured and reported.
* **F5. The shape.** Height and node count bounded in the keys ever put
  (R10's must, R12 (a)) or in the live keys (R10's wish, R12 (b), a
  bounded underfill; 011-01, Q1)? Recommended: decide after measuring the
  underfill case; a strict reading of "zero resources" against the twin
  asks for the live keys.
  **Frans, 2026-11-10, 10:38** (on 023-03's Q2, the same question): "I agree in general. However, it depends on how difficult Strict is. If we find a good Strict solution, let's go for it. But Bounded is ok. For Strict, it is enough to eventually, after one or several reclaims, to get the original Hello-world resource consumption."
  So the bound in the keys ever put (023-03's bounded allowance) is
  enough; the bound in the live keys (strict) is wanted if a good solution
  is found, and may be reached eventually, after one or more reclaim
  iterations.
* **F6. K and the lag.** How many cuts after a version is dead (R2), how
  many spans of lag (R6)? Recommended: K = 2, as a node version written
  during an iteration goes with the cut after the next (020-30, 4.2).
* **F7. Eventually in time?** In the user's writes only (P3), or also in
  time, which needs work no call asks for, or a call such as `maintain()`
  (010-01, P3's idea)? Recommended: the user's writes.
* **F8. Retain forever** (R8): section 4's bounds only? Recommended: yes.
* **F9. Earlier databases** (R23), which hold K4 to K6 already: (a) refuse
  them; (b) open them and leave what they hold; (c) open them and release
  it too. Recommended: (c) if it fits R11's bound, else (b) with a note in
  the release notes. 2026.4 already refuses 2026.3's encrypted ones.
  **Frans, 2026-11-10, 10:30: (a).** "No need for compatibility, we can
  ignore released before 2026.4, so: (a)." 2026.4 refuses databases of
  earlier releases.
* **F10. The format in 2026.4.** Is a change of the record format
  acceptable in 2026.4, with new digests, the C port after the release,
  and F9's answer? Recommended: yes, each change approved in its entry.
  **Frans, 2026-11-10, 10:30: "Yes, acceptable."**
* **F11. 2026.4's scope.** Which requirements must 2026.4 meet?
  Recommended: R1, R6, R9, R11, R12 (a), R13, and R2 to R5 for deleted
  KVs; F1's klongs, R7 and R12 (b) may follow in 2026.5.
* **F12. The numbers.** The constants of R2, R9, R12 and R13, and R26's
  tolerance. Recommended: set from the first measurements against the
  twins of 023-03, for Frans to approve.


## 8. Log

2026-11-10. Written by q23 for coord-1110, from 023's readme, 020-30 and
its helpers' files (facts and questions, not options), 020-24-14 to 18,
021-25, 021-28 (branch `scan-deleted-keys`), 011-01, 010-01, 018-01,
levels.md, sis-model.md and the code of `main`; Frans's words of 08:29,
08:50 and 09:55. No code, no build, no new measurement.

2026-11-10. Frans answered F9, (a): earlier releases' databases are
refused, and F10, yes: a change of the record format is acceptable in
2026.4 (10:30).

2026-11-10. Frans answered F5 (10:38): bounded is enough, strict if a good
solution is found; strict may be reached after one or more reclaims.

2026-11-10. Frans answered F2 (10:41): the rule covers every version that
has ended (R7).

2026-11-10. Frans answered F3 (10:44): R9 at every available time. F1
follows from F2 and F5: dead klongs in live nodes go, eventually.
