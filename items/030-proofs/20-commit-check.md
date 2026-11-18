# 030-20. CC: the commit check as the writer's guarantee

Created 2026-11-18 by Frans Lundberg. Status: a note; nothing decided.

Frans, 2026-11-18, 13:42: "This CC approach. I think that was smart.
Commit checks. Should we work with that? Now or later. I would like a
note about it. [...] It is an interesting way to prove the writer. Just
throw an exception if it does not follow the contract. Then all
transactions are following the assumptions the proofs rely on. Smart.
Just wonder about the performance cost of that. Could be too high, I am
afraid."

The idea is 026-23's third proposal (section 1.4, "CC: the commit
check"). Java's check exists, test-only, since 030-09 (section 3). This
note gathers what CC gives, what exists, what it would take, and what is
not known: the cost.


# 1. The idea

At each commit, after the writer has made its change and before the
record is appended, a checker tests that the transaction meets the
writer's contract (030-04, section 3.2; `lean/contract/`). If it does
not, the transaction is refused with an exception and nothing is written.
So every record on the stream meets the contract, and the read proofs
(gets and scans at every time, recovery, restarts, lazy reading,
eviction, reclaim's cut; 006-30, section 6) hold for the whole stream,
whatever the writer did.

The approach is known as translation validation or a certifying
algorithm: an unproved producer with a proved checker (026-23, section
1.4: Pnueli, Siegel and Singerman, 1998; McConnell, Mehlhorn, Näher and
Schweitzer, 2011; CompCert's validated register allocation, Rideau and
Leroy, 2010).


# 2. What it gives, and what it does not

- **It gives:** "no record on the stream breaks the contract", for any
  writer: today's, PE (026-24) or MT (026-22). 030-04's assumption 1 (the
  writer meets the contract: tested) is replaced by "Java's checker
  gives the Lean checker's verdict" (tested), a smaller and simpler piece
  of Java than the writer.
- **It does not give:** that the writer never fails the check. A writer
  bug becomes a refused transaction, an error the user sees, instead of
  a damaged database. That it never happens is what a writer proof shows.
- **With the aim** (030's readme, "The aim": the core algorithms
  proved): CC makes the claim about the stored data complete without a
  writer proof; a writer proof adds "and no transaction is refused for
  it". The two work together: CC is also a safety net while a new writer
  is written.


# 3. What exists

- **Java:** `java/src/bergdb/core/TransCheck.java` (587 lines; 030-09,
  section 3). Test-only: on with the system property `transcheck=1`, in
  the unit tests and in `java/stress/transcheck.sh` (a step of
  `night.sh`); off in production (a null test per node change). A failure
  throws an `AssertionError`, which fails the database (`Db.fail`). It
  walks from the space root at the transaction's time and the time
  before, through the paths of the transaction's keys and every node
  made, changed or replaced, and checks there: clause 1 (the node rules,
  the key order with the ranges passed down, the kinds, no node reached
  twice), clause 2 (each key of the transaction has its new value; the
  other keys of a changed leaf keep theirs), clause 3 (the frame: old
  nodes keep their klongs, added klongs start with a time klong of the
  transaction's time) and Java's search in each changed node.
- **Not checked by Java** (not local): that a node not in the dirty set
  is unchanged; the key order and kinds beyond the nodes visited; the
  levels; the contents beyond the leaves touched. The traces check them
  (`lean/contract/check.sh`). A pointer to a node not in memory ends the
  walk there.
- **Lean:** `checkTx` and `checkVerdict_sound` check a whole history from
  a trace; a local form, for the set of nodes a commit visits, is not
  written.


# 4. What it would take

1. **The cost measured** (section 5). If it is too high, the rest waits.
2. **The local check in Lean, proved sound:** the check passes on the
   visited nodes, and the tree before meets the contract's invariants,
   so the transaction meets the contract. Its frame for the nodes not
   visited rests on the writer's dirty set: either an assumption of its
   own (tested), or checked by other means.
3. **Java's checker made the Lean check,** clause for clause, and tested
   against it: the same verdicts as `contractcheck` on the traced
   transactions, and every fault of the fault sets found.
4. **Nodes not in memory:** the check must see every node it has to
   visit; under eviction it would read them from the stream, or the
   writer keeps them until the check is done.
5. **On failure:** with today's writer, memory is already changed when
   the check runs, so a failure must stop the database before the record
   is written (a restart recovers the last good state). With PE, the
   plan is data until it is emitted, so a failure refuses only the
   transaction.


# 5. The cost

**Measured 2026-11-18** (on s1, quiet; the numbers below, the evidence in
[20-commit-check/](20-commit-check/), `results.md` there): **today's
check makes an append commit 3.5 to 6 times slower** (4 to 6 at 1M
keys). It is 74 to 84 % of the time of a commit with it, for small and
large transactions alike: it
costs about 40 to 55 µs a key on s1 (1M keys), against 8 to 11 µs for the
whole commit without it. A transaction of 1 key: 6 to 8 µs without, 43 to
49 µs with; of 500 keys: 3.6 to 4.9 ms without, 28 to 30 ms with. A
large transaction does not spread the cost: the check walks the path of
each key, so its cost grows with the keys, as the commit's does. A
durable commit (execute, then sync) hardly sees it: the force of about
5 ms on s1 hides the 60 µs the check adds (median 5.1 ms with and
without).

**Judgment:** too high for a check that is always on, as Frans feared:
the check does 3 to 5 times the work of the commit it checks. It is
test-only code, written to find faults, not for speed, and most of its
cost is in how it walks, not in what the contract asks: three simple
changes took 20 to 30 % off it (below), and a check designed for speed
would look only at what the transaction added. Such a check, about the
writer's own work per node on the path, could plausibly cost of the
order of the tree's own part of a commit, a commit 1.5 to 2 times
slower, perhaps less; that is an estimate, not measured. Affordable now: CC where commits are durable
(the force dominates) or as a switch for tests and for a new writer
(PE, MT) while it is young. Before CC is on by default, the check should
be rewritten for speed and measured again.

**The numbers** (s1: 2 vCPUs, 3.8 GB, Linux, OpenJDK 27, G1, assertions
off; each JVM alone on the machine; the check off and on in ABBA order;
the median of the runs and, in brackets, the range):

- **Set 1, 1M keys of 100 bytes** (`CCBench`, a driver of this item, 4
  runs each): transactions of 1, 10, 100 and 500 keys; updates, inserts,
  deletes, and a mix (half updates, a quarter each inserts and deletes).
  Time a key, on/off: 1 key a transaction 4.9 to 5.8 (by kind; all kinds
  5.3), 10 keys 5.3 to 6.0 (5.6), 100 keys 5.0 to 7.1 (5.9), 500 keys
  5.7 to 7.3 (6.3). Off 7.8 to 11.2 µs a key, on 47 to 61 µs. The load
  (transactions of 500 puts): 6.3 s off, 49.4 s on, 7.8 times.
- **Set 4, 10M keys of 8 bytes** (3 runs each; all in memory, 2.5 GB of
  the 2.9 GB heap used after the load, so the collector works hard in
  both and the ratio is lower): updates and the mix, on/off 3.5 to 4.4
  for 1 key a transaction, 4.3 to 4.9 for 10, 4.0 to 4.9 for 100, 4.4 to
  4.7 for 500. Off 16 to 24 µs a key, on 72 to 104 µs. The load 151 s
  off, 791 s on.
- **Set 2, the suites' update scenarios** (`Perf`, the parameters of
  `performance-quick.suite` and `performance.suite`, one key a
  transaction, append commits; 3 runs each; heap 2 GB, 2.5 GB for the
  1M-key one, so not comparable with F53's references):
  - `w-uni-1k-inf` (100,000 keys of 1 KB): 88,468 puts/s off, 23,662 on
    (0.27); commit mean 9.1 → 41.0 µs, median 5.6 → 35.3 µs, p99 31 → 89
    µs.
  - `w-uni-1k-fin` (the same with reclaim, 6 physical cuts): 54,794 →
    18,733 puts/s (0.34); mean 15.6 → 52.0 µs, median 6.0 → 37.9 µs, p99
    122 → 264 µs.
  - `w-uni-100-inf` (1M keys of 100 bytes): 80,447 → 18,662 puts/s
    (0.23); mean 11.4 → 52.7 µs, median 8.4 → 46.3 µs, p99 43 → 109 µs.
- **Set 6, durable commits** (`d-1k-t1`, `d-1k-t16`; 100 and 1,600
  commits, 3 runs each): 1 thread, durable median 5.1 ms off and on, mean
  5.7 → 6.3 ms, p99 15.7 → 24.6 ms (few commits: noisy); 16 threads, no
  difference seen (median 11.1 and 10.0 ms).
- **The profile** (set 3, JFR's execution samples of the writer thread in
  one measured phase, 1M keys, updates): the check is 78 % of the samples
  in `Db.execute` for 1 key a transaction and 84 % for 500, as the A/B
  ratios say. For 1 key: the gets from the root of clause 2 (22 %), the
  keys made for the contents of the leaves (20 %), the visits (14 %), the
  live klongs' sort (10 %), and iterations of the per-transaction maps
  (10 %: an `IdentityHashMap` keeps its capacity after `clear()`, so
  after the load's 500-key transactions every later one iterates large
  empty tables). For 500 keys: the visits (42 %, mostly `through()`,
  which scans all the transaction's keys for every child of every node
  visited) and the gets of clause 2 (37 %).
- **Set 5, a tuned copy** (`tuned/TransCheck.java`, for measuring only;
  the same verdicts: the same counts on `CCBench`, the unit tests with the
  four faults of `TransCheckTester` found, the f-tests passed): new maps
  per transaction instead of `clear()`; clause 2 compares a key with the
  other walk's contents and gets it from the root only when that walk did
  not see it; `through()` by binary search. On/off 4.1 for 1 key a
  transaction, 4.7 for 10, 5.0 for 100 and 500 (from 5.3, 5.6, 5.9,
  6.3): 20 to 30 % of the check's time. What is left (F53's profile, the
  shares only) is the walk's design: every node visited is sorted into
  its live klongs, and every live child of it is followed and looked up
  in three identity maps, at tt and at tt - 1; the writer itself does a
  search and an append per node.

What limits the numbers:

- No eviction in any run (`noEvict()`, as `Perf`): every node is in
  memory, so the check did its whole local work; under eviction it stops
  at a node not in memory and does less, and a complete check (4.4)
  would read such nodes, which would cost more.
- The check is test-only code, not tuned; the tuned copy shows only the
  easy part. A check written for speed (only the klongs a transaction
  added, one walk for both times, no visit of children off the keys'
  paths) is not written or measured.
- One machine, small: 2 vCPUs, so the collector competes with the
  writer; at 10M keys the heap was nearly full. F53 was busy and not
  used for timing, only for the tuned copy's profile shares.
- What the check did (its summary line): for one-key updates at 1M keys
  (`w-uni-100-inf`), 13 nodes visited and 30 reads a transaction; no
  failure in any run.

Before the measurement, the note said:

- 026-23 guesses 10 to 30 % of the tree's part of a commit; the tree's
  share of a commit is not measured. No bytes are added.
- What the check does: two walks of the transaction's key paths (at the
  transaction's time and the time before) and a visit of each node made
  or changed, with the clauses on each; the writer itself walks the paths
  once. So more than the tree's own work is possible for small
  transactions; the walks share the nodes the writer just touched, so
  they are in the cache.
- **The measurement:** the performance suites (`java/stress/performance.sh`,
  011-09) with `transcheck=1` against without, at 1M and 10M keys, on a
  quiet machine (F53 when no other heavy run is going, or s1). Commit
  time and throughput per suite; a profile of one commit for the check's
  share. A few hours of machine time, little AI usage.


# 6. Proposed order

1. Now: this note; the measurement when the machine is quiet.
2. If the cost is acceptable: the local check in Lean (4.2), then Java's
   checker made the Lean check (4.3), whichever writer is chosen; with PE
   both fit best (4.5).
3. Frans decides whether CC is on by default in a release, and what a
   failure does.


# Log

2026-11-18. Written by coord-1118 from 026-23, section 1.4, and 030-09,
section 3, at Frans's request (13:42).

2026-11-18. The cost measured on s1 (section 5): with the check on, an
append commit is 3.5 to 6 times slower, small and large transactions
alike; durable commits hardly see it. Evidence and scripts in
[20-commit-check/](20-commit-check/). Unattended, by a subagent of
coord-1118.
