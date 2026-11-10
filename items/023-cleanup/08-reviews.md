# 023-08. The reviews of 023-07, merged

Created 2026-11-10 by Frans Lundberg. Status: open.

Three independent reviews of 023-07, the proposal for 2026.4, written at
the same time, none reading the others (Frans, 14:36: "make multiple
independent reviews with multiple AIs to ensure we get this right"):
review A (08-reviews/a.md), B (b.md) and C (c.md), each with its
evidence. Two checks of their findings, on the code: checks/p8-liveness.md
and checks/take-back.md. This document merges them. The reviewers are
named in the item's log (023's readme).


## 1. The verdict

**The delete design stands; P8 does not.**

* All three keep the delete side of the core: the unlink at the delete
  (UP), the empty key first (LE-b), root collapse (RC) and the take-back,
  with a complete rule. Each calls it the smallest design that meets the
  scan bound when the retain period is forever: the cleanup cannot wait
  for reclaim, because then reclaim never runs.
* All three found, on their own, that P8 can stop reclaim's cuts. The
  check confirmed it, and found `main` and P4 as today's rule expects.
* C found fault 12 in the take-back: a pointer to a node never written,
  and the database cannot be opened again. The check confirmed it, also
  with sorted keys, and a fix of about 25 lines passes every probe.
* None of the full set is needed for correctness or for Frans's rule.
* B and C: accept the core with changes. A: reject the core as written,
  for P8 and for the bounds, keeping the same delete design.

So the core gets smaller, not larger: section 5.


## 2. What the three agree on

| Point                                         | A        | B        | C        |
|---|---|---|---|
| UP, LE-b, RC, the take-back: the right design | keep     | keep     | keep     |
| P8 as built can stop the cuts                 | yes      | yes      | yes      |
| The take-back needs every pointer repointed   | yes      | (sound)  | yes      |
| Merges in 2026.4                              | later    | later    | later    |
| (b')                                          | later    | never    | never    |
| The replaced queue on by default              | later    | no       | never    |
| `maintain()`                                  | later    | 2026.5   | later    |
| Anything of the full set for correctness      | no       | no       | no       |
| Dead klongs stay in live nodes                | a gap    | accept   | accept   |
| Gates on one integration head before release  | yes      | yes      | yes      |

B read the take-back as sound; C found fault 12 in it (section 4).


## 3. Where they differ, and what the checks say

* **P8's fault: a slowdown or a stop?** B: under random growth an
  iteration takes exponentially longer. C and A: with a queue and any key
  after it, no iteration ends at all. The check ran all their probes on
  P8, P4 and `main`:
  * B's run A on P8: no cut in 2,000 transactions, 2,186 MB of stream.
  * C's queue with "/z": `main` ends in 22 transactions, P4 in 15, P8
    not in 3,000 (137.5 MB).
  * `main` and P4 follow today's rule: iterations of the data at tStart
    divided by the step's 16 kB.
  * A correction to B: in B's growing workload the oldest data kept
    (now - f) climbs on `main` too (66 s against P8's 61 s at the end of
    run B). The difference is the iteration lengths.

  Both are right; C's and A's form is the stronger.
* **X5 (c): dead code?** B: a transaction never puts and deletes one key,
  so make it a `Bug`. C: reached. The check: a key transformation can
  give one transaction a put and a delete of one key; the branch was hit
  2,187 times, always at a fresh leaf; its inner branch never. A `Bug`
  for the whole branch would fail a legal Core transaction. Only the
  inner branch becomes an assertion. C is right.
* **Fault 12 only with keys out of order?** C: yes, with a key
  transformation. The check: also with sorted keys, in larger
  transactions (UnlinkFuzz, seed 33 on P5, replayed through the plain
  Core API). C's explanation of the cause is right and complete.
* **The top-node window, (a) now?** A: yes, to honour Z13. B and C:
  later; the window is on `main` and in the twin too, and (a) changes the
  Lean model's take. C: run the ratchet test on `main` first; (a) becomes
  a fix if the window grows.
* **Dead klongs in live nodes.** B and C: at most B - 1 klongs a live
  leaf until its next time split; accept for 2026.4 with a note. A: the
  wait can be long. In a cold chain of segment trees an old delete entry
  stayed after 700 cuts (probe `SegmentAge`): bounded in space, not in
  time. All three see the same thing; they differ on whether to call it
  an allowance. It is Frans's call (Q5).
* **Merges later: a refusal?** B: a format 7 that refuses 2026.4's
  databases. C: the rerun knows each record's format, so merges can run
  only for records of a later format, with no refusal. C's way is the
  smaller.


## 4. The faults found, and their state

| Fault                                 | Found by | Check     | Fix                 | State   |
|---|---|---|---|---|
| 12: take-back, a pointer to no node   | C        | confirmed | 023-v12-fix         | gating  |
| 13: P8 can stop the cuts              | A, B, C  | confirmed | 023-v8-fix          | 2026.5  |
| X5 (c)'s inner branch unreachable     | C        | confirmed | an assertion        | to do   |
| `dirtyNodeBound` misses chained RC    | B, C     | -         | count them          | to do   |
| The last touch walks the new tail     | A        | -         | -                   | on main |
| The cache's tables stay at peak size  | A        | -         | -                   | open    |
| The refusal names format 2 only       | 023-07   | -         | name 2026.3         | to do   |

* **Fault 12.** In `Dag.spaceSplitInPlace` a segment leaf gets a second
  klong of tt for a split segment root of tt; the first still names the
  root. If tt then empties the root and takes it back, the shadowed klong
  names a node never written: with -ea the store fails, without it the
  next start fails ("Unexpected stream pointer"). Fix: the leaf's klong
  is repointed in place, as `TopDs.newSuperRoot` already does. On P5's
  head and on P4 with only the retarget; not on `main`. With the fix:
  every probe and UnlinkFuzz run (sorted, shuffled, with repeated keys)
  passes, and before-commit. level3 full: OK (25 traces, C-CUT 0 of
  303). level2 full: steps 1 to 6 OK, A2A3Check2 OK, the trace checker
  70 of 70 OK; it fails only conformance.sh's check that a trace of A6's
  kind (005-04: a segment root made and split in place in one
  transaction) shows an adoption below the old parent. The fix removes
  that adoption: the leaf's klong now names the new root, so no node is
  adopted below its old parent. The check must change (Q9).
* **Fault 13.** A step counts every KV it scans against its 16 kB, also
  the keys put ahead of the scan since tStart. The fix: a step counts
  only KVs stored before pStart. It ends every probe of the three
  reviews; before-commit passes; T1 passes but for C9 at 1M ascending
  (106 against 100). C's alternative, a quota in proportion to the
  transaction, also ends them but writes 30 to 35 % more stream.
* **The last touch** of an iteration walks every key put beyond the
  scan's end, in one transaction: one step dirtied 81,018 nodes (A,
  `ReclaimTail`). C: not new, `main` does the same. A prototyped
  "mark only the rewrite paths" (27 nodes); a later item.
* **The cache's tables.** After a fill and a mass delete the objects
  leave, but the hash table keeps its peak size: 219,104 slots against
  the twin's 22,144 (A, `CacheCapacity`). P6 noted it (P6, 4.4).


## 5. The proposal after the reviews: a smaller core, frozen

**For 2026.4, in two sentences: a delete removes what it emptied, in the
same transaction. Reclaim, unchanged, frees the rest at the cut.**

1. **At each delete, by the writer, in the deleting transaction:** UP's
   climb with LE-b and RC, as in P4. A node of tt that the climb empties
   is taken back, and every klong of tt that names it is repointed (P5's
   retarget and fault 12's fix). X5 (c)'s inner branch an assertion.
   `dirtyNodeBound` counted by node, chained collapses included.
2. **Reclaim, as on `main`:** each step scans at tStart. No P8.
3. **After each cut, by the writer's thread:** P6's dead hand, without
   its switches.
4. **Scans** end at their range's end (SE).
5. **Format 6**, with a refusal that names 2026.3.

Against 023-07's core: P8 out, fault 12's fix in, two small rules (the
assertion, the count). No new mechanism. About 1,000 lines of Java. No
change of the Lean model.

What it leaves, all bounded: one iteration of lag after a mass delete,
as on `main` (T1 at 1M needs a drive of 12,000, not 4,000); dead klongs
in live nodes, at most B a node; underfill after scattered deletes, in
the keys ever put; the top-node window, as on `main`; the cache's tables
at peak; the last touch over a new tail, as on `main`.

**Before it reaches `main`:** one integration branch; before-commit,
level1 to level4 full and `night.sh large`; UnlinkFuzz's new modes
(shuffled keys, repeated keys, larger transactions) for a night; a
reclaim liveness test (a queue with a key after it); T1, T3, T10 and a
cold start at 50 MB; then a review of the integrated code only.

**A stop rule:** if that night finds another fault in the take-back,
2026.4 is `main` with SE only, and 023 goes to 2026.5.

**Later, each on its own:** P8 with fault 13's fix and the liveness
tests; merges, switched on by record format; (a), if the ratchet test
on `main` shows the window grows; `maintain()`; the cache's tables; the
last touch. Never: (b'), the replaced queue on by default.


## 6. Questions for Frans

1. **Freeze the design at section 5?** Recommended: yes. It answers
   "I smell expanding complexity" (16:14): the reviews remove more than
   they add.
2. **P8 out of 2026.4?** Recommended: yes. Its fix exists (fault 13) but
   is a new reclaim argument; it can come in 2026.5 with no format cost.
3. **Fault 12's fix, the complete take-back rule?** Recommended: yes.
   Every tier needs it, and it is a rerun rule, so it must be in before
   format 6 is fixed.
4. **Sort the transformed keys before the index's puts** (Frans,
   16:07)? Recommended: not in 2026.4. It is small, but it needs a rule
   for two templates that become one key, and it does not remove fault
   12. A separate item.
5. **Dead klongs in live nodes,** at most B a node, kept as long as the
   node lives: accept as a named allowance for 2026.4, with a line in the
   release notes? Recommended: yes; compaction is a later item.
6. **The window (Z13):** (a) later; the ratchet test on `main` now?
   Recommended: yes.
7. **The stop rule** of section 5? Recommended: yes.
8. **The gates** of section 5 before the release, about a day and a
   night? Recommended: yes.
9. **005-04's trace check.** Fault 12's fix makes the a6 traces show no
   adoption below the old parent, which conformance.sh requires. Change
   the check to require none, that is A6 rather than A6', for those
   traces? Recommended: yes; the stricter A6 may then hold for the whole
   core, a simplification of the model for later. The other way, a fix
   that repoints in every node above (C's option 1), keeps the adoption
   but also the dead klong, and touches the take-back, its root case and
   the merges.


## 7. Frans's answers

2026-11-10, 16:34: "1 to 8. Everything as recommended except 4. Do 4.
Sorting keys within one transaction is cheap and reduces variability. It
defines equality of transactions in a sense i like. put of /a and /b can
be specifies in either order still the same identical transaction is
run, the same stream is generated."

* Q1 to Q3, Q5 to Q8: as recommended. The design is frozen at section 5.
* Q4: yes, in 2026.4. The Core transforms every key of a transaction
  first, then sorts them (stable), then puts them in the index; value
  transformations stay in the put loop; the startup rerun keeps the
  stored order. So two transactions with the same operations, given in
  any order, run the same and write the same stream. Fault 12's fix is
  needed all the same (it is reached with sorted keys).
* Q9: open.


## 8. State

2026-11-10, 16:23. The three reviews and the two checks are committed.
Fault 12's fix (023-v12-fix, 92bf4eb5, in the check's clone): level3
full OK; level2 full OK but for 005-04's trace check (Q9). Fault 13's
fix is on 023-v8-fix (0f4571fc), not gated
beyond before-commit. Nothing is integrated; nothing is in `main`'s
code. Frans answered Q1 to Q8 at 16:34 (section 7); next, the integration
branch of section 5 with Q4's sort.
