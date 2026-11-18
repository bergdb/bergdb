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


# 5. The cost: not known

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
