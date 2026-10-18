001-05. The K4 review: Level 4 in Java
======================================

By Claude (Opus 5.5, Claude Code), 2026-10-18, for Frans Lundberg. WP J10 of
the plan [01-plan.md](01-plan.md) (section 3, K4); the work is logged in
[02-progress.md](02-progress.md). Stage 4 of the plan, Level 4 in Java, is
done. K4 has passed: by the agent, on your go of 2026-10-17 19:59 ("Why
wait for me? If things work as expected"), with the plan's recommended
options: eviction on by default (Q10, your decision of 2026-10-16) and
`level4.sh` a required gate (`AGENTS.md`, `README.md`). This guide says what
was decided, the evidence, and how to check it.


1. What was decided
===================

K4 accepts Level 4 in Java: eviction of values and index nodes at
transaction boundaries and after loads, under a capacity controller whose
budget is `cacheSizeInMb` (by default a fifth of the JVM's maximum heap), on
by default; and `java/stress/level4.sh`, which prints `LEVEL 4 OK`, as the
fourth required gate. In `AGENTS.md`: "All four level scripts ... must print
`LEVEL n OK` before a change to the Java code is committed"; `README.md`
lists it.

Why it passed without waiting: things worked as expected (your go of
19:59). Stage 4's ten WPs are done, each with its checks and gates passed
and committed; `level4.sh` passes full and quick; J10 meets Q13's targets;
there is no change to the record format or the public API, and no Java
change outside the agreed list (level4-alignment.md, section 6, and the J
WPs of the plan). One fault was found and fixed inside J7 (section 3,
findings).

If you want K4 otherwise (eviction off by default, `level4.sh` not
required, another default budget), say so: the default is one line
(`Eviction.defaultSchedule`), the gate a line of `AGENTS.md`.


2. What Level 4 is in Java
==========================

As the model of stage 2 says (level4-alignment.md, sections 5 and 7):

| WP | What | Where |
|---|---|---|
| J1 | The registry of resident objects and its accounting; the pins; the node table names canonical objects only; a test-only audit of INV-CAN, the pins and INV-SLOT against an oracle of latest positions | `core/Residents.java`, `core/Audit.java`, `Cache3`, `Db` |
| J2, J3 | Eviction of values and index nodes at transaction boundaries: unswizzle under the slot's pointer lock, release (the node table's entry, the canonical flag), reload by R8's loader, the writer's follower promotes; forced schedules for tests | `core/Eviction.java` |
| J4 | Run E in the exporter, SLOT lines, and the checker's C-P (INV-SLOT on Java's physical states); an eviction set in `conformance.sh` | `java/stress/TraceExport.java`, `lean/Check/` |
| J5 | Readers under eviction: the protocol of Q8, its tests | `Eviction`'s comment, `core/EvictionReaderTester.java` |
| J6 | Reclaim under eviction: the step's reserve, reclaim's loads counted | `Reclaim`, `NodeCollection.MaintenanceFollower` |
| J7 | The capacity controller, on by default; the cache size in `long` (M45) | `Eviction` (schedule `budget`), `core/CapacityTester.java`, `DatabaseBuilderImp`, `Jmx` |
| J8 | A database larger than memory on disk in a capped JVM | `java/stress/LargerThanMemory.java`, `docs/level4-evidence.md` |
| J9 | `level4.sh` | `java/stress/level4.sh` |
| J10 | The performance comparison | `docs/level4-performance.md` |

No change to the record format, to existing databases or to the public API
(the comment of `DatabaseBuilder.cacheSizeInMb` says what it does now).
Every record stays what it was: the byte comparison against R8's digests
(`StreamDigest`) after every WP, and the eviction invariance runs (the same
stream with every schedule).


3. The evidence
===============

**The model** (stage 2, accepted at K1): with any cache schedule, the
physical writer appends exactly the model's records and leaves its D
(T-CACHE), reads give P (T-READ), also with restarts (T2-C), and every
object outside the pinned set may be evicted (T-PIN), under TREE, A6' and
A-COPY, which Java's runs meet. Lean, no `sorry`, the standard axioms only.

**Java against the model.**

| Check | What | Result |
|---|---|---|
| The audit (J1), every transaction or every N-th | INV-CAN, the pins and INV-SLOT on Java's resident objects, against an oracle of latest positions | Without eviction (J1): 1.3 million audits on the configurations of 8.4; with eviction, the campaigns of J2, J3, J6 and J7: 3.8 million; `level4.sh` full: 0.64 million; none failed |
| C-P (J4), `conformance.sh evict` | The model's INV-SLOT on Java's physical states, from SLOT lines, in the Lean checker | 80 traces (J4; 19,641 transactions, 784,821 slots); 30 in `level4.sh` full; no failure |
| `EvictionInvariance` (J2, J3, J7) | The same transactions with every schedule (none, values, every, random, the controller): the same stream byte for byte, the same D, the same answers | Every configuration of 8.4, without and with restarts and reclaim: no difference |
| `StreamDigest` after every WP | The records of 36 runs against R8's | 36 of 36 the same, every WP |

**Stress with eviction**: `ReclaimStress` (400 configurations with forced
schedules and split steps, J6; 100 with the controller, J7), `CrashTest`,
`RestartInvariance` and `LoadTest` with forced schedules and the
controller, `ReclaimReaders` (100 rounds each with forced schedules, J5; 30
with the controller): no failure, no audit failed. The readers' protocol
(Q8): `EvictionReaderTester`, deterministic interleavings and three reader
threads under eviction.

**Larger than memory** (J8,
[level4-evidence.md](../../docs/level4-evidence.md)): 20 million keys, an
index of 1.5 GB and 2 GB of values, on disk in a JVM capped at 2 GB with a
budget of 500 MB: every check right; the resident bytes at most the budget;
the live heap at most 646 MB.

**The gate** (J9): `level4.sh` full, `LEVEL 4 OK` in 982 s, and quick in
239 s, on a busy machine.

**Performance** (J10, [level4-performance.md](../../docs/level4-performance.md)):
with eviction off and with a budget
larger than the data, against `l34-base` in matched runs on a quiet
machine: warm gets and scans within 5 percent, commits within 1.2 percent,
startup 6.5 to 9.7 percent slower (Q13's targets: 10, 10 and 20); no alert.
Under a budget of a fifth of the data, reads are 30 to 90 times slower (no
target).

**Findings that changed the code** on the way, each with a test: values
that only the node table held were never released (J7's scan test; fixed in
J3's sweeps); the writer's own checks under `-ea` read a pointer's pair
without the node's monitor, which a swizzling reader holds (J5; the nodes
were never wrong); pinned state above the budget made every load sweep
(J7, the trigger); and a sweep counted only what it released, not what left
memory with it, so after reads it could empty the cache down to D (J8's
first run; J7's `Eviction.drop`).


4. The changes
==============

From R9's commit (`4151a80`) to J10's (`70c1801`), one commit per WP (J2
and J3 in one):

* `java/src/`: 2,957 lines added and 19 removed in 17 files, about 1,750 of
  them tests (`Audit`, test-only; `CapacityTester`; `EvictionReaderTester`;
  the testers of `Eviction`, `Residents` and `Reclaim`). New: `Eviction`
  (about 600 lines with its comments), `Residents` (215), `Audit` (347).
  Changed: `Db` (84 lines: the eviction calls, the audit's oracle, the load
  listener), `NodeCollection` (84: the load listener, the maintenance
  follower's counts), `Reclaim` (135: the step's reserve and counts, a test),
  `Cache3` (49: the registry; canonical objects only), `DbBuilder` (42: the
  schedule, the budget, the audit, the reserve), `KeyNode` (31: the size an
  object was counted with; the checks under the monitor), `DatabaseBuilderImp`
  (16: the cache size in `long`, a test), `Jmx` (11), `DbStarter` (9),
  `DatabaseBuilder` (5, the comment), `Pack` (4), `TopNode` (3).
* `java/stress/`: new `LargerThanMemory.java`, `ReclaimHitRate.java`,
  `level4.sh`; changed `EvictionInvariance.java` (J2, J7), `TraceExport.java`
  (run E, SLOT lines), `conformance.sh` (the eviction set), `performance.sh`
  (`JFLAGS`), and a line or three in four stress programs (the audit's
  summary line; `ReclaimReaders`' property `evict`).
* `lean/`: the checker's C-P (`Check/`, `TraceCheck.lean`; 175 lines), not
  the trusted model, which stage 4 did not change.
* No change to the record format, to existing databases or to the public
  API; every record byte for byte R8's (36 digests after every WP).


5. How to check it
==================

In `java/`, with Lean for the checker (`cd ../lean && lake build`):

    stress/level4.sh                # the Level 4 gate, about 16 minutes; quick: 4
    stress/level1.sh; stress/level2.sh; stress/level3.sh
    java -ea -Xmx3g -Dbudget=60000 -Dn=2000 -Dsd=1000 -Dkeys=500 -Devery=100 \
        -Dmaxnode=8 -Dlong=1 -Dbigtrans=10 -Daudit=5 -Ddel=1 \
        -cp build/bergdb.jar:build/stress bergdb.core.EvictionInvariance 1
    stress/conformance.sh evict 3   # C-P on the eviction set
    java -ea -Xmx2g -Dkeys=20000000 -Dbudget=500 -Dsd=10000000 -Ddir=/some/disk/dir \
        -cp build/bergdb.jar:build/stress bergdb.core.LargerThanMemory   # J8, about an hour

and the performance comparison as J10's entry shows. A database built with
`DbBuilder.noEvict()` or with a large `cacheSizeInMb` evicts nothing.


6. Open risks
=============

1. **The sweep walks every resident object**, twice (2.2 s at 500 MB): a
   reader or the writer that passes the budget waits for it. Incremental
   sweeps, or the incoming-reference lists of Q9, if J10 or use shows it
   matters.
2. **Loads cost two reads** when the index does not fit: the node's header
   for its id, then the node (J8's limits). The id could be kept in the
   unswizzled slot.
3. **What the budget does not count**: the node table's entries (about
   90 MB at 20 million keys), objects released while a reader still holds
   them, and D, which is pinned and bounded only loosely by the startup
   distance (22 MB at 10 MB in J8; Level 2's default is 50 MB).
4. **Concurrency is Java's, not the model's** (Q8): tested, not proved.
5. **Reclaim lags at large sizes** (26 GB on disk for 3 GB of live data in
   J8): a Level 3 matter.
6. **The flaky `StorageManagerTester.testAddReplica2`** (about one run in
   twelve, also on `l34-base`) fails a gate now and then; it is not Level
   4's, but four gates run it four times.
