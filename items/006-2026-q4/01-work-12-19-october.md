006-01. Summary: BergDB work, 12 to 19 October 2026
==================================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-19. Sources:
[docs/log.md](../../docs/log.md), the item readmes, item 001's
[final report](../001-lean-model-levels-3-4/06-final-report.md), and F1-007
and F1-008 in repo f1.

All of the BergDB work this month happened in the last eight days. F1-007
was created on 12 October, and the work moved to this repository on 14
October. In about a week, a bug-ridden 2017 codebase that had been
abandoned became a database that passes all four feature levels, each
aligned with a Lean model that has machine-checked proofs.


Phase 1: recovery and Levels 0 to 3 (12 to 14 October, in F1-007)
=================================================================

**12 October: recovery.**

* The 2017 source (525 commits, 2013 to 2017) was found in Frans's archive
  and builds on JDK 27.
* `RestartStress` reproduced the restart bug that was very likely
  ISSUE151111.

**Level 1 bugs fixed.** There were two:

* A delete of a missing key of 7 bytes or more broke the next restart.
* A transaction that replaced the space root twice made historical lookups
  miss changes. This affected every node size.

**Lean model.**

* [docs/sis-model.md](../../docs/sis-model.md) was written, and recovery
  (T1) and restart invariance (T2) were proved in Lean 4.
* That took about 3,500 lines, with no `sorry` and only standard axioms.

**Level 2 (bounded startup) repaired in three steps.**

* The main defects:
  * There were two node tables, so copies of nodes ended up in D.
  * Rule R had to work by node id.
  * Pointer resolution before writes was wrong.
  * Deletes of missing keys broke the got-dirty lookup.
* After the fixes, every test run passes, and the stream is byte for byte
  the same with and without restarts.

**13 October: load and crash testing.**

* Startup takes about 0.6 to 0.7 s at both 1.6 GB and 18.5 GB.
* Four more 2017 bugs were fixed: streams over 2.1 GB, `BufferedStream`
  reads after a restart, a crash inside the size bytes, and a sync that hid
  a failed write.
* Frans reverted Claude's change to sync. The 2017 group-commit design
  stays.
* The default startup distance is now 50 MB.

**Level 3 (reclaim).**

* The 2017 reclaim had never been tested with restarts after a cut, and 20
  of 20 random configurations failed. Ten bugs were fixed and
  `Reclaim.java` was reworked.
* Reclaim cost was tuned: an index-aware allowance and a 16 KB scan target.
  The largest user commit fell from 1,134 to 125 index nodes.
* Reader safety: a read that a cut overtakes now expires with an exception
  instead of stopping the database.
* `Kv.time()` was removed. A reader/writer data race and GetMany and
  backward-scan bugs were fixed.

**14 October.**

* Codex did the power-loss ordering work for `FileStream`
  ([docs/level3-durability.md](../011-docs-archive/07-level3-durability.md)): explicit
  forces, and an ordered directory force after each unlink. A failed
  pending cut was being acknowledged, and that is fixed. It was verified on
  macOS/APFS and a Linux VM, but with no physical power cycle.
* The performance harness was built.
* Work moved to this repository, and F1-007 became a read-only archive. Its
  only later change, on 18 October, is an Eclipse `.project` filter.


Phase 2: Level 2 alignment of code and model (14 to 16 October, F1-008)
=======================================================================

* Frans chose to keep the Java code and step the Lean model back to match
  it (F1-008-11; [docs/level2-alignment.md](../011-docs-archive/11-level2-alignment.md)).
* New tools:
  * a trace exporter (`TraceExport.java`)
  * the Lean trace checker (`lake exe tracecheck`)
  * `conformance.sh`
* **M18, a startup bug:** empty transactions could make the database
  unable to start. Fixed by storing topPos in every record, which bumped
  the record format to 5.
* **A Java transaction is now one model transaction.** In-place splits of
  nodes the transaction created, and the use of `toPreviousState`, give 1.4
  to 13.7 percent fewer stream bytes.
* The model gained a virtual root and assumptions R1 to R4. T13 says
  marking is exact.
* `level2.sh` now includes conformance checks, so it needs Lean.
* Quick Level 3 performance references were recorded before and after.


Phase 3: item 001, Levels 3 and 4 in Lean and Java (16 to 18 October)
=====================================================================

Item 001 was closed on 19 October. This was mostly unattended agent work.
It ran from 16 October 15:23 to 18 October 16:53, with checkpoints K1 to
K5.

**Model.**

* A physical layer, eviction and reclaim were added: about 37,300 lines in
  `lean/SIS/`.
* **Proved:** T-CACHE, T-READ, T2-C, T-PIN, T8, T9 and T12 (the last also
  with eviction).
* **Checked but not proved:** T-SCHEME, the claim that Java's reclaim gives
  safe cuts. It is checked at every cut Java makes. Frans accepted this at
  K5.

**Java corrections before eviction (R8).**

* Six changes, each compared byte for byte with the baseline.
* This includes M17: a reclaim step left replaced nodes in D.

**Level 4 (J1 to J10).**

* New code:
  * the `Residents` registry and the pins
  * the test-only `Audit`
  * `Eviction`
  * the reader protocol under eviction
  * reclaim's step reserve
  * a capacity controller on `cacheSizeInMb`
* **Eviction is now on by default**, and `level4.sh` is a required gate.
* About 2,950 lines in `java/src/`, 1,750 of them tests. No change to the
  record format or the public API.

**Evidence** ([docs/level4-evidence.md](../001-lean-model-levels-3-4/10-level4-evidence.md),
[docs/evidence/level34-conformance.txt](../001-lean-model-levels-3-4/07-level3-alignment/level34-conformance.txt)).

* Final conformance campaign: every trace `TRACECHECK OK`.
  * 81 Level 2 traces
  * 31 reclaim traces with 463 cuts
  * 30 eviction traces with about 473,000 slot checks
  * 68,901 Java-tier transactions
* Streams are identical byte for byte under every eviction schedule.
* Larger than memory: 20 million keys (a 1.5 GB index, 2 GB of values) in a
  2 GB JVM with a 500 MB budget. The live heap stayed at most 646 MB.
* Performance against Level 3: within the targets, with startup about 8
  percent slower.

**Bugs found along the way.**

* **Top node ordinals of 32,768 and more were written wrong (M30).** A
  database could restart silently wrong. Fixed first.
* **The node table could name a snapshot.** Fixed.
* **The cache size overflowed above 2,147 MB.** Fixed.
* **A6 fails in 5 of 68,901 transactions.** Frans accepted the weaker A6'
  with A-COPY at K1.

**The main weak spot is the sweep's cost (finding 10).** In the two-hour
soak with eviction:

* Reads were always right, and memory stayed bounded at 1.5 to 1.9 GB live,
  against 15 GB without eviction.
* But each sweep walks every resident object under the write lock: 35
  percent of the time.
* The paced writer reached only 123.5 of its 200 commits per second.
* G1 needed 81 full collections.


Phase 4: what is open (18 to 19 October)
========================================

* **Item 002:** M46, the top node ordinal bound of 2^30 − 1, which limits a
  database's lifetime under reclaim.
* **Item 003:** M49, a transaction that throws inside `Db.putKvs` is left
  half committed.
* **Item 004, indirect swizzling (open).**
  * It surveys the literature, takes measurements and sketches a design.
  * Recommendation: first take the pointer lock, the shared counter and
    `readSync` off the read path.
  * Then prototype handles for index nodes on a branch.
* **Item 005, the to-do list, created 19 October.**
  * Known faults: 005-01 (M49) and 005-02 (M46).
  * 005-03: the sweep's cost.
  * 005-04: what to do about A6.
  * 005-05: BergDB's future (publication, money, paid work).
  * 005-06: the literature for a publication.
  * 005-07: transaction synchronization.
  * Proposed order: 01 and 02 first, together with 07.

**Current state:** Levels 0 to 4 all pass their gates (`level1.sh` to
`level4.sh`). Levels 3 and 4 are also aligned with the proved Lean model.
The model does not cover concurrency, resource bounds, or the Java-to-model
mapping itself; those are tested or checked, not proved. Whether the idea
is novel is still open.
