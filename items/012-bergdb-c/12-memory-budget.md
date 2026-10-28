012-12. Task: the memory budget
===============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase D (012-01, section 8). Effort: high. After: 012-10.


# 1. The goal

Level 4 in C: a database larger than its memory. The index nodes and
values that are not pinned are evicted to a budget, and loaded again from
the stream when needed. Rewritten for C, not ported (012-01, 4.1): Java's
`Cache3`, `Eviction` and `Residents` are built for threads and the
garbage collector; C has one caller, and frees as 012-01, 4.5 says.

Done when:

1. **The node table**: node id to the node's handle (012-07's design), the
   canonical object of each node, and the bytes each resident node and
   value takes, counted exactly by the allocator (P8; 012-01, 4.5).
2. **What is pinned**, as Java pins it (levels.md, section 7): the super
   root, D (the index nodes dirty since the startup position), the record
   being written, the newest written top node; and a node in use by the
   call that runs.
3. **Eviction** to the budget at transaction ends and after loads, where
   Java evicts, in the call: a simple policy (CLOCK over the unpinned
   nodes and values, or what Java's capacity controller does, if as
   simple). It runs at the end of the call, a safe point (012-01, 4.5),
   so what it takes is freed at once; an evicted object's handle dies as
   in Java and is freed when no pointer holds it.
4. **The bytes do not change** (P2): every cross workload with budgets from
   a few kilobytes to unlimited gives the same files and dumps as without
   eviction, as Java's `EvictionInvariance` checks for Java.
5. **Larger than memory**: a database of a million keys with a budget of
   a few megabytes runs, its resident bytes stay below the budget plus
   what is pinned, and its reads equal Java's on the same workload.
6. The budget is the option `cache budget` (Java's cache size
   indicator), and `bergdb_stats` reports the resident bytes.


# 2. Read first

* Java: `Cache3` (292 code lines), `Eviction` (401), `Residents` (136),
  `Handle` (73), `NodeCollection`'s loads, `Db`'s `eviction` calls.
* 012-01, 4.5 (memory in C).
* `docs/levels.md`, Level 4 and section 7; 001-08 and 009-05 (the
  alignment of Level 4, with handles); 009-02 (the handle and the
  table); 010-01, P1, P3 and P8.
* `java/stress/EvictionInvariance.java`, `LargerThanMemory.java`.


# 3. The work

1. The node table and the byte counts, beside 012-07's handles.
2. Pinning, and the check that a pinned node is never evicted (a debug
   check under the test build).
3. Eviction in the calls; loads through 012-10's path.
4. The invariance runs, and the larger-than-memory run.


# 4. Tests

The cross sets with small budgets; a C invariance test (the same workload
under several budgets, the same bytes); the larger-than-memory run under
the sanitizers on a smaller size; `leaks` after long runs.


# 5. Notes

* Eviction decides only what is in memory, never the bytes. If a byte
  changes with the budget, the cause is a pointer whose serialized
  reference depends on residency: a bug in C, as Java proved the opposite
  for its handles (009-05).
* Java's default policy depends on timing (P8's noted departure); C's need
  not, and should not.


# 6. Progress

Not started.
