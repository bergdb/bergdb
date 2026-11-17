015-12. Fix: after a key node's growth, a reader can see its arrays without their contents
==========================================================================================

Status: done (2026-11-03). Kind: Fix. Created
2026-11-03 by Frans Lundberg.

For release 2026.2. Found by review R1 (016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F1, with probes.

What: `KeyNode.growCapacity` (and `setContentFrom`) copies the arrays and
stores the three array fields with plain stores. A reader that read
`size` before the growth and the fields after it sees the new arrays by a
data race; on AArch64 the fields' stores can become visible before the
copy's. The reader then reads 0 or null below `size`: a search misses a
key that was there long before its lookup time, or returns the value of a
later or uncommitted transaction.

Evidence (R1/, on F53 at `47ba87f`): `GrowSearch` 8 keys not found in
477 million searches; `GrowFuture` 3 values of time 20 at time 15 in 1.1
billion. A database probe (4 million transactions, 101 million gets) saw
no wrong answer. The same code is in 2026.1, so it goes into 2026.1's
post-release notes.

The fix chosen by the coordinator (016-02): a release fence
(`VarHandle.releaseFence()`) after the copies and before the field stores,
in both methods, which orders them on every machine and costs the
readers nothing; the reader's side keeps its plain reads, which depend on
the field's address, as the fast path does (015-14 is Frans's question
whether to make such reads acquire reads). A jcstress test of the growth
(the probe's two actors), and the probes rerun.

Done when: the probes show no wrong read; the jcstress test passes in
default mode on F53; `BEFORE COMMIT OK`.


State
-----

2026-11-03, 17:04: the fix, the jcstress test and the gate done in the
clone (rebased on `9d0f33c`); handed off for review (`/Users/f/fl/bench/016/015-12/handoff/`).
Open: the review; the jcstress test in default mode on F53 (Done when).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 16:49 to 17:04, by agent K (016-05), in
`/Users/f/fl/bench/016/015-12/repo` from `main` at `17270d1`:

* **The probes on the base** (R1/, compiled against the base's jar, 20 s
  each, F53 at a load average of about 40): `GrowRace` `reads
  1938146287, klong 0 below size: 71, null pointer below size: 76,
  reference 0 below size: 15`; `GrowSearch` `searches 373320916, key 1
  not found: 4, found with a wrong reference: 983`; `GrowFuture`
  `searches 953306847, the value of time 20 at time 15: 5, key 1 not
  found: 9, another reference: 7`. The fault, as R1 saw it.
* **The fix**, `dag/KeyNode.java`: `VarHandle.releaseFence()` after the
  three copies and before the three field stores, in `growCapacity` and
  in `setContentFrom` (there before the monitor, whose entry is no
  release). The readers keep their plain reads; they read the elements
  through the field they read, the address dependency of 015-14. The
  class comment and `klongs`' synch note say so.
* **The jcstress test**, `java/stress/jcstress/GrowthPublication.java`
  (the probe's two actors): a full key node of 14 klongs, each with a
  handle and a reference; the writer appends one (`addToEnd`, a growth to
  arrays of 30); the reader reads `size`, the three arrays plainly, and
  every element below the size it read. Forbidden: an element below the
  size without its copy, and the new size with an old array. `run.sh`'s
  header names it.
* **The mutation**: the test, run alone in quick mode with 4 CPUs (as
  `run.sh` does, plus `-c 4`): on the base's jar `[FAILED]`, `14, 1, 0`
  (an element below the size without its copy) 47 times in 40 million,
  with `14, 1, 1` (the old size, a new array with its copies) 91,408
  times; on the fix's jar `[OK]`, `14, 1, 0` 0 times in 41 million, with
  `14, 1, 1` 84,507 times. `run.sh` in sanity mode, all six tests on the
  fix: `[OK]` each. Default mode not run (the brief: sanity mode; F53
  shared).
* **The probes on the fix** (the same commands): `GrowRace` `reads
  1789348620, klong 0 below size: 0, null pointer below size: 0,
  reference 0 below size: 0`; `GrowSearch` `searches 479750101, key 1
  not found: 0, found with a wrong reference: 0`; `GrowFuture` `searches
  1206016220, the value of time 20 at time 15: 0, key 1 not found: 0,
  another reference: 0`; `DbGrowProbe 40` (`-Xmx6g`) `transactions
  3585410, gets 100246388, missing 0, wrong value 0, thrown 0` (R1's
  base run: none either).
* **The gate**: `java/before-commit.sh`, 16:57 to 16:59: `BEFORE COMMIT OK
  (104 s)`, 1,101 unit tests and 78 f-tests. Then the clone rebased on
  `main` at `9d0f33c` (015-07's change, in other files) and gated again,
  17:01 to 17:03: `BEFORE COMMIT OK (113 s)`, 1,108 unit tests and 78
  f-tests.
* Not changed: the stream format, the Pub API, 009-02 (its row "node
  arrays" in 3.3 is the plan's, before this), docs/levels.md (section 7
  names the jcstress tests as a set).

2026-11-03, 17:06. Reviewed by the coordinator (016-05, H5): no faults. Combined
gate on main: BEFORE COMMIT OK. jcstress in default mode with
GrowthPublication: in 016-08's F6.
