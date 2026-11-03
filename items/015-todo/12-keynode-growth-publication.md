015-12. Fix: after a key node's growth, a reader can see its arrays without their contents
==========================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2. Found by review R1 (016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F1, with probes.

What: `KeyNode.growCapacity` (and `setContentFrom`) copies the arrays and
stores the three array fields with plain stores. A reader that read
`size` before the growth and the fields after it sees the new arrays by a
data race; on AArch64 the fields' stores can become visible before the
copy's. The reader then reads 0 or null below `size`: a search misses a
key that was there long before its lookup time, or returns the value of a
later or uncommitted transaction.

Evidence (R1/, on F53 at `6f932f0`): `GrowSearch` 8 keys not found in
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


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
