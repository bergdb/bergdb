019-45. Investigate: does a start's rerun keep to the cache budget?
===================================================================

Status: done 2026-11-08, night 006-15. Kind: Investigate. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: in W7's rerun on F53 (016-10, night 4, 2026-11-06), ScaleBench's
runs from the OS's cache with a 133 MB cache budget, a 600 MB heap and a
startup distance of 200 MB, at 10M key24 keys, ran out of heap 8 s into
the database's start, in `DbStarter.rerunTransactions`, in both 2026.1
and 2026.2 (the same as on s1 on 2026-11-04, 016-02). The 665 MB runs
with a 2,660 MB heap were OK.

Why: is it by design (the rerun of a startup section holds its dirty
nodes, which cannot be evicted before they are written, so the heap must
hold about one startup distance's worth of them; then it is a limit to
state in docs/levels.md and the notes, next to the startup distance's
advice), or does the rerun not keep to the cache budget where it could
(a fault of 010-P5's bounded startup, in memory)? Not a known fault: in
both versions alike, and found by a benchmark's setting.

Frans: none, unless it turns out a fault of the Core before release
2026.3 (then Frans decides: fix or exception).

Done when: the rerun's memory at a start is explained (what it holds,
and its bound in terms of the startup distance and the budget), with a
probe; and either a sentence of the limit in docs/levels.md and
`releases/next.md`, or a fault registered.

First step: 016-10's State entry of 2026-11-07, 06:06 (agent mw4), the
outputs in `/Users/f/fl/bench/016/numbers/night/out/sb-c/`, and
`DbStarter.rerunTransactions`.


Findings
--------

Answer: by design, a limit, not a fault. The rerun keeps to the cache
budget as far as the budget applies, and a start needs, besides what the
running database holds, a transient working memory bounded by the startup
section and outside the budget, like D. A database that runs in a heap
can therefore fail to start in it; W7's runs had such a heap.

**What a start holds.** `Db.start` reads the startup section into
`StoredTrans` records (`Db.readTransactions`), every transaction after the
startup position, and keeps them until it returns; `DbStarter` keeps
maps of their node versions by position and by id (`newById`, `posToId`,
`posMap`, `HashMap<Long, ...>`), and its rerun (`rerunTransaction`)
makes a new `ValueNode` for each put of the section and rebuilds D, which
is pinned. The class histograms of the probe at 2M keys and a startup
distance of 200 MB, at the end of the rerun: 1.38M `StoredValueNode`s
with their 1.43M parsed `ValueNode`s and key arrays (about 145 MB; the
value bytes are shared with the rerun's values), 1.6M `HashMap$Node`s
and 2.0M `Long`s of the maps (about 80 MB), and the rerun's 1.33M new
`ValueNode`s, beside the key nodes, handles and pointers of the index.
The records and the maps are garbage when the start returns; the rerun's
values are the database's, as when it ran.

**The budget during the start.** The rerun's loads of nodes outside the
section start the capacity controller as a running database's loads do
(the load listener): 254 sweeps after loads in the start of the 200 MB
case. After the start the controller is at its usual level: within 2 s
the resident bytes were 242 MB, the pinned bytes (D) 209 MB plus the gap
between the watermarks (33 MB), and the live heap 229 MB, as when the
database ran (222 MB at the end of its load). So nothing that the budget
governs is left above it; what is above it is pinned (D) or not cache at
all (the records and the maps).

**Measured** with the probe `RerunHeapProbe` (in
[45-start-rerun-heap/](45-start-rerun-heap/RerunHeapProbe.java), test code
in package `bergdb.core`, kept here as evidence): ScaleBench's kind of
data (key24 keys, 8-byte values, transactions of 1,000 puts,
maxNodeSize30) loaded in a random order, then random updates, on a
`FileStream`; the live heap after a full GC every 50 transactions while
it ran, and every 25 ms during a new start; F53, JDK 27, G1, 2026-11-08.
MB of live heap; "extra" is the start's peak less the running maximum;
the section is the startup section's stream bytes:

| Keys | sd  | Budget | Running max | D (pinned) | Start peak | Extra | Section | Extra / section |
|---|---|---|---|---|---|---|---|---|
| 300k | 10  | 8   | 36.8  | 20.2  | 49.0  | 12.2  | 10.3  | 1.2 |
| 300k | 20  | 2   | 44.9  | 31.6  | 77.6  | 32.7  | 20.3  | 1.6 |
| 300k | 20  | 8   | 45.7  | 31.9  | 81.3  | 35.6  | 20.3  | 1.8 |
| 300k | 20  | 32  | 58.1  | 32.4  | 78.8  | 20.7  | 20.3  | 1.0 |
| 300k | 40  | 8   | 59.8  | 49.7  | 139.3 | 79.5  | 38.7  | 2.1 |
| 2M   | 20  | 8   | 77.0  | 45.1  | 94.2  | 17.2  | 20.1  | 0.9 |
| 2M   | 50  | 8   | 118.0 | 101.9 | 208.2 | 90.2  | 49.0  | 1.8 |
| 2M   | 200 | 133 | 288.1 | 228.9 | 663.0 | 374.9 | 181.0 | 2.1 |

* The start's peak does not follow the budget (77.6 to 81.3 MB for
  budgets of 2 to 32 MB at 20 MB) and follows the startup distance: 3.3
  to 4.9 times it, D included; the extra is 0.9 to 2.1 times the section.
* W7's failure, reproduced at 2M keys with W7's settings (startup
  distance 200 MB, budget 133 MB): the load and updates ran in a 600 MB
  heap (`-Xmx600m`, live at most 285 MB); a start in 600 MB ended with
  `OutOfMemoryError` in `DbStarter.postStartupCheck`; starts in 700, 800
  and 1,000 MB passed. The section is bounded by the startup distance, so
  the size of the database does not change this; at 10M keys D is larger
  (docs/levels.md, section 7: up to 2.3 times the startup distance's
  stream bytes at 200 MB), so W7's start needed more still.

**The limit**, now in docs/levels.md, section 7, Limits: a start needs
about twice the startup distance of heap above what the running database
needs (the section is near the startup distance, up to twice it by T3),
whatever the budget.

**Decided under Frans's delegation (2026-11-08, 22:17)**, by this
entry's agent:

* Not a fault of P5 or of the budget: P5 bounds the start's time, and its
  memory is bounded too, by the startup distance, not by the size of the
  database; the budget is the measure of what eviction can release, and
  the start's records and maps are not cache. No code change.
* Not reduced now: the start's working memory could be made smaller, by
  dropping each transaction's parsed value nodes (and their `posMap`
  entries) once it is rerun, and by maps of primitive longs in place of
  `HashMap<Long, ...>`; perhaps by half of the extra. That changes the
  startup algorithm's data of a Core released bug-free in 2026.3, and
  would not remove the limit (the records must be read before the rerun,
  D rebuilt). For 017-07 ("To consider") if Frans wants it.
* The line for `releases/next.md` is the coordinator's (the night's rule).

Log
---

2026-11-07. Registered by coord-1106 from W7's night 4 (agent mw4).

2026-11-08. Done in night 006-15 by the coordinator's agent C (after
020-10's B1 and H2's first part): the probe and its runs, the limit in
docs/levels.md, section 7; by design, not a fault; no code changed;
BEFORE COMMIT OK.
