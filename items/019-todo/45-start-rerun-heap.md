019-45. Investigate: does a start's rerun keep to the cache budget?
===================================================================

Status: open. Kind: Investigate. Frans: none.
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


Log
---

2026-11-07. Registered by coord-1106 from W7's night 4 (agent mw4).
