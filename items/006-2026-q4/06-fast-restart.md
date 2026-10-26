006-06 Fast restart
===================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: open. A note of an idea, for thinking and discussion; not
investigated.


The idea
--------

Frans, 2026-10-26, during 005-38 (writes at scale):

A large database, say 100M to 1000M entries, should have a large startup
distance and a large cache to perform well. But BergDB is an in-process
database: it is restarted with the application that uses it, and that may
happen often. The startup distance sets the startup time, and so the
application's uptime.

For a controlled restart, the startup distance could be lowered for a while
before the restart, say from 1000 MB to 100 MB. Restarts for upgrades are
controlled and can be done when the load is low, usually at night. So it is
fine to trade performance for uptime: lower performance while preparing
for the restart, then a short startup. Frans calls the feature **fast
restart**.


Why it matters
--------------

005-38's first measurements (2026-10-26, in memory, random 24-byte keys,
node size 30) show how much a large startup distance saves in writes:
stream bytes a put at the end of a load of 10M keys, 920 at a startup
distance of 10 MB and 688 at 50 MB; at 50M keys, 1,219 and 924. Runs at
200 and 1000 MB, in a steady state of updates, are in progress there. So the
setting that makes writes cheap is the one that makes startup long.


Questions for later
-------------------

1. What a startup costs, part by part, as a function of the startup
   distance, D's size, the database's size and the cache (cold or warm OS
   cache; the in-process cache starts empty).
2. How the startup distance is lowered at runtime (Db has a setter; what it
   does, and whether lowering is safe), how the writer then catches up and
   how long that takes, what it does to commits meanwhile, and how to know
   the startup section is short enough.
3. Alternatives: a "write D now" operation, or a time budget for startup
   instead of a byte distance.
4. What a changing startup distance means for bounded startup (T3,
   [007-bounds](../007-bounds/readme.md)), Rule A and Rule R, the startup pos
   policy and reclaim's use of twice the startup distance.
5. The cache after a restart: how long until a large database performs
   well again, and whether to save the hot set at a close and read it back
   at a start.
6. Crash restarts, which fast restart does not help.

What a clean close (`stop()`, `close()`) writes today is a separate
question, which Frans investigates in a session of its own (2026-10-26).
