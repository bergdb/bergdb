# 031-03. An elegant maintain()

Created 2026-11-25 by Frans Lundberg. Status: open.

A search for an elegant, simple design of `maintain()` and of how it
decides its work: one that gives an emptied database back its space
(RB-007 fixed), stops writing in a database the application no longer
writes to, and holds through crashes, stops and restarts without
recovery machinery of its own, with the stream deterministic (010-01,
P2). Frans, 2026-11-25: neither 028-53's A nor its B; `maintain()` is
the one part of the database's core that is not yet elegant, and an
elegant way is expected to exist.

What is known: 028-53 (the faults, A, B, C), 031-01 (one maintenance
step, w, Codex's review and the repair: the exact repair adds a state,
a store and a start that writes), 026-03, 024-32, 028-47, 028-51,
028-54.


Log
===

2026-11-25. Created by lead-1125 at Frans's request (14:54); taken by
an agent of lead-1125 (Fable, high).
