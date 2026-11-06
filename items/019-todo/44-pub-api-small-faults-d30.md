019-44. Fix: four small faults of the Pub API found by the documentation's read-through
========================================================================================

Status: open. Kind: Fix. Frans: none (the coordinator's defaults below;
Frans may choose otherwise).
Created 2026-11-06 by Frans Lundberg.

What: agent d30 of 006-13, reading the documentation against the code for
release 2026.3 (018-01, "Ready", 4), found four places where the Pub API
(part of the Core, 018-01, section 1) does something its Javadoc does
not say:

1. `DatabaseBuilder.clock(null)` is accepted; `start()` then throws
   `IllegalArgumentException`, after it has made the directory and
   `bergdb.lock`.
2. A `CryptoKey` of another algorithm makes `start()` throw
   `IllegalStateException`, which `start()`'s Javadoc does not list.
3. A String value with a lone surrogate is stored with '?' in its place,
   silently; keys refuse it since 015-49 (S2-F24), values do not.
4. `Clock` and `TestClock` never state their thread safety, and
   `TestClock`'s time is not volatile, while the transaction threads read
   it.

Why: Frans, 2026-11-06, 12:31: "If the bug is in Core, register it and
fix it to your best ability." A value changed silently (3) is the most
serious: the database returns other characters than were put.

Frans: none. The coordinator's defaults (KISS, 010-P13): (1) refused at
`clock(null)` with `IllegalArgumentException`, before any file is made;
(2) documented in `start()`'s `@throws` (or refused at the builder, if as
simple); (3) refused at the put with `IllegalArgumentException`, as for
keys (a behaviour change: a line in `releases/next.md`); (4) `TestClock`'s
time volatile, and one sentence each that a `Clock` must be thread-safe
and that `TestClock` is.

Done when: each with a test that fails before it (for 2 and 4 where a
test can show it); `BEFORE COMMIT OK`; landed before 20:15 (main's freeze
for release 2026.3), else left for Frans.

First step: d30's report in 006-13's progress (12:44), and each place in
the code.


Log
---

2026-11-06. Registered by coord-1106 from agent d30's read-through.
