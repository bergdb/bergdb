021-08. Fix: the object reader has no limit on nesting depth
============================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: `DbObject`'s writer refuses a nesting deeper than `MAX_DEPTH`
(1,000; 005-23), but its reader has no limit. An object from another
writer (the C clone, 012; a binding in another language; damaged bytes)
nested much deeper can give a `StackOverflowError` at a read, which fails
the database inside `rw()` (019-10). Found by agent r07 of coord-1107
while doing 021-07 (its entry, Log).

Why: data must not fail the database or escape as an `Error` (020-01,
N2; section 5.5, question 2); 2026.4's theme is "bug-free" (020).

Frans: none (the coordinator's default, below).

Done when: the reader refuses a nesting deeper than the writer's limit
(objects and arrays counted alike, as the writer counts them) with
`BadFormatException`, so a get gives `ObjectCreationException` as for
021-07's cases, inside and outside `rw()`, and the database keeps
working; a test that fails before the change; `BEFORE COMMIT OK`; a line
in `releases/next.md` (with 021-07's).

First step: how the writer counts depth (005-23), and every recursive
path of the reader (parse, the iterators, `toJavaObject`, `toString`,
the index code that reads fields).


Log
---

2026-11-07. Registered by coord-1107 from 021-07's open point (agent
r07).
