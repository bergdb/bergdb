021-08. Fix: the object reader has no limit on nesting depth
============================================================

Status: done. Kind: Fix. Frans: none.
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

2026-11-07. Taken by agent r07 of coord-1107.

2026-11-07. Done by agent r07 of coord-1107 (006-14).

* How the writer counts: `toDbObject` refuses more than `MAX_DEPTH`
  (1,000) objects on its path; arrays are not counted (005-23), so a
  chain of arrays is limited only by the stack (the writer reached 10,000
  levels, and failed at 50,000 with a `StackOverflowError`). And it
  writes a null object for a null field of its deepest object: 1,001
  object levels in the bytes.
* The reader's limits (`DbObject`): `MAX_READ_OBJECTS` = `MAX_DEPTH` + 1
  objects on a path, as the writer writes them, and `MAX_READ_LEVELS` =
  2 × `MAX_DEPTH` + 1 objects and arrays counted alike, which leaves
  room for an array between each two objects. Not one limit counted
  alike at 1,001: that would refuse what the writer writes, such as a
  chain of objects through `Object[]` fields (005-23's tests too).
* The check: the public constructors walk the bytes once, without
  copying, before the recursive parse (`checkNesting`, `scanObject`,
  `scanValue`), and refuse a deeper nesting with `BadFormatException`;
  nested objects are parsed without walking again. The walk must come
  before the parse: the reader copies each nested object's bytes and
  keeps them along its recursion, so a 2.2 MB value of 100,000 nested
  objects gave an `OutOfMemoryError` before the stack overflowed. The walk
  stops at the first fault that the reader refuses at the same place,
  and goes on wherever the reader goes on.
* The Builder (and so `toDbObject`, which builds with it) refuses to build
  deeper than the reader reads, with `IllegalArgumentException`: a put of
  a chain of more than 2,000 arrays was stored and is now refused.
* Every recursive path of the reader works on bytes so checked: the
  constructor's parse, `DbArray`'s parse and iterator, `toJavaObject` and
  the getters. `toString` does not recurse; the index code reads fields by
  the index's names, not by the data's depth.
* Measured on F53 (2026-11-07): the reader with `toJavaObject` read
  20,000 levels of arrays on the default stack (2 MB) and 2,500 on a
  1 MB stack; 1,000 objects with an `Object[]` between each (the
  writer's, 2,000 levels) read on 1 MB and 2 MB. With a 512 KB stack even
  the writer's 1,001 objects overflow, as before.
* Tests, each failing on `630acb3`'s code: `DbObjectTester`'s
  `testReaderNestingDepth` (arrays and objects at the limits, one more,
  and 100,000 deep, the bytes built by hand) and
  `testBuilderRefusesTooDeep`, and `PubTester.testDeepObjectRefused`
  (100,000 arrays, a `StackOverflowError` before, and 100,000 objects;
  gets outside and inside `rw()`, the database goes on), with 021-07's
  test now a call of the same helper.
* No change of the bytes written; the f-test `testDeepAtLimit` (1,000
  objects, written and read back) passes.
* `releases/next.md`: a Pub API bullet after 021-07's.

Left open, not this entry's: the writer has no cycle check for arrays (an
`Object[]` that holds itself gives a `StackOverflowError` at the put, an
Error that fails the database inside `rw()`); and a get of an object near
1,000 objects deep takes about 0.5 s (the nested bytes are parsed again at
each level of `toJavaObject`), a cost like 005-23's.

`BEFORE COMMIT OK (120 s)` (2026-11-07, 16:57; 1276 unit tests, 87
f-tests).
