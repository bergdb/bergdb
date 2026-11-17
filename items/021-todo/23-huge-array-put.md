021-23. Fix: a put of an array too large to store throws OutOfMemoryError
=========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a put of an object whose stored value would take more than 2^31 - 1
bytes is not refused with `IllegalArgumentException`, as the package's
"Objects" and `WBuilder.put()` say. With `-Xmx3g`, an object of 2,100
references to one 1 MiB `byte[]` (1 MiB in memory, 2.2 GB stored) throws
`OutOfMemoryError` after 0.5 to 1 s from `put()`, `w()` and
`DbObject.toDbObject()`, and inside `rw()` the error fails the database
(the next put throws `DbFailedException`). `DbArray.Builder.add()` copies
each element into its buffer, and `ObjectFormat.checkValueSize()` refuses
only the element that takes the array past the limit, so about 2 GB is
copied first; with `-Xmx8g` the refusal comes at a resident size of 4.6
GB, its message "size: a value of 2147493890 bytes; ..." without the
place. Found by a new-user application, 020-24-12, U12-1 (high); the
reproduction `probe/HugeProbe.java` (`HugeProbe rw 2100` with `-Xmx3g`)
in `/Users/f/fl/bench/2026-11-09/app-u12/app/`. With it, the Javadoc of
020-24-12's U12-2, U12-3 and U12-5 to U12-8 (changes of Javadoc only, as
020-24's commits).

Why: a call that the Javadoc says is refused fails the database in
`rw()`, and an application that keeps one large array in several places
meets it with a small object.

Frans: none. U12-4 (the messages of a field type not on the list name the
type, not the class put, one field a run, and suggest nothing) is an API
point for his list.

Done when: a test that fails before and needs no large heap; the object's
size counted before anything is copied, as an object's fields are summed
before it is built, and the refusal naming the place and the limit, not
the internal "size:"; `DbObject.Builder` and the other builders checked
for the same order; the Javadoc of U12-2, U12-3, U12-5 to U12-8 made true
and complete; `BEFORE COMMIT OK` and `JAVADOC PUB OK` under the gate lock;
lines in `releases/next.md`.

First step: where the put's walk copies before it checks a size.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-12's U12-1 (and the
Javadoc findings U12-2, U12-3, U12-5 to U12-8), and taken by its agent o23
(clone `clone-o23`, on main's 595418e).

2026-11-09. Done by o23: commits 71e909b (021-23, U12-1) and 4d65bb5
(020-24, U12-2, U12-3, U12-5 to U12-8) in `clone-o23`, on main's 595418e,
to land. Severity: high, as 020-24-12 gave it. In 2026.4's Data Objects
(020-09).

* Where it copied. `DataObjects.toDbObject()` builds bottom up:
  `DbByteArray`'s constructor clones each `byte[]`, `DbString` encodes
  each string, `DbArray.Builder.add()` writes each element into a growing
  `ByteArrayOutputStream`, and `build()` copies it twice; only then does
  the parent see the array's size. An object's fields are summed in
  `DbObject.Builder.build()` before it allocates, but its field values are
  already built, so an object of 25 fields of one 100 MiB array was
  cloned, 2.6 GB, before its refusal (020-24-12's `FieldsProbe`).
* Fix, in `DataObjects.Put`: a first walk, `storedSize()`, counts the
  stored bytes of the object exactly as the build writes them (integers
  by `integerSize`, strings by `StringUtil.utf8Size`, primitive arrays in
  a loop without boxing, each object's frame by `headSize`), without a
  copy, each byte once, when found; it refuses at the place where the
  count passes `MAX_ARRAY`, 2^31 - 9 bytes, the most a Java array holds
  and so the most that the build can make (R15 allows 2^31 - 1;
  `DbObject.Builder` refused above `MAX_ARRAY` already). The walk makes
  the build's checks that keep it finite and exact (a cycle, the depth, a
  value of another class, a null element), with the build's messages; a
  lone surrogate is left to the build. Then the build, unchanged but for
  an element's step, now kept as an index and made text only for a
  message. The message: "The object is too large: its stored value
  passes 2147483639 bytes at 'parts[2047]'. A stored value has at most
  2^31 - 1 bytes, and in Java at most 2^31 - 9, the largest Java array
  (bergdb 020-07, R15; 020-09, section 4.7)."
* The other builders. `DbObject.Builder` sums its fields before it
  allocates: right. `DbArray.Builder.add()` checks the size before it
  copies the element, as its Javadoc says, but a builder cannot know the
  elements to come, so an array built by hand to the limit copies what it
  holds; and its buffer grows by doubling, and `build()` copies it twice,
  part of U12-2's factor. Not changed (no behaviour change asked); a
  smaller factor would come from one exact allocation in the build, now
  that the size is known first.
* Cost: the walk reads each field and element once more. A put of an
  order of 14 fields with 5 lines in a memory database took 6.6 to 7.1 µs
  before and 6.9 to 7.5 µs after (F53 under a load of 20 to 26, noisy);
  `toDbObject()` of it 2.7 against 3.3 µs; of an `int[]` of a million, 68
  against 56 ms (the index step saves a String an element). A string
  costs a count of its chars.
* Tests in `DataObjectsTester`: `testPutTooLarge` (2,100 references to
  one 1 MiB `byte[]`, 240 to one `double[]` of 2^20, 2,100 to one object
  holding 1 MiB, and a `byte[][]` at the top: each refused by
  `toDbObject()`, `put()`, `w()` and `rw()`, the message naming the place,
  `parts[2047]`, `rows[227]`, `all[2047].parts[0]`, `[2047]`, and the
  limit; nothing written; the database goes on; under 0.1 s and a few MiB)
  and `testStoredSizeExact` (with a test hook, `toDbObject(x, limit)`: at
  the limit of the stored size taken, a byte below refused, for 23 values
  of every kind at the top and in fields, and the place in a string, a
  frame and a nested frame); `r1()` checks the same for each random
  object, 400 in the unit group and the night's. Before the fix, with
  `-Xmx2g`, all three failed: `testPutTooLarge` with `OutOfMemoryError`
  (89 s for the class), the others "taken, not refused".
* Probes on the fixed release jar, `-Xmx3g`: 020-24-12's `HugeProbe`
  put, w, rw and todb with 2,100, and rw with 4,097 references: refused in
  12 to 16 ms, the database goes on, nothing written; `FieldsProbe` put
  and rw: refused at 'b20' in 10 ms. A `String[]` of 2,100 references to
  one 1 MiB `String`: refused at 'texts[2047]' in 0.6 s (the strings'
  chars counted).
* Javadoc (020-24): the package's "Objects": the limit as Java has it,
  2^31 - 9, counted first; a reference stored once per reference (U12-1);
  the heap of a put, 4 to 5 times the stored size, and which
  `OutOfMemoryError` fails the database, `put()` and `w().put()`
  converting at the call, `rw()` in its action (U12-2, also at
  `Connection.put()`); a Data Object class top-level or static nested,
  superclasses that declare a stored field public, no platform class as a
  superclass, no field of a type variable (U12-3; 020-09, V1, V4, V5,
  V9); the grammar of a text read as a number, with what reads as 0
  (U12-5; 020-09, section 5.5); a float stored as a double: `eq(0.1)`
  against `eq(0.1f)` (also at `IndexBuilder`), its text, 9 bytes, 1e300
  as Infinity (U12-6); `Connection.get()` with a primitive, wrapper or
  array class reads "p" or "array" of any stored object, null without
  one (U12-7; 020-09, section 5.9); bytes as a scalar, an array into
  `byte[]` clamped (U12-8; 020-09, sections 5.4 and 5.7). `DbObject` and
  `WBuilder.put()` name the limit.
* `releases/next.md`: Pub API (021-23) and Documentation (020-24).

Runs, under the gate lock (2026-11-09, 16:59 to 17:02), on the tree of
both commits: `BEFORE COMMIT OK (149 s)` (unit 1582, f 86, demos);
`JAVADOC PUB OK`. No Core code changed, so no `level1.sh`.
