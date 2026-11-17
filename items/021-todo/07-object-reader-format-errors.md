021-07. Fix: the object reader's format errors are not BadFormatException
=========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: `DbObject`'s reader, given bytes that are not a well-formed object,
throws other exceptions than `BadFormatException`, and in one case an
`AssertionError` that fails the database inside `rw()` (019-10). Found by
agent p04 of coord-1107 while reading the code for 020-04 (020-04,
section 10), at `b4cf896`:

1. A nested object of size −1, which `DbObject.parse` reads as Java's
   null (lines 739 to 741): no writer writes it; reading it gives an
   `AssertionError` with `-ea` or a `NullPointerException` (the `DbField`
   constructor, 762; in an array, `DbArray`'s iterator, 241).
2. A string or byte array length below −1, or a field name's negative
   length: `NegativeArraySizeException` (`DbString.parseToString`, 112;
   `DbObject.readFieldInfo`, 700).
3. A bad field type byte: `IllegalArgumentException` (`DbField.parse`,
   857).
4. `Z` after an element ends an array silently (`DbArray`, 201).
5. `DbObject.Builder`: `addObject`, `addArray` and `addDbValue` with null
   throw an `AssertionError` (with `-ea`) or a `NullPointerException`,
   while `addString(name, null)` stores a null.

`KvToObjectImp` catches only `BadFormatException`, so 1 to 3 reach the
caller of a get as they are.

Why: data from another writer (the C clone, 012; a binding in another
language; a damaged value) must not fail the database or escape as an
unchecked JDK exception (020-01, N2; 020-01, section 5.5, question 2:
"May any user data ... make BergDB throw an Error, or fail the
database?"; the answer there should be no). 2026.4's theme is
"bug-free" (020).

Frans: none (the coordinator's default, below).

Done when: each of 1 to 4 is refused with `BadFormatException` by the
reader (so `DataFormatException` at a get), with a test of each that
fails before the change; 5: the Builder refuses a null with
`IllegalArgumentException` in each add method, or as 020-04 decides
(question 1b); `BEFORE COMMIT OK`; a line in `releases/next.md`.

The default for 1: refuse it as `BadFormatException` now. No writer
writes it, and under every option of 020-02's question 1b but (a) it
stays refused; under (a) it is read as a null. If Frans chooses (a)
before this entry is done, read it as a null instead.

Related: 021-06 (the read side of strings; it changes
`DbString.parseToString` too, so whichever is done second merges);
020-04 (no stored null; its step B touches the same reader).

First step: a test per case that builds the bytes by hand and gets them
through `get(key, SomeClass.class)` inside and outside `rw()`.


Log
---

2026-11-07. Registered by coord-1107 from 020-04, section 10 (agent p04).

2026-11-07. Taken by agent r07 of coord-1107.

2026-11-07. Done by agent r07 of coord-1107 (006-14), with the
defaults (1: refused now; 5: `IllegalArgumentException`). Each case is
refused by the reader with `BadFormatException`; at a get that is an
`ObjectCreationException` (`KvToObjectImp.entryToDbObject`), not the
`DataFormatException` that "Done when" says: a get never gave
`DataFormatException` for bytes that are not an object, while an index
update that reads the previous value does (`RwEnvironmentImp.indexEntries`).

* Case 1: `DbObject.parse` refuses every size below 0, −1 too, and a
  size past the end of the bytes. A null object as the writer writes it
  (a field count of −1) is read as before.
* Case 2: `DbString.parseToString` refuses a size below −1 or past the
  end (−1 is still a null string); `DbByteArray.parseToByteArray` a size
  past the end too; `DbField.parse` a name size of 0 or below, or past the
  end (a size of 0 gave an `AssertionError`, as an empty name). The
  past-the-end checks come before the allocation: a size near 2^31 gave an
  `OutOfMemoryError`, an Error that fails the database in `rw()`.
* Case 3: `DbField.parse`'s bad type byte is a `BadFormatException`.
* Case 4: `DbArray`'s iterator refuses `Z` after an element; `Z` as the
  first byte (the null array) is read as before.
* Case 5: the `DbField` constructor refuses a null or empty name and a
  null value with `IllegalArgumentException` (they were asserts), and
  `Builder.addString` a null value; so every add method refuses a null.
* Found on the way, the same fault: bytes that end inside a field. An
  array cut at its start gave an `AssertionError` (`DbArray`'s iterator,
  an assert, now a `BadFormatException`), other cuts an
  `IndexOutOfBoundsException`, which the `DbObject` constructor now turns
  into `BadFormatException` around each field's parse; a negative field
  position is refused with the others.
* Tests, each failing on `95f2ce5`'s code: `DbObjectTester`'s
  `testReaderNestedObjectSizeMinusOne`, `testReaderBadLengths`,
  `testReaderBadTypeByte`, `testReaderNullMarkAfterAnElement`,
  `testReaderCutBytes` (every proper prefix of an object with each type)
  and `testBuilderRefusesNull`, and `PubTester.testMalformedObjectRefused`
  (case 1 through `get` as a class, `DbObject` and `Object`, outside and
  inside `rw()`; the database goes on after).
* No change of the bytes written or of how a well-formed object is read;
  020-04's no-null design is not started.
* `releases/next.md`: a Pub API bullet.

Where it meets later work: `DbString.parseToString` has the new size
check, which 021-06 (its decoding) and 020-04's step A (−1 refused too)
change; whichever comes later merges. Of 020-04's section 4, this entry
did the `DbField` constructor's and `DbField.parse`'s lines, `addString`'s
refusal (in the Builder, not through `DbString`), `DbObject.parse`'s −1,
and `DbArray`'s `Z` after an element and its failed `o` element; step A
still refuses `Z` as the first byte, −1 for strings and byte arrays, and
a field count of −1. 020-04's line numbers are `b4cf896`'s.

Left open: the reader has no depth limit. An object nested deeper than
the writer's `MAX_DEPTH` (1000, 005-23), from another writer, recurses
in the `DbObject` constructor, and deep enough gives a
`StackOverflowError`, an Error that fails the database in `rw()`; each
level also copies its bytes. Not fixed here; a new entry if wanted.

`BEFORE COMMIT OK (122 s)` (2026-11-07, 16:41; 1273 unit tests, 87
f-tests); StreamDigest digests unchanged (the f-tests).
