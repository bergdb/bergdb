021-07. Fix: the object reader's format errors are not BadFormatException
=========================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: `DbObject`'s reader, given bytes that are not a well-formed object,
throws other exceptions than `BadFormatException`, and in one case an
`AssertionError` that fails the database inside `rw()` (019-10). Found by
agent p04 of coord-1107 while reading the code for 020-04 (020-04,
section 10), at `7edcbe2`:

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
