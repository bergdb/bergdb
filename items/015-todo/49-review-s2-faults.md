015-49. Fix: review S2's 27 faults of the indexes and the objects
=================================================================

Status: open. Kind: Fix (to be split). Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (known issues of it); every one is in 2026.1 too.

What: review S2 (items/016-release-2026-2/06-reviews/S2.md) read the
promises of the indexes and of the objects (016-06, sections 3.10 and
3.11) against their code, at `fa08db4`, and found 27 faults, each with a
probe (06-reviews/S2/), five also with a test that fails
(S2-tests.diff). They include wrong answers in normal use (scans with
`inclusive(false)`, `prefix()`, later composite levels, an index given a
directory twice), lost data (final fields, `Object[]` elements, a field
that hides a superclass's, `Date` and nested objects stored empty), an
ICU collator shared by threads without a lock, and a composite index whose
definition changes at a restart (S2-F14). No second agent has checked them
yet: the first step is a verification, as 016-06, section 2.6.

The faults:

* S2-F1. An ICU collator is used by several threads at once, and gives wrong sort bytes
* S2-F2. inclusive(false) without startAt() gives an empty secondary-index scan
* S2-F3. A String or byte[] put over an object leaves its index entry; the key can then not be deleted
* S2-F4. A double read into a String field reads as "d:1.5"
* S2-F5. A stored double of 2^63 reads into a long field as Long.MAX_VALUE
* S2-F6. A stored value of another kind read into a primitive field gives 0, or throws Bug
* S2-F7. The numbers, strings and booleans of an Object[], or of an Object field, read back as null
* S2-F8. An array that holds itself throws StackOverflowError on put
* S2-F9. A final field is not stored, silently
* S2-F10. A database with an ICU index does not start without ICU
* S2-F11. A build's job says it is done when the database stopped, and that it created an index that was deleted
* S2-F12. A put whose index set is read before deleteIndex() writes an entry that a new index of the name return
* S2-F13. prefix() on a secondary string index finds at most the exact matches at the start of the index
* S2-F14. A composite level with two or more fields loses its commas in the stored index info; after a restart t
* S2-F15. nestedField() accepts an empty part, and every put of an object with the outer field to the index's di
* S2-F16. A build indexes the objects of the directory's subdirectories, which the writers do not maintain
* S2-F17. usePrimary(): startAt() before dir() finds nothing, and without dir() the scan returns the database's
* S2-F18. A field of a JDK value class or an enum is stored as nothing: a Date reads back as the time of the rea
* S2-F19. A field that hides a superclass field of the same name is not stored; the superclass's value is stored
* S2-F20. An index with the same directory given twice returns each object twice
* S2-F21. A no-argument constructor that throws gives a Bug, and runs once more than the reads
* S2-F22. eq() or startAt() on a later composite level, with no eq() on the levels before, applies to the first
* S2-F23. hasNext() says true and next() throws NoSuchElementException when the last entries of a scan are stale
* S2-F24. Keys and index names with a lone surrogate are stored as with "?", so two keys, or two indexes, are on
* S2-F25. usePrimary(String.class) leaves out the String values and returns the objects' bytes as strings
* S2-F26. An object whose indexed String field is null cannot be put, and stops a build for good
* S2-F27. A refused index creation leaves the index in memory: its name is taken, and the writers write its entr

Done when: each is verified, then registered as an entry of its own and
fixed, or closed with the reason.

First step: verify the faults that can lose or invent data or give a wrong
answer in normal use (016-06, section 2.6), and split them into entries.



S2-F24 fixed (night 006-12, 2026-11-05)
---------------------------------------

S2-F24 is the one fault of this entry in release 2026.3's goal (018-01,
section 3.1); it is fixed, and the entry stays open for the others, the
experimental code's (018-01, section 3.2).

**The fault**, as S2 found it: `PubKeys.u2i` (with `createIKey`),
`PubKeys.udir2idir` and `IndexManager.checkIndexName` took a string with a
lone surrogate, a char of U+D800 to U+DFFF that is not part of a surrogate
pair; `Keys.toBytes` encodes with `getBytes("UTF-8")`, which writes it as
`?`. So "/k/a" followed by U+D800 and "/k/a?" were one stored key, and a
put of one overwrote the other; two index names so were one info key and
one entry directory.

**The fix**, the review's: `PubKeys.hasLoneSurrogate(String)` (new) finds
such a char, and `u2i`, `udir2idir` and `checkIndexName` refuse a string
that has one with `IllegalArgumentException`, as a malformed key ("If
'key' is null or otherwise invalid"). Every key of the Pub API passes
`u2i` (connections' and rw-transactions' get, put, delete and exists, and
`w()`), every directory of a scan or an index `udir2idir`, and every index
name `checkIndexName` (`Database.indexBuilder`).

**The stream's bytes** (P2): unchanged for every key that was taken and
stays taken: `u2i` returns the same ikey, and `Keys.toBytes` is untouched.
A key that was stored with `?` in a database stays as it is and is read
by its `?`; only a new call with a lone surrogate is refused. StreamDigest
does not apply: its workloads use the Core API, below `PubKeys`.

**Tests**, each failing before the fix:

* `PubTester.testKeyWithLoneSurrogateRefused`: put, get, exists, delete
  and `w().put` of four keys with a lone surrogate are refused, "/k/a?"
  keeps its value, and a key with a surrogate pair (U+1F600) is put and
  read. Before: "put took a key with a lone surrogate, /k/a\uD800".
* `PubKeys.testLoneSurrogateRefused`: `u2i` and `udir2idir` refuse lone
  surrogates (high or low, at the end, inside, reversed), and a pair keeps
  its ikey. Before: "Expected true, but was false".
* `IndexManager.Tester.testIndexNameWithLoneSurrogate`. Before: "taken, 2
  chars".

**Principles** (010-01): no setting, state, thread or format change; P11,
the review's own fix.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02), as
one entry for now: the review ended at 21:26 and no fix of it fits before
the freeze.

2026-11-05, night 006-12 (W1): S2-F24 fixed (its section above), in the
clone `/Users/f/fl/bench/006-12/g4b`, branch `w1-g4b`; the entry stays
open for the other faults, which are outside 2026.3's goal.
