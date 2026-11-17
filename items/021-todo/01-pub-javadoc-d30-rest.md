021-01. Fix: the Pub API's Javadoc: DataFormatException, dated history, Time's BadFormatException
=================================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: three places where the user Javadoc of the Pub API (`bergdb.pub`,
`bergdb.pub.util`) does not say what the code does, or says how it was
before. Checked on `main` at 8682edd (2026.4-dev); all three are open.

1. `bergdb.pub.DataFormatException` belongs to the object code and user
   indexes (thrown by `DbValue`, `DbObject`, `RwEnvironmentImp.indexEntries`
   and `IndexBuilderImp.createStep`), but its Javadoc says only "Thrown
   when data in the database has an illegal format". The other exceptions
   of that code say that they belong to it and that it is experimental
   (`ObjectCreationException`, `MissingKeyFieldException`,
   `NoSuchIndexException`, `IndexAlreadyExistsException`: "experimental
   in 2026.3 ... bergdb 018-01, D6"). Its trailing `NOTE 1304 Frans` asks
   how it relates to `core.InternalDataException`.
2. Dated history sentences in the user Javadoc: sentences that say since
   when, or how it was before, where a user needs only what is. Found:
   `Database` (stop() and close(): "2026-10-27, bergdb 005-55; until
   then ..."; "Errors (2026-11-06, bergdb 019-10)"), `DatabaseBuilder`
   ("Since 2026-10-18 the cache size indicator ...", "until 2026-10-25,
   such a start after ...", "Before, such a start created a new, empty
   ..."), `DatabaseMissingException` ("2026-11-03, bergdb 015-01",
   "2026-11-05, bergdb 015-05", "Before, such a start ..."),
   `DatabaseNotCreatedException` ("2026-10-25", "Before, such a database
   failed every ..."), `DbException` ("2026-10-23, bergdb 005-01; before,
   this comment called every DbException fatal"), `DbFailedException`
   ("2026-11-06, bergdb 019-10"), `SyncLevel` ("Until 2026-11-04 there
   was a third level, STRONG ..."). A grep of the `/** */` comments for
   years and for "since", "before", "until", "no longer" finds them; the
   agent checks each hit.
3. `Time.utc(String)`, `Time.resolve(TimeZone, String)` and
   `Time.resolve(TimeZone, Time, String)` do not document
   `bergdb.pub.util.BadFormatException`, which `TimeResolver` throws for a
   bad time string, nor the `IllegalArgumentException` for a null time
   string (and, for the three-argument `resolve`, a null zone).

Why: from agent d30's read-through of the documentation for release
2026.3 (006-13's progress, 12:44; 165bb9e), not fixed before the release:
006-13, section 5, "For Frans to decide (in the morning)", point 1.
Recommended there: after the release.

Frans, 2026-11-07, 08:00: "For a., do as recommended."

Frans: none. The defaults (KISS, 010-P13):

1. `DataFormatException` says what the other exceptions of the object
   code say: that it belongs to it, and the same "experimental" sentence
   while they have one. If 020 has made the object code part of the
   release by then and the other exceptions have lost the sentence, it
   gets none either, and only says where it is thrown. The `NOTE 1304`
   stays (Frans's note).
2. The history goes; the sentence says what is. A change of behaviour is
   in the release notes (`releases/`), not in the Javadoc. A date that is
   the source of a measured figure (`Database`, "Measured with the default
   settings (2026-10-13, ...)") may stay. Code comments (`//`) are not
   user Javadoc and are left as they are.
3. `@throws BadFormatException` and `@throws IllegalArgumentException` on
   the three methods, with the cases above.

Done when: the three changed; a test that `Time.utc` and both `resolve`s
throw `BadFormatException` for a bad string and `IllegalArgumentException`
for a null one, if no test shows it yet; `java/javadoc-pub.sh` prints
`JAVADOC PUB OK`; `BEFORE COMMIT OK`; a line in `releases/next.md`
(Documentation) if the Javadoc's words change what a user is told.

First step: the grep of item 2 over `java/src/bergdb/pub/`, and
`TimeResolver`'s throws.


Log
---

2026-11-07. Registered by coord-1106 from 006-13's morning list, point 1,
at Frans's word (2026-11-07, 08:00).

2026-11-07. Taken by agent f13 of coord-1107 (006-14).

2026-11-07. Done by agent f13 of coord-1107, with the defaults:

1. `DataFormatException`'s Javadoc says what it is thrown for (a stored
   value that does not fit the Java type or field it is read into, or a
   stored object that cannot be read when its index entries are updated or
   built) and that it belongs to the object code and the user indexes,
   experimental in 2026.3 (bergdb 018-01, D6), as the other exceptions of
   that code say. The `NOTE 1304` stays.
2. The grep of the `/** */` comments of `bergdb.pub` and `bergdb.pub.util`
   for years, "since", "before", "until", "no longer", "was", "now" and
   the like; each hit checked. The history went from `Database` ("Errors
   (2026-11-06, ...)", stop()'s "Until 005-35, ...", "2026-10-27, ...;
   until then the garbage collector ..."), `DatabaseBuilder` (create()'s
   "Until 015-05 this method was dir(String); until 005-66 ...", "Since
   2026-10-18", "until 2026-10-25, such a start ...", "Before, such a start
   created ..."), `CryptoKey.hashCode` ("until 015-45, Object's"),
   `DbException`, `DbFailedException`, `DatabaseMissingException`,
   `DatabaseNotCreatedException` and `SyncLevel` (now: no level for a copy
   elsewhere; one may come with a future replication design). The entry
   IDs stay as references, the dates go. Kept: the dates of measured
   figures (`Database`'s "Measured ... (2026-10-13, ...)",
   `DatabaseBuilder.startupDistanceInMb`'s "measured 2026-10-13"), the
   "experimental in 2026.3" sentences, and the `//` comments.
3. `Time.utc(String)` and both `Time.resolve` have `@throws
   BadFormatException` and `@throws IllegalArgumentException`. On the way:
   `Time.utc(null)` and `Time.resolve(zone, null)` threw a
   `NullPointerException` (`TimeResolver.resolveAbsolute` did not check),
   and `Time.resolve(zone, null, s)` too (`now.units()`); both now throw
   `IllegalArgumentException`, as the three-argument `resolve` did for a
   null string or zone. Test `Time.testResolveThrows`: bad strings give
   `BadFormatException`, nulls `IllegalArgumentException`, for all three
   methods; it fails without the fix (a `NullPointerException`, checked
   with the test compiled against `HEAD`'s `TimeResolver`).

Seen, not changed: `TimeResolver` accepts a month or a day out of range
("2000-13-01", "2013-02-50") and lets the calendar roll it over, on
purpose by its comment in `parseDate` (it allows "overflow" for now); a
candidate for a later entry if a user should be told or refused.

`releases/next.md`: a Pub API bullet (the nulls) and a Documentation
bullet. `JAVADOC PUB OK`. `BEFORE COMMIT OK (120 s)` (2026-11-07, 08:57; 1263 unit
tests, 87 f-tests), on the tree with this entry's and 021-03's changes.
