# 020-11 The known issues of 2026.4

Created 2026-11-09 by Frans Lundberg. Status: open, to be brought up to
date until the release. Every known fault and open question that release
2026.4 ("a bug-free database", 020) must settle, each with its state on
`main`: fixed (the commit and the test that shows it), open (who has it),
gone or not a fault (why), decided or open for Frans (questions). Asked by
Frans on 2026-11-08 at 22:03: "Keep working until you have a solution for
2026.4 with no known issues." Written in night 006-15 from `main` at
`fd6dd09`; brought up to date to `dee3e48` (2026-11-09, about 02:30) and
to `3d8b785` (020-12, step 4's measurements).

How it was checked: each "fixed" by reading the test it names, not the
commit message, and by running it on `main` (`-ea`, the unit group unless
said otherwise): every test named in the tables passed on `main` when its
row was written; at `dee3e48` the unit group as a whole passed (1,415
tests, 46 s), and `javadoc-pub.sh` printed JAVADOC PUB OK. A night test that was not run is said so. The sources:
020-01, section 13 (both tables) and section 12 (N1 to N11); 020-10,
section 8 (the fault map) and 10.2; 020-03's BG1 to BG6 and 020-05's
DB7 as 020-08 takes them; 020-08's tests and steps; 020-09's rules and
section 9; 020-04's and 020-07's questions; the lists of 015, 019 and
021; the night's reviews (coord-1108's state, 006-15).


## 1. In short

On `main` at `3d8b785` every fault of 020-01's, 020-08's and 020-10's
lists is fixed, gone or not a fault, and so is every finding of the
night's reviews (section 6). No known fault of BergDB is open. Open are
an approval, and three additions put after 2026.4 (the tool fault
T-OB was fixed in 621ee0e: `objectbench.sh` compiles ObjectBench for each
build); one known cost is accepted (below):

| Row | What | With |
|---|---|---|
| 020-07 | Frans's approval of the spec's text under 018-01's rule | Frans: a release step |
| L-F6 | DbObject: the String[] (nested path) form for every typed getter | later (B3's review, F6) |
| L-rec | Records as Data Objects (020-02, 5.1b; the coordinator's lean) | later |
| L-key | A key field in a stored object, opt-in (017-07, section 6) | later, on demand |

The night's runs passed (section 9). Closed since the first version:
S4, step 4's measurements (020-12, 3d8b785; 020-08 done);
N10-test, N4-doc, BK-015, BK-020 and BK-020-10 (3fa79d9); R3-F1, R3-N2
and R3-N3 (e92a95a); its review's two low points (c9e6975); N5 and B3
(48378fe, 7b008af); R46-L1 and R46-L2 (25978bc), and the assert that
25978bc added (dee3e48).

A known cost, accepted, not a fault:

| Row | What | State |
|---|---|---|
| C-M8 | A `w()` of one String or byte[] put at an object key: 2.6 µs, not 2.3 | accepted for 2026.4 |

C-M8 is 13 % (020-12, M8; a `.txt` key and 100 puts in one `w()` are as
before): the cost of 020-10, section 5.1's rule (I1, 249b684: the read
time fixed first, the directory's hash in the read set, the index
manager's lock), which fixes 015-28, 015-43 and 015-46 for every write at
an object key. Accepted under Frans's delegation of 22:17 for 2026.4. A
later reduction is possible, such as a lock-free read of an immutable
snapshot of the index set for directories without an index: Frans's to
decide.

For Frans to read: the decisions taken under his delegation (020-04 Q6;
020-07 Q2 to Q5; 020-09's 24; 020-10's 22; C-M8; and the night's others,
each in its commit and in 006-15).


## 2. Objects: F1, F2 (020-01) and 020-08

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 015-46, S2-F3 | String or byte[] over an object, indexed | fixed | 249b684; PubTesterIndexRaces.testStringOverObject |
| S2-F8 | An array holding itself: StackOverflowError | fixed | ca67411; DataObjectsTester K7, K9, W26 |
| S2-F9 | A final field not stored, silently | fixed, refused | ca67411; DataObjectsTester.testClassCases1, K6 |
| S2-F18 | Date, enum, collection, DbObject lost | fixed, refused | ca67411, 7681710; K7, K8, testReviewOfStep8 |
| S2-F19 | A field hiding a superclass's | fixed, refused | ca67411; testClassCases1, K10 |
| S2-F4 | A double into a String: "d:1.5" | fixed | ca67411; DataObjectsTester.testGetTable G40 to G44 |
| S2-F5 | The double 2^63 into a long gives MAX | not a fault | the rule: 020-09, 5.4 (delegated); G29, G30 |
| S2-F6 | Another kind into a primitive: 0 or a Bug | fixed | 8185c07, ca67411; testGetTable, testTableReference |
| S2-F7 | An Object[] or Object field read as null | fixed, refused | ca67411; K7, K9 |
| S2-F21 | A throwing constructor: a Bug, a second call | fixed | ca67411; DataObjectsTester.testConstructors, G121 |
| 005-22 | A get threw DataFormatException on overflow | changed | ca67411: clamped by 020-09; G27, G31 to G33 |
| BG1 | Typed nulls stored | fixed | 8185c07; DbObjectTester.testNullFieldsAbsent, W20 |
| BG2 | A null over a default read as null | fixed | 8185c07, ca67411; W21 |
| BG3 | A String into an int: 0, silently | fixed | ca67411; G54 to G65, G82; unparsable text is 0 by G61 |
| BG4 | Null elements stored; Object[] lost | fixed | 8185c07; DbObjectTester.testNullElementsRefused, W15 to W18 |
| BG5 | The null object 626572676f01ffff | fixed | 8185c07; DbObjectFormatTester.testNullAtTheTop, W28 |
| BG6 | Three index behaviours for null | fixed | 8185c07, 9a22bd6; PubTester.testOneIndexRule |
| DB7 | Raw double bits, NaN payloads, kept | fixed | 8185c07; DbObjectFormatTester.testDoubles |
| N1 | A null String fails every start | fixed | 8185c07; PubTesterIndexJobs.testBuildOverAnObjectItCannotIndex |
| N2 | User data gives an Error in rw() | fixed | S2-F6, F8, F21, F26 gone; 7681710; e92a95a (R3-N3) |
| N4 | The kind of a value is not stored | partly | 8185c07 (0x82 and the full check; the guess documented) |
| N4-doc | Put Javadoc silent on objects at suffixed keys | fixed | 020-11's rows; ObjectKeysTester |
| T1, H0 | The vectors; a reference codec; mutants | done | 9a45e06; ObjectFormatTester, 7 tests; night not run |
| T2 to T7 | The vectors by DbObject; refusals; integers; sizes | done | 8185c07; DbObjectFormatTester, 15 tests |
| T8 | Format-1 objects and definitions refused | done | 38afb1a; PubTester.testFormat1ObjectRefused and 2 more |
| T9 | "A String value is never an object" | fixed | e92a95a (R3-F1); PubTester.testStringThatStartsAsFormat1 |
| T10 | A long index over one integer | done | 8185c07; PubTester.testLongIndexOverOneInteger |
| T11, H1 | 020-09's G1-G122, K1-K18, W1-W36 | done | ca67411; DataObjectsTester, all 176 IDs; night not run |
| 020-04 N1-N14 | The no-null tests | done | N1 to N14 as planned under (c); N2, N6 to N8 were (d)'s, not made |
| Step 7 | `put(Object)`, the key field, `PubUtil` gone | done | 80bc546; PubTester.testKeyIsAnOrdinaryField |
| Step 6 | The objects' Javadoc and words | done | 9a22bd6 (JAVADOC PUB OK in its gate) |
| Step 5 | (d)'s constructor check | dropped | Frans chose (c), 2026-11-08, 21:47 |

Tonight's reviews of the objects' steps:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| R2-1 | Step 2 lost 019-42's restart test | fixed | 38afb1a; testBuildOverAnObjectItCannotIndex |
| R2-2 | R15 sizes give Errors | fixed | 38afb1a, e92a95a; DbObjectFormatTester.testSizesRefused |
| R2-3 | DbString's UTF-8 field: a data race | fixed | 38afb1a; testValueClassesClosed |
| R2-4 | DbValue's public constructor; DbObject not final | fixed | 38afb1a; testValueClassesClosed |
| R2-5 | A cycle's message with an empty place | fixed | 38afb1a; testCyclePlaces |
| R8-1 | A Number subclass stored as an integer | fixed | 7681710; DataObjectsTester.testReviewOfStep8 |
| R8-2 | A failed static init fails the DB in rw() | fixed | 7681710; testReviewOfStep8, BadInit three times |
| R8-3 | An assert on a null scan value | fixed | 5b08db5; PubTesterIndexJobs.testScanTypes |
| R8-4 | V5 lets a subclass of Date through | fixed | 7681710; testReviewOfStep8 |
| R8-5 | V9 takes a bounded type variable | fixed | 7681710; testReviewOfStep8 |
| R8-6 | Scans do not check the class first | fixed | 7681710, 5b08db5; testReviewOfStep8, testScanTypes |
| R8-7 | void.class gives a NullPointerException | fixed | 7681710; testReviewOfStep8 |
| R3-F1 | A String "bergo"+U+0001 taken for format 1 | fixed | e92a95a; PubTester.testStringThatStartsAsFormat1 |
| R3-N2 | `Entries.suffix`: ukey "/d/.h" none, ikey "h" | fixed | e92a95a: "h" for both; testSuffixOfANameThat... |
| R3-N3 | DbString encodes, then checks the size | fixed | e92a95a; testStringValueCountedFirst; night: Huge |
| R3-x | A bytes field into a String field repairs | not a fault | 020-09, 5.6 (delegated); not 021-06's rule |
| R4-1 | A long String: the encoder allocates 2 or 3 a char | fixed | c9e6975; StringUtil.testToBytesOfAKnownSize |
| R4-2 | A format-1 previous value blocks its key | fixed | c9e6975; testFormat1ObjectRefused, testFormat1InIndexed... |
| B3 | DbObject and its value classes into bergdb.pub | done | 48378fe; JAVADOC PUB OK; DbByteArray.testImmutable |
| B3-F1 | A put of a DbObject kept the caller's array | fixed | 7b008af; PubTester.testDbObjectPutStoresACopy |
| B3-F2 | A class in bergdb.pub could extend DbValue | fixed | 7b008af; DbObjectFormatTester.testPackagesSealed |
| B3-F2b | A user's DbObject put unchecked | fixed | 7b008af; DbObject.testPutChecksTheBytes |
| B3-F3 | The release notes and ReleaseDemo without DbObject | fixed | 6514764 (ReleaseDemo, in build.sh), d2de9af |
| B3-F4 | The Builders not final | fixed | 7b008af; DbObjectFormatTester.testValueClassesClosed |
| B3-F5 | build()'s limit; name parts checked after lookups | fixed | 7b008af; DbObject.testNamePartsCheckedFirst |
| B3-F6 | The String[] form for every typed getter | later | an addition, not a fault (section 1, L-F6) |

R4-1 and R4-2 are the review of e92a95a's two low points (section 6): a
String of 2^30 chars or more, whose UTF-8 fits, now encoded into an array
of its exact size (`PubTester.testLargeStringThatFits`, a night test, 1
GiB); and a previous value of format 1 has no entries, so a put over it
and a delete of it work in an indexed directory, also for a String whose
bytes are a whole format-1 structure; the refusal stays for a byte[]
put's new value and for a build.

R3-F1 in detail (the review of 38afb1a, probed at `c126d7d`): a String
value whose text starts with "bergo" and U+0001, at an object key, made
`get(key, Object.class)` throw `ObjectCreationException` "format-1";
`usePrimary(String.class)` left it out; `usePrimary(Object.class)` and a
class threw at it; in a directory with an index, a put of it was refused
(`w()` and `rw()`), a build over it failed, and a put over it or a delete
of it was refused. Fixed in e92a95a (decided under the delegation: a
String put is never format 1; format 1 is told by its structure, its
field count and a field table that fits, not by 6 bytes; the guess is in
`Connection.get`'s Javadoc): `PubTester.testStringThatStartsAsFormat1`
puts such a String and checks the gets, the scans of each type, the
puts, the delete and the index; `ObjectFormatTester.testIsFormat1` and
`Entries.testIsFormat1Object` the structure.


## 3. Indexes: F3 to F8 (020-01) and 020-10, section 8

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| S2-F1 | An ICU collator shared by threads | gone | 5b08db5, 41ea870: no collator; H2's 4 writers: night only |
| S2-F10 | No start without ICU | gone | 41ea870; build.sh refuses ICU in the release jar |
| S2-F14 | A level's commas lost | fixed | 7aca256; IndexDefinitionTester.testRoundTrip |
| S2-F15 | An empty nested part | fixed | 5b08db5; PubTesterIndexJobs.testNestedFieldEmptyPart |
| S2-F20 | dir() twice | fixed | 5b08db5; PubTesterIndexJobs.testDirTwice |
| S2-F26 | A null indexed String throws or stops a build | fixed | 8185c07, 5b08db5; PubTester.testOneIndexRule |
| N9 | ICU's sort keys in the stream | gone | 41ea870; a start refuses /#i/dii/ |
| 015-28 | A write racing a creation | fixed | 249b684; PubTesterIndexRaces.testRacesCreate |
| 015-43 | The index set read before R | fixed | 249b684; testRacesCreate, Activate, Delete |
| S2-F12 | An old entry in a new index of the name | fixed | 249b684, 5b08db5; testRacesDelete; H2 (fd6dd09) |
| 015-23 | A refused deletion stops maintenance | fixed | 5b08db5; IndexJobsHarness.testDeletionRefused |
| 015-29 | deleteIndex(PRIMARY) | gone | 5b08db5, 8be9a95: PRIMARY gone; testIndexNamedPrimary |
| 015-30 | A build reads past its directory | fixed | 5b08db5; PubTesterIndexJobs.testBuildStopsAtDir |
| 015-36 | An interrupted deletion | gone | 5b08db5: no deletion job; testDeleteWithInterruptFlag |
| 015-37, N6 | An interrupt ends a build | fixed | cecaf4c (019-38); testInterruptInBuildIsNotAFailure |
| 015-39 | A status that changes after it is read | fixed | 5b08db5; PubTesterIndexJobs.testStatusIsSnapshot |
| 015-61 | A stopped deletion says done | gone | 5b08db5: no job; testStartResumesBuildsAndCleanups |
| 019-40 C5 | A deletion done after a failure | gone | as 015-61; testBugInCleanupLeavesTheMarker |
| S2-F11 | Done when the database stopped | fixed | 5b08db5, 57f88ea; IndexJobsHarness.testStopDuringBuild |
| S2-F16 | A build indexes subdirectories | fixed | 5b08db5; testBuildStopsAtDir |
| S2-F27 | A refused creation stays in memory | fixed | 5b08db5, 57f88ea; IndexJobsHarness.testCreationRefused |
| N7 | A step refused for good, retried | fixed | 5b08db5: 4,096 bytes of levels; testLargeValueNoEntry |
| N10 | A pause without its cap | fixed | 5b08db5; IndexBuilderImp.testPauseCapped, in Pack since 020-11's rows |
| S2-F2 | inclusive(false) alone | fixed | 8be9a95: gone; PubTesterIndex.testExclusiveBounds; H2 |
| S2-F13 | prefix() on a secondary index | fixed | 8be9a95; PubTesterIndex.testPrefix; H2 |
| S2-F22 | A later level alone | fixed | 8be9a95; PubTesterIndex.testGrammar; H2 |
| S2-F23 | hasNext() true, next() throws | fixed | 8be9a95; PubTesterIndex.testStaleLastEntries |
| N3 | A scan changes transactionInfo() | fixed | 8be9a95; PubTesterIndex.testScanKeepsTransactionInfo |
| S2-F17 | The primary scan without dir() | fixed | ae68938; PubTesterPrimary.testPrimaryNeedsDir; H4 |
| S2-F25 | String.class gives objects | fixed | ae68938; PubTesterPrimary.testTypesListByKind |
| N5 | The API's boundary a convention | fixed | c88e5fa, 9a9e920, 41ea870, 2917cdb, 48378fe, 7b008af (sealed) |
| N11 | Key replace in an entry's level bytes | fixed | 5b08db5; PubTesterIndexJobs.testKeyReplaceIndexedText |
| N8 | No scans in rw() | not a fault | decided (020-01, 14.1) |
| "/" build | A build over "/" failed since 021-06 | fixed | 5b08db5; testBuildStopsAtDir, index "root" |

Tonight's reviews and harnesses of the index steps:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| I2-join | join() in another thread gave BUILDING | fixed | ab06e26; PubTesterIndexJobs.testJoinFromAnotherThread |
| I2-Error | An Error after a definition's commit | fixed | ab06e26; testErrorInDefinitionChangeFailsTheDatabase |
| H3-F1 | An Error in a creation: the DB runs on | fixed | ab06e26; IndexJobsHarness.testEveryPointAndFault |
| H3-F2 | A throw after a commit: stream and memory apart | fixed | ab06e26; as H3-F1 (KNOWN empty) |
| H3-F3 | A throw after an activation's commit | fixed | ab06e26; as H3-F1 |
| I1-starve | A build never ends under hot writes | fixed | ab06e26; PubTesterIndexJobs.testBuildEndsUnderWriters |
| H2 | Harness H2 against BergDB | runs | fd6dd09, c25808e (night: 8 seeds, 6 min); IndexHarness, 8 tests |
| H3 | Harness H3, the jobs under faults | runs | 57f88ea, ab06e26; IndexJobsHarness; night not run |
| H4 | Harness H4, the primary scan | runs | ae68938; PrimaryHarness.testSeeds; night not run |

Notes:

* N10's test was the only index test with `@Nano` outside `pubimp/Pack`,
  so it did not run in `before-commit.sh`; `IndexBuilderImp.class` is in
  `Pack` since "020-11, the open rows".
* 020-10, section 8, named `testRaceWriteCreate` and
  `testRaceSetBeforeReadTime`, which do not exist; it names
  `PubTesterIndexRaces.testRacesCreate`, `testRacesActivate` and
  `testRacesDelete` (36 forced orders) since "020-11, the open rows".
  `testSubdirNotIndexed` tests the writers; S2-F16's build is
  `testBuildStopsAtDir`.
* `level2.sh` ran on `5b08db5` (I2): LEVEL 2 OK.


## 4. Questions

| ID | Question | State |
|---|---|---|
| 020-01 4.5 | F1's questions of meaning (Q1 to Q6) | decided: 020-02, 4 and 5.1b; 020-09 |
| 020-01 5.5 | F2's questions of meaning (Q1 to Q4) | decided: 020-09 (21:47 to 21:59) |
| 020-04 Q1 | A put of a null field | decided: (c), Frans 21:47 |
| 020-04 Q2 | No constructor; a throwing one | decided: 020-09, V2 and 5.2 |
| 020-04 Q3 | A 2026.3 object with a null | decided: every format-1 object refused (17:06) |
| 020-04 Q4 | The version byte | decided: header 0x82 (16:22) |
| 020-04 Q5 | The Builder with null | decided: refused (021-07) |
| 020-04 Q6 | `DbObject.getString` of an absent field | decided (delegation): null, 0, false; has() tells |
| 020-07 Q1 | Is a scalar a level | decided: containers only (19:43) |
| 020-07 Q2 | Lookups without the full check | decided (delegation): 7.4 stays; Java checks every read |
| 020-07 Q3 | The Binson conversion normative | decided (delegation): normative for a converter |
| 020-07 Q4 | Top-level wrapping in "array" or "p" | decided (delegation): the API's convention |
| 020-07 Q5 | Later formats get a new header byte | decided (delegation): as written |
| 020-07 Q6 | The spec's and vectors' home | decided: vectors in java/ (9a45e06); 020-07 frozen |
| 020-07 Q7 | '.' and ',' in names and index paths | settled by 020-10 (nestedField parts) |
| 020-07 | The spec's approval under 018-01's rule | open for Frans before the release |
| 020-09, 9 | Questions for Frans | none; 24 decisions under the delegation, to read |
| 020-10, 11 | Decisions under the delegation | 22, to read |


## 5. The Core, and the lists of 015, 019 and 021

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 019-46 | A drop raced the writer's load | fixed | 68830b8; NodeCollection.testDropIfEmptyKeepsTheWritersObject |
| 019-47 | A start kept a large value | fixed | c126d7d; Eviction.testStartAdmitsLargeValuesOfThe... |
| R46-L1 | The writer could call dropIfEmpty itself | fixed | 25978bc; testWriterKeepsTheNodeWhateverItsPolicy |
| R46-L2 | Handle and 009-02 words on DEAD | fixed | 25978bc (words; 009-02 and Handle's Javadoc) |
| R46-L3 | 25978bc's assert fired, legal schedule | fixed | dee3e48; NodeCollection.testWriterDuringADropsDeadWindow |
| B2-R1 | bergdb.dev.Run could not start a non-public main | fixed | 3483a62; Run.testRunsMainOfAClassThatIsNotPublic |
| B2-R2 | Reflection through pubimp's classes fails | not a fault | 2917cdb's narrowing; in the release notes |
| 021-06 | Ill-formed UTF-8 read: keys and String values | fixed | d65f5b5, 3cf464e; Utf8ReadTester, 3 tests |
| 021-09 | udir2idir took "p/" and "/p//" | fixed | 913ffb4; PubKeys.testUdir2idirRefusesBadDirs |
| 021-10 | A '.' in a directory: no object key there | fixed | 38afb1a; Entries.testSuffixOfTheLastPart |
| 021 | The list | no open entry | items/021-todo/readme.md |
| 019 | The list | no open entry | items/019-todo/readme.md; 019-45 a limit, documented |
| BK-015 | 015-23, 28 to 30, 36, 37, 39, 43, 46, 49 said open | done | closed by 020-11's rows, each with its test |
| 015-03 | Lean follows 005-79's integer take | not 2026.4's | the Core's Lean model; no fault |
| 015-18 | night.sh large on a release | not 2026.4's | not tonight (Frans, 22:12) |
| 015-84 | Cap the pace's factor S/sd | not 2026.4's | an investigation of the Core's startup pace; no fault |


## 6. Night of 8 to 9 November: the reviews

Each step of the night had an independent review, read-only, by an agent
that had not written it, in a clone of its own, before or soon after it
reached `main`; each finding went to the step's agent, and its fix landed
with a test that failed before (coord-1108's state; 006-15).

* Objects, step 2 (8185c07): the bytes, the reader, the lookups. No fault
  there; five findings: 019-42's restart test lost, R15's sizes giving
  Errors, a data race on DbString's UTF-8, DbValue's public constructor
  and DbObject not final, a cycle's message. Fixed in 38afb1a (R2-1 to
  R2-5).
* Objects, step 8 (ca67411, DataObjects): the get table against 2,000,000
  random values, sound; seven findings (a Number subclass, a failed
  static initializer in `rw()`, a scan's assert, V5, V9, the scans'
  class check, `void.class`). Fixed in 7681710 and 5b08db5 (R8-1 to R8-7).
* Objects, steps 3 and 7 and 021-06's second half (38afb1a, 80bc546,
  3cf464e): format 1 refused everywhere, the key field gone, String reads.
  One fault, R3-F1 (a String that starts as format 1), and two notes
  (R3-N2, R3-N3). Fixed in e92a95a.
* The fix of R3-F1 (e92a95a): 2,816 of 2,816 real 2026.3 objects
  recognised, 2,000,000 hostile inputs without an exception, no format-2
  value taken for format 1, the cost linear and bounded. Two low points
  (R4-1, R4-2). Fixed in c9e6975.
* B3 (48378fe, `DbObject` in `bergdb.pub`): sound otherwise; F1 (medium,
  a put kept the caller's array, so a later change of it changed the
  committed value in memory), F2 (sealing; user DbObjects unchecked), F3
  (release notes, ReleaseDemo), F4 (final Builders), F5 (Javadoc, name
  parts), F6 (an addition for later). Fixed in 7b008af, 6514764, d2de9af.
* I1 (249b684, maintenance): 8.4 million writes, sound; one liveness
  fault in I2's build, starving under hot writes. Fixed in ab06e26.
* I2 part 1 (5b08db5, layout, jobs, API): 816 crash images, 60 stops, 30
  seeds, sound; `Job.join()` from another thread could return BUILDING; an
  Error after a definition's commit left memory and stream apart. Fixed in
  ab06e26, with harness H3's H3-F1 to H3-F3 (57f88ea; 9 planted faults
  found).
* I3 (8be9a95, the scan builder): 8,000 scans, 1,064,112 results equal to
  a reference. No fault.
* P1 and I0 (ae68938, 7aca256): no findings; a note for I1 (the entry
  function given no value) and a coverage note for the objects' steps.
* B1 (c88e5fa, the release jar): no fault; two notes for B2 (the ICU
  prefix, ICU's license), both gone with ICU (41ea870).
* B2 part 2 (2917cdb, the narrowing): sound; `bergdb.dev.Run` could not
  start a main that is no longer public (fixed in 3483a62); reflection
  through pubimp's classes now fails (in the release notes, d2de9af).
* 021-06 and 021-09 (d65f5b5, 913ffb4): a printer of keys in KeyNode
  that decoded with U+FFFD, fixed in 39fb346.
* 019-46 and 019-47 (68830b8, c126d7d, Core): both fixes correct (260,000
  jcstress-like rounds, 1,100 seeds, 1,477 starts); two low points
  (R46-L1, R46-L2), fixed in 25978bc. Its follow-up review of 25978bc:
  the code right, but its new assert could fire on a legal schedule with
  `-ea` (R46-L3), fixed in dee3e48 with a forced-schedule test.
* The first audit of this item (843e2f1): the open rows above, closed in
  3fa79d9, d39b3ed and the fixes listed.

The Core's two faults of the night were found outside these reviews:
019-46 by a gate on a loaded machine (an INV-SLOT), reproduced with a
widened window and fixed; 019-47 while 019-46 was reproduced.


## 7. Items and words

* BK-015, done: the entries of 015 that 020's steps fixed (015-23, 28,
  29, 30, 36, 37, 39, 43, 46, 49) are closed, each with its commit and
  test, and their rows moved in 015's readme.
* BK-020, done: 020-04, section 8, and 020-07, section 14, record each
  question's decision.
* BK-020-10, done: section 8's race test names (section 3, notes).
* N4-doc, done: the put Javadoc of `WBuilder`, `RwEnvironment` and
  `Connection` says that an object is put only at an object key and is
  refused elsewhere ("Bad key"), and the package page's Objects section
  what a suffix is (the name's last '.'; a directory's '.' is not one;
  ".h" has "h", as e92a95a settles `Entries.suffix` for ukeys and ikeys
  alike); `ObjectKeysTester.testObjectKeysOfThePutJavadoc` pins its
  examples in `w()` and `rw()`.


## 8. Measured and checked

* 020-08, step 4, done (020-12, 3d8b785): format 2 against format 1 on a
  quiet F53, M1 to M8, every figure as fast or faster but M8 (C-M8,
  section 1); `performance.sh ab` (quick) against release 2026.3: NO
  ALERTS. The tool fault T-OB is fixed (621ee0e).
* The level scripts after the last Core changes: `level4.sh` ran on
  019-46, 019-47 and 25978bc (LEVEL 4 OK); `level2.sh` on I2 and on the
  final `main` (LEVEL 2 OK); dee3e48 changed only an assert and added a
  test.


## 9. The night's runs (the coordinator's rows)

| Run | On | Result |
|---|---|---|
| Night tests (the night group) | c25808e | SUCCESS, 24 tests in 1,332 s |
| `night.sh` | 48378fe | NIGHT OK, 65 minutes (java/build/night/2026-11-09-0158/report.txt) |
| Night tests | 7231771 | SUCCESS, 26 tests in 1,262 s |
| `level2.sh` | 7231771 | LEVEL 2 OK |
| Step 4's quiet runs | 7231771 | 020-12: M1 to M8; `performance.sh ab`: NO ALERTS |

`night.sh` ran `before-commit.sh`, the core-build check, `level1.sh` to
`level4.sh`, the Lean tests, 25 night tests and the conformance set
(medium). The night tests on 7231771 are the night group of the final
`main`, 26 tests.


## 10. Log

2026-11-09. Written in night 006-15 from `main` at `fd6dd09`, at the
coordinator's request (Frans's 22:03), by the night's agent of 019-46 and
two read-only helpers: every "fixed" row's test read and run; the unit
group passed (1,399 tests). To be brought up to date when the night's last
fixes land.

2026-11-09. The open rows that were nobody's closed ("020-11, the open
rows"): N10's test in `Pack`; N4's put Javadoc, with a test; 015's ten
entries closed; 020-10's race test names; 020-04's Q2 to Q6 and 020-07's
Q2 to Q7 recorded as decided, Q6 of 020-04 and Q2 to Q5 of 020-07 under
Frans's delegation of 22:17, as recommended. Left for Frans: 020-07's
approval.

2026-11-09. R3-F1, R3-N2 and R3-N3 fixed on `main` in e92a95a (the
objects agent): their rows, N2's, R2-2's and T9's brought up to date;
the tests read and run.

2026-11-09, about 02:30. Brought up to date to `dee3e48` at the
coordinator's request: c25808e, e92a95a, c9e6975, 48378fe, 7b008af,
6514764, 3483a62, 25978bc, dee3e48, 2917cdb's review and the release
notes (d2de9af); each named test read and run, the unit group passed
(1,415 tests), JAVADOC PUB OK. No known fault open; open are step 4's
measurements, Frans's approval of 020-07, and three additions for later.
A section on the night's reviews (6); the night's runs left for the
coordinator (9).

2026-11-09, morning. Brought up to date to `3d8b785`: S4 closed (020-12;
020-08 done); C-M8, a known cost accepted under the delegation; T-OB, the
tool fault of `objectbench.sh` since B3, open with another agent; the
night's runs (section 9): `night.sh` NIGHT OK on 48378fe, the night tests
and `level2.sh` on 7231771.

2026-11-09, 04:36. T-OB fixed in 621ee0e (objectbench.sh compiles
ObjectBench for each build); its open row removed (coordinator).

2026-11-09, 05:40. `night.sh` on the final commit d6e8989: NIGHT OK
(63 minutes; levels 1 to 4, the Lean tests, 26 night tests, conformance
medium; java/build/night/2026-11-09-0436/report.txt) (coordinator).
