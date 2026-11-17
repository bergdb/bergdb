# 020-11 The known issues of 2026.4

Created 2026-11-09 by Frans Lundberg. Status: open, to be brought up to
date until the release. Every known fault and open question that release
2026.4 ("a bug-free database", 020) must settle, each with its state on
`main`: fixed (the commit and the test that shows it), open (who has it),
gone or not a fault (why), decided or open for Frans (questions). Asked by
Frans on 2026-11-08 at 22:03: "Keep working until you have a solution for
2026.4 with no known issues." Written in night 006-15 from `main` at
`b768ef0`; brought up to date to `4eaa97a` (2026-11-09, about 02:30), to
`01d2187` (020-12, step 4's measurements), and to `73dda0a` with the day's
document update (2026-11-09, afternoon): the faults that the day's bug
hunts found and fixed (section 10) and what they left for a later release
(section 11); and to `d00096e` by the evening's items pass: 021-13 to
021-27, Codex's round 3 and the late fixes (section 10, "Since 73dda0a"),
and the day's open questions and API wishes (section 11).

How it was checked: each "fixed" by reading the test it names, not the
commit message, and by running it on `main` (`-ea`, the unit group unless
said otherwise): every test named in the tables passed on `main` when its
row was written; at `4eaa97a` the unit group as a whole passed (1,415
tests, 46 s), and `javadoc-pub.sh` printed JAVADOC PUB OK. A night test that was not run is said so. The sources:
020-01, section 13 (both tables) and section 12 (N1 to N11); 020-10,
section 8 (the fault map) and 10.2; 020-03's BG1 to BG6 and 020-05's
DB7 as 020-08 takes them; 020-08's tests and steps; 020-09's rules and
section 9; 020-04's and 020-07's questions; the lists of 015, 019 and
021; the night's reviews (coord-1108's state, 006-15).


## 1. In short

On `main` at `01d2187` every fault of 020-01's, 020-08's and 020-10's
lists is fixed, gone or not a fault, and so is every finding of the
night's reviews (section 6). No known fault of BergDB is open. Open are
an approval, and three additions put after 2026.4 (the tool fault
T-OB was fixed in 00a8277: `objectbench.sh` compiles ObjectBench for each
build); one known cost is accepted (below):

| Row | What | With |
|---|---|---|
| 020-07 | Frans's approval of the spec's text under 018-01's rule | approved 2026-11-09, 07:33 |
| L-F6 | DbObject: the String[] (nested path) form for every typed getter | later (B3's review, F6) |
| L-rec | Records as Data Objects (020-02, 5.1b; the coordinator's lean) | later |
| L-key | A key field in a stored object, opt-in (017-07, section 6) | later, on demand |

The night's runs passed (section 9). Closed since the first version:
S4, step 4's measurements (020-12, 01d2187; 020-08 done);
N10-test, N4-doc, BK-015, BK-020 and BK-020-10 (16736f0); R3-F1, R3-N2
and R3-N3 (02995d9); its review's two low points (4ff57b6); N5 and B3
(fcc151b, 5e14229); R46-L1 and R46-L2 (a182faa), and the assert that
a182faa added (4eaa97a).

A known cost, accepted, not a fault:

| Row | What | State |
|---|---|---|
| C-M8 | A `w()` of one String or byte[] put at an object key: 2.6 µs, not 2.3 | accepted by Frans |

C-M8 is 13 % (020-12, M8; a `.txt` key and 100 puts in one `w()` are as
before): the cost of 020-10, section 5.1's rule (I1, 4a6deee: the read
time fixed first, the directory's hash in the read set, the index
manager's lock), which fixes 015-28, 015-43 and 015-46 for every write at
an object key. Accepted under Frans's delegation of 22:17 for 2026.4, and
by Frans on 2026-11-09, 07:18 ("Yes"): the time does not concern him, the
coupling does (that the index layer sees every write at an object key, of
any value), which 017-09 studies for a later release. A later reduction of
the time is possible, such as a lock-free read of an immutable snapshot of
the index set for directories without an index; not planned.

For Frans to read: the decisions taken under his delegation (020-04 Q6;
020-07 Q2 to Q5; 020-09's 24; 020-10's 22; C-M8; and the night's others,
each in its commit and in 006-15).

The bug hunts of 9 November (020-13 to 020-23, 021-11, 021-12) found
faults in 2026.4's new code and in older code, all now fixed on `main` at
`73dda0a` and in this update, each with a test (section 10): high, X1
(key replace in an object key's directory left an index wrong) and X2
(with 020-13's bug 2: an `Error` of a Data Object class's static
initializer failed the database in `rw()`); medium, X3, Y1, J8 and
020-18's F1, F3, F4 and F5 (a build that stalled writes or never ended, a
cleanup of square cost); the rest low, or not graded (020-13's bugs,
021-11, 021-12). No known fault is open. What the hunts left is for
a later release, none a broken promise of 2026.4 (section 11): O16-1,
fine as is for 2026.4 (Frans, 11:52); 020-18's observations O1 to O3;
020-15's coverage gaps; 020-22's writes through the Core that stay
undefined; and test gaps.

Since `73dda0a`, to `d00096e` (section 10, "Since 73dda0a"): the faults
that the new users' applications (020-24), the C port and its black-box
users (022, 022-06) and the reviews (020-23, Codex's rounds 3 and 4)
found, 021-13 to 021-24, 021-26 and Z1 to Z3, are fixed, or documented
where the behaviour is meant, each with a test; several were graded high
by their finders, most are older than 2026.4 (021-13, 021-16 and Z1 among
them; 021-26 and Z2 were never released). Two are not fixed, each for
Frans: 021-25, reclaim stops cutting a FIFO of keys in time order (in
2026.3 too; a known issue in `releases/next.md`, "Known issues and
limits"; its fix (c) ended the slowdown of puts that came with it), and
021-27, the Core's `Db.getTrans` at a position inside a record fails the
database (as its Javadoc says; a test keeps it). The day's open questions
and API wishes are in section 11, each for a later release or for Frans.


## 2. Objects: F1, F2 (020-01) and 020-08

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 015-46, S2-F3 | String or byte[] over an object, indexed | fixed | 4a6deee; PubTesterIndexRaces.testStringOverObject |
| S2-F8 | An array holding itself: StackOverflowError | fixed | 2ca4610; DataObjectsTester K7, K9, W26 |
| S2-F9 | A final field not stored, silently | fixed, refused | 2ca4610; DataObjectsTester.testClassCases1, K6 |
| S2-F18 | Date, enum, collection, DbObject lost | fixed, refused | 2ca4610, 7681710; K7, K8, testReviewOfStep8 |
| S2-F19 | A field hiding a superclass's | fixed, refused | 2ca4610; testClassCases1, K10 |
| S2-F4 | A double into a String: "d:1.5" | fixed | 2ca4610; DataObjectsTester.testGetTable G40 to G44 |
| S2-F5 | The double 2^63 into a long gives MAX | not a fault | the rule: 020-09, 5.4 (delegated); G29, G30 |
| S2-F6 | Another kind into a primitive: 0 or a Bug | fixed | 01e19c4, 2ca4610; testGetTable, testTableReference |
| S2-F7 | An Object[] or Object field read as null | fixed, refused | 2ca4610; K7, K9 |
| S2-F21 | A throwing constructor: a Bug, a second call | fixed | 2ca4610; DataObjectsTester.testConstructors, G121 |
| 005-22 | A get threw DataFormatException on overflow | changed | 2ca4610: clamped by 020-09; G27, G31 to G33 |
| BG1 | Typed nulls stored | fixed | 01e19c4; DbObjectTester.testNullFieldsAbsent, W20 |
| BG2 | A null over a default read as null | fixed | 01e19c4, 2ca4610; W21 |
| BG3 | A String into an int: 0, silently | fixed | 2ca4610; G54 to G65, G82; unparsable text is 0 by G61 |
| BG4 | Null elements stored; Object[] lost | fixed | 01e19c4; DbObjectTester.testNullElementsRefused, W15 to W18 |
| BG5 | The null object 626572676f01ffff | fixed | 01e19c4; DbObjectFormatTester.testNullAtTheTop, W28 |
| BG6 | Three index behaviours for null | fixed | 01e19c4, ee61d84; PubTester.testOneIndexRule |
| DB7 | Raw double bits, NaN payloads, kept | fixed | 01e19c4; DbObjectFormatTester.testDoubles |
| N1 | A null String fails every start | fixed | 01e19c4; PubTesterIndexJobs.testBuildOverAnObjectItCannotIndex |
| N2 | User data gives an Error in rw() | fixed | S2-F6, F8, F21, F26 gone; 7681710; 02995d9 (R3-N3) |
| N4 | The kind of a value is not stored | partly | 01e19c4 (0x82 and the full check; the guess documented) |
| N4-doc | Put Javadoc silent on objects at suffixed keys | fixed | 020-11's rows; ObjectKeysTester |
| T1, H0 | The vectors; a reference codec; mutants | done | 41cb0ba; ObjectFormatTester, 7 tests; night not run |
| T2 to T7 | The vectors by DbObject; refusals; integers; sizes | done | 01e19c4; DbObjectFormatTester, 15 tests |
| T8 | Format-1 objects and definitions refused | done | 577e867; PubTester.testFormat1ObjectRefused and 2 more |
| T9 | "A String value is never an object" | fixed | 02995d9 (R3-F1); PubTester.testStringThatStartsAsFormat1 |
| T10 | A long index over one integer | done | 01e19c4; PubTester.testLongIndexOverOneInteger |
| T11, H1 | 020-09's G1-G122, K1-K18, W1-W36 | done | 2ca4610; DataObjectsTester, all 176 IDs; night not run |
| 020-04 N1-N14 | The no-null tests | done | N1 to N14 as planned under (c); N2, N6 to N8 were (d)'s, not made |
| Step 7 | `put(Object)`, the key field, `PubUtil` gone | done | e4620c3; PubTester.testKeyIsAnOrdinaryField |
| Step 6 | The objects' Javadoc and words | done | ee61d84 (JAVADOC PUB OK in its gate) |
| Step 5 | (d)'s constructor check | dropped | Frans chose (c), 2026-11-08, 21:47 |

Tonight's reviews of the objects' steps:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| R2-1 | Step 2 lost 019-42's restart test | fixed | 577e867; testBuildOverAnObjectItCannotIndex |
| R2-2 | R15 sizes give Errors | fixed | 577e867, 02995d9; DbObjectFormatTester.testSizesRefused |
| R2-3 | DbString's UTF-8 field: a data race | fixed | 577e867; testValueClassesClosed |
| R2-4 | DbValue's public constructor; DbObject not final | fixed | 577e867; testValueClassesClosed |
| R2-5 | A cycle's message with an empty place | fixed | 577e867; testCyclePlaces |
| R8-1 | A Number subclass stored as an integer | fixed | 7681710; DataObjectsTester.testReviewOfStep8 |
| R8-2 | A failed static init fails the DB in rw() | fixed | 7681710; testReviewOfStep8, BadInit three times |
| R8-3 | An assert on a null scan value | fixed | 4f8210f; PubTesterIndexJobs.testScanTypes |
| R8-4 | V5 lets a subclass of Date through | fixed | 7681710; testReviewOfStep8 |
| R8-5 | V9 takes a bounded type variable | fixed | 7681710; testReviewOfStep8 |
| R8-6 | Scans do not check the class first | fixed | 7681710, 4f8210f; testReviewOfStep8, testScanTypes |
| R8-7 | void.class gives a NullPointerException | fixed | 7681710; testReviewOfStep8 |
| R3-F1 | A String "bergo"+U+0001 taken for format 1 | fixed | 02995d9; PubTester.testStringThatStartsAsFormat1 |
| R3-N2 | `Entries.suffix`: ukey "/d/.h" none, ikey "h" | fixed | 02995d9: "h" for both; testSuffixOfANameThat... |
| R3-N3 | DbString encodes, then checks the size | fixed | 02995d9; testStringValueCountedFirst; night: Huge |
| R3-x | A bytes field into a String field repairs | not a fault | 020-09, 5.6 (delegated); not 021-06's rule |
| R4-1 | A long String: the encoder allocates 2 or 3 a char | fixed | 4ff57b6; StringUtil.testToBytesOfAKnownSize |
| R4-2 | A format-1 previous value blocks its key | fixed | 4ff57b6; testFormat1ObjectRefused, testFormat1InIndexed... |
| B3 | DbObject and its value classes into bergdb.pub | done | fcc151b; JAVADOC PUB OK; DbByteArray.testImmutable |
| B3-F1 | A put of a DbObject kept the caller's array | fixed | 5e14229; PubTester.testDbObjectPutStoresACopy |
| B3-F2 | A class in bergdb.pub could extend DbValue | fixed | 5e14229; DbObjectFormatTester.testPackagesSealed |
| B3-F2b | A user's DbObject put unchecked | fixed | 5e14229; DbObject.testPutChecksTheBytes |
| B3-F3 | The release notes and ReleaseDemo without DbObject | fixed | 6514764 (ReleaseDemo, in build.sh), 2c60325 |
| B3-F4 | The Builders not final | fixed | 5e14229; DbObjectFormatTester.testValueClassesClosed |
| B3-F5 | build()'s limit; name parts checked after lookups | fixed | 5e14229; DbObject.testNamePartsCheckedFirst |
| B3-F6 | The String[] form for every typed getter | later | an addition, not a fault (section 1, L-F6) |

R4-1 and R4-2 are the review of 02995d9's two low points (section 6): a
String of 2^30 chars or more, whose UTF-8 fits, now encoded into an array
of its exact size (`PubTester.testLargeStringThatFits`, a night test, 1
GiB); and a previous value of format 1 has no entries, so a put over it
and a delete of it work in an indexed directory, also for a String whose
bytes are a whole format-1 structure; the refusal stays for a byte[]
put's new value and for a build.

R3-F1 in detail (the review of 577e867, probed at `db496dc`): a String
value whose text starts with "bergo" and U+0001, at an object key, made
`get(key, Object.class)` throw `ObjectCreationException` "format-1";
`usePrimary(String.class)` left it out; `usePrimary(Object.class)` and a
class threw at it; in a directory with an index, a put of it was refused
(`w()` and `rw()`), a build over it failed, and a put over it or a delete
of it was refused. Fixed in 02995d9 (decided under the delegation: a
String put is never format 1; format 1 is told by its structure, its
field count and a field table that fits, not by 6 bytes; the guess is in
`Connection.get`'s Javadoc): `PubTester.testStringThatStartsAsFormat1`
puts such a String and checks the gets, the scans of each type, the
puts, the delete and the index; `ObjectFormatTester.testIsFormat1` and
`Entries.testIsFormat1Object` the structure.


## 3. Indexes: F3 to F8 (020-01) and 020-10, section 8

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| S2-F1 | An ICU collator shared by threads | gone | 4f8210f, 6cbc619: no collator; H2's 4 writers: night only |
| S2-F10 | No start without ICU | gone | 6cbc619; build.sh refuses ICU in the release jar |
| S2-F14 | A level's commas lost | fixed | 0a6d8f4; IndexDefinitionTester.testRoundTrip |
| S2-F15 | An empty nested part | fixed | 4f8210f; PubTesterIndexJobs.testNestedFieldEmptyPart |
| S2-F20 | dir() twice | fixed | 4f8210f; PubTesterIndexJobs.testDirTwice |
| S2-F26 | A null indexed String throws or stops a build | fixed | 01e19c4, 4f8210f; PubTester.testOneIndexRule |
| N9 | ICU's sort keys in the stream | gone | 6cbc619; a start refuses /#i/dii/ |
| 015-28 | A write racing a creation | fixed | 4a6deee; PubTesterIndexRaces.testRacesCreate |
| 015-43 | The index set read before R | fixed | 4a6deee; testRacesCreate, Activate, Delete |
| S2-F12 | An old entry in a new index of the name | fixed | 4a6deee, 4f8210f; testRacesDelete; H2 (b768ef0) |
| 015-23 | A refused deletion stops maintenance | fixed | 4f8210f; IndexJobsHarness.testDeletionRefused |
| 015-29 | deleteIndex(PRIMARY) | gone | 4f8210f, f3c7966: PRIMARY gone; testIndexNamedPrimary |
| 015-30 | A build reads past its directory | fixed | 4f8210f; PubTesterIndexJobs.testBuildStopsAtDir |
| 015-36 | An interrupted deletion | gone | 4f8210f: no deletion job; testDeleteWithInterruptFlag |
| 015-37, N6 | An interrupt ends a build | fixed | cdabbcf (019-38); testInterruptInBuildIsNotAFailure |
| 015-39 | A status that changes after it is read | fixed | 4f8210f; PubTesterIndexJobs.testStatusIsSnapshot |
| 015-61 | A stopped deletion says done | gone | 4f8210f: no job; testStartResumesBuildsAndCleanups |
| 019-40 C5 | A deletion done after a failure | gone | as 015-61; testBugInCleanupLeavesTheMarker |
| S2-F11 | Done when the database stopped | fixed | 4f8210f, 9cbaa50; IndexJobsHarness.testStopDuringBuild |
| S2-F16 | A build indexes subdirectories | fixed | 4f8210f; testBuildStopsAtDir |
| S2-F27 | A refused creation stays in memory | fixed | 4f8210f, 9cbaa50; IndexJobsHarness.testCreationRefused |
| N7 | A step refused for good, retried | fixed | 4f8210f: 4,096 bytes of levels; testLargeValueNoEntry |
| N10 | A pause without its cap | fixed | 4f8210f; IndexBuilderImp.testPauseCapped, in Pack since 020-11's rows |
| S2-F2 | inclusive(false) alone | fixed | f3c7966: gone; PubTesterIndex.testExclusiveBounds; H2 |
| S2-F13 | prefix() on a secondary index | fixed | f3c7966; PubTesterIndex.testPrefix; H2 |
| S2-F22 | A later level alone | fixed | f3c7966; PubTesterIndex.testGrammar; H2 |
| S2-F23 | hasNext() true, next() throws | fixed | f3c7966; PubTesterIndex.testStaleLastEntries |
| N3 | A scan changes transactionInfo() | fixed | f3c7966; PubTesterIndex.testScanKeepsTransactionInfo |
| S2-F17 | The primary scan without dir() | fixed | 238b249; PubTesterPrimary.testPrimaryNeedsDir; H4 |
| S2-F25 | String.class gives objects | fixed | 238b249; PubTesterPrimary.testTypesListByKind |
| N5 | The API's boundary a convention | fixed | 51bcb9e, 4e2144d, 6cbc619, 4264ec5, fcc151b, 5e14229 (sealed) |
| N11 | Key replace in an entry's level bytes | fixed | 4f8210f; PubTesterIndexJobs.testKeyReplaceIndexedText |
| N8 | No scans in rw() | not a fault | decided (020-01, 14.1) |
| "/" build | A build over "/" failed since 021-06 | fixed | 4f8210f; testBuildStopsAtDir, index "root" |

Tonight's reviews and harnesses of the index steps:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| I2-join | join() in another thread gave BUILDING | fixed | 37c82cd; PubTesterIndexJobs.testJoinFromAnotherThread |
| I2-Error | An Error after a definition's commit | fixed | 37c82cd; testErrorInDefinitionChangeFailsTheDatabase |
| H3-F1 | An Error in a creation: the DB runs on | fixed | 37c82cd; IndexJobsHarness.testEveryPointAndFault |
| H3-F2 | A throw after a commit: stream and memory apart | fixed | 37c82cd; as H3-F1 (KNOWN empty) |
| H3-F3 | A throw after an activation's commit | fixed | 37c82cd; as H3-F1 |
| I1-starve | A build never ends under hot writes | fixed | 37c82cd; PubTesterIndexJobs.testBuildEndsUnderWriters |
| H2 | Harness H2 against BergDB | runs | b768ef0, e031ce3 (night: 8 seeds, 6 min); IndexHarness, 8 tests |
| H3 | Harness H3, the jobs under faults | runs | 9cbaa50, 37c82cd; IndexJobsHarness; night not run |
| H4 | Harness H4, the primary scan | runs | 238b249; PrimaryHarness.testSeeds; night not run |

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
* `level2.sh` ran on `4f8210f` (I2): LEVEL 2 OK.


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
| 020-07 Q6 | The spec's and vectors' home | decided: vectors in java/ (41cb0ba); 020-07 frozen |
| 020-07 Q7 | '.' and ',' in names and index paths | settled by 020-10 (nestedField parts) |
| 020-07 | The spec's approval under 018-01's rule | approved by Frans, 2026-11-09, 07:33 |
| 020-09, 9 | Questions for Frans | none; 24 decisions under the delegation, to read |
| 020-10, 11 | Decisions under the delegation | 22, to read |


## 5. The Core, and the lists of 015, 019 and 021

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 019-46 | A drop raced the writer's load | fixed | 9ac976d; NodeCollection.testDropIfEmptyKeepsTheWritersObject |
| 019-47 | A start kept a large value | fixed | db496dc; Eviction.testStartAdmitsLargeValuesOfThe... |
| R46-L1 | The writer could call dropIfEmpty itself | fixed | a182faa; testWriterKeepsTheNodeWhateverItsPolicy |
| R46-L2 | Handle and 009-02 words on DEAD | fixed | a182faa (words; 009-02 and Handle's Javadoc) |
| R46-L3 | a182faa's assert fired, legal schedule | fixed | 4eaa97a; NodeCollection.testWriterDuringADropsDeadWindow |
| B2-R1 | bergdb.dev.Run could not start a non-public main | fixed | 0586b65; Run.testRunsMainOfAClassThatIsNotPublic |
| B2-R2 | Reflection through pubimp's classes fails | not a fault | 4264ec5's narrowing; in the release notes |
| 021-06 | Ill-formed UTF-8 read: keys and String values | fixed | a1b505c, 2054805; Utf8ReadTester, 3 tests |
| 021-09 | udir2idir took "p/" and "/p//" | fixed | d099a3a; PubKeys.testUdir2idirRefusesBadDirs |
| 021-10 | A '.' in a directory: no object key there | fixed | 577e867; Entries.testSuffixOfTheLastPart |
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

* Objects, step 2 (01e19c4): the bytes, the reader, the lookups. No fault
  there; five findings: 019-42's restart test lost, R15's sizes giving
  Errors, a data race on DbString's UTF-8, DbValue's public constructor
  and DbObject not final, a cycle's message. Fixed in 577e867 (R2-1 to
  R2-5).
* Objects, step 8 (2ca4610, DataObjects): the get table against 2,000,000
  random values, sound; seven findings (a Number subclass, a failed
  static initializer in `rw()`, a scan's assert, V5, V9, the scans'
  class check, `void.class`). Fixed in 7681710 and 4f8210f (R8-1 to R8-7).
* Objects, steps 3 and 7 and 021-06's second half (577e867, e4620c3,
  2054805): format 1 refused everywhere, the key field gone, String reads.
  One fault, R3-F1 (a String that starts as format 1), and two notes
  (R3-N2, R3-N3). Fixed in 02995d9.
* The fix of R3-F1 (02995d9): 2,816 of 2,816 real 2026.3 objects
  recognised, 2,000,000 hostile inputs without an exception, no format-2
  value taken for format 1, the cost linear and bounded. Two low points
  (R4-1, R4-2). Fixed in 4ff57b6.
* B3 (fcc151b, `DbObject` in `bergdb.pub`): sound otherwise; F1 (medium,
  a put kept the caller's array, so a later change of it changed the
  committed value in memory), F2 (sealing; user DbObjects unchecked), F3
  (release notes, ReleaseDemo), F4 (final Builders), F5 (Javadoc, name
  parts), F6 (an addition for later). Fixed in 5e14229, 6514764, 2c60325.
* I1 (4a6deee, maintenance): 8.4 million writes, sound; one liveness
  fault in I2's build, starving under hot writes. Fixed in 37c82cd.
* I2 part 1 (4f8210f, layout, jobs, API): 816 crash images, 60 stops, 30
  seeds, sound; `Job.join()` from another thread could return BUILDING; an
  Error after a definition's commit left memory and stream apart. Fixed in
  37c82cd, with harness H3's H3-F1 to H3-F3 (9cbaa50; 9 planted faults
  found).
* I3 (f3c7966, the scan builder): 8,000 scans, 1,064,112 results equal to
  a reference. No fault.
* P1 and I0 (238b249, 0a6d8f4): no findings; a note for I1 (the entry
  function given no value) and a coverage note for the objects' steps.
* B1 (51bcb9e, the release jar): no fault; two notes for B2 (the ICU
  prefix, ICU's license), both gone with ICU (6cbc619).
* B2 part 2 (4264ec5, the narrowing): sound; `bergdb.dev.Run` could not
  start a main that is no longer public (fixed in 0586b65); reflection
  through pubimp's classes now fails (in the release notes, 2c60325).
* 021-06 and 021-09 (a1b505c, d099a3a): a printer of keys in KeyNode
  that decoded with U+FFFD, fixed in fecfb10.
* 019-46 and 019-47 (9ac976d, db496dc, Core): both fixes correct (260,000
  jcstress-like rounds, 1,100 seeds, 1,477 starts); two low points
  (R46-L1, R46-L2), fixed in a182faa. Its follow-up review of a182faa:
  the code right, but its new assert could fire on a legal schedule with
  `-ea` (R46-L3), fixed in 4eaa97a with a forced-schedule test.
* The first audit of this item (4aa8c70): the open rows above, closed in
  16736f0, 3323e5b and the fixes listed.

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
  ".h" has "h", as 02995d9 settles `Entries.suffix` for ukeys and ikeys
  alike); `ObjectKeysTester.testObjectKeysOfThePutJavadoc` pins its
  examples in `w()` and `rw()`.


## 8. Measured and checked

* 020-08, step 4, done (020-12, 01d2187): format 2 against format 1 on a
  quiet F53, M1 to M8, every figure as fast or faster but M8 (C-M8,
  section 1); `performance.sh ab` (quick) against release 2026.3: NO
  ALERTS. The tool fault T-OB is fixed (00a8277).
* The level scripts after the last Core changes: `level4.sh` ran on
  019-46, 019-47 and a182faa (LEVEL 4 OK); `level2.sh` on I2 and on the
  final `main` (LEVEL 2 OK); 4eaa97a changed only an assert and added a
  test.


## 9. The night's runs (the coordinator's rows)

| Run | On | Result |
|---|---|---|
| Night tests (the night group) | e031ce3 | SUCCESS, 24 tests in 1,332 s |
| `night.sh` | fcc151b | NIGHT OK, 65 minutes (java/build/night/2026-11-09-0158/report.txt) |
| Night tests | 7231771 | SUCCESS, 26 tests in 1,262 s |
| `level2.sh` | 7231771 | LEVEL 2 OK |
| Step 4's quiet runs | 7231771 | 020-12: M1 to M8; `performance.sh ab`: NO ALERTS |

`night.sh` ran `before-commit.sh`, the core-build check, `level1.sh` to
`level4.sh`, the Lean tests, 25 night tests and the conformance set
(medium). The night tests on 7231771 are the night group of the final
`main`, 26 tests.


## 10. The bug hunts of 9 November

The hunts before the release candidate (Frans, 08:41 and 09:21), each in
a clone of its own (020-13 to 020-20), Frans's API decisions (020-21),
the rules for writes through the Core (020-22), the reviews of the day's
fixes (020-23), and 021-11 and 021-12; on `main` from `f8046f3` to
`73dda0a`, and this update's commits (020-23's V1-2 to V1-4). Each test
named was read, and run at `73dda0a` with this update: the 43 tests named
outside `PubTesterJavadoc` in one unit run, and `PubTesterJavadoc`'s 50,
`-ea`, all passed; the gate on that tree passed (BEFORE COMMIT OK, unit
1,507, f 86, demos 14), and JAVADOC PUB OK.

The Pub layer:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 13-B1 | An rw() read two states after a get's conversion threw | fixed | 94d68d3; testRwFirstReadThatThrows... |
| X2, 13-B2 | A static initializer's Error failed the DB in rw() | fixed | 4883b11, 7357ea0; testInitializerError |
| X1 | Key replace in an object key's directory: a wrong index | refused | ae698d6; testKeyReplaceInDirectory... |
| 13-B3 | A replaced name deleted the literal key's entries | fixed | ae698d6, f758df6; testKeyReplaceKeeps... |
| X3 | A field of a package not exported passed the check | refused | 88e8a5e; testClassesOfAModule |
| 13-M | Three planted faults that the gate missed | tests | 5ad1539; testWriteRunsAgainAfterDeletion and 2 more |
| F16-1 | A corrupt entry key: a scan's IllegalArgumentException | fixed | f1101b0; testCorruptEntryKey and 1 more |
| F16-2 | A value at `/#i/didef/` hid the definitions from a start | refused | 3eceeed; testStartRefusesBadIndexData |
| F16-3 | A build failed over a Core key such as `/dp/-a/b` | fixed | 68068cf; testBuildSkipsKeysWithASlashInTheName |
| 18-F1 | A build step collided with suffix writes under the lock | fixed | 9d5aa1b; testSuffixWriteDoesNotRerun... |
| 18-F2, 19-F1 | A deleted build's note: "The next start takes it" | fixed | 103328d, 1c1b054; testNoteOfADeletedBuild |
| 18-F3 | A locked build step read 25 large values under the lock | fixed | 7cb285e; testBuildStepBoundedByBytes |
| 18-F4 | A build chased the writers appending to its directory | fixed | 42195a4; testBuildReadsUpToItsStarts... |
| 18-F5 | A cleanup's work grew as the square of its entries | fixed | 3a13d1b; testCleanupWorkIsLinear |
| 20-N1 | `CryptoKey.getKeyData()` gave the key's own array | fixed | b5b1a61; CryptoKey.testGetKeyDataGivesACopy |
| 21-1 | `Time` took strings that break its format, rolled over | fixed | 3b3064f; Time.testStrictTimeStrings |
| Y1 | A minus time's duration through a double, truncated | fixed | 34e4668; Time.testMinusTimeExact |
| Y2, V1-1 | "2020-06 12:34", which the grammar allows, refused | fixed | 69c8518; Time.testMonthWithTimeOfDay |
| 21-2 | `WBuilder.execute()` twice ran the writes twice | fixed | b4ff335; testWBuilderSpentByExecute |
| 21-3 | `setRetainDuration(null)`, `useIndex(String.class)`, `join(-1)` | fixed | 285d031; testSetRetainDurationNull, 2 |
| 21-3b | `CryptoKey.NULL`'s round trip; `parse(null)` | fixed | 285d031; CryptoKey.testNullRoundTrip |
| 21-Q1 | `Duration.seconds(NaN)` gave 0 | refused | 4081966; PubTesterJavadoc.testJavadocCorners |
| 21-4 | The gate's StoppedCheck did not see the index threads | fixed | 119c706; testIndexThreadsChecked |
| R22-1 | `transactionInfo()`: a key that is no Pub key's | fixed | 6f9f500; testTransactionInfoLeavesOut... |
| R22-2 | An index scan gave a Core value under `/r/`, no key | fixed | ded994b; testScanLeavesOutAKeyWithNoUkey |

The Core:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| 13-B4 | `BufferedStream.close()` waited a quarter of the buffer time | fixed | 12092e0; testCloseDuringAFlush... |
| V2-2 | An append that waited for room when close() began returned | fixed | e1f9676; testAppendWaitingForRoom... |
| T1 | A directory that cannot be listed: an NPE, bad advice | fixed | 4bba305; testUnlistableDirectory, 2 |
| 021-11 | A pointer to a node of another type, linked by node id | fixed | 36e003f, b8503a3; testFound021_11 |
| V2-1 | `linkToCanonical`'s own type check had no test | test | f744b7d; testLinkToCanonicalChecks... |
| 021-12 | A damaged key node before the section: an AssertionError | fixed | 4ff84fb; testFound021_12 |

The Javadoc and the documents:

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| J1 | `setCacheSizeInMb()` after `stop()`: "no effect" | fixed | d9aec63; PubTesterJavadoc.testCallsAfterStop |
| J2 | Only `toDbObject()`'s message names a lone surrogate's place | fixed | ddb024e; testLoneSurrogateRefusals |
| J3 | A get takes a primitive's class, its wrapper, an array | fixed | b7f140c; testGetOfPrimitivesAndArrays |
| J4 | `DbException`'s example was 2026.3's rule | fixed | 50bf8ff; testFormat1PutRefusedInEveryPath |
| J5 | A format-1 byte[] put's DataFormatException not listed | fixed | 797c8ce; testFormat1PutRefusedInEveryPath |
| J6 | An interrupted sync's DbException not listed | fixed | 13a92b4; testSyncInterrupted |
| J7 | `Time`'s grammar short of the code | fixed | 7607aa9, then 3b3064f (21-1); testTimeStrings |
| J8 | A refused write's DbException: too large, stopped, interrupt | fixed | 0a6fa2e; testTooLargeRefused and 2 |
| V1-2 | put(), delete(), execute(): the interrupt after a conflict | fixed | this update; testWritesInterrupted... |
| 21-3c | Six corners of the Javadoc (020-13, 4.2; 020-19, 6) | fixed | 285d031; PubTesterJavadoc.testJavadocCorners |
| KR-O1 | A creation or deletion that returned, undone by a crash | said | 52603cb (Javadoc); KillRestartHarness |
| R22-r | The rules for writes through the Core, in five places | done | ff5fbfa; Javadoc, levels.md, 3 more |
| V1-3 | 020-10, 6.1 and 6.2: the build before 020-18's fixes | done | this update (020-10's sections 6.1, 6.2, 3.2) |
| V1-4 | No release note for 13-B1; next.md against the day | done | this update (releases/next.md) |
| K-empty | `bkey2ikeyOrNull` of the empty bkey: "", no key | said | this update (`Keys`' Javadoc) |
| 47-doc | 019-47's test: its comment named the wrong case | fixed | this update (Eviction's test Javadoc) |

The harnesses (false findings, no fault of BergDB):

| ID | What | State | Commit; test (ran) |
|---|---|---|---|
| H3-O1 | A deletion during a build taken for a fault taken again | fixed | 073367f; testRetriedFaultThenDeleted... |
| H3-O2 to O4 | A stop at the workload's read; a racing check; a bound | fixed | 612da39, bd35404, f494703 |
| N16-1 | 020-07's sketch F2 reads past its extent | not BergDB's | none |

Since 73dda0a, to `d00096e` (the evening's items pass): the faults of
021-13 to 021-27, found by the new users' applications (020-24), by the C
port and its black-box users (022, 022-06), and by Codex's rounds 3 and 4
and the reviewers (020-23); and the fixes of 020-25, 020-27 and 020-28.
Each commit is on `main`, each test named was read, not run again for
this update: each ran in its fix's gate under the gate lock (BEFORE
COMMIT OK; `level1.sh` for the Core's), as each item's Log says, and the
integrator's gate of the combined tree that landed as `d00096e` passed.

The Core:

| ID | What | State | Commit; test (read) |
|---|---|---|---|
| 021-13 | `transactionInfo()` during another's write failed the DB | fixed | 1ad85d3; testGetTransOfARecord... |
| 021-14 | A read whose end overflows a long: no EOFException | fixed | 78c6718, 4957737; testReadPastEnd..., 3 |
| 021-15 | A start's refusal texts named nodes by identity hash | fixed | 6b58e8c; testNodeTextsSame..., 2 |
| 021-16 | A key of about 90 KB or more overflowed the stack | fixed | e5b552c, 0dc79be; DbTesterLongKeys, 4 |
| 021-18 | `GetMany.Prefix` stopped at the prefix's own key | fixed | dff9a6a; testPrefixHasThePrefixKey |
| 021-19 | A KV's time is its key node entry's, not the write's | said | 977b599; testKvTimeIsTheEntrysTime |
| 021-20 | A deleted directory's database wrote into a new one | fixed | 2557286; testNoNewFileIn..., 3 |
| 021-24 | A directory replaced during a force got the next file | fixed | 41b9b15, d00096e; testNoNewFile..., 1 |
| Z1 | `currentTime()` after the clock went back: earlier times | fixed | 7ad5019; DbClock.testClockGoesBack, 2 |
| 021-26 | A `currentTime()` past the end refused later puts | fixed | 007140d; testCurrentTimeWith..., 1 |
| 021-25c | Puts slowed after reclaim passed many deleted keys | fixed | e8cbf9d; KeyAccessPath's 3 Nano tests |
| 021-25 | Reclaim stops cutting a FIFO of keys in time order | known | 5ddffde (releases/next.md); section 11 |
| 021-27 | `Db.getTrans` inside a record fails the database | Frans | f1a5456; testGetTransInsideARecord |
| 27-C | 020-27's C1 to C3, and Q1 and Q2 as Frans decided | fixed | 3849076 to 50e3c5b, a848c62 to f490cfa |
| A-1 | Android: `java.lang.management`, modules (006-18-03) | fixed | aef43ff, 9c96452, 7278354; android.sh |

The Pub layer:

| ID | What | State | Commit; test (read) |
|---|---|---|---|
| 021-17 | After reclaim's copy, `transactionInfo()` refused | fixed | 7eb2852, 0d85f28; testTransactionInfo..., 2 |
| 021-21 | An `RwEnvironment` used by threads: lost puts, a failed DB | fixed | c0cff96; PubTesterThreads, 4 |
| 021-22 | A `Connection` shared by threads: wrong reads, a failed DB | refused | 18ddc6e; PubTesterThreads, 4 |
| 021-23 | A put of an object too large to store: OutOfMemoryError | refused | eba1c2f; testPutTooLarge, 1 |
| Z2 | A byte[] index scan returned a format-1 object | fixed | e85e021; testCorePutOfAFormat1Object... |
| Z3 | `Clock.getTime()`: a start with the clock out of range | said | 15bd3ec; testStartWithTheClockOutOfRange |
| 25-C | 020-25: C1 to C3, J1 to J7 | fixed | 2502275 to 89d1dbb; PubTesterJavadocRest |
| 020-28 | Encryption out of 2026.4's API (020-24-07, U7-1, U7-3) | done | 50caeb0; for later, 017-10 |
| 020-24 | The new users' findings: faults fixed, Javadoc made true | done | each app's Fixes (01 to 15) |

Notes:

* 13-B2 and X2, and 13-B3 and X1's sibling in the name, were found apart
  and are one fix each: X's code, with 020-13's tests added.
* 18-F2 and 19-F1 are one fault: 020-19's code, with 020-18's check of
  the note in `assertDeleted`, which every test of a deleted build calls.
* Release notes: each user-visible fix has its line in
  `releases/next.md` (V1-4 checked them all; the Core's V2-2 has none, as
  no `Db` reaches it, 020-23, section 3.4).
* New steps of `night.sh` since today: `harness-soak.sh` (020-17),
  `fuzz.sh` (020-16) and `kill-restart.sh` (020-15).
* 021-25 is not a regression: the same run on release 2026.3, byte for
  byte. Its fix (c) ended 020-24-14's U14-1 (puts slowed by index churn
  under reclaim) with no change of the stream; the cuts still stop.
  021-27 behaves as `Db.getTrans`'s Javadoc says; only the Core API can
  give such a position. Z2's rule, a scan leaves out a format-1 object
  for every type, is Frans's decision (16:20; 020-23's Log).


## 11. Left for a later release

None breaks a promise of 2026.4; each is an observation, a cost, a gap of
the tests, or a write that the rules leave undefined. The second table,
added on the evening of 9 November, holds the day's open questions and
API wishes, from the new users' applications (020-24), the C port's
black-box users (022-06; an ID `C-` is theirs), the fixes left open and
the proof of 020-29: each for a later release, or for Frans where it
says so; 021-25 is a known issue of 2026.4 (`releases/next.md`).

| ID | What | With |
|---|---|---|
| O16-1 | A get as DbObject or a class reads format 2 at a key with a suffix | Frans, 11:52: fine as is |
| 18-O1 | One thread per build and per cleanup; thousands at once could OOM | later: a queue, one thread |
| 18-O2 | A job's status lags its index by a moment (BUILDING, then ACTIVE) | later; as the stream says |
| 18-O3 | A scan visits the keys deleted in its range: slow after churn | later; large databases |
| 18-F3r | One value of tens of MB makes a locked build step that long | later: reads out of the lock |
| KR-lit | A literal key with a later time's digits keeps its old entry | later: an insert-if-absent |
| 15-gaps | Kill-restart: APFS only; no format-1 build; no power loss | later: s1's ext4, the cases |
| 22-W | Core writes that rules forbid, unseen: W6, W12, W16, W25 | undefined (A2); B4 later |
| 17-B | Harness blind spots: B9's String, B18, B19, H3's one index | later, tests only |
| 13-cov | Coverage: level1.sh's other steps; values near 2^31 bytes | later |
| 13-slow | Slow f-tests that add little (020-13, section 5) | Frans, if the gate should be faster |
| 21-flake | `Eviction.testInterruptedWhileAWriterWaits` failed once at load 19 | watch; passed since |

| ID | What | With |
|---|---|---|
| U12-4 | A field type not on the list: the message names it, not the class | Frans: API (020-24-12) |
| U13-4 | No delete of a directory: list the keys and delete each | later: API (020-24-13) |
| U13-5 | Paging an index of two levels takes three scan forms (U4-4) | later: a resume point |
| U13-7 | Starts after a transaction larger than the startup distance | Frans: bounded startup (007) |
| U14-2 | No listing of the indexes or of their definitions | later: API (020-24-14) |
| U14-3 | No listing of subdirectories: a tenant's tree is unknown | later: API |
| U14-4 | A rebuild under its name: queries throw until it is built | later: API |
| U14-5 | No word on limits on the number of indexes, or their cost | later: doc |
| U14-6 | No way to know that a deleted index's cleanup has ended | later: API |
| U15-6 | The Pub Javadoc names exceptions of packages that are not API | Frans: 020-24-15, Q2 |
| 15-Q1 | The Core API's Javadoc is not published | Frans: 020-24-15, Q1 |
| 021-24 | A replacement between the check and the step; its empty file | later: SecureDirectoryStream |
| 021-25 | Reclaim stops cutting a FIFO in time order, or under index churn | Frans: fixes (a), (b) |
| 021-27 | `Db.getTrans` inside a record fails the database | Frans: option A after 2026.4 |
| 16-Q1 | A long key's still-dirty loop is quadratic (C-U2-3, C-U1-1) | Frans: 021-16, Q1 |
| C-U2-6 | A stream file deleted or cut: synced records dropped (U8-1) | Frans: U8-1's options |
| C-U2-8 | Core puts under "/#" taken; bad reclaim settings: no start | later: Core refuses them |
| C-U2-2 | After a full disk, the torn record's size must be free | later: 014-01 |
| 29-fair | Builds of several names need a fair lock; `synchronized` is not | Frans: 020-29, section 7 |

* O16-1 (020-16, section 3): `get(key, DbObject.class)` and `get(key,
  C)` read a value of format 2 at a key with a suffix as an object, while
  `get(key, Object.class)` gives the `byte[]` and `usePrimary()` leaves
  the key out. Frans (11:52): fine as is for 2026.4; storing objects,
  bytes and strings at the Pub layer, indexing them and the relation to
  the Core are for a later release.
* 020-18's observations (section 2.5): O1, a burst of deletions or a
  start with many markers starts a thread each, and a thread's creation
  could throw `OutOfMemoryError`, which fails the database (P7); O2,
  between the activation's commit and the job's update `getStatus()` says
  BUILDING, and a deletion then gives a job that ends ACTIVE; O3, a read
  at the latest time visits the keys deleted in its range (the Core keeps
  them for earlier lookup times): an `eq()` with no result over a range
  that 100,000 entries left takes 2 to 12 ms against 0.1 ms, linear in
  the range's history, the primary scan likewise. F3's rest: a step under
  the manager's lock still reads one value whole.
* KR-lit (020-13, bug 3; 020-14, X1): a value written at a key as it is,
  whose name holds digits that a later replaced put's time gives, keeps
  its old entry when that put lands on it; a scan never returns it (it
  gives only the values that their entries still match).
* 020-15's gaps (section 4): only macOS's APFS ran (not s1's ext4); no
  values that a build cannot take (a FAILED build over format 1, taken
  again at a start); no power loss (the Core's PowerLossTest has its
  model).
* 020-22's undefined writes (sections 5 and 6, A2 as Frans decided): a
  Core put at an object key of an indexed directory (W6, allowed with
  care: no index while writing, or a repair after), a well-formed
  definition that the Pub layer did not write (W12), a deleted entry
  (W16), a definition written while the database runs (W25): values left
  out of scans, never a wrong result; no cheap check finds them. B4, a
  `src-dev` check of an index's content, after the release if wanted.
* Test gaps: 020-17's B9 (`String` scans), B18 (no refused writer in
  H2), B19 (no listing while transactions commit) and H3's single index;
  020-13's coverage (level1.sh's other steps, values near 2^31 bytes) and
  its proposals for slow f-tests; 020-21's timing failure of
  `Eviction.testInterruptedWhileAWriterWaits` at load 19, once.

The second table's sources, one line each (020-24's findings in each
app's table of findings; 022-06's in `items/022-bergdb-c/06-user-apps/`,
and the C users' own reports in `/Users/f/fl/bench/022/apps/u1/`, `u2/`
and `u3/`, `report.md`):

* U12-4: 020-24-12, "U12-4" and its Fixes; one fault a class, so not
  small.
* U13-4, U13-5: 020-24-13; U13-5 is U4-4's resume point (020-24-04).
* U13-7: 020-24-13, "U13-7"; said in `startupDistanceInMb()` (`445b54c`);
  a start's time bounded also then is 007's question.
* U14-2 to U14-6: 020-24-14, section 3. U14-1's slowdown of puts ended
  with 021-25's fix (c); its stall of the cuts under index churn is
  021-25's cause, parts 1 and 2, not fixed (021-25, "Fix (c)").
* U15-6 and 15-Q1: 020-24-15, "Questions for Frans" (Q2: a sentence now,
  an API exception for "directory in use" later; Q1: publish the Core
  API's Javadoc in the release after 2026.4).
* 021-24: its "Left": `SecureDirectoryStream` would close the window of
  microseconds (longer if the thread is paused) between the check and the
  step; the empty file it can leave is refused by an exception that
  depends on the directory; any `IOException` of the check's `stat` counts
  as "gone" (020-23, section 7).
* 021-25: "For Frans": (a) end the touch at `touchTo`, (b) drop index
  nodes that hold deleted keys only; both change the stream (022's C
  equality, StreamDigest); the known issue in `releases/next.md`, "Known
  issues and limits", names the FIFO.
* 021-27: options A to D; C for 2026.4 (as it is), A after it.
* 16-Q1: 021-16, Q1, `Db.handleStillDirtyNodes` (Rule A); 022-06-2's
  U2-3 and 022-06-1's U1-1, confirmed in Java (a 4 MB put next to 1 MB
  keys with a shared prefix: 29 to 48 s).
* C-U2-6: 022-06-2, U2-6, confirmed in Java, with 020-24-08's U8-1 and
  its options (a) to (c) (020-24-08, section 4).
* C-U2-8: 022-06-2, U2-8, confirmed in Java; under 020-22's A2 such a
  write is undefined; a Core refusal of writes under "/#" is later work.
* C-U2-2: 022-06-2, U2-2, confirmed in Java: 014-01's zero fill.
* 29-fair: 020-29 (on its branch, not merged), section 7: with several
  index names a build needs strong fairness of the index manager's lock,
  which Java's `synchronized` does not promise; with one name weak
  fairness suffices, and with finitely many definition changes too
  (`build_ends_weak`). Section 7.5: `ReentrantLock(true)` (cost to measure),
  a bound on definition changes while a build waits, or a Javadoc sentence;
  in practice a build starves only under a loop of index creations and
  deletions on other names.


## 12. Log

2026-11-09. Written in night 006-15 from `main` at `b768ef0`, at the
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

2026-11-09. R3-F1, R3-N2 and R3-N3 fixed on `main` in 02995d9 (the
objects agent): their rows, N2's, R2-2's and T9's brought up to date;
the tests read and run.

2026-11-09, about 02:30. Brought up to date to `4eaa97a` at the
coordinator's request: e031ce3, 02995d9, 4ff57b6, fcc151b, 5e14229,
6514764, 0586b65, a182faa, 4eaa97a, 4264ec5's review and the release
notes (2c60325); each named test read and run, the unit group passed
(1,415 tests), JAVADOC PUB OK. No known fault open; open are step 4's
measurements, Frans's approval of 020-07, and three additions for later.
A section on the night's reviews (6); the night's runs left for the
coordinator (9).

2026-11-09, morning. Brought up to date to `01d2187`: S4 closed (020-12;
020-08 done); C-M8, a known cost accepted under the delegation; T-OB, the
tool fault of `objectbench.sh` since B3, open with another agent; the
night's runs (section 9): `night.sh` NIGHT OK on fcc151b, the night tests
and `level2.sh` on 7231771.

2026-11-09, 04:36. T-OB fixed in 00a8277 (objectbench.sh compiles
ObjectBench for each build); its open row removed (coordinator).

2026-11-09, 05:40. `night.sh` on the final commit 5fb923f: NIGHT OK
(63 minutes; levels 1 to 4, the Lean tests, 26 night tests, conformance
medium; java/build/night/2026-11-09-0436/report.txt) (coordinator).

2026-11-09, afternoon. Brought up to date to `73dda0a` by coord-1109's
agent d27, the day's document update: section 10, every fault that the
day's bug hunts found and fixed (020-13 to 020-23, 021-11, 021-12), each
with its commit on `main` and its test, read and run (93 tests); section
11, what they left for a later release; section 1's summary; section 4's
row of 020-07's approval.

2026-11-09, evening. Brought up to date to `d00096e` by coord-1109's final
items pass: section 10, "Since 73dda0a", a row for each of 021-13 to
021-27, Z1 to Z3, and 020-25's, 020-27's, 020-28's and 020-24's fixes,
each with its commit on `main` and its test, read (each ran in its fix's
gate); section 11's second table, the day's open questions and API
wishes, each with its source; section 1's summary.
