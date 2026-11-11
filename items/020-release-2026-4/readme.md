020-release-2026-4
==================

Created 2026-11-06 by Frans Lundberg. Status: open.

Release 2026.4 of BergDB: a bug-free database. It adds to 2026.3's
bug-free Core (018) the rest of what a user of BergDB can use, user
indexes and the serialization of Java objects (DbObject) included, which
are experimental in 2026.3. The plan, its decisions and the work towards
the release.

Frans, 2026-11-06, 11:58: "I would like to discuss next release, 2026.4.
The overall theme is: a bug-free database. We add the non-Core part of
the database covering all functionality available to a user of it.
Including indexing, and serialization of Java objects." And, 12:05, to
the first questions: "No, nothing in particular is off the table. No need
for any backwards-compatibility. API can change." User indexes are a
must: "Yes. That is included."

The first step (Frans, 12:05: "I like your plan."): an inventory of the
non-Core part, feature by feature, with what each promises today, how it
is built, its known faults and tests, its open questions of meaning, and
options to keep, simplify or drop it, for Frans to decide feature by
feature before any fix. Then the contract (the promises), harnesses
against a simple reference (an index is a function of the data at a
lookup time; an object makes a round trip), and the fixes, as for 2026.3
(018-01).


Files
=====

Its todo list is 021-todo (Frans, 2026-11-06, 15:51).

* [01-inventory.md](01-inventory.md). 020-01, the inventory of the
  non-Core part, written 2026-11-06, nothing decided:
  * seven features and a boundary: objects and their format, the get
    into another class, index definition, index maintenance, index jobs,
    index reads, the primary scan, and what else a user can reach;
  * for each, its promises, how it is built, its size, its known faults
    (10 entries of 015 and 26 of review S2), its tests, its open
    questions of meaning, and options with a recommendation;
  * ten new findings (N1 to N10), among them a build over a null indexed
    `String` that fails the database at every start since 019-10;
  * a summary table, the order of Frans's decisions, and the first
    harness of each kept feature.
* [02-objects-design.md](02-objects-design.md). 020-02, objects: the
  design worked out with Frans one question at a time, from shape 1
  (Frans, 2026-11-07, 09:52); question 1, a conversion on a get, exact or
  best effort, and option (D), storage and conversion apart with a
  report; question 1b, whether BergDB stores null (Frans leans to no
  null). The main study of objects' storage (Frans, 2026-11-08, 15:22):
  section 4, the decisions on object storage one at a time, from 020-03
  to 020-06, with Frans's leans (no null; 020-05's (f); binary search,
  no hash list); section 5, the API and the conversion, not yet for
  decision; section 6, whether the studies are enough (yes).
* [03-null-study.md](03-null-study.md). 020-03, the study for 020-02's
  question 1b (Frans, 2026-11-07, 12:15): null and absence in languages,
  serialization formats (Binson, JSON, BSON, XML, CBOR, protobuf and
  more) and databases (MongoDB, SQLite, Prevayler and more), what BergDB
  does with null today (a probe, BG1 to BG6), and what each option asks
  of a binding in another language; the programs are in
  `/Users/f/fl/bench/006-14/020-null/`.
* [04-no-null-design.md](04-no-null-design.md). 020-04, the design and
  the change plan for "no stored null", option (d) of 020-02's question
  1b (Frans, 2026-11-07, 14:31: "Now it is ok to design and document"),
  ready for his "ok-and-implement": the rules of the put, the get, the
  constructor check and the indexes; the format and its spec text; the
  code sites at `7edcbe2`; the tests, old and new; the Javadoc and
  release notes drafted; questions Q1 to Q6 for Frans. No code changed.
  Written for today's format, version 1; what 020-05's option (f)
  changes in it, and what 021-07 and 021-08 did since: its section 11.
* [05-binson-for-objects.md](05-binson-for-objects.md). 020-05, Binson
  (binson.org) as the byte format of objects, a study for 020-02's
  question 4 (Frans, 2026-11-07, 20:42): the types, the bytes and their
  sizes, reads measured both ways, the kind of a value, the
  implementations in other languages, the spec as a BergDB profile, the
  cost; options (a) to (e), recommended (c1), Binson under a profile
  behind a short header of kind and version. Option (f) added on
  2026-11-08 (Frans, 09:32): DbObject's table with Binson's values,
  Binson's sizes with a field found without a walk, converted to and
  from Binson by copying the values; recommended since then, with the
  lookup's variant from 020-06. Frans leans to (f) (2026-11-08, 15:22:
  "binson value format but not the whole Binson format"), with a binary
  search for fields. No code changed; the programs are in
  `/Users/f/fl/bench/006-14/020-binson/` and, for (f),
  `/Users/f/fl/bench/006-15/020-05/`.
* [06-field-lookup-measured.md](06-field-lookup-measured.md). 020-06,
  a field's lookup in an object's bytes, measured (Frans, 2026-11-08,
  09:32): a linear scan of 16-bit hashes at the start of the bytes (H16)
  against a binary search on the names (B) and close variants, in the
  format of 020-05's option (f), for objects of 1 to 100 fields, Java and
  C, hot and cold, with the collisions of five hash functions on 16,944
  JDK field names and the cache lines each lookup reads. H16 is faster
  but in two corners: under 20 fields 1.1 to 1.5 times on hot hits, 2.3
  to 3.1 on hot misses, 1.5 to 1.9 on cold misses from 8 fields, 1.0 to
  1.2 on cold hits. Recommended for (f): 16-bit FNV-1a hashes of the
  names after the count, then the offsets; a scan, no binary search.
  Frans leans to the binary search instead (2026-11-08, 15:22: "binary
  search for fields (no hash list)"): a difference of at most 35 ns hot
  or warm, next to a get of 0.8 to 3.8 µs (020-02, section 4.3). The
  programs are in `/Users/f/fl/bench/006-15/020-06/`.
* [07-object-spec.md](07-object-spec.md). 020-07, the spec of stored
  objects, format 2, "DbObject's table with Binson's values", as Frans
  decided it on 2026-11-08 (020-02, section 4), written at his request
  (17:12) for his approval under 018-01's rule, approved 2026-11-09,
  07:33 (done): the model, the grammar,
  the rules R1 to R15, what a writer must do and a reader must refuse
  (each condition with a code), the limits, the lookup by binary search,
  the header and the old format, the conversion with Binson; seven
  questions for Frans (Q1 to Q7; Q1 decided). Its conformance vectors,
  since 020-08's step 1 in
  `java/src/bergdb/pubimp/doc-files/object-vectors.txt`: 33 valid
  values with 343 lookups, 85 invalid byte strings, 8 Binson inputs,
  checked by two implementations written apart; the programs are in
  `/Users/f/fl/bench/006-15/020-07/`.
* [08-implementation-plan.md](08-implementation-plan.md). 020-08, the
  implementation plan of format 2 and 020-04's no-null rules in the Java
  code, for Frans's "ok-and-implement" (17:12): a codec, `ObjectFormat`,
  under `DbObject`'s API; the changes file by file; the provisional
  choices where the API is open (020-02, section 5) and where each
  decision joins; 52 existing tests changed, about 25 new, the vectors
  run by Java and a harness against a reference codec; the measurements
  of 020-02, section 6; the steps and commits (since 2026-11-08, 22:38:
  steps 1, 2, 7, 8, 3, 4, 6, step 5 dropped, about 7 days); the risks.
  Done on 2026-11-09, each step's record in section 8; step 4's
  measurements are 020-12.
* [09-conversion-rules.md](09-conversion-rules.md). 020-09, the rules of
  the conversion between Data Objects and `DbObject`s in Java for 2026.4,
  both ways, from Frans's decisions (020-02, section 2's decision and
  section 5.1b, 19:21 to 21:59) and his delegation of the rest (22:17):
  which classes are Data Objects (public, a public no-argument
  constructor, public fields, the closed list of types; one check per
  class); the put, exact (a null field left out; a null element, a value
  of another class, a cycle and depth 17 refused, naming the path); the
  get, best effort (by name, the nearest value, the type's zero, never a
  throw for the data; `ObjectCreationException` for a class that is not
  a Data Object); today's code against it; 176 test cases and three
  properties. Section 6 lists the 24 decisions taken under the
  delegation. For 020-08's step 8. No code changed.
* [10-indexes-design.md](10-indexes-design.md). 020-10, the user indexes
  of 2026.4 designed for tonight's implementation, from Frans's decisions
  (020-01, section 14.1, 22:08 to 22:12) and his delegation of the rest
  (22:17): the API (`IndexBuilder` with one directory, one field per level,
  types `long`, `double`, `string`, `bytes`; a build's `Job` with three
  states; `deleteIndex` in one transaction; `UseIndexBuilder`'s `eq`, then
  a range or a prefix; `UsePrimaryBuilder` promoted); what each type
  accepts of a stored object; the reserved internal keys' layout
  (definitions as format-2 objects, entries per generation, cleanup
  markers) and the level encodings; maintenance with the read time fixed
  first; the jobs; the boundary; the fault map of F3 to F8 with a test for
  each; harnesses H2 to H4; nine steps for three agents, with the files
  each owns. Section 11 lists the decisions taken under the delegation.
  No code changed. Sections 6.1 and 6.2 describe the build and the
  cleanup as the code is since 020-18's fixes (020-23, V1-3).
* [11-known-issues.md](11-known-issues.md). 020-11, the known issues of
  2026.4: every fault and open question of 020-01 (sections 12 and 13),
  020-08, 020-09, 020-10 (section 8), 020-04, 020-07, the lists of 015,
  019 and 021 and the night's reviews, each with its state on `main`:
  fixed with its commit and the test that shows it (read and run), open
  with who has it, gone or not a fault, or Frans's question. Brought up
  to date until the release; since 2026-11-09, afternoon, with every
  fault that the day's bug hunts found and fixed (020-13 to 020-23, 021-11,
  021-12; its section 10) and what they left for a later release (its
  section 11); since the evening, to `03ce6ec`, with 021-13 to 021-27, Z1
  to Z3 and the late fixes, and the day's open questions and API wishes.
* [12-measurements.md](12-measurements.md). 020-12, format 2 measured,
  020-08's step 4, on a quiet machine (2026-11-09, 03:43 to 04:23):
  ObjectBench's M1 to M8 at `7231771` against format 1 at `ae68938`, and
  `performance.sh`'s quick suite against release 2026.3. A `Payment` is
  36 bytes against 71; the writer takes 0.29 to 0.66 of format 1's time,
  the read of bytes 0.16 to 0.74, a lookup 0.13 to 0.44, a get into
  `Payment` 0.70, a build 0.46; the Core unchanged (NO ALERTS). Two
  figures over 10 % worse, neither a fault: M4's get as `byte[]` (1.34,
  the JVM's state where ObjectBench runs it; alone 0.93) and a `w()` of
  one put at an object key (1.13, 020-10's I1 rule, by design).
* [13-test-study.md](13-test-study.md). 020-13, the test study before
  the release cut (Frans, 2026-11-09, 08:41: "So let's go bug-hunting"):
  the coverage of the unit and f-tests by JaCoCo (93.6 % of lines, 81.2 %
  of branches; the Pub layer's 2026.4 classes 95 to 99 % of lines), a
  sample of 47 faults planted by hand (43 of the 46 that a test can catch
  were caught; tests for the other three added), a bug hunt by probes and
  four sub-agents (format 2, scans and reads, the Javadoc's promises, a
  stress with restarts and crashes), and slow or duplicate tests that could
  go. Four bugs found and fixed in the study's clone, each with its test:
  an rw() that read two states of a key, an Error of a static initializer
  that failed the database in rw(), key replace that deleted another key's
  index entries, and a lost wake-up that made `BufferedStream.close()` wait
  a quarter of the buffer time; `Time`'s lenient parsing left for Frans.
  On `main` as `c950612`, `42201c2`, `3f61a74` and `4b520f9`, the three
  tests as `efe1bec`.
* [14-codex-review.md](14-codex-review.md). 020-14, a Codex review of
  2026.4's code (Codex CLI, GPT-6.1-Sol, effort max; Frans, 09:11), its
  report verbatim: three confirmed findings, X1 (high: key replace in an
  object key's directory left an index wrong), X2 (high: an `Error` of a
  Data Object class's static initializer failed the database in `rw()`)
  and X3 (medium: an inherited field of a package not exported passed the
  class check); each fixed with a test that failed first (`a03111e`,
  `987e734`, `ef6a3cf`), X1 by option (a), the refusal, which Frans
  confirmed (10:30).
* [15-kill-restart-harness.md](15-kill-restart-harness.md). 020-15, a
  kill-and-restart harness for the Pub layer (done): `KillRestartHarness`
  and `java/stress/kill-restart.sh`, a child JVM killed with SIGKILL
  during work on objects and indexes, each restart checked against what
  the promises allow; 2,993 kills and 78 stops, no fault of BergDB. One
  observation, KR-O1, a creation or deletion that returned can be undone
  by a crash before it is durable, said in the Javadoc (`f99f4c6`); a step
  of `night.sh`, 1,000 kills.
* [16-fuzzing.md](16-fuzzing.md). 020-16, fuzzing of the object format,
  the index keys and the index definitions: `FormatFuzzer`, six areas,
  each reader against its spec, and `java/stress/fuzz.sh`, a step of
  `night.sh`. Three low faults, each from data written through the Core,
  fixed: F16-1, a corrupt entry key gave a scan an
  `IllegalArgumentException`; F16-2, a value at a prefix's own key hid
  every index definition from a start; F16-3, a build failed over a key
  whose name holds a '/'. O16-1, a get of an object at a key with a
  suffix, fine as is for 2026.4 (Frans, 11:52).
* [17-harness-long-runs.md](17-harness-long-runs.md). 020-17, long runs
  of the Pub layer's randomized harnesses (H2 to H4 and the objects') on
  s1, with `java/stress/harness-soak.sh`, a step of `night.sh`: four false
  findings of `IndexJobsHarness` (H3-O1 to H3-O4), fixed, and the
  harnesses' blind spots read, the cheap ones closed (B1 to B17); no fault
  of BergDB.
* [18-index-concurrency-review.md](18-index-concurrency-review.md).
  020-18, the user indexes under concurrency, a review (Frans, 09:21): the
  shared state and its guards, 19 interleavings each with a verdict, and
  probes. Five faults fixed, each with a test: F1, F3, F4 and F5, medium (a
  build step that collided with writes of keys with a suffix under the
  manager's lock, a locked step of large values, a build that chased the
  writers appending to its directory, a cleanup whose work grew as the
  square of its entries), and F2, low (a deleted build's note); three
  observations for later (O1 to O3).
* [19-javadoc-against-behaviour.md](19-javadoc-against-behaviour.md).
  020-19, the public Javadoc checked against behaviour, promise by
  promise, for the classes that 2026.4 changed most, with
  `PubTesterJavadoc` (45 tests): one code fault (F1, a deleted build's
  note) and eight Javadoc faults (J1 to J8) fixed; Q1 (`Time`'s lenient
  parse) and Q2 (`WBuilder.execute()` twice), decided by Frans and done in
  020-21.
* [20-spotbugs.md](20-spotbugs.md). 020-20, SpotBugs 4.10.5 over 2026.4's
  code: 655 warnings kept and triaged, none a true defect; outside them,
  T1, a directory that cannot be listed (a `NullPointerException`, or a
  message that advised removing the database's files), fixed (`6db1ac3`);
  N1, `CryptoKey.getKeyData()` returns a copy, at Frans's decision
  (`a3bb07b`).
* [21-api-decisions-9-november.md](21-api-decisions-9-november.md).
  020-21, Frans's API decisions of 9 November (10:30: "1 to 5, all as
  recommended"), implemented, each with a test that failed first: a time
  string parsed strictly, `WBuilder.execute()` spends the builder, the
  small API faults and the Javadoc's corners, and the gate's check of the
  index threads; Q1, `Duration.seconds(NaN)` refused (Frans, 11:23); Y1 and
  Y2, two faults of the strict parse found by 020-23, fixed.
* [22-core-writes-and-pub-integrity.md](22-core-writes-and-pub-integrity.md).
  020-22, writes through the Core and the Pub layer's integrity, a study
  and a spec (Frans, 10:43): the key spaces that the Pub layer owns and
  their invariants; the rules W1 to W26 for writes through the Core, free,
  allowed with care or forbidden; the options, and Frans's decisions
  (11:13): A2, "Core is root, with a detection floor", the free space K2,
  W6 allowed with care, detection B1. R22-1 and an index scan's key with
  no ukey fixed; the rules written in five places, `Db`'s Javadoc first.
* [23-review-of-fixes.md](23-review-of-fixes.md). 020-23, independent
  reviews of the day's fixes (Frans, 11:57): Codex's round 2 (Y1, medium,
  and Y2, low, in the strict `Time` parse, fixed in 020-21); reviewer v1
  of the Pub layer's fixes (four low points on documents, V1-1 to V1-4,
  done in 020-21 and in the day's document update); reviewer v2 of the
  Core's (V2-1, a test, and V2-2, `BufferedStream.append` after its wait
  for room, fixed); Codex's round 3 (Z1 and Z2, high, and Z3, low, fixed;
  Z2's rule decided by Frans, 16:20); reviewer v2 of the late Core fixes
  (021-20 and U10's: sound, V5-1, a comment); Codex's round 4 (W1, high, a
  directory replaced during a file switch's force, fixed as 021-24); and
  reviewer v2 of 021-24 (sound; V7-1 and V7-2, wording, done).
* [24-new-user-apps/](24-new-user-apps/). 020-24, new users'
  applications of 2026.4, from 12:41, by coord-1109's agents (006-20 says
  how): a new user with only the release jar and the Javadoc writes a real
  application for one scenario, with an oracle of its own, and reports
  every fault, gap and unclear word; each file has its findings and a
  Fixes section with the commits on `main`; the larger faults became 021
  entries. Fifteen applications, in five rounds:
  * [01-event-log.md](24-new-user-apps/01-event-log.md). 020-24-01, an
    event log with time travel: U1-1, high, `transactionInfo()` during a
    write failed the database (021-13).
  * [02-inventory.md](24-new-user-apps/02-inventory.md). 020-24-02, an
    inventory with user indexes: no wrong result in 1.2 million checks;
    I-1 to I-8, the Javadoc and API wishes.
  * [03-concurrent.md](24-new-user-apps/03-concurrent.md). 020-24-03, a
    concurrent service, cache, counters and transfers: no wrong result;
    U3-1, `stop()`'s Javadoc, and U3-2 to U3-9.
  * [04-large-data.md](24-new-user-apps/04-large-data.md). 020-24-04, a
    catalogue larger than memory: no wrong result in 15 million values;
    U4-1 and U4-2, the cache budget and the heap, in the Javadoc.
  * [05-document-store.md](24-new-user-apps/05-document-store.md).
    020-24-05, a document store behind a small service: U5-1, critical,
    and U5-2, high, long keys overflowed the stack (021-16).
  * [06-metrics.md](24-new-user-apps/06-metrics.md). 020-24-06, a
    metrics service with expiring history: U6-1, `transactionInfo()`
    after reclaim (021-17); 136 million values checked, 36 crashes.
  * [07-encrypted.md](24-new-user-apps/07-encrypted.md). 020-24-07, a
    password vault on an encrypted database: U7-1, high, keystream reuse,
    and U7-3, no integrity: encryption out of 2026.4 (020-28).
  * [08-io-errors.md](24-new-user-apps/08-io-errors.md). 020-24-08, an
    append-heavy log store where the file system misbehaves: no hang, no
    wrong record; U8-1, a lost last stream file drops synced records
    silently, documented, its options for Frans.
  * [09-core-api.md](24-new-user-apps/09-core-api.md). 020-24-09, the
    Core API as an embedded key-value store: U9-1, a prefix scan (021-18),
    U9-3, a KV's time (021-19), and the Core API's Javadoc.
  * [10-lifecycle.md](24-new-user-apps/10-lifecycle.md). 020-24-10, many
    small databases, opened and closed all the time: U10-1, high, a
    directory deleted and made again (021-20); U10-3, U10-5, U10-6 fixed.
  * [11-reentrancy.md](24-new-user-apps/11-reentrancy.md). 020-24-11, a
    hurried service, reentrant calls and shared objects: U11-1 and U11-2,
    high (021-21 and 021-22).
  * [12-java-types.md](24-new-user-apps/12-java-types.md). 020-24-12, a
    domain model of Java types as Data Objects: U12-1, high, a put of a
    huge array (021-23); U12-4 for Frans.
  * [13-bulk-import-export.md](24-new-user-apps/13-bulk-import-export.md).
    020-24-13, bulk import and export: no bug (5 million records, kills
    during an import and during a commit of 1.88 GB); U13-1, U13-2, U13-3
    and U13-7 in the Javadoc.
  * [14-multi-tenant.md](24-new-user-apps/14-multi-tenant.md). 020-24-14,
    a multi-tenant backend with index churn in one database: no wrong
    result; U14-1, high, puts slowed by index churn under reclaim (021-25,
    fix (c)); U14-2 to U14-6, API wishes.
  * [15-docs-examples.md](24-new-user-apps/15-docs-examples.md).
    020-24-15, a new user who learns BergDB by copying the documentation:
    every example runs as documented; the findings fixed in the documents
    (U15-1 to U15-14 but U15-6 and U15-13); Q1 and Q2 for Frans.
* [25-javadoc-against-behaviour-rest.md](25-javadoc-against-behaviour-rest.md).
  020-25, the public Javadoc checked against behaviour, the rest of the
  Pub API after 020-19's classes: C1 to C3 (low) and J1 to J7 fixed with
  tests (`PubTesterJavadocRest`); Q1, a local time that summer time skips
  or repeats in `Time.resolve`.
* [26-index-model/](26-index-model/). 020-26, a TLA+ model of 2026.4's
  user indexes (writers with a read time, the virtual key, build steps,
  activation, deletion and cleanup, generations, crash and restart),
  checked with TLC: the safety invariants hold within small bounds,
  liveness under fairness in three runs; eleven planted faults caught; no
  design fault found.
* [27-core-api-javadoc.md](27-core-api-javadoc.md). 020-27, the Core
  API's Javadoc checked against behaviour: C1 to C3 (low) fixed, J1 to J6
  and K1 to K3, with tests; Q1, what the Core API is, named at the top of
  `Db`'s Javadoc, and Q2, a null or out-of-range argument refused with
  `IllegalArgumentException`, both at Frans's decision (16:20 and 16:27).
* [28-encryption-out-of-2026-4.md](28-encryption-out-of-2026-4.md).
  020-28, encryption out of 2026.4's API (Frans, 16:08 and 16:12, on
  020-24-07's U7-1 and U7-3): `DatabaseBuilder.cryptoKey()` and
  `CryptoKey` gone, the code kept internal and tested, an earlier
  release's encrypted database refused; done right later, 017-10.
* 29-index-proof/, on a branch, not merged: `020-29-index-proof` in
  `/Users/f/fl/bench/2026-11-09/clone-l29`. 020-29, a Lean proof, for
  every size, of 020-26 section 3's safety invariants (no `sorry`), in a
  wider model (several index names and directories, transactions of any
  keys), and liveness: cleanups end; builds end under strong fairness of
  the build thread, or under weak fairness with finitely many definition
  changes; weak fairness alone is not enough with several names (a model
  run shows it). 5,231 lines, head `9d33587`.
* [30-deleted-kvs-cost-nothing.md](30-deleted-kvs-cost-nothing.md).
  020-30, a deleted KV eventually costs nothing (Frans's rule, 2026-11-10):
  the index keeps the nodes of deleted keys for ever, so scans and the
  stream are not bounded by the live data (U16-1, U17-1, 021-25); the
  study and the fix. 2026.4 waits for it (Frans, 09:03).
* [31-release.md](31-release.md). 020-31, the release of 2026.4: commit A
  (`bb8da6d`, made again after its first night: main with 023-core merged,
  BuildInfo, two fixes of test races, two of corrupt streams, next.md and
  the docs), its night of 10 to 11 November on F53 and s1, and the morning's
  steps; the tag `release-2026.4`.


Log
===

2026-11-06. Created the item (Frans, 12:05), by coord-1106. The inventory
started the same day (agent v1, read-only).

2026-11-08. 020-02 to 020-06 checked and made ready for decisions on
object storage, at Frans's request (15:22), by coord-1108's agent d02:
the decisions in 020-02, section 4; the entries of 020-02, 020-04,
020-05 and 020-06 above brought up to date.

2026-11-08. Frans decided object storage, 15:51 to 17:09, one decision
at a time (020-02, section 4): no null in the stored format; format (f),
DbObject's table with Binson's values; binary search, no hash list;
names of 1 to 255 bytes; the header byte 0x82; arrays in Binson's
framing; one 64-bit integer; Binson's NaN rule as a must, −0.0 kept;
readers refuse ill-formed UTF-8; depth 16; old objects refused; the
format under 018-01's rule. These decisions are his approval of the
format's design under 018-01's rule; the spec, a subitem of 020, comes
to him for approval before the release.

2026-11-08. 020-07, the spec of stored objects (format 2, (f) as
decided) with its conformance vectors, and 020-08, the implementation
plan (six steps, about 5 days), drafted at Frans's request (17:12) by
coord-1108's agent s07; no code. The spec's questions Q1 to Q7 and the
plan's list of what Frans must say before it starts are for Frans.

2026-11-08. 020-10, the indexes' design for implementation, written after
Frans's decisions of 22:08 to 22:12 and his delegation of 22:17, by
coord-1108's agent; no code.

2026-11-08. 020-09, the conversion rules of Data Objects and `DbObject`s,
written at Frans's request (21:59), with what was left open decided
under his delegation of 22:17, by coord-1108's agent; 020-08 brought up
to date with it and with 020-10 (steps 7 and 8 added, step 5 dropped,
the order 1, 2, 7, 8, 3, 4, 6, about 7 days in all; `createFast()` left
to 020-10's step I2); a pointer in 020-02, section 5.1b. No code.

2026-11-09. 020-11, the known issues of 2026.4, written in night 006-15
from `main` at `fd6dd09` at the coordinator's request: twelve open rows
(the format-1 false positive for Strings, two Javadoc points, a String's
size checked after its encoding, N10's test outside `Pack`, B3, two low
points of 019-46's review, step 4's measurements, three item updates)
and six questions or approvals for Frans.

2026-11-09. 020-12, the measurements of 020-08's step 4, made on a quiet
machine in night 006-15 by the coordinator's agent C; 020-08 done.

2026-11-09. 020-13, the test study before the release cut, at Frans's
request (08:41), by the coordinator's agent in a clone of `main` at
`1d1b6f3`: four bugs fixed there with their tests, three tests for the
faults of its mutation sample that the gate missed, for the coordinator
to integrate.

2026-11-09. The bug hunts before the release candidate (Frans, 08:41:
"So let's go bug-hunting"; 09:21: "Start 1 to 4"), by coord-1109's agents,
each in a clone of its own: the test study (020-13), a Codex review
(020-14), a kill-and-restart harness (020-15), fuzzing (020-16), long
runs of the harnesses (020-17), a concurrency review of the indexes
(020-18), the Javadoc against behaviour (020-19) and SpotBugs (020-20);
then Frans's API decisions implemented (020-21), the rules for writes
through the Core (020-22) and independent reviews of the day's fixes
(020-23). Every fault found is fixed with a test, on `main` from
`a9e5488` to `b149d12`, with 021-11 and 021-12. The day's document update
by coord-1109's agent d27: 020-11 brought up to date (sections 10 and
11), 020-10's sections 6.1 and 6.2, `releases/next.md`, and the Javadoc
and comments of 020-23's V1-2 and V1-3.

2026-11-09, evening. The Files entries of 020-24 to 020-29 (020-29 on its
branch, not merged), and 020-11's and 020-23's brought up to date, by
coord-1109's final items pass.

2026-11-10. Release 2026.4 paused (Frans, 09:03: "My decision is to pause
2026.4 until this has been sorted out."): the index keeps the nodes of
deleted keys, so a scan's cost and the stream's size grow with every
delete (020-24-16, 020-24-17, 021-25). 020-30 created with Frans's rule
that a deleted KV eventually costs nothing; its study started. The
candidate `03ce6ec` is not tagged.

2026-11-11. Release 2026.4 made: the tag `release-2026.4` on `bb8da6d`,
after a clean night (020-31).
