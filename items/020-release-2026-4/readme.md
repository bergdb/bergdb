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
  No code changed.
* [11-known-issues.md](11-known-issues.md). 020-11, the known issues of
  2026.4: every fault and open question of 020-01 (sections 12 and 13),
  020-08, 020-09, 020-10 (section 8), 020-04, 020-07, the lists of 015,
  019 and 021 and the night's reviews, each with its state on `main`:
  fixed with its commit and the test that shows it (read and run), open
  with who has it, gone or not a fault, or Frans's question. Brought up
  to date until the release.
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
