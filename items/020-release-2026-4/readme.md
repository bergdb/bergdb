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
