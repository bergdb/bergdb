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
  best effort; question 1b, whether BergDB stores null.
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


Log
===

2026-11-06. Created the item (Frans, 12:05), by coord-1106. The inventory
started the same day (agent v1, read-only).
