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
  best effort.


Log
===

2026-11-06. Created the item (Frans, 12:05), by coord-1106. The inventory
started the same day (agent v1, read-only).
