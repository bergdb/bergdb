015-todo
========

Created 2026-11-03 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.

It continues 005-todo with a new numbering: the next entry is 015-01, not
005-84. An entry closely related to a 005 entry may still be added to 005,
for now.


The list
========

Two tables: what is left to do, and what is closed. A subitem's own
`Status:` line is the source. When an entry closes (done, dropped or
moved), its row moves from Open to Closed in the same edit, with the date
it closed; Closed is newest first. Files stay where they are, so links to
them keep working.


Open
----

| ID | Kind | What | Status |
|---|---|---|---|
| [015-01](01-empty-directory.md) | Fix | A directory without its stream starts as a new one | in progress |
| [015-02](02-c-follows-2026-2.md) | Implement | The C clone follows 2026.2's Java changes | open |
| [015-03](03-lean-follows-005-79.md) | Implement | Lean follows 005-79's integer take | open |
| [015-04](04-deps-helper-rule.md) | Investigate | deps.py counts take and dither as test code | open |
| [015-05](05-empty-or-missing-directory.md) | Decide | A start on an empty or missing directory creates a database | open |
| [015-06](06-refused-start-leaves-file.md) | Fix | A refused start leaves an empty first stream file | open |
| [015-07](07-node-fields-unchecked.md) | Fix | A node's inner fields unchecked; such a read does not fail the database | open |
| [015-08](08-streamdigest-compare-cut.md) | Fix | StreamDigest's compare reports the physical cut, which depends on timing | open |


Closed
------

| ID | Kind | What | Status | Closed |
|---|---|---|---|---|

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation), Implement (a
decided change).


Files
=====

* [01-empty-directory.md](01-empty-directory.md). 015-01, Fix: a database
  directory whose stream files are gone, or whose only file is empty,
  starts as a new, empty database; options A to G; A with A+ chosen.
* [02-c-follows-2026-2.md](02-c-follows-2026-2.md). 015-02, Implement: the
  C clone follows 2026.2's Java changes (005-79, 005-69, 005-78).
* [03-lean-follows-005-79.md](03-lean-follows-005-79.md). 015-03,
  Implement: Lean's take follows 005-79's fixed point (optional).
* [04-deps-helper-rule.md](04-deps-helper-rule.md). 015-04, Investigate:
  `deps.py`'s helper rule counts `TransSeq.take` and `dither` as test code.
* [05-empty-or-missing-directory.md](05-empty-or-missing-directory.md).
  015-05, Decide: 015-01's case 3, a start on an empty or missing
  directory; B1 (`createIfMissing()`) recommended for after 2026.2.
* [06-refused-start-leaves-file.md](06-refused-start-leaves-file.md).
  015-06, Fix: a refused start leaves an empty `00000000000000.bergdb`.
* [07-node-fields-unchecked.md](07-node-fields-unchecked.md). 015-07, Fix:
  the node parsers do not check their inner fields; a read that meets one
  throws an unchecked exception and the database stays active.
* [08-streamdigest-compare-cut.md](08-streamdigest-compare-cut.md).
  015-08, Fix: `StreamDigest compare` reports the physical cut's fields,
  which differ between runs.


Log
===

2026-11-03. Created the item, at Frans's request, to continue 005-todo
with a new numbering. Entries closely related to a 005 entry may still go
to 005, for now.
