014-stream
==========

Created 2026-11-03 by Frans Lundberg. Status: open.

Define BergDB's stream format and the contract between append-only stream
storage and the database. In Java the byte-storage interface is
`bergdb.stream.AppendOnlyStream`; transaction framing and serialization
are supplied by the layers above it.

This item owns the investigation and eventual specification, beginning
with startup correction promoted from 005-83. It does not yet adopt a new
format, change the interface or extend the supported crash model.


Scope
=====

* The storage interface: byte positions, reads, appends, concurrency,
  failure state, durability/acknowledgement and optional front reclaim.
* The stream format: identity and versioning, meta blocks, transaction
  framing, node encodings and integrity checks; Java/C compatibility.
* Startup's contract: permitted crash outcomes, how to recognize them,
  correction using appends, refusal conditions and repeated crashes.
* Interaction with bounded startup, reclaim, encryption and replicas.

Specify what storage must guarantee separately from what database recovery
can correct. A successful append, a committed transaction and a durable
transaction are different events. Preserve the append-only abstraction;
any proposed exception must be explicit and justified.


Files
=====

* [01-correction.md](01-correction.md). 014-01, stream correction: the
  discussion, historical evidence from F1-007, terminology, possible
  recovery contracts and the decisions/tests still needed; open.


Related work
============

* 005-83, original bug and power-loss experiment: retained at its existing
  location so its evidence, runner and old references remain usable. Its
  correction/format investigation now belongs to 014-01; moved is not fixed.
* 005-82, live `getTrans` errors that leave the database active: a separate
  fix, not permission to skip corruption during ordinary reads.
* 005-47, written-without-force durability; 005-11, replication; 007,
  startup bounds; 010-01, principles P2, P5 and P7.
* 012-02, the Java format at its recorded reference commit: existing
  implementation documentation and the basis of the C clone, not a
  proposed replacement specification.
* F1-007, read-only archive of the original documents and Git history.


Log
===

2026-11-03. Created at Frans's request as the home for stream format and
storage/database interface work. Added 014-01 after searching F1-007's
old notes, ODT drafts and the original Git bundle read-only. Promoted
005-83's investigation without moving its reproducible artifacts. Added
an item reference in AppendOnlyStream's Javadoc; no executable change.
