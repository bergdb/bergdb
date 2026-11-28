Created 2026-11-12 by Frans Lundberg



010-04 Rules
============

BergDB's rules: more detailed than the principles (010-01), more likely to
change, and closer to the implementation, but valid for every
implementation of BergDB (Java, C, and languages to come). The principles
are few and stable; the rules are many (up to about 100) and grow from
Frans's decisions: when a decision sets a precedent, it is written here as
a rule, in his words, with the cases it decided (Frans, 2026-11-12, 09:58:
"Principles should be few (10 or so) and stable. And not dependent on
detailed implementation. [...] We can allow more rules (perhaps up to
100), more detailed. More likely to change. More coupled with the
implementation. They should still not be too detailed. Most of them are
applicable to all implementations, Java, C, and future supported
languages.").

A rule is named R1, R2 and so on; elsewhere, write `010-R1`; in code
comments, `bergdb 010-R1`. A rule's number is stable: never reused, gaps
not filled, as for the principles. A rule's statement names concepts (a
call, a transaction, an index), not one implementation's classes; its
cases name the classes where it was decided. The Javadoc and the
specifications cite a rule; a rule does not quote them.

010-04 and not 010-03: 03 was used and removed on 2026-10-27 (the item's
Files), and a number is not reused.


R1. A refused call changes nothing
----------------------------------

A call that the database refuses, for its arguments or for a limit, leaves
the database and the transaction being built as they were before the
call; the database goes on. Every check of a call is made before the call
changes anything.

Serves P14 and P7.

Why: P7 already says it of a transaction ("A refused transaction is
another matter: it changes nothing, and the database goes on"); R1 says it
of each call within one, so that the user's code can know exactly what a
refusal did: nothing.

Cases:

* 024-27, QR1 (Frans, 2026-11-12, 09:34): a put or a delete refused in an
  rw() action changes nothing in the transaction; `RwEnvironment`'s
  Javadoc, "Refused calls".
* 024-24 (the limits L1 to L6): each limit is checked before anything is
  written.


R2. A commit holds all of its accepted calls, or none
-----------------------------------------------------

A transaction is committed whole, with every call that was accepted into
it, or not at all. There is no commit of a part of what the user's code
handed to the database for one transaction.

Serves P14.

Why: the database promises it to the user (the Pub package: "all of them,
or none"), and the user's code can build on it.

Cases:

* The Pub API's w(): "puts and deletes several keys at once: all of them,
  or none" (the `bergdb.pub` package Javadoc).
* An rw() action: what it wrote is committed only after it returns
  normally; an action that throws commits nothing (020-24-11, U11-7;
  `Action.run()`'s Javadoc).


R3. The database keeps its own structures consistent; the user owns what her keys mean
--------------------------------------------------------------------------------------

Whatever the user's code does through the Pub API, catching the
database's exceptions and going on included, the structures that the
database makes stay consistent: the stream, the Core's index, the Pub
layer's directories and objects, and the indexes the database creates.
What the user's own keys mean together, such as an entry she writes as an
index of her own, is the user's responsibility: the database neither
checks nor repairs it.

Serves P14: R3 draws its line between the database's integrity and the
user's responsibility.

Why: Frans, 2026-11-12, 09:16: "In general, the rule is that use of the
Pub API must keep the integrity of the database. Including features in the
pub layer. This includes indexes. But only indexed created by the database
itself. This is not the case in the example above where the database user
creates an index entry herself. Also in general; the user is responsible
for the code in Action. The example code is bad as it is. It is broken. But
the database is not broken." The same rule in 2012 (010-02, "The Pub
API"): "The user of this layer cannot destroy the integrity of the
database."

Cases:

* 024-27, QR1 (Frans, 2026-11-12, 09:34: "Keep as is, ensure its in the
  Javadoc."): an rw() action that catches a refused put and returns
  normally commits its other writes. The database's index entries are made
  after the action returns, from what it wrote, so they stay consistent;
  the action's own index entry is the action's.
* 020-24-11, U11-7: an rw() action that catches an
  `ObjectCreationException` from a get and goes on commits what it wrote
  (`RwEnvironment.get()`'s Javadoc).


R4. Removed
-----------

R4, "A safety belt is decided case by case", was removed on 2026-11-12,
10:19 (Frans: "Remove Rule R4."), minutes after it was written. Its number
is not reused.


R5. The Core API never destroys the KV store
--------------------------------------------

A call of the Core API, whatever its arguments, keeps the integrity of
the Core's key-value store: a caller's mistake, such as a position that
is not a transaction's, is refused with an exception to the caller, and
the database goes on. The Core API may break what is built on it (the Pub
layer's directories, objects and indexes are keys and values to it, P14),
but not the store itself: its stream, its index, its availability. A
database fails (P7) for damage, a failed environment or a bug, never for a
caller's misuse of an API.

Serves P14 and P7.

Why: Frans, 2026-11-12, 13:21: "I consider it a bug. It does destroy the
Core database, the KV store. The Core API may damage the integrity of the
functionality built on top of it such as Pub layer's secondary indexes,
but it should not destroy the integrity of the KV store itself." The
same rule for arguments, earlier: a bad argument of the Core API is
refused with `IllegalArgumentException` (020-27, Q2).

Cases:

* 021-27: `Db.getTrans` at a position inside a record failed the
  database; refused with `IllegalArgumentException` since 2026-11-12
  (without a walk; above 1 MiB a walk of the record headers confirms
  a record's start before its array is made, Q27-1).
* CA3 (024-37): a Core put under the Core's own keys
  (`/#i/dreclaim/-settings.txt`) made every later start fail; refused
  since 2026-11-12, `/#i/-dummy` and `/#i/dreclaim/` reserved to the Core.
* A value transformation (Core API) that throws, or whose result passes
  8 MiB, fails the database in 2026.5: to change in 2026.6 (Frans,
  2026-11-12, 14:42: "Yes to R5 and for 2026.6. I don't see it as a
  bug, but something to change anyhow."; 026's readme). Done since
  2026-11-13 (026-06): the value transformations run before the go point,
  and one that throws or passes a limit refuses the transaction; so does
  a key transformation that throws (Frans, 08:45, "yes to all").


R6. The storage owns the integrity of the bytes
-----------------------------------------------

BergDB assumes that its storage returns the bytes appended to it, and
that after a crash the stream is a prefix of them, with one expected
fault: a partial append, which leaves at the stream's end a part of what
was appended, or zeros in its place within the file's length. A start
handles that fault exactly: it takes every record that ends before it
and none after it. Any other damage of the stored bytes is the storage's
to prevent. BergDB's checks of it are a best effort, kept where they
cost little; damage that they do not see gives wrong values with no
error. A check that finds damage refuses the start or fails the database
(P7); none repairs it.

Provisional until 028-77 is decided (Frans, 2026-11-28): the rule states
the fault model as it is today, a prefix with a partial append or zeros
in its place, and 028-77 with its review (035-03) reopens that model:
what a crash may leave, who handles it, and whether a start may rewrite
the stream's tail.

Serves P7 and P13.

Why: BergDB assumes correct storage (Frans, 2026-11-06; 017-08), and its
detection of damaged bytes is a best effort, a low priority (Frans,
2026-11-12; 024-28, section 7). The two were stated in part in several
places and in no one place; 031-07's review of the stream's checks
proposed the wording (its inventory, section 5.4), and Frans decided it
as a rule, not a principle (2026-11-28).

Cases:

* 014-01 (prefix interruption, 2026-11-05).
* 015-73, 019-30, 019-31 and 019-33: damage outside the fault, decided
  (a) (2026-11-05 and 2026-11-06).
* 024-25: the node checksum, CRC-32C, a best effort kept for its cost;
  kept again by 031-07's N1 (2026-11-28).
* 028-60: zeros within the file's length, a face of the fault
  (2026-11-26).
* 028-67: another file's bytes within the length, refused with the cause
  and tied to their place (2026-11-27). Whether such a tail becomes a
  face of the fault, cut and not refused, is 028-77's (028-67's C2,
  held, 2026-11-28).
* 031-07: each check of the stream against the rule (its inventory,
  sections 4 and 5.4).
