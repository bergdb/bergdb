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


R4. A safety belt is decided case by case
-----------------------------------------

Beyond R1 to R3, the database may refuse more, to catch a likely mistake
of the user's code early, where that is cheap and documented. Such a
safety belt is not part of the database's integrity (P14, R3): each is decided
by Frans, case by case.

Why: the spoiled builder of 024-27 (Frans, 2026-11-12, 07:36: "B. Ensure
the behaviour is clear in the Javadoc."), set beside QR1, where an rw()
action got no such belt because its code is the user's (R3).

Cases:

* 024-27, U26-5: a refused call spoils a Pub `WBuilder` and a Core
  `Trans.Builder`: their execute() then throws and writes nothing, and
  so does every later call (tests `PubTester.testRefusedCallSpoilsWBuilder`,
  `Trans.testRefusedCallSpoilsBuilder`).
* 024-27, QR1: no belt for an rw() action (R3).

Open: a safety belt can stop code that is correct by R3, such as a
builder used to try keys and skip those refused. 026-02's public key check
would let such code test a key before the call instead of catching.
