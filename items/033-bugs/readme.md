033-bugs
========

Created 2026-11-20 by Frans Lundberg. Status: open.

The register of released bugs: faults in the code of a published release
of BergDB, one entry each, with a stable ID `RB-nnn`. For judging
BergDB's stability over its releases, how buggy or bug-free it is; later
also for users. It starts with release 2026.5, the first public release
of the 2026 era (Frans, 2026-11-20).


Rules
=====

Decided by Frans, 2026-11-20.

* **A released bug** is a fault in the code of a published release: the
  release does what its notes, its Javadoc or its contract say it does
  not, such as a lost or wrong value, a failed database, or a refusal it
  should not make. Not a released bug: performance, the wording of a
  document, a fault only in the tests or the harnesses. A fault known at
  the release, named in its Known issues, is a released bug too.
* **IDs** are `RB-001`, `RB-002`, ..., in the order of registration;
  never reused. Cite as `RB-001` (in code comments `bergdb RB-001`).
* **Severity**, the worst a user can meet:
  * S1: data lost or wrong;
  * S2: the database fails or will not start;
  * S3: a call fails or refuses wrongly, with no damage;
  * S4: minor.
* **An entry** has: what a user sees (one or two sentences, for users);
  severity; the releases with the bug and the release that fixes it;
  when and how it was found (review, AI-user apps, the C port, a harness,
  a proof, a user); known at the release or not; the fix's commits; the
  item with the details.
* **Kept current:** the commit that registers a fault of a released
  version (an entry in 028, a release item's subitem) or that fixes one
  adds or updates its entry here. A release's steps check this register
  before its tag (026's release steps), and its notes name the released
  bugs it fixes by ID.


Counts
======

Released bugs by the release they were found in, counting each bug once,
in the first published release that has it. Updated with each entry.

| Release | S1 | S2 | S3 | S4 | All |
|---|---|---|---|---|---|
| 2026.5 | 0 | 2 | 0 | 0 | 2 |


Released bugs
=============

RB-001. A value transformation that throws or passes 8 MiB fails the database
------------------------------------------------------------------------------

* **What a user sees:** a value transformation (Core API) that throws, or
  whose result is over 8 MiB, fails the database instead of refusing the
  transaction. A restart has the state before that transaction; nothing
  committed is lost.
* **Severity:** S2.
* **Releases:** 2026.5 (and 2026.4 and before); fixed on `main` for 2026.6.
* **Found:** before release 2026.5 (024-24, QL6; 015-51); known at the
  release, named in 2026.5's Known issues. Counted a bug by Frans,
  2026-11-20.
* **Fix:** 026-06 (`a5c67ba1`, `11a9ef81`), 2026-11-13: the transaction
  is refused with a `DbException` and the database goes on (010-04, R5).


RB-002. A key transformation that throws fails the database
-----------------------------------------------------------

* **What a user sees:** a key transformation (Core API) that throws a
  `RuntimeException` fails the database instead of refusing the
  transaction. A restart has the state before that transaction.
* **Severity:** S2.
* **Releases:** 2026.5; fixed on `main` for 2026.6.
* **Found:** 2026-11-13, by the review of the code while fixing RB-001
  (026-06, Q2); not known at the release.
* **Fix:** 026-06 (`b159cd30`), 2026-11-13: refused with a
  `DbException`, as for RB-001.


Log
===

2026-11-20. Created the item, with its rules (Frans), from release 2026.5.
Registered RB-001 and RB-002, both fixed by 026-06.
