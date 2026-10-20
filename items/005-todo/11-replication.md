005-11. Replication: study it, for Frans to decide
=================================================

Status: open. Kind: decide. Created 2026-10-20.


The question
------------

In Frans's words (2026-10-20): replication, "we should either remove it
or implement it fully. Not sure where we are with this." The work is to
study the existing implementation and its tests, and to give Frans the
material to decide. Likely options: remove the feature; make sure it works
and that its testing is complete; change its design.

Found in 005-10, where the Pub API's replication methods came up as
unused (G1): nothing in the repository calls `Database.addReplica`,
`removeReplica`, `getStorageInfos` or `DatabaseBuilder.replica`. They stay
until Frans decides here.


What is known (2026-10-20, from a first look in 005-10)
-------------------------------------------------------

* Replication is local: a replica is another `AppendOnlyStream`, for
  example a `FileStream` in another directory or on another disk. Nothing
  goes over a network.
* `StorageManager` (storage/) writes every append to the main storage and
  to every replica, each behind its own `BufferedStream`. A replica can be
  added while the database runs (`addReplica`; a thread copies the main
  stream into it, `syncReplica`) or removed (`removeReplica`). At startup
  the storages are synced: the longest stream wins and the others are
  appended to from it (`syncStreams`). A STRONG sync also waits for the
  replicas (D2, `syncStrong`); docs/levels.md describes ORDINARY and
  STRONG.
* With reclaim: a cut (`pretruncate`) goes to every stream; a replica that
  is added later starts at the main stream's first position
  (`seekFirstPos`).
* Reads come from the main storage only; there is no failover to a
  replica (a comment in `StorageManager.read` names it as a possibility).
* Tests: about ten unit tests in `storage/StorageManagerTester` (add a
  replica, also while appending; remove one; sync). In the core, only
  `DbTester.testBadReplica1` (the error path of `Db.addReplica`). None
  through the Pub API, none with reclaim's cuts, restarts, crashes or
  eviction. docs/levels.md and docs/level3-durability.md say that
  "replication with cuts" is not established. The Lean model has no
  replicas.


Questions for the study
-----------------------

1. What the code does, in full: `StorageManager` (main and replicas, the
   rules D1 and D2, errors, statuses), `DbHelper.AddReplicaClass`,
   `Db.addReplica` and `removeReplica`, `DbBuilder.stream` with more than
   one stream, and the Pub API's methods. Which parts are 2017 code that no
   2026 work has touched?
2. What the tests cover, and what they do not: the existing tests, run
   and read; then the combinations that matter: a replica with reclaim's
   cuts (and a replica added after a cut), a restart from a replica (the
   main storage lost), a crash in the middle of `syncReplica`, a replica
   whose writes fail, replicas with eviction (reads load from the main
   storage), a STRONG sync with a slow replica.
3. Does it work? Small probes for the combinations of 2, on a scratch
   clone, before any change.
4. What the theory says: is a replica a byte copy of the main stream at
   every durable point (docs/prior-art.md speaks of byte-identical
   replicas by T2)? What would the Lean model need, if anything?
5. What each option would take: remove (what goes: the API, the core, the
   storage manager's multi-storage code, the rules D1 and D2, the
   documents), make it complete (the tests of 2, fixes, documents, maybe
   gate steps), change the design (for example failover for reads, or
   replication as a separate process that copies the stream).
6. What it is worth: who would use local replicas, against copying the
   files, a file system's or a disk's own mirroring, or a replication
   over the network.


Done when
---------

A report (a subitem here, or an item of its own if it grows): what the
code does, what the tests cover, what the probes showed, and the options
with their cost and value, for Frans to decide. Then his decision is
recorded here; carrying it out is a following entry.


First step
----------

Read `StorageManager` and `StorageManagerTester`, and run the tests;
then write the probe of a replica with reclaim's cuts.


Size and order
--------------

M: reading and probes, some machine time. Independent of the other
entries; before 005-05's decision on publishing, as the API offers it.
