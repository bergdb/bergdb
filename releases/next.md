Notes for the next release
==========================

What the release notes of the next release after 2026.2 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.2](2026.2/readme.md) has them under its changes, and
empties this file.


Reliability
-----------

* **Reclaim's pSafe is the stream length after the call's own records**
  (bergdb 015-54, 016-06's R7-F5; 2026-11-05). The cut waits until the
  startup pos has passed an iteration's pSafe. `Reclaim` set pSafe to the
  end of the user transaction's record, read before the internal records
  that the same call appends before the marking (an iteration's table, a
  step, the table of an iteration done), whose takes can keep nodes dirty
  that the wait is for; it is now the stream's length when it is set, after
  them, as its Javadoc says. Cuts come a little later; no harm was shown
  before. The format is unchanged; the stream's bytes change with reclaim
  on (the table's pSafe values, and where cuts come): StreamDigest's
  decided digests differ from 2026.2's in its 4 configurations with
  reclaim (`l3-*`, 12 of 36), and are 2026.2's in the 8 without. The new
  reference is in 015-54's `digests-new.txt`.


Documentation
-------------

* **DbObject and user indexes are experimental** (bergdb 018-01, D2 and D6,
  W1; 2026-11-05). The Javadoc says that they are experimental in 2026.3,
  with known faults, and may change in a later release:
  `Database.indexBuilder` and `deleteIndex`, `Connection.useIndex` and
  `usePrimary`, the interfaces `IndexBuilder`, `UseIndexBuilder` and
  `UsePrimaryBuilder`, and a value that is neither a `String` nor a
  `byte[]`: `put(Object)` (`WBuilder`, `RwEnvironment`), a put of an object
  at a key (`Connection`, `WBuilder`, `RwEnvironment`) and a get into
  another class (`Connection`, `ReadInterface`, `RwEnvironment`); also
  `Database.PRIMARY`, `StartupInfo.getStartupJobs()` (the index jobs a
  start resumes), and `DbObject` and `DbArray` (`bergdb.pubimp`), and the
  exceptions `IndexAlreadyExistsException`, `NoSuchIndexException`,
  `MissingKeyFieldException` and `ObjectCreationException` say that they
  belong to these parts (Frans, 2026-11-05, 10:31). So do the Pub API's
  overview, `bergdb.pub`'s package description, README.md and
  docs/levels.md, section 1. Their tests still run in `before-commit.sh`.
  The notes say it in "What it is" and in the known issues, as 2026.2's say
  it of replication; their faults are those of 018-01, section 3.2.
