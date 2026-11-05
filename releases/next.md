Notes for the next release
==========================

What the release notes of the next release after 2026.2 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.2](2026.2/readme.md) has them under its changes, and
empties this file.


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
