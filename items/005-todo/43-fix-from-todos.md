005-43. Fix: two leftovers of TODO markers: getTrans past the end, and a bad directory
=====================================================================================

Status: done (2026-10-25). Kind: fix. Created 2026-10-25.

Found in the review of the TODO markers in `java/` (006-05, T4 and T13) by
Claude (Opus 5.5, Claude Code); added and fixed at Frans's request ("as
proposed"). It was proposed with a third, T14, `RecoverableStream`'s
reference to `bergdb.core`, which 005-40 did the same morning, the same
way.


The issue
---------

**`Db.getTrans` past the end.** Under a "TODO D." of 2016: "DbException or
something else?". `getTrans(tpos)` reads the transaction at a position:
for the Pub API's `Connection.transactionInfo()`, the one that a get gave.
Since 005-34 it refuses a position that cannot start a transaction
(negative, not a multiple of 8, in a meta block) with an
`IllegalArgumentException` before it reads. A position at or past the end
of the stream got past those checks, and the iterator found nothing there:
a `DbException`, "could not find transaction at stream pos 384". The Pub
API never passes one; a caller of the core API that does got another
exception for the same mistake.

**A bad directory.** Under a "TODO LATER" of 2014 in `PubKeys`: "Review
what exception to throw? Make it consistent. Consider throwing
IllegalArgumentException or subclass of it." A bad key (`PubKeys.u2i`, in
every get and put) and a bad ikey (`i2u`) give `IllegalArgumentException`;
a bad directory (`udir2idir`: null, empty, without `/` at the end, or with
`//`) gave `BadFormatException`, which is not one. So the Pub API's
`IndexBuilder.dir` and `UsePrimaryBuilder.dir` threw it for a bad
directory, beside `IllegalArgumentException` from the other checks of the
same builders, and neither Javadoc said so. `BadFormatException` is
otherwise for stored data that does not parse (`DbObject` and its
fields).


The fix
-------

* `Db.getTrans` refuses a position at or past the end of the stream with
  an `IllegalArgumentException`, as the others: "Not a position of a
  transaction, 384: at or past the end of the stream." Nothing is read, as
  before. The Javadoc's `@throws DbException` goes.
* `PubKeys.udir2idir` throws `IllegalArgumentException`, with the same
  messages. Its Javadoc, `IndexBuilderImp.dir`'s, and those of the Pub
  API's `IndexBuilder.dir` and `UsePrimaryBuilder.dir` say so. What the Pub
  API throws changes, for a bad directory only.
* The two TODOs go.


Done when
---------

* Unit tests that fail without the change.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), as proposed:

* The fix as above, in `Db.java`, `PubKeys.java`, `IndexBuilderImp.java`,
  `IndexBuilder.java` and `UsePrimaryBuilder.java`. docs/levels.md's
  sentence on `getTrans` names the end of the stream.
* `DbTester.testGetTransRefusesBadPositions` has three more positions: the
  end of the stream, 8 past it, and 200,128, which pass the other checks;
  without the change it fails with the `DbException` at 384.
  `PubKeys.testUdir2idirRefusesBadDirs`: null, "", "/a", "a" and "/a//b/"
  throw `IllegalArgumentException`, and "/a/" and "/a/b/" convert; without
  the change it fails with the `BadFormatException`.
* `before-commit.sh` passes, 1,018 unit tests and 67 f-tests, on `98ac9eb`
  with 005-40 and the comment changes of 006-05, all uncommitted at the
  time.

The stream is unchanged: neither change writes.
