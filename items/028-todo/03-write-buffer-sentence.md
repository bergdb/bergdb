028-03. Fix: the package's write buffer sentence
================================================

Status: done (2026-11-13). Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: bergdb.pub's package.html, "Good to know", says each started
database holds a write buffer of 10 MB.

Why: since 026-07 it is 64 KiB, growing to 10 MB while it writes fast and
back after 2 idle seconds; a user sizes the heap for many databases from
it.

Frans: none.

Done when: the sentence says so, as
`DatabaseBuilder.startupDistanceInMb()` does, and names the cache budget
(a fifth of the heap by default, for each database) as what many databases
in one JVM must set.

First step: the sentence and `DatabaseBuilder`'s paragraph side by side.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-1).

2026-11-13. Done by an agent of coord-1113, in the commit "028-03, 028-05, 028-06: the write buffer, the transformations and
maintain() in the Javadoc (documentation only)" on branch 028-jdoc:
bergdb.pub's package.html, "Good to know", now says that the write
buffer is 64 KiB at the start, up to 10 MB while the database writes
faster than the storage takes the writes, and back to 64 KiB after 2
idle seconds (`BufferedStream.INITIAL_CAPACITY`, `shrinkDelayMs`,
`StorageManager.DEFAULT_BUFFER_SIZE`), about 0.7 MB of heap in all for
a small file database, as `DatabaseBuilder.startupDistanceInMb()` says;
and that many databases in one JVM must set the cache budget, a fifth
of the maximum heap each by default (`DatabaseBuilderImp`), linking
`DatabaseBuilder.cacheSizeInMb()`. `java/javadoc-pub.sh` printed
`JAVADOC PUB OK`; `java/before-commit.sh` printed `BEFORE COMMIT OK`.
