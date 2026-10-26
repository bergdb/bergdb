005-50. Fix the start with another node size
=============================================

Status: open. Kind: fix. Created 2026-10-26.

Found in 005-38 ([report](38-writes-at-scale/report.md), section 6), by a
subagent (Claude, Opus 5.5) measuring node sizes; registered at Frans's
request (2026-10-26: "Yes to node-size fix entry. For now, it should fail
with a good error message. This should be the scope. Other options are
interesting, but later and in some other item.").


The issue
---------

A database starts only with the node size it was written with
(`DbBuilder.maxNodeSize8()`, `14()`, `30()`, `62()`; 30 by default). The
size is not in the stream. Started with another size, the rerun of the
startup section splits nodes differently, and the start fails with an
error that looks like a corrupt stream:

    StreamFormatException: startup error, node 1545529:1545529 not found,
    got dirty in trans tt=172, tpos=1545504; startup pos 1412496, time 174;
    in node table: no

All 12 pairs of 8, 14, 30 and 62 fail so; the same size starts and reads
every key back (`38-writes-at-scale/node-size/RestartNodeSize.java`, its
output `38-writes-at-scale/node-size/out/restart-check.txt`: 20,000 keys,
a startup section of about 1 MB). A startup section with no splits in it
might start, and then the database runs with the other size; not tested.


The scope
---------

Only this: a start with another node size than the stream was written with
fails with a clear error, which says that the node size differs, both
sizes, and what to do (start with the size the database was written with).
Allowing a change of node size, or making the size a property of the
stream that the builder need not set, is not part of this entry (Frans:
"later and in some other item").


Questions
---------

1. Where the written size is kept. The meta block has 83 reserved bytes,
   zero (`MetaBlock`, offset 44): the node size there, with 0 for streams
   written before the fix, which then start as today. Or in a record.
   Which needs a new `MetaBlock` version (005-40's `VersioningStreamException`)
   and which does not?
2. The error's type: a new exception, or `DbException` with a message;
   what the Pub API (`DatabaseBuilder`) shows.
3. Is a start with another size ever safe today (a startup section with no
   splits)? The fix refuses it anyway, if the size is known.


Done when
---------

A start with another node size fails with the clear error before it
writes anything (as 005-40's checks), with a test for every pair of sizes;
a stream written before the fix starts as today; `before-commit.sh`;
StreamDigest identical on the standard sets but for the bytes that hold
the size, if any; the Javadoc of the `maxNodeSize` methods says that the
size must stay the same for a database.


First step
----------

Run `RestartNodeSize` against the main tree's jar to confirm the failure,
and read how `DbStarter` and `MetaBlock` read the meta block before the
rerun, to answer question 1.


Size and order
--------------

S. Independent of the others.
