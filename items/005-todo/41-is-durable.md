005-41. Decide: isDurable(), whether a transaction is durable, without a wait
=============================================================================

Status: open. Kind: decide. Created 2026-10-25.

Frans's idea of 2026-10-13, kept until now as comments in the Pub API's
`Transaction` and `Connection`. Moved here at Frans's request ("as
proposed"), from the review of the TODO markers in `java/` (006-05, T10
and T11), by Claude (Opus 5.5, Claude Code); the comments are gone from
the code.


The idea
--------

In `Transaction`, in full:

    TODO LATER. Idea, 2026-10-13 (Frans): isDurable() and
    isDurable(SyncLevel), returning at once whether this transaction has
    attained the sync level. A non-blocking companion to sync(): commit
    now, ask later. Cheap to implement: StorageManager already tracks the
    durable stream length per level (d1Size, d2Size); compare with the
    transaction's last position. Same idea in Connection.

In `Connection`: "isDurable() and isDurable(SyncLevel) for the last
transaction started with this connection, as for sync(). See the same
idea in Transaction."

005-11 has it among its material on durability and the API, as an answer
without a wait.


Today
-----

* A commit returns before its bytes are durable. To wait, the application
  calls `Transaction.sync(level)`, `Connection.sync(level)` (the
  connection's last transaction) or `Database.sync(level)` (the last
  transaction written); `sync()` is ORDINARY.
* `StorageManager` keeps the durable lengths: d1Size, ORDINARY, the main
  storage's confirmed length; d2Size, STRONG, the main and one replica, at
  most d1Size. A sync waits on d1Lock or d2Lock until the length reaches
  the transaction's position. `Db.getDurableLength()` gives d1Size
  (reclaim uses it); nothing gives d2Size.
* So the answer is a comparison of two numbers: the comment's "cheap"
  holds.


The options
-----------

**A. Both methods, as the idea says.** `Transaction.isDurable()` and
`isDurable(SyncLevel)`, and the same in `Connection` for its last
transaction: true if the transaction's bytes are durable at the level,
answered at once. NONE is always true; STRONG compares with d2Size, which
follows d1Size when no replica is ACTIVE, as the syncs do. Below them,
`Db.isDurable(pos, level)` and a getter of d2Size in `StorageManager`. A
connection without a transaction: true, as there is nothing to wait for
(its `sync()` waits for the database's last transaction).

**B. ORDINARY only, now.** `isDurable()` without a level, in the same two
places; the level when 005-11 has decided what the levels are (today
STRONG is the main and one replica; 005-11's option A removes
replication). Nothing to take back whatever 005-11 decides.

**C. Not now.** An application that must not wait calls `sync()` in a
thread of its own. `Db.getDurableLength()` serves the code inside BergDB.

Proposed: B now, and the level with 005-11's decision. A question for
Frans whatever the option: is "commit now, ask later" worth more methods
in the API that is to be published (005-05)?


Questions
---------

1. A, B or C?
2. `Database` too, for everything so far, beside `Database.sync()`?
3. After a failure (005-01, 005-30) a sync still works for the
   transactions before it, and `isDurable` can answer from the same
   lengths; after `stop()` or `close()`, from the final ones. Or should a
   failed or stopped database throw, as its reads do?


Found on the way
----------------

* **One byte short.** A transaction's position, `Trans.lastPos`, is that
  of its last byte, the record's commit byte
  (`RecoverableStream.LAST_BYTE`), and `StorageManager.sync(pos)` waits
  while the durable length is below it: it returns when every byte but
  that one is durable. It is right only because a durable length never
  ends just before a last byte. Records and meta blocks are multiples of
  8 bytes, so a last byte is at 7 modulo 8, and a `BufferedStream` writes
  in parts that end at even positions when its size is a multiple of 4: it
  writes at most half its buffer at a time, and takes an append that does
  not fit in parts of the room left. The Pub API's sizes are (10 MB for
  the main stream, 20 MB for a replica), but the core API takes any size
  from 100 bytes (`DbBuilder.stream`, `Db.addReplica`). With one that is
  not a multiple of 4, a sync can return before the commit byte is
  written, and a crash then loses a transaction that the sync reported
  durable. From the code; not reproduced. `isDurable` compares
  `durable length > lastPos`. The syncs can do the same, with care: `Db`
  keeps the position of the last transaction as the stream length at
  start, and as a last byte's position after a transaction.
* **A w-transaction's `sync(level)`.** `WTransaction.sync(SyncLevel)` waits
  for the database's last transaction (`Db.sync(level)`, position 0), not
  for its own, as its `sync()` and the rw-transaction's `sync(level)` do. It
  waits longer than it needs to, never too short.


Done when
---------

* As decided: the methods in `Transaction` and `Connection` (and
  `Database`), with their Javadoc, on `Db.isDurable(pos, level)`, which
  compares `durable length > pos`.
* Unit tests: false at once after a commit with a long buffer time, true
  after its `sync()`; NONE true; STRONG without a replica as ORDINARY; a
  connection without a transaction.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S. Any time; the level after 005-11. The syncs' byte, if Frans wants it
fixed, is S too, and can go first.
