007-02. A transaction can stop the startup pos for good
========================================================

Created 2026-10-23 by Claude (Opus 5.5, Claude Code), found while writing
007-01 and checked with a probe. Status: registered as
[005-31](../005-todo/31-fix-take-blocked.md), where the fix is proposed;
not fixed.


The issue
---------

`TransSeq.take` takes whole transactions. Since bergdb 005-17 it does not
take the first transaction whose got-dirty nodes do not fit in the record,
"also when fewer than two are"; the record limit is about 2 GB. The record
of a transaction holds its value nodes and a 16-byte got-dirty id for each
node it made dirty; writing those nodes later takes about 360 bytes each.
So a transaction whose own record is well within the limit can make dirty
more node bytes than one record can hold. No later take can take it: the
startup pos stays before it for good, since D's nodes from it never leave
and never get smaller.

Then:

* The startup section grows with every transaction, and so does startup:
  each restart reruns everything after the stopped startup pos. The
  opposite of bounded startup (007-01).
* D keeps the transaction's nodes for good: memory that eviction cannot
  free.
* Reclaim cannot cut, since the cut waits for the startup pos
  ([levels.md](../011-docs-archive/04-levels.md), Level 3).
* A restart does not help: startup rebuilds the same D, and the take meets
  the same transaction (T2).

With the real limit it takes a transaction that updates some millions of
keys spread over as many key nodes, in a database of about a hundred
million keys or more. Rare, but allowed. A load into a new database does
not do it: new key nodes are made full of new keys, so they take fewer
bytes to write than the keys took in the record.


The probe
---------

[02-take-blocked/TakeStuckProbe.java](02-take-blocked/TakeStuckProbe.java),
on bergdb `1a329d1` (built in a clone), output in
[02-take-blocked/output.txt](02-take-blocked/output.txt). The record limit
is lowered to 200 KB, as `DbTester.testRecordsWithinLimit` lowers it, with
a startup distance of 20 KB. It loads 40,000 keys in random order, 100 per
transaction, runs 2,000 small transactions, then one transaction that
updates every n-th key with a 1-byte value, then 4,000 small transactions,
and restarts.

| n | Keys updated | Its record | Startup pos after 4,000 more | Section then | Restart |
|---|---|---|---|---|---|
| 20 | 2,000 | 138 KB | before it | 506 KB, 25 d | 57 ms |
| 40 | 1,000 | 73 KB | before it | 441 KB, 22 d | 45 ms |
| 100 | 400 | 34 KB | before it | 402 KB, 20 d | 46 ms |
| 200 | 200 | 18 KB | past it | 20 KB, 1 d | 13 ms |

With n = 100 the transaction's record is a sixth of the limit, and it
stops the startup pos. The section grows by the bytes of every later
transaction, without end, and the restart starts from the same pos.


Options for a fix
-----------------

* Refuse the transaction before its go point (M49) if the nodes it makes
  dirty could not be written in one record. The writer knows those nodes
  only after the puts; a bound from the number of keys and the height of
  the tree would refuse more than it must.
* Let a record hold more: a format change (the record's size field is 4
  bytes), or one transaction's writes in several records.
* Write a transaction's dirty nodes over several records, before the
  startup pos passes it. That is a change to the model: step 6 writes
  exactly the nodes taken, and a node left in D keeps its got-dirty index
  (INV-1, INV-3), so the startup pos cannot pass the transaction until all
  of its nodes are written. It needs its own proof.
