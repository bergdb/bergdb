028-84. Fix: the documents of a maintain() call's work and wait, a commit's getTrans(), and an emptied database's stream
========================================================================================================================

Status: open (built on a branch, to land).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: the findings on documents of 031-08, part A
(`items/031-release-2026-7/08-user-apps/apps-a.md`, section 4), and N1
of 031-02 (`items/031-release-2026-7/02-app-hunt/readme.md`, section
9.4):

* **UA-4.** `Database.maintain()`: "a pass takes about getStreamSize()
  divided by the budget's bytes in calls"; after a mass delete 5 to 13
  calls of `maintain(100)` wrote, where the sentence gives 77 to 563.
* **UA-5.** `Database.maintain()`: "may go past it by a small part's
  work"; the Core's `Db.maintain()`: "a step of about 16 kB of KVs". One
  call of `maintain(100)` wrote 8,462,864 bytes, with a live value of 8
  MiB (`probes/MaintainOverrun.java`).
* **UA-6.** `Db.getTrans()` and `StoredTrans.getValueNodes()` speak of
  reclaim's steps as transactions of their own, as before 031-06; since
  031-06 a commit's record carries reclaim's copies, with the copy mark,
  and its row and table, beside the transaction's KVs: of 3,000 commits
  of 20 puts each, 1,472 listed more value nodes, up to 60
  (`probes/CoreGetTrans.java`). "The Core API" does not name `isCopy()`.
* **UA-7.** `Database.maintain()` does not say how long a call may wait:
  it gives way to every commit that waits, so beside 8 threads that
  commit without a pause no call of `maintain(100)` returned in 10 s
  (`probes/MaintainWaits.java`).

Not in this entry: UA-2 and UA-10 (the exception of a call at a stop),
in 028-83; UA-1, done by 028-82 (UB-1); UA-3 and UA-8 (questions for
Frans); UA-9 (a product finding, 031-04's handover).

Why: a user who sizes a `maintain()` budget, calls it beside writers,
reads a commit's record with the Core API, or measures an emptied
database needs the document to say what the code does.

Frans: none.

Done when: the Javadoc of `Database.maintain(int)`, `Db.maintain(int)`,
`Db.getTrans()` and `StoredTrans.getValueNodes()`, 027-13 and 027-03
say what the code does; `java/before-commit.sh`
prints `BEFORE COMMIT OK`.

First step: `Db.maintain()`, `Db.giveWayToWriters()`, `Reclaim.planPart`
and `planStep`, `ConnectionImp.transactionInfo()`.

Found by: 031-08, part A (UA-4 to UA-7), and 031-02, section 9 (N1),
2026-11-28.


Result
------

On the branch `docs-1128` (2026-11-28). Javadoc and items only; no
check, no stream byte and no API method changed. The probes of
`apps-a.md`, run on the release jar of `main` at `16c64d9a`, give the
figures of section 4 again: `MaintainOverrun 100`, 8,462,864 bytes in
one call; `CoreGetTrans`, 1,472 of 3,000 commits, 31,802 value nodes
with the copy mark.

* **UA-4.** `Database.maintain()`: a pass costs about the live data
  that it rewrites, not the stream (a part's cost is what its record
  writes and a quarter of what its step reads, `Db.maintainPart`), so it
  takes about the live data divided by the budget's bytes in calls, at
  most about `getStreamSize()` divided by them; after a mass delete a
  few, and the calls after them mostly wait for the cut.
* **UA-5.** `Database.maintain()`: the call runs parts while it has used
  less than its budget and never splits one; a step copies whole values,
  the last whatever its size, up to 8 MiB (L4), and a take writes at
  least one whole transaction's index nodes, so the budget bounds the
  number of parts, not the bytes of a call. `Db.maintain()`: the step's
  last KV is copied whole (`Reclaim.planStep`), the take's first
  transaction taken whole. 027-13, 1.10 and section 4, the same.
* **UA-6.** `Db.getTrans()`: since 031-06 a commit's record and a part's
  carry reclaim's work, and `getValueNodes()` of a commit lists the
  copies, with `StoredValueNode.isCopy()`, and reclaim's keys that the
  record writes, without the mark; a user transaction's own KVs are the
  value nodes without the mark but those under "/#i/dreclaim/", and a
  copy is never at a key of the transaction's; the transaction that
  wrote a copied value is found as before, from the record that copied
  it. `StoredTrans.getValueNodes()` the same. "The Core API" names
  `StoredValueNode`'s `getKey()`, `getValueNode()` and `isCopy()`.
  `getTransactionCount()`: it counts the settings' records and the
  parts that write, not reclaim's steps apart. 027-03, section 12: the
  Core's `getTrans()` among the copy mark's readers.
* **UA-7.** `Database.maintain()`, a new paragraph "How long a call
  takes": the call gives way to commits before each part and again
  under the lock (031-04, Q9), so a commit waits for at most one part,
  and the call waits as long as commits come without a pause, with no
  bound, an interrupt not ending the wait; what a caller can rely on (it
  returns once it has used its budget or has nothing more to do,
  counting only the moments when no commit waits, and holds no lock
  while it waits); call it when idle, not beside writers that commit
  without a pause, nor inside an `rw()` action. `Db.maintain()` and
  027-13, 1.10, the same.


Log
---

2026-11-28. Registered by lead-1127 from 031-08's UA-4 to UA-7 and
031-02's N1; taken by an agent of lead-1127, on the branch `docs-1128`.

2026-11-28. Built: the Javadoc and the items.
