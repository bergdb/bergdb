# 020-33. A known issue after the release: reclaim with keys in time order

Created 2026-11-11 by Frans Lundberg. Status: done 2026-11-11: the known
issue in 2026.4's notes, the fix in releases/next.md for 2026.5.

Frans, 2026-11-11, 10:21: "1, 2, 3 decisions; all as recommended". The
first was 024-07, section 11, question 5: a line in 2026.4's known issues,
"a queue of tens of millions of keys with a retain duration: fixed in
2026.5 (024-07)".


## 1. The issue

In release 2026.4 and before, the last step of each reclaim iteration
makes dirty every index node after its scan's last key (`Db.touchRange`,
a key range with no end). With keys put after every key so far, as keys
in time order are (a queue, a log), that is the whole index (024-07,
section 2). Measured at 10M keys: 772,454 nodes dirty in one step, its
commit 20.6 and 22.3 s under the write lock, 0.67 to 2.31 GB resident
against a cache budget of 0.2 GB, a record of 206 MB; at 1M keys 1.6 s
and 17 MB. It needs a retain duration: with infinite retention, the
default, reclaim does not run (`Reclaim.transactionCompleted`).

Two faults follow (024-07, section 3):

* **The heap.** The step runs inside a user's commit; an
  `OutOfMemoryError` there fails the database, and after a restart the
  same step runs again. Shown with a queue of 1M keys and a heap of 256
  MB; with 8 GB, estimated at 35M to 120M keys, not run.
* **The record limit.** From about 104M keys in time order (13-byte keys,
  the default node size) the step's nodes pass 2^31 - 9 bytes;
  `TransSeq.take` never takes them, the startup position stops for good,
  no cut is made again, and the stream, the startup section and the heap
  grow without end. Nothing throws. Read from the code and reproduced
  with the limit lowered; not run at 104M keys.

Fixed on `main` in `a780b957` (024-07, option A; 024-13's integration): a
step makes dirty only the index nodes on the paths of its own puts; at
10M keys 5 to 15 nodes and a largest record of 29 kB. For release 2026.5.


## 2. How it was found

* **024-03** measured release 2026.4 at 1M and 10M keys on the morning
  after the release (05:03 to 06:29; the release was made at 04:55,
  020-31): with a FIFO of 10M live keys, records of 191 and 206 MB at the
  ends of iterations and commits of 20.6 and 22.2 s; 17 MB and 1.7 s at
  1M (024-03, section 7). 2026.3 did the same or worse.
* **024-05** (OP1, section 5) asked what the step does at the record
  limit: "It may be a case of aim 1."
* **024-07** counted the mechanism, read the record limit from the code,
  reproduced it with the limit lowered
  (`Reclaim.Tester.testLastStepWithinRecordLimit`), showed the heap case
  at 1M keys, and built the fix (024-07, sections 2, 3 and 7).


## 3. Why not before the release

* **The touch was seen as a cost.** Review A of 023-07 found that the
  last touch walks every key put after the scan's end (one step made
  81,018 nodes dirty, `ReclaimTail`); review C found it not new. It was
  left to a later item (023-08, section 4). Neither the record limit nor
  the heap was raised there.
* **No test at these sizes with keys in time order and a retain
  duration.** The release's run of 021-25's FIFO had 1,024 live keys
  (020-31, section 4), where the step's record is small. 024-05, section
  4: "No test in `java/` checks a bound of aim 2 or 3 at more than 1M
  keys."


## 4. The notes' new text

* releases/2026.4/readme.md, Known issues and limits: a group "Found
  after the release (added on 2026-11-11; Post-release notes)" first, with
  one entry, "Reclaim with keys in time order: one commit grows with the
  database, and at tens of millions of keys the heap runs out or reclaim
  stops": the use (a retain duration, keys in time order), the sizes
  (1M, 10M, about 104M keys), the two faults, that infinite retention
  avoids it, and the fix for 2026.5 (024-07).
* The same file, Post-release notes: the fault, dated, and a list
  "Changes of these notes", as 2026.2's notes have one (016-10).
* The jar, the zips and `SHA256SUMS` are unchanged: no zip holds
  releases/2026.4/readme.md (the source zip is of the release commit,
  before the folder was made), and `SHA256SUMS` has no line for it.
* releases/next.md, Core API: the fix with the two faults it removes and
  its numbers; beside it 024-10's rule for the builder; and a line for
  024-16. Known issues and limits: "Fixed: reclaim with keys in time
  order".
