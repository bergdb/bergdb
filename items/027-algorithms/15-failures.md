# 027-15. Failures

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 11 of 027's outline (027-04, section 2.3; levels: all). The error
model: the sound environment that BergDB assumes; what fails the database
(an I/O error, corrupt data, an `Error`, anything after the go point) and
what fails only the call; a failed database; interrupts; the next start's
recovery; index jobs.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.

Recorded before the part is written (031-06, 2026-11-27), from the code
at 8a0897cf (2026-11-28):

* **Refusal, failure and stop around an action's maintenance** (031-06,
  section 2, rule 8). Every accepted action, a commit, a setter or a
  part of `maintain(int budget)`, appends one record, and a commit's or a
  part's record carries its maintenance, planned before the go point
  (`Db.planMaintenance`, after the last check that may refuse the
  action) and applied after the append. So an action ends as a refusal
  with nothing changed, an accepted record that holds its maintenance, or
  a failed database:
  * an action is refused only by its own checks, before the plan;
  * a stop during the plan, or before it returns, refuses the action with
    nothing written: the transaction is given back (`Db.giveBack`: its
    keys, values and time) and a `DbStoppingException` is thrown, by the
    plan's read that the stop refused, or by the admission check after
    the plan;
  * any other exception from the plan on fails the database (010-01, P7);
  * after the go point a stop does not refuse: the close waits for the
    record.

  Checked: 031-06's `FaultProbe` (a stop and an exception before the
  plan and at the go point, a torn append, a stop and a failure after
  the append, each at 231 records of every kind: refused, accepted or
  failed as above, the start's memory the running database's, the stream
  continued the same; 031-06, section 4.2, and its landing, step 3).
* **A record that does not fit** (031-06's landing, step 2). A KV of
  the maintenance at a key of the action's (`Db.merge`) and a record
  whose got-dirty set a later record with no KVs could not take
  (`Db.checkTakeable`, before the append) are a `Bug`; a record over its
  cap is the serializer's `DbException`; each comes in or after the go
  point and fails the database with nothing of the record written
  (`ReclaimRoomTester.testUntakeableRecordFails`).
* **The next start's recovery** refuses a tail that is not the stream's
  own records before anything is written, with a `BadTailException` that
  names P, the end of the last record found to be one, and the way out
  (028-67; 027-11, section 1.3).


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-28. Recorded before the part is written, from the code at
8a0897cf: refusal, failure and stop around an action's maintenance
(031-06, section 2, rule 8), a record that does not fit (031-06's landing,
step 2), and the recovery's refusal of a tail that is not the stream's
records (028-67). By an agent of lead-1127, on the branch `031-06-docs`.
