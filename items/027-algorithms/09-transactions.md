# 027-09. Transactions

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 5 of 027's outline (027-04, section 2.3; levels: 0). How a
transaction becomes a change and a record: the clock and the times (56
bits; the last 1,024 times kept, for reclaim's internal transactions
until 031-06, its Q4); the read set and the STM check; the key and value
transformations; one record an action (031-06): a commit's, a setter's
and a part of `maintain(budget)`'s, through one path (`Db.executeLocked`);
the maintenance that a record carries, planned from the state before it
before the go point and applied after the append (027-13, 1.2); the KVs
in key order, one a key, the action's and the maintenance's merged, given
to the writer as one batch (record format 8, 026-25), after every value
transformation of the transaction has run; the limits L1 to L6, the check
of the dirty nodes (`dirtyNodeBound`, argued for PE since 028-21) and
the record's room (an action within 7/8 of the record limit, the record
within 15/16, the check before the append; 027-03, section 8.3); the go
point (R1: a refused call changes nothing; a stop during the plan
refuses with nothing written) and the steps after it (the record, the
maintenance's apply, statistics, eviction); one writer and readers
without locks; why a rerun gives the same record (P2, P8).

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The batch of record format 8 (026-25) and the status of
`dirtyNodeBound` with PE. By an agent of coord-1118, on the branch
`027-pe`.

2026-11-19. 028-21: `dirtyNodeBound` argued for PE. By an agent of
coord-1118, on the branch `028-21-dirty-bound`.

2026-11-28. One record an action (031-06): the path of every action, the
maintenance planned before the go point and applied after the record, the
record's room. By an agent of lead-1127, on the branch `031-06-docs`.
