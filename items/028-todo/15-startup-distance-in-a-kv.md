028-15. Change: the startup distance out of the meta block, into an internal KV
================================================================================

Status: open (made on the branch `028-15-sd-kv`, to land). Kind: Change.
Frans: A (2026-11-18, 10:50).
Created 2026-11-16 by Frans Lundberg.

Frans, 2026-11-16, 10:32: "There is still a stream format change that I
want to get in place in the next release. The startup distance! It does
not need to be in the fixed-location stream slots (forgot what they are
called). Ensure this is in the todo list as an open item." The slots are
the meta blocks (027-03, section 6); release 2026.6 takes this entry
(026).

What: the startup distance sd is kept in each meta block, bytes 40 to 43
(027-03, section 6). The meta block is for what cannot be stored
otherwise (Frans, 2026-11-05; 017-07, section 2), and sd can: only the
writer uses it, since a start takes its position from the last record.
To get a meta block with the new value written, `Db.setStartupDistance`
puts `/#i/-dummy`, 200,000 zero bytes, never read (027-03, section 15).
The change, as 026-12, SF7 (a), and 024-01, OT4, describe it:

* sd is an internal KV of the Core (a key under `/#i/`, such as
  `/#i/-startup-distance`), written by a small transaction when sd
  changes, as today's setting's record is, and in the primordial
  transaction.
* A start reads it at its end, before the writer takes its first
  transaction.
* The meta block's bytes 40 to 43 become reserved, written zero and not
  read.
* `/#i/-dummy` goes: 200 kB less at each change of sd.
* The unit stays stream bytes (026-12, SF7 (b), recommended).
* A new format number, since a start of such a stream needs the KV.

To decide (Frans): what a start does with an older stream, one whose sd
is in its meta block. **Decided: A** (Frans, 2026-11-18, 10:50: "SF4 (a),
028-15 A"). At 11:51 Frans set the stable format aside for 2026.6 ("Let's
forget about stable format for the stream. I decide to not focus on this
for this release. The focus for the release are the algorithsm,
simplifying them, proving them. If possible."): 026-12's SF4 is open
again, and 2026.6's format is not called stable; option A stands, as
made below.

* **A.** It refuses it, as starts have refused older databases since
  005-50. Simple; a 2026.5 database is not opened by 2026.6.
* **B.** It reads sd from the meta block once, and writes the KV in its
  first transaction. One more path to test; the older format stays
  readable.

Recommended: as 026-12's SF4 (the versioning rule) decides for 2026.6;
A if SF4 is (a), no fallback for older streams.

Done when:

* `java/`: sd in the KV, the meta bytes zero, the dummy gone, the format
  number raised, the start as decided; tests for a change of sd, a
  restart after it, a crash inside the setting's transaction (028-08's
  case), and a reclaim cut that leaves the KV live.
* 027-03 (sections 6, 15 and 21) and, if sd is in a trace, 027-02
  follow the code; the Lean model and the trace checkers, if they name
  where sd is kept.
* `java/before-commit.sh` prints BEFORE COMMIT OK, and `level2.sh`
  (startup) passes.

Not in it: the C clone (012), which follows a release, not `main`.

Sources: 026-12, SF7; 024-01, section 11.4 (OT4); 017-07, section 2;
027-03, sections 6 and 15; 017-11 (a key count K, a separate question,
SF7 (c)).


What was made
-------------

On the branch `028-15-sd-kv` (from `main` `2cc9493c`), by agent sdkv of
coord-1118, 2026-11-18.

* **The KV.** `/#i/-startup-distance` (`DbConstants.SD_KEY`), 4 bytes, an
  `i32` little-endian, from 10 to 10^9 (`DbBuilder.MAX_STARTUP_DISTANCE`).
  `Db.setStartupDistance` commits a transaction that puts it (the clamp
  and the "nothing written if in force" rule as before); a refused or
  failed call leaves the setting as it was. A start reads it at its end,
  after the database is active and before reclaim's settings and the
  writer's first transaction (`Db.readStartupDistanceKv`): other bytes
  are an `InternalDataException`; no KV is an SFE ("the stream is
  damaged") unless the stream holds the primordial record alone.
* **The creation.** The primordial record stays as it was (272 bytes,
  `Db.CREATION_LENGTH`, the model's initial structure). A start that
  finds the primordial record alone, a creation or a crash before the
  next record, commits the writer's first transaction: an internal one
  that puts the builder's sd at the KV (`Db.putStartupDistanceKv`). The
  counters (`getTransactionCount`, `getKvCount`) are reset after it, so
  they are 0 after a start, as their Javadoc says.
* **The meta block.** Bytes 40 to 43 reserved, written zero, not read
  (`MetaBlock.getStartupDistance`/`setStartupDistance` gone).
* **`/#i/-dummy`** gone, with its 200,000 bytes at each change.
  `Trans.coreKey` refuses a caller's write at `/#i/-startup-distance`
  instead of `/#i/-dummy`, which is now an ordinary key under `/#i/`.
* **The unit** stays stream bytes.

**The number: the meta block's version, 154 to 155** (`MetaBlock.
CURRENT_VERSION`). First checked: `git diff release-2026.5 main` raised
neither number (`StoredTrans.RECORD_FORMAT` 7, `MetaBlock` 154, unchanged
since the tag). Why the meta version and not the record format: the
change is the meta block's (bytes 40 to 43 lose their meaning) and a KV
that an older release does not read; no record's bytes or rerun change,
so record format 7 stays. 026-12's SF3 rule, "every change that an older
release cannot read raises the meta version (154 today), so that an older
release refuses the database before it writes anything" (027-03, section
21; `readMetaBlock` writes nothing before its checks, 005-40), gives the
meta version: release 2026.5 refuses a stream of 155 before it writes,
and this one refuses 154. The message for 154 names release 2026.5 and
says what to do (`RecoverableStream.versionRefused`): "make the database
again: read it with release 2026.5 and put the data into a new database
with this release. The start has written nothing." A larger version is a
newer BergDB's. The record format is raised separately if the compact
nodes (026-12, SF8) come.

**The "absent means older" paths** (026-12, SF4 (a)), all three removed,
each small:

* a meta block without the node size (0): a damaged block, an SFE, not a
  `VersioningStreamException` of a database before 2026-10-27;
* a reclaim row without endKey: refused ("Missing 'endKey'"), no longer
  read with no bound; `serialize` always writes it;
* format 6's message (and 5's and 2's): `StoredTrans.formatRefused`
  says "an older version" and that 2026.5's databases are refused by
  their meta block first.

**Decided by the agent, for Frans to confirm:**

1. *Where the creation puts the KV.* Not in the primordial record itself,
   but in the creating start's next record (an internal transaction).
   The primordial record is the Lean model's initial structure (the tree
   checker requires R(0) to be the model's `initStruct`), and putting a
   KV of four segments there means building its key nodes by hand. Its
   costs: the creation is two records (a new database's first
   transaction has a time one unit later; positions after the creation
   192 bytes later), and a crash between them is completed by the next
   start with its own builder's setting (nothing depended on sd then).
2. *The value's bytes*: 4 bytes, `i32` little-endian, as the meta field
   was; strict: other lengths and values outside 10 to 10^9 refused.
3. *The creating start's transaction is internal* (as reclaim's settings
   are put): it takes a time also when no user transaction has one left
   (DbClock's margin, 015-55), and reclaim does not count it.
   `setStartupDistance`'s transaction stays a user transaction, as its
   dummy's was.
4. *Every database has a KV of BergDB's* from its creation on, so a Core
   API scan of the whole key space returns it (Db's Javadoc, "Keys and
   the layers above", says so; the Pub API does not show it).

**Tests** (all in the unit tests):

* `DbTesterRestart.testStartupDistanceKvKept`: a change of sd, restarts
  with other builder settings keep it, a second change, bytes 40 to 43
  zero in every meta block; a KV of other bytes refused at the start
  (five cases); a stream without the KV refused.
* `DbTesterRestart.testCrashInsideSetStartupDistance` (028-08's case,
  rewritten): a cut at every 8th byte of the setter's record and at its
  end: the old sd before the end, the new at it, kept by a second start.
* `DbTesterRestart.testCrashInCreatingStartsKv`: a cut at every 8th byte
  of the creating start's record: the next start completes the creation
  with its builder's sd; the whole record keeps the creation's.
* `DbTesterRestart.testStartupDistanceKvAfterReclaimCut`: reclaim cuts
  past the setter's record (and the creation's); the KV is live in a
  record after the cut, and a restart reads the last setting.
* `RecoverableStream.testReadMetaBlockVersion154Refused` and
  `DbTesterRestart.testVersion154Refused`: an older stream refused with
  the message that names 2026.5, the stream unchanged; `MetaBlock`'s
  `startupDistanceBytesZero`.
* Changed with the format, no saved databases (none are in the
  repository: no test fixture or corpus holds a stream; StreamDigest has
  no stored digests): the tests that counted a new database's KVs,
  records, positions or times (GetMany's, the Javadoc tests, the
  creation's crash tests, `testDecreaseOfStartupDistance`'s bound, 116 to
  154 commits; the Pub API's `testDecreaseOfStartupDistanceInMbF`, whose
  payment now begins after the call's small record); the eviction test
  `testLoweredBudgetAfterPinsFell` (570 transactions, from a sweep of 480
  to 600); `testOrdinalsWithReclaim` (a top node about every nine
  transactions: from 150 below the bounds); CST's found cases re-located
  in the new streams (the same kinds of damage, refused or failing a read
  as before; three seeds changed); TraceExport's run A records the
  creating start's record as R(1) (027-02), and
  `lean/contract/bridge-faults.sh` moves two faults from TX 2 to TX 3.

**Descriptions.** 027-03, sections 3, 6, 14.2, 15, 19 (G9), 20 (Q4) and
21; 027-11 (1.1, 1.2, 1.4, 1.9, 6); 027-02 (R(1)). The Lean model and the
trace checkers do not name where sd is kept: unchanged.
`releases/next.md`: a line for users. Javadoc: Db, `Database`,
`DatabaseBuilder`, `Trans`.

**Follow-ups** (not made here):

* The C clone (012) follows a release: meta 155 and the KV when it
  follows 2026.6.
* The reclaim row's other defaults (cut, rewritten, pEnd, pSafe, pCut
  when absent) are leniency of the same kind; with a strict reader
  (026-12, SF5) they would be required too.
* 028-13 (the startup distance's two ranges) is unchanged: the KV takes
  10 to 10^9, as the builder does; the setter clamps to 400,000 to 10^9.


Gates
-----

On the branch after `main` was merged again (`13a9d368`; main had brought
items only, 026-21's study), 2026-11-18, 11:55 to 13:05, with another
agent's runs beside them (not timing runs):

* `java/before-commit.sh`: BEFORE COMMIT OK (77 s; 1733 unit tests, 89
  f-tests, the demos).
* `java/stress/level2.sh` full: LEVEL 2 OK (RestartStress, invariance,
  CrashTest, BryanRepro, treeconf small/drain/reclaim, the contract and
  the bridge with their fault tests, conformance and drain, TAKECHECK).
* `java/stress/level3.sh` full: LEVEL 3 OK (also before the merge).
* `java/stress/level1.sh` full: LEVEL 1 OK (Props' SS 1.53 for its first
  case, at most 1.54).
* `java/stress/level4.sh` full: LEVEL 4 OK (the exporter's run E, the
  eviction schedules, LargerThanMemory).

On the way: the unit tests first failed in 66 tests, every one from the
new database's KV, its record and its time; fixed as listed above, none
a fault of the change. TraceExport needed the creating start's record
recorded (`level2.sh quick` failed in treeconf until then).


State
-----

2026-11-18, 13:10. Done and gated on the branch `028-15-sd-kv`
(GATED `13a9d368`, then this item's commit), not merged to `main`, not
pushed. For Frans to confirm: the agent's decisions 1 to 4 above (the
creating start's record, the value's bytes, its transaction internal, the
KV in every database). 026-12's SF4 is open again (Frans, 11:51); 028-15
stands as option A.
