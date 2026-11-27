028-66, review (rev66)
======================

An independent review of the branch `028-66-c-rule`, head `9e7dd5e3`, on
`main`'s `734f05a2`: option C (the cut's deletes a batch with one
directory force; the open takes a gap in the files; a start refuses a
stream whose first position is after reclaim's cut) and Frans's rule of
the files before a gap (2026-11-27). By rev66, an agent of lead-1127,
2026-11-27, 22:43 to 23:20. I read the diff first, then the entry
(sections 1 to 6), then the code around it: `FileStream`,
`RecoverableStream.recover()`, `Reclaim` (the cut's decision, `apply`,
`initFromDb`), `Db.start`, the power-loss model.

Where: a clone of the branch at `9e7dd5e3` (the code unchanged), `main`
at `734f05a2` as a worktree beside it for one comparison, and two probes
in this directory: [NestedGap.java](NestedGap.java) and
[CreatedTxtProbe.java](CreatedTxtProbe.java). F53 was shared with
`java/night.sh` and another review; no timing run was made.


## 1. Verdict

**Land after the timing run.** I found no order of writes, deletes and
directory forces after which a power loss leaves a directory from which
a start loses an accepted record, takes the wrong files as the stream,
deletes a file it needs, or refuses a sound database; nor a path on
which the rule passes another database's file before a gap, or on which
a start deletes before it refuses. A probe with teeth (section 3)
checks the one case no test of the branch makes: a power loss inside
the start's own batch, the files before the gap and the stream's files
before the cut deleted together.

The findings are small, none in the order of the deletes:

* **R1** (low, shown by a run): the power-loss trace fails its own
  check of the forces for longer traces without per-append forces, a
  change of the trace (seeds 1001 to 1012 at 3,000 transactions, 5 of
  12). Level 3's seeds do not hit it. Best fixed with the landing.
* **R2** (low, shown by a probe): a start refused because its first
  position is after reclaim's cut has written `created.txt` first, if it
  was missing; the Javadoc and the entry say that it writes nothing but
  what recovery writes at a torn end.
* **R3** to **R5** (nits, read): two messages, a sentence of the stream
  contract, two corners of `FileStream` reached only by its own tests.

R2 to R5 can follow the landing.


## 2. Findings, by severity

### R1 (low; shown by a run). The trace's check of the forces fails for longer traces

* **Where:** `FileStreamPowerLossTester.trace`, the release of the cut's
  thread after the loop (`io.release(); stream.awaitDeletes();`, line
  1118), and `checkForcesWithoutAppendForces` (lines 1194 to 1198),
  which requires a `CLOSE` force.
* **What:** the cut's thread is held at its deletes and released every
  300 commits; the cuts made while it is held form its next batch, whose
  `forceTo` runs when it is released. The last release, after the loop,
  so forces the whole last file (`Force.CUT`), the final sync writes
  nothing more, and `close()` has nothing to force:
  "the trace made no CLOSE force: {OPEN=37, SWITCH=36, CUT=20}".
* **Shown:** `PowerLossTest 1001 6 3000 3` on the branch fails so at
  seed 1001, and `PowerLossTest 1002 5 3000 3` at seed 1006, each after
  the seed's trace with per-append forces has passed; `PowerLossTest
  1001 1 3000 3` on `main` passes (POWERLOSS OK). With the check made a
  print in a copy of the tester (not committed), `PowerLossTest 1001 12
  3000 3`: no `CLOSE` force in 5 of the 12 traces without per-append
  forces, and POWERLOSS OK, 732 cold recoveries with per-append forces
  and 744 without, 110 images with a gap, every one started and checked,
  the negative controls caught. So the product passes; the check is the
  tester's.
* **Why it matters:** level 3 runs seeds 1 to 8 at 1,500 transactions,
  which pass; a change of its seeds or its length, or a second harness
  with other sizes (AGENTS.md: a harness in two scripts runs with other
  seeds or sizes), fails without a fault.
* **Fix:** one commit after the release and before the final sync, or
  require `CLOSE` only when the last file had unforced bytes at
  `close()`.

### R2 (low; shown by a probe). A refused start writes created.txt

* **Where:** `Db.startInner` calls `writeCreatedTxtIfMissing()` (Db.java
  1351) before `reclaim.initFromDb` (Db.java 1358), whose refusal of a
  first position after the cut is new in 028-66 (Reclaim.java 1353).
* **What:** a Pub database whose `created.txt` is missing and whose
  stream lacks bytes (a copy of the stream files only, as `BackupGap`
  makes, or a first file removed by hand) is refused, and has
  `created.txt` afterwards. `FileStream`'s Javadoc ("A backup ...":
  "writes nothing before it refuses but what recovery writes at a torn
  end", line 95) and the entry (5.2, 6.2) say otherwise. No stream byte
  is written and nothing is deleted; the file marks the directory as one
  that held a database (`DatabaseBuilderImp.refuseMissingStream`), so a
  start there after the stream files are removed is refused until it is
  removed too.
* **Shown:** [CreatedTxtProbe.java](CreatedTxtProbe.java): a database of
  8 MB, never cut, startup distance 1 MB; `created.txt` and the first
  stream file removed; the start is refused ("... the stream lacks
  bytes of the database. The start has deleted nothing ..."); CREATED
  TXT WRITTEN BEFORE THE REFUSAL.
* **Fix:** write `created.txt` after `initFromDb`, or say in the Javadoc
  and in `Db.start()`'s that it may be written.

### R3 (nit; read). Two messages of a refusal

* `Db.refusalOfMissingBytes` (Db.java 1268) wraps every start failure
  whose cause chain holds a `ReadBelowFirstPosException`, so also
  `Reclaim.initFromDb`'s own refusal: the message begins "The start
  needs bytes of the stream before its first position" when the start
  read nothing there; the exact account ("The stream begins at F, after
  reclaim's cut, C") is the cause's. Leave a failure that is already the
  refusal as it is.
* The rule compares the files before the gap with the ID of the first
  block after it (`readFirstMetaBlock`, RecoverableStream.java 994;
  `checkLeftovers(id)`, line 203). If the file after the gap is the
  stranger (another database's file at the same position, put there by
  hand), the database's own files before the gap are named "another
  database's", and the way out says to move them out; the next start is
  then refused by 028-67's check of the ID. Nothing is deleted or
  written; only the message points at the wrong files.

### R4 (nit; read). The stream contract's sentence on durability

`AppendOnlyStream`'s class Javadoc (lines 22 to 29) gives the duty to
the caller: "A caller that cuts must have its record of the cut durable
before it calls pretruncate()". With per-append forcing off,
`FileStream` reports written bytes as durable, and Reclaim cuts then;
the argument rests on `FileStream`'s own `forceTo` before each batch
(`runCuts`). The contract should also say what an implementation must
do: remove bytes before a cut's position only after the bytes before its
length at that cut are on the device.

### R5 (nit; read). Two corners of FileStream that the Db does not reach

* `deleteAllFiles` (FileStream.java 1565) deletes the leftovers without
  the check; only `seekFirstPos` calls it, which `FileStream`'s own tests
  use.
* `pretruncate` queues the leftovers behind files that an earlier cut
  queued (line 747), not oldest first, if a cut at or after the first
  position came before `checkLeftovers()`; the Db always checks first.

### Limits of the rule (not findings)

* An older copy of a file of the same database passes and is deleted
  (5.10, 6.2, accepted). Its common form: a backup restored into the
  directory without clearing it, whose newest file ends before the
  directory's first one. Its files are then the files before a gap; the
  start takes the newer state and deletes the restored files, where
  before 028-66 the open refused the gap. `Database`'s Javadoc already
  asks for a restore of all the files together.
* The rule covers the files before a gap. A file that fills a gap
  exactly leaves none, and a cut deletes it with the other files before
  the cut, unchecked, as any file before the cut was deleted before
  028-66.


## 3. What was checked, and found right

* **The order** (`runCuts`): the batch's size and `forceTo` taken under
  the stream's monitor; the force before the first delete; the deletes
  oldest first; one directory force after them; a cut meanwhile is the
  next batch with its own force; a failed delete or force stops the
  thread with the rest queued.
* **The gap's end is at or before the durable cut** (5.4): Reclaim cuts
  only when the durable length has passed the length after the
  decision's record (`applyCut`, `cutIfDurable`); `pretruncate` records
  the length then (`cutForceTo`); every file before the last was forced
  at the switch; after a kill, the open forces the last file
  (`Force.OPEN`) before a start can cut; the table only moves forward
  (`planCut` drops the rows before the cut row only); every record that
  decides a cut is a committed record of its own (a part of
  `maintain()` too).
* **The start's cut deletes the leftovers:** a record never begins at a
  meta block's position (`getNextSpos`; a record that ends at one has
  the block written at once), so a file's start, the gap's end, is
  before the cut, and the start cuts.
* **Nothing is deleted before a refusal:** `recover()` checks the
  leftovers before the walk and recovery's writes; `initFromDb` refuses
  before it cuts; `FileStream` deletes no leftover before a check that
  passed, and only at a cut at or after the first position.
* **The rule's check:** magic, version, last byte, own position, ID;
  every file begins at a meta block (all of `FILE_SIZES` are multiples
  of 200,000; a new file begins at the end of a full one); the ID is the
  stream's first block's, set only at the creation.
* `checkLastTransSpos`'s new branch only changes the message of an
  existing refusal; the tail of zeros is the same before and after the
  leftovers' delete (`onlyFile`); `BufferedStream` and `StorageManager`
  pass the check on, and the Pub layer uses `FileStream` under them.
* `probes/ab-reclaimcost.sh`: its patterns match `ReclaimCost`'s lines,
  which are the same on `main` and the branch (read, not run).

**Probe.** [NestedGap.java](NestedGap.java) (package `bergdb.core`): a
database written while the cut's thread is held at its deletes, so that
7 files are taken off and none deleted; its files copied with the writer
idle after a sync. Level 1: every subset of the 7 removed (128 images).
Level 2: for each level-1 image, every subset of the start's own batch
(the files that a start on it deleted: the files before the gap and the
stream's files before the cut) removed from it (1,932 images). Each
image started on a plain `FileStream`, every key read against the model,
`checkNodes`, closed, and no gap left. Run with LEVEL2_SAMPLES 1000
(every level-1 image), with per-append forces on and off: 2,060 starts
each, 1,812 images with a gap, none refused: NESTED
GAP OK.

**Runs.** `PowerLossTest` on the branch with seeds 1001 to 1012 at
3,000 transactions (R1); traces with batches of up to 3 files, as in
level 3.

**Coverage, beside R1:**

* The trace holds the cut's thread and releases it while the writer
  waits (`awaitDeletes`), so no image has a batch's deletes beside the
  writer's appends or a new file's directory force. The property the
  argument needs, the record forced before the batch, does not depend
  on them; a real writer runs beside the thread.
* `testRecoveryAfterEverySubsetOfABatch` checks every subset on a bare
  `FileStream`; at the level of a start the subsets are random (77 gap
  images in level 3). NestedGap adds them exhaustively, and the start's
  own batch.
* `kill-restart.sh` leaves the kernel's directory as it is: it runs the
  batch, never a gap.
* `BackupGap` runs by hand only; it is in no script.


## 4. Simplicity

The change is in the right places: the order and the gap in
`FileStream`, the check of a block in `RecoverableStream` (the stream
layer knows no meta blocks), the refusal in `Reclaim.initFromDb`, where
the cut is known. `AppendOnlyStream.checkLeftovers()` with
`LeftoverCheck` and `PieceReader` is the least that keeps the layers
apart. About a quarter of the new code is messages (`gap`,
`frontAccount()`, `refusalOfMissingBytes`, the extra texts of
`recover()`); R3's first point would drop one of the wrappers.
`readLeftover` repeats `DbFile.read`'s handling of interrupts; opening
the leftovers read-only at the check would reuse it.
