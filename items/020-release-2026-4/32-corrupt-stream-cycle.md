# 020-32. CorruptStreamTester's hang in the release night of 2026.4

Created 2026-11-10 by Frans Lundberg. Status: done 2026-11-11: two fixes in release 2026.4
(58eba7cb, 21e8db97, through A' 76f66f89; 020-31); a third weakness for 2026.5 (024).

Frans Lundberg, 2026-11-10. The failure: `night.sh large` on commit A = 6e9671d4,
CorruptStreamTester.testFull, "long, seed 3971389, node, xor 128 at its byte 8, checksum
right, of the node at offset 32 (size 160, type 20) of the record at 19632: the start or
the reads did not end in 60 s".

# 1. The copy

- testFull's seed is the day's number: 20767 on 2026-11-10. The original of the
  workload LONG has the seed 20767 * 31 + "long".hashCode() = 3971389.
- LONG writes 50 transactions with keys of three segments and a startup distance
  of 5000 bytes. The stream is 26480 bytes, 51 records. The last record names the
  startup pos 19632, so the startup section starts at the record at 19632.
- The node at offset 32 of that record (stream position 19664) is key node 4431,
  an inner node with 8 klongs. It is the first node of the startup section.
- Its byte 8 is the first byte of its prevPos (StoredKeyNode: bytes 8 to 15). The
  prevPos is 13056, the node's previous version in the record at 13024. Xor 0x80
  makes it 13184. The checksum is made right, so the node parses.
- 13184 is the next node of the record at 13024: the version of 4431's child that
  pointer 2 of 4431 names. That record is before the startup section.

# 2. Reproduced, and where it loops

- A probe that builds this one copy and runs CorruptStreamTester.check on it
  (cst/probe/src/bergdb/core/CstProbe.java) hangs on A, every time.
- Its thread dump: the thread "CorruptStreamTester" is RUNNABLE in
  `Dag.getEqNodeInSegment` (Dag.java:443, the loop's end), from `Dag.getOne`,
  `Db.getOne`, `DbUtil.get`, `CorruptStreamTester.compare` (line 640: the compare
  at the time of an earlier transaction, not the last).
- With a counter in the loop: after 1, 2 and 3 million steps it is at key node
  4431 (spos 25936, its newest version), pointer 2, and the pointer leads to the
  same node 4431. The node points to itself.
- jstack could not attach to the probe's JVM (the attach handshake failed), so
  the dump is from Thread.getAllStackTraces in the probe.

# 3. Not new with 023

- On `main` before 023 (3cfee1e7, the merge fe82b47a's first parent), the same
  seed gives the same original: 26480 bytes, 51 records, the same records and
  nodes at the same positions. The same copy hangs there too, at the same place
  (Dag.getEqNodeInSegment, from Dag.getOne).
- The code that makes the cycle and the loop that runs in it are not changed by
  023: DbStarter only got keyNodeTakenBack, and getEqNodeInSegment is the same.
- So it is an old weakness. The night of 9 November (006-17) ran with the seed
  20766, whose copies do not have this coincidence. The take-back (Dag.takeBack,
  retarget, spaceSplitInPlace) has no part in it.

# 4. The cause

- At the start, `DbStarter.createMaps` maps each position to a node id (posToId):
  each version's own position, and also the prevPos that a key node version names.
  The damaged prevPos 13184 maps the child's position to 4431.
- `DbStarter.updateStreamPointers` applies Rule R: a pointer to a position whose id
  is known is set to the newest version of that id. Pointer 2 of 4431's newest
  version names 13184, so it is set to 4431's newest version: a pointer to itself.
- `Dag.getEqNodeInSegment` goes down a segment's tree in `while (true)`: in an
  inner node, `searchLte(time, compareValue)`, then follow the pointer, and repeat
  until a segment leaf. Its only ends are a segment leaf and a missing klong.
  Node 4431 is never a leaf, so the get loops for ever.
- The same damage can make a longer cycle. If the next node after the old version
  is a grandchild, its parent (4431's child) is set to point to 4431. Other damage
  (a pointer set to a position of an ancestor's version) can do it too.

# 5. The fix

- A descent checks that it does not come back to a node it passed. A valid tree
  never does that: each step goes one level down, and each node has one id.
- `OpData.descentFrom(root)` and `OpData.descentTo(next)` do Brent's cycle check on
  the node ids: the id of the node of step 2^k is kept, and each next node is
  compared with it. It finds any cycle within about twice the length of the path
  and the cycle. It needs no memory and no bound on a tree's height. Nodes without
  an id (Spos.NULL: a Dag without a Db, as in DagTester) are not compared.
- The descents that use it: `Dag.getEqNodeInSegment` (gets), the walk of
  `Dag.dirtyNodeBound`, and the descents of a put, `Dag.setValue` and
  `Dag.setNode` (also the start's rerun).
- A scan (`GetMany`'s chain) keeps its path from the root. `addLink` refuses a node
  that is already on the path. That costs a few compares when a scan goes down to
  a new key node, not per KV.
- The exception is a StreamFormatException, as `NodeCollection.checkPointeeType`
  throws for a pointer that names a node of the wrong type (019-32, 021-11). The
  package bergdb.dag may not use bergdb.storage (its package.html; deps.py), so the
  follower makes the exception: `PointerFollower.cycle(message)`, which Db's three
  followers in NodeCollection implement.
- What a reader sees: the get or the scan throws DbFailedException ("A read failed
  on the storage"), with the StreamFormatException "A descent came back to key node
  4431, which it passed: the pointers make a cycle." as its cause. The database is
  failed, and the next read throws IllegalDbStateException (P7). A start whose rerun
  meets a cycle refuses the stream with the StreamFormatException.
- Not changed: the two descents of the delete's climb (`descendToSegmentRoot` and
  `descendToRootQuietly`, 023 code). They walk again paths that the same delete has
  walked with the check, at the same time. The top nodes' walk (TopDs) is not a
  descent of key nodes and has no prevPos.
- Option (1), a check of each prevPos at the start, was not chosen. A prevPos before
  the startup section can only be checked by reading the node header there: one
  read for each node with a version in the section, which the bounded start
  (005-57, no header reads) removed. It also would not catch a cycle made by a
  damaged pointer.

# 6. The test

- `CorruptStreamTester.testFoundDescentCycle` (unit group): the copy of section 1,
  checked with a limit of 60 s; it must be "read failed". Then scans at each
  transaction's time until one fails the database (the scan at time 130 does), and
  a get after it must throw IllegalDbStateException.
- The commit: 58eba7cb on the branch fix-cst of cst/clone (on A).

# 7. A second old fault, found by more seeds

- The full set on the seeds 20769 and 20770 (the night seeds of 12 and 13 November)
  failed 32 copies each, on A and with the fix of section 5. Each failure is a change
  of the prevPos (bytes 8 to 15) of one key node of LONG, by a node field or by a
  flip of 0xff.
- The start threw an AssertionError from `NodeCollection.checkLinkById`: "rule 4 by
  position is not rule 4 by node id (bergdb 005-57)". That is linkD's check, which
  runs only with -ea.
- An example: seed 3971451 (20769), the node at offset 32 of the record at 22448
  (key node 5667), xor 1 at its byte 8. Pointer 2 of node 5669 names 13880, the
  version of 5667 before the startup section. With the prevPos changed, 13880 is not
  in posToId, so rule 4 by position finds no canonical object; by node id (a read
  of the header) it finds 5667's.
- Not new with 023: main 3cfee1e7 gives the same original and the same
  AssertionError on that copy.
- Without -ea the copy starts and holds all: the follow applies Rule R by the
  header's node id.
- The fix: in `checkLinkById`, none by position and a canonical object by node id
  is a damaged prevPos. It throws a StreamFormatException, and the start refuses the
  stream, as 021-11 did for a pointer to a node of the wrong type. Every other
  difference stays an AssertionError: a fault of the Core.
- The refusal: "Pointer 2 of node 5669 names 13880, a version of node 5667 (at 22480
  in the startup section), but no version of the section names it as its prevPos."
- The test: `CorruptStreamTester.testFoundLinkByIdPrevPos`, that copy, must be
  refused. It fails without the change (the AssertionError) and passes with it.
- `NodeCollection.testLinkToCanonicalCheck` (005-57's test of the check: section ids
  without the version before the node's version) expected the AssertionError. It now
  expects the StreamFormatException; the first before-commit of the change failed
  on it.
- A fault of the Core that left a link out of posToId on a valid stream would now be
  a refusal of a valid stream at the start. The tests would still see it.
- The commit: 21e8db97 on fix-cst, after 58eba7cb.

# 8. Runs

- The failing case alone (the probe): on A, it does not end (two runs, stopped
  after 20 s and 15 s, and one run with a counter, 3 million steps on node 4431);
  on main 3cfee1e7, the same (stopped after 20 s); with the fix, "read failed
  (DbFailedException)" at once.
- A scan of the same copy with the fix: DbFailedException with the cause
  "A scan came back to key node 4431, which it passed: the pointers make a cycle."
- java/before-commit.sh on 58eba7cb: BEFORE COMMIT OK (261 s; unit 1644 tests,
  F 89, demos 14 runs).
- The full set (`CorruptStreamTester SEED full 4`) on 58eba7cb: seeds 20766,
  20767, 20768 and 20771, 0 failures each (20767: 462578 copies, 107 s); seeds 20769
  and 20770, 32 failures each, all of section 7.
- testFull through the Night runner (bergdb.dev.Night, -m testFull) on 58eba7cb:
  SUCCESS, with NanotestForBergDB.databasesStopped (109 s).
- java/before-commit.sh on 21e8db97, a clean tree: BEFORE COMMIT OK (262 s; unit
  1645 tests, F 89, demos 14 runs).
- The full set on 21e8db97, one seed after the other (logs in cst/runs3/):

| Seed  | Copies | Time  | Failures |
|-------|--------|-------|----------|
| 20766 | 623225 | 138 s | 0 |
| 20767 | 462578 | 102 s | 0 |
| 20768 | 503956 | 106 s | 0 |
| 20769 | 468971 | 88 s | 0 |
| 20770 | 487916 | 106 s | 0 |
| 20771 | 518527 | 117 s | 0 |
| 20772 | 467252 | 119 s | 0 |
| 20773 | 442523 | 101 s | 0 |
| 20774 | 499215 | 85 s | 0 |
| 20775 | 533445 | 125 s | 1, section 9 |

# 9. A third old fault, not fixed

- Seed 20775 (the night of 18 November), one copy: "long, seed 3971637, node, xor 1
  at its byte 39, checksum right, of the node at offset 640 (size 192, type 20) of
  the record at 33416: the start threw java.lang.AssertionError: lastTimeIndex=0,
  lastTime: 72057594037928376, time=490", at KeyNode.addKlong, in the start's rerun.
- Byte 39 is the top byte of the node's first klong, a time klong: its time becomes
  about 2^56. The rerun's put at time 490 then meets the assert that times increase.
- Not new with 023 and not from the fixes: main 3cfee1e7 gives the same original and
  the same AssertionError on this copy.
- What the flip does: a time klong holds its type in bits 62 and 63 and its time in
  bits 0 to 55 (Klong.MAX_TIME = 0x00ffffffffffffff); bits 56 to 61 are unused. The
  flip sets bit 56. Klong.getTime still gives 440, so the node's data is right. The
  assert in KeyNode.addKlong compares the whole klong (2^56 + 440) with the time 490.
- The node is key node 30355 at 34056, a segment leaf, before the startup section
  (the last record names the startup pos 36552). Neither StoredKeyNode.parse nor
  validateKeyNode (021-12) looks at the unused bits.
- With -ea (the tests, the night): the start throws that AssertionError. A fault by
  the harness's rules.
- Without -ea (a user): the start goes on, and the copy holds all: the last state,
  the counter at each transaction's time, and every key at four earlier times are
  the original's (the probe, on 21e8db97). Right answers; no refusal and no later
  failure seen.
- Proposed fix (2026.5): StoredKeyNode.parse refuses a time klong whose bits 56 to 61
  are not zero (a time klong must have `(klong & ~Klong.MAX_TIME) == 0`), with a
  StreamFormatException "Bad time klong", next to its check of the klong type
  (019-32).

# 10. Files

- cst/clone, branch fix-cst: 58eba7cb (the cycle check) and 21e8db97 (checkLinkById).
- cst/wt-main: a worktree of 3cfee1e7, built, for the comparisons.
- cst/probe: the probes (CstProbe runs one node copy with a time limit and prints the
  threads; CstScanProbe scans and gets the cycle copy; CstRefusal prints a start's
  refusal) and their logs.
- cst/runs3: before-commit and the ten full runs on 21e8db97.
