024-release-2026-5
==================

Created 2026-11-10 by Frans Lundberg. Status: open.

Release 2026.5 of BergDB, after 2026.4 (020): its plan, its decisions and
the work towards it. Frans, 2026-11-10, 17:52: "Time to create the
nnn-release-2026-5 item? We are already planning for it, so why not."
Its theme, since 2026-11-11: **solid algorithms** (Frans, 06:44: "So,
solid algorithms perhaps comes before a "stable stream"?"). Bugs first;
operations and storage proportional to the value they bring to the user;
a Lean model that matches the code. The aim, its reasons and Frans's
words are in 024-04.

The first theme, 2026-11-10 to 2026-11-11: "a stable stream format"
(Frans, 2026-11-10, 19:54: "OK, release theme decided, "a stable stream
format"."). It follows in release 2026.6 (026), when the algorithms have
stopped moving (024-04, section 5).


Planned so far
==============

What Frans has put off to 2026.5 or to after 2026.4, with where it was
decided. The list is from before the theme of 2026-11-11: which of it
the aim asks for, with bounds and tests, is 024-05's work. Nothing else
is decided.

From 023, the Core's cleanup (023-08, section 5, "Later, each on its
own", and section 7):

* **The builder's rule "the last operation wins"**, put or delete, for
  `Trans.Builder` as for the KVs that key transformations make one key,
  with BergDB's C clone (Frans, 17:41 to 17:48; 2026.4 keeps 015-40's
  rule: the last put, or a delete if there is no put).
* **P8, each reclaim step scans at its own time**, with fault 13's fix (a
  step counts only the KVs stored before pStart; 023-08,
  checks/p8-liveness.md) and the liveness tests: a shorter lag after a
  mass delete. No format cost.
* **Merges at the delete** (023-05 P5), switched on by the record's
  format, so that 2026.4's databases need no refusal. Changed
  2026-11-11, 07:23 (Frans, "as recommended"): 2026.5 may refuse
  2026.4's databases, so one rerun path and a new record format; the
  design study is 024-11.
* **Fix (a) of the dirty top-node window** (023-05 P7), if the ratchet
  test shows that the window grows (023-08, Q6).
* **`maintain()`**, the explicit call that drives cleanup (023-04, Y10).
* **The cache's tables** that keep their peak size after a mass delete
  (023-08, section 4).
* **The last touch of a reclaim iteration** over keys put beyond the
  scan's end, maybe by marking only the rewrite paths (023-08, section 4;
  review A, section 4.2).
* **Dead klongs in live nodes**: compaction, beyond 2026.4's named
  allowance (023-08, Q5).

From the release night of 2026.4 (2026-11-10):

* **Done 2026-11-12 (0420c72e; 024-25, section 12).** **A time klong's
  unused bits** (56 to 61) are not checked:
  `StoredKeyNode.parse` should refuse a time klong whose bits 56 to 61 are
  not zero ("Bad time klong", a `StreamFormatException`, beside its check
  of the klong's type, 019-32). Found by CorruptStreamTester's seed 20775
  (the night of 18 November): such a damage makes a start with -ea fail
  an assertion in `KeyNode.addKlong`; without -ea the database starts and
  answers right. Old, on `main` before 023 too. A strictness check of
  the stream format, bits that must be zero are checked (024-02, section
  19, G1, and section 20, Q13): it was a case of the first theme; under
  "solid algorithms" it is not decided whether 2026.5 does it (024-04,
  section 5). It refuses no database that a writer wrote, so it can come
  at any time.

Not to do (023-08, section 5): rule (b') of the window, and the replaced
queue on by default.


Files
=====

* 01-inventory.md. 024-01, the inventory of candidates for 2026.5, for
  Frans to choose a theme and a scope (Frans, 19:24 to 19:26): 49
  candidates in eight areas, four possible themes ((A) consolidate
  2026.4, (B) large databases measured on a calm Core, recommended, (C)
  strict cleanup, (D) the Pub API), and the questions for Frans in order.
  Nothing decided.
* 02-stream-format.md. 024-02, the stream format's specification: the
  skeleton, written from release 2026.4's code (on 012-02's description
  of format 5): the structures from the files to the bits, field tables
  for the meta block, the record and the nodes; the gaps where the code
  accepts what a spec should refuse (G1 to G21) and its Java dependences
  (J1 to J8); the open format questions (Q1 to Q23, Q14 and Q16 first);
  the options for versioning, none decided.
* 03-measurements.md. 024-03, release 2026.4 measured at 1M and 10M keys
  beside 2026.3 (PF1): the same speed and MEM; a mass delete fixed (101
  nodes against 882,271); P8 not needed on these numbers (CL1); merges'
  underfill measured (CL2); the last touch the biggest fault measured
  (CL7: a 200 MB record and 21 s at 10M, old); the stream under steady
  overwrites. Outputs in 03-measurements/.
* 04-aim.md. 024-04, the aim of release 2026.5, "solid algorithms"
  (Frans, 2026-11-11), the document the release's work cites: bugs
  first; operations proportional; storage proportional; the model
  matches; in one line, cost follows value. Frans's words, the reasons
  for algorithms before a stable stream format, the known cases against
  the aim (CL7, CL2, MEM at 10M KVs), and what stays of the stream
  format's work (024-02 kept current; Q14 and Q16 maybe, not decided).
* 05-known-cases.md. 024-05, the aim against what is known: every known
  case against aims 2 and 3 with its figures checked at the source (OP1
  the last touch, OP2/ST2 the underfill, ST3 the stream kept, OP3 a
  put's bytes, ST4 dead klongs and the small ones); proposed bounds (BD1
  to BD13) with the tests that check them or none; what is not measured
  (100M keys; GM1 to GM8); a proposed order; questions QF1 to QF8.
  Corrects 024-03: a get at 10M loads 1.9 nodes, not 25.
* 06-model-gap.md. 024-06, the gap between the Lean model and release
  2026.4's code: the model is the theory of the stream and of memory,
  with the transaction's change an opaque function, so no proof broke
  and none covers the key tree; four weak points in the tie (PhysStep,
  T-SCHEME's argument, the draining configurations, javaTake); the work
  in an order (A the tie, B the tree in Lean run against Java, C and D
  its proofs, E the costs); questions 1 to 8.
* 07-last-touch.md. 024-07, the last touch of a reclaim iteration
  (CL7, OP1) fixed: a reclaim step makes dirty the index nodes on the
  paths of its own puts only (`Db.touchPaths` in place of the key
  range); with 10M keys the last step's record 29 kB, not 206 MB; the
  mechanism, the options, the theorems T-COVER and T-LATEST in Lean, the
  checker's touchPath and CUT-live, the numbers before and after, two
  changed tests. On main since a780b957. Outputs in 07-last-touch/.
* 08-mem-at-10m.md. 024-08, MEM's 327 bytes a KV at 10M keys explained:
  the shape of MEM's keys, not their count (a key of exactly 7 bytes is
  two segments and gets a key node of its own, about 226 heap bytes);
  shown by runs that separate shape from count, and a breakdown by
  class; the cost of key shape for a user, a proposed bound with three
  Mem runs, options (a) to (d), questions Q1 to Q3. Outputs in
  08-mem-at-10m/.
* 09-tie.md. 024-09, the tie of the Lean model and release 2026.4's code
  repaired (024-06's A1 to A4): T-SCHEME's argument written again for
  2026.4's code (it holds; checked on 90 reclaim traces); the draining
  configurations and UnlinkFuzz in the gates (level2.sh, conformance.sh
  drain, unlinkfuzz.sh in night.sh), which P5's head with fault 12 now
  fails; PhysStep proved in Lean; A6 checked; Lean's javaTake made
  Java's integer rule (015-03). On main since 379d8acf. Outputs in
  09-tie/.
* 10-last-operation-wins.md. 024-10, the builder's rule "the last
  operation wins" (CA1) in Java: the rule made exact (R1 for the calls
  on one key as written, R2 for the KVs that key transformations make
  one key: the later call), the 34 cases of which 11 differ from 2026.4,
  the change on the branch 024-10-last-operation-wins (not on main), its
  tests, two expected values changed (for Frans to approve), the same
  stream bytes without repeated keys, what C must change; questions QL1
  to QL5.
* 11-underfill.md. 024-11, the design study of the underfill's fix
  (OP2/ST2 of 024-05): the bound BU1 (every key node that is not a
  segment tree's root holds at least a quarter of a node's klongs, after
  every transaction), the options with their verdicts (merges at the
  delete: yes; borrowing, reclaim's rebuild, compaction: no), the
  algorithm stated for the Lean tree (invariants V1 to V9, theorems TH1
  to TH4, costs CB1 to CB4), a probe on P5's build and a model of the
  fill rules, a plan of about two weeks, questions QU1 to QU8. The
  probe's scripts and outputs and the model in 11-underfill/ (copied by
  the coordinator from the study's bench directory).
* 13-integration.md. 024-13, the integration branch of the day's
  approved changes, gated as one tree: `doubles.py` in 3 s, not 188 s
  (before-commit.sh about 80 s again), 024-10 and 024-07 merged; the
  gates' results. Landed as a780b957; then 024-09 merged and gated,
  landed as 379d8acf.
* 12-tree-model.md. 024-12, the model of BergDB's key tree in Lean, run
  against Java (024-06's B0 to B2): trace format 3 with keys; the tree
  in `lean/SIS/Tree/` as an instance of `Spec` (the searches, get,
  scan, put with the splits, delete with the upward unlink, the empty
  key first, the take-back, reclaim's part, `dirtyNodeBound`, the
  touch); the checker `treecheck` and `treeconf.sh`, step 8 of
  `level2.sh`: on 115 traces the model's own run writes Java's records;
  `treetest`, exhaustive at small node sizes; 27 stated properties, a
  few proved. Branch 024-12-tree-model. Approved by Frans 2026-11-11,
  14:28; on main since 14:56, the merge of 480f83da (gated: lake build,
  treetest, no sorry or axiom, test-traces, before-commit, level1 to
  level3 full).
* 14-merge-thresholds.md. 024-14, the merge's thresholds measured in
  Java at 1M and 10M keys, on a measuring build (P5's merge with fault
  12's fix, the thresholds as run parameters; not landed): the sets P5
  (7/15/15), m8 (8/17/17), m9, dense (10/20/20) and main; no set showed
  a fault or a thrash; with merges at most 1.90 (P5), 1.49 (m8), 1.25
  (dense) times the twin's key nodes, main up to 21.5; the put path's
  price (m8 1 % more bytes a put, dense 4 %); the recommendation m8;
  what is not measured. Probe, scripts and outputs in
  14-merge-thresholds/.
* 15-key-shape-cost.md. 024-15, the cost of key shape documented and
  bounded (024-08, option (a)): Javadoc in `Connection` and `Db` on what
  costs a key node of its own (about 226 heap bytes) and what eviction
  does instead; `Mem` with `-n` and `-keys`; two checks in `level1.sh`
  (SEG at most 230; MEM10M at most 131, full run only); docs/levels.md.
  On main since the merge of 251cd1e0.
* 16-one-operation-a-key.md. 024-16, one operation a key in a
  transaction, strictly (Frans, 2026-11-11): in a builder the last call
  on a key as written wins; a transaction whose key transformations make
  two keys one key is refused before the go point (`Db.transformKeys`,
  a `DbException`, the time given back by `DbClock.transactionCancel`),
  in the Core and the Pub layer; 024-10's rule R2 and what it needed
  removed; no stale index entry possible (024-10's F1); six tests'
  expected values changed. Branch 024-16-one-operation-a-key; its
  review in 16-one-operation-a-key/. On main since 2026-11-11, 14:12,
  the merge of 3af7513e (gated: before-commit, level1 to level4 full,
  unlinkfuzz, conformance drain).
* 17-limits.md. 024-17, the limits of BergDB: of a transaction, a key,
  a value, a record. The discussion with Frans (limits in the user's
  terms, checked; internal bounds proved; a key at most 256 bytes, the
  one limit for a user to remember; most kinds of files should fit);
  today's limits (only the record's 2^31 - 9, and two refusals that
  follow from it); what our own code uses; the cost against the batch
  size at 1M and 10M keys and of values of 16 MiB; the derivation of
  the node bound; a proposed table L1 to L8 (1,000 operations, 256
  bytes a key, 16 MiB a value, 64 MiB a transaction); the idea of
  database sizes S, M, L for later; questions QL1 to QL10. Probes and
  outputs in 17-limits/.
* 18-dead-klongs.md. 024-18, dead klongs in live nodes: what one costs
  (16 bytes each time its node is written, 24 heap bytes, a klong more
  in every lookup), the counts at 100k and 1M keys (0.4 to 0.5 per live
  klong under writes, 0.83 in a cold database with a retain duration),
  and the three options measured: 1 nothing more; 2 compaction at the
  write (by a threshold theta; reclaim's own writes compact cold leaves
  too); 3 by reclaim, in three variants, of which 3c (reclaim's writes
  leave nodes not changed since the iteration began as last versions)
  costs 0 to 3 % bytes and takes the cold case to 0.15. Recommended:
  3c with merges. Measuring patches named; nothing at 10M. Probes in
  18-dead-klongs/.
* 19-node-size.md. 024-19, the node size: which, and one fixed constant
  or not. Postponed 2026-11-11, 11:50, until the merges were in; done
  2026-11-12, 01:33, on format 7 (merges, option 2, CRC32C): 1M and 10M
  counts, times at 1M. Decided (Frans, 2026-11-12): B = 30 kept.
  Recommended: B a property of the
  database (8, 14, 30, 62) with the thresholds and theta scaled v*B/30,
  theta at least 2, 62 the hard maximum. Q1 to Q6. Outputs in
  19-node-size/.
* 20-compact-nodes.md. 024-20, a more compact stored form of an index
  node. Postponed 2026-11-11, 11:50; done 2026-11-12, 02:30, on format
  7: encoding C keeps 38 to 47 % of the index bytes in every workload,
  with compact value nodes, frames and top nodes the stream 19 to 52 %
  smaller; for 2026.6 (Frans, 2026-11-12, QC1), with the stable stream
  format; QC2 to QC5 wait for it. QC1 to QC5; found Reclaim.VALUE_NODE_BYTES stale
  after 024-25. The probe in 20-compact-nodes/.
* 21-merges-java.md. 024-21, merges at the delete in Java, record
  format 7 (2026.4's databases refused): P5's merge ported to main, the
  thresholds 8/17/17 at node size 30 (024-14, QT1), named constants,
  BU1's check, dirtyNodeBound with CB2. Its review in
  21-merges-java/review.md (land with fixes, made). On main since
  2026-11-11, 16:54, with 024-22: the merge of 2679622e (landing
  delegated by Frans, 14:48; gates in 024-13, section 9). QJ1 to QJ3.
* 22-merges-lean.md. 024-22, merges at the delete in 024-12's Lean model
  of the key tree, at 8/17/17; Java equal to it on 260 traces (54,877
  and 4,080 transactions); TP28, TP34 to TP38 proved, TP30 to TP33 left.
  On main with 024-21 (16:54).
* 23-dead-klongs-option2.md. 024-23, dead klongs in live nodes, option 2
  with theta 7 (Frans, 2026-11-11, 024-18 QD1), model first: the rule in
  the Lean tree model and in Java, at most theta dead klongs a node
  after every write; Java equal to the model on 222 traces; reviewed in
  23-dead-klongs-option2/review.md (land with fixes, made). On main
  since 2026-11-11, 18:16: the merge of e0fb9d77. QO1 to QO3; six
  changed tests (section 4.1) accepted by the coordinator for Frans to
  see.
* 24-limits-implemented.md. 024-24, the limits of 024-17 implemented
  (L1 500 operations, L2 111 bytes, L3 56 KiB, L4 8 MiB, L5 32 MiB, L6
  111 bytes refused, the reader reading a record's header first, the
  count with q in Lean); its review in 24-limits-implemented/review.md
  (land with fixes, made). On main since 2026-11-11, 20:19, the merge
  of 829d6135. Q1, Q2.
* 25-crc32c.md. 024-25, CRC32C in place of Fletcher-16 as the node
  checksum (024-17, QL9): the node header 12 bytes, node formats 3/3/5;
  reviewed (25-crc32c/review.md, land with fixes, made). On main since
  2026-11-11, 19:24, the merge of e1a87bec. QC1 to QC3.


Log
===

2026-11-10. Created the item (Frans, 17:52), with what 023-08 put off to
later.

2026-11-10. Frans (19:24): "About 2026.5. I would like to prepare for
this work. What can we do now?" 024-01, an inventory of the candidates,
started 19:26.

2026-11-10. 024-01 written (19:26 to 19:40): 49 candidates; four themes,
(B) recommended; the first questions: the theme, whether 2026.5 opens
2026.4's databases, measuring first, and fix (a) dropped since the window
does not grow (023-10).

2026-11-10. Frans on 024-01's first questions (19:49): "1. The theme. Not
sure. Parts of 2026.4 was pushed to 5. If Release 4 really is "bug-free
database", we don't need to chase bugs. But if there are still issues,
they have priority. I would like your feedback on "stable stream" as a
theme. 2026.5 does not need to open 2026.4 databases. But at some point
we want to publish this and then I would like the stream format to be
more stable. So, working towards a stable stream format is a good aim.
What do you think? 2. No. 3. Measurements on 2026.4 can be done in
parallell when possible, or at night. Start the work on the 2026.5
release directly after 2026.4 is done. 4. I don't know, you can
propose." So: 2026.5 need not open 2026.4's databases; measurements of
2026.4 beside the work or at night; the theme open, "a stable stream"
proposed by Frans for feedback.

2026-11-10. The theme decided (Frans, 19:54): "a stable stream format".
The coordinator's reading of it (19:52, accepted): 2026.4's bugs first;
a byte-level spec of the stream format, checked by the C clone; every
open format question decided once, now or never (merges and compaction,
the builder's "last operation wins", the startup distance in a KV, a
compact key node encoding; a place reserved for objects' storage and
encryption rather than the features); a compatibility rule and a corpus
of saved databases; measurements at 10M to 100M keys at night. Fix (a)
dropped (023-10: the window does not grow); strict cleanup decided in
2026.5 after the measurements. Tonight, after the release: 024-02, the
spec's skeleton; the builder's rule on a branch; the tag measured at 10M
keys if time.

2026-11-11. Release 2026.4 made (04:55; 020-31). 2026.5 started at 04:57
(Frans, 2026-11-10, 19:33: "start to work on 2026.5 without waiting for
me"): 024-02, the stream format's skeleton (done 05:29), and 024-03, the
measurements of 2026.4 at 10M keys (running).

2026-11-11. 024-03, the measurements of 2026.4 (05:03 to 06:29): the
numbers ask for CL7 (the last touch) first among the Core changes, and
for deciding 024-02's Q1 (the merge switch in the format) in 2026.5; P8
not needed.

2026-11-11. The theme changed (Frans, 06:44 to 06:50, with the
coordinator, coord-1111): from "a stable stream format" to **solid
algorithms**. 06:44: "I first though that "stable stream" should be the
theme of the release. But after sleeping on it, I am more more leaning
towards "solid algos". [...] The internal core algorithms of the
database must be right. This is what we want to prove correct. And not
change later." 06:50: "both storage and operations are proportional to
the value they bring to the user"; and "solid" is the worst-case
behaviour and the model and proof catching up: "Both." The aim in four
points, the full quotes and the reasons: 024-04, written 06:55 to 06:57.
The stable stream format follows in release 2026.6 (026); 024-02 is kept
current. The reading of 2026-11-10, 19:52 (above) belongs to the first
theme. Started beside 024-04: 024-05 (the aim against the known cases:
the list, the bounds, the tests) and 024-06 (the model gap: what the
Lean model covers of 2026.4's algorithm).
