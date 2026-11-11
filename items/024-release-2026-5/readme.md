024-release-2026-5
==================

Created 2026-11-10 by Frans Lundberg. Status: open.

Release 2026.5 of BergDB, after 2026.4 (020): its plan, its decisions and
the work towards it. Frans, 2026-11-10, 17:52: "Time to create the
nnn-release-2026-5 item? We are already planning for it, so why not."
Its theme: **a stable stream format** (Frans, 2026-11-10, 19:54: "OK,
release theme decided, "a stable stream format".").


Planned so far
==============

What Frans has put off to 2026.5 or to after 2026.4, with where it was
decided. Nothing else is decided.

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
  format, so that 2026.4's databases need no refusal.
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

* **A time klong's unused bits** (56 to 61) are not checked:
  `StoredKeyNode.parse` should refuse a time klong whose bits 56 to 61 are
  not zero ("Bad time klong", a `StreamFormatException`, beside its check
  of the klong's type, 019-32). Found by CorruptStreamTester's seed 20775
  (the night of 18 November): such a damage makes a start with -ea fail
  an assertion in `KeyNode.addKlong`; without -ea the database starts and
  answers right. Old, on `main` before 023 too. A case of the stable
  stream format: bits that must be zero are checked.

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
