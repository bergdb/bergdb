005-72. Decide: the files after reclaim's physical cut depend on timing
======================================================================

Status: done (decided: B dropped; 2026-11-05, see "Decision,
2026-11-05"). Kind: decide. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-02's determinism audit (012-02, section 10.3, finding C2; question Q1
in its section 13).


The issue
---------

Reclaim decides a cut (`getFirstAvailablePos`) and makes the physical cut
later, at the first user transaction at which the durable length has
reached the length at the decision (`Reclaim.cutIfDurable`). The durable
length grows by the buffer's thread (20 ms) and by syncs, so when the cut
is made is timing. `FileStream` sizes each new file from its distance to
the first position, so the names and sizes of the files after a cut
depend on when it was made. The bytes from the decided cut do not: P2
holds for the stream, not for its files.

Probe (012-02, `CutLayoutProbe`): 1,500 transactions 10 ms apart,
10,000-byte values on 50 keys, startup distance 200,000, retain 1 s, in
four modes: the decided cut (15,861,104), the length (18,207,728) and the
SHA-256 of the bytes from the decided cut are identical in all four; the
physical first position and the files holding the bytes differ.

Related (012-02, finding C1, not a bug): a restart reopens the last file
with a capacity from the last two files' lengths, so the file layout also
depends on where the restarts are, while the concatenated bytes do not.

Why it matters now: the C clone has no threads, so its cut is made at its
own points; its directory after a cut cannot match Java's file for file.
012's cross tests (012-05) compare files.


Options
-------

* **A.** Accept it: compare the concatenated bytes from the decided cut for
  workloads with reclaim, as `StreamDigest` does (012-01, 3.2, point 8);
  files elsewhere, with the same restart points.
* **B.** Make the file layout a function of the stream: for example, size
  new files from the decided cut instead of the physical first position.
  A Java change, a format-neutral one.
* **C.** Leave 012-01's done item 3 ("the same files, with the same names
  and bytes") as it is, which is then not reachable with reclaim.

Recommended (012-02): A now, so that 012's cross tests compare what is
deterministic; B can be decided later, on its own merits.


Decision
--------

Frans, 2026-10-29, 12:41, on 012-02's Q1: "(a) is good as long as there is an item in 005 to consider (b)". So A for 012's cross tests, done since 012-11 (`e068fba`:
workloads with reclaim are compared from the decided cut). This entry
stays open to consider B, a Java change on its own merits.


Done when
---------

B decided; if taken, the change with its gates (and the C clone's
`FileStream` port, in 012's `c/`, brought in line by hand, as C is a
separate project).


Decision, 2026-11-05
--------------------

Frans, decided 2026-11-04/05 (asked 2026-11-04, 19:23; answered
2026-11-05, 07:17): "Drop B, close". A covers what matters: the bytes from
the decided cut are deterministic, and the C clone's cross tests compare
them (012-11). A file layout that depends on timing has no effect a user
can see. So B is dropped and nothing changes in `java/` or in 012's `c/`;
"Done when" is met (B decided, not taken). 015-08, `StreamDigest compare`
reporting the physical cut's fields, is a fix of its own and stays open.


Log
---

2026-11-05. Closed as done at Frans's decision ("Drop B, close"): A
covers what matters; B dropped.
