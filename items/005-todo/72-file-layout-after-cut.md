005-72. Decide: the files after reclaim's physical cut depend on timing
======================================================================

Status: open. Kind: decide. Created 2026-10-28.

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


Done when
---------

Decided; for A, 012-05's `compare_dirs` compares the bytes from the
decided cut for workloads with reclaim before 012-11; for B, the change
with its gates.
