012-06. Task: the stream reader
===============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase B (012-01, section 8). Effort: high. After: 012-02, 012-04, 012-05.


# 1. The goal

C reads every stream that Java writes, at the level of the format: the
storage, the meta blocks, the framing, the records and the nodes. No index
and no reads of keys yet; those are 012-07 and 012-08. The first C tool,
`bergdb-scan`, prints what Java's `StreamScan` prints.

Done when:

1. **Storage.** A memory stream (for tests), and the directory as
   `FileStream` keeps it: the `.bergdb` files found, checked and ordered as
   Java does (names, sizes, gaps; the same refusals as
   `BadDirStateException`), the first position and the length, and reads
   at any position, across files. Read-only in this task; appends come in
   012-09, cuts in 012-11.
2. **Meta blocks.** Parsed and checked as `MetaBlock` and
   `RecoverableStream` do: the magic bytes, the version (154; another is
   refused as Java refuses it), the last byte, the node size (0 refused, as
   since 005-50).
3. **Framing.** Positions that skip meta blocks (`RecoverableStream.getSpos`
   and its inverse), a record's bytes read across a meta block, and the
   last whole record found from the last valid meta block as recovery
   finds it, without writing anything (the fill comes in 012-10).
4. **Records and nodes.** `StoredTrans.Parser`'s checks and fields, and the
   three nodes as `NodeStream.bytesToNode` reads them, with their
   checksums checked as Java checks them.
5. **`bergdb-scan`** prints, for every stream of 012-05's sets and their
   crash variants, exactly what `StreamScan` prints; `cross.sh` compares
   the scans with C as side B.
6. **Corrupt input** gives an error code with a text, never a crash: a
   first test flips random bytes of reference streams and cuts files, and
   runs the scanner under the sanitizers.


# 2. Read first

* 012-02, the format; 012-05, the harness and `StreamScan`'s format.
* Java: `RecoverableStream` (421 code lines; the recovery and the reads,
  not the appends), `MetaBlock` (126), `StoredTrans` (the parser),
  `StoredKeyNode`, `StoredTopNode`, `StoredValueNode`, `NodeStream`
  (`bytesToNode`, the trans iterator), `NodeChecksum`, `FileStream`
  (`handleExistingFiles`, `checkDbFiles`, `getSortedDbFiles`, the reads),
  `MemoryStream`, `AppendOnlyStream`.


# 3. The work

1. The stream interface in C: read at a position, the first position, the
   length; later append, force, truncate and cut. One small struct of
   function pointers, or two plain implementations behind one header:
   choose the simpler.
2. The memory stream; the directory stream (POSIX `open`, `pread`,
   `opendir`), in the module that holds the platform (012-01, 4.2).
3. Meta blocks, the framing and positions, the record and node parsers,
   each with unit tests on Java's bytes (vectors from 012-04's
   `Vectors.java`, extended with whole records and nodes).
4. The trans iterator: records in order from a position, as Java's
   `NodeStream.TransIterator`.
5. `tools/bergdb-scan`, and its place in `cross.sh`.
6. The corrupt-input test (done item 6).


# 4. Tests

Unit tests per parser; the scan comparison on the quick and full sets;
the corrupt-input runs. The gate runs the quick set.


# 5. Notes

* Parse as Java parses: the same checks, in the same order where an error
  depends on it, the same refusals. A stream that Java refuses, C refuses.
* The parsed nodes are the in-memory nodes of 012-07, or plain structs
  that 012-07 turns into them; decide with 012-07's design in mind.


# 6. Progress

Not started.
