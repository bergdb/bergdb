012-06. Task: the stream reader
===============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done 2026-10-28 16:50** (started 16:00);
approved with 012-01 by Frans's go (012-01, 9.1).
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


# 6. Decisions

Taken in this task, as the plan left them to it.

1. **The stream interface: two plain implementations behind one header**
   (`src/stream.h`), a kind and a switch, not a struct of function
   pointers: the simpler (step 1). A memory stream (`MemoryStream`: reads
   with its refusals, raw appends, `pretruncate` to a multiple of
   1,000,000 as its arrays, `truncate` for crash tests) and the directory
   (`FileStream`'s files and checks). An I/O seam for 012-14's faults can
   go into `plat` later, where the system calls are.
2. **The platform module is `plat`** (`plat_`): a directory's entries
   sorted by name, `stat`'s size as `File.length()`, `open`, `pread`,
   `close`, with POSIX 2008 (`_POSIX_C_SOURCE`). Writes, forces
   (`F_FULLFSYNC`), the lock and the clock come with 012-09 and 012-10.
3. **The directory stream is read-only here**: no lock, no file or
   directory created (Java's `FileStream` creates both; 012-09 writes). An
   empty directory is an empty stream; a missing one is `ERR_IO`.
4. **The parsed nodes are plain structs, views into the bytes they were
   parsed from** (`struct sn_node`, `src/snode.h`): the fixed fields
   decoded (type, position, id; a top node's ordinal, root time, root and
   h; a key node's prevPos, leaf and n; a value's stored offset, tpos,
   `offsetFromTrans`, value and key), the arrays read by accessors
   (`sn_skip_pos`, `sn_skip_time` with `TopNode`'s rule of −1 for an unset
   pointer, `sn_klong`, `sn_ref`, `sn_seg`). They own nothing and the
   parser allocates nothing per node; a record's node array is one
   allocation, grown and reused (`st_record`). 012-07 makes its in-memory
   nodes from them: its handles, counts and node table (012-07, step 1)
   are its own design, which the parser does not pre-empt, and a startup
   (012-10) parses a record, builds its nodes, and drops the bytes.
5. **Errors** (`src/err.h`): a code (`ERR_IO`, `ERR_FORMAT`, `ERR_ARG`,
   `ERR_NOT_AVAILABLE`, `ERR_NOMEM`, as 012-03's planned enum), the simple
   name of the exception that Java throws in the same case, and a text in
   the struct (no allocation). The tests compare the exception's name with
   Java's (`records.txt`); 012-03's `bergdb.h` maps the codes.
   `BadDirStateException`, an `IOException` in Java, is `ERR_FORMAT` (a
   directory that other software changed).
6. **Java's asserts on the stream's bytes are checks in C**, refusals with
   `ERR_FORMAT` and "AssertionError": `StoredTopNode.parse`'s size field
   against 40 + 16 h, `bytesToNode`'s buffer length, `Parser.parse`'s
   lastPos. Java's gates, tests and scanner run with `-ea`, where they
   refuse; Java without `-ea` would take such a (corrupt) stream.
7. **Bounds as Java's arrays have them**: a parser reads within the buffer
   it is given (a record's bytes, as Java's array), so a field past a
   node's size field but in the record is read as Java reads it, and a
   read past the buffer is `ArrayIndexOutOfBoundsException`.
8. **Two refusals that Java does not make, where Java hangs or runs out of
   memory** (findings F2 and F3): a negative node size in a record
   (`st_parse`), and a record or node size larger than the stream's bytes
   left, refused with the read's error before its buffer is allocated
   (`ns_iter_next`, `ns_read_node`, `ns_read_trans_bytes`).
9. **The scanner** (`tools/scan.c`, `bergdb-scan`) ports `StreamScan`
   line for line: its view of the directory (14-digit names, the
   "other" lines) is the tool's own, through `plat`, and its reads go
   through the library's stream (the directory, or a flat file read into
   a memory stream). Its checks run C's parser and walk; their error lines
   say "C's parser refuses ..." and "C's record walk fails ..." with C's
   error. Where `StreamScan` throws (a directory it refuses, a short
   value node at a record's end, finding F1), it prints what Java's
   `Batch` prints, the text up to there, and exits with status 3, the
   reason on standard error. Status 4 if the allocator's count is not 0 at
   the end.
10. **cross.sh, the C side**: side B scans the crash variants too, and
    both sides scan **corrupt variants**: copies (APFS clones) of side A's
    views of a few workloads with one bit flipped, at the fields of the
    records, nodes and meta blocks that the scan shows and at random
    positions, and with the first file cut by a byte, the second removed
    or the last renamed (quick: 2 workloads, 85 variants; full: 6
    workloads, about 500). Scans of crash and corrupt variants must have
    the same exit status and the same text but for the text of the error
    lines (`compare_scan`), which is each implementation's own; the main
    scans compare exactly. Without `C=` the same runs Java against Java.
    The gate runs the quick set with `C=build/test` (the sanitizers).
11. **Vectors**: `Vectors.java` writes `records.txt` too (47 kB): a small
    stream that `Db` writes (MemoryStream, node size 8, startup distance
    100, 14 transactions), its 15 records as `StoredTrans.parse` parses
    them at their positions and 40 bytes before a meta block (so that the
    value nodes' stored offsets differ from their distances, 005-34), and
    359 records with one change (the checksum made right again where the
    change is to reach a parser's own check) with Java's exception.
    `t_records.c` reads it (long lines: a reader of its own).


# 7. Findings, and differences from 012-02

No Java bug blocks the reader. For the conductor (005 entries are the
conductor's):

* **F1. `StreamScan` reads a value or delete node's first 24 bytes
  before it checks the node's size.** A node of 8 to 23 bytes at a
  record's end (a corrupt stream) makes it throw
  `ArrayIndexOutOfBoundsException` instead of printing an error line:
  status 3 in `Batch`; `StreamScan.main` exits with 1 and loses its
  buffered text (no flush on an exception). C does the same (status 3).
  Suggestion for 012-02's `StreamScan`: check the size (24 for a delete,
  28 for a value) first, with an error line, and flush in `main`.
* **F2. `StoredTrans.Parser` takes a negative node size** and moves its
  offset back. A crafted record loops for ever, its node list growing until
  `OutOfMemoryError` (an `Error`, not a `StreamFormatException`). Probe
  (in `bergdb.core`, against `build/java/classes`, `-Xmx256m`): a
  record of 112 bytes, format 5, a delete node at 32 (size 32, its
  checksum right, stored offset 32, one key segment), and at 64 a
  "node" of size −32, type 40, format 4, checksum 0 (over no bytes),
  stored offset 64, key size 8; `StoredTrans.parse(128, r)` gives
  `java.lang.OutOfMemoryError: Java heap space` within 3 s. The scan is
  not affected (its own walk refuses node sizes below 8 first). C refuses
  (decision 8). A 005 candidate: refuse a node size below 8 (or 6) in
  `Parser.next`, as `readNode` refuses 6 and less.
* **F3. A record's or node's size is allocated before its bytes are
  read** (`TransIterator.next`, `readNode`, `readTransBytes`): a corrupt
  size near 2^31 gives `OutOfMemoryError` in a small heap, which
  `StreamScan.checkJavaWalk` does not catch (status 3). C refuses with the
  read's error first (decision 8); a scan of such a stream differs (not met
  in the corrupt variants, whose single-bit flips give at most 1 GB).
* **F4. `StoredTopNode.parse`'s "TopNode ID too large" is dead**: the
  ordinal, `bytesToLongLE(...) >>> 16`, is at most 2^48 − 1 =
  `MAX_TOP_NODE_ID_VALUE`. Harmless; C keeps the check.
* **F5. `FileStream` names**: `stringToIndex` uses `Long.parseLong`, which
  takes a sign (`+6.bergdb` is file 6, `-0.bergdb` file 0) and non-ASCII
  decimal digits. C takes the sign, not the non-ASCII digits (a name Java
  never writes). `checkDbFiles` checks each file in name order, its name,
  then (but for the first) its start, then its size: a file before the
  last with a bad size is refused before a gap after it.

**012-02** (read in the 012-02 clone, sections 1 to 13): the reader agrees
with it. To add there: F4 (6.2: the ordinal's check cannot fail); F5
(9.5: the sign, and the order of the checks); 4.4: a torn header whose
four size bytes read 5 is left whole by recovery (its "last byte", byte 4,
is the filler 4), and sizes 6 to 16 are zero-filled, and the start's walk
then refuses either ("Bad transaction size", below 17); only a corrupt
size field gives these, as Java writes records of 48 bytes or more.
Neither changes a byte that Java writes.


# 8. Progress

**Java reference:** `main` at `0b6d08e`, `java/` as of `fd8f513`.
**Clone:** `/Users/f/fl/bench/012/06-stream-reader/` (a clone of
`bergdb` at `0b6d08e`), committed locally; the conductor copies the files
in.

* 2026-10-28 16:00: started; read 012-01, this task, 012-05 section 6,
  `StreamScan`, 012-02 (sections 1 to 7, 9, 11, 12) and the Java classes.
* 16:12: steps 1 to 5 (`bc36dd1`): the modules `err`, `plat`, `stream`,
  `meta`, `rstream`, `snode`, `strans`, `nstream` (2,400 lines with
  their headers and comments) and `tools/scan.c` (`bergdb-scan`, 950 lines, with
  `tools/sha256.h`). `cross.sh quick C=build/test`: the scans of all 10
  workloads by C equal Java's at the first run (side B's 20 scans by C).
* 16:20: step 6 and the tests (`c9deea7`): `cross.sh`'s corrupt variants
  and side B's scans of the crash variants (quick: 64 crash cuts and 85
  corrupt variants, 0 differences; 81 of the 85 refused or with error
  lines, mostly checksums, so the field checks are tested by the vectors);
  `records.txt` and `t_records.c`, `t_rstream.c` (Java's `MetaBlock` and
  `RecoverableStream` tests, the recovery plans of its crash tests, an
  incomplete creation, `getPosOfTransCompletedBefore` in a cut stream,
  the walk's refusals), `t_stream.c` (the memory stream; a directory, its
  names, gaps and sizes). 99 unit tests, 28,091 checks. The gate:
  `C BEFORE COMMIT OK (35 s)`.
* 16:24 to 16:46: `cross.sh full C=build/test`: **CROSS full OK: 278
  workloads, 1262 crash cuts, 918 corrupt variants, 6 in turns, the
  planted difference at 1164 was found and explained** (1,286 s): every
  scan of side A's and side B's views, of the 1,262 crash cuts and of the
  918 corrupt variants (853 refused or with error lines) by C equals
  Java's. The corrupt variants took 450 s there (150 flips per workload,
  mostly the clones); the full set now draws 80 (about 500 variants, the
  first 80 draws of the same seeds, so a subset of those that passed),
  for about 18 minutes in all.
* 16:48: `records_negative_node_size` (finding F2's record: C refuses
  it; with the end of the nodes there, taken). `cross.sh quick` without
  `C=` (Java against Java, the new parts too): OK (25 s). The gate:
  **C BEFORE COMMIT OK (34 s)**, 100 unit tests, 28,097 checks.

**Done.** Every item of "Done when" holds: the directory and memory
streams with `FileStream`'s checks; the meta blocks with their checks and
the node size of 005-50 (`rs_check_node_size`); the framing, the reads
across meta blocks and recovery's plan; the records and nodes with Java's
checks, on Java's vectors; `bergdb-scan` equal to `StreamScan` on every
stream of the quick and full sets and their crash variants; corrupt input
refused where Java refuses it, never a crash, under the sanitizers.
**Next:** 012-07, the index nodes, from `struct sn_node` (decision 4).
The conductor: the findings F1 to F5 (F2 a 005 candidate; F1 a change to
`StreamScan`, 012-02's), and the files to copy in: `c/src/{err,plat,
stream,meta,rstream,snode,strans,nstream}.{c,h}`, `c/tools/{scan.c,
sha256.h}`, `c/test/unit/{t_stream,t_rstream,t_records,main}.c`,
`c/test/unit/vectors/records.txt`, `c/test/cross/{cross.sh,
java/Vectors.java}`, `c/before-commit.sh`, `c/readme.md`, and this file.
