012-02. Task: the stream format, written down
=============================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase A (012-01, section 8). Effort: max. After: nothing.

This file is the task's plan now. When the task is done it is the format
document itself: sections 1 to 9 below are written, and this plan becomes
its last section, "How it was made".


# 1. The goal

A complete definition of BergDB's stream and directory, as Java writes
them at the reference commit: every byte, so that a second implementation
can read and write them. Today the code is the only definition (012-01,
3.1); `core/doc-files/stream-format.txt` of 2015 is partial and out of date
in places.

Done when:

1. Every field of the meta block, the framing, the record and the three
   nodes is described: its offset, size, type, meaning, range, and the
   Java method that writes it and the one that checks it on reading.
2. The directory is described: file names, sizes, how a file is chosen,
   what a cut removes, what Java refuses (`BadDirStateException`).
3. What decides the bytes is described, at the level a writer needs:
   which index nodes a record holds and in what order (the take), the
   startup position, `topPos`, ids and vpos, the got-dirty list, the
   padding, the creation's 264 bytes, the dummy transaction, reclaim's
   table. Each points to the Java code that decides it.
4. The determinism audit (section 3, step 4) is done and written.
5. `StreamScan`, Java's scanner, prints every field of a stream, and every
   field it prints is in the document. It runs on every stream of 012-05's
   sets without an unexplained line.
6. The differences from `stream-format.txt` are listed (one is known: the
   meta block's last byte is 10, not the 1 of `MetaBlock`'s comment).


# 2. Read first

* Java: `MetaBlock` (126 code lines), `RecoverableStream` (421),
  `StoredTrans` (521), `StoredKeyNode` (112), `StoredTopNode` (142),
  `StoredValueNode` (142), `NodeChecksum` (46), `NodeStream` (241),
  `Klong` (191), `Keys` (197), `Spos` (26), `FileStream` (661, the naming,
  the sizes and the cut), `TransSeq` (186, the take), `Db`'s creation
  (`writePrimordialTransaction`), `setStartupDistance`, and
  `Reclaim.IterationInfo` with `StringMap`.
* `core/doc-files/stream-format.txt` and `key-encoding.md`.
* `docs/sis-model.md` (records, D, the startup position) and 011-11, the
  Level 2 alignment, for the meaning of the record's fields.
* 012-01, section 3.


# 3. The work

1. **Pin the reference.** Record `main`'s HEAD; the document describes
   that commit and says so at its top.
2. **`StreamScan.java`**, first, as 012-05 needs it: a program in package
   `bergdb.core` (to reach the parsers) that reads a directory or a flat
   file and prints one line per item: each meta block with its fields; each
   record's header; each node with all its fields (klongs and pointers in
   decimal and hex, values as length and SHA-256, keys as hex); the
   got-dirty list; the padding (and whether it is zero); the last byte. A
   fixed text format, documented in the file's header, which C's scanner
   (012-06) prints too. It lives in the C directory's
   `test/cross/java/` (012-01, decision D1) and is compiled against the
   Core Layer as 012-01, 6.3 says.
3. **Write sections 1 to 9** (below), reading each field's writer and
   reader, and checking each claim with `StreamScan` on streams made for
   the purpose (a few `CoreSame`-like workloads: node sizes 8 and 30, a
   small startup distance, reclaim, a setStartupDistance, a crash).
4. **The determinism audit.** Every use in the Core of hash-ordered
   collections (`HashMap`, `HashSet`, `IdentityHashMap` and their
   iteration), `Random`, clocks (`currentTimeMillis`, `nanoTime`, and
   every read of the database's clock, which 012-01, 4.4 found at two
   points of `DbClock`), `identityHashCode`, floating point, and thread
   timing, as far as the writer, the startup and reclaim reach: for each,
   whether it can change the bytes, and why not. 012-01, 3.2 found the
   first ones harmless (`DbStarter`'s maps, `Dag.dirtyNodeBound`); this
   completes the list. A real dependence is a Java bug (P2): registered in
   005, and C follows Java's behaviour until it is fixed.
5. **Review** at max effort by a second agent that did not write it: the
   document against the code, field by field.

The document's sections:

1. The reference and the versions (meta 154, record 5, top 2, key 2,
   value 4) and what each version covers (`MetaBlock.CURRENT_VERSION`,
   `StoredTrans.RECORD_FORMAT`).
2. Numbers, positions and alignment: little-endian; positions; vpos;
   `Spos.NULL`; alignment 8; how positions skip meta blocks
   (`RecoverableStream.getSpos`).
3. The meta block.
4. The framing and recovery: records, the last byte, the torn record and
   its fill (`TORN_HEADER_FILLER`), an incomplete creation.
5. The record.
6. The nodes: top, key, value and delete; Fletcher-16 and the zeroed
   checksum bytes; klongs and their types; serialized references.
7. Keys: ikey, bkey, segments, compare values, order.
8. What decides the bytes (done item 3), with the internal keys
   (`/#i/-dummy`, `/#i/dreclaim/...`) and the text of reclaim's table.
9. The directory.

Then: the determinism audit; the differences from 2015's text; the
scanner's format.


# 4. Tests

`StreamScan` on every stream of 012-05's sets; and two runs of one
workload in two JVMs give the same scan (P2, as a check of the audit).


# 5. Notes

* Describe what Java does, also where it looks odd; propose nothing. A
  question for Frans goes at the end, with options.
* Decision D6 of 012-01 decides where the document lives once C writes
  Java's bytes.


# 6. Progress

Not started.
