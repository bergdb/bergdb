# 031-07. The stream's checks of integrity: the inventory and the options

A study, 2026-11-27, 18:52 to 19:40, by an agent of lead-1127, for
031-07's questions (its readme, section 3); for Frans to decide from.
`main` at `17c7c7db` (2026-11-27): record format 9, meta block version
155; 028-67's C1 and C3 are decided (2026-11-27, 15:50 to 16:02) and not
built (031-06's landing, step 4). Read: 031-07's readme, 027-03
(sections 4 to 9, 14, 18 to 20), 017-08, 024-25, 024-28 (section 7),
014-01 (sections 3 and 7), 028-60, 028-66, 028-67, 035-02 (sections 10
and 11), 027-14, 010-01 and 010-04, 030-04 (section 3.5), 031-06
(section 9), and the code on `main`. Line numbers are `main`'s at
`17c7c7db`, in `java/src/bergdb/`; 027-03 cites the lines of the tag
`release-2026.4`, which have moved.

One probe was written and run (**ran** below; `probe/`): every byte of
CorruptStreamTester's four workloads flipped (20,000 random ones in the
largest), its header-field sets and
cut-outs, and stale tails as 035-02 made them, each copy started, with
the check that refused it recorded; once with the node checksum and once
without it (a shadow `NodeStream` with the check switched off,
`probe/nochecksum.diff`). Nothing in `java/` or `lean/` was changed, and
no timing run was made: the CPU figures are estimates from figures
measured before (marked **inferred**).


## 1. In short

* **The inventory** (section 3): 44 checks, K1 to K44, from the files to
  the start's checks of meaning, the reads, and the development tools;
  the bytes no check covers end sections 3.2, 3.4 and 3.5; section 3.9
  has the checks decided for 2026.7.
* **What they serve** (section 4), each by its main purpose: 6 serve
  the one expected fault, the partial append (K3, K5, K7, K12, K13,
  K15), and 5 more serve it in part, against another file's bytes at the
  tail (K4, K9, K14, K19, K26); 23 find storage damage, a best effort; 9
  are development checks (K16, K34, K38 to K44); 6 have other purposes
  (versions, the node size, the lock, a caller's position).
* **The probe** (section 4.5): 255,169 damaged copies. With the node
  checksum no copy answered wrong values but the damage known and decided
  (171 of 019-30, 18 of 019-31, 1 of 015-73); without it 59,596 did, 54,944
  of them among the 94,272 flipped bytes of value nodes. Of 4,783 stale
  tails the node checksum refused 10, each refused by another check when
  it was off; 2 took another database's records as their own (S1), with
  or without it: the case that 028-67's C3 closes.
* **Recommendations** (section 5):
  * the node checksums stay as they are (N1);
  * the got-dirty list gets nothing new (GD1), the meta block C3's own
    position and database ID and nothing more (M1);
  * the header check stays 24 bits in bytes 5 to 7, as decided (W24): the
    low 24 bits of CRC-32C over the database ID, the record's position
    and the header's 29 bytes, checked at every parse of a record and by
    C1's recovery;
  * the principle is written as a rule, R6 of 010-04, in the words of
    section 5.4, and the Javadoc that state it today cite it.
* **For Frans** (section 7): the four decisions; a rule or a principle;
  whether another file's bytes at the tail are a face of the expected
  fault in R6's words (028-67's C2, open).


## 2. Terms

* *SFE*: `bergdb.storage.StreamFormatException` and its subclasses
  (`BadMagicBytes`, `VersioningStreamException`,
  `StreamChecksumException`).
* *Refuses*: a start throws, before or after recovery's fill; "nothing
  written" when the check comes before any append (027-03, section 7,
  G18). *Fails the database*: a read meets the SFE, and every later call
  throws `DbFailedException` (P7).
* *The expected fault*: a partial append, which leaves at the stream's
  end a part of a record, or zeros within the last file's length
  (028-60). Another file's bytes within that length (035-02) are refused
  with the cause and tied to their place from 2026.7 (028-67, C1 and
  C3); whether they are a third face of the fault, cut at a start as
  zeros are, is 028-67's C2, open.
* *Stale tail*: 035-02's case, the bytes of a deleted file from a page
  boundary Z to the last file's length.


## 3. The inventory

Each check: what it checks; where it is written and verified; its cost;
what it detects; what happens when it fails. Bytes are the stream's
bytes; a KV is a value or delete node.

### 3.1. The files (`stream/FileStream.java`)

* **K1. The files' names and lengths** at an open: a name that is a
  number (leniently, 027-03, G15), each file beginning where the one
  before ends, every file but the last a multiple of 100,000 bytes.
  * Written by `newFile`; verified by `checkDbFiles` (:1197), from
    `handleExistingFiles` (:1104).
  * Cost: none in the stream; a directory listing at an open.
  * Detects: a file missing from the middle (a gap), a renamed file, a
    file other than the last cut short.
  * On failure: `BadDirStateException` (an `IOException`, not an SFE);
    the start refuses, nothing written. 028-66's rule (Frans, 2026-11-27,
    17:26; not on `main`): a start deletes the files before a gap only if
    their first meta block is this database's, else refuses.
* **K2. The lock** (`bergdb.lock`, an OS lock on byte 2^62): another
  stream holding the directory.
  * Verified at the open (:886 to :945); no bytes in the stream.
  * On failure: `DirectoryInUseException`; the open refuses.
* **K3. The zero tail** (028-60, part 2): a run of zero bytes of at most
  8 MB at the end of the last file is left out of the stream at the
  open, and the first append truncates the file there.
  * Verified by `zeroTailLength` (:1590; `ZERO_TAIL_MAX`, :240); the cut
    at the first append (:1954).
  * Cost: a read of the last file's end at an open, up to 8 MB.
  * Detects: zeros that a kill during an append left (macOS, APFS;
    035-01). It relies on K7 and K15: a valid meta block and a committed
    record end in the byte 10.
  * On detection: a silent repair, by design (Frans, 2026-11-26).

### 3.2. The meta block (`storage/MetaBlock.java`, `storage/RecoverableStream.java`)

* **K4. The magic bytes** "berg" at offset 0 of every meta block read.
  * Written by `MetaBlock.initBlock` (:84) and in recovery's
    `FILL_OUT_TEMPLATE` (:65); verified by `RecoverableStream.readMetaBlock`
    (:858, `BadMagicBytes` at :890).
  * Cost: 4 bytes every 200,000.
  * Detects: bytes at a meta position that are not a meta block's: a
    stale tail at another delta, a stream that 2026.3 or earlier
    encrypted, damage.
  * On failure: a start refuses with "Invalid magic bytes", nothing
    written (`Db.startInner`, `core/Db.java`:1286); a read that searches
    the blocks fails the database.
* **K5. A block of 128 zero bytes is not valid** (028-60, part 1):
  `readMetaBlock` (:879). Detects zeros over a meta position; the block
  is passed over, silently, and the one before is taken.
* **K6. The version**, 155, an `i32` at offset 4 (bytes 6 and 7 since
  019-01): `readMetaBlock` (:893 to :898), `versionRefused` (:928).
  Written by `initBlock`. 4 bytes every 200,000. Detects a stream of
  another release; damage of bytes 4 to 7 reads as a version. On failure:
  `VersioningStreamException`, nothing written.
* **K7. The last byte 10**, the block's validity: `MetaBlock.isValid`
  (:245, :255), taken by `readAValidMetaBlock` (`RecoverableStream`:838).
  Written by `initBlock` (:88). 1 byte. Detects a block that a crash cut;
  such a block is passed over, silently. `fixMetaBlockIfNeeded` (:498)
  completes a block that the stream's end cuts, as an invalid one
  (the template, or zeros after zeros).
* **K8. The block's fields** (`MetaBlock.checkFormat`, :127, for a valid
  block): lastTrans −1 or not negative, a time not negative. An SFE.
* **K9. lastTrans in range** (`RecoverableStream.checkLastTransSpos`,
  :186; 019-34, 019-40): −1, or from max(128, the stream's first
  position) to before the block. An SFE before recovery writes.
  Detects a damaged lastTrans, and a block of an older file of the same
  database at the same offset (168 of 168 such stale blocks in 035-02,
  section 10.3).
* **K10. The node size** (`Db.refuseOtherNodeSize`, `core/Db.java`:1769):
  0 or above 62 is an SFE ("damaged"); another size than the start's is
  an SFE. Written by `Db.writePrimordialTransaction` (:1832). 2 bytes.
  Nothing written.
* **K11. A valid block exists** (`recover`, :153; for reads,
  `getPosOfTransCompletedBefore`, :720, :751). An SFE.

Not checked: the database ID (16 bytes at offset 24, written by
`writePrimordialTransaction`, :1831), compared with nothing; read only to
write a missing `created.txt` (`Db.java`:1712). The time (offset 8) is
read only by K8. Bytes 40 to 43 and 46 to 126 are reserved, not checked
(027-03, G7). There is no checksum of the block.

### 3.3. The framing and recovery

* **K12. An incomplete creation** (`RecoverableStream.isIncompleteCreation`,
  :215; `holdsFirstTransactionAlone`, :266; `Db.refuseIncompleteCreation`,
  `Db.java`:1735; 005-33, 028-18): a stream of at most the creation's
  length that holds a part of it, or the primordial record alone.
  Detects a crash while a database is made. On detection:
  `DatabaseNotCreatedException`, nothing written.
* **K13. Recovery's walk and fill** (`fixLastTransactionIfNeeded`, :329;
  `transHeaderFixBytes`, :369; `appendZeros`, :404): from the record that
  the last valid block names, by the records' sizes alone, to the end; a
  torn last record is completed with zeros and its last byte left 0
  (aborted). A size below 5 is an SFE (:355).
  * Cost: the reads of the walk; the fill, at most the torn record's
    size.
  * Detects and repairs the torn tail: the expected fault's own
    mechanism.
  * On failure: a refusal, possibly after a fill: a size read from
    damaged or stale bytes can append up to 2 GB first (014-01, 005-83's
    case; CorruptStreamTester's KNOWN); 028-67's C1 is to stop that.
* **K14. The record's size at the walk** (`NodeStream.readRecordHeader`,
  `core/NodeStream.java`:264: at most 16, or above `MAX_RECORD_SIZE`,
  :269, :273; `checkReadSize`, :305, a record beyond the stream, :312;
  `RecoverableStream.Iterator.next`, :975). An SFE, before the record's
  array is made (024-17, QL7).
* **K15. The record's last byte** (`readRecordHeader`, :283;
  `TransIterator.next`, :523): 10 committed, 0 failed (skipped), anything
  else an SFE; a record at an exact start position must be committed
  (:286, :576; 005-28). Written by `StoredTrans.Serializer.serializeEnd`
  (`core/StoredTrans.java`:949); recovery leaves 0. 1 byte a record.
  The commit mark: a record counts only if its last byte, written last,
  is 10.
* **K16. The append's own checks** (`RecoverableStream.append`, :585, with
  `useChecks`): the buffer's last byte is 10 and its size field its
  size; the stream not in the middle of a meta block. An
  `IllegalArgumentException` or an SFE: the writer checks itself.
* **K17. A caller's position** (`NodeStream.recordHolding`, :470;
  `TransIterator.next`, :553; 021-27): a large size at a caller's
  position in `Db.getTrans` is believed only at a record's start. An
  argument check (010-04, R5).

### 3.4. The record (`core/StoredTrans.java`, `core/Db.java`, `core/DbStarter.java`)

* **K18. The format byte**, 9 (`readRecordHeader`, :293, before the
  record is read, for a committed record; `StoredTrans.Parser.parse`,
  :461). Written by `serializeHeader` (:870). Detects a stream of another
  release; damage of byte 4 reads as another format. On failure:
  `VersioningStreamException`.
* **K19. The parser's structure** (`Parser.parse`, :428 to :531;
  `next`, :537 to :561): the size from 41 and within the buffer (:453);
  nodes until an end marker (:539), each from 12 bytes and within the
  record (:553); the got-dirty count within the room left (:490, :497);
  room for the padding (:515); and the content filling the size exactly
  (:524; 015-72). Each an SFE. In the probe the parser's checks of the
  node size and the end marker refused most flips of a node's size field
  and of the end marker (section 4.5).
* **K20. startupPos** (`Db.checkStartupPos`, :1476, on every committed
  record from the one the last valid block names to the end,
  `getStartupPosFromLastTransaction`, :1428): not negative, a multiple of
  8, 0 or from 128, before the record (015-75, 028-09). An SFE. Known
  gap: a position of an earlier record that the take never reached
  (015-73, decided (a), 2026-11-05).
* **K21. The section's order** (`DbStarter.validateTransactions`, :644):
  positions and times strictly increasing (:670, :678), times in range
  (:674), each key node validated (`validateKeyNode`, :724;
  `KeyNode.validateStreamNode`). An SFE. Known gap: a time changed within
  its neighbours' (019-30, decided (a), 2026-11-06).
* **K22. The last record's topPos** (`DbStarter.topNodeOfLastTransaction`,
  :305): a position, not −1 or a vpos (:309), the newest version of its
  top node in the section (:321), a top node (:342); and the super root
  found (:287, :292). An SFE. Only the last record's topPos is read: in
  the probe 2,226 of 2,274 flips of a topPos were harmless. Known gap: an
  older version of the top node before the section (019-30).
* **K23. The got-dirty pairs** (`DbStarter`, :460 to :476;
  `canonicalNode`, :505, :521): each id must be a node of the node table
  or the section, or the node at the pair's position. An SFE. The
  position is read only for a node that is neither: in the probe 24,900
  of 24,900 positions set to other values were harmless, and 757 of 942
  ids.
* **K24. The rerun's key order** (`DbStarter`, :394; 026-25): a record's
  KVs in strictly increasing key order. An SFE.
* **K25. The Core's internal KVs**: the startup distance's KV present on
  a start that did not create the database (`Db.readStartupDistanceKv`,
  :1413, :1418) and well formed (:760); reclaim's settings and table
  (`Reclaim`, :362, :1822 to :1906). An SFE or `InternalDataException`.

Not checked in a record: bytes 5 to 7, skipped (`Parser.parse`, :464;
027-03, G7), where 028-67's header check goes; the padding; the header
has no checksum (027-03, G12); nothing links a record to the one before
it or to its position (019-31, decided (a)).

### 3.5. The node (`core/NodeStream.java`, `core/Stored*Node.java`, `core/NodeChecksum.java`)

* **K26. The node checksum**: CRC-32C (`java.util.zip.CRC32C`, RFC 3720's)
  of the node's bytes 0 to 7 and 12 to its end, in bytes 8 to 11
  (`NodeChecksum`; 024-25, since 2026-11-11; Fletcher-16 before).
  * Written by `StoredTrans.Serializer.serializeNodes` (:909, :914) for
    top and key nodes, after their longs are copied, and by
    `StoredValueNode.toBytes` (:309) for value and delete nodes.
  * Verified by `NodeStream.checkChecksum` (:366), from `bytesToNode`
    (:331), before the type and the format: at every load
    (`readNode`, :211: a get's or a scan's descent, reclaim's reads of
    the values it copies, a start's follows) and every parse of a record
    (`Parser.next`, :558: the start's walk and section, `Db.getTrans`).
  * Cost in bytes: 4 in every node's 12-byte header, so +4 a value or
    delete node, +8 a top node version, 0 a key node (its 5 reserved
    bytes took them; 024-25, CD1). In CPU: 0.12 ms a MB, a 544-byte key
    node 0.05 µs (024-25, section 6, measured 2026-11-11). **Inferred**
    from 017-08's two figures (`w-uni-1k-inf`, one run each, 93,892 and
    236,737 commits a second with Fletcher-16 and with CRC-32C, F53 not
    quiet; the sums cost
    5.6 and 0.12 ms a MB): about 1,170 summed bytes a commit, so CRC-32C
    takes about 0.14 µs of a commit of 4.2 µs, about 3 %; at a restart
    the same figures give about 44 MB summed, about 5 ms of 0.46 s, about
    1 %.
  * Detects: any change of up to 32 adjacent bits, any change of one
    byte, a random change but once in 2^32; bytes read as a node at a
    wrong position (a pointer into a node's middle, a meta block skipped
    at the wrong offset, a stale record at another delta: 269 of 337 in
    035-02, section 10.3). Not: a whole node moved or copied (the
    position is not summed), a node of another database at the same
    place, a change with the sum made right.
  * On failure: `StreamChecksumException`: a start refuses, a read fails
    the database.
* **K27. The node's size** (`readNode`, :223, at most 6, and :226 beyond
  the stream; `checkChecksum`, :368, below 12; `Parser.next`, :553). An
  SFE.
* **K28. The node's position** (`readNode`, :215; 019-32): below 128 is
  an SFE.
* **K29. The node's type** (`bytesToNode`, :358): 10, 20, 30 or 40. An
  SFE. `readNodeHeader` (:178) reads the type and the id without the
  checksum (an SFE for another type, :198); Rule R's id lookups use it
  (`NodeCollection`, :445, :922; `DbStarter`, :315), and the node itself
  is read with K26 where it is loaded.
* **K30. The node's format byte**, 3, 3, 5 and 5 (`StoredKeyNode.parse`,
  :127; `StoredTopNode.parse`, :84; `StoredValueNode.parse`, :138).
  `VersioningStreamException`; after the checksum, so damage shows as
  K26.
* **K31. The node parsers' fields** (015-07, 019-32, 021-11; 024-25,
  section 12): a key node's size, leaf byte, count, prevPos, klong
  types, a time klong's reserved bits and refs (`StoredKeyNode.parse`,
  :105 to :210); a top node's height, size, root time and pointer,
  ordinal and skip pointers (`StoredTopNode.parse`, :69 to :169); a value
  node's size, flags (the copy mark, 031-06) and byte 7, value and key
  sizes, key and offset (`StoredValueNode.parse`, :111 to :197). Each an
  SFE.

Not checked in a node: bytes 6 and 7 of top and key nodes (written zero,
covered by the checksum; 027-03, G7); the value node's offset against its
record (G11).

### 3.6. The reads and the follows

* **K32. A pointer's target** when it is followed or linked
  (`NodeCollection.checkPointeeType`, :882; a bad pointer, :442; a pointer
  to a node not in the stream, :601; a bad value pointer, :644;
  `DbStarter`, :252, `checkStreamPointers`, :743, :756; two nodes of one
  id, `Cache3`, :277). An SFE: a start refuses or a read fails the
  database.
* **K33. A cycle in a descent** (`OpData.descentFrom`, `dag/OpData.java`:62;
  Brent's check; `58eba7cb`). An SFE.
* **K34. Rule 4 by node id** (`NodeCollection.checkLinkById`, :850):
  only with `-ea`; an SFE or an `AssertionError` (027-03, G14).
* **K35. A record's parse in `Db.getTrans`** (`Db.parseTrans`, :2484): a
  `RuntimeException` from a parse becomes an SFE, so that the read fails
  the database.

### 3.7. The Pub layer

* **K36. `created.txt`**: a directory with it and no stream bytes is
  refused, `DatabaseMissingException` (`DatabaseBuilderImp.refuseMissingStream`,
  `pubimp/DatabaseBuilderImp.java`:276); its crypto key line refuses a
  database that an earlier release encrypted, `VersioningStreamException`
  (`refuseEncrypted`, :304). Outside the stream; before the Core's start.
* **K37. The Pub layer's readers of its object bytes**
  (`DataFormatException`, `FormatFuzzer`): inside the values, under K26;
  outside the Core's format, named for completeness.

### 3.8. Development and test checks

* **K38. Assertions** with `-ea` in the writer and the readers (the
  serializer's, `KeyNode.check`, `RecoverableStream`'s; 027-03, G14 and
  J3).
* **K39. The audit** (`core/Audit.java`; `audit=N`): the model's
  invariants of the physical layer on Java's state.
* **K40. The commit-time check** (`TransCheck`): each key of a
  transaction has its new value at its time, in the tests (030-09).
* **K41. `StreamDigest`** (`java/stress/StreamDigest.java`): SHA-256 of
  the streams of 12 configurations in 4 modes, compared between builds
  by hand (P2).
* **K42. The conformance traces** (027-02; `TraceExport`, `tracecheck`):
  the model's step on every traced transaction, runs B and E's stream
  comparisons after restarts and eviction, values as hashes (`V h`).
* **K43. The state checksums** (`DbUtil.checksum`, `TransSeq.checksum`,
  `DbScan`): CRC32 of a database's state, to compare two databases in
  tests.
* **K44. The harnesses of damage**: `CorruptStreamTester` (harness 6.1:
  every cut must start with exactly its prefix; other damage refused,
  a failed read, or a state the database had), `FormatFuzzer`,
  `RestartInvariance`, the C clone's cross tests. They test the checks
  above; they are not in a production run.

### 3.9. Decided for 2026.7, not on `main`

028-67 (Frans, 2026-11-27, 15:50 to 16:02), built in 031-06's landing,
step 4:

* **C3, the meta block**: its own position, 8 of the reserved bytes from
  offset 46; a block is valid only if that position is where it was read
  and its database ID is this database's.
* **C3, the record**: bytes 5 to 7 hold CRC-32C over the database's ID,
  the record's own position and the header's other fields, truncated to
  24 bits; compared at each parse of a record.
* **C1**: a tail that fails these checks is refused with the cause and
  the way out, before anything is written; no zero fill from a size read
  out of such bytes.
* 028-66's rule (Frans, 2026-11-27, 17:26) compares the database ID of
  the first meta block of the files before a gap.


## 4. What each check serves

### 4.1. The one expected fault, the partial append

What a start needs to take every record that ends before the fault and
none after it:

* **The torn tail**: K13 (the walk and the fill), K15 (the last byte as
  the commit mark), K7 (a cut meta block not valid), K12 (a crash during
  the creation).
* **Zeros within the file's length** (028-60): K3 and K5, both relying
  on K7 and K15 (a valid block and a committed record end in 10).
* **Another file's bytes within the length** (035-02; refused, not
  recovered, by 028-67's C1, with C2 open): today K4, K9,
  K14, K15 and K19 refuse most such tails (035-02, section 10.3; the
  probe, section 4.5), and K26 some of them; none ties bytes to their
  place, and 2 of the probe's 4,783 stale tails were taken (S1). From
  2026.7 C3 and C1 do it exactly: a record to 1 in 2^24, a meta block by
  its position and ID.

So 6 checks by their main purpose, K3, K5, K7, K12, K13 and K15, and 5
in part, against another file's bytes: K4, K9 (since 035-02), K14 (a
size past the stream after recovery), K19 (a record whose content does
not fill its size exactly) and K26; with C1 and C3 from 2026.7.

### 4.2. Development: BergDB's own bugs

K16, K34, K38 to K44: 9. K26, K32 and K33 would also catch a bug of
BergDB's own that reads at a wrong position or links a wrong node; no
item records such a bug found by them. K32 and K33 were added when
CorruptStreamTester's damage met unhandled exceptions (019-32, 021-11;
`58eba7cb`).

### 4.3. Storage damage, a best effort

K1, K4, K8, K9 (its first purpose, 019-34), K11, K14, K19 to K29, K31
to K33, K35 to K37: 23. Their cost is the parsers' own work, but for
K26's 4 bytes a KV and its CPU (section 3.5). The decided gaps: 015-73,
019-30, 019-31 (CorruptStreamTester's KNOWN,
`core/CorruptStreamTester.java`:89).

### 4.4. Other purposes

* Versions and compatibility: K6, K18, K30 (021; 028-15).
* Configuration: K10 (the node size, 026-08).
* One writer: K2 (030-04, section 3.5, assumption 4).
* An API's argument: K17 (010-04, R5).

### 4.5. What refuses what: the probe

**Ran**, 2026-11-27, 19:02 to 19:12, seed 20768, CorruptStreamTester's
workloads all, take, meta and long (8,936 to 308,216 bytes, 33 to 53
records): every byte flipped by 0x01 and by 0xff (20,000 random
positions in meta's), CorruptStreamTester's header-field sets of every
record, and its cut-outs. Each copy started and read as
CorruptStreamTester does; the refusal's message mapped to its check
(`probe/tally.py`). The full counts: `probe/damage-with-checksum.txt`
and `probe/damage-without-checksum.txt`.

With the node checksum (255,169 copies):

* No copy answered wrong values but the decided ones: 171 of 019-30
  (a time or a topPos), 18 of 019-31 (a range cut out), 1 of 015-73.
* K26 was the first refusal for 139,519 copies (123,971 at the start,
  15,548 at a read); harmless, 86,339 (bytes no read reaches, such as a
  value overwritten later).
* Flips in a node's size: K19's node size first (2,625 of 3,462).
* By region, the first check and its count (the largest of each):
  * meta block flips, 802: harmless 684 (the time, the ID, the reserved
    bytes), K8 49, K4 24, K6 24, K10 12, K11 6, K9 3;
  * a record's size flipped, 1,124: a fill past 1 MB 526 (014-01), a
    prefix as after a cut 304, K13 257, K15 after a fill 16;
  * a record's size set, 6,793: K19 3,339 (015-72), K13 1,212, harmless
    1,042, a fill past 1 MB 924, a prefix 174;
  * the format byte, 278: K18 278;
  * startupPos flipped, 2,264: K20 2,103, harmless 158; set, 16,968:
    harmless 8,466 (a record not the last), K20 8,178, K15 151, K22 114;
  * the time flipped, 2,260: harmless 1,520, K21 657, 019-30 78;
  * topPos flipped, 2,274: harmless 2,226; set, 32,935: harmless 32,220,
    K22 484, K29 187, 019-30 34;
  * the end marker, 1,136: K19 1,118; the got-dirty count, 1,134: K19
    1,118; the got-dirty list, 4,342: harmless 3,816, K23 526;
  * the last byte, 284: K15 280;
  * cut-outs, 2,823: K20 682, K13 628, a fill past 1 MB 461, K4 365, a
    prefix 237, K23 171, K14 135, K15 90, 019-31 18, K26 13.

Without it (the same copies):

* 59,596 copies answered wrong values with no error: 54,944 of the
  94,272 flips in value nodes' bodies (58 %), 4,066 of 36,858 in key
  nodes' (11 %), 535 of 6,102 in top nodes' (9 %), 50 of 1,396 in delete
  nodes', 1 in a value node's size.
* The rest of the node flips were refused by K19, K21, K23 to K25 and
  K27 to K33, or met a read beyond the stream's end, or were harmless.

In both: bytes 5 to 7 (852 flips), the padding (1,286), the got-dirty
positions (24,900 set) and the topPos of a record not the last were
harmless as no check and no read touches them; with C3 a flip of a
header byte is refused wherever the record is parsed (a start's walk
and section, `Db.getTrans`).

Stale tails (4,783 copies; `probe/stale-*.txt`): from Z, every 512
bytes, to the end, the bytes of another database of the same workload at
the same positions and at 4,096, 12,288 and 200,000 bytes after, and the
stream's own bytes from as far before. With the node checksum: K4 1,950,
K13 (a size) 1,322, a fill past 1 MB 989 (014-01; C1 stops it), K15 432,
a prefix of the real records 56, K15 after a fill 20, K26 after a fill
10, K18 after a fill 2, and 2 that took another database's records and
answered its values (S1). Without it: the same, but the 10 that K26
refused were refused by K19 and K31. The 2 are at Z = 512 in the
workloads all and long, where the record at 512 begins exactly at Z: the
first three records (128, 272 and 416) of every database of a workload
have the same sizes, and the test clock gives the same times
(`probe/StaleLook.java`), so the other database's records passed every
check at their place, node checksums included. C3's header check, over
this database's ID and the position, refuses them (to 1 in 2^24).


## 5. The questions

### 5.1. The node checksums: stay, go, or one a record

* **N1. Stay as they are** (CRC-32C, 4 bytes, at every load and parse).
  * Costs: 4 bytes a value or delete node, 8 a top node version, none a
    key node; about 3 % of a 1 kB put's commit and 1 % of a restart
    (inferred, section 3.5); nothing to change.
  * Removes: nothing. Keeps the only check of a node's content, notably
    of the values (section 4.5), at the load, before reclaim copies a
    value forward or a loaded index node is changed and written again,
    each with a fresh checksum over whatever bytes it read.
* **N2. Go, with nothing in their place.**
  * Saves: 4 bytes a KV, 8 a top node version (a 12-byte node header
    back to 8, node formats 4, 4, 6 and 6), the CPU above.
  * Costs: values and keys damaged in storage are read without an error
    (59,596 of 255,169 copies in the probe), and reclaim's copies and the
    rewrites of loaded index nodes make such damage permanent and its
    origin invisible; 028-67's "Why three bytes suffice" counts the node
    checksums among the checks a stale record must also pass; a format
    change of every node (the parsers, CorruptStreamTester's pinned
    copies and node ranges, level1's SS limits, the Lean's top node
    bytes, section 6, the C clone when it follows).
  * Detects then: nodes only by K27 to K33's structure; the expected
    fault as well as today (the probe's stale tails, section 4.5) and
    exactly with C3.
* **N3. One checksum a record**, 017-08's wider form: CRC-32C over the
  database's ID, the position and the record's bytes after the header
  (its nodes, the end marker, the got-dirty list, the padding), 4 bytes
  before the last byte (0 or 8 bytes a record by the alignment, 4 on
  average), with C3's 24-bit header check kept, as C1 needs a check that
  a torn record's header alone can give; the node checksums go.
  * Saves: N2's bytes, less 4 a record.
  * Covers: the whole record, the got-dirty list too, tied to its place,
    at every parse of a record: the start's walk and section, and
    `Db.getTrans`.
  * Costs: no check at a node's load (a get, a scan, reclaim's reads):
    the record is not read to load one node, and a record is up to 2 GB.
    So N2's laundering by reclaim and by rewrites stays. The same CPU as
    N1 at a write and a start. The format changes of N2 and a new record
    field.
* **N4. Both**: N1 and N3's record checksum. Covers the got-dirty list
  and ties every record body to its place; costs 4 bytes a record more
  and a second pass of CRC-32C over every record at a write (about 3 %
  of a 1 kB commit, inferred) and a parse.
* **N5. Node checksums seeded with the node's position and the
  database's ID** (035-02, C3's other form): ties each node to its place
  at every load; costs a few ns a node, a change of every node's sum.
  After C3 the records are tied already; what it adds is a node loaded
  alone from another file's bytes, outside the expected fault.

**Recommended: N1.** The node checksum is the one check of the values
and the keys (section 4.5: without it 58 % of the flips in values gave
wrong answers), checked where a reader takes bytes from the storage,
before reclaim or a rewrite would make damage permanent; it costs about
3 % of a small commit and 4 bytes a KV; it is in place and tested, and
removing it is a change of every node for 4 bytes. By the principle
(section 5.4) it is a best effort kept for its low cost, and a part of
the stale face's checks that 028-67's 24 bits were decided with. N3 and
N4 cover the got-dirty list, which section 5.2 finds needs no checksum.

### 5.2. The got-dirty list and the meta block

What they hold and what checks them today:

* **The got-dirty list**: a count and pairs (id, position), 16 bytes a
  pair, after the nodes. Checked by K19 (the count fills the record
  exactly: a count must equal the record's own), K23 (an id is a node of
  the table or the section, or the node at its position) and K15. The
  position is read only for a node that is neither (section 4.5: all
  24,900 changed positions harmless). A damaged id that names another
  existing node gives a wrong D, silently; damage of storage, outside
  the expected fault. In the expected fault: a torn list is a torn
  record (K13); a stale list in a record whose header is real must give
  the exact count, ids of nodes that exist, and the last byte 10.
* **The meta block** after C3: magic, version, the creation's time,
  lastTrans, the database ID, the node size, its own position (new), the
  last byte. A block that holds another file's bytes from some offset
  on: if they cover the ID (offsets 24 to 39), it is another database's
  ID, or this database's in a block of an older file, whose position is
  another, and C3 refuses it either way. If they begin after the ID,
  lastTrans (16) and the ID are this block's own, and the node size (44)
  and the position (46) are refused by K10 and C3 unless they are this
  block's values. So C3 is exact for the stale face of the fault. What
  stays open is damage: a lastTrans changed to another record's start is
  taken (harmless: the walk goes from there; a position inside a record
  fails C3's header check); the time is read by nothing but K8.

The options:

* **GD1. The got-dirty list: nothing new.** The structure above. Cost:
  none.
* **GD2. A checksum of the record's end** (the end marker, the count,
  the pairs, the padding), CRC-32C in 4 bytes before the last byte: 0
  or 8 bytes a record, 4 on average; the parser checks it. Detects
  damage of the list; ties it to its place if seeded with C3's inputs.
* **GD3.** N3 or N4 (section 5.1), which cover it with the nodes.
* **M1. The meta block: C3 as decided, nothing more.** Cost: 8 of the
  reserved bytes; none in CPU worth counting.
* **M2. C3 and a CRC-32C of the block** in 4 more reserved bytes (54 to
  57), set at every write of a block (`RecoverableStream.writeMetaBlock`,
  :650, as C3's position must be) and checked at every read: a block that
  fails it is not valid, as a cut one is not. Detects damage of
  lastTrans, the time and the reserved bytes; 128 bytes summed every
  200,000.
* **M3. The reserved bytes must be zero**, refused otherwise (027-03,
  Q14): detects damage there; costs the rule of extension that let 005-50
  add the node size without a version (027-03, section 6).

**Recommended: GD1 and M1.** The expected fault needs neither more: a
torn list is a torn record, a stale one must fit the record exactly, and
with C3 a meta block of other bytes is not valid. The rest is storage
damage, a best effort by the principle; GD2 costs 4 bytes a record on
average for bytes that the probe could not make matter (but a wrong id,
which K23 refuses unless it names an existing node), and M2 guards
fields that a start does not use (the time) or that C3 and the header
check already make safe to take (lastTrans). M3 is Q14's question, not
this one's.

### 5.3. The header check's width

The check of 028-67's C3: CRC-32C over the database's ID (16 bytes), the
record's own position (8) and the header's fields: the size (4), the
format (1), the time, startupPos and topPos (8 each), 29 bytes stored.
**Ran** (`probe/hd.py`, 2026-11-27): the low 24 bits of that CRC-32C
detect every error of 1 to 3 bits in the header's 32 stored bytes (its 29
and the 3 of the field): a Hamming distance of 4, whether the ID and the
position come first or last; a random change passes once in 2^24, about
16.7 million. Keeping the high 24 bits instead gives a distance of at
least 4 too.

* **W24. 24 bits in bytes 5 to 7** (decided). Costs: no byte; the CRC of
  53 bytes a record at a write and a parse, **inferred** 10 to 50 ns, under
  1 % of the 4.2 µs commit of section 3.5. Removes: a stale or moved record
  or a damaged header taken, but once in 2^24 (and then the other checks:
  the format byte, the sizes, the node checksums, the last byte).
* **W32. 32 bits**: the header from 32 bytes to 40 (the nodes after it
  are 8-aligned), 8 bytes a record: about 0.7 % of a 1 kB put's stream
  and 4 to 6 % of a small record's (an empty one is 48 bytes). Passes a
  random change once in 2^32.
* **W64. 64 bits**: the same 8 bytes; Java has no 64-bit CRC (CRC-32C and
  CRC32 together, or another hash). Once in 2^64.

**Recommended: W24, as decided.** The case it serves is a record of
another file or place that begins exactly where a record ends (028-67;
section 4.5): one header checked per stale tail, so a miss is about 1 in
16.7 million such tails before the other checks, and storage damage is a
best effort. 8 bytes a record buy nothing the expected fault needs. With
it: the 24 bits are the low ones; the format byte is in the CRC; the
check is computed in `Serializer.serializeHeader` (`StoredTrans`:870),
where every input is known, and compared in `Parser.parse` and by C1's
recovery before a fill.

### 5.4. The principle

Where it is stated today, each in part: 014-01, section 7 (the crash
contract, Frans, 2026-11-05); 017-08 (Frans, 2026-11-06); 024-28, section
7 (Frans, 2026-11-12); `AppendOnlyStream`'s Javadoc, "CRASHES"
(`stream/AppendOnlyStream.java`:16 to :24); `Db`'s "Errors"
(`core/Db.java`:307 to :312); `CorruptStreamTester`'s (:46, :73);
030-04, section 3.5, assumptions 3 and 5; P7 (a failed database stops,
after corrupt data too).

Proposed wording:

> **R6. The storage owns the integrity of the bytes.** BergDB assumes
> that its storage returns the bytes appended to it, and that after a
> crash the stream is a prefix of them, with one expected fault: a
> partial append, which leaves at the stream's end a part of what was
> appended, or zeros in its place within the file's length. A start
> handles that fault exactly: it takes every record that ends before it
> and none after it. Any other damage of the stored bytes is the
> storage's to prevent. BergDB's checks of it are a best effort, kept
> where they cost little; damage that they do not see gives wrong values
> with no error. A check that finds damage refuses the start or fails the
> database (P7); none repairs it.
>
> Serves P7 and P13.
>
> Cases: 014-01 (prefix interruption, 2026-11-05); 015-73, 019-30,
> 019-31 and 019-33 (damage outside the fault, decided (a), 2026-11-05
> and 2026-11-06); 024-25 (the node checksum CRC-32C, a best effort kept
> for its cost); 028-60 (zeros within the file's length, a face of the
> fault, 2026-11-26); 028-67 (another file's bytes within the length,
> refused with the cause and tied to their place, 2026-11-27); 031-07.

Where: **a rule of 010-04, R6, recommended.** It holds for every
implementation (Java and C) and grew from decisions, as 010-04's rules
do; P7 already says what a database does after corrupt data, and the
principles are kept few. A principle, P15, if Frans sees it at P2's
level. Either way the Javadoc above and 030-04's assumptions 3 and 5 cite
it instead of restating it; 027-14 and 027-15 state the mechanism.

If 028-67's C2 is taken, the fault's words gain "or another file's bytes
in their place", and such a tail is cut, not refused.

Each check against it (section 4): from the expected fault, K3, K5, K7,
K12, K13 and K15, in part K4, K9, K14, K19 and K26, and C1 and C3; from
the principle's best effort, K1, K4, K8, K9, K11, K14, K19 to K29, K31 to
K33, K35 to K37; from neither, K2, K6, K10, K17, K18 and K30 (versions,
configuration, one writer, arguments) and K16, K34, K38 to K44
(development). No check contradicts it. Two places repair more than the
fault: K3 cuts a zero tail without a word also where the zeros are
damage (forced bytes lost), bounded at 8 MB by decision (2026-11-26); and
K13 appends zeros for a size read from damaged or other bytes, which C1
removes.


## 6. The Lean model, the trace format and the contract

* **The model** (`lean/SIS`, `lean/BergDB`, `lean/Check`) has no bytes: a
  stream is a list of records, and a crash keeps the first k + 1 of them
  (`T1_crash`, `lean/SIS/Theorems.lean`:45; the contract's
  `crash_java_reads`, `lean/contract/Contract/RecoverJavaTheorems.lean`:39).
  No checksum, magic byte, meta block or torn record is in it (searched:
  "checksum", "CRC", "magic", "meta block" match two comments only).
  027-17 names bytes and torn records among what the proofs leave out.
* **The contract's assumptions** (030-04, section 3.5; with their tests,
  030-26): 3, "a crash leaves at most a torn tail", which K3, K5, K7,
  K12, K13 and K15 make Java meet; and 5, "the bytes decode to what was
  written", tested by the restart tests, "damaged bytes are found on a
  best effort only". R6 is these two in the rules' words.
* **The trace format** (027-02) has no bytes or checksums: records are
  indexes (`REC i`), values hashes (`V h`). `TraceExport` reads ids with
  `readNodeHeader`, without the node checksum (`java/stress/TraceExport.java`,
  :469, :1899).
* **What a change touches.** C3 and C1 (W24, M1): no Lean file and no
  trace line; no size changes (bytes 5 to 7 and reserved meta bytes), so
  the record limits and `Dag.dirtyNodeBound` stay. N2 or N3: the node
  header from 12 bytes to 8, so `lean/SIS/Tree/Bound.lean`'s
  `ReleaseFits` (:385 to :392), which counts a top node as 48 + 16 · 48
  bytes "since CRC32C", and Java's `Db.checkDirtyNodes`; the theorems by
  `decide` would hold with the smaller figure. W32 or W64: 8 bytes a
  record in Java's record overhead; the model's cost of a record is a
  parameter (`Stream.span`, `lean/SIS/Bound.lean`:84) and needs no change.
  C3 changes `StreamDigest`'s digests (031-06's step 4 changes them
  anyway), as every option but N1 and M1 does, and CorruptStreamTester: with C3 its region "unused"
  becomes the check, and its KNOWN entries 015-73, 019-30 (header fields)
  and most of 019-31 (records moved to another position) become
  refusals, to be removed from KNOWN in the landing.


## 7. For Frans

1. **The node checksums**: N1, stay (recommended), or N2, N3, N4, N5
   (section 5.1).
2. **The got-dirty list and the meta block**: GD1 and M1 (recommended),
   or GD2, GD3, M2, M3 (section 5.2).
3. **The header check's width**: W24 as decided (recommended), or W32,
   W64 (section 5.3).
4. **The principle**: R6's wording (section 5.4); a rule of 010-04
   (recommended) or a principle (Frans's); with or without the stale
   face, by 028-67's C2.

A finding for the record, no decision: the probe made the S1 case that
028-67 described (another database's records at the same positions,
taken whole, with their values) in 2 of 4,783 stale tails, with every
check of `main`; C3 refuses it, as decided.


## 8. State

2026-11-27, 19:40, by an agent of lead-1127, on the branch
`031-07-inventory` of a clone of `main` at `17c7c7db`.

* Done: the inventory (section 3), what each check serves (4), the probe
  (4.5), the options with recommendations (5), the Lean (6).
* In `probe/`: `CstChecks.java` and `StaleLook.java` (package
  `bergdb.core`, run on the clone's `java/build/bergdb.jar`, before it on
  the class path), `nochecksum.diff` (the shadow `NodeStream`,
  `-Dprobe.nochecksum=true`), `tally.py`, `hd.py` and `hd.txt`, the
  tallied outputs.
* Not done: no timing (the machine was shared with `night.sh`); the CPU
  figures are inferred from 017-08's and 024-25's.
* Next: Frans's decisions (section 7); then the change in 031-06's
  landing, step 4.
