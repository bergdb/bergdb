# 031-07. The stream's checksums, a review

Created 2026-11-27 by Frans Lundberg. Status: open.

Frans, 2026-11-27: the checksums of the stream are reviewed for release
2026.7, with them the record header's new 3-byte check (028-67).


## 1. What exists

* **The nodes**: a CRC-32C of each node's bytes, 4 bytes in the node's
  12-byte header (`NodeChecksum`; 024-25; Fletcher-16 before 2026.5),
  checked at each load of a node and at each parse of a record, such as
  a start's.
* **The record header** (32 bytes), **the got-dirty list** and **the
  meta block** have no checksum (027-03, G12 and Q12; 017-08's part 1,
  its wider form of one checksum a record, and its question 6, none
  decided). A meta block has its magic, version, last byte and checks
  of its fields.
* **From 2026.7** (028-67): the header's 24-bit check (CRC-32C over the
  database's ID, the record's position and the header's fields), and
  the meta block's own position and database ID, checked at a start.


## 2. What to review against

* BergDB assumes correct storage (Frans, 2026-11-06; 017-08): the
  storage owns the integrity of the bytes, and BergDB's detection of
  damaged bytes is a best effort, a low priority (Frans, 2026-11-12;
  024-28, section 7).
* The one expected fault is a partial append (035-01, 035-02, 028-60).


## 3. The questions

* The node checksums: stay, go, or become one checksum a record. They
  refused most of 035-02's stale records at other offsets (269 of 337;
  035-02, section 10.3); they cost 4 bytes a KV and about 0.12 ms a MB
  (024-25).
* What the got-dirty list and the meta block need.
* The header check's width: 24 bits in the unused bytes, or 32 or 64
  bits at 8 more bytes a record (028-67).


## 4. Done when

An inventory of what each check detects and what it costs
(`CorruptStreamTester`'s cases, 035's cases); the options in full, with a
recommendation; Frans's decision; and the change, if any, in 2026.7's
format.

First step: the inventory.


## Log

2026-11-27. Created by Frans Lundberg, with 028-67's decision (registered
by lead-1127).
