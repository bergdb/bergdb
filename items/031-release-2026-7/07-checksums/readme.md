# 031-07. The stream's checksums, a review

Created 2026-11-27 by Frans Lundberg. Status: decided (Frans,
2026-11-28; section 5): no change of the checks beyond 028-67's; the
principle is rule 010-R6. Open: the Javadoc and 030-04 cite the rule.

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
* The principle itself (Frans, 2026-11-27): "the storage owns the
  integrity of the bytes; BergDB's detection of damaged bytes is a best
  effort" is stated in no one place today (section 2 cites the two
  statements it comes from). The review proposes its wording and where
  it is written (a rule of 010-04, or a principle: Frans's), and says
  for each check whether it follows from the principle, from the one
  expected fault, or from neither.


## 4. Done when

An inventory of what each check detects and what it costs
(`CorruptStreamTester`'s cases, 035's cases); the options in full, with a
recommendation; Frans's decision; and the change, if any, in 2026.7's
format.

First step: the inventory.


## 5. Decided

Frans, 2026-11-28, 07:30, as the inventory recommends (its section 5):

* **N1.** The node checksums stay as they are: a CRC-32C of each node's
  bytes, checked at every load and parse.
* **GD1.** The got-dirty list gets nothing new.
* **M1.** The meta block holds its own position and the database's ID
  (028-67's C3), nothing more.
* **W24.** The record header's check stays 24 bits, in bytes 5 to 7.
* **The principle is a rule, R6 of 010-04**, not a principle, in the
  wording of the inventory's section 5.4: the storage owns the integrity
  of the bytes, and BergDB's checks of damage are a best effort. Another
  file's bytes at the tail are not a face of the expected fault in its
  words: 028-67's C2 is held until 028-77 is decided.

So 2026.7's format has no change of the checks beyond 028-67's, built in
031-06's landing, step 4. Left to do: the Javadoc that state the
principle in part (`AppendOnlyStream`, `Db`, `CorruptStreamTester`) and
030-04's assumptions 3 and 5 cite 010-R6 (the inventory, section 5.4).

A check of the nodes' place (a node's checksum begun with its position
and the database's ID), which would close 028-67's finding that C3 does
not cover nodes, is a change of the format taken with 028-77's review
(035-03), not in 2026.7 (Frans, 2026-11-28).


## Files

* [inventory.md](inventory.md): the inventory of the stream's checks on
  `main` at `17c7c7db`, what each serves, the options for section 3's
  questions with a recommendation each, and the Lean's side (2026-11-27).
* `probe/`: the probe of the inventory's section 4.5 (CorruptStreamTester's
  damage and stale tails, with and without the node checksum) and of its
  section 5.3 (the header check's Hamming distance), with the tallied
  outputs.


## Log

2026-11-27. Created by Frans Lundberg, with 028-67's decision (registered
by lead-1127).

2026-11-27. The principle added to the questions (Frans): the review
considers its wording and place, and each check against it.

2026-11-27. The inventory (`inventory.md`), by an agent of lead-1127:
44 checks; recommended: the node checksums stay (N1), nothing new for
the got-dirty list and the meta block beyond C3 (GD1, M1), the header
check 24 bits as decided (W24), the principle as a rule of 010-04 (R6).
For Frans's decision.

2026-11-28. Decided by Frans (07:30): N1, GD1, M1, W24, and the
principle as rule R6 of 010-04 (section 5); R6 added to 010-04. The
nodes' place goes with 028-77's review.
