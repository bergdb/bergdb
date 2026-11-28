# 035-03. Append-only storage: what BergDB may take for granted

Created 2026-11-28 by Frans Lundberg. Status: open: not started (after
2026.7's work is stable).

A review of what append-only storage means for BergDB, exactly, and of
what its code may take for granted from the storage under it. It is the
ground for 028-77's decision (strictly append-only files, or rewrites of
the tail at a start). Until November 2026 BergDB assumed that a crash
leaves a prefix of what was appended (014-01, section 7); 035-01 and
035-02 found two other tails after a kill of the writing process.


## 1. Scope

* **What append-only means, exactly**, at two levels: for the stream
  that the Core sees (`AppendOnlyStream`), and for the files of its
  provider `FileStream`: which operations change a file (an append, the
  delete of a whole file, and since 028-60's part 2 one truncation at a
  start's first append), and what a copy, a replica and a later
  encryption (017-10) may rest on.
* **The faults that a crash may leave**, by environment: a prefix; a
  tail of zeros within the file's length (035-01: F53's APFS after a
  kill; not on s1's ext4 or on HFS+); another file's bytes in the tail
  (035-02: APFS RAM disks and disk images, not F53's internal SSD).
  What remains to test: a power loss (035's scope: a virtual machine
  stopped hard), and environments other than F53 and s1.
* **The contract today**: 014-01, section 7 (prefix interruption, the
  provider's duty, decided for 2026.3; the broader crash model open in
  its section 6), and where 028-60 and 028-67 changed what the provider
  and the start do (the zero tail left out and cut; a tail that is not
  the stream's own refused before anything is written).
* **The result**: a fault model, each fault with the storages that can
  leave it and with who handles it (the Core by appending, the provider
  by presenting a clean end, or a person), stated in 014-01's section 7
  and in 027-14, and the ground from which 028-77 is decided.
* **Encryption and replication are requirements of the model** (Frans,
  2026-11-28), though neither is implemented: both were meant to be
  simple on append-only storage, and each exception to append-only may
  complicate them. The review states, for each fault and each way of
  handling it, what an encrypted stream and a replica by files may
  still assume.


## Log

2026-11-28. Created at Frans's request, with 028-77. Not started.

2026-11-28. Scope: encryption and replication as requirements of the
model (Frans).
