028-15. Change: the startup distance out of the meta block, into an internal KV
================================================================================

Status: open. Kind: Change. Frans: A or B (older streams).
Created 2026-11-16 by Frans Lundberg.

Frans, 2026-11-16, 10:32: "There is still a stream format change that I
want to get in place in the next release. The startup distance! It does
not need to be in the fixed-location stream slots (forgot what they are
called). Ensure this is in the todo list as an open item." The slots are
the meta blocks (027-03, section 6); release 2026.6 takes this entry
(026).

What: the startup distance sd is kept in each meta block, bytes 40 to 43
(027-03, section 6). The meta block is for what cannot be stored
otherwise (Frans, 2026-11-05; 017-07, section 2), and sd can: only the
writer uses it, since a start takes its position from the last record.
To get a meta block with the new value written, `Db.setStartupDistance`
puts `/#i/-dummy`, 200,000 zero bytes, never read (027-03, section 15).
The change, as 026-12, SF7 (a), and 024-01, OT4, describe it:

* sd is an internal KV of the Core (a key under `/#i/`, such as
  `/#i/-startup-distance`), written by a small transaction when sd
  changes, as today's setting's record is, and in the primordial
  transaction.
* A start reads it at its end, before the writer takes its first
  transaction.
* The meta block's bytes 40 to 43 become reserved, written zero and not
  read.
* `/#i/-dummy` goes: 200 kB less at each change of sd.
* The unit stays stream bytes (026-12, SF7 (b), recommended).
* A new format number, since a start of such a stream needs the KV.

To decide (Frans): what a start does with an older stream, one whose sd
is in its meta block.

* **A.** It refuses it, as starts have refused older databases since
  005-50. Simple; a 2026.5 database is not opened by 2026.6.
* **B.** It reads sd from the meta block once, and writes the KV in its
  first transaction. One more path to test; the older format stays
  readable.

Recommended: as 026-12's SF4 (the versioning rule) decides for 2026.6;
A if SF4 is (a), no fallback for older streams.

Done when:

* `java/`: sd in the KV, the meta bytes zero, the dummy gone, the format
  number raised, the start as decided; tests for a change of sd, a
  restart after it, a crash inside the setting's transaction (028-08's
  case), and a reclaim cut that leaves the KV live.
* 027-03 (sections 6, 15 and 21) and, if sd is in a trace, 027-02
  follow the code; the Lean model and the trace checkers, if they name
  where sd is kept.
* `java/before-commit.sh` prints BEFORE COMMIT OK, and `level2.sh`
  (startup) passes.

Not in it: the C clone (012), which follows a release, not `main`.

Sources: 026-12, SF7; 024-01, section 11.4 (OT4); 017-07, section 2;
027-03, sections 6 and 15; 017-11 (a key count K, a separate question,
SF7 (c)).
