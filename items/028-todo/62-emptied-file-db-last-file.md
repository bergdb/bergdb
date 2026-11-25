028-62. Decide: RB-011, an emptied file database keeps its last stream file
==========================================================================

Status: open. Kind: Decide. Frans: decision.
Created 2026-11-25 by Frans Lundberg.

What: RB-011 (033; found by 031-02, F2, its cause by 028-61). A file
database that held much stream and is then emptied keeps, under
`maintain()` calls, the stream file that the first available position
is in. Reclaim cuts the stream below 400 kB (61 kB of stream in
RetainChurn's seed 5), but `FileStream` drops only whole files and
keeps its last one, whose capacity it chose when the file was made, up
to a quarter of the stream kept then (a 20 MB file made while about 85
MB was kept); after the deletes only reclaim's records are appended,
about 1 MB, so the file never fills, every cut lands inside it, and the
disk keeps it whole: 10,400 kB on disk for 61 kB of stream, on `main`
and 2026.6 alike. 031-03's design does not change it.

Why: the Javadoc of the Pub's `Database.maintain()` promises "within
about 400 kB of the size of a fresh one"; the Core's `Db.maintain()`
says "of the stream", which holds. 027-13, section 4 ("the disk: 6 to
9 percent more than the stream kept") does not hold for a stream that
has shrunk.

Frans: decision, between:

* **J. The Javadoc.** The 400 kB are of the stream; a file database
  also keeps the rest of the file that holds the first available
  position, up to a quarter of the stream kept when that file was made
  (5 MB after 20 MB kept, 20 MB after 80 MB, up to 500 MB after 2 GB).
  No code. The promise becomes what the code does; RB-011 is closed as
  documented. 027-13, section 4 says the same.
* **S. The storage.** A file boundary after the first available
  position: for example, at a cut that leaves the stream kept far below
  the last file's capacity, `FileStream` ends that file at its next
  record and begins the next, of the size its rule gives; `maintain()`'s
  M1 counts the storage's bytes (from the storage's first position, not
  fp), so the calls begin an iteration whose cut passes the old file,
  which is then deleted. Not designed or measured (028-61, section 3);
  to check: whether a start accepts a file that is not the last and is
  shorter than its capacity. It changes how the files are laid out,
  not the stream's bytes.

Recommendation, lead-1125: S, if a design of it stays small (a few
rules in `FileStream` and one count in M1), as the promise of a return
to empty is what `maintain()` is for (Frans, 2026-11-25: the database's
return to empty is wanted); else J, with the bound written.

Done when: Frans's choice; with J, the Javadoc of `Database.maintain()`
and 027-13, section 4 corrected; with S, a design and a fix with a
test that fails before it, `java/before-commit.sh` printing `BEFORE
COMMIT OK`, RetainChurn's case at about 400 kB of disk over a fresh
database's.

First step: 028-61, sections 2 and 3; `FileStream`'s rule for a new
file's capacity and its deletion of whole files.


Log
---

2026-11-25. Registered by lead-1125, from 028-61.
