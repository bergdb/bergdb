028-61. Investigate: an emptied database keeps 2 to 3 times the startup distance under maintain()
================================================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: 031-02's app hunt, finding F2 (section 5): with a retain duration
of 5 to 24 s and a startup distance of 5 MB, a database whose keys are
all deleted, then not written to, keeps 0.4 to 15.2 MB of stream under
`maintain()` called again and again as the clock moves (RetainChurn,
seeds 1 to 7; 19 of 20 emptied rounds more than 400 kB above a fresh
database's 904 bytes); the first available time stops near the end of
the deletes and stays, 19 minutes behind the clock in seed 1. `java
RetainChurn DIR 5 1` keeps 10,400 kB in about 4 minutes. Release 2026.6
gives the same bytes. 028-53's prototype A2 keeps 9,200 kB.

Why: the Javadoc of `Db.maintain()` and `Database.maintain()` says that
the calls bring an emptied database to within about 400 kB of a fresh
one's stream. RB-007's stated bound is below 2 sd (10 MB here); 15.2 MB
is above it, and A2 does not give the space back, so the case may be
RB-007 with a larger bound, 028-58, or a fault of its own.

Frans: none for the investigation. A fix goes with RB-007's (031-03),
unless it is a fault of its own that needs no decision.

Done when: RetainChurn's case run on `main`, 2026.6 and 031-03's
prototype (`031-03-proto`), the bytes kept and the first available time
quoted; the cause named (why no iteration begins or no cut comes); its
relation to RB-007 and 028-58; an RB entry drafted for 033 if it is a
released bug of its own, or RB-007's text corrected.

First step: 031-02, section 5, F2, and its app RetainChurn (e3);
027-13, sections 1.6 to 1.10; 031-03, sections 3.4 and 7.


Result
------

Investigated 2026-11-25 by an agent of lead-1125, on the branch `028-61`
of a clone of `main` at `cbf0a7e0`, with release 2026.6 (the tag
`release-2026.6`) and 031-03's prototype (`031-03-proto`, `eae8d1da`)
built beside it. The probe, in [probes/](probes/): `RetainChurnRows`,
031-02's RetainChurn with calls to `RowsShow`, which prints reclaim's
table whenever a row begins, ends, becomes safe or is cut, M1's parts
after each `maintain()` loop, and the stream's files at the end;
`run.sh` runs it against a tree's jar. The workload and the checks are
RetainChurn's, unchanged: every run printed `RETAINCHURN OK`.

### 1. The runs

`RetainChurnRows DIR 5 1` (RetainChurn's `5 1`: R = 12 s, sd 5 MB), the
emptied round:

* `main`: stream files 10,400 kB (a fresh database: 904 bytes); first
  available 00:01:38, clock 00:04:39. The stream kept (L - fp) is 61 kB.
  One file, from position 280,000 kB, 10,400 kB long.
* Release 2026.6: the same, byte for byte (L, fp, the file, the times).
* `031-03-proto`: stream files 8,801 kB; first available 00:01:38,
  clock 00:04:26; the stream kept 75 kB; one file, from 280,000 kB,
  8,801 kB long.

`RetainChurnRows DIR 1 4` (R = 10 s; round 0 does not empty), rounds 1
to 3, the stream files, then the stream kept:

* `main` and release 2026.6, the same bytes: 200, 2,600 and 3,800 kB of
  files; 36, 183 and 142 kB of stream; each time one file, from 590,000,
  785,000 and 860,000 kB; first available 2 min 42 s, 2 min 43 s and
  2 min 47 s behind the clock.
* `031-03-proto`: 3,601, 246 and 1,432 kB of files; 152, 102 and 227 kB
  of stream; one file each, from 590,000, 790,000 and 865,000 kB.

In every round of both seeds the stream kept is below 400 kB, and what
the disk keeps beyond it is the last file's bytes before fp: 200 kB
where the last file happened to begin just before the writes ended,
10,400 kB where it began 9 MB before. (031-02's 15,200 kB in seed 1 came
from an earlier version of the app, whose workload differed.)

### 2. The cause: the file storage keeps its last file

Reclaim does what it should. After the deletes, the calls finish the
iterations that the deletes' commits began and cut six times in 12
loops: fp goes from 206,188 to 290,339 kB
and the stream kept from 83,124 kB to 61 kB. Then no iteration begins,
rightly: both of M1's stretches are below MIN_RELEASE (5 kB from fp to
the last pStart, 0 after the table's store), as is 031-03's one (61 kB
kept). The first available time stays at the last cut's tEnd, 98.0 s,
because nothing is left to cut, so no iteration begins and no cut
moves it.

The 10,400 kB are the storage's (027-13, section 1.7: "a file storage
drops whole files"). `FileStream`:

* drops whole files only, and always keeps the last one
  (`pretruncate`; the last file kept since 015-31);
* chooses a file's capacity when it makes the file: the largest of
  0.2, 1, 5, 20, 100 and 500 MB, 2, 10, 50 and 200 GB that is at most a
  quarter of the stream kept then (`applyFileSizeChangeRules`); a
  smaller size takes effect only at the next file.

The last file began at 280,000 kB, near the end of the round's writes,
with about 85 MB kept (L 279,797 kB, fp 194,284): a file of 20 MB. The
writes end at 289,313 kB; the calls append only reclaim's records,
1,087 kB, so the file never fills, no next file is made, and every
later cut lands in it. The disk keeps the file from its start, 10,400
kB, of which the stream kept is 61 kB. The prototype's 8,801 kB is the same file, with other bytes
before the deletes' end (its rows hold `w`).

So the case is neither:

* **RB-007**: no stream is left that M1 fails to count; the stream kept
  is 61 kB, below MIN_RELEASE, and every row's cut came;
* **028-58**: the two stretches sum to 61 kB, not to more than
  400 kB;

but a fault of its own: `Database.maintain()`'s Javadoc says the calls
bring an emptied database "to within about 400 kB of the size of a fresh
one", and a file database's size is its files. The Core's
`Db.maintain()` says "of the stream of a fresh one", which holds (61
and 75 kB). It is in every release with `maintain()`, 2026.5 and 2026.6
(`FileStream` unchanged since 2026.6; its size rule since the 2017
source; 2026.5 not run). Disk space only, S4; writes give it back once
they fill the file and the cut passes its end.

The bound: an emptied file database keeps, beyond the stream kept (below
400 kB), the part before fp of the file that holds fp, less than that
file's capacity, which is at most a quarter of the stream kept when the
file was made: up to 5 MB after 20 MB was kept, 20 MB after 80 MB, 100
MB after 400 MB, 500 MB after 2 GB. 031-02's 0.4 to 15.2 MB fit files of
1 to 20 MB. 027-13, section 4 ("the disk: whole files, 6 to 9 percent
more than the stream kept") holds for a stream in use, not for one that
has shrunk.

### 3. 031-03's prototype does not end it

Its R4 measures the stream kept, L - fp: 75 kB, so it begins nothing,
and an iteration it began would cut inside the same last file and drop
nothing. The fault is below reclaim: no cut can drop the file that holds
fp, and nothing after the deletes makes a file boundary after it. The
fix is not in 031-03's design; it is independent of it, and fits
either M1. The ways seen:

* **The Javadoc**: the 400 kB are of the stream; a file database also
  keeps the rest of the file that holds the first available position,
  up to a quarter of the stream kept when that file was made.
  No code; the promise becomes what the code does.
* **The storage**: a file boundary after fp. For example, at a cut
  that leaves the stream kept far below the last file's capacity,
  `FileStream` ends that file at its next record and makes the next one
  of the size the rule gives; with M1 counting the storage's bytes
  (from the storage's first position, not fp), the calls then begin an
  iteration whose cut passes the old file, which goes. Not designed or
  measured here; whether a start accepts a file that is not the last
  and is shorter than its capacity, at an index unit boundary, is to be
  checked (the open reads the files by their lengths).

### 4. What this entry changed

The probes; this entry; the index line. No change to `java/`, 033 or
the release notes: an RB entry is drafted for the lead.


Log
---

2026-11-25. Registered by lead-1125, from 031-02's finding F2.

2026-11-25. Taken by an agent of lead-1125 (clone c61, branch 028-61).

2026-11-25. Investigated: the case run on `main`, 2026.6 and
`031-03-proto` (10,400, 10,400 and 8,801 kB in seed 5); reclaim cuts to
61 kB of stream kept, and the rest is the file storage's last file,
whose capacity (20 MB) was chosen while the stream was large. Not
RB-007, not 028-58: a fault of its own against `Database.maintain()`'s
Javadoc, S4, in 2026.5 and 2026.6; 031-03 does not end it. An RB entry
drafted for the lead. Status done.
