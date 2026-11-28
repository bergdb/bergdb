028-73. Decide: new stream files a tenth, the writer waits at a new database's first 10 MB
=========================================================================================

Status: decided (2026-11-28): (b); built and gated on a branch, to be
landed. Kind: Decide. Frans: decided.
Created 2026-11-27 by Frans Lundberg.

What: since 028-62 (`05fc573c`, the fix of RB-011), `FileStream` gives a
new stream file about a tenth of the stream kept, not a quarter
(`FileStream.determineFileSizeIndex`). A new database then writes its
first 10 MB in files of 200 kB: 50 files, where the quarter made 20
files up to 4 MB and 1 MB files from there. The stream's bytes are the
same; only the file boundaries move. With per-append forcing (the Pub
layer's default), each file costs about 10.5 ms in `BufferedStream`'s
thread: the APPEND force of its last piece, the OPEN force of the next
file and a directory force. The thread then drains about 20 MB/s while a
fast load appends about 46 MB/s. A flush takes up to 5 MB, half the
write buffer, and frees that room only when it ends
(`BufferedStream.flushToStream`); the 10 MB buffer is full at about
12.6 MB of stream, and the writer waits for room in it.

Found by the timing run on `main` of 2026-11-27 (`5b88cc80`, against
release 2026.6): the pause probe's load phase (1M keys in 2,000 commits
of 500 keys, not counted in the probe's figure) had waits for room in
the write buffer in 6 of 6 runs on `main`, the longest 144 to 282 ms;
2026.6 had 0 to 16 ms. Bisected the same evening to `05fc573c`: the
commit before it, `9cbf47f6`, waits at most 30 ms; 031-06's landing is
not involved (`a9d87266`, the merge's first parent, waits the same). At
1M keys: 122 files and 333 file forces, against 56 and 208. At 10M keys
the same, only at the start: 148 to 184 ms plus 51 to 53 ms, no other
wait in a load of about 140 s (2026.6: one wait of 23 to 42 ms). A
database whose kept stream stays between 4 and 10 MB is also back on
200 kB files, about 20 MB/s against about 90 MB/s in 2026.6 (not
measured).

The one commit of 68.9 ms in the full run's measured phase (the run of
17:16, phase tsize=500) is not explained by this: by then the stream is
over 230 MB, in 20 MB files. Two reruns of the pause step, ABBA against
2026.6, gave 10 to 13 ms, TIMING OK.

Why: not a correctness fault. P1's guide of no stop-the-world (010-01)
is passed once per new database, at its first 10 MB, by a wait for the
disk that 028-62's measurements did not look at.

Frans: decided, (b) (2026-11-28). 028-62's rule is Frans's ("a tenth",
2026-11-26), so a change of it was his. The options:

* **(a) Accept it.** No change. The wait is the disk's wait as 005-46
  counts it, once at a new database's first 10 MB; a database kept
  between 4 and 10 MB writes at about 20 MB/s.
* **(b) A floor of 1 MB once the kept stream reaches 4 MB**, as the
  quarter gave; the tenth unchanged above 10 MB. RB-011's bound on the
  disk becomes "a tenth of the stream kept, or 1 MB for 4 to 10 MB kept";
  RetainChurn's seed-5 case is unchanged. Made on branch
  `loadwait-1mb-floor` (`5731b6c9`, from `a20b0034`, not on `main`):
  the floor in `FileStream.determineFileSizeIndex` with its Javadoc and
  the class Javadoc's "The files and the disk", `testFileSizeRules0`,
  `tFileSizeIncrease` (27 files for 11 MB, was 51); BEFORE COMMIT OK.
  The probe's load phase, ABBA, 4 runs each: 1 wait of 7 to 21 ms,
  against `main`'s 2 waits of 145 to 169 ms.
* **(c) (b), and a floor of 5 MB from 20 MB**, for a writer faster than
  the probe's (b keeps 1 MB files for 10 to 50 MB of stream, about
  90 MB/s, above the probe's 46 to 70 MB/s). RB-011's bound becomes
  5 MB for 20 to 50 MB kept.
* **(d) Back to the quarter.** Undoes RB-011's fix (20 MB files after
  85 MB kept).

Recommendation: (b). It removes the wait in the measured case, keeps
RB-011's fix where the tenth matters (an emptied database's last file),
and is made and gated.

Decision: Frans, 2026-11-28, 07:27: (b).

Done when: Frans has chosen; for (b) or (c), the change is on `main`
with BEFORE COMMIT OK and the probe's load phase measured ABBA against
`main`'s; 027-13, section 4, 027-14, 028-62, 033 (RB-011) and
`releases/next.md` give the sizes that hold.

First step: rebase `loadwait-1mb-floor` onto `main`, the documents
above, the gate.


Result
------

Built 2026-11-28 by an agent of lead-1127, from `main` at `23a54033`:
`loadwait-1mb-floor`'s commit taken onto it; the class Javadoc's "The
files and the disk" merged with 028-66's text of the cut's batches and
the gap in the files, which `main` had since.

* **The code.** `FileStream.determineFileSizeIndex`: a size of at least
  1 MB (`FILE_SIZES[1]`) when the stream that the files hold is 4 MB or
  more; the tenth unchanged, so from 10 MB on the rule is the tenth's.
  The stream's bytes are the same; only the file boundaries move.
* **The tests.** `testFileSizeRules0` (unit): 10, 9 and 4 MB give 1 MB,
  3.9 MB gives 200 kB, and a kept stream of 3 MB after 1 MB files goes
  back to 200 kB at once; `tFileSizeIncrease` (f): 27 files for 11 MB,
  51 with the tenth alone. `testMixedFileSizes` and `DbTesterStream`'s
  `testZeroedTailOverMetaBlock`: Javadoc only.
* **The documents.** 027-03, section 4; 027-13, section 4 (the disk);
  027-14 (the files and the disk); 028-62's decision (a dated addition);
  033's RB-011; `releases/next.md`.
* **The probe** (each build's own `PauseProbe`, `-Dseconds=1
  -Dtsize=1`, ZGC, the load phase of 1M keys). The figures of 2026-11-27,
  the branch on `a20b0034`, ABBA, 2 rounds: the floor 1 wait in each run, 7.1 to
  20.9 ms, 99 directory and 286 to 287 file forces; `main` 2 waits,
  longest 145.5 to 168.6 ms, 123 directory and 333 file forces.
  2026-11-28, on this build and `main` at `23a54033`, ABBA, 1 round, F53
  busy (load average 15 to 19, other heavy runs): the floor 10 and 11
  waits, longest 489.6 and 417.7 ms, 1,492 and 1,547 ms in all, 99
  directory and 277 to 278 file forces; `main` 11 and 11 waits, longest
  991.3 and 801.6 ms, 2,403 and 2,411 ms in all, 123 directory and 324
  to 325 file forces. A figure of time on a busy machine decides
  nothing; the counts of forces are the change's: 24 fewer new files in
  the first 10 MB.
* **Not measured again:** RetainChurn (031-02): its figures in 027-13
  and RB-011 are of the tenth alone; the apps of 031-02 do not compile
  on `main` since `maintain()` takes a budget (031-04).


Log
---

2026-11-27. Registered by lead-1127, from the timing run on `main` of
17:16 and the bisection of 18:22 to 18:41 (an agent of lead-1127).

2026-11-28. Frans decided (b) (07:27). Not on `main` yet.

2026-11-28. Built by an agent of lead-1127 (branch `floor-74-r6`, from
`main` at `23a54033`): the floor, its tests and the documents; the probe
run ABBA against `main` on a busy F53. Gates: below.
