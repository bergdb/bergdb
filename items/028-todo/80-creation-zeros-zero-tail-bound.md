028-80. Fix: a creation left as zeros is not refused as a creation; the zero tail's bound rests on the default buffer
=====================================================================================================================

Status: done (2026-11-28): on `main` (`d5aa1cf7`, with 028-70's
follow-up `929537b5` and the gates `71cf993e`); F3 is RB-014 (033).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: two findings of the review of the start path of 2026-11-28 (033,
`reviews/2026-11-28-start.md`, F3 and F4), both S4 (033's rules).

* **F3. A creation whose first write a kill left as zeros.** A kill of
  a creation's first write can leave a file of zeros only (028-60's
  zeros begin at a page boundary, and the creation's first write begins
  at the file's start). `FileStream.zeroTailLength` leaves a stream
  whose only file is all zeros as it is (a repair never empties a
  stream), and `RecoverableStream.isIncompleteCreation` takes only
  bytes that begin as a meta block. The start refuses with "Could not
  find *any* valid meta block. At least the very first meta block must
  be valid in a db stream.", a `StreamFormatException`, where every
  other cut of a creation, with or without zeros after it, gives
  `DatabaseNotCreatedException` and "Remove its files and start it
  again" (028-18). The review's `CreationZerosProbe`: the creation (416
  bytes) cut at 12 positions, alone and followed by zeros to 4,096,
  `DatabaseNotCreatedException` in all 24; zeros only to 4,096, the
  `StreamFormatException`. No file changed. By reading, 2026.6's
  `isIncompleteCreation` has the same condition; whether 2026.6 shows
  it is checked with the fix (033 gets an entry if so).
* **F4. The zero tail's bound, the Core API only.**
  `FileStream.ZERO_TAIL_MAX` is 8 MB, by its Javadoc because "a write of
  BufferedStream's thread is at most 5 MB". A write is at most half of
  the buffer's largest size, and 5 MB is half of the default, 10 MB
  (`StorageManager.DEFAULT_BUFFER_SIZE`).
  `DbBuilder.stream(name, stream, bufferSize, bufferTime)` takes any
  size: from 16 MB a write can pass 8 MB, and a kill's zeros of more
  than 8 MB are left in the stream, where a start refuses them if they
  reach past a record's end ("Bad transaction size in db stream, 0").
  The Pub API has no such setting. By reading; not run. Not in 2026.6,
  which has no zero-tail rule (RB-012).

Why: F3: an application that removes the files of a database that was
not created does not see this one as such. F4: the rule of 028-60 holds
for the default buffer and is stated without that condition.

Frans: none.

Done when: tests that fail before the fix; F3 gives
`DatabaseNotCreatedException` as an interrupted creation does, and
writes nothing; F4's bound holds for every buffer size that the Core API
takes (the builder bounds the size, or the open's bound follows the
buffer's), or the limit is stated in `DbBuilder`'s and `FileStream`'s
Javadoc; `java/before-commit.sh` prints `BEFORE COMMIT OK`;
`CreationZerosProbe` shows no `StreamFormatException`; 027-11 and
027-14 agree with the code.

First step: the review's F3 and F4; `CreationZerosProbe`.

Found by: the review of the start and recovery path of 2026-11-28 (033,
`reviews/2026-11-28-start.md`, F3 and F4).


Result
------

On the branch `start-fixes`, on 028-70's branch `028-70-refuse-first`
(2026-11-28).

* **F3, built.** `RecoverableStream.isIncompleteCreation` also takes a
  stream that begins at 0, is at most a meta block distance (200,000
  bytes) long and holds zeros only: a creation's first write that a kill
  left as zeros. Such a stream holds no meta block and no record, so no
  data; the start refuses it with `DatabaseNotCreatedException` ("Remove
  its files and start it again") before it reads anything else, and
  writes nothing. The bound is `FileStream`'s first file: the stream
  moves to a second file only after the first is forced (`newFile`), so
  only a write into the first file can leave zeros from position 0; a
  longer stream of zeros, or one that begins after 0, is refused as
  before. `FileStream`'s open is unchanged: it leaves the only file all
  zeros as it is (a repair never empties a stream). Javadoc:
  `isIncompleteCreation`, `Db.refuseIncompleteCreation`,
  `DatabaseNotCreatedException`; 027-11, 1.2, step 2; 027-03, sections 7
  and 14.2; 027-14.
* **F4, built: the write bounded, in `FileStream`.** An append hands the
  system at most `FileStream.WRITE_MAX`, 5 MB, in one write; a longer one
  is written in pieces of 5 MB, one after the other, with one force
  after them, as before, with per-append forcing on. The zeros that a
  kill leaves within the last file's length are where the bytes of the
  write that it cut should be (031-02, F1; 035-01, section 9), so they
  are at most 5 MB, below `ZERO_TAIL_MAX`, whatever the buffer above:
  the bound holds for every buffer size that `DbBuilder.stream` takes
  and for any other user of `FileStream`. Why in `FileStream` and not
  the builder or `BufferedStream`: the bound and its reason are then in
  one class, which needs no knowledge of the layer above, and no API
  changes; a bound of the builder's size would refuse sizes that work
  today, and a bound that follows the buffer would need the buffer's
  size at `FileStream`'s open, which runs before the builder wraps the
  stream. 5 MB is half of the default buffer, so `BufferedStream`'s
  writes with the default are not split; a write of more than 5 MB
  needs a buffer of more than 10 MB and a last file of 20 MB or more, a
  stream of 200 MB or more. Javadoc: `ZERO_TAIL_MAX`, `WRITE_MAX`,
  `FileStream`'s class comment; 027-11, 1.3; 027-14.
* **Release 2026.6** (built from its tag and run with a probe, 2026-11-28):
  a creation's first write left as zeros (416 and 4,096 bytes) is
  refused with a `StreamFormatException`, "Invalid magic bytes in
  stream"; so is a cut creation with zeros after it within the file's
  length (200 or 300 bytes, then zeros to 4,096: "Bad transaction size
  in db stream, 0"), where 2026.6 has no rule of a zero tail (RB-012).
  So F3 is in 2026.6, with RB-012's zeros. F4 is not: 2026.6 leaves no
  zeros out.

Tests, each failing before the fix and passing after it (2026-11-28):

* `RecoverableStream.testIsIncompleteCreation`: zeros only of 1, 100,
  128, 272, 4,096 and 200,000 bytes are an incomplete creation, 200,001
  are not, nor zeros with one byte 10 at the start, the middle or the
  end; before, "1 zero bytes, expected true, got false".
* `DbTesterStream.testCreationLeftAsZeros`: a `FileStream` whose only
  file is zeros of 416 (the creation), 4,096, 16,384 and 200,000 bytes,
  and one of 200,000 zeros with a second file of 3,000 zeros, which the
  open leaves out: `DatabaseNotCreatedException`, no file changed; with
  the file removed the start creates the database. Before, "Could not
  find *any* valid meta block".
* `FileStream.testWritesAtMostWriteMax`: an append of 12 MB to a last
  file of 5,000,001 bytes (size class 20 MB) is three writes, 5, 5 and
  2 MB, and one force; before, one write of 12,000,000 bytes.

* `PubTester.testCrashInCreation` expected a `StreamFormatException`
  for a stream of 128 zero bytes, as 005-33 left such a stream an error:
  with a crypto key, zeros could not be told from a wrong key. There is
  no key since 028-69; the test expects `DatabaseNotCreatedException`,
  and the stream unchanged.


Gates
-----

On F53 beside other sessions' runs, 2026-11-28, on the branch: 028-80 on
028-70 as it landed on `main`; `before-commit.sh` also with 028-70's
follow-up (its review's three notes, the commit after 028-80's).

* `java/before-commit.sh`: BEFORE COMMIT OK (137 s; unit 1,763 tests,
  f 96). On the change's first form it failed at
  `PubTester.testCrashInCreation`'s zero bytes (above).
* `java/stress/level3.sh`: LEVEL 3 OK (its power-loss stage: POWERLOSS
  OK, 8 seeds, 488 cold recoveries).
* 031-06's probes: `sweep.sh`, 0 different in each of its 63 lines;
  `faults.sh`, bad 0 in each of its 42 lines.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* `java/stress/kill-restart.sh`: SELF-CHECK OK, LATE EXIT OK, KILL
  RESTART OK: 1000 kills and 50 exits in 1099 s, seed 20261128.
* The review's probes (033, `reviews/2026-11-28-start-probes`):
  `CreationZerosProbe`, `DatabaseNotCreatedException` in all 25 images,
  zeros only to 4,096 among them, no `StreamFormatException`, no file
  changed. `StartChain 70000 70099 20 2 30 1 0`, no other bytes: 2,000
  starts after 1,366 kills, 245 kills in a recovery's writes and 664
  power losses in a cut's batch; 32 refusals of 028-76's decided case
  (a), no failure. `StartChain 60000 60099 20 2 30 1 25`, other bytes
  after a quarter of the kills: 2,000 starts; of 197 tails of other
  bytes, 118 refused with a `BadTailException` and started after the cut
  at P, 74 taken; 35 of the decided case, no failure, and in these 100
  chains no later refusal of F2 (028-79). `StaleFirstBlockProbe`, as on
  `main`: F2's refusals (028-79).

On `main`'s tree at `8fe32468` with the three commits, as they landed
(2026-11-28, the lead): `java/before-commit.sh`, BEFORE COMMIT OK (161
s); `java/stress/level3.sh`, LEVEL 3 OK.


Log
---

2026-11-28. Registered by lead-1127 from the review's F3 and F4; taken
by an agent of lead-1127.

2026-11-28. F3 and F4 built on the branch `start-fixes` by an agent of
lead-1127 (on 028-70's branch): zeros only as an incomplete creation,
and `FileStream`'s writes of at most 5 MB; 2026.6 shows F3.

2026-11-28. The gates passed (above). Release 2026.6 refuses a
creation left as zeros with a `StreamFormatException`, so F3 is in it,
for 033.

2026-11-28. Landed on `main` (`d5aa1cf7`, `929537b5`, `71cf993e`)
after the gates of the combined tree (above). F3 registered in 033 as
RB-014, S4, in 2026.5 and 2026.6. Done.
