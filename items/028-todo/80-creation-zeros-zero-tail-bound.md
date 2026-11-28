028-80. Fix: a creation left as zeros is not refused as a creation; the zero tail's bound rests on the default buffer
=====================================================================================================================

Status: in progress (an agent of lead-1127, 2026-11-28). Kind: Fix.
Frans: none.
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


Log
---

2026-11-28. Registered by lead-1127 from the review's F3 and F4; taken
by an agent of lead-1127.
