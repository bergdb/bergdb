# 006-36 Day work, 26 November 2026

Created 2026-11-26 by Frans Lundberg. Status: active. The plan for the
lead's day of 2026-11-26 (lead-1126), a Thursday, and its night to
Friday 07:00: the progress and the outcome. The way of working is
013-04's (the lead).


## 1. The request

* Open from 006-35: 031-03's F1 to F6 (the design of `maintain()`),
  028-60's part 2, 028-62 and 028-54, all for Frans.
* `week.sh` takes about 15 hours since 028-63's envelope: bring it back
  to about 10 hours, at most 12 (028-64).


## 2. Decisions

Frans, 2026-11-26:

* 031-03, F6: 9.1 (RB-006's remaining part) and 9.2 (RB-010) confirmed
  as released bugs, S4; 9.3 a space cost, registered as 028-65 (09:46).
* 035 created, the environments BergDB runs in, examined with programs
  that use no BergDB code; 035-01 first, the zeros after a kill (031-02,
  F1); Windows not now. 028-60's part 2 waits for 035-01 (10:20).
* The lead answers within seconds; writing and chores (item texts,
  commits, the plan) go to a background helper of the lead, which may
  write to `main` while the lead does not (10:30).
* `week.sh`: an aim of 10 hours, at most 12 (06:35); no whole-run hang
  guard (07:58); 028-64 landed and a full `week.sh` started (07:58).

* 031-03: no choice of F1 to F5 yet. A study first of `maintain(int
  budget)`, a call with a cost budget and passes that end by
  construction (031-04); a study of the direction, not a decision to
  build it (09:17).
* 031-04, Q9: (b), the handoff, for the direction studied (10:42).
* 028-62 (RB-011): a new stream file gets about a tenth of the stream
  kept, not a quarter; no promise of disk size in the Pub API (the
  Javadoc of `Database.maintain()` speaks of the stream); `FileStream`'s
  Javadoc states the slack and that files are only appended to and
  deleted whole, so a copy in order is a backup; the copy-and-swap at a
  cut not made: complexity on the file system, and the backup property
  (11:18).
* The usage limit 70 % (13:05).
* 028-54 and the stream: every write to the stream a function of the
  stream itself and the user actions (accepted calls of `Db.execute()`
  and `Db.maintain()`, with their times); worded precisely and, when
  possible, proved; it extends P2 to maintenance and to anything that
  writes; studied in 031-05; a review by an agent on Fable, high, when
  the study is done (12:59, 13:03).
* 028-60's part 2: the zero tail removed by `FileStream` at open, the
  same rule on every system, at most 8 MB, nothing above `FileStream`
  (13:26).
* Frans off for the day at 13:39.

The lead, 2026-11-26:

* 028-64 by one agent (Opus, xhigh) in a clone: coverage kept where the
  time can be won by running steps side by side, cut only where it
  cannot (class 1, how a task is done).


## 3. Progress

* 06:31 lead-1126 started; 06:32 lead-1125 closed (006-35 closed,
  `5f946d61`). Nothing ran.
* 06:35 Frans: `week.sh` to about 10 hours, at most 12. Its last run:
  579 minutes without the large reclaim run, which takes 5.5 hours on a
  typical seed since 028-63 (60 to 90 minutes on 028-43's local seed).
  028-64 registered; an agent started.
* 07:46 028-64 done (agent, Opus xhigh, 69 minutes): the large reclaim
  run and the large conformance set beside the other steps, each in a
  clone of its own; the same steps, seeds and sizes; about 6 hours
  estimated (5.5 to 6.7). 08:01 the whole-run hang guard removed (Frans);
  `week.sh short` WEEK OK (13 minutes). Landed, with `AGENTS.md`'s and
  013-04's times of `week.sh`; a full `week.sh` started on `main`.
* 06:47 to 08:10 031-03 gone through with Frans: the witness and the
  drain; MIN_RELEASE and the step reserve; `maintain()` as the
  application's idle-time hook with a budget per call; the stream kept,
  the live bytes and the space amplification, kept / live.
* 09:20 031-04 registered (the study); one agent (Opus, xhigh) in a
  clone, stop 13:30; Codex's review after it.
* 10:19 031-04's study done (agent, 62 minutes): `void maintain(int
  budget)`, passes begun by calls cut at their own start, a pass begins
  when a >= fp (a: the application's last record's position, read off
  the stream); no drain, no MIN_RELEASE; Lean unchanged; RB-007's case
  117 kB kept, quiet when done, Codex's drain case ends; a P1 finding
  (Q9: a commit waits behind a call's parts at large budgets). Landed as
  text; Codex's review started (10:22).
* 10:25 035 and 035-01 created; an agent on 035-01 (F53, s1).
* 10:43 Q9 (b) to the prototype by an agent (Opus, high), with ZGC and
  the commit thread of PassProbe; results in 031-04's q9-handoff.md.
* 10:36 Codex's review of 031-04: the direction simpler and sounder
  than O-1; an upgrade recovery defect (P2) to repair before adoption;
  six more findings (031-04, section 11). The Q9 agent also repairs
  finding 1 in the prototype.
* 11:19 028-62 by an agent (Opus, high) in a clone, stop 14:30.
* 11:24 031-04: Q9's handoff and Codex's finding 1 in the prototype
  (agent, Opus high, 40 minutes): with ZGC the longest commit during
  calls 36 to 66 ms at a budget of 100,000 (before: up to 1.1 s); the
  upgrade restart case now the same stream; BEFORE COMMIT OK.
* 11:35 035-01 done (agent, Opus xhigh, 70 minutes): 29,600 kills on
  F53 and s1; zeros within a file's length only on APFS, in pieces of 1
  to 4 MiB aligned to the write's first page (as XNU's
  `cluster_write_copy` drops a failed piece); none on HFS+ or s1's
  ext4; on APFS images and RAM disks 7 cut writes held a deleted file's
  bytes. 028-60's part 2: B2 with four conditions recommended; the
  stale-bytes risk is new.
* 11:48 028-62 done (agent, Opus high, 30 minutes) and landed: a tenth;
  RetainChurn seed 5 from 10,400 to 400 kB on disk (61 kB of stream);
  the Pub's maintain() speaks of the stream only; FileStream's Javadoc
  states the slack and the backup by a copy in name order; BEFORE COMMIT
  OK, KILL RESTART OK. The cut's deletes lag more behind a fast writer
  with more files (028-66).
* 13:12 028-60's part 2: B2 inside `FileStream` only proposed (a zero
  tail of the last file truncated at open, the contract's prefix
  restored; nothing above `FileStream` changes); default start 14:30.
* 13:14 035-02 done (agent, Opus xhigh, 93 minutes): on F53's internal
  SSD no deleted file's bytes in 63 cut first writes of new files (59
  zeros, 4 prefixes); on APFS RAM disks and images in most; a failed
  write (EFAULT) cuts as a kill does, without one; ext4 clean prefixes.
  A start refuses most stale tails with unclear messages and may first
  fill up to 2 GB of zeros: 028-67 (C1 recommended now, C3 with the
  next format change).
* 13:56 028-60's part 2 done (agent, Opus high, 28 minutes) on a
  branch: seed 63 starts at its last synced transaction; BEFORE COMMIT
  OK, KILL RESTART OK, KillWriter OK; not landed: for encrypted streams
  it adds a switch in the Pub layer's builder, against the constraint;
  Codex's review started, with the alternative of a run of at least
  4,096 bytes.
* 14:10 031-05's study done (agent, Opus xhigh, 69 minutes): the
  wording of the invariant; the inputs outside the stream found and
  handled (N1 to N10); 15,625 crashes and 15,625 stops at every record
  boundary give the stream of the uninterrupted run (031-04's
  prototype: 195 of 1,857 boundaries differ); D2 recommended; a Lean
  theorem T16_crash sketched; Q1 to Q9 for Frans. Landed as text; the
  review by Fable started (14:09).
* 14:36 to 14:45 028-60's part 2 after Codex's review: the zero tail
  left out of the stream at open and cut at the first append; a keyless
  or refused start changes no byte; Codex's second round: two smaller
  findings being fixed; encryption for Frans.
* 14:47 031-05's review by Fable (agent, Fable high, 38 minutes): take
  the direction as D2; the prototype held at every record boundary,
  under concurrency and upgrades; nine findings (031-05, section 12),
  among them a crash inside a record (the goal holds at record
  boundaries), the clock held after some crashes, fixed by a start that
  writes what is due (Q2 (c)), and two f-tests that D2 fails.
* 16:04 028-66 (agent, Opus high, 20 minutes): a batch of the cut's
  deletes with one directory force keeps the disk at 1.03 to 1.15 of the
  stream kept at every writing rate (main 1.09 to 1.58), and with no
  limit the hard-sync writer at about 105,000 transactions a second
  (main since 028-62's tenth about 64,000: a force per deleted file);
  not landed: a batch breaks 011-07's rule that every prefix delete is
  forced before the next (two power-loss tests); options A to C for
  Frans (028-66). Figures indicative (week.sh's large run beside).
* 17:41 `week.sh` on `2a321805`, the first run in three lanes (028-64):
  WEEK OK in 565 minutes, 9.4 hours, under the day's heavy load from
  agents beside it (the large reclaim run 9.4 hours, 5.5 alone; the large
  conformance set 6.3 hours). 17:44 `night.sh` started on `8ad6599b`.
* 20:43 `night.sh` on `8ad6599b`: NIGHT OK in 180 minutes.


## 4. Waiting for Frans

* 031-03, F1 to F5: wait for 031-04's study.
* 028-60, part 2: B2 inside `FileStream` only (proposed 13:12; by
  default started 14:30).
* 028-67: stale bytes in a start's tail: C1 now, C3 with the next
  format change (recommended).
* 031-04: Q1 to Q8 and the direction, with 031-05's result.
* 028-54: whether P2 covers a restart inside a commit's maintenance.
* 028-66: the cut's deletes: A as is, B a batch with 011-07's rule
  changed, C a forced record (not designed); since 028-62 a hard-sync
  writer at full speed is about 40 % slower by the forces of its
  deletes.

## 5. Outcome

(At the end of the day.)
