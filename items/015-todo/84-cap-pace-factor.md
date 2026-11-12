015-84. Investigate: a decrease's commits grow with the keys: cap the pace's factor S/sd?
=========================================================================================

Made in 024-31 (2026-11-12).

Status: open. Kind: investigate. Created 2026-10-29 as 005-77; moved here
on 2026-11-05 at Frans's decision (decided 2026-11-04/05), untouched: what
follows is 005-77's as it was when it moved.

Registered as Frans decided (2026-10-29, 10:02), on 006-10's decision 4
(007-07 at 50M keys): "an entry for A as recommended", that is, an entry to
test a cap of the pace's factor S/sd at 10M and 50M keys. Registered only;
nothing run or changed.


The issue
---------

Since 007-07 (step 3 of 007-03, with D4:B) a record takes its share of the
startup section's got-dirty index nodes, in `TransSeq.take`:

    share = D * (o / O) * (S / sd)

with o the record's own bytes, D and O the section's got-dirty nodes and
own bytes, S the stream from the startup pos to its end, and sd the startup
distance's setting. In steady state S/sd is about 1: the section is at most
1.11 sd at 10M and 50M keys (007-07, 11.1). After a decrease with one call
(D4:B), S is still the old section, so S/sd starts at the ratio of the old
setting to the new one: 10 from 1000 to 100 MB, 4 from 200 to 50 MB.

007-07's section 11 (50M keys, 2026-10-28; 11.2 and 11.3) measured what
that does:

* From 1000 to 100 MB at 50M keys, the catch-up's records (from
  `setStartupDistance`'s record until the section is below the new 2 sd)
  are 12 to 14 times the new mean record: the largest user record 13.3 to
  15.4 MB, against 2.3 to 2.9 MB at 10M (3.3 to 4.3 times); the call's own
  record 11.4 to 11.6 MB, against 3.3 to 3.6 MB. Every one of the 196 to
  201 catch-up records is over 3 times the new mean, 61 to 62 over 5 times
  and 15 to 16 over 10 times. From 200 to 50 MB the largest is 8.8 MB, 6.9
  times the new mean (10M: 4.7 to 5.1 MB, 5.3 to 5.9 times).
* Each such record is written in the commit of a user transaction (the
  take runs in `Db.store`), so the committing thread writes it, and the
  writers behind it wait.
* The cause, from 007-07's share estimate (`share.py`, 11.2): the share
  writes both the plateau and the second peak, not the deadline; the nodes
  written are 0.5 to 1.2 times o × D/O × S/sd at every record. S/sd starts
  at 10 at both sizes, but D/O, the section's got-dirty nodes for each MB
  of own bytes, starts 4 times larger at 50M (12k against 3.2k), as a put
  more often makes a node dirty that was clean; at 90 percent of the
  catch-up D/O is 31k against 12k while S/sd is still 7 against 4.5, the
  peak.
* For the startup bound (T3_bounded, d + 2M with M the largest record),
  M is then 15 MB against d = 200 MB (11.3, point 3).

Not known:

* Only bytes were measured (byte counts, `nice -n 19`), not the commit
  times of these records.
* 100M keys were not run: the JVM needs a heap over F53's 32 GB. From 10M
  to 50M the largest record grew 4 times.


Proposal
--------

Cap the factor S/sd in the share, as two variants:

* **cap 2**: share = D × (o / O) × min(S / sd, 2);
* **cap 4**: share = D × (o / O) × min(S / sd, 4).

So that a decrease's commits stay near the steady ones (007-07, 11.3,
point 4).

* **The section still cannot grow.** The deadline, at max(d_h, span),
  takes whatever the share leaves, and the span only shrinks (007-07,
  10.4); the cap changes only the share.
* **The catch-up gets longer.** 007-06's "follow", whose factor was at most
  2, took 3.0 to 3.4M puts (1.6 to 1.7 GB of stream) from 1000 to 100 MB at
  10M keys to bring the section below the new 2 sd, against 0.59 to 0.67M
  puts (0.82 GB) with D4:B now (007-06, section 3; 007-07, 10.4). Its user
  records were at most 2.75 MB. Cap 2 should be about that; cap 4 between.
* **The Lean bounds are unaffected.** `T3_take` and `T3_take_decrease`
  hold for any pace (007-08, section 2): the pace is any function, and no
  theorem uses its arithmetic. `T3_take_decrease`'s second form, the
  section after T(m+n) plus n at most the section after T(m), says the
  section still shrinks with every transaction until it is below 2 sd',
  with or without the cap.
* **Steady state should not change.** With S/sd about 1 (at most about
  1.2 with the last record), a cap of 2 or 4 does not bind, so the steady
  streams should be the same, byte for byte. To check, not assume.
* The call's own record (`setStartupDistance`'s transaction, which already
  uses the new setting) is a share too, so the cap shrinks it as well.


Questions
---------

1. **Records and catch-up length, each cap, 10M and 50M keys.** 007-07's
   step-2 set, its decreases: 1000 to 100 and 200 to 50 MB, at the "worst"
   and "20M" points (10.4 at 10M, 11.2 at 50M). For each: the call's
   record, the largest user record and its multiple of the new mean, the
   catch-up's records over 3, 5 and 10 times the new mean, the puts and
   stream to the new 2 sd and to sd, and the section after. Against 10.4
   and 11.2 without a cap, and 007-06's "follow".
2. **Commit times of the largest records**, with and without the cap: a
   timed measurement, in a quiet block (F53 or s1, `performance.sh`'s quiet
   check): the commit latency of the call and of the catch-up's largest
   records, and the other writers' waits, at 50M keys from 1000 to 100 MB.
   This says whether 13 to 15 MB records matter in time, which the byte
   counts do not.
3. **Steady state unchanged:** the cap must not bind when S/sd is about 1.
   The steady runs of 007-07's step-2 set (10.4, 11.1) with each cap give
   records that are byte-identical with those without it; and the largest
   S/sd seen in them, logged, so the margin is known.
4. **StreamDigest:** identical against `main` (36 of 36), as no
   configuration of it lowers the startup distance (007-07, 10.3); the
   stream changes only after a decrease.
5. **Determinism with restarts during a catch-up:** a restart in the middle
   of a catch-up, with the cap, gives the same stream as without the
   restart (007-07, 10.2's restart test, at a decrease), as the cap uses
   only S and sd, which a start has.
6. **The deadline's part:** with a smaller share, how often the deadline
   takes a transaction that the share would not (`DlProbe`, 007-07, 10.4:
   10 to 40 percent of the catch-up's commits now), and whether the
   deadline then sets the records' sizes.
7. **One value or two:** from 200 to 50 MB S/sd starts at 4, so cap 4 does
   not bind there; does the cap need a different value at 1000 against
   200 MB (or one tied to sd), or is one constant enough?
8. **The quick suite's commit tail and startup** (added 2026-10-29, as
   Frans decided on 006-10's point 5: "as recommended", look at it with
   this entry). 007-07's quick suite (007-07, section 12.1; not a quiet
   block) showed, from main before 007-07 to 007-07's take, the commit's
   p99 and p99.9 9 to 11 percent higher with finite retention
   (w-uni-1k-fin's append p99 from 64.5 to 70.1 µs, p99.9 from 92.7 to
   102.9 µs; r-1k-fin's prepare phase +9.2 and +10.5 %), the median 2 to 6
   percent faster, and startup 1 to 4 percent slower (r-1k-fin reruns
   33,355 transactions instead of 32,540 from the same position;
   w-uni-1k-fin's restart from 0.595 to 0.620 s). Index writes moved from
   the user's records to reclaim's step records (from 430.0 to 462.8 bytes
   a put in steps, from 171 to 138 in the user's records); why the take
   moves them there was not looked into. Not yet explained. With each cap and without:
   the quick suite in a quiet block, its four scenarios in ABBA order, to
   see whether the tail and the startup move with the cap; and where the
   index writes go (the user's records against reclaim's steps), with an
   explanation of why the paced take puts more of them in the steps.


Done when
---------

* Both variants measured (questions 1 to 8), a recommendation (cap 2, cap
  4, another value, or no cap), and Frans's decision.
* With a cap: the change in `TransSeq.take`, with tests (a share capped at
  a large S/sd, the same share below the cap, a decrease's records);
  StreamDigest identical (36 of 36); `java/before-commit.sh` (BEFORE
  COMMIT OK), `java/stress/level2.sh` to `level4.sh`; and 007-07's step-2
  runs again on the changed code (10.4 at 10M, 11 at 50M); the comments of
  `TransSeq.take`, docs/levels.md section 5 and 007-07 follow.


First step
----------

A prototype in a scratch clone: the cap as a constant (or a system
property for the runs) in `TransSeq.take`'s share, one line. Run 007-07's
decrease from 1000 to 100 MB at 10M keys, "worst" point, with cap 2 and
cap 4 (`07-step3-paced-take/step2/`), and compare the records with 10.4's;
then the steady run at 1000 MB, to see it byte-identical. Then 50M keys
(`07-step3-paced-take/step2-50m/`, one JVM of 22 GB at a time).


Size and order
--------------

M: a line of code, but the runs are long: 16 decrease runs (4 decreases,
2 key counts, 2 caps) and the steady runs, about a day of F53 at the
lowest priority (007-07's set at 50M took 3 h 20 min), plus the timed
measurement in a quiet block. No deadline: decreases are rare, and the
section's bound holds without the cap. After 005-76, or independent of it
(different code; both need F53's quiet time). Builds on 005-49 (the pace),
007-06 (the variants, "follow"), 007-07 (step 3, D4:B, sections 10 and 11)
and 007-08 (T3_take for any pace).


Note: 005-79
------------

2026-10-29, at Frans's request (15:48): 005-79 replaces the doubles in
`TransSeq.take` with integers, option B (the share in fixed point, units
of 2^-16, the dither's top bits), done on its own, not with this entry.
Both change the same expression, the share. Whichever comes second builds
on the first: a cap of S/sd written in B's integers, or B's share computed
from the capped factor; the runs of this entry measure the take as it is
in `main` then.
