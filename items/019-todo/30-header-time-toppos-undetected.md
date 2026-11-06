019-30. Decide: a record's time or topPos changed within the checks passes undetected
=====================================================================================

Status: done (decided 2026-11-06: outside the fault model for 2026.3,
option (a)). Kind: Decide. Frans: decision.
Created 2026-11-06 by Frans Lundberg.

What: no checksum covers a record's header (019-07). A start checks its
fields only against each other: the times increase (005-75), the time is
in range, the `startupPos` is one the take can have written (015-75), and
the last record's `topPos` is the newest version of its top node among the
startup section's nodes (015-75). A change that stays within these checks
is taken, and the database answers other values than it wrote, with no
error:

* **The time** of a record raised or lowered within its neighbours' (one
  unit, one step of 10, a high bit of the last record's, or
  `Klong.MAX_TIME` for the last record): the transaction is taken at the
  new time, so a read at its own time misses it. A byte flip (xor 0x80) of
  the time's bytes 1 to 5 of the last record gives the same.
* **The last record's `topPos`** set to a top node's version that lies
  before the startup section (in the `take` configuration, `topPos` 6672
  for 27120): the section has no newer version of that node to compare
  with, so the start takes the older index, and reads answer older values.

Why: found by harness 6.1, corrupt streams at a start (018-07), in the
night 006-12; seed 1 of its sample (`CorruptStreamTester` 1, on `main`
with the harness), among others:

```text
all, flip, xor 128 at 7721 (record at 7712, offset 9: time): undetected: the counter
  at time 300 is "29", not 30
all, header, time 301 (was 300) of the record at 7712: undetected: the counter at time
  300 is "29", not 30
all, header, time 31 (was 30) of the record at 1016: undetected: the counter at time 30
  is "2", not 3
take, header, topPos 6672 (was 27120) of the record at 27088: undetected: holds 50
  transactions by the counter, and /a is 9 bytes, not 126 bytes
```

This is the class of 015-73, which Frans decided at 2026-11-05, 15:35
(option (a)): a header field changed to a value that passes the cheap
checks. Damage other than a cut tail is outside the crash contract, and
its detection is best effort (018-01, section 6.1; 014-01, section 7).
019-07, the header checksum at the next change of `RECORD_FORMAT`, names
the time as one of the fields it would protect.

Frans: a decision; he chose (a), 2026-11-06, 10:42 (the log).

* **(a) Outside the fault model for 2026.3, as 015-73.** The harness counts
  such a copy as known to pass undetected, and 019-07's checksum catches
  it at the next change of the record format. Nothing changes in the
  code; the release notes' limit for 015-73 names the time and `topPos`
  too. Cost: none. The damage stays undetected until 019-07.
* **(b) More cheap checks.** None found that catches these: a time within
  its neighbours' is a valid time, and an older version of a top node
  before the section is known only by reading records before it, which
  the bounded startup (007) does not do (the argument of 015-73's (b)).
* **(c) The checksum now** (019-07): a change of the stream format,
  which needs Frans's approval (018-01, section 2), the C clone (012)
  with it, and a new `RECORD_FORMAT`; streams of format 5 are refused.

Recommendation: (a), as for 015-73, with the release notes' limit
extended.

Done when: Frans has chosen; for (a), the entry is closed as decided and
the harness's skip list line becomes a `KNOWN` line (018-07, section 4);
for (c), 019-07's Done when.

First step: Frans's decision.


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-30" in `CorruptStreamTester.SKIP`.

2026-11-06, 10:42. Frans decided 019-30, 019-31 and 019-33 together, to
coord-1106, which asked for each as recommended: "Yes, as recommended.
BergDB assumes correct storage. Which makes sense. Ensure this is
documented in the relevant Javadoc comments. However, use of checksums
in the stream is also a reasonable design. Going in that direction is
definitely not for 2026.3. Remember the target: bug-free Core. Move the
possibility of checksums in the stream to a new item in 017. This may or
may not be added in some future release." Option (a): a record's time or
`topPos` changed to a value that passes the start's checks is outside
the fault model for 2026.3, as 015-73's `startupPos`. Option (c), a
checksum of the record header, is part 1 of 017-08, checksums in the
stream (019-07 moved there): not for 2026.3, and it may or may not come
in a future release.

2026-11-06. Done by agent d4 of coord-1106, option (a); nothing in the
Core changed. Harness 6.1 (018-07): a copy with a record's time or
`topPos` set, or a byte of them flipped, is marked known ("019-30") when
it is made, and an undetected one is counted as "known 019-30:
undetected", as 015-73's case is; its line left
`CorruptStreamTester.SKIP`, which keeps 019-32's only. Runs on the clone
d4: `unit.sh -c CorruptStreamTester` SUCCESS; the samples of seeds 1 to
5 and the full sets of seeds 20398 and 20399 (278,484 and 294,184
copies) with no failure; with nothing skipped
(`-Dbergdb.corrupt.skip=none`), seed 1's sample fails with one copy
only, 019-32's (it failed with 50 before). `releases/next.md`'s known
limit names the kind, with "BergDB assumes correct storage"; 018-01,
sections 3.1 and 6.1, and 018-07 follow. The statement in the Javadoc of
the Pub API, `Db` and `AppendOnlyStream` is agent i10's, with 019-10's
error model. BEFORE COMMIT OK.
