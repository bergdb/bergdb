# 024-31. Cap the take's pace after a decrease of the startup distance

Created 2026-11-12 by an agent ("pace") of the day's coordinator
(coord-1112). Status: done (2026-11-12): on `main` since `c1137b69`
(Frans, 13:09: section 10 approved). Not done: the 50M run of section 9.

Frans, 2026-11-12, 11:38, on OP4 of 024-05 and QF8 (the take's bursts):
"Yes, start it." The issue is 015-84: since 007-07 a record takes its
share of the startup section's got-dirty index nodes,
share = D (o / O) (S / sd), and right after a decrease of the startup
distance with one call S is still the old section, so the factor S / sd
starts at the old setting over the new one (10 from 1000 to 100 MB). The
catch-up's records were 13 to 15 MB at 50M keys (12 to 14 times the new
mean) and 5.1 MB at 10M from 200 to 50 MB (5.9 times), written in user
commits (007-07, sections 10.4 and 11.2). The brief's fix: cap the factor
at c, S replaced by min(S, c sd), in integers.

Outputs: [31-pace-cap/](31-pace-cap/).


## 1. In short

* **The rule, c = 2:** the share counts the span of the section's
  transactions as at most 2 sd: S' = S - max(0, span - 2 sd) in place of
  S (`TransSeq.shareSection`, `SHARE_FACTOR_CAP`). Not min(S, c sd) as
  briefed: that one also binds with a constant setting when records are
  large against sd, and changed 32 of StreamDigest's 48 digests and three
  unit tests that have no decrease (section 5). With the span, T3 (the
  span below 2 sd with a constant setting) makes the stream the same,
  byte for byte, whenever the setting has not been lowered.
* **At 10M keys it halves the catch-up's largest records:** from 200 to
  50 MB 4.12 to 2.36 MB (10.1 to 5.8 times the new mean), from 1000 to
  100 MB 1.90 to 0.99 MB (5.9 to 3.1 times); the call's own record 4.80
  to 2.49 and 3.18 to 0.82 MB.
* **The cost: a longer catch-up.** From 1000 to 100 MB the section is
  below the new 2 sd after 2.88M puts and 1451 MB of stream, against
  0.64M and 795 MB; from 200 to 50 MB after 0.13M and 250 MB, against
  0.08M and 234 MB. The section shrinks at every record meanwhile.
* **c = 4 does nothing from 200 to 50 MB** (measured on the brief's
  rule: main's stream, byte for byte), and c below 2 would bind with a
  constant setting; so c = 2.
* **Lean**: the theorems hold for any pace, no proof changes; the model's
  `javaPace` mirrors Java's arithmetic, so it has the cap too.
* **Expected values changed** in their own commit, for Frans's approval
  (section 7).


## 2. The proof (step 1)

`T3_take`, `T3_take_restarts`, `T3_take_decrease` and
`T3_take_decrease_restarts` (lean/SIS/BoundTheorems.lean) take any
`pace : Pace V T` with `al.policy = takePolicy size sd pace`; nothing in
them uses the share's arithmetic (docs/sis-model.md, section 10: "with
any share"). So the cap needs no change to a theorem or a proof.

But the model also keeps BergDB's own pace, `shareFp`, `ditherFp`,
`javaPace` and `javaTake` (lean/SIS/Bound.lean, the trusted part), used
by no theorem and kept to check the model against Java's arithmetic: the
`#guard`s of SIS/BoundExample.lean and `TakeCheck` (level2.sh, step 7).
`javaPace` fixes the share's formula, so the cap is mirrored there:
`shareFactorCap := 2`, and the length passed to `shareFp` is
`S.cost size s S.length - (S.span size - shareFactorCap * sd i)`, Nat's
truncated subtraction being Java's max(0, ...). `S.span size` is the span
that `takePolicy`'s deadline already uses, Java's `span()`. `shareFp`
itself is unchanged. `lake build` passes with the new numbers of section 7.


## 3. The rule (step 2)

* **What.** `TransSeq.take` passes `shareSection(S, span, sd)` =
  S - max(0, span - c sd) to `shareFp` in place of S, c =
  `SHARE_FACTOR_CAP` = 2; S is the section, from the startup pos to the
  end of the stream, span that of the section's transactions, from the
  tpos of the oldest to that of the newest (at most S). While the span
  is at most 2 sd, S' = S. After a decrease, S' = (S - span) + 2 sd: the
  records at the section's two ends and twice the setting, so the
  factor S' / sd is about 2, not the old setting over the new. S' is at
  most S, so `shareFp`'s bounds and 128-bit arithmetic hold as before;
  `shareFp` is unchanged.
* **The deadline is unchanged.** A transaction that begins d or more
  before the end of the stream is taken whatever the share, d the larger
  of 2 sd and the span. While the span is over 2 sd, after a decrease,
  each record takes at least the transactions that begin within the last
  record's length of the oldest, so the section without its last record
  shrinks with every record until it is below 2 sd (007-07, 10.4;
  `T3_take_decrease`). The cap binds exactly while the deadline is at the
  span.
* **When and by whom.** At every record, in `TransSeq.take`, which
  `Db.store` calls on the committing thread under the write lock; the
  only caller. A start rebuilds D, O and the span from the section's
  transactions and reads S and sd from the stream, so the stream does not
  depend on restarts (010-01, P2), with the cap as without.
* **Why the span and not S.** With a constant setting T3 bounds the span
  below 2 sd, but not S: S also holds the record at the startup pos and
  the last record, which may be many times sd when sd is small (the
  tests' 100 bytes to 100 kB). min(S, 2 sd) then binds in steady state;
  the span form does not, by T3, and needs no measurement to show it.
* **How it is checked.** Unit tests in `TransSeq`: `testShareCap` (right
  after a decrease from 1000 to 100 MB, S 1000 MB and span 999 MB, the
  section counted is 201 MB and the share 2.01 times the steady one; S as
  it is while the span is at most 2 sd), `testDecreaseCapped` (a decrease
  by ten: no record over c + 1 transactions, where the share without the
  cap was ten; the section shrinks at every record until below the new
  2 sd and stays below), and the existing `testDecrease` (a decrease by
  four, unchanged). `DbTester.testDecreaseOfStartupDistance` on a
  database. `TakeCheck check` (level2.sh, step 7) compares Java's take
  with the Lean model's `javaTake` on 300 cases, 95 of them with a span
  over 2 sd. RestartInvariance (level1, level2) compares the stream with
  and without restarts; StreamDigest by hand against main (section 8).


## 4. Measurements at 10M keys (step 4)

007-07's decrease harness (WriteBench of 007-06 and 007-07, from
`/Users/f/fl/bench/006-09/d2-007-07-runs/w8`), byte counts only (one
slot each, nice 10), on main `f166f5e5` ("main"), on the brief's rule
min(S, c sd) with c = 2 and 4 (branch `024-31-v1`, "min"), and on the
branch's rule ("span", c = 2). Two changes to the harness for today's
main: transactions of 500 puts (Db's limit L1 since 024-17), where 007-07
had 1,000, so the records are about half 007-07's; and no
`retainForever()` (removed in 015-87; forever is the default). Each
decrease is one call at main's "worst" point (the record with the
largest debt after 10M updates, pick.py on main's steady runs: 14,774,000
updates at 200 MB, 10,027,000 at 1000 MB), with 10M updates after it.

"Catch-up": from `setStartupDistance`'s record until the section without
its last record is first below the new 2 sd, both included. "New mean":
the mean record in the second half of the records after the catch-up
(007-07, 11.2). "Over 3/5/10": the catch-up's records over 3, 5 and 10
times the new mean, the call's record included.

From 200 to 50 MB (section 203 MB, debt 174 MB at the call):

| build      | call's record | to 2 sd: puts, stream, records | largest user record | over 3/5/10 |
|---|---|---|---|---|
| main        | 4.80 MB | 0.08M, 234 MB, 171 | 4.12 MB (10.1×) | 92 / 11 / 2 |
| min, c = 2  | 2.49 MB | 0.12M, 249 MB, 250 | 2.36 MB (5.8×)  | 39 / 3 / 0  |
| min, c = 4  | 4.80 MB | 0.08M, 234 MB, 171 | 4.12 MB (10.1×) | 92 / 11 / 2 |
| span, c = 2 | 2.49 MB | 0.13M, 250 MB, 254 | 2.36 MB (5.8×)  | 37 / 3 / 0  |

From 1000 to 100 MB (section 959 MB, debt 569 MB at the call):

| build      | call's record | to 2 sd: puts, stream, records | largest user record | over 3/5/10 |
|---|---|---|---|---|
| main        | 3.18 MB | 0.64M, 795 MB, 1291  | 1.90 MB (5.9×) | 145 / 2 / 0 |
| min, c = 2  | 0.82 MB | 2.90M, 1459 MB, 5801 | 0.98 MB (3.1×) | 2 / 0 / 0   |
| min, c = 4  | 1.46 MB | 1.39M, 1022 MB, 2784 | 1.24 MB (3.9×) | 57 / 0 / 0  |
| span, c = 2 | 0.82 MB | 2.88M, 1451 MB, 5760 | 0.99 MB (3.1×) | 1 / 0 / 0   |

After the catch-up, second half: new mean, section max, largest record:

| decrease    | main                     | span, c = 2              |
|---|---|---|
| 200 to 50   | 407 kB, 1.06 sd, 0.93 MB | 405 kB, 1.08 sd, 0.90 MB |
| 1000 to 100 | 320 kB, 1.04 sd, 0.78 MB | 319 kB, 1.04 sd, 0.71 MB |

To the new sd (not 2 sd) from 1000 to 100 MB: 0.71M puts and 904 MB on
main, 3.02M puts and 1626 MB with the span rule.

* **The section shrank at every record** in every run (ratchet.py): from
  the record after the call it never grew while at or over the new 2 sd,
  and no record was at or over 2 sd after it was first below.
* **c = 4 is main's stream, byte for byte, from 200 to 50 MB** (the .rec
  files are identical): S / sd is 4.06 at the call, and below 4 by the
  next record. A cap of 4 binds only for decreases by more than 4.
* **Where the largest records are.** From 200 to 50 MB, and on main from
  1000 to 100 MB, the largest user record is the first after the call,
  and the call's own record is larger still: its transaction carries a
  value of 200 kB (007-07, 10.5), five times a user record's own bytes,
  so its share is five times theirs; the records after it follow it
  down, as the deadline at the span takes at least the last record's
  length of the section (007-07, 10.4). From 200 to 50 MB with the cap:
  2.49, 2.36, 2.22, 1.94, 1.85 MB. With the cap from 1000 to 100 MB the
  largest is near the end (record 5753 of 5760), where D / O has grown.
* **With the cap, from 1000 to 100 MB, the catch-up's records are
  smaller than the new mean** for most of it (0.1 to 0.3 MB against
  319 kB): the share is about twice D / O times o, and D / O is still
  near the old setting's, lower, as at 1000 MB a put more often finds its
  node dirty already (007-07, 11.2). That is why the catch-up is 4.5
  times longer in puts.
* **Steady state (015-84, question 3).** In main's steady runs S / sd is
  at most 1.032 at 200 MB and 1.065 at 1000 MB. The steady runs at 200 MB
  on the min rule (c = 2) and the span rule are main's, byte for byte
  (all 80,000 records' size, index bytes, section, D and debt). The
  decreases' records before the call are main's in every run.


## 5. Why not min(S, c sd)

The brief's rule was measured first (branch `024-31-v1`, `c7c7b5af`).
Its 10M runs are those of section 4, nearly the span rule's. But its
gates showed that it binds with a constant setting:

* StreamDigest against main: 32 of 48 digests differed, in
  configurations without a decrease.
* Three unit tests without a decrease failed on it and pass on main:
  `CorruptStreamTester.testFound019_32` (its rows name nodes at stream
  positions, which moved), `Eviction.testLoweredBudgetAfterPinsFell`,
  and `TransSeq.testShare` (S / sd 2.5).
* TakeCheck: 80 of 300 cases changed, against 56 with the span rule.

The cause: S counts the record at the startup pos and the last record,
which in the tests (sd of 100 bytes to 100 kB) can be many times sd, so
S / sd exceeds 2 with no decrease. T3 bounds only the span. With the span
rule the same three tests pass unchanged, TakeCheck changes only in cases
whose span is over 2 sd, and StreamDigest is unchanged (section 8). So I
chose the span rule (decision by the agent, 2026-11-12, 12:20; for
Frans to confirm, section 10).


## 6. The choice: c = 2

* c below 2 would bind with a constant setting, where the span reaches
  up to 2 sd; c = 2 is the smallest that never binds there (by T3).
* c = 4 does nothing for a decrease by 4 or less (200 to 50 MB above:
  10.1 times the new mean, as main), and from 1000 to 100 MB it lies
  between: 1.24 MB (3.9 times), the call's 1.46 MB, 1.39M puts.
* 024-05's BD1 asks for no record over the larger of 1 MB and 5 times
  its run's mean. c = 2 meets it from 1000 to 100 MB (0.99 MB) and comes
  near it from 200 to 50 MB (2.36 MB, 5.8 times, set by the call's own
  record); c = 4 does not from 200 to 50 MB. At 50M keys, where D / O is
  4 times larger (007-07, 11.2), the records without the cap grew 4
  times; the smaller cap keeps more margin there.
* The cost is the catch-up's length: up to 4.5 times the puts and 1.8
  times the stream from 1000 to 100 MB. During it startup reads at most
  the section at the call (`T3_take_decrease`), a section the user had
  before the call; the setting is lowered rarely.
* What is left of the records is mostly the call's own 200 kB value and
  the deadline's echo of it (section 4). A smaller value for
  `setStartupDistance`'s record would lower both; not done here (007-07,
  10.5).


## 7. Expected values that changed

Commit B on the branch (`4b7c638e`), apart from the code, for Frans's
approval:

* `TakeCheck.EXPECTED` (java/stress/TakeCheck.java) and `javaTakes`
  (lean/SIS/BoundExample.lean): 56 of the 300 cases take fewer
  transactions (none more), all with a span over 2 sd; the share takes
  more than the deadline in 198 cases (213 before), stops before the end
  in 163 (unchanged).
* The Lean decrease example from 2000 to 400 after T(40): the section is
  1232 and 1080 after T(41) and T(42), not 1016 and 816; below 800 at
  T(43) as before, and shrinking at each.
* `DbTester.testDecreaseOfStartupDistance` (2 MB to 450 kB): the section
  is below the new 2 sd after 116 commits, not under 60; the bound is now
  150. Its other checks (no jump, the span shrinks at every commit, the
  deadline holds after) are unchanged and pass.

`shareFp`'s numbers (TakeCheck's FP_SHARE, the `#guard`s) and every
other test are unchanged.


## 8. Gates (step 6)

On `4b7c638e` (commit B), 2026-11-12, 12:41 to 13:05, each in one slot
(`/Users/f/fl/bench/2026-11-12/pace/gates/`):

| gate                                        | result                         |
|---|---|
| java/before-commit.sh                       | BEFORE COMMIT OK, 67 s         |
| java/stress/level2.sh (full)                | LEVEL 2 OK                     |
| its RestartInvariance (step 4)              | STREAM: identical, every run   |
| its TakeCheck check and lake build (step 7) | TAKECHECK OK (300, 8, 11)      |
| StreamDigest all, main against the branch   | DIGESTS IDENTICAL (48 of 48)   |

level2 is the level of the startup section's mechanism, the take
(docs/levels.md, section 5); its step 7 builds the Lean model (`lake
build`, the `#guard`s of section 7) and compares Java's take with it.
StreamDigest ran main's jar (`f166f5e5`) and the branch's with the
branch's compiled StreamDigest (unchanged): no digest changed, as no
configuration lowers the setting. On the brief's rule (`024-31-v1`) the
same gates failed: 3 unit tests and 32 of 48 digests (section 5).


## 9. 50M keys (step 5): the command for a later night step

Not run. One decrease from 1000 to 100 MB with the span rule, c = 2, at
007-07's fixed "20M" point (11.2: 15.36 MB records without the cap), so
that no steady run is needed first; one 22 GB JVM in one slot, nice 19,
perhaps 30 to 60 minutes; `VARIANT=main` gives the run without the cap
with the same 500 puts a transaction:

    sh items/024-release-2026-5/31-pace-cap/run50.sh

It runs in this item's work directory, `/Users/f/fl/bench/2026-11-12/pace/w`
(variant c2s: the branch's jar and WriteBench compiled against it), and
prints catchup.py's and ratchet.py's lines.


## 10. Questions for Frans

* Approve the changed expected values of section 7 (commit B).
* The span rule in place of min(S, c sd) (section 5), and c = 2?


## State

2026-11-12, 13:08.

* **Ready to land.** Clone `/Users/f/fl/bench/2026-11-12/pace/clone`,
  branch `024-31-pace-cap` from main `f166f5e5`, head **`4b7c638e`**:
  commit A `a9270c09` (the span rule, tests, Lean, levels.md), commit B
  `4b7c638e` (the expected values of section 7, for Frans's approval).
  Every gate of section 8 passed on it. Main has moved since (to
  `3b14e052`, 024-30's CountGates and items; no file of this branch),
  so the coordinator merges on its gates.
* **Not to land.** Branch `024-31-v1` (`c7c7b5af`), the brief's rule
  min(S, c sd), kept for section 5's comparison.
* **Done.** Sections 1 to 9; 015-84 marked "Made in 024-31".
* **Open.** Frans's answers to section 10; the 50M run of section 9 (a
  night step); 015-84's other questions not asked here (the commit
  times, the quick suite's tail, DlProbe) stay with 015-84.

2026-11-13. Status set after the release (coord-1113).
