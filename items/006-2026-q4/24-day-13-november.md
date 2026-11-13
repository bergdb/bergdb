# 006-24 Day work, 13 November 2026

Created 2026-11-13 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-13 (coord-1113), a Friday, the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1112's handover (006-23, section 6): the tag of 2026.5 (made by
Frans at 06:27), the second prover's run 2 to land, a todo of the tests'
time limits, 027's two questions, 026-04's open point.

Frans's answers:

* 06:38, on the todos: "Yes, register them." (021-28, 021-29.)
* 06:47, "Yes", to coord-1113's recommendation for TP11 (024-12): option
  B, `keyWf` unchanged (what `Keys.toSegments` makes, any length);
  `ScanOK` gets a premise, every key of the run at most `scanFuel`
  segments, which Java meets by L3 (57,344 bytes a transaction, about
  8,192 segments); `scanFuel`'s comment corrected. Rejected: A, `keyWf`
  bounded at L2's 16 segments (BergDB's own long keys pass L2, so runs
  Java makes would leave `Within`); C, a fuel from the structure (changes
  the trusted reader). Also yes: land the run 2 now, and delete the two
  false theorems instead of keeping unbuilt modules.


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones and do not commit to `main`. Clones and runs
under `/Users/f/fl/bench/2026-11-13/`; the common brief stays
`/Users/f/fl/bench/2026-11-12/common-brief.md`; heavy runs by
`/Users/f/fl/bench/2026-11-11/slot.sh` (in zsh, name both slots).

Usage: the week at 89 % at 06:33, "tight"; Frans's ceiling 95 % until the
reset on Monday 16 November, 22:00. At most two agents at a time, Opus
5.5 at high.


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 024-38 | The tag's record: 024-38 done, 024's log | coordinator | b3f64bb1 |
| 021-28, 021-29 | Two todos registered | coordinator | 9f32bff9 |
| 024-22 | Land the second prover's run 2; ScanOK's premise (B) | tp11b (high) | landed 59510cb5 |
| 024-12 | TP11 option C: the scan's fuel from the parameters; then TP11, TP7 | Codex run 3 (Sol xhigh) | landed 2e71a297: C made; TP11 reduced to TP7 + LatestScanOK |
| 024-12 | TP7, the tree's invariants | Codex run 4 (Sol max) | partial, landed 6caf8750: klong well-formedness through the writer |
| 024-12 | TP7, continued | Codex run 5 (Sol max) | running |
| 024, 015 | Statuses after the release; post-release notes (021-27, 020-29) | tidy (high) | committed ee5712c5 |
| 026-05 | P8: each reclaim step scans at its own time | p8 (xhigh) | landed fe5000ec: back to empty's lag about 1,270 at every n and f |
| 026-06 | A value transformation's failure refuses the transaction | vt (high) | landed 8bd6e3a7..944b4868 |
| 026-07 | The write buffer grows with use (ST8) | wb (high) | landed: an empty database 0.67 MB of heap, not 11.1 |
| 026-11 | G4's lag a gate at 2 R | lag (xhigh) | landed 343fff05: 1.28 R on main, 4.40 R without P8 |
| 026-10 | idByPos after back to empty | idpos (xhigh) | landed: G4 heap 1.08, G5 1.47 on the plain heaps |
| 026-08 | The node size 30 for users | ns30 (xhigh) | landed 000fca5b |
| 026-09 | Reclaim's keys-only scan | kscan (xhigh) | running |
| 026-12 | The stable format: a draft plan for Frans | sfplan (xhigh) | running |
| 026-13 | User apps against today's main | apps (xhigh) | running |
| 027-04 | A proposed outline for 027 | outline (xhigh) | done 92ab6713: 14 parts, Q1 to Q5 for Frans |
| night | `night.sh` on today's main | coordinator | planned for tonight |
| 026-04 | The back-to-empty lag at 10M keys, understood | frac (high) | done 07:44: the phase of reclaim's iteration at the deletes' end (a step scans at its iteration's start), not f; keep 1/4; P8 cures it |
| 021-29 | Unit tests that wait with no timeout | waits (high) | landed dc69b7a6 |
| 021-28 | Unit tests with fixed time limits | limits (high) | landed ffa39b4e |


## 4. Progress

* 06:33 coord-1113 started; coord-1112 closed 06:35.
* 06:47 Frans: TP11 option B; land run 2. Agent tp11b started.
* 06:57 tp11b landed 59510cb5: ScanOK's key premise; false theorems deleted; lake build 272 jobs, axioms standard. Open: a premise on the parameters for the positive TP11 proof (024-12).
* 07:21 Frans: option C instead of B ("OK, do C as recommended"): the proofs for every key length and tree size, no fixed constant; the scan's fuel from the parameters (`Params.fuel`, as the get's). Codex run 3 at xhigh started 07:22 (/Users/f/fl/bench/2026-11-13/cx3/).
* 07:24 Frans away until 09:00; unattended.
* 07:30 Frans 07:30: "Raise the limit to 98% of the usage" (was 95 %).
* 07:30 Frans 07:28: "Let's spend the AI usage left." 026-04 (frac) and 021-29 (waits) started at high.
* 07:36 021-29 landed dc69b7a6 (38 waits bounded, tests only; before-commit OK on 59510cb5 = main).
* 07:44 026-04 explained (frac): the lag follows the phase of reclaim's iterations against n, flipping order three times between 1M and 10M; predicted and measured to within 2 %; keep 1/4; P8 (023-05) removes it.
* 07:38 limits (021-28) started.
* 07:54 Frans 07:53: Codex run 4 at Max on TP7, on top of run 3 (/Users/f/fl/bench/2026-11-13/cx4/).
* 07:57 021-28 landed: the Eviction failure was a race between two reads of a thread's state (not the 2 s deadline); about 90 limits in 20 test files; before-commit OK, and three runs beside 20 CPU hogs OK. Tests only.
* 07:58 Codex run 3 landed 2e71a297 (lake 278 jobs, axioms of 40 theorems standard); 024-12 updated.
* 08:06 Frans 08:04: merge 020-29: landed b0cd3ac4 (lake build 291 jobs, 15 theorems on the standard axioms); 020-29 done.
* 08:09 Frans: usage reset, "plenty of usage left now". Started 2026.6's decided work: 026-05 (P8, xhigh), 026-06 (value transformations, R5), 026-07 (ST8, the write buffer).
* 08:12 tidy done: 024's subitems' statuses (3 open: 02, 12, 22), 015 has no open entry, post-release notes for 021-27 and 020-29.
* 08:41 Frans back.
* 08:47 Frans 08:45 "yes to all" (026-06 Q1 to Q4): 026-06 landed (value and key transformations refuse; gated before-commit, level1, level3); 010-04's R5 line done.
* 08:47 Frans: "Use effort xhigh as default for new agents. We have plenty of AI usage left."
* 08:51 Frans 08:50, yes: 027-02 the trace format kept current; 024-02 moves into 027 as 027-03 (agent sf).
* 08:55 Frans: 024-19 Q2 "Yes as recommended", Q3 "as built" (ea6d1d41).
* 09:12 Frans 09:11, 026-02: QK1 `bergdb.pub.Limits`, QK2 no `isKey`, QK3 "Leave it out. We can easy add it if requested." (no `levelBytes`, no `checkPut`), QK4 2026.6. Agent keys started.
* 09:21 Frans 09:17 and 09:21: the node size fixed at 30 for users, other sizes for tests only: 026-08 registered (3ed1ee7d); 024-19's Q2 revised, Q5 dropped.
* 09:24 Frans 09:23: QM1 and 027-03's section 21 decided work for 2026.6.
* 09:33 Frans, 026-02: Q9-1 `keyBytes` returns long, "Yes"; the new dependency of pub on core (D3) not accepted: "This needs to be discussed. A new package dependency." -> "Yes" to taking the constants through pubimp. The agent keys changes it.
* 09:36 026-02 landed 59c6e4b6: `bergdb.pub.Limits` (keyBytes, checkKey, the constants through pubimp).
* 09:37 Codex run 4 stopped by itself at 09:02 (TP7 partial, 137 theorems); checked (lake 306 jobs, axioms standard) and landed 6caf8750. Run 5 started 09:37 at max, told not to stop at a checkpoint.
* 09:38 Frans: Q34-1 option (b) for 2026.6 after P8: 026-09 registered.
* 09:42 Frans 09:41: 026-05's Q1 to Q4 "Yes to all four." P8 merged with main, gated again before landing.
* 09:54 026-05 (P8) landed fe5000ec, gated on the merged tree (before-commit, level1, level3).
* 10:00 Frans on 026-07: Q1 as recommended, Q4 ok; Q3 "keep it as a constant, but use 2 seconds"; Q2 "significant for certain applications [...] I don't like just adding the tables. We get a violation of back-to-empty" (in discussion); asked whether the 10 MB maximum of the buffer should be discussed.
* 10:05 Frans: the buffer's maximum stays 10 MB ("Keep 10 MB."); no study.
* 10:06 Frans on 026-07's Q2: "Keep it as is, KISS. Complexity and code size are costs too. Easy to implement later if ever needed." (Cache3's tables unchanged). 026-10 registered (idByPos after back to empty).
* 10:09 026-07 landed (gated on main with P8: before-commit, level1, count-gates).
* 10:11 Frans 10:09: "Sure, do them. As suggested." 026-11 (G4's lag as a gate), 026-10, 026-08, 026-09 started at xhigh.
* 10:18 026-11 landed 343fff05: G4's lag a gate at 2 R.
* 10:20 Frans 10:13 and 10:18: a todo list apart from the release items; 028-todo created, not tied to a release ("The release item itself will decided the scope of the release."); existing items stay where they are. The rule in items/readme.md, "Todos and release items".
* 10:26 Frans 10:24: "Yes to 'start 1 and 2 now, and plan 3 for tonight'." and "create a subagent at xhigh for 027". Started 026-12 (the stable format's plan), 026-13 (user apps), 027-04 (an outline for 027); `night.sh` on main tonight.
* 10:37 Frans 10:26 and 10:36: proofs with Claude too, as recommended, D on Fable at High: provers latest (LatestGetOK, LatestScanOK), cost (TP32, TP33), t4 (T4), tp7 (TP7, independent of Codex). Codex at its limit since 10:01 (resets 12:23).
* 10:38 026-08 landed 000fca5b (node size 30 for users). 027-04 written (92ab6713).
* 10:47 to 10:53: every subagent stopped on API errors (403, authentication) after an account change; Frans logged in again at 10:52; all seven resumed.
* 11:12 Frans 11:09 on 027-04: Q1 to Q4 as recommended (Q2: "Core is really the thing here", the Pub layer a last part); Q5: 027 with Lean the authority, Java comments may repeat or summarize. Stubs 027-05 to 027-18 made (58c87d27).
* 11:35 026-10 landed (Frans 11:31: Q1 keep the KeyModSet change; Q2 is 028-01).
* 11:36 Frans 11:34: the reclaim pilot of 027 (027-13): an agent drafts, a second reviews against the code.
* 12:08 Frans 12:07: no more Codex runs today (its budget nearly used; the Claude provers go on). Its run 5's partial TP7 work is checked and landed if clean.
* 12:14 Frans 12:11: the model's scope as an item, "prio now as all major algorithms are stabilizing": 026-14 (reclaim as a whole, the format as bytes, the conflict check; the assumption list).
* 12:22 Pushed: the provers' checkpoints "latest" (TP10 and TP11 at the latest time reduced to OpGetOK and CommitGetOK) and "t4" (T4 proved, its new definitions for Frans to review), main with both built (321 jobs); 026-14. 024-12's board updated.
* 12:34 Frans read 027-13, the reclaim pilot: "027-13 is good! I looks really good." The template for the other parts.
* 12:49 Frans: slots kept as two guards (timing alone, memory) with six as a net, "As recommended"; 007-09 Q1: A, a dated note in 007-01, section 6.
* 13:10 Unattended until 07:00 tomorrow (Frans, 13:09: "Unattended mode! I will likely check in at 16:00 or so. If I don't work until 07:00 tomorrow."). What runs:
  - the provers until 20:00 ("latest", "cost", "tp7"); their checkpoints landed as they come (check, combined build, push);
  - "t44" until 20:00: the bounds as the second review of T4's definitions asks (007-09, `09-t4-in-lean/second-review.md`: DropStep false for Java; reads, not objects; RecordBound; the take's skip past maxBytes);
  - 028-08 to 028-10 evaluated with tests, 028-11's texts (P5 for Frans); 028-03, 028-05, 028-06 (Javadoc); 026-09 (keys-only scan) until 15:00;
  - after 20:00: 007-09 brought up to date (the review, the Java-test and height results, t44);
  - about 20:15: `java/night.sh` on main (013-01); quiet from 22:00; the morning's summary in news.md from 06:00.
* 13:22 026-09 (reclaim's keys-only scan) finished on its branch (`026-09-keys-only-scan`, 7ae4b857, all gates passed), not landed: it changes reclaim and an existing gate's limit, and its 10M numbers are mixed (loads 44 to 60 % fewer, stream written 1.2 to 4.4 % more), so it waits for Frans.

For Frans to decide
-------------------

1. 026-09: land the keys-only scan (Q1), G5's dead-klong limit from the twin's plus 30 to plus 70 (Q2), the new StreamDigest digests (Q3), `GetMany.valuesBefore` public (Q4). Recommended by its agent: yes to all four. The coordinator's view: land, with the 10M stream-written cost named in the item; the timing pass of 026-04 then shows the net effect. Read: 026-09, items/026-release-2026-6/09-keys-only-scan.md on its branch (clone /Users/f/fl/bench/2026-11-13/kscan/clone).
2. 028-04: a null result of a value transformation deletes the key: document it (recommended) or refuse it.
3. 028-10: the public `Db.start(StartParams)` is a bug by R5 (a later startup pos loses keys for good); options A remove the parameters (recommended), B package-private, C check them. Read: 028-10.
4. 028-11: P5's sentence in 010-01 (T3 proved for BergDB's own take since 007-08); the proposal is in 028-11.

* 13:27 028-08 not a bug; 028-09 a bug, fixed (a startupPos at its own record is refused: before, a damaged last record started with every key gone); 028-11's texts fixed; 028-10 evaluated, for Frans. Landed (3edef8fa).
* 14:02 Prover t45: `bounded_startup` proved (007): one theorem that bounds a cold start's reads after any run that meets its explicit premises, joining T3 (count form), T4 and the read bound.
5. 028-12: Java's take byte limit never held the take back past the deadline in 18 runs (debt at most about half the room); proposal A: DbBuilder refuses a startup distance above 10^9, as `setStartupDistance` does (recommended), B take a due transaction that does not fit (needs a record split), C no change with the premise written down. Read: 028-12.
* 14:25 Frans: "Opus xhigh as now. And use Fable High if really needed. Those two are great at reasonable cost."
